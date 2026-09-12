-- | Type inference for @instral@ (MS5 phase 66c).
--
-- **Hindley-Milner over the signature table**, which is phase 66b's
-- ("Thena.Ops.operandTypes", "Thena.Ops.resultOf", "Thena.Rules.testTypes").
-- Nothing here knows what an op /does/; it knows what each one takes and leaves,
-- and works out the rest.
--
-- **The unit is every loaded base at once, not one base and not one rule.** A
-- call may name a rule written below it, a rule in a base loaded later, or
-- itself ("Thena.Ops.Call"), so a rule's signature is not decidable until the
-- whole program is in hand. 'inferProgram' is therefore what a load runs, after
-- every base is read and before any is installed — where 'Thena.Rules.validate'
-- is per-rule and runs as each is resolved.
--
-- **A call to a name nothing defines constrains nothing.** It is not an error:
-- §8 has always allowed it, and the machine reports it at run time when the
-- search finds no clause. Its arguments and its result get fresh variables and
-- the inference simply learns nothing from it.
--
-- **Every error, not the first** — 'Thena.Rules.validate'\'s rule, for its
-- reason: a rule base is edited as a file, and being told one mistake at a time
-- is being told to run the loop again.
module Thena.Instral.Infer
  ( InstralTypeError (..)
  , Site (..)
  , inferProgram
  , renderInstralTypeError
  ) where

import Data.List (nub)
import Data.Maybe (fromMaybe, listToMaybe)

import Thena.Core.Term (GlobalName (..))
import Thena.Instral.Type (Signature (..), Ty (..), renderTy, typeVarsIn)
import Thena.Rules (testTypes)
import Thena.Ops
  ( Instr (..)
  , Name
  , Op (..)
  , Operand (..)
  , Rule (..)
  , Test
  , Value (..)
  , operandTypes
  , resultOf
  )

-- --------------------------------------------------------------------------
-- What a failure says
-- --------------------------------------------------------------------------

-- | Where a constraint came from, so a message can point at a line.
--
-- A body position is the instruction's index, which is what every other rule
-- error already carries ('Thena.Rules.RuleError'): a body is written one
-- instruction to a line.
data Site
  = InHead GlobalName Int   -- ^ rule, which test
  | InBody GlobalName Int   -- ^ rule, which instruction
  | InSignature GlobalName Int
    -- ^ **the declaration itself, and its arity** (MS5 phase 67). His
    -- requirement: /a wrong annotation must report against the declaration, not
    -- only where it bites/. A body that contradicts its signature is reported
    -- where it contradicts it — that is the author's own rule, and §6.5(a) calls
    -- it local and clear — but the two faults that are the /declaration's/ are
    -- reported here.
  deriving (Eq, Show)

data InstralTypeError
  = Clash Site Ty Ty
    -- ^ wanted, got
  | Occurs Site Ty
    -- ^ a type would have to contain itself
  | BindsNothing Site GlobalName
    -- ^ @x = call f@ where no clause of @f@ returns anything.
    --
    -- **Phase 63 deferred exactly this to run time** — @produces (Call …)@ is
    -- 'True' unconditionally because /which clauses a name has is not known when
    -- a body is read/. That is true of reading a body and false of this pass,
    -- which has every base in hand, so the check comes back where MS5.md said
    -- it would.
  | AnnotationTooGeneral Site Ty
    -- ^ the signature promises a variable where the body needs a particular
    -- type. Carries what the body pinned it to.
  | SignatureUnanswered GlobalName Int
    -- ^ a signature for a callable no rule defines.
  | TextNotTextual Site Ty
    -- ^ a @\"…\"@ literal where that type is wanted.
    --
    -- **A string literal is accepted at 'TName' or at 'TString'** — his ruling,
    -- 2026-09-12 — and at nothing else. This is the case where the position
    -- wanted something a literal cannot be.
  deriving (Eq, Show)

nameOf :: GlobalName -> Name
nameOf (GlobalName n) = n

renderSite :: Site -> String
renderSite si = case si of
  InHead (GlobalName n) i -> n ++ ", test " ++ show (i + 1)
  InBody (GlobalName n) i -> n ++ ", instruction " ++ show (i + 1)
  InSignature (GlobalName n) a -> "signature " ++ n ++ "/" ++ show a

renderInstralTypeError :: InstralTypeError -> String
renderInstralTypeError e = case e of
  Clash si want got ->
    renderSite si ++ ": wanted " ++ renderTy want ++ ", got " ++ renderTy got
  Occurs si t ->
    renderSite si ++ ": " ++ renderTy t ++ " would have to contain itself"
  BindsNothing si (GlobalName n) ->
    renderSite si ++ ": no clause of " ++ n ++ " returns anything, so there is\
      \ nothing to bind"
  AnnotationTooGeneral si t ->
    renderSite si ++ ": the signature says any type here, but the body needs "
      ++ renderTy t
  SignatureUnanswered (GlobalName n) a ->
    "signature " ++ n ++ ": no rule of that name takes " ++ show a
      ++ (if a == 1 then " argument" else " arguments")
  TextNotTextual si t ->
    renderSite si ++ ": a string literal is a String or a Name, not "
      ++ renderTy t

-- --------------------------------------------------------------------------
-- The state
-- --------------------------------------------------------------------------

-- | Threaded rather than wrapped in a monad, and the substitution is an
-- association list rather than a map: a rule base is a few hundred
-- instructions, @containers@ is not a dependency of this package, and neither
-- a state monad nor a new one would be earning its keep here (§12, and his
-- standing *"no @Supply@ nonsense"*).
data St = St
  { stNext   :: Int
  , stSubst  :: [(Int, Ty)]
  , stErrors :: [InstralTypeError]
  , stText   :: [(Site, Ty)]
    -- ^ **text literals, deferred.** Whether @\"x\"@ is allowed where it stands
    -- cannot be answered when it is read: in a recursive group the position's
    -- type may still be a variable that the callee's own body will pin. So the
    -- question is asked again once everything is solved — see 'settleText'.
  }

fresh :: St -> (Ty, St)
fresh st = (TVar (stNext st), st { stNext = stNext st + 1 })

freshes :: Int -> St -> ([Ty], St)
freshes n st0 = go n st0 []
  where
    go 0 st acc = (reverse acc, st)
    go k st acc = let (t, st') = fresh st in go (k - 1) st' (t : acc)

oops :: InstralTypeError -> St -> St
oops e st = st { stErrors = stErrors st ++ [e] }

-- --------------------------------------------------------------------------
-- Unification
-- --------------------------------------------------------------------------

-- | Follow a variable as far as the substitution takes it, at the top only.
shallow :: St -> Ty -> Ty
shallow st t = case t of
  TVar i -> maybe t (shallow st) (lookup i (stSubst st))
  _      -> t

-- | …and everywhere, for a message.
deep :: St -> Ty -> Ty
deep st t = case shallow st t of
  TList a   -> TList (deep st a)
  TOption a -> TOption (deep st a)
  TPair a b -> TPair (deep st a) (deep st b)
  TFun as r -> TFun (map (deep st) as) (deep st r)
  t'        -> t'

unify :: Site -> Ty -> Ty -> St -> St
unify si want got st = case (shallow st want, shallow st got) of
  (TVar i, TVar j) | i == j -> st
  (TVar i, u)               -> bind si i u st
  (u, TVar i)               -> bind si i u st
  (TList a,   TList b)      -> unify si a b st
  (TOption a, TOption b)    -> unify si a b st
  (TPair a b, TPair c d)    -> unify si b d (unify si a c st)
  -- **Invariant in both positions, and the arity must agree** (MS5 phase 68b):
  -- @instral@ functions are n-ary and applied all at once, so a function of two
  -- arguments is not a function of one whatever the types.
  (TFun as x, TFun bs y)
    | length as == length bs ->
        unify si x y (foldl (\s (a, b) -> unify si a b s) st (zip as bs))
  (a, b) | a == b           -> st
         | otherwise        -> oops (Clash si (deep st want) (deep st got)) st

bind :: Site -> Int -> Ty -> St -> St
bind si i t st
  | occurs st i t = oops (Occurs si (deep st t)) st
  | otherwise     = st { stSubst = (i, t) : stSubst st }

occurs :: St -> Int -> Ty -> Bool
occurs st i t = case shallow st t of
  TVar j    -> i == j
  TList a   -> occurs st i a
  TOption a -> occurs st i a
  TPair a b -> occurs st i a || occurs st i b
  TFun as r -> any (occurs st i) as || occurs st i r
  _         -> False

-- | An op's or a test's declared types are a /scheme/: 'Thena.Instral.Type.TVar'
-- numbered from zero, meaning "any type, the same one wherever it repeats
-- inside this signature". Every use gets its own copy.
instantiate :: [Ty] -> St -> ([Ty], St)
instantiate ts st = let ((xs, _), st') = instantiateWith ts st in (xs, st')

-- | 'instantiate', and the renaming it used — which a declared signature needs
-- so that 'generalEnough' can ask what became of each variable.
instantiateWith :: [Ty] -> St -> (([Ty], [(Int, Ty)]), St)
instantiateWith ts st0 =
  let vs        = nub (concatMap typeVarsIn ts)
      (ns, st1) = freshes (length vs) st0
      table     = zip vs ns
      go t = case t of
        TVar i    -> fromMaybe t (lookup i table)
        TList a   -> TList (go a)
        TOption a -> TOption (go a)
        TPair a b -> TPair (go a) (go b)
        TFun as r -> TFun (map go as) (go r)
        _         -> t
   in ((map go ts, table), st1)

-- --------------------------------------------------------------------------
-- The signature environment
-- --------------------------------------------------------------------------

-- | A rule is addressed by its name **and its arity**, exactly as dispatch
-- addresses it ('Thena.Rules.clauses'): two rules of one name and different
-- arities are two callables, and *"a clause of another arity is skipped, not an
-- error"*.
type Callable = (GlobalName, Int)

-- | Every clause of one name and arity shares one signature — its parameters'
-- types and the type it returns. Clauses that disagree are what a 'Clash'
-- reports, and the site is whichever clause was walked second.
--
-- **The result is 'Nothing' when no clause of the callable says @return@.** Not
-- a variable: a variable would let @x = call f@ type-check and then fail at run
-- time with 'Thena.Errors.NothingReturned', which is precisely the check phase
-- 63 had to defer and this pass can make again. Every rule in the shipped base
-- is in that position today.
type SigEnv = [(Callable, Bound)]

-- | How a callable's type was arrived at, because uses of the two differ.
--
-- **A declared signature is a scheme and is instantiated at every use**, which
-- is the whole reason to write one: it is what lets a rule be used at two types.
-- An inferred one is a single set of variables shared by every use — the
-- monomorphism a recursive group has, and @ms5\/CLOSEOUT.md@ 8.
data Bound
  = Inferred [Ty] (Maybe Ty)
  | Declared Signature
  deriving (Eq, Show)

-- --------------------------------------------------------------------------
-- The pass
-- --------------------------------------------------------------------------

-- | Infer every rule in every loaded base, together.
--
-- Answers the signature it worked out for each callable, so that a later phase
-- can print them, and every error it found.
--
-- **The group is not broken into strongly connected components**, so a rule
-- used at two different types is inferred at one. That is the monomorphism a
-- single recursive group has, it is what Haskell would do inside one @let@
-- group without a signature, and phase 67 is where an annotation lifts it.
-- Nothing in the shipped base wants two types today.
inferProgram
  :: [(String, Signature)] -> [Rule]
  -> ([(Callable, Signature)], [InstralTypeError])
inferProgram sigs rs =
  let (env, st0) = declareAll sigs rs (St 0 [] [] [])
      st1        = foldl (clause env) st0 rs
      st2        = settleText st1
      out        = [ (c, whatItIs st2 b) | (c, b) <- env ]
      unanswered = [ SignatureUnanswered (GlobalName n) (length (sigParams t))
                   | (n, t) <- sigs
                   , (GlobalName n, length (sigParams t)) `notElem` map fst env
                   ]
   in (out, stErrors st2 ++ unanswered)

-- | What to report as a callable's signature: the declaration if there was one,
-- and otherwise what the solved substitution makes of its variables.
whatItIs :: St -> Bound -> Signature
whatItIs st b = case b of
  Declared sg    -> sg
  Inferred ps r  -> Signature (map (deep st) ps) (fmap (deep st) r)

-- | One fresh variable per parameter, and one for the result **only if some
-- clause of the callable returns**.
declareAll :: [(String, Signature)] -> [Rule] -> St -> (SigEnv, St)
declareAll sigs rs st0 = foldl one ([], st0) (nub (map callableOf rs))
  where
    one (env, st) c@(GlobalName n, k) = case declaredFor n k of
      -- **A declared signature is taken as given**, and the body is checked
      -- against it rather than the other way round — which is the difference
      -- between an annotation and a comment.
      Just sg -> (env ++ [(c, Declared sg)], st)
      Nothing ->
        let (ps, st1) = freshes k st
         in if any (returnsSomething . ruleBody) [ r | r <- rs, callableOf r == c ]
              then let (v, st2) = fresh st1
                    in (env ++ [(c, Inferred ps (Just v))], st2)
              else (env ++ [(c, Inferred ps Nothing)], st1)

    declaredFor n k =
      case [ t | (n', t) <- sigs, n' == n, length (sigParams t) == k ] of
        t : _ -> Just t
        []    -> Nothing

-- | Does this body end a call with a value?
--
-- **A @return@ inside a @do@ block does not count.** 'Thena.Ops.Block' builds an
-- ordinary call frame, so @return@ there ends the block and the value is
-- dropped — see "Thena.Engine"'s 'Thena.Ops.Return' case, which says so.
returnsSomething :: [Instr] -> Bool
returnsSomething is = or [ True | Do (Return _) <- is ] || or [ True | Bind _ (Return _) <- is ]

callableOf :: Rule -> Callable
callableOf r = (ruleName r, length (ruleParams r))

-- | Walk one clause: its head, then its body.
clause :: SigEnv -> St -> Rule -> St
clause env st0 r = case fromMaybe (error "declareAll missed a rule")
                          (lookup (callableOf r) env) of
  Inferred ps res -> walk ps res st0
  -- **A declared signature is checked, not assumed.** The clause is walked with
  -- a fresh copy of the scheme, and then 'generalEnough' asks whether the copy's
  -- variables are still variables: if the body pinned one, the signature
  -- promised more than the rule delivers, and that is the declaration's fault
  -- rather than the body's.
  Declared sg ->
    let ((ts, table), st1) = instantiateWith (sigParams sg ++ resultOfSig sg) st0
        (ps, res)          = splitAt (length (sigParams sg)) ts
        st2                = walk ps (listToMaybe res) st1
     in generalEnough (InSignature (ruleName r) (length (sigParams sg))) table st2
  where
    walk ps res st =
      let ctx = zip (ruleParams r) ps
          st1 = foldl (headTest r ctx) st (zip [0 ..] (ruleHead r))
       in body env r res ctx 0 st1 (ruleBody r)

    resultOfSig sg = maybe [] (: []) (sigResult sg)

-- | Are the scheme's variables still variables, and still distinct?
--
-- **Both halves matter.** A body that forces one to a particular type has
-- contradicted the promise; two that it forced together have contradicted it
-- just as much, because @a -> b@ said they need not be the same.
generalEnough :: Site -> [(Int, Ty)] -> St -> St
generalEnough si table st = foldl one st (zip [0 :: Int ..] images)
  where
    images = [ (v, shallow st img) | (v, img) <- table ]
    one s (i, (_, img)) = case img of
      TVar j
        | j `elem` [ k | (_, TVar k) <- take i images ] ->
            oops (AnnotationTooGeneral si (deep s img)) s
        | otherwise -> s
      other -> oops (AnnotationTooGeneral si (deep s other)) s

headTest :: Rule -> [(Name, Ty)] -> St -> (Int, Test) -> St
headTest r ctx st (i, t) =
  let si          = InHead (ruleName r) i
      declared    = testTypes t
      (want, st') = instantiate (map snd declared) st
   in foldl (\s (w, a) -> operandAgainst ctx si w a s) st'
        (zip want (map fst declared))

-- | Walk a body, threading what each @Bind@ adds to scope.
body :: SigEnv -> Rule -> Maybe Ty -> [(Name, Ty)] -> Int -> St -> [Instr] -> St
body _   _ _   _   _ st []             = st
body env r res ctx i st (instr : rest) =
  let si = InBody (ruleName r) i
      o  = case instr of { Bind _ x -> x; Do x -> x }
      (mres, st1) = operation env r res ctx si o st
      (ctx', st2) = case (instr, mres) of
        (Bind n _, Just t)  -> ((n, t) : ctx, st1)
        (Bind n _, Nothing) ->
          -- **A call is the case worth reporting.** For every other op
          -- 'Thena.Rules.validate' has already refused this
          -- ('Thena.Rules.BoundNonProducing'); a call passes that check because
          -- 'Thena.Ops.produces' cannot answer for one, and this pass can.
          let (t, s0) = fresh st1
              s = case o of
                Call nm as | notReturning (lookup (nm, length as) env) ->
                  oops (BindsNothing si nm) s0
                _ -> s0
           in ((n, t) : ctx, s)
        (Do _, _)           -> (ctx, st1)
   in body env r res ctx' (i + 1) st2 rest

-- | One op: check its operands, answer the type it leaves.
operation
  :: SigEnv -> Rule -> Maybe Ty -> [(Name, Ty)] -> Site -> Op -> St
  -> (Maybe Ty, St)
operation env r res ctx si o st0 = case o of
  -- **A lambda's type is worked out here** (MS5 phase 68b) — the table cannot,
  -- because a lambda's parameters and result are whatever its body makes them.
  -- The body is walked in a scope of its own with a result variable of its own,
  -- exactly as a rule's is; it already ends in a @return@, which is what pins
  -- the result.
  Lambda ps b ->
    let (vs, st1)   = freshes (length ps) st0
        (rv, st2)   = fresh st1
        st3         = body env r (Just rv) (zip ps vs ++ ctx) 0 st2 b
     in (Just (TFun vs rv), st3)

  -- **A local shadows a rule** — his ruling, 2026-09-12 — so a call whose name
  -- is bound here is an application of that value, and its type says so.
  Call nm as
    | Just t <- lookup (nameOf nm) ctx ->
        let (ats, st1) = freshes (length as) st0
            (rv, st2)  = fresh st1
            st3        = unify si t (TFun ats rv) st2
         in (Just rv, foldl (\s (w, a) -> operandAgainst ctx si w a s) st3 (zip ats as))

  -- **A call is where the signature environment is read**, and the only place.
  Call nm as ->
    case lookup (nm, length as) env of
      Nothing ->
        -- Nothing defines it — see the module header. Its arguments are still
        -- walked, so a mistake inside one is still found.
        let st1 = foldl (\s a -> snd (operandType ctx si a s)) st0 as
            (t, st2) = fresh st1
         in (Just t, st2)
      Just (Inferred ps cres) ->
        ( cres
        , foldl (\s (w, a) -> operandAgainst ctx si w a s) st0 (zip ps as)
        )
      -- **Every use of a declared signature gets its own copy**, which is what
      -- makes an annotated rule usable at two types where an inferred one is
      -- not (@ms5\/CLOSEOUT.md@ 8).
      Just (Declared sg) ->
        let n            = length (sigParams sg)
            (ts, st1)    = instantiate (sigParams sg ++ maybe [] (: []) (sigResult sg)) st0
            (ps, cres)   = splitAt n ts
         in ( listToMaybe cres
            , foldl (\s (w, a) -> operandAgainst ctx si w a s) st1 (zip ps as)
            )

  -- **@return@ is what says the rule's own result type**, and every clause of
  -- one callable says it about the same variable — which is how two clauses
  -- that disagree are caught.
  Return a -> case res of
    Just v  -> (Nothing, operandAgainst ctx si v a st0)
    -- 'declareAll' looked for exactly this instruction, so it cannot be missing.
    Nothing -> (Nothing, snd (operandType ctx si a st0))

  -- **A block is a body played in a scope of its own** (MS4 phase 45), so its
  -- bindings do not escape — and its @return@ is still this rule's, which is
  -- why 'res' is passed straight through.
  Block is ->
    let (v, st1) = fresh st0
     in (Nothing, body env r (Just v) ctx 0 st1 is)

  -- Everything else is the table, instantiated once: the operand types and the
  -- result together, so a scheme variable shared between them stays shared.
  _ ->
    let declared    = operandTypes o
        (want, st1) = instantiate (map snd declared ++ maybe [] (: []) (resultOf o)) st0
        ws          = take (length declared) want
        rw          = drop (length declared) want
        st2 = foldl (\s (w, a) -> operandAgainst ctx si w a s) st1
                (zip ws (map fst declared))
     in (listToMaybe rw, st2)

-- | Is this a callable that hands nothing back?
--
-- 'Nothing' — nothing defines it — is not: §8 allows a call to a name a later
-- base will define, so the pass learns nothing rather than complaining.
notReturning :: Maybe Bound -> Bool
notReturning b = case b of
  Just (Inferred _ Nothing) -> True
  Just (Declared sg)        -> sigResult sg == Nothing
  _                         -> False

-- | The type of an operand, checked against what the position wants.
operandAgainst :: [(Name, Ty)] -> Site -> Ty -> Operand -> St -> St
operandAgainst ctx si want o st = case o of
  -- **Deferred, not decided here** — see 'stText'.
  Lit (VText _) -> st { stText = stText st ++ [(si, want)] }
  _             -> let (got, st') = operandType ctx si o st
                    in unify si want got st'

-- | …and its type when nothing constrains it.
operandType :: [(Name, Ty)] -> Site -> Operand -> St -> (Ty, St)
operandType ctx si o st = case o of
  Ref n -> case lookup n ctx of
    Just t  -> (t, st)
    -- 'Thena.Rules.validate' has already refused an unbound name
    -- ('Thena.Rules.UnboundInRule'); a fresh variable keeps this pass total.
    Nothing -> fresh st
  Lit v      -> valueType si v st
  ListOf os  ->
    let (a, st1) = fresh st
        st2 = foldl (\s x -> operandAgainst ctx si a x s) st1 os
     in (TList a, st2)
  PairOf x y ->
    let (a, st1) = fresh st
        (b, st2) = fresh st1
        st3 = operandAgainst ctx si a x (operandAgainst ctx si b y st2)
     in (TPair a b, st3)

-- | A written value's type.
--
-- **A 'VText' never reaches here**, because 'operandAgainst' takes it first: it
-- is the one literal whose type the position decides.
valueType :: Site -> Value -> St -> (Ty, St)
valueType si v st = case v of
  VText _    -> (TString, st)
  VInt _     -> (TInt, st)
  VChar _    -> (TChar, st)
  VBool _    -> (TBool, st)
  VTerm _    -> (TCore, st)
  -- **An unresolved written term is a 'TCore' too** — his ruling, 2026-09-12.
  VRaw _     -> (TCore, st)
  VSurface _ -> (TSurface, st)
  -- **The brand is the type** (MS5 phase 69): the tag is what makes an object
  -- term's type distinct from a bare Surface one.
  VObject n _ -> (TObject n, st)
  VList vs   ->
    let (a, st1) = fresh st
        st2 = foldl (\s u -> let (t, s') = valueType si u s in unify si a t s') st1 vs
     in (TList a, st2)
  VPair a b  ->
    let (ta, st1) = valueType si a st
        (tb, st2) = valueType si b st1
     in (TPair ta tb, st2)
  -- **Cannot arise**: a closure is built by 'Thena.Ops.Lambda' and never
  -- written, so nothing puts one in a 'Thena.Ops.Lit'. Answered rather than left
  -- to a pattern-match failure.
  VClosure ps _ _  -> let (as, st1) = freshes (length ps) st
                          (rv, st2) = fresh st1
                       in (TFun as rv, st2)
  VOption Nothing  -> let (a, st1) = fresh st in (TOption a, st1)
  VOption (Just u) -> let (t, st1) = valueType si u st in (TOption t, st1)

-- | Ask the deferred text-literal questions, now that everything is solved.
--
-- **A position still unconstrained becomes a 'TString'.** It is the only thing
-- left to do — a text literal is not polymorphic, so leaving the variable free
-- would generalise a rule over a type only two values inhabit — and it is the
-- weaker of the two: a 'TName' has a use a 'TString' does not.
settleText :: St -> St
settleText st0 = foldl one st0 (stText st0)
  where
    one st (si, want) = case shallow st want of
      TName   -> st
      TString -> st
      TVar i  -> st { stSubst = (i, TString) : stSubst st }
      other   -> oops (TextNotTextual si (deep st other)) st
