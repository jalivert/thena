-- | Type inference for @instral@ (MS5 phase 66c).
--
-- **Hindley-Milner over the signature table**, which is phase 66b's
-- ("Thena.Instral.Ops.operandTypes", "Thena.Instral.Ops.resultOf", "Thena.Rules.testTypes").
-- Nothing here knows what an op /does/; it knows what each one takes and leaves,
-- and works out the rest.
--
-- **The unit is every loaded base at once, not one base and not one rule.** A
-- call may name a rule written below it, a rule in a base loaded later, or
-- itself ("Thena.Instral.Ops.Call"), so a rule's signature is not decidable until the
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
  , inferBlock
  , renderInstralTypeError
  ) where

import Data.Graph (flattenSCC, stronglyConnComp)
import Data.List (elemIndex, nub, sortOn)
import Data.Maybe (fromMaybe, listToMaybe)

import Thena.Core.Term (GlobalName (..))
import Thena.Syntax.Concrete (Splice (..), splices)
import Thena.Instral.Type (Signature (..), Ty (..), renderTy, typeVarsIn)
import Thena.Rules (testTypes, writtenPositions)
import Thena.Instral.Ops
  ( Instr (..)
  , Name
  , Op (..)
  , Operand (..)
  , Rule (..)
  , Pattern (..)
  , Test
  , Value (..)
  , operandsOf
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
  | InPattern GlobalName Int
    -- ^ **a rule or function's parameter, and which one** (MS5 phase 82),
    -- counted from zero. Its own site rather than 'InHead' or 'InBody': a
    -- pattern runs before both, and a message that named the first instruction
    -- for a fault in a parameter is exactly the class @ms5\/CLOSEOUT.md@ 28
    -- records — /a message must identify the thing it is about uniquely/.
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

renderSite :: Site -> String
renderSite si = case si of
  InHead (GlobalName n) i -> n ++ ", test " ++ show (i + 1)
  InBody (GlobalName n) i -> n ++ ", instruction " ++ show (i + 1)
  InSignature (GlobalName n) a -> "signature " ++ n ++ "/" ++ show a
  -- **Counted from one, like a test and an instruction**, and named /parameter/
  -- rather than given a number alone: a clause's parameters are where the
  -- reader's eye goes last, so the word is worth the four characters.
  InPattern (GlobalName n) i -> n ++ ", parameter " ++ show (i + 1)

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
-- instructions, so neither a state monad nor a @Map@ would be earning its keep
-- here (§12, and his standing *"no @Supply@ nonsense"*). MS5 phase 76 made
-- @containers@ a dependency for @Data.Graph@; that is not a reason to reach for
-- the rest of it.
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
-- **The callables are split into strongly connected components and each group
-- is generalised before the next is walked** — his ruling, 2026-09-13:
-- /"do the SCC and take the type system all the way to HM."/ So a helper called
-- at a @Surface@ in one place and a @Core@ in another is polymorphic rather than
-- a clash, which is @ms5\/CLOSEOUT.md@ 8, and an annotation stops being the only
-- way to a second type.
--
-- **Within a group nothing generalises**, which is Hindley-Milner and not a
-- shortcut: mutually recursive callables share one set of variables, exactly as
-- a Haskell @let@ group does. What the split buys is that the groups are as
-- small as the call graph allows.
--
-- The order the components come back in is the order they must be walked —
-- callees first — so this is a left fold and the environment grows as it goes.
inferProgram
  :: [(String, Signature)] -> [Rule]
  -> ([(Callable, Signature)], [InstralTypeError])
inferProgram sigs rs =
  let (env, st) = foldl (inferGroup sigs rs) ([], St 0 [] [] []) (components rs)
      -- **Reported in the order the file declares them, not the order they were
      -- walked.** The call graph decides the walking order and that is an
      -- implementation detail; @:accepts@, @:produces@ and the shipped base\'s
      -- own signature listing should read down the file.
      out       = [ (c, whatItIs st b) | c <- nub (map callableOf rs)
                  , Just b <- [lookup c env] ]
      unanswered = [ SignatureUnanswered (GlobalName n) (length (sigParams t))
                   | (n, t) <- sigs
                   , (GlobalName n, length (sigParams t)) `notElem` map fst env
                   ]
   in (out, inFileOrder rs (stErrors st) ++ unanswered)

-- | Type one block that runs where it is written, beside every callable, with
-- some names already holding values (MS5 phase 90, @ms5\/CLOSEOUT.md@ 41).
--
-- **A block is not a callable** — nothing can call it and it has no name a user
-- could write — so it is walked after the callables' groups and not among them.
--
-- **A name that already holds a value has that value's type**, read off the
-- value by 'valueType'. That is how a block typed while a rule is yielding sees
-- the rule's own locals: @do { goto h }@ reads the @h@ the rule bound, and is
-- checked against what @h@ actually is rather than refused as unbound.
inferBlock
  :: [(String, Signature)] -> [Rule] -> [(Name, Value)] -> Rule -> [InstralTypeError]
inferBlock sigs rs bound r =
  let (env, st0)  = foldl (inferGroup sigs rs) ([], St 0 [] [] []) (components rs)
      site        = InBody (ruleName r) 0
      (ctx, st1)  = foldr seed ([], st0) bound
      seed (n, v) (acc, st) = let (t, st') = valueType site v st in ((n, Mono t) : acc, st')
      (res, st2)  = fresh st1
   in stErrors (settleText (body env r (Just res) ctx (writtenPositions (ruleBody r)) st2 (ruleBody r)))

-- | The statement a body site points at; anything else counts as the first.
siteIndex :: Site -> Int
siteIndex si = case si of
  InBody _ i -> i
  _          -> 0

-- | Report errors down the file, not along the call graph.
--
-- **The walking order became the call graph\'s at MS5 phase 76** and that is an
-- implementation detail; a reader who loads a file with three mistakes in it
-- should meet them in the order they wrote them. A stable sort on the rule a
-- site names does it, and errors inside one rule keep the order they were
-- found in.
inFileOrder :: [Rule] -> [InstralTypeError] -> [InstralTypeError]
inFileOrder rs = sortOn position
  where
    order = nub (map ruleName rs)
    position e = maybe (length order) id (elemIndex (whose e) order)
    whose e = case e of
      Clash si _ _          -> nameIn si
      Occurs si _           -> nameIn si
      BindsNothing si _     -> nameIn si
      AnnotationTooGeneral si _ -> nameIn si
      SignatureUnanswered n _   -> n
      TextNotTextual si _   -> nameIn si

    nameIn si = case si of
      InHead n _      -> n
      InBody n _      -> n
      InPattern n _   -> n
      InSignature n _ -> n

-- | One strongly connected component: declare it, walk its clauses, generalise.
--
-- **@settleText@ runs before the generalisation and not once at the end**, and
-- it has to: a text literal in a position still unconstrained becomes a
-- 'TString', and generalising first would quantify that variable instead —
-- turning /this is a string/ into /this is any type/. See 'settleText', whose
-- comment says why leaving it free is wrong.
inferGroup
  :: [(String, Signature)] -> [Rule] -> (SigEnv, St) -> [Callable] -> (SigEnv, St)
inferGroup sigs rs (env0, st0) cs =
  let (env1, st1) = declareThese sigs rs cs (env0, st0)
      st2         = foldl (clause env1) st1 [ r | r <- rs, callableOf r `elem` cs ]
      st3         = settleText st2
   in ([ (c, if c `elem` cs then generalise st3 b else b) | (c, b) <- env1 ], st3)

-- | Close an inferred callable over the variables its group left free.
--
-- **The variables are renumbered from zero**, so an inferred scheme is spelled
-- the way a written one is — @a -> b -> ()@ and not @a19 -> a23 -> ()@. That
-- matters for more than looks: 'Thena.Instral.Type.letterFor' names a variable
-- by its number, and @InstralInferTests@ compares the shipped base's inferred
-- signatures as rendered text against what a person would write.
--
-- **Nothing else in the environment can be captured.** A group is declared only
-- when it is reached, and every earlier group is already a closed scheme, so
-- the only free variables in scope at this point are the group's own — which is
-- the side condition Hindley-Milner generalisation needs and which the walking
-- order supplies for free.
generalise :: St -> Bound -> Bound
generalise st b = case b of
  Declared _      -> b
  Inferred ps res ->
    let ps'   = map (deep st) ps
        res'  = fmap (deep st) res
        vs    = nub (concatMap typeVarsIn (ps' ++ maybe [] (: []) res'))
        table = zip vs [0 ..]
     in Declared (Signature (map (renumber table) ps') (fmap (renumber table) res'))

renumber :: [(Int, Int)] -> Ty -> Ty
renumber table t = case t of
  TVar i    -> maybe t TVar (lookup i table)
  TList a   -> TList (renumber table a)
  TOption a -> TOption (renumber table a)
  TPair a c -> TPair (renumber table a) (renumber table c)
  TFun as r -> TFun (map (renumber table) as) (renumber table r)
  _         -> t

-- | The callables, in the order they must be inferred: callees before callers,
-- and a mutually recursive knot as one group.
--
-- **@Data.Graph@ answers in exactly that order** — @stronglyConnComp@ is reverse
-- topologically sorted, which for edges that mean /calls/ is dependencies
-- first.
--
-- **The edges over-approximate, and the cost of that is stated rather than
-- hidden.** A @Call@ whose name is shadowed by a local is an application of the
-- local and not a call at all (his ruling, @ms5\/CLOSEOUT.md@ 14), and this does
-- not track binders, so such a name draws an edge that is not really there. The
-- only consequence is a group larger than it needed to be — less polymorphism,
-- never a wrong type — and a signature is the way out, as it was for everything
-- before this phase.
components :: [Rule] -> [[Callable]]
components rs = map flattenSCC (stronglyConnComp nodes)
  where
    defined = nub (map callableOf rs)
    nodes   = [ (c, c, calledBy c) | c <- defined ]
    calledBy c =
      [ d
      | r <- rs, callableOf r == c
      , d <- callsIn (ruleBody r)
      , d `elem` defined
      ]

-- | Every callable a body calls, descending into lambdas and blocks.
callsIn :: [Instr] -> [Callable]
callsIn = concatMap one
  where
    one i = case i of
      Bind _ _ o -> inOp o
      Do     o -> inOp o

    inOp o = case o of
      -- **Wrapped here, because a 'Callable' is keyed by a RULE's name** and
      -- @Call@ carries only a word (MS5 phase 83). The boundary is one line and
      -- is the whole cost of the narrow rename; widening 'Thena.Instral.Ops.Rule''s own
      -- @ruleName@ is @ms5\/CLOSEOUT.md@ 38 and is not done here.
      Call nm as  -> (GlobalName nm, length as) : concatMap inOperand as
      Lambda _ b  -> callsIn b
      Block b     -> callsIn b
      _           -> concatMap inOperand (operandsOf o)

    inOperand a = case a of
      Lit (VClosure _ b _) -> callsIn b
      _                    -> []

-- | One fresh variable per parameter, and one for the result **only if some
-- clause of the callable returns** — for the callables of one group.
declareThese
  :: [(String, Signature)] -> [Rule] -> [Callable] -> (SigEnv, St) -> (SigEnv, St)
declareThese sigs rs cs st0 = foldl one st0 cs
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

-- | What to report as a callable's signature: the declaration if there was one,
-- and otherwise what the solved substitution makes of its variables.
whatItIs :: St -> Bound -> Signature
whatItIs st b = case b of
  Declared sg    -> sg
  Inferred ps r  -> Signature (map (deep st) ps) (fmap (deep st) r)

-- | Does this body end a call with a value?
--
-- **A @return@ inside a @do@ block does not count.** 'Thena.Instral.Ops.Block' builds an
-- ordinary call frame, so @return@ there ends the block and the value is
-- dropped — see "Thena.Engine"'s 'Thena.Instral.Ops.Return' case, which says so.
returnsSomething :: [Instr] -> Bool
returnsSomething is = or [ True | Do (Return _) <- is ] || or [ True | Bind _ _ (Return _) <- is ]

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
      let (ctx, st1)  = patternCtx (InPattern (ruleName r)) (ruleParams r) ps st
          st2         = foldl (headTest r ctx) st1 (zip [0 ..] (ruleHead r))
       in body env r res ctx (writtenPositions (ruleBody r)) st2 (ruleBody r)

    resultOfSig sg = maybe [] (: []) (sigResult sg)

-- | Type a run of patterns against a run of parameter types (MS5 phase 82).
--
-- **A pattern says its parameter\'s type directly**, which is why the phase
-- made typing simpler rather than harder: @f [a, ...rest]@ needs no annotation
-- and no head test to be known to take a list. Before patterns the only thing
-- that could say so was 'testTypes', which maps a /head test/ to a type — one
-- mechanism for heads and nothing at all for parameters.
--
-- **A literal pattern constrains and binds nothing**: @f 0@ pins the parameter
-- to 'TInt' and adds no name. That is the same shape a head test has, one layer
-- down.
-- **The SITE comes from the caller** (MS5 phase 84). A parameter says
-- @‹rule›, parameter n@ and a binding says @‹rule›, instruction n@ — the same
-- typing, two different things to point at, and a binding reported as a
-- parameter is exactly the class @ms5\/CLOSEOUT.md@ 28 is about: /a message
-- must identify the thing it is about uniquely/.
patternCtx :: (Int -> Site) -> [Pattern] -> [Ty] -> St -> ([(Name, Local)], St)
patternCtx site ps ts st0 = foldl one ([], st0) (zip3 [0 ..] ps ts)
  where
    one (acc, st) (i, pt, t) =
      let (bs, st') = go (site i) pt t st in (acc ++ bs, st')

    go si pt t st = case pt of
      PVar n   -> ([(n, Mono t)], st)
      PWild    -> ([], st)
      PInt _   -> ([], unify si t TInt st)
      PChar _  -> ([], unify si t TChar st)
      PBool _  -> ([], unify si t TBool st)
      -- **A text literal's type is DEFERRED, exactly as an operand's is** —
      -- see 'settleText'. @f "x"@ therefore matches a 'TName' parameter as
      -- readily as a 'TString' one, which is his 2026-09-12 ruling that a
      -- string literal is accepted at either, holding on both sides of the @=@.
      PText _  -> ([], st { stText = stText st ++ [(si, t)] })
      PPair a b ->
        let ((u, v), st1)  = two st
            st2            = unify si t (TPair u v) st1
            (bs1, st3)     = go si a u st2
            (bs2, st4)     = go si b v st3
         in (bs1 ++ bs2, st4)
      PSome a ->
        let (e, st1) = fresh st
            st2      = unify si t (TOption e) st1
         in go si a e st2
      PNone ->
        let (e, st1) = fresh st in ([], unify si t (TOption e) st1)
      -- **Every element and the tail are typed against ONE element variable**,
      -- which is what makes @[a, ...rest]@ say /a list of the same thing/
      -- rather than three unrelated demands. The tail is a whole pattern, so it
      -- is typed against @TList e@ and not against @e@.
      PList qs mt ->
        let (e, st1)   = fresh st
            st2        = unify si t (TList e) st1
            (bs, st3)  = foldl (\(a, k) q -> let (b, k') = go si q e k in (a ++ b, k'))
                               ([], st2) qs
         in case mt of
              Nothing -> (bs, st3)
              Just tl -> let (b2, st4) = go si tl (TList e) st3 in (bs ++ b2, st4)

    two st = let (u, st1) = fresh st
                 (v, st2) = fresh st1
              in ((u, v), st2)

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

headTest :: Rule -> [(Name, Local)] -> St -> (Int, Test) -> St
headTest r ctx st (i, t) =
  let si          = InHead (ruleName r) i
      declared    = testTypes t
      (want, st') = instantiate (map snd declared) st
   in foldl (\s (w, a) -> operandAgainst ctx si w a s) st'
        (zip want (map fst declared))

-- | What a name in scope inside a body stands for.
--
-- **A local is monomorphic unless it is annotated** — his ruling, 2026-09-13,
-- agreeing with /Let Should Not Be Generalised/ and GHC's @MonoLocalBinds@.
-- An annotation makes it a scheme, instantiated at every use exactly as a
-- declared top-level signature is, so there is one rule for annotations at both
-- levels and not two.
data Local
  = Mono Ty  -- ^ one type, shared by every use
  | Poly Ty  -- ^ a scheme: its 'TVar's are quantified, and each use gets a copy

-- | The type a use of this name has here.
useOf :: Local -> St -> (Ty, St)
useOf l st = case l of
  Mono t -> (t, st)
  Poly t -> case instantiate [t] st of
    (u : _, st1) -> (u, st1)
    ([],    st1) -> (t, st1)

-- | Walk a body, threading what each @Bind@ adds to scope.
--
-- **The positions are the written statements, not the instructions** (MS5 phase
-- 91): a caller walking a rule's own body passes 'writtenPositions' of it, and
-- one walking a lambda's or a block's body passes the enclosing statement's
-- position for every instruction — the lambda is what the reader sees on that
-- line, which is the choice 'Thena.Rules.validate' already made.
body :: SigEnv -> Rule -> Maybe Ty -> [(Name, Local)] -> [Int] -> St -> [Instr] -> St
body _   _ _   _   _ st []             = st
body env r res ctx ps st (instr : rest) =
  let si = InBody (ruleName r) (case ps of { p : _ -> p ; [] -> 0 })
      o  = case instr of { Bind _ _ x -> x; Do x -> x }
      (mres, st1) = operation env r res ctx si o st
      (ctx', st2) = case (instr, mres) of
        -- **An annotated local is checked here and kept as a scheme** (MS5
        -- phase 77): a fresh copy of the annotation is unified with what the op
        -- leaves, and 'generalEnough' then asks whether the copy\'s variables
        -- survived as variables — the same instantiate-then-verify a declared
        -- top-level signature gets, one level down.
        -- **An annotation only ever meets a plain name** —
        -- 'Thena.Rules.resolveBlock' pairs one with a @RawPWord@ binding and
        -- nothing else (MS5 phase 84), so the 'PVar' here is the whole of that
        -- restriction showing up in the type checker.
        (Bind (PVar n) (Just ann) _, Just t) ->
          let ((us, table), sA) = instantiateWith [ann] st1
              sB = case us of
                u : _ -> unify si u t sA
                []    -> sA
           in ((n, Poly ann) : ctx, generalEnough si table sB)
        (Bind (PVar n) (Just ann) _, Nothing) ->
          -- Annotated, but the op leaves nothing to annotate. The @Nothing@
          -- branch below already reports what is wrong; the annotation is kept
          -- so a later use is measured against what the author said.
          ((n, Poly ann) : ctx, bindsNothing st1)
        -- **A pattern types what it binds against what the op leaves** (MS5
        -- phase 84), which is 'patternCtx' — the very function phase 82 wrote
        -- for a parameter. A binding and a parameter ask the same question of a
        -- pattern, so they get the same answer from the same code.
        (Bind p Nothing _, Just t)  ->
          let (bs, s0) = patternCtx (const si) [p] [t] st1
           in (bs ++ ctx, s0)
        (Bind p Nothing _, Nothing) ->
          -- **A call is the case worth reporting.** For every other op
          -- 'Thena.Rules.validate' has already refused this
          -- ('Thena.Rules.BoundNonProducing'); a call passes that check because
          -- 'Thena.Instral.Ops.produces' cannot answer for one, and this pass can.
          let (t, s0)  = fresh (bindsNothing st1)
              (bs, s1) = patternCtx (const si) [p] [t] s0
           in (bs ++ ctx, s1)
        -- Unreachable: an annotation is paired only with a plain name.
        (Bind _ (Just _) _, _) -> (ctx, st1)
        (Do _, _)              -> (ctx, st1)

      -- **A call is the case worth reporting.** For every other op
      -- 'Thena.Rules.validate' has already refused this
      -- ('Thena.Rules.BoundNonProducing'); a call passes that check because
      -- 'Thena.Instral.Ops.produces' cannot answer for one, and this pass can.
      bindsNothing s = case o of
        Call nm as | notReturning (lookup (GlobalName nm, length as) env) ->
          oops (BindsNothing si (GlobalName nm)) s
        _ -> s
   in body env r res ctx' (drop 1 ps) st2 rest

-- | One op: check its operands, answer the type it leaves.
operation
  :: SigEnv -> Rule -> Maybe Ty -> [(Name, Local)] -> Site -> Op -> St
  -> (Maybe Ty, St)
operation env r res ctx si o st0 = case o of
  -- **A lambda's type is worked out here** (MS5 phase 68b) — the table cannot,
  -- because a lambda's parameters and result are whatever its body makes them.
  -- The body is walked in a scope of its own with a result variable of its own,
  -- exactly as a rule's is; it already ends in a @return@, which is what pins
  -- the result.
  Lambda ps b ->
    let (vs, st1)    = freshes (length ps) st0
        (rv, st2)    = fresh st1
        (bs, st3)    = patternCtx (InPattern (ruleName r)) ps vs st2
        st4          = body env r (Just rv) (bs ++ ctx) (repeat (siteIndex si)) st3 b
     in (Just (TFun vs rv), st4)

  -- **A local shadows a rule** — his ruling, 2026-09-12 — so a call whose name
  -- is bound here is an application of that value, and its type says so.
  Call nm as
    | Just l <- lookup nm ctx ->
        -- **Its own copy if it was annotated**, which is what an annotated
        -- local buys: a use here does not pin the local for every other use.
        let (t, st1)   = useOf l st0
            (ats, st2) = freshes (length as) st1
            (rv, st3)  = fresh st2
            st4        = unify si t (TFun ats rv) st3
         in (Just rv, foldl (\s (w, a) -> operandAgainst ctx si w a s) st4 (zip ats as))

  -- **A call is where the signature environment is read**, and the only place.
  Call nm as ->
    case lookup (GlobalName nm, length as) env of
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
     in (Nothing, body env r (Just v) ctx (repeat (siteIndex si)) st1 is)

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
operandAgainst :: [(Name, Local)] -> Site -> Ty -> Operand -> St -> St
operandAgainst ctx si want o st = case o of
  -- **Deferred, not decided here** — see 'stText'.
  Lit (VText _) -> st { stText = stText st ++ [(si, want)] }
  _             -> let (got, st') = operandType ctx si o st
                    in unify si want got st'

-- | …and its type when nothing constrains it.
operandType :: [(Name, Local)] -> Site -> Operand -> St -> (Ty, St)
operandType ctx si o st = case o of
  Ref n -> case lookup n ctx of
    Just l  -> useOf l st
    -- 'Thena.Rules.validate' has already refused an unbound name
    -- ('Thena.Rules.UnboundInRule'); a fresh variable keeps this pass total.
    Nothing -> fresh st
  -- **A written term's splices are checked where it sits** (MS5 phase 81).
  -- A hole stands where a term stands — his observation — so what it wants is
  -- known from the grammar position and not from a pass of its own: every
  -- splice in a @Raw@ must be a 'TCore'.
  Lit (VRaw raw) ->
    -- **The position decides the type** (MS5 phase 88). A term splice must be
    -- filled with a 'TCore' and a name splice with a 'TName', and the grammar
    -- has already sorted them: nothing is annotated and nothing is guessed.
    -- **Each occurrence is typed where it sits** (phase 90): a binding used
    -- in both kinds of position is asked both questions, and one of them fails.
    let hole s sp = case sp of
          TermSplice x -> operandAgainst ctx si TCore (Ref x) s
          NameSplice x -> operandAgainst ctx si TName (Ref x) s
        st1 = foldl hole st (splices raw)
     in valueType si (VRaw raw) st1
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
  VLevel _   -> (TLevel, st)
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
  -- **Cannot arise**: a closure is built by 'Thena.Instral.Ops.Lambda' and never
  -- written, so nothing puts one in a 'Thena.Instral.Ops.Lit'. Answered rather than left
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
