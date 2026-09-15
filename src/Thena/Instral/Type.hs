-- | @instral@'s types (MS5 phase 66b).
--
-- **The type language, and nothing that uses it.** This module declares what a
-- type /is/; the signature every op has is 'Thena.Instral.Ops.signatureOf', and
-- inference over rule bodies is phase 66c. Splitting them that way is his call,
-- 2026-09-12: a signature that disagrees with 'Thena.Instral.Ops.operandsOf' is a bug
-- this phase can catch on its own, before inference exists to hide it behind a
-- type error somewhere else.
--
-- **Hindley-Milner over a ground set, plus four abstract types** — his design,
-- @discussion\/the-five-languages.md@ §5.4. @instral@ owns its data (§5.3)
-- rather than computing with the prelude's, so the ground set is closed and
-- declared here rather than growing with what the user writes. §6.6 is where
-- that stops being true: an object language declared in Surface generates an
-- abstract type of its own, and his ruling is that the environment growing that
-- way /is what instral is for/.
module Thena.Instral.Type
  ( Ty (..)
  , Signature (..)
  , renderTy
  , renderSignature
  , typeVarsIn
  , fits
  ) where

import Data.List (intercalate, nub)

-- | A type in @instral@.
--
-- **The abstract four are @Surface@, @Core@, @Development@ and @Name@** — his
-- list, 2026-09-11. @instral@ never looks inside any of them; they are handles
-- on things the machine owns.
--
-- 'TVar' is a variable in a /scheme/. The table in "Thena.Instral.Ops" numbers them
-- from zero per signature and inference instantiates them fresh at each use;
-- nothing here does the instantiating.
data Ty
  = TString              -- ^ text, written @"…"@
  | TName
    -- ^ **a name, and it is NOT 'TString'** — his ruling, 2026-09-12, on §5.4's
    -- argument that more types is more disambiguating power. It catches @say h@
    -- where @h@ is a hole's name and @goto m@ where @m@ is a message.
    --
    -- **A string literal is accepted at either** (his, same day), so nothing
    -- about how anything is written changes. A /variable/ is not: going from a
    -- name to a string is written down, with 'Thena.Instral.Ops.NameText'.
  | TInt                 -- ^ a whole number
  | TChar                -- ^ one character, written @'c'@
  | TBool                -- ^ @true@ or @false@
  | TSurface             -- ^ a focused surface term — 'Thena.Instral.Ops.VSurface'
  | TCore
    -- ^ a core term.
    --
    -- **It covers a written @core\`…\`@ too, which is not yet resolved** — his
    -- ruling, 2026-09-12, asked directly. @resolve-core@ is therefore
    -- @Core -> Core@, and handing an unresolved term to something that wants a
    -- resolved one is a run-time failure exactly as it is today, not a type
    -- error. He took that knowingly, against a second type for the unresolved
    -- form: the vocabulary stays the four he named.
  | TDevelopment
    -- ^ a whole development.
    --
    -- **Nothing has this type yet, and it is here because he said so** —
    -- 2026-09-12, ruling on the question 66a raised. Phase 66a separated
    -- 'Thena.Instral.Ops.VTerm' from a development by /removing/ the case rather than
    -- standing an empty one beside it, and the same argument would have kept
    -- this constructor out; he decided the language's vocabulary is fixed here
    -- even where the signature table never mentions it. MS5's doctrine is
    -- completeness over minimality and this is an instance of it.
  | TList Ty             -- ^ @[a, b, c]@
  | TPair Ty Ty          -- ^ @(a, b)@
  | TOption Ty           -- ^ @some x@ and @none@
  | TLevel
    -- ^ **a universe level** (MS5 phase 89) — @Thena.Core.Level.Level@, which
    -- is an algebra (@LZero | LSuc | LMax | LVar@) and not a number.
    --
    -- **It is its own type and not 'TInt' for the reason the algebra exists**:
    -- a level a rule holds is usually a /meta/ the solver has not decided, and
    -- no numeral can be one. @fresh-level@ mints exactly that.
    --
    -- **@instral@ can make one two ways and compute with it in none**:
    -- @fresh-level@ and @level ‹n›@ build, @universe-at@ consumes. @LSuc@ and
    -- @LMax@ have no ops on purpose — those are the /algebra/, and
    -- "Thena.Core.Level"'s solver stays their only author until something asks
    -- (@ms5\/CLOSEOUT.md@ 40).
  | TObject String
    -- ^ **a declared object language** (MS5 phase 69) — @Tm@, opaque.
    --
    -- **Its tag is its only introduction form** (§6.6, his), so a value of this
    -- type is well formed by construction, and there is a one-way coercion to
    -- 'TSurface' because an object term /is/ a Surface term. @instral@ never
    -- looks inside one.
    --
    -- **This is where the type environment stops being closed** — §5.3's
    -- \"contained\" weakens from /closed/ to /extensible by declaration/, which
    -- he ruled is *\"exactly what instral is for\"*.
  | TFun [Ty] Ty
    -- ^ **the argument list is never empty** (MS5 phase 94): a lambda takes at
    -- least one parameter, and calling a local with none is refused before a
    -- type is built for it. @ms5\/CLOSEOUT.md@ 23 is why — a function of no
    -- arguments had a type nothing could write.
    -- ^ **a function value** (MS5 phase 68b) — what a lambda is.
    --
    -- **N-ary, not curried**, and written as an arrow chain: @a -> b -> c@ is a
    -- function of /two/ arguments. That is not a spelling accident — an
    -- @instral@ call is n-ary and dispatch is on arity
    -- ('Thena.Rules.clauses'), so a curried reading would promise partial
    -- application that nothing implements. It also matches 'Signature', which is
    -- a list of parameters and a result rather than a chain.
    --
    -- **Parentheses are what make one a value.** A signature's top-level chain
    -- is split into parameters and a result, so only a parenthesised arrow
    -- reaches here: @signature f : (a -> b) -> a -> b@ takes a function and a
    -- value.
  | TVar Int             -- ^ a scheme variable
  deriving (Eq, Show)

-- | What an op takes and what it leaves.
--
-- **'sigResult' is 'Nothing' when the op produces nothing**, which is the whole
-- of 'Thena.Instral.Ops.produces' — and that function is derived from this one now
-- rather than being written twice (his ruling, 2026-09-12). The gain is a real
-- check and not tidiness: @RulesTests@ already runs every op through
-- "Thena.Engine" and asserts a name appears in the environment exactly when
-- @produces@ says it should, so deriving points that existing cross-check at
-- this table's result column — an invariant maintained by different code from
-- the code that checks it, which is the standing lesson.
data Signature = Signature
  { sigParams :: [Ty]     -- ^ one per operand, in the order they are written
  , sigResult :: Maybe Ty -- ^ 'Nothing' if the op leaves nothing to bind
  }
  deriving (Eq, Show)

-- | Every scheme variable a type mentions, in first-seen order.
typeVarsIn :: Ty -> [Int]
typeVarsIn t = nub (go t)
  where
    go ty = case ty of
      TVar i     -> [i]
      TList a    -> go a
      TOption a  -> go a
      TPair a b  -> go a ++ go b
      TFun as r  -> concatMap go as ++ go r
      _          -> []

-- | Does a signature's type fit a type someone asked about (MS5 phase 71)?
--
-- **One-way, and the scheme's variables are what may move.** @:accepts Core@
-- should list a rule whose parameter is @a@, because such a rule does accept a
-- @Core@; it should not list one whose parameter is @Surface@. So a 'TVar' on
-- the /signature/ side matches anything, consistently — @a -> a@ fits
-- @Core -> Core@ and not @Core -> Surface@ — and a 'TVar' on the asked side
-- matches only itself.
--
-- **It is a display question and not unification**, which is why it lives here
-- and not in "Thena.Instral.Infer": nothing is solved and no state is threaded.
fits :: Ty -> Ty -> Bool
fits scheme asked = case go [] scheme asked of
  Just _  -> True
  Nothing -> False
  where
    go bs s a = case (s, a) of
      (TVar i, _) -> case lookup i bs of
        Just t  -> if t == a then Just bs else Nothing
        Nothing -> Just ((i, a) : bs)
      (TList x,   TList y)   -> go bs x y
      (TOption x, TOption y) -> go bs x y
      (TPair x y, TPair u v) -> go bs x u >>= \bs' -> go bs' y v
      (TFun xs r, TFun ys q)
        | length xs == length ys ->
            foldl (\acc (x, y) -> acc >>= \b -> go b x y) (Just bs) (zip xs ys)
              >>= \bs' -> go bs' r q
      _ | s == a    -> Just bs
        | otherwise -> Nothing

-- | A type, spelled as a rule author would write it.
--
-- @needsParens@ is the argument position of a one-parameter constructor, which
-- is the only place a type nests without a bracket of its own.
renderTy :: Ty -> String
renderTy = go False
  where
    go p ty = case ty of
      TString      -> "String"
      TName        -> "Name"
      TInt         -> "Int"
      TChar        -> "Char"
      TBool        -> "Bool"
      TLevel       -> "Level"
      TObject n    -> n
      TSurface     -> "Surface"
      TCore        -> "Core"
      TDevelopment -> "Development"
      TFun as r    -> wrap p (intercalate " -> " (map (go True) as ++ [go True r]))
      TList a      -> wrap p ("List " ++ go True a)
      TOption a    -> wrap p ("Option " ++ go True a)
      TPair a b    -> "(" ++ go False a ++ ", " ++ go False b ++ ")"
      TVar i       -> letterFor i

    wrap p s = if p then "(" ++ s ++ ")" else s

-- | @a@, @b@, … @z@, then @a1@ and on. Scheme variables are few.
letterFor :: Int -> String
letterFor i
  | i < 26    = [toEnum (fromEnum 'a' + i)]
  | otherwise = letterFor (i `mod` 26) ++ show (i `div` 26)

-- | A signature, as an arrow chain: @Name -> Core -> Core@.
--
-- An op that produces nothing ends in @()@ rather than stopping, so that the
-- absence is visible rather than being read as a missing word.
renderSignature :: Signature -> String
renderSignature (Signature ps r) =
  intercalate " -> " (map argument ps ++ [maybe "()" argument r])
  where
    -- **A function-typed parameter OR RESULT takes parentheses** (MS5 phase 73;
    -- the result half added 2026-09-12). Without them
    -- @(String -> String) -> String -> String@ prints as
    -- @String -> String -> String -> String@, which is a different signature —
    -- and the one thing a reader would take from the listing is its arity.
    --
    -- The result was still bare until the second date, so @String -> (String ->
    -- String)@ at arity one and @String -> String -> String@ at arity two
    -- printed the same text and @:accepts String@ listed both that way.
    argument t = case t of
      TFun _ _ -> "(" ++ renderTy t ++ ")"
      _        -> renderTy t
