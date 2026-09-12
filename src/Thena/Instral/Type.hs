-- | @instral@'s types (MS5 phase 66b).
--
-- **The type language, and nothing that uses it.** This module declares what a
-- type /is/; the signature every op has is 'Thena.Ops.signatureOf', and
-- inference over rule bodies is phase 66c. Splitting them that way is his call,
-- 2026-09-12: a signature that disagrees with 'Thena.Ops.operandsOf' is a bug
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
  ) where

import Data.List (intercalate, nub)

-- | A type in @instral@.
--
-- **The abstract four are @Surface@, @Core@, @Development@ and @Name@** — his
-- list, 2026-09-11. @instral@ never looks inside any of them; they are handles
-- on things the machine owns.
--
-- 'TVar' is a variable in a /scheme/. The table in "Thena.Ops" numbers them
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
    -- name to a string is written down, with 'Thena.Ops.NameText'.
  | TInt                 -- ^ a whole number
  | TChar                -- ^ one character, written @'c'@
  | TBool                -- ^ @true@ or @false@
  | TSurface             -- ^ a focused surface term — 'Thena.Ops.VSurface'
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
    -- 'Thena.Ops.VTerm' from a development by /removing/ the case rather than
    -- standing an empty one beside it, and the same argument would have kept
    -- this constructor out; he decided the language's vocabulary is fixed here
    -- even where the signature table never mentions it. MS5's doctrine is
    -- completeness over minimality and this is an instance of it.
  | TList Ty             -- ^ @[a, b, c]@
  | TPair Ty Ty          -- ^ @(a, b)@
  | TOption Ty           -- ^ @some x@ and @none@
  | TVar Int             -- ^ a scheme variable
  deriving (Eq, Show)

-- | What an op takes and what it leaves.
--
-- **'sigResult' is 'Nothing' when the op produces nothing**, which is the whole
-- of 'Thena.Ops.produces' — and that function is derived from this one now
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
      _          -> []

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
      TSurface     -> "Surface"
      TCore        -> "Core"
      TDevelopment -> "Development"
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
  intercalate " -> " (map renderTy ps ++ [maybe "()" renderTy r])
