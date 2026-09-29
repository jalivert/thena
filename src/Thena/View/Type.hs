-- | An @instral@ type, as a frontend sees it (MS7 phase 133,
-- @ms7\/CLOSEOUT.md@ 27).
--
-- **A view over "Thena.Instral.Type", the way "Thena.View.Instral" is a view
-- over a statement** — his ruling, 2026-09-29: /"I want it to be principled and
-- correct and that means instral types get views too."/ Phase 131 had given
-- 'Thena.View.Rules.RuleView' the rendered 'String' instead, knowingly, because
-- "Thena.Instral.Type" is not on @thena:view@'s list; this is the principled
-- version and that field is now a 'SignatureView'.
--
-- **Parentheses are in the tree, not in a precedence rule the frontend
-- re-derives.** 'AFenced' is the only place a parenthesis is ever drawn — the
-- same shape of answer as 'Thena.View.Core.ARegion', one type over, and for the
-- same reason: the alternative is every frontend carrying its own copy of
-- 'Thena.Instral.Type.renderTy''s nesting flag, which is grammar knowledge
-- living in a second place. A 'APair' draws its own parentheses and commas
-- because those are the pair's /notation/ and not a fence.
--
-- **The crossing is "Thena.View.TypeTests"**, which rebuilds
-- 'Thena.Instral.Type.renderSignature''s exact output from a 'SignatureView',
-- byte for byte, over every signature the shipped rule bases infer — so the two
-- cannot drift, which is phase 132's lesson applied here.
module Thena.View.Type
  ( TypeView (..)
  , SignatureView (..)
  , displayType
  , displaySignature
  ) where

import Thena.Instral.Type (Signature (..), Ty (..), letterFor)

-- | A type in @instral@ — "Thena.Instral.Type.Ty"'s own shape, plus 'AFenced'.
--
-- The ground constructors are the vocabulary he fixed on 2026-09-11 and
-- 2026-09-12; 'Thena.Instral.Type.Ty' says why each is there and this adds
-- nothing to that argument.
data TypeView
  = AString              -- ^ @String@
  | AName                -- ^ @Name@, and it is not 'AString'
  | AnInt                -- ^ @Int@
  | AChar                -- ^ @Char@
  | ABool                -- ^ @Bool@
  | ASurface             -- ^ @Surface@
  | ACore                -- ^ @Core@
  | ADevelopment         -- ^ @Development@
  | ALevel               -- ^ @Level@ — the algebra, not a number
  | AList TypeView       -- ^ @List a@
  | AnOption TypeView    -- ^ @Option a@
  | APair TypeView TypeView
    -- ^ @(a, b)@ — **it draws its own parentheses and its own comma**, which
    -- are the pair's notation. It is never wrapped in an 'AFenced'.
  | AFunction [TypeView] TypeView
    -- ^ @a -> b -> c@, n-ary and never curried
    -- ('Thena.Instral.Type.TFun' says why). The argument list is never empty.
  | ASchemeVar String
    -- ^ a scheme variable, **by the letter it is written with** rather than by
    -- the index it has in "Thena.Instral.Ops"' table. The numbering is per
    -- signature and is that table's business; the letter is what a reader sees,
    -- and 'Thena.Instral.Type.letterFor' is injective, so two slots share a
    -- letter exactly when they share a variable.
  | AFenced TypeView
    -- ^ **parentheses are drawn here, and nowhere else.** That is the whole
    -- rule. It wraps whatever would otherwise read as a wider type than it is —
    -- an 'AFunction', 'AList' or 'AnOption' standing inside another type's
    -- argument, or an 'AFunction' standing as a signature's parameter or
    -- result, which is the case that makes an arity read right.
  deriving (Eq, Show)

-- | What a rule or an op takes, and what it leaves.
--
-- **Drawn as an arrow chain**: the parameters and then the result, joined by
-- @->@, with @()@ where there is no result — the absence written out rather
-- than left to read as a missing word, which is
-- 'Thena.Instral.Type.renderSignature''s own choice and is kept here.
data SignatureView = SignatureView
  { signatureViewParams :: [TypeView] -- ^ one per operand, in written order
  , signatureViewResult :: Maybe TypeView
    -- ^ 'Nothing' if it leaves nothing to bind — draw @()@.
  }
  deriving (Eq, Show)

-- | A type on its own, at the top level, where nothing needs fencing.
displayType :: Ty -> TypeView
displayType = at False

-- | A signature, with its parameters and result fenced as an arrow chain needs.
--
-- **Only an 'AFunction' is fenced here**, and that is not the same rule as
-- 'at''s. A parameter of @List a@ reads unambiguously in a chain, so
-- 'Thena.Instral.Type.renderSignature' leaves it bare; a parameter that is
-- itself a function does not, and @(String -> String) -> String@ collapsing to
-- @String -> String -> String@ would change the arity, which is the one thing a
-- reader takes from a listing.
displaySignature :: Signature -> SignatureView
displaySignature (Signature ps r) =
  SignatureView (map parameter ps) (fmap parameter r)
  where
    parameter t = case t of
      TFun _ _ -> AFenced (at False t)
      _        -> at False t

-- | 'Thena.Instral.Type.renderTy''s own nesting flag, kept in step with it.
--
-- @True@ means "this type stands inside another type's argument", which is
-- where a function, a list and an option each have to be fenced to read as one
-- thing. A pair never is, and a ground type never can be.
at :: Bool -> Ty -> TypeView
at nested ty = case ty of
  TString      -> AString
  TName        -> AName
  TInt         -> AnInt
  TChar        -> AChar
  TBool        -> ABool
  TSurface     -> ASurface
  TCore        -> ACore
  TDevelopment -> ADevelopment
  TLevel       -> ALevel
  TFun as r    -> fence (AFunction (map (at True) as) (at True r))
  TList a      -> fence (AList (at True a))
  TOption a    -> fence (AnOption (at True a))
  TPair a b    -> APair (at False a) (at False b)
  TVar i       -> ASchemeVar (letterFor i)
  where
    fence v = if nested then AFenced v else v
