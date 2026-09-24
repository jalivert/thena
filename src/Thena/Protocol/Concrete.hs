{-# OPTIONS_GHC -Wno-orphans #-}

-- | The as-written trees, as JSON (phase 112a).
--
-- **These are the project's storage format.** His decision of 2026-09-24: a
-- module is stored as it was written, not resolved, so that a tactic which
-- becomes a rule keeps working under its own name and so that JSON and text are
-- two spellings of one artifact rather than two artifacts. See
-- @discussion\/editor-protocol.md@ §4 A2 for the argument, and @ms7\/MS7.md@ for
-- why that makes loading one pipeline with two front doors.
--
-- **Mechanical, and deliberately so.** Every instance is one constructor per
-- line in the shape "Thena.Protocol.Codec" fixes. There is no judgement in this
-- file; the judgement is in the two modules it sits on.
--
-- **The instances are orphans, and the warning is switched off for this module
-- alone.** This is the one place in the project where @-Wall@ is not simply
-- clean, so it is worth stating what was weighed:
--
-- * putting each instance beside its type would make "Thena.Surface.Concrete"
--   and its neighbours depend on the protocol, which inverts the module order
--   (§2.5) — the syntax sits below the protocol, not above it;
-- * dropping the two classes for plain functions would remove the orphans
--   entirely, at the cost of naming a codec for every field by hand instead of
--   letting the type pick it. That is the alternative with no wart at all, and
--   it is the one to reach for if this ever needs revisiting.
--
-- Every instance is here, in one file, so there is nowhere else to look for
-- one — which is the practical risk orphans carry, and it is answered by
-- keeping them together rather than by the warning.
module Thena.Protocol.Concrete () where

import Thena.Protocol.Codec (FromJson (..), ToJson (..), noSuchCase, tagged, untagged)

import qualified Thena.Core.Term as T
import qualified Thena.Driver as D
import qualified Thena.Instral.Concrete as I
import qualified Thena.Language.Reader as R
import qualified Thena.Surface.Concrete as U
import qualified Thena.Syntax.Concrete as S
import qualified Thena.Syntax.Lexer as L

instance ToJson T.Literal where
  toJson x = case x of
    (T.LString a0) -> tagged "LString" [toJson a0]
    (T.LChar a0) -> tagged "LChar" [toJson a0]
    (T.LInt a0) -> tagged "LInt" [toJson a0]
    (T.LRegex a0) -> tagged "LRegex" [toJson a0]

instance FromJson T.Literal where
  fromJson v = untagged "Literal" v >>= \case
    ("LString", [a0]) -> T.LString <$> fromJson a0
    ("LChar", [a0]) -> T.LChar <$> fromJson a0
    ("LInt", [a0]) -> T.LInt <$> fromJson a0
    ("LRegex", [a0]) -> T.LRegex <$> fromJson a0
    (t, as) -> noSuchCase "Literal" t as

instance ToJson L.BlockKind where
  toJson x = case x of
    L.LanguageBlock -> tagged "LanguageBlock" []
    L.ContextBlock -> tagged "ContextBlock" []
    L.JudgmentBlock -> tagged "JudgmentBlock" []

instance FromJson L.BlockKind where
  fromJson v = untagged "BlockKind" v >>= \case
    ("LanguageBlock", []) -> Right L.LanguageBlock
    ("ContextBlock", []) -> Right L.ContextBlock
    ("JudgmentBlock", []) -> Right L.JudgmentBlock
    (t, as) -> noSuchCase "BlockKind" t as

instance ToJson S.Raw where
  toJson x = case x of
    (S.RawName a0) -> tagged "RawName" [toJson a0]
    (S.RawUniverse a0) -> tagged "RawUniverse" [toJson a0]
    (S.RawPrimitive a0) -> tagged "RawPrimitive" [toJson a0]
    S.RawUniverseOpen -> tagged "RawUniverseOpen" []
    (S.RawAt a0 a1) -> tagged "RawAt" [toJson a0, toJson a1]
    (S.RawLam a0 a1) -> tagged "RawLam" [toJson a0, toJson a1]
    (S.RawPi a0 a1) -> tagged "RawPi" [toJson a0, toJson a1]
    (S.RawArrow a0 a1) -> tagged "RawArrow" [toJson a0, toJson a1]
    (S.RawApp a0 a1) -> tagged "RawApp" [toJson a0, toJson a1]
    (S.RawLet a0 a1 a2 a3) -> tagged "RawLet" [toJson a0, toJson a1, toJson a2, toJson a3]
    (S.RawClaim a0 a1 a2) -> tagged "RawClaim" [toJson a0, toJson a1, toJson a2]
    (S.RawGuess a0 a1 a2 a3) -> tagged "RawGuess" [toJson a0, toJson a1, toJson a2, toJson a3]
    (S.RawPending a0 a1) -> tagged "RawPending" [toJson a0, toJson a1]
    (S.RawQuote a0) -> tagged "RawQuote" [toJson a0]
    (S.RawSplice a0) -> tagged "RawSplice" [toJson a0]
    (S.RawObject a0 a1 a2) -> tagged "RawObject" [toJson a0, toJson a1, toJson a2]
    (S.RawElim a0 a1 a2 a3 a4 a5 a6) -> tagged "RawElim" [toJson a0, toJson a1, toJson a2, toJson a3, toJson a4, toJson a5, toJson a6]

instance FromJson S.Raw where
  fromJson v = untagged "Raw" v >>= \case
    ("RawName", [a0]) -> S.RawName <$> fromJson a0
    ("RawUniverse", [a0]) -> S.RawUniverse <$> fromJson a0
    ("RawPrimitive", [a0]) -> S.RawPrimitive <$> fromJson a0
    ("RawUniverseOpen", []) -> Right S.RawUniverseOpen
    ("RawAt", [a0, a1]) -> S.RawAt <$> fromJson a0 <*> fromJson a1
    ("RawLam", [a0, a1]) -> S.RawLam <$> fromJson a0 <*> fromJson a1
    ("RawPi", [a0, a1]) -> S.RawPi <$> fromJson a0 <*> fromJson a1
    ("RawArrow", [a0, a1]) -> S.RawArrow <$> fromJson a0 <*> fromJson a1
    ("RawApp", [a0, a1]) -> S.RawApp <$> fromJson a0 <*> fromJson a1
    ("RawLet", [a0, a1, a2, a3]) -> S.RawLet <$> fromJson a0 <*> fromJson a1 <*> fromJson a2 <*> fromJson a3
    ("RawClaim", [a0, a1, a2]) -> S.RawClaim <$> fromJson a0 <*> fromJson a1 <*> fromJson a2
    ("RawGuess", [a0, a1, a2, a3]) -> S.RawGuess <$> fromJson a0 <*> fromJson a1 <*> fromJson a2 <*> fromJson a3
    ("RawPending", [a0, a1]) -> S.RawPending <$> fromJson a0 <*> fromJson a1
    ("RawQuote", [a0]) -> S.RawQuote <$> fromJson a0
    ("RawSplice", [a0]) -> S.RawSplice <$> fromJson a0
    ("RawObject", [a0, a1, a2]) -> S.RawObject <$> fromJson a0 <*> fromJson a1 <*> fromJson a2
    ("RawElim", [a0, a1, a2, a3, a4, a5, a6]) -> S.RawElim <$> fromJson a0 <*> fromJson a1 <*> fromJson a2 <*> fromJson a3 <*> fromJson a4 <*> fromJson a5 <*> fromJson a6
    (t, as) -> noSuchCase "Raw" t as

instance ToJson S.RawPiece where
  toJson x = case x of
    (S.RawChunk a0) -> tagged "RawChunk" [toJson a0]
    (S.RawSpliced a0) -> tagged "RawSpliced" [toJson a0]

instance FromJson S.RawPiece where
  fromJson v = untagged "RawPiece" v >>= \case
    ("RawChunk", [a0]) -> S.RawChunk <$> fromJson a0
    ("RawSpliced", [a0]) -> S.RawSpliced <$> fromJson a0
    (t, as) -> noSuchCase "RawPiece" t as

instance ToJson S.RawIdent where
  toJson x = case x of
    (S.RawWord a0) -> tagged "RawWord" [toJson a0]
    (S.RawIdentSplice a0) -> tagged "RawIdentSplice" [toJson a0]

instance FromJson S.RawIdent where
  fromJson v = untagged "RawIdent" v >>= \case
    ("RawWord", [a0]) -> S.RawWord <$> fromJson a0
    ("RawIdentSplice", [a0]) -> S.RawIdentSplice <$> fromJson a0
    (t, as) -> noSuchCase "RawIdent" t as

instance ToJson S.RawBinder where
  toJson x = case x of
    (S.RawBinder a0 a1) -> tagged "RawBinder" [toJson a0, toJson a1]

instance FromJson S.RawBinder where
  fromJson v = untagged "RawBinder" v >>= \case
    ("RawBinder", [a0, a1]) -> S.RawBinder <$> fromJson a0 <*> fromJson a1
    (t, as) -> noSuchCase "RawBinder" t as

instance ToJson S.RawConstraint where
  toJson x = case x of
    (S.RawConstraint a0 a1 a2 a3) -> tagged "RawConstraint" [toJson a0, toJson a1, toJson a2, toJson a3]

instance FromJson S.RawConstraint where
  fromJson v = untagged "RawConstraint" v >>= \case
    ("RawConstraint", [a0, a1, a2, a3]) -> S.RawConstraint <$> fromJson a0 <*> fromJson a1 <*> fromJson a2 <*> fromJson a3
    (t, as) -> noSuchCase "RawConstraint" t as

instance ToJson R.Block where
  toJson x = case x of
    (R.Block a0 a1 a2 a3 a4) -> tagged "Block" [toJson a0, toJson a1, toJson a2, toJson a3, toJson a4]

instance FromJson R.Block where
  fromJson v = untagged "ReaderBlock" v >>= \case
    ("Block", [a0, a1, a2, a3, a4]) -> R.Block <$> fromJson a0 <*> fromJson a1 <*> fromJson a2 <*> fromJson a3 <*> fromJson a4
    (t, as) -> noSuchCase "ReaderBlock" t as

instance ToJson R.RawRule where
  toJson x = case x of
    (R.RawRule a0 a1 a2 a3 a4) -> tagged "RawRule" [toJson a0, toJson a1, toJson a2, toJson a3, toJson a4]

instance FromJson R.RawRule where
  fromJson v = untagged "ReaderRule" v >>= \case
    ("RawRule", [a0, a1, a2, a3, a4]) -> R.RawRule <$> fromJson a0 <*> fromJson a1 <*> fromJson a2 <*> fromJson a3 <*> fromJson a4
    (t, as) -> noSuchCase "ReaderRule" t as

instance ToJson R.Production where
  toJson x = case x of
    (R.Production a0 a1 a2 a3) -> tagged "Production" [toJson a0, toJson a1, toJson a2, toJson a3]

instance FromJson R.Production where
  fromJson v = untagged "Production" v >>= \case
    ("Production", [a0, a1, a2, a3]) -> R.Production <$> fromJson a0 <*> fromJson a1 <*> fromJson a2 <*> fromJson a3
    (t, as) -> noSuchCase "Production" t as

instance ToJson R.Metadata where
  toJson x = case x of
    (R.AsOccurrence a0) -> tagged "AsOccurrence" [toJson a0]
    (R.AsBinders a0) -> tagged "AsBinders" [toJson a0]

instance FromJson R.Metadata where
  fromJson v = untagged "Metadata" v >>= \case
    ("AsOccurrence", [a0]) -> R.AsOccurrence <$> fromJson a0
    ("AsBinders", [a0]) -> R.AsBinders <$> fromJson a0
    (t, as) -> noSuchCase "Metadata" t as

instance ToJson R.RawItem where
  toJson x = case x of
    (R.Word a0) -> tagged "Word" [toJson a0]
    (R.Binding a0 a1) -> tagged "Binding" [toJson a0, toJson a1]

instance FromJson R.RawItem where
  fromJson v = untagged "RawItem" v >>= \case
    ("Word", [a0]) -> R.Word <$> fromJson a0
    ("Binding", [a0, a1]) -> R.Binding <$> fromJson a0 <*> fromJson a1
    (t, as) -> noSuchCase "RawItem" t as

instance ToJson I.RawRule where
  toJson x = case x of
    (I.RawRule a0 a1 a2 a3) -> tagged "RawRule" [toJson a0, toJson a1, toJson a2, toJson a3]

instance FromJson I.RawRule where
  fromJson v = untagged "InstralRule" v >>= \case
    ("RawRule", [a0, a1, a2, a3]) -> I.RawRule <$> fromJson a0 <*> fromJson a1 <*> fromJson a2 <*> fromJson a3
    (t, as) -> noSuchCase "InstralRule" t as

instance ToJson I.RawPattern where
  toJson x = case x of
    (I.RawPWord a0) -> tagged "RawPWord" [toJson a0]
    (I.RawPApp a0 a1) -> tagged "RawPApp" [toJson a0, toJson a1]
    (I.RawPInt a0) -> tagged "RawPInt" [toJson a0]
    (I.RawPChar a0) -> tagged "RawPChar" [toJson a0]
    (I.RawPText a0) -> tagged "RawPText" [toJson a0]
    (I.RawPList a0 a1) -> tagged "RawPList" [toJson a0, toJson a1]
    (I.RawPPair a0 a1) -> tagged "RawPPair" [toJson a0, toJson a1]
    (I.RawPObject a0 a1 a2) -> tagged "RawPObject" [toJson a0, toJson a1, toJson a2]

instance FromJson I.RawPattern where
  fromJson v = untagged "RawPattern" v >>= \case
    ("RawPWord", [a0]) -> I.RawPWord <$> fromJson a0
    ("RawPApp", [a0, a1]) -> I.RawPApp <$> fromJson a0 <*> fromJson a1
    ("RawPInt", [a0]) -> I.RawPInt <$> fromJson a0
    ("RawPChar", [a0]) -> I.RawPChar <$> fromJson a0
    ("RawPText", [a0]) -> I.RawPText <$> fromJson a0
    ("RawPList", [a0, a1]) -> I.RawPList <$> fromJson a0 <*> fromJson a1
    ("RawPPair", [a0, a1]) -> I.RawPPair <$> fromJson a0 <*> fromJson a1
    ("RawPObject", [a0, a1, a2]) -> I.RawPObject <$> fromJson a0 <*> fromJson a1 <*> fromJson a2
    (t, as) -> noSuchCase "RawPattern" t as

instance ToJson I.RawDecl where
  toJson x = case x of
    (I.DeclRule a0) -> tagged "DeclRule" [toJson a0]
    (I.DeclSignature a0) -> tagged "DeclSignature" [toJson a0]
    (I.DeclFunction a0) -> tagged "DeclFunction" [toJson a0]

instance FromJson I.RawDecl where
  fromJson v = untagged "RawDecl" v >>= \case
    ("DeclRule", [a0]) -> I.DeclRule <$> fromJson a0
    ("DeclSignature", [a0]) -> I.DeclSignature <$> fromJson a0
    ("DeclFunction", [a0]) -> I.DeclFunction <$> fromJson a0
    (t, as) -> noSuchCase "RawDecl" t as

instance ToJson I.RawFunction where
  toJson x = case x of
    (I.RawFunction a0 a1 a2) -> tagged "RawFunction" [toJson a0, toJson a1, toJson a2]

instance FromJson I.RawFunction where
  fromJson v = untagged "RawFunction" v >>= \case
    ("RawFunction", [a0, a1, a2]) -> I.RawFunction <$> fromJson a0 <*> fromJson a1 <*> fromJson a2
    (t, as) -> noSuchCase "RawFunction" t as

instance ToJson I.RawRhs where
  toJson x = case x of
    (I.RhsOp a0) -> tagged "RhsOp" [toJson a0]
    (I.RhsValue a0) -> tagged "RhsValue" [toJson a0]

instance FromJson I.RawRhs where
  fromJson v = untagged "RawRhs" v >>= \case
    ("RhsOp", [a0]) -> I.RhsOp <$> fromJson a0
    ("RhsValue", [a0]) -> I.RhsValue <$> fromJson a0
    (t, as) -> noSuchCase "RawRhs" t as

instance ToJson I.RawBody where
  toJson x = case x of
    (I.BodyRhs a0) -> tagged "BodyRhs" [toJson a0]
    (I.BodyBlock a0) -> tagged "BodyBlock" [toJson a0]

instance FromJson I.RawBody where
  fromJson v = untagged "RawBody" v >>= \case
    ("BodyRhs", [a0]) -> I.BodyRhs <$> fromJson a0
    ("BodyBlock", [a0]) -> I.BodyBlock <$> fromJson a0
    (t, as) -> noSuchCase "RawBody" t as

instance ToJson I.RawSignature where
  toJson x = case x of
    (I.RawSignature a0 a1) -> tagged "RawSignature" [toJson a0, toJson a1]

instance FromJson I.RawSignature where
  fromJson v = untagged "RawSignature" v >>= \case
    ("RawSignature", [a0, a1]) -> I.RawSignature <$> fromJson a0 <*> fromJson a1
    (t, as) -> noSuchCase "RawSignature" t as

instance ToJson I.RawTy where
  toJson x = case x of
    (I.RawTyCon a0 a1) -> tagged "RawTyCon" [toJson a0, toJson a1]
    (I.RawTyVar a0) -> tagged "RawTyVar" [toJson a0]
    (I.RawTyPair a0 a1) -> tagged "RawTyPair" [toJson a0, toJson a1]
    I.RawTyUnit -> tagged "RawTyUnit" []
    (I.RawTyArrow a0 a1) -> tagged "RawTyArrow" [toJson a0, toJson a1]
    (I.RawTyGroup a0) -> tagged "RawTyGroup" [toJson a0]

instance FromJson I.RawTy where
  fromJson v = untagged "RawTy" v >>= \case
    ("RawTyCon", [a0, a1]) -> I.RawTyCon <$> fromJson a0 <*> fromJson a1
    ("RawTyVar", [a0]) -> I.RawTyVar <$> fromJson a0
    ("RawTyPair", [a0, a1]) -> I.RawTyPair <$> fromJson a0 <*> fromJson a1
    ("RawTyUnit", []) -> Right I.RawTyUnit
    ("RawTyArrow", [a0, a1]) -> I.RawTyArrow <$> fromJson a0 <*> fromJson a1
    ("RawTyGroup", [a0]) -> I.RawTyGroup <$> fromJson a0
    (t, as) -> noSuchCase "RawTy" t as

instance ToJson I.RawInstr where
  toJson x = case x of
    (I.RawBind a0 a1) -> tagged "RawBind" [toJson a0, toJson a1]
    (I.RawDo a0) -> tagged "RawDo" [toJson a0]
    (I.RawAnnot a0 a1) -> tagged "RawAnnot" [toJson a0, toJson a1]

instance FromJson I.RawInstr where
  fromJson v = untagged "RawInstr" v >>= \case
    ("RawBind", [a0, a1]) -> I.RawBind <$> fromJson a0 <*> fromJson a1
    ("RawDo", [a0]) -> I.RawDo <$> fromJson a0
    ("RawAnnot", [a0, a1]) -> I.RawAnnot <$> fromJson a0 <*> fromJson a1
    (t, as) -> noSuchCase "RawInstr" t as

instance ToJson I.RawOp where
  toJson x = case x of
    (I.RawOp a0 a1) -> tagged "RawOp" [toJson a0, toJson a1]

instance FromJson I.RawOp where
  fromJson v = untagged "RawOp" v >>= \case
    ("RawOp", [a0, a1]) -> I.RawOp <$> fromJson a0 <*> fromJson a1
    (t, as) -> noSuchCase "RawOp" t as

instance ToJson I.RawTest where
  toJson x = case x of
    (I.RawTest a0 a1) -> tagged "RawTest" [toJson a0, toJson a1]

instance FromJson I.RawTest where
  fromJson v = untagged "RawTest" v >>= \case
    ("RawTest", [a0, a1]) -> I.RawTest <$> fromJson a0 <*> fromJson a1
    (t, as) -> noSuchCase "RawTest" t as

instance ToJson I.RawOperand where
  toJson x = case x of
    (I.RawQuoted a0) -> tagged "RawQuoted" [toJson a0]
    (I.RawRegion a0 a1 a2) -> tagged "RawRegion" [toJson a0, toJson a1, toJson a2]
    (I.RawNested a0 a1) -> tagged "RawNested" [toJson a0, toJson a1]
    (I.RawLambda a0 a1) -> tagged "RawLambda" [toJson a0, toJson a1]
    (I.RawRef a0) -> tagged "RawRef" [toJson a0]
    (I.RawPos a0) -> tagged "RawPos" [toJson a0]
    (I.RawText a0) -> tagged "RawText" [toJson a0]
    (I.RawChar a0) -> tagged "RawChar" [toJson a0]
    (I.RawList a0) -> tagged "RawList" [toJson a0]
    (I.RawPairOf a0 a1) -> tagged "RawPairOf" [toJson a0, toJson a1]

instance FromJson I.RawOperand where
  fromJson v = untagged "RawOperand" v >>= \case
    ("RawQuoted", [a0]) -> I.RawQuoted <$> fromJson a0
    ("RawRegion", [a0, a1, a2]) -> I.RawRegion <$> fromJson a0 <*> fromJson a1 <*> fromJson a2
    ("RawNested", [a0, a1]) -> I.RawNested <$> fromJson a0 <*> fromJson a1
    ("RawLambda", [a0, a1]) -> I.RawLambda <$> fromJson a0 <*> fromJson a1
    ("RawRef", [a0]) -> I.RawRef <$> fromJson a0
    ("RawPos", [a0]) -> I.RawPos <$> fromJson a0
    ("RawText", [a0]) -> I.RawText <$> fromJson a0
    ("RawChar", [a0]) -> I.RawChar <$> fromJson a0
    ("RawList", [a0]) -> I.RawList <$> fromJson a0
    ("RawPairOf", [a0, a1]) -> I.RawPairOf <$> fromJson a0 <*> fromJson a1
    (t, as) -> noSuchCase "RawOperand" t as

instance ToJson U.Plicity where
  toJson x = case x of
    U.Explicit -> tagged "Explicit" []
    U.Implicit -> tagged "Implicit" []

instance FromJson U.Plicity where
  fromJson v = untagged "Plicity" v >>= \case
    ("Explicit", []) -> Right U.Explicit
    ("Implicit", []) -> Right U.Implicit
    (t, as) -> noSuchCase "Plicity" t as

instance ToJson U.Surface where
  toJson x = case x of
    (U.SurfaceName a0) -> tagged "SurfaceName" [toJson a0]
    (U.SurfaceUniverse a0) -> tagged "SurfaceUniverse" [toJson a0]
    (U.SurfaceLiteral a0) -> tagged "SurfaceLiteral" [toJson a0]
    U.SurfaceUniverseOpen -> tagged "SurfaceUniverseOpen" []
    U.SurfacePlaceholder -> tagged "SurfacePlaceholder" []
    (U.SurfaceHole a0) -> tagged "SurfaceHole" [toJson a0]
    (U.SurfaceObject a0 a1 a2) -> tagged "SurfaceObject" [toJson a0, toJson a1, toJson a2]
    (U.SurfaceApp a0 a1) -> tagged "SurfaceApp" [toJson a0, toJson a1]
    (U.SurfaceLam a0 a1) -> tagged "SurfaceLam" [toJson a0, toJson a1]
    (U.SurfacePi a0 a1) -> tagged "SurfacePi" [toJson a0, toJson a1]
    (U.SurfaceArrow a0 a1) -> tagged "SurfaceArrow" [toJson a0, toJson a1]
    (U.SurfaceLet a0 a1 a2 a3) -> tagged "SurfaceLet" [toJson a0, toJson a1, toJson a2, toJson a3]
    (U.SurfaceAnnot a0 a1) -> tagged "SurfaceAnnot" [toJson a0, toJson a1]
    (U.SurfaceDo a0) -> tagged "SurfaceDo" [toJson a0]
    (U.SurfaceElim a0 a1 a2 a3 a4 a5) -> tagged "SurfaceElim" [toJson a0, toJson a1, toJson a2, toJson a3, toJson a4, toJson a5]

instance FromJson U.Surface where
  fromJson v = untagged "Surface" v >>= \case
    ("SurfaceName", [a0]) -> U.SurfaceName <$> fromJson a0
    ("SurfaceUniverse", [a0]) -> U.SurfaceUniverse <$> fromJson a0
    ("SurfaceLiteral", [a0]) -> U.SurfaceLiteral <$> fromJson a0
    ("SurfaceUniverseOpen", []) -> Right U.SurfaceUniverseOpen
    ("SurfacePlaceholder", []) -> Right U.SurfacePlaceholder
    ("SurfaceHole", [a0]) -> U.SurfaceHole <$> fromJson a0
    ("SurfaceObject", [a0, a1, a2]) -> U.SurfaceObject <$> fromJson a0 <*> fromJson a1 <*> fromJson a2
    ("SurfaceApp", [a0, a1]) -> U.SurfaceApp <$> fromJson a0 <*> fromJson a1
    ("SurfaceLam", [a0, a1]) -> U.SurfaceLam <$> fromJson a0 <*> fromJson a1
    ("SurfacePi", [a0, a1]) -> U.SurfacePi <$> fromJson a0 <*> fromJson a1
    ("SurfaceArrow", [a0, a1]) -> U.SurfaceArrow <$> fromJson a0 <*> fromJson a1
    ("SurfaceLet", [a0, a1, a2, a3]) -> U.SurfaceLet <$> fromJson a0 <*> fromJson a1 <*> fromJson a2 <*> fromJson a3
    ("SurfaceAnnot", [a0, a1]) -> U.SurfaceAnnot <$> fromJson a0 <*> fromJson a1
    ("SurfaceDo", [a0]) -> U.SurfaceDo <$> fromJson a0
    ("SurfaceElim", [a0, a1, a2, a3, a4, a5]) -> U.SurfaceElim <$> fromJson a0 <*> fromJson a1 <*> fromJson a2 <*> fromJson a3 <*> fromJson a4 <*> fromJson a5
    (t, as) -> noSuchCase "Surface" t as

instance ToJson U.ObjectPiece where
  toJson x = case x of
    (U.ObjectText a0) -> tagged "ObjectText" [toJson a0]
    (U.ObjectSplice a0) -> tagged "ObjectSplice" [toJson a0]

instance FromJson U.ObjectPiece where
  fromJson v = untagged "ObjectPiece" v >>= \case
    ("ObjectText", [a0]) -> U.ObjectText <$> fromJson a0
    ("ObjectSplice", [a0]) -> U.ObjectSplice <$> fromJson a0
    (t, as) -> noSuchCase "ObjectPiece" t as

instance ToJson U.SurfaceArg where
  toJson x = case x of
    (U.SurfaceArg a0 a1) -> tagged "SurfaceArg" [toJson a0, toJson a1]

instance FromJson U.SurfaceArg where
  fromJson v = untagged "SurfaceArg" v >>= \case
    ("SurfaceArg", [a0, a1]) -> U.SurfaceArg <$> fromJson a0 <*> fromJson a1
    (t, as) -> noSuchCase "SurfaceArg" t as

instance ToJson U.SurfaceBinder where
  toJson x = case x of
    (U.SurfaceBinder a0 a1 a2) -> tagged "SurfaceBinder" [toJson a0, toJson a1, toJson a2]

instance FromJson U.SurfaceBinder where
  fromJson v = untagged "SurfaceBinder" v >>= \case
    ("SurfaceBinder", [a0, a1, a2]) -> U.SurfaceBinder <$> fromJson a0 <*> fromJson a1 <*> fromJson a2
    (t, as) -> noSuchCase "SurfaceBinder" t as

instance ToJson U.SurfaceData where
  toJson x = case x of
    (U.SurfaceData a0 a1 a2 a3) -> tagged "SurfaceData" [toJson a0, toJson a1, toJson a2, toJson a3]

instance FromJson U.SurfaceData where
  fromJson v = untagged "SurfaceData" v >>= \case
    ("SurfaceData", [a0, a1, a2, a3]) -> U.SurfaceData <$> fromJson a0 <*> fromJson a1 <*> fromJson a2 <*> fromJson a3
    (t, as) -> noSuchCase "SurfaceData" t as

instance ToJson U.SurfaceConstructor where
  toJson x = case x of
    (U.SurfaceConstructor a0 a1) -> tagged "SurfaceConstructor" [toJson a0, toJson a1]

instance FromJson U.SurfaceConstructor where
  fromJson v = untagged "SurfaceConstructor" v >>= \case
    ("SurfaceConstructor", [a0, a1]) -> U.SurfaceConstructor <$> fromJson a0 <*> fromJson a1
    (t, as) -> noSuchCase "SurfaceConstructor" t as

instance ToJson U.SurfaceDecl where
  toJson x = case x of
    (U.SurfaceSignature a0 a1) -> tagged "SurfaceSignature" [toJson a0, toJson a1]
    (U.SurfaceEquation a0 a1) -> tagged "SurfaceEquation" [toJson a0, toJson a1]
    (U.SurfaceDatatype a0) -> tagged "SurfaceDatatype" [toJson a0]
    (U.SurfaceGrammar a0 a1 a2) -> tagged "SurfaceGrammar" [toJson a0, toJson a1, toJson a2]
    (U.SurfaceBlock a0) -> tagged "SurfaceBlock" [toJson a0]

instance FromJson U.SurfaceDecl where
  fromJson v = untagged "SurfaceDecl" v >>= \case
    ("SurfaceSignature", [a0, a1]) -> U.SurfaceSignature <$> fromJson a0 <*> fromJson a1
    ("SurfaceEquation", [a0, a1]) -> U.SurfaceEquation <$> fromJson a0 <*> fromJson a1
    ("SurfaceDatatype", [a0]) -> U.SurfaceDatatype <$> fromJson a0
    ("SurfaceGrammar", [a0, a1, a2]) -> U.SurfaceGrammar <$> fromJson a0 <*> fromJson a1 <*> fromJson a2
    ("SurfaceBlock", [a0]) -> U.SurfaceBlock <$> fromJson a0
    (t, as) -> noSuchCase "SurfaceDecl" t as

instance ToJson U.SurfaceModule where
  toJson x = case x of
    (U.SurfaceModule a0 a1) -> tagged "SurfaceModule" [toJson a0, toJson a1]

instance FromJson U.SurfaceModule where
  fromJson v = untagged "SurfaceModule" v >>= \case
    ("SurfaceModule", [a0, a1]) -> U.SurfaceModule <$> fromJson a0 <*> fromJson a1
    (t, as) -> noSuchCase "SurfaceModule" t as

instance ToJson D.Item where
  toJson x = case x of
    (D.ItemData a0) -> tagged "ItemData" [toJson a0]
    (D.ItemTheorem a0 a1 a2) -> tagged "ItemTheorem" [toJson a0, toJson a1, toJson a2]
    (D.ItemBlock a0) -> tagged "ItemBlock" [toJson a0]
    (D.ItemGrammar a0) -> tagged "ItemGrammar" [toJson a0]

instance FromJson D.Item where
  fromJson v = untagged "Item" v >>= \case
    ("ItemData", [a0]) -> D.ItemData <$> fromJson a0
    ("ItemTheorem", [a0, a1, a2]) -> D.ItemTheorem <$> fromJson a0 <*> fromJson a1 <*> fromJson a2
    ("ItemBlock", [a0]) -> D.ItemBlock <$> fromJson a0
    ("ItemGrammar", [a0]) -> D.ItemGrammar <$> fromJson a0
    (t, as) -> noSuchCase "Item" t as
