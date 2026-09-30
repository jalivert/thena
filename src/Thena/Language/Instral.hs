-- | @instral@ as an Earley grammar, **derived from the op table rather than
-- written a second time** (MS7 phase 137, Tier A of @.jalivert\/LIVE-OFFERS.md@).
--
-- **The problem this solves.** @instral@'s syntax is parsed by Happy
-- ("Thena.Syntax.Parser"), a generated LALR parser, which can say /is this a
-- program/ and cannot say /what may I write next/. The chart can, and
-- "Thena.Language.Earley" has done it for object languages since phase 102b —
-- but only ever inside a tagged region, pointed at one object grammar. Nothing
-- pointed it at @instral@ itself, so the prompt offered nothing at all.
--
-- **HIS ruling, 2026-09-29: this sits alongside Happy, as a secondary parser.**
-- Whether it ever replaces @Thena.Syntax.Parser@ is deliberately left open.
--
-- **And it is not a second copy of the language.** That would be the obvious
-- shape and it is the one to refuse: two grammars for one syntax drift, and the
-- drift is silent. Instead every production here is /derived/ —
-- 'Thena.Rules.opWords' gives the words, 'Thena.Instral.Ops.signatureOf' gives
-- each one's arity and the type of each slot, and the loaded bases give the
-- rules that may be called. The same tables dispatch reads. A new op appears in
-- this grammar the day it appears in that table, without anyone editing this
-- module.
--
-- **The typed slots are Tier A.** A slot is a nonterminal named after the type
-- it wants — @Operand:Core@, @Operand:Name@ — so *"argument 2 wants a @Core@"*
-- is not a feature layered on top of the offer, it is what the offer already
-- says. 'Thena.Language.Earley.offerOptions' at that position names the
-- nonterminal, and a frontend narrows by it without being told anything new.
module Thena.Language.Instral
  ( instralRules
  , operandHead
  , statementHead
  ) where

import Data.List (nub)

import Thena.Core.Term (GlobalName (..))
import qualified Thena.Instral.Ops as Ops
import Thena.Instral.Type (Signature (..), Ty (..), renderTy)
import qualified Thena.Language.Earley as E
import Thena.Language.Regex (Regex, parseRegex)
import Thena.Rules (RuleBase (..), allCallable, opWords)

-- | The nonterminal a whole statement parses at.
statementHead :: String
statementHead = "Statement"

-- | The nonterminal an operand of this type parses at.
--
-- **The type is in the name, and that is the whole mechanism.** An offer at a
-- slot comes back as @Nonterminal \"Operand:Core\"@, so the narrowing Tier A
-- asked for needs no field beside the offer and no second question — the answer
-- already carries it. 'Thena.Instral.Type.renderTy' spells the type, so what a
-- frontend shows is what @:accepts@ would print.
operandHead :: Ty -> String
operandHead t = "Operand:" ++ renderTy t

-- | Every production of the REPL's statement syntax, for the bases loaded now.
--
-- Session-driven the same way 'Thena.View.sessionGrammars' is: pass the
-- session's bases and the rules that may be called are the ones that are
-- actually there.
instralRules :: [RuleBase] -> [E.Rule]
instralRules bs = statements bs ++ operandProductions bs

-- | One statement form: the word that opens it, the type of each slot, and the
-- type it produces if it produces one.
--
-- **Every production in this module comes from this one table** (MS7 phase 139).
-- Before it there were two walks — one building the statement productions and a
-- second recovering each slot's type by reading the nonterminal's /name/ back
-- out of the rules the first had generated. That inverse could only ever work
-- against a hardcoded list of ten types, which is why a @List Core@ slot had no
-- productions: it could not be spelled back. The table carries the 'Ty' forward
-- instead, and the inverse is gone.
data Form = Form
  { formWord   :: String
  , formParams :: [Ty]
  , formResult :: Maybe Ty
    -- ^ 'Nothing' where the form leaves nothing to bind, **and where a rule did
    -- not declare one**. An undeclared rule genuinely does not say what it
    -- produces, so it is not offered inside a slot — the same asymmetry
    -- 'formParams' has.
  }
  deriving (Eq)

-- | Every form the loaded bases make writable.
forms :: [RuleBase] -> [Form]
forms bs = opForms ++ ruleForms bs

-- | One form per op. **Arity comes from the signature, not from a table here.**
-- An op that gains a parameter gains a slot, and nothing in this module is
-- edited.
opForms :: [Form]
opForms =
  [ Form word ps r
  | (word, op) <- opWords
  , let Signature ps r = Ops.signatureOf op
  ]

-- | A rule in a loaded base may be called by name, with one slot per parameter.
--
-- **Its declared type narrows the slots when it has one**; where the file
-- declared none the slots are untyped, which is 'anyType' below and offers
-- everything. That asymmetry is the truth: an undeclared rule genuinely does not
-- say what it wants.
ruleForms :: [RuleBase] -> [Form]
ruleForms bs =
  nub
    [ Form nm (paramsFor nm arity) (resultFor nm arity)
    | r <- allCallable bs
    , let GlobalName nm = Ops.ruleName r
    , let arity = length (Ops.ruleParams r)
    ]
  where
    declared = [ (nm, sg) | b <- bs, (nm, sg) <- baseSignatures b ]

    -- No declaration, or one whose arity disagrees with this clause: the slots
    -- stand, untyped. **Not dropped** — the arity is what the clause says, and a
    -- wrong signature must not silence the offer.
    paramsFor nm arity = case agreeing nm arity of
      Just (Signature ps _) -> ps
      Nothing               -> replicate arity anyType

    resultFor nm arity = agreeing nm arity >>= \(Signature _ r) -> r

    agreeing nm arity = case lookup nm declared of
      Just sg@(Signature ps _) | length ps == arity -> Just sg
      _                                            -> Nothing

-- | Every production whose head is 'statementHead'.
statements :: [RuleBase] -> [E.Rule]
statements bs =
  [ E.Rule (formWord f ++ "/" ++ show (length (formParams f))) statementHead
      (E.Literal (formWord f) : concatMap slot (formParams f)) []
  | f <- forms bs
  ]

-- | The type an undeclared slot stands at. 'TVar' with an index no signature
-- mints, so it renders as a letter and cannot collide with a real scheme
-- variable in the same grammar.
anyType :: Ty
anyType = TVar 25

-- | A slot.
--
-- **No space symbol**: the scanner skips whitespace between symbols itself, the
-- way every object grammar relies on, so writing one here would ask the user to
-- type a space the chart has already eaten.
slot :: Ty -> [E.Symbol]
slot t = [E.Nonterminal (operandHead t)]

-- | The nonterminal a comma-separated run of this element type parses at.
--
-- Its own head rather than an inlined repetition, because the chart offers
-- whatever an item is waiting for: standing after @[a@ the item is
-- @Elements -> Operand . \",\" Elements@, so @,@ and @]@ are exactly what comes
-- back. **Right-recursive** for that reason — a left-recursive run would have
-- the comma waiting on the wrong side of the dot.
elementsHead :: Ty -> String
elementsHead t = "Elements:" ++ renderTy t

-- | What may stand at a slot of each type any form mentions.
--
-- **Built only for the types in play**, so the grammar has no productions for a
-- type nothing asks for — and, since 'shapes' walks into a list's or a pair's
-- components, @List (Name, Core)@ brings @Name@ and @Core@ with it.
operandProductions :: [RuleBase] -> [E.Rule]
operandProductions bs = concatMap forType (shapes (concatMap formParams fs))
  where
    fs = forms bs

    forType t = written t ++ nested t ++ compound t

    -- **A literal where the type is ground, and a name everywhere.** The name
    -- case is not a fallback: a local bound earlier in the body stands at any
    -- slot whatever its type, so @f xs@ is as writable as @f [a, b]@.
    written t = name t : case t of
      TString -> [ lit t "string" stringRegex ]
      TInt    -> [ lit t "int" numberRegex ]
      TChar   -> [ lit t "char" charRegex ]
      TBool   -> [ word t "true", word t "false" ]
      _       -> []

    -- **A nested call is the same table read at its result** (MS7 phase 139).
    -- @( word … )@ is 'Thena.Instral.Concrete.RawNested', which resolution
    -- hoists into @RhsOp (RawOp word …)@ — the very op-or-rule dispatch a
    -- top-level statement goes through. So what may be called inside a slot is
    -- every form whose result is that slot's type, with its own slots after it,
    -- and there is nothing to write down twice.
    nested t =
      [ E.Rule (renderTy t ++ "/(" ++ formWord f ++ ")") (operandHead t)
          ( E.Literal "(" : E.Literal (formWord f)
              : concatMap slot (formParams f) ++ [E.Literal ")"] ) []
      | f <- fs
      , formResult f == Just t
      ]

    compound t = case t of
      TList a ->
        [ rule t "[]" [E.Literal "[", E.Literal "]"]
        , rule t "[..]" [E.Literal "[", E.Nonterminal (elementsHead a), E.Literal "]"]
        , E.Rule (renderTy a ++ "/one") (elementsHead a) (slot a) []
        , E.Rule (renderTy a ++ "/more") (elementsHead a)
            (slot a ++ [E.Literal ",", E.Nonterminal (elementsHead a)]) []
        ]
      TPair a b ->
        [ rule t "pair"
            ( E.Literal "(" : slot a ++ [E.Literal ","] ++ slot b ++ [E.Literal ")"] ) ]
      -- **An @Option@ has no shape of its own**: @some x@ and @none@ are ops, so
      -- they reach a slot as @( some x )@ and @( none )@ through 'nested' — which
      -- is also the only spelling "Thena.Syntax.Parser" accepts, since a bare
      -- word at an operand is a reference and not a call.
      _ -> []

    rule t nm body = E.Rule (renderTy t ++ "/" ++ nm) (operandHead t) body []
    lit t nm re = E.Rule (renderTy t ++ "/" ++ nm) (operandHead t) [E.Scan nm re] []
    word t w    = E.Rule (renderTy t ++ "/" ++ w) (operandHead t) [E.Literal w] []
    name t      = lit t "name" identRegex

-- | Every type a slot may stand at, given the types the forms ask for directly:
-- those, and the components of any list, pair or option among them.
--
-- **A function type is not walked into.** Its argument types are not slots of
-- anything — what stands at a higher-order slot is a name — so walking it would
-- mint operand productions for types nothing can be written at.
shapes :: [Ty] -> [Ty]
shapes = go []
  where
    go done [] = reverse done
    go done (t : rest)
      | t `elem` done = go done rest
      | otherwise     = go (t : done) (parts t ++ rest)

    parts t = case t of
      TList a   -> [a]
      TOption a -> [a]
      TPair a b -> [a, b]
      _         -> []

-- The token classes. Written here rather than taken from a grammar file because
-- these are Thena's own lexemes and no object language declares them.

identRegex :: Regex
identRegex = regex "[a-zA-Z_][a-zA-Z0-9_'-]*"

numberRegex :: Regex
numberRegex = regex "-?[0-9]+"

stringRegex :: Regex
stringRegex = regex "\"[^\"]*\""

charRegex :: Regex
charRegex = regex "'[^']'"

-- | **Total by construction**: the four expressions above are constants of this
-- module and are parsed at every call, so a typo fails every test rather than
-- waiting for a rare input.
regex :: String -> Regex
regex src = case parseRegex src of
  Right r -> r
  Left _  -> error ("Thena.Language.Instral: bad built-in regex " ++ show src)
