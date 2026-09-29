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

-- | Every production whose head is 'statementHead'.
statements :: [RuleBase] -> [E.Rule]
statements bs = opProductions ++ callProductions bs

-- | One production per op: its keyword, then a slot per declared parameter.
--
-- **Arity comes from the signature, not from a table here.** An op that gains a
-- parameter gains a slot, and nothing in this module is edited.
opProductions :: [E.Rule]
opProductions =
  [ E.Rule (word ++ "/" ++ show (length ps)) statementHead
      (E.Literal word : concatMap slot ps) []
  | (word, op) <- opWords
  , let Signature ps _ = Ops.signatureOf op
  ]

-- | A rule in a loaded base may be called by name, with one slot per parameter.
--
-- **Its declared type narrows the slots when it has one**; where the file
-- declared none the slots are untyped, which is 'AnyOperand' below and offers
-- everything. That asymmetry is the truth: an undeclared rule genuinely does not
-- say what it wants.
callProductions :: [RuleBase] -> [E.Rule]
callProductions bs =
  nub
    [ E.Rule (nm ++ "/" ++ show (length params)) statementHead
        (E.Literal nm : concatMap slot (typesFor nm (length params))) []
    | r <- allCallable bs
    , let GlobalName nm = Ops.ruleName r
    , let params = Ops.ruleParams r
    ]
  where
    declared = [ (nm, sg) | b <- bs, (nm, sg) <- baseSignatures b ]
    typesFor nm arity = case lookup nm declared of
      Just (Signature ps _) | length ps == arity -> ps
      -- No declaration, or one whose arity disagrees with this clause: the
      -- slots stand, untyped. **Not dropped** — the arity is what the clause
      -- says, and a wrong signature must not silence the offer.
      _ -> replicate arity anyType

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

-- | What may stand at a slot of each type that any production mentions.
--
-- **Built only for the types in play**, so the grammar has no productions for a
-- type nothing asks for.
operandProductions :: [RuleBase] -> [E.Rule]
operandProductions bs =
  concat [ forType t | t <- nub (concatMap slotsOf (statements bs)) ]
  where
    forType t = case t of
      TString -> [ lit t "string" stringRegex ]
      TName   -> [ lit t "name" identRegex ]
      TInt    -> [ lit t "int" numberRegex ]
      TChar   -> [ lit t "char" charRegex ]
      TBool   -> [ word t "true", word t "false" ]
      -- The four abstract types and everything else are written as a name bound
      -- earlier in the body, or as a literal of the object language. A region is
      -- another grammar's business and enters as its own nonterminal, which the
      -- caller supplies; here it is the name case that matters, and it is the
      -- one a completion has anything to say about.
      _       -> [ lit t "name" identRegex ]

    slotsOf r =
      [ ty | E.Nonterminal n <- E.ruleBody r, Just ty <- [typeOfHead n] ]

    -- The inverse of 'operandHead'. **Kept beside it on purpose**: the two are
    -- one encoding and a reader should meet them together.
    typeOfHead n = case splitAt (length prefix) n of
      (p, rest) | p == prefix -> lookup rest spelled
      _                       -> Nothing
      where prefix = "Operand:"

    spelled = [ (renderTy t, t) | t <- candidates ]
    candidates =
      [ TString, TName, TInt, TChar, TBool, TSurface, TCore, TDevelopment
      , TLevel, anyType ]

    lit t nm re = E.Rule (renderTy t ++ "/" ++ nm) (operandHead t) [E.Scan nm re] []
    word t w    = E.Rule (renderTy t ++ "/" ++ w) (operandHead t) [E.Literal w] []

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
