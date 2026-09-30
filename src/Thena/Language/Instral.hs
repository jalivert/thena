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
  , standsAt
  , statementHead
  ) where

import Data.List (nub)

import Thena.Core.Term (GlobalName (..))
import qualified Thena.Instral.Ops as Ops
import Thena.Instral.Type (Signature (..), Ty (..), renderTy)
import qualified Thena.Language.Earley as E
import Thena.Language.Build (languageNames, productionNames)
import Thena.Language.Grammar (Grammar, earleyRules)
import Thena.Language.Regex (Regex, parseRegex)
import Thena.Rules (RuleBase (..), allCallable, opWords)

-- | The nonterminal a whole statement parses at.
statementHead :: String
statementHead = "instral:Statement"

-- | The nonterminal an operand of this type parses at.
--
-- **The type is in the name, and that is the whole mechanism.** An offer at a
-- slot comes back as @Nonterminal \"Operand:Core\"@, so the narrowing Tier A
-- asked for needs no field beside the offer and no second question — the answer
-- already carries it. 'Thena.Instral.Type.renderTy' spells the type, so what a
-- frontend shows is what @:accepts@ would print.
operandHead :: Ty -> String
operandHead t = "Operand:" ++ renderTy t

-- | May a value of this type stand at the slot this nonterminal names?
--
-- **Forward only.** A slot's name is built from a 'Ty' by 'operandHead' and is
-- never read back — phase 139 deleted the inverse that could not spell
-- @List Core@, and this must not reintroduce it. So the question is asked by
-- building the name and comparing, which is the direction that cannot fail.
--
-- **A slot whose type is a scheme variable takes anything**, because an
-- undeclared rule does not say what it wants. Those slots are found by building
-- their names too, not by recognising a letter.
standsAt :: Ty -> String -> Bool
standsAt t n = n == operandHead t || n `elem` variableSlots

-- | The names of the slots that accept any type at all.
variableSlots :: [String]
variableSlots = [ operandHead (TVar i) | i <- [0 .. 25] ]

-- | Every production of the REPL's statement syntax, for the bases loaded now.
--
-- Session-driven the same way 'Thena.View.sessionGrammars' is: pass the
-- session's bases and the rules that may be called are the ones that are
-- actually there.
instralRules :: [Grammar] -> [RuleBase] -> [E.Rule]
instralRules gs bs =
  statements fs ++ operandProductions fs types ++ earleyRules gs
    ++ literalProductions gs types
  where
    -- **The table and the types in play are worked out once.** Three of the four
    -- producers below need them, and each computing its own was a second place
    -- deciding /which types are in play/ — the kind of duplicate that agrees today
    -- and drifts later.
    fs    = forms bs
    types = shapes (concatMap formParams fs)

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
statements :: [Form] -> [E.Rule]
statements fs =
  [ E.Rule (formWord f ++ "/" ++ show (length (formParams f))) statementHead
      (E.Literal (formWord f) : concatMap slot (formParams f)) []
  | f <- fs
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
operandProductions :: [Form] -> [Ty] -> [E.Rule]
operandProductions fs types = concatMap forType types
  where
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

-- | **A tagged term literal is an operand** (MS7 phase 141), so one chart reads a
-- whole line and the offer inside a literal is the same answer as the offer outside
-- it.
--
-- The object grammars are concatenated into this rule set by 'instralRules' and a
-- literal is three symbols: the opening tag, the language's own nonterminal, and
-- the closing fence. Everything inside is then the object grammar answering for
-- itself, which is what makes @fill LC\`( \955 x : @ offer @\953@ — @abs@'s type slot,
-- read out of the grammar the user wrote.
--
-- **It stands where a @Core@ stands**, because that is what one resolves to:
-- @Thena.Rules@ turns a region of a declared object language into a @VTerm@ or an
-- @ObjectOf@, never a @Surface@. It is offered at a variable-typed slot too, since
-- an undeclared rule's slot takes anything.
--
-- **@surface\`…\`@ and @core\`…\`@ are not here**, and that is deliberate — see the
-- module header of "Thena.View.Statement" for what still answers for them.
literalProductions :: [Grammar] -> [Ty] -> [E.Rule]
literalProductions gs types =
  [ rule t l | t <- coreish, l <- languageNames gs ]
    ++ [ atRule t l p
       | t <- coreish, l <- languageNames gs, p <- productionNames gs l ]
  where
    coreish = [ t | t <- types, t == TCore || isVariable t ]

    isVariable t = case t of { TVar _ -> True; _ -> False }

    -- @LC\`…\`@ — a term of the language.
    rule t l =
      E.Rule (renderTy t ++ "/`" ++ l) (operandHead t)
        [E.Literal (l ++ "`"), E.Nonterminal l, E.Literal "`"] []

    -- @LC[var]\`…\`@ — a term of one named production of it (MS6 phase 104c).
    --
    -- **The production's body is inlined, not reached through a nonterminal of its
    -- own.** A wrapper was the first shape and it was wrong for a reason only the
    -- offer shows: the chart names whatever nonterminal sits at the cursor, so
    -- @fill LC[var]\`@ answered with @At:LC:var@ — a name this module invented,
    -- handed to a frontend to draw. Inlined, the answer is the production's own
    -- first symbols, which is what the user is being asked for.
    atRule t l p =
      E.Rule (renderTy t ++ "/`" ++ l ++ "[" ++ p ++ "]") (operandHead t)
        ( E.Literal (l ++ "[" ++ p ++ "]`") : bodyOf p ++ [E.Literal "`"] ) []

    -- **The search is across every loaded grammar, and that is safe because a
    -- production name is unique across all of them.** Each production becomes a
    -- datatype constructor, and a second language declaring one of the same name is
    -- refused when it loads — @A's constructor same is already declared@. Checked
    -- by loading such a pair, not assumed; @productionNamesAreUnique@ in
    -- "Thena.View.StatementTests" pins it, because if that ever relaxed this
    -- lookup would quietly hand one language another's production.
    bodyOf p = case [ E.ruleBody r | r <- earleyRules gs, E.ruleName r == p ] of
      b : _ -> b
      -- **Cannot arise** — the production came from 'productionNames' of a grammar
      -- in this very list. Answered rather than crashed, because this is a view.
      []    -> []

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
