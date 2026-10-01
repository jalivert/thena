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
  , commandRules
  , commandHead
  , operandHead
  , standsAt
  , statementHead
  ) where

import Data.List (nub)

import Thena.Core.Term (GlobalName (..))
import qualified Thena.Instral.Ops as Ops
import Thena.Instral.Type (Signature (..), Ty (..), renderTy)
import qualified Thena.Language.Earley as E
import Thena.Instral.Commands (Argument (..), Command (..), commands)
import Thena.Language.Build (languageNames, productionNames)
import qualified Thena.Language.Builtin as Builtin
import Thena.Language.Grammar (Grammar, earleyRules, productionBody)
import Thena.Language.Lexemes (charRegex, identRegex, numberRegex, stringRegex)
import Thena.Rules (RuleBase (..), allCallable, opWords)

-- | The nonterminal a whole statement parses at.
statementHead :: String
statementHead = "instral:Statement"

-- | The nonterminal a whole @:@-command parses at.
--
-- **Its own head, and not another production of 'statementHead'** — the reason is
-- in "Thena.Instral.Commands": a command is a whole line, so sharing would let the
-- chart accept @x = :where@ and @attack ; :where@, which the system refuses. An
-- advising grammar may be narrower than the running one and never wider.
commandHead :: String
commandHead = "instral:Command"

-- | Where an argument the chart cannot enumerate stands.
--
-- **A nonterminal with no productions**, deliberately. Standing just after
-- @:infer @ the offer names it and the line is not stuck, which says /something
-- goes here and I cannot list it/; type into it and the line reads as stuck, which
-- is what it does today. See 'Thena.Instral.Commands.Opaque'.
opaqueHead :: String
opaqueHead = "instral:Argument"

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
    -- **Thena's own two languages, on the same footing as an object language**
    -- (MS7 phase 147). They are here rather than beside the chart because this
    -- is the rule set a REPL line is read with, and because the @do@ block below
    -- needs a statement head to point at — which only this module has.
    ++ Builtin.surfaceRules gs ++ Builtin.coreRules gs ++ surfaceBlock
  where
    -- **The table and the types in play are worked out once.** Three of the four
    -- producers below need them, and each computing its own was a second place
    -- deciding /which types are in play/ — the kind of duplicate that agrees today
    -- and drifts later.
    fs    = forms bs
    types = shapes (concatMap formParams fs)

    -- **A surface @do@ block is `instral` written in place**
    -- (@discussion\/the-five-languages.md@ §0b, table F), so the block's own
    -- productions are the statement ones and there is no second answer to /what
    -- is a block/. Contributed from here for the dependency's sake:
    -- "Thena.Language.Builtin" may not import this module, and the statement
    -- head is this module's.
    surfaceBlock =
      [ E.Rule (Builtin.surfaceHead ++ "/atom/do") (Builtin.surfaceHead ++ "/atom")
          [E.Literal "do", E.Literal "{", E.Nonterminal blockHead, E.Literal "}"] []
      , E.Rule (blockHead ++ "/one") blockHead [E.Nonterminal statementHead] []
      , E.Rule (blockHead ++ "/more") blockHead
          [E.Nonterminal blockHead, E.Literal ";", E.Nonterminal statementHead] []
      ]

    blockHead = statementHead ++ "/block"

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
    ++ builtIn
  where
    coreish = [ t | t <- types, t == TCore || isVariable t ]

    isVariable t = case t of { TVar _ -> True; _ -> False }

    -- **Thena's own two tags, at the slots they resolve to** (MS7 phase 147).
    -- @Thena.Rules@ gives a @surface@ region a @VSurface@ and a @core@ one a
    -- @VRaw@, so the first stands at a @Surface@ slot and the second at a @Core@
    -- one — and neither at the other, which is the narrowing that makes
    -- @elaborate@'s slot say something true. **Corners are the other spelling of
    -- a @core@ region** (@AGENDA.md@ 56), so they stand wherever it does.
    builtIn =
      [ tagRule t "surface" Builtin.surfaceHead
      | t <- types, t == TSurface || isVariable t
      ] ++
      [ tagRule t "core" Builtin.coreHead | t <- coreish ]

    -- **Corners are not offered, and the phase's own test is why** (@AGENDA.md@
    -- 56). @⌜ t ⌝@ is an operand in @Thena.Syntax.Parser@ and **is not one in
    -- @Thena.Surface.Parser@** — the two instral grammars differ in exactly this
    -- place — so offering them put @do { prim-try ⌜ x ⌝ }@ in reach of a surface
    -- @do@ block, which Happy refuses. @neverWiderSurface@ caught it. @core\`t\`@
    -- is the spelling both grammars accept and says the same thing, which is
    -- item 56's own conclusion, so nothing a user needs is lost by leaving the
    -- narrower spelling out.
    tagRule t tag h = fenced t ("`" ++ tag) (tag ++ "`") h "`"

    fenced t nm open h close =
      E.Rule (renderTy t ++ "/" ++ nm) (operandHead t)
        [E.Literal open, E.Nonterminal h, E.Literal close] []

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
        ( E.Literal (l ++ "[" ++ p ++ "]`") : productionBody gs p ++ [E.Literal "`"] ) []


-- | **The @:@-command productions, as a rule set of their own** (MS7 phase 142).
--
-- **Not concatenated into 'instralRules'.** The two heads are disjoint — a command
-- is a whole line and a statement is an instruction, so no line is ever both — and
-- 'Thena.Language.Earley.offerOptions' tries every candidate symbol /in the rule
-- set/ at the cursor to see which could still finish the line, so a statement offer
-- would be trying thirty-one command literals at a position none of them can stand
-- in. **Measured at about 5% of the offer at a statement slot**, back to back in one
-- session: worth having and not dramatic. The reason to split is that the union is
-- needless, not that it was slow.
commandRules :: [Grammar] -> [E.Rule]
commandRules gs =
  commandProductions gs
    -- **The grammars the command productions now point into** (MS7 phase 147).
    -- Before it, every command argument was either a literal or the opaque
    -- nonterminal, so this set needed no productions but its own; @:parse LC @,
    -- @:core @ and @:infer @ reach a real grammar now.
    ++ earleyRules gs ++ Builtin.surfaceRules gs ++ Builtin.coreRules gs

-- | One production per shape of every @:@-command, derived from
-- 'Thena.Instral.Commands.commands'.
--
-- **Nothing here lists a command**: the words, the arities and the argument shapes
-- are that table's, and a command added to it is completable with nothing edited
-- here. The one thing this function knows is how each 'Argument' becomes symbols.
commandProductions :: [Grammar] -> [E.Rule]
commandProductions gs =
  [ E.Rule (commandWord c ++ "/" ++ show n ++ "/" ++ show k) commandHead
      (E.Literal (commandWord c) : body) []
  | c <- commands
  , (n, shape) <- zip [0 :: Int ..] (commandShapes c)
  , (k, body) <- zip [0 :: Int ..] (expand shape)
  ]
  where
    -- **A choice is spelled out as separate productions, not reached through a
    -- nonterminal of its own.** A nonterminal was the first shape and it leaked:
    -- the chart names whatever sits at the cursor, so @:step @ answered with
    -- @instral:Choice:on.off.@ — a name invented here, handed to a frontend to
    -- draw. **The same mistake phase 141 made with @At:LC:var@ and caught**, which
    -- is why the check for it is now a test over every nonterminal an offer can
    -- report and not a check on one name.
    expand []         = [[]]
    expand (a : rest) = [ pre ++ post | pre <- waysOf a, post <- expand rest ]

    waysOf a = case a of
      OneOf ws  -> [ [E.Literal w] | w <- ws ]
      ANumeral  -> [ [E.Scan "int" numberRegex] ]
      -- **Whatever is loaded**, so @:parse @ names the languages that are actually
      -- there and nothing has to be kept in step.
      ALanguage -> [ [E.Literal l] | l <- languageNames gs ]
      -- **The name and the term together**, because the second depends on the
      -- first and 'expand' is a product over independent arguments (MS7 phase
      -- 147). @:parse LC @ then offers @LC@'s own productions and nothing else's.
      ALanguageTerm -> [ [E.Literal l, E.Nonterminal l] | l <- languageNames gs ]
      -- **Thena's own two languages are describable now** (MS7 phase 147), so a
      -- term argument is a nonterminal with productions rather than the opaque
      -- one below.
      ASurfaceTerm -> [ [E.Nonterminal Builtin.surfaceHead] ]
      ACoreTerm    -> [ [E.Nonterminal Builtin.coreHead] ]
      -- The one nonterminal an offer may report from this module, and the one a
      -- frontend is meant to see: see 'opaqueHead'.
      Opaque    -> [ [E.Nonterminal opaqueHead] ]

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

