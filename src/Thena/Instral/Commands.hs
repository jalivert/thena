-- | **The @:@-commands, as a table** (MS7 phase 142).
--
-- The driver dispatches a @:@-line with a @case@ on the word
-- (@Thena.Driver.dispatch@), and @Thena.Driver.commandSummary@ writes the words a
-- second time for @:help@ — the duplication @.claude\/plans\/LONG-TERM.md@ 24 holds
-- open. This module is a third thing and deliberately not a fourth copy: it is the
-- only place that says what shape a command's **argument** has, which is what a
-- grammar needs and which neither of the other two records.
--
-- **What it is for.** 'Thena.Language.Instral' derives the productions of a
-- @:@-line from this table, so the prompt can complete @:inf@ to @:infer@ and can
-- say what may follow a word. The words are crossed against @commandSummary@ by
-- the suite, so a command added to one and not the other is caught.
--
-- **A @:@-command is a whole line and nothing smaller** — established by running
-- it, not read off the grammar: @x = :where@ and @attack ; :where@ are both parse
-- errors, @:where ; :where@ treats the whole rest of the line as one argument, and
-- a line with a newline in it is no command at all. That is why it has a head of
-- its own rather than being another production of a statement: sharing one would
-- let the chart accept lines the system refuses, and an advising grammar may be
-- narrower than the running one but never wider.
module Thena.Instral.Commands
  ( Command (..)
  , Argument (..)
  , commands
  , isCommandLine
  ) where

-- | What may follow a command word.
data Argument
  = OneOf [String]
    -- ^ exactly one of these words — @:step on@, @:step off@.
  | ANumeral
    -- ^ a whole number — @:step 3@, @:run 20@.
  | ALanguage
    -- ^ the name of a loaded object language — @:parse LC …@. Filled in from the
    -- session, so it is right for whatever is loaded.
  | ASurfaceTerm
    -- ^ a surface term written out — @:surface \ x -> x@, @:infer@'s bare form
    -- (MS7 phase 147). Read by "Thena.Surface.Read"; described by
    -- "Thena.Language.Builtin".
  | ACoreTerm
    -- ^ a term of the development calculus — @:core@, @:whnf \‹t\›@, @:goal@,
    -- both sides of @:convert@, @:dev@ (MS7 phase 147). Read by
    -- "Thena.Syntax.Parser"; described by "Thena.Language.Builtin".
  | ALanguageTerm
    -- ^ **a language's name and then a term of /that/ language** — @:parse LC …@
    -- (MS7 phase 147). One 'Argument' and not two, because the two positions are
    -- correlated: which nonterminal follows depends on which name was written,
    -- and 'Thena.Language.Instral.commandProductions' expands a shape as an
    -- independent product.
  | Opaque
    -- ^ **real syntax the chart has no grammar for**: a file path, a global's
    -- name, a theorem's statement.
    --
    -- It becomes a nonterminal with **no productions**, which is the honest
    -- answer rather than a convenient one. Standing just after @:infer @ the offer
    -- names it and is /not/ stuck — a production is open and waiting — and once
    -- something is typed into it the line reads as stuck, exactly as it does
    -- today. **Widening the grammar to accept anything there is what he
    -- rejected** (@.claude\/RULINGS.md@: it drowns the offer that matters).
    --
    -- **The term cases are gone from this constructor since MS7 phase 147** —
    -- they are 'ASurfaceTerm' and 'ACoreTerm' above, and they are described by
    -- a grammar rather than closed by one. What is left here genuinely has no
    -- grammar: a path, a name, a statement.
  deriving (Eq, Show)

-- | One command: its word, and each shape its argument may take.
--
-- @[[]]@ is /takes no argument/ — one alternative, which is empty. A command with
-- an optional argument has two alternatives, and @commandSummary@ writes those the
-- same way: @:show \/ :show ‹name›@.
data Command = Command
  { commandWord   :: String
  , commandShapes :: [[Argument]]
  }
  deriving (Eq, Show)

-- | Is this line a command rather than an entry?
--
-- **The driver's own rule, in one place.** @Thena.Driver.command@ splits the first
-- word off and treats it as a command when it begins with a colon; the offer has to
-- ask the same question and must not have its own answer to it.
isCommandLine :: String -> Bool
isCommandLine line = case dropWhile (== ' ') line of
  ':' : _ -> True
  _       -> False

-- | Every command the driver dispatches, with the shape of its argument.
--
-- **The words are @Thena.Driver.dispatch@'s, and the suite crosses them against
-- @commandSummary@** so the three lists cannot drift apart silently. The /shapes/
-- are this table's own contribution and are written from the dispatch arms.
commands :: [Command]
commands =
  [ nothing ":help"
  , nothing ":quit"
  , nothing ":done"
  , nothing ":where"
  , nothing ":matches"
  , nothing ":choices"
  , nothing ":bases"
  , nothing ":rules"
  , nothing ":revalidate"
  , nothing ":extract"
  , nothing ":suspend"
  , nothing ":abandon"
  , nothing ":proofs"
  , nothing ":undo"
  -- **A term, in one language or the other** (MS7 phase 147). Which one is the
  -- dispatch arm's, not a guess: @:core@, @:dev@, @:goal@ and @:whnf@'s argument
  -- all go to 'Thena.Driver.parseCore' or @parseDevelopment@, and @:surface@ to
  -- @parseSurfaceTerm@.
  , Command ":core"    [[ACoreTerm]]
  , Command ":dev"     [[ACoreTerm]]
  , Command ":goal"    [[ACoreTerm]]
  , Command ":surface" [[ASurfaceTerm]]
  -- One argument the chart cannot enumerate: a path, a name, a statement.
  , one ":elim"
  , one ":accepts"
  , one ":produces"
  , one ":load"
  , one ":theorem"
  , one ":resume"
  -- Optional: the focus, or a term written out.
  , optional ":show"
  -- **Only the bare, surface form.** @Thena.Driver.cornered@ also accepts
  -- @:infer ⌜ t ⌝@ as a core term and that still runs — it is simply not
  -- offered, on his instruction of 2026-10-01: corners are to be replaced by
  -- @core\`t\`@ throughout (@AGENDA.md@ 98) and nothing new may point at them.
  , Command ":infer" [[], [ASurfaceTerm]]
  , Command ":whnf"  [[], [ACoreTerm]]
  -- @:convert ‹t› ≟ ‹u›@ — two opaque terms with a fence between them, which is
  -- the one shape where a literal sits *after* something unenumerable, so the
  -- fence is offered only once the first term reads.
  , Command ":convert" [[ACoreTerm, OneOf ["\8799"], ACoreTerm]]
  -- The enumerable ones, and the reason this table earns its keep.
  , Command ":step" [[], [OneOf ["on", "off"]], [ANumeral]]
  , Command ":run"  [[], [ANumeral]]
  , Command ":parse" [[ALanguage], [ALanguageTerm]]
  ]
  where
    nothing w  = Command w [[]]
    one w      = Command w [[Opaque]]
    optional w = Command w [[], [Opaque]]
