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
  , acts
  , actWords
  , isCommandLine
  , isWholeLine
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
  -- MS8 phase 174. **Not @:rules@**, which is the engine's rule base: an
  -- @instral@ rule and an inference rule are two different things, and one word
  -- for both would be the kind of collision the naming is careful about.
  , one ":judgment"
  , one ":accepts"
  , one ":produces"
  , one ":load"
  -- A path, like @:load@'s: a proof-script is reached by path and not by module
  -- name, because its naming is the frontend's (MS11 phase 302).
  , one ":replay"
  , one ":consult"
  , one ":theorem"
  , one ":resume"
  -- Optional: the focus, or a term written out.
  , optional ":show"
  -- **Only the bare, surface form.** @Thena.Driver.coreFenced@ also accepts
  -- @:infer core\`t\`@ as a development-calculus term and that runs; it is
  -- simply not offered. **The reason has changed and the line has not** (MS10
  -- phase 269): it used to be that corners were on their way out and nothing
  -- new could point at them, and now the fence is the only spelling there is,
  -- so offering both arms of one word here is a question for whoever wants
  -- two.
  , Command ":infer" [[], [ASurfaceTerm]]
  , Command ":whnf"  [[], [ACoreTerm]]
  -- @:convert ‹t› ≟ ‹u›@ — two opaque terms with a fence between them, which is
  -- the one shape where a literal sits *after* something unenumerable, so the
  -- fence is offered only once the first term reads.
  , Command ":convert" [[ACoreTerm, OneOf ["\8799"], ACoreTerm]]
  -- The enumerable ones, and the reason this table earns its keep.
  , Command ":step" [[], [OneOf ["on", "off"]], [ANumeral]]
  , Command ":run"  [[], [ANumeral]]
  -- **The trust level, and its three settings are enumerable** (MS8 phase 151),
  -- so the offer names them rather than leaving the user to remember three
  -- words. The bare form is the look.
  , Command ":trust"
      [[], [OneOf ["none", "no-undischargeable", "any"]]]
  , Command ":parse" [[ALanguage], [ALanguageTerm]]
  ]

-- | __The bare-word acts, with the shape of their argument__ (MS12 phase 312).
--
-- **Why there has to be a second table.** These are the words a /file/ writes, so
-- §2.4 spells them without a colon — and 'isCommandLine' therefore answers 'False'
-- for a line beginning with one, which sends it to the statement grammar, where no
-- production names it. The visible result was that @impo@ was offered nothing at
-- all, and @cons@ was offered four ops whose spelling happens to start the same
-- way and not @consult@.
--
-- **They are the driver's and not the rule base's, which is the whole reason they
-- need writing down.** An op — @attack@, @certify@, @constructors-of@ — is a form
-- in a rule base and the statement grammar offers it already; these five are a
-- @case@ in @Thena.Driver.dispatch@ and nothing the offer reads knows about them.
--
-- **Not another set of productions of the statement head**, which is also a
-- @do@ block's head: @data@ is not an instruction, and an advising grammar may be
-- narrower than the running one but never wider. They stand under
-- 'Thena.Language.Instral.lineHead', which is a prompt line and derives either.
--
-- **@open@'s argument is enumerable and the others are not.** The namespaces
-- that can be opened are a read of the session
-- (@Thena.Driver.openableNamespaces@), so they are offered by name; a module
-- name would need the engine's module search, which is not a pure read of a
-- session, and a declaration or a signature has no finite set at all.
--
-- **@open@ keeps an 'Opaque' shape beside the enumerated one**, so that a
-- namespace the offer does not list — a shortened spelling, or one declared
-- since — still reads as a line rather than going stuck under the cursor.
acts :: [String] -> [Command]
acts namespaces =
  [ Command "open" [[OneOf namespaces], [Opaque]]
  , one "declare"
  , one "import"
  , one "consult"
  , one "data"
  ]

-- | The words 'acts' names, which is a question with no namespaces in it.
--
-- **@acts []@ and not a second list**: the namespaces decide what may follow
-- @open@ and not whether @open@ is a word, so the words can be read off the
-- table with none supplied rather than written down twice and kept in step.
actWords :: [String]
actWords = map commandWord (acts [])

-- | Is this line a whole-line form — a @:@-command, or one of the bare acts?
--
-- **The question the offer has to ask about CONTEXT** (MS12 phase 312). A
-- statement is asked about context-free, because the text before a word in one
-- may not read on its own — @LC\`x\` atta@ has no reading up to @atta@ — but a
-- whole-line form always reads up to its argument, so @:step o@ offers @on@ and
-- @off@, and before this @open E@ offered nothing at all. The two kinds of
-- whole line differ in their punctuation and in nothing else that matters here.
isWholeLine :: String -> Bool
isWholeLine line = isCommandLine line || firstWord line `elem` actWords
  where firstWord = takeWhile (/= ' ') . dropWhile (== ' ')

nothing, one, optional :: String -> Command
nothing w  = Command w [[]]
one w      = Command w [[Opaque]]
optional w = Command w [[], [Opaque]]
