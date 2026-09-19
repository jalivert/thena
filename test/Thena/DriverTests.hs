-- | Commands: what they compile to, what they refuse, and where they leave the
-- session.
module Thena.DriverTests (tests) where

import Data.List (nub)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Convert (convert)
import Thena.Core.Level (levelOfNat)
import Thena.Core.Term (Core (..), GlobalName (..), Ident (..))
import Thena.Development.Component (Component (..))
import Thena.Development.Partial (Partial (..))
import Thena.Standard (withRules)
import Thena.Driver
  ( CommandError (..)
  , Response (..)
  , Session (..)
  , Stop (..)
  , answer
  , command
  , commandSummary
  , newSession
  )
import Thena.Development.Cursor (rebuild)
import Thena.Engine (Machine (..), Question (..), globals, development, flatten)
import Thena.Errors (FailReason (..))
import Thena.Global.Declare (DeclareError (..))
import Thena.Global.Env (isDeclared)
import Thena.Repl (entriesOf, unclosedEntry)

-- | The names in a 'Fitting' listing, for the tests below.

import Thena.Instral.Ops (AnswerKind (..), partWords)
import Thena.Instral.Infer (InstralTypeError (..), Site (..))
import Thena.Rules (RuleError (..))

-- | Run a script of command lines, answering nothing, and give back the last
-- response and the session it left.
-- | **Starting from a session with the standard base**, because elaboration is
-- a rule now (MS4 phase 49) and `:infer ‹surface›` calls it. It was
-- 'newSession' while elaboration was reachable without one.
say :: [String] -> (Session, Response)
say = foldl next (withRules, Blank)
  where
    next (s, _) l = command s l

devOf :: Session -> Partial
devOf = flatten . development . sessionMachine

-- | What is typed to declare the running example. The @data@ word is the
-- command; everything after it is the grammar's (§2.4).
natCommand :: String
natCommand = "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"

declaredIn :: Session -> String -> Bool
declaredIn s g = isDeclared (GlobalName g) (globals (sessionMachine s))

-- | The words of every spelling @:help@ shows, and those of them that are
-- colon words.
wordsIn :: [(String, String)] -> [String]
wordsIn = concatMap (words . fst)

-- A colon and something: the bare @:@ of @assume \8249x\8250 : \8249S\8250@ is
-- ascription\'s, not a command\'s.
colonWordsIn :: [(String, String)] -> [String]
colonWordsIn = filter (\w -> take 1 w == ":" && length w > 1) . wordsIn

-- | Every @:word@ the given text mentions.
--
-- A colon followed by lowercase letters, which is what a command is and what
-- nothing else in Haskell source is: @::@ has a second colon, @:|@ has a bar,
-- and a constructor is capitalised.
colonWordsInSource :: String -> [String]
colonWordsInSource src = case break (== ':') src of
  (_, ':' : rest) ->
    let (w, more) = span (`elem` ['a' .. 'z']) rest
     in [ ':' : w | not (null w) ] ++ colonWordsInSource more
  _ -> []

unknown :: String -> Bool
unknown w = case snd (command withRules w) of
  Rejected (NoSuchCommand _) -> True
  _                          -> False

-- | The driver\'s own words, written out. **Hand-written and not total** — no
-- function can enumerate a @case@ — so this is a mirror that has to be kept up
-- by the same hand that adds a command. It is here rather than in the driver
-- because a mirror in the same module as the thing it mirrors checks nothing.
everyColonCommand :: [String]
everyColonCommand =
  [ ":help", ":quit", ":core", ":surface", ":dev", ":show", ":elim", ":where", ":matches", ":accepts", ":produces"
  , ":choices", ":goal", ":whnf", ":infer", ":parse", ":done", ":load", ":bases", ":rules"
  , ":revalidate", ":extract", ":theorem", ":suspend", ":resume", ":abandon"
  , ":proofs", ":undo", ":convert", ":step", ":run"
  ]

-- | **Hand-written, and it had the same gaps as the list it checks** (MS4
-- phase 43): @declare@ and @quantify@ were missing from both, and @prove@ was
-- in both after phase 41 made it a rule rather than a command. A mirror that
-- shares the blind spot of what it mirrors cannot catch anything — which is the
-- argument for @ms3\/CLOSEOUT.md@ 26, not against having it.
-- | Colon words the driver's source mentions that are **not** commands.
--
-- Each is a word the module writes for another reason — a prefix it matches on,
-- a spelling in an error message, a word from another language quoted in a
-- comment. Listing them is the price of deriving the rest, and it is a price
-- worth paying: the alternative is a mirror nothing crosses.
notCommands :: [String]
notCommands =
  -- Both appear only in comments that say they are *not* commands: @yield@ is
  -- bare because §2.4 says a bare word acts, and there is no @:ops@ because
  -- @:rules@ shows the base instead. 'notReallyCommands' below checks the
  -- driver agrees, so this list cannot be used to hide one.
  [ ":yield", ":ops" ]

everyBareCommand :: [String]
everyBareCommand =
  [ "assume", "claim", "quantify", "data", "declare"
  , "along", "into", "back", "reduce", "unify"
  , "do", "yield"
  , "retry", "goto-named", "cross", "certify", "qed"
  ] ++ partWords

tests :: TestTree
tests =
  testGroup
    "Thena.Driver"
    [ testGroup
        "the command line"
        [ testCase "an empty line does nothing" $
            snd (command withRules "") @?= Blank
        , testCase ":quit leaves the loop" $
            snd (command withRules ":quit") @?= Quit
        , testCase "an unknown word is not a term, it is a mistake" $
            -- **Refused before it runs** since MS5 phase 92: a name nothing
            -- defines is a type error, at the prompt as in a file.
            snd (command withRules "hello")
              @?= EntryMistyped [Undefined (InBody (GlobalName "entry") 0) "hello" 0 []]
        , testCase "a command that merely starts with :core is not :core" $
            snd (command withRules ":corex") @?= Rejected (NoSuchCommand ":corex")
        , testCase "a view command with no argument says so" $
            snd (command withRules ":core") @?= Rejected (MissingArgument ":core")
        , -- **These five are refused by "Thena.Rules" now** (MS5 phase 62b), not
          -- by a case of 'dispatch' with an argument grammar of its own — the
          -- word and its operands are read at the prompt by exactly the pass
          -- that reads a rule body. The words are unmoved and so are the
          -- refusals; what changed is who says so.
          testCase "cross must say which field" $
            snd (command withRules "cross")
              @?= LineRefused [BadOperands (GlobalName "entry") 0 "cross"]
        , testCase "and it must be one of the two there are" $
            snd (command withRules "cross body")
              @?= LineRefused [BadOperands (GlobalName "entry") 0 "cross"]
        , testCase "a positional descent needs a number" $
            snd (command withRules "param")
              @?= LineRefused [BadOperands (GlobalName "entry") 0 "param"]
        , testCase "and it has to be one" $
            snd (command withRules "param x")
              @?= LineRefused [BadOperands (GlobalName "entry") 0 "param"]
        , testCase "a plain descent takes no argument" $
            snd (command withRules "cod 2")
              @?= LineRefused [BadOperands (GlobalName "entry") 0 "cod"]
        , testCase ":where answers with the cursor, not with text" $
            case snd (command withRules ":where") of
              Where _ -> pure ()
              other   -> assertFailure ("expected Where, got " ++ show other)
        , testCase ":show with an argument is a global, not a mistake" $
            snd (command withRules ":show x") @?= Rejected (NoSuchGlobal "x")
        , testCase ":step takes on, off, or nothing" $
            snd (command withRules ":step sideways") @?= Rejected (UnexpectedArgument ":step")
        ]
    , testGroup
        "the help list"
        -- 'commandSummary' is a second place a command word is written and
        -- 'dispatch' is a @case@, so nothing can derive one from the other.
        -- These three cross them as far as anything can: the first direction
        -- is total, the other two lean on a hand-written list below, exactly
        -- as @RuleSyntaxTests@\' @everyOp@ does and with the same admitted
        -- incompleteness.
        [ testCase "every colon word it lists is a command" $
            filter unknown (colonWordsIn commandSummary) @?= []
        , testCase "every colon command is listed" $
            filter (`notElem` colonWordsIn commandSummary) everyColonCommand @?= []
        , testCase "every bare command the driver has is listed" $
            filter (`notElem` wordsIn commandSummary) everyBareCommand @?= []

          -- **The mirror, made total against the source** (2026-09-13).
          -- 'everyColonCommand' is hand-written and cannot be derived, because
          -- @dispatch@ is a @case@ — which is @ms3\/CLOSEOUT.md@ 26 and is his
          -- to restructure, not mine. What /can/ be derived without touching
          -- the design is the set of colon words the module mentions at all:
          -- every one of them is either dispatched (and so must be listed) or
          -- is not a command, and the second list says which.
          --
          -- A word the driver accepts and @:help@ does not name is the exact
          -- failure phase 36 shipped and phase 43 found again.
        , testCase "and no colon word in the driver's source is unaccounted for" $ do
            src <- readFile "src/Thena/Driver.hs"
            let mentioned = nub (colonWordsInSource src)
                unaccounted =
                  [ w
                  | w <- mentioned
                  , w `notElem` everyColonCommand
                  , w `notElem` notCommands
                  ]
            unaccounted @?= []

          -- The exclusion list, checked: a word here that the driver *does*
          -- accept would be a command hidden from @:help@ by this very test.
        , testCase "and nothing excluded is secretly a command" $
            filter (not . unknown) notCommands @?= []
        ]
    , testGroup
        "a typed entry is an instral block"
        -- **MS5 phase 70, his §4**: a REPL entry is a block, so assignment and
        -- sequencing are legal at the prompt and a binding dies with the entry —
        -- not by prohibition, but because that is what block scope means.
        [ testCase "several instructions run as one program" $
            devOf (fst (say [natCommand, ":theorem t : Nat", "attack ; intro"]))
              @?= devOf (fst (say [natCommand, ":theorem t : Nat", "attack", "intro"]))
        , testCase "a binding is read later in the same entry" $
            snd (say [natCommand, ":theorem t : Nat", "m = concat \"a\" \"b\" ; say m"])
              @?= Ran ["ab"] [] Completed
          -- **And it dies with the entry**, which is the whole of §4's argument:
          -- there is no persistent REPL environment to unwind.
        , testCase "and not in the next one" $
            -- **Refused at entry time as of the MS5 review** — a typed entry is
            -- validated and typed the way a rule file is, so the binding being
            -- gone is reported before anything runs rather than halting mid-way.
            snd (say [ natCommand, ":theorem t : Nat"
                     , "m = concat \"a\" \"b\"", "say m" ])
              @?= LineRefused [UnboundInRule (GlobalName "entry") 0 "m"]
          -- A value may be bound at the prompt now too (phase 68a's `Op.Value`).
        , testCase "a literal may be bound" $
            snd (say [natCommand, ":theorem t : Nat", "n = 42 ; say \"ok\""])
              @?= Ran ["ok"] [] Completed
        ]
    , testGroup
        "the REPL's do command is checked like any other entry"
        -- **MS5 phase 90, @ms5\/CLOSEOUT.md@ 41.** It resolved its block and
        -- loaded it, so @prim-try 3@ halted mid-run where the same instruction
        -- typed bare is refused before anything starts.
        [ testCase "a type error in one is refused" $
            case snd (say [":theorem t : Type\8320", "do { prim-try 3 }"]) of
              EntryMistyped (_ : _) -> pure ()
              other -> assertFailure ("expected a type error, got " ++ show other)
        , testCase "and an unbound name in one is refused" $
            snd (say [":theorem t : Type\8320", "do { say nope }"])
              @?= LineRefused [UnboundInRule (GlobalName "entry") 0 "nope"]
        , testCase "and the development is as it was" $
            devOf (fst (say [":theorem t : Type\8320", "do { attack ; prim-try 3 }"]))
              @?= devOf (fst (say [":theorem t : Type\8320"]))
        ]
    , testGroup
        "a do block in a surface term is checked before it runs"
        -- **MS5 phase 79, and @ms5\/CLOSEOUT.md@ 20.** Until then
        -- 'Thena.Instral.Ops.Play' resolved a block as it ran, so a mistake in one
        -- halted the machine with half a proof already built. The block is a
        -- body like any other now: resolved, validated and typed when the term
        -- it sits in is read.
        [ testCase "a mistake in one is refused" $
            case snd (say [":theorem t : Type\8320", "elaborate \10216 do { say 3 } \10217"]) of
              EntryMistyped (_ : _) -> pure ()
              other -> assertFailure ("expected a type error, got " ++ show other)

          -- **The point of doing it early**: the development is exactly as it
          -- was, where before the machine ran until it hit the bad instruction.
        , testCase "and nothing of the term was elaborated" $
            let before = devOf (fst (say [":theorem t : Type\8320"]))
                after  = devOf (fst (say [":theorem t : Type\8320"
                                         , "elaborate \10216 do { say 3 } \10217"]))
             in after @?= before

          -- **A @return@ has nothing to answer.** A block in a surface term is
          -- the solution to the hole it stands in, and 'Thena.Instral.Ops.Play' splices
          -- it into the running program rather than opening a frame — so before
          -- this check a @return@ there quietly abandoned the elaboration.
        , testCase "a return in one is refused" $
            case snd (say [":theorem t : Type\8320"
                          , "elaborate \10216 do { u = fresh-universe ; return u } \10217"]) of
              LineRefused (_ : _) -> pure ()
              other -> assertFailure ("expected a refusal, got " ++ show other)

          -- …and a good one still elaborates, which is the case the check must
          -- not break: the block fills the hole it stands in.
        , testCase "a good one still runs" $
            case snd (say [":theorem t : Type\8320"
                          , "elaborate \10216 let x : Type\8320 = do { u = fresh-universe ; fill u ; solve } in x \10217"]) of
              Ran _ _ Completed -> pure ()
              other -> assertFailure ("expected it to run, got " ++ show other)
        ]
    , testGroup
        "a multi-line entry is bracketed by :{ and :}"
        -- **MS5 phase 78, his choice**: GHCi's spelling, replacing phase 70's
        -- /keep reading while it cannot be finished/ — @ms5\/CLOSEOUT.md@ 18
        -- answered rather than left split. 'entriesOf' is the rule in a form
        -- that can be driven without a terminal; 'loop' uses the same two
        -- predicates.
        [ testCase "an ordinary line is its own entry" $
            entriesOf ["attack", "intro"] @?= [Right "attack", Right "intro"]

        , testCase "a bracketed run is one entry, brackets dropped" $
            entriesOf [":{", "h = here", "goto h", ":}"]
              @?= [Right "h = here\ngoto h"]

        , testCase "and the lines around it are their own" $
            entriesOf ["attack", ":{", "a", "b", ":}", "qed"]
              @?= [Right "attack", Right "a\nb", Right "qed"]

          -- A colon command inside the brackets is just a line of the entry;
          -- outside it, it is a command as it always was.
        , testCase "a colon command is an entry like any other" $
            entriesOf [":where"] @?= [Right ":where"]

          -- **The brackets must stand alone**, which is GHCi's rule too, so a
          -- line that merely begins with them is ordinary text.
        , testCase "an opener must be alone on its line" $
            entriesOf [":{ h = here"] @?= [Right ":{ h = here"]

        , testCase "surrounding spaces are still an opener" $
            entriesOf ["  :{  ", "a", ":}"] @?= [Right "a"]

        , testCase "an empty bracket is an empty entry" $
            entriesOf [":{", ":}"] @?= [Right ""]

          -- Input that ends inside one is a problem, not a silent entry.
        , testCase "input that ends inside one is reported" $
            entriesOf [":{", "a"] @?= [Left unclosedEntry]

          -- **A trailing @;@ is a complete entry now** (MS5 phase 78). Phase 70
          -- read one as /more is coming/; with the bracket doing that job, it
          -- had to mean something, and a parse error naming the @}@ layout
          -- inserted at @0:0@ is not it.
        , testCase "a trailing semicolon is a complete entry" $
            snd (say [":theorem t : Type\8320", "h = here ;"])
              @?= Ran [] [] Completed
        ]
    , testGroup
        "the second matching instruction"
        -- **MS5 phase 71, his §1.1.** Different input from ':matches' — a type,
        -- not the development — different relation, different consumer. No pair.
        [ testCase ":accepts finds a rule by its parameter" $
            fittingNames (snd (command withRules ":accepts Surface"))
              @?= ["elaborate", "intro-binders", "enter-binders", "spine-arguments"]
          -- **One thing in the shipped base returns a @Core@ since MS5 phase
          -- 89** — @fresh-universe@, which stopped being an op and became a
          -- function over @fresh-level@ and @universe-at@. Before that nothing
          -- did, and this case asserted an empty listing.
        , testCase ":produces finds the one callable that gives a Core" $
            case snd (command withRules ":produces Core") of
              Fitting v _ rows -> do
                v @?= "gives"
                [ n | (GlobalName n, _, _, _) <- rows ] @?= ["fresh-universe"]
              other -> assertFailure ("expected a listing, got " ++ show other)
          -- **It lists rules and functions both** (his ruling), and the two are
          -- told apart in the row rather than in two commands.
        , testCase "a rule is marked as one" $
            case snd (command withRules ":accepts Surface") of
              Fitting _ _ ((_, _, isRule, _) : _) -> isRule @?= True
              other -> assertFailure ("expected a listing, got " ++ show other)
        , testCase "a type that is not one is refused" $
            case snd (command withRules ":accepts Nonsense") of
              LineRefused _ -> pure ()
              other -> assertFailure ("expected a refusal, got " ++ show other)
        ]
    , testGroup
        "views"
        [ testCase ":core resolves a term" $
            case snd (command withRules ":core λ (x : Type₀) -> x") of
              Rendered _ -> pure ()
              other      -> assertFailure ("expected Rendered, got " ++ show other)
        , testCase ":core reports a scope error" $
            case snd (command withRules ":core y") of
              Failed _ -> pure ()
              other    -> assertFailure ("expected Failed, got " ++ show other)
        , testCase ":core sees what the development binds" $
            -- The whole reason a view command takes the development's context.
            case snd (say ["assume \"A\" ⌜ Type₀ ⌝", ":core A"]) of
              Rendered _ -> pure ()
              other      -> assertFailure ("expected Rendered, got " ++ show other)
        , testCase ":dev resolves a development" $
            case snd (command withRules ":dev let ? h : Type₀ in h") of
              RenderedDev _ -> pure ()
              other         -> assertFailure ("expected RenderedDev, got " ++ show other)
        , testCase ":core rejects a hole, which is development-only" $
            case snd (command withRules ":core let ? h : Type₀ in h") of
              Failed _ -> pure ()
              other    -> assertFailure ("expected Failed, got " ++ show other)
        , testCase ":show renders the development the machine holds" $
            case snd (say ["assume \"A\" ⌜ Type₀ ⌝", ":show"]) of
              Shown c | Under (Assume _ (Ident "A") _) _ <- rebuild c -> pure ()
              other -> assertFailure ("expected the assumption, got " ++ show other)
        ]
    , testGroup
        "commands that run"
        [ testCase "assume changes the development, through the machine" $
            case devOf (fst (say ["assume \"A\" ⌜ Type₀ ⌝"])) of
              Under (Assume _ (Ident "A") _) (Under Claim {} (Trailing _)) -> pure ()
              other -> assertFailure ("wrong shape: " ++ show other)
        , -- **And says nothing** (MS5 phase 62b). @assume@ is an op and an op is
          -- silent: @attack@, @intro@ and @try-core@ always were. The
          -- @"assumed A"@ line came from the driver's own @compile@, which
          -- built a @Say@ after the op because it was building the program by
          -- hand; there is no such place any more.
          testCase "and says nothing, as every other tactic does" $
            snd (say ["assume \"A\" ⌜ Type₀ ⌝"]) @?= Ran [] [] Completed
        , -- **The asking form is a rule now** — @rule assume ty@ in the base —
          -- so this is one clause of @assume@ picked by arity, not a second
          -- instruction sequence chosen by the driver. It still says what it
          -- did, because the rule's body ends in a @say@.
          testCase "a nameless assume asks for the name" $
            case snd (say ["assume ⌜ Type₀ ⌝"]) of
              Ran [] _ (Waiting (Question p k)) ->
                (p, k) @?= ("name for the assumption?", AName)
              other -> assertFailure ("expected a question, got " ++ show other)
        , testCase "the answer is used, and the message is built from it" $
            let (s, _) = say ["assume ⌜ Type₀ ⌝"]
             in snd (answer s "B") @?= Ran ["assumed B"] [] Completed
        , testCase "and the binder carries the answered name" $
            let (s, _) = say ["assume ⌜ Type₀ ⌝"]
             in case devOf (fst (answer s "B")) of
                  Under (Assume _ (Ident "B") _) _ -> pure ()
                  other -> assertFailure ("wrong shape: " ++ show other)
        , testCase "an answer that is not a name gets stuck, and keeps the machine" $
            let (s, _) = say ["assume ⌜ Type₀ ⌝"]
             in snd (answer s "let") @?= Ran [] [] (Halted (NotAnIdentifier "let"))
        , testCase "answering when nothing was asked is refused" $
            snd (answer newSession "B") @?= Rejected NotAsking
        , -- With nothing after it the word is an arity no op and no rule has,
          -- so it is a call nothing answers (MS5 phase 62b) — refused before it
          -- runs since phase 92, naming the arities that exist: the rule
          -- that asks for the name, and the op that is given one.
          testCase "assume needs a type" $
            snd (command withRules "assume")
              @?= EntryMistyped [Undefined (InBody (GlobalName "entry") 0) "assume" 0 [1, 2]]
        , testCase "assume resolves its type in the development's context" $
            case snd (say ["assume \"A\" ⌜ Type₀ ⌝", "assume \"x\" ⌜ A ⌝"]) of
              Ran [] _ Completed -> pure ()
              other -> assertFailure ("expected success, got " ++ show other)
        ]
    , testGroup
        "the goal"
        [ testCase ":goal claims a new one, in context" $
            case snd (say ["assume \"A\" ⌜ Type₀ ⌝", ":goal A -> A"]) of
              Shown c
                | Under Assume {} (Under (Claim _ (Ident "goal") _) (Trailing _)) <-
                    rebuild c -> pure ()
              other -> assertFailure ("wrong shape: " ++ show other)
        , testCase ":goal replaces the old one rather than stacking" $
            case devOf (fst (say [":goal Type₀", ":goal Type₁"])) of
              Under (Claim _ _ ty) (Trailing _) -> ty @?= Universe (levelOfNat 1)
              other -> assertFailure ("wrong shape: " ++ show other)
        , testCase "an assumption made later still lands outside the goal" $
            case devOf (fst (say [":goal Type₀", "assume \"A\" ⌜ Type₀ ⌝"])) of
              Under Assume {} (Under Claim {} (Trailing _)) -> pure ()
              other -> assertFailure ("wrong shape: " ++ show other)
        ]
      -- **@:infer ‹surface›@ elaborates and then puts the development back**
      -- (MS4 phase 43). @test\/golden\/surface-inference.golden@ shows the same
      -- thing through @:show@; this asks the development itself, which is
      -- different code from the code that maintains it (phase 5's lesson).
    , testGroup
        "inferring a surface term leaves nothing behind"
        [ testCase "the development is exactly as it was" $
            devOf (fst (say [natCommand, ":theorem t : Nat", ":infer succ zero"]))
              @?= devOf (fst (say [natCommand, ":theorem t : Nat"]))
        , testCase "and so it is when the term does not elaborate" $
            devOf (fst (say [natCommand, ":theorem t : Nat", ":infer nosuchthing"]))
              @?= devOf (fst (say [natCommand, ":theorem t : Nat"]))
          -- **A bare argument is surface, corners are core**, and the two
          -- answers agree **up to conversion, not syntactically**: the surface
          -- one is read off the hole the elaboration solved, so it is whnf\'d to
          -- see past the hole\'s own variable and comes back as the saturated
          -- former where the core path stops at the wrapper. Both print @Nat@.
        , testCase "a bare argument is surface, corners are core" $
            case ( snd (say [natCommand, ":infer succ zero"])
                 , snd (say [natCommand, ":infer ⌜ succ zero ⌝"])
                 ) of
              (InferredSurface _ a, Inferred _ b) ->
                case convert (globals (sessionMachine (fst (say [natCommand])))) [] 0 a b of
                  (Nothing, _, _)  -> pure ()
                  (Just why, _, _) -> assertFailure (show why)
              (x, y) -> assertFailure (show x ++ " / " ++ show y)
        ]
    , testGroup
        "declarations"
        [ testCase "data says what it declared" $
            snd (say [natCommand]) @?= Ran ["declared Nat"] [] Completed
        , testCase "and the globals hold it afterwards" $
            declaredIn (fst (say [natCommand])) "Nat" @?= True
        , testCase "so do the names it generated" $
            map (declaredIn (fst (say [natCommand]))) ["zero", "succ"] @?= [True, True]
        , testCase "the development is untouched: globals are not Development (§7.4)" $
            devOf (fst (say [natCommand])) @?= devOf newSession
        , testCase "data needs an argument" $
            snd (command withRules "data") @?= Rejected (MissingArgument "data")
        , testCase "a declaration that does not fit the form is a syntax error" $
            case snd (command withRules "data T : Type\8320 where { c }") of
              Failed _ -> pure ()
              other    -> assertFailure ("expected Failed, got " ++ show other)
        , testCase "a declaration the checker refuses stops the run" $
            snd (say [natCommand, "data T : Type\8320 where { c : (T -> T) -> T }"])
              @?= Ran [] [] (Refused (NotStrictlyPositive (GlobalName "c") (Ident "x")))
        , testCase "and writes nothing" $
            declaredIn (fst (say [natCommand, "data T : Type\8320 where { c : (T -> T) -> T }"])) "T"
              @?= False
        , testCase "while what was already declared survives it" $
            declaredIn (fst (say [natCommand, "data T : Type\8320 where { c : (T -> T) -> T }"])) "Nat"
              @?= True
        , testCase "a refused declaration abandons the rest of the program" $
            case fst (say [natCommand, "data T : Type\8320 where { c : (T -> T) -> T }", ":run"]) of
              s' -> snd (command s' ":run") @?= Ran [] [] Completed
        , testCase ":show ‹datatype› is the declaration" $
            case snd (say [natCommand, ":show Nat"]) of
              ShownData _ -> pure ()
              other       -> assertFailure ("expected ShownData, got " ++ show other)
        , testCase ":show ‹former› is the generated wrapper, type and body" $
            case snd (say [natCommand, ":show succ"]) of
              ShownGlobal (GlobalName "succ") _ _ _ _ (Just _) -> pure ()
              other -> assertFailure ("expected ShownGlobal, got " ++ show other)
        , testCase "a global is in scope for an ordinary term" $
            case snd (say [natCommand, ":core succ zero"]) of
              Rendered _ -> pure ()
              other      -> assertFailure ("expected Rendered, got " ++ show other)
        , testCase "and can be assumed at" $
            snd (say [natCommand, "assume \"n\" ⌜ Nat ⌝"]) @?= Ran [] [] Completed
        , testCase "stepping installs the declaration before it pauses" $
            let s' = fst (say [":step on", natCommand])
             in declaredIn s' "Nat" @?= True
        , testCase "and the message is still to come" $
            snd (say [":step on", natCommand]) @?= Ran [] [] Paused
        ]
    , testGroup
        "stepping"
        [ -- **A line with a written term is two instructions now** (MS5 phase
          -- 62b): @assume "A" ⌜ Type₀ ⌝@ compiles to
          -- @⌜1⌝ = resolve-core ⌜ Type₀ ⌝ ; assume "A" ⌜1⌝@, which is what a
          -- rule body writes by hand. So the first pause is before the
          -- resolution and the second before the op — and that is the point of
          -- compiling the step in rather than resolving quietly in the driver
          -- (phase 61b: /a reader should be able to see which one it got/).
          testCase ":step on makes a command stop after one instruction" $
            case snd (say [":step on", "assume \"A\" ⌜ Type₀ ⌝"]) of
              Ran [] _ Paused -> pure ()
              other         -> assertFailure ("expected Paused, got " ++ show other)
        , testCase "and :step takes the next one" $
            case snd (say [":step on", "assume \"A\" ⌜ Type₀ ⌝", ":step"]) of
              Ran [] _ Paused -> pure ()
              other -> assertFailure ("expected a second pause, got " ++ show other)
        , testCase "and the one after that finishes it" $
            case snd (say [":step on", "assume \"A\" ⌜ Type₀ ⌝", ":step", ":step"]) of
              Ran [] _ Completed -> pure ()
              other -> assertFailure ("expected Completed, got " ++ show other)
        , testCase ":run finishes the program whatever the mode" $
            case snd (say [":step on", "assume \"A\" ⌜ Type₀ ⌝", ":run"]) of
              Ran [] _ Completed -> pure ()
              other -> assertFailure ("expected Completed, got " ++ show other)
        , testCase ":step off puts it back" $
            case snd (say [":step on", ":step off", "assume \"A\" ⌜ Type₀ ⌝"]) of
              Ran [] _ Completed -> pure ()
              other -> assertFailure ("expected Completed, got " ++ show other)
        , testCase "stepping is a session setting and does not touch the machine" $
            sessionStepping (fst (say [":step on"])) @?= True
        ]
    ]

-- | The names a @:accepts@ / @:produces@ listing came back with (MS5 phase 71).
fittingNames :: Response -> [String]
fittingNames r = case r of
  Fitting _ _ fs -> [ n | (GlobalName n, _, _, _) <- fs ]
  _              -> []
