-- | Commands: what they compile to, what they refuse, and where they leave the
-- session.
module Thena.DriverTests (tests) where

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
import Thena.Repl (unfinished)

-- | The names in a 'Fitting' listing, for the tests below.

import Thena.Ops (AnswerKind (..), partWords)
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
  , ":choices", ":goal", ":whnf", ":infer", ":load", ":bases", ":rules"
  , ":revalidate", ":extract", ":theorem", ":suspend", ":resume", ":abandon"
  , ":proofs", ":undo", ":convert", ":step", ":run"
  ]

-- | **Hand-written, and it had the same gaps as the list it checks** (MS4
-- phase 43): @declare@ and @quantify@ were missing from both, and @prove@ was
-- in both after phase 41 made it a rule rather than a command. A mirror that
-- shares the blind spot of what it mirrors cannot catch anything — which is the
-- argument for @ms3\/CLOSEOUT.md@ 26, not against having it.
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
            snd (command withRules "hello") @?= Ran [] (Halted (NoClauseMatched (GlobalName "hello") 0 []))
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
              @?= Ran ["ab"] Completed
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
              @?= Ran ["ok"] Completed
        ]
    , testGroup
        "an entry keeps reading while it cannot be finished"
        -- The trigger for a multi-line entry (MS5 phase 70). Indentation is what
        -- a continuation must LOOK like; this is what says one is coming.
        [ testCase "a trailing semicolon wants more" $
            unfinished "h = here ;" @?= True
        , testCase "an unclosed brace wants more" $
            unfinished "do {" @?= True
        , testCase "an unclosed bracket too" $
            unfinished "f [1," @?= True
        , testCase "a finished entry does not" $
            unfinished "h = here ; goto h" @?= False
        , testCase "a balanced block does not" $
            unfinished "do { attack }" @?= False
          -- Something the lexer cannot read is a syntax error and not a
          -- continuation, so the driver gets to report it.
        , testCase "and nor does something that will not lex" $
            unfinished "\"unterminated" @?= False
        ]
    , testGroup
        "the second matching instruction"
        -- **MS5 phase 71, his §1.1.** Different input from ':matches' — a type,
        -- not the development — different relation, different consumer. No pair.
        [ testCase ":accepts finds a rule by its parameter" $
            fittingNames (snd (command withRules ":accepts Surface"))
              @?= ["elaborate", "intro-binders", "enter-binders", "spine-arguments"]
          -- Nothing in the shipped base returns, so this is the honest answer
          -- rather than an empty listing with no explanation.
        , testCase ":produces says so when nothing does" $
            case snd (command withRules ":produces Core") of
              Fitting v _ [] -> v @?= "gives"
              other -> assertFailure ("expected an empty listing, got " ++ show other)
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
            snd (say ["assume \"A\" ⌜ Type₀ ⌝"]) @?= Ran [] Completed
        , -- **The asking form is a rule now** — @rule assume ty@ in the base —
          -- so this is one clause of @assume@ picked by arity, not a second
          -- instruction sequence chosen by the driver. It still says what it
          -- did, because the rule's body ends in a @say@.
          testCase "a nameless assume asks for the name" $
            case snd (say ["assume ⌜ Type₀ ⌝"]) of
              Ran [] (Waiting (Question p k)) ->
                (p, k) @?= ("name for the assumption?", AName)
              other -> assertFailure ("expected a question, got " ++ show other)
        , testCase "the answer is used, and the message is built from it" $
            let (s, _) = say ["assume ⌜ Type₀ ⌝"]
             in snd (answer s "B") @?= Ran ["assumed B"] Completed
        , testCase "and the binder carries the answered name" $
            let (s, _) = say ["assume ⌜ Type₀ ⌝"]
             in case devOf (fst (answer s "B")) of
                  Under (Assume _ (Ident "B") _) _ -> pure ()
                  other -> assertFailure ("wrong shape: " ++ show other)
        , testCase "an answer that is not a name gets stuck, and keeps the machine" $
            let (s, _) = say ["assume ⌜ Type₀ ⌝"]
             in snd (answer s "let") @?= Ran [] (Halted (NotAnIdentifier "let"))
        , testCase "answering when nothing was asked is refused" $
            snd (answer newSession "B") @?= Rejected NotAsking
        , -- With nothing after it the word is an arity no op and no rule has,
          -- so it is a call that finds no clause — which is what any other
          -- word with no clause does (MS5 phase 62b).
          testCase "assume needs a type" $
            case snd (command withRules "assume") of
              Ran [] (Halted (NoClauseMatched (GlobalName "assume") 0 as)) -> as @?= [1]
              other -> assertFailure ("expected no clause, got " ++ show other)
        , testCase "assume resolves its type in the development's context" $
            case snd (say ["assume \"A\" ⌜ Type₀ ⌝", "assume \"x\" ⌜ A ⌝"]) of
              Ran [] Completed -> pure ()
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
            snd (say [natCommand]) @?= Ran ["declared Nat"] Completed
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
              @?= Ran [] (Refused (NotStrictlyPositive (GlobalName "c") (Ident "x")))
        , testCase "and writes nothing" $
            declaredIn (fst (say [natCommand, "data T : Type\8320 where { c : (T -> T) -> T }"])) "T"
              @?= False
        , testCase "while what was already declared survives it" $
            declaredIn (fst (say [natCommand, "data T : Type\8320 where { c : (T -> T) -> T }"])) "Nat"
              @?= True
        , testCase "a refused declaration abandons the rest of the program" $
            case fst (say [natCommand, "data T : Type\8320 where { c : (T -> T) -> T }", ":run"]) of
              s' -> snd (command s' ":run") @?= Ran [] Completed
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
            snd (say [natCommand, "assume \"n\" ⌜ Nat ⌝"]) @?= Ran [] Completed
        , testCase "stepping installs the declaration before it pauses" $
            let s' = fst (say [":step on", natCommand])
             in declaredIn s' "Nat" @?= True
        , testCase "and the message is still to come" $
            snd (say [":step on", natCommand]) @?= Ran [] Paused
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
              Ran [] Paused -> pure ()
              other         -> assertFailure ("expected Paused, got " ++ show other)
        , testCase "and :step takes the next one" $
            case snd (say [":step on", "assume \"A\" ⌜ Type₀ ⌝", ":step"]) of
              Ran [] Paused -> pure ()
              other -> assertFailure ("expected a second pause, got " ++ show other)
        , testCase "and the one after that finishes it" $
            case snd (say [":step on", "assume \"A\" ⌜ Type₀ ⌝", ":step", ":step"]) of
              Ran [] Completed -> pure ()
              other -> assertFailure ("expected Completed, got " ++ show other)
        , testCase ":run finishes the program whatever the mode" $
            case snd (say [":step on", "assume \"A\" ⌜ Type₀ ⌝", ":run"]) of
              Ran [] Completed -> pure ()
              other -> assertFailure ("expected Completed, got " ++ show other)
        , testCase ":step off puts it back" $
            case snd (say [":step on", ":step off", "assume \"A\" ⌜ Type₀ ⌝"]) of
              Ran [] Completed -> pure ()
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
