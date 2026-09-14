-- | Inference over @instral@ (MS5 phase 66c).
--
-- **Two halves, and the first is the phase's done-when**: the shipped rule base
-- infers, and what it infers is written out here so a later phase cannot move a
-- signature quietly. The second half is one file per way a program can be
-- ill typed, written as a rule-base file and loaded — which is how a user meets
-- it, and which also checks that a bad program is refused rather than installed.
module Thena.InstralInferTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

import Thena.Core.Term (GlobalName (..))
import Thena.Driver (Response (..), RuleFileError (..), Session, Stop (..), command, loadRuleBases, newSession)
import Thena.Engine (Machine (..))
import Thena.Driver (Session (..))
import Thena.Instral.Infer
  ( InstralTypeError (..)
  , Site (..)
  , inferProgram
  , renderInstralTypeError
  )
import Thena.Instral.Type (Signature (..), Ty (..), renderSignature)
import Thena.Ops (Instr (..), Op (..), Operand (..), Pattern (..), Rule (..), Value (..))
import Thena.Errors (SyntaxError (..))
import Thena.Instral.Grammar (GrammarError (..))
import Thena.Syntax.Parser (ParseError (..))
import Thena.Rules (RuleBase (..), RuleError (..))
import Data.List (isInfixOf)
import Thena.Repl (renderCursor, transcriptFrom)
import Thena.Standard (expectedBase, expectedStandard)

tests :: TestTree
tests =
  testGroup
    "Thena.Instral.Infer"
    [ shippedBase
    , illTyped
    , wellTyped
    , blockReturn
    , annotations
    , noKeyword
    , generalisation
    , annotatedLocals
    , surfaceBlockTyping
    , functionsAreFunctions
    , patternTyping
    , bareWordRightOfEquals
    , destructuringRuns
    , spliceTemplates
    , blockBodies
    , badSignatures
    , functions
    , lambdas
    , objectLanguages
    ]

-- --------------------------------------------------------------------------
-- Generalisation, per strongly connected component (MS5 phase 76)
-- --------------------------------------------------------------------------

-- | **His ruling, 2026-09-13**: /"do the SCC and take the type system all the
-- way to HM."/
--
-- A top-level callable is generalised once its component is solved, so a later
-- caller instantiates it; a local is not, which is /Let Should Not Be
-- Generalised/ and GHC's @MonoLocalBinds@ — **his agreement, the same day**.
-- The pair of tests below is the whole distinction, and neither passes without
-- the other side being right.
generalisation :: TestTree
generalisation =
  testGroup
    "a top-level callable is generalised, a local is not"
    [ -- The payoff, at its smallest: one global used at two types, no signature.
      loads "a global used at two types is fine"
        "idf x = do { return x }\n\
        \rule go :- then h = here ; a = idf h ; n = fresh-name \"x\" ; b = idf n"

      -- …and the same shape one level in is refused, which is /Let Should Not
      -- Be Generalised/ and GHC's @MonoLocalBinds@ — his agreement, 2026-09-13.
    , clashes "a local used at two types is not"
        "rule go :- then g = \\ z -> do { return z } ; h = here ; a = g h\n\
        \     ; n = fresh-name \"x\" ; b = g n"

      -- **A mutually recursive pair is ONE component**, so within it the two
      -- share their variables: calling @oddish@ at a Core and at a Name from
      -- inside @evenish@ is a clash. That is the monomorphism Hindley-Milner
      -- has and this phase did not remove.
    , clashes "and inside one component nothing is generalised either"
        "evenish x = do { h = here ; a = oddish h ; n = fresh-name \"q\"\n\
        \               ; b = oddish n ; return x }\n\
        \oddish y = do { c = evenish y ; return y }"

      -- **…but the component as a whole is**, so two uses from OUTSIDE it are
      -- independent. This is the half that would be wrong if the group were
      -- generalised one callable at a time, or not at all.
    , loads "…while outside it, the whole component is"
        "evenish x = do { n = fresh-name \"q\" ; a = oddish n ; return x }\n\
        \oddish y = do { return y }\n\
        \rule go :- then h = here ; a = evenish h ; m = fresh-name \"x\" ; b = evenish m"

      -- **Errors are still reported down the file.** The walking order is the
      -- call graph\'s now, so @zzz@ — a leaf — is inferred before the @aaa@ that
      -- calls it, and without a sort its mistake would be printed first.
    , testCase "and a file's mistakes are reported in the order they were written" $
        case load "rule aaa :- then h = here ; say h ; zzz\n\
                  \rule zzz :- then g = here ; say g" of
          BasesIllTyped [Clash (InBody a _) _ _, Clash (InBody z _) _ _] ->
            (a, z) @?= (GlobalName "aaa", GlobalName "zzz")
          other -> assertFailure ("expected two clashes, got " ++ show other)
    ]
  where
    loads what src = testCase what $ case load src of
      BasesLoaded _ -> pure ()
      other         -> assertFailure ("expected a load, got " ++ show other)

    clashes what src = testCase what $ case load src of
      BasesIllTyped (Clash{} : _) -> pure ()
      other -> assertFailure ("expected a clash, got " ++ show other)

-- --------------------------------------------------------------------------
-- Annotated locals (MS5 phase 77)
-- --------------------------------------------------------------------------

-- | **@n : Ty@ on a line of its own, above the binding it is about.**
--
-- His, 2026-09-13: /"When I want poly let-bound (in expressions) or poly local
-- variables in rules, I will write annotation."/ So an annotation does not
-- merely constrain a local — it makes it a **scheme**, instantiated at every
-- use, which is what a declared top-level signature already did one level up.
--
-- The spelling is the same one level up too, which is the point: a signature is
-- @f : Ty@ in column 1 since phase 74, and this is that line indented.
annotatedLocals :: TestTree
annotatedLocals =
  testGroup
    "a local may be annotated, and then it is polymorphic"
    [ loads "an annotated local is usable at two types"
        "rule go :- then\n\
        \  g : a -> a\n\
        \  g = \\ z -> do { return z }\n\
        \  h = here\n\
        \  x = g h\n\
        \  n = fresh-name \"q\"\n\
        \  y = g n"

      -- …and the same body without the annotation is the monomorphic one.
    , clashes "…where the same local without one is not"
        "rule go :- then\n\
        \  g = \\ z -> do { return z }\n\
        \  h = here\n\
        \  x = g h\n\
        \  n = fresh-name \"q\"\n\
        \  y = g n"

      -- **An annotation is checked, not believed** — the same
      -- instantiate-then-verify a top-level signature gets, so a promise the
      -- binding does not keep is refused.
    , testCase "an annotation the binding does not keep is refused" $
        case load "rule go :- then\n\
                  \  g : a -> a\n\
                  \  g = \\ z -> do { return (concat z \"!\") }\n\
                  \  h = here\n\
                  \  x = g h" of
          BasesIllTyped (AnnotationTooGeneral{} : _) -> pure ()
          other -> assertFailure ("expected a refusal, got " ++ show other)

      -- **A concrete annotation is an ordinary constraint**, and wrong is wrong.
    , testCase "and a concrete one still has to be true" $
        case load "rule go :- then\n\
                  \  h : Name\n\
                  \  h = here" of
          BasesIllTyped (Clash{} : _) -> pure ()
          other -> assertFailure ("expected a clash, got " ++ show other)

      -- **An annotation about nothing is a typo, most often a renamed line.**
    , testCase "an annotation with no binding after it is refused" $
        case loadRaw "rule base a where\nrule go :- then\n  g : a -> a\n  say \"hi\"\n" of
          RuleFileRefused _ (RuleIllFormed es)
            | [AnnotationWithoutBinding _ _ "g"] <- es -> pure ()
          other -> assertFailure ("expected a refusal, got " ++ show other)
    ]
  where
    loads what src = testCase what $ case load src of
      BasesLoaded _ -> pure ()
      other         -> assertFailure ("expected a load, got " ++ show other)

    clashes what src = testCase what $ case load src of
      BasesIllTyped (Clash{} : _) -> pure ()
      other -> assertFailure ("expected a clash, got " ++ show other)

    loadRaw src = snd (loadRuleBases newSession [("a.thena.rules", src)])

-- --------------------------------------------------------------------------
-- A do block in a surface term is typed (MS5 phase 79)
-- --------------------------------------------------------------------------

-- | **@ms5\/CLOSEOUT.md@ 20, closed.**
--
-- A @do@ block written inside a surface term is @instral@, and until this phase
-- it was the only @instral@ nothing checked: 'Thena.Ops.Play' resolved it as it
-- ran. It is resolved, validated and typed when the term it sits in is read
-- now — in a rule file here, and at the prompt, in a module and in a
-- @declare@ (@DriverTests@ drives those).
--
-- **The block is typed as an extra body, not as a callable.** Nothing can call
-- one, so it goes to 'inferProgram' beside the callables rather than among
-- them.
surfaceBlockTyping :: TestTree
surfaceBlockTyping =
  testGroup
    "a do block inside a surface literal is typed with the file"
    [ loads "a good one loads"
        "rule go :- then call elaborate surface`do { u = fresh-universe ; fill u ; solve }`"

    , testCase "a bad one is refused when the file loads" $
        case load "rule go :- then call elaborate surface`do { say 3 }`" of
          BasesIllTyped (Clash{} : _) -> pure ()
          other -> assertFailure ("expected a type error, got " ++ show other)

      -- **A block inside a block.** A block's own instructions may hold another
      -- surface literal, and 'Thena.Rules.surfaceBlocks' recurses for it.
    , testCase "and so is one nested inside another" $
        case load "rule go :- then call elaborate surface`do { call elaborate surface\\`do { say 3 }\\` }`" of
          BasesIllTyped (Clash{} : _) -> pure ()
          other -> assertFailure ("expected a type error, got " ++ show other)

      -- A @return@ in one is refused at resolution, before typing.
    , testCase "a return in one is refused" $
        case loadRaw "rule base b where\nrule go :- then call elaborate surface`do { u = fresh-universe ; return u }`\n" of
          RuleFileRefused _ (RuleIllFormed es)
            | [ReturnInSurfaceBlock _ _] <- es -> pure ()
          other -> assertFailure ("expected a refusal, got " ++ show other)
    ]
  where
    loads what src = testCase what $ case load src of
      BasesLoaded _ -> pure ()
      other         -> assertFailure ("expected a load, got " ++ show other)

    loadRaw src = snd (loadRuleBases newSession [("b.thena.rules", src)])

-- --------------------------------------------------------------------------
-- A function is called, a rule is searched (MS5 phase 80)
-- --------------------------------------------------------------------------

-- | **His ruling, 2026-09-13.** A rule with several clauses is a search: the
-- engine builds a choice point and tries each clause that matches. A function
-- is not — it is called, it enters one clause, and it stays there.
--
-- **A function therefore has one clause until there are patterns**, because a
-- second is reached only where something tells the two apart and nothing can.
-- Before this phase it was reached by the FIRST clause failing, which is a
-- rule\'s behaviour wearing a function\'s spelling.
--
-- **Refusing the second clause is the whole change.** "Thena.Engine" decides
-- @Choice@ against @Call@ by @hasNext@ alone and never asks what kind of
-- callable it has, so with one clause it already builds a @Call@ frame — which
-- is why the last two cases here pass without a line of engine code.
functionsAreFunctions :: TestTree
functionsAreFunctions =
  testGroup
    "a function has one clause"
    [ testCase "a second clause at the same arity is refused" $
        case loadRaw "rule base f where\nf x = concat x \"a\"\nf x = concat x \"b\"\n" of
          RuleFileRefused _ (RuleIllFormed es)
            | [FunctionClauseUnreachable "f" 1] <- es -> pure ()
          other -> assertFailure ("expected a refusal, got " ++ show other)

      -- **A different arity is a different callable**, which is how dispatch
      -- has always read a name, so these are two functions and not two clauses.
    , loads "…but another arity is another function"
        "f x = concat x \"a\"\nf x y = concat x y"

      -- **A rule is unchanged**: several clauses, searched.
    , loads "…and a rule may still have as many clauses as it likes"
        "rule g :- when focus-is-hole then prove\nrule g :- when focus-is-guess then solve"

      -- **The positive half, and it needed no engine code.** A call to a
      -- function leaves the stack with no live decision on it — before the
      -- phase, a two-clause one announced @chose@, was listed by @:choices@ and
      -- was re-entered by @retry@, so the view whose job is /the live decisions
      -- in your proof/ listed a call to a string function among them.
    , testCase "and calling one leaves no choice point" $
        choicesAfter "twice x = concat x x\nrule go :- then m = twice \"a\" ; say m"
          @?= Just []

      -- ----------------------------------------------------------------
      -- MS5 phase 82 — patterns narrow the refusal above, and make the
      -- searched/called split something the code has to do rather than
      -- something that fell out of a function having one clause.
      -- ----------------------------------------------------------------

      -- **The lifting.** The paragraph above says /with no head and no
      -- patterns, nothing can tell two clauses apart/. There are patterns now.
    , loads "a second clause IS admitted when the first is refutable"
        "size [] = \"empty\"\nsize [_, ..._] = \"many\""

      -- …and the refusal is still there, narrowed to the case it was about.
    , testCase "…and still refused when the first matches everything" $
        case loadRaw "rule base f where\nf x = concat x \"a\"\nf [] = \"b\"\n" of
          RuleFileRefused _ (RuleIllFormed es)
            | [FunctionClauseUnreachable "f" 1] <- es -> pure ()
          other -> assertFailure ("expected a refusal, got " ++ show other)

      -- **A function is CALLED**: first match, no decision left standing.
      -- Before this phase 'Thena.Rules.clauses' offered every matching clause
      -- and the engine built a @Choice@ over them by @hasNext@ alone, which is
      -- exactly the behaviour phase 80 removed, arriving again by another road.
    , testCase "a multi-clause function takes the first match and leaves nothing" $
        choicesAfter (sizeBase ++ "rule go :- then m = size [\"a\"] ; say m")
          @?= Just []

    , testCase "…and where two clauses overlap, the FIRST one runs" $
        ranBy (sizeBase ++ "rule go :- then m = size [\"a\"] ; say m")
          @?= Just ["one"]

    , testCase "…while a value only the second matches reaches the second" $
        ranBy (sizeBase ++ "rule go :- then m = size [\"a\", \"b\"] ; say m")
          @?= Just ["many"]

      -- **A RULE is searched**, with the very same patterns — which is the
      -- split made visible. @retry@ reaching the second clause is what a
      -- function must not do and a rule must.
    , testCase "a multi-clause rule with patterns still builds a choice point" $
        (length <$> choicesAfter
           ("rule pick [a, ..._] :- then say a\n"
              ++ "rule pick x :- then say \"fallback\"\n"
              ++ "rule go :- then pick [\"one\"]"))
          @?= Just 1
    ]
  where
    loads what src = testCase what $ case load src of
      BasesLoaded _ -> pure ()
      other         -> assertFailure ("expected a load, got " ++ show other)

    loadRaw src = snd (loadRuleBases newSession [("f.thena.rules", src)])

    -- **Two clauses that OVERLAP**, and that is the whole point of the
    -- fixture: @["a"]@ matches both @[_]@ and @[_, ..._]@. A non-overlapping
    -- pair would leave 'Thena.Rules.clauses' with one candidate whatever it
    -- did, so it would say nothing about first-match — and it did not: the
    -- first draft of these cases used @[]@ against @[]@ / @[_, ..._]@ and
    -- survived deleting the @take 1@.
    sizeBase = "size [_] = \"one\"\nsize [_, ..._] = \"many\"\n"

    -- Load, run @go@, and report what the machine said.
    ranBy src =
      let s0 = fst (loadRuleBases newSession [("f.thena.rules", "rule base f where\n" ++ src ++ "\n")])
       in case snd (command s0 "go") of
            Ran ms _ -> Just ms
            _        -> Nothing

    -- Load, run @go@, and ask what decisions are left standing.
    choicesAfter src =
      let s0 = fst (loadRuleBases newSession [("f.thena.rules", "rule base f where\n" ++ src ++ "\n")])
       in case snd (command (fst (command s0 "go")) ":choices") of
            Choices cs -> Just cs
            _          -> Nothing

-- --------------------------------------------------------------------------
-- Destructuring in a body (MS5 phase 84 — stage d)
-- --------------------------------------------------------------------------

-- | **@(x, y) = some-rule@**, and what happens when it does not fit.
--
-- **His ruling is the whole design:** a refutable pattern that does not match is
-- a __failure__ — *"you write for the happy path and let it fail"* — so in a
-- rule it backtracks like any other failure and in a function it is the
-- caller\'s, as in Haskell. The two halves are asserted separately below,
-- because they are two different mechanisms reaching the same ruling.
destructuringRuns :: TestTree
destructuringRuns =
  testGroup
    "destructuring a binding"
    [ testCase "a pair is taken apart and both halves are bound" $
        ranBy (pairs ++ "rule go :- then p = mk \"l\" \"r\" ; (x, y) = p ; m = concat x y ; say m")
          @?= Just ["lr"]

    , testCase "a list pattern binds the head and the rest" $
        ranBy (lists ++ "rule go :- then [a, ...r] = three ; say a ; [b, ..._] = r ; say b")
          @?= Just ["alpha", "beta"]

      -- The destination of a CALL is a pattern too, so the answer is taken
      -- apart where it lands rather than in a following line.
    , testCase "a call's answer is destructured where it lands" $
        ranBy (pairs ++ "rule go :- then (u, v) = mk \"U\" \"V\" ; say v")
          @?= Just ["V"]

    , testCase "a wildcard runs the op and discards it" $
        ranBy (pairs ++ "rule go :- then _ = mk \"a\" \"b\" ; say \"discarded\"")
          @?= Just ["discarded"]

      -- **HIS RULING, the rule half**: the first clause's @[only]@ refuses a
      -- two-element list, and that is an ordinary failure, so the search takes
      -- the second clause.
      -- **The announcement is asserted, not just the answer.** §1 asks that
      -- search be visible, and @backtracking to@ is the evidence that the
      -- refusal went through the ordinary failure path rather than being
      -- special-cased into a skip.
    , testCase "a refused pattern backtracks to the next clause of a rule" $
        ranBy (lists
                 ++ "rule go :- then xs = three ; [only] = xs ; say only\n"
                 ++ "rule go :- then xs = three ; [a, b, c] = xs ; say c")
          @?= Just ["chose 1: go", "backtracking to 1: go", "gamma"]

      -- **…and the function half**: one clause, no head, nothing to search, so
      -- the refusal is the answer.
    , testCase "…and in a function it is the caller's failure" $
        stoppedBy ("single [a] = a\nrule go :- then m = single [\"x\", \"y\"] ; say m")

      -- The binding's own refusal, where nothing is left to backtrack into.
    , testCase "a refused binding with no alternative stops the command" $
        stoppedBy (lists ++ "rule go :- then xs = three ; [only] = xs ; say only")

      -- **A binding's pattern is TYPED, at load, against what the op leaves.**
      -- The same 'patternCtx' a parameter gets — a binding and a parameter ask
      -- the same question of a pattern, so they get the same answer from the
      -- same code, and this is what says so.
      -- **Nothing downstream uses @x@**, deliberately. The first draft ended
      -- the body with @say x@ and passed with the typing of the pattern
      -- disabled — the clash it was seeing came from @say@ wanting a String,
      -- not from the list pattern. A mutation found that; the fixture now has
      -- no second reason to fail.
    , testCase "a pattern that cannot fit the op's result is a clash" $
        clashAt (pairs ++ "rule go :- then p = mk \"l\" \"r\" ; [x] = p ; prove")

      -- **An ASK's answer lands through the pattern too**, and this is the one
      -- shape that can tell the difference: a compound pattern is refused by
      -- the type checker (an @ask@ answers with text), so only a literal can
      -- refuse at run time. **A refusal leaves the machine exactly as it was**,
      -- which for an interaction means the prompt comes back rather than the
      -- command failing on the user's behalf — the right answer for a question,
      -- and the opposite of what a binding in a body does.
      --
      -- Written because a mutation survived without it: bypassing the match
      -- here changed nothing any test could see.
    , testCase "an ask whose answer does not match the pattern asks again" $
        -- **The COUNT is the assertion.** A first draft asked only whether the
        -- prompt and the confirmation appeared, and a mutation that skipped the
        -- match passed it: with the match skipped the wrong answer is accepted,
        -- so the prompt appears once and the confirmation still appears. Two
        -- prompts is the only thing that says the refusal happened.
        asking [ "confirm", "no", "yes" ]
          "rule confirm :- then \"yes\" = ask \"say yes: \" text ; say \"confirmed\""
          2 "confirmed"

      -- **…and it is reported as an INSTRUCTION, not a parameter.** The first
      -- build of this phase reused the parameter site and said
      -- @go, parameter 1@ for a fault on the body's second line — which is
      -- @ms5\/CLOSEOUT.md@ 28's class exactly: a message must identify the
      -- thing it is about uniquely.
    , testCase "…reported against the instruction, not a parameter" $
        siteOf (pairs ++ "rule go :- then p = mk \"l\" \"r\" ; [x] = p ; prove")
          @?= Just (InBody (GlobalName "go") 1)
    ]
  where
    pairs = "mk a b = (a, b)\n"
    lists = "three = do { return [\"alpha\", \"beta\", \"gamma\"] }\n"

    run src = snd (command
      (fst (loadRuleBases newSession
              [("f.thena.rules", "rule base f where\n" ++ src ++ "\n")])) "go")

    ranBy src = case run src of
      Ran ms _ -> Just ms
      _        -> Nothing

    stoppedBy src = case run src of
      Ran _ (Halted _) -> pure ()
      other            -> assertFailure ("expected a halt, got " ++ show other)

    clashAt src = case load (src ++ "\n") of
      BasesIllTyped (Clash{} : _) -> pure ()
      other -> assertFailure ("expected a clash, got " ++ show other)

    siteOf src = case load (src ++ "\n") of
      BasesIllTyped (Clash si _ _ : _) -> Just si
      _                                -> Nothing

    -- Drive the prompt, and assert on the lines it printed rather than on the
    -- shape of the session: what is being tested is what the user sees.
    asking ls src prompts final =
      let s0 = fst (loadRuleBases newSession
                     [("f.thena.rules", "rule base f where\n" ++ src ++ "\n")])
          out = lines (transcriptFrom s0 ls)
          n   = length [ () | l <- out, "say yes: " `isInfixOf` l ]
       in do
            assertBool ("expected " ++ show prompts ++ " prompts in " ++ show out)
                       (n == prompts)
            assertBool (final ++ " not in " ++ show out)
                       (any (final `isInfixOf`) out)

-- --------------------------------------------------------------------------
-- What a bare word right of an = means (MS5 phase 82)
-- --------------------------------------------------------------------------

-- | **@id x = x@ gave /no rule is called x/, and that was a gap, not a
-- spelling.** His, 2026-09-14: *"@x@ is clearly just an occurrence. This needs
-- fixing, if this is what we are doing that's a massive gap."*
--
-- The right of an @=@ is the one place a bare word goes to
-- 'Thena.Rules.operation' instead of being read as an operand, so @= x@ asked
-- for @x@ applied to no arguments. That types as @TFun []@ —
-- @ms5\/CLOSEOUT.md@ 23's unwritable type — and the thunk leaked into a
-- user-facing message: @a string literal is a String or a Name, not -> String@.
--
-- **Phase 73 had already fixed the same defect one guard over**, for @true@ and
-- @false@, and its comment is the best statement of the class. This is that
-- guard with @bound@ in place of @reservedNames@.
--
-- **The rule is his, 2026-09-12, and "Thena.Engine" states it in a comment**:
-- /an op if one bears the name, else the local if one is bound, else a rule
-- call/. All three layers are asserted below, because until this phase the
-- middle one was implemented only for a closure.
bareWordRightOfEquals :: TestTree
bareWordRightOfEquals =
  testGroup
    "a bare word right of an ="
    [ testCase "a parameter is that value — the identity function" $
        ranBy "id x = x\nrule go :- then m = id \"hello\" ; say m"
          @?= Just ["hello"]

      -- **The design conversation's own first snippet**, which did not parse
      -- until this phase (@discussion\/pattern-matching.md@ §2).
    , testCase "…and so is a base case that hands a parameter back" $
        ranBy (firstOr ++ "rule go :- then m = firstOr \"d\" [] ; say m")
          @?= Just ["d"]

    , testCase "…while the other clause hands back an element" $
        ranBy (firstOr ++ "rule go :- then m = firstOr \"d\" [\"x\"] ; say m")
          @?= Just ["x"]

      -- **The local beats a callable of the same name** — his ruling, and
      -- @ms5\/CLOSEOUT.md@ 14 records the cost he took with it. Before this
      -- phase the base did not even load: the bare @helper@ was read as a call
      -- and the binding above it as a thunk.
    , testCase "a local beats a function of the same name" $
        ranBy ("helper = \"from the function\"\n"
                 ++ "rule go :- then helper = \"from the local\" ; m = helper ; say m")
          @?= Just ["from the local"]

      -- **…and an op beats the local**, which is the top of his three-way rule
      -- and is why the guard asks 'Thena.Rules.isOpWord'. @here@ answers with
      -- the focused component's variable, so binding a local of that name and
      -- reading it back gives a 'Thena.Instral.Type.TCore' and not the string.
    , clashes "an op word beats a local of the same name"
        "rule go :- then here = \"shadow\" ; m = here ; say m"

      -- The bottom of the rule, unchanged, and worth a regression guard: a word
      -- nothing binds is still a call.
    , testCase "a word that is not bound is still a call" $
        ranBy "helper = \"from the function\"\nrule go :- then m = helper ; say m"
          @?= Just ["from the function"]

      -- **A lambda's own parameters are in scope in its body**, which is the
      -- same question one nesting down and is answered by handing 'closure''s
      -- body the names its patterns bind. Without it @\\ x -> x@ is the
      -- identity spelled as a call to a rule called @x@.
    , testCase "a lambda's parameter is in scope in its own body" $
        ranBy "rule go :- then f = \\ x -> x ; m = f \"through a lambda\" ; say m"
          @?= Just ["through a lambda"]

      -- Phase 73's case, which this one generalises rather than replaces.
    , loads "true right of an = is still the literal"
        "rule go :- then b = true ; m = bool-text b ; say m"
    ]
  where
    firstOr = "firstOr d [] = d\nfirstOr _ [x, ..._] = x\n"

    ranBy src =
      let s0 = fst (loadRuleBases newSession [("f.thena.rules", "rule base f where\n" ++ src ++ "\n")])
       in case snd (command s0 "go") of
            Ran ms _ -> Just ms
            _        -> Nothing

    loads what src = testCase what $ case load (src ++ "\n") of
      BasesLoaded _ -> pure ()
      other         -> assertFailure ("expected a load, got " ++ show other)

    clashes what src = testCase what $ case load (src ++ "\n") of
      BasesIllTyped (Clash{} : _) -> pure ()
      other -> assertFailure ("expected a clash, got " ++ show other)

-- --------------------------------------------------------------------------
-- Patterns say what a parameter takes (MS5 phase 82)
-- --------------------------------------------------------------------------

-- | **A pattern says its parameter's type directly**, which is why stage a of
-- @discussion\/pattern-matching.md@ makes typing simpler rather than harder.
--
-- Before it, the only thing that could say a parameter's type was a head test
-- ('Thena.Rules.testTypes') or a written signature. A pattern says it as part of
-- saying what the clause is about, and — the half worth testing — it says it
-- __consistently across the clauses of one callable__, so two clauses that
-- disagree are a clash rather than a silently widened type.
patternTyping :: TestTree
patternTyping =
  testGroup
    "a pattern types its parameter"
    [ loads "a list pattern makes the parameter a list"
        "f [] = \"a\"\nf [_, ..._] = \"b\"\ng = do { m = f [\"x\"] ; return m }"

    , clashes "…so passing something else is a clash"
        "f [] = \"a\"\nf [_, ..._] = \"b\"\ng = do { m = f 3 ; return m }"

    , loads "a pair pattern makes it a pair"
        "swap (x, y) = do { return (y, x) }\ng = do { m = swap (1, 2) ; return m }"

    , clashes "…and a non-pair is a clash"
        "swap (x, y) = do { return (y, x) }\ng = do { m = swap 3 ; return m }"

    , loads "an option pattern makes it an option"
        "d none = \"n\"\nd (some _) = \"s\"\ng = do { o = some 1 ; m = d o ; return m }"

    , clashes "…and a bare value is a clash"
        "d none = \"n\"\nd (some _) = \"s\"\ng = do { m = d 1 ; return m }"

    , loads "a literal pattern pins the parameter to its own type"
        "yes true = \"y\"\nyes false = \"n\"\ng = do { m = yes true ; return m }"

    , clashes "…so another type there is a clash"
        "yes true = \"y\"\nyes false = \"n\"\ng = do { m = yes 1 ; return m }"

      -- **One element variable, not one per element.** @[a, ...rest]@ says /a
      -- list of the same thing/, so elements that disagree must clash — this is
      -- what a per-element fresh variable would silently allow.
    , clashes "every element of a list pattern shares one type"
        "f [a, b] = do { m = concat a b ; return m }\ng = do { m = f [\"x\", 1] ; return m }"

      -- The tail is a whole pattern, typed against the LIST, not the element.
    , clashes "…and the tail is the list, not an element"
        "f [_, ...r] = do { m = concat r \"a\" ; return m }"

      -- His 2026-09-12 ruling — a string literal is accepted at either — now
      -- holding on the left of the @=@ as well as the right.
      -- **Deferred, not pinned** — his 2026-09-12 ruling that a string literal
      -- is accepted at a 'TName' or a 'TString', now holding on the left of the
      -- @=@ too. The second clause is what makes the case bite: its body forces
      -- the parameter to a name, so a text pattern pinned to 'TString' would
      -- clash here. Without that clause nothing constrains the parameter and
      -- the case passes either way — which is how the first draft of it was
      -- wrong.
    , loads "a text pattern is accepted where a name is wanted"
        "rule h \"x\" :- then solve\nrule h n :- then goto-named n"
    ]
  where
    loads what src = testCase what $ case load (src ++ "\n") of
      BasesLoaded _ -> pure ()
      other         -> assertFailure ("expected a load, got " ++ show other)

    clashes what src = testCase what $ case load (src ++ "\n") of
      BasesIllTyped (Clash{} : _) -> pure ()
      other -> assertFailure ("expected a clash, got " ++ show other)

-- --------------------------------------------------------------------------
-- Splices in a written core term (MS5 phase 81)
-- --------------------------------------------------------------------------

-- | **@core`${d} -> ${c}`@ — a term written in the language\'s own notation
-- with holes filled from bindings.** His design, 2026-09-13.
--
-- **A splice always supplies a nonterminal** — his observation, and it is what
-- makes the phase small: a hole stands where a term stands, so the template
-- parses once at load, what each hole wants is known from where it sits, and
-- the values arrive when the instruction runs.
--
-- **The first two cases are the crossing**, and they are the point: a spliced
-- template and the op it replaces must build the *same term*. That is checked
-- by proving the same theorem both ways and comparing what the kernel admitted,
-- rather than by comparing the two terms in Haskell — which would compare this
-- phase against itself.
spliceTemplates :: TestTree
spliceTemplates =
  testGroup
    "a written core term may have holes"
    [ testCase "an arrow built by splicing is the arrow the op builds" $
        builtBy "ar = resolve-core core`${d} -> ${c}`" @?= builtBy "ar = arrow d c"

    , testCase "…and an application likewise" $
        appliedBy "ap = resolve-core core`${f} ${sv}`" @?= appliedBy "ap = apply-to f sv"

      -- **A splice must be a term**, and that is known when the file loads,
      -- because the hole's type comes from the grammar position.
    , testCase "a splice that is not a term is refused at load" $
        case load "rule go :- then n = fresh-name \"q\" ; u = resolve-core core`${n} -> ${n}` ; prove" of
          BasesIllTyped (Clash{} : _) -> pure ()
          other -> assertFailure ("expected a type error, got " ++ show other)

      -- …and a splice naming nothing is caught by @validate@, which sees inside
      -- a written term now for the same reason it sees inside a list literal.
    , testCase "a splice naming nothing is refused at load" $
        case loadRaw "rule base s where\nrule go :- then h = here ; u = resolve-core core`${h} -> ${nope}` ; prove\n" of
          RuleFileRefused _ (RuleIllFormed es)
            | [UnboundInRule _ _ "nope"] <- es -> pure ()
          other -> assertFailure ("expected a refusal, got " ++ show other)

      -- **The values a splice carries are ones no text could.** Every term the
      -- elaborator builds is at a fresh level meta, and @Type (suc ?ℓ683)@ does
      -- not parse — which is why a template is a term with holes and not a
      -- string with substitutions.
      -- **Corners carry a splice too, and that was not the plan.** His scope
      -- for the phase was the tagged spelling; what forced it is that the main
      -- lexer had to learn @${@ so a region's reassembled text could be read
      -- back, and an escape whose closing brace stayed a plain brace made the
      -- layout pass report /this closes a block that was not opened/ for a
      -- perfectly reasonable term. Pushing the escape mode fixes the message and
      -- makes both spellings agree — which is one less divergence for
      -- @ms5\/CLOSEOUT.md@ 22, not one more. Pinned because it works, and
      -- untested working behaviour is what this project keeps being bitten by.
    , testCase "and the two core spellings agree" $
        builtBy "ar = resolve-core \8988 ${d} -> ${c} \8989"
          @?= builtBy "ar = resolve-core core`${d} -> ${c}`"

    , testCase "and it carries a term with an unsolved level meta" $
        case builtBy "ar = resolve-core core`${d} -> ${c}`" of
          Just t | "?\8467" `isInfixOf` t -> pure ()
          other -> assertFailure ("expected a level meta in " ++ show other)
    ]
  where
    -- Claim two holes at fresh universes, build an arrow of them, fill with it,
    -- and answer what the development says afterwards.
    builtBy how = shown
      ("rule go :- then dn = fresh-name \"A\" ; u1 = fresh-universe ; d = claim dn u1\n\
       \     ; cn = fresh-name \"B\" ; u2 = fresh-universe ; c = claim cn u2\n\
       \     ; " ++ how ++ "\n\
       \     ; fill ar")

    appliedBy how = shown
      ("rule go :- then dn = fresh-name \"A\" ; u1 = fresh-universe ; d = claim dn u1\n\
       \     ; cn = fresh-name \"B\" ; u2 = fresh-universe ; c = claim cn u2\n\
       \     ; ar = arrow d c\n\
       \     ; fn = fresh-name \"f\" ; f = claim fn ar\n\
       \     ; sn = fresh-name \"s\" ; sv = claim sn d\n\
       \     ; " ++ how ++ "\n\
       \     ; fill ap")

    -- The test base is loaded on its own — a call to a rule nothing here
    -- defines is not a load error — and the shipped rules are put beside it
    -- afterwards, because 'loadRuleBases' replaces the list rather than adding
    -- to it.
    shown body =
      let s0 = fst (loadRuleBases newSession
                 [("s.thena.rules", "rule base s where\n" ++ body ++ "\n")])
          m0 = sessionMachine s0
          s0' = s0 { sessionMachine = m0 { rules = expectedBase ++ rules m0 } }
          s1 = fst (command s0' ":theorem t : Type")
          s2 = fst (command s1 "go")
       in case snd (command s2 ":show") of
            Shown c -> Just (renderCursor (names (sessionMachine s2)) c)
            _       -> Nothing

    loadRaw src = snd (loadRuleBases newSession [("s.thena.rules", src)])

-- --------------------------------------------------------------------------
-- A function body may be a block (MS5 phase 75b)
-- --------------------------------------------------------------------------

-- | **@f x = do ‹block›@** — his choice of opener, 2026-09-13, which is what
-- lets a function have locals at all.
--
-- A block body /is/ the rule's body, so it says @return@ itself and the short
-- form @f x = e@ is that block with the @return@ written for you. The two go
-- through one compiler, 'Thena.Rules.bodyInstrs'.
--
-- **The first three assert the VALUE and not merely that it loads**, and that
-- is deliberate: the grammar accumulates a block in reverse, so the first build
-- of this phase ran every block backwards and still loaded — @shout@ reported
-- /no earlier binding is called closed/ only because the two locals happened to
-- depend on each other. A block of independent instructions would have run in
-- the wrong order in silence.
blockBodies :: TestTree
blockBodies =
  testGroup
    "a function body may be a do block"
    [ testCase "with locals, in the order they are written" $
        said "shout s = do { wrapped = concat \"<\" s ; closed = concat wrapped \">\" ; return closed }\n\
             \rule go :- then m = shout \"hi\" ; say m"
          @?= Just "<hi>"

      -- The short form is unchanged and goes through the same compiler.
    , testCase "…and the one-expression form still means what it did" $
        said "short s = concat s \"!\"\n\
             \rule go :- then m = short \"yo\" ; say m"
          @?= Just "yo!"

      -- **A lambda gets it too**, because §1.1 reads both ways: a lambda is a
      -- function without a name, so there is one body compiler and not two.
    , testCase "…and so may a lambda's body" $
        said "apply2 f x = f (f x)\n\
             \rule go :- then m = apply2 (\\ z -> do { p = concat z \".\" ; return p }) \"q\" ; say m"
          @?= Just "q.."

      -- **A block that never returns is refused**, which is the block form of
      -- the check @f x = say \"hi\"@ already got. It is reported against the
      -- name, not against a binding the author never wrote.
    , testCase "a block that returns nothing is refused" $
        case loadRaw "rule base b where\nf s = do { say s }\n" of
          RuleFileRefused _ (RuleIllFormed es)
            | FunctionLeavesNothing "f" `elem` es -> pure ()
          other -> assertFailure ("expected a refusal, got " ++ show other)

      -- It is an ordinary rule body by the time anything else sees it, so
      -- inference reads it with no case of its own.
    , testCase "and inference types it like any other body" $
        case load "f : String -> String\nf s = do { a = concat s s ; return a }" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)
    ]
  where
    said src = case snd (command (fst (loadRuleBases newSession
                 [("b.thena.rules", "rule base b where\n" ++ src ++ "\n")])) "go") of
      Ran msgs _ -> case reverse msgs of { m : _ -> Just m; [] -> Nothing }
      other      -> error ("expected Ran, got " ++ show other)

    loadRaw src = snd (loadRuleBases newSession [("b.thena.rules", src)])

-- --------------------------------------------------------------------------
-- A signature needs no keyword (MS5 phase 74)
-- --------------------------------------------------------------------------

-- | **An annotation is @f : Ty@ in column 1** — his ruling, 2026-09-13, closing
-- @ms5\/CLOSEOUT.md@ 11.
--
-- A declaration that begins with a plain word is a signature or a function, and
-- the two part on the **token after the name**: @:@ there, another parameter or
-- @=@ here. That is one token of lookahead and the grammar has no conflict, so
-- what these check is the parting itself — each of the three shapes, read back
-- as the declaration it is meant to be.
--
-- **The word is an ordinary identifier again**, which is the point of the phase:
-- one lexer serves every language, so @signature@ had been unusable as a name in
-- Surface, Core and every object language, not only in a rule file.
noKeyword :: TestTree
noKeyword =
  testGroup
    "a signature is written without a keyword"
    [ loads "a name, a colon and a type is a signature"
        "f : Core -> ()\nrule f x :- then prim-try x"

      -- The two function shapes, either side of the one that is a signature.
    , loads "a name, parameters and an = is a function"
        "twice s = concat s s"

    , loads "a name and an = with no parameters is a function too"
        "greeting = concat \"hi\" \"!\""

      -- **The word is free**, and a rule is the sharpest place to show it: a
      -- declaration beginning @signature@ used to be a keyword and can now only
      -- be a name.
    , loads "signature is an ordinary name for a rule"
        "rule signature :- then prove"

    , loads "…for a function"
        "signature s = concat s s"

    , loads "…for a parameter"
        "f : Core -> ()\nrule f signature :- then prim-try signature"

      -- …and for a callable that is itself annotated, which is the one that
      -- would have been unwritable in every spelling.
    , loads "…and for a callable with a signature of its own"
        "signature : String -> String\nsignature s = concat s s"

      -- **The old spelling is a parse error and nothing special-cases it.**
      -- Pinned so the message cannot drift silently: @signature f : T@ reads as
      -- a function named @signature@ taking @f@, which then meets a @:@ where it
      -- wanted an @=@.
    , testCase "and the old keyword spelling is refused where the colon is" $
        case load "signature f : Core -> ()\nrule f x :- then prim-try x" of
          RuleFileRefused _ (RuleSyntaxError (ParseFailed (UnexpectedToken _ _))) -> pure ()
          other -> assertFailure ("expected a parse error, got " ++ show other)
    ]
  where
    loads what src = testCase what $ case load src of
      BasesLoaded _ -> pure ()
      other         -> assertFailure ("expected a load, got " ++ show other)

-- --------------------------------------------------------------------------
-- The done-when
-- --------------------------------------------------------------------------

-- | **The shipped base must infer cleanly** — MS5.md names this as the real
-- constraint on how precise the signatures of phase 66b could be. It did, first
-- time and without a signature being loosened for it.
shippedBase :: TestTree
shippedBase =
  testGroup
    "the shipped base"
    [ testCase "infers with no errors at all" $
        map renderInstralTypeError (snd (inferProgram [] expectedStandard)) @?= []

      -- **What it inferred, handed back as a DECLARATION** (2026-09-13).
      -- Inference and checking are two modes over one program — §6.5 — and
      -- nothing crossed them: every annotation test writes a signature by hand,
      -- so a type inference can produce but the checker will not accept has
      -- nowhere to show up. Declaring exactly what was inferred must change
      -- nothing.
      --
      -- It is also the strongest statement available that an inferred type is
      -- /sayable/: 'generalEnough' refuses a declared scheme whose variables do
      -- not stay distinct variables, so an inferred signature that could not be
      -- written down fails here.
    , testCase "and declaring exactly what it inferred changes nothing" $
        let inferred = [ (n, sg) | ((GlobalName n, _), sg) <- fst (inferProgram [] expectedStandard) ]
         in map renderInstralTypeError (snd (inferProgram inferred expectedStandard)) @?= []

      -- **Written out, not counted.** A signature is what a later phase will
      -- move by accident, and every one of these was inferred from the head
      -- predicates and the ops in the body — nothing is annotated.
    , testCase "and these are the signatures it works out" $
        [ n ++ "/" ++ show a ++ " : " ++ renderSignature s
        | ((GlobalName n, a), s) <- fst (inferProgram [] expectedStandard)
        ]
          @?= [ "attack/0 : ()"
              , "try-core/1 : Core -> ()"
              , "abandon/0 : ()"
              , "intro/0 : ()"
              , "solve/0 : ()"
              , "regret/0 : ()"
              , "eliminate-core/1 : Core -> ()"
              , "prove/0 : ()"
              , "fill/1 : Core -> ()"
              , "unify-refine-core/1 : Core -> ()"
              , "apply-core/1 : Core -> ()"
              , "claim/1 : Core -> ()"
              , "assume/1 : Core -> ()"
              , "quantify/1 : Core -> ()"
              , "elaborate/1 : Surface -> ()"
              , "intro-binders/1 : Surface -> ()"
              , "enter-binders/1 : Surface -> ()"
              , "spine-arguments/3 : Core -> Core -> Surface -> ()"
              ]

      -- **`elaborate`'s parameter is a Surface term and nothing says so.** It
      -- comes from the head predicates: sixteen clauses each ask a
      -- `surface-is-…` question of `t`, and 'Thena.Rules.testTypes' is what
      -- makes that an answer.
    , testCase "elaborate's parameter came from its head" $
        lookup (GlobalName "elaborate", 1) (fst (inferProgram [] expectedStandard))
          @?= Just (Signature [TSurface] Nothing)

      -- **`spine-arguments` has no head test about `h` or `f` at all.** Their
      -- types come from the body — `goto h` wants a Core, `apply-next f n` wants
      -- one — which is the part a head-only reading would miss.
    , testCase "and spine-arguments' came from its body" $
        lookup (GlobalName "spine-arguments", 3) (fst (inferProgram [] expectedStandard))
          @?= Just (Signature [TCore, TCore, TSurface] Nothing)
    ]

-- --------------------------------------------------------------------------
-- One file per way to be wrong
-- --------------------------------------------------------------------------

illTyped :: TestTree
illTyped =
  testGroup
    "a program that does not type check is refused"
    [ -- The head says Surface, the body hands it to an op that wants Core.
      refused "a parameter used at two types"
        "rule bad t :- when (surface-is-name t) then prim-try t"
        [ Clash (InBody (GlobalName "bad") 0) TCore TSurface ]

      -- **A literal is checked against the position**, and this one cannot be.
      -- 'Thena.Ops.Try' wants a term; a number is not one. **This is one of the
      -- three checks phase 63 and 64 had to defer to run time** — MS5.md says
      -- phase 66 is where it comes back, and this is it.
    , refused "a numeral where a term was wanted"
        "rule bad :- then prim-try 3"
        [ Clash (InBody (GlobalName "bad") 0) TCore TInt ]

      -- …and its text sibling, which is a separate error because a string
      -- literal is the one whose type the position decides.
    , refused "a string where a term was wanted"
        "rule bad :- then prim-try \"x\""
        [ TextNotTextual (InBody (GlobalName "bad") 0) TCore ]

      -- **The other deferred check** (MS5 phase 63): binding a call to a rule
      -- no clause of which returns. It was 'Thena.Errors.NothingReturned' at run
      -- time because /which clauses a name has is not known when a body is
      -- read/ — true of reading one body, false of a pass over every base.
    , refused "binding a call that cannot return"
        "rule mute t :- then say \"nothing\"\n\
        \rule bad t :- then x = mute t ; say x"
        [ BindsNothing (InBody (GlobalName "bad") 0) (GlobalName "mute") ]

      -- **Two clauses of one name must agree**, because they are one callable:
      -- dispatch chooses between them at run time and a caller cannot know
      -- which it got.
    , refused "two clauses that disagree about a parameter"
        "rule two t :- when (surface-is-name t) then prim-prove\n\
        \rule two t :- then prim-try t"
        [ Clash (InBody (GlobalName "two") 0) TCore TSurface ]

      -- A list is homogeneous, and the literal is where that is enforced.
    , refused "a list of two different things"
        "rule bad :- then prim-try [3, 'c']"
        [ Clash (InBody (GlobalName "bad") 0) TInt TChar
        , Clash (InBody (GlobalName "bad") 0) TCore (TList TInt)
        ]
    ]
  where
    refused label src want =
      testCase label $ case load src of
        BasesIllTyped errs -> errs @?= want
        other -> assertFailure ("expected a refusal, got " ++ show other)

-- --------------------------------------------------------------------------
-- …and one per thing that must keep working
-- --------------------------------------------------------------------------

wellTyped :: TestTree
wellTyped =
  testGroup
    "a program that does type check is installed"
    [ -- **A string literal is accepted where a Name is wanted** — his ruling,
      -- 2026-09-12 — so nothing about how a rule is written changes.
      accepted "a string literal at a name position"
        "rule fine :- then n = fresh-name \"h\" ; goto-named n"

      -- …and the coercion is what carries it the other way, because @n@ here is
      -- a variable and not a literal.
    , accepted "and name-text carries a name back to a string"
        "rule fine :- then n = fresh-name \"h\" ; t = name-text n ; say t"

      -- **A call to a name nothing defines constrains nothing**, and is not an
      -- error: §8 has always allowed it and the machine reports it when the
      -- search finds no clause.
    , accepted "a call to a rule nothing defines"
        "rule fine t :- then call nowhere t"

      -- **A rule used before it is written**, which is why the pass is over the
      -- whole program rather than one rule at a time.
    , accepted "a call to a rule written below it"
        "rule fine t :- then call later t\n\
        \rule later t :- when (surface-is-name t) then prove"

      -- **Recursion**: the one that would not terminate if a rule's signature
      -- had to be known before its own body was walked.
      -- **An op word at another arity is a call to a RULE** (MS5 phase 62b,
      -- his ruling), so this constrains nothing rather than being a wrong-arity
      -- error. It is the one of the three checks deferred at 62b–64 that this
      -- pass does NOT bring back; see @ms5/CLOSEOUT.md@.
    , accepted "an op word at the wrong arity is an unknown call"
        "rule fine t :- then call say t t"

    , accepted "a rule that calls itself"
        "rule walk t :- when (surface-is-app t) then a = app-tail t ; call walk a"

    ]
  where
    accepted label src =
      testCase label $ case load src of
        BasesLoaded bs -> length (concatMap baseRules bs) > 0 @?= True
        other -> assertFailure ("expected a load, got " ++ show other)

-- | **A @return@ inside a @do@ block ends the BLOCK, not the rule** — see
-- "Thena.Engine"'s 'Thena.Ops.Return' case, which says so in as many words.
--
-- Built by hand rather than written in a file, because a block is never spelled
-- in a rule body ('Thena.Ops.Block'): it comes from a surface @do { … }@. So
-- @blocked@ returns nothing, and binding a call to it is refused. Read the
-- other way — the block's @return@ taken for the rule's — this would type check
-- and then fail at run time with 'Thena.Errors.NothingReturned'.
blockReturn :: TestTree
blockReturn =
  testCase "a return inside a block is not the rule's" $
    let blocked = Rule (GlobalName "blocked") [] []
                    [Do (Block [Do (Return (Lit (VText "x")))])]
        bad     = Rule (GlobalName "bad") [] []
                    [Bind (PVar "y") Nothing (Call "blocked" []), Do (Say (Ref "y"))]
     in snd (inferProgram [] [blocked, bad])
          @?= [BindsNothing (InBody (GlobalName "bad") 0) (GlobalName "blocked")]

-- --------------------------------------------------------------------------
-- Declared signatures (MS5 phase 67)
-- --------------------------------------------------------------------------

-- | **What an annotation buys, and it is a capability rather than a comment.**
--
-- Phase 67 was originally scoped as a signature pre-pass so that bodies could be
-- parsed; §6.0.1's tags removed that need and phase 66c demonstrated it — the
-- whole shipped base infers with no annotations at all. What is left is these
-- two: a rule usable at two types, and a wrong promise reported where it was
-- made.
annotations :: TestTree
annotations =
  testGroup
    "a declared signature"
    [ -- @ignore@ is used at a Name and at a Core, and a signature says so.
      testCase "makes a rule usable at two types" $
        case load polymorphic of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)

      -- **AND SO DOES INFERENCE, SINCE MS5 PHASE 76** — his ruling, take the
      -- type system all the way to HM. This case asserted a @Clash@ until then,
      -- which was @ms5\/CLOSEOUT.md@ 8: one recursive group, one type, so the
      -- second use was an error and an annotation was the only way out.
      -- **`ignore` is its own strongly connected component**, so it is
      -- generalised before either caller is walked and each use gets its own
      -- copy — exactly as the declared version does.
    , testCase "…and now so does the same base without one" $
        case load (unlines (drop 1 (lines polymorphic))) of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)

      -- **What the annotation still buys is the promise**, which is the whole
      -- of its remaining job: the inferred scheme and the written one agree.
    , testCase "…and the two agree on what it is" $
        case load (unlines (drop 1 (lines polymorphic))) of
          BasesLoaded (b : _) ->
            lookup (GlobalName "ignore", 1) (fst (inferProgram [] (baseRules b)))
              @?= Just (Signature [TVar 0] Nothing)
          other -> assertFailure ("expected a load, got " ++ show other)

      -- **His requirement: a wrong annotation reports against the
      -- DECLARATION.** The signature promises any type; the body hands the
      -- parameter to an op that wants a term, so the promise is broken and it is
      -- the promise that is at fault, not the instruction.
    , testCase "that promises more than the body delivers is refused at the signature" $
        load "f : a -> ()\nrule f x :- then prim-try x"
          @?= BasesIllTyped
                [AnnotationTooGeneral (InSignature (GlobalName "f") 1) TCore]

      -- …and a signature that is simply the wrong type is still reported in the
      -- body, which is §6.5(a) — the author's own rule, local and clear.
    , testCase "that names the wrong type is refused in the body" $
        load "f : Core -> ()\nrule f x :- when (surface-is-name x) then prove"
          @?= BasesIllTyped [Clash (InHead (GlobalName "f") 0) TSurface TCore]

      -- A signature is a claim about a callable, so a claim nothing answers is
      -- a mistake — most likely a typo or a changed arity.
    , testCase "for a callable nothing defines is refused" $
        load "nobody : Core -> ()\nrule f :- then prove"
          @?= BasesIllTyped [SignatureUnanswered (GlobalName "nobody") 1]

      -- **The arity is the arrow chain's**, so this signature is about @f@ at
      -- one argument and says nothing about the @f@ of none — a different
      -- callable, which dispatch already treats as one.
      -- **Two variables in one signature stay two** (found by mutation testing,
      -- 2026-09-12). @resolveSignature@ resolved each link of the arrow chain on
      -- its own, and each numbered its variables from zero — so @a -> b -> ()@
      -- was @a -> a -> ()@ and every signature's variables collapsed. Nothing
      -- noticed, because a collapsed signature is still a signature.
    , testCase "keeps its variables apart" $
        case load "ignore2 : a -> b -> ()\n\
                  \rule ignore2 x y :- then prove\n\
                  \rule use :- then h = here ; n = fresh-name \"k\" ; ignore2 h n" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)

      -- **A NESTED arrow's variables too** — `(a -> b)` had the same collapse as
      -- the top-level chain, one level down, and it is the case a higher-order
      -- signature is made of.
    , testCase "and keeps a nested arrow's apart as well" $
        case load "f : (a -> b) -> a -> b\nf g x = g x" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)

      -- …and a body that forces two of them TOGETHER breaks the promise as
      -- surely as one that pins either, which is the other half of
      -- 'Thena.Instral.Infer.generalEnough' and was untested until now.
    , testCase "and a body may not force two of them together" $
        case load "pairUp : a -> a -> ()\n\
                  \rule pairUp x y :- then prove\n\
                  \same : a -> b -> ()\n\
                  \rule same x y :- then pairUp x y" of
          BasesIllTyped (AnnotationTooGeneral _ _ : _) -> pure ()
          other -> assertFailure ("expected a refusal, got " ++ show other)

    , testCase "is about one arity only" $
        case load "f : Core -> ()\nrule f x :- then prim-try x\nrule f :- then prove" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)

      -- **A lambda's body is scoped at load** (found in the long hunt,
      -- 2026-09-13). @operandsOf@ answers with what an op /reads/ and a
      -- lambda's body is a program rather than an operand, so @validate@ walked
      -- straight past it: the rule below loaded clean and failed at run time,
      -- where the same name outside the lambda is a load error. Phase 68b added
      -- lambdas and the walk was not told.
    , testCase "an unbound name inside a lambda is a load error, like anywhere else" $
        case load "rule go :- then g = \\ z -> concat z nosuchname ; prove" of
          RuleFileRefused _ (RuleIllFormed es)
            | UnboundInRule (GlobalName "go") 0 "nosuchname" `elem` es -> pure ()
          other -> assertFailure ("expected an unbound name, got " ++ show other)

      -- …and one that IS bound by the lambda is not reported, which is the
      -- half a walk that simply refused every lambda would get wrong.
    , testCase "and a name the lambda binds is not" $
        case load "rule go :- then g = \\ z -> concat z z ; prove" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)

      -- Nested one level down, so the walk has to recurse rather than peek.
    , testCase "and it looks inside a lambda inside a lambda" $
        case load "rule go :- then g = \\ z -> (\\ w -> concat w deepermissing) ; prove" of
          RuleFileRefused _ (RuleIllFormed es)
            | UnboundInRule (GlobalName "go") 0 "deepermissing" `elem` es -> pure ()
          other -> assertFailure ("expected an unbound name, got " ++ show other)

      -- **A RESULT may be a function, and could not be said until 2026-09-12.**
      -- The grammar dropped the parentheses, so @String -> (String -> String)@
      -- and @String -> String -> String@ were one tree and the signature below
      -- described @mk@ at arity /two/ — @SignatureUnanswered mk 2@, while the
      -- @mk@ that exists went uncovered. Inference has always worked the type
      -- out; the declared half of the type system simply could not spell it.
    , testCase "may give a function, not only take one" $
        case load "mk : String -> (String -> String)\n\
                  \mk s = \\ z -> concat s z" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)

      -- …and it is not the same signature as the flat one, which is the whole
      -- point of keeping the parentheses.
    , testCase "and giving a function is not the same as taking two arguments" $
        case load "mk : String -> String -> String\n\
                  \mk s = \\ z -> concat s z" of
          BasesIllTyped _ -> pure ()
          other -> assertFailure ("expected a refusal, got " ++ show other)

      -- A group around something that is not an arrow is nothing at all.
    , testCase "a group around a plain type changes nothing" $
        case load "f : (Core) -> (())\nrule f x :- then prim-try x" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)
    ]
  where
    polymorphic =
      "ignore : a -> ()\n\
      \rule ignore x :- then say \"ignored\"\n\
      \rule usesName :- then n = fresh-name \"h\" ; ignore n\n\
      \rule usesTerm :- then h = here ; ignore h\n"

-- | A signature that does not resolve is refused when the FILE is read, before
-- anything is inferred — it is a question one file can answer.
badSignatures :: TestTree
badSignatures =
  testGroup
    "a signature that does not resolve"
    [ refused "an unknown type"      "f : Trm -> ()"   (UnknownType "f" "Trm")
    , refused "a constructor's arity" "f : List -> ()" (TypeArity "f" "List" 1 0)
    , refused "a variable applied"   "f : a Core -> ()" (TypeVariableApplied "f" "a")
    , refused "() as an argument"    "f : () -> ()"    (UnitInsideAType "f")
    , refused "two for one callable"
        "f : Core -> ()\nf : Surface -> ()"
        (DuplicateSignature "f" 1)
    ]
  where
    refused label src want =
      testCase label $ case load (src ++ "\nrule f x :- then prove") of
        RuleFileRefused _ (RuleIllFormed es) | want `elem` es -> pure ()
        other -> assertFailure ("expected " ++ show want ++ ", got " ++ show other)

-- --------------------------------------------------------------------------
-- Global functions (MS5 phase 68a)
-- --------------------------------------------------------------------------

-- | **A function is a rule with one clause and no head** — his §1.1 — so what
-- is checked here is mostly that nothing had to be added to make that true.
functions :: TestTree
functions =
  testGroup
    "a global function"
    [ -- **No keyword** — his choice, 2026-09-12. @rule@ and @signature@ are
      -- keywords, so a declaration beginning with a plain word can only be this.
      testCase "is declared with no keyword and is callable" $
        said "rule go :- then m = twice \"a\" ; say m" @?= Just "aa"

      -- **The boundary is column 1** — his ruling, 2026-09-12. Without it the
      -- @g@ below is parsed as another operand of @say@, silently, because
      -- Happy shifts.
    , testCase "does not get swallowed by the declaration above it" $
        said "rule go :- then m = twice \"b\" ; say m" @?= Just "bb"

      -- …and the rule that buys it. **MS5 phase 75 restated it as Haskell's**:
      -- the file is one layout block whose column is the FIRST declaration's, so
      -- what is refused is a declaration that does not line up with the others.
      -- A whole file written indented is consistent and therefore fine — it is
      -- the disagreement that is the mistake, and that is what used to be
      -- misparsed in silence.
    , testCase "and a declaration that does not line up is refused" $
        case loadRaw "rule base i where\nrule f :- then prove\n  rule g :- then prove\n" of
          RuleFileRefused _ (RuleSyntaxError _) -> pure ()
          other -> assertFailure ("expected a syntax error, got " ++ show other)

    , testCase "…in either direction" $
        case loadRaw "rule base i where\n  rule f :- then prove\nrule g :- then prove\n" of
          RuleFileRefused _ (RuleSyntaxError _) -> pure ()
          other -> assertFailure ("expected a syntax error, got " ++ show other)

      -- **A file indented as a whole is a file**, which is the half that is new.
    , testCase "…but a file that lines up at another column loads" $
        case loadRaw "rule base i where\n  rule f :- then prove\n  rule g :- then prove\n" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)

      -- **It is not offered as a tactic.** A function has no head, and a
      -- headless rule matches everywhere — so if functions were kept with the
      -- rules, @prove@ would run them. 'Thena.Rules.baseFunctions' is why they
      -- are a separate list.
    , testCase "is not listed among the rules" $
        case load "twice x = concat x x\nrule go :- then prove" of
          BasesLoaded bs -> map (map ruleNameOf . baseRules) bs @?= [["go"]]
          other -> assertFailure ("expected a load, got " ++ show other)

      -- …and its type is inferred like any rule's, because it is one.
    , testCase "is inferred like a rule" $
        case load "twice x = concat x x" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)

      -- **A function must produce.** Refused where it is written rather than by
      -- 'Thena.Rules.validate', which would report it against a binding the
      -- author never wrote.
      -- **A function is validated like any rule** (found by mutation testing,
      -- 2026-09-12): dropping functions from @resolveAll@'s validation pass left
      -- the suite green, so nothing had checked that an unbound name in a
      -- function body is refused.
    , testCase "is validated like a rule" $
        case load "f x = concat x y" of
          RuleFileRefused _ (RuleIllFormed es)
            | UnboundInRule (GlobalName "f") 0 "y" `elem` es -> pure ()
          other -> assertFailure ("expected a refusal, got " ++ show other)

      -- **A name may not be a rule and a function at one arity** (MS5 review).
      -- They would be two clauses of one callable, so the function would join
      -- the rule's backtracking and a call could run either — which is exactly
      -- what a function is not.
    , testCase "may not share a name and arity with a rule" $
        case load "rule dup x :- then say \"rule\"\ndup x = concat x x" of
          RuleFileRefused _ (RuleIllFormed es)
            | RuleAndFunction "dup" 1 `elem` es -> pure ()
          other -> assertFailure ("expected a refusal, got " ++ show other)
      -- …and at a different arity they are two callables, as they are for two
      -- rules.
    , testCase "but may share one at a different arity" $
        case load "rule dup x :- then say \"rule\"\ndup = concat \"a\" \"b\"" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)

    , testCase "that leaves nothing is refused" $
        case load "f x = say \"hi\"" of
          RuleFileRefused _ (RuleIllFormed es)
            | FunctionLeavesNothing "f" `elem` es -> pure ()
          other -> assertFailure ("expected a refusal, got " ++ show other)

      -- **@x = ‹value›@, which `ms5/CLOSEOUT.md` 3 owed this phase** (his
      -- ruling, 2026-09-12). It resolves to 'Thena.Ops.Value', an op with a word
      -- and no written form.
      -- **@x = true@ is the literal** (MS5 phase 73). @true@ and @false@ are read
      -- as values wherever an operand is, and the right of an @=@ was the one
      -- place a bare word went somewhere else — so this used to say /no rule is
      -- called false/.
    , testCase "and a boolean on the right of an = is the literal" $
        case load "rule go :- then b = false ; prove" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)
    , testCase "and a literal can be bound to a name at last" $
        case load "rule go :- then p = (1, true) ; l = [1, 2, 3] ; n = 42 ; prove" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)
    ]
  where
    ruleNameOf r = case ruleName r of GlobalName n -> n

    said line = case snd (command (fst (loadRuleBases newSession
                  [("f.thena.rules", "rule base f where\ntwice x = concat x x\n" ++ line ++ "\n")]))
                  "go") of
      Ran msgs _ -> case reverse msgs of { m : _ -> Just m; [] -> Nothing }
      other      -> error ("expected Ran, got " ++ show other)

    loadRaw src = snd (loadRuleBases newSession [("i.thena.rules", src)])

-- --------------------------------------------------------------------------
-- Lambdas (MS5 phase 68b)
-- --------------------------------------------------------------------------

-- | **A lambda is a function without a name** — §1.1 read the other way — so it
-- compiles the way a function does and is applied through the frame a call
-- already pushes.
lambdas :: TestTree
lambdas =
  testGroup
    "a lambda"
    [ -- Bound to a local and applied. **This is the shadowing his ruling
      -- bought**: @k \"z\"@ is an application of the local, not a call to a rule
      -- called @k@.
      testCase "is bound to a local and applied" $
        said "rule go :- then k = \\ s -> concat \"<\" s ; n = k \"z\" ; say n"
          @?= Just "<z"

      -- **Higher order, with the signature that says so.** @(a -> b)@ in a
      -- signature was refused by name until this phase.
    , testCase "is passed to a function that takes one" $
        said "onTwice : (String -> String) -> String -> String\n\
             \onTwice f x = f (f x)\n\
             \rule go :- then d = \\ s -> concat s s ; m = onTwice d \"a\" ; say m"
          @?= Just "aaaa"

      -- **Parenthesised in an argument**, like every other compound one.
    , testCase "takes parentheses in an argument position" $
        said "once : (String -> String) -> String\n\
             \once f = f \"q\"\n\
             \rule go :- then m = once (\\ s -> concat s s) ; say m"
          @?= Just "qq"

      -- **N-ary and not curried** — a function of one is not a function of two,
      -- whatever the types, because dispatch is on arity.
    , testCase "applied at the wrong arity is refused" $
        case load "rule go :- then d = \\ s -> concat s s ; m = d \"a\" \"b\" ; say m" of
          BasesIllTyped (Clash _ _ _ : _) -> pure ()
          other -> assertFailure ("expected a clash, got " ++ show other)

      -- Its body must produce, for a function's reason and with the same
      -- message.
      -- **A lambda's BODY is inferred**, not just its arity (found by mutation
      -- testing, 2026-09-12: disabling the inference case left the suite green).
      -- Without it a lambda would be a hole in the type system that anything
      -- could be hidden in.
    , testCase "has its body type checked too" $
        load "rule go :- then f = \\ z -> concat z 3 ; prove"
          @?= BasesIllTyped [Clash (InBody (GlobalName "go") 0) TString TInt]

    , testCase "whose body leaves nothing is refused" $
        case load "rule go :- then d = \\ s -> prim-try s ; prove" of
          RuleFileRefused _ (RuleIllFormed es)
            | FunctionLeavesNothing "λ" `elem` es -> pure ()
          other -> assertFailure ("expected a refusal, got " ++ show other)

      -- **A function type is writable in a signature now**, which it was not
      -- before this phase — @TypeIsAFunction@ refused it and is deleted.
    , testCase "and a function type is writable in a signature" $
        case load "f : (a -> b) -> a -> b\nf g x = g x" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)
    ]
  where
    said src = case snd (command (fst (loadRuleBases newSession
                 [("l.thena.rules", "rule base l where\n" ++ src ++ "\n")])) "go") of
      Ran msgs _ -> case reverse msgs of { m : _ -> Just m; [] -> Nothing }
      other      -> error ("expected Ran, got " ++ show other)

-- --------------------------------------------------------------------------
-- Object languages (MS5 phase 69)
-- --------------------------------------------------------------------------

-- | **The seam §6.6 asks for**: a declared language gets an opaque @instral@
-- type, a tag that is its only introduction form, and a one-way coercion to
-- Surface.
objectLanguages :: TestTree
objectLanguages =
  testGroup
    "a declared object language"
    [ -- The whole path: declared, tagged, parsed by the generated parser, and
      -- used at the type the declaration generated.
      testCase "is a type, a tag and a coercion" $
        case load (tm ++ "asSurface : Tm -> Surface\n\
                         \asSurface t = surface-of t\n\
                         \rule go :- then t = Tm`(x y)` ; s = asSurface t ; prove") of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)

      -- **The brand is the point.** Without the coercion an object term is not a
      -- Surface term as far as the type system is concerned, which is what makes
      -- the tag worth having.
    , testCase "is not a Surface term until it is coerced" $
        load (tm ++ "want : Surface -> ()\n\
                    \rule want s :- then prove\n\
                    \rule go :- then t = Tm`(x y)` ; want t")
          @?= BasesIllTyped [Clash (InBody (GlobalName "go") 1) TSurface (TObject "Tm")]

      -- **The generated parser is a real parser**, and a term it cannot read is
      -- a syntax error naming the tag — arriving at load, with every other one
      -- (§6.0.1).
    , testCase "reports a term its grammar cannot read" $
        case load (tm ++ "rule go :- then t = Tm`(x y` ; prove") of
          RuleFileRefused _ (RuleIllFormed (BadRegion _ _ "Tm" _ : _)) -> pure ()
          other -> assertFailure ("expected a region error, got " ++ show other)

      -- **A grammar may span lines with its closing brace in column 1** (found
      -- by mutation testing, 2026-09-12). Phase 68a's rule is that a declaration
      -- begins in column 1; phase 73 had to narrow it to tokens that could
      -- actually begin one, because a @language@ block's @}@ sits there too.
      -- Every other grammar test writes the block on one line, so the narrowing
      -- was never pinned.
    , testCase "a grammar may close its brace in column 1" $
        case load "language Tm where {\n  var : name ;\n  app : \"(\" Tm Tm \")\"\n}\n\
                  \rule go :- then t = Tm`(x y)` ; prove" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)

      -- **A parse must consume the WHOLE region** (found by mutation testing,
      -- 2026-09-12). @x y@ has a valid prefix — @x@ is a @var@ — and dropping
      -- the whole-input condition made this load with the @y@ silently thrown
      -- away. The tests until now used inputs that either parsed completely or
      -- not at all, so the condition was never exercised.
    , testCase "refuses a term whose prefix parses and whose rest does not" $
        case load (tm ++ "rule go :- then t = Tm`x y` ; prove") of
          RuleFileRefused _ (RuleIllFormed (BadRegion _ _ "Tm" _ : _)) -> pure ()
          other -> assertFailure ("expected a region error, got " ++ show other)

      -- **A `${ … }` escape lexes and no grammar reads it** (found 2026-09-12,
      -- @ms5\/CLOSEOUT.md@ 27). @discussion\/the-five-languages.md@ §6.9 makes
      -- the escape the nesting mechanism and @MS5.md@ put it in phase 60's
      -- scope; the lexer builds it and @LexerTests@ covers it in five cases,
      -- but neither @Syntax.Parser@ nor @Surface.Parser@ declares
      -- @TEscapeOpen@, so a region containing one is a parse error at load.
      --
      -- Pinned as a refusal so that the day it is implemented, this test has to
      -- be changed on purpose rather than quietly starting to pass.
      --
      -- **MS5 phase 81 is that day, and only half of it.** A splice in a
      -- @core@ region is read now — see @spliceTemplates@ below. A splice in a
      -- **generated** parser\'s region still is not: the region\'s text reaches
      -- @Tm@\'s parser with the @${…}@ in it and @Tm@ has no production for one,
      -- so it is refused there rather than at the fence. Changed on purpose, and
      -- the refusal is still pinned — one language over.
    , testCase "a nesting escape into an object language is still refused" $
        case load (tm ++ "rule go t :- then u = Tm`(x ${ t })` ; prove") of
          RuleFileRefused _ (RuleIllFormed [BadRegion _ _ "Tm" _]) -> pure ()
          other -> assertFailure ("expected a refusal, got " ++ show other)

      -- **An empty region is end of input** (found probing degenerate input,
      -- 2026-09-12). The failure path picked a token out of the token list to
      -- report, and an empty region has none, so it fell back on an arbitrary
      -- constructor and told the user @unexpected ;@ about a character that is
      -- not there.
    , testCase "an empty region says end of input, not a token that is not there" $
        case load (tm ++ "rule go :- then t = Tm`` ; prove") of
          RuleFileRefused _ (RuleIllFormed (BadRegion _ _ "Tm" e : _)) ->
            e @?= ParseFailed UnexpectedEndOfInput
          other -> assertFailure ("expected a region error, got " ++ show other)

      -- The three shapes the generated parser could not run, refused when the
      -- grammar is declared rather than when it is used.
    , refusedGrammar "left recursion"
        "language Tm where { loop : Tm \"x\" }"
        (BadGrammar "Tm" (LeftRecursive "Tm" "loop"))
    , refusedGrammar "an empty production"
        "language Tm where { nothing : }"
        (BadGrammar "Tm" (EmptyProduction "Tm" "nothing"))
    , refusedGrammar "a terminal that is not one token"
        "language Tm where { var : \"a b\" }"
        (BadGrammar "Tm" (TerminalDoesNotLex "Tm" "a b"))
      -- **A built-in tag may not be taken** (MS5 review). 'Thena.Rules.operandOf'
      -- looks a declared language up BEFORE the built-ins, so without this
      -- @language surface where { … }@ silently replaced the @⟨ … ⟩@ fence's
      -- sibling spelling — and §6.0.1 says a user cannot tell a built-in tag
      -- from a generated one, which is what makes it a trap.
    , refusedGrammar "a built-in tag's name"
        "language surface where { var : name }"
        (BuiltInLanguage "surface")
    , refusedGrammar "and the other one"
        "language core where { var : name }"
        (BuiltInLanguage "core")
      -- **A language's name is a TYPE as well as a tag** (2026-09-12), and
      -- 'Thena.Rules.resolveTyIn' looks a declared one up before the built-ins
      -- exactly as 'operandOf' does. Without this @language String where { … }@
      -- made @String@ in every signature mean the object language, and the clash
      -- said /wanted String, got String/ — the same nonsense the nullary function
      -- type printed. @List@ was worse: it loaded, and @signature f : List -> ()@
      -- stopped being the arity error it is.
    , refusedGrammar "a built-in type's name"
        "language String where { var : name }"
        (BuiltInType "String")
    , refusedGrammar "a built-in type that takes an argument"
        "language List where { var : name }"
        (BuiltInType "List")
    , refusedGrammar "and a type whose tag is not taken"
        "language Development where { var : name }"
        (BuiltInType "Development")
      -- **Two grammars under one name** (2026-09-12) — every lookup of a
      -- language is a @lookup@, so the second was loaded and unreachable. It is
      -- 'DuplicateSignature' one layer over.
    , refusedGrammar "two grammars under one name"
        "language Tm where { var : name }\nlanguage Tm where { other : name }"
        (DuplicateLanguage "Tm")
    , refusedGrammar "a word that is neither the language nor name"
        "language Tm where { var : nonsense }"
        (BadGrammarItem "Tm" "nonsense")
    ]
  where
    tm = "language Tm where { var : name ; app : \"(\" Tm Tm \")\" }\n"

    refusedGrammar label src want =
      testCase label $ case load (src ++ "\nrule go :- then prove") of
        RuleFileRefused _ (RuleIllFormed es) | want `elem` es -> pure ()
        other -> assertFailure ("expected " ++ show want ++ ", got " ++ show other)

load :: String -> Response
load src = snd (loadRuleBases newSession [("t.thena.rules", "rule base t where\n" ++ src)])

-- Keeps @-Wall@ quiet about the imports the helpers above do not reach.
_unusedSessionShape :: Session -> [RuleBase]
_unusedSessionShape = rules . sessionMachine
