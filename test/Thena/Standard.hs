-- | The shipped rule base, read off disk, and what it is supposed to say.
--
-- **Two independent encodings of the same ten rules**, which is the whole
-- point. 'standardBases' reads @rules/standard.thena.rules@ through the same
-- path the REPL uses at startup; 'expectedStandard' is the same ten rules as
-- Haskell literals, moved here from @Thena.Rules@ when phase 22 deleted
-- @standardRules@. "Thena.RuleSyntaxTests" asserts they agree.
--
-- Phase 21's load-bearing check was written text against a Haskell literal.
-- Deleting the literal from the library would have left it comparing the file
-- with itself, so the literal moved rather than went — the standing lesson from
-- phases 2–5 about an invariant that must be checked by different code from the
-- code that maintains it.
module Thena.Standard
  ( standardBases
  , standardVisible
  , expectedStandard
  , expectedBase
  , withRules
  ) where

import Thena.Core.Term (GlobalName (..))
import Thena.Driver (Session (..), newSession)
import Thena.Engine (Machine (..))
import Thena.Ops
  ( Instr (..)
  , Op (..)
  , Operand (..)
  , Rule (..)
  , Test (..)
  )
import Thena.Ops (Value (VText))
import qualified Thena.Ops as Op
import Thena.Repl (loadStandardRules)
import Thena.Rules (RuleBase (..), allRules, ruleBase)

-- | The shipped base, loaded exactly as @thena@ loads it.
--
-- A failure to load is a fixture failure and errors loudly: every other test
-- that asks for the base would otherwise turn into an unrelated assertion about
-- an empty one. It is also, in itself, the regression that the shipped file
-- parses, resolves and validates.
standardBases :: IO [RuleBase]
standardBases = do
  (s, problems) <- loadStandardRules newSession
  case problems of
    [] -> pure (rules (sessionMachine s))
    ps -> error ("the shipped rule base did not load:\n" ++ unlines ps)

-- | Its rules, flattened — what 'Thena.Rules.resolveRule' wants as the rules
-- visible to a further rule being read.
standardVisible :: IO [Rule]
standardVisible = allRules <$> standardBases

-- | What @rules/standard.thena.rules@ is supposed to contain, in order.
--
-- **One rule per bare word the REPL already has for the life of a hole**
-- (thesis tables 2.7 and 2.8), chosen by the user 2026-08-23. @intro@ is two
-- rules and not one because table 2.8 has two.
expectedStandard :: [Rule]
expectedStandard =
  [ Rule (GlobalName "attack")     []    [FocusIsHole]                 [Do Attack]
  , Rule (GlobalName "try-core") ["t"] [FocusIsHole] [Do (Try (Ref "t"))]
  , Rule (GlobalName "abandon")    []    [FocusIsHole]                 [Do Abandon]
    -- **Two clauses of one name** (phase 23b): table 2.8 has two intro rules and
    -- they differ only in their head, which is exactly what a second clause is
    -- for. Before phase 23 a call could not backtrack, so they had to be
    -- @intro-pi@ and @intro-let@; now they are @intro@, and typing @intro@ at
    -- the REPL reaches whichever one applies.
  , Rule (GlobalName "intro")      []    [FocusIsGuess, GoalTypeIsPi]  [Do (Intro Nothing)]
  , Rule (GlobalName "intro")      []    [FocusIsGuess, GoalTypeIsLet] [Do (Intro Nothing)]
  , Rule (GlobalName "solve")      []    [FocusIsGuess]                [Do Solve]
  , Rule (GlobalName "regret")     []    [FocusIsGuess]                [Do Regret]
  , Rule (GlobalName "eliminate-core")  ["t"] [FocusIsHole]                 [Do (Op.Eliminate (Ref "t"))]
  , proveRule
  , proveGuess
  , fillRule
  , unifyRefine
  , applyRule
  ]
    ++ elaborateClauses

-- | Brady's @FILL@ — **his request, 2026-09-01** (MS4 phase 48):
--
-- **No @-core@ postfix, and his correction is why** (2026-09-03). Phase 38's
-- postfix frees a word for a /surface twin/ — @try@, @apply@, @eliminate@ and
-- @unify-refine@ are tactics the surface language will want the good names of.
-- It is not what marks an argument as core: the corners already do that.
--
-- Nothing is holding @fill@\'s word, because *"fill this hole with a term I
-- wrote"* **is @elaborate@**. And its argument is a core term for a reason that
-- has nothing to do with notation: **its caller is a rule, not a user.** By the
-- time an @elaborate@ clause calls it, the clause has just built the term with
-- @apply-to@ or @resolve-name@, and it arrives as a @Ref@ with no corners typed
-- anywhere. The surface parts are elaborated /after/ the fill — phases 41e and
-- 44 both found that filling last leaves the argument holes already solved, so
-- the @goto@s find nothing.
--
-- /"Can you maybe add two new tactics @fill@ and @solve@ and define
-- @unify-refine@ with them instead of just replacing @unify-refine@? It is
-- Conor's tactic and I would like to keep it."/
--
-- The @=@-binding is the load-bearing part: the term being refined with does
-- not yet have the goal's type, so it is parked in a definition until
-- unification makes the two converge, and only then attached.
--
-- **@unify-into@ and not @unify@**, which is where this rule and
-- "Thena.Elaborate"\'s inline @fill@ had come apart. Phase 41g gave the
-- elaborator the directed sibling — the term's type need only be /usable/
-- where the goal is wanted, and @prim-try@ on the next line does the real
-- check — and left this rule symmetric, so the same operation answered
-- differently depending on which one you reached it through.
fillRule :: Rule
fillRule = Rule (GlobalName "fill") ["t"] [FocusIsHole]
  [ Bind "n" (FreshName (Lit (VText "refined")))
  , Bind "x" (Define (Ref "n") (Ref "t"))
  , Bind "s" (Typing (Ref "x"))
  , Bind "g" Goal
  , Do (Op.UnifyInto (Ref "s") (Ref "g"))
  , Do (Try (Ref "x"))
  ]

-- | Thesis §2.7's two-phase tactic, less the claiming half (which is phase
-- 25's @apply@) and the arity search (phase 27's @fit@).
--
-- **Two calls, and that is the whole rule now** (MS4 phase 48): fill, then
-- discharge. It calls the /rules/ and not the primitives, so the seam Brady
-- needs — @FILL@, the two @FOCUS@es, @SOLVE@ — is one a caller can get at.
unifyRefine :: Rule
unifyRefine = Rule (GlobalName "unify-refine-core") ["t"] [FocusIsHole]
  [ Do (Call (GlobalName "fill") [Ref "t"])
  , Do (Call (GlobalName "solve") [])
  ]

-- | Phase 25's claiming half — §2.7's @naive-refine@ with the search left out.
--
-- Two instructions, and that is the phase's argument: @prim-apply@ builds the
-- saturated spine and 'unifyRefine' is what makes it fit, unchanged. @apply@
-- adds no capability the two of them did not already have.
applyRule :: Rule
applyRule = Rule (GlobalName "apply-core") ["f"] [FocusIsHole]
  [ Bind "s" (Op.Apply (Ref "f"))
  , Do (Call (GlobalName "unify-refine-core") [Ref "s"])
  ]

-- | A fresh session with 'expectedBase' installed, for the suites that drive
-- the driver without IO.
--
-- **Needed as of phase 23b**: @attack@, @try@ and @solve@ are rules now, so a
-- session with no base cannot run the commands every REPL test types.
withRules :: Session
withRules =
  newSession { sessionMachine = (sessionMachine newSession) { rules = expectedBase } }

-- | 'expectedStandard' as a base, for the suites that want one and do not want
-- IO. They were testing against a Haskell literal before phase 22 and still
-- are; "Thena.RuleSyntaxTests" is where the literal is tied to the file, and
-- "Thena.GoldenTests" is where the file itself is driven.
expectedBase :: [RuleBase]
expectedBase = [ruleBase "standard" Nothing "" expectedStandard]

-- | Search: every rule whose head passes, in definition order (MS4 phase 41).
--
-- @prove@ is a rule and no longer a special case in the driver — his ruling,
-- 2026-09-01. The op under it is @prim-prove@, the good word having gone to the
-- rule (phase 23b's convention).
--
-- **Two clauses, and that is how the rule language spells a disjunction** —
-- @intro@ has had two for the same reason since phase 15. Search makes sense
-- wherever a component is focused, and there is no single test for /hole or
-- guess/; one clause with @focus-is-hole@ would have made @prove@ silent at a
-- guess, where the base has @intro@, @solve@ and @regret@ waiting, and an
-- empty head would have offered it in the core fragment, where nothing can
-- act at all.
proveRule :: Rule
proveRule = Rule (GlobalName "prove") [] [FocusIsHole] [Do Prove]

proveGuess :: Rule
proveGuess = Rule (GlobalName "prove") [] [FocusIsGuess] [Do Prove]

-- | Elaboration (MS4 phase 41): one clause over the large instruction.
--
-- It replaces @elab-var@, whose head asked about the retired hint and whose
-- body resolved it. Step 2 of the two-step (@MS4.md@) is what turns this into
-- a clause per surface node.
-- | Elaboration, **one clause per surface node** (MS4 phase 49, step 2).
--
-- **Every clause names the node it is for**, so exactly one head matches any
-- term and a call to @elaborate@ never has a choice to make. His ruling,
-- 2026-09-03, on head predicates: /"adding them is not payed in design. They
-- are not a design decision. If we never use them after MS4, we just drop them
-- during a cleanup refactor."/
--
-- The clauses whose body is still @prim-elaborate@ are the cases step 2 has not
-- reached; each later phase fills one in, and when the last is done
-- @prim-elaborate@ and "Thena.Elaborate" go together.
elaborateClauses :: [Rule]
elaborateClauses =
  [ clause SurfaceIsName
      [ Bind "w" (Op.SurfaceNameOf (Ref "t"))
      , Bind "x" (Op.ResolveName (Ref "w"))
      , call "fill" [Ref "x"], call "solve" []
      ]
  , clause SurfaceIsUniverse
      [ Bind "u" (Op.SurfaceUniverseOf (Ref "t"))
      , call "fill" [Ref "u"], call "solve" []
      ]
  , clause SurfaceIsUniverseOpen
      [ Bind "u" Op.FreshUniverse
      , call "fill" [Ref "u"], call "solve" []
      ]
    -- **Two empty bodies**, which the rule grammar did not admit before phase
    -- 49: @E⟦_⟧@ /is/ do nothing, and a clause that does nothing is a different
    -- answer from a clause that does not match.
  , clause SurfaceIsPlaceholder []
  , clause SurfaceIsHole []
    -- Still in Haskell, behind @prim-elaborate@: the three cases that iterate —
    -- a λ over its binder group, an application over its arguments against the
    -- head's plicities, an @elim@ over its fields. The rule language has no
    -- lists (MS4 phase 49b).
    -- **Brady's split, as two clauses** (MS4 phase 49d). The first is
    -- @E⟦x ⃗a⟧@, which begins with @EXPAND@ and is still in Haskell because
    -- matching written arguments against a head's plicities is a computation
    -- over two lists (@ms4\/CLOSEOUT.md@ 28). **It may fail and fall through**
    -- to the second, which is what the Haskell @case@ did: a partial
    -- application of a head with recorded plicities is an ordinary binary
    -- application.
  , Rule (GlobalName "elaborate") ["t"]
      [FocusIsHole, SurfaceIsApp (Ref "t"), AppHeadIsName (Ref "t")]
      [Do (Op.Elaborate (Ref "t"))]
  , Rule (GlobalName "elaborate") ["t"]
      [FocusIsHole, SurfaceIsApp (Ref "t"), AppArgsAreExplicit (Ref "t")]
      [ Bind "h" Here
      , Bind "dn" (FreshName (Lit (VText "A")))
      , Bind "u1" Op.FreshUniverse
      , Bind "d" (Claim (Ref "dn") (Ref "u1"))
      , Bind "cn" (FreshName (Lit (VText "B")))
      , Bind "u2" Op.FreshUniverse
      , Bind "c" (Claim (Ref "cn") (Ref "u2"))
      , Bind "ar" (Arrow (Ref "d") (Ref "c"))
      , Bind "fn" (FreshName (Lit (VText "f")))
      , Bind "f" (Claim (Ref "fn") (Ref "ar"))
      , Bind "sn" (FreshName (Lit (VText "s")))
      , Bind "sv" (Claim (Ref "sn") (Ref "d"))
      , Bind "ap" (ApplyTo (Ref "f") (Ref "sv"))
      , call "fill" [Ref "ap"]
      , Do (Goto (Ref "f"))
      , Bind "g" (Op.AppFunction (Ref "t"))
      , call "elaborate" [Ref "g"]
      , Do (Goto (Ref "sv"))
      , Bind "a" (Op.AppLastArgument (Ref "t"))
      , call "elaborate" [Ref "a"]
      , Do (Goto (Ref "h")), call "solve" []
      ]
    -- **The group is walked by recursion**, not by an iterating instruction:
    -- each helper peels one binder and calls itself on the tail, so the surface
    -- term is its own counter (MS4 phase 49c). Attacking once per binder
    -- instead would nest the λs and put an extra @let@ round each — a different
    -- proof term.
  , clause SurfaceIsLambda
      [ Bind "h" Here
      , Do Attack
      , call "intro-binders" [Ref "t"]
      , Do Into
      , call "enter-binders" [Ref "t"]
      , Bind "b" (Op.LambdaBody (Ref "t"))
      , call "elaborate" [Ref "b"]
      , Do (Goto (Ref "h")), call "solve" []
      ]
    -- **The parts are read before the development is touched**, so a binder
    -- with no type fails without having claimed or quantified anything.
  , clause SurfaceIsForall
      [ Bind "x" (Op.ForallName (Ref "t"))
      , Bind "ty" (Op.ForallDomain (Ref "t"))
      , Bind "tl" (Op.ForallTail (Ref "t"))
      , Bind "h" Here
      , Bind "dn" (FreshName (Lit (VText "A")))
      , Bind "u" Op.FreshUniverse
      , Bind "d" (Claim (Ref "dn") (Ref "u"))
      , Do Attack
      , Do (Op.Quantify (Ref "x") (Ref "d"))
      , Do Into, Do Along
      , Bind "c" Here
      , Do (Goto (Ref "d"))
      , call "elaborate" [Ref "ty"]
      , Do (Goto (Ref "c"))
      , call "elaborate" [Ref "tl"]
      , Do (Goto (Ref "h")), call "solve" []
      ]
  , clause SurfaceIsArrow
      [ Bind "h" Here
      , Bind "dn" (FreshName (Lit (VText "A")))
      , Bind "u1" Op.FreshUniverse
      , Bind "d" (Claim (Ref "dn") (Ref "u1"))
      , Bind "cn" (FreshName (Lit (VText "B")))
      , Bind "u2" Op.FreshUniverse
      , Bind "c" (Claim (Ref "cn") (Ref "u2"))
      , Bind "ar" (Arrow (Ref "d") (Ref "c"))
      , call "fill" [Ref "ar"]
      , Do (Goto (Ref "d"))
      , Bind "a" (Op.ArrowDomain (Ref "t"))
      , call "elaborate" [Ref "a"]
      , Do (Goto (Ref "c"))
      , Bind "b" (Op.ArrowCodomain (Ref "t"))
      , call "elaborate" [Ref "b"]
      , Do (Goto (Ref "h")), call "solve" []
      ]
    -- **Two clauses for @let@**, because the annotation is optional and the
    -- head language has no negation.
  , Rule (GlobalName "elaborate") ["t"] [FocusIsHole, LetIsAnnotated (Ref "t")]
      (letPrelude ++
        [ Do (Goto (Ref "x"))
        , Bind "ty" (Op.LetType (Ref "t"))
        , call "elaborate" [Ref "ty"]
        ] ++ letBody)
  , Rule (GlobalName "elaborate") ["t"] [FocusIsHole, LetIsBare (Ref "t")]
      (letPrelude ++ letBody)
  , clause SurfaceIsAscription
      [ Bind "h" Here
      , Bind "xn" (FreshName (Lit (VText "X")))
      , Bind "u" Op.FreshUniverse
      , Bind "x" (Claim (Ref "xn") (Ref "u"))
      , Do (Goto (Ref "x"))
      , Bind "ty" (Op.AscriptionType (Ref "t"))
      , call "elaborate" [Ref "ty"]
      , Do (Goto (Ref "h"))
      , Bind "g" Goal
      , Do (Op.UnifyInto (Ref "x") (Ref "g"))
      , Bind "e" (Op.AscriptionTerm (Ref "t"))
      , call "elaborate" [Ref "e"]
      ]
  , clause SurfaceIsElim
      [ Bind "a" (Op.ElimSpine (Ref "t"))
      , call "elaborate" [Ref "a"]
      ]
  , clause SurfaceIsDo [Do (Op.Play (Ref "t"))]
  ]
    ++ binderWalkers
  where
    clause test = Rule (GlobalName "elaborate") ["t"] [FocusIsHole, test (Ref "t")]
    call nm as = Do (Call (GlobalName nm) as)

    letPrelude =
      [ Bind "h" Here
      , Bind "xn" (FreshName (Lit (VText "X")))
      , Bind "u" Op.FreshUniverse
      , Bind "x" (Claim (Ref "xn") (Ref "u"))
      , Bind "vn" (FreshName (Lit (VText "V")))
      , Bind "v" (Claim (Ref "vn") (Ref "x"))
      ]
    letBody =
      [ Do (Goto (Ref "v"))
      , Bind "val" (Op.LetValue (Ref "t"))
      , Do (Call (GlobalName "elaborate") [Ref "val"])
      , Do (Goto (Ref "h"))
      , Bind "w" (Op.LetName (Ref "t"))
      , Do (Define (Ref "w") (Ref "v"))
      , Bind "b" (Op.LetBody (Ref "t"))
      , Do (Call (GlobalName "elaborate") [Ref "b"])
      ]

-- | The two rules that walk a λ's binder group (MS4 phase 49c).
--
-- **Recursion is how the rule language loops.** A body is a straight run of
-- instructions with no iteration and no accumulator; a clause that peels one
-- binder and calls itself on the tail gets the run of @prim-intro@s the λ case
-- needs, and the surface term is the counter.
--
-- Two clauses each, on two positive tests, for @let@'s reason: the head
-- language has no negation.
binderWalkers :: [Rule]
binderWalkers =
  [ Rule (GlobalName "intro-binders") ["t"]
      [FocusIsGuess, LambdaBindsMore (Ref "t")]
      [ Bind "x" (Op.LambdaName (Ref "t"))
      , Do (Intro (Just (Ref "x")))
      , Bind "tl" (Op.LambdaTail (Ref "t"))
      , Do (Call (GlobalName "intro-binders") [Ref "tl"])
      ]
  , Rule (GlobalName "intro-binders") ["t"]
      [FocusIsGuess, LambdaBindsOne (Ref "t")]
      [ Bind "x" (Op.LambdaName (Ref "t"))
      , Do (Intro (Just (Ref "x")))
      ]
    -- The binders are the count and nothing else about them is read.
  , Rule (GlobalName "enter-binders") ["t"]
      [FocusIsComponent, LambdaBindsMore (Ref "t")]
      [ Do Along
      , Bind "tl" (Op.LambdaTail (Ref "t"))
      , Do (Call (GlobalName "enter-binders") [Ref "tl"])
      ]
  , Rule (GlobalName "enter-binders") ["t"]
      [FocusIsComponent, LambdaBindsOne (Ref "t")]
      [Do Along]
  ]
