-- | The cursor (§4).
--
-- The shape of this suite follows phase 3's lesson, which phases 2 and 3 both
-- measured: a round trip reads and writes with the same code, so a
-- self-consistent error agrees with itself. 'rebuild' after a move is the round
-- trip here, and it is the /weak/ test — a move that pushed the wrong step and
-- an @unwind@ that read it back the same wrong way would pass it happily.
--
-- What does the work is Γ. 'context' is derived from the prefix by a different
-- rule from the one the moves use to build it (§4.5), so an exact-list
-- assertion on Γ at a hand-picked position catches a mis-pushed step that no
-- round trip can see. The guess cases are the sharpest: @Γ_(?x ≐ P : S . p) =
-- Γ_P@ is invisible to everything else in this file.
module Thena.CursorTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Level (Level (..), LevelVar (..), levelOfNat)
import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Term (Core (..), Ident (..), close, fresh)
import Thena.Development.Component (Component (..))
import Thena.Development.Cursor
  ( Cursor
  , Focus (..)
  , Part (..)
  , along
  , back
  , context
  , crossType
  , crossValue
  , down
  , enter
  , expectedType
  , focus
  , insertAbove
  , into
  , overLevels
  , rebuild
  , replaceFocus
  )
import Thena.Development.Partial (Constraint (..), Partial (..))
import Thena.Errors (MoveError (..))
import Thena.Fixtures
  ( allFour
  , guessShadowing
  , idMidway
  , richTypes
  , trailingLam
  , withConstraint
  )
import Thena.Repl (renderCursor, renderWhere)

tests :: TestTree
tests =
  testGroup
    "Thena.Cursor"
    [ testGroup "enter and rebuild" enterTests
    , testGroup "every position, walked" walkTests
    , testGroup "context" contextTests
    , testGroup "expected type" typeTests
    , testGroup "impossible moves" refusalTests
    , testGroup "changing the development" changeTests
    , testGroup "display" displayTests
    , testGroup "a level solution reaches every core term" levelTests
    ]

-- --------------------------------------------------------------------------
-- A test-local way to name a position
-- --------------------------------------------------------------------------

-- | A descent, with the word the user would type for it.
data Move = Move String (Int -> Cursor -> Either MoveError (Cursor, Int))

instance Show Move where
  show (Move w _) = w

keeping :: (Cursor -> Either MoveError Cursor) -> Int -> Cursor -> Either MoveError (Cursor, Int)
keeping g n cur = fmap (\cur' -> (cur', n)) (g cur)

mAlong, mInto, mCrossType, mCrossValue :: Move
mAlong      = Move "along"     (keeping along)
mInto       = Move "into"      (keeping into)
mCrossType  = Move "cross type" (keeping crossType)
mCrossValue = Move "cross val"  (keeping crossValue)

mDown :: Part -> Move
mDown part = Move (show part) (down part)

-- | The counter every test starts from. Above every 'Var' the fixtures mint, so
-- a variable opened by a descent can never collide with one already there.
start :: Int
start = 100

-- | Follow a sequence of descents from the root.
--
-- It calls 'error' on a move that fails, and deliberately: a test that meant to
-- stand at a position and could not get there is a broken test, not a failing
-- assertion, and saying which move died is the only useful thing to report.
at :: Partial -> [Move] -> Cursor
at p = fst . foldl go (enter p, start)
  where
    go (cur, n) m@(Move _ f) = case f n cur of
      Right r -> r
      Left e  -> error ("cursor test: " ++ show m ++ " failed with " ++ show e)

-- --------------------------------------------------------------------------
-- enter and rebuild
-- --------------------------------------------------------------------------

everyFixture :: [(String, Partial)]
everyFixture =
  [ ("idMidway", idMidway)
  , ("withConstraint", withConstraint)
  , ("allFour", allFour)
  , ("guessShadowing", guessShadowing)
  , ("trailingLam", trailingLam)
  , ("richTypes", richTypes)
  ]

enterTests :: [TestTree]
enterTests =
  [ testCase (name ++ ": rebuild . enter is the identity") $
      rebuild (enter p) @?= p
  | (name, p) <- everyFixture
  ]

-- --------------------------------------------------------------------------
-- Every position, walked
-- --------------------------------------------------------------------------

-- | Every 'Part' a descent could name, including positions past the end of a
-- list, so that 'down' is asked for fields the focus does not have as well as
-- ones it does.
everyPart :: [Part]
everyPart =
  [Fun, Arg, Dom, Cod, Val, Type, Body, Motive, Target]
    ++ concat [[Param k, Method k, Index k, CanonArg k] | k <- [0 .. 3]]

everyMove :: [Move]
everyMove = [mAlong, mInto, mCrossType, mCrossValue] ++ map mDown everyPart

-- | Every cursor reachable from the root by descents alone, paired with the way
-- it was reached.
--
-- Descents only, so the search is a walk over a finite tree and needs no
-- visited set: each descent strictly consumes structure, and 'along' from a
-- trailing term is refused, which is what ends it. 'back' is excluded here on
-- purpose — it is what each node is then tested against.
positions :: Partial -> [([Move], Cursor)]
positions p = go [] (enter p, start)
  where
    go route (cur, n) =
      (reverse route, cur)
        : [ node
          | m@(Move _ f) <- everyMove
          , Right r <- [f n cur]
          , node <- go (m : route) r
          ]

walkTests :: [TestTree]
walkTests =
  concat
    [ [ testCase (name ++ ": rebuild is the identity everywhere") $
          case [ (route, rebuild cur) | (route, cur) <- positions p, rebuild cur /= p ] of
            []            -> pure ()
            (route, q) : _ ->
              assertFailure ("at " ++ show route ++ " rebuild gave\n" ++ show q)
      , testCase (name ++ ": back undoes every descent") $
          case badBacks p of
            []                  -> pure ()
            (route, m, r) : _ ->
              assertFailure
                ("at " ++ show route ++ ", " ++ show m ++ " then back gave\n" ++ show r)
      , testCase (name ++ ": back is refused only at the root") $
          [ map show route
          | (route, cur) <- positions p
          , Left AtRoot <- [back cur]
          ]
            @?= [[]]
      ]
    | (name, p) <- everyFixture
    ]

-- | Every (position, descent) pair whose 'back' does not restore the position.
--
-- This is the assertion that pins closing a core binder: descending into a Π's
-- codomain opens its 'Thena.Core.Term.Scope' with a fresh variable, and coming
-- back must 'close' over that same variable. A move that opened with one
-- variable and closed over another would still rebuild the whole development
-- correctly — 'rebuild' unwinds the same step that was pushed — so only this
-- catches it.
badBacks :: Partial -> [([Move], Move, Either MoveError Cursor)]
badBacks p =
  [ (route, m, back cur')
  | (route, cur) <- positions p
  , m@(Move _ f) <- everyMove
  , Right (cur', _) <- [f start cur]
  , back cur' /= Right cur
  ]

-- --------------------------------------------------------------------------
-- context — §4.5
-- --------------------------------------------------------------------------

-- | Γ as names and nothing else. The types are checked separately where they
-- matter; here what is being pinned is /which entries are in it and in what
-- order/, and a list of identifiers says that without a page of terms.
names :: Context -> [String]
names = map entryName
  where
    entryName e = case e of
      Hypothesis _ (Ident i) _   -> i
      Definition _ (Ident i) _ _ -> i

contextTests :: [TestTree]
contextTests =
  [ testCase "at the root, nothing is in scope — you are on the first link, not past it" $
      names (context (at idMidway [])) @?= []
  , testCase "one step along adds exactly the link walked past" $
      names (context (at idMidway [mAlong])) @?= ["A"]
  , testCase "a guess body does NOT see the hole it is filling (§2.2.1)" $
      names (context (at idMidway [mAlong, mInto])) @?= ["A"]
  , testCase "a guess body's own links do enter Γ" $
      names (context (at idMidway [mAlong, mInto, mAlong])) @?= ["A", "a"]
  , testCase "the guess binder stays out however deep the body goes" $
      names (context (at idMidway [mAlong, mInto, mAlong, mAlong])) @?= ["A", "a", "h"]
  , testCase "a nested guess: neither hole is in scope in the inner body" $
      names (context (at guessShadowing [mInto])) @?= []

  , testCase "a constraint binds nothing, so walking past one leaves Γ alone" $
      names (context (at withConstraint [mAlong, mAlong, mAlong])) @?= ["A", "a", "h"]
  , testCase "and Ξ is the constraint's own telescope, not the development's" $
      names (context (at withConstraint [mAlong, mAlong, mAlong, mAlong]))
        @?= ["A", "a", "h"]

  , testCase "crossing into a type adds nothing — a hole's type may not mention it" $
      names (context (at richTypes [mAlong, mAlong, mAlong, mCrossType]))
        @?= ["A", "f", "d"]
  , testCase "descending into a Π's domain opens no binder" $
      names (context (at richTypes [mAlong, mAlong, mAlong, mCrossType, mDown Dom]))
        @?= ["A", "f", "d"]
  , testCase "descending into a Π's codomain opens one" $
      names (context (at richTypes [mAlong, mAlong, mAlong, mCrossType, mDown Cod]))
        @?= ["A", "f", "d", "x"]
  , testCase "a let body opens a DEFINITION, not a hypothesis" $
      let ctx = context (at richTypes [mAlong, mAlong, mAlong, mCrossType, mDown Cod, mDown Body])
       in (names ctx, [i | Definition _ (Ident i) _ _ <- ctx])
            @?= (["A", "f", "d", "x", "y"], ["d", "y"])
  , testCase "a lambda body opens a hypothesis" $
      let ctx = context (at richTypes [mAlong, mAlong, mCrossValue, mDown Body])
       in (names ctx, [i | Definition _ (Ident i) _ _ <- ctx]) @?= (["A", "f", "z"], [])
  , testCase "a definition's value sees the chain above it and nothing more" $
      names (context (at richTypes [mAlong, mAlong, mCrossValue])) @?= ["A", "f"]
  ]

-- --------------------------------------------------------------------------
-- expectedType — §4.0 D2
-- --------------------------------------------------------------------------

type0 :: Core
type0 = Universe (LZero)

typeTests :: [TestTree]
typeTests =
  [ testCase "on a component, its own type" $
      expectedType (at allFour []) @?= Just type0
  , testCase "on a constraint, the type the two sides are compared at" $
      case focus (at withConstraint [mAlong, mAlong, mAlong]) of
        OnConstraint (Equate _ _ _ ty) ->
          expectedType (at withConstraint [mAlong, mAlong, mAlong]) @?= Just ty
        f -> assertFailure ("expected a constraint focus, got " ++ show f)
  , testCase "beside a definition's value, the type written next to it" $
      expectedType (at richTypes [mAlong, mAlong, mCrossValue])
        @?= Just (componentTypeOf (at richTypes [mAlong, mAlong]))
  , testCase "a guess body's trailing term must have the guess's type (§4.5)" $
      expectedType (at idMidway [mAlong, mInto, mAlong, mAlong])
        @?= Just (componentTypeOf (at idMidway [mAlong]))
  , testCase "the top-level trailing term: nothing is written down, so nothing is claimed" $
      expectedType (at allFour [mAlong, mAlong, mAlong, mAlong]) @?= Nothing
  , testCase "a focus that IS a type: its level needs inference, and says so" $
      expectedType (at allFour [mCrossType]) @?= Nothing
  , testCase "inside a core term: infer's job, phase 8" $
      expectedType (at richTypes [mAlong, mAlong, mAlong, mCrossType, mDown Dom]) @?= Nothing
  ]

componentTypeOf :: Cursor -> Core
componentTypeOf cur = case focus cur of
  OnComponent (Assume _ _ s)   -> s
  OnComponent (Define _ _ _ s) -> s
  OnComponent (Claim _ _ s)    -> s
  OnComponent (Guess _ _ _ s)  -> s
  f                            -> error ("not on a component: " ++ show f)

-- --------------------------------------------------------------------------
-- Impossible moves are structured errors — §4.0 C4, §12 invariant 2
-- --------------------------------------------------------------------------

refusalTests :: [TestTree]
refusalTests =
  [ testCase "back, at the root" $
      back (at allFour []) @?= Left AtRoot
  , testCase "into, on something that is not a guess" $
      into (at allFour []) @?= Left NotAGuess
  , testCase "into, on a constraint — a constraint has no body to enter" $
      into (at withConstraint [mAlong, mAlong, mAlong]) @?= Left NotAGuess
  , testCase "cross val, on a hole" $
      crossValue (at allFour [mAlong, mAlong]) @?= Left NotADefinition
  , testCase "cross type, on a constraint — decided against, and it says so" $
      crossType (at withConstraint [mAlong, mAlong, mAlong])
        @?= Left NoCrossingIntoAConstraint
  , testCase "along, in the core fragment" $
      along (at allFour [mCrossType]) @?= Left NotOnTheSpine
  , testCase "cross, in the core fragment — it happens once, or not at all" $
      crossType (at allFour [mCrossType]) @?= Left NotOnTheSpine
  , testCase "a core descent, on the spine" $
      down Fun start (at allFour []) @?= Left NotInCore
  , testCase "a field the focused form has not" $
      down Cod start (at richTypes [mAlong, mAlong, mCrossValue]) @?= Left NoSuchPart
  , testCase "a list position past the end" $
      down (Param 1) start (at allFour [mCrossType]) @?= Left NoSuchPart
  , testCase "replaceFocus, in the core fragment" $
      replaceFocus (Trailing type0) (at allFour [mCrossType]) @?= Left NotOnTheSpine
  ]

-- --------------------------------------------------------------------------
-- Changing the development
-- --------------------------------------------------------------------------

changeTests :: [TestTree]
changeTests =
  [ testCase "insertAbove goes above the focus, and the focus does not move" $
      let cur  = at allFour [mAlong]
          cur' = insertAbove newBinder cur
       in (focus cur' == focus cur, names (context cur')) @?= (True, ["A", "n"])
  , testCase "insertAbove at the root makes the new component outermost" $
      rebuild (insertAbove newBinder (enter allFour)) @?= Under newBinder allFour
  , testCase "insertAbove in the core fragment goes above the component crossed into" $
      let cur = at richTypes [mAlong, mAlong, mAlong, mCrossType, mDown Cod]
       in names (context (insertAbove newBinder cur)) @?= ["A", "f", "d", "n", "x"]
  , testCase "replaceFocus discards the focus and lands on the replacement's head" $
      let cur = at allFour [mAlong]
       in fmap rebuild (replaceFocus (Trailing type0) cur)
            @?= Right (Under (headOf allFour) (Trailing type0))
  ]
  where
    newBinder = Assume (fst (fresh 90)) (Ident "n") type0
    headOf (Under c _) = c
    headOf p           = error ("not a chain: " ++ show p)

-- --------------------------------------------------------------------------
-- Display — §4.0 J1 and J2
-- --------------------------------------------------------------------------

-- | Exact strings, on purpose.
--
-- A marker in the wrong gutter and a breadcrumb naming the wrong link both
-- print perfectly legal output, so nothing weaker than the whole string can
-- tell them apart. This is phase 2's and phase 3's finding applied to the two
-- things this phase adds.
displayTests :: [TestTree]
displayTests =
  [ testCase ":show marks the link the focus is on" $
      renderCursor start (at allFour [mAlong, mAlong])
        @?= unlines'
          [ "  λ (A : Type₀) ->"
          , "  let d = A : Type₀ in"
          , "▶ let ? h : A in"
          , "  let ? g : A ≐ ("
          , "    h"
          , "  ) in"
          , "  g"
          ]
  , testCase ":show marks a line inside a guess body, indent and all" $
      renderCursor start (at allFour [mAlong, mAlong, mAlong, mInto])
        @?= unlines'
          [ "  λ (A : Type₀) ->"
          , "  let d = A : Type₀ in"
          , "  let ? h : A in"
          , "  let ? g : A ≐ ("
          , "▶   h"
          , "  ) in"
          , "  g"
          ]
  , testCase ":show marks the component a core focus is inside" $
      renderCursor start (at allFour [mAlong, mCrossType])
        @?= unlines'
          [ "  λ (A : Type₀) ->"
          , "▶ let d = A : Type₀ in"
          , "  let ? h : A in"
          , "  let ? g : A ≐ ("
          , "    h"
          , "  ) in"
          , "  g"
          ]
  , testCase ":show marks a constraint" $
      renderCursor start (at withConstraint [mAlong, mAlong, mAlong])
        @?= unlines'
          [ "  λ (A : Type₀) ->"
          , "  λ (a : A) ->"
          , "  let ? h : A in"
          , "▶ (x : A) ⊢ h ≟ x : A ▸"
          , "  h"
          ]

  , testCase ":where on the spine" $
      renderWhere start (at idMidway [mAlong])
        @?= [ "focus"
            , "  let ? id' : A -> A ≐ ("
            , "path"
            , "  root ▸ A"
            , "context"
            , "  A : Type₀"
            , "type"
            , "  A -> A"
            ]
  , testCase ":where inside a guess — the hole is on the path and not in Γ" $
      renderWhere start (at idMidway [mAlong, mInto])
        @?= [ "focus"
            , "  λ (a : A) ->"
            , "path"
            , "  root ▸ A ▸ ≐ id'"
            , "context"
            , "  A : Type₀"
            , "type"
            , "  A"
            ]
  , testCase ":where in the core fragment names every step of the way in" $
      renderWhere start (at richTypes [mAlong, mAlong, mAlong, mCrossType, mDown Cod, mDown Body])
        @?= [ "focus"
            , "  f y"
            , "path"
            , "  root ▸ A ▸ f ▸ d ▸ type of h ▸ cod ▸ body"
            , "context"
            , "  A : Type₀"
            , "  f : A -> A"
            , "  d = λ (z : A) -> z : A -> A"
            , "  x : A"
            , "  y = x : A"
            ]
  , testCase ":where at a position with nothing in scope and no type written down" $
      renderWhere start (at allFour [mAlong, mAlong, mAlong, mAlong])
        @?= [ "focus"
            , "  g"
            , "path"
            , "  root ▸ A ▸ d ▸ h ▸ g ▸ the term"
            , "context"
            , "  A : Type₀"
            , "  d = A : Type₀"
            , "  h : A"
            , "  g : A"
            ]
  ]

unlines' :: [String] -> String
unlines' = foldr1 (\a b -> a ++ "\n" ++ b)

-- Kept honest: 'close' and 'Level' are used by the fixtures this module reads,
-- and by 'type0' above.
_unused :: Core
_unused = Pi (Ident "_") type0 (close (fst (fresh 0)) type0)

-- --------------------------------------------------------------------------
-- overLevels (MS3 phase 33)
-- --------------------------------------------------------------------------

-- | A development with the same level written into every place a 'Level' can
-- occur, so one substitution has to find all of them.
--
-- Not a valid development and not meant to be: what is under test is that the
-- traversal is total over the /shape/, and a shape is what this is.
metaEverywhere :: Level -> Partial
metaEverywhere l =
  let (vA, n1) = fresh 700
      (vd, n2) = fresh n1
      (vh, n3) = fresh n2
      (vg, n4) = fresh n3
      (vx, _)  = fresh n4
      u        = Universe l
   in Under (Assume vA (Ident "A") u)
        (Under (Define vd (Ident "d") u (Universe (LSuc l)))
          (Pending (Equate [Hypothesis vx (Ident "x") u] (Free vx) (Free vx) u)
            (Under (Claim vh (Ident "h") (Pi (Ident "x") u (close vx u)))
              (Under (Guess vg (Ident "g") (Trailing u) u)
                (Trailing u)))))

-- | **The check that matters is that the focus is not an exception.**
-- 'overComponents' has to skip a focused component, because promoting a 'Claim'
-- to a 'Define' would strand the 'Slot' naming its kind; a level substitution
-- changes no constructor, so leaving the focus out would just be a place a
-- solution failed to reach — and a hole standing on its own type while its
-- level is solved is exactly where that would bite.
levelTests :: [TestTree]
levelTests =
  [ reaches "from the root" []
  , reaches "with a component above the focus" [mAlong]
  , reaches "standing on a constraint" [mAlong, mAlong]
  , reaches "standing on the hole whose type is being rewritten"
      [mAlong, mAlong, mAlong]
  , reaches "inside a guess" [mAlong, mAlong, mAlong, mAlong, mInto]
  , -- @Dom@ leaves a 'Scope' in the term step, which is the one field the
    -- traversal cannot reach with plain 'substLevelsIn'.
    reaches "under a binder's domain, where the sibling is a Scope"
      [mAlong, mAlong, mAlong, mCrossType, mDown Dom]
  , reaches "under a binder's codomain, where the sibling is not"
      [mAlong, mAlong, mAlong, mCrossType, mDown Cod]
  ]
  where
    meta  = LMeta 900
    zero  = levelOfNat 0
    solve = [(meta, zero)]

    reaches what moves = testCase what $
      let cur  = at (metaEverywhere (LVar meta)) moves
          cur' = overLevels solve cur
          want = at (metaEverywhere zero) moves
       in (rebuild cur', focus cur' == focus want) @?= (metaEverywhere zero, True)
