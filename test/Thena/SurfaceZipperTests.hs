-- | The surface zipper (MS4 phase 46).
--
-- **The law is that a move loses nothing**: @root (into… z) == root z@. It is
-- worth testing rather than reading off the code because 'Thena.Surface.Zipper'
-- maintains the path in one place — each move pushes a frame — and reads it in
-- another — @rebuild@, written per frame. A frame that records the wrong
-- siblings, or a pair of moves whose frames are swapped, type-checks and is
-- caught here and nowhere else. That is the standing testing lesson's
-- /"look for the invariant that is checked by different code from the code that
-- maintains it"/.
--
-- Every descent a clause of @elaborate@ performs is covered, and the tests
-- destructure each node the way that module does, so the two agree about which
-- child a move is meant to reach.
module Thena.SurfaceZipperTests (tests) where

import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

import Thena.Surface.Concrete
  (Plicity (..), Surface (..), SurfaceArg (..), SurfaceBinder (..))
import Thena.Surface.Zipper

tests :: TestTree
tests =
  testGroup
    "the surface zipper"
    [ testGroup "a term focused at its root" [rootIsWhole, focusIsWhole]
    , testGroup "every move reaches the child it names" (map child descents)
    , testGroup "and no move loses the term" (map preserved descents)
    , testGroup "and puts a changed focus back where it came from" markers
    , testGroup "a Π binder group" [groupPeeled, groupRebuilt, nestingCollapses]
    ]

-- --------------------------------------------------------------------------
-- Fixtures — one per node kind, each with a distinguishable subterm

nm :: String -> Surface
nm = SurfaceName

-- | @f a b@
appTerm :: Surface
appTerm = SurfaceApp (nm "f") (SurfaceArg Explicit (nm "a") :| [SurfaceArg Explicit (nm "b")])

-- | @λ x y -> body@
lamTerm :: Surface
lamTerm = SurfaceLam (bare "x" :| [bare "y"]) (nm "body")
  where bare x = SurfaceBinder Explicit x Nothing

-- | @∀ (A : dom) -> cod@
piTerm :: Surface
piTerm = SurfacePi (SurfaceBinder Explicit "A" (Just (nm "dom")) :| []) (nm "cod")

-- | @∀ (A : dom) (b : mid) -> cod@ — one group, two binders
piGroup :: Surface
piGroup =
  SurfacePi
    ( SurfaceBinder Explicit "A" (Just (nm "dom"))
        :| [SurfaceBinder Explicit "b" (Just (nm "mid"))] )
    (nm "cod")

arrowTerm :: Surface
arrowTerm = SurfaceArrow (nm "dom") (nm "cod")

-- | @let x : ann = val in body@
letTerm :: Surface
letTerm = SurfaceLet "x" (Just (nm "ann")) (nm "val") (nm "body")

annotTerm :: Surface
annotTerm = SurfaceAnnot (nm "e") (nm "ty")

-- | @elim D (p) mot (m1 m2) (i) tgt@
elimTerm :: Surface
elimTerm = SurfaceElim "D" [nm "p"] (nm "mot") [nm "m1", nm "m2"] [nm "i"] (nm "tgt")

-- --------------------------------------------------------------------------
-- The descent table
--
-- Each row is a move exactly as a clause makes it: the whole term,
-- the child the move should reach, and the zipper the move produces from the
-- term's root.

data Descent = Descent String Surface Surface SurfaceZipper

descents :: [Descent]
descents =
  [ -- The spine, folded right to left: @f a b@ has function part @f a@ and
    -- last argument @b@ at position 1.
    d "into the function part of a spine" appTerm (SurfaceApp (nm "f") (arg "a" :| []))
      (intoFun (arg "b") (SurfaceApp (nm "f") (arg "a" :| [])) (rootedAt appTerm))
  , d "into a spine's first argument" appTerm (nm "a")
      (intoArg (nm "f") appArgs 0 (nm "a") (rootedAt appTerm))
  , d "into a spine's last argument" appTerm (nm "b")
      (intoArg (nm "f") appArgs 1 (nm "b") (rootedAt appTerm))
  , d "into a lambda's body" lamTerm (nm "body")
      (intoLamBody (lamBinders lamTerm) (nm "body") (rootedAt lamTerm))
  , d "into a Π's domain" piTerm (nm "dom")
      (intoPiDomain Explicit "A" [] (nm "cod") (nm "dom") (rootedAt piTerm))
  , d "into a Π's codomain" piTerm (nm "cod")
      (intoPiTail (SurfaceBinder Explicit "A" (Just (nm "dom"))) (nm "cod")
         (rootedAt piTerm))
  , d "into an arrow's domain" arrowTerm (nm "dom")
      (intoArrowDomain (nm "cod") (nm "dom") (rootedAt arrowTerm))
  , d "into an arrow's codomain" arrowTerm (nm "cod")
      (intoArrowCodomain (nm "dom") (nm "cod") (rootedAt arrowTerm))
  , d "into a let's annotation" letTerm (nm "ann")
      (intoLetType "x" (nm "val") (nm "body") (nm "ann") (rootedAt letTerm))
  , d "into a let's value" letTerm (nm "val")
      (intoLetValue "x" (Just (nm "ann")) (nm "body") (nm "val") (rootedAt letTerm))
  , d "into a let's body" letTerm (nm "body")
      (intoLetBody "x" (Just (nm "ann")) (nm "val") (nm "body") (rootedAt letTerm))
  , d "into an ascription's type" annotTerm (nm "ty")
      (intoAnnotType (nm "e") (nm "ty") (rootedAt annotTerm))
  , d "into an ascription's term" annotTerm (nm "e")
      (intoAnnotTerm (nm "ty") (nm "e") (rootedAt annotTerm))
  ]
    -- **Every field of an @elim@, in the flat order the elaborator walks
    -- them.** The motive and the target sit either side of the two variable
    -- length groups, which is where an off-by-one in 'intoElimField' would
    -- live, so each is asked for by name.
    ++ [ d ("into an elim's field " ++ show k) elimTerm f (elimAt k f)
       | (k, f) <- zip [0 ..] elimFields
       ]
  where
    d = Descent
    arg x = SurfaceArg Explicit (nm x)
    appArgs = arg "a" :| [arg "b"]
    lamBinders (SurfaceLam bs _) = bs
    lamBinders _                 = bare :| []
    bare = SurfaceBinder Explicit "x" Nothing
    elimFields = [nm "p", nm "mot", nm "m1", nm "m2", nm "i", nm "tgt"]
    elimAt k f =
      intoElimField "D" [nm "p"] (nm "mot") [nm "m1", nm "m2"] [nm "i"] (nm "tgt")
        k f (rootedAt elimTerm)

-- | **A frame that writes nowhere passes the test above by coincidence**, and
-- one did: 'intoElimField' started the indices a slot late, so descending to an
-- index replaced nothing and the term came back unchanged because the focus it
-- failed to write was the value already there. The fix to the test is to
-- rebuild with a focus that is /not/ the child.
--
-- Building a zipper whose focus did not come from the node is representable and
-- not well formed — "Thena.Surface.Zipper" says so — and that is exactly what
-- makes it the sharp instrument here: it asks where the frame puts things,
-- which is the only question 'rebuild' answers.
markers :: [TestTree]
markers =
  [ testCase what $ assertEqual "root" expected (root z)
  | (what, expected, z) <-
      [ ( "a spine's argument " ++ show k
        , SurfaceApp (nm "f") (replace k (arg "a" :| [arg "b"]))
        , intoArg (nm "f") (arg "a" :| [arg "b"]) k marker (rootedAt appTerm)
        )
      | k <- [0, 1]
      ]
      ++ [ ( "an elim's field " ++ show k
           , elimWith k
           , intoElimField "D" [nm "p"] (nm "mot") [nm "m1", nm "m2"] [nm "i"]
               (nm "tgt") k marker (rootedAt elimTerm)
           )
         | k <- [0 .. 5]
         ]
  ]
  where
    marker = nm "MARK"
    arg x = SurfaceArg Explicit (nm x)
    replace k as =
      NE.zipWith (\i a@(SurfaceArg p _) ->
                    if i == (k :: Int) then SurfaceArg p marker else a)
                 (0 :| [1 ..]) as
    -- The flat order written out by hand, so the test does not compute it the
    -- way the code under test does.
    elimWith k =
      let fs = [ if i == k then marker else f | (i, f) <- zip [0 ..] flat ]
       in case fs of
            [p, mot, m1, m2, i, tgt] ->
              SurfaceElim "D" [p] mot [m1, m2] [i] tgt
            _ -> elimTerm
    flat = [nm "p", nm "mot", nm "m1", nm "m2", nm "i", nm "tgt"]

child :: Descent -> TestTree
child (Descent what _ c z) = testCase what $ assertEqual "focus" c (focus z)

preserved :: Descent -> TestTree
preserved (Descent what whole _ z) =
  testCase what $ assertEqual "root" whole (root z)

-- --------------------------------------------------------------------------

rootIsWhole :: TestTree
rootIsWhole = testCase "rebuilds to itself" $
  assertEqual "root" letTerm (root (rootedAt letTerm))

focusIsWhole :: TestTree
focusIsWhole = testCase "focuses itself" $
  assertEqual "focus" letTerm (focus (rootedAt letTerm))

-- | The group is peeled by the move, which is what phase 46 replaced the Π
-- case's tree rewrite with. The codomain of @∀ (A : dom) (b : mid) -> cod@ is
-- the Π that remains once @A@ is taken off.
groupPeeled :: TestTree
groupPeeled = testCase "is peeled one binder at a time" $
  assertEqual "focus"
    (SurfacePi (SurfaceBinder Explicit "b" (Just (nm "mid")) :| []) (nm "cod"))
    (focus (peel piGroup))

groupRebuilt :: TestTree
groupRebuilt = testCase "and the group comes back as it was written" $
  assertEqual "root" piGroup (root (peel piGroup))

-- | **The one place the law holds only up to spelling.** @'InPiTail'@ merges
-- on the way out, matching the parser's own @spine@, so a Π written as two
-- nested ones comes back as a single group — the same term, spelled the other
-- way. The surface tree admitting both is a wart of the AST rather than of the
-- zipper; @ms4\/CLOSEOUT.md@ 18 carries it, and it is pinned here so that a
-- later fix is seen to change this and not something else.
nestingCollapses :: TestTree
nestingCollapses = testCase "written nested, it comes back grouped" $
  assertEqual "root" piGroup (root (peel nested))
  where
    nested =
      SurfacePi (SurfaceBinder Explicit "A" (Just (nm "dom")) :| [])
        (SurfacePi (SurfaceBinder Explicit "b" (Just (nm "mid")) :| []) (nm "cod"))

-- | Descend into a Π's codomain the way the ∀ clause does.
peel :: Surface -> SurfaceZipper
peel t@(SurfacePi bs body) = case NE.uncons bs of
  (b, rest) -> intoPiTail b (maybe body (`SurfacePi` body) rest) (rootedAt t)
peel t = rootedAt t
