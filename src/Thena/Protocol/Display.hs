-- | What a @Core@ term looks like to the editor (MS7 phase 115a).
--
-- **The seam, and it is `discussion\/editor-display.md` §1:** the server resolves
-- everything that needs the system — which variable this is and what it is
-- called here, what a level normalises to, which arguments are implicit — and
-- the editor decides what it all looks like. So there is no text in here except
-- where the text /is/ the answer, and no parentheses, indentation or layout at
-- all.
--
-- **`Scope` does not cross.** A binder carries a name and a body, so nothing has
-- to see inside @MkScope@ and nothing has to build one — which sending @Core@
-- itself would have required, opening for a wire format the boundary §3.4 relies
-- on.
--
-- **Every node carries its address**, so the editor can point back at any part
-- of what it drew. The addresses are phase 111's moves, which already descend
-- into core terms, so a subterm three levels down is one address and needs no
-- second scheme.
module Thena.Protocol.Display
  ( Display (..)
  , Shape (..)
  , Binding (..)
  , Budget (..)
  , displayCore
  ) where

import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Ident (..)
  , Literal (..)
  , Var
  , fresh
  , open
  )
import Thena.Development.Cursor (Part (..))
import Thena.Protocol.Address (Address (..), Move (..))
import Thena.Syntax.Print
  ( Env
  , escapeChar
  , escapeString
  , freshen
  , nameOf
  , renderLevel
  , renderLevelAtom
  )

-- | A node, and where it is.
data Display = Display
  { displayAt    :: Address
  , displayShape :: Shape
  }
  deriving (Eq, Show)

-- | What a node is — never what it looks like.
data Shape
  = AVariable String (Maybe Address)
    -- ^ the name it is shown under, and the binder it belongs to.
    --
    -- **Not a de Bruijn index and not a 'Var'.** The address is what makes
    -- /hover a binder, highlight its occurrences/ free rather than a separate
    -- annotation computed for display. It is absent only when the binder is
    -- outside what was asked for.
  | AGlobal String [String]
    -- ^ the name as it should be written, and its level arguments, normalised.
  | AUniverse String
    -- ^ the level, **already normalised**. Level normalisation is system work
    -- and the editor should never do it.
  | ALiteral String
    -- ^ the text a reader takes back — escaped here, because what reads back as
    -- this literal is the reader's rule and therefore the server's.
  | AnApplication Display Display
  | AFunction Binding Display
    -- ^ @Π@. **Whether it prints as an arrow is the editor's** — that is only
    -- whether the bound variable occurs, and occurrences carry their binder, so
    -- the editor can see it without being told.
  | AnAbstraction Binding Display
  | ALet Binding Display Display
    -- ^ the binding, its value, and the body.
  | AFormer String [String] [Display]
  | AnElimination
      { eliminatorName :: String
      , eliminatorLevels :: [String]
      , eliminatorParameters :: [Display]
      , eliminatorMotive :: Display
      , eliminatorMethods :: [Display]
      , eliminatorIndices :: [Display]
      , eliminatorTarget :: Display
      }
    -- ^ **The slots are labelled**, so the editor can let you point at /the
    -- motive/ rather than at /argument four/.
  | ADangling Int
    -- ^ a @Bound@ index nothing binds. Representable and not well formed (§3.4);
    -- the terminal printer shows it too rather than pretending.
  | AnElision
    -- ^ the budget stopped here. **Visible, never silent** — a tree that quietly
    -- stopped would draw a term that is not the term.
  deriving (Eq, Show)

-- | A binder: what it binds, and the type it binds at.
--
-- It has no address of its own; **an occurrence points at the node that binds
-- it**, which is the 'AFunction', 'AnAbstraction' or 'ALet' this sits in.
data Binding = Binding
  { bindingName :: String
  , bindingType :: Display
  }
  deriving (Eq, Show)

-- | How deep to go before eliding.
newtype Budget = Budget Int
  deriving (Eq, Show)

-- | Build the display of a term standing at an address.
--
-- @binders@ maps a free variable to the node that binds it, so an occurrence of
-- something bound outside this term — a component of the development — still
-- points at it. A variable missing from it displays with no binder rather than
-- with a wrong one.
displayCore
  :: Budget
  -> Env
  -> [(Var, Address)]
  -> Int
  -> Address
  -> Core
  -> Display
displayCore budget env binders counter here term = go budget env binders counter here term
  where
    go (Budget d) e bs n at t
      | d <= 0 = Display at AnElision
      | otherwise = Display at (shapeOf (Budget (d - 1)) e bs n at t)

    shapeOf b e bs n at t = case t of
      Bound i -> ADangling i
      Free v -> AVariable (nameOf v e) (lookup v bs)
      Global (GlobalName g) ls -> AGlobal g (map renderLevelAtom ls)
      Universe l -> AUniverse (renderLevel l)
      Primitive l -> ALiteral (literal l)
      App f a -> AnApplication (go b e bs n (down at Fun) f) (go b e bs n (down at Arg) a)
      Pi i dom sc -> binder AFunction b e bs n at i dom sc Dom Cod
      Lam i dom sc -> binder AnAbstraction b e bs n at i dom sc Dom Body
      Let (Ident hint) val ty sc ->
        let (v, n1) = fresh n
            nm = freshen hint e
            e' = (v, nm) : e
            bs' = (v, at) : bs
         in ALet
              (Binding nm (go b e bs n (down at Type) ty))
              (go b e bs n (down at Val) val)
              (go b e' bs' n1 (down at Body) (open v sc))
      Canonical (GlobalName g) ls as ->
        AFormer g (map renderLevelAtom ls) (slots b e bs n at CanonArg as)
      Eliminate d' ls ps m ms is tgt ->
        AnElimination
          (let GlobalName g = d' in g)
          (map renderLevelAtom ls)
          (slots b e bs n at Param ps)
          (go b e bs n (down at Motive) m)
          (slots b e bs n at Method ms)
          (slots b e bs n at Index is)
          (go b e bs n (down at Target) tgt)

    -- One binder shape, twice, because a Π and a λ differ only in which part
    -- names the body and in what the editor draws.
    binder con b e bs n at (Ident hint) dom sc domPart bodyPart =
      let (v, n1) = fresh n
          nm = freshen hint e
       in con
            (Binding nm (go b e bs n (down at domPart) dom))
            (go b ((v, nm) : e) ((v, at) : bs) n1 (down at bodyPart) (open v sc))

    -- **One-based**, because @down@'s @pick@ is one-based and an address has to
    -- mean the same thing to the cursor as it does here.
    slots b e bs n at part xs =
      [go b e bs n (down at (part k)) x | (k, x) <- zip [1 ..] xs]

    literal l = case l of
      LString s -> escapeString s
      LChar c -> escapeChar c
      LInt k -> show k
      LRegex r -> "/" ++ r ++ "/"

-- | One step deeper.
down :: Address -> Part -> Address
down (Address ms) p = Address (ms ++ [GoDown p])
