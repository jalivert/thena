-- | What a @Core@ term looks like to the editor (MS7 phase 115a, extended by
-- 115b for a term written in a modelled language).
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
--
-- **§6, object-language terms (phase 115b).** A node is a production, not a
-- shape: 'AnObjectTerm' carries the language, the production and its slots in
-- order, and the editor lays it out from the grammar it holds — nothing about
-- notation crosses. What the grammar alone cannot say, and so what has to
-- cross, is exactly two things: where a splice was needed for grouping
-- (phase 110's fencing — a slot's 'Bool'), and, deferred here, which slot is a
-- binder and which is an occurrence (see the Haddock on 'AnObjectTerm').
module Thena.Protocol.Display
  ( Display (..)
  , Shape (..)
  , Binding (..)
  , ObjectItem (..)
  , Budget (..)
  , displayCore
  ) where

import Data.List (elemIndex)

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
import Thena.Language.Build (Draft (..), objectDraft, settled)
import Thena.Language.Grammar
  ( Argument (..)
  , GProduction (..)
  , Grammar
  , Item (..)
  , Sort (..)
  )
import Thena.Protocol.Address (Address, Move (..), extend)
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
  | AnObjectTerm String String [ObjectItem]
    -- ^ a term of a modelled language (§6, phase 115b): the language, the
    -- production, and its slots **in the order the grammar writes them** — a
    -- node is a production, not a shape. The editor lays it out from the
    -- grammar it holds; whether a Π is an arrow or where the parentheses go
    -- has no counterpart here because there is no fallback notation to choose
    -- between — the production's own items are the only layout there is.
    --
    -- **Deferred**: which slot is a binder and which is an occurrence, so
    -- that an object-language variable highlights like a Core one does. That
    -- needs a name environment keyed by the grammar's own @as binder@/
    -- @as occurrence@ roles and its per-slot context restriction
    -- ('Thena.Language.Grammar' 's @Item@'s @[String]@), which is a second
    -- resolution pass the same shape as this one and not a small addition to
    -- it — recorded rather than folded in under this phase's done-when.
    -- Until then an object-language variable is a plain 'ObjectToken', drawn
    -- as text with no link back to its binder.
  | AToken String
    -- ^ what a token class matched, in the object language's own escaping —
    -- **not `ALiteral`'s**, which quotes. What a token reads back is the
    -- notation's own text (`Thena.Language.Build`'s `DToken`), a name rather
    -- than a Core string literal, even though a 'Primitive' string is what
    -- stands behind it.
  deriving (Eq, Show)

-- | One slot of an object-language production, in written order.
data ObjectItem
  = ObjectText String
    -- ^ a grammar terminal — the notation's own fixed text. No Core node
    -- stands behind it, so it carries no address.
  | ObjectToken Display
    -- ^ a token class's match — 'AToken', at this slot's own address.
  | ObjectChild Bool Display
    -- ^ a subterm: 'AnObjectTerm' when the notation still reaches it, the
    -- ordinary shape when it does not. **The 'Bool' is whether the editor
    -- must give it its own boundary** — phase 110's fencing, computed once by
    -- the parser and handed across because the editor could not otherwise
    -- rediscover it without one: printing this slot inline here would read
    -- back as a different tree, or (when the notation does not reach at all)
    -- there is no notation to lay out inline in the first place.
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
-- @grammars@ is what is installed on the machine — the same list
-- 'Thena.Repl.renderCore' takes, and for the same reason: whether a term
-- prints in its language's notation depends on what is loaded, not on the
-- term.
--
-- @binders@ maps a free variable to the node that binds it, so an occurrence of
-- something bound outside this term — a component of the development — still
-- points at it. A variable missing from it displays with no binder rather than
-- with a wrong one.
displayCore
  :: [Grammar]
  -> Budget
  -> Env
  -> [(Var, Address)]
  -> Int
  -> Address
  -> Core
  -> Display
displayCore grammars budget env binders counter here term =
  go budget env binders counter here term
  where
    -- **Tried first, at every node, not only at the top of the call** — a
    -- term inside an ordinary application's argument is exactly as eligible
    -- as the term `displayCore` was asked for. `Thena.Repl.go` makes the same
    -- choice for the same reason (phase 110): the property is "can this node
    -- be written in a language's notation", and that never depends on where
    -- the node sits.
    go (Budget d) e bs n at t
      | d <= 0 = Display at AnElision
      | Just shape <- objectShape (Budget (d - 1)) e bs n at t = Display at shape
      | otherwise = Display at (shapeOf (Budget (d - 1)) e bs n at t)

    -- | 'Nothing' exactly when 'Thena.Language.Build.printTerm' would print
    -- nothing — the two share 'objectDraft', so they agree by construction
    -- and not by parallel maintenance.
    objectShape b e bs n at t = do
      d <- objectDraft grammars t
      fromDraft b e bs n at t d

    -- | The shape for a term already known to draft as @d@ at @t@. Threads
    -- its own address bookkeeping because 'Thena.Language.Build' has none —
    -- addressing is this module's concern, not the language layer's.
    fromDraft b e bs n at t d = case d of
      DNode p g children _ -> do
        args <- argsAt at t
        items <- objectItems b e bs n p args children
        let GlobalName lang = g
            GlobalName prod = gproductionName p
        Just (AnObjectTerm lang prod items)
      _ -> Nothing -- a fenced or foreign draft has no shape of its own here;
                   -- 'objectItem' below is what turns one into a slot.

    -- | One slot of a production per grammar item, in written order — a
    -- 'Terminal' needs no child, a 'Slot' consumes the next one. Mirrors
    -- 'Thena.Language.Build.laid's own interleaving of items against
    -- children, which is why the two lists line up.
    objectItems b e bs n p args0 = walk (gproductionItems p)
      where
        names = map argumentName (gproductionArguments p)
        argOf x = do
          k <- elemIndex x names
          arg <- at k (gproductionArguments p)
          slot <- at k args0
          Just (argumentSort arg, slot)
        at k xs = case drop k xs of
          y : _ -> Just y
          []    -> Nothing

        walk [] _ = Just []
        walk (Terminal txt : is) cs = (ObjectText txt :) <$> walk is cs
        walk (Slot x _ _ : is) (c : cs) = do
          (sort, (addr, core)) <- argOf x
          item <- objectItem b e bs n sort addr core c
          (item :) <$> walk is cs
        walk (Slot {} : _) [] = Nothing -- a validated grammar never does this

    -- | What one slot draws, given what 'Thena.Language.Build.draft' decided
    -- for it.
    --
    -- **A stub renderer at the re-fencing call is exact, not an
    -- approximation** — same reason 'objectDraft' needs none: the round trip
    -- only asks whether the parser's shape matches, and a foreign subterm is
    -- one opaque splice to it regardless of what stands for its text.
    objectItem b e bs n sort addr core d = case (sort, d) of
      (OfClass {}, DToken s) -> Just (ObjectToken (Display addr (AToken s)))
      (OfLanguage {}, DNode {}) -> do
        shape <- fromDraft b e bs n addr core d
        Just (ObjectChild False (Display addr shape))
      (OfLanguage {}, DFenced _ _ inner) -> case settled grammars (const "") inner of
        Just settled' -> do
          shape <- fromDraft b e bs n addr core settled'
          Just (ObjectChild True (Display addr shape))
        Nothing -> Just (ObjectChild True (go b e bs n addr core))
      (_, DForeign _) -> Just (ObjectChild True (go b e bs n addr core))
      _ -> Nothing -- a token slot that did not draft as a token, or the
                   -- reverse; a validated grammar never produces this either

    -- | A saturated constructor application's arguments, addressed —
    -- 'Thena.Language.Build.spineOf' with the address threaded through, for
    -- the same two spellings and by the same rule (phase 110: level
    -- arguments rule a term out of the notation entirely). **Kept beside
    -- 'spineOf'**: the two must keep agreeing on which terms qualify, or
    -- 'objectShape' and 'Thena.Language.Build.draft' would disagree about
    -- whether a node has arguments to address at all.
    argsAt at t = case t of
      Canonical _ ls as | null ls -> Just (zip (map (down at . CanonArg) [1 ..]) as)
      Global _ ls       | null ls -> Just []
      App {}                      -> case peel at t [] of
        (Global _ ls, as) | null ls -> Just as
        _                           -> Nothing
      _ -> Nothing
      where
        peel a u acc = case u of
          App f x -> peel (down a Fun) f ((down a Arg, x) : acc)
          _       -> (u, acc)

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
down at p = extend at (GoDown p)
