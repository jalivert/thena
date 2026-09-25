-- | What a development looks like to the editor (MS7 phase 115c;
-- @discussion\/editor-display.md@ §5).
--
-- **The chain is flat and the guesses branch** — exactly 'Partial'\'s own
-- shape, mirrored here rather than flattened: a 'LinkView' per component or
-- constraint, in order, ending in the trailing term, with a guess's own body
-- nested inside its link.
--
-- **Three things the editor cannot work out, which is why they are here**:
-- whether a link is the focus, whether a guess is pure (so whether @solve@
-- would take — 'Thena.Development.Partial.extract'\'s answer, not something
-- to guess at), and, for a hole (a 'Claim' or an unsolved 'Guess'), whether
-- anything later in the development still mentions its name.
module Thena.Protocol.Development
  ( LinkView (..)
  , LinkShape (..)
  , ConstraintView (..)
  , displayDevelopment
  ) where

import Thena.Core.Context (Entry (..))
import Thena.Core.Term (Ident (..), Var)
import Thena.Development.Component (Component (..))
import Thena.Development.Cursor (Focus, Step (..))
import Thena.Development.Partial
  ( Constraint (..)
  , Partial (..)
  , extract
  , freeVarsPartial
  )
import Thena.Language.Grammar (Grammar)
import Thena.Protocol.Address (Address, Move (..), extend)
import Thena.Protocol.Display (Budget, Display, displayCore)
import Thena.Syntax.Print (Env, freshen)

-- | One link, addressed and marked.
data LinkView = LinkView
  { linkAt    :: Address
  , linkFocus :: Bool
    -- ^ does the cursor stand on this link — **chain-link precision, not
    -- term precision** ('Thena.Repl.renderCursor's own words): a focus
    -- somewhere inside the type or value is a further
    -- 'Thena.Protocol.Display.Display' address the editor already has.
  , linkShape :: LinkShape
  }
  deriving (Eq, Show)

data LinkShape
  = AnAssumption String Display
  | ADefinition  String Display Display
    -- ^ the type, then the value.
  | AClaimLink
      { claimName    :: String
      , claimType    :: Display
      , claimBlocked :: Bool
        -- ^ does anything later in the development still mention this hole's
        -- name — 'freeVarsPartial' over what follows, not a guess at it.
      }
  | AGuessLink
      { guessName    :: String
      , guessType    :: Display
      , guessPure    :: Bool
        -- ^ 'extract' on the guess's own body succeeds — what decides
        -- whether @solve@ would take.
      , guessBlocked :: Bool
      , guessBody    :: [LinkView]
        -- ^ the guess's own chain — a guess branches; nothing else does.
      }
  | AQuantifier String Display
  | APending ConstraintView
  | AResult Display
    -- ^ the trailing term the chain ends in. Every 'Partial' has exactly one,
    -- so it is the last 'LinkView' and the only one built this way.
  deriving (Eq, Show)

-- | @Ξ ⊢ s ≟ t : T@. **There is deliberately no move into a constraint's own
-- fields** (phase 111: "a 'Crossing' contributes nothing" for one, HIS,
-- 2026-08-18), so Ξ and the three terms are built at the constraint's own
-- link address rather than at addresses of their own — there is no finer
-- position for them to have yet.
data ConstraintView = ConstraintView
  { constraintXi   :: [(String, Display)]
    -- ^ Ξ's binder groups, outermost first — named so the terms below read,
    -- not because a name here is independently addressable.
  , constraintLhs  :: Display
  , constraintRhs  :: Display
  , constraintType :: Display
  }
  deriving (Eq, Show)

-- | Build the display of a development standing at an address, with the
-- cursor's position marked if one is given.
--
-- @route@ is the cursor's prefix read root-first — @toList (prefix cur)@,
-- exactly what 'Thena.Protocol.Address.addressOf' and
-- 'Thena.Repl.renderCursor' both walk — paired with its focus. 'Nothing'
-- draws the whole development unmarked.
--
-- Rendered from the root with no seed environment, for the reason
-- 'Thena.Repl.renderCursor' gives one: rendering from the root introduces
-- every binder on the way down, and a later component's type or value may
-- freely mention an earlier one.
--
-- @n@ is the name supply's starting point, exactly 'Thena.Repl.renderPartial's
-- own — high enough that a fresh name 'displayCore' mints while checking
-- whether a Π is dependent cannot collide with a 'Var' the development
-- already uses.
displayDevelopment
  :: [Grammar]
  -> Budget
  -> Int
  -> Address
  -> Maybe ([Step], Focus)
  -> Partial
  -> [LinkView]
displayDevelopment gs budget n0 at0 route0 p0 = go [] [] n0 at0 route0 p0
  where
    go :: Env -> [(Var, Address)] -> Int -> Address -> Maybe ([Step], Focus) -> Partial -> [LinkView]
    go env bs n at route p = case p of
      Trailing t ->
        [LinkView at (isHere route) (AResult (displayCore gs budget env bs n at t))]

      Pending k rest ->
        LinkView at (isHere route) (APending (constraintView env n at k))
          : go env bs n (extend at GoAlong) (past route) rest

      Under c rest ->
        let ty       = displayCore gs budget env bs n (extend at GoCrossType) (typeOf c)
            (v, name, env', bs') = bind env bs at c
            shape = case c of
              Assume {}   -> AnAssumption name ty
              Quantify {} -> AQuantifier  name ty
              Define _ _ val _ ->
                ADefinition name ty (displayCore gs budget env bs n (extend at GoCrossValue) val)
              Claim {} -> AClaimLink name ty (mentioned v rest)
              Guess _ _ g _ ->
                AGuessLink name ty (pureGuess g) (mentioned v rest)
                  (go env bs n (extend at GoInto) (inward route) g)
         in LinkView at (isHere route) shape : go env' bs' n (extend at GoAlong) (onward route) rest

    typeOf c = case c of
      Assume   _ _ s   -> s
      Define   _ _ _ s -> s
      Claim    _ _ s   -> s
      Guess    _ _ _ s -> s
      Quantify _ _ s   -> s

    -- The name a component would like, and the environment/binders extended
    -- for what follows — **not** for the component's own type or value
    -- (typed in the context before its own binder, same as 'Thena.Repl.link')
    -- and **not** for a guess's own body (@Γ_(?x ≐ P : S . p) = Γ_P@,
    -- 'Thena.Repl.goP's comment on the same line): only 'rest' ever sees it.
    bind env bs at c =
      let (v, Ident hint) = case c of
            Assume   x i _   -> (x, i)
            Define   x i _ _ -> (x, i)
            Claim    x i _   -> (x, i)
            Guess    x i _ _ -> (x, i)
            Quantify x i _   -> (x, i)
          name = freshen hint env
       in (v, name, (v, name) : env, (v, at) : bs)

    pureGuess g = case extract g of
      Right _ -> True
      Left  _ -> False

    mentioned x rest = x `elem` freeVarsPartial rest

    constraintView env n at (Equate xi s t ty) =
      let (groups, env') = telescope env n at xi
       in ConstraintView
            groups
            (displayCore gs budget env' [] n at s)
            (displayCore gs budget env' [] n at t)
            (displayCore gs budget env' [] n at ty)

    -- Ξ's own binders are likewise addressed at the constraint's link — see
    -- 'ConstraintView'.
    telescope env _ _ [] = ([], env)
    telescope env n at (e : rest) =
      let (v, hint, ty) = case e of
            Hypothesis x (Ident h) s   -> (x, h, s)
            Definition x (Ident h) _ s -> (x, h, s)
          name = freshen hint env
          env' = (v, name) : env
          (groups, env'') = telescope env' n at rest
       in ((name, displayCore gs budget env [] n at ty) : groups, env'')

isHere :: Maybe ([Step], Focus) -> Bool
isHere (Just ([], _)) = True
isHere _              = False

-- | Each follows one kind of step and refuses the others, so a route can
-- never be handed to the wrong part of a link — 'Thena.Repl.onward'/'past'/
-- 'inward's own three, over a plain list rather than a 'Path'.
onward, past, inward :: Maybe ([Step], Focus) -> Maybe ([Step], Focus)
onward (Just (Along _ : ss, f))      = Just (ss, f)
onward _                             = Nothing
past   (Just (Past _ : ss, f))       = Just (ss, f)
past   _                             = Nothing
inward (Just (IntoGuess {} : ss, f)) = Just (ss, f)
inward _                             = Nothing
