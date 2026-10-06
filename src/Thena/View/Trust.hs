-- | What a development rests on that nothing derived, for the editor (MS8
-- phase 151).
--
-- **A view on the development, not a hook in type checking — HIS RULING,
-- 2026-10-06.** Checking runs on every fill and every conversion; /what does
-- this proof currently rest on/ is a question about the chain, the same shape as
-- @:where@. So a pane showing this can be live without anything being
-- recomputed per keystroke, and it goes stale only when the development moves.
--
-- **Both halves of every claim cross, and so does the site each verdict came
-- from.** The pair @(claimed, body)@ /is/ the obligation written down (his
-- observation, 2026-10-05), and @body@ is what says whether the trust is still
-- load-bearing — as the names inside them instantiate the two converge and the
-- node evaporates. A view that showed the claim alone would hide exactly that.
-- And a verdict without its site misleads where it matters most: the same node
-- is honest inside a definition and a lie at a use that instantiates it.
--
-- **The level is here too, so a pane can show it and bind a key to it.** The
-- engine owns the level and the frontend switches it, through the @:trust@
-- command like any other change to a session.
--
-- **DO NOT LABEL 'Thena.Core.Trust.NoUndischargeableTrust' SAFE** — his
-- instruction. @Empty@ is provable using nothing but claims that rung admits,
-- measured 2026-10-06. It stops accidents, not adversaries, and only
-- 'Thena.Core.Trust.NoTrust' is a soundness guarantee.
module Thena.View.Trust
  ( TrustView (..)
  , ClaimView (..)
  , displayTrust
    -- * The vocabulary, re-exported so that this one import serves a frontend
    --
    -- | The three types a 'ClaimView' and a 'TrustView' are read with live in
    -- "Thena.Core.Trust", which is below the boundary and not a module a
    -- frontend may import. They are here for the reason 'Thena.View' gives for
    -- gathering the session's own reads: a view whose fields cannot be named is
    -- not usable.
  , TrustLevel (..)
  , TrustClass (..)
  , TrustSite (..)
  ) where

import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Term (GlobalName (..), Ident (..), Var)
import Thena.Core.Trust
  ( TrustClaim (..)
  , TrustClass (..)
  , TrustLevel (..)
  , TrustSite (..)
  )
import Thena.Language.Grammar (Grammar)
import Thena.View.Address (Address)
import Thena.View.Core (Budget, Display, displayCore)
import Thena.Syntax.Print (Env, freshen)

-- | The level a session is at, and every claim the development on it rests on.
--
-- **The level is a field and not something a frontend reads separately**,
-- because the list means different things under different rungs: the same
-- 'Pending' claim is admitted at 'NoUndischargeableTrust' and refused at
-- 'NoTrust', so a pane drawing one without the other cannot say whether @qed@
-- will go through.
data TrustView = TrustView
  { trustViewLevel  :: TrustLevel
  , trustViewClaims :: [ClaimView]
  , trustViewRefused :: [ClaimView]
    -- ^ the claims this level does not permit — the subset of
    -- 'trustViewClaims', in the same order.
    --
    -- **Here rather than left to the frontend to filter**, because deciding
    -- which rung admits which class is the engine's rule and a second copy of
    -- it would drift. A frontend highlights these; it does not work out which
    -- they are.
  }
  deriving (Eq, Show)

-- | One claim, as the editor sees it.
data ClaimView = ClaimView
  { claimViewClass :: TrustClass
  , claimViewSite  :: TrustSite
  , claimViewRoute :: [String]
    -- ^ the definitions the walk went through to reach it, outermost first.
    -- Empty for a node standing in the development itself, which with
    -- 'AtDefinition' is what \"written here\" means.
  , claimViewClaimed :: Display
    -- ^ the type the node asserts.
  , claimViewBody :: Display
    -- ^ the type the body was really checked at — @actual@, and the half that
    -- says whether the trust is still carrying anything.
  }
  deriving (Eq, Show)

-- | Build the view.
--
-- **Each claim is displayed in its own context and not the session's.** A node
-- under a binder is reached with that binder opened, so the two types mention
-- variables the focus has never heard of; naming them from the claim's own
-- context is the only way they read. That is why 'Thena.Core.Trust.TrustClaim'
-- carries one.
--
-- **The address is the one the caller passes, for every claim.** A claim is not
-- a subterm of the focus and there is nothing in the development to point at —
-- these terms are assembled by the walk, out of a definition's body and a use's
-- arguments. Giving them the focus's address says /this is what the thing you
-- are looking at rests on/, which is true, and inventing a route into them
-- would invite a @goto@ into nothing.
displayTrust
  :: [Grammar]
  -> Budget
  -> [(Var, Address)]
  -> Int
  -> Address
  -> TrustLevel
  -> [TrustClaim]
  -> TrustView
displayTrust grammars budget binders counter here lvl claims =
  TrustView
    { trustViewLevel   = lvl
    , trustViewClaims  = map one claims
    , trustViewRefused = [ one c | c <- claims, not (permitted (claimClass c)) ]
    }
  where
    one c =
      ClaimView
        { claimViewClass   = claimClass c
        , claimViewSite    = claimSite c
        , claimViewRoute   = [ g | GlobalName g <- claimRoute c ]
        , claimViewClaimed = display c (claimClaimed c)
        , claimViewBody    = display c (claimActual c)
        }

    display c = displayCore grammars budget (envOf (claimContext c)) binders counter here

    permitted k = case lvl of
      AnyTrust               -> True
      NoUndischargeableTrust -> k /= Undischargeable
      NoTrust                -> k == Discharged

-- | Display names for a context's variables, the same fold
-- 'Thena.Render.envOf' and 'Thena.View.envAt' use — so a view agrees with them
-- about what a variable is called.
envOf :: Context -> Env
envOf = foldl add []
  where
    add e entry =
      let (v, hint) = case entry of
            Hypothesis x (Ident h) _   -> (x, h)
            Definition x (Ident h) _ _ -> (x, h)
       in (v, freshen hint e) : e
