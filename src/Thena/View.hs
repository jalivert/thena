-- | The views, over a session (MS7 phase 125).
--
-- **@.jalivert\/FRONTEND.md@ is what a frontend reads instead of this module's
-- source** (MS7 phase 129; his notes directory, not in this repository) — the modules it may import, the two ways it advances
-- a session, and every view below with its type. @Thena.FrontendTests@ crosses
-- that document against this export list, so a view added here and left out of
-- it fails the suite.
--
-- **This is the seam.** "Thena.View.Core" and its eight siblings each turn one
-- part of the system into something an editor can lay out; every one of them
-- takes the same six-argument prefix first — the installed grammars, a depth
-- budget, display names for the variables in scope, where each of those
-- variables is bound, the session's name counter, and the address of what is
-- being displayed. This module is where those six come from, so that a frontend
-- asks for a view of a 'Session' and nothing else.
--
-- **It replaces the envelope, and it is not a message layer** — his ruling of
-- 2026-09-27 (@discussion\/tight-integration.md@ §0b): there is no wire, so a
-- view is not returned /with/ a response, it is computed from the session and
-- pulled. His own TUI already worked that way, recomputing every draw, which is
-- what makes a view follow the cursor for free.
--
-- **Every caller was passing @[]@ for the binders, so no occurrence anywhere
-- linked to what binds it.** 'Thena.View.Core.displayCore's own comment says a
-- variable missing from that map "displays with no binder rather than with a
-- wrong one" — true, and until this module nothing ever supplied one outside
-- 'Thena.View.Development', which builds its own as it walks. 'binderAddresses'
-- is the map, from the development the session is on.
--
-- **Reading a session goes through here.** 'Thena.Driver.Session' exports no
-- constructor as of this phase, so it cannot be built or edited outside the
-- driver; what a frontend may read off one is the list below. 'machineOf'
-- is deliberately among them and deliberately last: it hands out the engine's
-- own state, and a frontend that needs it is a frontend missing a view. What
-- stops it being reached for casually is the @view@ sublibrary (phase 126),
-- which leaves a frontend without "Thena.Engine" to make sense of one.
module Thena.View
  ( -- * The session
    Session
  , sessionGlobals
  , sessionGrammars
  , sessionRules
  , sessionCursor
  , sessionContext
  , sessionNames
    -- ** and the driver's own reads, so that one import serves a frontend
  , workingOn
  , parked
  , fuelOf
  , parsingLanguage
  , pendingQuestion
  , machineOf

    -- * The views
  , Budget (..)
  , developmentView
  , machineView
  , focusTypeView
  , rulesView
  , matchesView
  , parseView
  , offerView

    -- * Addressing
  , focusAddress
  , binderAddresses
  , focusProgram
  ) where

import Data.Foldable (toList)

import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Term (Ident (..), Var)
import Thena.Development.Component (Component (..))
import Thena.Development.Cursor (Cursor, Focus, Step, expectedType, focus, prefix, rebuild)
import Thena.Development.Partial (Partial (..))
import Thena.Driver
  ( Session
  , fuelOf
  , machineOf
  , parked
  , parsingLanguage
  , pendingQuestion
  , workingOn
  )
import Thena.Engine (Machine (..), cursor, development, focusContext)
import Thena.Global.Env (GlobalEnv)
import Thena.Instral.Ops (Instr, Rule)
import Thena.Language.Grammar (Grammar)
import Thena.Rules (RuleBase (..), RuleIter, matches, next)
import Thena.Syntax.Print (Env, freshen)
import Thena.View.Address (Address (..), Move (..), addressOf, extend, focusing)
import Thena.View.Chart
  ( FailureView
  , OfferProblem
  , OfferView
  , TreeView
  , Written
  , displayOffer
  , displayParse
  )
import Thena.View.Core (Budget (..), Display, displayCore)
import Thena.View.Development (LinkView, displayDevelopment)
import Thena.View.Machine (MachineView, displayMachine)
import Thena.View.Rules (RuleView, displayRule)

-- ---------------------------------------------------------------------------
-- The session

-- | The declarations in scope. His ruling of 2026-09-24 — the editor holds the
-- globals and the grammars, kept current as the session advances.
sessionGlobals :: Session -> GlobalEnv
sessionGlobals = globals . machineOf

-- | The object-language grammars installed so far, latest first.
sessionGrammars :: Session -> [Grammar]
sessionGrammars = grammars . machineOf

-- | The ordered rule bases.
sessionRules :: Session -> [RuleBase]
sessionRules = rules . machineOf

-- | Where the focus is in the development being worked on.
sessionCursor :: Session -> Cursor
sessionCursor = cursor . development . machineOf

-- | Γ at the focus.
sessionContext :: Session -> Context
sessionContext = focusContext . development . machineOf

-- | The name counter. Every view that opens a 'Thena.Core.Term.Scope' needs it,
-- which is exactly why no caller should have to know that.
sessionNames :: Session -> Int
sessionNames = names . machineOf

-- ---------------------------------------------------------------------------
-- Addressing

-- | Where the cursor stands.
focusAddress :: Session -> Address
focusAddress = addressOf . sessionCursor

-- | Every variable a component of the development binds, and the link that
-- binds it — the map 'Thena.View.Core.displayCore' wants so that an occurrence
-- of something bound outside the term being displayed still points at it.
--
-- **It takes the session, and until phase 129 it took a
-- 'Thena.Development.Partial.Partial'** — which a frontend has no way to obtain
-- or name, since that module is not one the @view@ sublibrary re-exports. Its own
-- comment said so and lived with it, because "Thena.ViewTests" asserts its
-- invariant and nothing else called it. Writing @.jalivert\/FRONTEND.md@ made that
-- the only entry here a reader could be told about and not shown, which is the
-- fault phase 126 deleted three other exports for; the walk is 'go' below and
-- the plumbing is unchanged.
--
-- **A frontend still rarely wants it**: every view that needs the map already
-- has it, and an occurrence carries its binder's address
-- ('Thena.View.Core.AVariable'). It is here for a pane that wants the map
-- itself — every binder in the development, whether or not anything shown
-- mentions it.
--
-- **The whole chain, not the prefix.** A variable that is not in scope where the
-- term is simply never occurs in it, so nothing is gained by cutting the walk
-- short, and a value sitting on the machine may mention any component the line
-- that built it could see.
binderAddresses :: Session -> [(Var, Address)]
binderAddresses = go (Address []) . rebuild . sessionCursor
  where
    go at p = case p of
      Trailing _   -> []
      Pending _ r  -> go (extend at GoAlong) r
      Under c r    -> (bound c, at) : inside at c ++ go (extend at GoAlong) r
    inside at c = case c of
      Guess _ _ g _ -> go (extend at GoInto) g
      _             -> []
    bound c = case c of
      Assume   x _ _   -> x
      Define   x _ _ _ -> x
      Claim    x _ _   -> x
      Guess    x _ _ _ -> x
      Quantify x _ _   -> x

-- | The instructions that move the cursor to an address, for
-- 'Thena.Driver.oneProgram' — an absolute move, wherever the cursor stands
-- (phase 121).
focusProgram :: Address -> [Instr]
focusProgram = focusing

-- ---------------------------------------------------------------------------
-- The views

-- | The development chain, the focus marked (@ms7\/CLOSEOUT.md@ 7: the whole
-- chain, no budget on its length — the editor scrolls to the focus itself).
developmentView :: Budget -> Session -> [LinkView]
developmentView budget s =
  displayDevelopment
    (sessionGrammars s)
    budget
    (sessionNames s)
    (Address [])
    (Just (route (sessionCursor s)))
    (rebuild (sessionCursor s))

-- | The running machine: its program, its bindings, and the calls underneath.
machineView :: Budget -> Session -> MachineView
machineView budget s =
  displayMachine
    (sessionGrammars s)
    budget
    (envAt s)
    (binderAddresses s)
    (sessionNames s)
    (focusAddress s)
    (machineOf s)

-- | The type the focus is expected to have, in the context it sits in — @:where@'s
-- own \"type\" section, and a goal pane's whole content.
--
-- 'Nothing' when the structure carries no type, which is not a failure to look:
-- deriving one for an arbitrary core subterm is @infer@'s job
-- ('Thena.Development.Cursor.expectedType' says the same).
--
-- **It replaced a @coreView@ that took the term — MS7 phase 126.** That one
-- could not be called by a frontend at all: a frontend has no 'Core' and cannot
-- name one, which the @view@ sublibrary made plain. What a frontend wanted from
-- it was always this.
focusTypeView :: Budget -> Session -> Maybe Display
focusTypeView budget s = fmap display (expectedType (sessionCursor s))
  where
    display =
      displayCore (sessionGrammars s) budget (envAt s) (binderAddresses s) (sessionNames s) (focusAddress s)

-- | Every rule base, in order, each with its rules.
--
-- **The bases' own names, and nothing else about a base**: a frontend that wants
-- a rule's clauses together groups them by 'Thena.View.Rules.ruleViewName' and
-- the length of its params, which is what a rule /is/. What is not here and was
-- wanted is a rule's declared signature — see @ms7\/CLOSEOUT.md@.
rulesView :: Budget -> Session -> [(String, [RuleView])]
rulesView budget s =
  [ (baseName b, map (ruleOf budget s) (baseRules b)) | b <- sessionRules s ]

-- | The rules whose heads hold at the focus — the match list, the same one
-- @:matches@ prints.
matchesView :: Budget -> Session -> [RuleView]
matchesView budget s =
  map (ruleOf budget s) (drain (matches (sessionRules s) (sessionGlobals s) (sessionCursor s)))
  where
    drain :: RuleIter -> [Rule]
    drain it = case next it of
      Nothing        -> []
      Just (r, rest) -> r : drain rest

-- | Is this region one term of this language, and if not, why.
parseView :: Session -> String -> Maybe String -> [Written] -> Either FailureView TreeView
parseView s = displayParse (sessionGrammars s)

-- | What may be written at the cursor inside a region (phase 115e, given the
-- shape an editor holds a region in at phase 125).
offerView
  :: Session
  -> String
  -> Maybe String
  -> [Written]
  -> [Written]
  -> Either OfferProblem OfferView
offerView s = displayOffer (sessionGrammars s)

-- ---------------------------------------------------------------------------
-- The plumbing itself

-- | One rule, with the session's plumbing supplied.
ruleOf :: Budget -> Session -> Rule -> RuleView
ruleOf budget s =
  displayRule (sessionGrammars s) budget (envAt s) (binderAddresses s) (sessionNames s) (focusAddress s)

-- | Display names for the variables at the focus, freshened the way the chain
-- printer freshens a component's — 'Thena.Repl.envOf's own fold, here because
-- a view must agree with it about what a variable is called.
envAt :: Session -> Env
envAt = foldl add [] . sessionContext
  where
    add e entry =
      let (v, hint) = case entry of
            Hypothesis x (Ident h) _   -> (x, h)
            Definition x (Ident h) _ _ -> (x, h)
       in (v, freshen hint e) : e

route :: Cursor -> ([Step], Focus)
route cur = (toList (prefix cur), focus cur)
