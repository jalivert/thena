-- | The working context — what a core judgment can see (§3.2).
--
-- Imports "Thena.Core.Term" and must never be imported by it.
module Thena.Core.Context
  ( Entry (..)
  , Context
  , entryVar
  , entryIdent
  , entryType
  , writableIn
  , freeIn
  , freshIdent
  , substLevelsInEntry
  , piOver
  , lamOver
  ) where

import Thena.Core.Level (Level, LevelVar)
import Thena.Core.Term
  (Core (..), Ident (..), Scope, Var, anonymousIdent, close, substLevelsIn)

-- | An entry in a working context: a name with a type, or a name with a type
-- and a value.
--
-- **Provenance-free by design.** An entry may have come from a development
-- component read forgetfully, or from opening a core 'Thena.Core.Term.Scope',
-- and nothing downstream may ask which. That is what makes it honest: the
-- alternative carries hole-ness and guess bodies into the context, so a consumer
-- /can/ ask, and sooner or later one would (§3.2).
--
-- The type is always the last field, as in 'Thena.Development.Component' — the
-- shape reads like the notation.
--
-- 'Eq' is derived and so compares 'Ident's, unlike 'Eq' on
-- 'Thena.Core.Term.Core'. That is deliberate: a context is named (§3.5), and two
-- entries differing only in display name are two different entries.
data Entry
  = Hypothesis Var Ident      Core   -- ^ @x     : S@
  | Definition Var Ident Core Core   -- ^ @x = s : S@
  deriving (Eq, Show)

-- | Outermost first.
type Context = [Entry]

-- | The variable an entry binds. Unique within a session, and what every
-- lookup and scope check actually compares (§3.5).
entryVar :: Entry -> Var
entryVar e = case e of
  Hypothesis v _ _   -> v
  Definition v _ _ _ -> v

-- | The display name an entry was written with. Never used to decide anything
-- semantic — see 'Thena.Core.Term.Ident'.
entryIdent :: Entry -> Ident
entryIdent e = case e of
  Hypothesis _ i _   -> i
  Definition _ i _ _ -> i

-- | The word a binder carries as it enters this context: its own where that
-- word is free here, and otherwise a free one.
--
-- **HIS RULING, 2026-11-20** — @.claude\/RULINGS.md@, /THERE IS ONE NAME/, part
-- one: **every name the system puts into a scope is free in that scope**, and
-- the copies count as inventing. The write-up is
-- @.jalivert\/discussion\/binder-names-and-the-dagger.md@. So this is asked
-- wherever the system supplies a word rather than the user writing one —
-- "Thena.Engine"\'s @intro@ taking the word off the goal\'s Π binder,
-- "Thena.Tactics.Specialise" peeling a method\'s telescope, and
-- "Thena.Syntax.Resolve" minting one for an arrow\'s nameless argument.
--
-- Two things it does, and they were one ruling each:
--
--   * **a binder with no written name gets a real, writable one** — his ruling
--     of the same day, /An unnamed argument gets a real name/. A binder with
--     none carries 'Thena.Core.Term.anonymousIdent', and two of them in one
--     context are two entries sharing the word @_@: the development printed @_@
--     and @_1@, the user wrote @_@ meaning the first, and
--     "Thena.Syntax.Resolve"\'s innermost-wins lookup gave the second —
--     silently, where both have the same type, with @qed@ admitting the wrong
--     term. The stem is @x@, which is what that module\'s @prefix@ mints for a
--     generated wrapper\'s argument.
--   * **a word already taken here is numbered** until it is free. That is the
--     part the printer used to do on the way out, where nothing read it back:
--     @tied@\'s method binds the @m@ its /data block/ wrote inside a theorem
--     that has its own @m@, and @fill core`m`@ reached the inner binder while
--     the screen said @m@ on the outer.
--
-- **A word the USER wrote is never touched, taken or not** — that is theirs to
-- write (MS4 phase 41f, /"the name is used as given, taken or not"/), the
-- shadowing it causes is allowed, and what it costs the outer binder is said
-- where the outer binder is printed. This function is only ever asked about a
-- word the system supplied, and a caller that cannot tell the two apart must
-- not ask it.
writableIn :: Context -> Ident -> Ident
writableIn ctx i
  | i == anonymousIdent = freshIdent (map entryIdent ctx) (Ident "x")
  | otherwise           = freeIn ctx i

-- | The word a binder already carries, made free in this context — and
-- **nothing invented where there is no word.**
--
-- 'writableIn' plus the one thing it does that this does not, and the split is
-- the one place a caller has to choose: a binder that enters the context
-- /here/ needs a word and so is asked the other question, while a binder whose
-- word is only being carried past — a method's telescope on its way to the
-- report an arm binds from — may still be nameless when it arrives, and
-- whoever finally binds it mints the word. Minting here as well would mean two
-- stems for one binder, and the rule base's are the better words: an induction
-- hypothesis is called @ih@ and not @x1@.
--
-- So an anonymous binder is passed through unchanged — @_@ numbered to @_1@ is
-- the defect @~5g3tv@ named, not a repair of it — and a written word that is
-- taken is numbered until it is free.
freeIn :: Context -> Ident -> Ident
freeIn ctx i
  | i == anonymousIdent = i
  | otherwise           = freshIdent (map entryIdent ctx) i

-- | An identifier not already taken: the hint, or the hint with the first
-- number that frees it.
--
-- **Freshening happens when a binder is built, not when it is printed —
-- DECIDED by the user 2026-08-25 for a development\'s components, and
-- 2026-11-20 for a context\'s words.** Before this, two things could carry the
-- same 'Ident' and the printer told them apart for the screen only, so the name
-- you saw was not the name that was stored and @goto ‹name›@ could not find it.
--
-- **One numbering rule for both**, which is why it lives here rather than in
-- "Thena.Development.Cursor", which re-exports it: a word is freshened against
-- a development\'s identifiers there and against a context\'s words in
-- 'writableIn', and two spellings of the suffix would mean the two disagreed
-- about what a free word is.
freshIdent :: [Ident] -> Ident -> Ident
freshIdent taken i@(Ident hint)
  | free i    = i
  | otherwise = numbered (1 :: Int)
  where
    free j = j `notElem` taken
    numbered k =
      let j = Ident (hint ++ show k) in if free j then j else numbered (k + 1)

-- | The type of an entry, whichever kind it is. Both constructors have one, in
-- the same last position, which is why this accessor is total.
entryType :: Entry -> Core
entryType e = case e of
  Hypothesis _ _ t   -> t
  Definition _ _ _ t -> t

-- | Apply a level substitution to an entry's types (MS3 phase 33).
--
-- Here rather than repeated in its two callers — "Thena.Core.Unify", pushing a
-- level solution through Ξ, and "Thena.Development.Cursor", pushing one through
-- a constraint's binders — so that the entry's shape is walked in one place.
substLevelsInEntry :: [(LevelVar, Level)] -> Entry -> Entry
substLevelsInEntry sub e = case e of
  Hypothesis x i t   -> Hypothesis x i (substLevelsIn sub t)
  Definition x i v t -> Definition x i (substLevelsIn sub v) (substLevelsIn sub t)

-- | @∀ Γ -> T@: bind a whole context over a term.
--
-- A context is a telescope, and this is the type it stands for. Phase 6's
-- declarations are what want it — an inductive definition's parameters and a
-- constructor's arguments are both contexts, and both are printed and stored as
-- the Π-type they bind (§3.7). A 'Definition' entry becomes a @let@, which is
-- what it means; only 'Hypothesis' entries arise in practice.
piOver :: Context -> Core -> Core
piOver = bindOver Pi

-- | @λ Γ -> t@. The same fold with the other binder: it is what a generated
-- former wrapper abstracts (§3.7 item 2).
lamOver :: Context -> Core -> Core
lamOver = bindOver Lam

bindOver :: (Ident -> Core -> Scope Core -> Core) -> Context -> Core -> Core
bindOver con tel body = foldr bind body tel
  where
    bind (Hypothesis v i t)   b = con i t (close v b)
    bind (Definition v i s t) b = Let i s t (close v b)
