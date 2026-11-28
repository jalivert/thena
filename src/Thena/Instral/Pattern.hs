-- | Patterns — what stands on the left of a clause's parameter list and, since
-- MS5 phase 84, on the left of a binding.
--
-- **Its own module for the reason 'Thena.Instral.Type' is** (MS5 phase 84):
-- "Thena.Errors" has to name a 'Pattern' — a call's destination is one, so
-- @NothingReturned@ carries one — and it cannot import "Thena.Instral.Ops", which
-- reaches "Thena.Errors" through "Thena.Development.Cursor". The type is pure
-- syntax and depends on nothing, so it moves down a layer and both import it.
--
-- **The matcher stays in "Thena.Instral.Ops"**, because matching needs a
-- 'Thena.Instral.Ops.Value' and a value is what the machine has. What lives here is the
-- shape and the two questions that are about the shape alone.
module Thena.Instral.Pattern
  ( Pattern (..)
  , Skeleton (..)
  , Slot (..)
  , CoreP (..)
  , LevelP (..)
  , CoreSlot (..)
  , ComponentP (..)
  , skeletonHoles
  , corePHoles
  , corePSlots
  , componentPSlots
  , componentPBinds
  , patternBinds
  , patternIrrefutable
  ) where

import Thena.Core.Term (GlobalName, Literal)

type Name = String

-- | What stands in a parameter position (MS5 phase 82).
--
-- **A pattern is written in the language of the value it matches** — his
-- correction, and the whole of @discussion\/pattern-matching.md@ §2. Claude
-- proposed a word notation, @(cons x xs)@; he wanted the literal's own
-- spelling, so a list pattern /is/ a list literal and a pair pattern is a pair.
-- The strongest argument for him turned out to be accuracy rather than taste: a
-- word-pattern has to name every field or silently drop one.
--
-- **A bare identifier is a VARIABLE, and that is decision 1 of §4** — it is what
-- buys @[a, ...rest]@ with no sigil, and its price is that a /named constructor/
-- cannot be matched. That price is not paid here: @instral@'s own data has no
-- named constructors except 'PSome' and 'PNone', which are words in the grammar
-- rather than values a user can shadow. It is paid at stage b and c, which are
-- not built.
--
-- **This stage is @instral@'s own data only.** A Surface pattern
-- (@surface\`a -> b\`@)
-- and a Core one are stages b and c of that document, and c waits on the two
-- decisions §4 records as open.
data Pattern
  = PVar Name            -- ^ @x@ — binds, and matches anything
  | PWild                -- ^ @_@ — matches anything, binds nothing
  | PInt  Int            -- ^ @3@
  | PChar Char           -- ^ @\'c\'@
  | PBool Bool           -- ^ @true@, @false@
  | PText String
    -- ^ @"…"@ — matches a @VText@, and a name by its dotted form (MS10), so
    -- @\"Nat.zero\"@ matches the name @Nat.zero@ and @\"zero\"@ does not.
  | PList [Pattern] (Maybe Pattern)
    -- ^ @[a, b]@ closed, @[a, ...rest]@ open.
    --
    -- **The tail is a whole pattern, not a name**, so @[a, ...rest]@,
    -- @[a, ..._]@ and @[a, ...[]]@ all read — his §2. @...@ prefixes /any/ list
    -- pattern, which is why the field is a 'Pattern' and not a 'Maybe' 'Name'.
    --
    -- **Final position only.** @[...xs, a]@ is a snoc and wants the list
    -- reversed; it is not written.
  | PPair Pattern Pattern -- ^ @(x, y)@ — the pair /value/ needs nothing new
  | PSome Pattern         -- ^ @some x@
  | PNone                 -- ^ @none@
  | PObject (Skeleton Pattern)
    -- ^ @LC[app]\`( ${f} ${a} )\`@ — **a term of an object language** (MS6
    -- phase 104c), matched against the 'Thena.Core.Term.Core' it denotes.
    --
    -- **The reading is already compiled away**: what is left is the skeleton,
    -- which names constructors and knows which holes are terms and which are a
    -- token class\'s literal. The grammar was consulted when the pattern was
    -- read and is never needed again.
  | PCore (CoreP Pattern)
    -- ^ @core\`trusted ${c} ${a} ${b}\`@ — **a term of the development
    -- calculus**, matched against the 'Thena.Core.Term.Core' a value holds
    -- (MS12 phase 352, @~9j34x@).
    --
    -- **It is a 'Pattern' and not a mechanism of its own**, which is the whole
    -- of what @spec\/machine.md@ §8 asks for: stage b matches the shape of a
    -- /surface/ term and this asks the same question of a /core/ one, so a
    -- second mechanism would answer one question twice. A head and a
    -- destructuring binding both reach this through 'Thena.Rules.resolvePattern'.
    --
    -- **Resolution is already done**, as it is for 'PObject': a bare word
    -- inside the region named a global and is refused when the base is read if
    -- it named nothing, so nothing here has to be looked up when the pattern
    -- runs.
  deriving (Eq, Show)

-- | A term of an object language with something at each of its splices (MS6
-- phase 104c).
--
-- **One type, two directions** — @discussion\/patterns-and-the-editor.md@ §5:
-- /splice a value IN when building, bind a value OUT when matching/. A
-- @Skeleton Pattern@ is the matching direction and a
-- @Skeleton Thena.Instral.Ops.Operand@ the building one; the position decides
-- which.
--
-- **It is grammar-free on purpose.** Resolution has the grammars and does all
-- the work that needs them — which production a node is, which argument each
-- slot fills, what a token class matched. What reaches the machine is a shape
-- with holes, so nothing about grammars has to be threaded into the engine.
data Skeleton a
  = SNode GlobalName [Skeleton a]
    -- ^ a constructor of the generated datatype, applied to its arguments in
    -- the order §4.6 gives them
  | SLit Literal
    -- ^ a token class's match, written out as the literal it denotes
  | SHole Slot a
    -- ^ a splice, and what the slot at it takes
  deriving (Eq, Show)

-- | What the term at a hole has to be.
data Slot
  = AtTerm
    -- ^ a language slot: an object term, so a 'Thena.Core.Term.Core'
  | AtPrimitive GlobalName
    -- ^ a token class's slot — @String@, @Char@ or @Int@ — so an @instral@
    -- value of that type on either side of the hole
  deriving (Eq, Show)

-- | What the thing at a core pattern's hole has to be (MS12 phase 355).
--
-- **'Slot' one language down, and a type of its own rather than two more
-- constructors there.** An object language's grammar has no binder position and
-- a core region has no token class, so one type would carry a case neither
-- language can reach — and @-Wall@ would then ask every total walk over the
-- other language's holes for an arm it can never take. The question /what does
-- a splice in a region take/ has one shape and two answers, which is what these
-- two types are.
data CoreSlot
  = AtCore
    -- ^ a term position, so a 'Thena.Core.Term.Core'
  | AtBinder
    -- ^ **a binder's identity**, so a 'Thena.Instral.Ops.Identifier' — the
    -- one position in a @core\`…\`@ region that wants a /name/ rather than a
    -- term.
  | AtLevel
    -- ^ **a level argument**, so a 'Thena.Core.Level.Level' (MS12 phase 361,
    -- @~bkrvn@) — the third kind of position a region has, and the level
    -- arrives whole.
  deriving (Eq, Show)

-- | A level argument in a core pattern: written, or a position (MS12 phase
-- 361, @~bkrvn@).
--
-- **'Thena.Syntax.Concrete.RawLevel' after resolution**, and the reason it is
-- a type of its own rather than @CoreP a@ at a level position is that a level
-- is not a term: nothing matches /inside/ a level expression
-- (@spec\/machine.md@ §8), so the only two things a pattern can say about one
-- are /this numeral/ and /whatever it is, and I will take it/.
data LevelP a
  = LPNat Int   -- ^ @{0}@ — compared whole, by normal form
  | LPHole a    -- ^ @{${l}}@ — whatever level stands here, and what takes it
  deriving (Eq, Show)

-- | A core term's shape with something at each of its splices (MS12 phase
-- 352).
--
-- **The twin of 'Skeleton', one language down.** A 'Skeleton' is an object
-- language's term with holes and this is the development calculus's, and both
-- are a tree of the constructors the reading named with a parameter where a
-- @${…}@ stood — so a @CoreP Pattern@ is the matching direction and the
-- building one would be a @CoreP Thena.Instral.Ops.Operand@. Nothing builds
-- one yet: a written @core\`…\`@ in an operand stays a
-- 'Thena.Instral.Ops.VRaw' and is resolved where there is a development to
-- resolve it against.
--
-- **Every field of a node is a position** — @spec\/machine.md@ §8 — which is
-- why 'CPTrusted' carries three and not the two a surface term writes: the
-- derived @actual@ is a field, so a pattern may stand at it.
--
-- **THE BINDERS OPEN A SCOPE, AND THAT IS WHY MATCHING MINTS** (MS12 phase
-- 355). 'CPPi', 'CPLam' and 'CPLet' each carry what their /binder/ binds as
-- well as their sub-terms, and matching one mints a token, puts it in the
-- 'Thena.Instral.Ops.Identifier' the binder position binds, and opens the body
-- at it — so the body a @${E}@ holds is an ordinary term with a free variable
-- where the binder's occurrences were. @~thwhg@ (an alternative is matched
-- again when it is taken) is what made that safe and @~2n5tn@ is what decided
-- the word @intro@ gives it.
data CoreP a
  = CPHole a
    -- ^ @${x}@ — whatever stands here, and what the position takes
  | CPName GlobalName [LevelP a]
    -- ^ a word, resolved, and the level arguments written in braces after it
    --
    -- **No braces means no level arguments, and that is the development
    -- calculus's own reading** (@Thena.Syntax.Resolve@'s @plain@), not a
    -- rule of this type's: @Empty@ written in an operand is
    -- @Global Empty []@, so @Empty@ written in a pattern is what matches it.
    -- A level in braces is a numeral or a position ('LevelP'), and nothing
    -- matches inside one (§8).
  | CPUniverse Int
    -- ^ @Type₀@ — a universe at a written level. @Type@ with no level is an
    -- /inferred/ one and is refused in a pattern: there is nothing to infer
    -- against when a pattern runs.
  | CPLit Literal
    -- ^ @"ab"@, @'c'@, @3@ — a literal of a primitive type, as written
  | CPApp (CoreP a) (CoreP a)
    -- ^ @f a@. **A constructor application is written this way too**, because
    -- that is how the development calculus writes one; the matcher accepts the
    -- saturated 'Thena.Core.Term.Canonical' spelling of the same term, which is
    -- the line 'Thena.Instral.Ops.matchSkeleton' already draws.
  | CPTrusted (CoreP a) (CoreP a) (CoreP a)
    -- ^ @trusted claimed actual body@ — all three fields
  | CPPi a (CoreP a) (CoreP a)
    -- ^ @∀ (${x} : ${T}) -> ${E}@ — the binder, its domain and its opened body
    -- (MS12 phase 355).
    --
    -- **The first field is a name position and the other two are term
    -- positions**, which is why it is an @a@ and not a @CoreP a@: a binder's
    -- identity is a 'Thena.Instral.Ops.Identifier', so the pattern at it is
    -- matched against one. @spec\/machine.md@ §8 — /@${…}@ is the only binding
    -- marker/ — is why a written word is refused there rather than compared: a
    -- binder's word decides nothing, so there is nothing for a written one to
    -- mean.
    --
    -- **@${S} -> ${B}@ is this with the binder unbound**, non-dependent or
    -- not: an arrow's body still sits under a scope, so it is opened to be
    -- matched, and the pattern simply does not name what it was opened at.
  | CPLam a (CoreP a) (CoreP a)
    -- ^ @λ (${x} : ${T}) -> ${E}@ — the binder, its domain and its opened body
  | CPLet a (CoreP a) (CoreP a) (CoreP a)
    -- ^ @let ${x} = ${v} : ${T} in ${E}@ — the binder, its value, its type and
    -- its opened body, in 'Thena.Core.Term.Let''s own field order
  | CPEliminate GlobalName [LevelP a] [CoreP a] (CoreP a) [CoreP a] [CoreP a] (CoreP a)
    -- ^ @elim d {ℓ} (params) motive (methods) (indices) target@ — positional
    -- and in 'Thena.Core.Term.Eliminate''s own field order, exactly as the
    -- development calculus writes it
  deriving (Eq, Show)

-- | The focus as a pattern — what stands after @at@ in a rule head (MS12 phase
-- 358, @~9j34x@).
--
-- **It matches a development COMPONENT, which is a different language from
-- 'Thena.Core.Term.Core'** — his framing of 2026-09-14, @at@ names the subject
-- and the tag names the language. The five constructors are
-- 'Thena.Development.Component.Component'\'s five, in the notation §3.2 prints
-- them in, and they carry no fence while the development calculus is built in
-- (his ruling of 2026-09-13).
--
-- **A component pattern is NOT a 'Pattern'**, and that is not an omission. A
-- 'Pattern' matches a 'Thena.Instral.Ops.Value', and a component is not one:
-- @Development@ is a separate @instral@ type with no introduction form until an
-- op produces one (his ruling of 2026-09-11). So a component pattern stands
-- after @at@ and nowhere else, which is what makes the missing @PComponent@ a
-- consequence of the vocabulary rather than a case left out.
--
-- **Every position holds an ordinary 'Pattern', so a bare word there BINDS.**
-- That is the opposite of a @core\`…\`@ region, where a bare word resolves to a
-- global and only @${…}@ binds, and the tag is the reason: inside a region the
-- text belongs to another language and needs an escape, where @at ? x : s@ is
-- the rule language itself. A @core\`…\`@ pattern may of course stand at a type
-- position — @at ? h : core\`∀ (${x} : ${T}) -> ${E}\`@ — which is what the whole
-- landing is for.
data ComponentP
  = CompAny      Pattern
    -- ^ @‹x›@ — /any/ of the five, standing at its identity and nothing
    -- else (MS12 phase 363, @~9m27n@, his ruling of 2026-11-27).
    --
    -- **It is the one form whose shape is not one of the five**, and that is
    -- the point: a lone pattern is not a near-miss of any particular
    -- component, where @‹x› : ‹S›@ — the other spelling measured — is
    -- @? ‹x› : ‹S›@ with its sigil dropped and would read as /a hole/. **His
    -- objection, 2026-11-27**, and it is what decided the spelling.
    --
    -- What it gives up: a rule wanting the focus\'s /type/ without saying
    -- which form it is has to be written five times, or ask @goal@. Nothing in
    -- the shipped base wants that — the five clauses that used to ask
    -- @focus-is-component@ want the identity or nothing at all.
  | CompAssume   Pattern Pattern
    -- ^ @λ ‹x› : ‹S›@ — the binder and its type
  | CompDefine   Pattern Pattern Pattern
    -- ^ @‹x› = ‹v› : ‹S›@ — the binder, its value and its type
  | CompClaim    Pattern Pattern
    -- ^ @? ‹x› : ‹S›@ — an unopened hole
  | CompGuess    Pattern Pattern
    -- ^ @? ‹x› ≐ _ : ‹S›@ — a hole with a development under it.
    --
    -- **The @≐@ position takes @_@ and nothing else, so it is not a field
    -- here.** What stands there is a 'Thena.Development.Partial.Partial', a
    -- development of its own rather than a term, and @Development@ has no
    -- introduction form until an op produces one (his ruling of 2026-09-11) —
    -- so a pattern binding it would be that introduction form arriving through
    -- a pattern, and nothing in the vocabulary could read the value.
    -- 'Thena.Rules.resolveComponentP' refuses anything but @_@ there, and
    -- @spec\/machine.md@ §8 has the two readings that were measured and
    -- rejected.
  | CompQuantify Pattern Pattern
    -- ^ @∀ ‹x› : ‹S›@ — the fifth component, which folds into a Π
  deriving (Eq, Show)

-- | Each of a component pattern\'s positions with what it stands at, left to
-- right (MS12 phase 358).
--
-- **'CoreSlot' is the right vocabulary and not a coincidence**: a component\'s
-- binder wants a name exactly as a @core\`…\`@ region\'s binder does, and its
-- type and a definition\'s value are core terms. So the question /what does
-- this position take/ has the same two answers here, and
-- 'Thena.Instral.Infer' types both from this one type.
componentPSlots :: ComponentP -> [(CoreSlot, Pattern)]
componentPSlots cp = case cp of
  CompAny      x     -> [(AtBinder, x)]
  CompAssume   x s   -> [(AtBinder, x), (AtCore, s)]
  CompDefine   x v s -> [(AtBinder, x), (AtCore, v), (AtCore, s)]
  CompClaim    x s   -> [(AtBinder, x), (AtCore, s)]
  CompGuess    x s   -> [(AtBinder, x), (AtCore, s)]
  CompQuantify x s   -> [(AtBinder, x), (AtCore, s)]

-- | The names a component pattern binds, left to right (MS12 phase 358).
--
-- **It is 'patternBinds' over the positions**, so a name bound by the focus is
-- bound by the same machinery as one bound by a parameter — which is what lets
-- 'Thena.Rules.validate'\'s scope check and 'Thena.Rules.initiallyBound' reach
-- it without a case of their own.
componentPBinds :: ComponentP -> [Name]
componentPBinds = concatMap (patternBinds . snd) . componentPSlots

-- | What sits at each hole, left to right.
skeletonHoles :: Skeleton a -> [a]
skeletonHoles sk = case sk of
  SNode _ kids -> concatMap skeletonHoles kids
  SLit _       -> []
  SHole _ a    -> [a]

-- | What sits at each of a core pattern's holes, left to right (MS12 phase
-- 352) — 'skeletonHoles' for the language one down.
corePHoles :: CoreP a -> [a]
corePHoles = map snd . corePSlots

-- | Each hole with the slot it stands at, left to right (MS12 phase 355) —
-- 'Thena.Instral.Infer.holesOf' for the language one down.
--
-- **It exists because the binders gave a core region a second kind of hole.**
-- Until them every @${…}@ inside a @core\`…\`@ stood where a term stands, so
-- 'corePHoles' alone was enough and the type was read off the region's tag; a
-- binder position wants a name, so the position has to say what it takes.
corePSlots :: CoreP a -> [(CoreSlot, a)]
corePSlots cp = case cp of
  CPHole a         -> [(AtCore, a)]
  -- **A level argument is a position too, as of MS12 phase 361** (@~bkrvn@),
  -- and it comes before the arguments written after the word, which is the
  -- order it is written in.
  CPName _ ls      -> levelled ls
  CPUniverse _     -> []
  CPLit _          -> []
  CPApp f a        -> corePSlots f ++ corePSlots a
  CPTrusted c a b  -> corePSlots c ++ corePSlots a ++ corePSlots b
  -- **The binder first, then the sub-terms left to right**, which is the order
  -- they are written in and the order the matcher binds them in.
  CPPi x d b       -> (AtBinder, x) : corePSlots d ++ corePSlots b
  CPLam x d b      -> (AtBinder, x) : corePSlots d ++ corePSlots b
  CPLet x v t b    -> (AtBinder, x) : corePSlots v ++ corePSlots t ++ corePSlots b
  CPEliminate _ ls ps m ms is t ->
    levelled ls ++ concatMap corePSlots ps ++ corePSlots m
      ++ concatMap corePSlots ms ++ concatMap corePSlots is ++ corePSlots t
  where
    levelled ls = [ (AtLevel, a) | LPHole a <- ls ]

-- | The names a pattern binds, left to right.
--
-- **Every name-shaped question about a rule goes through this**, which is what
-- keeps @ruleParams@ becoming patterns from being twenty separate changes:
-- 'Thena.Rules.initiallyBound', the reserved-name check and the head's scope
-- check all asked @ruleParams@ for its names and now ask this.
patternBinds :: Pattern -> [Name]
patternBinds pt = case pt of
  PVar n      -> [n]
  PWild       -> []
  PInt _      -> []
  PChar _     -> []
  PBool _     -> []
  PText _     -> []
  PList ps mt -> concatMap patternBinds ps ++ maybe [] patternBinds mt
  PPair a b   -> patternBinds a ++ patternBinds b
  PSome a     -> patternBinds a
  PNone       -> []
  PObject sk  -> concatMap patternBinds (skeletonHoles sk)
  PCore cp    -> concatMap patternBinds (corePHoles cp)

-- | Does this pattern match every value of its type?
--
-- **Only 'Thena.Driver' asks**, and only to decide whether an earlier clause of
-- a /function/ makes a later one unreachable (MS5 phase 80's refusal, narrowed
-- by this phase). A list pattern is refutable even when its elements are
-- variables, because the value may be a different length; a pair is not,
-- because the type says it is a pair.
--
-- **It is deliberately an under-approximation.** Answering 'False' only means
-- /not obviously total/, so the refusal fires less often than it could — which
-- is the safe direction: refusing a clause that would in fact be unreachable is
-- a false alarm, and admitting one is merely dead code the author can see.
patternIrrefutable :: Pattern -> Bool
patternIrrefutable pt = case pt of
  PVar _    -> True
  PWild     -> True
  PPair a b -> patternIrrefutable a && patternIrrefutable b
  _         -> False

