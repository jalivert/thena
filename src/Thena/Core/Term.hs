-- | The core language: its terms, the names that appear in them, and the
-- opaque 'Scope' that carries a binder's body.
--
-- This module spends two of the three places the project uses levelOfNat 1
-- enforcement (@PLAN.md@ §3.4, §2.5):
--
--   * 'Scope' — only 'close' builds one; only 'open' and 'instantiate' take one
--     apart. A dangling de Bruijn index is therefore unconstructible.
--   * 'Var' — only 'fresh' mints one, which makes §3.2's "globally unique"
--     structural rather than a convention followed by hand.
--
-- 'Scope' is declared here rather than in a module of its own because 'Core'
-- mentions it and 'close' must traverse 'Core': two modules would import each
-- other. Decided 2026-08-21; §2.5 and @AGENDA.md@ item 20a carry the argument.
module Thena.Core.Term
  ( -- * Names
    Var
  , fresh
  , Ident (..)
  , GlobalName (..)
  , rootName
  , nameDotted
  , declarationNamespace
  , inDeclarationOf
  , inLemmataOf
  , lemmataStep
  , declarationOf
  , declarationNamed
  , globalUnder
  , InScope (..)
  , rootScope
  , openingOnly
  , Opened (..)
  , openedWhole
  , openedWord
  , shortestEnding
  , Spelling (..)
  , wholePath
  , spelledIn
  , nameFromText

    -- * Terms
  , Core (..)
  , Literal (..)
  , primitiveType
  , tokenName
  , tokenType
  , Scope  -- NB: the type only. Hiding 'MkScope' is the point of the module.

    -- * Binding
  , close
  , open
  , instantiate
  , freeVars
  , globalsIn
  , holdsTrusted
  , beyond
  , substLevelsIn
  , substLevelsInScope
  , referencesAt
  , levelMetasIn
  ) where

import Data.List (intercalate, nub)

import Thena.Core.Level (Level (..), LevelVar, metasIn, substLevel)

-- | A reference to a binding, globally unique within a session.
--
-- The constructor is not exported: 'fresh' is the only way to make one, so
-- nothing can write @Var 3@ and collide with a live binding (§2.5).
newtype Var = Var Int
  deriving (Eq, Ord, Show)

-- | Mint a variable from the session's name counter and give the counter back.
--
-- The counter is an 'Int' held in the outer state and threaded by hand. There is
-- deliberately no supply type, no monad and no newtype around it (§3.5,
-- @PREPLAN.md@ standing rule 7).
fresh :: Int -> (Var, Int)
fresh n = (Var n, n + 1)

-- | What the user calls a binding. Display only, no semantic content (§3.2) —
-- which is exactly why 'Eq' on 'Core' ignores it.
--
-- 'Eq' here is real, and phase 2's resolver depends on that: it looks a written
-- name up in the context by comparing identifiers.
newtype Ident = Ident String
  deriving (Eq, Ord, Show)

-- | A name in the global environment (§3.6, decided 2026-08-11; given a path
-- 2026-10-30, MS10's module system).
--
-- __The steps of a namespace path, then the base word.__ @Nat.elim@ is
-- @GlobalName ["Nat"] "elim"@, and a name in no namespace has no steps — which
-- is every name the system had before MS10, and what 'rootName' makes.
--
-- No namespace /tag/ — the node position already says which kind of thing is
-- being named, so a tag would be data derivable from its own context and able to
-- disagree with it. One namespace, shared with generated names. A path is not a
-- tag: it says where a name lives, not what kind of thing it names, so the 2026-08-11
-- ruling stands except for the word "flat" (his ruling of 2026-10-29).
--
-- __The word is unrestricted; only the path has structure.__ @‹x›@ and
-- @", do block 2"@ are words containing brackets and spaces, so nothing may
-- assume a name is lexable. 'nameDotted' is therefore a printed form and not
-- always something that can be typed back.
data GlobalName = GlobalName
  { nameSteps :: [String]  -- ^ the namespace path, outermost first; empty at the root
  , nameWord  :: String    -- ^ the base word, unrestricted
  }
  deriving (Eq, Ord, Show)

-- | A name in no namespace — what every global name was before MS10.
rootName :: String -> GlobalName
rootName = GlobalName []

-- | The full path, dotted: @Nat.elim@, and @elim@ for a name at the root.
--
-- **This is the whole name and not what a user is shown.** The printer's policy
-- (his ruling of 2026-10-30) is to print the shortest ending of the path that
-- re-resolves to the same name in the scope being printed from, so this is what
-- that policy falls back to and what a name with nothing open prints as.
nameDotted :: GlobalName -> String
nameDotted (GlobalName ps w) = concatMap (++ ".") ps ++ w

-- | The namespace a declaration of this name opens.
--
-- __The declaration's own steps, because the declaration lives inside its own
-- namespace__ (MS10 phase 248): a datatype is @Nat.Nat@, so the namespace it
-- opens is @["Nat"]@ and its equipment is @Nat.elim@, @Nat.Below@ and so on.
-- **This is the line that moved the constructors in** — not the twelve sites
-- that mint a name, which all go through 'inDeclarationOf' and said nothing
-- about placement. Before phase 248 a datatype was @Nat@ at the root and this
-- appended its word.
declarationNamespace :: GlobalName -> [String]
declarationNamespace = nameSteps

-- | A name for @word@ in the namespace @d@\'s declaration opens.
inDeclarationOf :: GlobalName -> String -> GlobalName
inDeclarationOf d word = GlobalName (declarationNamespace d) word

-- | The step a datatype\'s generated relations and proofs live under.
--
-- __His ruling of 2026-11-01.__ A datatype\'s namespace holds what the user
-- wrote plus the eliminator pair; everything the system /derives/ sits one step
-- deeper, so the two levels can never answer the same word. Before this,
-- @data Below@ was refused — the datatype wanted @Below.Below@ and so did its
-- own generated structural order — and the word @Below@ was ambiguous six ways
-- in a bare session, the prelude\'s datatypes having each put one in scope.
lemmataStep :: String
lemmataStep = "lemmata"

-- | A name for @word@ among @d@\'s generated lemmata: @Nat.lemmata.Below@.
--
-- **Not 'inDeclarationOf'** — that is for what the declaration itself names,
-- which is the datatype, its constructors, @elim@ and @case@. A word minted
-- here is one no user wrote, so it is reached by @open Nat.lemmata@ rather than
-- competing with their own names.
inLemmataOf :: GlobalName -> String -> GlobalName
inLemmataOf d word = GlobalName (declarationNamespace d ++ [lemmataStep]) word

-- | A name as a user writes it, split on the reserved dot: @Nat.elim@ is
-- @GlobalName ["Nat"] "elim"@, and a word with no dot comes back rooted.
--
-- __For text that has not been through the lexer, which is a REPL command's
-- argument and nothing else.__ Every other name in the system arrives as the
-- pieces the lexer made — @.@ is reserved, so @Nat.elim@ in a /term/ is three
-- tokens before anything sees it. A command's argument is the one name taken
-- from a raw line, and @:show Nat.elim@ has to work, so the split happens here
-- rather than each command inventing it.
--
-- **It is not a check**: a word the lexer would refuse comes back as a word, and
-- the lookup that follows is what reports it. @nameDotted@ is the inverse where
-- the word holds no dot of its own, which a generated name's does not.
nameFromText :: String -> GlobalName
nameFromText t = case reverse (steps t) of
  w : rs -> GlobalName (reverse rs) w
  []     -> rootName t
  where
    steps u = case break (== '.') u of
      (a, '.' : b) -> a : steps b
      (a, _)       -> [a]

-- | 'inDeclarationOf' backwards: whose declaration's namespace is this name in?
--
-- @declarationOf (GlobalName ["Nat"] "elim")@ is @Just (GlobalName ["Nat"] "Nat")@,
-- and a name at the root is in nobody's, so 'Nothing'. **The last step names the
-- declaration** (MS10 phase 248), because a declaration's word is the step it
-- contributed.
--
-- __It is what replaces reading a generated name's spelling.__ Recovering the
-- datatype from @elimNat@ meant stripping the four characters @elim@ off the
-- front and hoping the rest named one, which is a test on how a name is spelled
-- rather than on what it is; the path says it outright. The word is still
-- compared — a name is @elim@ or it is not — but that is one equality against a
-- fixed word, not arithmetic on a string the user may also have written.
declarationOf :: GlobalName -> Maybe GlobalName
declarationOf (GlobalName ps _) = case reverse ps of
  []    -> Nothing
  w : _ -> Just (GlobalName ps w)

-- | The declaration a written short name denotes: @Nat@ is @Nat.Nat@.
--
-- __The resolver-level short name a declaration mints__ (HIS ruling,
-- 2026-10-29; MS10 phase 248). A @data Nat@ declaration puts everything it
-- produces inside the namespace @Nat@, **the type among them**, so the one name
-- it adds to the enclosing scope is the namespace — and @Nat@ written in a
-- signature is this.
--
-- **It is a resolution fact and not a definition.** Nothing enters the
-- environment, so δ has nothing to unfold and no stored term can carry the
-- short name instead of the real one: a 'Core' term says @Nat.Nat@ and always
-- did say the real name.
--
-- **And it is derived rather than recorded**, which is the same argument that
-- kept a namespace table out of 'Thena.Global.Env' (HIS ruling, 2026-10-30): a
-- table of aliases would hold a second copy of what the environment's keys
-- already say and could disagree with them. The two sites that need it are
-- resolution, which probes it, and 'Thena.Driver.datatypeProgram', which mints
-- the name it points at — one function, so they cannot drift apart.
declarationNamed :: GlobalName -> GlobalName
declarationNamed (GlobalName ps w) = GlobalName (ps ++ [w]) w

-- | __Where a written name is looked up from.__
--
-- **Two lists and they are not the same kind of thing** (MS10 phase 254).
-- 'scopeWithin' is ordered and a nearer rung wins outright; 'scopeOpens' is a
-- set, and two of them answering one written word is a refusal rather than a
-- choice — his ruling of 2026-10-30.
--
-- **One record rather than two parameters**, for the reason
-- 'Thena.Syntax.Resolve.Globals' already gives about the opens: a caller saying
-- what is in scope says it in full, instead of every door having to remember a
-- second argument.
data InScope = InScope
  { scopeWithin :: [[String]]
    -- ^ the namespaces this point is inside, **innermost first** — what
    -- @namespace X where { … }@ pushes for its declarations
  , scopeOpens  :: [Opened]
    -- ^ the namespaces an @open@ has brought into view, latest first
  }
  deriving (Eq, Show)

-- | __One @open@, with whatever it said about which names it brings in.__
--
-- **His ruling of 2026-10-30 gives five forms and this is all of them**:
-- @open X@, @open X Y Z@ (which is three of these), @open X ( a b )@,
-- @open X hiding ( … )@ and @open X renaming ( e -\> c )@.
--
-- **Hiding and renaming are a filter on the WORD, not on a path.** A namespace
-- is a prefix, so what an @open@ can say something about is the word that
-- follows the prefix — and for a deeper name it is the first step, so
-- @open A ( B )@ brings in @B.c@ and nothing else of @A@'s.
--
-- **Renaming replaces the word rather than adding one**, as Agda's does: after
-- @open Expr renaming ( e -\> expr )@ a written @expr@ is @Expr.e@ and a written
-- @e@ is not in scope. Which is what makes it the tie-break when two opened
-- languages use one letter.
--
-- **Visibility, and not opacity.** A name an @open@ hid is still a key in the
-- environment and still what a term carries, so a hidden constructor can appear
-- in a printed goal. Making it genuinely opaque would mean the printer and the
-- kernel respecting an @open@, which is not what this is.
data Opened = Opened
  { openedPath     :: [String]
    -- ^ the namespace's whole path
  , openedOnly     :: Maybe [String]
    -- ^ @Just ws@ for @open X ( ws )@ — only these words. 'Nothing' is every
    -- word under the prefix, which is what @open X@ says.
  , openedHiding   :: [String]
    -- ^ the words @open X hiding ( … )@ keeps out
  , openedRenaming :: [(String, String)]
    -- ^ @(original, as written)@ — @open X renaming ( e -\> c )@ is @("e", "c")@
  }
  deriving (Eq, Show)

-- | @open X@ — the whole namespace, nothing hidden and nothing renamed.
openedWhole :: [String] -> Opened
openedWhole p = Opened p Nothing [] []

-- | The word an @open@ answers a written name with, if it answers it at all.
--
-- **The written name's first step is what is filtered**, and a renaming
-- replaces it. 'Nothing' means this @open@ says nothing about the name.
openedWord :: Opened -> GlobalName -> Maybe GlobalName
openedWord o g = case lookup first [ (w, orig) | (orig, w) <- openedRenaming o ] of
  Just orig -> Just (under (orig : rest))
  Nothing
    | first `elem` map fst (openedRenaming o) -> Nothing
      -- **a word that was renamed is no longer in scope under its own
      -- spelling**, which is what makes a renaming a tie-break rather than a
      -- second way in
    | first `elem` openedHiding o -> Nothing
    | maybe False (notElem first) (openedOnly o) -> Nothing
    | otherwise -> Just (under (first : rest))
  where
    -- 'nameSteps' may be empty; the word never is, so this list never is.
    (first, rest) = case nameSteps g of
      st : sts -> (st, sts ++ [nameWord g])
      []       -> (nameWord g, [])
    under ws = case reverse ws of
      w : before -> GlobalName (openedPath o ++ reverse before) w
      []         -> GlobalName (openedPath o) (nameWord g)

-- | At the root, with nothing opened — a prompt's scope before any @open@.
rootScope :: InScope
rootScope = InScope [] []

-- | Only these namespaces open whole, at the root.
openingOnly :: [[String]] -> InScope
openingOnly ps = InScope [] (map openedWhole ps)

-- | __Which global a written name means, in a scope.__
--
-- **The one walk, and every door calls it** (MS10 phase 249, repairing
-- `~7zn7k`). It lives here, at the bottom of the import graph, because the two
-- doors cannot both reach either of their own modules:
-- 'Thena.Engine.globalNamed' had the only copy and 'Thena.Syntax.Resolve' — a
-- REPL command's argument, a core term, a tagged term literal — could not call
-- it, since 'Thena.Engine' imports 'Thena.Syntax.Resolve'. **A name meaning two
-- things depending on which door the text came in by is exactly what the first
-- design principle forbids**, and it was a live defect: after @open Ctx@,
-- @:infer empty@ answered @empty : Ctx.Ctx@ while @:theorem foo : … empty …@
-- answered @not in scope: empty@.
--
-- The caller supplies @known@, because what counts as in scope differs
-- legitimately: the engine asks its environment, and a declaration resolving
-- its own constructors adds the datatype being declared, which is not in the
-- environment and cannot be.
--
-- * @Right g@ — this is the name.
-- * @Left []@ — nothing answers it.
-- * @Left gs@, two or more — **refused and not chosen** (2026-10-30): either
--   would type-check, so picking one would be the system deciding what the user
--   did not write. The caller names them all.
--
-- **The enclosing namespaces are walked innermost outward, and nearer wins
-- outright** (MS10 phase 254, his ruling of 2026-10-30). Inside @A.B@ a written
-- @x@ is tried as @A.B.x@, then @A.x@, then @x@ — the root is the last rung of
-- the walk and not the first. The @open@s are tried only once every rung has
-- failed, which is what makes an @open@ able to add a way to resolve and never
-- change one: a name that the walk answers is never reconsidered under one.
--
-- **A path the writer wrote says what they meant**, so the whole written name
-- goes under each prefix: inside @A@, a written @B.c@ tries @A.B.c@ first.
globalUnder
  :: (GlobalName -> Bool) -> InScope -> GlobalName
  -> Either [GlobalName] GlobalName
globalUnder known sc g =
  case [ c | ns <- scopeWithin sc ++ [[]], c <- under ns, known c ] of
    c : _ -> Right c
    []    -> case nub (filter known (concatMap opened (scopeOpens sc))) of
      [g'] -> Right g'
      gs   -> Left gs
  where
    -- **The whole written name under a prefix**, so @open A@ and a written
    -- @B.c@ tries @A.B.c@.
    --
    -- **Then the same as a declaration's short name**: @Nat@ is the datatype
    -- @Nat.Nat@, the alias 'declarationNamed' derives. It is applied under the
    -- prefixes too, so @open A@ and a written @Nat@ reaches @A.Nat.Nat@ — the
    -- alias is a fact about a name, not about the scope it was found in.
    --
    -- **The exact name comes first and the alias second**, which is what makes
    -- a rung answer with one name rather than two: a theorem called @Nat@ and a
    -- datatype @Nat.Nat@ both answer a written @Nat@, and the theorem wins
    -- because it is what the word names exactly (`~s89ch`).
    under ns = let q = GlobalName (ns ++ nameSteps g) (nameWord g)
                in [q, declarationNamed q]
    -- **An @open@ may say nothing about this name at all** — hidden, not in its
    -- selection, or spelled under a word it renamed — and then it offers no
    -- candidate, so it cannot make an ambiguity either.
    opened o = case openedWord o g of
      Nothing -> []
      Just q  -> [q, declarationNamed q]

-- | __Where a name is being written from, and what answers there.__
--
-- The two arguments 'shortestEnding' takes, travelling together — because they
-- always do: a scope with no environment answers nothing, and an environment
-- with no scope answers the whole path. 'Thena.Render.Rendering' holds the same
-- pair beside the grammars, and **the view\'s shapes take one of these** (MS10
-- phase 256, `~fjrrr`), so that a name has one spelling whichever door the
-- reader came in by.
data Spelling = Spelling
  { spellingKnown :: GlobalName -> Bool
  , spellingScope :: InScope
  }

-- | A spelling that knows no environment and has nothing open — every name is
-- written whole. What a caller with no session to ask gets.
wholePath :: Spelling
wholePath = Spelling (const False) rootScope

-- | The shortest ending of this name that still means it here.
spelledIn :: Spelling -> GlobalName -> String
spelledIn sp = shortestEnding (spellingKnown sp) (spellingScope sp)

-- | __How to write a name here: the shortest ending of it that still means
-- it.__
--
-- **The inverse of 'globalUnder', and it asks that function rather than
-- reasoning about it** (MS10 phase 254): an ending is right exactly when
-- resolving it in this scope gives back the name we started from. So the
-- printer cannot drift from the reader, and an ending that two namespaces
-- would answer is rejected for free — 'globalUnder' calls that an ambiguity
-- and does not return a name at all.
--
-- @Nat.Nat@ prints as @Nat@ with nothing open, because a declaration's short
-- name resolves to it; @Nat.zero@ prints as @zero@ after @open Nat@ and as
-- @Nat.zero@ before it. **With nothing declared and nothing open the answer is
-- the whole path**, which is what a caller that knows no environment gets.
shortestEnding :: (GlobalName -> Bool) -> InScope -> GlobalName -> String
shortestEnding known sc g = case [ e | e <- endings, means e ] of
  e : _ -> intercalate "." e
  []    -> nameDotted g
  where
    ws = nameSteps g ++ [nameWord g]
    -- Shortest first, and the whole name last.
    endings = [ drop k ws | k <- [length ws - 1, length ws - 2 .. 0] ]
    means e = case reverse e of
      w : before -> globalUnder known sc (GlobalName (reverse before) w) == Right g
      []         -> False

-- | The body of a binder, with the bound variable replaced by a de Bruijn index.
--
-- The constructor is not exported. 'close' is the only way in and 'open' and
-- 'instantiate' are the only ways out, which is what makes a dangling index
-- unconstructible (§3.4).
newtype Scope a = MkScope a
  deriving (Eq, Show)

-- | A literal (MS6 phases 97a and 100).
--
-- The four sit here rather than in constructors of 'Core' because nothing about
-- the term language distinguishes them: they are opaque values whose type is
-- fixed ('primitiveType') and whose only operation is equality.
data Literal
  = LString String
  | LChar Char
  | LInt Integer                       -- ^ arbitrary precision, per @ms6\/SPEC.md@ §2.1
  | LRegex String
    -- ^ a token class's regular expression, as its source text between the
    -- slashes (MS6 phase 100, @ms6\/SPEC.md@ §3.1). **Only the text**: which of
    -- @String@, @Char@, @Int@ a match becomes is an /argument/, not a field —
    -- see 'primitiveType'. Two are equal when their text is, as strings are:
    -- @\/a|b\/@ and @\/b|a\/@ accept the same strings and are different terms.
  deriving (Eq, Show)

-- | The type a literal inhabits, read off the literal alone.
--
-- The three primitive types and @Token@ are seeded into every environment as
-- constants ('Thena.Global.Env.primitives'), so a user cannot declare something
-- else by those names, and this function is the only place the association is
-- written.
--
-- **A regex literal's type is a Π — HIS RULING, 2026-09-19.** @\/[a-z]\/@ is a
-- @Token String@ in one declaration and a @Token Char@ in another, so the
-- literal takes its @T@ as an argument:
--
-- @
-- \/[a-z]\/ : ∀ (T : Type₀) -> Token T
-- @
--
-- and elaboration applies it to a hole that unification solves from the goal.
-- The alternative, @T@ carried /inside/ the literal, would need @T@ before
-- @fill@ — it is only in the goal, which nothing in @instral@ can take apart —
-- or a literal holding a Core term, which every traversal here would then have
-- to look inside. @\/[a-z]\/ Bool@ is therefore well typed; it is refused by the
-- token-class checks at declaration (@Thena.Driver.checkedTokenClass@), and
-- cannot be unsound because nothing eliminates a @Token@.
primitiveType :: Literal -> Core
primitiveType l = case l of
  LString{} -> Global (rootName "String") []
  LChar{}   -> Global (rootName "Char") []
  LInt{}    -> Global (rootName "Int") []
  LRegex{}  -> Pi (Ident "T") (Universe LZero) (MkScope (App (Global tokenName []) (Bound 0)))

-- | @Token : Type₀ -> Type₀@, the type former of token classes (MS6 phase 100).
tokenName :: GlobalName
tokenName = rootName "Token"

-- | 'tokenName'\'s type. Seeded by 'Thena.Global.Env.emptyGlobals'; written
-- here because 'Scope' can only be built in this module.
tokenType :: Core
tokenType = Pi (Ident "T") (Universe LZero) (MkScope (Universe LZero))

-- | The core language (§3.6).
--
-- **§3.6 said "settled and closed: no later phase adds a constructor here", and
-- MS6 phase 97a is the one exception, with his ruling of 2026-09-18 behind it.**
-- The level change of MS3 stayed inside the letter of that sentence by making
-- 'Global' carry a field; a literal cannot, because a literal /is/ a term and
-- there is no node it could be without pretending to be a 'Canonical' of a
-- former nothing declares. The alternative he weighed and refused was building
-- @Char@ and @String@ from an inductive numeral in the prelude, which costs a
-- constructor chain per identifier in every object-language term.
-- See @discussion\/object-language-modelling.md@ §9.11 and @ms6\/SPEC.md@ §2.1.
data Core
  = Bound Int                          -- ^ a binder inside this term
  | Free Var                           -- ^ a component in the context
  | Global GlobalName [Level]          -- ^ a definition, at level arguments
  | Universe Level
  | Pi Ident Core (Scope Core)         -- ^ @Π x : S . B@
  | Lam Ident Core (Scope Core)        -- ^ @λ x : S . b@
  | App Core Core
  | Let Ident Core Core (Scope Core)   -- ^ @x = s : S . t@
  | Canonical GlobalName [Level] [Core] -- ^ saturated former, at level arguments
  | Primitive Literal                        -- ^ a literal of a primitive type (MS6 phase 97a)
  | Eliminate                          -- ^ saturated use of an eliminator
      { eliminated :: GlobalName
      , levels     :: [Level]
      , parameters :: [Core]
      , motive     :: Core
      , methods    :: [Core]
      , indices    :: [Core]
      , target     :: Core
      }
  | Trusted Core Core Core
    -- ^ @trusted claimed actual body@ (MS8 phase 149): a term whose type is
    -- /asserted/ to be @claimed@ while @body@ was checked at @actual@. The
    -- second exception to the closed core term language, after 'Primitive'.
    --
    -- **@actual@ is derived and the user never writes it**, the way 'Lam'
    -- always carries its domain while a surface lambda's annotation is
    -- optional: elaboration infers the body's type, because nothing can type
    -- this node without it.
    --
    -- **The pair @(claimed, actual)@ is the obligation, written down with both
    -- halves visible** — his observation, 2026-10-05. As the names in them
    -- instantiate the two converge and the node contracts away, so @actual@ is
    -- what says whether the trust is still load-bearing.
  deriving (Show)

-- | Alpha-equivalence (§3.5).
--
-- Written out rather than derived because 'Pi', 'Lam' and 'Let' carry an
-- 'Ident', and a derived instance would compare display names — making
-- @λ x:A. x@ and @λ y:A. y@ unequal. Every other field is compared
-- structurally, with no renaming and no environment: that is what the de Bruijn
-- scopes buy, and it holds only because 'Canonical' is saturated, so a former
-- application has exactly one spelling (§12 invariant 6).
--
-- The final catch-all makes a missing case compare 'False' rather than warn.
-- That is tolerable only because 'Core' changes rarely — and when MS6 phase 97a
-- added 'Primitive', this instance was indeed the first place that needed a
-- line. Two literals compare by 'Literal'\'s own derived instance, so a 'LChar'
-- and a one-character 'LString' are unequal, which is what keeps @'a'@ and
-- @\"a\"@ from converting (@Thena.Core.PrimitiveTests@ states that as a test,
-- because 'Thena.Core.Convert' has no case of its own for a literal).
--
-- **All four places a 'Thena.Core.Level.Level' can sit are compared** — a
-- 'Universe' and the three reference forms' arguments (MS3, his ruling of
-- 2026-08-29). @Canonical@ and @Eliminate@ discarded theirs from phase 29 until
-- then, which made this instance disagree with the two places that state the
-- rule: 'Thena.Core.Convert' calls two uses of one former at different levels a
-- clash, and 'Thena.Core.Unify' unifies their level arguments before their term
-- arguments.
--
-- **Nothing could exhibit the disagreement**, because a @Canonical@ reaches a
-- term only by δ-unfolding a saturated wrapper, so two written terms still
-- compare at their @Global@ heads — where the levels /were/ compared — and the
-- fast path correctly declined. That is not a reason to leave it: **equal
-- implies convertible** is the licence conversion's fast path runs on (see
-- 'Thena.Core.Convert'), and it was false as written.
instance Eq Core where
  Bound i        == Bound j          = i == j
  Free x         == Free y           = x == y
  Global f ks    == Global g ls      = f == g && ks == ls
  Universe k     == Universe l       = k == l
  Pi _ s b       == Pi _ s' b'       = s == s' && b == b'
  Lam _ s b      == Lam _ s' b'      = s == s' && b == b'
  App f a        == App g c          = f == g && a == c
  Let _ v s b    == Let _ v' s' b'   = v == v' && s == s' && b == b'
  Primitive a    == Primitive b      = a == b
  Canonical f ks as == Canonical g ls bs = f == g && ks == ls && as == bs
  Eliminate d ks ps m ms is t == Eliminate d' ls ps' m' ms' is' t' =
    d == d' && ks == ls && ps == ps' && m == m' && ms == ms' && is == is' && t == t'
  Trusted c a b  == Trusted c' a' b'  = c == c' && a == a' && b == b'
  _ == _ = False

-- | Abstract a free variable: every @'Free' x@ becomes the index of the binder
-- being built. The @abstract@ of §3.4.
close :: Var -> Core -> Scope Core
close x = MkScope . go 0
  where
    go :: Int -> Core -> Core
    go d t = case t of
      Bound i        -> Bound i
      Free y         -> if y == x then Bound d else Free y
      Global g ls    -> Global g ls
      Universe k     -> Universe k
      Primitive l    -> Primitive l
      Pi i s b       -> Pi i (go d s) (under d b)
      Lam i s b      -> Lam i (go d s) (under d b)
      App f a        -> App (go d f) (go d a)
      Let i v s b    -> Let i (go d v) (go d s) (under d b)
      Canonical f ls as -> Canonical f ls (map (go d) as)
      Eliminate dn ls ps m ms is tgt ->
        Eliminate dn ls (map (go d) ps) (go d m) (map (go d) ms)
                  (map (go d) is) (go d tgt)
      Trusted c a b  -> Trusted (go d c) (go d a) (go d b)

    under :: Int -> Scope Core -> Scope Core
    under d (MkScope b) = MkScope (go (d + 1) b)

-- | Replace the variable a 'Scope' binds with a term. The @instantiate@ of §3.4.
--
-- **No shifting.** Everything free is a 'Free' and never a 'Bound', so nothing
-- in the substituted term can be captured and nothing needs renumbering. This is
-- the bug class §11 says locally nameless removes, and it is removed by there
-- being no function here to get wrong.
--
-- An index greater than the current depth would be dangling, and cannot occur:
-- a 'Scope' is only ever built by 'close', which abstracts one variable.
instantiate :: Core -> Scope Core -> Core
instantiate v (MkScope body) = go 0 body
  where
    go :: Int -> Core -> Core
    go d t = case t of
      Bound i        -> if i == d then v else Bound i
      Free y         -> Free y
      Global g ls    -> Global g ls
      Universe k     -> Universe k
      Primitive l    -> Primitive l
      Pi i s b       -> Pi i (go d s) (under d b)
      Lam i s b      -> Lam i (go d s) (under d b)
      App f a        -> App (go d f) (go d a)
      Let i w s b    -> Let i (go d w) (go d s) (under d b)
      Canonical f ls as -> Canonical f ls (map (go d) as)
      Eliminate dn ls ps m ms is tgt ->
        Eliminate dn ls (map (go d) ps) (go d m) (map (go d) ms)
                  (map (go d) is) (go d tgt)
      Trusted c a b  -> Trusted (go d c) (go d a) (go d b)

    under :: Int -> Scope Core -> Scope Core
    under d (MkScope b) = MkScope (go (d + 1) b)

-- | Open a 'Scope' with a variable. The move the cursor makes descending under a
-- binder (§3.5, §4.6), and what conversion does to compare two binders' bodies
-- (§5.2).
open :: Var -> Scope Core -> Core
open x = instantiate (Free x)

-- | The free variables of a term, in order of first occurrence, without repeats.
--
-- Here because it is what makes the 'close'/'open' round-trip test mean
-- anything: a 'close' and an 'open' that both did nothing would satisfy the
-- round trip by themselves. §3.4's scope check for @fill@ wants this too, from
-- phase 4.
freeVars :: Core -> [Var]
freeVars = nub . go
  where
    go :: Core -> [Var]
    go t = case t of
      Bound _                     -> []
      Primitive _                 -> []
      Free y                      -> [y]
      Global _ _                  -> []
      Universe _                  -> []
      Pi _ s (MkScope b)          -> go s ++ go b
      Lam _ s (MkScope b)         -> go s ++ go b
      App f a                     -> go f ++ go a
      Let _ v s (MkScope b)       -> go v ++ go s ++ go b
      Canonical _ _ as              -> concatMap go as
      Eliminate _ _ ps m ms is tgt  ->
        concatMap go ps ++ go m ++ concatMap go ms ++ concatMap go is ++ go tgt
      Trusted c a b                 -> go c ++ go a ++ go b

-- | The global names a term mentions, in order of first occurrence, without
-- repeats.
--
-- Here for the same reason 'freeVars' is: it must see inside a 'Scope', and
-- 'MkScope' is not exported. Phase 6's strict-positivity check is what wants
-- it — "does the datatype being declared occur in this constructor argument's
-- domain?" is exactly this question, and asking it by opening every binder
-- would mint display variables for no reason (§3.7).
-- | Does this term hold a 'Trusted' node anywhere inside it? (MS8 phase 151.)
--
-- **Here for 'globalsIn'\'s reason**: it must see inside a 'Scope', and
-- @MkScope@ is not exported. Asking it by opening every binder would mint a
-- display variable for no reason (§3.7) — and in this case for a very definite
-- reason not to, since what wants this is a walk whose whole cost is the
-- variables it would otherwise mint.
holdsTrusted :: Core -> Bool
holdsTrusted t = case t of
  Bound _                      -> False
  Free _                       -> False
  Global _ _                   -> False
  Universe _                   -> False
  Primitive _                  -> False
  Trusted {}                   -> True
  Pi _ s (MkScope b)           -> holdsTrusted s || holdsTrusted b
  Lam _ s (MkScope b)          -> holdsTrusted s || holdsTrusted b
  App f x                      -> holdsTrusted f || holdsTrusted x
  Let _ v s (MkScope b)        -> any holdsTrusted [v, s, b]
  Canonical _ _ as             -> any holdsTrusted as
  Eliminate _ _ ps m ms is tgt ->
    any holdsTrusted (ps ++ [m] ++ ms ++ is ++ [tgt])

globalsIn :: Core -> [GlobalName]
globalsIn = nub . go
  where
    go :: Core -> [GlobalName]
    go t = case t of
      Bound _                     -> []
      Primitive _                 -> []
      Free _                      -> []
      Global g _                  -> [g]
      Universe _                  -> []
      Pi _ s (MkScope b)          -> go s ++ go b
      Lam _ s (MkScope b)         -> go s ++ go b
      App f a                     -> go f ++ go a
      Let _ v s (MkScope b)       -> go v ++ go s ++ go b
      Canonical g _ as              -> g : concatMap go as
      Eliminate d _ ps m ms is tgt  ->
        d : (concatMap go ps ++ go m ++ concatMap go ms ++ concatMap go is ++ go tgt)
      Trusted c a b                 -> go c ++ go a ++ go b

-- | Apply a level substitution everywhere in a term (MS3 phase 30).
--
-- What instantiating a definition's level scheme does to its stored type.
--
-- **Levels occur in exactly four places** and this is the list: a @Universe@,
-- and the level arguments of the three reference forms. Everything else is
-- structural recursion — which is the practical shape of levels being
-- context-free, the same fact that lets 'close' and 'open' ignore them
-- entirely.
--
-- **This lives here and not in "Thena.Core.Level"** because it traverses
-- 'Core', and that module deliberately knows nothing about terms.
substLevelsIn :: [(LevelVar, Level)] -> Core -> Core
substLevelsIn sub = go
  where
    at = substLevel sub

    go t = case t of
      Bound i        -> Bound i
      Primitive l    -> Primitive l
      Free x         -> Free x
      Global g ls    -> Global g (map at ls)
      Universe l     -> Universe (at l)
      Pi i s (MkScope b)  -> Pi i (go s) (MkScope (go b))
      Lam i s (MkScope b) -> Lam i (go s) (MkScope (go b))
      App f a        -> App (go f) (go a)
      Let i v s (MkScope b) -> Let i (go v) (go s) (MkScope (go b))
      Canonical f ls as -> Canonical f (map at ls) (map go as)
      Eliminate dn ls ps m ms is tgt ->
        Eliminate dn (map at ls) (map go ps) (go m) (map go ms)
                  (map go is) (go tgt)
      Trusted c a b  -> Trusted (go c) (go a) (go b)

-- | Give every reference to @g@ that carries no level arguments these ones
-- (MS3, review of the milestone).
--
-- **What a datatype's own recursive occurrences need.** A declaration is
-- resolved before anything knows how many level parameters it will have, so
-- @succ : N -> N@ stores its argument as @Global N []@; generalisation then
-- gives @N@ a parameter and that stored @[]@ becomes an arity error, which is
-- how @data N : Type where { z : N ; s : N -> N }@ came to be refused outright.
-- 'Thena.Global.Declare' repairs it the moment the parameter list exists.
--
-- **Only the empty list is filled in.** A reference that already says which
-- levels it is at was written that way on purpose and is left alone.
--
-- Reaching inside a 'Scope' is safe for 'substLevelsIn''s reason: this touches
-- no 'Bound' and no 'Free', so it commutes with every binder.
referencesAt :: GlobalName -> [Level] -> Core -> Core
referencesAt g ls = go
  where
    go t = case t of
      Bound i             -> Bound i
      Primitive l         -> Primitive l
      Free x              -> Free x
      Global h []
        | h == g          -> Global h ls
      Global h ks         -> Global h ks
      Universe l          -> Universe l
      Pi i s (MkScope b)  -> Pi i (go s) (MkScope (go b))
      Lam i s (MkScope b) -> Lam i (go s) (MkScope (go b))
      App f a             -> App (go f) (go a)
      Let i v s (MkScope b) -> Let i (go v) (go s) (MkScope (go b))
      Canonical f ks as   -> Canonical f ks (map go as)
      Eliminate d ks ps m ms is tgt ->
        Eliminate d ks (map go ps) (go m) (map go ms) (map go is) (go tgt)
      Trusted c a b       -> Trusted (go c) (go a) (go b)

-- | The same, under a binder.
--
-- **No opening and no freshening**, which is the whole point: levels are
-- context-free, so a level substitution commutes with a binder and 'Scope' can
-- be reached inside without breaking what hiding @MkScope@ protects. Exported
-- for "Thena.Development.Cursor", whose 'Thena.Development.Cursor.TermStep'
-- carries scoped siblings of the field the focus went into.
substLevelsInScope :: [(LevelVar, Level)] -> Scope Core -> Scope Core
substLevelsInScope sub (MkScope b) = MkScope (substLevelsIn sub b)

-- | Every level meta the term mentions, without duplicates, in first-seen
-- order (MS3 phase 33).
--
-- The level analogue of 'freeVars', and it walks the same four places
-- 'substLevelsIn' writes to. 'Thena.Kernel' is the caller: a closed term whose
-- levels are all determined is what a global definition may be built from.
levelMetasIn :: Core -> [LevelVar]
levelMetasIn = nub . concatMap metasIn . go
  where
    go t = case t of
      Bound _                       -> []
      Primitive _                   -> []
      Free _                        -> []
      Global _ ls                   -> ls
      Universe l                    -> [l]
      Pi _ s (MkScope b)            -> go s ++ go b
      Lam _ s (MkScope b)           -> go s ++ go b
      App f a                       -> go f ++ go a
      Let _ v s (MkScope b)         -> go v ++ go s ++ go b
      Canonical _ ls as             -> ls ++ concatMap go as
      Eliminate _ ls ps m ms is tgt ->
        ls ++ concatMap go ps ++ go m ++ concatMap go ms
           ++ concatMap go is ++ go tgt
      Trusted c a b                 -> go c ++ go a ++ go b

-- | A counter value greater than every variable given.
--
-- **What a checker needs when it did not mint the variables it is walking
-- among.** 'fresh' guarantees uniqueness only within one monotonic run of the
-- counter; a checker handed terms that were built during an *earlier* run has
-- to start above them or it will mint a variable that is already in use, and
-- 'close' will capture it.
--
-- Returns the representation's @Int@ rather than a 'Var', so the constructor
-- stays hidden and the caller can only do with it the one thing it is for:
-- start counting.
beyond :: [Var] -> Int
beyond vs = 1 + maximum (-1 : [i | Var i <- vs])
