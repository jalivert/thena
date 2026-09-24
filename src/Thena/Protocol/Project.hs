-- | A stored project (phase 112b).
--
-- **What a project is: an ordered list of modules.** The order is not
-- presentation — a module's globals are in scope for the next one loaded in the
-- same session, and the prelude's order is load-bearing (@CLAUDE.md@). A set
-- would lose the only thing that makes a project reloadable.
--
-- **Stored as written, not resolved** (his decision, 2026-09-24): a tactic that
-- later becomes a rule keeps working under its own name, and JSON and text stay
-- two spellings of one artifact rather than two artifacts. See
-- @discussion\/editor-protocol.md@ §4 A2.
--
-- **Nothing here touches a disk.** §12 invariant 4 keeps IO at the frontend, so
-- this module turns a project into named contents and back, and whoever has the
-- file system writes them. That also makes the round trip testable without one.
module Thena.Protocol.Project
  ( StoredModule (..)
  , Project (..)
  , ProjectError (..)
    -- * Storage
  , manifestName
  , storeProject
  , readStoredProject
    -- * Using one
  , loadInto
  ) where

import Thena.Driver
  ( Item
  , Response
  , Session
  , loadProofItems
  , loadRuleDecls
  )
import Thena.Instral.Concrete (RawDecl)
import Thena.Protocol.Codec (CodecError, FromJson (..), ToJson (..), noSuchCase, tagged, untagged)
import Thena.Protocol.Concrete ()
import Thena.Protocol.Json (Json, JsonError, decode, encode)

-- | One module of a project, as written.
--
-- The two kinds are the two kinds of file the system already loads, and they
-- carry exactly what their readers produce: a surface module is a name and its
-- items, a rule file is a name, a description and its declarations.
data StoredModule
  = StoredSurface String [Item]
  | StoredRules String (Maybe String) [RawDecl]
  deriving (Eq, Show)

-- | A project: a name, and its modules **in load order**.
data Project = Project
  { projectName    :: String
  , projectModules :: [StoredModule]
  }
  deriving (Eq, Show)

-- | Why a stored project would not read.
--
-- Structured, never a message (§12), and every one that concerns a module names
-- the file, because a project is many files and "it did not parse" is useless
-- without saying which.
data ProjectError
  = ManifestMissing
  | ManifestUnreadable JsonError
  | ManifestMalformed CodecError
  | ModuleMissing FilePath
  | ModuleUnreadable FilePath JsonError
  | ModuleMalformed FilePath CodecError
  deriving (Eq, Show)

-- | The manifest's file name, which is the one name a reader has to know.
manifestName :: FilePath
manifestName = "project.json"

-- --------------------------------------------------------------------------
-- Storage
-- --------------------------------------------------------------------------

-- | The files a project is, manifest first.
--
-- **One file per module, named by position.** The name is @000.json@, @001.json@
-- and so on rather than anything derived from the module's own name: an
-- identifier may contain almost anything (§2.6), including characters no file
-- system will take, and a project is ordered anyway — so position is the honest
-- key and it cannot collide. The module's real name is inside its file.
storeProject :: Project -> [(FilePath, String)]
storeProject p =
  (manifestName, encode (manifest p))
    : [(moduleFile i, encode (toJson m)) | (i, m) <- zip [0 :: Int ..] (projectModules p)]

moduleFile :: Int -> FilePath
moduleFile i = pad (show i) <> ".json"
  where
    pad s = replicate (max 0 (3 - length s)) '0' <> s

-- | The manifest: the project's name, and its module files in load order.
manifest :: Project -> Json
manifest p =
  tagged
    "Project"
    [ toJson (projectName p)
    , toJson [moduleFile i | i <- take (length (projectModules p)) [0 ..]]
    ]

-- | Read a project back from its files.
--
-- Takes everything that was found, in any order, and looks up what the manifest
-- asks for — so a stray file is ignored and a missing one is named.
readStoredProject :: [(FilePath, String)] -> Either ProjectError Project
readStoredProject files = do
  src <- maybe (Left ManifestMissing) Right (lookup manifestName files)
  j <- mapLeft ManifestUnreadable (decode src)
  (nm, names) <- mapLeft ManifestMalformed (readManifest j)
  ms <- traverse readModule names
  Right (Project nm ms)
  where
    readModule f = do
      src <- maybe (Left (ModuleMissing f)) Right (lookup f files)
      j <- mapLeft (ModuleUnreadable f) (decode src)
      mapLeft (ModuleMalformed f) (fromJson j)

readManifest :: Json -> Either CodecError (String, [FilePath])
readManifest v =
  untagged "Project" v >>= \case
    ("Project", [a, b]) -> (,) <$> fromJson a <*> fromJson b
    (t, as) -> noSuchCase "Project" t as

mapLeft :: (e -> f) -> Either e a -> Either f a
mapLeft f = either (Left . f) Right

instance ToJson StoredModule where
  toJson m = case m of
    StoredSurface nm items    -> tagged "StoredSurface" [toJson nm, toJson items]
    StoredRules nm desc decls -> tagged "StoredRules" [toJson nm, toJson desc, toJson decls]

instance FromJson StoredModule where
  fromJson v =
    untagged "StoredModule" v >>= \case
      ("StoredSurface", [a, b])  -> StoredSurface <$> fromJson a <*> fromJson b
      ("StoredRules", [a, b, c]) -> StoredRules <$> fromJson a <*> fromJson b <*> fromJson c
      (t, as) -> noSuchCase "StoredModule" t as

-- --------------------------------------------------------------------------
-- Using one
-- --------------------------------------------------------------------------

-- | Load a project into a session, in order.
--
-- **The rule modules go in together and first**, which is not this module's
-- choice: a rule load /replaces/ the whole list (his ruling of 2026-08-25, and
-- @loadRuleBases@' comment), so they are one act rather than several, and
-- 'Thena.Repl.startingSession' already establishes that a session takes its
-- bases before its surface modules. Surface modules then load one at a time, in
-- the order the project gives, because that order is what puts each module's
-- globals in scope for the next.
--
-- Every response is returned rather than only the last: a project is many loads
-- and the caller decides which of them are worth showing.
loadInto :: Session -> Project -> (Session, [Response])
loadInto s0 p = (sn, rs <> rs')
  where
    (s1, rs) = case [(label i, nm, desc, ds) | (i, StoredRules nm desc ds) <- zip [0 :: Int ..] (projectModules p)] of
      []  -> (s0, [])
      bss -> let (s', r) = loadRuleDecls s0 bss in (s', [r])

    (sn, rs') = foldl step (s1, []) [(nm, items) | StoredSurface nm items <- projectModules p]

    step (s, acc) (nm, items) = let (s', r) = loadProofItems s nm items in (s', acc <> [r])

    -- The path a base reports is the file it came from, which for a stored
    -- project is its module file.
    label i = moduleFile i
