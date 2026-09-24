-- | The Core display representation (MS7 phase 115a).
--
-- **The test is the whole argument for the design.** `redraw` below is what an
-- editor would be: it takes only a 'Display' — no session, no context, no
-- globals, no grammars — and produces text. If that text is what
-- 'Thena.Repl.renderCore' produces for the same term, then the display really
-- does carry everything the editor needs, and the seam in
-- @discussion\/editor-display.md@ §1 falls where that document says it does.
--
-- **It is a crossing and not a round trip.** `redraw` and `renderCore` are two
-- independent walks over two different structures; nothing here reads the other
-- one's table, so agreeing is evidence rather than tautology.
--
-- Notice what `redraw` has to work out for itself, because that is the seam
-- being tested: **where the parentheses go**, **whether a Π is an arrow** (only
-- whether the bound variable occurs, which it can see because occurrences carry
-- their binder), and **how to chain consecutive binders**. None of that crosses.
module Thena.Protocol.DisplayTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase)

import Thena.Core.Term (Core)
import Thena.Global.Env
  ( Constant (..)
  , Definition (..)
  , GlobalEnv (..)
  )
import Thena.Driver (Session (..))
import Thena.Engine (Machine (..))
import Thena.Protocol.Address (Address (..))
import Thena.Protocol.Display
  ( Binding (..)
  , Budget (..)
  , Display (..)
  , Shape (..)
  , displayCore
  )
import Thena.Repl (renderCore, startingSession)

tests :: TestTree
tests =
  testGroup
    "Thena.Protocol.Display"
    [ testCase "the display carries everything the printer needed" corpus
    , testCase "and the corpus really holds terms" notVacuous
    ]

-- | What an editor is: a function from a 'Display' to text, and nothing else.
redraw :: Display -> String
redraw = at Loose
  where
    at prec (Display here s) = case s of
      AVariable nm _ -> nm
      AGlobal g ls -> g <> levels ls
      AUniverse l -> l
      ALiteral t -> t
      ADangling i -> "\8249bound " <> show i <> "\8250"
      AnElision -> "\8230"
      AnApplication f a -> paren (prec > Spine) (at Spine f <> " " <> at Atom a)
      AnAbstraction b body -> paren (prec > Loose) ("\955 " <> chainLam [] here b body)
      AFunction b body
        -- **The editor works this out, and that is the seam being tested.** An
        -- arrow is a Π whose variable does not occur; an occurrence carries the
        -- address of its binder, and a binder binds at its own node — so this is
        -- answerable from the display alone.
        | occurs here body -> paren (prec > Loose) ("\8704 " <> chainPi [] here b body)
        | otherwise -> paren (prec > Loose) (at Spine (bindingType b) <> " -> " <> at Loose body)
      ALet b val body ->
        paren (prec > Loose) $
          "let " <> bindingName b
            <> " = " <> at Loose val
            <> " : " <> at Loose (bindingType b)
            <> " in " <> at Loose body
      AFormer g ls as -> spine (prec > Spine) (g <> levels ls) as
      -- **The slot groups are drawn as groups**, which the editor can do only
      -- because they arrive labelled rather than as one list of arguments.
      AnElimination d ls ps m ms is t ->
        paren (prec > Spine) $
          unwords
            [ "elim " <> d <> levels ls
            , bracket ps
            , at Atom m
            , bracket ms
            , bracket is
            , at Atom t
            ]

    bracket xs = "(" <> unwords (map (at Atom) xs) <> ")"

    spine p headText as
      | null as = headText
      | otherwise = paren p (unwords (headText : map (at Atom) as))

    levels [] = ""
    levels ls = " {" <> unwords ls <> "}"

    paren True t = "(" <> t <> ")"
    paren False t = t

    group b = "(" <> bindingName b <> " : " <> at Loose (bindingType b) <> ")"

    -- Consecutive binders are grouped. Presentation, therefore the editor's.
    chainLam acc _ b body = case displayShape body of
      AnAbstraction b' body' -> chainLam (group b : acc) (displayAt body) b' body'
      _ -> unwords (reverse (group b : acc)) <> " -> " <> at Loose body

    chainPi acc _ b body = case displayShape body of
      AnAbstraction {} -> stop
      AFunction b' body' | occurs (displayAt body) body' -> chainPi (group b : acc) (displayAt body) b' body'
      _ -> stop
      where
        stop = unwords (reverse (group b : acc)) <> " -> " <> at Loose body

data Prec = Loose | Spine | Atom
  deriving (Eq, Ord)

-- | Does anything under here point at that binder?
--
-- **The editor's own walk**, and it is possible only because an occurrence says
-- which binder it belongs to. Nothing about the term's internals crosses.
occurs :: Address -> Display -> Bool
occurs a (Display _ s) = case s of
  AVariable _ b -> b == Just a
  AnApplication f x -> occurs a f || occurs a x
  AFunction b body -> occurs a (bindingType b) || occurs a body
  AnAbstraction b body -> occurs a (bindingType b) || occurs a body
  ALet b val body -> occurs a (bindingType b) || occurs a val || occurs a body
  AFormer _ _ as -> any (occurs a) as
  AnElimination _ _ ps m ms is t ->
    any (occurs a) (ps <> [m] <> ms <> is <> [t])
  _ -> False

-- | Every term the prelude and the standard base leave in the environment.
termsOf :: GlobalEnv -> [Core]
termsOf gs =
  [definitionType d | (_, d) <- definitions gs]
    <> [definitionBody d | (_, d) <- definitions gs]
    <> [constantType c | (_, c) <- constants gs]

corpus :: IO ()
corpus = do
  ts <- termsOf . globals . sessionMachine . fst <$> startingSession
  case [e | Just e <- map mismatch ts] of
    [] -> pure ()
    e : _ -> assertFailure e

mismatch :: Core -> Maybe String
mismatch t
  | shown == drawn = Nothing
  | otherwise = Just ("printed: " <> shown <> "\n  drawn:   " <> drawn)
  where
    shown = renderCore [] 0 [] t
    drawn = redraw (displayCore (Budget 200) [] [] 0 (Address []) t)

-- | A green test over an empty corpus would prove nothing.
notVacuous :: IO ()
notVacuous = do
  n <- length . termsOf . globals . sessionMachine . fst <$> startingSession
  if n >= 50 then pure () else assertFailure ("only " <> show n <> " terms in the corpus")
