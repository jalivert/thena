-- | The lexer's tagged regions (MS5 phase 60).
--
-- A region is @name\`…\`@. The lexer finds its extent and hands the contents
-- over as **raw text**, because an embedded language has its own lexical rules
-- and tokenising it here would impose Thena's
-- (@discussion\/the-five-languages.md@ §6.9). Nesting happens through an escape
-- and never through the fence, so raw text never contains another region.
module Thena.LexerTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Repl (describe)
import Thena.Syntax.Lexer (Located (..), Token (..), lexTokens)

tests :: TestTree
tests =
  testGroup
    "Thena.Syntax.Lexer — tagged regions"
    [ testGroup
        "the extent of a region"
        [ lexes "a plain region" "s`f x`" [TTagOpen "s", TRaw "f x", TTagClose]
        , lexes "an empty one emits no chunk" "s``" [TTagOpen "s", TTagClose]
        , lexes
            "the tag may be any identifier, including one above ASCII"
            "\120138`x`"
            [TTagOpen "\120138", TRaw "x", TTagClose]
        , lexes
            "a region sits in an ordinary token run"
            "fill s`x` ;"
            [TIdent "fill", TTagOpen "s", TRaw "x", TTagClose, TSemi]
        ]
    , testGroup
        "raw text is not tokenised — the point of the whole mechanism"
        [ lexes
            "reserved operator characters are just text"
            "s`λx. x`"
            [TTagOpen "s", TRaw "\955x. x", TTagClose]
        , lexes
            "and so are Thena's own keywords and brackets"
            "s`let (] ;`"
            [TTagOpen "s", TRaw "let (] ;", TTagClose]
        , lexes
            "a comment marker inside a region is text, not a comment"
            "s`-- not a comment`"
            [TTagOpen "s", TRaw "-- not a comment", TTagClose]
        ]
    , testGroup
        "the three backslash escapes"
        [ lexes "a literal backtick" "s`a\\`b`" [TTagOpen "s", TRaw "a`b", TTagClose]
        , lexes "a literal backslash" "s`a\\\\b`" [TTagOpen "s", TRaw "a\\b", TTagClose]
        , lexes "a literal dollar" "s`a\\$b`" [TTagOpen "s", TRaw "a$b", TTagClose]
        , lexes
            "a backslash before anything else is ordinary text"
            "s`a\\nb`"
            [TTagOpen "s", TRaw "a\\nb", TTagClose]
        ]
    , testGroup
        "escapes resume ordinary lexing"
        [ lexes
            "an escape splits the raw text around it"
            "s`a${x}b`"
            [ TTagOpen "s"
            , TRaw "a"
            , TEscapeOpen
            , TIdent "x"
            , TEscapeClose
            , TRaw "b"
            , TTagClose
            ]
        , lexes
            "an escape at the very start emits no leading chunk"
            "s`${x}`"
            [TTagOpen "s", TEscapeOpen, TIdent "x", TEscapeClose, TTagClose]
        , lexes
            "a brace written inside an escape does not close it"
            "s`${f {0} }`"
            [ TTagOpen "s"
            , TEscapeOpen
            , TIdent "f"
            , TLBrace
            , TNumber 0
            , TRBrace
            , TEscapeClose
            , TTagClose
            ]
        ]
    , testGroup
        "nesting goes through an escape and never through the fence"
        [ lexes
            "a region inside an escape inside a region"
            "a`x${ b`y` }z`"
            [ TTagOpen "a"
            , TRaw "x"
            , TEscapeOpen
            , TTagOpen "b"
            , TRaw "y"
            , TTagClose
            , TEscapeClose
            , TRaw "z"
            , TTagClose
            ]
        , lexes
            "and the inner region's own text stays raw"
            "a`${ b`let ;` }`"
            [ TTagOpen "a"
            , TEscapeOpen
            , TTagOpen "b"
            , TRaw "let ;"
            , TTagClose
            , TEscapeClose
            , TTagClose
            ]
        ]
    , testGroup
        "the angle-bracket alias for a surface region (MS5 phase 62)"
        [ lexes
            "it opens a region tagged surface"
            "\10216f x\10217"
            [TTagOpen "surface", TRaw "f x", TTagClose]
        , lexes
            "and its contents are raw, like any region's"
            "\10216let (] ;\10217"
            [TTagOpen "surface", TRaw "let (] ;", TTagClose]
        , lexes
            "a backtick inside it is ordinary text, because it is not the fence"
            "\10216a`b\10217"
            [TTagOpen "surface", TRaw "a`b", TTagClose]
        , lexes
            "a backslash escapes the closing bracket"
            "\10216a\\\10217b\10217"
            [TTagOpen "surface", TRaw "a\10217b", TTagClose]
        , lexes
            "it nests through an escape, like any region"
            "\10216x${ core`t` }\10217"
            [ TTagOpen "surface"
            , TRaw "x"
            , TEscapeOpen
            , TTagOpen "core"
            , TRaw "t"
            , TTagClose
            , TEscapeClose
            , TTagClose
            ]
        , fails "and one that is never closed" "\10216abc"
        ]
    , testGroup
        "failures"
        [ fails "a region that is never closed" "s`abc"
        , fails "an escape that is never closed" "s`a${x"
        , fails "a stray backtick outside any region" "f ` g"
        ]
    , testGroup
        -- **The single quote is free at the start of a token and nowhere else**
        -- (MS5 phase 64): it is an @$idchar@ and not an @$idstart@, so no
        -- identifier has ever been able to begin with one. That is what makes
        -- the literal purely additive, exactly as the string literal was.
        "character literals"
        [ lexes "one character" "'a'" [TChar 'a']
        , lexes "an escape" "'\\n'" [TChar '\n']
        , lexes "the quote itself" "'\\''" [TChar '\'']
        , lexes "a double quote needs no escape" "'\"'" [TChar '\"']
        , lexes "and a backslash does" "'\\\\'" [TChar '\\']
        , -- The corpus's own identifier, which must not have changed meaning:
          -- the prime is inside the name, not in front of it.
          lexes "a prime still continues an identifier" "t1'" [TIdent "t1'"]
        , lexes "even two of them" "t''" [TIdent "t''"]
        , -- Longest match settles this: @'a'@ is three characters and what
          -- follows is a separate token.
          lexes "a literal and a name after it" "'a' b" [TChar 'a', TIdent "b"]
        , fails "an empty literal" "''"
        , fails "one that is never closed" "'a"
        ]
    , testGroup
        -- Reserved characters with no token rule until MS5 phase 65: they
        -- could not appear in a name and could not be written either, so
        -- giving them tokens took nothing away.
        "brackets and the comma"
        [ lexes "a list" "[a, b]"
            [TLBracket, TIdent "a", TComma, TIdent "b", TRBracket]
        , lexes "an empty one" "[]" [TLBracket, TRBracket]
        , -- Longest match keeps corners working: @[|@ is one token and @[@ is
          -- another, and the two cannot be confused.
          lexes "and the corner alias still wins" "[| x |]"
            [TOpenQuote, TIdent "x", TCloseQuote]
        ]
    , testGroup
        "the backtick is reserved now"
        [ lexes
            "so it no longer continues an identifier"
            "ab`c`"
            [TTagOpen "ab", TRaw "c", TTagClose]
        ]
    , tokensReadBack
    ]
  where
    lexes what src want = testCase what $ case lexTokens src of
      Left e   -> assertFailure ("lex failed: " ++ show e)
      Right ts -> map tokenOf ts @?= want

    fails what src = testCase what $ case lexTokens src of
      Left _   -> pure ()
      Right ts -> assertFailure ("expected a lex error, got " ++ show (map tokenOf ts))

    tokenOf (Located _ t) = t

-- --------------------------------------------------------------------------
-- Every token the lexer produces reads back from how it is described (2026-09-13)
-- --------------------------------------------------------------------------

-- | **A message that says /unexpected X/ must be able to mean it.**
--
-- @Thena.Repl.describe@ turns a token into the text a syntax error names, and
-- it is what every @unexpected …@ line is built from. If it prints something
-- that does not lex back to the same token, the message points at a character
-- the user did not write — which this review has already met twice, once from
-- an invented @TSemi@ in an empty region and once from three arguments sharing
-- a name.
--
-- **The list is a hand-written mirror**, because no enumeration of 'Token'
-- exists; @describe@ itself is a total @case@, so @-Wall@ makes a new
-- constructor say how it is spelled, and this is what checks the spelling is
-- real. The five exclusions are stated rather than omitted.
tokensReadBack :: TestTree
tokensReadBack =
  testGroup
    "how a token is described is how it lexes"
    [ testCase "every token that stands on its own" $
        [ (t, describe t, lexTokens (describe t))
        | t <- standalone
        , fmap (map unlocated) (lexTokens (describe t)) /= Right [t]
        ] @?= []

      -- **Five are excluded and each for its own reason**, none of them a
      -- defect: @TDeclSep@ is inserted by the driver and never lexed, so it is
      -- described in prose rather than as a spelling; and the four region
      -- tokens only exist inside a scan that is stateful, so one of them alone
      -- is not a token stream.
    , testCase "and the five that cannot, described in prose or mid-scan" $
        map describe excluded
          @?= [ "the start of a declaration", "s`", "`", "raw", "${", "}" ]
    ]
  where
    unlocated (Located _ t) = t

    standalone =
      [ TLambda, TLanguage, TChar 'c'
      , TLBracket, TRBracket, TComma, TForall, TArrow
      , TLParen, TRParen, TColon, TLBrace, TRBrace, TSemi, TEquals, TQuery
      , TGuessed, TPending, TTurnstile, TEquate, TOpenQuote, TCloseQuote
      , TLet, TIn, TElim, TWhere, TData, TModule, TDo
      , TRule, TWhen, TThen, TNeck
      , TNumber 42, TString "hi", TUniverse 3, TUniverseOpen, TIdent "foo"
      , TDashes
      ]

    excluded =
      [ TDeclSep, TTagOpen "s", TTagClose, TRaw "raw", TEscapeOpen, TEscapeClose ]
