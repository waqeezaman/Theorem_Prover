{-# LANGUAGE OverloadedStrings #-}
module Parser where

import Text.Megaparsec
    ( (<|>),
      optional,
      parse,
      between,
      many,
      sepBy,
      Parsec,
      MonadParsec(eof),
      ParseErrorBundle )
import Text.Megaparsec.Char
    ( alphaNumChar,
      char,
      digitChar,
      lowerChar,
      space1,
      upperChar,
      string )
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Char (isUpper)
import Data.Void
import FOL ( Literal(..), Predicate(..), Term(..) ) 

type Parser = Parsec Void String

-- | Parser for a full TPTP File
parseTPTP :: String -> Either (ParseErrorBundle String Void) [[Literal]]
-- parseTPTP = parse (many (lexeme cnfParser) <* eof) ""
-- New version: spaceConsumer runs first to clear out the header comments
parseTPTP = parse (spaceConsumer *> many (lexeme cnfParser) <* eof) ""

-- | Parses a single 'cnf(name, role, (literals)).' line
cnfParser :: Parser [Literal]
cnfParser = do
    _ <- lexeme (string "cnf")
    _ <- lexeme (char '(')
    _ <- name -- ignore name
    _ <- lexeme (char ',')
    _ <- name -- ignore role
    _ <- lexeme (char ',')
    
    -- Use lexeme on these parentheses to handle ( lives(...) )
    literals <- between (lexeme (char '(')) (lexeme (char ')')) literalList 
                <|> literalList
    
    _ <- lexeme (string ").")
    return literals

literalList :: Parser [Literal]
literalList = literalParser `sepBy` lexeme (char '|')

literalParser :: Parser Literal
literalParser = lexeme $ do
    isNeg <- optional (char '~')
    spaceConsumer -- Add this to skip spaces after '~' if it exists
    p <- predicateParser
    case isNeg of
        Just _  -> return (Neg p)
        Nothing -> return (Pos p)

predicateParser :: Parser Predicate
predicateParser = do
    n <- lexeme name
    args <- between (lexeme (char '(')) (lexeme (char ')')) (termParser `sepBy` lexeme (char ',')) 
            <|> pure []
    return (R (n, args))

-- | Parses a Term: f(x) or X
termParser :: Parser Term
termParser = do
    n <- lexeme name
    args <- optional (between (lexeme (char '(')) (lexeme (char ')')) (termParser `sepBy` lexeme (char ',')))
    case args of
        Just ts -> return (Fn (n, ts))
        Nothing -> if isVariable n then return (Var n) else return (Fn (n, []))

-- | Helper: TPTP names (alphanumeric and underscores)
name :: Parser String
name = lexeme ((:) <$> (lowerChar <|> upperChar <|> digitChar) <*> many (alphaNumChar <|> char '_'))

isVariable :: String -> Bool
isVariable (c:_) = isUpper c
isVariable _ = False

-- | Lexer helpers
lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

spaceConsumer :: Parser ()
spaceConsumer = L.space space1 (L.skipLineComment "%") (L.skipBlockComment "/*" "*/")