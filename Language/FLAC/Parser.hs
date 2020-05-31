-- Based off a fantastic video by Tsoding: https://www.youtube.com/watch?v=N9RUqGYuGfw 

module Language.FLAC.Parser where

import Language.FLAC.Syntax.Runtime
import Control.Applicative
import Data.Text (pack)

-- Parser newtype 
newtype Parser a = Parser
  { runFLACParser :: String -> Maybe (String, a)}

instance Functor Parser where
  fmap f (Parser p) =
    Parser $ \input -> do
      (input', x) <- p input
      Just (input', f x)

instance Applicative Parser where
  pure x = Parser $ \input -> Just (input, x)
  (Parser p1) <*> (Parser p2) =
    Parser $ \input -> do
      (input', f) <- p1 input
      (input'', a) <- p2 input'
      Just (input'', f a)

instance Alternative Parser where
  empty = Parser $ \_ -> Nothing
  (Parser p1) <|> (Parser p2) =
      Parser $ \input -> p1 input <|> p2 input

-- Parses a single character 
charP :: Char -> Parser Char
charP x = Parser f
  where
    f (y:ys)
      | y == x = Just (ys, x)
      | otherwise = Nothing
    f [] = Nothing

-- Parses a sequence of characters 
stringP :: String -> Parser String
stringP = sequenceA . map charP

-- Parses characters that meet a condition
spanP :: (Char -> Bool) -> Parser String
spanP f =
  Parser $ \input ->
    let (token, rest) = span f input
     in Just (rest, token)

-- Parses Principals
-- In GHCI: runFLACParser principalValue "inputString"
    -- runFLACParser principalValue "Top" 
    -- runFLACParser principalValue "Bottom" 
    -- runFLACParser principalValue "Name \"name1\"" 
-- ToDo: deal with whitespace
-- Use many in GHCI: :m +Control.Applicative 

principalValue :: Parser Prin
principalValue = principalTop <|> principalBottom <|> principalName <|> principalPVar <|> principalInteg 
  <|> principalConf <|> principalVoice <|> principalEye <|> principalConj <|> principalDisj

principalTop :: Parser Prin
principalTop = (\_ -> Top) <$> stringP "Top"

principalBottom :: Parser Prin
principalBottom = (\_ -> Bot) <$> stringP "Bottom"

principalName :: Parser Prin 
principalName = Raw <$> fmap pack (stringP "Name \"" *> spanP (/= '"') <* charP '"')

principalPVar :: Parser Prin 
principalPVar = PVar <$> fmap pack (stringP "PVar \"" *> spanP (/= '"') <* charP '"')

principalInteg :: Parser Prin
principalInteg = Integ <$> (stringP "Integ " *> principalValue)

principalConf :: Parser Prin
principalConf = Conf <$> (stringP "Conf " *> principalValue) 

principalVoice :: Parser Prin
principalVoice = Voice <$> (stringP "Voice " *> principalValue) 

principalEye :: Parser Prin
principalEye = Eye <$> (stringP "Eye " *> principalValue) 

principalConj :: Parser Prin
principalConj = (\_ p1 _ p2 -> Conj p1 p2) <$> stringP "Conj " <*> principalValue <*> charP ' ' <*> principalValue

principalDisj :: Parser Prin
principalDisj = (\_ p1 _ p2 -> Disj p1 p2) <$> stringP "Disj " <*> principalValue <*> charP ' ' <*> principalValue


-- Parses Types

-- typeValue :: Parser Type 
-- typeValue = typeUnit 

-- typeUnit :: Parser Type 
-- typeUnit = (\_ -> Unit) <$> stringP "Unit"

-- For setup debugging
parserMain :: IO ()
parserMain = do
    putStrLn "Hello Parser :)"
