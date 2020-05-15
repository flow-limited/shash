-- Based off a fantastic video by Tsoding: https://www.youtube.com/watch?v=N9RUqGYuGfw 

module Language.FLAC.Parser where

import Language.FLAC.Syntax
import Control.Applicative

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

principalValue :: Parser Prin
principalValue = principalTop <|> principalBottom <|> principalName <|> principalPVar <|> principalInteg 
  <|> principalConf <|> principalVoice <|> principalEye

principalTop :: Parser Prin
principalTop = (\_ -> Top) <$> stringP "Top"

principalBottom :: Parser Prin
principalBottom = (\_ -> Bot) <$> stringP "Bottom"

principalName :: Parser Prin 
principalName = Name <$> (stringP "Name \"" *> spanP (/= '"') <* charP '"')

principalPVar :: Parser Prin 
principalPVar = PVar <$> (stringP "PVar \"" *> spanP (/= '"') <* charP '"')

principalInteg :: Parser Prin
principalInteg = Integ <$> (stringP "Integ " *> principalValue)

principalConf :: Parser Prin
principalConf = Conf <$> (stringP "Conf " *> principalValue) 

principalVoice :: Parser Prin
principalVoice = Voice <$> (stringP "Voice " *> principalValue) 

principalEye :: Parser Prin
principalEye = Eye <$> (stringP "Eye " *> principalValue) 

principalConj :: Parser Prin
principalConj = undefined 

principalDisj :: Parser Prin
principalDisj = undefined 

-- Parses Types

-- typeValue :: Parser Type 
-- typeValue = typeUnit 

-- typeUnit :: Parser Type 
-- typeUnit = (\_ -> Unit) <$> stringP "Unit"

-- For setup debugging
parserMain :: IO ()
parserMain = do
    putStrLn "Hello Parser :)"
