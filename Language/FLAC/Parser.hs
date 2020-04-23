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

-- Parses Principals
-- In GHCI: runFLACParser principalValue "inputString"
    -- runFLACParser principalValue "Top" (works?)
    -- runFLACParser principalValue "Bottom" (works?)

principalValue :: Parser Principal
principalValue = principalTop <|> principalBottom

principalTop :: Parser Principal
principalTop = (\_ -> Top) <$> stringP "Top"

principalBottom :: Parser Principal
principalBottom = (\_ -> Bottom) <$> stringP "Bottom"


-- For setup debugging
parserMain :: IO ()
parserMain = do
    putStrLn "Hello Parser :)"
