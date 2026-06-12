-- | Tests for the surface language and its type checker. We parse each example
-- under @examples/@ and assert what the certified-reduction checker should say:
-- the well-typed programs have zero errors; the impossibility example is
-- rejected with a sigma>5 diagnostic; the error catalogue raises the expected
-- errors.tex codes plus a stage-ordering error.
module Main (main) where

import           Control.Monad (forM, unless)
import           Data.List     (isInfixOf)
import           System.Exit   (exitFailure)

import           UDGColor.Parser    (parseProgram)
import           UDGColor.TypeCheck

data Expect
  = NoErrors
  | HasErrSubstr String
  | HasCodesAnd [Int] String

data Case = Case
  { cName   :: String
  , cFile   :: FilePath
  , cExpect :: Expect
  }

cases :: [Case]
cases =
  [ Case "paper_example type-checks (0 errors)"
         "examples/paper_example.udgc" NoErrors
  , Case "triangle type-checks (0 errors)"
         "examples/triangle.udgc" NoErrors
  , Case "star supergraph rejected by sigma>5"
         "examples/supergraph_star.udgc" (HasErrSubstr "sigma")
  , Case "error catalogue raises #2,#3,#4,#5,#8,#9 and a stage-ordering error"
         "examples/errors.udgc" (HasCodesAnd [2, 3, 4, 5, 8, 9] "stage-ordering")
  ]

runCase :: Case -> IO (String, Bool, String)
runCase (Case nm fp expect) = do
  src <- readFile fp
  case parseProgram fp src of
    Left e  -> pure (nm, False, "parse error: " ++ show e)
    Right p -> do
      let ds    = crDiags (checkProgram p)
          errs  = [ d | d <- ds, dSev d == Err ]
          codes = [ c | d <- errs, Just c <- [dCode d] ]
          msgs  = unwords (map dMsg errs)
          (ok, detail) = case expect of
            NoErrors ->
              (null errs, show (length errs) ++ " errors")
            HasErrSubstr s ->
              (s `isInfixOf` msgs, "looked for substring " ++ show s)
            HasCodesAnd cs s ->
              ( all (`elem` codes) cs && s `isInfixOf` msgs
              , "codes=" ++ show codes ++ ", substr " ++ show s )
      pure (nm, ok, detail)

main :: IO ()
main = do
  results <- forM cases runCase
  let failures = [ (nm, d) | (nm, ok, d) <- results, not ok ]
  mapM_ (\(nm, ok, d) ->
            putStrLn ((if ok then "ok   " else "FAIL ") ++ nm ++ "  (" ++ d ++ ")"))
        results
  putStrLn (show (length cases - length failures) ++ "/" ++ show (length cases)
              ++ " language checks passed")
  unless (null failures) exitFailure
