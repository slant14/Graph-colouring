-- | @udgc@: the front-end driver for the surface language. It parses a @.udgc@
-- program, type-checks it (the certified-reduction discipline), and elaborates
-- each @instance@ down to the device instance the simulator would consume —
-- stopping before any simulation.
--
-- Usage:
--
-- > udgc FILE.udgc          parse, type-check, and elaborate (default)
-- > udgc --check FILE.udgc  parse and type-check only (no elaboration)
module Main (main) where

import           Control.Monad      (forM_, unless, when)
import           System.Directory   (createDirectoryIfMissing)
import           System.Environment (getArgs, getProgName)
import           System.Exit        (exitFailure)

import           UDGColor.Ast
import           UDGColor.Elaborate
import           UDGColor.Emit
import           UDGColor.Parser
import           UDGColor.TypeCheck

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--check", fp]    -> run False fp
    ["--emit-sim", fp] -> emitSim fp "sim/instances"
    ["--emit-sim", fp, outdir] -> emitSim fp outdir
    [fp]               -> run True  fp
    _                  -> usage

usage :: IO ()
usage = do
  p <- getProgName
  putStrLn $ "usage: " ++ p ++ " [--check | --emit-sim [OUTDIR]] FILE.udgc"
  exitFailure

run :: Bool -> FilePath -> IO ()
run doElaborate fp = do
  src <- readFile fp
  putStrLn ("== parsing " ++ fp ++ " ==")
  case parseProgram fp src of
    Left e  -> do
      putStrLn "parse error:"
      print e
      exitFailure
    Right prog -> do
      putStrLn "parsed OK"
      let result = checkProgram prog
          ds     = crDiags result
          errs   = [ d | d <- ds, dSev d == Err ]

      putStrLn "\n== inferred types =="
      forM_ (crTypes result) $ \(nm, ty) ->
        putStrLn ("  " ++ pad 12 nm ++ " :: " ++ ppTy ty)

      putStrLn "\n== diagnostics =="
      if null ds
        then putStrLn "  (none)"
        else forM_ ds (putStrLn . ("  " ++) . ppDiag)

      when (doElaborate && null errs) $ do
        putStrLn "\n== elaboration (pre-simulation device instances) =="
        let outs = elaborateProgram (crEnv result) prog
        if null outs
          then putStrLn "  (no instances to elaborate)"
          else forM_ outs printElab

      putStrLn ""
      putStrLn (summary ds)
      unless (null errs) exitFailure

-- | Type-check, then write one @<instance>.sim.json@ per instance for the
-- neutral-atom simulator. Refuses to emit if the program has type errors.
emitSim :: FilePath -> FilePath -> IO ()
emitSim fp outdir = do
  src <- readFile fp
  case parseProgram fp src of
    Left e -> putStrLn "parse error:" >> print e >> exitFailure
    Right prog -> do
      let result = checkProgram prog
          errs   = [ d | d <- crDiags result, dSev d == Err ]
      if not (null errs)
        then do
          putStrLn "refusing to emit: program has type errors:"
          forM_ errs (putStrLn . ("  " ++) . ppDiag)
          exitFailure
        else do
          createDirectoryIfMissing True outdir
          let jsons = programInstanceJsons (crEnv result) prog
          if null jsons
            then putStrLn "no instances to emit"
            else forM_ jsons $ \(nm, ej) -> case ej of
              Left msg -> putStrLn ("  " ++ nm ++ ": not emitted — " ++ msg)
              Right j  -> do
                let path = outdir ++ "/" ++ nm ++ ".sim.json"
                writeFile path j
                putStrLn ("wrote " ++ path)

printElab :: Either (Name, String) DeviceInstance -> IO ()
printElab (Left (nm, msg)) =
  putStrLn ("  instance " ++ nm ++ ": not elaborated — " ++ msg)
printElab (Right di) = do
  putStrLn ("  instance " ++ diInstance di ++ "  (graph " ++ diGraph di ++ ")")
  putStrLn ("    path        : " ++ diPath di)
  putStrLn ("    input G     : n=" ++ show (diN di) ++ ", k=" ++ show (diK di))
  putStrLn ("    color-choice: |V'|=" ++ show (diChoiceV di)
              ++ " (=nk), |E'|=" ++ show (diChoiceE di))
  putStrLn ("    gadget A    : atoms=" ++ show (diAtoms di)
              ++ " (logical " ++ show (diLogical di)
              ++ " + gadget " ++ show (diGadgetAtoms di) ++ ")"
              ++ ", offset C=" ++ show (diOffsetC di))
  putStrLn ("    layout      : r*=" ++ show (round2 (diRadius di))
              ++ ", missing=" ++ show (diMissing di)
              ++ ", false=" ++ show (diFalse di))
  putStrLn ("    oracle      : " ++ show (diK di) ++ "-colorable = "
              ++ show (diColorable di))
  putStrLn ("    >> ready for simulation (not run)")

summary :: [Diag] -> String
summary ds =
  let ne = length [ () | d <- ds, dSev d == Err ]
      nw = length [ () | d <- ds, dSev d == Warn ]
  in if ne == 0
       then "OK — " ++ show nw ++ " warning(s), 0 errors"
       else show ne ++ " error(s), " ++ show nw ++ " warning(s)"

pad :: Int -> String -> String
pad n s = s ++ replicate (max 0 (n - length s)) ' '

round2 :: Double -> Double
round2 x = fromIntegral (round (x * 100) :: Int) / 100
