------------------------------------------------------------------------------
--- This library defines I/O actions to read and write
--- type-annotated FlatCurry programs.
---
--- @author Michael Hanus
--- @version February 2022
------------------------------------------------------------------------------

module FlatCurry.TypeAnnotated.Files where

import Data.List           ( isSuffixOf )
import Data.Maybe          ( isNothing )
import System.FilePath     ( takeFileName, (</>), (<.>) )
import System.Directory    ( doesFileExist, getFileWithSuffix )
import System.FrontendExec ( FrontendParams, FrontendTarget (..), defaultParams
                           , setQuiet
                           , callFrontend, callFrontendWithParams )
import System.CurryPath    ( lookupModuleSourceInLoadPath, getLoadPathForModule
                           , inCurrySubdir, stripCurrySuffix )
import ReadShowTerm        ( readUnqualifiedTerm, showTerm )
import FlatCurry.Annotated.Types

--- Transforms a name of a Curry program (with or without suffix ".curry"
--- or ".lcurry") into the name of the file containing the
--- corresponding type-annotated FlatCurry program.
typeAnnotatedFlatCurryFileName :: String -> String
typeAnnotatedFlatCurryFileName prog =
  inCurrySubdir (stripCurrySuffix prog) <.> "afcy"

--- Gets the standard type-annotated FlatCurry file location
--- for a given Curry module name.
--- The Curry source program must exist in the Curry load path,
--- otherwise an error is raised.
typeAnnotatedFlatCurryFilePath :: String -> IO String
typeAnnotatedFlatCurryFilePath mname = do
  mbsrc <- lookupModuleSourceInLoadPath mname
  case mbsrc of
    Nothing      -> error $ "Curry source file for module '" ++ mname ++
                            "' not found!"
    Just (dir,_) -> return (typeAnnotatedFlatCurryFileName (dir </> mname))

--- I/O action which parses a Curry program and returns the corresponding
--- type-annotated FlatCurry program.
--- The argument is the module path (without suffix ".curry"
--- or ".lcurry") and the result is a type-annotated FlatCurry term
--- representing this program.
readTypeAnnotatedFlatCurry :: String -> IO (AProg TypeExpr)
readTypeAnnotatedFlatCurry progname =
   readTypeAnnotatedFlatCurryWithParseOptions progname
     (setQuiet True defaultParams)

--- I/O action which parses a Curry program
--- with respect to some parser options and returns the
--- corresponding FlatCurry program.
--- This I/O action is used by `readTypeAnnotatedFlatCurry`.
--- @param progfile - the program file name (without suffix ".curry")
--- @param options - parameters passed to the front end
readTypeAnnotatedFlatCurryWithParseOptions :: String -> FrontendParams
                                           -> IO (AProg TypeExpr)
readTypeAnnotatedFlatCurryWithParseOptions progname options = do
  mbsrc <- lookupModuleSourceInLoadPath progname
  case mbsrc of
    Nothing -> do -- no source file, try to find FlatCurry file in load path:
      loadpath <- getLoadPathForModule progname
      filename <- getFileWithSuffix
                    (typeAnnotatedFlatCurryFileName (takeFileName progname))
                    [""] loadpath
      readTypeAnnotatedFlatCurryFile filename
    Just (dir,_) -> do
      callFrontendWithParams TAFCY options progname
      readTypeAnnotatedFlatCurryFile
        (typeAnnotatedFlatCurryFileName (dir </> takeFileName progname))

--- Reads a type-annotated FlatCurry program from a file in `.afcy` format
--- where the file name is provided as the argument.
readTypeAnnotatedFlatCurryFile :: String -> IO (AProg TypeExpr)
readTypeAnnotatedFlatCurryFile filename = do
  filecontents <- readTypeAnnotatedFlatCurryFileRaw filename
  -- ...with generated Read class instances (slow!):
  --return (read filecontents)
  -- ...with built-in generic read operation (faster):
  return (readUnqualifiedTerm ["FlatCurry.Annotated.Types", "FlatCurry.Types",
                               "Prelude"]
                              filecontents)
 where
  readTypeAnnotatedFlatCurryFileRaw fname = do
    exafcy <- doesFileExist fname
    if exafcy
      then readFile fname
      else error $ "EXISTENCE ERROR: Typed FlatCurry file '" ++
                   fname ++ "' does not exist"

--- Writes a type-annotated FlatCurry program into a file in `.afcy` format.
--- The file is written in the standard location for intermediate files,
--- i.e., in the 'typeAnnotatedFlatCurryFileName' relative to the directory
--- of the Curry source program (which must exist!).
writeTypeAnnotatedFlatCurry :: AProg TypeExpr -> IO ()
writeTypeAnnotatedFlatCurry prog@(AProg mname _ _ _ _) = do
  fname <- typeAnnotatedFlatCurryFilePath mname
  writeTypeAnnotatedFlatCurryFile fname prog

--- Writes a type-annotated FlatCurry program into a file in ".afcy" format.
--- The first argument must be the name of the target file
--- (with suffix `.afcy`).
writeTypeAnnotatedFlatCurryFile :: String -> AProg TypeExpr -> IO ()
writeTypeAnnotatedFlatCurryFile file prog = writeFile file (showTerm prog)

