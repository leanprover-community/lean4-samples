import Lake
open System Lake DSL

package Rubiks

def npmCmd : String :=
  if Platform.isWindows then "npm.cmd" else "npm"

target packageLock : FilePath := do
  let widgetDir := __dir__ / "widget"
  let packageFile ← inputFile <| widgetDir / "package.json"
  let packageLockFile := widgetDir / "package-lock.json"
  buildFileAfterDep packageLockFile packageFile fun _srcFile => do
    proc {
      cmd := npmCmd
      args := #["install"]
      cwd := some widgetDir
    }

def tsxTarget (pkg : Package) (tsxName : String) [Fact (pkg.name = _package.name)]
    : IndexBuildM (BuildJob FilePath) := do
  let widgetDir := __dir__ / "widget"
  let jsFile := widgetDir / "dist" / s!"{tsxName}.js"
  let deps : Array (BuildJob FilePath) := #[
    ← inputFile <| widgetDir / "src" / s!"{tsxName}.tsx",
    ← inputFile <| widgetDir / "rollup.config.js",
    ← inputFile <| widgetDir / "tsconfig.json",
    ← fetch (pkg.target ``packageLock)
  ]
  buildFileAfterDepArray jsFile deps fun _srcFile => do
    proc {
      cmd := npmCmd
      args := #["run", "build", "--", "--tsxName", tsxName]
      cwd := some widgetDir
    }

target rubiksJs (pkg : Package) : FilePath := tsxTarget pkg "rubiks"

-- TODO: https://github.com/leanprover/lake/issues/86#issuecomment-1185028364
@[defaultTarget]
lean_lib Rubiks
