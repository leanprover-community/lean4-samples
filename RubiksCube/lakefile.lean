import Lake
open System Lake DSL

package Rubiks

def npmCmd : String :=
  if Platform.isWindows then "npm.cmd" else "npm"

target packageLock : FilePath :=
  let packageFile := inputFileTarget <| __dir__ / s!"widget/package.json"
  let packageLockFile := __dir__ / s!"widget/package-lock.json"
  fileTargetWithDep packageLockFile packageFile fun _srcFile => do
    proc {
      cmd := npmCmd
      args := #["install"]
      cwd := some <| __dir__ / "widget"
    }

def tsxTarget (tsxName : String) : FileTarget :=
  let jsFile := __dir__ / s!"widget/dist/{tsxName}.js"
  let deps : Array FileTarget := #[
    inputFileTarget <| __dir__ / s!"widget/src/{tsxName}.tsx",
    inputFileTarget <| __dir__ / s!"widget/rollup.config.js",
    inputFileTarget <| __dir__ / s!"widget/tsconfig.json",
    packageLock.target
  ]
  fileTargetWithDepArray jsFile deps fun _srcFile => do
    proc {
      cmd := npmCmd
      args := #["run", "build", "--", "--tsxName", tsxName]
      cwd := some <| __dir__ / "widget"
    }

target rubiksJs : FilePath := tsxTarget "rubiks"

-- TODO: https://github.com/leanprover/lake/issues/86#issuecomment-1185028364
@[defaultTarget]
lean_lib Rubiks
