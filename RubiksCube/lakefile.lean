import Lake
open System Lake DSL

def jsTarget (pkgDir : FilePath) : FileTarget :=
  let jsFile := pkgDir / "widget/dist/rubiks.js"
  let srcFiles := inputFileTarget <| pkgDir / "widget/src/rubiks.tsx"
  fileTargetWithDep jsFile srcFiles fun _srcFile => do
    proc {
      cmd := "npm"
      args := #["install"]
      cwd := some <| pkgDir / "widget"
    }
    proc {
      cmd := "npm"
      args := #["run", "build"]
      cwd := some <| pkgDir / "widget"
    }

package Rubiks (pkgDir) {
  extraDepTarget := jsTarget pkgDir |>.withoutInfo
  defaultFacet := PackageFacet.oleans
  dependencies := #[ ]
}
