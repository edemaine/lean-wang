/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraphLocalCoverageGeometry
import LeanWang.Robinson.Closed104.RedShadeGraphSearch
import LeanWang.Robinson.Closed104.RedShadeGraphStaticCertificate

/-!
# Static red-graph certificate generator

This executable is not imported by the proof. It records the
`RedShadeGraphSearch` computation used to produce
`RedShadeGraphStaticCertificateData.lean`; `RedShadeGraphSearchSoundness`
contains the reference proof of that search.  The generated predecessor
forests are checked independently by `RedShadeGraphStaticCertificate`.
-/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphStaticCertificateGenerator

open RedShadeGraph RedShadeGraphCertificate RedShadeGraphLocalCoverage
  RedShadeGraphRefinement RedShadeGraphSearch
  RedShadeGraphStaticCertificate

def findIndex? {α : Type} (values : Array α) (accept : α → Bool) : Option Nat :=
  (List.range values.size).find? fun index =>
    match values[index]? with
    | some value => accept value
    | none => false

def instructionFor (sources : List Port) (seen : Array Node)
    (node : Node) : Instruction :=
  match node.reverseMoves with
  | [] =>
      match sources.findIdx? (· = node.origin) with
      | some source => .root source
      | none => .root sources.length
  | move :: _ =>
      let previousParity := Bool.xor node.parity move.parity
      match findIndex? seen fun previous =>
          decide (previous.origin = node.origin) &&
            decide (previous.current = move.first) &&
            decide (previous.parity = previousParity) with
      | some previous => .step previous move
      | none => .root sources.length

def instructionsFor (sources : List Port) (nodes : List Node) :
    List Instruction :=
  ((nodes.reverse).foldl (fun (seen, instructions) node =>
    (seen.push node, instructions.push (instructionFor sources seen node)))
    (#[], #[])).2.toList

def localNodes (parent : Index) : List Node :=
  exploreFast (fineGrid parent) 8 8 1000 (sources parent)

def connectorNodes (parent : Index) (side : ExitSide) (offset : Nat) :
    List Node :=
  exploreFast (fineGrid parent) 8 8 1000 [internalPort side offset]

def oddIndexGrid : Nat → Nat → Index :=
  RedCycles.iterateRefine 4 (fun _ _ => (0 : Index))

def oddCyclePorts : List Port :=
  [⟨5, 5, .east⟩, ⟨12, 5, .west⟩,
    ⟨12, 12, .west⟩, ⟨5, 12, .east⟩]

def oddNodes : List Node :=
  exploreFast oddIndexGrid 16 16 4000 oddCyclePorts

def allLocalForests : List (List Instruction) :=
  (List.finRange 104).map fun parent =>
    instructionsFor (sources parent) (localNodes parent)

def localForests : List (List Instruction) :=
  allLocalForests.eraseDups

def localForestIndices : List Nat :=
  allLocalForests.map fun forest =>
    (localForests.findIdx? (forest = ·)).getD localForests.length

def allConnectorBundles : List (List (List Instruction)) :=
  (List.finRange 104).map fun parent =>
    exitSides.flatMap fun side =>
      (List.range 2).map fun offset =>
        let source := internalPort side offset
        instructionsFor [source]
          (RedShadeGraphStaticCertificateGenerator.connectorNodes
            parent side offset)

def connectorBundles : List (List (List Instruction)) :=
  allConnectorBundles.eraseDups

def connectorBundleIndices : List Nat :=
  allConnectorBundles.map fun bundle =>
    (connectorBundles.findIdx? (bundle = ·)).getD connectorBundles.length

def baseForest : List Instruction :=
  instructionsFor [cycleSource]
    (exploreFast (fineGrid 0) 8 8 1000 [cycleSource])

def oddBaseForest : List Instruction :=
  instructionsFor oddCyclePorts oddNodes

def kindName : Kind → String
  | .horizontalMatch => "horizontalMatch"
  | .verticalMatch => "verticalMatch"
  | .horizontal => "horizontal"
  | .vertical => "vertical"
  | .westNorth => "westNorth"
  | .westSouth => "westSouth"
  | .eastNorth => "eastNorth"
  | .eastSouth => "eastSouth"
  | .crossing => "crossing"

def renderInstruction : Instruction → String
  | .root source => s!".root {source}"
  | .step previous move =>
      s!".step {previous} ⟨{move.x}, {move.y}, .{kindName move.kind}, {move.reverse}⟩"

def renderInstructions (instructions : List Instruction)
    (indent : String) : String :=
  if instructions.isEmpty then "[]"
  else
    "[\n" ++ String.intercalate ",\n"
      (instructions.map fun instruction =>
        indent ++ "  " ++ renderInstruction instruction) ++
      "\n" ++ indent ++ "]"

def renderForests (forests : List (List Instruction)) : String :=
  if forests.isEmpty then "[]"
  else
    "[\n" ++ String.intercalate ",\n"
      (forests.map fun forest => "  " ++ renderInstructions forest "  ") ++
      "\n]"

def renderForestBundles (bundles : List (List (List Instruction))) : String :=
  if bundles.isEmpty then "[]"
  else
    "[\n" ++ String.intercalate ",\n"
      (bundles.map fun bundle => "  " ++
        (renderForests bundle).replace "\n" "\n  ") ++
      "\n]"

def renderNats (values : List Nat) : String :=
  let lineCount := (values.length + 15) / 16
  let lines := (List.range lineCount).map fun line =>
    String.intercalate ", "
      (((values.drop (16 * line)).take 16).map toString)
  "[\n  " ++ String.intercalate ",\n  " lines ++ "\n]"

def output : String :=
  "/-\n" ++
  "Copyright (c) 2026 lean-wang contributors. All rights reserved.\n" ++
  "Released under Apache 2.0 license as described in the file LICENSE.\n" ++
  "Authors: Erik Demaine, Stefan Langerman, GPT 5.5\n" ++
  "-/\n" ++
  "import LeanWang.Robinson.Closed104.RedShadeGraphStaticCertificate\n\n" ++
  "/-!\n" ++
  "Generated static predecessor forests for finite red-graph paths.  Regenerate\n" ++
  "this file with `RedShadeGraphStaticCertificateGenerator`; the active proof\n" ++
  "checks these instructions without importing the generator or graph search.\n" ++
  "-/\n\n" ++
  "namespace LeanWang\nnamespace OllingerRobinson\n" ++
  "namespace Figure13Layers\nnamespace Closed104\n" ++
  "namespace RedShadeGraphStaticCertificateData\n\n" ++
  "open RedShadeGraphStaticCertificate\n\n" ++
  "def localForests : List (List Instruction) :=\n" ++
    renderForests localForests ++ "\n\n" ++
  "def localForestIndices : List Nat :=\n" ++
    renderNats localForestIndices ++ "\n\n" ++
  "def connectorBundles : List (List (List Instruction)) :=\n" ++
    renderForestBundles connectorBundles ++ "\n\n" ++
  "def connectorBundleIndices : List Nat :=\n" ++
    renderNats connectorBundleIndices ++ "\n\n" ++
  "def baseForest : List Instruction :=\n" ++
    renderInstructions baseForest "" ++ "\n\n" ++
  "def oddBaseForest : List Instruction :=\n" ++
    renderInstructions oddBaseForest "" ++ "\n\n" ++
  "end RedShadeGraphStaticCertificateData\nend Closed104\n" ++
  "end Figure13Layers\nend OllingerRobinson\nend LeanWang\n"

end RedShadeGraphStaticCertificateGenerator
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang

open LeanWang.OllingerRobinson.Figure13Layers.Closed104

def main : IO Unit :=
  IO.FS.writeFile
    "LeanWang/Robinson/Closed104/RedShadeGraphStaticCertificateData.lean"
    RedShadeGraphStaticCertificateGenerator.output
