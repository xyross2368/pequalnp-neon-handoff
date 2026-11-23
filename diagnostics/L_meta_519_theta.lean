import Std
import PEqualNP.Defs.MetaComplexity

namespace Meta519Diagnostic

abbrev Vertex := Fin 10

def vertices : List Vertex := List.finRange 10

-- Three internally disjoint paths of lengths 3, 4, and 4 between 0 and 1.
def edges : List (Vertex × Vertex) :=
  [(0, 2), (2, 3), (3, 1), (0, 4), (4, 5), (5, 6), (6, 1),
   (0, 7), (7, 8), (8, 9), (9, 1)]

def adjacent (u v : Vertex) : Bool :=
  edges.any fun (a, b) => (u == a && v == b) || (u == b && v == a)

def neighbors (u : Vertex) : List Vertex := vertices.filter (adjacent u)

-- Extend by unused vertices only. At most nine extensions fit on ten vertices.
def simplePaths : Nat → List Vertex → List (List Vertex)
  | 0, path => [path]
  | _ + 1, [] => []
  | fuel + 1, u :: rest =>
    let path := u :: rest
    path :: (neighbors u).flatMap fun v =>
      if path.contains v then [] else simplePaths fuel (v :: path)

def allPaths : List (List Vertex) := vertices.flatMap fun u => simplePaths 9 [u]

def cycleLengths : List Nat :=
  (List.range 11).filter fun length =>
    3 ≤ length && allPaths.any fun path =>
      path.length == length && adjacent (path.headD 0) (path.getLastD 0)

def maximumDegreeTwoRun : Nat :=
  let runs := allPaths.filter fun path => path.all fun u => (neighbors u).length == 2
  (runs.map List.length).foldl max 0

def vertexSubsets : List (List Vertex) :=
  vertices.foldr (fun v subsets => subsets ++ subsets.map (v :: ·)) [[]]

def minimumCoverSizeFor (graphEdges : List (Vertex × Vertex)) : Nat :=
  let covers := vertexSubsets.filter fun selected =>
    graphEdges.all fun (u, v) => selected.contains u || selected.contains v
  (covers.map List.length).foldl min 10

def minimumCoverSize : Nat := minimumCoverSizeFor edges

def withoutIncidentEdges (v : Vertex) : List (Vertex × Vertex) :=
  edges.filter fun (u, w) => u != v && w != v

set_option maxRecDepth 4096 in
theorem thetaDiagnostic :
    (vertices.map fun u => (neighbors u).length) = [3, 3, 2, 2, 2, 2, 2, 2, 2, 2] ∧
    cycleLengths = [7, 8] ∧ maximumDegreeTwoRun = 3 := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem thetaCover : minimumCoverSize = 5 := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaZeroRestrictions :
    (withoutIncidentEdges 0).length = 8 ∧ minimumCoverSizeFor (withoutIncidentEdges 0) = 4 ∧
    (withoutIncidentEdges 1).length = 8 ∧ minimumCoverSizeFor (withoutIncidentEdges 1) = 4 := by
  decide

private def matchingLeft (i : Fin 5) : Vertex :=
  ([0, 5, 2, 7, 9] : List Vertex).getD i.val 0

private def matchingRight (i : Fin 5) : Vertex :=
  ([4, 6, 3, 8, 1] : List Vertex).getD i.val 0

private def matchingIndex (v : Vertex) : Fin 5 :=
  ([0, 4, 2, 2, 0, 1, 1, 3, 3, 4] : List (Fin 5)).getD v.val 0

/-- The five disjoint matching edges give the cover lower bound in Finset form. -/
theorem thetaCoverLowerBound (T : Finset Vertex)
    (hcover : ∀ u v, adjacent u v = true → u ∈ T ∨ v ∈ T) : 5 ≤ T.card := by
  have edgesInGraph : ∀ i, adjacent (matchingLeft i) (matchingRight i) = true := by decide
  have leftIndex : ∀ i, matchingIndex (matchingLeft i) = i := by decide
  have rightIndex : ∀ i, matchingIndex (matchingRight i) = i := by decide
  let pick (i : Fin 5) : Vertex := if matchingLeft i ∈ T then matchingLeft i else matchingRight i
  have picked : ∀ i, pick i ∈ T := by
    intro i
    unfold pick
    split
    · assumption
    · exact (hcover _ _ (edgesInGraph i)).resolve_left (by assumption)
  have indexOfPick : ∀ i, matchingIndex (pick i) = i := by
    intro i
    unfold pick
    split
    · exact leftIndex i
    · exact rightIndex i
  let f (i : Fin 5) : {v // v ∈ T} := ⟨pick i, picked i⟩
  have hf : Function.Injective f := by
    intro i j h
    have equalPicked : pick i = pick j := congrArg Subtype.val h
    rw [← indexOfPick i, ← indexOfPick j, equalPicked]
  simpa using Fintype.card_le_of_injective f hf

def thetaCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [2, 4]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [0, 11]⟩,
    ⟨.or, [3, 6]⟩, ⟨.or, [13, 9]⟩, ⟨.and, [1, 14]⟩,
    ⟨.and, [2, 3]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [5, 17]⟩,
    ⟨.or, [7, 9]⟩, ⟨.and, [8, 19]⟩,
    ⟨.or, [12, 15]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [22, 18]⟩, ⟨.or, [23, 20]⟩], 24⟩

theorem thetaUpperBound :
    PEqualNP.MetaComplexity.HasCircuitSize 10
      (fun x => edges.any fun (u, v) => x u && x v) 15 := by
  refine ⟨thetaCircuit, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, thetaCircuit]
  · intro x
    have hEval : thetaCircuit.eval (List.ofFn x) =
        (((((x 0 && ((x 2 || x 4) || x 7)) || (x 1 && ((x 3 || x 6) || x 9))) ||
          (x 2 && x 3)) || (x 5 && (x 4 || x 6))) || (x 8 && (x 7 || x 9))) := by
      simp [thetaCircuit, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.GateOp.eval,
        List.getD_eq_getElem?_getD]
    rw [hEval]
    simp only [edges, List.any_cons, List.any_nil, Bool.and_or_distrib_left, Bool.or_false]
    ac_rfl

end Meta519Diagnostic
