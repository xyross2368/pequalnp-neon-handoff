import PEqualNP.Defs.MetaComplexity

namespace NeonAudit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def treeFn (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) ||
  (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 7)

def zeroFn (x : Fin 8 → Bool) : Bool :=
  (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6) || (x 6 && x 7)

def neonCircuit : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [5, 12]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩

theorem neonSize : HasCircuitSize 8 treeFn 10 := by
  refine ⟨neonCircuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, neonCircuit]
  · intro x
    have heval : neonCircuit.eval (List.ofFn x) = ((((x 1 && (x 0 || x 2)) || (x 3 && (x 0 || x 4))) || (x 5 && (x 0 || x 6))) || (x 6 && x 7)) := by
      simp [neonCircuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD]
    rw [heval]
    simp only [treeFn, Bool.and_or_distrib_left]
    ac_rfl

def alternativeCircuit : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [16, 14]⟩], 17⟩

theorem alternativeSize : HasCircuitSize 8 treeFn 10 := by
  refine ⟨alternativeCircuit, ?_, by decide, ?_⟩
  · simp [FanInTwo, alternativeCircuit]
  · intro x
    have heval : alternativeCircuit.eval (List.ofFn x) = ((((x 0 && ((x 1 || x 3) || x 5)) || (x 1 && x 2)) || (x 3 && x 4)) || (x 6 && (x 5 || x 7))) := by
      simp [alternativeCircuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD]
    rw [heval]
    simp only [treeFn, Bool.and_or_distrib_left]
    ac_rfl

def zeroFolded : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [13, 11]⟩], 14⟩

theorem foldedSize : HasCircuitSize 8 zeroFn 7 := by
  refine ⟨zeroFolded, ?_, by decide, ?_⟩
  · simp [FanInTwo, zeroFolded]
  · intro x
    have heval : zeroFolded.eval (List.ofFn x) = ((((x 1 && x 2) || (x 3 && x 4)) || (x 5 && x 6)) || (x 6 && x 7)) := by
      simp [zeroFolded, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD]
    rw [heval]
    rfl

def zeroRefactored : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩

theorem refactoredSize : HasCircuitSize 8 zeroFn 6 := by
  refine ⟨zeroRefactored, ?_, by decide, ?_⟩
  · simp [FanInTwo, zeroRefactored]
  · intro x
    have heval : zeroRefactored.eval (List.ofFn x) = (((x 1 && x 2) || (x 3 && x 4)) || (x 6 && (x 5 || x 7))) := by
      simp [zeroRefactored, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD]
    rw [heval]
    simp only [zeroFn, Bool.and_or_distrib_left]
    ac_rfl

theorem zeroFnMatches (x : Fin 8 → Bool) :
    treeFn (Function.update x 0 false) = zeroFn x := by
  simp [treeFn, zeroFn, Function.update]

theorem exactGateCounts : neonCircuit.size = 10 ∧ alternativeCircuit.size = 10 ∧
    zeroFolded.size = 7 ∧ zeroRefactored.size = 6 := by
  decide

end NeonAudit
