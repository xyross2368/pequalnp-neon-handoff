import Mathlib.Computability.Language
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Computability.TuringMachine.Computable

/-!
# Boolean circuits and nonuniform classes

The ruling behind this file is `CircuitLowerBounds/README.md`. The pinned Mathlib has no
Boolean circuits, so they are defined here, as straight-line programs.

A circuit on an input string `x` has wires numbered from `0`. Wires `0` to `x.length - 1`
carry the input bits. Each gate, in order, adds one wire: its operation applied to the values
of the wires it names. A gate can only see wires that exist when it is evaluated (inputs and
earlier gates), so a circuit is acyclic by construction. A wire index that does not exist
yet reads `false`. The value of the circuit is the value of its output wire.

Gates have unbounded fan-in. A class that wants fan-in two says so (`SIZE`).
-/

namespace PEqualNP.CircuitLowerBounds

/-- The operation of a gate. -/
inductive GateOp where
  /-- AND of all inputs (`true` on no inputs). -/
  | and
  /-- OR of all inputs (`false` on no inputs). -/
  | or
  /-- NOT of the first input. Further inputs are ignored; on no inputs it is `true`. -/
  | not
  /-- MOD `m`: `true` exactly when the number of true inputs is divisible by `m`. -/
  | mod (m : ℕ)
  /-- MAJORITY: `true` exactly when at least half of the inputs are true. -/
  | maj

/-- The value of a gate operation on the list of its input values. -/
def GateOp.eval : GateOp → List Bool → Bool
  | GateOp.and, l => l.all id
  | GateOp.or, l => l.any id
  | GateOp.not, l => !(l.headD false)
  | GateOp.mod m, l => decide (l.count true % m = 0)
  | GateOp.maj, l => decide (l.length ≤ 2 * l.count true)

/-- A gate: an operation and the wires it reads, in order, repetitions allowed. -/
structure Gate where
  /-- The operation. -/
  op : GateOp
  /-- The indices of the wires it reads. -/
  inputs : List ℕ

/-- A circuit: its gates in evaluation order and the index of its output wire. -/
structure Circuit where
  /-- The gates. Gate number `j` (from `0`) produces wire `(input length) + j`. -/
  gates : List Gate
  /-- The index of the output wire. -/
  output : ℕ

/-- The values of all wires of `C` on input `x`: the bits of `x`, then one value per gate. -/
def Circuit.wires (C : Circuit) (x : List Bool) : List Bool :=
  C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

/-- The value of `C` on input `x`: the value of its output wire (`false` if there is none). -/
def Circuit.eval (C : Circuit) (x : List Bool) : Bool :=
  (C.wires x).getD C.output false

/-- The size of a circuit: its number of gates. Input wires are not counted. -/
def Circuit.size (C : Circuit) : ℕ :=
  C.gates.length

/-- The depth of every wire of `C` on `n` inputs: an input wire has depth `0`, and a gate has
depth one more than the largest depth among the wires it reads (a wire that does not exist
counts as depth `0`). Every gate counts, NOT gates included. -/
def Circuit.depths (C : Circuit) (n : ℕ) : List ℕ :=
  C.gates.foldl (fun d g => d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1])
    (List.replicate n 0)

/-- The depth of `C` on `n` inputs: the depth of its output wire. -/
def Circuit.depth (C : Circuit) (n : ℕ) : ℕ :=
  (C.depths n).getD C.output 0

/-- `C` decides `L` on inputs of length `n`. -/
def Circuit.Decides (C : Circuit) (L : Language Bool) (n : ℕ) : Prop :=
  ∀ x : List Bool, x.length = n → (C.eval x = true ↔ x ∈ L)

/-- SIZE(s): the languages decided, at every input length `n`, by a circuit of AND, OR and NOT
gates of fan-in at most two with at most `s n` gates. One circuit per length, no uniformity. -/
def SIZE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∀ n, ∃ C : Circuit,
    (∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) ∧
    C.size ≤ s n ∧ C.Decides L n}

/-- P/poly: the languages with circuits of polynomial size. -/
def PPoly : Set (Language Bool) :=
  {L | ∃ p : Polynomial ℕ, L ∈ SIZE fun n => p.eval n}

/-- The languages decided, at every input length `n`, by a circuit with gates from the basis
`B`, of unbounded fan-in, with at most `s n` gates, each reading at most `s n` wires, and of
depth at most `d`. -/
def SizeDepth (B : Set GateOp) (s : ℕ → ℕ) (d : ℕ) : Set (Language Bool) :=
  {L | ∀ n, ∃ C : Circuit,
    (∀ g ∈ C.gates, g.op ∈ B ∧ g.inputs.length ≤ s n) ∧
    C.size ≤ s n ∧ C.depth n ≤ d ∧ C.Decides L n}

/-- AC0: polynomial size, constant depth, unbounded fan-in AND, OR and NOT gates. -/
def AC0 : Set (Language Bool) :=
  {L | ∃ (p : Polynomial ℕ) (d : ℕ),
    L ∈ SizeDepth {GateOp.and, GateOp.or, GateOp.not} (fun n => p.eval n) d}

/-- AC0[m]: AC0 with MOD `m` gates as well, for one fixed `m`. -/
def AC0Mod (m : ℕ) : Set (Language Bool) :=
  {L | ∃ (p : Polynomial ℕ) (d : ℕ),
    L ∈ SizeDepth {GateOp.and, GateOp.or, GateOp.not, GateOp.mod m} (fun n => p.eval n) d}

/-- ACC0: the union of AC0[m] over all `m`. -/
def ACC0 : Set (Language Bool) :=
  {L | ∃ m : ℕ, L ∈ AC0Mod m}

/-- TC0: polynomial size, constant depth, unbounded fan-in AND, OR, NOT and MAJORITY gates. -/
def TC0 : Set (Language Bool) :=
  {L | ∃ (p : Polynomial ℕ) (d : ℕ),
    L ∈ SizeDepth {GateOp.and, GateOp.or, GateOp.not, GateOp.maj} (fun n => p.eval n) d}

/-- Depth-two threshold circuits (a threshold gate of threshold gates, THR of THR) with at
most `s n` bottom gates and integer weights of any magnitude. At length `n` there are `k`
bottom gates; gate `j` is true on `x` when the weighted sum of the input bits, with weights
`w j`, is at least `t j`; the circuit is true when the weighted sum of the bottom gates, with
weights `a`, is at least `t0`. Negative weights give negations, so no NOT gate is needed. -/
def THRTHR (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∀ n : ℕ, ∃ (k : ℕ) (w : Fin k → Fin n → ℤ) (t : Fin k → ℤ) (a : Fin k → ℤ) (t0 : ℤ),
    k ≤ s n ∧ ∀ x : Fin n → Bool, (List.ofFn x ∈ L ↔
      t0 ≤ ∑ j : Fin k, a j *
        (if t j ≤ ∑ i : Fin n, w j i * (if x i = true then 1 else 0) then 1 else 0))}

/-! ## Depth-two threshold circuits as data, and their satisfiability problem -/

/-- A depth-two threshold circuit as data. Each bottom gate is a triple: the weights of the
input bits (in order), the gate's threshold, and the gate's weight at the top gate. `top` is
the threshold of the top gate. -/
structure ThrCircuit where
  /-- The bottom gates: input weights, threshold, weight at the top gate. -/
  gates : List (List ℤ × ℤ × ℤ)
  /-- The threshold of the top gate. -/
  top : ℤ

/-- The number of inputs: the length of the longest weight list. -/
def ThrCircuit.inputs (c : ThrCircuit) : ℕ :=
  (c.gates.map fun g => g.1.length).foldr max 0

/-- The value on `x`: a bottom gate is true when the sum of its weights at the true positions
of `x` reaches its threshold (a position without a weight, or without an input bit, counts
`0`); the circuit is true when the sum of the top weights of the true gates reaches `top`. -/
def ThrCircuit.eval (c : ThrCircuit) (x : List Bool) : Bool :=
  decide (c.top ≤ (c.gates.map fun g =>
    g.2.2 * (if g.2.1 ≤ ((g.1.zip x).map fun p => if p.2 = true then p.1 else 0).sum
      then 1 else 0)).sum)

/-- Some input of the right length makes the circuit true. -/
def ThrCircuit.Satisfiable (c : ThrCircuit) : Prop :=
  ∃ x : List Bool, x.length = c.inputs ∧ c.eval x = true

/-- A natural number in binary, self-delimiting: each bit is preceded by `true`, and `false`
ends the number. -/
def encodeNat (m : ℕ) : List Bool :=
  (Nat.bits m).flatMap (fun b => [true, b]) ++ [false]

/-- An integer: a sign bit (`true` for negative), then its absolute value. -/
def encodeInt (z : ℤ) : List Bool :=
  decide (z < 0) :: encodeNat z.natAbs

/-- A list, self-delimiting: each element is preceded by `true`, and `false` ends the list. -/
def encodeList {α : Type} (e : α → List Bool) (l : List α) : List Bool :=
  l.flatMap (fun a => true :: e a) ++ [false]

/-- A depth-two threshold circuit as a binary string, of length linear in the number of bits
of its weights and thresholds. -/
def encodeThr (c : ThrCircuit) : List Bool :=
  encodeList (fun g => encodeList encodeInt g.1 ++ encodeInt g.2.1 ++ encodeInt g.2.2) c.gates
    ++ encodeInt c.top

/-- The set `S` is decided by one machine that, on each `a`, halts with the answer within
`T a` steps. Unlike `PEqualNP.Library.DecidableInTime`, the bound may depend on the input
itself and not only on the length of its encoding. -/
def DecidableWithin {α : Type} (ea : α → List Bool) (S : Set α) (T : α → ℕ) : Prop :=
  ∃ (f : α → Bool) (c : Turing.TM2ComputableAux Bool Bool), (∀ a, a ∈ S ↔ f a = true) ∧
    ∀ a, Nonempty (Turing.TM2OutputsInTime c.tm ((ea a).map c.inputAlphabet.invFun)
      (some ((Computability.encodeBool (f a)).map c.outputAlphabet.invFun)) (T a))

/-- The number of inputs of the right length on which the circuit is true. -/
def ThrCircuit.satCount (c : ThrCircuit) : ℕ :=
  Fintype.card {x : Fin c.inputs → Bool // c.eval (List.ofFn x) = true}

/-- The function `g` is computed by one machine that, on each `a`, halts with the encoding of
`g a` within `T a` steps. The function version of `DecidableWithin`. -/
def ComputableWithin {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (g : α → β)
    (T : α → ℕ) : Prop :=
  ∃ c : Turing.TM2ComputableAux Bool Bool,
    ∀ a, Nonempty (Turing.TM2OutputsInTime c.tm ((ea a).map c.inputAlphabet.invFun)
      (some ((eb (g a)).map c.outputAlphabet.invFun)) (T a))

end PEqualNP.CircuitLowerBounds
