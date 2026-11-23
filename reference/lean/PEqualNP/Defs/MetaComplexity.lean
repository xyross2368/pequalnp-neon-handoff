import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Set.Card
import PEqualNP.Defs.CircuitLowerBounds

/-!
# Definitions of the meta-complexity program

The ruling behind this file is `MetaComplexity/README.md`. Boolean circuits, their size,
`SIZE s` and P/poly are those of the circuit lower bounds program
(`PEqualNP.Defs.CircuitLowerBounds`): straight-line programs, size the number of gates. This
module adds the thin layer the meta-complexity program needs on top of them:

* "the function `f` on `n` inputs has a circuit of size at most `s`", for circuits of AND, OR
  and NOT gates of fan-in at most two, exactly the circuits `SIZE` counts;
* truth tables, and the minimum circuit size problem `MCSP` as a language over `Bool`;
* the two combinatorial conditions on a natural property, largeness and usefulness.

Nothing here speaks of machines. A statement that needs both sides (for example "MCSP is in
NP") uses `PEqualNP.Library.NP` and `PEqualNP.MetaComplexity.MCSP` together.
-/

namespace PEqualNP.MetaComplexity

/-- The circuit uses only AND, OR and NOT gates, each reading at most two wires. This is the
condition `PEqualNP.CircuitLowerBounds.SIZE` puts on its circuits. An AND gate reading no wire
is the constant `true` and an OR gate reading no wire is the constant `false`. -/
def FanInTwo (C : PEqualNP.CircuitLowerBounds.Circuit) : Prop :=
  ∀ g ∈ C.gates,
    g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
    g.inputs.length ≤ 2

/-- The Boolean function `f` on `n` inputs has a circuit with at most `s` gates: some circuit
of AND, OR and NOT gates of fan-in at most two, with at most `s` gates, outputs `f x` on every
input `x`. Inputs are not counted. As in `PEqualNP.CircuitLowerBounds`, an output wire that
does not exist reads `false`, so the constant `false` has size zero. -/
def HasCircuitSize (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    FanInTwo C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x

/-- The position of the input `x` in a truth table: the number whose binary digit `i` (digit
`0` is the least significant) is `x i`. It is below `2 ^ n`. -/
def tableIndex {n : ℕ} (x : Fin n → Bool) : ℕ :=
  Finset.univ.sum (fun i : Fin n => if x i = true then 2 ^ (i : ℕ) else 0)

/-- The Boolean function on `n` inputs whose truth table is `T`: the value on `x` is the entry
of `T` at position `tableIndex x`. Meant for `T` of length `2 ^ n`; a missing entry reads
`false`. -/
def tableFun (n : ℕ) (T : List Bool) : (Fin n → Bool) → Bool :=
  fun x : Fin n → Bool => T.getD (tableIndex x) false

/-- MCSP, the minimum circuit size problem, as a language over `Bool`. An instance is a size
bound `s` written in unary (`s` times `true`), then one `false`, then a truth table `T` of
length `2 ^ n` for some `n`. It is a member when the function with truth table `T` has a
circuit with at most `s` gates. The unary bound loses nothing up to polynomial time: every
function on `n` inputs has a circuit of size below `5 * 2 ^ n`, so larger bounds are all
equivalent. -/
def MCSP : Language Bool :=
  {w | ∃ (n s : ℕ) (T : List Bool),
    w = List.replicate s true ++ false :: T ∧ T.length = 2 ^ n ∧
      HasCircuitSize n (tableFun n T) s}

/-- A property of Boolean functions is a set `Q` of truth tables, given as a language: the
functions on `n` inputs with the property are the members of `Q` of length `2 ^ n`. The
property is large when, for some constant `c` and every `n`, at least a `2 ^ (-(c * (n + 1)))`
fraction of the `2 ^ (2 ^ n)` truth tables of length `2 ^ n` are in `Q`. -/
def Large (Q : Language Bool) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ,
    2 ^ (2 ^ n) ≤ 2 ^ (c * (n + 1)) * {T : List Bool | T.length = 2 ^ n ∧ T ∈ Q}.ncard

/-- The property `Q` is useful against circuits of size `s`: for every large enough `n`, no
function on `n` inputs with the property has a circuit with at most `s n` gates. -/
def UsefulAgainst (Q : Language Bool) (s : ℕ → ℕ) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ T : List Bool, T.length = 2 ^ n → T ∈ Q →
    ¬ HasCircuitSize n (tableFun n T) (s n)

/-- The binary code of a partial truth table: an undefined entry `none` is written
`false, false` and a defined entry `some b` is written `true, b`. Two bits per entry. -/
def encodePartial (T : List (Option Bool)) : List Bool :=
  T.flatMap fun o : Option Bool =>
    match o with
    | none => [false, false]
    | some b => [true, b]

/-- The total function `f` on `n` inputs is consistent with the partial truth table `T`: it
takes the value `b` wherever `T` has the defined entry `some b`. Entries are indexed by
`tableIndex`, as in `tableFun`; a missing entry is undefined. -/
def Consistent (n : ℕ) (T : List (Option Bool)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ (x : Fin n → Bool) (b : Bool), T.getD (tableIndex x) none = some b → f x = b

/-- Partial MCSP, the minimum circuit size problem for partial functions, as a language over
`Bool`. An instance is a size bound `s` in unary (`s` times `true`), one `false`, then the code
`encodePartial T` of a partial truth table `T` of length `2 ^ n` for some `n`. It is a member
when some total function consistent with `T` has a circuit with at most `s` gates. -/
def PartialMCSP : Language Bool :=
  {w | ∃ (n s : ℕ) (T : List (Option Bool)),
    w = List.replicate s true ++ false :: encodePartial T ∧ T.length = 2 ^ n ∧
      ∃ f : (Fin n → Bool) → Bool, Consistent n T f ∧ HasCircuitSize n f s}

end PEqualNP.MetaComplexity
