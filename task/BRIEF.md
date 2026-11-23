# Exact problem and proof target

For a finite undirected simple graph `G`, the edge function on Boolean vertex inputs is true if some edge has both endpoints true. `L-meta-519` asks whether every circuit for this function needs at least `m + τ - 1` gates, where `m` is the edge count and `τ` is the minimum vertex-cover size. The graph has at least one edge, maximum degree three, and every cycle has length at least seven. `STATEMENT.lean.txt` expresses the bound with `k` as a lower bound on every vertex cover and `s` as a circuit-size budget.

The project counts fan-in-at-most-two AND, OR, and NOT gates. Wires can be read more than once, input wires are free, and the circuit is a list of gates evaluated in order. See the exact `FanInTwo`, `HasCircuitSize`, `Circuit.eval`, and `GateOp.eval` definitions under `reference/lean/PEqualNP/Defs/`.

When a vertex `v` is fixed to zero, the remaining edge function drops the edges incident to `v`. For degree three, the edge count falls by three. The minimum vertex-cover size falls by one exactly when some minimum cover of the original graph contains `v`. If both drops occur, induction on the same `edges + cover` potential needs a restricted circuit at least four gates smaller, or another reason the restricted instance is stronger than the inductive lower bound alone. This is a question about the inductive argument. A failed four-gate deletion would leave the full lower bound undecided.

The prior checked circuit proof `L-meta-522` assumes that all distinct degree-three-or-higher vertices are at walk distance at least seven. See its selected source in `reference/L_meta_522-excerpts.lean.txt`. The posted target omits that distance assumption. `L-meta-531` gives the numerical bound for monotone binary formulas, where a subcomputation cannot be shared. When studying general circuits, account for both gate sharing and NOT gates explicitly.

The desk permits `Mathlib` and `PEqualNP.Defs` for the eventual contribution file `lean/PEqualNP/Outside/L_meta_519.lean`. The same-named theorem must have the exact statement, with no `sorry`, new axioms, or `native_decide`. The later local stage will check those requirements.
