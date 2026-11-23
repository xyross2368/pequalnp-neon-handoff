# The remaining gate in the ten-vertex theta graph

The exact circuit size of `H10` lies in `{14, 15}`. Lean checked the explicit 15-gate upper-bound circuit in `diagnostics/L_meta_519_theta.lean`. The lower bound of 14 has been audited mathematically. The graph-specific Lean proof of 14 is for the local Flash stage. The one-gate restriction lemma it needs is already Lean-checked in `diagnostics/L_meta_519_one_gate.lean` using the pinned upstream `Readers` helpers.

## Short proof of 14

`H10` has paths `0-2-3-1`, `0-4-5-6-1`, and `0-7-8-9-1`. Fixing `x4=false` leaves the 7-cycle `0-2-3-1-9-8-7-0`, the attached path `1-6-5`, and the isolated vertex `4`. There are 9 edges and only vertex `1` has degree three, so the separation condition in `L204` is vacuous. Four cover vertices are needed on the 7-cycle and a fifth on the vertex-disjoint edge `56`. The cover `{0,1,2,5,8}` attains five. A five-edge matching cannot serve as the certificate because there are only nine non-isolated vertices.

With the singleton set empty, `L204` gives a restricted lower bound of `9 + 5 - 1 = 13`. Input `4` is essential and both its cofactors are nonconstant. One gate can therefore be saved on the false restriction, yielding 14 for the original circuit. The checked one-gate lemma uses `Readers.exists_least`, `Least.dep_read`, `Least.save`, and `rc_input`. There is no need to formalize the full `L107` table to establish 14.

## What an exact proof still needs

To prove 15 using vertex `4`, show that an optimum circuit can be restricted there with a saving of two gates. A hypothetical 14-gate minimum circuit cannot have two direct readers of `x4`, because both readers would be removed. If the unique reader is AND or NOT, setting `x4=false` makes it constant and removes a downstream reader as well. The restricted function is nonconstant, so the reader cannot itself be the output in this case. The remaining local pattern is a unique OR reader with a gate sibling. The same argument applies at `4,6,7,9`. A sound argument for a different vertex, a pair of vertices, or a finite certificate could also settle the benchmark.

The previous pass verified that the edge function meets `L107`'s dependence, nonconstant-cofactor, and no-pair-funnel conditions. Its three-cofactor argument applies to graphs of girth at least five with at least one edge and every non-isolated degree at least two. For `H10`, the finite cofactor decompositions and the table below were independently enumerated. The two false rows at `5,8` need an extra leaf restriction. An implication column describes the consequence **if** `L107` chooses that row. Its conclusion is existential.

| Fixed bit | Vertices | Lower bound on restricted gates | `L107` saving | Implied original bound |
| --- | --- | ---: | ---: | ---: |
| false | `0,1` | 11 | 3 | 14 |
| false | `2,3` | 12 | 3 | 15 |
| false | `4,6,7,9` | 13 | 3 | 16 |
| false | `5,8` | 12 after accounting for the extra leaf restriction | 3 | 15 |
| true | `0,1,2,3,4,6,7,9` | 10 | 4 | 14 |
| true | `5,8` | 12 | 4 | 16 |

The earlier tree and constant-true counterexamples are in `task/ROUND2.md`. The public theorem `L-meta-519` concerns all subcubic graphs of girth at least seven and admits arbitrary AND/OR/NOT fan-in-two circuits. A smaller circuit for `H10` would refute that statement. A proof of 15 would settle only this benchmark. `reference/L_meta_516-certificate-excerpts.lean.txt` shows an upstream precedent for a checked finite lower bound on a different theta graph.
