# Audit of the first Neon pass

The target is still the general `L-meta-519` lower bound in `STATEMENT.lean.txt`. The previous pass found a failure of a particular gate-deletion argument. The following checks define precisely which claims survived the audit.

## Eight-vertex tree T*

Use vertices `0` through `7` and edges `01, 12, 03, 34, 05, 56, 67`. There are 7 edges and the minimum cover has size 4. A matching is `12, 34, 05, 67`. Covers of size 4 include `{0,1,3,6}` and `{1,3,5,6}`. Setting `x0=false` leaves 4 edges and cover size 3.

The first circuit is

```text
(x1 & (x0 | x2)) | (x3 & (x0 | x4)) | (x5 & (x0 | x6)) | (x6 & x7)
```

It has 10 binary gates. Constant propagation and dead-gate elimination leave 7 gates when `x0=false`. Factoring `(x5 & x6) | (x6 & x7)` as `x6 & (x5 | x7)` gives 6. A different optimum 10-gate circuit simplifies directly to 6:

```text
(x0 & (x1 | x3 | x5)) | (x1 & x2) | (x3 & x4) | (x6 & (x5 | x7))
```

`diagnostics/L_meta_519_tstar.lean` checks the four circuit witnesses, their exact gate counts, and their Boolean functions. The optimum counts 10 and 6 follow by applying the published forest bound `L104` to the two graphs. That application is a mathematical argument with the stated edge and cover counts. The diagnostic file checks the witnesses. The example defeats a universal claim about plain syntactic simplification of every minimum circuit. It leaves size-preserving choice of a different optimum circuit or semantic rewriting as possible approaches.

## Ten-vertex tree T**

Extend `T*` by the edges `18, 89`. Now `m=9`, `tau=5`, and a matching of size 5 extends the matching above by edge `89`. The set `{0,1,3,6,8}` is a cover of size 5. Append the OR term `x8 & (x1 | x9)` to the first `T*` circuit. This gives an optimal 13-gate circuit by `L104`, even though the degree-three vertices `0` and `1` are adjacent. The forest bound has no branch-distance condition.

All 1,024 input assignments were checked independently for this circuit. With constant propagation and dead-gate elimination alone, the result uses 10 gates after `x0=false` and 7 after `x0=true`. In the false branch, `m + tau` drops by 4. In the true branch, `x1`, `x3`, and `x5` are singleton OR inputs, and the only residual edges are `67` and `89`. The potential `singletonCount + m + tau` drops from 14 to 7. Syntactic savings are only 3 and 6, respectively. Semantic absorption simplifies `x1 | (x8 & (x1 | x9))` to `x1 | (x8 & x9)` and recovers the missing true-branch gate.

## Correction to the reusable gate-saving claim

The claimed generic two-gate saving under a zero restriction needs a constant-output case. The minimum circuit for `!v | w` uses two gates. Input `v` feeds one NOT gate with the OR gate as its consumer. Setting `v=false` gives constant true, which needs one gate in the project circuit model. Any general lemma must handle that case or exclude it. Verify the output convention and explicitly justify normalization, fanout, and any semantic absorption you use.

## A concrete unresolved benchmark

`H10` is the theta graph with three paths of lengths 3, 4, and 4 between vertices `0` and `1`. Its explicit graph and checked 15-gate circuit are in `diagnostics/L_meta_519_theta.lean`. Deleting edges at vertex `4` leaves 9 edges, minimum cover size 5, and just one degree-three vertex. The surviving 7-cycle needs at least four cover vertices, and the edge `56` is disjoint from it. The set `{0,1,2,5,8}` attains five. With singleton set empty, the separated-branch theorem `L204` gives a lower bound of 13 gates for the restricted graph. The remaining finite problem is to establish at least 15 gates for `H10` or exhibit a circuit of at most 14 gates. A proposed local proof must handle the possibility that input `4` has a single OR reader. A restricted lower bound of 13 by itself does not give the two required gate savings.

Use `reference/lean/PEqualNP/MetaComplexity/L104.lean`, `L204.lean`, and `L107.lean` for exact known hypotheses. `L107` is an existential three-or-four gate-elimination theorem for certain Boolean functions. Neither its selected input nor its guaranteed savings automatically match the degree-three accounting in `L-meta-519`.
