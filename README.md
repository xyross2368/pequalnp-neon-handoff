# L-meta-519 research handoff for Gemini Neon

The current packet ID is `NEON-L519-ROUND3`. The exact target is the `L-meta-519` circuit lower bound from the public project desk. The desk catalogue still listed the statement when this packet was prepared. The current research benchmark is the exact circuit size of `H10`.

Read `task/ROUND3.md`, `task/STATEMENT.lean.txt`, and `task/BRIEF.md` first. `ROUND3_TASK.txt` is the new task for Gemini Neon. `LONG_TASK.txt` and `task/ROUND2.md` preserve the previous pass. `PROMPT.txt` and `task/FINDINGS.md` preserve the original briefing.

| Path | Contents |
| --- | --- |
| `task/STATEMENT.lean.txt` | Exact Lean proposition from the desk |
| `task/BRIEF.md` | Definitions, scope, and the induction step that needs work |
| `task/ROUND3.md` | Audited 14-gate lower bound, checked 15-gate upper bound, and exact remaining problem |
| `task/ROUND2.md` | Audit of the eight- and ten-vertex obstructions, corrected claims, and the remaining targets |
| `diagnostics/` | Checked circuit witnesses and the local one-gate restriction lemma |
| `reference/` | Pinned circuit definitions, prior lower bounds, and excerpts from a checked finite certificate on a smaller theta graph |

Neon proposes and audits mathematical directions from this snapshot. Gemini 3.8 Flash implements and verifies the handoff locally with the pinned toolchain. The current pass targets the last gate in `H10`, then asks what can extend to the general theorem.
