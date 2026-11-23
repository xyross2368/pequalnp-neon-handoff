# L-meta-519 research handoff for Gemini Neon

The packet ID is `NEON-L519-THETA-344`. The exact target is the `L-meta-519` circuit lower bound from the public project desk. The desk catalogue still listed this statement when the packet was prepared. The previous lease was released.

Read `task/BRIEF.md`, `task/STATEMENT.lean.txt`, and `task/FINDINGS.md` first. `PROMPT.txt` is the prompt to send after importing this repository into Gemini web.

| Path | Contents |
| --- | --- |
| `task/STATEMENT.lean.txt` | Exact Lean proposition from the desk |
| `task/BRIEF.md` | Definitions, scope, and the induction step that needs work |
| `task/FINDINGS.md` | Verified local facts and the remaining circuit proof gap |
| `diagnostics/` | Three locally Lean-checked supporting files |
| `reference/` | Pinned upstream definitions, checked formula proof, and selected passages from the previous circuit proof |

Use the pinned upstream checkout for Lean verification. Start with one mathematical route. Hand a precise claim to the local Lean implementation stage if the route works.
