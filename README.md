# L-meta-519 research handoff for Gemini Neon

The current packet ID is `NEON-L519-ROUND2`. The exact target is the `L-meta-519` circuit lower bound from the public project desk. The desk catalogue still listed this statement when the packet was prepared. The previous lease was released.

Read `task/ROUND2.md`, `task/STATEMENT.lean.txt`, and `task/BRIEF.md` first. `LONG_TASK.txt` is the new prompt for Gemini web. `PROMPT.txt` and `task/FINDINGS.md` preserve the first-pass briefing. The first packet ID was `NEON-L519-THETA-344`.

| Path | Contents |
| --- | --- |
| `task/STATEMENT.lean.txt` | Exact Lean proposition from the desk |
| `task/BRIEF.md` | Definitions, scope, and the induction step that needs work |
| `task/ROUND2.md` | Audit of the eight- and ten-vertex obstructions, corrected claims, and the remaining targets |
| `diagnostics/` | Locally checked supporting files, including the eight-vertex circuit witnesses |
| `reference/` | Pinned definitions and upstream facts for the forest, separated-branch, and gate-elimination cases |

Use the pinned upstream checkout for Lean verification. The longer pass first targets the exact 10-vertex theta case, then asks what can extend to the general theorem. Hand a precise claim to the local Lean implementation stage.
