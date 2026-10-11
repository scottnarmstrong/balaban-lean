# Brief W37 — large fields, Lean block A: geometry of the reconstruction (Part I §I.2)

**Goal.** Formalize block **A** of the Lean declaration list in `notes/phase1/LF-RECONSTRUCTION.md`
§I.6 (Part I v1.1, §I.2 and Lemma I.3.13), namespace `Balaban.LargeField`, files under
`Balaban/LargeField/Geometry/`: A1 (distances, neighbourhoods `X^{∼m}`, thickenings), A2 (metric facts,
geodesics), A3, A4 (coarsening `blockMap`), A5 (L-block cover and openings), A6 (continuous torus
cubes, `N_r`), A7 (small sets, hulls, boxes, injective lift to ℤ^d), A8 (components as classes of
"distance < ω", separation, diameter bound), A9 (`nbhd_disjoint_of_comps` with the λ ≥ 0 hypothesis of
the v1.1 fix P1-02, `local_eq_global`), A10 (`DmodOmega`, `treeLengthMod`), A12 (Lemma S on the cube
torus: connect to the landed `Balaban/LargeField/Geometry/{Timar,LemmaS}.lean` of W31 —
`exteriorBoundary_starConn`, `enclosed_by_single_component`, `not_enclosed_boxes`,
`exists_shell_path_iff_not_enclosed` — through the torus lift of A7 / Lemma I.2.10(e); A11 is already
landed). A13 is low priority (skip unless cheap).

Use exactly the definitions of Part I v1.1 (the reconstruction's statements are the contract; if a
statement is false as printed, stop and report it with a counterexample). Reuse the landed
`Balaban/Lattice/Blocks.lean` (`blockMap`, `blockCoord`), `Balaban/Frozen/Model/Torus.lean`
(`Torus`), and the W31 namespace `Balaban.LatticeGeom` (do not duplicate its definitions; bridge to
them).

**Ownership.** New files under `Balaban/LargeField/Geometry/` (not the W31 files `Lattice.lean`,
`Plaquette.lean`, `BoundaryConnectivity.lean`, `Escape.lean`, `Timar.lean`, `LemmaS.lean`, which you
may import but not edit) in your worktree `/home/scott/Balaban-worktrees/W37` (branch
`w37-lf-geometry`), plus import lines in `Balaban.lean`. Never import `Balaban/Frozen/Roots/*` or
`Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).
Commit after each module.

**Stop condition.** A1–A10 and A12, or about 3,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions; main theorem names with statements; any Part I statement found
false; checks and results; axioms; last commit hash.
