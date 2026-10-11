# Brief W34 — correct the C-1* interface (`C1Star`) per the observables review

**Goal.** Apply edits 1–3 of `notes/phase1/OBSERVABLES-review.md` ("Summary of required edits") to
the landed C-1* structure and re-prove Root-C from it, keeping the final theorem
`Balaban.Correlations.rootC_of_rootFAndC1Star : RootFAndC1Star d N hN → RootCStatement d N`
(`Balaban/Correlations/RootCFromFlow.lean`) with its exact type (only the definitions it mentions
change):

1. **`C1StarF3`** (`Balaban/Correlations/C1Star.lean`): add the term `ν ^ (((d : ℝ) − 2) / 2)` inside
   the bracket of the `rtr` and `rlg` bounds, exactly as in the review (lines ~86–90: 
   `cStar * ((1 + ‖x − y‖) ^ (−((d:ℝ) − 2 + ρ₀)) + ν ^ (((d:ℝ) − 2) / 2)) * exp(−cPrime √ν ‖x − y‖)`),
   and adapt `BoundsNu.lean` (`hrem′`, the Step B two-point bound: Root-C's `c` grows by a factor
   depending on `d` and `cPrime`, its `c′` is halved — see the review) and `ZeroLimit.lean`
   (`ν^{(d−2)/2} → 0`), `abs_rtrLim_le`.
2. **`C1StarF2`**: restrict the `em` bound to tori with `ℓ ≥ ℓ₀(ν, x)` (O-02: winding terms on small
   tori are of size β⁻¹ν^{(d−2)/2}); choose the exact form (e.g. `∃ ℓ₀, ∀ ℓ ≥ ℓ₀, …` inside the
   `ν, x` quantifiers, or `2‖x‖ < ℓ`-type) that the derivation in OBSERVABLES.md §5 supports and that
   `LemmaThree.lean` (Lemma 3.0, limits along tori) can consume; adapt `LemmaThree.lean`.
3. **`C1Star`**: move `J`, `J_pos`, `J_tendsto`, `J_bounds` inside `data` (after `β`), as a weakening
   (O-03/F-A); adapt `Assembly.lean` (the destructuring at ~line 49 moves after `data β hβS`) and any
   other consumer.

Then re-run the probe yourself only through the landed theorem: `rootC_of_rootFAndC1Star` must still
build with an unchanged type (the orchestrator re-checks definitional equality with the frozen
Root-C). Report the new full text of `C1StarF2`, `C1StarF3` and the `C1Star` structure.

**Ownership.** In-place edits to `Balaban/Correlations/{C1Star,Assembly,BoundsNu,ZeroLimit,LemmaThree,MainTerm}.lean`
and other `Balaban/Correlations/*` consumers as needed, in your worktree
`/home/scott/Balaban-worktrees/W34` (branch `w34-c1star-fix`). Never import `Balaban/Frozen/Roots/*`
or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` on
`rootC_of_rootFAndC1Star` standard; `python3 -I scripts/check_lean_modules.py --root .`.

**Stop condition.** Items 1–3, or a precise obstruction (a step of Root-C that no longer follows —
quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; the new definitions (full text); confirmation that `rootC_of_rootFAndC1Star`'s
type is unchanged; checks and results; axioms; last commit hash.
