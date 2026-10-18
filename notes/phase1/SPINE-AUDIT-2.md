# SPINE-AUDIT-2 — truth and non-vacuity of the seven Root-F inputs (W1097, 2026-10-18)

Scope: `Balaban/Spine/{RootFInputs,Activities,RootF,RootC,Witness}.lean`, `notes/phase1/SPINE.md`, at origin/main (a4b9d79a). No Lean file of the
repository was changed. Probe: `/home/scott/Balaban-scratch/W1097/P1.lean` (compiled with `lake env lean` from `/home/scott/Balaban`, no warnings).
Method: for each input, look for a choice of data making it false, or trivially true, using the landed class definitions (`IsRep2`, `IsRepFlat2`,
`Coh`, `CoeffBounds`, `D9Coeff`, `D9Flat`, `Geo`, `SFFlat2`, `D1Form2`).

## Verdict table

| Input | Verdict | Reason (short) |
|---|---|---|
| `PrefixInput` | TRUE-PLAUSIBLE, but **incomplete** (see F1-F4) | satisfiable (c₈ small, L ≥ 3); `c₈ q/(1-q) ≤ 1/20` contradicts no landed fact |
| `BaseStepInput` | UNDECIDED (not trivial) | existence of `ρ₁` with `∫ρ₁ = C Z(g)`; contains real content; the class at `K = kf+1` has no landed witness |
| `ClassStepInput` | TRUE-PLAUSIBLE, vacuous unless `BaseStepInput` holds | `∀ρ ∈ ℛ_k`: `D9Coeff.k_le`, `nu_le` consistent for `k+1 ≤ k₀` |
| `TransferInput` | UNDECIDED | reduces to (H6′) ⇒ (H6♭) at `K = kf+1` (the other six clauses are identical or weaker) |
| `FrozenStepInput` | TRUE-PLAUSIBLE (same remark) | `ν_{k+1} ≤ 7/8 (1+ξ₃)/(1+ξ₂) ≤ 1` keeps `D9Flat.nu_le` |
| `LastIntegralInput` | UNDECIDED, one real risk (F5) | does not tie `sf.β 0` to `β`; the activities carry real content |
| `KfZeroInput` | TRUE-PLAUSIBLE | physical statement, no class; not trivial (see (d)) |

No input is FALSE or TRIVIAL for every provider choice, so no counterexample probe is claimed. One probe shows that a PrefixInput-admissible provider
choice (`L = 2`) makes the class empty at scales `k ≥ 3`, hence makes `ClassStepInput`/`FrozenStepInput` false (F1).

## Findings

**(a) Constants against landed facts.**
* `c₈`: `Def6.Consts.Admissible` only requires `0 < c₈`; `CoeffBounds.flow` only bounds `ξ` above (`c₈/4 q^{n+1}`). Choosing `c₈` small is free,
  and the stop lemma `stop_of_flatClassAt` uses exactly `exp(1/20) ≤ 20/19` and `19/20 > 7/8`. No contradiction.
* **The kernel-constant window.** `CoeffBounds` gives at every scale `k` of the class `9/10 (1-L⁻²)⁻¹ ≤ a_k < 3/2`, with `a_k = compWeight L a k = a (1-L⁻²)/(1-L^{-2k})`
  and the same `a = cs₀.aKer` at all scales (`Coh.a_free`). For `L = 2`: `k = 1` forces `a ∈ [1.2, 1.5)`, and `k = 3` forces `a ≥ 1.575`.
  Probe `L2_window_clash` (P1.lean), proved:
  `∀ a, (9/10·(1-(2²)⁻¹)⁻¹ ≤ compWeight 2 a 1 ∧ compWeight 2 a 1 < 3/2) → 9/10·(1-(2²)⁻¹)⁻¹ ≤ compWeight 2 a 3 → False`.
  So `PrefixInput`'s `2 ≤ L` (Root-F's range) is not enough: at `L = 2` and `k̂_f ≥ 3` the inputs are false. For `L ≥ 3` the window
  `a ∈ [0.9/(1-L⁻²)², 3/2)` is nonempty (`L = 3`: `[1.14, 1.5)`; the witness uses `5/4`). The provider must also choose `aKer` in it; PrefixInput does not say so.
* `Geo` has `M = c·M₁` and `14 ≤ c`; `Coh.M_pow` has `M = L^{m₀+m₁}`. With `L = 7`, `c` must be a power of 7 (`c = 49`), not 14. PrefixInput records none of these. They fail closed
  (the class is empty, so `BaseStepInput` is false), but nothing in the statement of the spine tells the provider.
* (H-λ) for the transfer: `θ = (d-2) log L`, and `hH1 : k̂ - k₀ < λ_{k₀}`, `hH2 : λ_{k̂} ≤ d/2 λ_{k₀} + c_H` hold asymptotically iff `(d-2)/2 < θ ≤ (d-2) log L`. The prefix
  is at the upper edge, `hH2` is an equality up to the additive constant `c_H`. Fine for `L ≥ 2` (`log 2 > 1/2`), but it is a hypothesis of `IsRep2.toFlat` that the spine hides inside `TransferInput`.

**(b) Horizons.**
* `FlatClassAt` is `IsRepFlat2 … K = kf+1 … khat = kf`; `RepClassAt` is `IsRep2 … K = kf+1`. No landed witness has `K ≥ 2` (`wIsRepFlat2`: `K = k = khat = 1`); the only witness
  statement, `repClassAt_witness`, is `kf = 0` and is never used in the flow regime (the flow needs `kf ≥ 1`). So the class is not known to be inhabited where the spine uses it.
  What decides it: a zero-term witness `wRep` over `K = 2`, `k = 1` (`D4Pin 2` ranges over `j = 1` only; `D6Flat` with `khat = 1`); or any proof of `BaseStepInput`.
* `TransferInput`: `IsRep2` and `IsRepFlat2` differ only in `range`, `sfData` (landed `toFlat2`), `budget` (`D6Budget` vs `D6Flat khat`) and `coeff` (landed `toFlat`); `form`, `corr`, `pin`, `opBound`, `bdry`,
  `coherent`, `complete` are the same clauses on the same `F`. So the input is exactly (H6′) ⇒ (H6♭) at `K = kf+1`. The landed lemma needs `K ≤ k+1` and `Rep.budgetFlat_of_LF2` needs `K ≤ khat`.
  No obstruction to the truth was found, but `∃ F'` in `FlatClassAt` is the same `F` in practice, so the claim is not weaker than the landed lemma.
* `LastIntegralInput` at `k < kf` with `ν_k L² > 7/8` (early stop) is consistent: `ν_k ≤ 1` (`D9Flat`), activities of top scale `k+1 ≤ kf` are inside `ObservableActivities`.

**(c) Quantifiers.**
* `ν`, `h`, `g`: `ν L² ≤ 7/8` vs `> 7/8` partition `(0,1]`; `IsHorizon` is unique; the boundary `ν L² = 7/8` is handled by `stop_of_flatClassAt` (`ν_{kf} L² ≥ 19/20`). `g` is in the open ball
  (`<1`), the spine's `Z` identity and the class's `l1Ball` agree. `‖h‖ = 1`: the class carries any real unit `hv`; fine.
* Tiny tori (`n_K = 1`, `ℓ = M L^{kf+1}`): the only scale-`(kf+1)` polymer is the whole torus, the amplitude bound is `c₉/2 L^{-…} e^{-κ}`; the content is a smallness estimate of the nonlinear part of `log Z`, true for `β ≥ β₀`.
* **F5 (what the class does not tie).** `RepClassAt`/`FlatClassAt` add `ν_0 = ν` only. `sf.β 0` is not tied to the spine `β` (`Coh` uses `β` only in `λ̂_j`, `k₀`;
  `CoeffBounds.flow` has `β₀` existential; `D9Coeff.beta_gt : B L^{k(d-2)} < β_k`). `ClassStepInput`, `TransferInput`, `FrozenStepInput`, `LastIntegralInput` are `∀ρ ∈ class`, so they quantify over
  members with any running coupling `β'` allowed by the class. The step inputs do not care. `LastIntegralInput` claims activity amplitude `c₉/2` for arbitrary `c₉ > 0`, which is false for a member with `β'` of the size
  of `B` unless `B` (a provider choice) or the budget (`D6Flat`: `A₂ λ_{k₀}^{p₂} ≤ G`, with `G` through `log β_k`) forces `β' → ∞` with `β`. This is undecided; it is removed by adding `F.sf.β 0 = β` (F4). Likewise `P6.κ`, `P6.c₉` are not tied
  to the spine's `κ, c₉`, which enter only `ObservableActivities`; the amplitude conversion needs `P6.c₉ ≤ c₉/2`-type and `P6.κ ≥ κ`-type ties.

**(d) Two-torus clause (small polymers).** Exact equality `p_ℓ(X; g) = p_{ℓ'}(X; g)` on quarter-box polymers does not contradict the exponential identity: the finite-size defect of `log Z_ℓ` (periodic images of the covariance, the
  magnetization `m_ℓ - m_∞`) is not local to a small `X`, but it can be put on polymers `X' ∋ x` that wrap the torus (`≥ n_K` blocks at the top scale, bound `e^{-κ n_K}`), since `p` may depend on `g|_{X'}`, `X' ⊃ X`.
  This needs defect `≲ e^{-cM L} L^{-kf(d-2)}/β ≤ c₉/2 L^{-(kf+1)((d-2)/2+δ)} e^{-κ n_K}` for every `n_K ≥ 1` and every `kf`; the factor `e^{-cM}` is where `M` must beat `κ`. Plausible, not proved; the `p` is then the infinite-volume activity
  on small polymers, which has to be a definition. The clause is not vacuous (`observableActivities_zero` shows it holds for `p = 0`, and then the identity is the real content). Undecided; what decides it is W1088's construction of `p` with a wrapped remainder.
  At scale `j = kf+1` and the minimal torus the clause is empty (no quarter-box image is a union of blocks).

**(e) Unused or vacuous.** All seven are used by `rootF_clauses_of_spine`. `ClassStepInput`, `TransferInput`, `FrozenStepInput`, `LastIntegralInput` are vacuous exactly if the class is empty at the provider's
constants; `BaseStepInput` is the only one that rules this out (it asserts a member, with `∫ρ₁ = C Z ≠ 0`). `KfZeroInput` is independent of the classes and has no `P6, C7, PB, …`, so it holds or fails with `T` only (through `L, M`).

## Fixes

F1. `PrefixInput`: replace `2 ≤ L` by `3 ≤ L` (Root-F's `2 ≤ L` follows). Add the window `0.9/(1-L⁻²)² ≤ aKer < 3/2` for `cs₀ κ c₉` (`a_ge` at all scales, `a_lt` at `k = 1`).
F2. Add `T.M = c·M1`, `14 ≤ c`, `1 ≤ M1`, `T.M = T.L^(P6.m₀ + C7.m₁)` to `PrefixInput` (they are the fields of `Geo`/`Coh` that every class member needs), so a class with no members is caught at A1.
F3. Add the ties `P6.κ = κ`-type and `P6.c₉ ≤ c₉/2`-type (whichever `rootFClauses` conversion needs) to `PrefixInput`, so that Root-F's `κ, c₉` are not free of the class constants.
F4. Add `F.sf.β 0 = β` (and `F.sf.z 0 = 1` if `z` is normalised) to `RepClassAt`, `FlatClassAt`; `BaseStepInput` produces it, the step inputs preserve it, and `LastIntegralInput` becomes a statement about the physical flow only.
F5. Before using the spine for the Root-F closure, prove `Nonempty (FlatClassAt …)` at `kf = 1`, `K = 2` (zero-term witness over `K = 2`), as `Witness.lean` does for `RepClassAt` at `kf = 0`. Until then rule 10 is open for `FlatClassAt`.
F6. Record the (H-λ) window `(d-2)/2 < θ ≤ (d-2) log L` and `hH1, hH2` as a lemma of the prefix (they are hypotheses of `IsRep2.toFlat` that `TransferInput` currently absorbs).
