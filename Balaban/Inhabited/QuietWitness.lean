/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.QuietImage
public import Balaban.Inhabited.QuietHist
public import Balaban.LargeField.Def7Inhabited


/-!
# `QuietStepInput'` at a positive scale

The witness of `QuietStepInput'` of `QuietLocalInput.lean` on a setting with a realized quiet step
`1 → 2` (`VACUITY-AUDIT-3`, P1): `L = 3`, `d = 3`, `M = 27` (the Def-7 witness setting `wS`, radii
`wR`, geometry `wGeo`), horizon `K = 2`, `k₀ = 0`, tori `n_j = 3^{2-j}`.

* `wH`: the region history with one large-field cube created at `0 → 1` and one component at each
  scale `1 ≤ k ≤ 2` (`QuietHist.hist`); `wH_quiet`: the step `1 → 2` is quiet in the component
  at scale `2`; `wa_realized`: its localized history is quiet realized (`QuietRealized`);
* `quietStepInput'_nonempty_pos`: `QuietStepInput'` is inhabited.  `real_euclid` is the theorem
  `quietRealized_iff_of_histImage` (the image history under a lattice symmetry, `QuietImage.lean`;
  the quiet realizable localized histories form a nonempty `HistImage`-closed set, by `wa_realized`);
  the boundary exponent is `b = 0`, which satisfies the landed bound (S0) as soon as
  `C_b, B_0 ≥ 0` and `log β_k ≥ 0`;
* `keptData_nonempty`: the zero kept data (no component of `wH` is kept, `wH_not_kept`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.Inhabited.QuietWit

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7.Wit RegionHistory

/-- The tori `n_j = 3^{2-j}` (horizon `K = 2`, a single cube at the top scale). -/
noncomputable abbrev wn : ℕ → ℕ := sides wS.L 2 1

theorem wn_top {j : ℕ} (h : 2 ≤ j) : wn j = 1 := by
  unfold wn sides
  rw [Nat.sub_eq_zero_of_le h]
  simp

/-- The region history: one large-field cube at `0 → 1`, a single component at every scale
`1 ≤ k ≤ 2`, `k₀ = 0`. -/
noncomputable def wH : RegionHistory wS wn wR 0 2 :=
  QuietHist.hist (k0 := 0) wS_ok le_rfl le_rfl wRH (sides_hnn wS.L 2 1)

theorem wH_comp : ∃ c : wH.Comp 2, ∀ c' : wH.Comp 2, c' = c :=
  QuietHist.comp_unique (k0 := 0) wS_ok le_rfl le_rfl wRH (sides_hnn wS.L 2 1) 2 (by norm_num)
    le_rfl


theorem wH_admissible : wH.Admissible := fun _ _ hc => absurd hc (Finset.notMem_empty _)

/-- The step `1 → 2` of `wH` is quiet in its component. -/
theorem wH_quiet (c : wH.Comp 2) : IsQuiet (wH.locRH 2 c) 1 c.1 := by
  unfold IsQuiet
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨-, hx2⟩ := Finset.mem_inter.mp hx
  have hx3 : x ∈ ((wH.locRH 2 c).step 1).newCubes := mem_finOf.mp hx2
  obtain ⟨hP, hQ, hR, hS⟩ := locRH_new c (j := 1) (by norm_num) (by norm_num)
  rcases hx3 with ((hx3 | hx3) | hx3) | hx3
  · rw [hP] at hx3
    obtain ⟨⟨h1, -⟩, -⟩ := hx3
    omega
  · rw [hQ] at hx3
    exact hx3.1
  · rw [hR] at hx3
    exact hx3.1
  · rw [hS] at hx3
    exact hx3.1

/-- The localized history of the component at scale `2`. -/
noncomputable def wa : LocalHistory wS wn 27 2 := wH.localHistory 27 2 2 (wH_comp.choose)

/-- **A realized quiet step `1 → 2`.** -/
theorem wa_realized : QuietRealized wR 0 1 wa :=
  ⟨wH, wH_admissible, wH_comp.choose, le_rfl, le_rfl, wH_quiet _, rfl⟩


/-- **`QuietStepInput'` at a positive scale** (`K = 2`, `k₀ = 0`, `L = 3`, `M = 27`): the
closure of the quiet realizable localized histories under lattice symmetries is proved
(`quietRealized_iff_of_histImage`), the boundary exponent is `b = 0` (allowed by the bound (S0)
for `C_b ≥ 0`, `B_0 ≥ 0`, `log β_k ≥ 0`).  The quiet step `1 → 2` of `wH` is realized
(`wa_realized`), so the fields are not vacuous. -/
theorem quietStepInput'_nonempty_pos (cs : OpConsts) (N : ℕ) (hCb : 0 ≤ cs.Cb) (hB0 : 0 ≤ cs.B0)
    (hlog : ∀ k, 0 ≤ Real.log (cs.beta k)) :
    Nonempty (QuietStepInput' 2 0 (wGeo wn) cs N) := by
  refine ⟨{
    real_euclid := fun k σ a a' hI =>
      quietRealized_iff_of_histImage (fun j hj => wn_top hj) (Nat.zero_le _) hI
    b := fun _ _ _ _ _ _ => 0
    b_meas := fun _ _ _ _ _ => measurable_const
    b_analytic := fun _ _ _ _ _ _ => analyticOnNhd_const
    b_real := fun _ _ _ _ _ _ _ _ _ => by simp
    b_supp := fun _ _ _ _ _ _ _ _ _ => rfl
    b_rot := fun _ _ _ _ _ _ _ _ => rfl
    b_euclid := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    b_bound := fun H _ k _ _ Z' _ o x hv g _ _ => by
      simp only [norm_zero]
      refine mul_nonneg (add_nonneg (mul_nonneg hCb (hlog k)) (mul_nonneg hCb hB0)) ?_
      unfold volScale
      positivity }⟩


/-- With `k₀ = 0` no component of `wH` is kept (kept events need `1 ≤ k ≤ k₀`). -/
theorem wH_not_kept (k : ℕ) (Z : wH.Comp k) : ¬ IsKept wH k Z := fun h => by
  have h1 := h.1
  have h2 := h.2.1
  omega

/-- **The kept data for the positive-scale witness** (the zero kept kernels; no component of `wH`
is kept, `wH_not_kept`). -/
theorem keptData_nonempty (cs : OpConsts) (N : ℕ) (κ : ℕ → LocalHistory wS wn 27 2 → ℝ)
    (lamHat : ℕ → ℝ) : Nonempty (KeptData 0 (wGeo wn) cs N κ lamHat) :=
  ⟨zeroKeptData (wGeo wn) cs κ lamHat⟩

end Balaban.Inhabited.QuietWit
