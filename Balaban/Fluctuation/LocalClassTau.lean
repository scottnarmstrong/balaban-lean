/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassSum

/-!
# The parameter map of the local terms: `σ = τ ∘ extParams`

The local terms of a polymer `Y` (`localB_eTermHat_evTerm_xiFieldDom`, `localB_eTermHat_evTerm_local`,
`localB_eTermHat_evTerm_ext`) are computed on `𝔹 = 𝔹_{k+1}(Y⁺)` with a parameter map `σ` from the
parameters `w` of the expansion of the ambient level set `𝔹_{k+1}` (indices `ParIdx 𝔹_{k+1} X₁`, the
cubes of the cover disjoint from `X₁`) to the parameters of the cover of `𝔹`.  The map of P3 p. 78
(W799, W803) is `σ w = τ (extParams 𝔹_{k+1} X₁ w)`: the extension of `w` by `1` at the cubes meeting
`X₁`, transported to the cover of `𝔹` by keeping it at the cubes with base in the top layer
`Ω_{k+1}(𝔹)` and putting `0` at the others.  This file proves the five hypotheses on `σ` of those
theorems (for `𝔹_{k+1}` a level set):

* `localB_tauExt_analyticAt` (`hσan`): every coordinate is a coordinate of `w` or a constant;
* `localB_tauExt_norm_lt` (`hσκ`): `|(σ w)_P| < e^κ` on the polydisc of radius `e^κ`, `κ > 0`
  (`localB_tau_norm_lt`);
* `localB_tauExt_eq_one` (`hσ1`): `(σ w)_P = 1` at the cubes of the cover of `𝔹` contained in
  `X₁f ⊆ X₁ ∩ Y`: such a cube has its base in the top layer (`localB_collar_margin`), is a cube of
  the cover of `𝔹_{k+1}` (`level_localB_mem_cubeIdx_iff`) and meets `X₁`;
* `hσ0` is `localB_tau_off_top` at `extParams 𝔹_{k+1} X₁ w`;
* `localB_tauExt_active_subset` (`hσY`): for a connected family `𝒞` with `Y[𝒞] = Y` and `w`
  supported on `𝒞`, a cube with `(σ w)_P ≠ 0` lies in `Y`: it is a top-layer cube of the cover of
  `𝔹_{k+1}`, and either a parameter cube with `w_P ≠ 0`, hence in `𝒞`, hence in `Y[𝒞]`
  (`Pset_subset_Ysites'`), or a cube meeting `X₁`, hence inside `X₁ ⊆ Y[𝒞]`
  (`Pset_subset_of_not_disjoint`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.SmallField.GsSpec Finset

section TauExt

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **`hσan`**: the parameter map `w ↦ τ (extParams 𝔹_{k+1} X₁ w)` is analytic (each coordinate is a
coordinate of `w`, `1` or `0`). -/
theorem localB_tauExt_analyticAt (hk : k + 1 ≤ k + 1) (Yp : Set (CTorus d L N₁ m₁ (k + 1)))
    (X₁ : Set (CTorus d L N₁ m₁ (k + 1))) (w : ParIdx Gp X₁ → ℂ) :
    AnalyticAt ℂ (fun w : ParIdx Gp X₁ → ℂ =>
      fun P : ↥(coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx =>
        if P.1.2 ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) then
          Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0) w := by
  classical
  rw [analyticAt_pi_iff]
  intro P
  by_cases ht : P.1.2 ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
  · simp only [ht, ↓reduceIte]
    unfold Dec2.extS
    by_cases h1 : P.1 ∈ (coverOf Gp).cubeIdx
    · simp only [h1, ↓reduceDIte]
      unfold extParams
      by_cases h2 : Disjoint (Pset m₁ (⟨P.1, h1⟩ : ↥(coverOf Gp).cubeIdx).1) X₁
      · simp only [h2, ↓reduceDIte]
        exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ParIdx Gp X₁ => ℂ)
          ⟨⟨P.1, h1⟩, h2⟩).analyticAt w
      · simp only [h2, ↓reduceDIte]
        exact analyticAt_const
    · simp only [h1, ↓reduceDIte]
      exact analyticAt_const
  · simp only [ht, ↓reduceIte]
    exact analyticAt_const

/-- **`hσκ`**: on the polydisc of radius `e^κ`, `κ > 0`, every coordinate of
`τ (extParams 𝔹_{k+1} X₁ w)` has modulus `< e^κ`. -/
theorem localB_tauExt_norm_lt (hk : k + 1 ≤ k + 1) (Yp : Set (CTorus d L N₁ m₁ (k + 1)))
    (X₁ : Set (CTorus d L N₁ m₁ (k + 1))) {κ : ℝ} (hκ : 0 < κ) :
    ∀ w ∈ polydisc (0 : ParIdx Gp X₁ → ℂ) (fun _ => Real.exp κ),
      ∀ P : ↥(coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx,
        ‖(fun P : ↥(coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx =>
          if P.1.2 ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) then
            Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0) P‖ < Real.exp κ := by
  classical
  intro w hw
  have h1 : (1 : ℝ) < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  refine localB_tau_norm_lt hk Yp (le_refl (minSep L (L ^ m₁))) (fun P => ?_) h1
  unfold extParams
  split_ifs with h
  · simpa using hw ⟨P, h⟩
  · simpa using h1

/-- **`hσ1`**: `τ (extParams 𝔹_{k+1} X₁ w)` is `1` at every cube of the cover of `𝔹 = 𝔹_{k+1}(Y⁺)`
contained in `X₁f`, for `X₁f ⊆ X₁` and `X₁f ⊆ Y` (`𝔹_{k+1}` a level set, `Y⁺` the collar of
`Y`). -/
theorem localB_tauExt_eq_one (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    {Y Yp : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hX₁f : ∀ x ∈ X₁f, x ∈ X₁) (hX₁Y : ∀ x ∈ X₁f, x ∈ Y) :
    ∀ (w : ParIdx Gp X₁ → ℂ) (P : ℕ × CTorus d L N₁ m₁ (k + 1))
      (hP : P ∈ (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx),
      P ∉ (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).parCubes X₁f →
      (fun P : ↥(coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx =>
          if P.1.2 ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) then
            Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0) ⟨P, hP⟩ = 1 := by
  classical
  intro w P hP hpar
  have hsub : cubeP P ⊆ X₁f := by
    by_contra h
    exact hpar (Finset.mem_filter.2 ⟨hP, h⟩)
  have hP2 : P.2 ∈ X₁f := hsub (mem_cubeP.2 (SameCell.refl _ _))
  have htop : P.2 ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) :=
    localB_collar_margin hk (le_refl (minSep L (L ^ m₁))) hYp (R := X₁f) hX₁Y P.2 hP2 P.2
      (by rw [supDist_self]; exact Nat.zero_le _)
  have hPG : P ∈ cubeIdx Gp :=
    (level_localB_mem_cubeIdx_iff hG' hk Yp (le_refl (minSep L (L ^ m₁))) (q := P)
      ((GsSpec.mem_localB_Ω_top P.2).1 htop)).2 hP
  have hnd : ¬ Disjoint (Pset m₁ P) X₁ :=
    Set.not_disjoint_iff.2 ⟨P.2, self_mem_Pset P, hX₁f _ hP2⟩
  show (if P.2 ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) then
    Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P else 0) = 1
  rw [ite_eq_left htop]
  unfold Dec2.extS
  rw [dite_eq_left (show P ∈ (coverOf Gp).cubeIdx from hPG)]
  exact extParams_nonpar w ⟨P, hPG⟩ hnd

/-- **`hσY`**: for a connected family `𝒞` of the expansion of `𝔹_{k+1}` with `Y[𝒞] = Y` and `w`
supported on `𝒞`, every cube of the cover of `𝔹 = 𝔹_{k+1}(Y⁺)` at which
`τ (extParams 𝔹_{k+1} X₁ w)` does not vanish lies in `Y` (`𝔹_{k+1}` a level set, `X₁ = X₁(X)` of
the cover setup of the old polymer `X`). -/
theorem localB_tauExt_active_subset (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    (Yp : Set (CTorus d L N₁ m₁ (k + 1))) {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup Gp m₀ j X 𝒦X) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (κ : ℝ) :
    ∀ C ∈ connFams (fun i : ParIdx Gp (X1 Gp m₀ j 𝒦X) => i.1.1) Gp m₀ (X1 Gp m₀ j 𝒦X) Y,
      ∀ w ∈ supN C (Real.exp κ),
      ∀ P ∈ (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx,
        Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          ((fun P : ↥(coverOf (GsSpec.localB (k + 1) hk Yp
              (le_refl (minSep L (L ^ m₁))))).cubeIdx =>
            if P.1.2 ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) then
              Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0)) P ≠ 0 →
        ∀ y, SameCell (L ^ (P.1 + m₁)) y P.2 → y ∈ Y := by
  classical
  intro C hC w hw P hP hne y hy
  obtain ⟨-, hYs⟩ := (mem_connFams _).1 hC
  have hσP : Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
      ((fun P : ↥(coverOf (GsSpec.localB (k + 1) hk Yp
          (le_refl (minSep L (L ^ m₁))))).cubeIdx =>
        if P.1.2 ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) then
          Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0)) P =
      if P.2 ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) then
        Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P else 0 := by
    unfold Dec2.extS
    rw [dite_eq_left hP]
  rw [hσP] at hne
  by_cases htop : P.2 ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
  swap
  · exact absurd (ite_eq_right htop) hne
  rw [ite_eq_left htop] at hne
  have hPG : P ∈ cubeIdx Gp :=
    (level_localB_mem_cubeIdx_iff hG' hk Yp (le_refl (minSep L (L ^ m₁))) (q := P)
      ((GsSpec.mem_localB_Ω_top P.2).1 htop)).2 hP
  have hyP : y ∈ Pset m₁ P := hy
  unfold Dec2.extS at hne
  rw [dite_eq_left (show P ∈ (coverOf Gp).cubeIdx from hPG)] at hne
  have hne' : extParams Gp (X1 Gp m₀ j 𝒦X) w ⟨P, hPG⟩ ≠ 0 := hne
  by_cases hd : Disjoint (Pset m₁ P) (X1 Gp m₀ j 𝒦X)
  · have hval : extParams Gp (X1 Gp m₀ j 𝒦X) w ⟨P, hPG⟩ = w ⟨⟨P, hPG⟩, hd⟩ :=
      extParams_par w ⟨⟨P, hPG⟩, hd⟩
    rw [hval] at hne'
    have hi : (⟨⟨P, hPG⟩, hd⟩ : ParIdx Gp (X1 Gp m₀ j 𝒦X)) ∈ C := by
      by_contra h
      exact hne' (hw.1 _ h)
    have h1 := Pset_subset_Ysites' hcov (c := fun i : ParIdx Gp (X1 Gp m₀ j 𝒦X) => i.1.1)
      (fun i => i.1.2) hi hyP
    rw [hYs] at h1
    exact h1
  · have h1 := Pset_subset_of_not_disjoint hcov.polySetup hPG hd hyP
    rw [← hYs]
    exact subset_Ysites _ _ h1

end TauExt

end Balaban.Localization
