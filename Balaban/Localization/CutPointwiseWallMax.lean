/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.CutLemmaPCube

/-!
# The pointwise cut estimate at a mixed wall: maximum principle (VMOD-9 §4, (1.4))

`cut_prop48_cube`: for `x ∈ Ω₁(H)`, the retained quantity `U_D(x)` of the cut solution with the
physical wall retained satisfies
`U_D(x) ≤ K_p e^{-γ d_H(x, y')} L^{2j'} M_f` (`K_p = 2 K₁ = cutKp d L`) when `d_H(x, y') < ⊤`, and
`U_D(x) = 0` when `d_H(x, y') = ⊤`.  The proof is the maximum-principle form of the recursion of
Lemma P (`cut_lemmaP_cube`) exactly as in the landed `Multiscale/Pointwise48.lean prop48`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.LatticeGreen Balaban.Reflection Finset Matrix Filter Topology

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The constant `K_p = 2 K₁` of VMOD-9 (1.3).** -/
noncomputable def cutKp (d L : ℕ) : ℝ := 2 * cutK1 d L

/-- **VMOD-9 Theorem 1.1, (1.4).** -/
theorem cut_prop48_cube (hd : 3 ≤ d) (hL : 3 ≤ L) {G : GeneratingSet d L N₀ k ϱ} (hϱ : 1 ≤ ϱ)
    (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights k a) {α : G.Ω 1 → ℂ}
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    (S : ℕ) [NeZero S] (c : Fin d → ℕ) (hSℓ : S < N₀ * L ^ k)
    (hΛ : BlockAligned G (cubeSet (N₀ * L ^ k) S c))
    {j' : ℕ} (hj'1 : 1 ≤ j') (hj'k : j' ≤ k) {y' : Torus d (N₀ * L ^ k)} (hy' : y' ∈ G.layer j')
    (hy'Λ : y' ∈ cubeSet (N₀ * L ^ k) S c) {f : G.Ω 1 → ℂ}
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖f i‖ ≤ Mf) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    (G.pathDist x y' ≠ ⊤ →
      cutU G (cubeCut G (cubeSet (N₀ * L ^ k) S c))
        (zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f))
        x ≤ cutKp d L * Real.exp (-(agmonRate d / 2 * (G.pathDist x y').toReal)) *
          ((L : ℝ) ^ (2 * j') * Mf)) ∧
    (G.pathDist x y' = ⊤ →
      cutU G (cubeCut G (cubeSet (N₀ * L ^ k) S c))
        (zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f))
        x = 0) := by
  classical
  have hd0 : 0 < d := by omega
  set cut := cubeCut G (cubeSet (N₀ * L ^ k) S c) with hcutdef
  set ut := zeroExt (G.Ω 1) ((cutOperator G a ν cut α)⁻¹ *ᵥ f) with hutdef
  obtain ⟨U, hUdef⟩ : ∃ U : Torus d (N₀ * L ^ k) → ℝ, ∀ z, U z = cutU G cut ut z :=
    ⟨fun z => cutU G cut ut z, fun _ => rfl⟩
  set K1 := cutK1 d L with hK1def
  have hK1 : 0 ≤ K1 := cutK1_nonneg hd
  have hP : ∀ {x : Torus d (N₀ * L ^ k)}, x ∈ G.Ω 1 → ∀ {t : ℝ}, 0 ≤ t →
      ENNReal.ofReal t ≤ G.pathDist x y' → ∀ {M : ℝ}, 0 ≤ M →
      (∀ z ∈ G.Ω 1, G.pathDist z x ≤ ENNReal.ofReal (2 * d + 1) → U z ≤ M) →
      U x ≤ K1 * Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * j') * Mf) +
        thetaStar d * M := by
    intro x hx t ht0 ht M hM0 hM
    rw [hUdef x]
    exact cut_lemmaP_cube hd hL hϱ hsep hν hν1 ha hα S c hSℓ hΛ hj'1 hj'k hy' hy'Λ hsupp hMf0 hMf
      hx ht0 ht hM0 (fun z hz hzd => by rw [← hUdef z]; exact hM z hz hzd)
  have hU0 : ∀ z, 0 ≤ U z := fun z => by rw [hUdef z]; exact cutU_nonneg G cut ut z
  unfold cutKp
  rw [← hUdef x]
  have hε0 := agmonRate_pos hd0
  have hθ := thetaStar_pos d
  set F := (L : ℝ) ^ (2 * j') * Mf with hF
  have hF0 : 0 ≤ F := by positivity
  set D0 : ℝ := 2 * d + 1 with hD0
  have hD00 : 0 ≤ D0 := by positivity
  have hnear : ∀ {a b : Torus d (N₀ * L ^ k)}, G.pathDist a y' ≠ ⊤ →
      G.pathDist b a ≤ ENNReal.ofReal D0 → G.pathDist b y' ≠ ⊤ := by
    intro a b ha hba
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ha⟩)
      ((G.pathDist_triangle b a y').trans (add_le_add hba le_rfl))
  -- the finite-distance part
  have hfin : ∀ z ∈ G.Ω 1, G.pathDist z y' ≠ ⊤ →
      Real.exp (agmonRate d / 2 * (G.pathDist z y').toReal) * U z ≤ 2 * K1 * F := by
    set Dfin := Finset.univ.filter
      (fun z : Torus d (N₀ * L ^ k) => z ∈ G.Ω 1 ∧ G.pathDist z y' ≠ ⊤) with hDfin
    intro z hz hzt
    have hzD : z ∈ Dfin := by simp [hDfin, hz, hzt]
    obtain ⟨xs, hxs, hmax⟩ := Finset.exists_max_image Dfin
      (fun z => Real.exp (agmonRate d / 2 * (G.pathDist z y').toReal) * U z) ⟨z, hzD⟩
    refine (hmax z hzD).trans ?_
    obtain ⟨hxsΩ, hxst⟩ : xs ∈ G.Ω 1 ∧ G.pathDist xs y' ≠ ⊤ := by
      simpa [hDfin] using hxs
    set τ := (G.pathDist xs y').toReal with hτ
    have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
    set Wm := Real.exp (agmonRate d / 2 * τ) * U xs with hWm
    have hWm0 : 0 ≤ Wm := by
      have := hU0 xs; positivity
    set M := Real.exp (-(agmonRate d / 2 * (τ - D0))) * Wm with hMdef
    have hM0 : 0 ≤ M := by positivity
    have hM : ∀ z' ∈ G.Ω 1, G.pathDist z' xs ≤ ENNReal.ofReal D0 → U z' ≤ M := by
      intro z' hz' hdist
      have hzt' : G.pathDist z' y' ≠ ⊤ := hnear hxst hdist
      have hzD' : z' ∈ Dfin := by simp [hDfin, hz', hzt']
      have hW := hmax z' hzD'
      set τ' := (G.pathDist z' y').toReal with hτ'
      have hlow : τ - D0 ≤ τ' := by
        have h1 : G.pathDist xs y' ≤ ENNReal.ofReal D0 + G.pathDist z' y' := by
          refine (G.pathDist_triangle xs z' y').trans (add_le_add ?_ le_rfl)
          rw [GeneratingSet.pathDist_comm]; exact hdist
        have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hzt'⟩) h1
        rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hzt', ENNReal.toReal_ofReal hD00] at h2
        linarith
      have hU' : U z' = Real.exp (-(agmonRate d / 2 * τ')) *
          (Real.exp (agmonRate d / 2 * τ') * U z') := by
        rw [← mul_assoc, ← Real.exp_add]; simp
      rw [hU']
      calc _ ≤ Real.exp (-(agmonRate d / 2 * τ')) * Wm :=
            mul_le_mul_of_nonneg_left hW (Real.exp_pos _).le
        _ ≤ Real.exp (-(agmonRate d / 2 * (τ - D0))) * Wm := by
            apply mul_le_mul_of_nonneg_right _ hWm0
            apply Real.exp_le_exp.2
            nlinarith
    have hmain := hP hxsΩ hτ0 (ENNReal.ofReal_toReal hxst).le hM0 hM
    have hE : Real.exp (agmonRate d / 2 * τ) * Real.exp (-(agmonRate d / 2 * τ)) = 1 := by
      rw [← Real.exp_add]; simp
    have hEM : Real.exp (agmonRate d / 2 * τ) * M = Real.exp (agmonRate d / 2 * D0) * Wm := by
      rw [hMdef, ← mul_assoc, ← Real.exp_add]
      congr 2; ring
    have h2 : Wm ≤ K1 * F + 1 / 4 * Wm := by
      calc Wm = Real.exp (agmonRate d / 2 * τ) * U xs := rfl
        _ ≤ Real.exp (agmonRate d / 2 * τ) * (K1 * Real.exp (-(agmonRate d / 2 * τ)) * F +
            thetaStar d * M) := mul_le_mul_of_nonneg_left hmain (Real.exp_pos _).le
        _ = K1 * F * (Real.exp (agmonRate d / 2 * τ) * Real.exp (-(agmonRate d / 2 * τ))) +
            thetaStar d * (Real.exp (agmonRate d / 2 * τ) * M) := by ring
        _ = K1 * F + (thetaStar d * Real.exp (agmonRate d / 2 * D0)) * Wm := by
            rw [hE, hEM]; ring
        _ = K1 * F + 1 / 4 * Wm := by rw [hD0, thetaStar_mul]
    have hK1F : 0 ≤ K1 * F := by positivity
    linarith
  -- the infinite-distance part
  have hinf : ∀ z ∈ G.Ω 1, G.pathDist z y' = ⊤ → U z = 0 := by
    set Dinf := Finset.univ.filter
      (fun z : Torus d (N₀ * L ^ k) => z ∈ G.Ω 1 ∧ G.pathDist z y' = ⊤) with hDinf
    intro z hz hzt
    have hzD : z ∈ Dinf := by simp [hDinf, hz, hzt]
    obtain ⟨xs, hxs, hmax⟩ := Finset.exists_max_image Dinf (fun z => U z) ⟨z, hzD⟩
    refine le_antisymm ((hmax z hzD).trans ?_) (hU0 z)
    obtain ⟨hxsΩ, hxst⟩ : xs ∈ G.Ω 1 ∧ G.pathDist xs y' = ⊤ := by
      simpa [hDinf] using hxs
    have hM : ∀ z' ∈ G.Ω 1, G.pathDist z' xs ≤ ENNReal.ofReal D0 → U z' ≤ U xs := by
      intro z' hz' hdist
      have hzt' : G.pathDist z' y' = ⊤ := by
        by_contra hne
        exact (hnear hne (by rw [GeneratingSet.pathDist_comm]; exact hdist)) hxst
      exact hmax z' (by simp [hDinf, hz', hzt'])
    have hbound : ∀ t : ℝ, 0 ≤ t →
        (1 - thetaStar d) * U xs ≤ K1 * F * Real.exp (-(agmonRate d / 2 * t)) := by
      intro t ht0
      have := hP hxsΩ ht0 (by rw [hxst]; exact le_top) (hU0 xs) hM
      linarith
    have hθ1 : thetaStar d ≤ 1 / 4 := by
      have := thetaStar_mul d
      have h1 : 1 ≤ Real.exp (agmonRate d / 2 * (2 * d + 1)) := Real.one_le_exp (by positivity)
      nlinarith
    have hlim : Tendsto (fun t : ℝ => K1 * F * Real.exp (-(agmonRate d / 2 * t))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => agmonRate d / 2 * t) atTop atTop :=
        tendsto_id.const_mul_atTop (by positivity)
      have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
      simpa using h2.const_mul (K1 * F)
    have hle : (1 - thetaStar d) * U xs ≤ 0 :=
      ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨0, fun t ht => hbound t ht⟩)
    have : 0 < 1 - thetaStar d := by linarith
    nlinarith [hU0 xs]
  refine ⟨fun hxt => ?_, fun hxt => hinf x hx hxt⟩
  have h := hfin x hx hxt
  calc U x = Real.exp (-(agmonRate d / 2 * (G.pathDist x y').toReal)) *
        (Real.exp (agmonRate d / 2 * (G.pathDist x y').toReal) * U x) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (-(agmonRate d / 2 * (G.pathDist x y').toReal)) * (2 * K1 * F) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by rw [hF]; ring

end Balaban.Localization
