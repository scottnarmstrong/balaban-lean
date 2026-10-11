/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwiseP

/-!
# Proposition 4.8 (G-2(ii), pointwise decay)

Let `u = G_D(α) f`, `f` supported in the `j'`-block of `y'` with `|f| ≤ M_f`, and
`U(x) = |ũ(x)| + ℓ(x) ∑_μ |ũ(x + e_μ) - ũ(x)|`.  Then for every `x ∈ Ω₁` at finite path distance
`d(x, y')` from `y'`

`U(x) ≤ K₂ e^{-(ε₀/2) d(x, y')} ℓ_{j'}² M_f`,

and `U(x) = 0` if `d(x, y') = ∞`; the constant `K₂` depends only on `d`, `L` and the mass cap `Λ` (`ν L^{2k} ≤ Λ`).
The proof is the maximum-principle form of the recursion (4.3): at a maximiser of
`e^{(ε₀/2) d(x, y')} U(x)`, Lemma P and the contraction `θ* e^{(ε₀/2)(2d+1)} = ¼` give the bound.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban Balaban.LatticeGreen Filter Topology

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem thetaStar_mul (d : ℕ) :
    thetaStar d * Real.exp (agmonRate d / 2 * (2 * d + 1)) = 1 / 4 := by
  unfold thetaStar
  rw [mul_assoc, ← Real.exp_add]
  simp

/-- **Proposition 4.8.** -/
theorem prop48 (hd : 3 ≤ d) (hL : 3 ≤ L) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ K2 : ℝ, 0 ≤ K2 ∧ ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)
      (S : PtSetting G Λ) {Mf : ℝ}, 0 ≤ Mf → (∀ i, ‖S.f i‖ ≤ Mf) →
      ∀ {x : Torus d (N₀ * L ^ k)}, x ∈ G.Ω 1 →
      (G.pathDist x S.y' ≠ ⊤ →
        S.U x ≤ K2 * Real.exp (-(agmonRate d / 2 * (G.pathDist x S.y').toReal)) *
          ((L : ℝ) ^ (2 * S.j') * Mf)) ∧
      (G.pathDist x S.y' = ⊤ → S.U x = 0) := by
  classical
  obtain ⟨K1, hK1, hP⟩ := lemmaP (d := d) (L := L) hd hL Λ hΛ
  refine ⟨2 * K1, by positivity, ?_⟩
  intro k N₀ _ ϱ G S Mf hMf0 hMf x hx
  have hε0 := agmonRate_pos S.hd0
  have hθ := thetaStar_pos d
  set F := (L : ℝ) ^ (2 * S.j') * Mf with hF
  have hF0 : 0 ≤ F := by positivity
  set D0 : ℝ := 2 * d + 1 with hD0
  have hD00 : 0 ≤ D0 := by positivity
  have hnear : ∀ {a b : Torus d (N₀ * L ^ k)}, G.pathDist a S.y' ≠ ⊤ →
      G.pathDist b a ≤ ENNReal.ofReal D0 → G.pathDist b S.y' ≠ ⊤ := by
    intro a b ha hba
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ha⟩)
      ((G.pathDist_triangle b a S.y').trans (add_le_add hba le_rfl))
  -- the finite-distance part
  have hfin : ∀ z ∈ G.Ω 1, G.pathDist z S.y' ≠ ⊤ →
      Real.exp (agmonRate d / 2 * (G.pathDist z S.y').toReal) * S.U z ≤ 2 * K1 * F := by
    set Dfin := Finset.univ.filter
      (fun z : Torus d (N₀ * L ^ k) => z ∈ G.Ω 1 ∧ G.pathDist z S.y' ≠ ⊤) with hDfin
    intro z hz hzt
    have hzD : z ∈ Dfin := by simp [hDfin, hz, hzt]
    obtain ⟨xs, hxs, hmax⟩ := Finset.exists_max_image Dfin
      (fun z => Real.exp (agmonRate d / 2 * (G.pathDist z S.y').toReal) * S.U z) ⟨z, hzD⟩
    refine (hmax z hzD).trans ?_
    obtain ⟨hxsΩ, hxst⟩ : xs ∈ G.Ω 1 ∧ G.pathDist xs S.y' ≠ ⊤ := by
      simpa [hDfin] using hxs
    set τ := (G.pathDist xs S.y').toReal with hτ
    have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
    set Wm := Real.exp (agmonRate d / 2 * τ) * S.U xs with hWm
    have hWm0 : 0 ≤ Wm := by
      have := S.U_nonneg xs; positivity
    set M := Real.exp (-(agmonRate d / 2 * (τ - D0))) * Wm with hMdef
    have hM0 : 0 ≤ M := by positivity
    have hM : ∀ z' ∈ G.Ω 1, G.pathDist z' xs ≤ ENNReal.ofReal D0 → S.U z' ≤ M := by
      intro z' hz' hdist
      have hzt' : G.pathDist z' S.y' ≠ ⊤ := hnear hxst hdist
      have hzD' : z' ∈ Dfin := by simp [hDfin, hz', hzt']
      have hW := hmax z' hzD'
      set τ' := (G.pathDist z' S.y').toReal with hτ'
      have hlow : τ - D0 ≤ τ' := by
        have h1 : G.pathDist xs S.y' ≤ ENNReal.ofReal D0 + G.pathDist z' S.y' := by
          refine (G.pathDist_triangle xs z' S.y').trans (add_le_add ?_ le_rfl)
          rw [GeneratingSet.pathDist_comm]; exact hdist
        have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hzt'⟩) h1
        rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hzt', ENNReal.toReal_ofReal hD00] at h2
        linarith
      have hU' : S.U z' = Real.exp (-(agmonRate d / 2 * τ')) *
          (Real.exp (agmonRate d / 2 * τ') * S.U z') := by
        rw [← mul_assoc, ← Real.exp_add]; simp
      rw [hU']
      calc _ ≤ Real.exp (-(agmonRate d / 2 * τ')) * Wm :=
            mul_le_mul_of_nonneg_left hW (Real.exp_pos _).le
        _ ≤ Real.exp (-(agmonRate d / 2 * (τ - D0))) * Wm := by
            apply mul_le_mul_of_nonneg_right _ hWm0
            apply Real.exp_le_exp.2
            nlinarith
    have hmain := hP G S hMf0 hMf hxsΩ hτ0 (ENNReal.ofReal_toReal hxst).le hM0 hM
    have hE : Real.exp (agmonRate d / 2 * τ) * Real.exp (-(agmonRate d / 2 * τ)) = 1 := by
      rw [← Real.exp_add]; simp
    have hEM : Real.exp (agmonRate d / 2 * τ) * M = Real.exp (agmonRate d / 2 * D0) * Wm := by
      rw [hMdef, ← mul_assoc, ← Real.exp_add]
      congr 2; ring
    have h2 : Wm ≤ K1 * F + 1 / 4 * Wm := by
      calc Wm = Real.exp (agmonRate d / 2 * τ) * S.U xs := rfl
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
  have hinf : ∀ z ∈ G.Ω 1, G.pathDist z S.y' = ⊤ → S.U z = 0 := by
    set Dinf := Finset.univ.filter
      (fun z : Torus d (N₀ * L ^ k) => z ∈ G.Ω 1 ∧ G.pathDist z S.y' = ⊤) with hDinf
    intro z hz hzt
    have hzD : z ∈ Dinf := by simp [hDinf, hz, hzt]
    obtain ⟨xs, hxs, hmax⟩ := Finset.exists_max_image Dinf (fun z => S.U z) ⟨z, hzD⟩
    refine le_antisymm ((hmax z hzD).trans ?_) (S.U_nonneg z)
    obtain ⟨hxsΩ, hxst⟩ : xs ∈ G.Ω 1 ∧ G.pathDist xs S.y' = ⊤ := by
      simpa [hDinf] using hxs
    have hM : ∀ z' ∈ G.Ω 1, G.pathDist z' xs ≤ ENNReal.ofReal D0 → S.U z' ≤ S.U xs := by
      intro z' hz' hdist
      have hzt' : G.pathDist z' S.y' = ⊤ := by
        by_contra hne
        exact (hnear hne (by rw [GeneratingSet.pathDist_comm]; exact hdist)) hxst
      exact hmax z' (by simp [hDinf, hz', hzt'])
    have hbound : ∀ t : ℝ, 0 ≤ t →
        (1 - thetaStar d) * S.U xs ≤ K1 * F * Real.exp (-(agmonRate d / 2 * t)) := by
      intro t ht0
      have := hP G S hMf0 hMf hxsΩ ht0 (by rw [hxst]; exact le_top) (S.U_nonneg xs) hM
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
    have hle : (1 - thetaStar d) * S.U xs ≤ 0 :=
      ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨0, fun t ht => hbound t ht⟩)
    have : 0 < 1 - thetaStar d := by linarith
    nlinarith [S.U_nonneg xs]
  refine ⟨fun hxt => ?_, fun hxt => hinf x hx hxt⟩
  have h := hfin x hx hxt
  calc S.U x = Real.exp (-(agmonRate d / 2 * (G.pathDist x S.y').toReal)) *
        (Real.exp (agmonRate d / 2 * (G.pathDist x S.y').toReal) * S.U x) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (-(agmonRate d / 2 * (G.pathDist x S.y').toReal)) * (2 * K1 * F) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by rw [hF]; ring

end Balaban.Multiscale
