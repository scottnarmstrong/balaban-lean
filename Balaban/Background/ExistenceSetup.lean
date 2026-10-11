/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Approximate
public import Balaban.Background.ContractionAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 5.2: the standing hypotheses, the constants and the reduction to Proposition 5.1

(BACKGROUND.md §5.2, §5.4.)  With `α₀ = 0` and `δΨ = 0`, the Euler–Lagrange system (EL) for the
data `(Ψ, h̃)` is equivalent to the perturbed system (P-1), (P-2) around the approximate field
`φ₀ = approxField` of Lemma 5.3 with `f₁ = residual` (`isPerturbed_iff_isEL`).

* `BgHyp`: the standing hypotheses of Theorem 5.2 on `(G, a, ν)`;
* `bgC0`, `bgC1`, `bgK1`: the constants `c₀`, `c₁`, `K₁`, functions of `(d, L, N)` only;
* `prop51Hyp_of_data`, `strictData_of_data`: Lemma 5.3 supplies the hypotheses of Prop 5.1.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The separation threshold `R₀(d, L)` of Theorem 5.2. -/
noncomputable def bgR0 (d L : ℕ) : ℝ :=
  max (4 * d * L) (1 + 2 * d * Real.log L / (agmonRate d / 2 / 2))

/-- **The standing hypotheses of Theorem 5.2** on a generating set `G` and the weights `a`, mass `ν`
(`ν` is `μ` of BACKGROUND.md in fine units): `d ≥ 3`, `L ≥ 3`, `ϱ ≥ R₀(d, L)`, admissible weights
`a_n ∈ [1/2, 2]`, and `0 ≤ ν ≤ L^{-2k}`. -/
structure BgHyp (d L k : ℕ) (ϱ : ℝ) (a : ℕ → ℝ) (ν : ℝ) : Prop where
  hd : 3 ≤ d
  hL : 3 ≤ L
  hϱ : bgR0 d L ≤ ϱ
  weights : IsAdmissibleWeights k a
  mass : 0 ≤ ν
  massLe : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1

theorem BgHyp.green {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν) :
    GreenSetting G a ν where
  hd := H.hd
  hL := H.hL
  mass := H.mass
  massLe := H.massLe
  weights := H.weights
  sep := by
    have hr : 0 < agmonRate d / 2 / 2 := by
      have := agmonRate_pos (d := d) (by have := H.hd; omega)
      positivity
    have h1 : 1 + 2 * d * Real.log L / (agmonRate d / 2 / 2) ≤ ϱ :=
      (le_max_right _ _).trans H.hϱ
    have h2 : 2 * d * Real.log L / (agmonRate d / 2 / 2) ≤ ϱ - 1 := by linarith
    rw [div_le_iff₀ hr] at h2
    linarith

omit [NeZero L] [NeZero N₀] in
/-- The remaining hypotheses of Lemma 5.3 for data in the domain with parameters `(δ, ε)`. -/
theorem BgHyp.approxSetting {a : ℕ → ℝ} {ν δ ε : ℝ} (H : BgHyp d L k ϱ a ν) (hδ0 : 0 < δ)
    (hδε : δ ≤ ε) (hε : ε ≤ 1 / 16) (hδ : δ ≤ 1 / 1024)
    (hνε : ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2) : ApproxSetting d L k ϱ a ν δ ε where
  hϱ := (le_max_left _ _).trans H.hϱ
  hd := by have := H.hd; omega
  hL := by have := H.hL; omega
  ha := H.weights
  hν0 := H.mass
  hν1 := H.massLe
  hνε := hνε
  hδ0 := hδ0
  hδε := hδε
  hε := hε
  hδ := hδ

/-! ### The constants -/

theorem lemma53Const_pos (d L : ℕ) : 0 < lemma53Const d L :=
  lt_of_lt_of_le (by have := cB7_pos d L; positivity) (cB7_le_const d L)


section Constants

variable (d L N : ℕ) [NeZero L]

/-- The constant `K₁` of Theorem 5.2: `K₁ = C₃ (1 + L + 2 d L² + (2 N + 1) K₂)`,
`C₃ = lemma53Const`, `K₂ = cK2` (Proposition 5.1). -/
noncomputable def bgK1 : ℝ :=
  lemma53Const d L * (1 + L + 2 * d * (L : ℝ) ^ 2 + (2 * N + 1) * cK2 d L N)

/-- The radius `c₀` of Theorem 5.2: `min (c₆, 1/16)`. -/
noncomputable def bgC0 : ℝ := min (c6 d L N) (1 / 16)

/-- The constant `c₁` of Theorem 5.2. -/
noncomputable def bgC1 : ℝ :=
  min (min (approxDelta d L) (deltaStar d L N / (2 * lemma53Const d L)))
    (min (1 / (32 * lemma53Const d L)) (bgC0 d L N / (2 * bgK1 d L N)))

theorem cK2_pos : 0 < cK2 d L N := by
  have := cB1_ge d L
  have := cF_pos d L
  have := cN_pos d L N
  unfold cK2
  positivity

theorem bgK1_pos : 0 < bgK1 d L N := by
  have := lemma53Const_pos d L
  have := cK2_pos d L N
  unfold bgK1
  positivity

theorem bgC0_pos (hd : 0 < d) : 0 < bgC0 d L N := by
  unfold bgC0
  exact lt_min (c6_pos d L N hd) (by norm_num)

theorem bgC0_le_c6 : bgC0 d L N ≤ c6 d L N := min_le_left _ _

theorem bgC0_le : bgC0 d L N ≤ 1 / 16 := min_le_right _ _

/-- The smallness conditions implied by `δ ≤ c₁`. -/
theorem bgC1_facts (hd : 0 < d) {δ : ℝ} (hδ : δ ≤ bgC1 d L N) :
    δ ≤ approxDelta d L ∧ 2 * (lemma53Const d L * δ) ≤ deltaStar d L N ∧
      lemma53Const d L * δ ≤ 1 / 32 ∧ bgK1 d L N * δ ≤ bgC0 d L N / 2 := by
  have hC := lemma53Const_pos d L
  have hK := bgK1_pos d L N
  have h0 := bgC0_pos d L N hd
  unfold bgC1 at hδ
  refine ⟨hδ.trans ((min_le_left _ _).trans (min_le_left _ _)), ?_, ?_, ?_⟩
  · have := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  · have := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  · have := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at this
    linarith

theorem bgK1_ge_one : 1 ≤ bgK1 d L N := by
  have h1 : (500 : ℝ) ≤ lemma53Const d L :=
    le_trans (by have := cB7_pos d L; linarith) (cB7_le_const d L)
  have h2 := cK2_pos d L N
  unfold bgK1
  have : (1 : ℝ) ≤ 1 + L + 2 * d * (L : ℝ) ^ 2 + (2 * N + 1) * cK2 d L N := by
    have : (0 : ℝ) ≤ L + 2 * d * (L : ℝ) ^ 2 + (2 * N + 1) * cK2 d L N := by positivity
    linarith
  nlinarith

theorem bgC1_le_bgC0 (hd : 0 < d) : bgC1 d L N ≤ bgC0 d L N := by
  have h0 := bgC0_pos d L N hd
  have h1 := bgK1_ge_one (d := d) (L := L) (N := N)
  unfold bgC1
  refine (min_le_right _ _).trans ((min_le_right _ _).trans ?_)
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end Constants

section Reduction

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem pertSource_zeroΨ (f₁ : G.Ω 1 × Fin N → ℂ) :
    pertSource G a (0 : Torus d (N₀ * L ^ k) → Fin N → ℂ) f₁ = f₁ := by
  funext p
  simp [pertSource, qStar, boundaryTerm]

/-- With `α₀ = 0` and `δΨ = 0`, the perturbed system around `φ₀` with `f₁ = S - H_D(0) φ₀` is
(EL) for `φ = φ₀ + δφ` and `α = δα`. -/
theorem isPerturbed_iff_isEL (D : BgData G N) (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ) :
    IsPerturbed G a ν (0 : G.Ω 1 → ℂ) φ₀ (residual G a ν D φ₀) δφ δα ↔
      IsEL G a ν D (fun p => φ₀ p.1 p.2 + δφ p) δα := by
  have key : ∀ p : G.Ω 1 × Fin N,
      (liftOp N (dirichletOperator G a ν δα) *ᵥ (fun q => φ₀ q.1 q.2 + δφ q)) p =
        (liftOp N (dirichletOperator G a ν 0) *ᵥ (fun q => φ₀ q.1 q.2)) p +
          (liftOp N (dirichletOperator G a ν 0) *ᵥ δφ) p + δα p.1 * (φ₀ p.1 p.2 + δφ p) := by
    intro p
    have h := liftOp_dirichlet_add (G := G) a ν 0 δα (fun q => φ₀ q.1 q.2 + δφ q) p
    rw [zero_add] at h
    rw [h]
    have e : (fun q : G.Ω 1 × Fin N => φ₀ q.1 q.2 + δφ q) = (fun q => φ₀ q.1 q.2) + δφ := rfl
    rw [e, Matrix.mulVec_add]
    simp only [Pi.add_apply]
  unfold IsPerturbed IsEL
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨funext fun p => ?_, h2⟩
    rw [key p]
    have h := congrFun h1 p
    simp only [Pi.add_apply, residual, Pi.sub_apply] at h
    linear_combination h
  · rintro ⟨h1, h2⟩
    refine ⟨funext fun p => ?_, h2⟩
    have h := congrFun h1 p
    rw [key p] at h
    simp only [Pi.add_apply, residual, Pi.sub_apply]
    linear_combination h

end Reduction

section FromData

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν δ ε : ℝ} {D : BgData G N}

/-- The real data `(Ψ, h₀)` underlying a decomposition `W` of complex data. -/
noncomputable def DataWit.real (W : DataWit G ν δ ε D) : BgData G N :=
  BgData.clip G (fun x i => (W.Ψ x i : ℂ)) (fun _ i => (W.h₀ i : ℂ))
    (fun n hn1 hnk x hx x' hx' => by
      funext i; simp only [W.P.layerConst n hn1 hnk x hx x' hx'])
    (fun _ _ _ _ _ _ _ => rfl)

theorem DataWit.real_Ψ (W : DataWit G ν δ ε D) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites G)
    (i : Fin N) : W.real.Ψ x i = (W.Ψ x i : ℂ) := by
  simp [DataWit.real, BgData.clip, hx]

theorem DataWit.real_h (W : DataWit G ν δ ε D) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (i : Fin N) : W.real.h x i = (W.h₀ i : ℂ) := by
  simp [DataWit.real, BgData.clip, hx]

/-- The data are close to the sphere: `|Ψ + Ψ'| ≤ 1 + ε + 2δ`. -/
theorem DataWit.vn_le (W : DataWit G ν δ ε D) (hδ0 : 0 < δ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ dataSites G) : vn (D.Ψ x) ≤ 1 + δ + (ε + δ) := by
  have e : D.Ψ x = cplx (W.Ψ x) + W.Ψ' x := by
    funext i; simp [cplx, W.hΨ x hx i]
  rw [e]
  refine (vn_add _ _).trans (add_le_add ?_ (W.P.c2a x hx).le)
  rw [vn_eq_cNorm, cNorm_cplx_eq_rn]
  have h2 := W.P.r2 x hx
  unfold rn
  rw [Real.sqrt_le_left (by linarith)]
  have := (abs_lt.1 h2).2
  nlinarith

/-- A vanishing defect `g = 0` has vanishing zero extension and Laplacian. -/
theorem negLap_zeroExt_gdef {φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hg : ∀ x ∈ G.Ω 1, φ₀ x ⬝ᵥ φ₀ x = 1) (x : Torus d (N₀ * L ^ k)) :
    negLap (zeroExt (G.Ω 1) (gdef G φ₀)) x = 0 := by
  have h0 : gdef G φ₀ = 0 := by
    funext y
    have := hg y y.2
    simp only [gdef, Pi.zero_apply]
    rw [sub_eq_zero]; exact this
  have : zeroExt (G.Ω 1) (gdef G φ₀) = 0 := by
    funext y; simp [zeroExt, h0]
  rw [this]; simp [negLap]

/-- **Lemma 5.3 supplies the hypotheses of Proposition 5.1**: for data in `Ψ̃^c(δ, ε)` with
`C₃ δ ≤ δ_*` and `C₃ δ ≤ 1/32`, the approximate field `φ₀`, `α₀ = 0`, `δΨ = 0`, `f₁ = S - H_D(0) φ₀`
satisfy (P1)–(P4) with `δ₀ = δ₁ = C₃ δ`. -/
theorem prop51Hyp_of_data (H : BgHyp d L k ϱ a ν) (S : ApproxSetting d L k ϱ a ν δ ε)
    (hδa : δ ≤ approxDelta d L) (W : DataWit G ν δ ε D)
    (hC : lemma53Const d L * δ ≤ deltaStar d L N) (hC32 : lemma53Const d L * δ ≤ 1 / 32) :
    Prop51Hyp G a ν (0 : G.Ω 1 → ℂ) (approxField G a ν D.Ψ D.h)
      (0 : Torus d (N₀ * L ^ k) → Fin N → ℂ) (residual G a ν D (approxField G a ν D.Ψ D.h))
      (lemma53Const d L * δ) (lemma53Const d L * δ) := by
  have hCδ : 0 ≤ lemma53Const d L * δ := mul_nonneg (lemma53Const_pos d L).le S.hδ0.le
  obtain ⟨g1, g2, g3, -⟩ := lemma53 S hδa D W.real W
    (fun x hx i => W.real_Ψ hx i) (fun x hx i => W.real_h hx i)
  refine ⟨H.green, hCδ, hCδ, hC, hC, g2, fun x hx => ?_, fun x => by simpa using hCδ, fun x i => ?_,
    fun x hx => by simpa [vn_zero] using hCδ, fun x => ?_, fun x => ?_⟩
  · have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have h1 := (g1 x hxd).2
    have h2 := W.vn_le S.hδ0 hxd
    have e : approxField G a ν D.Ψ D.h x = (approxField G a ν D.Ψ D.h x - D.Ψ x) + D.Ψ x := by
      funext i; simp
    rw [e]
    refine (vn_add _ _).trans ?_
    have := S.hε; have := S.hδ
    linarith
  · exact (mul_le_mul_of_nonneg_left (norm_le_vn (fun j => residual G a ν D
      (approxField G a ν D.Ψ D.h) (x, j)) i) (by positivity)).trans (g3 x)
  · have h := (g1 x ((mem_dataSites G).2 (Or.inl x.2))).1
    have e : gdef G (approxField G a ν D.Ψ D.h) x = 0 := by
      simp only [gdef]; rw [sub_eq_zero]; exact h
    rw [e, norm_zero]; exact hCδ
  · rw [negLap_zeroExt_gdef (fun y hy => (g1 y ((mem_dataSites G).2 (Or.inl hy))).1)]
    simpa using hCδ

end FromData

end Balaban.Background
