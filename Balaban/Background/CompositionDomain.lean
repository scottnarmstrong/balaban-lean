/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.CompositionEstimates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The composition domains: Lemma 6.2 (real data) and Lemma 6.3 (complex data)
(BACKGROUND.md §6.6, P2 Lemmas 4.3, 4.4)
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-! ### The weights: `a_p / a_n · L^{2(n-p)} ∈ [0, 1]` -/

omit [NeZero L] in
theorem compWeight_antitone (hL : 2 ≤ L) {a₁ : ℝ} (ha : 0 < a₁) {n p : ℕ} (hn : 1 ≤ n)
    (hnp : n ≤ p) : compWeight L a₁ p ≤ compWeight L a₁ n := by
  have h2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hn' := compWeight_pos hL ha hn
  unfold compWeight at hn' ⊢
  have hlt : (((L : ℝ) ^ 2)⁻¹) < 1 := by
    rw [inv_lt_one₀ (by positivity)]; nlinarith
  have hnum : 0 ≤ a₁ * (1 - (((L : ℝ) ^ 2)⁻¹)) := mul_nonneg ha.le (by linarith)
  have hle : (((L : ℝ) ^ p) ^ 2)⁻¹ ≤ (((L : ℝ) ^ n) ^ 2)⁻¹ := by
    refine inv_anti₀ (by positivity) ?_
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    exact pow_le_pow_right₀ (by linarith) hnp
  have hDn : 0 < 1 - (((L : ℝ) ^ n) ^ 2)⁻¹ := by
    by_contra hcon
    push Not at hcon
    have : a₁ * (1 - (((L : ℝ) ^ 2)⁻¹)) / (1 - (((L : ℝ) ^ n) ^ 2)⁻¹) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos hnum hcon
    linarith
  exact div_le_div_of_nonneg_left hnum hDn (by linarith)

omit [NeZero L] in
theorem compWeight_ratio (hL : 2 ≤ L) {a₁ : ℝ} (ha : 0 < a₁) {n p : ℕ} (hn : 1 ≤ n)
    (hnp : n ≤ p) :
    0 ≤ compWeight L a₁ p / compWeight L a₁ n ∧ compWeight L a₁ p / compWeight L a₁ n ≤ 1 := by
  have h1 := compWeight_pos hL ha hn
  have h2 := compWeight_pos hL ha (hn.trans hnp)
  exact ⟨div_nonneg h2.le h1.le, (div_le_one h1).2 (compWeight_antitone hL ha hn hnp)⟩

omit [NeZero L] in
/-- **The weights of (6.2)**: `a_p / a_n · L^{2(n-p)} ∈ [0, 1]` for `1 ≤ n ≤ p` (this was left open
by the composition identities, which hold for any weights `a_n ≠ 0`). -/
theorem compWeight_kappa_mem (hL : 2 ≤ L) {a₁ : ℝ} (ha : 0 < a₁) {n p : ℕ} (hn : 1 ≤ n)
    (hnp : n ≤ p) :
    0 ≤ compWeight L a₁ p / compWeight L a₁ n * (((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ p) ^ 2) ∧
      compWeight L a₁ p / compWeight L a₁ n * (((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ p) ^ 2) ≤ 1 := by
  obtain ⟨r0, r1⟩ := compWeight_ratio hL ha hn hnp
  have h2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hq0 : 0 ≤ ((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ p) ^ 2 := by positivity
  have hq1 : ((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ p) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith) hnp) 2
  exact ⟨mul_nonneg r0 hq0, (mul_le_of_le_one_left hq0 r1).trans hq1⟩

/-! ### Realness -/

section Real

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

theorem blockMean_im_zero {n : ℕ} (w : Torus d (N₀ * L ^ k) → ℂ) (x : Torus d (N₀ * L ^ k))
    (hw : ∀ y, (w y).im = 0) : (blockMean G n w x).im = 0 := by
  unfold blockMean
  rw [Complex.im_ofReal_mul]
  simp [Complex.im_sum, hw]

theorem mem_collar_of_not_mem (h : Precedes G G') {x : Torus d (N₀ * L ^ k)} (hx : x ∈ collar G)
    (hx' : x ∉ G'.Ω 1) : x ∈ collar G' := by
  obtain ⟨-, z, hz, hadj⟩ := (mem_collar G).1 hx
  exact (mem_collar G').2 ⟨hx', z, h.mem_Ω1 hz, hadj⟩

theorem composeField_im (h : Precedes G G') (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) (hφ : ∀ z i, (φ' (z, i)).im = 0)
    (hΨ : ∀ x ∈ dataSites G', ∀ i, (Ψ' x i).im = 0) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    (composeField G G' a φ' Ψ' x i).im = 0 := by
  by_cases hx : x ∈ G.Ω 1
  · rw [composeField_of_mem a φ' Ψ' hx]
    have hs : ∀ y, (svec G' φ' y i).im = 0 := fun y => by
      by_cases hy : y ∈ G'.Ω 1
      · rw [svec_of_mem' φ' hy]; exact hφ _ _
      · simp [svec, zeroExt, hy]
    have h1 := blockMean_im_zero (G := G) (n := G.layerIndex x) (fun y => svec G' φ' y i) x hs
    have h2 := blockMean_im_zero (G := G') (n := G'.layerIndex x) (fun y => svec G' φ' y i) x hs
    have h3 := hΨ x ((mem_dataSites G').2 (Or.inl (h.mem_Ω1 hx))) i
    rw [Complex.add_im, h1, Complex.im_ofReal_mul]
    simp [Complex.sub_im, h2, h3]
  · by_cases hc : x ∈ collar G
    · rw [composeField_of_collar a φ' Ψ' hc]
      by_cases hx' : x ∈ G'.Ω 1
      · simp only [barField, hx', ↓reduceDIte]; exact hφ _ _
      · simp only [barField, hx', ↓reduceDIte]
        exact hΨ x ((mem_dataSites G').2 (Or.inr (mem_collar_of_not_mem h hc hx'))) i
    · have : x ∉ dataSites G := fun h' => by
        rcases (mem_dataSites G).1 h' with h' | h'
        · exact hx h'
        · exact hc h'
      rw [composeField_of_not_mem a φ' Ψ' this]; simp

/-- **Realness** (item 4): `composeData` is real for real data and a real field `φ'`. -/
theorem composeData_isReal (h : Precedes G G') (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (D' : BgData G' N) (hφ : ∀ z i, (φ' (z, i)).im = 0) (hD : D'.IsReal) :
    (composeData h a φ' D').IsReal := by
  intro x i
  refine ⟨?_, ?_⟩
  · exact composeField_im h a φ' D'.Ψ hφ (fun x _ i => (hD x i).1) x i
  · show ((if x ∈ G.Ω 1 then D'.h x i else 0 : ℂ)).im = 0
    split_ifs
    · exact (hD x i).2
    · simp

end Real

/-! ### Real-vector helpers -/

section RealAux

theorem rn_smul (c : ℝ) (v : Fin N → ℝ) : rn (fun i => c * v i) = |c| * rn v := by
  rw [← vn_ofReal, ← vn_ofReal]
  have := vn_smul_real c (fun i => (v i : ℂ))
  simpa using this

theorem rn_triangle (x y z : Fin N → ℝ) :
    rn (fun i => x i - z i) ≤ rn (fun i => x i - y i) + rn (fun i => y i - z i) := by
  rw [← vn_ofReal, ← vn_ofReal, ← vn_ofReal]
  have h := vn_triangle (fun i => (x i : ℂ)) (fun i => (y i : ℂ)) (fun i => (z i : ℂ))
  have e1 : ((fun i => (x i : ℂ)) - fun i => (z i : ℂ)) = fun i => ((x i - z i : ℝ) : ℂ) := by
    funext i; simp
  have e2 : ((fun i => (x i : ℂ)) - fun i => (y i : ℂ)) = fun i => ((x i - y i : ℝ) : ℂ) := by
    funext i; simp
  have e3 : ((fun i => (y i : ℂ)) - fun i => (z i : ℂ)) = fun i => ((y i - z i : ℝ) : ℂ) := by
    funext i; simp
  rwa [e1, e2, e3] at h

theorem IsRealCVec.norm_dot_sub_one {v : Fin N → ℂ} (h : IsRealCVec v) :
    ‖∑ i, v i * v i - 1‖ = |rn (fun i => (v i).re) ^ 2 - 1| := by
  rw [h.dot_self, rn_sq_sum]
  have : ((∑ i, (v i).re ^ 2 : ℝ) : ℂ) - 1 = (((∑ i, (v i).re ^ 2 : ℝ) - 1 : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs]

theorem IsRealCVec.vn_eq_one {v : Fin N → ℂ} (h : IsRealCVec v) (hv : ∑ i, v i * v i = 1) :
    vn v = 1 := by
  rw [h.vn_eq]
  have h1 : rn (fun i => (v i).re) ^ 2 = 1 := by
    rw [rn_sq_sum]
    have := h.dot_self
    rw [hv] at this
    exact_mod_cast this.symm
  have h2 := rn_nonneg (fun i => (v i).re)
  nlinarith

/-- `1 - u · h = ½ |u - h|² + ½ (1 - |h|²)` for a unit vector `u = Ψ / |Ψ|`, and the bound of
condition (R3) for a vector `Ψ` of length `1 ± b`. -/
theorem r3_core {Ψ h0 : Fin N → ℝ} {s c b E δ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hc : c = s ^ 2)
    (hb : |rn Ψ ^ 2 - 1| ≤ b) (hb2 : b ≤ 1 / 2)
    (hdist : s * rn (fun i => Ψ i - h0 i) ≤ E)
    (hh : c * |∑ i, h0 i ^ 2 - 1| < δ ^ 2) :
    c * |1 - (∑ i, Ψ i * h0 i) / rn Ψ| < (1 / 2) * (b + E) ^ 2 + (1 / 2) * δ ^ 2 := by
  set r := rn Ψ with hr
  have hr0 : 0 ≤ r := rn_nonneg Ψ
  have hb0 : 0 ≤ b := (abs_nonneg _).trans hb
  have hr2 : 1 / 2 ≤ r ^ 2 := by
    have := (abs_le.1 hb).1
    linarith
  have hrpos : 0 < r := by
    rcases hr0.eq_or_lt with h | h
    · rw [← h] at hr2; norm_num at hr2
    · exact h
  set u : Fin N → ℝ := fun i => Ψ i / r with hu
  have hΨ2 : ∑ i, Ψ i ^ 2 = r ^ 2 := (rn_sq_sum Ψ).symm
  have hid : 1 - (∑ i, Ψ i * h0 i) / r =
      (1 / 2) * rn (fun i => u i - h0 i) ^ 2 + (1 / 2) * (1 - ∑ i, h0 i ^ 2) := by
    rw [rn_sq_sum]
    have e1 : ∑ i, (u i - h0 i) ^ 2 =
        ∑ i, (Ψ i ^ 2 / r ^ 2 - 2 * (Ψ i * h0 i / r) + h0 i ^ 2) :=
      Finset.sum_congr rfl fun i _ => by simp only [hu]; field_simp; ring
    rw [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum,
      ← Finset.sum_div, hΨ2, div_self (by positivity)]
    ring
  have hur : rn (fun i => u i - Ψ i) = |1 - r| := by
    have : (fun i => u i - Ψ i) = fun i => (1 / r - 1) * Ψ i := by
      funext i; simp only [hu]; field_simp
    rw [this, rn_smul]
    have : |1 / r - 1| * r = |1 - r| := by
      rw [show 1 / r - 1 = (1 - r) / r by field_simp, abs_div, abs_of_pos hrpos]
      field_simp
    rw [← hr] at *
    exact this
  have h1r : |1 - r| ≤ b := by
    have h2 : |1 - r ^ 2| = |1 - r| * (1 + r) := by
      rw [show 1 - r ^ 2 = (1 - r) * (1 + r) by ring, abs_mul,
        abs_of_pos (show (0 : ℝ) < 1 + r by linarith)]
    have h3 : |1 - r ^ 2| ≤ b := by rwa [abs_sub_comm]
    nlinarith [abs_nonneg (1 - r)]
  have htri := rn_triangle u Ψ h0
  have hsrn : s * rn (fun i => u i - h0 i) ≤ b + E := by
    calc s * rn (fun i => u i - h0 i) ≤ s * (|1 - r| + rn (fun i => Ψ i - h0 i)) := by
          apply mul_le_mul_of_nonneg_left _ hs0
          rw [hur] at htri; exact htri
      _ = s * |1 - r| + s * rn (fun i => Ψ i - h0 i) := by ring
      _ ≤ 1 * b + E := add_le_add (mul_le_mul hs1 h1r (abs_nonneg _) zero_le_one) hdist
      _ = b + E := by ring
  have hs_nn : 0 ≤ s * rn (fun i => u i - h0 i) := mul_nonneg hs0 (rn_nonneg _)
  rw [hid]
  calc c * |(1 / 2) * rn (fun i => u i - h0 i) ^ 2 + (1 / 2) * (1 - ∑ i, h0 i ^ 2)|
      ≤ c * ((1 / 2) * rn (fun i => u i - h0 i) ^ 2 + (1 / 2) * |∑ i, h0 i ^ 2 - 1|) := by
        apply mul_le_mul_of_nonneg_left _ (by rw [hc]; positivity)
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2) * rn (fun i => u i - h0 i) ^ 2),
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_sub_comm]
    _ = (1 / 2) * (s * rn (fun i => u i - h0 i)) ^ 2 + (1 / 2) * (c * |∑ i, h0 i ^ 2 - 1|) := by
        rw [hc]; ring
    _ < (1 / 2) * (b + E) ^ 2 + (1 / 2) * δ ^ 2 := by
        have : (s * rn (fun i => u i - h0 i)) ^ 2 ≤ (b + E) ^ 2 :=
          pow_le_pow_left₀ hs_nn hsrn 2
        linarith

theorem rn_re_sub_eq_vn {u v : Fin N → ℂ} (hu : IsRealCVec u) (hv : IsRealCVec v) :
    rn (fun i => (u i).re - (v i).re) = vn (u - v) := by
  have h : IsRealCVec (u - v) := fun i => by simp [hu i, hv i]
  rw [h.vn_eq]
  simp

theorem rn_re_sub_cast_eq_vn {u : Fin N → ℂ} (hu : IsRealCVec u) (h0 : Fin N → ℝ) :
    rn (fun i => (u i).re - h0 i) = vn (u - fun i => (h0 i : ℂ)) := by
  have h : IsRealCVec (u - fun i => (h0 i : ℂ)) := fun i => by simp [hu i]
  rw [h.vn_eq]
  simp

theorem vn_cast_sub (u v : Fin N → ℝ) :
    vn ((fun i => (u i : ℂ)) - fun i => (v i : ℂ)) = rn (fun i => u i - v i) := by
  rw [← vn_ofReal]
  congr 1
  funext i; simp

end RealAux

/-! ### Real estimates (shared by Lemma 6.2 and (R-S)) -/

section RealEstimates

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {θ η : ℝ}
  {a : ℕ → ℝ} {Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φ' : G'.Ω 1 × Fin N → ℂ}

theorem compVec_collar (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ collar G) :
    compVec G G' a φ' Ψ' x = barVec G' Ψ' φ' x := by
  funext i
  exact composeField_of_collar a φ' Ψ' hx i

theorem compVec_isReal (h : Precedes G G') (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) (hφ : ∀ z i, (φ' (z, i)).im = 0)
    (hΨ : ∀ x ∈ dataSites G', ∀ i, (Ψ' x i).im = 0) (x : Torus d (N₀ * L ^ k)) :
    IsRealCVec (compVec G G' a φ' Ψ' x) := fun i => composeField_im h a φ' Ψ' hφ hΨ x i

/-- On `Ω'₁` the field `φ̄'` is `φ'`; a real unit field has `|φ'| = 1`. -/
theorem barVec_vn_eq_one (hφ : ∀ z i, (φ' (z, i)).im = 0)
    (hu : ∀ z : G'.Ω 1, ∑ i, φ' (z, i) * φ' (z, i) = 1) (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G'.Ω 1) : vn (barVec G' Ψ' φ' y) = 1 := by
  have e : barVec G' Ψ' φ' y = fun i => φ' (⟨y, hy⟩, i) := by
    funext i; exact barVec_of_mem Ψ' φ' hy i
  rw [e]
  exact IsRealCVec.vn_eq_one (fun i => hφ _ i) (hu ⟨y, hy⟩)

/-- **(R2)-type estimate** at a site of `Ω₁`: `| |Ψ|² - 1 | ≤ (2dθη)² + 2θ²η + θ⁴η²`. -/
theorem CompHyp.re_r2 (H : CompHyp G G' a θ η Ψ' φ') (hφ : ∀ z i, (φ' (z, i)).im = 0)
    (hΨ : ∀ x ∈ dataSites G', ∀ i, (Ψ' x i).im = 0) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) :
    |rn (fun i => (compVec G G' a φ' Ψ' x i).re) ^ 2 - 1| ≤
      (2 * d * (θ * η)) ^ 2 + 2 * θ ^ 2 * 1 * η + (θ ^ 2) ^ 2 * η ^ 2 := by
  have hreal := compVec_isReal H.prec a φ' Ψ' hφ hΨ x
  rw [← hreal.norm_dot_sub_one]
  exact H.dot_sub_one hx (M := 1) (fun y hy =>
    (barVec_vn_eq_one hφ H.bounds.unit Ψ' (blk_mem_Ω1' H.prec hx hy).2).le)

theorem sqrt_mul_spacing_le_one {ν : ℝ} (hν : 0 ≤ ν) (hνk : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (G : GeneratingSet d L N₀ k ϱ) (x : Torus d (N₀ * L ^ k)) :
    Real.sqrt ν * G.spacing x ≤ 1 := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h1 : G.spacing x ≤ (L : ℝ) ^ k := pow_le_pow_right₀ hL (layerIndex_le_k G x)
  have h0 : 0 ≤ G.spacing x := (G.spacing_ge_one x).trans' zero_le_one
  have h2 : (Real.sqrt ν * G.spacing x) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt hν]
    calc ν * G.spacing x ^ 2 ≤ ν * ((L : ℝ) ^ k) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 2) hν
      _ ≤ 1 := hνk
  nlinarith [mul_nonneg (Real.sqrt_nonneg ν) h0]

/-- **(R3)-type distance** at a site of `Ω₁`: `√ν ℓ(x) |Ψ(x) - h| ≤ θη + θ²η`, given the
bound `√ν ℓ'(z) |φ'(z) - h| ≤ η`. -/
theorem CompHyp.re_dist (H : CompHyp G G' a θ η Ψ' φ') (hφ : ∀ z i, (φ' (z, i)).im = 0)
    (hΨ : ∀ x ∈ dataSites G', ∀ i, (Ψ' x i).im = 0) {ν : ℝ} (hν : 0 ≤ ν)
    (hνk : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) (h0 : Fin N → ℝ)
    (hmass : ∀ z : G'.Ω 1, Real.sqrt ν * G'.spacing z * vn (fun i => φ' (z, i) - (h0 i : ℂ)) ≤ η)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    Real.sqrt ν * G.spacing x * rn (fun i => (compVec G G' a φ' Ψ' x i).re - h0 i) ≤
      θ * η + θ ^ 2 * η := by
  obtain ⟨-, hnk, -⟩ := G.layerIndex_spec hx
  set s := Real.sqrt ν * G.spacing x with hs
  have hs0 : 0 ≤ s := mul_nonneg (Real.sqrt_nonneg ν) (G.spacing_ge_one x |>.trans' zero_le_one)
  have hs1 : s ≤ 1 := sqrt_mul_spacing_le_one hν hνk G x
  have hreal := compVec_isReal H.prec a φ' Ψ' hφ hΨ x
  have hv : IsRealCVec (compVec G G' a φ' Ψ' x - fun i => (h0 i : ℂ)) := fun i => by
    simp [hreal i]
  have e : rn (fun i => (compVec G G' a φ' Ψ' x i).re - h0 i) =
      vn (compVec G G' a φ' Ψ' x - fun i => (h0 i : ℂ)) := by
    rw [hv.vn_eq]
    congr 1
  rw [e]
  have h1 := H.compVec_sub_mean hx
  have h2 : s * vn (fun i => blockMean G (G.layerIndex x) (fun y => barVec G' Ψ' φ' y i) x -
      (h0 i : ℂ)) ≤ θ * η := by
    refine vn_blockMean_sub_le_scaled (G := G) hnk (barVec G' Ψ' φ') x (fun i => (h0 i : ℂ))
      hs0 (fun y hy => ?_)
    obtain ⟨hy1, hy2⟩ := blk_mem_Ω1' H.prec hx hy
    have hyl := blk_mem_layer hx hy
    have hsp : G.spacing y = G.spacing x := by
      unfold GeneratingSet.spacing
      rw [G.layerIndex_eq (G.layerIndex_spec hx).1 hnk hyl]
    have hm := hmass ⟨y, hy2⟩
    have e2 : (fun i => barVec G' Ψ' φ' y i - (h0 i : ℂ)) = fun i => φ' (⟨y, hy2⟩, i) - (h0 i : ℂ) := by
      funext i; rw [barVec_of_mem Ψ' φ' hy2]
    rw [e2]
    have hg := H.gap y hy1
    have hν0 := Real.sqrt_nonneg ν
    calc s * vn (fun i => φ' (⟨y, hy2⟩, i) - (h0 i : ℂ))
        = Real.sqrt ν * G.spacing y * vn (fun i => φ' (⟨y, hy2⟩, i) - (h0 i : ℂ)) := by
          rw [hs, hsp]
      _ ≤ Real.sqrt ν * (θ * G'.spacing y) * vn (fun i => φ' (⟨y, hy2⟩, i) - (h0 i : ℂ)) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hν0) (vn_nonneg _)
      _ = θ * (Real.sqrt ν * G'.spacing y * vn (fun i => φ' (⟨y, hy2⟩, i) - (h0 i : ℂ))) := by
          ring
      _ ≤ θ * η := mul_le_mul_of_nonneg_left hm H.θ_pos.le
  have h3 := vn_triangle (compVec G G' a φ' Ψ' x) (meanVec G (barVec G' Ψ' φ') x)
    (fun i => (h0 i : ℂ))
  calc s * vn (compVec G G' a φ' Ψ' x - fun i => (h0 i : ℂ))
      ≤ s * (vn (compVec G G' a φ' Ψ' x - meanVec G (barVec G' Ψ' φ') x) +
          vn (meanVec G (barVec G' Ψ' φ') x - fun i => (h0 i : ℂ))) :=
        mul_le_mul_of_nonneg_left h3 hs0
    _ = s * vn (compVec G G' a φ' Ψ' x - meanVec G (barVec G' Ψ' φ') x) +
          s * vn (fun i => blockMean G (G.layerIndex x) (fun y => barVec G' Ψ' φ' y i) x -
            (h0 i : ℂ)) := by
        rw [mul_add]; rfl
    _ ≤ 1 * (θ ^ 2 * η) + θ * η := add_le_add
        (mul_le_mul hs1 h1 (vn_nonneg _) zero_le_one) h2
    _ = θ * η + θ ^ 2 * η := by ring

/-- **(R3)** at a site of `Ω₁`, for the real part of the composed field. -/
theorem CompHyp.re_r3 (H : CompHyp G G' a θ η Ψ' φ') (hφ : ∀ z i, (φ' (z, i)).im = 0)
    (hΨ : ∀ x ∈ dataSites G', ∀ i, (Ψ' x i).im = 0) {ν δ₄ : ℝ} (hν : 0 ≤ ν)
    (hνk : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) (h0 : Fin N → ℝ)
    (hmass : ∀ z : G'.Ω 1, Real.sqrt ν * G'.spacing z * vn (fun i => φ' (z, i) - (h0 i : ℂ)) ≤ η)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (hb2 : (2 * d * (θ * η)) ^ 2 + 2 * θ ^ 2 * 1 * η + (θ ^ 2) ^ 2 * η ^ 2 ≤ 1 / 2)
    (hh : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * |∑ i, h0 i ^ 2 - 1| < δ₄ ^ 2) :
    ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
      |1 - (∑ i, (compVec G G' a φ' Ψ' x i).re * h0 i) /
        rn (fun i => (compVec G G' a φ' Ψ' x i).re)| <
      (1 / 2) * (((2 * d * (θ * η)) ^ 2 + 2 * θ ^ 2 * 1 * η + (θ ^ 2) ^ 2 * η ^ 2) +
        (θ * η + θ ^ 2 * η)) ^ 2 + (1 / 2) * δ₄ ^ 2 := by
  have hxc : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 = (Real.sqrt ν * G.spacing x) ^ 2 := by
    unfold GeneratingSet.spacing; rw [mul_pow, Real.sq_sqrt hν]
  have hs0 : 0 ≤ Real.sqrt ν * G.spacing x :=
    mul_nonneg (Real.sqrt_nonneg ν) ((G.spacing_ge_one x).trans' zero_le_one)
  exact r3_core (Ψ := fun i => (compVec G G' a φ' Ψ' x i).re) (h0 := h0) hs0
    (sqrt_mul_spacing_le_one hν hνk G x) hxc (H.re_r2 hφ hΨ hx) hb2
    (H.re_dist hφ hΨ hν hνk h0 hmass hx) hh

/-- **(R3)** at a collar site of `Ω'₁` (where `Ψ = φ'`, a unit vector): the bound
`ν |1 - φ'·h| < ½ (θη)² + ½ δ₄²`, if `ℓ(x) ≤ θ ℓ'(x)`. -/
theorem CompHyp.re_r3_collar (H : CompHyp G G' a θ η Ψ' φ') (hφ : ∀ z i, (φ' (z, i)).im = 0)
    (hΨ : ∀ x ∈ dataSites G', ∀ i, (Ψ' x i).im = 0) {ν δ₄ : ℝ} (hν : 0 ≤ ν)
    (hνk : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) (h0 : Fin N → ℝ)
    (hmass : ∀ z : G'.Ω 1, Real.sqrt ν * G'.spacing z * vn (fun i => φ' (z, i) - (h0 i : ℂ)) ≤ η)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ collar G) (hx' : x ∈ G'.Ω 1)
    (hgap : G.spacing x ≤ θ * G'.spacing x)
    (hh : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * |∑ i, h0 i ^ 2 - 1| < δ₄ ^ 2) :
    ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
      |1 - (∑ i, (compVec G G' a φ' Ψ' x i).re * h0 i) /
        rn (fun i => (compVec G G' a φ' Ψ' x i).re)| <
      (1 / 2) * (0 + θ * η) ^ 2 + (1 / 2) * δ₄ ^ 2 := by
  have hxc : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 = (Real.sqrt ν * G.spacing x) ^ 2 := by
    unfold GeneratingSet.spacing; rw [mul_pow, Real.sq_sqrt hν]
  have hs0 : 0 ≤ Real.sqrt ν * G.spacing x :=
    mul_nonneg (Real.sqrt_nonneg ν) ((G.spacing_ge_one x).trans' zero_le_one)
  have hreal := compVec_isReal H.prec a φ' Ψ' hφ hΨ x
  have hu : rn (fun i => (compVec G G' a φ' Ψ' x i).re) = 1 := by
    have h1 : vn (compVec G G' a φ' Ψ' x) = 1 := by
      rw [compVec_collar a φ' Ψ' hx]
      exact barVec_vn_eq_one hφ H.bounds.unit Ψ' hx'
    rwa [hreal.vn_eq] at h1
  have hb0 : |rn (fun i => (compVec G G' a φ' Ψ' x i).re) ^ 2 - 1| ≤ 0 := by rw [hu]; norm_num
  have hdist : Real.sqrt ν * G.spacing x *
      rn (fun i => (compVec G G' a φ' Ψ' x i).re - h0 i) ≤ θ * η := by
    rw [rn_re_sub_cast_eq_vn hreal h0, compVec_collar a φ' Ψ' hx]
    have e2 : barVec G' Ψ' φ' x - (fun i => (h0 i : ℂ)) =
        fun i => φ' (⟨x, hx'⟩, i) - (h0 i : ℂ) := by
      funext i; simp [barVec_of_mem Ψ' φ' hx']
    rw [e2]
    have := hmass ⟨x, hx'⟩
    calc _ ≤ Real.sqrt ν * (θ * G'.spacing x) *
          vn (fun i => φ' (⟨x, hx'⟩, i) - (h0 i : ℂ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap (Real.sqrt_nonneg ν))
            (vn_nonneg _)
      _ = θ * (Real.sqrt ν * G'.spacing x * vn (fun i => φ' (⟨x, hx'⟩, i) - (h0 i : ℂ))) := by
          ring
      _ ≤ θ * η := mul_le_mul_of_nonneg_left this H.θ_pos.le
  exact r3_core (Ψ := fun i => (compVec G G' a φ' Ψ' x i).re) (h0 := h0) hs0
    (sqrt_mul_spacing_le_one hν hνk G x) hxc hb0 (by norm_num) hdist hh

end RealEstimates

/-! ### Lemma 6.2 -/

section Lemma62

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

/-- The constant `C₄ = C₄(d)` of Lemma 6.2 (P2 (4.29)): the domain `Ψ̃(𝔹_j; C₄ K₁ δ)`. -/
noncomputable def compC4 (d : ℕ) : ℝ := 4 * d + 8

/-- **Lemma 6.2, core form** (P2 Lemma 4.3; BACKGROUND.md §6.6).  Let `(Ψ0, h0) ∈ Ψ̃(𝔹'_k; δ)` be
real data (`hP`), `Ψ'` a block-constant lifted field equal to `Ψ0` on `Ω'₁ ∪ C(Ω'₁)`, and `φ'` a
real field satisfying the bounds of Theorem 5.2 (3) with constant `K₁` (`FieldBounds`:
`|φ' - Q*Ψ'|₀ ≤ K₁δ`, `|∂φ̄'|₁, |Δφ̄'|₂ ≤ K₁δ`, `φ'·φ' = 1`) and the (R3)-type bound
`√ν ℓ'|φ' - h0| ≤ K₁δ` (`hmass`).  Then the real part of the composed field (6.2) and `h0` lie in
`Ψ̃(𝔹_j; C₄ K₁ δ)`, `C₄ = 4d + 6`.  The remaining hypotheses are the standing assumptions of the
notes: `K₁ ≥ 1`, `ν L^{2k} ≤ 1`, and the smallness `(4d + 6) K₁ δ ≤ 1`. -/
theorem lemma62_core (hL : 2 ≤ L) (h : Precedes G G') {a₁ : ℝ} (ha₁ : 0 < a₁) {ν δ K₁ : ℝ}
    (hK₁ : 1 ≤ K₁) (hδ : 0 < δ) (hsmall : (4 * d + 6) * (K₁ * δ) ≤ 1) (hν : 0 ≤ ν)
    (hνk : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) {Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h0 : Fin N → ℝ}
    (hP : InPsiTilde G' ν δ Ψ0 h0) (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hΨ'c : IsLayerConstant G' Ψ') (hΨ0 : ∀ x ∈ dataSites G', ∀ i, Ψ' x i = (Ψ0 x i : ℂ))
    (φ' : G'.Ω 1 × Fin N → ℂ) (hφ : ∀ z i, (φ' (z, i)).im = 0)
    (hb : FieldBounds G' (K₁ * δ) Ψ' φ')
    (hmass : ∀ z : G'.Ω 1,
      Real.sqrt ν * G'.spacing z * vn (fun i => φ' (z, i) - (h0 i : ℂ)) ≤ K₁ * δ) :
    InPsiTilde G ν (compC4 d * (K₁ * δ))
      (fun x i => (compVec G G' (compWeight L a₁) φ' Ψ' x i).re) h0 := by
  set η := K₁ * δ with hη
  have hηpos : 0 < η := mul_pos (by linarith) hδ
  have hδη : δ ≤ η := by nlinarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hC4 : compC4 d * η = (4 * d + 8) * η := rfl
  set a := compWeight L a₁ with ha
  have H : CompHyp G G' a 1 η Ψ' φ' :=
    { prec := h, θ_pos := one_pos, η_nn := hηpos.le, gap := scaleGap_one h,
      ratio := fun x hx => compWeight_ratio hL ha₁ (G.layerIndex_spec hx).1
        (h.layerIndex_le hx)
      layerConst := hΨ'c, bounds := hb }
  have hΨreal : ∀ x ∈ dataSites G', ∀ i, (Ψ' x i).im = 0 := fun x hx i => by
    rw [hΨ0 x hx i]; simp
  have hreal := compVec_isReal h a φ' Ψ' hφ hΨreal
  have hmass0 := hmass
  set Ψo : Torus d (N₀ * L ^ k) → Fin N → ℝ := fun x i => (compVec G G' a φ' Ψ' x i).re
    with hΨo
  have hcast : ∀ x i, compVec G G' a φ' Ψ' x i = (Ψo x i : ℂ) := fun x i =>
    congrFun (hreal x).eq_ofReal i
  -- smallness consequences
  have hsm1 : (2 * d + 3) * η ≤ 1 / 2 := by nlinarith
  have hs2 : (2 * d * (1 * η)) ^ 2 + 2 * 1 ^ 2 * 1 * η + (1 ^ 2) ^ 2 * η ^ 2 ≤ (2 * d + 3) * η := by
    nlinarith [mul_nonneg hd0 hηpos.le]
  have hR2 : ∀ x ∈ G.Ω 1, |rn (Ψo x) ^ 2 - 1| ≤ (2 * d + 3) * η := fun x hx =>
    (H.re_r2 hφ hΨreal hx).trans hs2
  have hunitcol : ∀ x ∈ collar G, x ∈ G'.Ω 1 → rn (Ψo x) = 1 := by
    intro x hx hx'
    have h1 : vn (compVec G G' a φ' Ψ' x) = 1 := by
      rw [compVec_collar a φ' Ψ' hx]
      exact barVec_vn_eq_one hφ hb.unit Ψ' hx'
    rwa [(hreal x).vn_eq] at h1
  -- (R1)
  have hB : ∀ z z', z ∈ dataSites G → z' ∈ dataSites G → Adj z z' →
      vn (barVec G' Ψ' φ' z - barVec G' Ψ' φ' z') ≤ η := by
    intro z z' hz hz' hadj
    by_cases hz2 : z ∈ G'.Ω 1
    · rw [vn_sub_comm]; exact H.bond_out hz2 hadj
    · by_cases hz2' : z' ∈ G'.Ω 1
      · exact H.bond_out hz2' hadj.symm
      · have hc : z ∈ collar G := by
          rcases (mem_dataSites G).1 hz with h1 | h1
          · exact absurd (h.mem_Ω1 h1) hz2
          · exact h1
        have hc' : z' ∈ collar G := by
          rcases (mem_dataSites G).1 hz' with h1 | h1
          · exact absurd (h.mem_Ω1 h1) hz2'
          · exact h1
        have hc1 := mem_collar_of_not_mem h hc hz2
        have hc1' := mem_collar_of_not_mem h hc' hz2'
        have hip : IsInterfacePair G' z z' :=
          ⟨(mem_dataSites G').2 (Or.inr hc1), (mem_dataSites G').2 (Or.inr hc1'),
            Or.inl (by rw [layerIndex_of_not_mem G' hz2, layerIndex_of_not_mem G' hz2']),
            z, by rw [blockSet_of_not_mem G' hz2]; simp,
            z', by rw [blockSet_of_not_mem G' hz2']; simp, hadj⟩
        have h1 := hP.r1 z z' hip
        have e : barVec G' Ψ' φ' z - barVec G' Ψ' φ' z' =
            (fun i => (Ψ0 z i : ℂ)) - fun i => (Ψ0 z' i : ℂ) := by
          funext i
          simp only [Pi.sub_apply, barVec_of_not_mem Ψ' φ' hz2,
            barVec_of_not_mem Ψ' φ' hz2',
            hΨ0 z ((mem_dataSites G').2 (Or.inr hc1)),
            hΨ0 z' ((mem_dataSites G').2 (Or.inr hc1'))]
        rw [e, vn_cast_sub]
        linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- layer constancy
    intro n hn1 hnk x hx x' hx'
    funext i
    have := congrFun (composeField_layerConst h a φ' hΨ'c n hn1 hnk x hx x' hx') i
    exact congrArg Complex.re this
  · -- (R1)
    intro x x' hxx'
    have h1 := H.interface hxx' hB
    rw [rn_re_sub_eq_vn (hreal x) (hreal x')]
    have : 2 * ((2 * (d : ℝ) + 1) * (1 * η)) + η < compC4 d * η := by
      rw [hC4]; nlinarith
    linarith
  · -- (R2)
    intro x hx
    rcases (mem_dataSites G).1 hx with hx | hx
    · have := hR2 x hx
      rw [rn_sq_sum] at this
      refine this.trans_lt ?_
      rw [hC4]; nlinarith
    · have hn : x ∉ G.Ω 1 := ((mem_collar G).1 hx).1
      by_cases hx' : x ∈ G'.Ω 1
      · have : ∑ i, Ψo x i ^ 2 = 1 := by
          rw [← rn_sq_sum, hunitcol x hx hx']; norm_num
        rw [this]; simp; rw [hC4]; positivity
      · have hc1 := mem_collar_of_not_mem h hx hx'
        have hds : x ∈ dataSites G' := (mem_dataSites G').2 (Or.inr hc1)
        have e : ∀ i, Ψo x i = Ψ0 x i := fun i => by
          have : (compVec G G' a φ' Ψ' x i) = Ψ' x i := by
            rw [compVec_collar a φ' Ψ' hx]
            exact barVec_of_not_mem Ψ' φ' hx' i
          simp only [hΨo, this, hΨ0 x hds i, Complex.ofReal_re]
        simp only [e]
        have := hP.r2 x hds
        refine this.trans_le ?_
        rw [hC4]; nlinarith
  · -- (R3)
    intro x hx
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    have hh : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * |∑ i, h0 i ^ 2 - 1| < δ ^ 2 := by
      refine lt_of_le_of_lt ?_ hP.r4
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (pow_le_pow_right₀ hL1 (layerIndex_le_k G x)) 2) hν
    have hfin : ∀ {E b : ℝ}, 0 ≤ b → b ≤ (2 * d + 3) * η → E ≤ 2 * η →
        0 ≤ E → ((1 / 2) * (b + E) ^ 2 + (1 / 2) * δ ^ 2) ≤ (compC4 d * η) ^ 2 := by
      intro E b hb0 hb1 hE1 hE0
      have h1 : (b + E) ^ 2 ≤ ((2 * d + 5) * η) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by nlinarith) 2
      have h2 : δ ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hδ.le hδη 2
      rw [hC4]
      nlinarith [sq_nonneg η, mul_nonneg hd0 hηpos.le, sq_nonneg (d * η)]
    rcases (mem_dataSites G).1 hx with hx | hx
    · have hb2 : (2 * d * (1 * η)) ^ 2 + 2 * 1 ^ 2 * 1 * η + (1 ^ 2) ^ 2 * η ^ 2 ≤ 1 / 2 :=
        hs2.trans hsm1
      have := H.re_r3 hφ hΨreal hν hνk h0 hmass0 hx hb2 hh
      exact this.trans_le (hfin (E := 1 * η + 1 ^ 2 * η)
        (b := (2 * d * (1 * η)) ^ 2 + 2 * 1 ^ 2 * 1 * η + (1 ^ 2) ^ 2 * η ^ 2)
        (by positivity) hs2 (by linarith) (by positivity))
    · have hn : x ∉ G.Ω 1 := ((mem_collar G).1 hx).1
      by_cases hx' : x ∈ G'.Ω 1
      · have hgs : G.spacing x ≤ 1 * G'.spacing x := by
          have : G.spacing x = 1 := by
            unfold GeneratingSet.spacing; rw [layerIndex_of_not_mem G hn]; simp
          rw [this, one_mul]; exact G'.spacing_ge_one x
        have := H.re_r3_collar hφ hΨreal hν hνk h0 hmass0 hx hx' hgs hh
        exact this.trans_le (hfin (E := 1 * η) (b := 0) le_rfl (by positivity) (by linarith)
          (by positivity))
      · have hc1 := mem_collar_of_not_mem h hx hx'
        have hds : x ∈ dataSites G' := (mem_dataSites G').2 (Or.inr hc1)
        have e : ∀ i, Ψo x i = Ψ0 x i := fun i => by
          have : (compVec G G' a φ' Ψ' x i) = Ψ' x i := by
            rw [compVec_collar a φ' Ψ' hx]
            exact barVec_of_not_mem Ψ' φ' hx' i
          simp only [hΨo, this, hΨ0 x hds i, Complex.ofReal_re]
        have h1 := hP.r3 x hds
        have hl : G.layerIndex x = 0 := layerIndex_of_not_mem G hn
        have hl' : G'.layerIndex x = 0 := layerIndex_of_not_mem G' hx'
        rw [hl'] at h1
        rw [show Ψo x = Ψ0 x from funext e, hl]
        refine h1.trans_le ?_
        have h2 : δ ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hδ.le hδη 2
        rw [hC4]
        nlinarith [sq_nonneg η, mul_nonneg hd0 hηpos.le, sq_nonneg (d * η)]
  · -- (R4)
    have := hP.r4
    refine this.trans_le ?_
    rw [hC4]
    nlinarith

/-- **Lemma 6.2** (P2 Lemma 4.3; BACKGROUND.md §6.6), for `BgData`.  For real data
`(Ψ', h) ∈ Ψ̃(𝔹'_k; δ)` and a real field `φ'` with the bounds of Theorem 5.2 (3) (taken as
hypotheses: `FieldBounds`, and the (R3)-type bound `hmass`), the composed datum (6.2),
`composeData`, lies in `Ψ̃(𝔹_j; C₄ K₁ δ)`, `C₄ = 4d + 6`; it is real. -/
theorem lemma62 (hL : 2 ≤ L) (h : Precedes G G') {a₁ : ℝ} (ha₁ : 0 < a₁) {ν δ K₁ : ℝ}
    (hK₁ : 1 ≤ K₁) (hδ : 0 < δ) (hsmall : (4 * d + 6) * (K₁ * δ) ≤ 1) (hν : 0 ≤ ν)
    (hνk : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) (D' : BgData G' N) (hD' : InDomainR G' ν δ D')
    (φ' : G'.Ω 1 × Fin N → ℂ) (hφ : ∀ z i, (φ' (z, i)).im = 0)
    (hb : FieldBounds G' (K₁ * δ) D'.Ψ φ')
    (hmass : ∀ z : G'.Ω 1,
      Real.sqrt ν * G'.spacing z * vn (fun i => φ' (z, i) - D'.h z i) ≤ K₁ * δ) :
    InDomainR G ν (compC4 d * (K₁ * δ)) (composeData h (compWeight L a₁) φ' D') ∧
      (composeData h (compWeight L a₁) φ' D').IsReal := by
  obtain ⟨Ψ0, h0, hP, hΨ0, hh0⟩ := hD'
  have hmass0 : ∀ z : G'.Ω 1,
      Real.sqrt ν * G'.spacing z * vn (fun i => φ' (z, i) - (h0 i : ℂ)) ≤ K₁ * δ := by
    intro z
    have := hmass z
    have e : (fun i => φ' (z, i) - D'.h z i) = fun i => φ' (z, i) - (h0 i : ℂ) := by
      funext i; rw [hh0 z z.2 i]
    rwa [e] at this
  have hΨreal : ∀ x ∈ dataSites G', ∀ i, (D'.Ψ x i).im = 0 := fun x hx i => by
    rw [hΨ0 x hx i]; simp
  have hcore := lemma62_core hL h ha₁ hK₁ hδ hsmall hν hνk hP D'.Ψ D'.Ψ_layerConst hΨ0 φ' hφ
    hb hmass0
  refine ⟨⟨_, h0, hcore, ?_, ?_⟩, ?_⟩
  · intro x _ i
    exact congrFun (compVec_isReal h (compWeight L a₁) φ' D'.Ψ hφ hΨreal x).eq_ofReal i
  · intro x hx i
    show (if x ∈ G.Ω 1 then D'.h x i else 0 : ℂ) = _
    simp only [hx, ↓reduceIte]
    exact hh0 x (h.mem_Ω1 hx) i
  · refine composeData_isReal h _ φ' D' hφ ?_
    intro x i
    refine ⟨?_, ?_⟩
    · by_cases hx : x ∈ dataSites G'
      · exact hΨreal x hx i
      · rw [D'.Ψ_zero x hx]; simp
    · by_cases hx : x ∈ G'.Ω 1
      · rw [hh0 x hx i]; simp
      · rw [D'.h_zero x hx]; simp

end Lemma62

/-! ### Lemma 6.3: helpers -/

section Lemma63Aux

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

theorem rn_add' (x y : Fin N → ℝ) : rn (fun i => x i + y i) ≤ rn x + rn y := by
  rw [← vn_ofReal, ← vn_ofReal, ← vn_ofReal]
  have := vn_add' (fun i => (x i : ℂ)) (fun i => (y i : ℂ))
  simpa using this

theorem rn_zero_sub (a : Fin N → ℝ) : rn (fun i => a i - 0) = rn a := by simp

/-- Normalization is Lipschitz: `|a/|a| - b/|b|| ≤ 2 |a - b| / |a|`. -/
theorem rn_normalize_sub (a b : Fin N → ℝ) (ha : 0 < rn a) (hb : 0 < rn b) :
    rn (fun i => a i / rn a - b i / rn b) ≤ 2 * rn (fun i => a i - b i) / rn a := by
  have e : (fun i => a i / rn a - b i / rn b) =
      fun i => (1 / rn a) * (a i - b i) + (1 / rn a - 1 / rn b) * b i := by
    funext i; field_simp; ring
  rw [e]
  refine (rn_add' _ _).trans ?_
  rw [rn_smul, rn_smul]
  have h1 := rn_triangle b (fun i => a i) (fun _ => 0)
  have h2 := rn_triangle a (fun i => b i) (fun _ => 0)
  have hba : rn (fun i => b i - a i) = rn (fun i => a i - b i) := by
    have := rn_smul (-1) (fun i => a i - b i)
    rw [show (fun i => -1 * (a i - b i)) = fun i => b i - a i by funext i; ring] at this
    simpa using this
  simp only [sub_zero] at h1 h2
  have habs : |rn b - rn a| ≤ rn (fun i => a i - b i) := by
    rw [abs_le]; constructor <;> linarith
  have : |1 / rn a - 1 / rn b| * rn b = |rn b - rn a| / rn a := by
    rw [show 1 / rn a - 1 / rn b = (rn b - rn a) / (rn a * rn b) by field_simp,
      abs_div, abs_of_pos (mul_pos ha hb)]
    field_simp
  rw [this, abs_of_pos (one_div_pos.2 ha)]
  have h3 : |rn b - rn a| / rn a ≤ rn (fun i => a i - b i) / rn a :=
    div_le_div_of_nonneg_right habs ha.le
  calc 1 / rn a * rn (fun i => a i - b i) + |rn b - rn a| / rn a ≤
      1 / rn a * rn (fun i => a i - b i) + rn (fun i => a i - b i) / rn a := by linarith
    _ = 2 * rn (fun i => a i - b i) / rn a := by ring

theorem InPsiTilde.mono {ν δ δ' : ℝ} {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h : Fin N → ℝ}
    (H : InPsiTilde G ν δ Ψ h) (hδ : 0 ≤ δ) (hle : δ ≤ δ') : InPsiTilde G ν δ' Ψ h where
  layerConst := H.layerConst
  r1 x x' hxx' := (H.r1 x x' hxx').trans_le hle
  r2 x hx := (H.r2 x hx).trans_le hle
  r3 x hx := (H.r3 x hx).trans_le (pow_le_pow_left₀ hδ hle 2)
  r4 := H.r4.trans_le (pow_le_pow_left₀ hδ hle 2)

/-- `δ² / ε ≤ δ'² / max ε δ'` if `δ ≤ ε` and `δ ≤ δ'`. -/
theorem eps_ratio_le {δ δ' ε : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε) (hδδ : δ ≤ δ') :
    δ ^ 2 / ε ≤ δ' ^ 2 / max ε δ' := by
  have hε : 0 < ε := hδ.trans_le hδε
  have hδ' : 0 < δ' := hδ.trans_le hδδ
  rw [div_le_div_iff₀ hε (lt_max_of_lt_left hε)]
  rcases le_total ε δ' with h | h
  · rw [max_eq_right h]
    have h1 : δ * δ ≤ δ' * ε := mul_le_mul hδδ hδε hδ.le hδ'.le
    nlinarith
  · rw [max_eq_left h]
    have h1 : δ ^ 2 ≤ δ' ^ 2 := pow_le_pow_left₀ hδ.le hδδ 2
    nlinarith

/-- Two sites of `dataSites G` that are adjacent: one is in `Ω'₁`, or both are in the
collar of `𝔹'_k` and form an interface pair there. -/
theorem dataSites_pair (h : Precedes G G') {z z' : Torus d (N₀ * L ^ k)}
    (hz : z ∈ dataSites G) (hz' : z' ∈ dataSites G) (hadj : Adj z z') :
    z ∈ G'.Ω 1 ∨ z' ∈ G'.Ω 1 ∨ (z ∉ G'.Ω 1 ∧ z' ∉ G'.Ω 1 ∧ IsInterfacePair G' z z') := by
  by_cases hz2 : z ∈ G'.Ω 1
  · exact Or.inl hz2
  by_cases hz2' : z' ∈ G'.Ω 1
  · exact Or.inr (Or.inl hz2')
  right; right
  have hc : z ∈ collar G := by
    rcases (mem_dataSites G).1 hz with h1 | h1
    · exact absurd (h.mem_Ω1 h1) hz2
    · exact h1
  have hc' : z' ∈ collar G := by
    rcases (mem_dataSites G).1 hz' with h1 | h1
    · exact absurd (h.mem_Ω1 h1) hz2'
    · exact h1
  have hc1 := mem_collar_of_not_mem h hc hz2
  have hc1' := mem_collar_of_not_mem h hc' hz2'
  refine ⟨hz2, hz2', (mem_dataSites G').2 (Or.inr hc1), (mem_dataSites G').2 (Or.inr hc1'),
    Or.inl (by rw [layerIndex_of_not_mem G' hz2, layerIndex_of_not_mem G' hz2']),
    z, by rw [blockSet_of_not_mem G' hz2]; simp,
    z', by rw [blockSet_of_not_mem G' hz2']; simp, hadj⟩

theorem CompHyp.bar_pair {a : ℕ → ℝ} {θ η : ℝ} {Ψx : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {φx : G'.Ω 1 × Fin N → ℂ} (H : CompHyp G G' a θ η Ψx φx) {ρ : ℝ} (hρ : η ≤ ρ)
    (hout : ∀ z z', IsInterfacePair G' z z' → z ∉ G'.Ω 1 → z' ∉ G'.Ω 1 →
      vn (fun i => Ψx z i - Ψx z' i) ≤ ρ) :
    ∀ z z', z ∈ dataSites G → z' ∈ dataSites G → Adj z z' →
      vn (barVec G' Ψx φx z - barVec G' Ψx φx z') ≤ ρ := by
  intro z z' hz hz' hadj
  rcases dataSites_pair H.prec hz hz' hadj with h1 | h1 | ⟨h1, h2, h3⟩
  · rw [vn_sub_comm]; exact (H.bond_out h1 hadj).trans hρ
  · exact (H.bond_out h1 hadj.symm).trans hρ
  · have e : barVec G' Ψx φx z - barVec G' Ψx φx z' = fun i => Ψx z i - Ψx z' i := by
      funext i
      simp only [Pi.sub_apply, barVec_of_not_mem Ψx φx h1, barVec_of_not_mem Ψx φx h2]
    rw [e]; exact hout z z' h3 h1 h2

end Lemma63Aux

/-! ### Lemma 6.3 -/

/-! ### Lemma 6.3 -/

section Lemma63

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

/-- A real field as a complex one. -/
def psiR (Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ) : Torus d (N₀ * L ^ k) → Fin N → ℂ :=
  fun x i => (Ψ0 x i : ℂ)

/-- The complex data field `Ψ0 + Ψ''`. -/
def psiC (Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ) (Ψ'' : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    Torus d (N₀ * L ^ k) → Fin N → ℂ :=
  fun x i => (Ψ0 x i : ℂ) + Ψ'' x i

variable (G G') in
/-- The composed field for the real data `Ψ0` and the real field `φr`. -/
noncomputable def crv (a₁ : ℝ) (φr : G'.Ω 1 × Fin N → ℂ)
    (Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ) : Torus d (N₀ * L ^ k) → Fin N → ℂ :=
  compVec G G' (compWeight L a₁) φr (psiR Ψ0)

variable (G G') in
/-- The composed field for the complex data `Ψ0 + Ψ''` and the complex field `φc`. -/
noncomputable def ccv (a₁ : ℝ) (φc : G'.Ω 1 × Fin N → ℂ)
    (Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ) (Ψ'' : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    Torus d (N₀ * L ^ k) → Fin N → ℂ :=
  compVec G G' (compWeight L a₁) φc (psiC Ψ0 Ψ'')

variable (G G') in
/-- The complex displacement of the composed field. -/
noncomputable def dPsi (a₁ : ℝ) (φr φc : G'.Ω 1 × Fin N → ℂ)
    (Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ) (Ψ'' : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    Torus d (N₀ * L ^ k) → Fin N → ℂ :=
  fun x i => ccv G G' a₁ φc Ψ0 Ψ'' x i - crv G G' a₁ φr Ψ0 x i

variable (G G') in
/-- The real part of the composed field. -/
noncomputable def reR (a₁ : ℝ) (φr : G'.Ω 1 × Fin N → ℂ)
    (Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ) : Torus d (N₀ * L ^ k) → Fin N → ℝ :=
  fun x i => (crv G G' a₁ φr Ψ0 x i).re

variable (G) in
/-- `h''` restricted to `Ω₁`. -/
noncomputable def hRes (h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    Torus d (N₀ * L ^ k) → Fin N → ℂ :=
  fun x i => by classical exact if x ∈ G.Ω 1 then h'' x i else 0

theorem hRes_of_mem (h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) : hRes G h'' x = h'' x := by
  funext i; simp [hRes, hx]

/-- The hypotheses of Lemma 6.3 and of the complex part of (R-S): the data
`(Ψ0 + Ψ'', h0 + h'') ∈ Ψ̃^c(𝔹'_k; δ, ε)`, the real field `φr` and the complex field `φc` with the
bounds of Theorem 5.2 (3) of size `η = K₁ δ` and `|φc - φr|₀ ≤ ε + η`. -/
structure Hyp63 (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ') (a₁ ν δ ε K₁ η : ℝ)
    (Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h0 : Fin N → ℝ)
    (Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φr φc : G'.Ω 1 × Fin N → ℂ) : Prop where
  prec : Precedes G G'
  hL : 2 ≤ L
  ha₁ : 0 < a₁
  hK₁ : 1 ≤ K₁
  hδ : 0 < δ
  hδε : δ ≤ ε
  hε1 : ε ≤ 1
  hη : η = K₁ * δ
  hsmall : (4 * d + 6) * η ≤ 1
  hν : 0 ≤ ν
  hνk : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1
  hPC : InPsiTildeC G' ν δ ε Ψ0 h0 Ψ'' h''
  hφr : ∀ z i, (φr (z, i)).im = 0
  hbr : FieldBounds G' η (psiR Ψ0) φr
  hmass : ∀ z : G'.Ω 1, Real.sqrt ν * G'.spacing z * vn (fun i => φr (z, i) - (h0 i : ℂ)) ≤ η
  hbc : FieldBounds G' η (psiC Ψ0 Ψ'') φc
  hdiff : ∀ z : G'.Ω 1, vn (fun i => φc (z, i) - φr (z, i)) ≤ ε + η

theorem c3b_numeric {d η δ ε : ℝ} (hd0 : 0 ≤ d) (hη : 0 < η) (hδ : 0 < δ) (hδη : δ ≤ η)
    (hδε : δ ≤ ε) :
    δ ^ 2 + 3 * ((2 * d + 2) * η) * (δ ^ 2 / ε) ≤ (2 * ((4 * d + 8) * η)) ^ 2 := by
  have hε : 0 < ε := hδ.trans_le hδε
  have h1 : δ ^ 2 / ε ≤ η := by
    rw [div_le_iff₀ hε]; nlinarith
  have h2 : δ ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hδ.le hδη 2
  have h3 : 3 * ((2 * d + 2) * η) * (δ ^ 2 / ε) ≤ 3 * ((2 * d + 2) * η) * η :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith [sq_nonneg η, mul_nonneg hd0 (sq_nonneg η), mul_nonneg hd0 hd0,
    mul_nonneg (mul_nonneg hd0 hd0) (sq_nonneg η)]

theorem psiR_im_zero {Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ} :
    ∀ x ∈ dataSites G', ∀ i, (psiR Ψ0 x i).im = 0 := fun x _ i => by simp [psiR]

namespace Hyp63

variable {a₁ ν δ ε K₁ η : ℝ} {Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h0 : Fin N → ℝ}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φr φc : G'.Ω 1 × Fin N → ℂ}
  (H : Hyp63 G G' a₁ ν δ ε K₁ η Ψ0 h0 Ψ'' h'' φr φc)

include H

theorem ηpos : 0 < η := by
  rw [H.hη]; exact mul_pos (by linarith [H.hK₁]) H.hδ

theorem δη : δ ≤ η := by
  rw [H.hη]; nlinarith [H.hK₁, H.hδ]

theorem η6 : η ≤ 1 / 6 := by
  have := H.hsmall
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [H.ηpos]

theorem psiR_const : IsLayerConstant G' (psiR Ψ0) := by
  intro n hn1 hnk x hx x' hx'
  funext i
  have := congrFun (H.hPC.layerConst n hn1 hnk x hx x' hx') i
  simp only [psiR, this]

theorem psiC_const : IsLayerConstant G' (psiC Ψ0 Ψ'') := by
  intro n hn1 hnk x hx x' hx'
  funext i
  have h1 := congrFun (H.hPC.layerConst n hn1 hnk x hx x' hx') i
  have h2 := congrFun (H.hPC.layerConst' n hn1 hnk x hx x' hx') i
  simp only [psiC, h1, h2]

theorem hr : CompHyp G G' (compWeight L a₁) 1 η (psiR Ψ0) φr :=
  { prec := H.prec, θ_pos := one_pos, η_nn := H.ηpos.le, gap := scaleGap_one H.prec
    ratio := fun _ hx => compWeight_ratio H.hL H.ha₁ (G.layerIndex_spec hx).1
      (H.prec.layerIndex_le hx)
    layerConst := H.psiR_const, bounds := H.hbr }

theorem hc : CompHyp G G' (compWeight L a₁) 1 η (psiC Ψ0 Ψ'') φc :=
  { prec := H.prec, θ_pos := one_pos, η_nn := H.ηpos.le, gap := scaleGap_one H.prec
    ratio := fun _ hx => compWeight_ratio H.hL H.ha₁ (G.layerIndex_spec hx).1
      (H.prec.layerIndex_le hx)
    layerConst := H.psiC_const, bounds := H.hbc }

theorem real_crv (x : Torus d (N₀ * L ^ k)) : IsRealCVec (crv G G' a₁ φr Ψ0 x) :=
  compVec_isReal H.prec _ φr (psiR Ψ0) H.hφr psiR_im_zero x

theorem core : InPsiTilde G ν (compC4 d * η) (reR G G' a₁ φr Ψ0) h0 := by
  have hP := H.hPC.toInPsiTilde
  have := lemma62_core H.hL H.prec H.ha₁ H.hK₁ H.hδ (by rw [← H.hη]; exact H.hsmall) H.hν H.hνk
    hP (psiR Ψ0) H.psiR_const (fun x _ i => rfl) φr H.hφr (by rw [← H.hη]; exact H.hbr)
    (by rw [← H.hη]; exact H.hmass)
  rw [← H.hη] at this
  exact this

theorem layerConst' : IsLayerConstant G (dPsi G G' a₁ φr φc Ψ0 Ψ'') := by
  intro n hn1 hnk x hx x' hx'
  funext i
  have h1 := congrFun (composeField_layerConst H.prec (compWeight L a₁) φc H.psiC_const n hn1 hnk
    x hx x' hx') i
  have h2 := congrFun (composeField_layerConst H.prec (compWeight L a₁) φr H.psiR_const n hn1 hnk
    x hx x' hx') i
  simp only at h1 h2
  simp only [dPsi, ccv, crv, compVec, h1, h2]

theorem hLayerConst' : IsLayerConstant G (hRes G h'') := by
  intro n hn1 hnk x hx x' hx'
  have hxΩ := G.layer_subset hn1 hnk hx
  have hn : G.layerIndex x = n := G.layerIndex_eq hn1 hnk hx
  have hx'b : x' ∈ G.blk (G.layerIndex x) x := by rw [hn]; exact hx'
  obtain ⟨hx'1, -, -, -, -⟩ := H.prec.block_compat hxΩ hx'b
  obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec (H.prec.mem_Ω1 hxΩ)
  have hx'p : x' ∈ G'.blk (G'.layerIndex x) x := blk_subset_blk' H.prec hxΩ hx'b
  rw [hRes_of_mem h'' hxΩ, hRes_of_mem h'' hx'1]
  funext i
  exact congrFun (H.hPC.hLayerConst' _ hp1 hpk x hxp x' hx'p) i

theorem c1 : ∀ x x', IsInterfacePair G x x' →
    vn (dPsi G G' a₁ φr φc Ψ0 Ψ'' x - dPsi G G' a₁ φr φc Ψ0 Ψ'' x') < 2 * (compC4 d * η) := by
  intro x x' hxx'
  have hP := H.hPC.toInPsiTilde
  have hη := H.ηpos
  have hδη := H.δη
  have hBr := H.hr.bar_pair (ρ := 2 * η) (by linarith) (fun z z' hip _ _ => by
    have e : (fun i => psiR Ψ0 z i - psiR Ψ0 z' i) =
        (fun i => (Ψ0 z i : ℂ)) - fun i => (Ψ0 z' i : ℂ) := rfl
    rw [e, vn_cast_sub]
    exact (hP.r1 z z' hip).le.trans (by linarith))
  have hBc := H.hc.bar_pair (ρ := 2 * η) (by linarith) (fun z z' hip _ _ => by
    have e : (fun i => psiC Ψ0 Ψ'' z i - psiC Ψ0 Ψ'' z' i) = fun i =>
        ((fun j => (Ψ0 z j : ℂ)) - fun j => (Ψ0 z' j : ℂ)) i + (Ψ'' z - Ψ'' z') i := by
      funext i; simp only [psiC, Pi.sub_apply]; ring
    rw [e]
    refine (vn_add' _ _).trans ?_
    have h1 := H.hPC.c1 z z' hip
    have h2 : vn ((fun j => (Ψ0 z j : ℂ)) - fun j => (Ψ0 z' j : ℂ)) < δ := by
      rw [vn_cast_sub]; exact hP.r1 z z' hip
    linarith)
  have h1 : vn (ccv G G' a₁ φc Ψ0 Ψ'' x - ccv G G' a₁ φc Ψ0 Ψ'' x') ≤ _ :=
    H.hc.interface hxx' hBc
  have h2 : vn (crv G G' a₁ φr Ψ0 x - crv G G' a₁ φr Ψ0 x') ≤ _ := H.hr.interface hxx' hBr
  have e : dPsi G G' a₁ φr φc Ψ0 Ψ'' x - dPsi G G' a₁ φr φc Ψ0 Ψ'' x' =
      fun i => (ccv G G' a₁ φc Ψ0 Ψ'' x - ccv G G' a₁ φc Ψ0 Ψ'' x') i -
        (crv G G' a₁ φr Ψ0 x - crv G G' a₁ φr Ψ0 x') i := by
    funext i; simp only [dPsi, Pi.sub_apply]; ring
  rw [e]
  refine (vn_sub_le' _ _).trans_lt ?_
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hC4 : compC4 d * η = (4 * d + 8) * η := rfl
  rw [hC4]
  nlinarith


theorem c2a : ∀ x ∈ dataSites G, vn (dPsi G G' a₁ φr φc Ψ0 Ψ'' x) <
    max ε (2 * (compC4 d * η)) + 2 * (compC4 d * η) := by
  intro x hx
  have hη := H.ηpos
  have hδη := H.δη
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hC4 : compC4 d * η = (4 * d + 8) * η := rfl
  have hε'ge : ε ≤ max ε (2 * ((4 * d + 8) * η)) := le_max_left _ _
  have hdη := mul_nonneg hd0 hη.le
  have hD : ∀ y ∈ dataSites G', vn (fun i => psiC Ψ0 Ψ'' y i - psiR Ψ0 y i) ≤ ε + η := by
    intro y hy
    have e : (fun i => psiC Ψ0 Ψ'' y i - psiR Ψ0 y i) = Ψ'' y := by
      funext i; simp [psiC, psiR]
    rw [e]
    have := H.hPC.c2a y hy
    linarith
  show vn (fun i => ccv G G' a₁ φc Ψ0 Ψ'' x i - crv G G' a₁ φr Ψ0 x i) < _
  rcases (mem_dataSites G).1 hx with hx | hx
  · have hD' := hD x ((mem_dataSites G').2 (Or.inl (H.prec.mem_Ω1 hx)))
    have := compVec_sub_bound H.hc H.hr le_rfl (AΔ := ε + η) (e := 0) H.hdiff le_rfl hx
      (by linarith)
    refine lt_of_le_of_lt this ?_
    rw [hC4]
    nlinarith
  · have hn : x ∉ G.Ω 1 := ((mem_collar G).1 hx).1
    have e : (fun i => ccv G G' a₁ φc Ψ0 Ψ'' x i - crv G G' a₁ φr Ψ0 x i) =
        fun i => barVec G' (psiC Ψ0 Ψ'') φc x i - barVec G' (psiR Ψ0) φr x i := by
      funext i
      simp only [ccv, crv]
      rw [compVec_collar _ φc _ hx, compVec_collar _ φr _ hx]
    rw [e]
    by_cases hx' : x ∈ G'.Ω 1
    · have e2 : (fun i => barVec G' (psiC Ψ0 Ψ'') φc x i - barVec G' (psiR Ψ0) φr x i) =
          fun i => φc (⟨x, hx'⟩, i) - φr (⟨x, hx'⟩, i) := by
        funext i; rw [barVec_of_mem _ φc hx', barVec_of_mem _ φr hx']
      rw [e2]
      refine lt_of_le_of_lt (H.hdiff ⟨x, hx'⟩) ?_
      rw [hC4]; nlinarith
    · have hds : x ∈ dataSites G' :=
        (mem_dataSites G').2 (Or.inr (mem_collar_of_not_mem H.prec hx hx'))
      have e2 : (fun i => barVec G' (psiC Ψ0 Ψ'') φc x i - barVec G' (psiR Ψ0) φr x i) =
          fun i => psiC Ψ0 Ψ'' x i - psiR Ψ0 x i := by
        funext i; rw [barVec_of_not_mem _ φc hx', barVec_of_not_mem _ φr hx']
      rw [e2]
      have := hD x hds
      rw [hC4]
      nlinarith

theorem c2b : ∀ x ∈ dataSites G,
    ‖∑ i, (((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) + dPsi G G' a₁ φr φc Ψ0 Ψ'' x i) *
        (((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) + dPsi G G' a₁ φr φc Ψ0 Ψ'' x i) -
      ∑ i, ((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) * ((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ)‖ <
      2 * (compC4 d * η) := by
  intro x hx
  have hP := H.hPC.toInPsiTilde
  have hη := H.ηpos
  have hδη := H.δη
  have hη6 := H.η6
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hC4 : compC4 d * η = (4 * d + 8) * η := rfl
  have hδ'0 : 0 < 2 * (compC4 d * η) := by rw [hC4]; positivity
  have hcastr : ∀ x i, crv G G' a₁ φr Ψ0 x i = ((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) := fun x i =>
    congrFun (H.real_crv x).eq_ofReal i
  have hdη := mul_nonneg hd0 hη.le
  have e0 : ∀ i, crv G G' a₁ φr Ψ0 x i + dPsi G G' a₁ φr φc Ψ0 Ψ'' x i =
      ccv G G' a₁ φc Ψ0 Ψ'' x i := fun i => by
    simp [dPsi]
  simp only [← hcastr x _]
  simp only [e0]
  rcases (mem_dataSites G).1 hx with hx | hx
  · have hMr : ∀ y ∈ G.blk (G.layerIndex x) x,
        vn (barVec G' (psiR Ψ0) φr y) ≤ 1 := fun y hy =>
      (barVec_vn_eq_one H.hφr H.hbr.unit _ (blk_mem_Ω1' H.prec hx hy).2).le
    have hMc : ∀ y ∈ G.blk (G.layerIndex x) x, vn (barVec G' (psiC Ψ0 Ψ'') φc y) ≤ 3 := by
      intro y hy
      have hy2 := (blk_mem_Ω1' H.prec hx hy).2
      have hyd : y ∈ dataSites G' := (mem_dataSites G').2 (Or.inl hy2)
      have e : barVec G' (psiC Ψ0 Ψ'') φc y =
          fun i => (φc (⟨y, hy2⟩, i) - psiC Ψ0 Ψ'' y i) + psiC Ψ0 Ψ'' y i := by
        funext i; rw [barVec_of_mem _ φc hy2]; ring
      rw [e]
      refine (vn_add' _ _).trans ?_
      have h1 := H.hbc.close ⟨y, hy2⟩
      have e2 : psiC Ψ0 Ψ'' y = fun i => (psiR Ψ0 y i) + Ψ'' y i := by
        funext i; simp [psiC, psiR]
      have h2 : vn (psiC Ψ0 Ψ'' y) ≤ vn (psiR Ψ0 y) + vn (Ψ'' y) := by
        rw [e2]; exact vn_add' _ _
      have h3 : vn (psiR Ψ0 y) ≤ 1 + δ := by
        have e3 : psiR Ψ0 y = fun i => (Ψ0 y i : ℂ) := rfl
        rw [e3, vn_ofReal]
        have := hP.r2 y hyd
        rw [← rn_sq_sum] at this
        have h4 := rn_nonneg (Ψ0 y)
        have h5 := (abs_lt.1 this).2
        by_contra hcon
        push Not at hcon
        nlinarith [H.hδ]
      have h6 := H.hPC.c2a y hyd
      have : vn (fun i => φc (⟨y, hy2⟩, i) - psiC Ψ0 Ψ'' y i) ≤ η := h1
      have hε1 := H.hε1
      linarith
    have hc := H.hc.dot_sub_one hx hMc
    have hr := H.hr.dot_sub_one hx hMr
    have e : ∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i -
        ∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i =
        (∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i - 1) -
        (∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i - 1) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans_lt ?_
    have hc' : ‖∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i - 1‖ ≤ _ := hc
    have hr' : ‖∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i - 1‖ ≤ _ := hr
    have h2dη : 2 * d * η ≤ 1 := by have := H.hsmall; nlinarith
    have hη1 : η ^ 2 ≤ η := by nlinarith
    have hsq : (2 * d * (1 * η)) ^ 2 ≤ 2 * d * η := by nlinarith
    rw [hC4]
    nlinarith
  · have hn : x ∉ G.Ω 1 := ((mem_collar G).1 hx).1
    by_cases hx' : x ∈ G'.Ω 1
    · have e1 : ∀ i, ccv G G' a₁ φc Ψ0 Ψ'' x i = φc (⟨x, hx'⟩, i) := fun i => by
        simp only [ccv]; rw [compVec_collar _ φc _ hx]; exact barVec_of_mem _ φc hx' i
      have e2 : ∀ i, crv G G' a₁ φr Ψ0 x i = φr (⟨x, hx'⟩, i) := fun i => by
        simp only [crv]; rw [compVec_collar _ φr _ hx]; exact barVec_of_mem _ φr hx' i
      simp only [e1, e2, H.hbc.unit ⟨x, hx'⟩, H.hbr.unit ⟨x, hx'⟩, sub_self, norm_zero]
      exact hδ'0
    · have hds : x ∈ dataSites G' :=
        (mem_dataSites G').2 (Or.inr (mem_collar_of_not_mem H.prec hx hx'))
      have e1 : ∀ i, ccv G G' a₁ φc Ψ0 Ψ'' x i = (Ψ0 x i : ℂ) + Ψ'' x i := fun i => by
        simp only [ccv]; rw [compVec_collar _ φc _ hx, barVec_of_not_mem _ φc hx']; rfl
      have e2 : ∀ i, crv G G' a₁ φr Ψ0 x i = (Ψ0 x i : ℂ) := fun i => by
        simp only [crv]; rw [compVec_collar _ φr _ hx, barVec_of_not_mem _ φr hx']; rfl
      simp only [e1, e2]
      refine (H.hPC.c2b x hds).trans_le ?_
      rw [hC4]; nlinarith

theorem c3a : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (hRes G h'' x) <
    (2 * (compC4 d * η)) ^ 2 / max ε (2 * (compC4 d * η)) := by
  intro x hx
  rw [hRes_of_mem h'' hx]
  have h1 := H.hPC.c3a x (H.prec.mem_Ω1 hx)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hmono : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h'' x) ≤
      ν * ((L : ℝ) ^ G'.layerIndex x) ^ 2 * vn (h'' x) := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (by positivity) (pow_le_pow_right₀ hL1 (H.prec.layerIndex_le hx)) 2) H.hν) (vn_nonneg _)
  have hη := H.ηpos
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h2 := eps_ratio_le H.hδ H.hδε (δ' := 2 * (compC4 d * η))
    (by have : compC4 d * η = (4 * d + 8) * η := rfl
        rw [this]; nlinarith [H.δη])
  exact (hmono.trans_lt h1).trans_le h2

/-- The real part of the composed field has length at least `2/3`. -/
theorem rn_lower {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    2 / 3 ≤ rn (reR G G' a₁ φr Ψ0 x) := by
  have hη := H.ηpos
  have hsmall := H.hsmall
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h2dη : 2 * d * η ≤ 1 := by nlinarith
  have hη1 : η ^ 2 ≤ η := by nlinarith [H.η6]
  have h2dη0 : 0 ≤ 2 * d * η := by positivity
  have hsq : (2 * d * (1 * η)) ^ 2 ≤ 2 * d * η := by
    nlinarith [mul_le_mul_of_nonneg_left h2dη h2dη0]
  have hbr2 : |rn (reR G G' a₁ φr Ψ0 x) ^ 2 - 1| ≤ (2 * d + 3) * η := by
    refine (H.hr.re_r2 H.hφr psiR_im_zero hx).trans ?_
    nlinarith
  have hr2 : 1 / 2 ≤ rn (reR G G' a₁ φr Ψ0 x) ^ 2 := by
    have := (abs_le.1 hbr2).1
    nlinarith
  have hrn0 := rn_nonneg (reR G G' a₁ φr Ψ0 x)
  by_contra hcon
  push Not at hcon
  nlinarith

/-- The distance of the composed field to the data: `|Ψ - Ψ0| ≤ (2d + 2) η`. -/
theorem dist_bound {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    rn (fun i => reR G G' a₁ φr Ψ0 x i - Ψ0 x i) ≤ (2 * d + 2) * η := by
  have hx' := H.prec.mem_Ω1 hx
  have hreal := H.real_crv x
  have h0 : (fun i => reR G G' a₁ φr Ψ0 x i - Ψ0 x i) =
      fun i => (crv G G' a₁ φr Ψ0 x i).re - Ψ0 x i := rfl
  rw [h0, rn_re_sub_cast_eq_vn hreal (Ψ0 x)]
  have t1 := H.hr.compVec_sub_mean hx
  have t2 := H.hr.mean_sub_bar hx (x_mem_blk (G := G) _ x)
  have t3 : vn ((fun i => φr (⟨x, hx'⟩, i)) - psiR Ψ0 x) ≤ η := H.hbr.close ⟨x, hx'⟩
  have e : barVec G' (psiR Ψ0) φr x = fun i => φr (⟨x, hx'⟩, i) := by
    funext i; exact barVec_of_mem _ φr hx' i
  rw [e] at t2
  have u1 := vn_triangle (compVec G G' (compWeight L a₁) φr (psiR Ψ0) x)
    (meanVec G (barVec G' (psiR Ψ0) φr) x) (fun i => φr (⟨x, hx'⟩, i))
  have u2 := vn_triangle (compVec G G' (compWeight L a₁) φr (psiR Ψ0) x)
    (fun i => φr (⟨x, hx'⟩, i)) (psiR Ψ0 x)
  show vn (compVec G G' (compWeight L a₁) φr (psiR Ψ0) x - psiR Ψ0 x) ≤ _
  simp only [one_pow, one_mul] at t1 t2
  linarith


theorem c3b : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
    ‖∑ i, ((reR G G' a₁ φr Ψ0 x i / rn (reR G G' a₁ φr Ψ0 x) : ℝ) : ℂ) * hRes G h'' x i‖ <
      (2 * (compC4 d * η)) ^ 2 := by
  intro x hx
  have hx' := H.prec.mem_Ω1 hx
  have hxd : x ∈ dataSites G' := (mem_dataSites G').2 (Or.inl hx')
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hη := H.ηpos
  have hδη := H.δη
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hrlow := H.rn_lower hx
  have hrpos : 0 < rn (reR G G' a₁ φr Ψ0 x) := by linarith
  have hr0pos : 0 < rn (Ψ0 x) := by
    have h1 := (abs_lt.1 (H.hPC.toInPsiTilde.r2 x hxd)).1
    rw [← rn_sq_sum] at h1
    have := rn_nonneg (Ψ0 x)
    by_contra hcon
    push Not at hcon
    have h2 : rn (Ψ0 x) = 0 := le_antisymm hcon this
    rw [h2] at h1
    nlinarith [H.hδ, H.hδε, H.hε1]
  have hτ := H.dist_bound hx
  have hτ0 : 0 ≤ (2 * d + 2) * η := by positivity
  have hnorm := rn_normalize_sub (reR G G' a₁ φr Ψ0 x) (Ψ0 x) hrpos hr0pos
  have hru : rn (fun i => reR G G' a₁ φr Ψ0 x i / rn (reR G G' a₁ φr Ψ0 x) -
      Ψ0 x i / rn (Ψ0 x)) ≤ 3 * ((2 * d + 2) * η) := by
    refine hnorm.trans ?_
    rw [div_le_iff₀ hrpos]
    nlinarith
  rw [hRes_of_mem h'' hx]
  have hsum : ∑ i, ((reR G G' a₁ φr Ψ0 x i / rn (reR G G' a₁ φr Ψ0 x) : ℝ) : ℂ) * h'' x i =
      ∑ i, ((Ψ0 x i / rn (Ψ0 x) : ℝ) : ℂ) * h'' x i +
      ∑ i, ((reR G G' a₁ φr Ψ0 x i / rn (reR G G' a₁ φr Ψ0 x) - Ψ0 x i / rn (Ψ0 x) : ℝ) : ℂ) *
        h'' x i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  rw [hsum]
  have hB : ‖∑ i, ((reR G G' a₁ φr Ψ0 x i / rn (reR G G' a₁ φr Ψ0 x) - Ψ0 x i / rn (Ψ0 x) : ℝ) :
      ℂ) * h'' x i‖ ≤ 3 * ((2 * d + 2) * η) * vn (h'' x) := by
    refine (norm_dot_le _ _).trans ?_
    rw [vn_ofReal]
    exact mul_le_mul_of_nonneg_right hru (vn_nonneg _)
  have hT := H.hPC.c3b x hx'
  have hV := H.hPC.c3a x hx'
  have hmono : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ ν * ((L : ℝ) ^ G'.layerIndex x) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (pow_le_pow_right₀ hL1 (H.prec.layerIndex_le hx)) 2) H.hν
  have hνn0 : 0 ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 := by have := H.hν; positivity
  have hnum := c3b_numeric hd0 hη H.hδ hδη H.hδε
  set S1 := ‖∑ i, ((Ψ0 x i / rn (Ψ0 x) : ℝ) : ℂ) * h'' x i‖ with hS1
  set S2 := ‖∑ i, ((reR G G' a₁ φr Ψ0 x i / rn (reR G G' a₁ φr Ψ0 x) - Ψ0 x i / rn (Ψ0 x) : ℝ) :
    ℂ) * h'' x i‖ with hS2
  have hS : ‖∑ i, ((Ψ0 x i / rn (Ψ0 x) : ℝ) : ℂ) * h'' x i +
      ∑ i, ((reR G G' a₁ φr Ψ0 x i / rn (reR G G' a₁ φr Ψ0 x) - Ψ0 x i / rn (Ψ0 x) : ℝ) : ℂ) *
        h'' x i‖ ≤ S1 + S2 := norm_add_le _ _
  have h1 : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * S1 ≤ ν * ((L : ℝ) ^ G'.layerIndex x) ^ 2 * S1 :=
    mul_le_mul_of_nonneg_right hmono (norm_nonneg _)
  have h2 : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * S2 ≤
      3 * ((2 * d + 2) * η) * (ν * ((L : ℝ) ^ G'.layerIndex x) ^ 2 * vn (h'' x)) := by
    calc ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * S2
        ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * (3 * ((2 * d + 2) * η) * vn (h'' x)) :=
          mul_le_mul_of_nonneg_left hB hνn0
      _ = 3 * ((2 * d + 2) * η) * (ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h'' x)) := by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hmono (vn_nonneg _)
  have h3 := mul_lt_mul_of_pos_left hV (by positivity : 0 < 3 * ((2 * d + 2) * η))
  calc ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * ‖_‖
      ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * (S1 + S2) :=
        mul_le_mul_of_nonneg_left hS hνn0
    _ = ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * S1 + ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * S2 := by
        ring
    _ < δ ^ 2 + 3 * ((2 * d + 2) * η) * (δ ^ 2 / ε) := by linarith
    _ ≤ (2 * (compC4 d * η)) ^ 2 := hnum

/-- **Lemma 6.3, assembled** (see `lemma63`). -/
theorem inPsiTildeC : InPsiTildeC G ν (2 * (compC4 d * η)) (max ε (2 * (compC4 d * η)))
    (reR G G' a₁ φr Ψ0) h0 (dPsi G G' a₁ φr φc Ψ0 Ψ'') (hRes G h'') := by
  have hC4 : compC4 d * η = (4 * d + 8) * η := rfl
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hη := H.ηpos
  exact
    { toInPsiTilde := H.core.mono (by rw [hC4]; positivity) (by rw [hC4]; nlinarith)
      eps_pos := lt_max_of_lt_left H.hPC.eps_pos
      layerConst' := H.layerConst'
      hLayerConst' := H.hLayerConst'
      c1 := H.c1
      c2a := H.c2a
      c2b := H.c2b
      c3a := H.c3a
      c3b := H.c3b }

end Hyp63

/-- **Lemma 6.3** (P2 Lemma 4.4; BACKGROUND.md §6.6, complex data).  Let
`(Ψ0 + Ψ'', h0 + h'') ∈ Ψ̃^c(𝔹'_k; δ, ε)` (`hPC`), `φr` the real field for `(Ψ0, h0)` and `φc` the
complex field for `(Ψ0 + Ψ'', h0 + h'')`, with the bounds of Theorem 5.2 (3) (`FieldBounds`, constant
`η = K₁ δ`), the (R3)-type bound `√ν ℓ'|φr - h0| ≤ η`, and `|φc - φr|₀ ≤ ε + η` (`hdiff`; the last
line of Theorem 5.2 (3)).  Then the composed real datum `reR` (formula (6.2) with `φr`) and `h0`,
with complex displacement `dPsi = Ψ_c - Ψ_r` (formula (6.2) with `φc`, minus the real one) and `h''`
restricted to `Ω₁`, lie in `Ψ̃^c(𝔹_j; δ', ε')`, `δ' = 2 C₄ K₁ δ`, `ε' = max ε δ'` (P2 (4.37)).
The standing assumptions (fields of `Hyp63`): `K₁ ≥ 1`, `δ ≤ ε ≤ 1`, `ν L^{2k} ≤ 1`,
`(4d + 6) K₁ δ ≤ 1`; the weights are `compWeight L a₁`, `a₁ > 0`. -/
theorem lemma63 {a₁ ν δ ε K₁ η : ℝ} {Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h0 : Fin N → ℝ}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φr φc : G'.Ω 1 × Fin N → ℂ}
    (H : Hyp63 G G' a₁ ν δ ε K₁ η Ψ0 h0 Ψ'' h'' φr φc) :
    InPsiTildeC G ν (2 * (compC4 d * η)) (max ε (2 * (compC4 d * η)))
      (reR G G' a₁ φr Ψ0) h0 (dPsi G G' a₁ φr φc Ψ0 Ψ'') (hRes G h'') :=
  H.inPsiTildeC

/-- `composeField` only sees the values of the datum on `Ω'₁ ∪ C(Ω'₁)`. -/
theorem composeField_congr_data (h : Precedes G G') (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    {Ψ1 Ψ2 : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hΨ : ∀ x ∈ dataSites G', ∀ i, Ψ1 x i = Ψ2 x i) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    composeField G G' a φ' Ψ1 x i = composeField G G' a φ' Ψ2 x i := by
  by_cases hx : x ∈ G.Ω 1
  · rw [composeField_of_mem a φ' Ψ1 hx, composeField_of_mem a φ' Ψ2 hx,
      hΨ x ((mem_dataSites G').2 (Or.inl (h.mem_Ω1 hx))) i]
  · by_cases hc : x ∈ collar G
    · rw [composeField_of_collar a φ' Ψ1 hc, composeField_of_collar a φ' Ψ2 hc]
      by_cases hx' : x ∈ G'.Ω 1
      · simp [barField, hx']
      · simp only [barField, hx', ↓reduceDIte]
        exact hΨ x ((mem_dataSites G').2 (Or.inr (mem_collar_of_not_mem h hc hx'))) i
    · have : x ∉ dataSites G := fun h' => by
        rcases (mem_dataSites G).1 h' with h' | h'
        · exact hx h'
        · exact hc h'
      rw [composeField_of_not_mem a φ' Ψ1 this, composeField_of_not_mem a φ' Ψ2 this]

/-- **Lemma 6.3 for `BgData`**: for complex data `Dc` of `𝔹'_k` (equal to `Ψ0 + Ψ''`, `h0 + h''`),
the composed datum `composeData` (formula (6.2) with the complex field `φc`) lies in the complex
domain `Ψ̃^c(𝔹_j; δ', ε')` of `𝔹_j`. -/
theorem lemma63_inDomainC {a₁ ν δ ε K₁ η : ℝ} {Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ}
    {h0 : Fin N → ℝ} {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {φr φc : G'.Ω 1 × Fin N → ℂ} (H : Hyp63 G G' a₁ ν δ ε K₁ η Ψ0 h0 Ψ'' h'' φr φc)
    (Dc : BgData G' N) (hDΨ : ∀ x ∈ dataSites G', ∀ i, Dc.Ψ x i = psiC Ψ0 Ψ'' x i)
    (hDh : ∀ x ∈ G'.Ω 1, ∀ i, Dc.h x i = (h0 i : ℂ) + h'' x i) :
    InDomainC G ν (2 * (compC4 d * η)) (max ε (2 * (compC4 d * η)))
      (composeData H.prec (compWeight L a₁) φc Dc) := by
  refine ⟨reR G G' a₁ φr Ψ0, h0, dPsi G G' a₁ φr φc Ψ0 Ψ'', hRes G h'', H.inPsiTildeC, ?_, ?_⟩
  · intro x _ i
    have hcastr : crv G G' a₁ φr Ψ0 x i = ((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) :=
      congrFun (H.real_crv x).eq_ofReal i
    show composeField G G' (compWeight L a₁) φc Dc.Ψ x i = _
    rw [composeField_congr_data H.prec (compWeight L a₁) φc hDΨ x i, ← hcastr]
    simp [dPsi, ccv, compVec]
  · intro x hx i
    show (if x ∈ G.Ω 1 then Dc.h x i else 0 : ℂ) = _
    simp only [hx, ↓reduceIte]
    rw [hDh x (H.prec.mem_Ω1 hx) i, hRes_of_mem h'' hx]

end Lemma63

end Balaban.Background
