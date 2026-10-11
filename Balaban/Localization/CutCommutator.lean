/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Cover
public import Balaban.Background.Calculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The cut commutators `K_z = χ_z H - H χ_z` and the bound (K) (LOCALIZATION.md §1.2)

For a centre `z` the scalar field `χ_z` (as a field with `N = 1` components) is a smooth field in
the sense of `Balaban.Multiscale.IsSmoothField`, with `δ = C_χ / M₁`, `M₁ = L ^ m₁`
(`chiField_isSmooth`; this is (Cov3)).  Hence the commutator bound of BACKGROUND.md Lemma 3.1
(`Balaban.Background.commK_bound`, itself the discrete Leibniz rule `negLap_mul`) gives (K):
`ℓ(x)² |K_z s (x)| ≤ commKConst d L 1 · (C_χ / M₁) · V` for `|s|₀, |∂s|₁ ≤ V`
(`cutCommutator_bound`).  The commutator vanishes outside the interaction cube
(`cutCommutator_apply_eq_zero`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- The constant `C_χ(d, L)` of (Cov3): `ℓ(x) |∂χ_z| ≤ C_χ / M₁`, `ℓ(x)² |Δχ_z| ≤ C_χ / M₁`. -/
noncomputable def Cchi (d L : ℕ) : ℝ := cH1 d L + d * cH2 d L

theorem Cchi_nonneg (d L : ℕ) : 0 ≤ Cchi d L := by
  unfold Cchi; have := cH1_nonneg d L; have := cH2_nonneg d L; positivity

omit [NeZero N₁] [NeZero L] in
/-- The Euclidean norm of a constant vector with one component. -/
theorem vn_const_one (c : ℝ) : vn (fun _ : Fin 1 => (c : ℂ)) = |c| := by
  have h := vn_sq (fun _ : Fin 1 => (c : ℂ))
  have h0 := vn_nonneg (fun _ : Fin 1 => (c : ℂ))
  simp only [Finset.univ_unique, Finset.sum_singleton, Complex.norm_real, Real.norm_eq_abs] at h
  exact (sq_eq_sq₀ h0 (abs_nonneg c)).1 h

/-- The scalar field `χ_z` as a field of `ℂ ^ 1`. -/
noncomputable def chiField (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (q : ℕ × CTorus d L N₁ m₁ K)
    (x : CTorus d L N₁ m₁ K) : Fin 1 → ℂ := fun _ => ((chi G q x : ℝ) : ℂ)


/-- **(Cov3) as smoothness of the field `χ_z`:** `|∂χ_z|₁, |Δχ_z|₂ ≤ δ = C_χ / M₁`. -/
theorem chiField_isSmooth (hG : CubeAligned G m₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) :
    IsSmoothField G (Cchi d L / (L : ℝ) ^ m₁) (chiField G q) := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hM1 : (1 : ℝ) ≤ (L : ℝ) ^ m₁ := one_le_pow₀ hLr
  have hM0 : (0 : ℝ) < (L : ℝ) ^ m₁ := by linarith
  have hCc := Cchi_nonneg d L
  have hH1 := cH1_nonneg d L
  have hH2 := cH2_nonneg d L
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hH1C : cH1 d L ≤ Cchi d L := by
    unfold Cchi; nlinarith [mul_nonneg hd0 hH2]
  have hdH2C : d * cH2 d L ≤ Cchi d L := by
    unfold Cchi; linarith
  have hgrad : ∀ (n : ℕ) (δ' : ℝ), |δ'| ≤ cH1 d L / (L : ℝ) ^ (n + m₁) →
      |δ'| ≤ Cchi d L / (L : ℝ) ^ m₁ / (L : ℝ) ^ n := by
    intro n δ' h
    refine h.trans ?_
    calc cH1 d L / (L : ℝ) ^ (n + m₁) = cH1 d L / (L : ℝ) ^ m₁ / (L : ℝ) ^ n := by
          rw [pow_add, div_div, mul_comm]
      _ ≤ Cchi d L / (L : ℝ) ^ m₁ / (L : ℝ) ^ n := by gcongr
  constructor
  · intro x hx μ
    obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hx
    have hsp := G.spacing_eq hn1 hnK hxl
    obtain ⟨d1, d1', -⟩ := chi_diff hG hϱ hd hL hn1 hnK hxl μ hq
    have e1 : chiField G q (x + Pi.single μ 1) - chiField G q x =
        fun _ => ((chi G q (x + Pi.single μ 1) - chi G q x : ℝ) : ℂ) := by
      funext i; simp [chiField]
    have e2 : chiField G q (x - Pi.single μ 1) - chiField G q x =
        fun _ => ((chi G q (x - Pi.single μ 1) - chi G q x : ℝ) : ℂ) := by
      funext i; simp [chiField]
    rw [hsp]
    constructor
    · rw [e1, vn_const_one]; exact hgrad _ _ d1
    · rw [e2, vn_const_one]; exact hgrad _ _ d1'
  · intro x hx
    obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hx
    have hsp := G.spacing_eq hn1 hnK hxl
    set n := G.layerIndex x with hn
    have hvec : (fun i : Fin 1 => ∑ μ : Fin d, (chiField G q (x + Pi.single μ 1) i +
        chiField G q (x - Pi.single μ 1) i - 2 * chiField G q x i)) =
        fun _ => ((∑ μ : Fin d, (chi G q (x + Pi.single μ 1) + chi G q (x - Pi.single μ 1) -
          2 * chi G q x) : ℝ) : ℂ) := by
      funext i; simp [chiField]
    rw [hvec, vn_const_one, hsp]
    have hLn : (0 : ℝ) < (L : ℝ) ^ n := by positivity
    calc |∑ μ : Fin d, (chi G q (x + Pi.single μ 1) + chi G q (x - Pi.single μ 1) -
          2 * chi G q x)|
        ≤ ∑ μ : Fin d, |chi G q (x + Pi.single μ 1) + chi G q (x - Pi.single μ 1) -
          2 * chi G q x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _μ : Fin d, cH2 d L / ((L : ℝ) ^ (n + m₁)) ^ 2 :=
          Finset.sum_le_sum fun μ _ => (chi_diff hG hϱ hd hL hn1 hnK hxl μ hq).2.2
      _ = d * (cH2 d L / ((L : ℝ) ^ (n + m₁)) ^ 2) := by simp
      _ ≤ Cchi d L / (L : ℝ) ^ m₁ / ((L : ℝ) ^ n) ^ 2 := by
          have e : d * (cH2 d L / ((L : ℝ) ^ (n + m₁)) ^ 2) =
              (d * cH2 d L) / (L : ℝ) ^ m₁ / ((L : ℝ) ^ n) ^ 2 / (L : ℝ) ^ m₁ := by
            rw [pow_add]; field_simp
          rw [e]
          have h1 : (d * cH2 d L) / (L : ℝ) ^ m₁ / ((L : ℝ) ^ n) ^ 2 / (L : ℝ) ^ m₁ ≤
              (d * cH2 d L) / (L : ℝ) ^ m₁ / ((L : ℝ) ^ n) ^ 2 := by
            apply div_le_self (by positivity) hM1
          refine h1.trans ?_
          gcongr


/-- The cut commutator `K_z = χ_z H - H χ_z` of the Dirichlet operator `H = H_D(α)` with the
multiplication by `χ_z` (acting on scalar fields, `N = 1`). -/
noncomputable def cutCommutator (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (α : G.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) : Matrix (G.Ω 1) (G.Ω 1 × Fin 1) ℂ :=
  commK (dirichletOperator G a ν α) (restrictField G (chiField G q))

/-- **(K)** The Leibniz bound for the cut commutator: for `|s|₀, |∂s|₁ ≤ V`,
`ℓ(x)² |K_z s (x)| ≤ C · (C_χ / M₁) · V` with `C = commKConst d L 1 = 2 d L + 1 + 4 d`
(BACKGROUND.md Lemma 3.1 with `φ₀ = χ_z`, `δ₀ = C_χ / M₁`). -/
theorem cutCommutator_bound (hG : CubeAligned G m₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L) {a : ℕ → ℝ}
    (ha : IsAdmissibleWeights K a) (ν : ℝ) (α : G.Ω 1 → ℂ) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) {s : G.Ω 1 × Fin 1 → ℂ} {V : ℝ} (hV : 0 ≤ V) (hs : StarBound G s V)
    (x : G.Ω 1) :
    G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖(cutCommutator G a ν α q *ᵥ s) x‖ ≤
      commKConst d L 1 * (Cchi d L / (L : ℝ) ^ m₁) * V := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hM0 : (0 : ℝ) < (L : ℝ) ^ m₁ := by positivity
  exact commK_bound (by omega) (by omega) ha ν α (chiField_isSmooth hG hϱ hd hL hq)
    (div_nonneg (Cchi_nonneg d L) hM0.le) hV hs x

section Support

variable {N : ℕ}

/-- `K(φ) s (x) = 0` if `φ` is constant on the star and on the block of `x`. -/
theorem commK_apply_eq_zero {a : ℕ → ℝ} (ν : ℝ) (α : G.Ω 1 → ℂ)
    {φ : CTorus d L N₁ m₁ K → Fin N → ℂ} (s : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1)
    (hstar : ∀ μ : Fin d, φ ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) = φ x ∧
      φ ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) = φ x)
    (hblk : ∀ y ∈ G.blk (G.layerIndex (x : CTorus d L N₁ m₁ K)) x, φ y = φ x) :
    (commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x = 0 := by
  rw [commK_dirichlet_split]
  have h1 : lapTerm G φ s x = 0 := by
    unfold lapTerm
    refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun i _ => ?_
    rw [(hstar μ).1, (hstar μ).2]
    ring
  have h2 : ((avgMatrix G a).map (algebraMap ℝ ℂ) *ᵥ commArg G φ s x) x = 0 := by
    obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec x.2
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases hy : y ∈ G.blk (G.layerIndex (x : CTorus d L N₁ m₁ K)) x
    · have : commArg G φ s x y = 0 := by
        unfold commArg
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hblk y hy]; ring
      rw [this, mul_zero]
    · rw [avgMatrix_apply_of_layer G a hj1 hjk hxl, layerProjMatrix_apply_of_layer G hj1 hjk hxl]
      simp [hy]
  rw [h1, h2, add_zero]

end Support

/-- **Locality of `K_z`.**  The cut commutator vanishes at points outside the interaction cube
`□_z`: it only sees `χ_z` on the star and the block of `x`, which are disjoint from `C_z` there. -/
theorem cutCommutator_apply_eq_zero (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L) {a : ℕ → ℝ} (ν : ℝ) (α : G.Ω 1 → ℂ)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) (s : G.Ω 1 × Fin 1 → ℂ) (x : G.Ω 1)
    (hx : ¬ InBox m₁ q.1 q.2 (5 / 2 * (L : ℝ) ^ (q.1 + m₁)) (x : CTorus d L N₁ m₁ K)) :
    (cutCommutator G a ν α q *ᵥ s) x = 0 := by
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec x.2
  have hz : ∀ z : CTorus d L N₁ m₁ K,
      ((∃ μ, z = (x : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∨
        z = (x : CTorus d L N₁ m₁ K) - Pi.single μ 1) ∨
        SameCell (L ^ G.layerIndex (x : CTorus d L N₁ m₁ K)) (x : CTorus d L N₁ m₁ K) z) →
      chiField G q z = 0 := by
    intro z hnear
    funext i
    by_contra hne
    have hchi : chi G q z ≠ 0 := by
      intro h0; apply hne; simp [chiField, h0]
    exact hx (inSq_of_near hϱ hM hL hq hn1 hnK hxl (inBox_of_chi_ne_zero hchi) hnear)
  have hx0 : chiField G q (x : CTorus d L N₁ m₁ K) = 0 :=
    hz _ (Or.inr (SameCell.refl _ _))
  unfold cutCommutator
  refine commK_apply_eq_zero ν α s x (fun μ => ?_) (fun y hy => ?_)
  · rw [hz _ (Or.inl ⟨μ, Or.inl rfl⟩), hz _ (Or.inl ⟨μ, Or.inr rfl⟩), hx0]
    exact ⟨rfl, rfl⟩
  · rw [hz y (Or.inr (sameCell_of_jBlock_eq hnK (G.mem_blk.1 hy).symm)), hx0]

end Balaban.Localization
