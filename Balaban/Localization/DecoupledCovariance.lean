/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledXAnalytic
public import Balaban.Localization.DecoupledXClose
public import Balaban.Localization.DecoupledXLocal
public import Balaban.Multiscale.ConstraintSandwich
public import Balaban.Multiscale.XVariantIdentities
public import Balaban.Localization.Decoupled2Self
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The constraint sandwich for the decoupled x-variant (I-4c (i))

LOCALIZATION.md §3.4, Theorem I-4c (i): for the decoupled x-variant Green's operator
`G_{k,x,s} = Gsx` (DG7), the data `φ₀` of the constraint (`IsConstraintField`) and
`H = H_{k,x}` (`xDirichletOperator`),

`M_{x,s} = φ₀² - K_x(φ₀) · G_{k,x,s} φ₀`  (`constraintM H Gsx φ₀`),
`N_{x,s} f = φ₀ · f - K_x(φ₀) · G_{k,x,s} f`  (`constraintN H Gsx φ₀`),
`Π_{x,s} = G_{k,x,s} φ₀ M_{x,s}⁻¹ N_{x,s}`  (`decPi`).

The weighted `L²` argument of `Balaban/Multiscale/ConstraintSandwich.lean` (G-2(v)) is repeated
with the DG7 bounds (`XData.dg2_cwsq`, `XData.dg2_grad`) and the x-variant commutator
(`agmonSource_commKx_le`); the constants carry the factor `e^{2 N₀ κ}`.

* `smallConstX`: the smallness constant, `δ² · smallConstX ≤ 1/4`;
* `decM_lower`, `decM_isUnit`: `‖ℓ w s‖² ≤ 4 ‖ℓ w M s‖²`, `M_{x,s}` is invertible (`‖M⁻¹‖ ≤ 2`);
* `decN_src_le`, `decPi_weighted_bounds`: the block-`L²` bounds of `Π_{x,s}` (G-2(v)).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}
  {α : G.Ω 1 → ℂ} {κ : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {ε : ℝ} {r : CTorus d L N₁ m₁ (k + 1) → ℝ} {δ : ℝ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

/-! ### The definitions -/

section Defs

variable (G a aT x ν α s φ)

/-- `M_{x,s} = φ₀² - K_x(φ₀) · G_{k,x,s} φ₀`. -/
noncomputable def decM : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  constraintM (xDirichletOperator G a aT x ν α) (Gsx G a aT x ν α s) (restrictField G φ)

/-- `N_{x,s} f = φ₀ · f - K_x(φ₀) · G_{k,x,s} f`. -/
noncomputable def decN : Matrix (G.Ω 1) (G.Ω 1 × Fin N) ℂ :=
  constraintN (xDirichletOperator G a aT x ν α) (Gsx G a aT x ν α s) (restrictField G φ)

/-- `Π_{x,s} = G_{k,x,s} φ₀ M_{x,s}⁻¹ N_{x,s}` (acting on `N`-vector fields). -/
noncomputable def decPi : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ :=
  liftOp N (Gsx G a aT x ν α s) * fieldMul (restrictField G φ) *
    (decM G a aT x ν α s φ)⁻¹ * decN G a aT x ν α s φ

end Defs

/-! ### Constants -/

/-- The factor `K` in `‖ℓ w K_x(φ₀) G_{k,x,s} f‖² ≤ δ² K ‖ℓ w f‖²`. -/
noncomputable def kConstX (d L : ℕ) (κ : ℝ) : ℝ :=
  commXConst d L * ((gradConstX d + valConstX d) * Real.exp (N0 d L * κ) ^ 2)

theorem kConstX_nonneg (d L : ℕ) (κ : ℝ) : 0 ≤ kConstX d L κ := by
  unfold kConstX gradConstX valConstX
  have := commXConst_nonneg d L
  positivity

/-- The smallness constant: `δ² · smallConstX ≤ 1/4` gives `‖s - M s‖² ≤ 1/4 ‖s‖²`. -/
noncomputable def smallConstX (d L : ℕ) (κ : ℝ) : ℝ := 2 + 9 / 2 * kConstX d L κ

theorem smallConstX_pos (d L : ℕ) (κ : ℝ) : 0 < smallConstX d L κ := by
  unfold smallConstX
  have := kConstX_nonneg d L κ
  positivity

/-- The explicit threshold `δ_*(d,L,κ) = 1 / (2 √(smallConstX))`-type bound, in the squared form
`δ² · smallConstX ≤ 1/4` (existence of `δ_* > 0`). -/
theorem exists_deltaStar (d L : ℕ) (κ : ℝ) :
    ∃ δs : ℝ, 0 < δs ∧ ∀ δ : ℝ, δ ≤ δs → δ ^ 2 * smallConstX d L κ ≤ 1 / 4 ∨ δ < 0 := by
  have hc := smallConstX_pos d L κ
  refine ⟨1 / (2 * (smallConstX d L κ + 1)), by positivity, fun δ hδ => ?_⟩
  by_cases hδ0 : 0 ≤ δ
  · left
    have h1 : δ ^ 2 ≤ (1 / (2 * (smallConstX d L κ + 1))) ^ 2 := pow_le_pow_left₀ hδ0 hδ 2
    have h2 : (1 / (2 * (smallConstX d L κ + 1))) ^ 2 * smallConstX d L κ ≤ 1 / 4 := by
      rw [div_pow, one_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (smallConstX d L κ)]
    calc δ ^ 2 * smallConstX d L κ ≤ (1 / (2 * (smallConstX d L κ + 1))) ^ 2 * smallConstX d L κ :=
          mul_le_mul_of_nonneg_right h1 hc.le
      _ ≤ 1 / 4 := h2
  · right; exact not_le.1 hδ0

/-! ### Vector bounds for `G_{k,x,s}` -/

section Bounds

theorem comp_liftOp' (A : Matrix (G.Ω 1) (G.Ω 1) ℂ) (g : G.Ω 1 × Fin N → ℂ) (i : Fin N) :
    comp G (liftOp N A *ᵥ g) i = A *ᵥ comp G g i := by
  funext y
  exact liftOp_mulVec A g y i

theorem vecGradOn_eq (ε : ℝ) (r : CTorus d L N₁ m₁ (k + 1) → ℝ)
    (Λ : Finset (CTorus d L N₁ m₁ (k + 1))) (u : G.Ω 1 × Fin N → ℂ) :
    vecGradOn G ε r Λ u = ∑ i, gradOn G ε r Λ (comp G u i) := by
  unfold vecGradOn gradOn
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin N)))]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ Λ
  · simp only [hy, ↓reduceIte]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin N)))]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_add_distrib, vn_sq, vn_sq]
    rfl
  · simp [hy]

section Cover

variable {Cx : ℝ} (D : Dec2.XData (coverOf G) G a aT ν x α κ s Cx) (W : XWeight G ε r)
include D W

/-- The block-`L²` bounds of `Ĝ_{k,x,s}` on vector fields, for the data `Dec2.XData` of the pair
`(coverOf G, G)`. -/
theorem Gsx_vec_bounds_cover (g : G.Ω 1 × Fin N → ℂ) :
    vecM G ε r (liftOp N (Gsx G a aT x ν α s) *ᵥ g) ≤
        valConstX d * Real.exp (N0 d L * κ) ^ 2 * vecSrc G ε r g ∧
      vecGradOn G ε r Finset.univ (liftOp N (Gsx G a aT x ν α s) *ᵥ g) ≤
        gradConstX d * Real.exp (N0 d L * κ) ^ 2 * vecSrc G ε r g := by
  refine ⟨?_, ?_⟩
  · rw [vecM_eq, vecSrc, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [comp_liftOp']
    exact D.dg2_cwsq W _
  · rw [vecGradOn_eq, vecSrc, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [comp_liftOp']
    exact D.dg2_grad W _

/-- `‖ℓ w K_x(φ₀) Ĝ_{k,x,s} g‖² ≤ δ² K ‖ℓ w g‖²`, for the data of the pair `(coverOf G, G)`. -/
theorem commKx_Gsx_le_cover (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ) (g : G.Ω 1 × Fin N → ℂ) :
    agmonSource G ε r (commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *ᵥ
      (liftOp N (Gsx G a aT x ν α s) *ᵥ g)) ≤ δ ^ 2 * kConstX d L κ * vecSrc G ε r g := by
  have hd : 0 < d := by have := D.st.hd; omega
  have hL1 : 1 ≤ L := by have := D.st.hL; omega
  have hε2 : ε ≤ agmonRate d := W.ε1.trans (xAgmonRate_le_agmonRate hd hL1)
  have hK := agmonSource_commKx_le_of_ak (ν := ν) G hd D.st.ha ⟨D.st.hak1, D.st.hak2⟩ D.st.haT1 D.x0 α hφ hδ W.agm W.ε0 hε2
    (liftOp N (Gsx G a aT x ν α s) *ᵥ g) Finset.univ (fun y hy => absurd (Finset.mem_univ _) hy)
  obtain ⟨hM, hGr⟩ := Gsx_vec_bounds_cover D W g
  have hV0 := vecSrc_nonneg G ε r g
  have hc := commXConst_nonneg d L
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hsum : vecGradOn G ε r Finset.univ (liftOp N (Gsx G a aT x ν α s) *ᵥ g) +
      vecM G ε r (liftOp N (Gsx G a aT x ν α s) *ᵥ g) ≤
      ((gradConstX d + valConstX d) * Real.exp (N0 d L * κ) ^ 2) * vecSrc G ε r g := by
    nlinarith
  have := mul_le_mul_of_nonneg_left hsum (mul_nonneg hc hδ2)
  unfold kConstX
  nlinarith

end Cover

/-- The standing data of (DG7) for `G` give those of the pair `(coverOf G, G)`
(`Dec2.XData` with `Cx = Cchi d L`; the generalized objects at `coverOf G` are the landed ones). -/
theorem XData.toCover (D : XData G a aT ν x α κ s) :
    Dec2.XData (coverOf G) G a aT ν x α κ s (Cchi d L) :=
  ⟨Dec2.xCover_self D.st, Cchi_nonneg d L, D.pot, D.x0, D.κ0, D.big, D.sb⟩

variable (D : XData G a aT ν x α κ s) (W : XWeight G ε r)
include D W

/-- The block-`L²` bounds of `Ĝ_{k,x,s}` on vector fields. -/
theorem Gsx_vec_bounds (g : G.Ω 1 × Fin N → ℂ) :
    vecM G ε r (liftOp N (Gsx G a aT x ν α s) *ᵥ g) ≤
        valConstX d * Real.exp (N0 d L * κ) ^ 2 * vecSrc G ε r g ∧
      vecGradOn G ε r Finset.univ (liftOp N (Gsx G a aT x ν α s) *ᵥ g) ≤
        gradConstX d * Real.exp (N0 d L * κ) ^ 2 * vecSrc G ε r g :=
  Gsx_vec_bounds_cover D.toCover W g

/-- `‖ℓ w K_x(φ₀) Ĝ_{k,x,s} g‖² ≤ δ² K ‖ℓ w g‖²`. -/
theorem commKx_Gsx_le (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ) (g : G.Ω 1 × Fin N → ℂ) :
    agmonSource G ε r (commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *ᵥ
      (liftOp N (Gsx G a aT x ν α s) *ᵥ g)) ≤ δ ^ 2 * kConstX d L κ * vecSrc G ε r g :=
  commKx_Gsx_le_cover D.toCover W hφ hδ g

end Bounds

/-! ### The Neumann estimate for `M_{x,s}` -/

theorem constraintM_mulVec_gen (Hm Gm : Matrix (G.Ω 1) (G.Ω 1) ℂ) (f : G.Ω 1 → ℂ) :
    f - constraintM Hm Gm (restrictField G φ) *ᵥ f =
      (fun y : G.Ω 1 => (1 - ∑ i, φ y i * φ y i) * f y) +
        commK Hm (restrictField G φ) *ᵥ
          (liftOp N Gm *ᵥ (fieldMul (restrictField G φ) *ᵥ f)) := by
  unfold constraintM
  have e1 : (commK Hm (restrictField G φ) * liftOp N Gm * fieldMul (restrictField G φ)) *ᵥ f =
      commK Hm (restrictField G φ) *ᵥ
        (liftOp N Gm *ᵥ (fieldMul (restrictField G φ) *ᵥ f)) := by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have e2 : ((fieldMul (restrictField G φ))ᵀ * fieldMul (restrictField G φ)) *ᵥ f =
      (fieldMul (restrictField G φ))ᵀ *ᵥ (fieldMul (restrictField G φ) *ᵥ f) := by
    rw [mulVec_mulVec]
  rw [sub_mulVec, e1, e2]
  funext y
  simp only [Pi.sub_apply, Pi.add_apply]
  have h1 : ((fieldMul (restrictField G φ))ᵀ *ᵥ (fieldMul (restrictField G φ) *ᵥ f)) y =
      (∑ i, φ y i * φ y i) * f y := by
    rw [fieldMul_transpose_mulVec, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [fieldMul_mulVec]; simp [restrictField]; ring
  rw [h1]
  ring

/-! The Neumann estimate for the data `Dec2.XData` of the pair `(coverOf G, G)` (no `DGSetting`);
the statements of the section `Neumann` are their instances through `XData.toCover`. -/

section NeumannCover

variable {Cx : ℝ} (D : Dec2.XData (coverOf G) G a aT ν x α κ s Cx) (W : XWeight G ε r)
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
include D W hφ hδ hsm

omit hsm in
/-- **The Neumann estimate.** `‖ℓ w (s - M s)‖² ≤ δ² C ‖ℓ w s‖²`. -/
theorem decM_error_le_cover (f : G.Ω 1 → ℂ) :
    agmonSource G ε r (f - decM G a aT x ν α s φ *ᵥ f) ≤
      δ ^ 2 * smallConstX d L κ * agmonSource G ε r f := by
  unfold decM
  rw [constraintM_mulVec_gen]
  refine (agmonSource_add_le G ε r _ _).trans ?_
  have hA : agmonSource G ε r (fun y : G.Ω 1 => (1 - ∑ i, φ y i * φ y i) * f y) ≤
      δ ^ 2 * agmonSource G ε r f := by
    refine agmonSource_mul_le G ε r _ f (c := δ) fun y => ?_
    rw [norm_sub_rev]
    exact hφ.sq y y.2
  have hK := commKx_Gsx_le_cover D W hφ.toIsSmoothField hδ (fieldMul (restrictField G φ) *ᵥ f)
  have hΦ := vecSrc_fieldMul_le (ε := ε) (r := r) hφ f
  have hk0 := kConstX_nonneg d L κ
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hS0 := agmonSource_nonneg G ε r f
  have hB := hK.trans (mul_le_mul_of_nonneg_left hΦ (mul_nonneg hδ2 hk0))
  unfold smallConstX
  nlinarith [mul_nonneg hδ2 (mul_nonneg hk0 hS0)]

/-- `‖ℓ w s‖² ≤ 4 ‖ℓ w M s‖²`: the weighted lower bound for `M_{x,s}`. -/
theorem decM_lower_cover (f : G.Ω 1 → ℂ) :
    agmonSource G ε r f ≤ 4 * agmonSource G ε r (decM G a aT x ν α s φ *ᵥ f) := by
  set Ms := decM G a aT x ν α s φ *ᵥ f with hMs
  have h1 := decM_error_le_cover D W hφ hδ f
  have h2 : f = Ms + (f - Ms) := by abel
  have h3 := agmonSource_add_le G ε r Ms (f - Ms)
  rw [← h2] at h3
  have h4 : δ ^ 2 * smallConstX d L κ * agmonSource G ε r f ≤ 1 / 4 * agmonSource G ε r f :=
    mul_le_mul_of_nonneg_right hsm (agmonSource_nonneg G ε r f)
  have h5 : agmonSource G ε r (f - Ms) ≤ 1 / 4 * agmonSource G ε r f := h1.trans h4
  linarith

omit W in
/-- **`M_{x,s}` is invertible.** -/
theorem decM_isUnit_cover : IsUnit (decM G a aT x ν α s φ) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro f f' hff
  have hlin : decM G a aT x ν α s φ *ᵥ (f - f') = 0 := by
    rw [Matrix.mulVec_sub, hff, sub_self]
  have hW0 : XWeight G 0 (fun _ => 0) := by
    refine ⟨isAgmonWeight_zero G, le_rfl, ?_⟩
    have hd : 0 < d := by have := D.st.hd; omega
    exact (xAgmonRate_pos hd D.st.hL).le
  have h := decM_lower_cover D hW0 hφ hδ hsm (f - f')
  rw [hlin] at h
  have h0 : agmonSource G 0 (fun _ => 0) (0 : G.Ω 1 → ℂ) = 0 := by
    rw [agmonSource_zero_eq]; simp
  rw [h0, mul_zero] at h
  exact sub_eq_zero.1 (eq_zero_of_agmonSource_zero h)

/-- `‖ℓ w M⁻¹ f‖² ≤ 4 ‖ℓ w f‖²`: `‖M⁻¹‖ ≤ 2` on the weighted `L²`. -/
theorem decM_inv_le_cover (f : G.Ω 1 → ℂ) :
    agmonSource G ε r ((decM G a aT x ν α s φ)⁻¹ *ᵥ f) ≤ 4 * agmonSource G ε r f := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 (decM_isUnit_cover D hφ hδ hsm)
  have := decM_lower_cover D W hφ hδ hsm ((decM G a aT x ν α s φ)⁻¹ *ᵥ f)
  rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at this

/-- `‖ℓ w N_{x,s} f‖² ≤ 5 ‖ℓ w f‖²` for a vector field `f`. -/
theorem decN_src_le_cover (f : G.Ω 1 × Fin N → ℂ) :
    agmonSource G ε r (decN G a aT x ν α s φ *ᵥ f) ≤ 5 * vecSrc G ε r f := by
  unfold decN constraintN
  rw [sub_mulVec, ← mulVec_mulVec]
  refine (agmonSource_sub_le G ε r _ _).trans ?_
  have h1 := agmonSource_fieldMul_transpose_le (ε := ε) (r := r) hφ f
  have hK := commKx_Gsx_le_cover D W hφ.toIsSmoothField hδ f
  have hV0 := vecSrc_nonneg G ε r f
  have hk0 := kConstX_nonneg d L κ
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hq : 0 ≤ δ ^ 2 * kConstX d L κ := mul_nonneg hδ2 hk0
  have hsm' := hsm
  unfold smallConstX at hsm'
  have hkey : δ ^ 2 * kConstX d L κ ≤ 1 / 18 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hkey hV0]

/-- **G-2(v), weighted `L²` form for `Π_{x,s}`**: the block-`L²` bounds
`‖ℓ⁻¹ w Π f‖² ≤ 45 V e^{2N₀κ} ‖ℓ w f‖²` and `‖w ∂ Π f‖² ≤ 45 g e^{2N₀κ} ‖ℓ w f‖²`. -/
theorem decPi_weighted_bounds_cover (f : G.Ω 1 × Fin N → ℂ) :
    vecM G ε r (decPi G a aT x ν α s φ *ᵥ f) ≤
        45 * (valConstX d * Real.exp (N0 d L * κ) ^ 2) * vecSrc G ε r f ∧
      vecGradOn G ε r Finset.univ (decPi G a aT x ν α s φ *ᵥ f) ≤
        45 * (gradConstX d * Real.exp (N0 d L * κ) ^ 2) * vecSrc G ε r f := by
  set h : G.Ω 1 → ℂ := (decM G a aT x ν α s φ)⁻¹ *ᵥ (decN G a aT x ν α s φ *ᵥ f) with hh
  have hsrc : agmonSource G ε r h ≤ 20 * vecSrc G ε r f := by
    have h4 := decM_inv_le_cover D W hφ hδ hsm (decN G a aT x ν α s φ *ᵥ f)
    have h5 := decN_src_le_cover D W hφ hδ hsm f
    linarith
  have hPi : decPi G a aT x ν α s φ *ᵥ f =
      liftOp N (Gsx G a aT x ν α s) *ᵥ (fieldMul (restrictField G φ) *ᵥ h) := by
    unfold decPi
    rw [hh, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  rw [hPi]
  obtain ⟨hM, hGr⟩ := Gsx_vec_bounds_cover D W (fieldMul (restrictField G φ) *ᵥ h)
  have hΦ := vecSrc_fieldMul_le (ε := ε) (r := r) hφ h
  have hV0 := vecSrc_nonneg G ε r f
  have hv : 0 ≤ valConstX d * Real.exp (N0 d L * κ) ^ 2 := by unfold valConstX; positivity
  have hg : 0 ≤ gradConstX d * Real.exp (N0 d L * κ) ^ 2 := by unfold gradConstX; positivity
  refine ⟨?_, ?_⟩
  · calc _ ≤ valConstX d * Real.exp (N0 d L * κ) ^ 2 *
          vecSrc G ε r (fieldMul (restrictField G φ) *ᵥ h) := hM
      _ ≤ valConstX d * Real.exp (N0 d L * κ) ^ 2 * (9 / 4 * agmonSource G ε r h) :=
          mul_le_mul_of_nonneg_left hΦ hv
      _ ≤ valConstX d * Real.exp (N0 d L * κ) ^ 2 * (9 / 4 * (20 * vecSrc G ε r f)) := by
          gcongr
      _ = _ := by ring
  · calc _ ≤ gradConstX d * Real.exp (N0 d L * κ) ^ 2 *
          vecSrc G ε r (fieldMul (restrictField G φ) *ᵥ h) := hGr
      _ ≤ gradConstX d * Real.exp (N0 d L * κ) ^ 2 * (9 / 4 * agmonSource G ε r h) :=
          mul_le_mul_of_nonneg_left hΦ hg
      _ ≤ gradConstX d * Real.exp (N0 d L * κ) ^ 2 * (9 / 4 * (20 * vecSrc G ε r f)) := by
          gcongr
      _ = _ := by ring

end NeumannCover

section Neumann

variable (D : XData G a aT ν x α κ s) (W : XWeight G ε r)
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
include D W hφ hδ hsm

omit hsm in
/-- **The Neumann estimate.** `‖ℓ w (s - M s)‖² ≤ δ² C ‖ℓ w s‖²`. -/
theorem decM_error_le (f : G.Ω 1 → ℂ) :
    agmonSource G ε r (f - decM G a aT x ν α s φ *ᵥ f) ≤
      δ ^ 2 * smallConstX d L κ * agmonSource G ε r f :=
  decM_error_le_cover D.toCover W hφ hδ f

/-- `‖ℓ w s‖² ≤ 4 ‖ℓ w M s‖²`: the weighted lower bound for `M_{x,s}`. -/
theorem decM_lower (f : G.Ω 1 → ℂ) :
    agmonSource G ε r f ≤ 4 * agmonSource G ε r (decM G a aT x ν α s φ *ᵥ f) :=
  decM_lower_cover D.toCover W hφ hδ hsm f

omit W in
/-- **`M_{x,s}` is invertible.** -/
theorem decM_isUnit : IsUnit (decM G a aT x ν α s φ) :=
  decM_isUnit_cover D.toCover hφ hδ hsm

/-- `‖ℓ w M⁻¹ f‖² ≤ 4 ‖ℓ w f‖²`: `‖M⁻¹‖ ≤ 2` on the weighted `L²`. -/
theorem decM_inv_le (f : G.Ω 1 → ℂ) :
    agmonSource G ε r ((decM G a aT x ν α s φ)⁻¹ *ᵥ f) ≤ 4 * agmonSource G ε r f :=
  decM_inv_le_cover D.toCover W hφ hδ hsm f

/-- `‖ℓ w N_{x,s} f‖² ≤ 5 ‖ℓ w f‖²` for a vector field `f`. -/
theorem decN_src_le (f : G.Ω 1 × Fin N → ℂ) :
    agmonSource G ε r (decN G a aT x ν α s φ *ᵥ f) ≤ 5 * vecSrc G ε r f :=
  decN_src_le_cover D.toCover W hφ hδ hsm f

/-- **G-2(v), weighted `L²` form for `Π_{x,s}`**: the block-`L²` bounds
`‖ℓ⁻¹ w Π f‖² ≤ 45 V e^{2N₀κ} ‖ℓ w f‖²` and `‖w ∂ Π f‖² ≤ 45 g e^{2N₀κ} ‖ℓ w f‖²`. -/
theorem decPi_weighted_bounds (f : G.Ω 1 × Fin N → ℂ) :
    vecM G ε r (decPi G a aT x ν α s φ *ᵥ f) ≤
        45 * (valConstX d * Real.exp (N0 d L * κ) ^ 2) * vecSrc G ε r f ∧
      vecGradOn G ε r Finset.univ (decPi G a aT x ν α s φ *ᵥ f) ≤
        45 * (gradConstX d * Real.exp (N0 d L * κ) ^ 2) * vecSrc G ε r f :=
  decPi_weighted_bounds_cover D.toCover W hφ hδ hsm f

end Neumann

end Balaban.Localization
