/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2X
public import Balaban.Localization.DecoupledXBounds

/-!
# (DG7): weighted `L²` bounds for the cube Green's functions of the x-variant, for a cover `C`

The overlap bookkeeping of the cover, the energy inequality for one cube (`cube_energy`: the cube is
a union of `H`-blocks, `CoverGeom.blockAligned`), the commutator bound `Kzx_agmonSource_le` (the
`H`-scaled derivative bound `CoverGeom.chi_smooth`) and (DG1) `dg1x` with the constant
`cstarX d L Cx`.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ (k + 1)} {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {aT x ν Cx : ℝ} {α : H.Ω 1 → ℂ}

theorem card_overlap_le (S : XCover C H a aT ν Cx) (y : H.Ω 1) :
    ((C.cubeIdx).filter (fun q => (y : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q)).card ≤
      3 * 5 ^ d := by
  classical
  convert S.card_box _ y.2

theorem sq_norm_sum_overlap (S : XCover C H a aT ν Cx) {F : ℕ × CTorus d L N₁ m₁ (k + 1) → H.Ω 1 → ℂ}
    (hF : ∀ q ∈ C.cubeIdx, ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∉ intBox q → F q y = 0)
    (y : H.Ω 1) :
    ‖∑ q ∈ C.cubeIdx, F q y‖ ^ 2 ≤ (3 * 5 ^ d : ℝ) * ∑ q ∈ C.cubeIdx, ‖F q y‖ ^ 2 := by
  classical
  set Q := (C.cubeIdx).filter (fun q => (y : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q) with hQ
  have hsum : ∑ q ∈ C.cubeIdx, F q y = ∑ q ∈ Q, F q y := by
    symm
    refine Finset.sum_filter_of_ne fun q hq hne => ?_
    by_contra hnb
    exact hne (hF q hq y hnb)
  rw [hsum]
  have h1 : ‖∑ q ∈ Q, F q y‖ ≤ ∑ q ∈ Q, ‖F q y‖ := norm_sum_le _ _
  have h2 : (∑ q ∈ Q, ‖F q y‖) ^ 2 ≤ (Q.card : ℝ) * ∑ q ∈ Q, ‖F q y‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : (Q.card : ℝ) ≤ 3 * 5 ^ d := by exact_mod_cast card_overlap_le S y
  have h4 : ∑ q ∈ Q, ‖F q y‖ ^ 2 ≤ ∑ q ∈ C.cubeIdx, ‖F q y‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
  have h5 : 0 ≤ ∑ q ∈ Q, ‖F q y‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ‖∑ q ∈ Q, F q y‖ ^ 2 ≤ (∑ q ∈ Q, ‖F q y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (Q.card : ℝ) * ∑ q ∈ Q, ‖F q y‖ ^ 2 := h2
    _ ≤ (3 * 5 ^ d : ℝ) * ∑ q ∈ Q, ‖F q y‖ ^ 2 := mul_le_mul_of_nonneg_right h3 h5
    _ ≤ (3 * 5 ^ d : ℝ) * ∑ q ∈ C.cubeIdx, ‖F q y‖ ^ 2 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)

theorem agmonSource_sum_le (S : XCover C H a aT ν Cx)
    {F : ℕ × CTorus d L N₁ m₁ (k + 1) → H.Ω 1 → ℂ}
    (hF : ∀ q ∈ C.cubeIdx, ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∉ intBox q → F q y = 0)
    (ε : ℝ) (r : CTorus d L N₁ m₁ (k + 1) → ℝ) :
    agmonSource H ε r (fun y => ∑ q ∈ C.cubeIdx, F q y) ≤
      (3 * 5 ^ d : ℝ) * ∑ q ∈ C.cubeIdx, agmonSource H ε r (F q) := by
  simp only [agmonSource_eq]
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun y _ => ?_
  have h := sq_norm_sum_overlap S hF y
  have h0 : 0 ≤ H.spacing (y : CTorus d L N₁ m₁ (k + 1)) ^ 2 *
      Real.exp (ε * r y) ^ 2 := by positivity
  calc H.spacing y ^ 2 * Real.exp (ε * r y) ^ 2 * ‖∑ q ∈ C.cubeIdx, F q y‖ ^ 2
      ≤ H.spacing y ^ 2 * Real.exp (ε * r y) ^ 2 *
        ((3 * 5 ^ d : ℝ) * ∑ q ∈ C.cubeIdx, ‖F q y‖ ^ 2) := mul_le_mul_of_nonneg_left h h0
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring


theorem sum_agmonSource_cD_le (S : XCover C H a aT ν Cx) (ε : ℝ)
    (r : CTorus d L N₁ m₁ (k + 1) → ℝ) (g : H.Ω 1 → ℂ) :
    ∑ q ∈ C.cubeIdx, agmonSource H ε r (cD H q *ᵥ g) ≤
      (3 * 5 ^ d : ℝ) * agmonSource H ε r g := by
  classical
  simp only [agmonSource_eq]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  have e : ∀ q, H.spacing y ^ 2 * Real.exp (ε * r y) ^ 2 * ‖(cD H q *ᵥ g) y‖ ^ 2 =
      if (y : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q then
        H.spacing y ^ 2 * Real.exp (ε * r y) ^ 2 * ‖g y‖ ^ 2 else 0 := by
    intro q
    rw [cD_mulVec]
    split_ifs <;> simp
  simp only [e]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have h3 : (((C.cubeIdx).filter (fun q => (y : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q)).card : ℝ)
      ≤ 3 * 5 ^ d := by exact_mod_cast card_overlap_le S y
  have h0 : 0 ≤ H.spacing y ^ 2 * Real.exp (ε * r y) ^ 2 * ‖g y‖ ^ 2 := by positivity
  calc _ ≤ (3 * 5 ^ d : ℝ) * (H.spacing y ^ 2 * Real.exp (ε * r y) ^ 2 * ‖g y‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h3 h0
    _ = _ := by ring



theorem cube_energy (S : XCover C H a aT ν Cx) (hα : AdmPot H α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ C.cubeIdx)
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight H r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (g : H.Ω 1 → ℂ) :
    (1 / 2) * cutEnergy (cubeCut H (intBox q))
        (agmonField H ε r (cubeGx H a aT x ν α q *ᵥ g)) +
      (1 / 32) * cwsq H (agmonField H ε r (cubeGx H a aT x ν α q *ᵥ g)) ≤
      8 * agmonSource H ε r (cD H q *ᵥ g) :=
  x_agmon_energy_cut_of_ak H (cubeCut_aligned H (S.blockAligned q hq)) (by have := S.hd; omega) S.hL S.mass S.ha ⟨S.hak1, S.hak2⟩ S.haT1 S.haT2 hx α (AdmPot.le_eighth' S.hd hα) hr hε0 hε1
    (cubeHx_cubeGx S hα hx hq g)

theorem cube_cwsq_le (S : XCover C H a aT ν Cx) (hα : AdmPot H α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ C.cubeIdx)
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight H r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (g : H.Ω 1 → ℂ) :
    cwsq H (agmonField H ε r (cubeGx H a aT x ν α q *ᵥ g)) ≤
      256 * agmonSource H ε r (cD H q *ᵥ g) := by
  have h := cube_energy S hα hx hq hr hε0 hε1 g
  have hE := cutEnergy_nonneg (cubeCut H (intBox q))
    (agmonField H ε r (cubeGx H a aT x ν α q *ᵥ g))
  linarith

theorem cube_cutEnergy_le (S : XCover C H a aT ν Cx) (hα : AdmPot H α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ C.cubeIdx)
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight H r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (g : H.Ω 1 → ℂ) :
    cutEnergy (cubeCut H (intBox q)) (agmonField H ε r (cubeGx H a aT x ν α q *ᵥ g)) ≤
      16 * agmonSource H ε r (cD H q *ᵥ g) := by
  have h := cube_energy S hα hx hq hr hε0 hε1 g
  have hW := cwsq_nonneg H (agmonField H ε r (cubeGx H a aT x ν α q *ᵥ g))
  linarith



theorem Kzx_agmonSource_le (S : XCover C H a aT ν Cx) (hCx : 0 ≤ Cx) (hα : AdmPot H α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ C.cubeIdx)
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight H r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (g : H.Ω 1 → ℂ) :
    agmonSource H ε r (Kzx C H a aT x ν q *ᵥ (cubeGx H a aT x ν α q *ᵥ g)) ≤
      324 * commXConst d L * (Cx / (L : ℝ) ^ m₁) ^ 2 *
        agmonSource H ε r (cD H q *ᵥ g) := by
  classical
  have hd : 0 < d := by have := S.hd; omega
  have hL1 : 1 ≤ L := by have := S.hL; omega
  have hε2 : ε ≤ agmonRate d := hε1.trans (xAgmonRate_le_agmonRate hd hL1)
  have hM0 : (0 : ℝ) < (L : ℝ) ^ m₁ := by
    have : (0 : ℝ) < L := by exact_mod_cast hL1
    positivity
  have hsmooth := S.chi_smooth q hq
  have hδ : 0 ≤ Cx / (L : ℝ) ^ m₁ := div_nonneg (hCx) hM0.le
  set u := cubeGx H a aT x ν α q *ᵥ g with hu
  set Λ : Finset (CTorus d L N₁ m₁ (k + 1)) := Finset.univ.filter (fun y => Inner q y) with hΛ
  have hKe : Kzx C H a aT x ν q *ᵥ u = commK (xDirichletOperator H a aT x ν 0)
      (restrictField H (C.chiField q)) *ᵥ (fun p : H.Ω 1 × Fin 1 => u p.1) := by
    funext y; exact Kzx_mulVec_eq_commK a aT x ν 0 q u y
  have hΛ0 : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∉ Λ →
      (commK (xDirichletOperator H a aT x ν 0) (restrictField H (C.chiField q)) *ᵥ
        (fun p : H.Ω 1 × Fin 1 => u p.1)) y = 0 := by
    intro y hy
    rw [← hKe]
    by_contra hne
    exact hy (by simp [hΛ, inner_of_Kzx_ne_zero S hq u y hne])
  have hcomm := agmonSource_commKx_le_of_ak H hd S.ha ⟨S.hak1, S.hak2⟩ S.haT1 hx (ν := ν) 0 hsmooth hδ hr hε0 hε2
    (fun p : H.Ω 1 × Fin 1 => u p.1) Λ hΛ0
  rw [vecGradOn_scalar, vecM_scalar] at hcomm
  rw [hKe]
  have hgrad := gradOn_le H (cut := cubeCut H (intBox q)) (Λ := Λ)
    (fun y hy => (by simpa [hΛ] using hy : Inner q y).noCut) hr hε0
    (by linarith [agmonRate_le hd]) u
  have hE := cube_cutEnergy_le S hα hx hq hr hε0 hε1 g
  have hW := cube_cwsq_le S hα hx hq hr hε0 hε1 g
  have hS0 := agmonSource_nonneg H ε r (cD H q *ᵥ g)
  have hε3 : ε ^ 2 * d ≤ 1 / 1024 := by
    have h1 := rate_mul_le hd hε2
    have h2 : ε ≤ 1 / 32 := hε2.trans (agmonRate_le hd)
    nlinarith [mul_nonneg hε0 hε0]
  have hgr : gradOn H ε r Λ u + cwsq H (agmonField H ε r u) ≤
      324 * agmonSource H ε r (cD H q *ᵥ g) := by
    have : 16 * ε ^ 2 * (d * cwsq H (agmonField H ε r u)) ≤
        16 * (1 / 1024) * cwsq H (agmonField H ε r u) := by
      have hw0 := cwsq_nonneg H (agmonField H ε r u)
      nlinarith [mul_nonneg hw0 (by linarith : (0 : ℝ) ≤ 1 / 1024 - ε ^ 2 * d)]
    nlinarith
  have hC0 := commXConst_nonneg d L
  calc _ ≤ commXConst d L * (Cx / (L : ℝ) ^ m₁) ^ 2 *
        (gradOn H ε r Λ u + cwsq H (agmonField H ε r u)) := hcomm
    _ ≤ commXConst d L * (Cx / (L : ℝ) ^ m₁) ^ 2 *
        (324 * agmonSource H ε r (cD H q *ᵥ g)) :=
        mul_le_mul_of_nonneg_left hgr (by positivity)
    _ = _ := by ring



/-! ### (DG1) -/

/-- The constant `c_*(d, L)` of (DG1): `M₁ ≥ c_* e^{N₀ κ₁}`. -/
noncomputable def cstarX (d L : ℕ) (Cx : ℝ) : ℝ :=
  72 * (3 * 5 ^ d) * (commXConst d L + 1) * (Cx + 1)

theorem cstarX_pos (d L : ℕ) (hCx : 0 ≤ Cx) : 0 < cstarX d L Cx := by
  have := commXConst_nonneg d L
  have := hCx
  unfold cstarX; positivity

theorem Kcalx_mulVec (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (f : H.Ω 1 → ℂ) :
    Kcalx C H a aT x ν α s *ᵥ f = fun y => ∑ q ∈ C.cubeIdx, C.sProd s q *
      (Kzx C H a aT x ν q *ᵥ (cubeGx H a aT x ν α q *ᵥ f)) y := by
  funext y
  unfold Kcalx
  rw [Matrix.sum_mulVec, Finset.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, ← Matrix.mulVec_mulVec]

theorem Gstarx_mulVec (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (f : H.Ω 1 → ℂ) :
    Gstarx C H a aT x ν α s *ᵥ f = fun y => ∑ q ∈ C.cubeIdx, C.sProd s q *
      (chiD C H q *ᵥ (cubeGx H a aT x ν α q *ᵥ f)) y := by
  funext y
  unfold Gstarx
  rw [Matrix.sum_mulVec, Finset.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, ← Matrix.mulVec_mulVec]

/-- **(DG1), weighted `L²` form.** For `M₁ ≥ c_* e^{N₀ κ₁}`, `|s_P| ≤ e^{κ₁}`, `|A| ≤ γ₁`, every
weight `w = e^{ε r}` with `0 ≤ ε ≤ ε_x`, uniformly in `x ≥ 0`:
`‖ℓ w 𝒦_{x,s}(A) f‖ ≤ ¼ ‖ℓ w f‖`. -/
theorem dg1x (S : XCover C H a aT ν Cx) (hCx : 0 ≤ Cx) (hα : AdmPot H α) (hx : 0 ≤ x) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMκ : cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight H r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (f : H.Ω 1 → ℂ) :
    agmonSource H ε r (Kcalx C H a aT x ν α s *ᵥ f) ≤ (1 / 16) * agmonSource H ε r f := by
  classical
  set F : ℕ × CTorus d L N₁ m₁ (k + 1) → H.Ω 1 → ℂ := fun q y =>
    C.sProd s q * (Kzx C H a aT x ν q *ᵥ (cubeGx H a aT x ν α q *ᵥ f)) y with hF
  have hFs : ∀ q ∈ C.cubeIdx, ∀ y : H.Ω 1,
      (y : CTorus d L N₁ m₁ (k + 1)) ∉ intBox q → F q y = 0 := by
    intro q hq y hy
    simp only [hF]
    have : (Kzx C H a aT x ν q *ᵥ (cubeGx H a aT x ν α q *ᵥ f)) y = 0 := by
      by_contra hne
      exact hy (inner_of_Kzx_ne_zero S hq _ y hne).self
    rw [this, mul_zero]
  have hL1 : 1 ≤ L := by have := S.hL; omega
  have hM0 : (0 : ℝ) < (L : ℝ) ^ m₁ := by
    have : (0 : ℝ) < L := by exact_mod_cast hL1
    positivity
  rw [Kcalx_mulVec]
  have h1 := agmonSource_sum_le S hFs ε r
  have hE1 : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by positivity)
  have hterm : ∀ q ∈ C.cubeIdx, agmonSource H ε r (F q) ≤ Real.exp (N0 d L * κ) ^ 2 *
      (324 * commXConst d L * (Cx / (L : ℝ) ^ m₁) ^ 2 *
        agmonSource H ε r (cD H q *ᵥ f)) := by
    intro q hq
    have hsp : ‖C.sProd s q‖ ≤ Real.exp (N0 d L * κ) :=
      C.norm_sProd_le (S.card_qset q hq) hκ hs
    have h2 := agmonSource_mul_le H ε r (fun _ => C.sProd s q)
      (Kzx C H a aT x ν q *ᵥ (cubeGx H a aT x ν α q *ᵥ f)) (c := Real.exp (N0 d L * κ))
      (fun _ => hsp)
    refine h2.trans ?_
    exact mul_le_mul_of_nonneg_left (Kzx_agmonSource_le S hCx hα hx hq hr hε0 hε1 f) (by positivity)
  have h3 := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h3
  have h4 := sum_agmonSource_cD_le S ε r f
  have hC0 := commXConst_nonneg d L
  have hnum := dg1_numeric (n := 3 * 5 ^ d) (C := commXConst d L) (Cχ := Cx)
    (E := Real.exp (N0 d L * κ)) (M := (L : ℝ) ^ m₁)
    (by have : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num); linarith) hC0 (hCx) hE1
    (by unfold cstarX at hMκ; linarith)
  have hS0 := agmonSource_nonneg H ε r f
  calc _ ≤ (3 * 5 ^ d : ℝ) * ∑ q ∈ C.cubeIdx, agmonSource H ε r (F q) := h1
    _ ≤ (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 *
        (324 * commXConst d L * (Cx / (L : ℝ) ^ m₁) ^ 2 *
          ∑ q ∈ C.cubeIdx, agmonSource H ε r (cD H q *ᵥ f))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 *
        (324 * commXConst d L * (Cx / (L : ℝ) ^ m₁) ^ 2 *
          ((3 * 5 ^ d : ℝ) * agmonSource H ε r f))) := by
        gcongr
    _ = ((3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 *
        (324 * commXConst d L * (Cx / (L : ℝ) ^ m₁) ^ 2)) * (3 * 5 ^ d : ℝ)) *
          agmonSource H ε r f := by ring
    _ ≤ (1 / 16) * agmonSource H ε r f := by
        refine mul_le_mul_of_nonneg_right ?_ hS0
        have e : (324 * commXConst d L * (Cx / (L : ℝ) ^ m₁) ^ 2) =
            (324 * commXConst d L * (Cx / (L : ℝ) ^ m₁) ^ 2) := rfl
        linarith [hnum]



end Balaban.Localization.Dec2
