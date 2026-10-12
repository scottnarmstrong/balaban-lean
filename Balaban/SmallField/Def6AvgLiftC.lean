/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgInv
public import Balaban.SmallField.Def6BridgeInfLift
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Reynolds averaging: the lifted term of `T∞` at an arbitrary centre

The centre-`0` analytic premises of the bridge (`Def6BridgeLift`, `Def6BridgeInfLift`) transported
to an arbitrary centre block `y ∈ X'` of a polymer of `T∞`: the average over paving offsets uses
the terms `ℰ_∞(y, X')` of all centres `y` of the box of offsets.

* `EauxC`, `EauxC_rot`, `EauxC_orth`: the class term at the centre `y` and its invariance under
  complex orthogonal matrices (from (H.3) `rotE`);
* `LiftCtx.orthC`, `LiftCtx.analyticAt_EauxC`, `LiftCtx.norm_EauxC_le`;
* `GE`: the cut-off term of `T∞` as a function of the configuration, with `GE_of_ball`,
  `GE_analyticAt`, `GE_rot`, `GE_norm_le` on the ball around the reference point.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.SmallField Balaban.Multiscale Balaban.Background Balaban.Localization Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} {ϱ : ℝ}

section CoreC

variable [NeZero L] [NeZero N₁]

/-- The class term in the centred form for the representative at the centre block `y`. -/
noncomputable def EauxC (Tm : Terms d L N₁ m₁ k N ϱ) (j : ℕ) (i₀ : Fin N) (νj : ℝ)
    (y : Site d) (X' : Finset (Site d)) (c : Cfg d N X') : ℂ :=
  Tm.E j (blockPt j y) (Ypoly j X') (fieldOf j i₀ X' c) (hOf νj X' c)

variable {P : Consts} {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ}

/-- **Rotation invariance of the centred term** (from (H.3) `rotE`): two configurations in the
ball of radius `ρ` around the reference point, related by a matrix `M` of `IsRot` type with entries
bounded by `B`, have the same term.  The domain lemma is used at the radius `ρ₂ ≥ ρ (1 + N B)`. -/
theorem EauxC_rot (hsf : IsSF P β ν a Tm ρd Ek)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (y : Site d) (hnw : NonWind L N₁ m₁ k j X') (hy : y ∈ X') (i₀ : Fin N)
    {δ ρ ρ₂ B : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hρ0 : 0 < ρ) (hB : 0 ≤ B) (hρ₂ : ρ * (1 + N * B) ≤ ρ₂) (hρ : (N : ℝ) * ρ₂ < δ ^ 2)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsRot M) (hMb : ∀ i k, ‖M i k‖ ≤ B)
    {u u' : Cfg d N X'} (hu : u ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ)
    (hu' : u' ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ) (hrot : rotCfgL M X' u = u') :
    EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X' u' = EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X' u := by
  set x₀ : CTorus d L N₁ m₁ k := blockPt j y with hx₀def
  have hx₀ : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x₀ ∈ X' :=
    blockPt_mem_Ypoly hjk hnw hy
  have hNB : 0 ≤ (N : ℝ) * B := by positivity
  have hρρ₂ : ρ ≤ ρ₂ := by nlinarith
  have hρ₂0 : 0 < ρ₂ := lt_of_lt_of_le hρ0 hρρ₂
  have ball_mono : ∀ {c : Cfg d N X'}, c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ →
      c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ₂ := fun hc => ball_subset_ball hρρ₂ hc
  have hXi := fp_mem_xiDom hsf hBg hν hj1 hjk hX i₀ hδ0 hδc0 hδc1 hρ₂0 hρ hε (ball_mono hu)
  have h0u : fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u' x₀ = M.mulVec (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u x₀) := by
    have := fieldOf_rot (j := j) (i₀ := i₀) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) M u
      (x := x₀) hx₀
    rw [← hrot, this]; rfl
  have hMe : ∀ i, ‖(M.mulVec (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤
      ρ * (1 + N * B) := by
    intro i
    have h1 := fieldOf_sub_le (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (j := j) hu' hρ0.le x₀ i
    have h2 := fun k' => fieldOf_sub_le (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (j := j) hu hρ0.le x₀ k'
    have e1 : (M.mulVec (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i =
        (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u' x₀ i - (Pi.single i₀ 1 : Fin N → ℂ) i) -
          ∑ k', M i k' * (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u x₀ k' - (Pi.single i₀ 1 : Fin N → ℂ) k') := by
      rw [h0u]
      simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e1]
    calc _ ≤ ‖fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u' x₀ i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ +
          ‖∑ k', M i k' * (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u x₀ k' - (Pi.single i₀ 1 : Fin N → ℂ) k')‖ :=
          norm_sub_le _ _
      _ ≤ ρ + ∑ _k' : Fin N, B * ρ := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' _ => ?_)
          rw [norm_mul]
          exact mul_le_mul (hMb i k') (h2 k') (norm_nonneg _) hB
      _ = ρ * (1 + N * B) := by simp; ring
  have hXirot : XiDom (Tm.gs j (Ypoly j X')) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j
      (P.eps d L j) (rotField M (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u)) (rotField M (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (ν k) j) X' u)) := by
    rw [← hOf_rot, hrot]
    refine xiDom_of_field hsf hBg hν hj1 hjk hX i₀ hδ0 hδc0 hδc1 hρ₂0 hρ hε _ (fun i => u' (Sum.inr i))
      (fun x i => ?_) (fun x x' h => ?_) (fun i => ?_)
    · by_cases hx : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x ∈ X'
      · rw [← fieldOf_rot M u hx, hrot]
        exact (fieldOf_sub_le hu' hρ0.le x i).trans hρρ₂
      · have : fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u x = (Pi.single i₀ 1 : Fin N → ℂ) := by
          funext i; simp [fieldOf, hx]
        have e : rotField M (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' u) x = M.mulVec (Pi.single i₀ 1 : Fin N → ℂ) := by
          simp [rotField, this]
        rw [e]; exact (hMe i).trans hρ₂
    · simp only [rotField]
      rw [fieldOf_block u h]
    · have := (dist_le_pi_dist u' (refPt i₀ (nuIdeal L k (ν k) j) X') (Sum.inr i)).trans_lt
        (mem_ball.1 hu')
      rw [dist_eq_norm, refPt_inr] at this
      exact this.trans_le hρρ₂
  have hr := hsf.rotE j hj1 hjk x₀ (Ypoly j X') hX hx₀ M hM _ _ hXi hXirot
  unfold EauxC
  rw [← hr]
  refine hsf.localE j x₀ (Ypoly j X') _ _ _ _ (fun x hx => ⟨?_, ?_⟩)
  · rw [← hrot, fieldOf_rot M u hx]
  · rw [← hrot, hOf_rot]



/-- **Rotation invariance for `O(N, ℂ)`**: as `Eaux_rot`, for any complex orthogonal `M`
(determinant `±1`), using one real reflection `P` of a coordinate `p ≠ i₀`. -/
theorem EauxC_orth (hsf : IsSF P β ν a Tm ρd Ek)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hν : 0 < ν k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (y : Site d) (hnw : NonWind L N₁ m₁ k j X') (hy : y ∈ X') {i₀ p : Fin N} (hp : p ≠ i₀)
    {δ ρ ρ₂ B : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hρ0 : 0 < ρ) (hB : 1 ≤ B) (hρ₂ : ρ * (1 + N * B) ≤ ρ₂) (hρ : (N : ℝ) * ρ₂ < δ ^ 2)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsOrth M) (hMb : ∀ i k, ‖M i k‖ ≤ B)
    {u u' : Cfg d N X'} (hu : u ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ)
    (hu' : u' ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ) (hrot : rotCfgL M X' u = u') :
    EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X' u' = EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X' u := by
  have hB0 : 0 ≤ B := by linarith
  rcases det_isOrth hM with hd | hd
  · exact EauxC_rot hsf hBg hν hj1 hjk hX y hnw hy i₀ hδ0 hδc0 hδc1 hρ0 hB0 hρ₂ hρ hε ⟨hM, Or.inr hd⟩
      hMb hu hu' hrot
  · -- reflect first
    set Pm := reflP N p with hPm
    have hPball : rotCfgL Pm X' u ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ := by
      rw [mem_ball, dist_eq_norm] at hu ⊢
      have e : rotCfgL Pm X' u - refPt i₀ (nuIdeal L k (ν k) j) X' =
          rotCfgL Pm X' (u - refPt i₀ (nuIdeal L k (ν k) j) X') := by
        rw [map_sub, hPm, reflP_refPt hp]
      rw [e]
      exact (rotCfgL_reflP_norm_le p X' _).trans_lt hu
    have h1 := EauxC_rot hsf hBg hν hj1 hjk hX y hnw hy i₀ hδ0 hδc0 hδc1 hρ0 hB0 hρ₂ hρ hε
      (isRot_reflP p) (fun i k => (reflP_norm_le p i k).trans hB) hu hPball rfl
    have hMP : IsRot (M * Pm) := by
      refine ⟨?_, Or.inr ?_⟩
      · rw [Matrix.transpose_mul, hPm, reflP_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc M.transpose,
          hM, Matrix.one_mul, reflP_mul_self]
      · rw [Matrix.det_mul, hd, hPm, reflP_det]; norm_num
    have hMPb : ∀ i k, ‖(M * Pm) i k‖ ≤ B := by
      intro i k
      rw [hPm]
      unfold reflP
      rw [Matrix.mul_diagonal]
      by_cases h : k = p
      · simp [h]; exact hMb i p
      · simp [h]; exact hMb i k
    have h2 := EauxC_rot hsf hBg hν hj1 hjk hX y hnw hy i₀ hδ0 hδc0 hδc1 hρ0 hB0 hρ₂ hρ hε hMP hMPb hPball
      hu' (by
        have hPP : Pm * Pm = 1 := by rw [hPm]; exact reflP_mul_self p
        rw [← rotCfgL_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]; exact hrot)
    rw [h2, h1]



variable {ρ : ℝ}

theorem LiftCtx.orthC (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (y : Site d) (hnw : NonWind L N₁ m₁ k j X') (hy : y ∈ X') {i₀ p : Fin N} (hp : p ≠ i₀)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsOrth M) (hMb : ∀ i k, ‖M i k‖ ≤ rotB N)
    {u u' : Cfg d N X'} (hu : u ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ)
    (hu' : u' ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ) (hrot : rotCfgL M X' u = u') :
    EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X' u' = EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X' u := by
  obtain ⟨δ, hδ0, hδ1, hδ2, hδ3, hδ4⟩ := ctx.radius
  exact EauxC_orth ctx.sf ctx.bg ctx.nu_pos ctx.j1 ctx.jk hX y hnw hy hp hδ0 hδ1 hδ2 ctx.rho_pos
    (one_le_rotB i₀) le_rfl hδ4 hδ3 hM hMb hu hu' hrot

theorem LiftCtx.analyticAt_EauxC (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N)
    {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (y : Site d) (hnw : NonWind L N₁ m₁ k j X') (hy : y ∈ X') {u₀ : Cfg d N X'}
    (hu : u₀ ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ) :
    AnalyticAt ℂ (EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X') u₀ := by
  have hXi := ctx.mem_xiDom i₀ hX hu
  have hE := ctx.sf.analyticE j ctx.j1 ctx.jk (blockPt j y) (Ypoly j X') hX
    (blockPt_mem_Ypoly ctx.jk hnw hy)
    (fieldOf j i₀ X' u₀, hOf (nuIdeal L k (ν k) j) X' u₀) hXi
  exact AnalyticAt.comp (g := fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
    Tm.E j (blockPt j y) (Ypoly j X') p.1 p.2)
    (f := fun c : Cfg d N X' => ((fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' c,
      hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (ν k) j) X' c) :
        Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N)) (x := u₀) hE
    (analyticAt_fp j i₀ (nuIdeal L k (ν k) j) X' u₀)

theorem LiftCtx.norm_EauxC_le (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N)
    {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (y : Site d) (hnw : NonWind L N₁ m₁ k j X') (hy : y ∈ X') {c : Cfg d N X'}
    (hXi : XiDom (Tm.gs j (Ypoly j X')) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j
      (P.eps d L j) (fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' c)
      (hOf (nuIdeal L k (ν k) j) X' c)) :
    ‖EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X' c‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X')) :=
  ctx.sf.boundE j ctx.j1 ctx.jk (blockPt j y) (Ypoly j X') hX (blockPt_mem_Ypoly ctx.jk hnw hy) _ _ hXi

end CoreC

section Z

variable [NeZero L] {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

/-- The context of the torus `n` of the sequence. -/
theorem IsSFFamily.ctxSeq (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    (i₀ : Fin N) (n : ℕ) :
    LiftCtx P β ν a (Tm (torusSeq L P.m₀ n)) (ρd (torusSeq L P.m₀ n)) (Ek (torusSeq L P.m₀ n)) j
      (liftRadius d L N P j) :=
  hF.liftCtx (torusSeq L P.m₀ n) hn.hd hn.hL hn.hϱ hn.hj1 hn.hjk
    (liftRadius_pos (eps_pos hF.admissible.α₀_pos j) i₀)
    (liftRadius_spec (eps_pos hF.admissible.α₀_pos j) i₀ hn.hsmall)

omit [NeZero L] in
/-- A bound valid with the covering size of every good torus is valid with `dInf`. -/
theorem bound_dInf {m₀ : ℕ} {X' : Finset (Fin d → ℤ)} {n₀ : ℕ}
    (hn₀ : GoodAt L m₁ k m₀ j X' n₀) {x E κ : ℝ} (hx0 : 0 ≤ x) (hκ0 : 0 ≤ κ)
    (hx : ∀ n, GoodAt L m₁ k m₀ j X' n → x ≤ E * Real.exp (-κ * sizeSeq L m₁ k m₀ j X' n)) :
    x ≤ E * Real.exp (-κ * dInf L m₁ k m₀ j X') := by
  have hE0 : 0 ≤ E := by
    have h1 := hx0.trans (hx n₀ hn₀)
    by_contra hneg
    push Not at hneg
    have : E * Real.exp (-κ * sizeSeq L m₁ k m₀ j X' n₀) < 0 :=
      mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
    linarith
  refine le_mul_exp_of_forall fun ε hε => ?_
  obtain ⟨n, hn, hlt⟩ := exists_goodAt_gt hn₀ hε
  refine (hx n hn).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hE0
  nlinarith

/-- **The cut-off term of `T∞` as a function of the configuration** of the polymer `X'` at the
centre `y`: `ℰ_∞(y, X'; ψ_c, h_c)` with the fields `ψ_c, h_c` of `ℤ^d` of the configuration. -/
noncomputable def GE (P : Consts) (β ν a : ℕ → ℝ)
    (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (j : ℕ) (i₀ : Fin N) (νj : ℝ)
    (y : Site d) (X' : Finset (Site d)) (c : Cfg d N X') : ℂ :=
  FB P β ν a Tm j ⟨X', y, fieldInfOf L j i₀ X' c, hInfOf νj X' c⟩

section GEfacts

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N}
include hF hn

/-- On the ball around the reference point the data of a configuration extend into the analyticity
domain on every torus on which the polymer is good, so the cut-off is inactive. -/
theorem GE_supp {X' : Finset (Site d)} (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {y : Site d} (hy : y ∈ X') {c : Cfg d N X'}
    (hc : c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') (liftRadius d L N P j)) :
    Supp P β ν a Tm j ⟨X', y, fieldInfOf L j i₀ X' c, hInfOf (nuIdeal L k (ν k) j) X' c⟩ := by
  refine ⟨hX, hy, ?_⟩
  show ∀ᶠ n in atTop, _
  filter_upwards [hX] with n hn'
  have ctx := hF.ctxSeq hn i₀ n
  refine ⟨fieldOf j i₀ X' c, hOf (nuIdeal L k (ν k) j) X' c, fun x _ => ?_,
    ctx.mem_xiDom i₀ hn'.2 hc⟩
  rw [pullFld_fieldInfOf, pullFld_hInfOf]
  exact ⟨rfl, rfl⟩

theorem GE_of_ball {X' : Finset (Site d)} (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {y : Site d} (hy : y ∈ X') {c : Cfg d N X'}
    (hc : c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') (liftRadius d L N P j)) :
    GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' c =
      Einf P.m₀ Tm j y X' (fieldInfOf L j i₀ X' c) (hInfOf (nuIdeal L k (ν k) j) X' c) := by
  unfold GE FB
  rw [ite_eq_left (GE_supp hF hn hX hy hc)]

theorem GE_eq_EauxC {X' : Finset (Site d)} (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {y : Site d} (hy : y ∈ X') {c : Cfg d N X'}
    (hc : c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') (liftRadius d L N P j)) {n : ℕ}
    (hgood : GoodAt L m₁ k P.m₀ j X' n) :
    GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' c =
      EauxC (Tm (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) y X' c := by
  rw [GE_of_ball hF hn hX hy hc,
    Einf_eq_torus hF.torusIndep hn.hj1 hn.hjk hy hX _ _ (torusSeq L P.m₀ n) hgood.1 hgood.2,
    pullFld_fieldInfOf, pullFld_hInfOf]
  rfl

theorem GE_analyticAt {X' : Finset (Site d)} (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {y : Site d} (hy : y ∈ X') {u₀ : Cfg d N X'}
    (hu : u₀ ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') (liftRadius d L N P j)) :
    AnalyticAt ℂ (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X') u₀ := by
  obtain ⟨n, hgood⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  have ctx := hF.ctxSeq hn i₀ n
  have han := ctx.analyticAt_EauxC i₀ hgood.2 y hgood.1 hy hu
  refine han.congr ?_
  filter_upwards [isOpen_ball.mem_nhds hu] with c hc
  exact (GE_eq_EauxC hF hn hX hy hc hgood).symm

theorem GE_rot (hne : i₁ ≠ i₀) {X' : Finset (Site d)}
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {y : Site d} (hy : y ∈ X') {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsOrth M)
    (hMb : ∀ i k, ‖M i k‖ ≤ rotB N) {u u' : Cfg d N X'}
    (hu : u ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') (liftRadius d L N P j))
    (hu' : u' ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') (liftRadius d L N P j))
    (hrot : rotCfgL M X' u = u') :
    GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' u' =
      GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' u := by
  obtain ⟨n, hgood⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  have ctx := hF.ctxSeq hn i₀ n
  rw [GE_eq_EauxC hF hn hX hy hu' hgood, GE_eq_EauxC hF hn hX hy hu hgood]
  exact ctx.orthC hgood.2 y hgood.1 hy hne hM hMb hu hu' hrot

theorem GE_norm_le {X' : Finset (Site d)} (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {y : Site d} (hy : y ∈ X') {c : Cfg d N X'}
    (hc : c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') (liftRadius d L N P j)) :
    ‖GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' c‖ ≤
      P.E₀ * Real.exp (-P.κ * dInf L m₁ k P.m₀ j X') := by
  obtain ⟨n₀, hgood₀⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  refine bound_dInf hgood₀ (norm_nonneg _) hF.admissible.κ_pos.le fun n hgood => ?_
  have ctx := hF.ctxSeq hn i₀ n
  rw [GE_eq_EauxC hF hn hX hy hc hgood]
  exact ctx.norm_EauxC_le i₀ hgood.2 y hgood.1 hy (ctx.mem_xiDom i₀ hgood.2 hc)

end GEfacts

end Z

end Balaban.SmallField.Def6
