/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CovarianceGeom

/-!
# Uniform kernel decay of the unit-lattice resolvent (FLUCTUATION.md Lemma 2.4)

For the concrete unit lattice (`unitQ`, `unitP`) the decoupled covariance at `s = 1`,
`C_x = (x + 𝒜)⁻¹`, satisfies the two-sided Agmon weighted bound
`‖e^{ε ρ} C_x h‖ ≤ K (a_k + x)⁻¹ ‖e^{ε ρ} h‖` (`cov_weighted_bound`), `ρ` the block minimum of an
Agmon weight and `K = covDecayConst`, and hence the entry bound
`|C_x(p,i; q,i')| ≤ K' (a_k + x)⁻¹ e^{-(γ/L) dist(p,q)}` uniform in `x ≥ 0`
(`cov_entry_decay`), `dist` the `ℓ¹` distance of the unit torus.
-/

@[expose] public section

open Balaban Balaban.Localization Balaban.Multiscale Finset Matrix

namespace Balaban.Fluctuation


section Weighted

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {r : CTorus d L N₁ m₁ (k + 1) → ℝ}

theorem cov_r_le_unitRho_add (hr : IsAgmonWeight G r) {b : UnitTorus d L N₁ m₁ k}
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : unitBlock y = b) (hyl : y ∈ G.layer (k + 1)) :
    r y ≤ unitRho r b + 2 * d := by
  obtain ⟨y0, hy0, he⟩ := exists_unitRho_eq r b
  have hy0l : y0 ∈ G.layer (k + 1) := layer_of_unitBlock G (hy.trans hy0.symm) hyl
  have hj := jBlock_eq_of_unitBlock_eq (hy.trans hy0.symm)
  have hb := hr.block (k + 1) (by omega) le_rfl y0 y hy0l hj
  rw [he]
  have := (abs_le.1 hb).1
  linarith

theorem cov_unitRho_P (hr : IsAgmonWeight G r) (b b' : unitPts G) (h : unitP G b b' ≠ 0) :
    unitRho r b.1 ≤ unitRho r b'.1 + 2 * d := by
  obtain ⟨y0, hy0, he0⟩ := exists_unitRho_eq r b.1
  obtain ⟨y1, hy1, he1⟩ := exists_unitRho_eq r b'.1
  have hP1 : unitBlock1 b.1 = unitBlock1 b'.1 := by
    by_contra hne; apply h; simp [unitP, hne]
  have hy0l : y0 ∈ G.layer (k + 1) := (unitBlock_mem_iff G y0).1 (hy0 ▸ b.2)
  have hj : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y1 =
      jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y0 := by
    rw [← unitBlock1_unitBlock, ← unitBlock1_unitBlock, hy0, hy1]; exact hP1.symm
  have hb := hr.block (k + 1) (by omega) le_rfl y0 y1 hy0l hj
  rw [he0, he1]
  have := (abs_le.1 hb).2
  linarith

theorem cov_unitRho_Q (b : unitPts G) (y : G.Ω 1) (h : unitQ G b y ≠ 0) :
    unitRho r b.1 ≤ r y := by
  refine unitRho_le _ ?_
  by_contra hne; apply h; simp [unitQ, hne]

theorem cov_unitRho_nonneg (hr0 : ∀ y, 0 ≤ r y) (b : UnitTorus d L N₁ m₁ k) : 0 ≤ unitRho r b := by
  obtain ⟨y, _, he⟩ := exists_unitRho_eq r b
  rw [he]; exact hr0 y

theorem cov_QT_apply (z : unitPts G × Fin N → ℂ) (y : G.Ω 1) (i : Fin N) :
    ((liftRect N (unitQ G))ᵀ *ᵥ z) (y, i) =
      if h : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ∈ unitPts G then
        ((Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹) : ℝ) : ℂ) * z (⟨_, h⟩, i) else 0 := by
  classical
  rw [liftRect_transpose, liftRect_mulVec]
  simp only [mulVec, dotProduct, transpose_apply, unitQ]
  by_cases h : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ∈ unitPts G
  · rw [Finset.sum_eq_single (⟨unitBlock (y : CTorus d L N₁ m₁ (k + 1)), h⟩ : unitPts G)]
    · simp [h]
    · intro b _ hb
      have : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
        intro e; apply hb; exact Subtype.ext e.symm
      simp [this]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [Finset.sum_eq_zero]
    · simp [h]
    · intro b _
      have : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
        intro e; exact h (e ▸ b.2)
      simp [this]


theorem cov_vecSrc_QT_le (hr : IsAgmonWeight G r) {ε : ℝ} (hε : 0 ≤ ε)
    (z : unitPts G × Fin N → ℂ) :
    vecSrc G ε r ((liftRect N (unitQ G))ᵀ *ᵥ z) ≤
      ((L : ℝ) ^ (k + 1)) ^ 2 * Real.exp (ε * (2 * d)) ^ 2 *
        ∑ p : unitPts G × Fin N, Real.exp (ε * unitRho r p.1) ^ 2 * ‖z p‖ ^ 2 := by
  classical
  set q : ℝ := Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹) with hq
  have hLk : (0 : ℝ) < ((L ^ k : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k
  have hq2 : q ^ 2 * (((L ^ k : ℕ) : ℝ) ^ d) = 1 := by
    have hc : (0 : ℝ) ≤ (((L ^ k : ℕ) : ℝ) ^ d)⁻¹ := by positivity
    have hpos : (0 : ℝ) < ((L ^ k : ℕ) : ℝ) ^ d := by positivity
    rw [hq, Real.sq_sqrt hc]; field_simp
  unfold vecSrc
  simp only [agmonSource_eq]
  set g : Fin N → unitPts G → ℝ := fun i b => ((L : ℝ) ^ (k + 1)) ^ 2 * Real.exp (ε * (2 * d)) ^ 2 *
    (q ^ 2 * (Real.exp (ε * unitRho r b.1) ^ 2 * ‖z (b, i)‖ ^ 2)) with hg
  have hg0 : ∀ i b, 0 ≤ g i b := fun i b => by positivity
  have hpt : ∀ (i : Fin N) (y : G.Ω 1),
      G.spacing y ^ 2 * Real.exp (ε * r y) ^ 2 *
        ‖Balaban.Multiscale.comp G ((liftRect N (unitQ G))ᵀ *ᵥ z) i y‖ ^ 2 ≤
      ∑ b : unitPts G, (if unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = b.1 then g i b else 0) := by
    intro i y
    by_cases h : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ∈ unitPts G
    · rw [Finset.sum_eq_single (⟨unitBlock (y : CTorus d L N₁ m₁ (k + 1)), h⟩ : unitPts G)]
      · simp only [ite_true]
        have hyl : (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) :=
          (unitBlock_mem_iff G _).1 h
        have hsp := G.spacing_eq (by omega : 1 ≤ k + 1) le_rfl hyl
        have hw : Balaban.Multiscale.comp G ((liftRect N (unitQ G))ᵀ *ᵥ z) i y =
            (q : ℂ) * z (⟨_, h⟩, i) := by
          unfold Balaban.Multiscale.comp
          rw [cov_QT_apply]; simp [h, hq]
        have hrle := cov_r_le_unitRho_add hr rfl hyl
        have hexp : Real.exp (ε * r y) ≤ Real.exp (ε * unitRho r (unitBlock (y : CTorus d L N₁ m₁ (k + 1)))) *
            Real.exp (ε * (2 * d)) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.2 (by nlinarith)
        rw [hw, hsp, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        simp only [hg]
        have h0 : 0 ≤ Real.exp (ε * r y) := (Real.exp_pos _).le
        have h1 : Real.exp (ε * r y) ^ 2 ≤ (Real.exp (ε * unitRho r (unitBlock (y : CTorus d L N₁ m₁ (k + 1)))) *
            Real.exp (ε * (2 * d))) ^ 2 := pow_le_pow_left₀ h0 hexp 2
        have hq2' : q ^ 2 * ‖z (⟨_, h⟩, i)‖ ^ 2 = (q * ‖z (⟨_, h⟩, i)‖) ^ 2 := by ring
        calc ((L : ℝ) ^ (k + 1)) ^ 2 * Real.exp (ε * r y) ^ 2 * (q * ‖z (⟨_, h⟩, i)‖) ^ 2
            ≤ ((L : ℝ) ^ (k + 1)) ^ 2 * (Real.exp (ε * unitRho r (unitBlock (y : CTorus d L N₁ m₁ (k + 1)))) *
              Real.exp (ε * (2 * d))) ^ 2 * (q * ‖z (⟨_, h⟩, i)‖) ^ 2 := by gcongr
          _ = _ := by ring
      · intro b _ hb
        have : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
          intro e; apply hb; exact Subtype.ext e.symm
        simp [this]
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · have hw : Balaban.Multiscale.comp G ((liftRect N (unitQ G))ᵀ *ᵥ z) i y = 0 := by
        unfold Balaban.Multiscale.comp
        rw [cov_QT_apply]; simp [h]
      rw [hw]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      exact Finset.sum_nonneg fun b _ => by
        split_ifs
        · exact hg0 i b
        · exact le_rfl
  calc ∑ i : Fin N, ∑ y : G.Ω 1, G.spacing y ^ 2 * Real.exp (ε * r y) ^ 2 *
          ‖Balaban.Multiscale.comp G ((liftRect N (unitQ G))ᵀ *ᵥ z) i y‖ ^ 2
      ≤ ∑ i : Fin N, ∑ y : G.Ω 1, ∑ b : unitPts G,
          (if unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = b.1 then g i b else 0) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun y _ => hpt i y
    _ = ∑ i : Fin N, ∑ b : unitPts G, g i b * (((L ^ k : ℕ) : ℝ) ^ d) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        have := sum_unit_fibre G b.2
        rw [← this, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> simp
    _ = _ := by
        rw [Fintype.sum_prod_type_right, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [hg]
        calc _ = ((L : ℝ) ^ (k + 1)) ^ 2 * Real.exp (ε * (2 * d)) ^ 2 *
              (Real.exp (ε * unitRho r b.1) ^ 2 * ‖z (b, i)‖ ^ 2) *
              (q ^ 2 * (((L ^ k : ℕ) : ℝ) ^ d)) := by ring
          _ = _ := by rw [hq2]; ring


section Main

variable {κι : Type*} [Fintype κι]

/-- The weighted vector `e^{ε ρ} h`. -/
noncomputable def covWVec (ε : ℝ) (ρ : κι → ℝ) (h : κι × Fin N → ℂ) : κι × Fin N → ℂ :=
  fun p => ((Real.exp (ε * ρ p.1) : ℝ) : ℂ) * h p

theorem covWVec_sqNorm (ε : ℝ) (ρ : κι → ℝ) (h : κι × Fin N → ℂ) :
    Green.sqNorm (covWVec ε ρ h) = ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 * ‖h p‖ ^ 2 := by
  unfold Green.sqNorm covWVec
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]

omit [Fintype κι] in
theorem covWVec_add (ε : ℝ) (ρ : κι → ℝ) (u v : κι × Fin N → ℂ) :
    covWVec ε ρ (u + v) = covWVec ε ρ u + covWVec ε ρ v := by
  funext p; simp [covWVec, mul_add]

omit [Fintype κι] in
theorem covWVec_smul (ε : ℝ) (ρ : κι → ℝ) (c : ℂ) (v : κι × Fin N → ℂ) :
    covWVec ε ρ (c • v) = c • covWVec ε ρ v := by
  funext p; simp [covWVec]; ring

end Main

section Decay

variable {yq : CTorus d L N₁ m₁ (k + 1)} {a : ℕ → ℝ} {aT ν : ℝ} {α : G.Ω 1 → ℂ} {δ : ℝ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

/-- The constant of the weighted covariance bound. -/
noncomputable def covDecayConst (d L : ℕ) (ak ε : ℝ) : ℝ :=
  2 * Real.exp (2 * d * ε) *
    (1 + 2 * ak * (L : ℝ) ^ 2 * Real.sqrt (92 * valConstX d) * Real.exp (4 * d * ε))


theorem cov_decay_arith {d L : ℕ} {ak x ε c Λ : ℝ} (hak : 0 < ak) (hx : 0 ≤ x)
    (hcΛ : c * Λ ^ 2 = ak ^ 2 * (L : ℝ) ^ 2) :
    (1 + c * (2 * Real.exp (ε * (2 * d)) * (ak + x)⁻¹) *
        (Λ ^ 2 * Real.sqrt (92 * valConstX d) * Real.exp (ε * (2 * d)))) *
      (2 * Real.exp (ε * (2 * d)) * (ak + x)⁻¹) ≤ covDecayConst d L ak ε * (ak + x)⁻¹ := by
  have hcx : 0 < ak + x := by linarith
  set α0 := (ak + x)⁻¹ with hα0
  have hα0p : 0 < α0 := inv_pos.2 hcx
  set E := Real.exp (ε * (2 * d)) with hE
  set S := Real.sqrt (92 * valConstX d) with hS
  have hE0 : 0 < E := Real.exp_pos _
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have haα : ak ^ 2 * α0 ≤ ak := by
    rw [hα0, ← div_eq_mul_inv, div_le_iff₀ hcx]; nlinarith [sq_nonneg ak]
  have e1 : c * (2 * E * α0) * (Λ ^ 2 * S * E) = 2 * (ak ^ 2 * α0) * (L : ℝ) ^ 2 * S * E ^ 2 := by
    calc _ = (c * Λ ^ 2) * (2 * E * α0 * S * E) := by ring
      _ = _ := by rw [hcΛ]; ring
  have hE2 : E ^ 2 = Real.exp (4 * d * ε) := by
    rw [hE, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hE1 : E = Real.exp (2 * d * ε) := by rw [hE]; ring_nf
  have hXY : 2 * (ak ^ 2 * α0) * (L : ℝ) ^ 2 * S * Real.exp (4 * d * ε) ≤
      2 * ak * (L : ℝ) ^ 2 * S * Real.exp (4 * d * ε) := by
    have h0 : 0 ≤ 2 * (L : ℝ) ^ 2 * S * Real.exp (4 * d * ε) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right haα h0]
  rw [e1, hE2]
  unfold covDecayConst
  rw [← hE1]
  have h2 : 0 ≤ 2 * E * α0 := by positivity
  calc _ ≤ (1 + 2 * ak * (L : ℝ) ^ 2 * S * Real.exp (4 * d * ε)) * (2 * E * α0) :=
        mul_le_mul_of_nonneg_right (by linarith) h2
    _ = _ := by ring

theorem cov_weighted_bound (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    {x : ℝ} (hx : 0 ≤ x) {ε : ℝ} (hr : XWeight G ε r) (h : unitPts G × Fin N → ℂ) :
    n2 (covWVec ε (fun b : unitPts G => unitRho r b.1)
        (decCov G a aT x ν α (fun _ => 1) φ (unitQ G) (unitP G) *ᵥ h)) ≤
      covDecayConst d L (a k) ε * ((a k + x)⁻¹) *
        n2 (covWVec ε (fun b : unitPts G => unitRho r b.1) h) := by
  classical
  have D := hfam x hx
  have hU := (isUnitLatticeB_unit (G := G)).toIsUnitLattice
  have hk := D.st.hk
  have hak : a k ∈ Set.Icc (1 / 2 : ℝ) 2 := D.st.ha k hk le_rfl
  have hcx : 0 < a k + x := by have := D.x0; linarith [hak.1]
  have hb : 0 ≤ aT / (L : ℝ) ^ 2 := by
    have := D.st.haT1
    positivity
  obtain ⟨hPh, hPi⟩ := liftOp_herm_idem (N := N) hU
  have hPh' : (unitP G)ᴴ = unitP G := hU.herm
  have hPi' : unitP G * unitP G = unitP G := hU.idem
  set ρ : unitPts G → ℝ := fun b => unitRho r b.1 with hρ
  set Av := covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G)) with hAv
  set cs : ℂ := (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ) with hcs
  set Λ : ℝ := (L : ℝ) ^ (k + 1) with hΛ
  set α0 : ℝ := (a k + x)⁻¹ with hα0
  have hα0p : 0 < α0 := inv_pos.2 hcx
  have hε0 := hr.ε0
  set A1 : ℝ := 2 * Real.exp (ε * (2 * d)) * α0 with hA1
  have hA1p : 0 ≤ A1 := by positivity
  have hAv : ∀ g : unitPts G × Fin N → ℂ,
      n2 (covWVec ε ρ (Av *ᵥ g)) ≤ A1 * n2 (covWVec ε ρ g) := by
    intro g
    have h1 := sum_w_covA_le (ρ := ρ) (ε := ε) (c₀ := 2 * d) hε0 (by positivity)
      (fun b b' hbb => cov_unitRho_P hr.agm b b' hbb) hPh' hPi'
      (fun b b' => unitP_nonneg_real b b') hcx hb g
    rw [← covWVec_sqNorm, ← covWVec_sqNorm] at h1
    exact (sqNorm_le_iff hA1p).1 h1
  -- decompose
  have hdec : decCov G a aT x ν α (fun _ => 1) φ (unitQ G) (unitP G) *ᵥ h =
      Av *ᵥ h + cs • (Av *ᵥ (liftRect N (unitQ G) *ᵥ (decZ G a aT x ν α (fun _ => 1) φ *ᵥ
        ((liftRect N (unitQ G))ᵀ *ᵥ (Av *ᵥ h))))) := by
    unfold decCov decZ
    rw [Matrix.add_mulVec, Matrix.smul_mulVec]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rfl
  set z := Av *ᵥ h with hz
  set w := (liftRect N (unitQ G))ᵀ *ᵥ z with hw
  set u := decZ G a aT x ν α (fun _ => 1) φ *ᵥ w with hu
  set v := liftRect N (unitQ G) *ᵥ u with hv
  have hz1 : n2 (covWVec ε ρ z) ≤ A1 * n2 (covWVec ε ρ h) := hAv h
  have hsrc := cov_vecSrc_QT_le (N := N) hr.agm hε0 z
  have hZ : vecM G ε r u ≤ 92 * valConstX d * vecSrc G ε r w := by
    have hG := Gsx_vec_bounds D hr w
    have hP := decPi_weighted_bounds D hr hφ hδ hsm w
    have hsub : u = liftOp N (Gsx G a aT x ν α (fun _ => 1)) *ᵥ w -
        decPi G a aT x ν α (fun _ => 1) φ *ᵥ w := by
      rw [hu]; unfold decZ; rw [Matrix.sub_mulVec]
    have h1 := vecM_sub_le (G := G) ε r (liftOp N (Gsx G a aT x ν α (fun _ => 1)) *ᵥ w)
      (decPi G a aT x ν α (fun _ => 1) φ *ᵥ w)
    rw [← hsub] at h1
    simp only [mul_zero, Real.exp_zero, one_pow, mul_one] at hG hP
    nlinarith [hG.1, hP.1]
  have hv1 : Green.sqNorm (covWVec ε ρ v) ≤ Λ ^ 2 * vecM G ε r u := by
    rw [covWVec_sqNorm]
    exact sum_wQ_vec_le hU (fun b y => unitQ_nonneg_real b y)
      (fun b y hby => cov_unitRho_Q b y hby) hε0 u
  have hV0 : 0 ≤ valConstX d := by unfold valConstX; positivity
  set S : ℝ := Real.sqrt (92 * valConstX d) with hS
  have hS2 : S ^ 2 = 92 * valConstX d := Real.sq_sqrt (by positivity)
  set E : ℝ := Real.exp (ε * (2 * d)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hvz : n2 (covWVec ε ρ v) ≤ (Λ ^ 2 * S * E) * n2 (covWVec ε ρ z) := by
    rw [← sqNorm_le_iff (by positivity)]
    have hsrc' : vecSrc G ε r w ≤ Λ ^ 2 * E ^ 2 * Green.sqNorm (covWVec ε ρ z) := by
      rw [covWVec_sqNorm]; exact hsrc
    have hΛ0 : 0 ≤ Λ ^ 2 := by positivity
    calc Green.sqNorm (covWVec ε ρ v) ≤ Λ ^ 2 * vecM G ε r u := hv1
      _ ≤ Λ ^ 2 * (92 * valConstX d * vecSrc G ε r w) := by gcongr
      _ ≤ Λ ^ 2 * (92 * valConstX d * (Λ ^ 2 * E ^ 2 * Green.sqNorm (covWVec ε ρ z))) := by
          gcongr
      _ = (Λ ^ 2 * S * E) ^ 2 * Green.sqNorm (covWVec ε ρ z) := by
          rw [mul_pow, mul_pow, hS2]; ring
  have hy2 : n2 (covWVec ε ρ (Av *ᵥ v)) ≤ A1 * n2 (covWVec ε ρ v) := hAv v
  have hcsn : ‖cs‖ = (a k) ^ 2 / (L : ℝ) ^ (2 * k) := by
    rw [hcs, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hcsΛ : ‖cs‖ * Λ ^ 2 = (a k) ^ 2 * (L : ℝ) ^ 2 := by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    rw [hcsn, hΛ]; field_simp; ring
  rw [hdec, covWVec_add, covWVec_smul]
  refine (n2_add_le _ _).trans ?_
  rw [n2_smul]
  have hcs0 : 0 ≤ ‖cs‖ := norm_nonneg _
  have hn0 := n2_nonneg (covWVec ε ρ h)
  have hz0 := n2_nonneg (covWVec ε ρ z)
  have hv0 := n2_nonneg (covWVec ε ρ v)
  have hstep : n2 (covWVec ε ρ z) + ‖cs‖ * n2 (covWVec ε ρ (Av *ᵥ v)) ≤
      (1 + ‖cs‖ * A1 * (Λ ^ 2 * S * E)) * n2 (covWVec ε ρ z) := by
    have : ‖cs‖ * n2 (covWVec ε ρ (Av *ᵥ v)) ≤ ‖cs‖ * (A1 * ((Λ ^ 2 * S * E) * n2 (covWVec ε ρ z))) :=
      mul_le_mul_of_nonneg_left (hy2.trans (mul_le_mul_of_nonneg_left hvz hA1p)) hcs0
    nlinarith
  have hM : 0 ≤ 1 + ‖cs‖ * A1 * (Λ ^ 2 * S * E) := by positivity
  have hfin : (1 + ‖cs‖ * A1 * (Λ ^ 2 * S * E)) * A1 ≤ covDecayConst d L (a k) ε * α0 :=
    cov_decay_arith (d := d) (L := L) (ε := ε) (by linarith [hak.1]) D.x0 hcsΛ
  calc _ ≤ (1 + ‖cs‖ * A1 * (Λ ^ 2 * S * E)) * n2 (covWVec ε ρ z) := hstep
    _ ≤ (1 + ‖cs‖ * A1 * (Λ ^ 2 * S * E)) * (A1 * n2 (covWVec ε ρ h)) :=
        mul_le_mul_of_nonneg_left hz1 hM
    _ = ((1 + ‖cs‖ * A1 * (Λ ^ 2 * S * E)) * A1) * n2 (covWVec ε ρ h) := by ring
    _ ≤ (covDecayConst d L (a k) ε * α0) * n2 (covWVec ε ρ h) :=
        mul_le_mul_of_nonneg_right hfin hn0
    _ = _ := by ring


theorem cov_siteSetDist_self_trunc (hyq : yq ∈ G.Ω 1) (T : ℝ) :
    truncSetDistR G {yq} T yq = 0 := by
  have : siteSetDist G {yq} yq = 0 := by
    unfold siteSetDist
    simp [GeneratingSet.pathDist_self hyq]
  unfold truncSetDistR
  rw [this]; simp

omit [NeZero N₁] in
theorem cov_entry_le_n2 {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ℝ) (ρ : ι → ℝ)
    (M : Matrix (ι × Fin N) (ι × Fin N) ℂ) (p q : ι) (i i' : Fin N) :
    Real.exp (ε * ρ p) * ‖M (p, i) (q, i')‖ ≤
      n2 (covWVec ε ρ (M *ᵥ (Pi.single (q, i') 1 : ι × Fin N → ℂ))) := by
  unfold n2
  refine Real.le_sqrt_of_sq_le ?_
  rw [covWVec_sqNorm]
  have hv : (M *ᵥ (Pi.single (q, i') 1 : ι × Fin N → ℂ)) (p, i) = M (p, i) (q, i') := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hs1 := Finset.single_le_sum (f := fun p' : ι × Fin N =>
      Real.exp (ε * ρ p'.1) ^ 2 * ‖(M *ᵥ (Pi.single (q, i') 1 : ι × Fin N → ℂ)) p'‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ (p, i))
  simp only [hv] at hs1
  rw [mul_pow]; exact hs1

omit [NeZero N₁] in
theorem cov_n2_single {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ℝ) (ρ : ι → ℝ) (q : ι)
    (i' : Fin N) : n2 (covWVec ε ρ (Pi.single (q, i') 1 : ι × Fin N → ℂ)) = Real.exp (ε * ρ q) := by
  unfold n2
  rw [covWVec_sqNorm, Finset.sum_eq_single (q, i')]
  · simp [Real.sqrt_sq (Real.exp_pos _).le]
  · intro b _ hb; simp [hb]
  · simp

theorem cov_exists_weight (p q : unitPts G) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ xAgmonRate d L) :
    ∃ r : CTorus d L N₁ m₁ (k + 1) → ℝ, XWeight G ε r ∧ unitRho r q.1 = 0 ∧
      max 0 ((Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1 - d) / L) ≤
        unitRho r p.1 := by
  classical
  obtain ⟨yq, hyq, hyqb⟩ := (mem_unitPts G).1 q.2
  have hyqΩ : yq ∈ G.Ω 1 := G.layer_subset (by omega) le_rfl hyq
  set ud := Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1 with hud
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set Dd : ℝ := max 0 ((ud - d) / L) with hDd
  have hD0 : 0 ≤ Dd := le_max_left _ _
  have hr := isAgmonWeight_truncSetDistR G ({yq} : Finset (CTorus d L N₁ m₁ (k + 1))) Dd
  refine ⟨truncSetDistR G ({yq} : Finset (CTorus d L N₁ m₁ (k + 1))) Dd, ⟨hr, hε0, hε1⟩, ?_, ?_⟩
  · have hr0 : ∀ y, 0 ≤ truncSetDistR G ({yq} : Finset (CTorus d L N₁ m₁ (k + 1))) Dd y :=
      fun y => ENNReal.toReal_nonneg
    refine le_antisymm ?_ (cov_unitRho_nonneg hr0 _)
    have := unitRho_le (truncSetDistR G ({yq} : Finset (CTorus d L N₁ m₁ (k + 1))) Dd) hyqb
    rwa [cov_siteSetDist_self_trunc hyqΩ] at this
  · refine unitRho_ge hD0 fun y hy => cov_ofReal_le_siteSetDist fun w hw => ?_
    rw [Finset.mem_singleton] at hw
    subst hw
    have h1 := cov_unit_torusDist_le y w
    rw [hy, hyqb] at h1
    have h2 := torusDist_nonneg' (d := d) (L := L) (N₀ := N₁ * L ^ m₁) (k := k + 1) y w
    rcases le_total 0 ((ud - d) / L) with hc | hc
    · rw [hDd, max_eq_right hc]
      have : (ud - d) / L * (L : ℝ) ^ (k + 1) = (ud - d) * (L : ℝ) ^ k := by
        field_simp; ring
      rw [this]; nlinarith
    · rw [hDd, max_eq_left hc]; simpa using h2

theorem cov_entry_decay (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    {x : ℝ} (hx : 0 ≤ x) (p q : unitPts G) (i i' : Fin N) :
    ‖decCov G a aT x ν α (fun _ => 1) φ (unitQ G) (unitP G) (p, i) (q, i')‖ ≤
      covDecayConst d L (a k) (xAgmonRate d L) *
        Real.exp (xAgmonRate d L * d / L) * (a k + x)⁻¹ *
        Real.exp (-(xAgmonRate d L / L) *
          Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1) := by
  classical
  have hε0 := xAgmonRate_nonneg_of_fam hfam
  set ε := xAgmonRate d L with hε
  set ud := Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1 with hud
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨r, WW, hρq, hρp⟩ := cov_exists_weight (G := G) p q hε0 (le_refl ε)
  have hDd1 : (ud - d) / L ≤ unitRho r p.1 := (le_max_right _ _).trans hρp
  set M := decCov G a aT x ν α (fun _ => 1) φ (unitQ G) (unitP G) with hM
  have hmain := cov_weighted_bound hfam hφ hδ hsm hx WW
    (Pi.single (q, i') 1 : unitPts G × Fin N → ℂ)
  rw [cov_n2_single, hρq, mul_zero, Real.exp_zero, mul_one] at hmain
  have hent := cov_entry_le_n2 (N := N) ε (fun b : unitPts G => unitRho r b.1) M p q i i'
  have hKnn : 0 ≤ covDecayConst d L (a k) ε * (a k + x)⁻¹ := by
    have D := hfam x hx
    have hak := D.st.ha k D.st.hk le_rfl
    have : 0 < a k + x := by linarith [hak.1, D.x0]
    have hα : 0 ≤ (a k + x)⁻¹ := inv_nonneg.2 this.le
    have hak0 : 0 ≤ a k := by linarith [hak.1]
    unfold covDecayConst
    have : 0 ≤ valConstX d := by unfold valConstX; positivity
    positivity
  have hpos : 0 < Real.exp (ε * unitRho r p.1) := Real.exp_pos _
  have hfin : ‖M (p, i) (q, i')‖ ≤
      covDecayConst d L (a k) ε * (a k + x)⁻¹ * Real.exp (-(ε * unitRho r p.1)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
    exact hent.trans hmain
  have hexp : Real.exp (-(ε * unitRho r p.1)) ≤
      Real.exp (ε * d / L) * Real.exp (-(ε / L) * ud) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have : ε * ((ud - d) / L) ≤ ε * unitRho r p.1 := mul_le_mul_of_nonneg_left hDd1 hε0
    have e : ε * ((ud - d) / L) = ε * ud / L - ε * d / L := by ring
    have e2 : -(ε / L) * ud = -(ε * ud / L) := by ring
    rw [e2]; linarith
  calc _ ≤ _ := hfin
    _ ≤ covDecayConst d L (a k) ε * (a k + x)⁻¹ *
          (Real.exp (ε * d / L) * Real.exp (-(ε / L) * ud)) :=
        mul_le_mul_of_nonneg_left hexp hKnn
    _ = _ := by ring

end Decay

end Weighted
end Balaban.Fluctuation
