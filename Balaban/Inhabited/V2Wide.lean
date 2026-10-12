/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2Inhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-6 v2: field-dependent terms on the wide domain at positive mass

The bound `‖h‖ ≤ 2` on `Ξ^c_j(𝔹_j; 1, ε_j)` at the positive mass `μ` when `ε_j ≤ μ / 2` and
`μ ≤ 1` (`vn_le_two_of_xiDom`; the bound `‖h‖ ≤ 1 + 2/ν` of `hBh_of_xi` restated for the
domain `xiFieldDom`, with the explicit smallness of the radius), the term clauses for
`pinTerms` needing the bound only on the level generating set (`pinTerms_clausesB`), and a member
of `IsSFFamily2` on the wide domain `xiFieldDom` at the complete mass, with the nonzero
`h`-dependent terms `ℳ^{(j)}` (`isSFFamily2_xi_witness_M`).
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The bound on `h` on the wide domain at positive mass**: if `Ω₁ = 𝕋`, `0 < μ ≤ 1`,
`ε ≤ μ/2`, then every `h` of `Ξ^c_j(𝔹; 1, ε)` satisfies `‖h(x)‖ ≤ 2`. -/
theorem vn_le_two_of_xiDom {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ} {μ ε : ℝ}
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hε : ε ≤ μ / 2) (hΩ : ∀ x, x ∈ G.Ω 1) {j : ℕ}
    {Ψ h : Fld d L N₁ m₁ k N} (hd : XiDom G a μ j ε Ψ h) (x : CTorus d L N₁ m₁ k) :
    vn (h x) ≤ 2 := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', _, hh, hσ, hε0, Dr, Dc, hXi, _, _, hB⟩ := hd
  have hn := hXi.2.2.hnorm
  have ha := hB.hAbs x (hΩ x)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hp1 : (1 : ℝ) ≤ ((L : ℝ) ^ j) ^ 2 := one_le_pow₀ (one_le_pow₀ hL1)
  set S := ∑ i, h₀ i ^ 2 with hS
  have h1 : μ * |S - 1| < ε ^ 2 := by
    have := mul_le_mul_of_nonneg_right hp1 (mul_nonneg hμ.le (abs_nonneg (S - 1)))
    nlinarith
  have hS2 : S ≤ 3 / 2 := by
    have h3 : ε ^ 2 ≤ μ * (μ / 2) := by nlinarith
    have h4 := le_abs_self (S - 1)
    nlinarith
  have hv0 : vn (fun i => (h₀ i : ℂ)) ≤ 3 / 2 := by
    have e : vn (fun i => (h₀ i : ℂ)) ^ 2 = S := by
      rw [vn_sq]; simp [hS]
    nlinarith [vn_nonneg (fun i => (h₀ i : ℂ))]
  have hlay : (1 : ℝ) ≤ ((L : ℝ) ^ G.layerIndex x) ^ 2 := one_le_pow₀ (one_le_pow₀ hL1)
  have hv1 : vn (h'' x) ≤ 1 / 2 := by
    have e : (1 * ε) ^ 2 / ε = ε := by field_simp
    rw [e] at ha
    have := mul_le_mul_of_nonneg_right hlay (mul_nonneg hμ.le (vn_nonneg (h'' x)))
    have h5 : μ * vn (h'' x) < ε := by nlinarith
    have h6 : vn (h'' x) < ε / μ := by rw [lt_div_iff₀ hμ]; linarith
    have h7 : ε / μ ≤ 1 / 2 := by rw [div_le_iff₀ hμ]; linarith
    linarith
  have e : h x = (fun i => (h₀ i : ℂ)) + h'' x := funext fun i => by simpa using hh x i
  rw [e]
  linarith [vn_add (fun i => (h₀ i : ℂ)) (h'' x)]

/-- **The field-dependent terms satisfy the term clauses** on every field domain on which the
field is bounded by `2` at the level generating sets `𝔹_j` (the only ones the terms use). -/
theorem pinTerms_clausesB {P : Consts} {cj : ℕ → ℝ} {Dom : FieldDom d L N₁ m₁ k N ϱ}
    (hE₀ : 0 ≤ P.E₀) (hκ : 0 ≤ P.κ) (hc0 : ∀ j, 0 ≤ cj j)
    (hc : ∀ j, 20 * cj j ≤ P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hc9 : ∀ j, 0 < P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hB : ∀ j, 1 ≤ j → ∀ (hjk : j ≤ k), cj j ≠ 0 → ∀ Ψ h, Dom.dom j (levelGS j hjk) Ψ h → ∀ x, vn (h x) ≤ 2) :
    SFTermClauses P Dom (pinTerms d L N₁ m₁ k N ϱ P.κ cj) where
  gs_spec := by
    intro j hj1 hjk X _
    rw [pinTerms_gs hjk]
    refine ⟨?_, ?_⟩
    · intro x _
      simp [levelGS, hj1]
    · intro i hi
      have : ¬ i ≤ j := by omega
      simp [levelGS, this]
  analyticE := fun j _ _ y X _ _ => analyticOnNhd_const
  analyticM := fun j _ _ x X _ _ p _ => by
    set T : (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N) →L[ℂ] (Fin N → ℂ) :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ k => Fin N → ℂ) x).comp
        ((ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)) with hT
    have h1 : AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
        mCore (T p)) p := (mCore_analyticAt (T p)).comp (T.analyticAt p)
    have h0 : AnalyticAt ℂ (fun _ : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
        ((wCoef P.κ cj j X : ℝ) : ℂ)) p := analyticAt_const
    exact h0.smul h1
  rotE := by intros; rfl
  pavingGS := by
    intro j hj1 hjk X _ r _ i
    rw [pinTerms_gs hjk, pinTerms_gs hjk]
    by_cases hi : i ≤ j <;> simp [levelGS, hi]
  eucE := by intros; rfl
  eucEloc := by
    intro j _ hjk y r _ Ψ h _ _
    rw [Eloc_pinTerms, Eloc_pinTerms]
  rotM := by
    intro j _ _ x X _ _ R hR Ψ h g _ _
    show ((wCoef P.κ cj j X : ℝ) : ℂ) • mCore (R *ᵥ h x) =
      R *ᵥ (((wCoef P.κ cj j X : ℝ) : ℂ) • mCore (h x))
    rw [mCore_rot hR.1, Matrix.mulVec_smul]
  eucM := by
    intro j _ _ x X _ _ r _ Ψ h g _ _
    show ((wCoef P.κ cj j (r '' X) : ℝ) : ℂ) • mCore (h (r.symm (r x))) =
      ((wCoef P.κ cj j X : ℝ) : ℂ) • mCore (h x)
    rw [wCoef_image, Equiv.symm_apply_apply]
  eucMloc := by
    intro j _ hjk x r _ Ψ h g _ _
    rw [Mloc_pinTerms, Mloc_pinTerms]
    show _ • mCore (h (r.symm (r x))) = _
    rw [Equiv.symm_apply_apply]
  localE := by intros; rfl
  localM := by
    intro j x X Ψ Ψ' h h' g g' hloc
    show ((wCoef P.κ cj j X : ℝ) : ℂ) • mCore (h x) = ((wCoef P.κ cj j X : ℝ) : ℂ) • mCore (h' x)
    by_cases hX : X = Set.univ
    · rw [(hloc x (hX ▸ Set.mem_univ x)).2.1]
    · simp [wCoef, hX]
  boundE := by
    intro j _ _ y X _ _ Ψ h _
    show ‖(0 : ℂ)‖ ≤ _
    rw [norm_zero]
    exact mul_nonneg hE₀ (Real.exp_pos _).le
  boundM := by
    intro j hj1 hjk x X hX _ Ψ h g hd _
    rw [pinTerms_gs hjk] at hd
    show vn (((wCoef P.κ cj j X : ℝ) : ℂ) • mCore (h x)) < _
    have he := Real.exp_pos (-P.κ * sizeJ P.m₀ j X)
    have h6 := hc9 j
    by_cases hcj : cj j = 0
    · have hw : wCoef P.κ cj j X = 0 := by
        unfold wCoef; split_ifs <;> simp [hcj]
      rw [hw]
      simp only [Complex.ofReal_zero, zero_smul, vn_zero]
      exact mul_pos h6 he
    · rw [vn_smul_c, Complex.norm_real, Real.norm_of_nonneg (wCoef_nonneg hc0 j X)]
      have h1 := vn_mCore_le (hB j hj1 hjk hcj Ψ h hd x)
      have h2 := wCoef_le hκ hc0 (m₀ := P.m₀) hX
      have h4 : wCoef P.κ cj j X * vn (mCore (h x)) ≤
          cj j * Real.exp (-P.κ * sizeJ P.m₀ j X) * ((2 ^ 2 + 1) * 2) :=
        mul_le_mul h2 h1 (vn_nonneg _) (mul_nonneg (hc0 j) he.le)
      have h5 := hc j
      nlinarith [mul_pos h6 he, mul_le_mul_of_nonneg_right h5 he.le]

/-- **The field-dependent terms form a member of `IsSF2`** on every field domain on which the
field is bounded by `2` at the level generating sets. -/
theorem isSF2_pinTermsB {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ} {cj : ℕ → ℝ}
    {Dom : FieldDom d L N₁ m₁ k N ϱ} (hE₀ : 0 ≤ P.E₀) (hκ : 0 ≤ P.κ) (hc0 : ∀ j, 0 ≤ cj j)
    (hc : ∀ j, 20 * cj j ≤ P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hc9 : ∀ j, 0 < P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hB : ∀ j, 1 ≤ j → ∀ (hjk : j ≤ k), cj j ≠ 0 → ∀ Ψ h, Dom.dom j (levelGS j hjk) Ψ h → ∀ x, vn (h x) ≤ 2)
    (H : BgHyp d L k ϱ (aIdeal L k (a k)) (Rg.sfBgMass k)) :
    IsSF2 P Rg β a Dom (pinTerms d L N₁ m₁ k N ϱ P.κ cj)
      (rho2 P Rg β a (pinTerms d L N₁ m₁ k N ϱ P.κ cj) 0) 0 := by
  refine isSF2_rho2 (pinTerms_clausesB hE₀ hκ hc0 hc hc9 hB)
    (fun j hj1 hjk X _ => by
      rw [pinTerms_gs hjk]; exact GsSpec.levelGS_strong hj1 hjk X) ?_
  intro Ψ₀ h₀ g D hD
  have hDh : ∀ x i, (D.h x i).im = 0 := realizes_h_im hD.1
  have h1 := im_Fcomp_zero H hD.2.1 P.m₀ g
  rw [Fcomp_zero] at h1
  have hF : (Fcomp P.m₀ (pinTerms d L N₁ m₁ k N ϱ P.κ cj) (aIdeal L k (a k)) (Rg.sfBgMass k) D
      (fun x i => (g x i : ℂ))).im = 0 := by
    unfold Fcomp
    rw [Complex.add_im, h1, zero_add, Complex.im_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    unfold Floc
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Mloc_pinTerms]
    have h2 := mCore_im (fun l => composedPair_h_im (a := aIdeal L k (a k)) (ν := Rg.sfBgMass k)
      hDh j x l) i
    simp [Complex.mul_im, h2]
  have hE : Ecomp P.m₀ (pinTerms d L N₁ m₁ k N ϱ P.κ cj) (aIdeal L k (a k)) (Rg.sfBgMass k) D = 0 := by
    simp [Ecomp, Edens, Eloc_pinTerms]
  unfold expo2
  rw [hE]
  simp [Complex.add_im, Complex.mul_im, hF]


/-! ### The witness on the wide domain -/

theorem epsTail_le_zero (j : ℕ) : epsTail j ≤ epsTail 0 := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact (epsTail_succ_le j).trans ih

theorem eps_witness_le (α₀ : ℝ) (hα : 0 ≤ α₀) (j : ℕ) :
    (witnessConsts α₀).eps 3 3 j ≤ α₀ * epsTail 0 := by
  unfold Consts.eps epsSeq
  have hq : (((3 : ℕ) : ℝ) ^ (-((witnessConsts α₀).alpha 3))) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · norm_num
    · simp only [Consts.alpha, witnessConsts]; norm_num
  have hq0 : 0 ≤ (((3 : ℕ) : ℝ) ^ (-((witnessConsts α₀).alpha 3))) := by positivity
  have h1 := pow_le_one₀ hq0 hq (n := j)
  have h2 := epsTail_le_zero j
  have h3 := epsTail_pos j
  have : (witnessConsts α₀).α₀ = α₀ := rfl
  rw [this]
  calc α₀ * epsTail j * ((((3 : ℕ) : ℝ) ^ (-((witnessConsts α₀).alpha 3))) ^ j)
      ≤ α₀ * epsTail j * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ α₀ * epsTail 0 := by rw [mul_one]; exact mul_le_mul_of_nonneg_left h2 hα

/-- The scale of the radius of the wide witness: `α₀ = μ / (2 T)`, `μ = (7/72) 9^{-k}`. -/
noncomputable def wideα₀ (k : ℕ) : ℝ := physMass 3 k (witnessν k k) / (2 * epsTail 0)

theorem physMass_witness_pos (k : ℕ) : 0 < physMass 3 k (witnessν k k) := by
  unfold physMass witnessν; positivity

theorem physMass_witness_le_one (k : ℕ) : physMass 3 k (witnessν k k) ≤ 1 := by
  unfold physMass witnessν
  have h1 : (1 : ℝ) ≤ 9 ^ k := one_le_pow₀ (by norm_num)
  have h2 : (((3 : ℕ) : ℝ) ^ k)⁻¹ ^ 2 ≤ 1 := by
    have : (1 : ℝ) ≤ ((3 : ℕ) : ℝ) ^ k := one_le_pow₀ (by norm_num)
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ this)
  have e : 7 / 72 * (9 : ℝ) ^ k / 9 ^ k = 7 / 72 := by field_simp
  rw [e]
  nlinarith [(by positivity : (0 : ℝ) ≤ (((3 : ℕ) : ℝ) ^ k)⁻¹ ^ 2)]

theorem wideα₀_pos (k : ℕ) : 0 < wideα₀ k := by
  unfold wideα₀; have := epsTail_pos 0; have := physMass_witness_pos k; positivity

theorem wide_eps_le (k j : ℕ) :
    (witnessConsts (wideα₀ k)).eps 3 3 j ≤ physMass 3 k (witnessν k k) / 2 := by
  refine (eps_witness_le _ (wideα₀_pos k).le j).trans ?_
  unfold wideα₀
  have := epsTail_pos 0
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [physMass_witness_pos k]

/-- **A member of `IsSFFamily2` on the wide domain `xiFieldDom` at positive mass with nonzero
`h`-dependent terms `ℳ^{(j)}`** (`d = L = 3`, `N = 2`, any `m₁`, `k`, `k₀`, `ϱ ≥ R₀(3,3)`; the
radius scale `α₀ = μ_k / (2 T)`): `ℳ^{(j)}(x, 𝕋; Ψ, h, g) = c_j e^{-κ|𝕋|²} (h(x)·h(x) - 1) h(x)`
with `c_j = L^{-2j}/20`.  The bound `‖h‖ ≤ 2` on the domain is `vn_le_two_of_xiDom`. -/
theorem isSFFamily2_xi_witness_M (m₁ k k₀ : ℕ) (ϱ : ℝ) (hϱ : bgR0 3 3 ≤ ϱ) :
    IsSFFamily2 (d := 3) (L := 3) (m₁ := m₁) (k := k) (N := 2) (ϱ := ϱ)
      (witnessConsts (wideα₀ k)) ⟨k₀, witnessν k⟩ witnessβ witnessa
      (fun _ _ => xiFieldDom (aIdeal 3 k (witnessa k)) (physMass 3 k (witnessν k k))
        ((witnessConsts (wideα₀ k)).eps 3 3))
      (fun N₁ _ => pinTerms 3 3 N₁ m₁ k 2 ϱ (witnessConsts (wideα₀ k)).κ (witCj 3))
      (fun N₁ _ => rho2 (witnessConsts (wideα₀ k)) ⟨k₀, witnessν k⟩ witnessβ witnessa
        (pinTerms 3 3 N₁ m₁ k 2 ϱ (witnessConsts (wideα₀ k)).κ (witCj 3)) 0) (fun _ => 0) where
  admissible := witnessConsts_admissible (wideα₀_pos k)
  coeff := witness_coeff k
  torus := fun N₁ _ => isSF2_pinTermsB le_rfl (witnessConsts_admissible (wideα₀_pos k)).κ_pos.le
    (fun j => (witCj_pos j).le) (witness_cj_le _) (witness_c9_pos _)
    (fun j hj1 hjk _ Ψ h hd x => by
      refine vn_le_two_of_xiDom (physMass_witness_pos k) (physMass_witness_le_one k)
        (wide_eps_le k j) (fun x => ?_) (hd : XiDom _ _ _ _ _ Ψ h) x
      simp [levelGS, hj1])
    (bgHyp_of_class2 (witnessConsts_admissible (wideα₀_pos k)) (witness_coeff k) le_rfl le_rfl hϱ)
  torusIndep := torusIndep_pinTerms _ _ _
  renorm := fun _ _ _ => renormCond_pinTerms _ _ _ _ _ _

/-- The terms of the wide member are not zero: at the constant field `h = (1 + s) e₀`. -/
theorem wide_witness_M_ne_zero (m₁ k N₁ : ℕ) [NeZero N₁] (ϱ : ℝ) (j : ℕ) {s : ℝ} (hs : 0 < s)
    (x : CTorus 3 3 N₁ m₁ k) (Ψ g : Fld 3 3 N₁ m₁ k 2) :
    (pinTerms 3 3 N₁ m₁ k 2 ϱ (witnessConsts (wideα₀ k)).κ (witCj 3)).M j x Set.univ Ψ
      (constFld (((1 + s : ℝ) : ℂ) • Pi.single 0 1)) g ≠ 0 :=
  pinTerms_M_const_ne_zero (witCj_pos j) 0 hs x Ψ g

end Balaban.SmallField.Def6v2
