/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.V2Energy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-6 v2: the source form and the reference jet at a nonzero energy

`dbE` and `RefJet` for the energy terms of `eTerms`: the term is `c · F(b / ν_j)` on the
whole-torus polymer, `F(v) = (v·v - 1)²`, so its value and `b`-derivative at the reference point
vanish and its second transverse jet is zero; on the anisotropic polydisc the field `b / ν_j` is
bounded by 2.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Finset Matrix

section Jet

variable {N : ℕ}

theorem fderiv_fCore_unit {v : Fin N → ℂ} (hv : ∑ l, v l * v l = 1) :
    fderiv ℂ (fCore (N := N)) v = 0 := by
  have h := Finset.analyticAt_sum (𝕜 := ℂ)
    (f := fun (l : Fin N) (w : Fin N → ℂ) => w l * w l) (c := v) Finset.univ
    (fun l _ => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) l).analyticAt v).mul
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) l).analyticAt v))
  have e0 : (∑ l : Fin N, fun w : Fin N → ℂ => w l * w l) = fun w => ∑ l, w l * w l := by
    funext w; simp [Finset.sum_apply]
  rw [e0] at h
  have hd : DifferentiableAt ℂ (fun w : Fin N → ℂ => ∑ l, w l * w l - 1) v :=
    (h.sub analyticAt_const).differentiableAt
  have e : (fCore (N := N)) = fun w => (∑ l, w l * w l - 1) * (∑ l, w l * w l - 1) := by
    funext w; simp [fCore, sq]
  rw [e]
  have := fderiv_mul hd hd
  simp only [Pi.mul_def] at this
  rw [this, hv, sub_self]
  ext u
  simp

theorem vn_single_one (i₀ : Fin N) : vn (Pi.single i₀ 1 : Fin N → ℂ) = 1 := by
  have h : vn (Pi.single i₀ 1 : Fin N → ℂ) ^ 2 = 1 := by
    rw [vn_sq]
    have : ∀ x : Fin N, ‖(Pi.single i₀ 1 : Fin N → ℂ) x‖ ^ 2 = if x = i₀ then 1 else 0 := by
      intro x; by_cases hx : x = i₀ <;> simp [hx]
    simp [this]
  have h0 := vn_nonneg (Pi.single i₀ 1 : Fin N → ℂ)
  nlinarith

end Jet

section Aniso

variable {d N : ℕ}

/-- On the anisotropic polydisc the field `b / ν` is within `√N r / ν ≤ 1` of `e_{i₀}`, hence of
norm at most `2`. -/
theorem vn_src_le_two {i₀ : Fin N} {ν r : ℝ} {X : Finset (Site d)} (hν : 0 < ν) (hr : 0 < r)
    (hr1 : r ≤ 1) (hrad : (N : ℝ) * (r / ν) ^ 2 ≤ 1) {c : Cfg d N X}
    (hc : c ∈ polyAniso i₀ ν r X) :
    vn ((ν : ℂ)⁻¹ • fun i => c (Sum.inr i)) ≤ 2 := by
  set w : Fin N → ℂ := fun i => (ν : ℂ)⁻¹ * c (Sum.inr i) - (Pi.single i₀ 1 : Fin N → ℂ) i with hw
  have hwi : ∀ i, ‖w i‖ ≤ r / ν := by
    intro i
    have h1 := hc (Sum.inr i)
    have e : w i = (ν : ℂ)⁻¹ * (c (Sum.inr i) - refPt i₀ ν X (Sum.inr i)) := by
      have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
      simp only [hw, refPt, pack, Sum.elim_inr, Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hν.le]
    have h2 : anisoWt i₀ r X (Sum.inr i) ≤ r := by
      simp only [anisoWt, Sum.elim_inr]
      split_ifs
      · nlinarith
      · exact le_rfl
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_right ((le_of_lt h1).trans h2) hν.le
  have hvw : vn w ≤ 1 := by
    have h1 : vn w ^ 2 ≤ 1 := by
      rw [vn_sq]
      calc ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin N, (r / ν) ^ 2 :=
            Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hwi i) 2
        _ = (N : ℝ) * (r / ν) ^ 2 := by simp
        _ ≤ 1 := hrad
    nlinarith [vn_nonneg w]
  have e : ((ν : ℂ)⁻¹ • fun i => c (Sum.inr i)) = (Pi.single i₀ 1 : Fin N → ℂ) + w := by
    funext i; simp [hw]
  rw [e]
  linarith [vn_add (Pi.single i₀ 1 : Fin N → ℂ) w, vn_single_one i₀]

/-- **The reference-jet certificate of the energy term** `c₀ · F(b / ν)`. -/
theorem refJet_fCore {i₀ : Fin N} {ν r c₀ M : ℝ} {X : Finset (Site d)} (hν : 0 < ν) (hr : 0 < r)
    (hr1 : r ≤ 1) (hrad : (N : ℝ) * (r / ν) ^ 2 ≤ 1) (hc₀ : 0 ≤ c₀) (hM : c₀ * 25 ≤ M) :
    RefJet i₀ ν r M X
      (fun c : Cfg d N X => (c₀ : ℂ) * fCore ((ν : ℂ)⁻¹ • fun i => c (Sum.inr i))) := by
  refine RefJet.of_polyAniso hr ?_ ?_
  · intro c _
    set T : Cfg d N X →L[ℂ] (Fin N → ℂ) :=
      (ν : ℂ)⁻¹ • ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Idx d N X => ℂ) (Sum.inr i) with hT
    exact analyticAt_const.mul ((fCore_analyticAt (T c)).comp (T.analyticAt c))
  · intro c hc
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc₀]
    have h1 := norm_fCore_le (B := 2) (vn_src_le_two hν hr hr1 hrad hc)
    have h2 : ‖fCore ((ν : ℂ)⁻¹ • fun i => c (Sum.inr i))‖ ≤ 25 := by nlinarith
    calc c₀ * _ ≤ c₀ * 25 := mul_le_mul_of_nonneg_left h2 hc₀
      _ ≤ M := hM

end Aniso

/-! ### The source form of the energy terms -/

section Source

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem sourceOf_E_eTerms (P : Consts) (cj : ℕ → ℝ) (ν : ℕ → ℝ) (j : ℕ)
    (y : CTorus d L N₁ m₁ k) (X : Set (CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N)
    (b : Fin N → ℂ) :
    (sourceOf ν (eTerms d L N₁ m₁ k N ϱ P cj)).E j y X Ψ (constFld b) =
      open Classical in
      if N₁ = 1 ∧ j = k ∧ X = Set.univ then
        ((cEn d L N₁ m₁ k P : ℝ) : ℂ) * fCore ((nuIdeal L k (ν k) j : ℂ)⁻¹ • b)
      else 0 := by
  classical
  show (eTerms d L N₁ m₁ k N ϱ P cj).E j y X Ψ ((nuIdeal L k (ν k) j : ℂ)⁻¹ • constFld b) = _
  rw [E_eTerms]
  split_ifs
  · congr 1
    exact eAvg_const ((nuIdeal L k (ν k) j : ℂ)⁻¹ • b)
  · rfl

/-- **`SourceForm` at a nonzero energy**: the source form of `eTerms` (`C_D = 0`), with the
reference-jet certificate of the energy term, for positive masses, on every field domain on
which `h` is bounded by `2` at the level generating sets. -/
theorem sourceForm_eTerms {P : Consts} {cj : ℕ → ℝ} {ν : ℕ → ℝ}
    {Dom : FieldDom d L N₁ m₁ k N ϱ} (hα : 0 < P.α₀) (hE₀ : 0 ≤ P.E₀) (hκ : 0 ≤ P.κ)
    (hc0 : ∀ j, 0 ≤ cj j)
    (hc : ∀ j, 20 * cj j ≤ P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hc9 : ∀ j, 0 < P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hB : ∀ j, 1 ≤ j → ∀ (hjk : j ≤ k) Ψ h, Dom.dom j (levelGS j hjk) Ψ h → ∀ x, vn (h x) ≤ 2)
    (hν : 0 < ν k) (i₀ : Fin N)
    (hr1 : anisoRadius d L N P k ≤ 1)
    (hrad : (N : ℝ) * (anisoRadius d L N P k / nuIdeal L k (ν k) k) ^ 2 ≤ 1) :
    SourceForm P ν Dom (eTerms d L N₁ m₁ k N ϱ P cj)
      (sourceOf ν (eTerms d L N₁ m₁ k N ϱ P cj)) i₀ 0 := by
  classical
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hnu : ∀ j, 0 < nuIdeal L k (ν k) j := fun j => by unfold nuIdeal; positivity
  have hrpos : ∀ j, 0 < anisoRadius d L N P j := fun j => by
    have hε := eps_pos (d := d) (L := L) hα j
    have hK := bgK1_pos d L N
    have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos i₀
    unfold anisoRadius rotB
    positivity
  refine sourceForm_of_pos (eTerms_clauses hE₀ hκ hc0 hc hc9 hB) (fun j _ _ => hnu j) ?_ ?_
  · intro j hj1 hjk y X hX hy u
    have hfd : fderiv ℂ (fun b : Fin N → ℂ =>
        (sourceOf ν (eTerms d L N₁ m₁ k N ϱ P cj)).E j y X (constFld (Pi.single i₀ 1))
          (constFld b)) ((nuIdeal L k (ν k) j : ℂ) • Pi.single i₀ 1) = 0 := by
      simp only [sourceOf_E_eTerms]
      by_cases hcd : N₁ = 1 ∧ j = k ∧ X = Set.univ
      · have hfe : (fun b : Fin N → ℂ => if N₁ = 1 ∧ j = k ∧ X = Set.univ then
            ((cEn d L N₁ m₁ k P : ℝ) : ℂ) * fCore ((nuIdeal L k (ν k) j : ℂ)⁻¹ • b) else 0) =
            fun b => ((cEn d L N₁ m₁ k P : ℝ) : ℂ) * fCore ((nuIdeal L k (ν k) j : ℂ)⁻¹ • b) :=
          funext fun b => ite_eq_left_iff.2 (fun h => absurd hcd h)
        rw [hfe]
        have hν' : (nuIdeal L k (ν k) j : ℂ) ≠ 0 := by exact_mod_cast (hnu j).ne'
        set b0 : Fin N → ℂ := (nuIdeal L k (ν k) j : ℂ) • Pi.single i₀ 1 with hb0
        have e1 : (nuIdeal L k (ν k) j : ℂ)⁻¹ • b0 = Pi.single i₀ 1 := by
          rw [hb0, smul_smul, inv_mul_cancel₀ hν', one_smul]
        have hunit : ∑ l, (Pi.single i₀ 1 : Fin N → ℂ) l * (Pi.single i₀ 1 : Fin N → ℂ) l = 1 := by
          simp [Pi.single_apply]
        have hF : HasFDerivAt (fCore (N := N)) (0 : (Fin N → ℂ) →L[ℂ] ℂ)
            (Pi.single i₀ 1 : Fin N → ℂ) := by
          have := ((fCore_analyticAt (Pi.single i₀ 1 : Fin N → ℂ)).differentiableAt).hasFDerivAt
          rwa [fderiv_fCore_unit hunit] at this
        have hT : HasFDerivAt (fun b : Fin N → ℂ => (nuIdeal L k (ν k) j : ℂ)⁻¹ • b)
            ((nuIdeal L k (ν k) j : ℂ)⁻¹ • ContinuousLinearMap.id ℂ (Fin N → ℂ)) b0 :=
          ((nuIdeal L k (ν k) j : ℂ)⁻¹ • ContinuousLinearMap.id ℂ (Fin N → ℂ)).hasFDerivAt
        have hF' : HasFDerivAt (fun b : Fin N → ℂ => fCore ((nuIdeal L k (ν k) j : ℂ)⁻¹ • b))
            ((0 : (Fin N → ℂ) →L[ℂ] ℂ).comp
              ((nuIdeal L k (ν k) j : ℂ)⁻¹ • ContinuousLinearMap.id ℂ (Fin N → ℂ))) b0 := by
          refine HasFDerivAt.comp b0 (g := fCore (N := N))
            (f := fun b : Fin N → ℂ => (nuIdeal L k (ν k) j : ℂ)⁻¹ • b) ?_ hT
          simpa only [e1] using hF
        have := (hF'.const_mul (((cEn d L N₁ m₁ k P : ℝ) : ℂ))).fderiv
        rw [this]
        ext w; simp
      · have hfe : (fun b : Fin N → ℂ => if N₁ = 1 ∧ j = k ∧ X = Set.univ then
            ((cEn d L N₁ m₁ k P : ℝ) : ℂ) * fCore ((nuIdeal L k (ν k) j : ℂ)⁻¹ • b) else 0) =
            fun _ => 0 := funext fun b => ite_eq_right_iff.2 (fun h => absurd h hcd)
        rw [hfe]
        exact fderiv_const_apply _
    rw [hfd]
    simp
  · intro j hj1 hjk X' hX'
    have hr := hrpos j
    by_cases hcd : N₁ = 1 ∧ j = k ∧ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' = Set.univ
    · obtain ⟨hN1, rfl, hU⟩ := hcd
      have hfun : srcPack (sourceOf ν (eTerms d L N₁ m₁ j N ϱ P cj)) j i₀ X' =
          fun c : Cfg d N X' => ((cEn d L N₁ m₁ j P : ℝ) : ℂ) *
            fCore ((nuIdeal L j (ν j) j : ℂ)⁻¹ • fun i => c (Sum.inr i)) := by
        funext c
        have := sourceOf_E_eTerms (ϱ := ϱ) P cj ν j 0 (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := j) j X')
          (fieldOf j i₀ X' c) (fun i => c (Sum.inr i))
        exact this.trans (ite_eq_left_iff.2 (fun h => absurd ⟨hN1, rfl, hU⟩ h))
      rw [hfun]
      refine refJet_fCore (hnu j) hr hr1 hrad (cEn_nonneg hE₀) ?_
      rw [hU]
      unfold cEn
      exact le_of_eq (by ring)
    · have hfun : srcPack (sourceOf ν (eTerms d L N₁ m₁ k N ϱ P cj)) j i₀ X' =
          fun _ : Cfg d N X' => (0 : ℂ) := by
        funext c
        have := sourceOf_E_eTerms (ϱ := ϱ) P cj ν j 0 (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')
          (fieldOf j i₀ X' c) (fun i => c (Sum.inr i))
        exact this.trans (ite_eq_right_iff.2 (fun h => absurd h hcd))
      rw [hfun]
      refine (refJet_const i₀ _ hr X' 0).mono hr ?_
      rw [norm_zero]
      exact mul_nonneg hE₀ (Real.exp_pos _).le

end Source

/-! ### The witness -/

section Witness

theorem anisoRadius_le_eps {d L N : ℕ} [NeZero L] (P : Consts) (j : ℕ) (hN : 1 ≤ N)
    (hε : 0 ≤ P.eps d L j) : anisoRadius d L N P j ≤ P.eps d L j / 8 := by
  unfold anisoRadius
  have hK := bgK1_pos d L N
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 8 ≤ (2 * bgK1 d L N + 2) * (4 * N * (1 + N * rotB N)) := by
    have : 0 ≤ rotB N := by unfold rotB; positivity
    have h3 : 0 ≤ (N : ℝ) * rotB N := by positivity
    have h2 : 4 ≤ 4 * (N : ℝ) * (1 + N * rotB N) := by nlinarith
    nlinarith
  exact div_le_div_of_nonneg_left hε (by norm_num) h1

/-- **`SourceForm` is inhabited at a nonzero energy** (`d = L = 3`, `N = 2`, any `m₁`, `k`, torus
`N₁`): the source form of the wide-domain member `isSFFamily2_xi_witness_E`, with `C_D = 0`,
whose energy term is not zero (`E_eTerms_const_ne_zero`). -/
theorem sourceForm_eTerms_witness (m₁ k N₁ : ℕ) [NeZero N₁] (ϱ : ℝ) :
    SourceForm (d := 3) (L := 3) (N₁ := N₁) (m₁ := m₁) (k := k) (N := 2) (ϱ := ϱ)
      (eConsts (wideα₀ k)) (witnessν k)
      (xiFieldDom (aIdeal 3 k (witnessa k)) (physMass 3 k (witnessν k k))
        ((eConsts (wideα₀ k)).eps 3 3))
      (eTerms 3 3 N₁ m₁ k 2 ϱ (eConsts (wideα₀ k)) (witCj 3))
      (sourceOf (witnessν k) (eTerms 3 3 N₁ m₁ k 2 ϱ (eConsts (wideα₀ k)) (witCj 3))) 0 0 := by
  have hnuk : nuIdeal 3 k (witnessν k k) k = 7 / 72 := by
    simp only [nuIdeal, Nat.sub_self, pow_zero, inv_one, one_pow, mul_one, witnessν]
    field_simp
  have hepsk : (eConsts (wideα₀ k)).eps 3 3 k ≤ 7 / 144 := by
    have h1 := wide_eps_le k k
    have h2 := physMass_witness_le_one k
    have h3 : physMass 3 k (witnessν k k) ≤ 7 / 72 := by
      unfold physMass witnessν
      have e : 7 / 72 * (9 : ℝ) ^ k / 9 ^ k = 7 / 72 := by field_simp
      rw [e]
      have : (((3 : ℕ) : ℝ) ^ k)⁻¹ ^ 2 ≤ 1 := by
        have : (1 : ℝ) ≤ ((3 : ℕ) : ℝ) ^ k := one_le_pow₀ (by norm_num)
        exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ this)
      nlinarith [(by positivity : (0 : ℝ) ≤ (((3 : ℕ) : ℝ) ^ k)⁻¹ ^ 2)]
    show (witnessConsts (wideα₀ k)).eps 3 3 k ≤ 7 / 144
    linarith
  have hr : anisoRadius 3 3 2 (eConsts (wideα₀ k)) k ≤ 7 / 1152 := by
    have := anisoRadius_le_eps (d := 3) (L := 3) (eConsts (wideα₀ k)) k (N := 2) (by norm_num)
      (eps_pos (d := 3) (L := 3) (P := witnessConsts (wideα₀ k)) (wideα₀_pos k) k).le
    linarith
  have hr0 : 0 ≤ anisoRadius 3 3 2 (eConsts (wideα₀ k)) k := by
    unfold anisoRadius
    have := bgK1_pos 3 3 2
    have := eps_pos (d := 3) (L := 3) (P := witnessConsts (wideα₀ k)) (wideα₀_pos k) k
    have h5 : (0 : ℝ) ≤ (eConsts (wideα₀ k)).eps 3 3 k := this.le
    unfold rotB
    positivity
  refine sourceForm_eTerms (eConsts_admissible (wideα₀_pos k)).α₀_pos zero_le_one
    (eConsts_admissible (wideα₀_pos k)).κ_pos.le (fun j => (witCj_pos j).le)
    (witness_cj_le (wideα₀ k)) (witness_c9_pos (wideα₀ k))
    (fun j hj1 hjk Ψ h hd x => by
      refine vn_le_two_of_xiDom (physMass_witness_pos k) (physMass_witness_le_one k)
        (wide_eps_le k j) (fun x => ?_) (hd : XiDom _ _ _ _ _ Ψ h) x
      simp [levelGS, hj1])
    (eConsts_coeff k (α₀ := wideα₀ k)).nu_pos (0 : Fin 2) (by linarith) ?_
  rw [hnuk]
  have h7 : anisoRadius 3 3 2 (eConsts (wideα₀ k)) k / (7 / 72) ≤ 1 / 16 := by
    rw [div_le_iff₀ (by norm_num)]; linarith
  have h8 : 0 ≤ anisoRadius 3 3 2 (eConsts (wideα₀ k)) k / (7 / 72) := div_nonneg hr0 (by norm_num)
  nlinarith

end Witness

end Balaban.SmallField.Def6v2
