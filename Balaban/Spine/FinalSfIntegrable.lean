/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfDomain
public import Balaban.Spine.FinalNumerics
public import Balaban.Spine.InheritedBound
public import Balaban.Fluctuation.ClassOldBirthConsts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The small-field factor of the whole torus is integrable for the members of `ℛ♭_k`

A6-3 (a), item 1 (A4-1i for the cut `Y = univ`): at the stopping scale (`ν_k L² > 7/8`) of a
member of `ℛ♭_k`, on every torus of the family and for every source of the unit `ℓ¹` ball, the
small-field factor `sfFactor2 C vc univ` is integrable in the block field `ψ_k`
(`measInt_sfFactor2_of_flatRep`), for `β` large. The proof is the transport of the domains of
the inherited terms on the support of `χ_k(univ)` (`Spine/FinalDomPsiJ.lean`) together with the
smallness of the tolerance `δ_k` against the radii `ε_j` (`Spine/FinalNumerics.lean`). The
separation of the cube generating sets, `R₀(d, L) ≤ 5 L M₁` (`minSep`), is a typing premise.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField
  Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Localization

namespace Balaban.RootFSpine

section Stop

/-- **The stopping scale lies above the regime index**: if `ν_k L² > 7/8`, `ν_k = ν L^{2k} δ_k`,
`|log δ_k| ≤ 1/20`, `k ≥ 1`, `d ≥ 3` and `β ≥ 2 L`, then `k₀ = kZero d L β ν < k`. -/
theorem kZero_lt_of_stop {d L k : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ L) {β ν δk : ℝ}
    (hβ : 2 * (L : ℝ) ≤ β) (hν : 0 < ν) (hk : 1 ≤ k) (hδ0 : 0 < δk)
    (hδ : |Real.log δk| ≤ 1 / 20) (hstop : 7 / 8 < ν * (L : ℝ) ^ (2 * k) * δk * (L : ℝ) ^ 2) :
    kZero d L β ν < k := by
  by_contra hge
  push Not at hge
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hβ0 : 0 < β := by linarith
  have hk0 : kZero d L β ν ≠ 0 := by omega
  have hg : KZeroGenuine β ν := by
    by_contra hng
    exact hk0 (kZero_of_not_genuine hL hng)
  have hspec := kZero_spec (d := d) (L := L) (β := β) (ν := ν) (by omega) hL (mul_pos hβ0 hν) hg
  have hmono : (L : ℝ) ^ (k * d) ≤ (L : ℝ) ^ (kZero d L β ν * d) :=
    pow_le_pow_right₀ hL1 (Nat.mul_le_mul_right d hge)
  have hbn : 0 ≤ β * ν := by positivity
  have h1 : β * ν * (L : ℝ) ^ (k * d) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hmono hbn).trans hspec
  -- δ_k ≤ 20/19
  have hexp : δk ≤ 20 / 19 := by
    have h2 : Real.log δk ≤ 1 / 20 := (abs_le.1 hδ).2
    have h3 : Real.exp (1 / 20) < 1 / (1 - 1 / 20) :=
      Real.exp_bound_div_one_sub_of_interval' (x := 1 / 20) (by norm_num) (by norm_num)
    calc δk = Real.exp (Real.log δk) := (Real.exp_log hδ0).symm
      _ ≤ Real.exp (1 / 20) := Real.exp_le_exp.2 h2
      _ ≤ 20 / 19 := by norm_num at h3 ⊢; linarith
  have hX : 4 / 5 < ν * (L : ℝ) ^ (2 * k) * (L : ℝ) ^ 2 := by
    have hXp : 0 ≤ ν * (L : ℝ) ^ (2 * k) * (L : ℝ) ^ 2 := by positivity
    nlinarith
  have he : (L : ℝ) ^ (k * d) = (L : ℝ) ^ (2 * k) * (L : ℝ) ^ (k * (d - 2)) := by
    rw [← pow_add]; congr 1
    have : k * d = 2 * k + k * (d - 2) := by
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    exact this
  have hpow : (L : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := by
    refine le_self_pow₀ hL1 ?_
    have : 1 ≤ d - 2 := by omega
    nlinarith
  have hXnn : 0 ≤ ν * (L : ℝ) ^ (2 * k) := by positivity
  have hLL : (L : ℝ) ^ 2 = L * L := by ring
  have h4 : 4 / 5 < ν * (L : ℝ) ^ (2 * k) * L * L := by nlinarith
  have h6 : 1 < β * ν * (L : ℝ) ^ (k * d) := by
    rw [he]
    have hh : β * ν * ((L : ℝ) ^ (2 * k) * (L : ℝ) ^ (k * (d - 2))) =
        β * (ν * (L : ℝ) ^ (2 * k)) * (L : ℝ) ^ (k * (d - 2)) := by ring
    rw [hh]
    have hh2 : β * (ν * (L : ℝ) ^ (2 * k)) * L ≤
        β * (ν * (L : ℝ) ^ (2 * k)) * (L : ℝ) ^ (k * (d - 2)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have hh3 : 1 < β * (ν * (L : ℝ) ^ (2 * k)) * L := by
      have hb2 : 2 * (L : ℝ) * (ν * (L : ℝ) ^ (2 * k)) * L ≤ β * (ν * (L : ℝ) ^ (2 * k)) * L := by
        have := mul_le_mul_of_nonneg_right hβ hXnn
        nlinarith [mul_nonneg hXnn hL0.le]
      nlinarith
    linarith
  linarith

end Stop

section Arith

/-- Two numbers with logarithm of modulus at most `1/20`: `a ≤ 4 b`. -/
theorem le_four_mul_of_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ha' : |Real.log a| ≤ 1 / 20)
    (hb' : |Real.log b| ≤ 1 / 20) : a ≤ 4 * b := by
  have h1 : a ≤ 20 / 19 := by
    have h3 : Real.exp (1 / 20) < 1 / (1 - 1 / 20) :=
      Real.exp_bound_div_one_sub_of_interval' (x := 1 / 20) (by norm_num) (by norm_num)
    calc a = Real.exp (Real.log a) := (Real.exp_log ha).symm
      _ ≤ Real.exp (1 / 20) := Real.exp_le_exp.2 (abs_le.1 ha').2
      _ ≤ 20 / 19 := by norm_num at h3 ⊢; linarith
  have h2 : 19 / 20 ≤ b := by
    have := Real.add_one_le_exp (-(1 / 20 : ℝ))
    calc (19 / 20 : ℝ) ≤ Real.exp (-(1 / 20)) := by linarith
      _ ≤ Real.exp (Real.log b) := Real.exp_le_exp.2 (abs_le.1 hb').1
      _ = b := Real.exp_log hb
  linarith

/-- `α₀ (L^{-α})^k ≤ ε_k`. -/
theorem le_epsSeq (L : ℕ) (α α₀ : ℝ) (hα₀ : 0 ≤ α₀) (hL : (0 : ℝ) < L) (k : ℕ) :
    α₀ * ((L : ℝ) ^ (-α)) ^ k ≤ epsSeq L α α₀ k := by
  unfold epsSeq
  have h1 : 1 ≤ epsTail k := by
    unfold epsTail
    have : 0 ≤ ∑' m : ℕ, if k ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0 :=
      tsum_nonneg fun m => by split_ifs <;> positivity
    linarith
  have h2 : 0 ≤ ((L : ℝ) ^ (-α)) ^ k := by positivity
  nlinarith [mul_nonneg hα₀ h2]

/-- `ν L^{2j} δ_j ≤ 4 (ν L^{2k} δ_k L^{-2k} L^{2j})` when `δ_j ≤ 4 δ_k`. -/
theorem ratio_aux {L : ℝ} (hL : 0 < L) {ν δj δk : ℝ} (hν : 0 ≤ ν) (jj k : ℕ)
    (hδ : δj ≤ 4 * δk) :
    ν * L ^ (2 * jj) * δj ≤ 4 * (ν * L ^ (2 * k) * δk * (L ^ k)⁻¹ ^ 2 * (L ^ jj) ^ 2) := by
  have h1 : L ^ (2 * k) * (L ^ k)⁻¹ ^ 2 = 1 := by
    rw [show 2 * k = k * 2 by ring, pow_mul, inv_pow]
    field_simp
  have h2 : (L ^ jj) ^ 2 = L ^ (2 * jj) := by rw [show 2 * jj = jj * 2 by ring, pow_mul]
  have e : ν * L ^ (2 * k) * δk * (L ^ k)⁻¹ ^ 2 * (L ^ jj) ^ 2 = ν * L ^ (2 * jj) * δk := by
    rw [h2]
    calc ν * L ^ (2 * k) * δk * (L ^ k)⁻¹ ^ 2 * L ^ (2 * jj)
        = ν * δk * L ^ (2 * jj) * (L ^ (2 * k) * (L ^ k)⁻¹ ^ 2) := by ring
      _ = ν * L ^ (2 * jj) * δk := by rw [h1]; ring
  rw [e]
  have : 0 ≤ ν * L ^ (2 * jj) := by positivity
  nlinarith

/-- `x * (L^k)⁻² * (L^k)² = x`. -/
theorem physMass_mul_sq' {L : ℕ} (hL : (0 : ℝ) < L) (x : ℝ) (m : ℕ) :
    physMass L m x * ((L : ℝ) ^ m) ^ 2 = x := by
  unfold physMass
  have : ((L : ℝ) ^ m) ≠ 0 := by positivity
  field_simp

/-- `bgMass · L^{2k} ≤ ν_k`. -/
theorem bgMass_mul_sq_le {L : ℕ} (hL : (0 : ℝ) < L) {βk νk : ℝ} (hν : 0 < νk) (k : ℕ) :
    Def6.bgMass L k βk νk * ((L : ℝ) ^ k) ^ 2 ≤ νk := by
  unfold Def6.bgMass
  split_ifs
  · simpa using hν.le
  · have : ((L : ℝ) ^ k) ≠ 0 := by positivity
    have e : νk * ((L : ℝ) ^ k)⁻¹ ^ 2 * ((L : ℝ) ^ k) ^ 2 = νk := by field_simp
    rw [show νk * ((L : ℝ) ^ k)⁻¹ ^ 2 = νk * ((L : ℝ) ^ k)⁻¹ ^ 2 from rfl, e]

end Arith

section Inputs

variable (d N : ℕ) (δ : ℝ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **The small-field factor of the whole torus is integrable at the stopping scale** (A6-3 (a),
item 1). -/
theorem measInt_sfFactor2_of_flatRep (hPre : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ) :
    ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
    ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
    ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
    ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
    ∀ k : ℕ, 1 ≤ k → k ≤ kf →
    ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ) hM6 hkK R geo cs P F St vc,
      FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk →
      7 / 8 < νk * ((T κ c₉).L : ℝ) ^ 2 →
      ∀ (nK : ℕ) [NeZero nK]
        (g : GIdx 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
          (kf + 1) N → ℂ), g ∈ LargeField.l1Ball _ →
        BgHyp d (T κ c₉).L k (minSep (T κ c₉).L (geo nK).M1) (F.ctx hM6 hkK nK).weights
          (cs.muBg k) ∧
        Measurable (fun ψ => sfFactor2 (F.ctx hM6 hkK nK) vc Set.univ ψ h g) ∧
        Integrable fun ψ => sfFactor2 (F.ctx hM6 hkK nK) vc Set.univ ψ h g := by
  intro κ hκ c₉ hc₉
  obtain ⟨hL3, haKer1, haKer2, -, -, -, -, hMpow, hadm, hc9pos, -, -, hδγ, hκf, hc9f, hTy, hϱ, -, -, hsepM, -⟩ :=
    hPre κ hκ c₉ hc₉
  have hd : 3 ≤ d := hTy.1.three_le_d
  have hLr : (2 : ℝ) ≤ (T κ c₉).L := by exact_mod_cast (by omega : 2 ≤ (T κ c₉).L)
  have hNZ : NeZero (T κ c₉).L := ⟨by omega⟩
  obtain ⟨β₁, hβ₁2, hβ₁⟩ := exists_beta_delta_le (d := d) (L := (T κ c₉).L) hd (by omega)
    (γP := (P6 κ c₉).γ) hadm.γ_pos (by linarith [hadm.γ_lt]) (a := (cs₀ κ c₉).aKer) haKer1
    (C7 κ c₉).A0 (T κ c₉).p0 (gammaConst d (T κ c₉).L N) (deltaCap d (T κ c₉).L N)
    (P6 κ c₉).α₀ (gammaConst_pos d (T κ c₉).L N).le (deltaCap_pos d (T κ c₉).L N (by omega))
    (by have := hadm.α₀_pos; exact this)
  refine ⟨max β₁ (2 * (T κ c₉).L), fun β hβ ν hν hνL h hh kf hkf _ _ k hk1 hkkf ρ νk hM6 hkK R geo
    cs P F St vc hF hstop nK _ g hg => ?_⟩
  obtain ⟨hgeo, hakr, -, -, -, -, -, -, hrep, -, -, hνkF, hrun, -, hν9⟩ := hF
  have hsf : SFFlat2 (P6 κ c₉) (kZero d (T κ c₉).L β ν) F.sf := hrep.sfData
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨-, -, -, hν0', -, -, -, -, hbeta, hnu⟩ := hrun
  obtain ⟨δk, hδk0, hδk, hνk'⟩ := hnu (j + 1) le_rfl
  obtain ⟨gk, hgk0, hgk, hbk⟩ := hbeta (j + 1) le_rfl
  have hLpos : (0 : ℝ) < (T κ c₉).L := by linarith
  have hνs : 0 < F.sf.ν (j + 1) := hsf.coeff.nu_pos
  have hβ2 : 2 * ((T κ c₉).L : ℝ) ≤ β := (le_max_right _ _).trans hβ
  have hβ1 : β₁ ≤ β := (le_max_left _ _).trans hβ
  have hstop' : 7 / 8 < ν * ((T κ c₉).L : ℝ) ^ (2 * (j + 1)) * δk * ((T κ c₉).L : ℝ) ^ 2 := by
    have := hstop
    rw [← hνkF, hνk'] at this
    exact this
  have hk0 : kZero d (T κ c₉).L β ν < j + 1 :=
    kZero_lt_of_stop hd (by omega) hβ2 hν0' (by omega) hδk0 hδk hstop'
  have hfield := hrep.field
  have hcoh := hrep.coh
  have hdiv : ∀ x : ℝ, ∀ m : ℕ, x / ((T κ c₉).L : ℝ) ^ (2 * m) =
      physMass (T κ c₉).L m x := fun x m => by
    unfold physMass
    rw [div_eq_mul_inv, show 2 * m = m * 2 by ring, pow_mul, inv_pow]
  have hμ : cs.mu (j + 1) = sfBgMassAt (T κ c₉).L (j + 1) (F.sf.ν (j + 1)) := by
    rw [hfield.mu_eq (j + 1) le_rfl]
    unfold Balaban.LargeField.bgMass
    simp only [not_le.2 hk0, ↓reduceIte]
    exact hdiv _ _
  have hμBg : cs.muBg (j + 1) = sfBgMassAt (T κ c₉).L (j + 1) (F.sf.ν (j + 1)) := by
    rw [hfield.muBg_eq (j + 1) le_rfl]
    exact hdiv _ _
  have hact : 0 ≤ cs.muAct (j + 1) := by
    rw [hfield.muAct_eq (j + 1) le_rfl]; positivity
  have hread : ReadTorus (T κ c₉).L (P6 κ c₉).m₀ (sfIdx (T κ c₉).L (P6 κ c₉).m₀
      (sides (T κ c₉).L (kf + 1) nK) (j + 1)) := dvd_mul_right _ _
  obtain ⟨ρsf, hρ⟩ := hsf.torus
  have hTm := (hρ _ hread).terms
  have hRt := hsf.rTerms (sfIdx (T κ c₉).L (P6 κ c₉).m₀ (sides (T κ c₉).L (kf + 1) nK) (j + 1))
  have hνs9 : F.sf.ν (j + 1) ≤ 1 := by rw [hνkF]; linarith [hν9]
  have hcapBg : cs.muBg (j + 1) * ((T κ c₉).L ^ (j + 1) : ℝ) ^ 2 ≤ 1 := by
    rw [hμBg]
    unfold sfBgMassAt physMass
    have : ((T κ c₉).L : ℝ) ^ (j + 1) ≠ 0 := by positivity
    calc F.sf.ν (j + 1) * (((T κ c₉).L : ℝ) ^ (j + 1))⁻¹ ^ 2 * (((T κ c₉).L : ℝ) ^ (j + 1)) ^ 2
        = F.sf.ν (j + 1) := by field_simp
      _ ≤ 1 := hνs9
  have HB : BgHyp d (T κ c₉).L (j + 1) (minSep (T κ c₉).L (geo nK).M1)
      (F.ctx hM6 hkK nK).weights (cs.muBg (j + 1)) := by
    have hM1 : (geo nK).M1 = M1 κ c₉ := (hgeo nK).1
    rw [hM1]
    refine bgHyp_of_ideal (L := (T κ c₉).L) hd hL3 hsepM hsf.coeff.a_ge hsf.coeff.a_lt
      ?_ hcapBg
    rw [hμBg]; unfold sfBgMassAt physMass; positivity
  have hνpos : ∀ jj, jj ≤ j + 1 → 0 < F.sf.ν jj := by
    intro jj hjj
    obtain ⟨δj, hδj0, -, hνj⟩ := hnu jj hjj
    rw [hνj]; positivity
  have hBgJ : ∀ jj, 1 ≤ jj → jj ≤ j + 1 → BgHyp d (T κ c₉).L (j + 1) (ϱ κ c₉)
      (aIdeal (T κ c₉).L (j + 1) (F.sf.a (j + 1))) (physMass (T κ c₉).L jj (F.sf.ν jj)) :=
    fun jj _ hj => bgHyp_birth hsf hd hL3 hϱ (hνpos jj hj).le
      (birth_cap_of_run hL3 hν0' hnu hkf hkkf (by rw [hνkF]; exact hν9) jj hj)
  have hratioJ : ∀ jj, 1 ≤ jj → jj ≤ j + 1 →
      physMass (T κ c₉).L jj (F.sf.ν jj) * (((T κ c₉).L : ℝ) ^ jj) ^ 2 ≤
        4 * (sfBgMassAt (T κ c₉).L (j + 1) (F.sf.ν (j + 1)) * (((T κ c₉).L : ℝ) ^ jj) ^ 2) := by
    intro jj _ hj
    rw [physMass_mul_sq' hLpos]
    obtain ⟨δj, hδj0, hδj, hνj⟩ := hnu jj hj
    rw [hνj]
    unfold sfBgMassAt physMass
    rw [hνk']
    exact ratio_aux hLpos hν0'.le jj (j + 1) (le_four_mul_of_log hδj0 hδk0 hδj hδk)
  have hBgR : BgHyp d (T κ c₉).L (j + 1) (ϱ κ c₉) (aIdeal (T κ c₉).L (j + 1) (F.sf.a (j + 1)))
      (Def6.bgMass (T κ c₉).L (j + 1) (F.sf.β (j + 1)) (F.sf.ν (j + 1))) :=
    bgHyp_of_ideal hd hL3 hϱ hsf.coeff.a_ge hsf.coeff.a_lt (Def6.bgMass_nonneg hνs _ _)
      ((bgMass_mul_sq_le hLpos hνs _).trans hνs9)
  have hratioR : Def6.bgMass (T κ c₉).L (j + 1) (F.sf.β (j + 1)) (F.sf.ν (j + 1)) *
        (((T κ c₉).L : ℝ) ^ (j + 1)) ^ 2 ≤
      4 * (sfBgMassAt (T κ c₉).L (j + 1) (F.sf.ν (j + 1)) * (((T κ c₉).L : ℝ) ^ (j + 1)) ^ 2) := by
    unfold sfBgMassAt
    rw [physMass_mul_sq' hLpos]
    have := bgMass_mul_sq_le hLpos hνs (βk := F.sf.β (j + 1)) (j + 1)
    linarith
  have hdelta : cs.delta (j + 1) = (F.sf.β (j + 1) * (cs₀ κ c₉).aKer) ^ (-(1 / 2 : ℝ)) *
      ((C7 κ c₉).A0 * Real.log (F.sf.β (j + 1) * (cs₀ κ c₉).aKer) ^ (T κ c₉).p0) := by
    rw [hcoh.delta_cs (j + 1) le_rfl, hakr]
    rfl
  have hmain := hβ₁ β hβ1 (F.sf.β (j + 1)) (j + 1) ⟨gk, hgk0, hgk, hbk⟩
  have hΓpos := gammaConst_pos d (T κ c₉).L N
  have hnum0 : gammaConst d (T κ c₉).L N * cs.delta (j + 1) ≤
      min (deltaCap d (T κ c₉).L N)
        ((P6 κ c₉).α₀ * (((T κ c₉).L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - (P6 κ c₉).γ))) ^ (j + 1)) := by
    refine le_trans ?_ hmain
    rw [hdelta]
    exact mul_le_mul_of_nonneg_left (le_abs_self _) hΓpos.le
  have hnum : gammaConst d (T κ c₉).L N * cs.delta (j + 1) ≤ deltaCap d (T κ c₉).L N :=
    hnum0.trans (min_le_left _ _)
  have hα0 : 0 ≤ (P6 κ c₉).alpha d := by
    unfold Consts.alpha
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith [hadm.γ_lt]
  have hnumε : ∀ jj, 1 ≤ jj → jj ≤ j + 1 →
      gammaConst d (T κ c₉).L N * cs.delta (j + 1) ≤ (P6 κ c₉).eps d (T κ c₉).L jj := by
    intro jj _ hj
    refine hnum0.trans ((min_le_right _ _).trans ?_)
    refine (le_epsSeq (T κ c₉).L ((P6 κ c₉).alpha d) (P6 κ c₉).α₀ hadm.α₀_pos.le hLpos (j + 1)).trans ?_
    exact Balaban.Fluctuation.epsSeq_anti (T κ c₉).L ((P6 κ c₉).alpha d) (P6 κ c₉).α₀ hadm.α₀_pos.le hα0 hj
  have hβpos : 0 < β := by linarith
  have hβk : 0 ≤ F.sf.β (j + 1) := by rw [hbk]; positivity
  refine ⟨HB, ?_⟩
  exact measInt_sfFactor2_univ_of_delta_le (F.ctx hM6 hkK nK) h vc rfl hTm hRt g hg HB hL3
    hνs hh hμ hμBg hact hβk hBgJ hratioJ hBgR hratioR hnum hnumε

end Inputs

end Balaban.RootFSpine
