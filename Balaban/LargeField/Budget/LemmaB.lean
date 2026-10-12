module

public import Balaban.LargeField.Budget.Exponents
public import Balaban.LargeField.Counter.Instantiation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Lemma B: the budget recursion (Part II, Lemma II.5.12)

For every component `Z'` of `Z^pre_{k+1}` (hull closure included: the hull cubes are cubes of
`Z^c_k ∩ Z'`, charged at the rate of `κ^{(k)}`),
```
G^pre_{k+1}(Z') ≥ ∑_{Y ∈ Anc_k(Z')} G_k(Y) + g_k |𝒩_{k+1} ∩ Z'|_# - c_v λ̂_{k+1} |Z'|_#.
```
`lemmaB` states this in exactly the form of the `budget` argument of `RegionHistory.toLF2Hyp`,
for arbitrary post-`R` exponents and factors; `lemmaB_recursive` is the case of the recursive
`kappa`, `logC` of Definition II.5.11.

The numerical hypotheses are collected in `BudgetSetup`: the running coefficients (I.2), the
conversion `λ_j = λ̂_j` of (I.3), the analytic conditions (Λ15), (Λ16) at every scale, and
`c_v ≥ M^d (H₀ + c₁ + 3)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

/-- The hypotheses of Lemma II.5.12 (data and conditions): the running coefficients `β_j`
satisfy (I.2) with `ε ≤ 1/20`; `λ_j = λ̂_j`; (Λ15), (Λ16) hold at every `λ_j`; `L ≤ M`;
`H₀, c₁ ≥ 0`; `c_v ≥ M^d (H₀ + c₁ + 3)`. -/
structure BudgetSetup (S : Setting) (P : BudgetConsts) where
  β : ℝ
  ν : ℝ
  a : ℝ
  ε : ℝ
  nuRun : ℕ → ℝ
  K : AnalyticConsts
  run : RunningHyp S.d S.L β ν a ε P.beta nuRun
  lam_eq : ∀ j, S.lam j = lamHat S.d S.L β a j
  Kd : K.d = S.d
  KL : K.L = S.L
  Kp0 : K.p0 = S.p0
  KH0 : K.H0 = P.H0
  Kc2 : K.c2 = P.c2
  lam_cond : ∀ j, AnalyticLamAt K (S.lam j)
  H0_nonneg : 0 ≤ P.H0
  c1_nonneg : 0 ≤ P.c1
  L_le_M : S.L ≤ S.M
  cv_ge : (S.M : ℝ) ^ S.d * (P.H0 + P.c1 + 3) ≤ S.cv

theorem Setting.Ok.one_le_p0 {S : Setting} (ok : S.Ok) : 1 ≤ S.p0 := by
  have h1 := ok.p2_ge
  have h2 := ok.p0_gt
  omega

theorem Setting.Ok.L_pow_pos {S : Setting} (ok : S.Ok) : (0 : ℝ) < (S.L : ℝ) ^ S.d := by
  have := ok.two_le_L
  positivity

theorem Setting.Ok.M_pow_pos {S : Setting} (ok : S.Ok) : (0 : ℝ) < (S.M : ℝ) ^ S.d := by
  have := ok.one_le_M
  positivity

namespace BudgetSetup

variable {S : Setting} {P : BudgetConsts} (B : BudgetSetup S P) (ok : S.Ok)

include B ok

/-- Lemma II.1.2 (d) with (Λ15): the gain `g_k ≤ A₃ (log β_k)^{2p₀}`. -/
theorem gain_ge (k : ℕ) :
    S.g k ≤ S.A3 * Real.log (P.beta k) ^ (2 * S.p0) := by
  have h15 := (B.lam_cond k).lam15
  rw [B.Kp0, B.lam_eq] at h15
  have := B.run.gain_conv ok.A3_pos.le ok.one_le_p0 k h15
  unfold Setting.g
  rw [B.lam_eq]
  exact this

/-- Old volume: `H_k - L^{-d} H_{k+1} ≥ 1` (Lemma II.1.2 (b), (e) with (Λ16)). -/
theorem old_volume (k : ℕ) :
    1 ≤ HRun P.H0 P.beta k - ((S.L : ℝ) ^ S.d)⁻¹ * HRun P.H0 P.beta (k + 1) := by
  have h16 := (B.lam_cond k).lam16a
  rw [B.KH0, B.Kd, B.KL] at h16
  have hb := B.run.logBeta_ge k
  have hs := B.run.logBeta_succ_le k
  have hε := B.run.hε
  have hε0 := B.run.hε0
  have hu : 0 < ((S.L : ℝ) ^ S.d)⁻¹ := inv_pos.2 (ok.L_pow_pos)
  have hu1 : ((S.L : ℝ) ^ S.d)⁻¹ ≤ 1 := by
    have : (1 : ℝ) ≤ (S.L : ℝ) ^ S.d := by
      have : (1 : ℝ) ≤ S.L := by exact_mod_cast (by have := ok.two_le_L; omega : 1 ≤ S.L)
      exact one_le_pow₀ this
    exact inv_le_one_of_one_le₀ this
  set u := ((S.L : ℝ) ^ S.d)⁻¹ with hu_def
  rw [B.lam_eq] at h16
  unfold HRun
  have key : (1 - u) * (lamHat S.d S.L B.β B.a k - 3) - u * (thetaOf S.d S.L + 1) ≤
      Real.log (P.beta k) - u * Real.log (P.beta (k + 1)) := by
    nlinarith [mul_nonneg hu.le (show (0 : ℝ) ≤ 1 / 10 - 2 * B.ε by linarith)]
  have := mul_le_mul_of_nonneg_left key B.H0_nonneg
  nlinarith [this]

/-- The new-volume charge: `(c₁ log β_k + c₂ + H_{k+1}) M^d + (5/4) L^d ≤ c_v λ_{k+1}`. -/
theorem new_volume (k : ℕ) :
    (P.c1 * Real.log (P.beta k) + P.c2 + HRun P.H0 P.beta (k + 1)) * (S.M : ℝ) ^ S.d +
      5 / 4 * (S.L : ℝ) ^ S.d ≤ S.cv * S.lam (k + 1) := by
  have h16 := (B.lam_cond (k + 1)).lam16b
  rw [B.Kc2] at h16
  have hlk : Real.log (P.beta k) ≤ S.lam (k + 1) := by
    have h1 := B.run.logBeta_le k
    have hθ := B.run.theta_nonneg
    have h2 : lamHat S.d S.L B.β B.a k ≤ lamHat S.d S.L B.β B.a (k + 1) := by
      unfold lamHat; push_cast; nlinarith
    rw [B.lam_eq]; linarith
  have hlk1 : Real.log (P.beta (k + 1)) ≤ S.lam (k + 1) := by
    rw [B.lam_eq]; exact B.run.logBeta_le (k + 1)
  have hlam0 : 0 ≤ S.lam (k + 1) := by
    have := ok.one_le_lam (k + 1)
    linarith
  have hML : ((S.L : ℝ)) ≤ (S.M : ℝ) := by exact_mod_cast B.L_le_M
  have hLd : (S.L : ℝ) ^ S.d ≤ (S.M : ℝ) ^ S.d := pow_le_pow_left₀ (by positivity) hML _
  have hM := ok.M_pow_pos
  have hLpos := ok.L_pow_pos
  have hH1 : HRun P.H0 P.beta (k + 1) ≤ P.H0 * S.lam (k + 1) :=
    mul_le_mul_of_nonneg_left hlk1 B.H0_nonneg
  have hc1 : P.c1 * Real.log (P.beta k) ≤ P.c1 * S.lam (k + 1) :=
    mul_le_mul_of_nonneg_left hlk B.c1_nonneg
  have h2 : (P.c1 * Real.log (P.beta k) + P.c2 + HRun P.H0 P.beta (k + 1)) +
      5 / 4 * ((S.L : ℝ) ^ S.d / (S.M : ℝ) ^ S.d) ≤ (P.H0 + P.c1 + 3) * S.lam (k + 1) := by
    have : (S.L : ℝ) ^ S.d / (S.M : ℝ) ^ S.d ≤ 1 := (div_le_one hM).2 hLd
    nlinarith
  have h3 : ((S.M : ℝ) ^ S.d * (P.H0 + P.c1 + 3)) * S.lam (k + 1) ≤ S.cv * S.lam (k + 1) :=
    mul_le_mul_of_nonneg_right B.cv_ge hlam0
  have h4 := mul_le_mul_of_nonneg_left h2 hM.le
  have e : (S.M : ℝ) ^ S.d * (5 / 4 * ((S.L : ℝ) ^ S.d / (S.M : ℝ) ^ S.d)) =
      5 / 4 * (S.L : ℝ) ^ S.d := by field_simp
  nlinarith [h4, h3, e]

end BudgetSetup

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0) {P : BudgetConsts}

/-- **Lemma II.5.12 (Lemma B: the budget recursion; LF-2's hypothesis (B))**, in the form of the
`budget` argument of `RegionHistory.toLF2Hyp`: for every component `Z'` of `Z^pre_{k+1}` (hull
closure included),
`∑_Y G_k(Y) + g_k |𝒩_{k+1} ∩ Z'|_# - c_v λ_{k+1} |Z'|_# ≤ G^pre_{k+1}(Z')`,
for arbitrary post-`R` exponents `κ_k` and factors `log C_k` of the old parts. -/
theorem lemmaB (B : BudgetSetup S P) (ok : S.Ok) (κ logC : ∀ k, H.Comp k → ℝ) (K : ℕ) :
    ∀ k, k < K → ∀ Z' : H.Comp (k + 1),
      ∑ c ∈ H.parts k Z', H.Gpost P κ logC k c + S.g k * (Z'.1 ∩ H.newCubes (k + 1)).card -
        S.cv * S.lam (k + 1) * Z'.1.card ≤ H.Gpre P κ logC (k + 1) Z' := by
  intro k _ Z'
  have hcnt := H.card_oldCubes_add_outCubes k Z'
  have hsum := H.sum_parts_card k Z'
  have hu := ok.L_pow_pos
  have hm := ok.M_pow_pos
  -- the sum of the old budgets
  have hG : ∑ c ∈ H.parts k Z', H.Gpost P κ logC k c =
      ∑ c ∈ H.parts k Z', κ k c - ∑ c ∈ H.parts k Z', logC k c -
        HRun P.H0 P.beta k * ((S.M : ℝ) ^ S.d * ((H.oldCubes k Z').card : ℝ)) := by
    unfold Gpost BudgetConsts.budgetG BudgetConsts.cubeVol
    have hsum' : ∑ c ∈ H.parts k Z', ((c.1.card : ℕ) : ℝ) = ((H.oldCubes k Z').card : ℝ) := by
      exact_mod_cast hsum
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hsum',
      ← Finset.mul_sum]
  have hP : H.Gpre P κ logC (k + 1) Z' =
      (∑ c ∈ H.parts k Z', κ k c + S.A3 * Real.log (P.beta k) ^ (2 * S.p0) * (((Z'.1 ∩ H.newCubes (k + 1)).card : ℕ) : ℝ) -
        (P.c1 * Real.log (P.beta k) + P.c2) * ((S.M : ℝ) ^ S.d / (S.L : ℝ) ^ S.d * ((H.outCubes k Z').card : ℝ))) -
      (∑ c ∈ H.parts k Z', logC k c + ((H.oldCubes k Z').card : ℝ) + 5 / 4 * ((H.outCubes k Z').card : ℝ)) -
        HRun P.H0 P.beta (k + 1) * ((S.M : ℝ) ^ S.d * ((Z'.1.card : ℕ) : ℝ)) := by
    simp only [Gpre, BudgetConsts.budgetG, BudgetConsts.cubeVol, kappaPre, logCPre,
      BudgetConsts.kappaStep]
    ring
  set n1 : ℝ := ((H.oldCubes k Z').card : ℝ) with hn1
  set n2 : ℝ := ((H.outCubes k Z').card : ℝ) with hn2
  set z : ℝ := (Z'.1.card : ℝ) with hz
  set N : ℝ := ((Z'.1 ∩ H.newCubes (k + 1)).card : ℝ) with hN
  have hcnt' : n1 + n2 = (S.L : ℝ) ^ S.d * z := by
    rw [hn1, hn2, hz]; exact_mod_cast hcnt
  have hsum' : ∑ c ∈ H.parts k Z', (c.1.card : ℝ) = n1 := by
    rw [hn1]; exact_mod_cast hsum
  have hn1nn : 0 ≤ n1 := Nat.cast_nonneg _
  have hn2nn : 0 ≤ n2 := Nat.cast_nonneg _
  have hNnn : 0 ≤ N := Nat.cast_nonneg _
  have hznn : 0 ≤ z := Nat.cast_nonneg _
  rw [hG, hP]
  have hgain := B.gain_ge ok k
  have hvol := B.old_volume ok k
  have hnew := B.new_volume ok k
  have h1 : S.g k * N ≤ S.A3 * Real.log (P.beta k) ^ (2 * S.p0) * N :=
    mul_le_mul_of_nonneg_right hgain hNnn
  -- n₁ term
  have hz_eq : z = (n1 + n2) / (S.L : ℝ) ^ S.d := by
    field_simp; linarith
  have h2 : 0 ≤ n1 * ((S.M : ℝ) ^ S.d * (HRun P.H0 P.beta k -
      ((S.L : ℝ) ^ S.d)⁻¹ * HRun P.H0 P.beta (k + 1)) - 1) := by
    apply mul_nonneg hn1nn
    have hM1 : (1 : ℝ) ≤ (S.M : ℝ) ^ S.d := by
      have : (1 : ℝ) ≤ S.M := by exact_mod_cast ok.one_le_M
      exact one_le_pow₀ this
    nlinarith
  -- n₂ term
  have h3 : n2 * ((P.c1 * Real.log (P.beta k) + P.c2 + HRun P.H0 P.beta (k + 1)) *
      ((S.M : ℝ) ^ S.d / (S.L : ℝ) ^ S.d) + 5 / 4) ≤ S.cv * S.lam (k + 1) * z := by
    have hcvl : 0 ≤ S.cv * S.lam (k + 1) := by
      have h0 : 0 ≤ S.cv := by
        have := B.cv_ge
        have h5 : 0 ≤ (S.M : ℝ) ^ S.d * (P.H0 + P.c1 + 3) := by
          have := B.H0_nonneg; have := B.c1_nonneg; positivity
        linarith
      have h6 := ok.one_le_lam (k + 1)
      positivity
    have e1 : (P.c1 * Real.log (P.beta k) + P.c2 + HRun P.H0 P.beta (k + 1)) *
        ((S.M : ℝ) ^ S.d / (S.L : ℝ) ^ S.d) + 5 / 4 =
        ((P.c1 * Real.log (P.beta k) + P.c2 + HRun P.H0 P.beta (k + 1)) * (S.M : ℝ) ^ S.d +
          5 / 4 * (S.L : ℝ) ^ S.d) / (S.L : ℝ) ^ S.d := by
      field_simp
    rw [e1]
    have e2 : S.cv * S.lam (k + 1) * z = S.cv * S.lam (k + 1) * (n1 + n2) /
        (S.L : ℝ) ^ S.d := by rw [hz_eq]; ring
    rw [e2, ← mul_div_assoc, div_le_div_iff_of_pos_right hu]
    have := mul_le_mul_of_nonneg_left hnew hn2nn
    nlinarith [mul_nonneg hcvl hn1nn]
  have e3 : HRun P.H0 P.beta (k + 1) * ((S.M : ℝ) ^ S.d * z) =
      HRun P.H0 P.beta (k + 1) * ((S.M : ℝ) ^ S.d * ((n1 + n2) / (S.L : ℝ) ^ S.d)) := by
    rw [hz_eq]
  have e4 : (P.c1 * Real.log (P.beta k) + P.c2) * ((S.M : ℝ) ^ S.d / (S.L : ℝ) ^ S.d * n2) +
      HRun P.H0 P.beta (k + 1) * ((S.M : ℝ) ^ S.d * ((n1 + n2) / (S.L : ℝ) ^ S.d)) =
      n2 * ((P.c1 * Real.log (P.beta k) + P.c2 + HRun P.H0 P.beta (k + 1)) *
        ((S.M : ℝ) ^ S.d / (S.L : ℝ) ^ S.d)) +
      HRun P.H0 P.beta (k + 1) * (S.M : ℝ) ^ S.d * ((S.L : ℝ) ^ S.d)⁻¹ * n1 := by
    field_simp
    ring
  have e5 : n1 * ((S.M : ℝ) ^ S.d * (HRun P.H0 P.beta k -
      ((S.L : ℝ) ^ S.d)⁻¹ * HRun P.H0 P.beta (k + 1)) - 1) =
      n1 * (S.M : ℝ) ^ S.d * HRun P.H0 P.beta k -
        HRun P.H0 P.beta (k + 1) * (S.M : ℝ) ^ S.d * ((S.L : ℝ) ^ S.d)⁻¹ * n1 - n1 := by
    ring
  rw [e3]
  nlinarith [h1, h2, h3, e4, e5]

/-- **Lemma B along the history** (Definition II.5.11): the same for the recursive `kappa`,
`logC` with kept data `κK`, `lK`. -/
theorem lemmaB_recursive (B : BudgetSetup S P) (ok : S.Ok) (κK lK : ∀ k, H.Comp k → ℝ)
    (K : ℕ) :
    ∀ k, k < K → ∀ Z' : H.Comp (k + 1),
      ∑ c ∈ H.parts k Z', H.budgetPost P κK lK k c + S.g k * (Z'.1 ∩ H.newCubes (k + 1)).card -
        S.cv * S.lam (k + 1) * Z'.1.card ≤ H.budgetPre P κK lK (k + 1) Z' :=
  H.lemmaB B ok (H.kappa P κK) (H.logC lK) K

/-- The abstract history of LF-2 for the flow's region history, with (B) supplied by Lemma B for
the recursive exponents of Definition II.5.11; (Rg) remain hypotheses (LF-4R, Part III). -/
noncomputable def toLF2HypBudget (B : BudgetSetup S P) (ok : S.Ok) (hadm : H.Admissible)
    (κK lK : ∀ k, H.Comp k → ℝ) (K : ℕ)
    (rg_ripe : ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : H.Comp k, c.1 ∉ H.rem k → S.Ripe k (H.bk k c) →
      H.budgetPre P κK lK k c - S.CR * S.lam k ^ (2 * S.d + 1) + S.A3' * S.lam k ^ S.pR ≤
        H.budgetPost P κK lK k c)
    (rg_nonripe : ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : H.Comp k, c.1 ∉ H.rem k → ¬ S.Ripe k (H.bk k c) →
      H.budgetPost P κK lK k c = H.budgetPre P κK lK k c)
    (rg_frozen : ∀ k, k0 < k → ∀ c : H.Comp k,
      H.budgetPost P κK lK k c = H.budgetPre P κK lK k c) : LF2Hyp S n k0 K :=
  H.toLF2Hyp hadm K (H.budgetPre P κK lK) (H.budgetPost P κK lK)
    (H.lemmaB_recursive B ok κK lK K) rg_ripe rg_nonripe rg_frozen

end RegionHistory

end Balaban.LargeField
