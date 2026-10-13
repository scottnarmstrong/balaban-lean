/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.D1ParentDomain

/-!
# From a threshold `β₀` to the premises of the early parent-domain theorem (`InitialBetaBridge`)

`notes/phase1/Q13-LATE.md`, "Initial coupling and all-scale theorem".  The landed early theorem
`inPsiTilde_of_postTerm2_ne_zero` assumes at each scale `k` a largeness condition on the running
coupling `2 a e^{2ε} < A₀² λ_k^{2p₀}` and smallness of the tolerances `δ_k = (β_k a)^{-1/2} A₀ λ_k^{p₀}`.
In the papers these hold because `β ≥ β₀` with `β₀` large.  Here the threshold is two explicit
inequalities on `x₀ = log (a β₀) - 1`:

* `2 a e^{2ε} < A₀² x₀^{2p₀}` and `0 ≤ x₀` (largeness);
* `(4 (D+1) + 3 D L) · A₀ · 2^{p₀+1} (p₀+1)! < x₀` (smallness; `D = S.d`).

Since `λ̂₀ - 2 = log (a β) - 1` and `λ_k ≥ λ̂_k - 2 ≥ λ̂₀ - 2`, every scale `k` satisfies
`λ_k ≥ x₀`, and `δ_k ≤ A₀ 2^{p₀+1} (p₀+1)! / λ_k` by `e^y ≥ y^n / n!`.  `exists_beta0` shows the
thresholds are satisfiable (for `1 ≤ p₀`).

NOT proved here: the late-scale parent domain (`k > k₀`), the directional estimate on retained
shells, and the physical instantiation.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.LargeField.Def7
  Balaban.SmallField.Def6v2

/-- Threshold constant `2^{p₀+1} (p₀+1)!` in `x^{p₀} e^{-x/2} ≤ M / x`. -/
noncomputable def expTailConst (p0 : ℕ) : ℝ := 2 ^ (p0 + 1) * ((p0 + 1).factorial : ℝ)

theorem expTailConst_pos (p0 : ℕ) : 0 < expTailConst p0 := by
  unfold expTailConst; positivity

/-- `x^{p₀+1} ≤ M e^{x/2}` for `x ≥ 0`. -/
theorem pow_succ_le_const_mul_exp (p0 : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ (p0 + 1) ≤ expTailConst p0 * Real.exp (x / 2) := by
  have h := Real.pow_div_factorial_le_exp (x / 2) (by positivity) (p0 + 1)
  have hf : (0 : ℝ) < ((p0 + 1).factorial : ℝ) := by positivity
  rw [div_pow, div_div, div_le_iff₀ (by positivity)] at h
  unfold expTailConst
  nlinarith [h, Real.exp_pos (x / 2)]

/-- **T1.**  Monotone transfer of the threshold: `λ̂₀ - 2 = log (a β) - 1`. -/
theorem lamHat_zero_sub_two (d L : ℕ) (β a : ℝ) :
    lamHat d L β a 0 - 2 = Real.log (a * β) - 1 := by
  unfold lamHat; simp [mul_comm]; ring

theorem threshold_transfer {d L : ℕ} {a A0 β0 β ε : ℝ} {p0 : ℕ} (ha : 0 < a) (hβ0 : 0 < β0)
    (hβ : β0 ≤ β)
    (h2 : 2 ≤ Real.log (a * β0) + 1)
    (hlam : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * (Real.log (a * β0) - 1) ^ (2 * p0)) :
    2 ≤ lamHat d L β a 0 ∧
      2 * a * Real.exp (2 * ε) < A0 ^ 2 * (lamHat d L β a 0 - 2) ^ (2 * p0) := by
  have hlog : Real.log (a * β0) ≤ Real.log (a * β) :=
    Real.log_le_log (mul_pos ha hβ0) (by nlinarith)
  have e := lamHat_zero_sub_two d L β a
  refine ⟨by linarith, ?_⟩
  rw [e]
  refine lt_of_lt_of_le hlam ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (by linarith) (by linarith) _

variable {d L : ℕ} {β ν a ε : ℝ} {b n : ℕ → ℝ}

/-- **T2 (lower bound).**  Under `β₀ ≤ β`, `x₀ = log (a β₀) - 1 ≤ λ_k` for every scale `k`. -/
theorem runLam_ge_threshold (h : RunningHyp d L β ν a ε b n) {β0 : ℝ} (hβ0 : 0 < β0)
    (hβ : β0 ≤ β) (k : ℕ) : Real.log (a * β0) - 1 ≤ runLam a b k := by
  have h1 := h.hat_le_runLam_add_two k
  have h2 := h.lamHat_mono k
  have h3 := lamHat_zero_sub_two d L β a
  have ha : 0 < a := by linarith [h.ha1]
  have hlog : Real.log (a * β0) ≤ Real.log (a * β) :=
    Real.log_le_log (mul_pos ha hβ0) (by nlinarith)
  linarith

/-- **T2.**  The premises `hl0`, `hlam` of `inPsiTilde_of_postTerm2_ne_zero`, at every scale. -/
theorem premises_of_threshold (h : RunningHyp d L β ν a ε b n) {A0 β0 : ℝ} {p0 : ℕ}
    (hβ0 : 0 < β0) (hβ : β0 ≤ β) (h2 : 2 ≤ Real.log (a * β0) + 1)
    (hlam : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * (Real.log (a * β0) - 1) ^ (2 * p0)) (k : ℕ) :
    0 ≤ runLam a b k ∧ 2 * a * Real.exp (2 * ε) < A0 ^ 2 * runLam a b k ^ (2 * p0) := by
  have hx := runLam_ge_threshold h hβ0 hβ k
  have hx0 : 0 ≤ Real.log (a * β0) - 1 := by linarith
  refine ⟨by linarith, lt_of_lt_of_le hlam ?_⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx _) (by positivity)

/-- `δ_k = A₀ λ_k^{p₀} e^{-λ_k/2}`. -/
theorem deltaRun_eq_exp (h : RunningHyp d L β ν a ε b n) (A0 : ℝ) (p0 : ℕ) (k : ℕ) :
    deltaRun A0 p0 a b k = A0 * runLam a b k ^ p0 * Real.exp (-(runLam a b k / 2)) := by
  obtain ⟨γ, hγ, -, hb⟩ := h.beta_eq k
  have hpos : 0 < b k * a := by
    rw [hb]
    have : 0 < (L : ℝ) := by have := h.hL; positivity
    have := h.hβ; have := h.ha1
    positivity
  unfold deltaRun pZero
  rw [Real.rpow_def_of_pos hpos]
  have : Real.log (b k * a) * -(1 / 2 : ℝ) = -(runLam a b k / 2) := by
    unfold runLam; ring
  rw [this]; ring

/-- **T3 (smallness, general form).**  If `λ ≥ x₀ > 0` and `K A₀ M < x₀`, then
`δ(λ) · K < 1` and `δ(λ) > 0`. -/
theorem delta_small_aux {A0 : ℝ} {p0 : ℕ} {Kc x lam : ℝ} (hA0 : 0 < A0) (hK : 0 ≤ Kc)
    (hx : Kc * (A0 * expTailConst p0) < x) (hl : x ≤ lam) :
    0 < A0 * lam ^ p0 * Real.exp (-(lam / 2)) ∧
      Kc * (A0 * lam ^ p0 * Real.exp (-(lam / 2))) < 1 := by
  have hM := expTailConst_pos p0
  have hxpos : 0 < x := lt_of_le_of_lt (by positivity) hx
  have hlpos : 0 < lam := lt_of_lt_of_le hxpos hl
  refine ⟨by positivity, ?_⟩
  have h1 := pow_succ_le_const_mul_exp p0 hlpos.le
  rw [Real.exp_neg]
  have hE := Real.exp_pos (lam / 2)
  have key : lam ^ p0 * (Kc * (A0 * expTailConst p0)) < lam ^ p0 * lam := by
    exact mul_lt_mul_of_pos_left (lt_of_lt_of_le hx hl) (by positivity)
  have : Kc * (A0 * lam ^ p0 * (Real.exp (lam / 2))⁻¹) =
      (Kc * A0 * lam ^ p0) / Real.exp (lam / 2) := by field_simp
  rw [this, div_lt_one hE]
  have hKA : 0 ≤ Kc * A0 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hKA, pow_succ lam p0]

/-- **T3.**  For every scale `k` the tolerances are positive and `(4 (D+1) + 3 D L') δ_k < 1`. -/
theorem deltaRun_small (h : RunningHyp d L β ν a ε b n) {A0 β0 : ℝ} {p0 : ℕ} (D L' : ℕ)
    (hA0 : 0 < A0) (hβ0 : 0 < β0) (hβ : β0 ≤ β)
    (hK : ((4 * ((D : ℝ) + 1) + 3 * D * L') * (A0 * expTailConst p0)) <
      Real.log (a * β0) - 1) (k : ℕ) :
    0 < deltaRun A0 p0 a b k ∧
      (4 * ((D : ℝ) + 1) + 3 * D * L') * deltaRun A0 p0 a b k < 1 := by
  rw [deltaRun_eq_exp h]
  exact delta_small_aux hA0 (by positivity) hK (runLam_ge_threshold h hβ0 hβ k)

/-- **T3 (the three premises).**  `0 < δ_k`, `(D+1) δ_k ≤ 1` and
`max (3 D L' δ_{k-1}) (4 (D+1) δ_k) < 1`, stated at `k = j + 1` with `δ_j`. -/
theorem deltaRun_premises (h : RunningHyp d L β ν a ε b n) {A0 β0 : ℝ} {p0 : ℕ} (D L' : ℕ)
    (hA0 : 0 < A0) (hβ0 : 0 < β0) (hβ : β0 ≤ β)
    (hK : ((4 * ((D : ℝ) + 1) + 3 * D * L') * (A0 * expTailConst p0)) <
      Real.log (a * β0) - 1) (j : ℕ) :
    0 < deltaRun A0 p0 a b (j + 1) ∧ ((D : ℝ) + 1) * deltaRun A0 p0 a b (j + 1) ≤ 1 ∧
      max (3 * (D : ℝ) * L' * deltaRun A0 p0 a b j)
        (4 * ((D : ℝ) + 1) * deltaRun A0 p0 a b (j + 1)) < 1 := by
  obtain ⟨p1, s1⟩ := deltaRun_small h D L' hA0 hβ0 hβ hK (j + 1)
  obtain ⟨p2, s2⟩ := deltaRun_small h D L' hA0 hβ0 hβ hK j
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ L' := Nat.cast_nonneg _
  refine ⟨p1, by nlinarith [mul_nonneg (mul_nonneg hD hL) p1.le], max_lt ?_ ?_⟩
  · nlinarith [mul_nonneg (mul_nonneg hD hL) p2.le, mul_pos (by linarith : (0:ℝ) < 4 * (D + 1)) p2]
  · nlinarith [mul_nonneg (mul_nonneg hD hL) p1.le]

/-- **Non-vacuity.**  For `1 ≤ p₀` and `a, A₀ > 0` there is `β₀ > 0` satisfying both thresholds. -/
theorem exists_beta0 (D L' : ℕ) (a A0 ε : ℝ) (p0 : ℕ) (ha : 0 < a) (hA0 : 0 < A0)
    (hp : 1 ≤ p0) :
    ∃ β0 : ℝ, 0 < β0 ∧ 2 ≤ Real.log (a * β0) + 1 ∧
      2 * a * Real.exp (2 * ε) < A0 ^ 2 * (Real.log (a * β0) - 1) ^ (2 * p0) ∧
      ((4 * ((D : ℝ) + 1) + 3 * D * L') * (A0 * expTailConst p0)) < Real.log (a * β0) - 1 := by
  set x : ℝ := max 1 (max ((4 * ((D : ℝ) + 1) + 3 * D * L') * (A0 * expTailConst p0) + 1)
    (2 * a * Real.exp (2 * ε) / A0 ^ 2 + 1)) with hx
  have hx1 : 1 ≤ x := le_max_left _ _
  have hx2 : (4 * ((D : ℝ) + 1) + 3 * D * L') * (A0 * expTailConst p0) + 1 ≤ x :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hx3 : 2 * a * Real.exp (2 * ε) / A0 ^ 2 + 1 ≤ x :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Real.exp (x + 1) / a, by positivity, ?_⟩
  have hl : Real.log (a * (Real.exp (x + 1) / a)) = x + 1 := by
    rw [mul_div_cancel₀ _ ha.ne', Real.log_exp]
  rw [hl]
  refine ⟨by linarith, ?_, by linarith⟩
  have hA2 : 0 < A0 ^ 2 := by positivity
  have h1 : 2 * a * Real.exp (2 * ε) / A0 ^ 2 < x := by linarith
  rw [div_lt_iff₀ hA2] at h1
  have h2 : x ≤ x ^ (2 * p0) := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ (2 * p0) := pow_le_pow_right₀ hx1 (by omega)
  have : x + 1 - 1 = x := by ring
  rw [this]
  nlinarith

section Wrapper

/-- **T4.**  The early parent-domain theorem with `hl0`, `hlam`, `hδ`, `hδ1` replaced by
`β₀ ≤ β` and the two thresholds on `x₀ = log (a β₀) - 1`.  The remaining hypotheses are those of
`inPsiTilde_of_postTerm2_ne_zero`, unchanged.  Scales `k = j + 1 ≤ k₀` only. -/
theorem inPsiTilde_of_postTerm2_ne_zero_of_beta0
    {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
    [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ) (rep : Rep S n R k0 K M N geo cs P (j + 1))
    (A : LabHist S n R k0 K)
    {d : ℕ} {β ν0 a ε : ℝ} {b nr : ℕ → ℝ} {A0 : ℝ} {p0 : ℕ}
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (vc : Def7v2.CorrCoef S.d)
    (hgeo : Cx.geo = geo) (hcs : Cx.cs = cs)
    (hreg : RunningHyp d S.L β ν0 a ε b nr) (hg' : KZeroGenuine β ν0)
    (hk : j + 1 ≤ kZero d S.L β ν0) (hA0 : 0 ≤ A0)
    {β0 : ℝ} (hβ0 : 0 < β0) (hβ : β0 ≤ β)
    (hthr1 : 2 ≤ Real.log (a * β0) + 1)
    (hthr2 : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * (Real.log (a * β0) - 1) ^ (2 * p0))
    (hthr3 : ((4 * ((S.d : ℝ) + 1) + 3 * S.d * S.L) * (A0 * expTailConst p0)) <
      Real.log (a * β0) - 1)
    (hδrun : Cx.cs.delta = deltaRun A0 p0 a b) (hunit : ‖hv‖ = 1)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    (hT : Def7v2.postTerm2 Cx vc rep A ψk hv g ≠ 0) :
    InPsiTilde (Cx.genW ((A.H.step (j + 1)).Z)ᶜ) (sfBgMassAt S.L (j + 1) (nr (j + 1)))
      (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
      (parentPsi Cx ψk) (fun i => hv i) := by
  obtain ⟨hl0, hlam⟩ := premises_of_threshold (A0 := A0) (p0 := p0) hreg hβ0 hβ hthr1 hthr2 (j + 1)
  have hApos : 0 < A0 := by
    rcases hA0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hthr2
      have : 0 < 2 * a * Real.exp (2 * ε) := by
        have := hreg.ha1; positivity
      simp at hthr2; linarith
  obtain ⟨hδ, hδ1, -⟩ := deltaRun_premises hreg S.d S.L hApos hβ0 hβ hthr3 j
  exact inPsiTilde_of_postTerm2_ne_zero Cx rep A ψk hv g vc hgeo hcs hreg hg' hk hA0 hl0 hlam
    hδrun hunit (by rw [hδrun]; exact hδ) (by rw [hδrun]; exact hδ1) HB hT

/-- **T4, existential form.**  For `1 ≤ p₀`, `a, A₀ > 0` there is a threshold `β₀ > 0` (depending only
on `S.d`, `S.L`, `a`, `A₀`, `ε`, `p₀`) such that for every `β ≥ β₀` the early parent-domain
conclusion holds without the premises `hl0`, `hlam`, `hδ`, `hδ1`. -/
theorem exists_beta0_inPsiTilde
    {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
    [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ) (rep : Rep S n R k0 K M N geo cs P (j + 1))
    (A : LabHist S n R k0 K) (a ε A0 : ℝ) (p0 : ℕ) (ha : 0 < a) (hA0 : 0 < A0) (hp : 1 ≤ p0) :
    ∃ β0 : ℝ, 0 < β0 ∧ ∀ {d : ℕ} {β ν0 : ℝ} {b nr : ℕ → ℝ},
      β0 ≤ β →
      ∀ (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))
        (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) (vc : Def7v2.CorrCoef S.d),
      Cx.geo = geo → Cx.cs = cs →
      RunningHyp d S.L β ν0 a ε b nr → KZeroGenuine β ν0 →
      j + 1 ≤ kZero d S.L β ν0 →
      Cx.cs.delta = deltaRun A0 p0 a b → ‖hv‖ = 1 →
      BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)) →
      Def7v2.postTerm2 Cx vc rep A ψk hv g ≠ 0 →
      InPsiTilde (Cx.genW ((A.H.step (j + 1)).Z)ᶜ) (sfBgMassAt S.L (j + 1) (nr (j + 1)))
        (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
        (parentPsi Cx ψk) (fun i => hv i) := by
  obtain ⟨β0, hβ0, h1, h2, h3⟩ := exists_beta0 S.d S.L a A0 ε p0 ha hA0 hp
  exact ⟨β0, hβ0, fun hβ ψk hv g vc hgeo hcs hreg hg' hk hδrun hunit HB hT =>
    inPsiTilde_of_postTerm2_ne_zero_of_beta0 Cx rep A ψk hv g vc hgeo hcs hreg hg' hk hA0.le hβ0
      hβ h1 h2 h3 hδrun hunit HB hT⟩

end Wrapper

/-- **T5.**  Explicit constants (`a = 5/4`, `A₀ = 1`, `p₀ = 1`, `ε = 1/20`, `d = 3`, `L = 2`)
for which a common threshold `β₀` exists. -/
theorem exists_beta0_example :
    ∃ β0 : ℝ, 0 < β0 ∧ 2 ≤ Real.log (5 / 4 * β0) + 1 ∧
      2 * (5 / 4) * Real.exp (2 * (1 / 20)) < 1 ^ 2 * (Real.log (5 / 4 * β0) - 1) ^ (2 * 1) ∧
      ((4 * (((3 : ℕ) : ℝ) + 1) + 3 * ((3 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) * (1 * expTailConst 1)) <
        Real.log (5 / 4 * β0) - 1 :=
  exists_beta0 3 2 (5 / 4) 1 (1 / 20) 1 (by norm_num) one_pos le_rfl

end Balaban.LargeField
