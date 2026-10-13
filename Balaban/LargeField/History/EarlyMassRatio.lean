/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.ParentDomain
public import Balaban.SmallField.Def6v2Regime

/-!
# The early mass ratio (`EarlyMassRatio`)

`notes/phase1/Q13-YDOMAIN.md` §2.  The parent-domain theorem `inPsiTilde_genW_of_factors` has the
hypothesis `hmass : 2 ν (L^k)² < η²`.  For scales `k ≤ k₀` (genuine a priori index) the parent
small-field solver has the physical mass, `ν (L^k)² = ν_k` (`physMass_mul_sq`), and the running
bound gives `β_k ν_k ≤ E = e^{2ε}` (`beta_mul_nu_le`).  The landed tolerance satisfies
`δ_k² = A₀² λ_k^{2p₀} / (a β_k)` with `λ_k = log (a β_k)` (`deltaRun_eq`), hence

`2 ν_k ≤ (2 a E / (A₀² λ_k^{2p₀})) δ_k²`    (M1, `two_mul_nu_le_ratio_mul_delta_sq`).

* `EarlyMassRatio` (`two_nu_lt_delta_sq`): `2 ν_k < δ_k²` under the single largeness condition
  `hlam : 2 a E < A₀² λ_k^{2p₀}`.
* `two_nu_lt_delta_sq_of_lamHat`: the same for all `k ≤ k₀` under a condition on the initial
  coupling, `2 a E < A₀² (λ̂₀ - 2)^{2p₀}` (`λ̂₀ ≥ 2`).  The running `λ_j` is not exactly monotone
  (the fluctuations `γ_j` of `RunningHyp`), but `λ_j ≥ λ̂_j - 2 ≥ λ̂₀ - 2`.
* `inPsiTilde_genW_of_early`: the parent-domain theorem with `hmass` removed, at scale
  `j + 1 ≤ k₀`, the solver mass being the physical mass `sfBgMassAt L (j+1) ν_{j+1}`.
  The scale `k = j + 1 = k₀` is covered (`beta_mul_nu_le` holds for `j ≤ k₀`); the scales covered
  are exactly `1 ≤ k ≤ k₀`.
* `lower_ratio_of_gt_kZero`: above `k₀` the landed bound is a lower bound, `ν_k > c δ_k²`
  with `c = a e^{-2ε}/(A₀² λ_k^{2p₀})`; no mass-only smallness holds there, and a directional
  condition would be needed (note §2).  This is why the corollary is restricted to `k ≤ k₀`, which
  is the range of the current non-flat use (`D9Coeff.k_le`).

The mass of the `chiY` cube solver (`FieldClauses.mu_eq`, `bgMass k₀`, zero for `k ≤ k₀`) is a
different object from the parent solver's mass `sfBgMassAt` (physical at every scale); here only
the latter is used, as the datum's clause R3 requires.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.LargeField.Def7
  Balaban.SmallField.Def6v2

section Ratio

variable {d L : ℕ} {β ν a ε : ℝ} {b nr : ℕ → ℝ}

/-- `δ_k² = A₀² λ_k^{2p₀} / (a β_k)`. -/
theorem deltaRun_sq (h : RunningHyp d L β ν a ε b nr) (A0 : ℝ) (p0 : ℕ) (k : ℕ) :
    deltaRun A0 p0 a b k ^ 2 = A0 ^ 2 * runLam a b k ^ (2 * p0) / (b k * a) := by
  have ha : 0 < a := by linarith [h.ha1]
  have hb := mul_pos (h.betaRun_pos k) ha
  rw [deltaRun_eq A0 p0 a b k hb, mul_pow, ← Real.exp_nat_mul, mul_pow, ← pow_mul,
    mul_comm p0 2]
  have : (2 : ℕ) * (-runLam a b k / 2) = -runLam a b k := by push_cast; ring
  rw [this, Real.exp_neg]
  have : Real.exp (runLam a b k) = b k * a := by
    unfold runLam; exact Real.exp_log hb
  rw [this]; field_simp

/-- **(M1).**  For `k ≤ k₀` (genuine), `2 ν_k ≤ (2 a E / (A₀² λ_k^{2p₀})) δ_k²`, `E = e^{2ε}`. -/
theorem two_mul_nu_le_ratio_mul_delta_sq (h : RunningHyp d L β ν a ε b nr)
    (hg : KZeroGenuine β ν) {A0 : ℝ} {p0 : ℕ} {k : ℕ} (hk : k ≤ kZero d L β ν)
    (hpos : 0 < A0 ^ 2 * runLam a b k ^ (2 * p0)) :
    2 * nr k ≤ (2 * a * Real.exp (2 * ε) / (A0 ^ 2 * runLam a b k ^ (2 * p0))) *
      deltaRun A0 p0 a b k ^ 2 := by
  have ha : 0 < a := by linarith [h.ha1]
  have hb := h.betaRun_pos k
  have hE := h.beta_mul_nu_le hg hk
  rw [deltaRun_sq h A0 p0 k]
  have : 2 * a * Real.exp (2 * ε) / (A0 ^ 2 * runLam a b k ^ (2 * p0)) *
      (A0 ^ 2 * runLam a b k ^ (2 * p0) / (b k * a)) = 2 * Real.exp (2 * ε) / b k := by
    have hne := hpos.ne'
    have hA : A0 ≠ 0 := fun h0 => by simp [h0] at hpos
    have hp : runLam a b k ^ (2 * p0) ≠ 0 := fun h0 => by simp [h0] at hpos
    field_simp
  rw [this, le_div_iff₀ hb]
  linarith

/-- **`EarlyMassRatio`.**  For `k ≤ k₀` and `2 a E < A₀² λ_k^{2p₀}`: `2 ν_k < δ_k²`. -/
theorem two_nu_lt_delta_sq (h : RunningHyp d L β ν a ε b nr) (hg : KZeroGenuine β ν)
    {A0 : ℝ} {p0 : ℕ} {k : ℕ} (hk : k ≤ kZero d L β ν)
    (hlam : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * runLam a b k ^ (2 * p0)) :
    2 * nr k < deltaRun A0 p0 a b k ^ 2 := by
  have ha : 0 < a := by linarith [h.ha1]
  have h0 : 0 < 2 * a * Real.exp (2 * ε) := by positivity
  have hpos : 0 < A0 ^ 2 * runLam a b k ^ (2 * p0) := h0.trans hlam
  have hM := two_mul_nu_le_ratio_mul_delta_sq h hg hk hpos
  have hδ : 0 < deltaRun A0 p0 a b k ^ 2 := by
    rw [deltaRun_sq h A0 p0 k]
    exact div_pos hpos (mul_pos (h.betaRun_pos k) ha)
  have hr : 2 * a * Real.exp (2 * ε) / (A0 ^ 2 * runLam a b k ^ (2 * p0)) < 1 :=
    (div_lt_one hpos).2 hlam
  calc 2 * nr k ≤ _ := hM
    _ < 1 * deltaRun A0 p0 a b k ^ 2 := mul_lt_mul_of_pos_right hr hδ
    _ = _ := one_mul _

/-- The largeness condition in terms of the initial coupling: `λ_k ≥ λ̂₀ - 2` for every `k`, so
`2 a E < A₀² (λ̂₀ - 2)^{2p₀}` with `λ̂₀ ≥ 2` gives `EarlyMassRatio` at every `k ≤ k₀`. -/
theorem two_nu_lt_delta_sq_of_lamHat (h : RunningHyp d L β ν a ε b nr) (hg : KZeroGenuine β ν)
    {A0 : ℝ} {p0 : ℕ} (h2 : 2 ≤ lamHat d L β a 0)
    (hlam : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * (lamHat d L β a 0 - 2) ^ (2 * p0))
    {k : ℕ} (hk : k ≤ kZero d L β ν) :
    2 * nr k < deltaRun A0 p0 a b k ^ 2 := by
  refine two_nu_lt_delta_sq h hg hk (hlam.trans_le ?_)
  have h1 : lamHat d L β a 0 - 2 ≤ runLam a b k := by
    linarith [h.hat_le_runLam_add_two k, h.lamHat_mono k]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h1 _) (sq_nonneg A0)

/-- Above `k₀` the landed bound is a lower bound:
`(a e^{-2ε} / (A₀² λ_k^{2p₀})) δ_k² < ν_k` (from `lt_beta_mul_nu`).  No mass-only smallness
`2 ν_k < δ_k²` can follow there. -/
theorem lower_ratio_of_gt_kZero (h : RunningHyp d L β ν a ε b nr) {A0 : ℝ} {p0 : ℕ} {k : ℕ}
    (hk : kZero d L β ν < k) (hpos : 0 < A0 ^ 2 * runLam a b k ^ (2 * p0)) :
    (a * Real.exp (-(2 * ε)) / (A0 ^ 2 * runLam a b k ^ (2 * p0))) *
      deltaRun A0 p0 a b k ^ 2 < nr k := by
  have ha : 0 < a := by linarith [h.ha1]
  have hb := h.betaRun_pos k
  have hE := h.lt_beta_mul_nu hk
  rw [deltaRun_sq h A0 p0 k]
  have : a * Real.exp (-(2 * ε)) / (A0 ^ 2 * runLam a b k ^ (2 * p0)) *
      (A0 ^ 2 * runLam a b k ^ (2 * p0) / (b k * a)) = Real.exp (-(2 * ε)) / b k := by
    have hne := hpos.ne'
    have hA : A0 ≠ 0 := fun h0 => by simp [h0] at hpos
    have hp : runLam a b k ^ (2 * p0) ≠ 0 := fun h0 => by simp [h0] at hpos
    field_simp
  rw [this, div_lt_iff₀ hb]
  linarith

end Ratio

section Parent

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (H : RegionHistory S n R k0 K)
  (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- **`hmass` at the early scales.**  At scale `k = j + 1 ≤ k₀` the solver mass is
`ν = sfBgMassAt L k ν_k` (so `ν L^{2k} = ν_k`), the context tolerance is `δ_j = deltaRun … j`
(`Coh.delta_cs`), `η_Y ≥ δ_k`, and `2 a E < A₀² λ_k^{2p₀}`.  Then `2 ν L^{2k} < η²`. -/
theorem hmass_of_early {d : ℕ} {β ν0 a ε : ℝ} {b nr : ℕ → ℝ} {A0 : ℝ} {p0 : ℕ} {ηY : ℝ}
    (h : RunningHyp d S.L β ν0 a ε b nr) (hg : KZeroGenuine β ν0)
    (hk : j + 1 ≤ kZero d S.L β ν0) (hA0 : 0 ≤ A0) (hl0 : 0 ≤ runLam a b (j + 1))
    (hlam : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * runLam a b (j + 1) ^ (2 * p0))
    (hηY : deltaRun A0 p0 a b (j + 1) ≤ ηY) :
    2 * sfBgMassAt S.L (j + 1) (nr (j + 1)) * ((S.L : ℝ) ^ (j + 1)) ^ 2 <
      (max (3 * S.d * S.L * deltaRun A0 p0 a b j) ηY) ^ 2 := by
  have h1 := two_nu_lt_delta_sq h hg hk hlam
  have ha : 0 < a := by linarith [h.ha1]
  have hδ0 : 0 ≤ deltaRun A0 p0 a b (j + 1) := by
    rw [deltaRun_eq A0 p0 a b _ (mul_pos (h.betaRun_pos _) ha)]
    positivity
  have h2 : deltaRun A0 p0 a b (j + 1) ^ 2 ≤ ηY ^ 2 := pow_le_pow_left₀ hδ0 hηY 2
  have h3 : ηY ^ 2 ≤ (max (3 * S.d * S.L * deltaRun A0 p0 a b j) ηY) ^ 2 :=
    pow_le_pow_left₀ (hδ0.trans hηY) (le_max_right _ _) 2
  have h4 : 2 * sfBgMassAt S.L (j + 1) (nr (j + 1)) * ((S.L : ℝ) ^ (j + 1)) ^ 2 =
      2 * nr (j + 1) := by
    rw [mul_assoc]; unfold sfBgMassAt; rw [physMass_mul_sq]
  rw [h4]
  linarith

section Assembly

variable (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
  (ηY : ℝ)

/-- **The parent-domain theorem at the early scales `1 ≤ k = j + 1 ≤ k₀`**: `inPsiTilde_genW_of_factors`
with `hmass` replaced by the regime hypotheses.  The solver mass is `sfBgMassAt L (j+1) ν_{j+1}`;
`hδ` is `Coh.delta_cs`; `hlam` is the largeness condition. -/
theorem inPsiTilde_genW_of_early {d : ℕ} {β ν0 a ε : ℝ} {b nr : ℕ → ℝ} {A0 : ℝ} {p0 : ℕ}
    (hreg : RunningHyp d S.L β ν0 a ε b nr) (hg : KZeroGenuine β ν0)
    (hk : j + 1 ≤ kZero d S.L β ν0) (hA0 : 0 ≤ A0) (hl0 : 0 ≤ runLam a b (j + 1))
    (hlam : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * runLam a b (j + 1) ^ (2 * p0))
    (hδ : Cx.cs.delta j = deltaRun A0 p0 a b j)
    (hηYδ : deltaRun A0 p0 a b (j + 1) ≤ ηY)
    (hunit : ‖hv‖ = 1) (hηY : 0 < ηY)
    (hAct : ∀ C : H.Comp (j + 1), C.1 ∉ H.rem (j + 1) →
      (∃ t ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ), parentSiteCube Cx t ∈ C.1) →
      ∃ (A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1)))
        (o : OutT N R (H.localHistory M K (j + 1) C) (j + 1))
        (x : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A),
        ChiDomAt Cx.geo Cx.cs H (j + 1) C o x ∧ outField N o = ψk)
    (hR2Y : ∀ s ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ),
      parentSiteCube Cx s ∈ ((H.step (j + 1)).Z)ᶜ → |∑ i, parentPsi Cx ψk s i ^ 2 - 1| < ηY)
    (hR1Y : ∀ s s', IsInterfacePair (Cx.genW ((H.step (j + 1)).Z)ᶜ) s s' →
      parentSiteCube Cx s ∈ ((H.step (j + 1)).Z)ᶜ → parentSiteCube Cx s' ∈ ((H.step (j + 1)).Z)ᶜ →
      rn (fun i => parentPsi Cx ψk s i - parentPsi Cx ψk s' i) < ηY) :
    InPsiTilde (Cx.genW ((H.step (j + 1)).Z)ᶜ) (sfBgMassAt S.L (j + 1) (nr (j + 1)))
      (max (3 * S.d * S.L * Cx.cs.delta j) ηY)
      (parentPsi Cx ψk) (fun i => hv i) := by
  have hm := hmass_of_early (S := S) (j := j) hreg hg hk hA0 hl0 hlam hηYδ
  rw [← hδ] at hm
  have hν : 0 ≤ sfBgMassAt S.L (j + 1) (nr (j + 1)) := by
    obtain ⟨δ, hδp, -, he⟩ := hreg.nu_eq (j + 1)
    unfold sfBgMassAt
    refine physMass_nonneg _ _ ?_
    rw [he]
    have := hreg.hν
    positivity
  exact inPsiTilde_genW_of_factors H Cx ψk hv _ ηY hν hunit hηY hm hAct hR2Y hR1Y

end Assembly

end Parent

end Balaban.LargeField
