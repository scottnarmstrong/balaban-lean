/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.DenominatorSqueeze
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The denominator of `R` (Lemma III.8.2, P7 (3.3)-(3.5))

`denominator_eq`: for `ψ_k ∈ Ψ̃(X ∖ Z₀; δ)` with the smallness `K₆ δ + 5 ρ ≤ etaDen` (`ρ = C₆ β_k^{-1/2} p₀(β_k)` the radius
of the cutoff `χ_{Z₀}`) and `C₆ p₀(β_k) ≥ 1`,
`∫ du ρ_{k,0}(Z)(u) = exp(-β_k A*_k(Z; ψ⁰_k) - (N/2) log β_k |Z₀| + Ẽ₀)` where `Ẽ₀ = tildeE0` is the logarithm of the ratio
and `|Ẽ₀| ≤ C_Ẽ D₀^d` with the explicit constant `cTildeE N d D = |N log 2 - (N/2) log N - 1| + (N/2) |log (2π/g_D)|`,
`g_D = gaussConst d D = ½ γ_LF c_D` the Gaussian constant of a box of diameter `≤ D` (independent of `k`).

Proof: the expansion about the critical point `ψ⁰_k` (`DenominatorSqueeze`: the linear term vanishes since `ψ⁰_k` is an
interior minimizer, and the Hessian lies in `[g_D L^{k(d-2)}, 2 L^{k(d-2)}]` on the polydisc of the cutoff), the Gaussian
upper bound, and the lower bound on the integral over the cube of side `2 (Nβ)^{-1/2}` (inside the cutoff since
`C₆ p₀ ≥ 1`), where the integrand is `≥ e^{-βA* - |Z₀|}`.  The cubic remainder is not used: the two-sided Hessian
bound on the whole polydisc suffices for the `O(D₀^d)` bound.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background MeasureTheory Filter Topology

section Den2

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)
  [NeZero N]

variable {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)

local notation "Zb" => boxFinset (L := L) (N₀ := N₀) (k := k) b0 w

/-- The explicit constant `C_Ẽ` of Lemma III.8.2: `|N log 2 - (N/2) log N - 1| + (N/2) |log (2π / g_D)|`. -/
noncomputable def cTildeE (N d D : ℕ) : ℝ :=
  |(N : ℝ) * Real.log 2 - (N : ℝ) / 2 * Real.log N - 1| + (N : ℝ) / 2 * |Real.log (2 * Real.pi / gaussConst d D)|

/-- **`Ẽ₀^{(k)}(Z₀; ψ⁰_k)`** of Lemma III.8.2, defined by the identity of the lemma:
`log ∫ρ_{k,0}(Z) + β_k A*_k(Z; ψ⁰_k) + (N/2) log β_k |Z₀|`. -/
noncomputable def tildeE0 {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (β p0 : ℝ) : ℝ :=
  Real.log (∫ u, rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u) +
    β * effActionNorm G a (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk) +
    (N : ℝ) / 2 * Real.log β * ((Zb).card : ℝ)

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **Lemma III.8.2 (the denominator)**: `∫ dψ_k↾Z₀ ρ_{k,0}(Z) = exp(-β_k A*_k(Z; ψ⁰_k, φ⁰_k) - (N/2) log β_k |Z₀| + Ẽ₀)`
with the integral positive and `|Ẽ₀| ≤ C_Ẽ D₀^d`, `C_Ẽ = cTildeE N d D₀` depending on `N, d, D₀, γ₀` (through `g_D`) only.
Hypotheses: `0 < β_k`, `C₆ p₀(β_k) ≥ 1` and the smallness `K₆ δ + 5 C₆ β_k^{-1/2} p₀(β_k) ≤ etaDen` (the geometric
step: `k ≤ k₀`, `β_k` large); they are satisfiable (`denominator_params_exist`). -/
theorem denominator_eq {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) {β p0 : ℝ} (hβ : 0 < β)
    (hp0 : 1 ≤ cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) * p0)
    (hrad : psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ +
      5 * zeroRadius (cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)) β p0 ≤ etaDen d L N D) :
    ∫ u, rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u =
      Real.exp (-β * effActionNorm G a (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk)
        - (N : ℝ) / 2 * Real.log β * ((Zb).card : ℝ) +
        tildeE0 G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0) ∧
    0 < ∫ u, rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u ∧
    |tildeE0 G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0| ≤ cTildeE N d D * (D : ℝ) ^ d := by
  set K := psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H with hKdef
  have hK : 0 < K := psiZeroK_pos N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H
  have hd0 : 0 < d := by omega
  have hD1 : 1 ≤ D := (hw1 ⟨0, hd0⟩).trans (hwD _)
  have hC6 : 0 < cSix d D K := by
    unfold cSix
    have : (0 : ℝ) < d := by exact_mod_cast hd0
    have : (0 : ℝ) < D := by exact_mod_cast hD1
    positivity
  have hp0pos : 0 < p0 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hC6.le h]
  set ρ := zeroRadius (cSix d D K) β p0 with hρdef
  have hρpos : 0 < ρ := by
    unfold zeroRadius at hρdef
    rw [hρdef]; positivity
  have hρsq : 1 / β ≤ ρ ^ 2 := by
    have h1 : (β ^ (-(1 / 2 : ℝ))) ^ 2 = β⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hβ.le]
      norm_num
      exact Real.rpow_neg_one β
    have h2 : ρ ^ 2 = (cSix d D K * p0) ^ 2 * β⁻¹ := by
      rw [hρdef]; unfold zeroRadius
      calc (cSix d D K * β ^ (-(1 / 2 : ℝ)) * p0) ^ 2 = (cSix d D K * p0) ^ 2 * (β ^ (-(1 / 2 : ℝ))) ^ 2 := by ring
        _ = _ := by rw [h1]
    rw [h2, one_div]
    have : 1 ≤ (cSix d D K * p0) ^ 2 := by nlinarith
    exact le_mul_of_one_le_left (by positivity) this
  obtain ⟨hcrit, hF, hsq⟩ := effAction_squeeze G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hρpos hrad
  obtain ⟨hsol, -⟩ := psiZero_spec N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk
  set ψ0 := psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk with hψ0
  set u0 := restrictSupp Zb ψ0 with hu0
  have hmerge0 : mergeField Zb ψk u0 = ψ0 :=
    mergeField_restrict (fun z hz => hsol.2.1 z (fun h => hz (mem_boxFinset.2 h)))
  have hLk : (0 : ℝ) < (L : ℝ) ^ (k * (d - 2)) := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  set Lk := (L : ℝ) ^ (k * (d - 2)) with hLkdef
  set A : SuppSpace Zb N → ℝ := fun y => effActionNorm G a (mergeField Zb ψk (u0 + y)) with hA
  have hAeff : ∀ y, A y = effOn G a Zb ψk (u0 + y) / Lk := fun y => rfl
  have hA0 : effActionNorm G a ψ0 = effOn G a Zb ψk u0 / Lk := by
    show effAction G a ψ0 / Lk = effAction G a (mergeField Zb ψk u0) / Lk
    rw [hmerge0]
  -- the translation and the identification of the integrand
  have hcut : ∀ y : SuppSpace Zb N, ZeroCutoff ψ0 ρ (u0 + y) ↔ y ∈ siteBall (Z := ↥Zb) (N := N) ρ := by
    intro y
    unfold ZeroCutoff siteBall
    refine forall_congr' fun z => ?_
    have : (fun i => (u0 + y) (z, i) - ψ0 z i) = fun i => y (z, i) := by
      funext i; simp [hu0, restrictSupp]
    rw [this]
    unfold rn
    exact Real.sqrt_lt' hρpos
  have hI : ∫ u, rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u =
      ∫ y, (siteBall (Z := ↥Zb) (N := N) ρ).indicator (fun y => Real.exp (-β * A y)) y := by
    rw [← integral_add_left_eq_self (μ := volume) (fun u => rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u) u0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ siteBall (Z := ↥Zb) (N := N) ρ
    · rw [Set.indicator_of_mem hy]
      exact rhoZeroWith_of_cutoff G a Zb ψ0 ψk _ β p0 (u0 + y) ((hcut y).2 hy)
    · rw [Set.indicator_of_notMem hy]
      exact rhoZeroWith_eq_zero G a Zb ψ0 ψk _ β p0 (u0 + y) (fun h => hy ((hcut y).1 h))
  have hg := gaussConst_pos d D hd0
  have hlowA : ∀ y ∈ siteBall (Z := ↥Zb) (N := N) ρ,
      effActionNorm G a ψ0 + gaussConst d D / 2 * ‖y‖ ^ 2 ≤ A y := by
    intro y hy
    have h := (hsq y hy).1
    rw [hAeff, hA0]
    have e : effOn G a Zb ψk u0 / Lk + gaussConst d D / 2 * ‖y‖ ^ 2 =
        (effOn G a Zb ψk u0 + hessConst d L k D / 2 * ‖y‖ ^ 2) / Lk := by
      unfold hessConst; field_simp; rw [hLkdef]; ring
    rw [e]
    exact div_le_div_of_nonneg_right h hLk.le
  have hupA : ∀ y ∈ siteBall (Z := ↥Zb) (N := N) ρ, A y ≤ effActionNorm G a ψ0 + ‖y‖ ^ 2 := by
    intro y hy
    have h := (hsq y hy).2
    rw [hAeff, hA0]
    have e : effOn G a Zb ψk u0 / Lk + ‖y‖ ^ 2 = (effOn G a Zb ψk u0 + Lk * ‖y‖ ^ 2) / Lk := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right h hLk.le
  have hcontA : ContinuousOn A (siteBall (Z := ↥Zb) (N := N) ρ) := by
    intro y hy
    have h1 : ContinuousAt (fun y => effOn G a Zb ψk (u0 + y)) y :=
      (hF y hy).continuousAt.comp (f := fun y => u0 + y) (by fun_prop)
    exact (h1.div_const Lk).continuousWithinAt
  obtain ⟨hlo, hhi⟩ := zeroDensity_bounds (A := A) (A0 := effActionNorm G a ψ0) hβ hg hρsq hcontA hlowA hupA
  rw [← hI] at hlo hhi
  set I := ∫ u, rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u with hIdef
  set m : ℝ := ((Zb).card : ℝ) with hmdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set A0 := effActionNorm G a ψ0 with hA0def
  simp only [Fintype.card_coe] at hlo hhi
  have hJlo_pos : 0 < Real.exp (-β * A0) * (2 / Real.sqrt (N * β)) ^ ((Zb).card * N) * Real.exp (-m) := by
    positivity
  have hIpos : 0 < I := lt_of_lt_of_le hJlo_pos hlo
  have hE : tildeE0 G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 =
      Real.log I + β * A0 + (N : ℝ) / 2 * Real.log β * m := rfl
  have hlogN : Real.log (N * β) = Real.log N + Real.log β := Real.log_mul hNpos.ne' hβ.ne'
  have hlsq : Real.log (Real.sqrt (N * β)) = (Real.log N + Real.log β) / 2 := by
    rw [Real.log_sqrt (by positivity), hlogN]
  have hl2 : Real.log (2 / Real.sqrt (N * β)) = Real.log 2 - (Real.log N + Real.log β) / 2 := by
    rw [Real.log_div (by norm_num) (by positivity), hlsq]
  have hlogJlo : Real.log (Real.exp (-β * A0) * (2 / Real.sqrt (N * β)) ^ ((Zb).card * N) * Real.exp (-m)) =
      -β * A0 + (m * N) * (Real.log 2 - (Real.log N + Real.log β) / 2) - m := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_exp, Real.log_pow, hl2]
    push_cast
    rw [hmdef]; ring
  have hlower : m * (N * Real.log 2 - N / 2 * Real.log N - 1) ≤
      tildeE0 G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 := by
    have h1 := Real.log_le_log hJlo_pos hlo
    rw [hlogJlo] at h1
    rw [hE]
    linarith only [h1]
  set g := gaussConst d D with hgdef
  have hq : 0 < Real.pi / (β * g / 2) := by positivity
  have hJhi_pos : 0 < Real.exp (-β * A0) * (Real.pi / (β * g / 2)) ^ (m * N / 2) := by positivity
  have hlq : Real.log (Real.pi / (β * g / 2)) = Real.log (2 * Real.pi / g) - Real.log β := by
    have : Real.pi / (β * g / 2) = (2 * Real.pi / g) / β := by field_simp
    rw [this, Real.log_div (by positivity) hβ.ne']
  have hlogJhi : Real.log (Real.exp (-β * A0) * (Real.pi / (β * g / 2)) ^ (m * N / 2)) =
      -β * A0 + (m * N / 2) * (Real.log (2 * Real.pi / g) - Real.log β) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_rpow hq, hlq]
  have hupper : tildeE0 G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 ≤
      m * (N / 2 * Real.log (2 * Real.pi / g)) := by
    have h1 := Real.log_le_log hIpos hhi
    rw [hlogJhi] at h1
    rw [hE]
    linarith only [h1]
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hmD : m ≤ (D : ℝ) ^ d := card_boxFinset_le b0 w hwD
  have hCnn : 0 ≤ cTildeE N d D := by unfold cTildeE; positivity
  refine ⟨?_, hIpos, ?_⟩
  · rw [hE]
    have : -β * A0 - (N : ℝ) / 2 * Real.log β * m + (Real.log I + β * A0 + (N : ℝ) / 2 * Real.log β * m) =
        Real.log I := by ring
    rw [this, Real.exp_log hIpos]
  · have hcl : |(N : ℝ) * Real.log 2 - (N : ℝ) / 2 * Real.log N - 1| ≤ cTildeE N d D := by
      unfold cTildeE; have : 0 ≤ (N : ℝ) / 2 * |Real.log (2 * Real.pi / g)| := by positivity
      linarith
    have hcu : (N : ℝ) / 2 * |Real.log (2 * Real.pi / g)| ≤ cTildeE N d D := by
      unfold cTildeE; have := abs_nonneg ((N : ℝ) * Real.log 2 - (N : ℝ) / 2 * Real.log N - 1)
      linarith
    have hl1 := neg_abs_le ((N : ℝ) * Real.log 2 - (N : ℝ) / 2 * Real.log N - 1)
    have hu1 := le_abs_self (Real.log (2 * Real.pi / g))
    have hmc : m * cTildeE N d D ≤ cTildeE N d D * (D : ℝ) ^ d := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left hmD hCnn
    rw [abs_le]
    constructor
    · have : m * (-(cTildeE N d D)) ≤ m * ((N : ℝ) * Real.log 2 - (N : ℝ) / 2 * Real.log N - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hm0
      linarith
    · have h2 : N / 2 * Real.log (2 * Real.pi / g) ≤ cTildeE N d D := by
        have : (N : ℝ) / 2 * Real.log (2 * Real.pi / g) ≤ (N : ℝ) / 2 * |Real.log (2 * Real.pi / g)| :=
          mul_le_mul_of_nonneg_left hu1 (by positivity)
        linarith
      have := mul_le_mul_of_nonneg_left h2 hm0
      linarith

theorem zeroRadius_inv_sq {C6 p0 x : ℝ} (hx : 0 < x) (hp : C6 * p0 = 1) :
    zeroRadius C6 (x ^ 2) p0 = 1 / x := by
  unfold zeroRadius
  have h1 : (x ^ 2) ^ (-(1 / 2 : ℝ)) = x⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
    exact Real.rpow_neg_one x
  rw [h1]
  calc C6 * x⁻¹ * p0 = (C6 * p0) * x⁻¹ := by ring
    _ = 1 / x := by rw [hp]; ring

/-- The parameters of `denominator_eq` exist: for every `K₆ δ` below the tube radius there are `β, p₀` with
`C₆ p₀ = 1` and `K₆ δ + 5 ρ ≤ etaDen`. -/
theorem denominator_params_exist {d L N D : ℕ} [NeZero L] {C6 K δ : ℝ} (hC : 0 < C6)
    (hKδ : K * δ < etaDen d L N D) :
    ∃ β p0 : ℝ, 0 < β ∧ 1 ≤ C6 * p0 ∧ K * δ + 5 * zeroRadius C6 β p0 ≤ etaDen d L N D := by
  set η := etaDen d L N D - K * δ with hη
  have hηpos : 0 < η := by linarith
  refine ⟨(5 / η) ^ 2, 1 / C6, by positivity, by field_simp; exact le_rfl, ?_⟩
  rw [zeroRadius_inv_sq (by positivity) (by field_simp)]
  have : 5 * (1 / (5 / η)) = η := by field_simp
  linarith

theorem etaDen_pos {d L N D : ℕ} [NeZero L] (hd : 0 < d) : 0 < etaDen d L N D :=
  lt_min (Balaban.Localization.bgC1_pos' hd) (etaHess_pos d L N D hd)

end Den2

end Balaban.LargeField
