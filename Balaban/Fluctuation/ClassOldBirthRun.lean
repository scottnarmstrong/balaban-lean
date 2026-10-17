/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldBirthFluct
public import Balaban.Fluctuation.LocalClassBirth
public import Balaban.Inhabited.DAPhysicalCutoff
public import Balaban.LargeField.Analytic.Constants
public import Balaban.LargeField.R.CancelIdentity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The run-specific hypotheses of the birth-domain old-cover expansion

`classOldDec_expansion_cover_birth_consts_fluct` takes the lower bound `β_k ≥ M L^{(d-2)k}`, the
amplitude `‖cc‖ ≤ β_k^{-1/2}`, the cutoff `c_ψ = A₁ (log β_k)^p`, the flow bound and mass relation,
the background hypotheses at the two masses, and positivity of the amplitude product.  Here they
are tied to the objects of the run:

* `β_k = betaK d L k β₀` (or the running coupling of `RunningHyp`) gives the lower bound;
* the amplitude is `cc = β_k^{-1/2}` and the cutoff is `pLog A₁ p β_k`;
* the mass `μ` is the rescaled mass `ν_K L^{-2K}` of the running flow, `ν = ν_j L^{-2j}`; the flow
  bound is the hypothesis of `rg_flow_infty` with `c₈ = 4C/β`;
* `BgHyp` at `ν` and at `μ` follows from the margin `ν L^{2(k+1)} (1 + r) ≤ 1`;
* positivity of the amplitude product is proved.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Flow Finset

/-! ### (a) The coupling lower bound -/

theorem betaK_rpow_eq {d : ℕ} (hd : 2 ≤ d) (L k : ℕ) :
    (L : ℝ) ^ (((d : ℝ) - 2) * k) = (L : ℝ) ^ (k * (d - 2)) := by
  have : ((d : ℝ) - 2) * k = ((k * (d - 2) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hd]; ring
  rw [this, Real.rpow_natCast]

/-- **(a)** `β_k = β₀ L^{k(d-2)} ≥ M L^{(d-2)k}` for `M ≤ β₀`. -/
theorem betaK_lower {d : ℕ} (hd : 2 ≤ d) (L k : ℕ) {β₀ M : ℝ} (hM : M ≤ β₀) :
    M * (L : ℝ) ^ (((d : ℝ) - 2) * k) ≤ Balaban.LargeField.ActionConv.betaK d L k β₀ := by
  rw [betaK_rpow_eq hd]
  unfold Balaban.LargeField.ActionConv.betaK
  exact mul_le_mul_of_nonneg_right hM (by positivity)

/-- **(a), running coupling**: `β_k = β L^{k(d-2)} γ_k`, `|log γ_k| ≤ ε` gives
`β_k ≥ (β e^{-ε}) L^{(d-2)k}`. -/
theorem betaRun_lower {d L : ℕ} {β ν a ε : ℝ} {betaRun nuRun : ℕ → ℝ}
    (H : Balaban.LargeField.RunningHyp d L β ν a ε betaRun nuRun) (k : ℕ) :
    β * Real.exp (-ε) * (L : ℝ) ^ (((d : ℝ) - 2) * k) ≤ betaRun k := by
  obtain ⟨γ, hγ, hlog, hb⟩ := H.beta_eq k
  rw [hb, betaK_rpow_eq H.hd]
  have h1 : Real.exp (-ε) ≤ γ := by
    have : -ε ≤ Real.log γ := by linarith [neg_abs_le (Real.log γ)]
    calc Real.exp (-ε) ≤ Real.exp (Real.log γ) := Real.exp_le_exp.2 this
      _ = γ := Real.exp_log hγ
  have hL : (0 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := by positivity
  have := H.hβ
  calc β * Real.exp (-ε) * (L : ℝ) ^ (k * (d - 2)) = β * (L : ℝ) ^ (k * (d - 2)) * Real.exp (-ε) := by
        ring
    _ ≤ β * (L : ℝ) ^ (k * (d - 2)) * γ := mul_le_mul_of_nonneg_left h1 (by positivity)

theorem one_lt_of_lower {d : ℕ} (hd : 2 ≤ d) {L k : ℕ} (hL : 1 ≤ (L : ℝ)) {M βk : ℝ} (hM : 1 < M)
    (h : M * (L : ℝ) ^ (((d : ℝ) - 2) * k) ≤ βk) : 1 < βk := by
  have : 1 ≤ (L : ℝ) ^ (((d : ℝ) - 2) * k) := by
    apply Real.one_le_rpow hL
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  nlinarith

/-! ### (b) The amplitude and the cutoff -/

theorem norm_amp {βk : ℝ} (h : 0 < βk) :
    ‖(((βk ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)‖ = βk ^ (-(1 / 2 : ℝ)) := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg h.le _)]

theorem covSupConstC_pos {d L N : ℕ} [NeZero N] [NeZero L] (hd : 0 < d) (hL : 3 ≤ L) {a : ℝ}
    (ha : 0 < a) (κ : ℝ) : 0 < covSupConstC d L N a κ := by
  have hB := ballConst_pos (d := d) (L := L) hd hL
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hT := covTConst_nonneg d L a (xAgmonRate d L) κ
  have h1 : 0 < covC1Const d L a (xAgmonRate d L) κ := by
    unfold covC1Const
    have := Real.exp_pos (xAgmonRate d L * (2 * d))
    positivity
  unfold covSupConstC covSqrtEntryConstC
  have := Real.sqrt_pos.2 ha
  have := Real.exp_pos (xAgmonRate d L * d / L)
  positivity


/-! ### (c) The flow: mass relation and the background hypotheses -/

/-- The mass relation of the birth domain from the running mass sequence:
`ν = ν_j L^{-2j}`, `μ = ν_K L^{-2K}` give `μ = ν ∏_{n ∈ [j,K)} (1 + ξ₃)/(1 + ξ₂)`. -/
theorem mass_relation_of_nuSeq {L : ℕ} [NeZero L] {ξ : ℕ → Fin 3 → ℂ} {ν₀ ν μ : ℝ} {j K : ℕ}
    (hjK : j ≤ K)
    (hνj : (ν : ℂ) * ((L : ℝ) : ℂ) ^ (2 * j) = nuSeq (L : ℝ) ξ (ν₀ : ℂ) j)
    (hμK : (μ : ℂ) * ((L : ℝ) : ℂ) ^ (2 * K) = nuSeq (L : ℝ) ξ (ν₀ : ℂ) K) :
    (μ : ℂ) = ν * ∏ n ∈ Ico j K, ((1 + ξ n 2) / (1 + ξ n 1)) := by
  have hL : ((L : ℝ) : ℂ) ≠ 0 := by
    have : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    exact_mod_cast this
  rw [nuSeq_eq] at hνj hμK
  have e1 : (ν : ℂ) = ν₀ * deltaSeq ξ j :=
    mul_right_cancel₀ (pow_ne_zero (2 * j) hL) (by rw [hνj]; ring)
  have e2 : (μ : ℂ) = ν₀ * deltaSeq ξ K :=
    mul_right_cancel₀ (pow_ne_zero (2 * K) hL) (by rw [hμK]; ring)
  rw [e2, e1, deltaSeq_eq_mul_prod_Ico hjK]
  ring

/-- The mass `μ` is within the factor `1 ± r` of `ν` when the cumulated factor is. -/
theorem mu_bounds_of_flow {ξ : ℕ → Fin 3 → ℂ} {q c₈ r ν μ : ℝ} {j K : ℕ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q) (hξ : ∀ n, ‖ξ n‖ ≤ c₈ / 4 * q ^ (n + 1)) (hν0 : 0 ≤ ν)
    (hμ : (μ : ℂ) = ν * ∏ n ∈ Ico j K, ((1 + ξ n 2) / (1 + ξ n 1)))
    (hτr : Real.exp (3 * (c₈ / 4 * (q ^ (j + 1) / (1 - q)))) - 1 < r) :
    ν * (1 - r) ≤ μ ∧ μ ≤ ν * (1 + r) := by
  have h := norm_ratio_prod_sub_one_le_geom hq0 hq1 hc hs hξ j K
  have hd : ‖(μ : ℂ) - ν‖ ≤ ν * r := by
    have : (μ : ℂ) - ν = ν * (∏ n ∈ Ico j K, ((1 + ξ n 2) / (1 + ξ n 1)) - 1) := by
      rw [hμ]; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg hν0]
    exact mul_le_mul_of_nonneg_left (h.trans hτr.le) hν0
  have : ‖(μ : ℂ) - ν‖ = |μ - ν| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [this, abs_le] at hd
  constructor <;> nlinarith [hd.1, hd.2]

theorem compWeight_admissible {L : ℕ} (hL : 3 ≤ L) {a₁ : ℝ} (h1 : 9 / 16 ≤ a₁) (h2 : a₁ ≤ 2)
    (K : ℕ) : IsAdmissibleWeights K (compWeight L a₁) := by
  intro j hj _
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hx : ((L : ℝ) ^ 2)⁻¹ ≤ 1 / 9 := by
    rw [inv_eq_one_div]; apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have hx0 : 0 < ((L : ℝ) ^ 2)⁻¹ := by positivity
  have hLj : (L : ℝ) ^ 2 ≤ ((L : ℝ) ^ j) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    calc (L : ℝ) = (L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (L : ℝ) ^ j := pow_le_pow_right₀ (by linarith) hj
  have hy : (((L : ℝ) ^ j) ^ 2)⁻¹ ≤ ((L : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) hLj
  have hy0 : 0 < (((L : ℝ) ^ j) ^ 2)⁻¹ := by positivity
  unfold compWeight
  set x := ((L : ℝ) ^ 2)⁻¹
  set y := (((L : ℝ) ^ j) ^ 2)⁻¹
  have hden : 0 < 1 - y := by linarith
  constructor
  · rw [le_div_iff₀ hden]; nlinarith
  · rw [div_le_iff₀ hden]; nlinarith

theorem bgHyp_of_mass {d L k : ℕ} {ϱ : ℝ} {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hϱ : bgR0 d L ≤ ϱ) (hw : IsAdmissibleWeights k a) (hν : 0 ≤ ν)
    (hm : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) : BgHyp d L k ϱ a ν :=
  ⟨hd, hL, hϱ, hw, hν, hm⟩

/-! ### The composed theorem -/

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X : Set (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- **The birth-domain old-cover expansion for the run.**  `β_k = betaK d L k β₀` with `M ≤ β₀`;
the amplitude is `cc = β_k^{-1/2}` and the cutoff `c_ψ = pLog A₁ p β_k`; the masses are
`ν = ν_j L^{-2j}` and `μ = ν_K L^{-2K}` of the running flow `ξ`, whose bound is the hypothesis of
`rg_flow_infty` with `c₈ = 4 C_f/β`; `BgHyp` at `ν` and `μ` follows from the margin
`ν L^{2(k+1)} (1 + r) ≤ 1`; positivity of the amplitude product is proved. -/
theorem classOldDec_expansion_cover_birth_run [NeZero N] {P : Consts} {μ : ℝ}
    {α α₀ c₃ cfl A cδ : ℝ}
    {u A₁ βk M : ℝ} {p : ℕ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀)
    {j : ℕ} {y : CTorus d L N₁ m₁ (k + 1)}
    (hgs : X ⊆ ↑((C.Tm.gs j X).Ω 1) ∧ ∀ i, j < i → (C.Tm.gs j X).Ω i = ∅)
    (hAn : AnalyticOnNhd ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => C.Tm.E j y X p.1 p.2)
      {p | (xiFieldDom (compWeight L a₁) μ (epsSeq L α α₀) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
        (C.Tm.gs j X) p.1 p.2})
    (hBd : ∀ Ψ h, (xiFieldDom (compWeight L a₁) μ (epsSeq L α α₀) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      (C.Tm.gs j X) Ψ h → ‖C.Tm.E j y X Ψ h‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X))
    {β : ℝ} (hβ : 0 < β) (hE₀ : 0 ≤ P.E₀) (hN : L ^ C.m₀ ∣ N₁) (hjk : j ≤ k)
    (hXp : IsPolyDom C.m₀ j X)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) {cc : ℂ} {cψ : ℝ}
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    {K : ℕ} {ξ : ℕ → Fin 3 → ℂ} {q r Cf β₀ ν₀ : ℝ}
    (hϱ : bgR0 d L ≤ ϱ) (hν0 : 0 ≤ ν) (hjK : j ≤ K) (ha₁ : 9 / 16 ≤ a₁) (ha₂ : a₁ ≤ 2)
    (hmargin : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (1 + r) ≤ 1)
    (heps : 0 < eps)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hCf : 0 ≤ Cf) (hβs : 6 * Cf * q ≤ β * (1 - q))
    (hξ : ∀ n, ‖ξ n‖ ≤ (4 * Cf / β) / 4 * q ^ (n + 1))
    (hνj : (ν : ℂ) * ((L : ℝ) : ℂ) ^ (2 * j) = nuSeq (L : ℝ) ξ (ν₀ : ℂ) j)
    (hμK : (μ : ℂ) * ((L : ℝ) : ℂ) ^ (2 * K) = nuSeq (L : ℝ) ξ (ν₀ : ℂ) K)
    (hτr : Real.exp (3 * ((4 * Cf / β) / 4 * (q ^ (j + 1) / (1 - q)))) - 1 < r) (hr : r ≤ 1 / 16)
    (hα₀ : 0 ≤ α₀) (hα0 : 0 ≤ α) (hBG : 0 ≤ BG) (hBG₂ : 0 ≤ BG₂) (hcδ : 0 ≤ cδ)
    (hLge : 3 ≤ L) (hd3 : 3 ≤ d) (hp1 : 1 ≤ p) (hu : 0 < u) (hu2 : u < 1 / 2)
    (hA₁ : 0 < A₁) (hM : 1 < M) (hMβ : M ≤ β₀)
    (hβkdef : βk = Balaban.LargeField.ActionConv.betaK d L k β₀)
    (hccdef : cc = ((βk ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (hcψdef : cψ = Balaban.Inhabited.pLog A₁ p βk)
    (hαu : α ≤ ((d : ℝ) - 2) * (1 / 2 - u))
    (hsize : 2 * Real.sqrt N * covSupConstC d L N (compWeight L a₁ k) κ * A₁ * ((p : ℝ) / u) ^ p ≤
      cδ * α₀ * M ^ (1 / 2 - u))
    (hδ₁def : δ₁ = 2 * (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))))
    (hδ₃def : δ₃ = N * composedCloseBound d L N m₁ BG κ (xiC1 d * eps) r₀)
    (hδfldef : δfl = N * (5 * (cK2' d L N (famConst d L BG₂ κ) * δ₁) + δ₁))
    (hc₃def : c₃ = N * (xiC1 d * (L : ℝ) ^ (-α)) * composedCloseBound d L N m₁ BG κ 1 r₀)
    (hcfldef : cfl = N * (5 * cK2' d L N (famConst d L BG₂ κ) + 1) * cδ)
    (hepsK : eps ≤ epsSeq L α α₀ (k + 1)) (hLα : 16 * scaledC0 d ^ 4 ≤ (L : ℝ) ^ α)
    (hcc : 16 * scaledC0 d ^ 2 * xiK2 d L N * (c₃ + cfl) ≤ 1)
    (hAdef : A = α₀ * epsTail 0)
    (hAK : ((N : ℝ) + 1) * cK2 d L N * A ≤ 4)
    (hrK : (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * r ≤ 1)
    (hsmA : (4 * d + 6) * ((2 * d + 1) * A) ≤ 1) (hc1A : 4 * (xiC1 d * A) ≤ bgC1 d L N)
    (hKA : bgK1 d L N * (xiC1 d * A) + 3 * r ≤ deltaStar d L N)
    (hζA : 8 * A * r ≤ deltaStar d L N) :
    ∃ 𝒦X : Set (CTorus d L N₁ m₁ (k + 1)),
      ∀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1)),
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp C.m₀ j 𝒦X →
        ∀ (hB : BgSetting N Gp Gk (C.Tm.gs j X) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f),
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
          RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
        (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
          ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
          flComp hB hF (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
            (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
          ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
            Gp C.m₀ (X1 Gp C.m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
        (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
          ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
          agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) →
          Ev Y u = Ev Y u') ∧
        (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
          ‖Ev Y u‖ ≤ (β⁻¹ * P.E₀) *
            Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov Gp C.m₀ Y)) ∧
        (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  have hd2 : 2 ≤ d := by omega
  have hd : 0 < d := by omega
  have hL1 : (1 : ℝ) ≤ L := by
    have : (3 : ℝ) ≤ L := by exact_mod_cast hLge
    linarith
  have hβk : M * (L : ℝ) ^ (((d : ℝ) - 2) * k) ≤ βk := by
    rw [hβkdef]; exact betaK_lower hd2 L k hMβ
  have hβ1 : 1 < βk := one_lt_of_lower hd2 hL1 hM hβk
  have hβ0 : 0 < βk := by linarith
  have hw := compWeight_admissible (L := L) hLge ha₁ ha₂ (k + 1)
  have ha : 0 < compWeight L a₁ k := by
    have := (hw k hk (by omega)).1
    linarith
  have hr0 : 0 ≤ r := by
    have hq : 0 < 1 - q := by linarith
    have : 0 ≤ 3 * ((4 * Cf / β) / 4 * (q ^ (j + 1) / (1 - q))) := by positivity
    have := Real.one_le_exp this
    linarith
  have hc : 0 ≤ 4 * Cf / β := by positivity
  have hs : 4 * Cf / β * q ≤ 1 - q := by
    have : 4 * Cf / β * q = 4 * Cf * q / β := by ring
    rw [this, div_le_iff₀ hβ]
    have := mul_nonneg hCf hq0
    linarith
  have hμ := mass_relation_of_nuSeq (ξ := ξ) (ν₀ := ν₀) hjK hνj hμK
  have hb := mu_bounds_of_flow hq0 hq1 hc hs hξ hν0 hμ hτr
  have hLpos : (0 : ℝ) ≤ ((L : ℝ) ^ (k + 1)) ^ 2 := by positivity
  have hmH : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1 := by
    have := mul_nonneg (mul_nonneg hν0 hLpos) hr0
    linarith
  have hμ0 : 0 ≤ μ := by
    have := mul_nonneg hν0 (by linarith : 0 ≤ 1 - r)
    linarith [hb.1]
  have hmH' : μ * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hb.2 hLpos
    linarith
  have H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν := bgHyp_of_mass hd3 hLge hϱ hw hν0 hmH
  have H' : BgHyp d L (k + 1) ϱ (compWeight L a₁) μ := bgHyp_of_mass hd3 hLge hϱ hw hμ0 hmH'
  have hcc0 : ‖cc‖ = βk ^ (-(1 / 2 : ℝ)) := by rw [hccdef]; exact norm_amp hβ0
  have hcψ0 : 0 < cψ := by rw [hcψdef]; exact Balaban.Inhabited.pLog_pos hA₁ p hβ1
  have hcψ : 0 ≤ cψ := hcψ0.le
  have hCpos := covSupConstC_pos (N := N) (d := d) (L := L) hd hLge ha κ
  have hNpos : 0 < Real.sqrt N := by
    apply Real.sqrt_pos.2
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hW : 0 < Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) := by
    rw [hcc0]
    have := Real.rpow_pos_of_pos hβ0 (-(1 / 2 : ℝ))
    positivity
  exact classOldDec_expansion_cover_birth_consts_fluct (cc := cc) (cψ := cψ) (c₈ := 4 * Cf / β)
    (K := K) (ξ := ξ) (q := q) (r := r) C hm hgs hAn hBd hβ hE₀ hN hjk hXp hk hG hG' hcψ hMX hdm hα
    hsm hconn hrow hκ₀ hκdec hκ h1 hlog hκP H H' heps hq0 hq1 hc hs hξ hμ hτr hr hα₀ hα0 hBG hBG₂
    hd hcδ hLge ha hp1 hu hu2 hA₁.le hM hβk (hcc0.le) (by rw [hcψdef]; rfl) hαu hd2 hsize hW hδ₁def hδ₃def
    hδfldef hc₃def hcfldef hepsK hLα hcc hAdef hAK hrK hsmA hc1A hKA hζA

end Balaban.Fluctuation
