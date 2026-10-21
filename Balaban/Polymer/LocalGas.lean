/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.SteinerGas
public import Balaban.Polymer.MayerSupport
public import Balaban.Polymer.Holomorphic
public import Balaban.Analysis.ParamIntegralAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The gas of a local family analytic in a source

The gas layer of the last integral in a general form (A6-3; P7 (4.9)–(4.14), P4 (6.6)). `B` is a
finite set of sites with a connected graph `H` of degree at most `Δ`, `μ = ⨂_b μ_b` a product of
probability measures on configurations `Φ ∈ ∏_b Ω_b` carried by a compact set, and `g : I → ℂ` a
source, each index `i` of which belongs to a site `σ i`. A family `W_Y(Φ, g)` of local terms on the
sets `Y` of sites has the local form on the open set `U` of sources (`LocalGasForm`) if

* (W1) `W_Y` depends on `Φ` only through `Φ|_Y`;
* (W2) `W_Y` depends on `g` only through `g` at the indices of the sites of `Y`;
* (W3) `W_Y = 0` unless `Y` is nonempty and connected;
* (W4) `g ↦ W_Y(Φ, g)` is analytic on `U` and `(g, Φ) ↦ W_Y(Φ, g)` is continuous on `U × ∏_b Ω_b`;
* (W5) `Σ_{Y ∋ b} ‖W_Y(Φ, g)‖ e^{a|Y|} ≤ ε` for every site `b`, configuration `Φ` and `g ∈ U`.

The local terms of the gas are the explicit `P_g(Y) = PY` of the Mayer activities
`K_g(X) = ∫ Σ_C ∏_{t ∈ C} (e^{W_t} - 1) dμ` (`localGasK`, `localGasP`). Under the numerical conditions of
`steiner_gas` with `κ₀ + κ₁ ≤ a`, `ε ≤ log 2` and `ε · 4 e^{-κ₀} ≤ 1/4`:

* `integral_exp_eq_gasP`: `∫ exp(Σ_Y W_Y(Φ, g)) dμ(Φ) = exp(Σ_Y P_g(Y))` for `g ∈ U`;
* `gasP_kp_bound`: `Σ_{Y ∋ b} ‖P_g(Y)‖ e^{κ'|Y|_St} ≤ 64 e ε e^{-2κ₀}` for `g ∈ U`;
* `gasP_eq_zero_of_not_isAnimal`: `P_g(Y) = 0` unless `Y` is connected;
* `gasP_congr_g`: `P_g(Y)` depends on `g` only at the indices of the sites of `Y`;
* `analyticOnNhd_gasP`: `g ↦ P_g(Y)` is analytic on `U` (the Mayer activities are integrals over a
  compact carrier of jointly continuous functions analytic in `g`,
  `Analysis.analyticAt_integral_of_continuousOn`, and the cluster sum is analytic under the
  Kotecký–Preiss condition, `pe_PY_analyticOnNhd`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory Filter Topology

namespace Balaban.Polymer

variable {B : Type*} [Fintype B] [DecidableEq B] {H : SimpleGraph B}
  {Ω : B → Type*} [∀ b, TopologicalSpace (Ω b)] [∀ b, MeasurableSpace (Ω b)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {I : Type*} [Fintype I]

/-- **The local form of a family of terms with a parameter** on the sets of sites (clauses (W1),
(W3)–(W5) of the module docstring), on an open set `U` of a complex normed space of parameters, with
the decay rate `a` and the bound `ε`. -/
structure LocalGasFormE (H : SimpleGraph B) (U : Set E) (a ε : ℝ)
    (W : Finset B → (∀ b, Ω b) → E → ℂ) : Prop where
  /-- (W1) -/
  local_w : ∀ Y e, DepOn Y (fun Φ => W Y Φ e)
  /-- (W3) -/
  support : ∀ Y, ¬ IsAnimal H Y → ∀ Φ e, W Y Φ e = 0
  /-- (W4) analyticity in the parameter -/
  analytic : ∀ Y Φ, AnalyticOnNhd ℂ (W Y Φ) U
  /-- (W4) joint continuity -/
  cont : ∀ Y, ContinuousOn (fun q : E × (∀ b, Ω b) => W Y q.2 q.1) (U ×ˢ Set.univ)
  /-- (W5) -/
  bound : ∀ Φ, ∀ e ∈ U, ∀ b : B,
    ∑ Y ∈ Finset.univ.filter (fun Y : Finset B => b ∈ Y), ‖W Y Φ e‖ * Real.exp (a * (Y.card : ℝ)) ≤ ε

/-- **The local form of a family of terms** on the sets of sites (clauses (W1)–(W5) of the module
docstring), on the open set `U` of sources, with the decay rate `a` and the bound `ε`: the local
form with the sources as parameters (`LocalGasFormE`) and the locality (W2) in the source. -/
structure LocalGasForm (H : SimpleGraph B) (σ : I → B) (U : Set (I → ℂ)) (a ε : ℝ)
    (W : Finset B → (∀ b, Ω b) → (I → ℂ) → ℂ) : Prop extends LocalGasFormE H U a ε W where
  /-- (W2) -/
  local_g : ∀ Y Φ g g', (∀ i, σ i ∈ Y → g i = g' i) → W Y Φ g = W Y Φ g'

omit [∀ b, MeasurableSpace (Ω b)] in
/-- **Rule 10: the zero family has the local form** (every graph, set of sources, rate and bound
`ε ≥ 0`). -/
theorem localGasForm_zero (H : SimpleGraph B) (σ : I → B) (U : Set (I → ℂ)) (a : ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) : LocalGasForm (Ω := Ω) H σ U a ε (fun _ _ _ => 0) where
  local_w _ _ _ _ _ := rfl
  support _ _ _ _ := rfl
  analytic _ _ := analyticOnNhd_const
  cont _ := continuousOn_const
  bound _ _ _ _ := by simpa using hε
  local_g _ _ _ _ _ := rfl

variable (μ : ∀ b, Measure (Ω b))

/-- The local terms at the source `g`, on the nonempty sets of sites. -/
def localGasTerm (W : Finset B → (∀ b, Ω b) → E → ℂ) (g : E) :
    NePoly B → (∀ b, Ω b) → ℂ :=
  fun X Φ => W X.1 Φ g

/-- **The Mayer activities of the gas** at the source `g`:
`K_g(X) = ∫ Σ_{C connected, ∪C = X} ∏_{t ∈ C} (e^{W_t(Φ, g)} - 1) dμ(Φ)`. -/
def localGasK (W : Finset B → (∀ b, Ω b) → E → ℂ) (g : E) : NePoly B → ℂ :=
  mayerK μ (fun X : NePoly B => X.1) (localGasTerm W g)

/-- **The local terms of the gas** at the source `g`: `P_g(Y)`, the clusters of activities
`localGasK` with union `Y`. -/
def localGasP (W : Finset B → (∀ b, Ω b) → E → ℂ) (g : E) (Y : Finset B) : ℂ :=
  PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val (localGasK μ W g) Y

variable {μ}

section Basic

variable {U : Set E} {a ε : ℝ} {W : Finset B → (∀ b, Ω b) → E → ℂ}

omit [∀ b, MeasurableSpace (Ω b)] in
/-- The sum over all sets of sites is the sum over the nonempty ones (`W_∅ = 0`). -/
theorem sum_finset_eq_sum_nePoly (hW : LocalGasFormE H U a ε W) (Φ : ∀ b, Ω b) (g : E) :
    ∑ Y : Finset B, W Y Φ g = ∑ X : NePoly B, localGasTerm W g X Φ := by
  have h0 : W ∅ Φ g = 0 := hW.support ∅ (fun h => by simpa using h.1) Φ g
  have h1 : ∑ X : NePoly B, localGasTerm W g X Φ =
      ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => Y.Nonempty), W Y Φ g :=
    (Finset.sum_subtype _ (fun Y => by simp) (fun Y => W Y Φ g)).symm
  rw [h1, Finset.sum_filter_of_ne]
  intro Y _ hY
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  exact hY (hne ▸ h0)

omit [∀ b, MeasurableSpace (Ω b)] in
/-- The per-term bound from (W5): `‖W_X(Φ, g)‖ ≤ ε e^{-a |X|_St}` for `g ∈ U`. -/
theorem norm_gasTerm_le (hconn : H.Connected) (hW : LocalGasFormE H U a ε W) {g : E}
    (hg : g ∈ U) (X : NePoly B) (Φ : ∀ b, Ω b) :
    ‖localGasTerm W g X Φ‖ ≤ ε * Real.exp (-a * stSizeG H X.1) := by
  have hε : 0 ≤ ε := by
    have := hconn.nonempty
    obtain ⟨b⟩ := this
    exact le_trans (Finset.sum_nonneg fun Y _ => by positivity) (hW.bound Φ g hg b)
  unfold localGasTerm
  by_cases hX : IsAnimal H X.1
  · obtain ⟨b, hb⟩ := X.2
    have hsingle := (Finset.single_le_sum (f := fun Y : Finset B =>
      ‖W Y Φ g‖ * Real.exp (a * (Y.card : ℝ))) (fun Y _ => by positivity)
      (Finset.mem_filter.2 ⟨Finset.mem_univ X.1, hb⟩)).trans (hW.bound Φ g hg b)
    rw [stSizeG_eq_card hX]
    have hpos : 0 < Real.exp (a * (X.1.card : ℝ)) := Real.exp_pos _
    rw [show -a * (X.1.card : ℝ) = -(a * (X.1.card : ℝ)) by ring, Real.exp_neg]
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    exact hsingle
  · rw [hW.support X.1 hX Φ g, norm_zero]
    positivity

end Basic

section Gas

variable [∀ b, BorelSpace (Ω b)] [∀ b, SecondCountableTopology (Ω b)]
  [∀ b, IsProbabilityMeasure (μ b)]
  {U : Set E} {a ε : ℝ} {W : Finset B → (∀ b, Ω b) → E → ℂ}

omit [∀ b, IsProbabilityMeasure (μ b)] in
theorem measurable_gasTerm (hW : LocalGasFormE H U a ε W) {g : E} (hg : g ∈ U)
    (X : NePoly B) : Measurable (localGasTerm W g X) := by
  have hc : Continuous fun Φ : ∀ b, Ω b => W X.1 Φ g := by
    rw [← continuousOn_univ]
    exact (hW.cont X.1).comp (f := fun Φ : ∀ b, Ω b => (g, Φ))
      (Continuous.continuousOn (by fun_prop)) (fun Φ _ => ⟨hg, Set.mem_univ _⟩)
  exact hc.measurable

/-- **The gas of the local family**: for `g ∈ U`, `∫ exp(Σ_Y W_Y(Φ, g)) dμ = exp(Σ_Y P_g(Y))`, with
`Σ_{Y ∋ b} ‖P_g(Y)‖ e^{κ'|Y|_St} ≤ 64 e ε e^{-2κ₀}` (`steiner_gas` with `H₀ = ε`). -/
theorem integral_exp_eq_gasP (hconn : H.Connected) {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ)
    {κ0 κ1 κ' : ℝ} (hq : (Δ : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2)
    (hκ0 : Real.log 4 + 1 ≤ κ0) (hκ' : 0 ≤ κ') (hκ : κ' + κ0 + 1 ≤ κ1 - 3 / 2)
    (ha : κ0 + κ1 ≤ a) (hεlog : ε ≤ Real.log 2) (hεK : ε * (4 * Real.exp (-κ0)) ≤ 1 / 4)
    (hW : LocalGasFormE H U a ε W) {g : E} (hg : g ∈ U) :
    ∫ Φ, Complex.exp (∑ Y : Finset B, W Y Φ g) ∂(Measure.pi μ) =
        Complex.exp (∑ Y : Finset B, localGasP μ W g Y) ∧
      ∀ b : B, ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ‖localGasP μ W g Y‖ * Real.exp (κ' * stSizeG H Y) ≤
          64 * Real.exp 1 * ε * Real.exp (-(2 * κ0)) := by
  have hε : 0 ≤ ε := by
    obtain ⟨b⟩ := hconn.nonempty
    have hΦ : Nonempty (∀ b, Ω b) := ⟨fun b => (nonempty_of_isProbabilityMeasure (μ b)).some⟩
    exact le_trans (Finset.sum_nonneg fun Y _ => by positivity) (hW.bound hΦ.some g hg b)
  have hbd : ∀ (X : NePoly B) Φ, ‖localGasTerm W g X Φ‖ ≤
      ε * Real.exp (-(κ0 + κ1) * stSizeG H X.1) := by
    intro X Φ
    refine (norm_gasTerm_le hconn hW hg X Φ).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 ?_) hε)
    have := stSizeG_nonneg (H := H) X.1
    nlinarith
  have hmain := steiner_gas μ hconn hdeg hq hκ0 hκ' hκ hε hεlog hεK (localGasTerm W g)
    (fun X Φ Φ' hΦ => hW.local_w X.1 g Φ Φ' hΦ) (measurable_gasTerm hW hg) hbd
  refine ⟨?_, hmain.2.1⟩
  have e : (fun Φ : ∀ b, Ω b => Complex.exp (∑ Y : Finset B, W Y Φ g)) =
      fun Φ => Complex.exp (∑ X : NePoly B, localGasTerm W g X Φ) := by
    funext Φ; rw [sum_finset_eq_sum_nePoly hW Φ g]
  rw [e, hmain.1, hmain.2.2]
  rfl

omit [∀ b, BorelSpace (Ω b)] [∀ b, SecondCountableTopology (Ω b)]
  [∀ b, IsProbabilityMeasure (μ b)] in
/-- **The local terms vanish off connected sets** (W3). -/
theorem gasP_eq_zero_of_not_isAnimal (hW : LocalGasFormE H U a ε W) (g : E)
    (Y : Finset B) (hY : ¬ IsAnimal H Y) : localGasP μ W g Y = 0 :=
  PY_shareBlock_eq_zero_of_not_isAnimal H _ (fun Z hZ =>
    mayerK_eq_zero_of_not_isAnimal H μ (fun X : NePoly B => X.1) (localGasTerm W g)
      (fun X hX Φ => hW.support X.1 hX Φ g) Z hZ) Y hY

omit [DecidableEq B] [∀ b, TopologicalSpace (Ω b)] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [∀ b, BorelSpace (Ω b)] [∀ b, SecondCountableTopology (Ω b)]
  [∀ b, IsProbabilityMeasure (μ b)] in
/-- **The gas of vanishing terms is trivial**: if every term vanishes at the parameter `e`, every
local term `P(Y)` vanishes there. -/
theorem localGasP_eq_zero_of_terms_zero {e : E} (h : ∀ X Φ, W X Φ e = 0) (Y : Finset B) :
    localGasP μ W e Y = 0 := by
  have hK : localGasK μ W e = 0 := by
    funext Z
    unfold localGasK mayerK
    refine (integral_congr_ae (g := fun _ => (0 : ℂ)) (Filter.Eventually.of_forall fun Φ => ?_)).trans
      (integral_zero _ _)
    unfold mayerAct polyAct
    refine Finset.sum_eq_zero fun C hC => ?_
    obtain ⟨t, ht⟩ := (mem_Cfam.1 hC).1.1
    refine Finset.prod_eq_zero ht ?_
    show Complex.exp (W t.1 Φ e) - 1 = 0
    rw [h, Complex.exp_zero, sub_self]
  unfold localGasP PY
  rw [hK]
  refine (tsum_congr fun n => ?_).trans tsum_zero
  unfold Pterm
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun X _ => ?_)
  exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ 0) rfl)

omit [DecidableEq B] [∀ b, TopologicalSpace (Ω b)] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [∀ b, BorelSpace (Ω b)] [∀ b, SecondCountableTopology (Ω b)]
  [∀ b, IsProbabilityMeasure (μ b)] in
/-- **Locality of the local terms in the parameter**: if the terms supported in `Y` agree at the
parameters `e`, `e'`, so do the local terms `P(Y)`. -/
theorem gasP_congr_param (Y : Finset B) {e e' : E}
    (hee : ∀ X : Finset B, X ⊆ Y → ∀ Φ, W X Φ e = W X Φ e') :
    localGasP μ W e Y = localGasP μ W e' Y := by
  unfold localGasP
  refine PY_congr _ _ Y fun Z hZ => ?_
  unfold localGasK mayerK mayerAct polyAct
  refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
  refine Finset.sum_congr rfl fun C hC => Finset.prod_congr rfl fun X hX => ?_
  show Complex.exp (W X.1 Φ e) - 1 = Complex.exp (W X.1 Φ e') - 1
  rw [hee X.1 ((sub_of_mem_Cfam hC hX).trans hZ) Φ]

omit [∀ b, BorelSpace (Ω b)] [∀ b, SecondCountableTopology (Ω b)]
  [∀ b, IsProbabilityMeasure (μ b)] in
/-- **Locality of the local terms in the source** (W2): `P_g(Y)` depends on `g` only at the
indices of the sites of `Y`. -/
theorem gasP_congr_g {σ : I → B} {U : Set (I → ℂ)} {W : Finset B → (∀ b, Ω b) → (I → ℂ) → ℂ}
    (hW : LocalGasForm H σ U a ε W) (Y : Finset B) {g g' : I → ℂ}
    (hgg : ∀ i, σ i ∈ Y → g i = g' i) : localGasP μ W g Y = localGasP μ W g' Y :=
  gasP_congr_param Y fun X hX Φ => hW.local_g X Φ g g' fun i hi => hgg i (hX hi)

/-- **The Mayer activities are analytic in the parameter** on `U`, when `μ` is carried by a compact
set (`Analysis.analyticAt_integral_of_continuousOn`). -/
theorem analyticOnNhd_gasK [FiniteDimensional ℂ E] (hU : IsOpen U) {Kc : Set (∀ b, Ω b)} (hKc : IsCompact Kc)
    (hKm : MeasurableSet Kc) (hμK : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Kc) (hW : LocalGasFormE H U a ε W)
    (Z : NePoly B) : AnalyticOnNhd ℂ (fun g => localGasK μ W g Z) U := by
  intro g0 hg0
  unfold localGasK mayerK
  refine Balaban.Analysis.analyticAt_integral_of_continuousOn hKc hKm hμK
    (hU.mem_nhds hg0) (fun Φ _ => ?_) ?_
  · unfold mayerAct polyAct
    refine Finset.analyticOnNhd_fun_sum _ fun C _ => Finset.analyticOnNhd_fun_prod _ fun X _ => ?_
    exact ((hW.analytic X.1 Φ).cexp).sub analyticOnNhd_const
  · unfold mayerAct polyAct
    refine continuousOn_finsetSum _ fun C _ => continuousOn_finsetProd _ fun X _ => ?_
    have h := (hW.cont X.1).mono (Set.prod_mono (subset_refl U) (Set.subset_univ Kc))
    exact (Complex.continuous_exp.comp_continuousOn h).sub continuousOn_const

/-- **The local terms are analytic in the parameter** on `U` (`pe_PY_analyticOnNhd`, with the
Kotecký–Preiss data of `steinerGen_kp`). -/
theorem analyticOnNhd_gasP [FiniteDimensional ℂ E] (hconn : H.Connected) {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ)
    {κ0 κ1 κ' : ℝ} (hq : (Δ : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2)
    (hκ0 : Real.log 4 + 1 ≤ κ0) (hκ' : 0 ≤ κ') (hκ : κ' + κ0 + 1 ≤ κ1 - 3 / 2)
    (ha : κ0 + κ1 ≤ a) (hεlog : ε ≤ Real.log 2) (hεK : ε * (4 * Real.exp (-κ0)) ≤ 1 / 4)
    (hU : IsOpen U) {Kc : Set (∀ b, Ω b)} (hKc : IsCompact Kc) (hKm : MeasurableSet Kc)
    (hμK : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Kc) (hW : LocalGasFormE H U a ε W) (Y : Finset B) :
    AnalyticOnNhd ℂ (fun g => localGasP μ W g Y) U := by
  intro g0 hg0
  have hε : 0 ≤ ε := by
    obtain ⟨b⟩ := hconn.nonempty
    have hΦ : Nonempty (∀ b, Ω b) := ⟨fun b => (nonempty_of_isProbabilityMeasure (μ b)).some⟩
    exact le_trans (Finset.sum_nonneg fun Y _ => by positivity) (hW.bound hΦ.some g0 hg0 b)
  have hκ0nn : 0 ≤ κ0 := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hdp : ∀ g ∈ U, _ := fun g hg =>
    expm1_dom_prod μ (sup := fun X : NePoly B => X.1) (d := stSizeG H) (κ0 := κ0) (κ1 := κ1)
      (measurable_gasTerm hW hg) hε hεlog hκ0nn (by linarith) (fun Y => stSizeG_nonneg Y)
      (fun X Φ => (norm_gasTerm_le hconn hW hg X Φ).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (by have := stSizeG_nonneg (H := H) X.1; nlinarith)) hε))
  have hkp : ∀ g ∈ U, _ := fun g hg =>
    steinerGen_kp μ hconn hdeg hq hκ0 hκ' hκ hε hεK
      (fun X Φ => Complex.exp (localGasTerm W g X Φ) - 1)
      (fun X => (Complex.measurable_exp.comp (measurable_gasTerm hW hg X)).sub_const 1)
      (hdp g hg).1 (hdp g hg).2
  have h := pe_PY_analyticOnNhd (shareBlock (Subtype.val : NePoly B → Finset B))
    (Subtype.val : NePoly B → Finset B) (hkp g0 hg0).2 hU (fun Z g => localGasK μ W g Z)
    (fun Z => analyticOnNhd_gasK hU hKc hKm hμK hW Z) (fun Z g hg => (hkp g hg).1 Z) Y
  exact h g0 hg0

end Gas

end Balaban.Polymer
