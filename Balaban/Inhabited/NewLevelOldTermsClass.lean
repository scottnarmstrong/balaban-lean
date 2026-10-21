/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelSystem
public import Balaban.Fluctuation.OldTermClassDomain
public import Balaban.Fluctuation.LocalClassDensityIrrelChainX
public import Balaban.Fluctuation.OldTermBirthDomain
public import Balaban.Fluctuation.ClassOldCoverBirth
public import Balaban.Fluctuation.LocalClassDensityIrrelSuppLen

/-!
# The fields of the inherited terms from the class (route R-LOC, L5; ruling R13)

The final theorem of the new level on the local generating sets (`localFamily_castLocal_of`) takes
the analyticity `hEan`, the bound `hEbd` and the spin covariance `hEr` of the old terms `Eτ` on the
charts of their generating sets.  When the old terms are the irrelevant terms of the class composed
on the generating sets of the class (`OldTermsAreIrrel`), these follow from the clauses of the class
on its term domain, once the chart lies in the term domain (the inclusion of the class domain,
ruling R2) and the bound is given on the term domain (the open input A4-1b (ii), P1 (3.128)).

* `rotRaw_mem_xiCRaw`: the charts `XiCRaw` are invariant under the real rotations;
* `irrelTorus_fields_of_class`: analyticity and spin covariance of the irrelevant term of a label
  on any rotation-invariant set of its term domain (with `Ψ(y)·Ψ(y)` in the slit plane);
* `irrelTorus_bound_on` (`irrelTorus_bound_of_class`): the bound of the irrelevant term on a set,
  in the size of a cover `XL ⊇ X` with `d(XL) ≤ d(X) + c`, from its bound on the set (on the term
  domain);
* `NewLevelSystem.oldTerm_chart_dom_of_labels`, `oldTerm_charts_an_rot_of_labels`: the chart of the
  step in the term domain, and the analyticity and spin covariance of the old terms on it;
* `NewLevelSystem.oldTerm_charts_of_labels`: for a system whose old terms are the irrelevant terms of
  a class on the birth-mass domain (the data of `OldTermsAreIrrel`, ruling R13), the analyticity,
  the bound and the spin covariance of `β⁻¹ Eτ` on the chart `Ξ^c_j(Gj τ; b, e)` of the step, in
  the size of the
  polymer `O.XL τ = X ∪ □(y)`, from the class clauses and the bound of the class on its term domain
  (the open input A4-1b (ii), P1 (3.128)), through the inclusion of the chart in the term domain
  (`xiCRaw_mem_birthXiDom`);
* `NewLevelSystem.oldTerm_charts_of_labels_composed`: the same with the bound of the class at the
  data composed into its generating sets from the charts of level `k + 1` (`composedChart`, P1
  (3.128) at the data of the step), giving the bound of `β⁻¹ Eτ` on the composed chart.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Matrix

section Rot

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The charts `Ξ^c_n(𝔹; σ, ε)` are invariant under the real rotations** (any level `n`). -/
theorem rotRaw_mem_xiCRaw {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν σ ε : ℝ}
    {n : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {r : RawData d L (N₁ * L ^ m₁) K N}
    (hr : r ∈ XiCRaw G a ν n σ ε) : rotRaw (cmat Q) r ∈ XiCRaw G a ν n σ ε := by
  obtain ⟨D, hD, rfl⟩ := hr
  exact ⟨D.rot (cmat Q), xiCData_rot hQ hD, (rawOf_rot _ D).symm⟩

end Rot

section Fields

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **Analyticity and spin covariance of the irrelevant term of a label of the class** on any set
`𝒮` of raw data in its term domain `Dom.dom j (Tm.gs j X)` with `Ψ(y)·Ψ(y)` in the slit plane
(`irrelTorus_analyticOnNhd`, `irrelTorus_rot`), scaled by `β⁻¹`. -/
theorem irrelTorus_fields_of_class {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    {Tm : Terms d L N₁ m₁ (k + 1) N ϱ} (hcl : SFTermClauses P Dom Tm) (m₀ : ℕ) (i₀ i₁ : Fin N)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) {y : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))} (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X)
    {𝒮 : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    (hdom : ∀ r ∈ 𝒮, Dom.dom j (Tm.gs j X) r.1 r.2 ∧ dot (r.1 y) (r.1 y) ∈ Complex.slitPlane)
    (β : ℝ) :
    AnalyticOnNhd ℂ (fun r : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        (β : ℂ)⁻¹ * irrelTorus m₀ Tm i₀ i₁ j y X r.1 r.2) 𝒮 ∧
      ∀ (Q : Matrix (Fin N) (Fin N) ℝ), Qᵀ * Q = 1 → ∀ r ∈ 𝒮, rotRaw (cmat Q) r ∈ 𝒮 →
        (β : ℂ)⁻¹ * irrelTorus m₀ Tm i₀ i₁ j y X (rotRaw (cmat Q) r).1 (rotRaw (cmat Q) r).2 =
          (β : ℂ)⁻¹ * irrelTorus m₀ Tm i₀ i₁ j y X r.1 r.2 := by
  refine ⟨fun r hr => ?_, fun Q hQ r hr hr' => ?_⟩
  · exact analyticAt_const.mul
      (irrelTorus_analyticOnNhd hcl m₀ i₀ i₁ hj1 hjk hX hy r (hdom r hr))
  · congr 1
    exact irrelTorus_rot hcl m₀ i₀ i₁ hj1 hjk hX hy
      ⟨(isRealOrth_ofReal hQ).1, (isRealOrth_ofReal hQ).2⟩ (hdom r hr).1 (hdom _ hr').1

/-- **The bound of the irrelevant term of a label on a set of raw data** (the core of
`irrelTorus_bound_of_class`), in the size of a cover `XL` with `d(XL) ≤ d(X) + c`: from the bound
`B e^{-(κ_dec - 1) d(X)}` on the set `𝒮`, `‖β⁻¹ ℰ_irrel‖ ≤ |β|⁻¹ B e^{(κ_dec - 1) c}
e^{-(κ_dec - 1) d(XL)}` on `𝒮`. -/
theorem irrelTorus_bound_on {m₀ : ℕ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ} {i₀ i₁ : Fin N} {j : ℕ}
    {y : CTorus d L N₁ m₁ (k + 1)} {X XL : Set (CTorus d L N₁ m₁ (k + 1))} {B κdec c : ℝ}
    (hB0 : 0 ≤ B) (hκ : 1 ≤ κdec)
    (hle : treeLenCovOne m₀ j XL ≤ treeLenCovOne m₀ j X + c)
    {𝒮 : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    (hB : ∀ r ∈ 𝒮, ‖irrelTorus m₀ Tm i₀ i₁ j y X r.1 r.2‖ ≤
      B * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    (β : ℝ) :
    ∀ r ∈ 𝒮, ‖(β : ℂ)⁻¹ * irrelTorus m₀ Tm i₀ i₁ j y X r.1 r.2‖ ≤
      |β|⁻¹ * B * Real.exp ((κdec - 1) * c) * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j XL) := by
  intro r hr
  have h := irrel_bound_transfer hB0 hκ hle (hB r hr)
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  have hb : 0 ≤ |β|⁻¹ := inv_nonneg.2 (abs_nonneg β)
  calc |β|⁻¹ * ‖irrelTorus m₀ Tm i₀ i₁ j y X r.1 r.2‖
      ≤ |β|⁻¹ * (B * Real.exp ((κdec - 1) * c) * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j XL)) :=
        mul_le_mul_of_nonneg_left h hb
    _ = _ := by ring

/-- **The bound of the irrelevant term of a label on a set of its term domain**, in the size of a
cover `XL` with `d(XL) ≤ d(X) + c`: from the bound `B e^{-(κ_dec - 1) d(X)}` on the term domain,
`‖β⁻¹ ℰ_irrel‖ ≤ |β|⁻¹ B e^{(κ_dec - 1) c} e^{-(κ_dec - 1) d(XL)}` (the instance of
`irrelTorus_bound_on`). -/
theorem irrelTorus_bound_of_class {m₀ : ℕ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
    {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ} {i₀ i₁ : Fin N} {j : ℕ}
    {y : CTorus d L N₁ m₁ (k + 1)} {X XL : Set (CTorus d L N₁ m₁ (k + 1))} {B κdec c : ℝ}
    (hB0 : 0 ≤ B) (hκ : 1 ≤ κdec)
    (hle : treeLenCovOne m₀ j XL ≤ treeLenCovOne m₀ j X + c)
    (hB : ∀ Ψ h : Fld d L N₁ m₁ (k + 1) N, Dom.dom j (Tm.gs j X) Ψ h →
      dot (Ψ y) (Ψ y) ∈ Complex.slitPlane →
      ‖irrelTorus m₀ Tm i₀ i₁ j y X Ψ h‖ ≤ B * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {𝒮 : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    (hdom : ∀ r ∈ 𝒮, Dom.dom j (Tm.gs j X) r.1 r.2 ∧ dot (r.1 y) (r.1 y) ∈ Complex.slitPlane)
    (β : ℝ) :
    ∀ r ∈ 𝒮, ‖(β : ℂ)⁻¹ * irrelTorus m₀ Tm i₀ i₁ j y X r.1 r.2‖ ≤
      |β|⁻¹ * B * Real.exp ((κdec - 1) * c) * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j XL) :=
  irrelTorus_bound_on hB0 hκ hle (fun r hr => hB r.1 r.2 (hdom r hr).1 (hdom r hr).2) β

end Fields

section Charts

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The charts of the old terms of a system of the class lie in the term domain** (rulings R2,
R6, R13): for old terms that are the irrelevant terms of the class composed on its generating sets
(`hE`, `hlab`), under the hypotheses of `xiCRaw_mem_birthXiDom` at every level `j ≤ k`, the chart
`Ξ^c_j(Gj τ; b, e)` of the step lies in the birth-mass domain of `Tm.gs j X` and `Ψ(y)·Ψ(y)` lies in
the slit plane there. -/
theorem NewLevelSystem.oldTerm_chart_dom_of_labels [NeZero N] {S : StepSetting d L N₁ m₁ k N ϱ}
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ}
    {Jr : S.JointRep t pp} (NS : NewLevelSystem S C z Jr)
    {P : Consts} (Rg : Regime L) (a : ℕ → ℝ) (hPm : P.m₀ = C.m₀)
    (hcl : SFTermClauses P (birthXiDom P Rg a N₁) C.Tm)
    (hA : aIdeal L (k + 1) (a (k + 1)) = compWeight L S.a₁)
    (H : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
    (H' : ∀ j, 1 ≤ j → j ≤ k → BgHyp d L (k + 1) ϱ (compWeight L S.a₁) (physMass L j (Rg.ν j)))
    {b e τm r : ℝ} (hb : 1 ≤ b) (he : 0 < e)
    (hμ : ∀ j, 1 ≤ j → j ≤ k → ∃ tm, physMass L j (Rg.ν j) = S.ν * (1 + tm) ∧ |tm| ≤ τm)
    (hτr : τm < r) (hr : r ≤ 1 / 16)
    (hDL : ∀ j, 1 ≤ j → j ≤ k →
      (2 * (b ^ 2 * e) + 2 * ((N : ℝ) + 1) * (cK2 d L N * (b ^ 2 * e) ^ 2)) *
        (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τm) ≤ P.eps d L j)
    (hsmε : ∀ j, 1 ≤ j → j ≤ k → (4 * d + 6) * ((2 * d + 1) * P.eps d L j) ≤ 1)
    (hc1ε : ∀ j, 1 ≤ j → j ≤ k → 4 * (xiC1 d * P.eps d L j) ≤ bgC1 d L N)
    (hKε : ∀ j, 1 ≤ j → j ≤ k → bgK1 d L N * (xiC1 d * P.eps d L j) + 3 * r ≤ deltaStar d L N)
    (hζε : ∀ j, 1 ≤ j → j ≤ k → 8 * P.eps d L j * r ≤ deltaStar d L N)
    (y : NS.O.ι → CTorus d L N₁ m₁ (k + 1)) (X : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hlab : ∀ τ, NS.O.Gj τ = C.Tm.gs (NS.O.jL τ) (X τ) ∧ 1 ≤ NS.O.jL τ ∧ NS.O.jL τ ≤ k ∧
      Aligned (L ^ NS.O.jL τ) (y τ) ∧ IsPolyDom C.m₀ (NS.O.jL τ) (X τ) ∧ y τ ∈ X τ ∧
      NS.O.XL τ = X τ ∪ box (cbase (cellSide L C.m₀ m₁ (NS.O.jL τ)) (y τ) -
        natT fun _ => L / 2 * cellSide L C.m₀ m₁ (NS.O.jL τ))
          (L * cellSide L C.m₀ m₁ (NS.O.jL τ))) :
    ∀ τ, ∀ q : RawData d L (N₁ * L ^ m₁) (k + 1) N,
      q ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b e →
      (birthXiDom P Rg a N₁).dom (NS.O.jL τ) (C.Tm.gs (NS.O.jL τ) (X τ)) q.1 q.2 ∧
        dot (q.1 (y τ)) (q.1 (y τ)) ∈ Complex.slitPlane := by
  intro τ q hq
  obtain ⟨hGj, hj1, hjk, -, hX, hy, -⟩ := hlab τ
  rw [hGj] at hq
  have hXP : IsPolyDom P.m₀ (NS.O.jL τ) (X τ) := hPm ▸ hX
  obtain ⟨tm, hmeq, htm⟩ := hμ _ hj1 hjk
  have h := xiCRaw_mem_birthXiDom P Rg a hA H (H' _ hj1 hjk)
    (gs_top_layer_empty_of_clauses hcl hj1 (hjk.trans (Nat.le_succ k)) hXP) hb he hmeq htm hτr
    hr (hDL _ hj1 hjk) (hsmε _ hj1 hjk) (hc1ε _ hj1 hjk) (hKε _ hj1 hjk) (hζε _ hj1 hjk) q hq
  refine ⟨h.1, h.2 _ ?_⟩
  exact (mem_dataSites (G := C.Tm.gs (NS.O.jL τ) (X τ))).2
    (Or.inl ((hcl.gs_spec _ hj1 (hjk.trans (Nat.le_succ k)) _ hXP).1 hy))

/-- **Analyticity and spin covariance of the old terms of a system of the class on the step's
charts** (from `oldTerm_chart_dom_of_labels` and `irrelTorus_fields_of_class`). -/
theorem NewLevelSystem.oldTerm_charts_an_rot_of_labels [NeZero N] {S : StepSetting d L N₁ m₁ k N ϱ}
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ}
    {Jr : S.JointRep t pp} (NS : NewLevelSystem S C z Jr)
    {P : Consts} (Rg : Regime L) (a : ℕ → ℝ) (hPm : P.m₀ = C.m₀)
    (hcl : SFTermClauses P (birthXiDom P Rg a N₁) C.Tm)
    (hA : aIdeal L (k + 1) (a (k + 1)) = compWeight L S.a₁)
    (H : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
    (H' : ∀ j, 1 ≤ j → j ≤ k → BgHyp d L (k + 1) ϱ (compWeight L S.a₁) (physMass L j (Rg.ν j)))
    {b e τm r : ℝ} (hb : 1 ≤ b) (he : 0 < e)
    (hμ : ∀ j, 1 ≤ j → j ≤ k → ∃ tm, physMass L j (Rg.ν j) = S.ν * (1 + tm) ∧ |tm| ≤ τm)
    (hτr : τm < r) (hr : r ≤ 1 / 16)
    (hDL : ∀ j, 1 ≤ j → j ≤ k →
      (2 * (b ^ 2 * e) + 2 * ((N : ℝ) + 1) * (cK2 d L N * (b ^ 2 * e) ^ 2)) *
        (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τm) ≤ P.eps d L j)
    (hsmε : ∀ j, 1 ≤ j → j ≤ k → (4 * d + 6) * ((2 * d + 1) * P.eps d L j) ≤ 1)
    (hc1ε : ∀ j, 1 ≤ j → j ≤ k → 4 * (xiC1 d * P.eps d L j) ≤ bgC1 d L N)
    (hKε : ∀ j, 1 ≤ j → j ≤ k → bgK1 d L N * (xiC1 d * P.eps d L j) + 3 * r ≤ deltaStar d L N)
    (hζε : ∀ j, 1 ≤ j → j ≤ k → 8 * P.eps d L j * r ≤ deltaStar d L N)
    (i₀ i₁ : Fin N) (y : NS.O.ι → CTorus d L N₁ m₁ (k + 1))
    (X : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hE : ∀ τ r, NS.O.Eτ τ r = irrelTorus C.m₀ C.Tm i₀ i₁ (NS.O.jL τ) (y τ) (X τ) r.1 r.2)
    (hlab : ∀ τ, NS.O.Gj τ = C.Tm.gs (NS.O.jL τ) (X τ) ∧ 1 ≤ NS.O.jL τ ∧ NS.O.jL τ ≤ k ∧
      Aligned (L ^ NS.O.jL τ) (y τ) ∧ IsPolyDom C.m₀ (NS.O.jL τ) (X τ) ∧ y τ ∈ X τ ∧
      NS.O.XL τ = X τ ∪ box (cbase (cellSide L C.m₀ m₁ (NS.O.jL τ)) (y τ) -
        natT fun _ => L / 2 * cellSide L C.m₀ m₁ (NS.O.jL τ))
          (L * cellSide L C.m₀ m₁ (NS.O.jL τ))) :
    (∀ τ, AnalyticOnNhd ℂ (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
        (XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b e)) ∧
      (∀ τ (Q : Matrix (Fin N) (Fin N) ℝ), Qᵀ * Q = 1 →
        ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b e,
          (S.β : ℂ)⁻¹ * NS.O.Eτ τ (rotRaw (cmat Q) r) = (S.β : ℂ)⁻¹ * NS.O.Eτ τ r) := by
  have hdom := NS.oldTerm_chart_dom_of_labels Rg a hPm hcl hA H H' hb he hμ hτr hr hDL hsmε hc1ε
    hKε hζε y X hlab
  refine ⟨fun τ => ?_, fun τ Q hQ => ?_⟩
  · obtain ⟨-, hj1, hjk, -, hX, hy, -⟩ := hlab τ
    have hf := (irrelTorus_fields_of_class hcl C.m₀ i₀ i₁ hj1 (hjk.trans (Nat.le_succ k))
      (hPm ▸ hX) hy (hdom τ) S.β).1
    exact fun r hr => by
      rw [show (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r) = fun r =>
        (S.β : ℂ)⁻¹ * irrelTorus C.m₀ C.Tm i₀ i₁ (NS.O.jL τ) (y τ) (X τ) r.1 r.2 from
        funext fun r => by rw [hE τ r]]
      exact hf r hr
  · obtain ⟨-, hj1, hjk, -, hX, hy, -⟩ := hlab τ
    intro r hr
    rw [hE τ r, hE τ]
    exact (irrelTorus_fields_of_class hcl C.m₀ i₀ i₁ hj1 (hjk.trans (Nat.le_succ k))
      (hPm ▸ hX) hy (hdom τ) S.β).2 Q hQ r hr (rotRaw_mem_xiCRaw hQ hr)

/-- **The fields of the old terms of a system of the class on the step's charts, for given labels**
(route R-LOC, L5; rulings R2, R6, R13).  Let the old term of `τ` be the irrelevant term of the class
`C` at the label `(jL τ, y τ, X τ)`, composed on the generating set of the class (`hE`, `hlab`: the
data of `OldTermsAreIrrel`), the class terms satisfy the clauses on the birth-mass domain
`birthXiDom P Rg a` (`hcl`), the class weights be the step's (`hA`), the birth mass of every level
`j ≤ k` be `ν (1 + t_j)` with `|t_j| ≤ τm < r ≤ 1/16` (`hμ`), and let the (DL-gap) and the
smallness of `ε_j` of `xiCRaw_mem_birthXiDom` hold at every level `j ≤ k`.  If the irrelevant term
of every label is bounded by `B_l(j, y, X) e^{-(κ_dec - 1) d(X)}` on its term domain (`hB`, the open
input A4-1b (ii), P1 (3.128)), then on the chart `Ξ^c_j(Gj τ; b, e)` of the step the function
`β⁻¹ Eτ` is analytic, bounded by `|β|⁻¹ B_l e^{(κ_dec - 1) c_G} e^{-(κ_dec - 1) d(O.XL τ)}` and
invariant under the real rotations. -/
theorem NewLevelSystem.oldTerm_charts_of_labels [NeZero N] {S : StepSetting d L N₁ m₁ k N ϱ}
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ}
    {Jr : S.JointRep t pp} (NS : NewLevelSystem S C z Jr)
    {P : Consts} (Rg : Regime L) (a : ℕ → ℝ) (hPm : P.m₀ = C.m₀)
    (hcl : SFTermClauses P (birthXiDom P Rg a N₁) C.Tm)
    (hA : aIdeal L (k + 1) (a (k + 1)) = compWeight L S.a₁)
    (H : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
    (H' : ∀ j, 1 ≤ j → j ≤ k → BgHyp d L (k + 1) ϱ (compWeight L S.a₁) (physMass L j (Rg.ν j)))
    {b e τm r : ℝ} (hb : 1 ≤ b) (he : 0 < e)
    (hμ : ∀ j, 1 ≤ j → j ≤ k → ∃ tm, physMass L j (Rg.ν j) = S.ν * (1 + tm) ∧ |tm| ≤ τm)
    (hτr : τm < r) (hr : r ≤ 1 / 16)
    (hDL : ∀ j, 1 ≤ j → j ≤ k →
      (2 * (b ^ 2 * e) + 2 * ((N : ℝ) + 1) * (cK2 d L N * (b ^ 2 * e) ^ 2)) *
        (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τm) ≤ P.eps d L j)
    (hsmε : ∀ j, 1 ≤ j → j ≤ k → (4 * d + 6) * ((2 * d + 1) * P.eps d L j) ≤ 1)
    (hc1ε : ∀ j, 1 ≤ j → j ≤ k → 4 * (xiC1 d * P.eps d L j) ≤ bgC1 d L N)
    (hKε : ∀ j, 1 ≤ j → j ≤ k → bgK1 d L N * (xiC1 d * P.eps d L j) + 3 * r ≤ deltaStar d L N)
    (hζε : ∀ j, 1 ≤ j → j ≤ k → 8 * P.eps d L j * r ≤ deltaStar d L N)
    {κdec : ℝ} (hκ : 1 ≤ κdec)
    (Bl : ℕ → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) → ℝ)
    (hBl : ∀ j y X, 0 ≤ Bl j y X)
    (hB : ∀ (i₀ i₁ : Fin N) (j : ℕ) (y : CTorus d L N₁ m₁ (k + 1))
      (X : Set (CTorus d L N₁ m₁ (k + 1))), 1 ≤ j → j ≤ k → IsPolyDom C.m₀ j X → y ∈ X →
      ∀ Ψ h : Fld d L N₁ m₁ (k + 1) N, (birthXiDom P Rg a N₁).dom j (C.Tm.gs j X) Ψ h →
      dot (Ψ y) (Ψ y) ∈ Complex.slitPlane →
      ‖irrelTorus C.m₀ C.Tm i₀ i₁ j y X Ψ h‖ ≤
        Bl j y X * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ j X))
    (hm : NS.O.m₀ = C.m₀) (i₀ i₁ : Fin N) (y : NS.O.ι → CTorus d L N₁ m₁ (k + 1))
    (X : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hE : ∀ τ r, NS.O.Eτ τ r = irrelTorus C.m₀ C.Tm i₀ i₁ (NS.O.jL τ) (y τ) (X τ) r.1 r.2)
    (hlab : ∀ τ, NS.O.Gj τ = C.Tm.gs (NS.O.jL τ) (X τ) ∧ 1 ≤ NS.O.jL τ ∧ NS.O.jL τ ≤ k ∧
      Aligned (L ^ NS.O.jL τ) (y τ) ∧ IsPolyDom C.m₀ (NS.O.jL τ) (X τ) ∧ y τ ∈ X τ ∧
      NS.O.XL τ = X τ ∪ box (cbase (cellSide L C.m₀ m₁ (NS.O.jL τ)) (y τ) -
        natT fun _ => L / 2 * cellSide L C.m₀ m₁ (NS.O.jL τ))
          (L * cellSide L C.m₀ m₁ (NS.O.jL τ))) :
    (∀ τ, AnalyticOnNhd ℂ (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
        (XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b e)) ∧
      (∀ τ, ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b e,
        ‖(S.β : ℂ)⁻¹ * NS.O.Eτ τ r‖ ≤
          |S.β|⁻¹ * Bl (NS.O.jL τ) (y τ) (X τ) * Real.exp ((κdec - 1) * cG d L) *
            Real.exp (-(κdec - 1) * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (NS.O.XL τ))) ∧
      (∀ τ (Q : Matrix (Fin N) (Fin N) ℝ), Qᵀ * Q = 1 →
        ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b e,
          (S.β : ℂ)⁻¹ * NS.O.Eτ τ (rotRaw (cmat Q) r) = (S.β : ℂ)⁻¹ * NS.O.Eτ τ r) := by
  have hN : L ^ C.m₀ ∣ N₁ := hm ▸ NS.OS.hN
  have hdom := NS.oldTerm_chart_dom_of_labels Rg a hPm hcl hA H H' hb he hμ hτr hr hDL hsmε hc1ε
    hKε hζε y X hlab
  obtain ⟨han, hrot⟩ := NS.oldTerm_charts_an_rot_of_labels Rg a hPm hcl hA H H' hb he hμ hτr hr
    hDL hsmε hc1ε hKε hζε i₀ i₁ y X hE hlab
  refine ⟨han, fun τ => ?_, hrot⟩
  obtain ⟨-, hj1, hjk, -, hX, hy, hXL⟩ := hlab τ
  have hle : treeLenCovOne C.m₀ (NS.O.jL τ) (NS.O.XL τ) ≤
      treeLenCovOne C.m₀ (NS.O.jL τ) (X τ) + cG d L := by
    rw [hXL]
    exact treeLenCovOne_support_le hN (hjk.trans (Nat.le_succ k)) hX hy
  intro r hr
  rw [hE τ r, hm]
  exact irrelTorus_bound_of_class (Dom := birthXiDom P Rg a N₁) (hBl _ _ _) hκ hle
    (fun Ψ h hD hs => hB i₀ i₁ _ _ _ hj1 hjk hX hy Ψ h hD hs) (hdom τ) S.β r hr

/-- **The fields of the old terms of a system of the class, with the bound on the composed
charts** (route R-LOC, L5; rulings R2, R6, R13; P1 (3.128) at the data of the step).  Under the
hypotheses of `oldTerm_charts_of_labels`, if the irrelevant term of every label is bounded by
`B_l(j, y, X) e^{-(κ_dec - 1) d(X)}` at the data composed into the generating set `Tm.gs j X` of the
class from the charts of level `k + 1` (`composedChart`, the data the step reads; the open input
A4-1b (ii) in the form of P1 (3.128)), then `β⁻¹ Eτ` is analytic and invariant under the real
rotations on the chart `Ξ^c_j(Gj τ; b, e)` of the step and bounded by
`|β|⁻¹ B_l e^{(κ_dec - 1) c_G} e^{-(κ_dec - 1) d(O.XL τ)}` on its composed chart. -/
theorem NewLevelSystem.oldTerm_charts_of_labels_composed [NeZero N] {S : StepSetting d L N₁ m₁ k N ϱ}
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ}
    {Jr : S.JointRep t pp} (NS : NewLevelSystem S C z Jr)
    {P : Consts} (Rg : Regime L) (a : ℕ → ℝ) (hPm : P.m₀ = C.m₀)
    (hcl : SFTermClauses P (birthXiDom P Rg a N₁) C.Tm)
    (hA : aIdeal L (k + 1) (a (k + 1)) = compWeight L S.a₁)
    (H : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
    (H' : ∀ j, 1 ≤ j → j ≤ k → BgHyp d L (k + 1) ϱ (compWeight L S.a₁) (physMass L j (Rg.ν j)))
    {b e τm r : ℝ} (hb : 1 ≤ b) (he : 0 < e)
    (hμ : ∀ j, 1 ≤ j → j ≤ k → ∃ tm, physMass L j (Rg.ν j) = S.ν * (1 + tm) ∧ |tm| ≤ τm)
    (hτr : τm < r) (hr : r ≤ 1 / 16)
    (hDL : ∀ j, 1 ≤ j → j ≤ k →
      (2 * (b ^ 2 * e) + 2 * ((N : ℝ) + 1) * (cK2 d L N * (b ^ 2 * e) ^ 2)) *
        (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τm) ≤ P.eps d L j)
    (hsmε : ∀ j, 1 ≤ j → j ≤ k → (4 * d + 6) * ((2 * d + 1) * P.eps d L j) ≤ 1)
    (hc1ε : ∀ j, 1 ≤ j → j ≤ k → 4 * (xiC1 d * P.eps d L j) ≤ bgC1 d L N)
    (hKε : ∀ j, 1 ≤ j → j ≤ k → bgK1 d L N * (xiC1 d * P.eps d L j) + 3 * r ≤ deltaStar d L N)
    (hζε : ∀ j, 1 ≤ j → j ≤ k → 8 * P.eps d L j * r ≤ deltaStar d L N)
    {κdec : ℝ} (hκ : 1 ≤ κdec)
    (Bl : ℕ → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) → ℝ)
    (hBl : ∀ j y X, 0 ≤ Bl j y X)
    (hB : ∀ (i₀ i₁ : Fin N) (j : ℕ) (y : CTorus d L N₁ m₁ (k + 1))
      (X : Set (CTorus d L N₁ m₁ (k + 1))), 1 ≤ j → j ≤ k → IsPolyDom C.m₀ j X → y ∈ X →
      ∀ r ∈ composedChart (C.Tm.gs j X) (compWeight L S.a₁) S.ν j b e,
      ‖irrelTorus C.m₀ C.Tm i₀ i₁ j y X r.1 r.2‖ ≤
        Bl j y X * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ j X))
    (hm : NS.O.m₀ = C.m₀)
    (i₀ i₁ : Fin N) (y : NS.O.ι → CTorus d L N₁ m₁ (k + 1))
    (X : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hE : ∀ τ r, NS.O.Eτ τ r = irrelTorus C.m₀ C.Tm i₀ i₁ (NS.O.jL τ) (y τ) (X τ) r.1 r.2)
    (hlab : ∀ τ, NS.O.Gj τ = C.Tm.gs (NS.O.jL τ) (X τ) ∧ 1 ≤ NS.O.jL τ ∧ NS.O.jL τ ≤ k ∧
      Aligned (L ^ NS.O.jL τ) (y τ) ∧ IsPolyDom C.m₀ (NS.O.jL τ) (X τ) ∧ y τ ∈ X τ ∧
      NS.O.XL τ = X τ ∪ box (cbase (cellSide L C.m₀ m₁ (NS.O.jL τ)) (y τ) -
        natT fun _ => L / 2 * cellSide L C.m₀ m₁ (NS.O.jL τ))
          (L * cellSide L C.m₀ m₁ (NS.O.jL τ))) :
    (∀ τ, AnalyticOnNhd ℂ (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
        (XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b e)) ∧
      (∀ τ, ∀ r ∈ composedChart (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b e,
        ‖(S.β : ℂ)⁻¹ * NS.O.Eτ τ r‖ ≤
          |S.β|⁻¹ * Bl (NS.O.jL τ) (y τ) (X τ) * Real.exp ((κdec - 1) * cG d L) *
            Real.exp (-(κdec - 1) * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (NS.O.XL τ))) ∧
      (∀ τ (Q : Matrix (Fin N) (Fin N) ℝ), Qᵀ * Q = 1 →
        ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b e,
          (S.β : ℂ)⁻¹ * NS.O.Eτ τ (rotRaw (cmat Q) r) = (S.β : ℂ)⁻¹ * NS.O.Eτ τ r) := by
  have hN : L ^ C.m₀ ∣ N₁ := hm ▸ NS.OS.hN
  obtain ⟨han, hrot⟩ := NS.oldTerm_charts_an_rot_of_labels Rg a hPm hcl hA H H' hb he hμ hτr hr
    hDL hsmε hc1ε hKε hζε i₀ i₁ y X hE hlab
  refine ⟨han, fun τ => ?_, hrot⟩
  obtain ⟨hGj, hj1, hjk, -, hX, hy, hXL⟩ := hlab τ
  have hle : treeLenCovOne C.m₀ (NS.O.jL τ) (NS.O.XL τ) ≤
      treeLenCovOne C.m₀ (NS.O.jL τ) (X τ) + cG d L := by
    rw [hXL]
    exact treeLenCovOne_support_le hN (hjk.trans (Nat.le_succ k)) hX hy
  intro q hq
  rw [hE τ q, hm]
  rw [hGj] at hq
  exact irrelTorus_bound_on (hBl _ _ _) hκ hle
    (fun q hq => hB i₀ i₁ _ _ _ hj1 hjk hX hy q hq) S.β q hq

end Charts

end Balaban.Inhabited
