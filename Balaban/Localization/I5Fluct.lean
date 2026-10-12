/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5FluctLocal
public import Balaban.Localization.I5
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem I-5 with the fluctuation field `ψ'` (LOCALIZATION.md §4.4, P3 (4.41))

For `X ⊂ X₁ ⊂ Ω_{k+1}` and `𝓔(X; ·)` analytic on `Ξ^c_j(𝔹_j(X); C₀, ε₃)` with
`|𝓔| ≤ E e^{-(κ-1) d^{cov}_j(X)}`, the composite
`F(Θ, ψ') = 𝓔(X; ψ(𝔹_j(X), 𝔹_k(X); ψ(𝔹_k(X), 𝔹_{k+1}; Θ) + δψ(𝔹_k(X), 𝔹_k; ψ')))`
(the decoupled objects at `s ≡ 1`; the fluctuation field `δφ` of `𝔹_k` is the solution of Theorem
I-4a (mode P) for the pair `(C, H⁻)`, `C` the decoupling cover of `𝔹_{k+1}`, with the background
`(φ_{k+1}, α_{k+1})`, and `δψ = Q(𝔹_k(X)) δφ + a(𝔹_k(X))⁻¹ Q*(𝔹_k, 𝔹_k(X)) a(𝔹_k) (ψ' - Q(𝔹_k) δφ)`,
P3 (4.17)) expands, for `Θ ∈ Ξ^c_{k+1}(𝔹_{k+1}; 1, ε')` and `ψ'` a block field of `𝔹_k` with
`|ψ'| < δ₁` (`FlBallLC`), as
`∑_{Y ⊃ X₁} 𝓔(X, Y; Θ, ψ')` with terms analytic in `(Θ, ψ')`, depending on `Θ` only through its
restriction to the thickening of `Y` and on `ψ'` only through its restriction to `Y` and its
neighbours, and bounded by `E e^{-κ₀ d^{cov}_j(X) - 2κ d̃^{cov}_{k+1}(Y)}` (`i5_fluct`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix

section I5Fluct

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}

variable (Hm) in
/-- **The datum of `𝔹_k(X)` in the composite of P3 (4.41) at `s ≡ 1`**:
`ψ(𝔹_k(X), 𝔹_{k+1}; Θ) + δψ(𝔹_k(X), 𝔹_k; ψ')` (P3 (4.16), (4.17); FLDATUM (3)), with the
background field `bgFieldC` of `𝔹_{k+1}`, the fluctuation field `δφ = flField` of Theorem I-4a
(mode P) for the pair `(C, H⁻)` with the data `(φ̄_{k+1}, α_{k+1}|, ψ', 0)` and `s ≡ 1`, and the
composition of the pair `(δφ, ψ')` from `𝔹_k` to `𝔹_k(X)`, for a block field `ψ'` of `𝔹_k`. -/
noncomputable def flDatumOne (BG₂ κ : ℝ) (hP : Precedes Gk Gp) (hPm : Precedes Gk Hm)
    (a₁ ν : ℝ) (D : BgData Gp N) (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (hψ' : IsLayerConstant Hm ψ') : BgData Gk N :=
  flDatum Gk hP hPm (compWeight L a₁) (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D)
    (flField (coverOf Gp) Hm (compWeight L a₁) ν
      (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) (fun _ => 1)
      (flEdat Gp Hm (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) D.Ψ ψ')) D ψ' hψ'

variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

/-- **Theorem I-5 with the fluctuation field `ψ'`.** -/
theorem i5_fluct (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) K N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X)) :
    ∃ Ev : Set (CTorus d L N₁ m₁ K) →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
        ∀ ψ' (hψ : ψ' ∈ FlBallLC Hm δ₁),
        E (rawOf (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatumOne Hm BG₂ κ hB.hP hF.hPm a₁ ν D ψ' hψ.2))
          (flDatumOne Hm BG₂ κ hB.hP hF.hPm a₁ ν D ψ' hψ.2))) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψ')) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBallLC Hm δ₁,
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBallLC Hm δ₁,
        agreeOn (thickSet Gp Y) u.1 u'.1 → (∀ y ∈ psiThick Y, u.2 y = u'.2 y) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBallLC Hm δ₁,
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBallLC Hm δ₁)) := by
  classical
  have hd : 3 ≤ d := hB.HBp.hd
  have hL : 3 ≤ L := hB.HBp.hL
  have hd0 : 0 < d := by omega
  have hc1 := one_le_xiC1 d
  have hε := hB.num.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hB.hS.fam.2.1 hd0).le hδ0.le)
  -- the analytic functions of Theorems I-4b, I-4a (mode P) and 7.2
  obtain ⟨F₁, hF₁an, hF₁⟩ := i4b_analytic hB.hS hB.Sp hB.HBp hB.hκ.le hB.hM
  obtain ⟨Fk, hFkan, hFk⟩ := theorem72_analytic (G := Gk) (a := compWeight L a₁) (ν := ν) hB.HBk
  obtain ⟨Sol, hSolan, hSolprop⟩ := Dec2.i4a_analytic (N := N) hF.hS2.fam hF.hS2.an
    hF.SM.toCoverBase hB.hκ.le hF.hM2 false hB0 hF.num.δ₁_pos.le hF.num.B_le hF.num.δ₁_le
  set ι := ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) with hι
  set cc : ι → ℕ × CTorus d L N₁ m₁ K := fun i => i.1.1 with hcc
  have hc : ∀ i, cc i ∈ cubeIdx Gp := fun i => i.1.2
  have hcinj : Function.Injective cc := fun i i' h => Subtype.ext (Subtype.ext h)
  have hdisj : ∀ i, Disjoint (Pset m₁ (cc i)) (X1 Gp m₀ j 𝒦X) := fun i => hX₁ ▸ i.2
  set F : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → (ι → ℂ) → ℂ :=
    fun u s => E (D2raw Gk Gj (compWeight L a₁) Fk (D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) u)) with hF'
  have hana := fan_analytic_fl hB hF hF₁an hF₁ hFkan hFk hSolan hSolprop hEan
  have hbd : ∀ u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBallLC Hm δ₁,
      ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ),
      ‖F u s‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X) := fun u hu s hs =>
    fan_bound_fl hB hF hF₁ hFk hSolprop hEbd hu.1 hu.2 hs
  have hloc := fan_local_fl hB hF hcov hX₁ hconn hrow hF₁ hFk hSolprop E
  have hloc' : LocalityAEOn (Real.exp κ)
      (XiCRaw (N := N) Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBallLC Hm δ₁)
      (fun i : ι => Pset m₁ (cc i)) (compY cc (X1 Gp m₀ j 𝒦X))
      (fun C u u' => agreeOn (N := N) (thickSet Gp (compY cc (↑X₁f : Set (CTorus d L N₁ m₁ K)) C))
        u.1 u'.1 ∧ ∀ y ∈ psiThick (compY cc (↑X₁f : Set (CTorus d L N₁ m₁ K)) C), u.2 y = u'.2 y)
      F := by
    rw [← hX₁]; exact hloc
  have hrefl : ∀ (C : Finset ι) (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)), u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBallLC Hm δ₁ →
      (fun C u u' => agreeOn (N := N) (thickSet Gp (compY cc (↑X₁f : Set (CTorus d L N₁ m₁ K)) C))
        u.1 u'.1 ∧ ∀ y ∈ psiThick (compY cc (↑X₁f : Set (CTorus d L N₁ m₁ K)) C), u.2 y = u'.2 y)
        C u u := fun C u _ => ⟨agreeOn_refl _ u.1, fun _ _ => rfl⟩
  have hlink : ∀ (C : Finset ι) (u u' : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)), (agreeOn (N := N) (thickSet Gp (Ysites Gp m₀ cc (X1 Gp m₀ j 𝒦X) C)) u.1 u'.1 ∧
        ∀ y ∈ psiThick (Ysites Gp m₀ cc (X1 Gp m₀ j 𝒦X) C), u.2 y = u'.2 y) →
      (agreeOn (N := N) (thickSet Gp (compY cc (↑X₁f : Set (CTorus d L N₁ m₁ K)) C)) u.1 u'.1 ∧
        ∀ y ∈ psiThick (compY cc (↑X₁f : Set (CTorus d L N₁ m₁ K)) C), u.2 y = u'.2 y) := by
    intro C u u' h
    have hsub : compY cc (↑X₁f : Set (CTorus d L N₁ m₁ K)) C ⊆
        Ysites Gp m₀ cc (X1 Gp m₀ j 𝒦X) C := by
      rw [hX₁]; exact compY_subset_Ysites hcov.hU hcov.hN hc _ C
    exact ⟨agreeOn_mono (thickSet_mono hsub) h.1, fun y hy => h.2 y (psiThick_mono hsub hy)⟩
  obtain ⟨hsum, hlocY, hbound, hanY⟩ := localization_expansion (c := cc) hcov hd hL hc hcinj hdisj
    hopt hκ₀ hκdec hκ h1 hlog hEb
    (Ag := fun C u u' => agreeOn (N := N) (thickSet Gp (compY cc (↑X₁f : Set (CTorus d L N₁ m₁ K)) C))
        u.1 u'.1 ∧ ∀ y ∈ psiThick (compY cc (↑X₁f : Set (CTorus d L N₁ m₁ K)) C), u.2 y = u'.2 y)
    (AgY := fun Y u u' => agreeOn (N := N) (thickSet Gp Y) u.1 u'.1 ∧
      ∀ y ∈ psiThick Y, u.2 y = u'.2 y) hrefl hlink hana hbd hloc'
  refine ⟨evTerm cc Gp m₀ (X1 Gp m₀ j 𝒦X) F, fun D hD ψ' hψ => ?_,
    fun Y u hu u' hu' h1 h2 => hlocY Y u hu u' hu' ⟨h1, h2⟩, hbound, hanY⟩
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hB.hκ
  have hsx : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ :=
    fun P => by simpa using hE1
  have hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
      (fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) ⟨P, hP⟩ = 1 := fun P hP hPn => rfl
  have hsum' := hsum (rawOf D, ψ') ⟨⟨D, hD, rfl⟩, hψ⟩
  rw [← hsum']
  symm
  show E (D2raw Gk Gj (compWeight L a₁) Fk (D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol
    (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) 1) (rawOf D, ψ'))) = _
  rw [extParams_one]
  obtain ⟨φ, α, δφ, hI, hFeq, hstrict, hδφ, hX3, hrawD, hD2, hX2⟩ :=
    point_facts_fl hB hF hF₁ hFk hSolprop hsx hs1 hD hψ.1 hψ.2
  rw [hrawD, hD2]
  -- identification of the background at `s ≡ 1`
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hB.num.c7le.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hB.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hB.HBp hB.num.small1 hD
  obtain ⟨-, hφ1, hα1⟩ := i4b_one hB.hS hB.Sp hB.HBp hB.hκ.le hB.hM hδ0 le_rfl hδ0' hB.num.c7le
    hνε hDom hI
  -- identification of the fluctuation at `s ≡ 1`
  obtain ⟨hfld, hfix, hs6, -, -, huniq⟩ := hSolprop ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
    flEdat Gp Hm (φ, α) D.Ψ ψ') hsx hstrict
  have hmult := flMult_spec (C := coverOf Gp) (Hm := Hm) (a := compWeight L a₁) (ν := ν)
    (ρ := c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) (s := fun _ : ↥(cubeIdx Gp) => (1 : ℂ))
    (e := flEdat Gp Hm (φ, α) D.Ψ ψ') ⟨hs6, hfix⟩ (fun δα' h => huniq δα' h.1 h.2)
  have hfl : flField (coverOf Gp) Hm (compWeight L a₁) ν
      (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) (fun _ => 1)
      (flEdat Gp Hm (φ, α) D.Ψ ψ') = δφ := by
    unfold flField
    exact (congrArg (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν
      (fun _ : ↥(cubeIdx Gp) => (1 : ℂ))) (flEdat Gp Hm (φ, α) D.Ψ ψ').2.1
      (flEdat Gp Hm (φ, α) D.Ψ ψ').1 (pertSource Hm (compWeight L a₁)
      (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.1 (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.2)) hmult).trans
      (hfld.symm.trans hδφ)
  have hflD : flDatumOne Hm BG₂ κ hB.hP hF.hPm a₁ ν D ψ' hψ.2 =
      flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψ.2 := by
    unfold flDatumOne
    rw [hφ1, hα1, hfl]
  rw [hflD]

end I5Fluct

end Balaban.Localization
