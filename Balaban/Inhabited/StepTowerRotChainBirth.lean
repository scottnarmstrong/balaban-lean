/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRotChainRen
public import Balaban.Fluctuation.OldTermBirthDomain
public import Balaban.Fluctuation.BirthMassFlow

/-!
# The class chain on its formula path with the chart premise replaced by the inclusion
(`StepTowerRotChainBirth`; rulings R2, R6, R13)

`StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_ren_rot_formula` takes the
chart premise `hchart` (the composed step data of every label lie in the class term domain) and the
bound of the irrelevant parts at the composed step data.  For a class whose term domain is the
birth-mass domain `birthXiDom` (ruling R6), in the regime of ruling R13 (`ClassHatCond`: the class
generating sets are the local sets `𝔹_j(X̂)`, the chain composes each term on them), the chart
premise is the inclusion of the composed data in the class domain at the birth masses
(`d2raw_mem_birthXiDom_of_class`), under the weights of the step, the flow of the masses of the class
(`birthMass_defect_of_flow`, `birthMass_bgHyp_of_flow`), the (DL-gap) of the charts and the
smallness of `ε_j`; and the bound at the composed data is the bound of the class on its term domain
(the open input A4-1b (ii), ruling R2).  The family is then the coefficient of a system of the class
(`NewLevelFormula`).

* `StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_ren_rot_formula_birth`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

open Classical in
/-- **The class chain on its formula path, with the chart premise replaced by the inclusion of the
composed data in the class domain at the birth masses** (rulings R2, R6, R13).  The statement of
`StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_ren_rot_formula` for a class
on the birth-mass domain `birthXiDom P Rg a`, in the regime `ClassHatCond` of ruling R13, with the
weights of the step, the flow of the masses of the class (the step mass `ν = ν_k L^{-2k}`), the
(DL-gap) of the charts at the birth masses and the smallness of `ε_j`, in place of `hchart`; the
bound of the irrelevant parts is taken on their term domain (A4-1b (ii)); the family is the
coefficient of a system of the class (`NewLevelFormula`). -/
theorem StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_ren_rot_formula_birth (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    (m₀ : ℕ) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2) :
    ∃ (κmin : ℝ) (_ : stepHullMinG d L ≤ κmin) (T₀ : StepTowerG d L N κmin) (κdec Q F η : ℝ),
      T₀.m₀ = 1 ∧ T₀.κ0 = aEnt d L + 2 ∧
      4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ T₀.κ ∧
      (2 * T₀.κdec - 1) * ((L : ℝ) ^ (m₀ - 1) + 2 * (d : ℝ) *
        (L : ℝ) ^ m₀ * ((((L ^ (m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L) + 1 ≤ 2 * κdec ∧
      Q = (N : ℝ) * composedCloseBound d L N T₀.m₁ T₀.BG T₀.κ (xiC1 d) (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) ∧
      xiK2 d L N * Q ≤ (1 - (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ))) / (2 * (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ))) ∧
      F = (N : ℝ) * (5 * cK2' d L N (famConst d L T₀.BG₂ T₀.κ) + 1) ∧
      η = (1 - (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ))) / (4 * xiK2 d L N * F) ∧ 0 ≤ Q ∧ 0 < F ∧ 0 < η ∧
      ∀ P₀ : Consts, P₀.γ = γ → 0 < P₀.α₀ → ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ r₀ lam : ℝ, 0 < r₀ → lam = 1 + xiK2 d L N * ((3 / 2 : ℝ) * r₀) →
      xiK2 d L N * ((3 / 2 : ℝ) * r₀) * (3 + (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ))) ≤
        1 - (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) → lam * P₀.eps d L 1 ≤ T₀.t →
      ∀ (k : ℕ) (hk : 1 ≤ k), ∃ Tk : StepTowerG d L N κmin, Tk.t = lam * P₀.eps d L (k + 1) ∧
        Tk.m₁ = T₀.m₁ ∧ Tk.c = T₀.c ∧ Tk.BG = T₀.BG ∧ Tk.κ = T₀.κ ∧ Tk.c₂ = T₀.c₂ ∧
        Tk.BG₂ = T₀.BG₂ ∧ Tk.δc = T₀.δc ∧ Tk.δ = T₀.δ ∧ Tk.δ' = T₀.δ' ∧ Tk.κ0 = T₀.κ0 ∧ Tk.m₀ = T₀.m₀ ∧
        ChainNum d L N Tk.m₁ Tk.BG Tk.κ (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) Tk.t (Q * Tk.t) ∧
        FlNum d L N Tk.BG Tk.BG₂ Tk.κ Tk.t (Q * Tk.t) (min Tk.t (η * (lam * P₀.eps d L k)))
          (F * min Tk.t (η * (lam * P₀.eps d L k))) ∧
        -- the cover: the radius premise of `newLabels_castInputs` at `eps = Tk.t`
        P₀.eps d L (k + 1) ≤ Tk.t ∧
        -- the room of the inherited labels at every level `j ≤ k`
        (∀ j ≤ k, Tk.t + xiK2 d L N * (Q * Tk.t) +
          xiK2 d L N * (F * min Tk.t (η * (lam * P₀.eps d L k))) ≤ P₀.eps d L j) ∧
      ∀ (N₁ : ℕ) [NeZero N₁] (_ : L ^ Tk.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ {ϱ : ℝ} (_ : ϱ = rhoSepG d L Tk.m₁) (S : StepSetting d L N₁ Tk.m₁ k N ϱ)
        (_ : S = hatStepKG Tk.hN k Tk.m₁ ϱ hk ν β p₁ Tk.δ),
      ∃ Jr : S.JointRep Tk.t (2 * p₁),
      ∀ (C : StepClass d L N₁ Tk.m₁ k N ϱ) (z : RootIdx d L N₁ Tk.m₁ (k + 1))
        (𝒯E : Finset (ℕ × CTorus d L N₁ Tk.m₁ (k + 1) × Set (CTorus d L N₁ Tk.m₁ (k + 1))))
        (_ : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ Tk.m₁ (k + 1) ×
            Set (CTorus d L N₁ Tk.m₁ (k + 1))))).filter
          (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
        {P : Consts} (Rg : Regime L) (a : ℕ → ℝ)
        (_ : P.m₀ = C.m₀) (_ : SFTermClauses P (birthXiDom P Rg a N₁) C.Tm)
        (_ : 0 ≤ P.E₀) (i₀ i₁ : Fin N)
        (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1)
            ϱ, (∀ i, j < i → G.Ω i = ∅) →
          ∀ Ψ : Fld d L N₁ Tk.m₁ (k + 1) N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
          (∀ x x', jBlock d L (N₁ * L ^ Tk.m₁) (k + 1) j x = jBlock d L (N₁ * L ^ Tk.m₁) (k + 1) j x' →
            Ψ x = Ψ x') →
          (birthXiDom P Rg a N₁).dom j G Ψ (constFld (Pi.single i₀ 1)))
        (XL 𝒦X : {τ // τ ∈ 𝒯E} → Set (CTorus d L N₁ Tk.m₁ (k + 1)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, XL τ = τ.1.2.2 ∪ box (cbase (cellSide L C.m₀ Tk.m₁ τ.1.1) τ.1.2.1 -
          natT fun _ => L / 2 * cellSide L C.m₀ Tk.m₁ τ.1.1) (L * cellSide L C.m₀ Tk.m₁ τ.1.1))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ChosenOne C.m₀ τ.1.1 (XL τ) (𝒦X τ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∃ (W₀ : Finset (CTorus d L N₁ Tk.m₁ (k + 1)))
          (E₀ : Finset (CTorus d L N₁ Tk.m₁ (k + 1) × CTorus d L N₁ Tk.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
            bondCost (scaleW L C.m₀ Tk.m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 (XL τ))
        (_ : L ^ C.m₀ ∣ N₁) (_ : d ≤ C.m₀) {s : ℕ} (_ : s ≤ C.m₀)
        (_ : (((5 * L + 13) * L ^ s : ℕ) : ℝ) + (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) * (L : ℝ) ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (C.m₀ + 1))
        (_ : rhoSepG d L Tk.m₁ ≤ Balaban.LargeField.minSep L (L ^ (Tk.m₁ + s))) (_ : C.m₀ = m₀)
        -- the regime of ruling R13, and the composed data of the labels in the class domain at the
        -- birth masses (the weights, the flow of the masses, the (DL-gap) and the smallness of `ε_j`)
        (_ : ClassHatCond C s (4 * (d : ℝ) * (L : ℝ) ^ 3 + L))
        (_ : aIdeal L (k + 1) (a (k + 1)) = compWeight L S.a₁)
        {ξ : ℕ → Fin 3 → ℂ} {q c₈ ν₀ : ℝ} (_ : 0 ≤ q) (_ : q < 1) (_ : 0 ≤ c₈)
        (_ : c₈ * q ≤ 1 - q) (_ : ∀ n, ‖ξ n‖ ≤ c₈ / 4 * q ^ (n + 1))
        (_ : ∀ n, n ≤ k → ((Rg.ν n : ℝ) : ℂ) = Flow.nuSeq (L : ℝ) ξ (ν₀ : ℂ) n)
        (_ : ν = physMass L k (Rg.ν k))
        {rm : ℝ} (_ : (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1) ≤ 1 / 2) (_ : 2 * (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1) < rm) (_ : rm ≤ 1 / 16)
        (_ : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (1 + 2 * (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1)) ≤ 1)
        (_ : ∀ j, 1 ≤ j → j ≤ k →
          (2 * (Tk.t + xiK2 d L N * (Q * Tk.t) + xiK2 d L N * (F * min Tk.t (η * (lam * P₀.eps d L k)))) + 2 * ((N : ℝ) + 1) * (cK2 d L N * (Tk.t + xiK2 d L N * (Q * Tk.t) + xiK2 d L N * (F * min Tk.t (η * (lam * P₀.eps d L k)))) ^ 2)) *
            (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * (2 * (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1))) ≤ P.eps d L j)
        (_ : ∀ j, 1 ≤ j → j ≤ k → (4 * d + 6) * ((2 * d + 1) * P.eps d L j) ≤ 1)
        (_ : ∀ j, 1 ≤ j → j ≤ k → 4 * (xiC1 d * P.eps d L j) ≤ bgC1 d L N)
        (_ : ∀ j, 1 ≤ j → j ≤ k → bgK1 d L N * (xiC1 d * P.eps d L j) + 3 * rm ≤ deltaStar d L N)
        (_ : ∀ j, 1 ≤ j → j ≤ k → 8 * P.eps d L j * rm ≤ deltaStar d L N),
      ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1) ϱ)
        (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1) ϱ)
        (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus d L N₁ Tk.m₁ (k + 1))),
        (∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ Tk.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
        (∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν Tk.c Tk.BG Tk.κ (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) Tk.t (Q * Tk.t) (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ Tk.m₁ k ϱ) S.a₁ S.ν Tk.κ Tk.BG Tk.t (Q * Tk.t)
          (levelKc d L) (Cchi d L) Tk.c₂ Tk.BG₂ (min Tk.t (η * (lam * P₀.eps d L k))) (F * min Tk.t (η * (lam * P₀.eps d L k))) (X₁f τ)) ∧
        (∀ τ : {τ // τ ∈ 𝒯E}, Gj τ = C.Tm.gs τ.1.1 τ.1.2.2) ∧
        ∀
        -- the per-label bounds of the irrelevant parts in `d(X)` on their term domain
        -- (P1 (3.128), the open input A4-1b (ii))
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ Ψ h : Fld d L N₁ Tk.m₁ (k + 1) N,
          (birthXiDom P Rg a N₁).dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) Ψ h →
          dot (Ψ τ.1.2.1) (Ψ τ.1.2.1) ∈ Complex.slitPlane →
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 Ψ h‖ ≤
            Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
        {CI KL α₃ : ℝ} (n₁ : ℕ) (_ : 0 ≤ CI) (_ : 0 ≤ KL) (_ : 0 < α₃)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 + n₁ ≤ k →
          Bτ τ ≤ CI * P.E₀ * ((((L : ℝ)⁻¹ ^ (k - τ.1.1)) ^ ((d : ℝ) + α₃))))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, k < τ.1.1 + n₁ → Bτ τ ≤ KL * P.E₀),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 Tk.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld d L N₁ Tk.m₁ (k + 1) N × Fld d L N₁ Tk.m₁ (k + 1) N =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- the smallness of the class constants against the marked radius
      (corrU / ((min Tk.t (η * (lam * P₀.eps d L k))) / (2 * markedRad d L N k S.a₁ Tk.κ p₁
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          (((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + C.m₀ + Tk.m₁)) ^ d) * P.E₀ *
          (2 * K0 d L Tk.κ0 * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * ((((L : ℝ) ^ (n₁ - 1)) ^ d))))) *
          Real.exp ((2 * Tk.κdec - 1) * (2 * (d : ℝ) * (L : ℝ) ^ C.m₀ *
            ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L)))) ≤
          1 / (8 * (2 * (K0 d L Tk.κ0 + 1) + (K0 d L Tk.κ0 + rootUnionK d L 1 Tk.m₁ Tk.κ0) +
            rootUnionK d L 1 Tk.m₁ Tk.κ0) ^ 3 * c1 d L *
            Real.exp (((2 * Tk.κdec - 1) - 2 * Tk.κ0) * cG d L + c1 d L + Tk.κ' * cG d L))) →
      ∃ e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
        (∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1)
            Set.univ),
          AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν Tk.t) ∧
          (∀ θ ∈ physV S S.a₁ S.ν Tk.t, ∀ θ' ∈ physV S S.a₁ S.ν Tk.t,
            physRestrict (N := N) (thickSet S.G' (Yhat Set.univ (sitesOf T')))
                (physIncl N S θ) =
              physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf T'))) (physIncl N S θ') →
            e θ T' = e θ' T') ∧
          (∀ θ ∈ physV S S.a₁ S.ν Tk.t, ‖e θ T'‖ ≤
            (L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L Tk.κ /
                (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp Tk.κ))) *
                Real.exp (-((Tk.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) *
                  dExt T') +
              B * Real.exp (-Tk.κ' * dExt T')) ∧
          (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T'))) ∧
        (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 Tk.t D →
          Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ Tk.m₁ (k + 1) → Fin N → ℂ)) T' ∧
          (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub N S.G'), (0 : CTorus d L N₁ Tk.m₁ (k + 1) → Fin N → ℂ)) T') ∧
        (∀ ε : ℝ, ε ≤ Tk.t → ∀ q : Fld d L N₁ Tk.m₁ (k + 1) N × Fld d L N₁ Tk.m₁ (k + 1) N,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub N S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'), 0) T' else 0)) ∧
        -- the per-label spin covariance of the family
        (∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν Tk.t, ∀ θ' ∈ physV S S.a₁ S.ν Tk.t,
          (θ'.1 : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N) =
            rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N) →
          ∀ T', e θ' T' = e θ T') ∧ NewLevelFormula S C z Jr
          ⟨Tk.κ, Tk.BG, Tk.BG₂, p₁, Tk.κ0, Tk.κ, Tk.BG, Tk.BG₂, min Tk.t (η * (lam * P₀.eps d L k)), p₁, C.m₀,
            Tk.c, 4 * (d : ℝ) * (L : ℝ) ^ 3 + L, Q * Tk.t, levelKc d L, Cchi d L, Tk.c₂,
            F * min Tk.t (η * (lam * P₀.eps d L k))⟩ e := by
  classical
  have : NeZero N := ⟨by omega⟩
  obtain ⟨κmin, hlo, T₀, κdec, Q, F, η, hm0, hk0, hκ₀, hrate₀, hQdef, hQθ, hFdef, hηdef, hQ, hF,
    hη, Hφ⟩ := StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_ren_rot_formula
      d L N hd hL hN m₀ hA p hγ0 hγ1
  refine ⟨κmin, hlo, T₀, κdec, Q, F, η, hm0, hk0, hκ₀, hrate₀, hQdef, hQθ, hFdef, hηdef, hQ, hF, hη,
    fun P₀ hγ hα₀ => ?_⟩
  obtain ⟨β₀, hβ₀, H⟩ := Hφ P₀ hγ hα₀
  refine ⟨β₀, hβ₀, fun r₀ lam hr hlam hrr hε1 k hk => ?_⟩
  obtain ⟨Tk, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hTk0, hTm0, hC, hFl, hcov, hroom,
    Hk⟩ := H r₀ lam hr hlam hrr hε1 k hk
  refine ⟨Tk, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hTk0, hTm0, hC, hFl, hcov, hroom, ?_⟩
  intro N₁ _ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ ϱ hϱ S hS
  obtain ⟨Jr, Hφ'⟩ := Hk N₁ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ hϱ S hS
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Rg a hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7 s hs hidx hmin hCm hHat
    hAw ξ q c₈ ν₀ hq0 hq1 hc₈ hc₈q hξ hνflow hνS rm hτ hτr hrm hmass hDL hsmε hc1ε hKε hζε
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, hGjC, HG⟩ := @Hφ' C z 𝒯E h𝒯 P (birthXiDom P Rg a N₁) hm
    hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7 s hs hidx hmin hCm
  have hGj := hGjC hHat
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, hGj, ?_⟩
  intro Bτ hBτ hB CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hE hεnum
  have hSν : S.ν = ν := by subst hS; rfl
  -- the composed step data of the labels lie in the class term domain at the birth masses
  have hchart : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N →
        ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ)),
      (∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
        Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
          bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D)) →
      ∀ t ∈ FlRealLC S.G' (stepG d L N₁ Tk.m₁ k ϱ) S.a₁ S.ν Tk.BG Tk.κ Tk.t
        (X₁f τ) Tk.BG₂ (min Tk.t (η * (lam * P₀.eps d L k))),
      ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) Fk
        (d1Triple S.G' (Gk τ) (stepG d L N₁ Tk.m₁ k ϱ) (compWeight L S.a₁) t.1.1
          t.2.1 t.2.2) →
      (birthXiDom P Rg a N₁).dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
        dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane := by
    intro τ Fk hFk t ht r hr
    subst hr
    have hmem : τ.1.1 ∈ Finset.Icc 1 k ∧ Aligned (L ^ τ.1.1) τ.1.2.1 ∧
        IsPolyDom C.m₀ τ.1.1 τ.1.2.2 ∧ τ.1.2.1 ∈ τ.1.2.2 := by
      have h : τ.1 ∈ ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ Tk.m₁ (k + 1) ×
          Set (CTorus d L N₁ Tk.m₁ (k + 1))))).filter
          (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2) := by
        rw [← h𝒯]; exact τ.2
      rw [Finset.mem_filter, Finset.mem_product] at h
      exact ⟨h.1.1, h.2⟩
    obtain ⟨hjI, -, hX, hy⟩ := hmem
    obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hjI
    have hB' := hBs τ
    have hF' := hFs τ
    rw [hGj τ] at hB'
    rw [hGj τ]
    have HB := hB'.HBp
    have H' := birthMass_bgHyp_of_flow HB hq0 hq1 hc₈ hc₈q hξ hτ hνflow (hSν.trans hνS)
      (by rw [hSν]; exact hmass)
    obtain ⟨t', ht', htb⟩ := birthMass_defect_of_flow hq0 hq1 hc₈ hc₈q hξ hτ hνflow _ hj1 hjk
    have hK2 : 0 < xiK2 d L N := by
      have := cK2_pos d L N
      unfold xiK2; positivity
    have he : 0 < Tk.t + xiK2 d L N * (Q * Tk.t) +
        xiK2 d L N * (F * min Tk.t (η * (lam * P₀.eps d L k))) := by
      have h1 := hB'.num.eps_pos
      have h2 := mul_nonneg hK2.le hB'.num.δ₃_nn
      have h3 := mul_nonneg hK2.le hF'.num.δfl_nn
      linarith
    exact d2raw_mem_birthXiDom_of_class P Rg a hcl hj1 (hjk.trans (Nat.le_succ k)) (hm ▸ hX) hy hB'
      hF' hAw HB (H' _ hj1 hjk) (by rw [ht', hSν, hνS]) htb hτr hrm he (hDL _ hj1 hjk)
      (hsmε _ hj1 hjk) (hc1ε _ hj1 hjk) (hKε _ hj1 hjk) (hζε _ hj1 hjk) hFk ht
  -- the bound of the irrelevant parts at the composed step data, by the inclusion
  obtain ⟨e, B, h1, h2, h3, h4, hW⟩ := @HG hchart Bτ hBτ
    (fun τ Fk hFk t ht r hr => hB τ r.1 r.2 (hchart τ Fk hFk t ht r hr).1
      (hchart τ Fk hFk t ht r hr).2) CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hE hεnum
  exact ⟨e, B, h1, h2, h3, h4, hW.2 hHat⟩

end Balaban.Inhabited
