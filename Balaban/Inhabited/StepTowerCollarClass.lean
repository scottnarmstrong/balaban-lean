/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerCollarUniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The decoupled class chain at the class radii `ε_j = P.eps 3 3 j` (`StepTowerCollarClass`)

`e0CoeffFamily_class_exists_tower_struct_step_collar_classEps`: the instance of
`e0CoeffFamily_class_exists_tower_struct_step_collar_uniform` at the class sequence
`ε_j = α₀ (1 + Σ_{n ≥ j} n^{-2}) 3^{-α j}` (P4 (H.1)) with `α = 1/2 - γ`, `0 < γ < 1/2`,
`q = 3^{-α}` (`classEps_antitone`, `classEps_gap`, `classEps_lower` with `c₁ = α₀`).  The order of the
choices is that of the source (FLUCTUATION §1.5): `γ`, then the reference tower `T₀` (its block
`m₁` from `K₂ Q ≤ (1 - q) / (2 q)`), then `α₀` with `ε_1 ≤ T₀.t`, then `β₀`.  At every scale
`k ≥ 1` the tower `T_k` has the step radius `T_k.t = ε_{k+1}`, so the radius premise
`P.eps 3 3 (k + 1) ≤ eps` of `newLabels_castInputs` holds at `eps = T_k.t` (the chain's
`XiCData … T_k.t` and `XiDom … ε`, `ε ≤ T_k.t`), and the room `t_k + K₂ δ₃ + K₂ δ_fl ≤ ε_j`
(`j ≤ k`) of the inherited labels (`d2raw_d1Triple_mem_xiDom`) holds at the same tower.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

open Classical in
/-- **The class chain at the collar of a general tower at the class radii, with the formula of its
family.**  The statement of `StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_phi`
with one more premise of `hΦ`: the family `e` is the coefficient of a system of the new level of `C`
(`NewLevelFormula`). -/
theorem StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_phi_formula (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
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
      ∀ P₀ : Consts, P₀.γ = γ → 0 < P₀.α₀ → P₀.eps d L 1 ≤ T₀.t → ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k), ∃ Tk : StepTowerG d L N κmin, Tk.t = P₀.eps d L (k + 1) ∧
        Tk.m₁ = T₀.m₁ ∧ Tk.c = T₀.c ∧ Tk.BG = T₀.BG ∧ Tk.κ = T₀.κ ∧ Tk.c₂ = T₀.c₂ ∧
        Tk.BG₂ = T₀.BG₂ ∧ Tk.δc = T₀.δc ∧ Tk.δ = T₀.δ ∧ Tk.δ' = T₀.δ' ∧ Tk.κ0 = T₀.κ0 ∧ Tk.m₀ = T₀.m₀ ∧
        ChainNum d L N Tk.m₁ Tk.BG Tk.κ (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) Tk.t (Q * Tk.t) ∧
        FlNum d L N Tk.BG Tk.BG₂ Tk.κ Tk.t (Q * Tk.t) (min Tk.t (η * P₀.eps d L k))
          (F * min Tk.t (η * P₀.eps d L k)) ∧
        -- the cover: the radius premise of `newLabels_castInputs` at `eps = Tk.t`
        P₀.eps d L (k + 1) ≤ Tk.t ∧
        -- the room of the inherited labels at every level `j ≤ k`
        (∀ j ≤ k, Tk.t + xiK2 d L N * (Q * Tk.t) +
          xiK2 d L N * (F * min Tk.t (η * P₀.eps d L k)) ≤ P₀.eps d L j) ∧
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
        {P : Consts} {Dom : FieldDom d L N₁ Tk.m₁ (k + 1) N ϱ}
        (_ : P.m₀ = C.m₀) (_ : SFTermClauses P Dom C.Tm)
        (_ : 0 ≤ P.E₀) (i₀ i₁ : Fin N)
        (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1)
            ϱ, (∀ i, j < i → G.Ω i = ∅) →
          ∀ Ψ : Fld d L N₁ Tk.m₁ (k + 1) N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
          (∀ x x', jBlock d L (N₁ * L ^ Tk.m₁) (k + 1) j x = jBlock d L (N₁ * L ^ Tk.m₁) (k + 1) j x' →
            Ψ x = Ψ x') →
          Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
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
        (_ : rhoSepG d L Tk.m₁ ≤ Balaban.LargeField.minSep L (L ^ (Tk.m₁ + s))) (_ : C.m₀ = m₀),
      ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1) ϱ)
        (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1) ϱ)
        (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus d L N₁ Tk.m₁ (k + 1))),
        (∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ Tk.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
        (∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν Tk.c Tk.BG Tk.κ (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) Tk.t (Q * Tk.t) (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ Tk.m₁ k ϱ) S.a₁ S.ν Tk.κ Tk.BG Tk.t (Q * Tk.t)
          (levelKc d L) (Cchi d L) Tk.c₂ Tk.BG₂ (min Tk.t (η * P₀.eps d L k)) (F * min Tk.t (η * P₀.eps d L k)) (X₁f τ)) ∧
        (ClassHatCond C s (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) → ∀ τ : {τ // τ ∈ 𝒯E}, Gj τ = C.Tm.gs τ.1.1 τ.1.2.2) ∧
        ∀
        -- the composed step data of the labels lie in the term domain, `Ψ(y)·Ψ(y)` in the slit plane
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N →
            ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
              bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG d L N₁ Tk.m₁ k ϱ) S.a₁ S.ν Tk.BG Tk.κ Tk.t
            (X₁f τ) Tk.BG₂ (min Tk.t (η * P₀.eps d L k)),
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG d L N₁ Tk.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) →
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
            dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
        -- the per-label bounds of the irrelevant parts in `d(X)` at the composed step data
        -- (P1 (3.128), open)
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N →
            ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
              bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG d L N₁ Tk.m₁ k ϱ) S.a₁ S.ν Tk.BG Tk.κ Tk.t
            (X₁f τ) Tk.BG₂ (min Tk.t (η * P₀.eps d L k)),
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG d L N₁ Tk.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) →
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
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
      (corrU / ((min Tk.t (η * P₀.eps d L k)) / (2 * markedRad d L N k S.a₁ Tk.κ p₁
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          (((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + C.m₀ + Tk.m₁)) ^ d) * P.E₀ *
          (2 * K0 d L Tk.κ0 * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * ((((L : ℝ) ^ (n₁ - 1)) ^ d))))) *
          Real.exp ((2 * Tk.κdec - 1) * (2 * (d : ℝ) * (L : ℝ) ^ C.m₀ *
            ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L)))) ≤
          1 / (8 * (2 * (K0 d L Tk.κ0 + 1) + (K0 d L Tk.κ0 + rootUnionK d L 1 Tk.m₁ Tk.κ0) +
            rootUnionK d L 1 Tk.m₁ Tk.κ0) ^ 3 * c1 d L *
            Real.exp (((2 * Tk.κdec - 1) - 2 * Tk.κ0) * cG d L + c1 d L + Tk.κ' * cG d L))) →
      (Φ : (physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) → ℝ → Prop) →
      (∀ (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) (B : ℝ),
        -- the spin covariance of `e`
        (∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν Tk.t, ∀ θ' ∈ physV S S.a₁ S.ν Tk.t,
          (θ'.1 : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N) =
            rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N) →
          ∀ T', e θ' T' = e θ T') →
        (NewLevelFormulaW S C z Jr
          ⟨Tk.κ, Tk.BG, Tk.BG₂, p₁, Tk.κ0, Tk.κ, Tk.BG, Tk.BG₂, min Tk.t (η * P₀.eps d L k), p₁, C.m₀,
            Tk.c, 4 * (d : ℝ) * (L : ℝ) ^ 3 + L, Q * Tk.t, levelKc d L, Cchi d L, Tk.c₂,
            F * min Tk.t (η * P₀.eps d L k)⟩ e ∧
          (ClassHatCond C s (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) → NewLevelFormula S C z Jr
          ⟨Tk.κ, Tk.BG, Tk.BG₂, p₁, Tk.κ0, Tk.κ, Tk.BG, Tk.BG₂, min Tk.t (η * P₀.eps d L k), p₁, C.m₀,
            Tk.c, 4 * (d : ℝ) * (L : ℝ) ^ 3 + L, Q * Tk.t, levelKc d L, Cchi d L, Tk.c₂,
            F * min Tk.t (η * P₀.eps d L k)⟩ e)) →
        B ≤ CPE d L (2 * (K0 d L Tk.κ0 + 1) + (K0 d L Tk.κ0 + rootUnionK d L 1 Tk.m₁ Tk.κ0) +
          rootUnionK d L 1 Tk.m₁ Tk.κ0) (2 * Tk.κdec - 1) Tk.κ0 Tk.κ' *
          (corrF0G Tk k β p₁ * K0 d L Tk.κ0 +
            (((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + C.m₀ + Tk.m₁)) ^ d) * P.E₀ *
          (2 * K0 d L Tk.κ0 * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * ((((L : ℝ) ^ (n₁ - 1)) ^ d))))) *
          Real.exp ((2 * Tk.κdec - 1) * (2 * (d : ℝ) * (L : ℝ) ^ C.m₀ *
            ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L)))) / (2 * (min Tk.t (η * P₀.eps d L k) / (4 * decMRG Tk k (β * (L : ℝ) ^ (k * (d - 2))) p₁))) *
              (((nFibre d L : ℕ) : ℝ) * Real.exp ((2 * Tk.κdec - 1) * cBr d L)) * K0 d L Tk.κ0 +
            ((nFibre d L : ℕ) : ℝ) * Real.exp (Tk.κ0 * cBr d L) * K0 d L Tk.κ0) → Φ e B) →
      ∃ e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
        Φ e B ∧
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
        ∀ ε : ℝ, ε ≤ Tk.t → ∀ q : Fld d L N₁ Tk.m₁ (k + 1) N × Fld d L N₁ Tk.m₁ (k + 1) N,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub N S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'), 0) T' else 0) := by
  have h3d : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hq0 : 0 < (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) := Real.rpow_pos_of_pos hLpos _
  have hq1 : (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < L)) (by linarith)
  have hαd : 2 * (((d : ℝ) - 2) / 2 - γ) < ((d - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; linarith
  obtain ⟨κmin, hlo, T₀, κdec, Q, F, η, hm0, hk0, hκ₀, hrate₀, hQdef, hQθ, hFdef, hηdef, hQ, hF,
    hη, H⟩ := StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_uniform_phi_formula d L N hd hL hN m₀ hA p hq0 hq1 (α := ((d : ℝ) - 2) / 2 - γ) hαd
  refine ⟨κmin, hlo, T₀, κdec, Q, F, η, hm0, hk0, hκ₀, hrate₀, hQdef, hQθ, hFdef, hηdef, hQ, hF, hη,
    fun P₀ hγ hα₀ hε1 => ?_⟩
  have hαP : P₀.alpha d = ((d : ℝ) - 2) / 2 - γ := by
    unfold Consts.alpha
    rw [hγ]
  obtain ⟨β₀, hβ₀, HC⟩ := H P₀.α₀ hα₀
  refine ⟨β₀, hβ₀, fun k hk => ?_⟩
  have hpos : ∀ j, 0 < P₀.eps d L j := fun j => by
    have := epsTail_pos j
    unfold Consts.eps epsSeq
    positivity
  have hgap : ∀ j, P₀.eps d L (j + 1) ≤ (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) * P₀.eps d L j := fun j => by
    have := classEpsG_gap (d := d) (L := L) hα₀.le j
    rwa [hαP] at this
  have hlow : ∀ j : ℕ, P₀.α₀ * (L : ℝ) ^ (-((((d : ℝ) - 2) / 2 - γ) * (j : ℝ))) ≤ P₀.eps d L j :=
    fun j => by
      have := classEpsG_lower (d := d) (L := L) hα₀.le j
      rwa [hαP] at this
  obtain ⟨Tk, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hTk0, hTm0, hC, hFl, hroom,
    Hk⟩ := HC (P₀.eps d L) (classEpsG_antitone hα₀.le (by rw [hαP]; linarith)) hpos hgap hlow hε1
    k hk
  exact ⟨Tk, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hTk0, hTm0, hC, hFl, hTt.ge,
    hroom, Hk⟩

open Classical in
/-- The class chain at the class radii of a general tower, with `B` bounded by an explicit constant. -/
theorem StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_phi (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
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
      ∀ P₀ : Consts, P₀.γ = γ → 0 < P₀.α₀ → P₀.eps d L 1 ≤ T₀.t → ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k), ∃ Tk : StepTowerG d L N κmin, Tk.t = P₀.eps d L (k + 1) ∧
        Tk.m₁ = T₀.m₁ ∧ Tk.c = T₀.c ∧ Tk.BG = T₀.BG ∧ Tk.κ = T₀.κ ∧ Tk.c₂ = T₀.c₂ ∧
        Tk.BG₂ = T₀.BG₂ ∧ Tk.δc = T₀.δc ∧ Tk.δ = T₀.δ ∧ Tk.δ' = T₀.δ' ∧ Tk.κ0 = T₀.κ0 ∧ Tk.m₀ = T₀.m₀ ∧
        ChainNum d L N Tk.m₁ Tk.BG Tk.κ (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) Tk.t (Q * Tk.t) ∧
        FlNum d L N Tk.BG Tk.BG₂ Tk.κ Tk.t (Q * Tk.t) (min Tk.t (η * P₀.eps d L k))
          (F * min Tk.t (η * P₀.eps d L k)) ∧
        -- the cover: the radius premise of `newLabels_castInputs` at `eps = Tk.t`
        P₀.eps d L (k + 1) ≤ Tk.t ∧
        -- the room of the inherited labels at every level `j ≤ k`
        (∀ j ≤ k, Tk.t + xiK2 d L N * (Q * Tk.t) +
          xiK2 d L N * (F * min Tk.t (η * P₀.eps d L k)) ≤ P₀.eps d L j) ∧
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
        {P : Consts} {Dom : FieldDom d L N₁ Tk.m₁ (k + 1) N ϱ}
        (_ : P.m₀ = C.m₀) (_ : SFTermClauses P Dom C.Tm)
        (_ : 0 ≤ P.E₀) (i₀ i₁ : Fin N)
        (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1)
            ϱ, (∀ i, j < i → G.Ω i = ∅) →
          ∀ Ψ : Fld d L N₁ Tk.m₁ (k + 1) N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
          (∀ x x', jBlock d L (N₁ * L ^ Tk.m₁) (k + 1) j x = jBlock d L (N₁ * L ^ Tk.m₁) (k + 1) j x' →
            Ψ x = Ψ x') →
          Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
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
        (_ : rhoSepG d L Tk.m₁ ≤ Balaban.LargeField.minSep L (L ^ (Tk.m₁ + s))) (_ : C.m₀ = m₀),
      ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1) ϱ)
        (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1) ϱ)
        (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus d L N₁ Tk.m₁ (k + 1))),
        (∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ Tk.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
        (∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν Tk.c Tk.BG Tk.κ (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) Tk.t (Q * Tk.t) (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ Tk.m₁ k ϱ) S.a₁ S.ν Tk.κ Tk.BG Tk.t (Q * Tk.t)
          (levelKc d L) (Cchi d L) Tk.c₂ Tk.BG₂ (min Tk.t (η * P₀.eps d L k)) (F * min Tk.t (η * P₀.eps d L k)) (X₁f τ)) ∧
        ∀
        -- the composed step data of the labels lie in the term domain, `Ψ(y)·Ψ(y)` in the slit plane
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N →
            ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
              bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG d L N₁ Tk.m₁ k ϱ) S.a₁ S.ν Tk.BG Tk.κ Tk.t
            (X₁f τ) Tk.BG₂ (min Tk.t (η * P₀.eps d L k)),
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG d L N₁ Tk.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) →
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
            dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
        -- the per-label bounds of the irrelevant parts in `d(X)` at the composed step data
        -- (P1 (3.128), open)
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N →
            ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
              bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG d L N₁ Tk.m₁ k ϱ) S.a₁ S.ν Tk.BG Tk.κ Tk.t
            (X₁f τ) Tk.BG₂ (min Tk.t (η * P₀.eps d L k)),
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG d L N₁ Tk.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) →
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
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
      (corrU / ((min Tk.t (η * P₀.eps d L k)) / (2 * markedRad d L N k S.a₁ Tk.κ p₁
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          (((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + C.m₀ + Tk.m₁)) ^ d) * P.E₀ *
          (2 * K0 d L Tk.κ0 * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * ((((L : ℝ) ^ (n₁ - 1)) ^ d))))) *
          Real.exp ((2 * Tk.κdec - 1) * (2 * (d : ℝ) * (L : ℝ) ^ C.m₀ *
            ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L)))) ≤
          1 / (8 * (2 * (K0 d L Tk.κ0 + 1) + (K0 d L Tk.κ0 + rootUnionK d L 1 Tk.m₁ Tk.κ0) +
            rootUnionK d L 1 Tk.m₁ Tk.κ0) ^ 3 * c1 d L *
            Real.exp (((2 * Tk.κdec - 1) - 2 * Tk.κ0) * cG d L + c1 d L + Tk.κ' * cG d L))) →
      (Φ : (physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) → ℝ → Prop) →
      (∀ (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) (B : ℝ),
        -- the spin covariance of `e`
        (∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν Tk.t, ∀ θ' ∈ physV S S.a₁ S.ν Tk.t,
          (θ'.1 : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N) =
            rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N) →
          ∀ T', e θ' T' = e θ T') →
        B ≤ CPE d L (2 * (K0 d L Tk.κ0 + 1) + (K0 d L Tk.κ0 + rootUnionK d L 1 Tk.m₁ Tk.κ0) +
          rootUnionK d L 1 Tk.m₁ Tk.κ0) (2 * Tk.κdec - 1) Tk.κ0 Tk.κ' *
          (corrF0G Tk k β p₁ * K0 d L Tk.κ0 +
            (((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + C.m₀ + Tk.m₁)) ^ d) * P.E₀ *
          (2 * K0 d L Tk.κ0 * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * ((((L : ℝ) ^ (n₁ - 1)) ^ d))))) *
          Real.exp ((2 * Tk.κdec - 1) * (2 * (d : ℝ) * (L : ℝ) ^ C.m₀ *
            ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L)))) / (2 * (min Tk.t (η * P₀.eps d L k) / (4 * decMRG Tk k (β * (L : ℝ) ^ (k * (d - 2))) p₁))) *
              (((nFibre d L : ℕ) : ℝ) * Real.exp ((2 * Tk.κdec - 1) * cBr d L)) * K0 d L Tk.κ0 +
            ((nFibre d L : ℕ) : ℝ) * Real.exp (Tk.κ0 * cBr d L) * K0 d L Tk.κ0) → Φ e B) →
      ∃ e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := Tk.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
        Φ e B ∧
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
        ∀ ε : ℝ, ε ≤ Tk.t → ∀ q : Fld d L N₁ Tk.m₁ (k + 1) N × Fld d L N₁ Tk.m₁ (k + 1) N,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub N S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'), 0) T' else 0) := by
  have h3d : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hq0 : 0 < (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) := Real.rpow_pos_of_pos hLpos _
  have hq1 : (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < L)) (by linarith)
  have hαd : 2 * (((d : ℝ) - 2) / 2 - γ) < ((d - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; linarith
  obtain ⟨κmin, hlo, T₀, κdec, Q, F, η, hm0, hk0, hκ₀, hrate₀, hQdef, hQθ, hFdef, hηdef, hQ, hF,
    hη, H⟩ := StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_uniform_phi_formula d L N hd hL hN m₀ hA p hq0 hq1 (α := ((d : ℝ) - 2) / 2 - γ) hαd
  refine ⟨κmin, hlo, T₀, κdec, Q, F, η, hm0, hk0, hκ₀, hrate₀, hQdef, hQθ, hFdef, hηdef, hQ, hF, hη,
    fun P₀ hγ hα₀ hε1 => ?_⟩
  have hαP : P₀.alpha d = ((d : ℝ) - 2) / 2 - γ := by
    unfold Consts.alpha
    rw [hγ]
  obtain ⟨β₀, hβ₀, HC⟩ := H P₀.α₀ hα₀
  refine ⟨β₀, hβ₀, fun k hk => ?_⟩
  have hpos : ∀ j, 0 < P₀.eps d L j := fun j => by
    have := epsTail_pos j
    unfold Consts.eps epsSeq
    positivity
  have hgap : ∀ j, P₀.eps d L (j + 1) ≤ (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) * P₀.eps d L j := fun j => by
    have := classEpsG_gap (d := d) (L := L) hα₀.le j
    rwa [hαP] at this
  have hlow : ∀ j : ℕ, P₀.α₀ * (L : ℝ) ^ (-((((d : ℝ) - 2) / 2 - γ) * (j : ℝ))) ≤ P₀.eps d L j :=
    fun j => by
      have := classEpsG_lower (d := d) (L := L) hα₀.le j
      rwa [hαP] at this
  obtain ⟨Tk, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hTk0, hTm0, hC, hFl, hroom,
    Hk⟩ := HC (P₀.eps d L) (classEpsG_antitone hα₀.le (by rw [hαP]; linarith)) hpos hgap hlow hε1
    k hk
  refine ⟨Tk, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hTk0, hTm0, hC, hFl, hTt.ge,
    hroom, ?_⟩
  intro N₁ _ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ ϱ hϱ S hS
  obtain ⟨Jr, H'⟩ := Hk N₁ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ hϱ S hS
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7 s hs hidx hmin hCm
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, -, HG⟩ := @H' C z 𝒯E h𝒯 P Dom hm hcl hE₀ i₀ i₁ hdom XL 𝒦X
    hXL h𝒦 hopt hN hm7 s hs hidx hmin hCm
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, ?_⟩
  intro hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hE hεnum Φ hΦ
  exact @HG hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hE hεnum Φ
    (fun e B hc _ hb => hΦ e B hc hb)

open Classical in
/-- The class chain at the class radii, with `B` bounded by an explicit constant. -/
theorem e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_phi (m₀ : ℕ) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2) :
    ∃ (κmin : ℝ) (_ : stepHullMin ≤ κmin) (T₀ : StepTower κmin) (κdec Q F η : ℝ),
      4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ T₀.κ ∧
      (2 * T₀.κdec - 1) * (((3 : ℕ) : ℝ) ^ (m₀ - 1) + 2 * ((3 : ℕ) : ℝ) *
        ((3 : ℕ) : ℝ) ^ m₀ * ((((3 ^ (m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3) + 1 ≤ 2 * κdec ∧
      Q = 2 * composedCloseBound 3 3 2 T₀.m₁ T₀.BG T₀.κ (xiC1 3) 327 ∧
      xiK2 3 3 2 * Q ≤ (1 - (3 : ℝ) ^ (-(1 / 2 - γ))) / (2 * (3 : ℝ) ^ (-(1 / 2 - γ))) ∧
      F = 2 * (5 * cK2' 3 3 2 (famConst 3 3 T₀.BG₂ T₀.κ) + 1) ∧
      η = (1 - (3 : ℝ) ^ (-(1 / 2 - γ))) / (4 * xiK2 3 3 2 * F) ∧ 0 ≤ Q ∧ 0 < F ∧ 0 < η ∧
      ∀ P₀ : Consts, P₀.γ = γ → 0 < P₀.α₀ → P₀.eps 3 3 1 ≤ T₀.t → ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k), ∃ Tk : StepTower κmin, Tk.t = P₀.eps 3 3 (k + 1) ∧
        Tk.m₁ = T₀.m₁ ∧ Tk.c = T₀.c ∧ Tk.BG = T₀.BG ∧ Tk.κ = T₀.κ ∧ Tk.c₂ = T₀.c₂ ∧
        Tk.BG₂ = T₀.BG₂ ∧ Tk.δc = T₀.δc ∧ Tk.δ = T₀.δ ∧ Tk.δ' = T₀.δ' ∧
        ChainNum 3 3 2 Tk.m₁ Tk.BG Tk.κ 327 Tk.t (Q * Tk.t) ∧
        FlNum 3 3 2 Tk.BG Tk.BG₂ Tk.κ Tk.t (Q * Tk.t) (min Tk.t (η * P₀.eps 3 3 k))
          (F * min Tk.t (η * P₀.eps 3 3 k)) ∧
        -- the cover: the radius premise of `newLabels_castInputs` at `eps = Tk.t`
        P₀.eps 3 3 (k + 1) ≤ Tk.t ∧
        -- the room of the inherited labels at every level `j ≤ k`
        (∀ j ≤ k, Tk.t + xiK2 3 3 2 * (Q * Tk.t) +
          xiK2 3 3 2 * (F * min Tk.t (η * P₀.eps 3 3 k)) ≤ P₀.eps 3 3 j) ∧
      ∀ (N₁ : ℕ) [NeZero N₁] (_ : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (S : StepSetting 3 3 N₁ Tk.m₁ k 2 (rhoSep Tk.m₁))
        (_ : S = Tk.step k hk N₁ ν β p₁),
      ∃ Jr : S.JointRep Tk.t (2 * p₁),
      ∀ (C : StepClass 3 3 N₁ Tk.m₁ k 2 (rhoSep Tk.m₁)) (z : RootIdx 3 3 N₁ Tk.m₁ (k + 1))
        (𝒯E : Finset (ℕ × CTorus 3 3 N₁ Tk.m₁ (k + 1) × Set (CTorus 3 3 N₁ Tk.m₁ (k + 1))))
        (_ : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus 3 3 N₁ Tk.m₁ (k + 1) ×
            Set (CTorus 3 3 N₁ Tk.m₁ (k + 1))))).filter
          (fun τ => Aligned (3 ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
        {P : Consts} {Dom : FieldDom 3 3 N₁ Tk.m₁ (k + 1) 2 (rhoSep Tk.m₁)}
        (_ : P.m₀ = C.m₀) (_ : SFTermClauses P Dom C.Tm)
        (_ : 0 ≤ P.E₀) (i₀ i₁ : Fin 2)
        (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1)
            (rhoSep Tk.m₁), (∀ i, j < i → G.Ω i = ∅) →
          ∀ Ψ : Fld 3 3 N₁ Tk.m₁ (k + 1) 2, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin 2 → ℂ) i‖ ≤ ρ) →
          (∀ x x', jBlock 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) j x = jBlock 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) j x' →
            Ψ x = Ψ x') →
          Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
        (XL 𝒦X : {τ // τ ∈ 𝒯E} → Set (CTorus 3 3 N₁ Tk.m₁ (k + 1)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, XL τ = τ.1.2.2 ∪ box (cbase (cellSide 3 C.m₀ Tk.m₁ τ.1.1) τ.1.2.1 -
          natT fun _ => 3 / 2 * cellSide 3 C.m₀ Tk.m₁ τ.1.1) (3 * cellSide 3 C.m₀ Tk.m₁ τ.1.1))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ChosenOne C.m₀ τ.1.1 (XL τ) (𝒦X τ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∃ (W₀ : Finset (CTorus 3 3 N₁ Tk.m₁ (k + 1)))
          (E₀ : Finset (CTorus 3 3 N₁ Tk.m₁ (k + 1) × CTorus 3 3 N₁ Tk.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
            bondCost (scaleW 3 C.m₀ Tk.m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 (XL τ))
        (_ : 3 ^ C.m₀ ∣ N₁) (_ : 7 ≤ C.m₀) (_ : C.m₀ = m₀),
      ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) (rhoSep Tk.m₁))
        (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) (rhoSep Tk.m₁))
        (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus 3 3 N₁ Tk.m₁ (k + 1))),
        (∀ τ, (↑(X₁f τ) : Set (CTorus 3 3 N₁ Tk.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
        (∀ τ, BgSetting 2 S.G' (Gk τ) (Gj τ) S.a₁ S.ν Tk.c Tk.BG Tk.κ 327 Tk.t (Q * Tk.t) (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting 2 S.G' (Gk τ) (stepG 3 3 N₁ Tk.m₁ k (rhoSep Tk.m₁)) S.a₁ S.ν Tk.κ Tk.BG Tk.t (Q * Tk.t)
          (levelKc 3 3) (Cchi 3 3) Tk.c₂ Tk.BG₂ (min Tk.t (η * P₀.eps 3 3 k)) (F * min Tk.t (η * P₀.eps 3 3 k)) (X₁f τ)) ∧
        ∀
        -- the composed step data of the labels lie in the term domain, `Ψ(y)·Ψ(y)` in the slit plane
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) 2 →
            ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
              bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ Tk.m₁ k (rhoSep Tk.m₁)) S.a₁ S.ν Tk.BG Tk.κ Tk.t
            (X₁f τ) Tk.BG₂ (min Tk.t (η * P₀.eps 3 3 k)),
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ Tk.m₁ k (rhoSep Tk.m₁)) (compWeight 3 S.a₁) t.1.1
              t.2.1 t.2.2) →
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
            dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
        -- the per-label bounds of the irrelevant parts in `d(X)` at the composed step data
        -- (P1 (3.128), open)
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) 2 →
            ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
              bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ Tk.m₁ k (rhoSep Tk.m₁)) S.a₁ S.ν Tk.BG Tk.κ Tk.t
            (X₁f τ) Tk.BG₂ (min Tk.t (η * P₀.eps 3 3 k)),
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ Tk.m₁ k (rhoSep Tk.m₁)) (compWeight 3 S.a₁) t.1.1
              t.2.1 t.2.2) →
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
            Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
        {CI KL α₃ : ℝ} (n₁ : ℕ) (_ : 0 ≤ CI) (_ : 0 ≤ KL) (_ : 0 < α₃)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 + n₁ ≤ k →
          Bτ τ ≤ CI * P.E₀ * ((((3 : ℕ) : ℝ)⁻¹ ^ (k - τ.1.1)) ^ (((3 : ℕ) : ℝ) + α₃)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, k < τ.1.1 + n₁ → Bτ τ ≤ KL * P.E₀),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 Tk.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld 3 3 N₁ Tk.m₁ (k + 1) 2 × Fld 3 3 N₁ Tk.m₁ (k + 1) 2 =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- the smallness of the class constants against the marked radius
      (corrU / ((min Tk.t (η * P₀.eps 3 3 k)) / (2 * markedRad 3 3 2 k S.a₁ Tk.κ p₁
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          (((2 ^ 3 ^ 3 : ℕ) : ℝ) * (c1 3 3 * ((((3 : ℕ) : ℝ) ^ (1 + C.m₀ + Tk.m₁)) ^ 3 * P.E₀ *
          (2 * K0 3 3 Tk.κ0 * (CI * Real.exp ((κdec - 1) * cG 3 3) * (1 - ((3 : ℕ) : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG 3 3)) * ((((3 : ℕ) : ℝ) ^ (n₁ - 1)) ^ 3)))) *
          Real.exp ((2 * Tk.κdec - 1) * (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ C.m₀ *
            ((((3 ^ (C.m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3)))) ≤
          1 / (8 * (2 * (K0 3 3 Tk.κ0 + 1) + (K0 3 3 Tk.κ0 + rootUnionK 3 3 1 Tk.m₁ Tk.κ0) +
            rootUnionK 3 3 1 Tk.m₁ Tk.κ0) ^ 3 * c1 3 3 *
            Real.exp (((2 * Tk.κdec - 1) - 2 * Tk.κ0) * cG 3 3 + c1 3 3 + Tk.κ' * cG 3 3))) →
      (Φ : (physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := Tk.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) → ℝ → Prop) →
      (∀ (e : physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := Tk.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) (B : ℝ),
        -- the spin covariance of `e`
        (∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν Tk.t, ∀ θ' ∈ physV S S.a₁ S.ν Tk.t,
          (θ'.1 : RawData 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) 2) =
            rotRaw (cmat Q) (θ.1 : RawData 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) 2) →
          ∀ T', e θ' T' = e θ T') →
        B ≤ CPE 3 3 (2 * (K0 3 3 Tk.κ0 + 1) + (K0 3 3 Tk.κ0 + rootUnionK 3 3 1 Tk.m₁ Tk.κ0) +
          rootUnionK 3 3 1 Tk.m₁ Tk.κ0) (2 * Tk.κdec - 1) Tk.κ0 Tk.κ' *
          (corrF0 Tk k β p₁ * K0 3 3 Tk.κ0 +
            (((2 ^ 3 ^ 3 : ℕ) : ℝ) * (c1 3 3 * ((((3 : ℕ) : ℝ) ^ (1 + C.m₀ + Tk.m₁)) ^ 3 * P.E₀ *
          (2 * K0 3 3 Tk.κ0 * (CI * Real.exp ((κdec - 1) * cG 3 3) * (1 - ((3 : ℕ) : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG 3 3)) * ((((3 : ℕ) : ℝ) ^ (n₁ - 1)) ^ 3)))) *
          Real.exp ((2 * Tk.κdec - 1) * (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ C.m₀ *
            ((((3 ^ (C.m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3)))) / (2 * (min Tk.t (η * P₀.eps 3 3 k) / (4 * decMR Tk k (β * 3 ^ k) p₁))) *
              (((nFibre 3 3 : ℕ) : ℝ) * Real.exp ((2 * Tk.κdec - 1) * cBr 3 3)) * K0 3 3 Tk.κ0 +
            ((nFibre 3 3 : ℕ) : ℝ) * Real.exp (Tk.κ0 * cBr 3 3) * K0 3 3 Tk.κ0) → Φ e B) →
      ∃ e : physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := Tk.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
        Φ e B ∧
        (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1)
            Set.univ),
          AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν Tk.t) ∧
          (∀ θ ∈ physV S S.a₁ S.ν Tk.t, ∀ θ' ∈ physV S S.a₁ S.ν Tk.t,
            physRestrict (N := 2) (thickSet S.G' (Yhat Set.univ (sitesOf T')))
                (physIncl 2 S θ) =
              physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf T'))) (physIncl 2 S θ') →
            e θ T' = e θ' T') ∧
          (∀ θ ∈ physV S S.a₁ S.ν Tk.t, ‖e θ T'‖ ≤
            27 * covBLogMax 3 3 Tk.κ /
                (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp Tk.κ)) *
                Real.exp (-((Tk.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / 18) *
                  dExt T') +
              B * Real.exp (-Tk.κ' * dExt T')) ∧
          (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T'))) ∧
        (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 Tk.t D →
          Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
            (0 : CTorus 3 3 N₁ Tk.m₁ (k + 1) → Fin 2 → ℂ)) T' ∧
          (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub 2 S.G'), (0 : CTorus 3 3 N₁ Tk.m₁ (k + 1) → Fin 2 → ℂ)) T') ∧
        ∀ ε : ℝ, ε ≤ Tk.t → ∀ q : Fld 3 3 N₁ Tk.m₁ (k + 1) 2 × Fld 3 3 N₁ Tk.m₁ (k + 1) 2,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub 2 S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub 2 S.G'), 0) T' else 0) := by
  classical
  obtain ⟨κmin, hlo, T₀, κdec, Q, F, η, hm0, hk0, hκ₀, hrate₀, hQdef, hQθ, hFdef, hηdef, hQ, hF,
    hη, Hu⟩ := StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_phi 3 3 2 le_rfl le_rfl le_rfl m₀ hA p hγ0 hγ1
  have hcol : 4 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 3 + ((3 : ℕ) : ℝ) = 327 := by norm_num
  have hqq : (((3 : ℕ) : ℝ)) ^ (-((((3 : ℕ) : ℝ) - 2) / 2 - γ)) = (3 : ℝ) ^ (-(1 / 2 - γ)) := by
    norm_num
  rw [hcol] at hQdef
  rw [hqq] at hQθ hηdef
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num] at hQdef hFdef
  refine ⟨κmin, by rwa [stepHullMinG_three] at hlo, T₀.ofThree hk0 hm0, κdec, Q, F, η,
    by exact_mod_cast hκ₀, by exact_mod_cast hrate₀, hQdef, hQθ, hFdef, hηdef, hQ, hF, hη,
    fun P₀ hγ hα₀ hε1 => ?_⟩
  obtain ⟨β₀, hβ₀, HC⟩ := Hu P₀ hγ hα₀ hε1
  refine ⟨β₀, hβ₀, fun k hk => ?_⟩
  obtain ⟨Tk, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hTk0, hTm0, hC, hFl, hcov,
    hroom, Hcls⟩ := HC k hk
  rw [hcol] at hC
  have hm1 : Tk.m₀ = 1 := hTm0.trans hm0
  refine ⟨Tk.ofThree (hTk0.trans hk0) hm1, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ',
    hC, hFl, hcov, hroom, ?_⟩
  intro N₁ _ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ S hS
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have G := Hcls N₁ (by rw [hm1]; simpa using h3N) hN₁ ν hν0 (by simpa using hν) β hβ p₁ hp0
    (by rw [e]; exact hp₁) (ϱ := rhoSep Tk.m₁) (rhoSepG_three _).symm S hS
  obtain ⟨Jr, G'⟩ := G
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN₃ hm7 hCm
  have hidxG : (((5 * 3 + 13) * 3 ^ 4 : ℕ) : ℝ) +
      (4 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 3 + ((3 : ℕ) : ℝ)) * ((3 : ℕ) : ℝ) ≤
      (((3 - 2 : ℕ)) : ℝ) * ((3 : ℕ) : ℝ) ^ (C.m₀ + 1) := by
    have h := index_condition_shift_collar hm7 (show (327 : ℝ) ≤ 1431 by norm_num)
    rw [hcol]
    norm_num at h ⊢
    linarith
  have hminG : rhoSepG 3 3 Tk.m₁ ≤ Balaban.LargeField.minSep 3 (3 ^ (Tk.m₁ + 4)) := by
    rw [rhoSepG_three]; exact rhoSep_le_minSep_of_four Tk.m₁_four
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, G''⟩ := @G' C z 𝒯E h𝒯 P Dom hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN₃ (by omega) 4 (by omega) hidxG hminG hCm
  rw [hcol] at hBs
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, ?_⟩
  intro hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL
  have h27 : ∀ a b : ℝ, ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * ((2 : ℕ) : ℝ) * a / b) = 27 * a / b := by
    intro a b
    norm_num
    ring
  have h18 : (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = 18 := by norm_num
  simp only [e, h27, h18] at G''
  simp only [ofThree_corrF0, ofThree_decMR]
  exact @G'' hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL

open Classical in
/-- The class chain at the class radii of a general tower. -/
theorem StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_classEps (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
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
      ∀ P₀ : Consts, P₀.γ = γ → 0 < P₀.α₀ → P₀.eps d L 1 ≤ T₀.t → ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k), ∃ Tk : StepTowerG d L N κmin, Tk.t = P₀.eps d L (k + 1) ∧
        Tk.m₁ = T₀.m₁ ∧ Tk.c = T₀.c ∧ Tk.BG = T₀.BG ∧ Tk.κ = T₀.κ ∧ Tk.c₂ = T₀.c₂ ∧
        Tk.BG₂ = T₀.BG₂ ∧ Tk.δc = T₀.δc ∧ Tk.δ = T₀.δ ∧ Tk.δ' = T₀.δ' ∧ Tk.κ0 = T₀.κ0 ∧ Tk.m₀ = T₀.m₀ ∧
        ChainNum d L N Tk.m₁ Tk.BG Tk.κ (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) Tk.t (Q * Tk.t) ∧
        FlNum d L N Tk.BG Tk.BG₂ Tk.κ Tk.t (Q * Tk.t) (min Tk.t (η * P₀.eps d L k))
          (F * min Tk.t (η * P₀.eps d L k)) ∧
        -- the cover: the radius premise of `newLabels_castInputs` at `eps = Tk.t`
        P₀.eps d L (k + 1) ≤ Tk.t ∧
        -- the room of the inherited labels at every level `j ≤ k`
        (∀ j ≤ k, Tk.t + xiK2 d L N * (Q * Tk.t) +
          xiK2 d L N * (F * min Tk.t (η * P₀.eps d L k)) ≤ P₀.eps d L j) ∧
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
        {P : Consts} {Dom : FieldDom d L N₁ Tk.m₁ (k + 1) N ϱ}
        (_ : P.m₀ = C.m₀) (_ : SFTermClauses P Dom C.Tm)
        (_ : 0 ≤ P.E₀) (i₀ i₁ : Fin N)
        (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1)
            ϱ, (∀ i, j < i → G.Ω i = ∅) →
          ∀ Ψ : Fld d L N₁ Tk.m₁ (k + 1) N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
          (∀ x x', jBlock d L (N₁ * L ^ Tk.m₁) (k + 1) j x = jBlock d L (N₁ * L ^ Tk.m₁) (k + 1) j x' →
            Ψ x = Ψ x') →
          Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
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
        (_ : rhoSepG d L Tk.m₁ ≤ Balaban.LargeField.minSep L (L ^ (Tk.m₁ + s))) (_ : C.m₀ = m₀),
      ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1) ϱ)
        (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ Tk.m₁) (k + 1) ϱ)
        (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus d L N₁ Tk.m₁ (k + 1))),
        (∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ Tk.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
        (∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν Tk.c Tk.BG Tk.κ (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) Tk.t (Q * Tk.t) (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ Tk.m₁ k ϱ) S.a₁ S.ν Tk.κ Tk.BG Tk.t (Q * Tk.t)
          (levelKc d L) (Cchi d L) Tk.c₂ Tk.BG₂ (min Tk.t (η * P₀.eps d L k)) (F * min Tk.t (η * P₀.eps d L k)) (X₁f τ)) ∧
        ∀
        -- the composed step data of the labels lie in the term domain, `Ψ(y)·Ψ(y)` in the slit plane
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N →
            ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
              bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG d L N₁ Tk.m₁ k ϱ) S.a₁ S.ν Tk.BG Tk.κ Tk.t
            (X₁f τ) Tk.BG₂ (min Tk.t (η * P₀.eps d L k)),
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG d L N₁ Tk.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) →
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
            dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
        -- the per-label bounds of the irrelevant parts in `d(X)` at the composed step data
        -- (P1 (3.128), open)
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData d L (N₁ * L ^ Tk.m₁) (k + 1) N →
            ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
              bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG d L N₁ Tk.m₁ k ϱ) S.a₁ S.ν Tk.BG Tk.κ Tk.t
            (X₁f τ) Tk.BG₂ (min Tk.t (η * P₀.eps d L k)),
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG d L N₁ Tk.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) →
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
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
      (corrU / ((min Tk.t (η * P₀.eps d L k)) / (2 * markedRad d L N k S.a₁ Tk.κ p₁
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
        ∀ ε : ℝ, ε ≤ Tk.t → ∀ q : Fld d L N₁ Tk.m₁ (k + 1) N × Fld d L N₁ Tk.m₁ (k + 1) N,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub N S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'), 0) T' else 0) := by
  have h3d : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hq0 : 0 < (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) := Real.rpow_pos_of_pos hLpos _
  have hq1 : (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < L)) (by linarith)
  have hαd : 2 * (((d : ℝ) - 2) / 2 - γ) < ((d - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; linarith
  obtain ⟨κmin, hlo, T₀, κdec, Q, F, η, hm0, hk0, hκ₀, hrate₀, hQdef, hQθ, hFdef, hηdef, hQ, hF,
    hη, H⟩ := StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_uniform d L N hd hL hN m₀ hA p hq0 hq1 (α := ((d : ℝ) - 2) / 2 - γ) hαd
  refine ⟨κmin, hlo, T₀, κdec, Q, F, η, hm0, hk0, hκ₀, hrate₀, hQdef, hQθ, hFdef, hηdef, hQ, hF, hη,
    fun P₀ hγ hα₀ hε1 => ?_⟩
  have hαP : P₀.alpha d = ((d : ℝ) - 2) / 2 - γ := by
    unfold Consts.alpha
    rw [hγ]
  obtain ⟨β₀, hβ₀, HC⟩ := H P₀.α₀ hα₀
  refine ⟨β₀, hβ₀, fun k hk => ?_⟩
  have hpos : ∀ j, 0 < P₀.eps d L j := fun j => by
    have := epsTail_pos j
    unfold Consts.eps epsSeq
    positivity
  have hgap : ∀ j, P₀.eps d L (j + 1) ≤ (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) * P₀.eps d L j := fun j => by
    have := classEpsG_gap (d := d) (L := L) hα₀.le j
    rwa [hαP] at this
  have hlow : ∀ j : ℕ, P₀.α₀ * (L : ℝ) ^ (-((((d : ℝ) - 2) / 2 - γ) * (j : ℝ))) ≤ P₀.eps d L j :=
    fun j => by
      have := classEpsG_lower (d := d) (L := L) hα₀.le j
      rwa [hαP] at this
  obtain ⟨Tk, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hTk0, hTm0, hC, hFl, hroom,
    Hk⟩ := HC (P₀.eps d L) (classEpsG_antitone hα₀.le (by rw [hαP]; linarith)) hpos hgap hlow hε1
    k hk
  exact ⟨Tk, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hTk0, hTm0, hC, hFl, hTt.ge,
    hroom, Hk⟩

open Classical in
/-- **The decoupled class chain at the collar `327` at the class radii, one threshold `β₀` for
every scale.**  See the module doc-string. -/
theorem e0CoeffFamily_class_exists_tower_struct_step_collar_classEps (m₀ : ℕ) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2) :
    ∃ (κmin : ℝ) (_ : stepHullMin ≤ κmin) (T₀ : StepTower κmin) (κdec Q F η : ℝ),
      4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ T₀.κ ∧
      (2 * T₀.κdec - 1) * (((3 : ℕ) : ℝ) ^ (m₀ - 1) + 2 * ((3 : ℕ) : ℝ) *
        ((3 : ℕ) : ℝ) ^ m₀ * ((((3 ^ (m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3) + 1 ≤ 2 * κdec ∧
      Q = 2 * composedCloseBound 3 3 2 T₀.m₁ T₀.BG T₀.κ (xiC1 3) 327 ∧
      xiK2 3 3 2 * Q ≤ (1 - (3 : ℝ) ^ (-(1 / 2 - γ))) / (2 * (3 : ℝ) ^ (-(1 / 2 - γ))) ∧
      F = 2 * (5 * cK2' 3 3 2 (famConst 3 3 T₀.BG₂ T₀.κ) + 1) ∧
      η = (1 - (3 : ℝ) ^ (-(1 / 2 - γ))) / (4 * xiK2 3 3 2 * F) ∧ 0 ≤ Q ∧ 0 < F ∧ 0 < η ∧
      ∀ P₀ : Consts, P₀.γ = γ → 0 < P₀.α₀ → P₀.eps 3 3 1 ≤ T₀.t → ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k), ∃ Tk : StepTower κmin, Tk.t = P₀.eps 3 3 (k + 1) ∧
        Tk.m₁ = T₀.m₁ ∧ Tk.c = T₀.c ∧ Tk.BG = T₀.BG ∧ Tk.κ = T₀.κ ∧ Tk.c₂ = T₀.c₂ ∧
        Tk.BG₂ = T₀.BG₂ ∧ Tk.δc = T₀.δc ∧ Tk.δ = T₀.δ ∧ Tk.δ' = T₀.δ' ∧
        ChainNum 3 3 2 Tk.m₁ Tk.BG Tk.κ 327 Tk.t (Q * Tk.t) ∧
        FlNum 3 3 2 Tk.BG Tk.BG₂ Tk.κ Tk.t (Q * Tk.t) (min Tk.t (η * P₀.eps 3 3 k))
          (F * min Tk.t (η * P₀.eps 3 3 k)) ∧
        -- the cover: the radius premise of `newLabels_castInputs` at `eps = Tk.t`
        P₀.eps 3 3 (k + 1) ≤ Tk.t ∧
        -- the room of the inherited labels at every level `j ≤ k`
        (∀ j ≤ k, Tk.t + xiK2 3 3 2 * (Q * Tk.t) +
          xiK2 3 3 2 * (F * min Tk.t (η * P₀.eps 3 3 k)) ≤ P₀.eps 3 3 j) ∧
      ∀ (N₁ : ℕ) [NeZero N₁] (_ : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (S : StepSetting 3 3 N₁ Tk.m₁ k 2 (rhoSep Tk.m₁))
        (_ : S = Tk.step k hk N₁ ν β p₁),
      ∃ Jr : S.JointRep Tk.t (2 * p₁),
      ∀ (C : StepClass 3 3 N₁ Tk.m₁ k 2 (rhoSep Tk.m₁)) (z : RootIdx 3 3 N₁ Tk.m₁ (k + 1))
        (𝒯E : Finset (ℕ × CTorus 3 3 N₁ Tk.m₁ (k + 1) × Set (CTorus 3 3 N₁ Tk.m₁ (k + 1))))
        (_ : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus 3 3 N₁ Tk.m₁ (k + 1) ×
            Set (CTorus 3 3 N₁ Tk.m₁ (k + 1))))).filter
          (fun τ => Aligned (3 ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
        {P : Consts} {Dom : FieldDom 3 3 N₁ Tk.m₁ (k + 1) 2 (rhoSep Tk.m₁)}
        (_ : P.m₀ = C.m₀) (_ : SFTermClauses P Dom C.Tm)
        (_ : 0 ≤ P.E₀) (i₀ i₁ : Fin 2)
        (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1)
            (rhoSep Tk.m₁), (∀ i, j < i → G.Ω i = ∅) →
          ∀ Ψ : Fld 3 3 N₁ Tk.m₁ (k + 1) 2, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin 2 → ℂ) i‖ ≤ ρ) →
          (∀ x x', jBlock 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) j x = jBlock 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) j x' →
            Ψ x = Ψ x') →
          Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
        (XL 𝒦X : {τ // τ ∈ 𝒯E} → Set (CTorus 3 3 N₁ Tk.m₁ (k + 1)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, XL τ = τ.1.2.2 ∪ box (cbase (cellSide 3 C.m₀ Tk.m₁ τ.1.1) τ.1.2.1 -
          natT fun _ => 3 / 2 * cellSide 3 C.m₀ Tk.m₁ τ.1.1) (3 * cellSide 3 C.m₀ Tk.m₁ τ.1.1))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ChosenOne C.m₀ τ.1.1 (XL τ) (𝒦X τ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∃ (W₀ : Finset (CTorus 3 3 N₁ Tk.m₁ (k + 1)))
          (E₀ : Finset (CTorus 3 3 N₁ Tk.m₁ (k + 1) × CTorus 3 3 N₁ Tk.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
            bondCost (scaleW 3 C.m₀ Tk.m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 (XL τ))
        (_ : 3 ^ C.m₀ ∣ N₁) (_ : 7 ≤ C.m₀) (_ : C.m₀ = m₀),
      ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) (rhoSep Tk.m₁))
        (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) (rhoSep Tk.m₁))
        (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus 3 3 N₁ Tk.m₁ (k + 1))),
        (∀ τ, (↑(X₁f τ) : Set (CTorus 3 3 N₁ Tk.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
        (∀ τ, BgSetting 2 S.G' (Gk τ) (Gj τ) S.a₁ S.ν Tk.c Tk.BG Tk.κ 327 Tk.t (Q * Tk.t) (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting 2 S.G' (Gk τ) (stepG 3 3 N₁ Tk.m₁ k (rhoSep Tk.m₁)) S.a₁ S.ν Tk.κ Tk.BG Tk.t (Q * Tk.t)
          (levelKc 3 3) (Cchi 3 3) Tk.c₂ Tk.BG₂ (min Tk.t (η * P₀.eps 3 3 k)) (F * min Tk.t (η * P₀.eps 3 3 k)) (X₁f τ)) ∧
        ∀
        -- the composed step data of the labels lie in the term domain, `Ψ(y)·Ψ(y)` in the slit plane
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) 2 →
            ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
              bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ Tk.m₁ k (rhoSep Tk.m₁)) S.a₁ S.ν Tk.BG Tk.κ Tk.t
            (X₁f τ) Tk.BG₂ (min Tk.t (η * P₀.eps 3 3 k)),
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ Tk.m₁ k (rhoSep Tk.m₁)) (compWeight 3 S.a₁) t.1.1
              t.2.1 t.2.2) →
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
            dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
        -- the per-label bounds of the irrelevant parts in `d(X)` at the composed step data
        -- (P1 (3.128), open)
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) 2 →
            ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
              bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ Tk.m₁ k (rhoSep Tk.m₁)) S.a₁ S.ν Tk.BG Tk.κ Tk.t
            (X₁f τ) Tk.BG₂ (min Tk.t (η * P₀.eps 3 3 k)),
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ Tk.m₁ k (rhoSep Tk.m₁)) (compWeight 3 S.a₁) t.1.1
              t.2.1 t.2.2) →
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
            Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
        {CI KL α₃ : ℝ} (n₁ : ℕ) (_ : 0 ≤ CI) (_ : 0 ≤ KL) (_ : 0 < α₃)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 + n₁ ≤ k →
          Bτ τ ≤ CI * P.E₀ * ((((3 : ℕ) : ℝ)⁻¹ ^ (k - τ.1.1)) ^ (((3 : ℕ) : ℝ) + α₃)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, k < τ.1.1 + n₁ → Bτ τ ≤ KL * P.E₀),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 Tk.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld 3 3 N₁ Tk.m₁ (k + 1) 2 × Fld 3 3 N₁ Tk.m₁ (k + 1) 2 =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- the smallness of the class constants against the marked radius
      (corrU / ((min Tk.t (η * P₀.eps 3 3 k)) / (2 * markedRad 3 3 2 k S.a₁ Tk.κ p₁
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          (((2 ^ 3 ^ 3 : ℕ) : ℝ) * (c1 3 3 * ((((3 : ℕ) : ℝ) ^ (1 + C.m₀ + Tk.m₁)) ^ 3 * P.E₀ *
          (2 * K0 3 3 Tk.κ0 * (CI * Real.exp ((κdec - 1) * cG 3 3) * (1 - ((3 : ℕ) : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG 3 3)) * ((((3 : ℕ) : ℝ) ^ (n₁ - 1)) ^ 3)))) *
          Real.exp ((2 * Tk.κdec - 1) * (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ C.m₀ *
            ((((3 ^ (C.m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3)))) ≤
          1 / (8 * (2 * (K0 3 3 Tk.κ0 + 1) + (K0 3 3 Tk.κ0 + rootUnionK 3 3 1 Tk.m₁ Tk.κ0) +
            rootUnionK 3 3 1 Tk.m₁ Tk.κ0) ^ 3 * c1 3 3 *
            Real.exp (((2 * Tk.κdec - 1) - 2 * Tk.κ0) * cG 3 3 + c1 3 3 + Tk.κ' * cG 3 3))) →
      ∃ e : physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := Tk.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
        (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1)
            Set.univ),
          AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν Tk.t) ∧
          (∀ θ ∈ physV S S.a₁ S.ν Tk.t, ∀ θ' ∈ physV S S.a₁ S.ν Tk.t,
            physRestrict (N := 2) (thickSet S.G' (Yhat Set.univ (sitesOf T')))
                (physIncl 2 S θ) =
              physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf T'))) (physIncl 2 S θ') →
            e θ T' = e θ' T') ∧
          (∀ θ ∈ physV S S.a₁ S.ν Tk.t, ‖e θ T'‖ ≤
            27 * covBLogMax 3 3 Tk.κ /
                (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp Tk.κ)) *
                Real.exp (-((Tk.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / 18) *
                  dExt T') +
              B * Real.exp (-Tk.κ' * dExt T')) ∧
          (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T'))) ∧
        (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 Tk.t D →
          Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
            (0 : CTorus 3 3 N₁ Tk.m₁ (k + 1) → Fin 2 → ℂ)) T' ∧
          (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub 2 S.G'), (0 : CTorus 3 3 N₁ Tk.m₁ (k + 1) → Fin 2 → ℂ)) T') ∧
        ∀ ε : ℝ, ε ≤ Tk.t → ∀ q : Fld 3 3 N₁ Tk.m₁ (k + 1) 2 × Fld 3 3 N₁ Tk.m₁ (k + 1) 2,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub 2 S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub 2 S.G'), 0) T' else 0) := by
  classical
  obtain ⟨κmin, hlo, T₀, κdec, Q, F, η, hm0, hk0, hκ₀, hrate₀, hQdef, hQθ, hFdef, hηdef, hQ, hF,
    hη, Hu⟩ := StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_classEps 3 3 2 le_rfl le_rfl le_rfl m₀ hA p hγ0 hγ1
  have hcol : 4 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 3 + ((3 : ℕ) : ℝ) = 327 := by norm_num
  have hqq : (((3 : ℕ) : ℝ)) ^ (-((((3 : ℕ) : ℝ) - 2) / 2 - γ)) = (3 : ℝ) ^ (-(1 / 2 - γ)) := by
    norm_num
  rw [hcol] at hQdef
  rw [hqq] at hQθ hηdef
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num] at hQdef hFdef
  refine ⟨κmin, by rwa [stepHullMinG_three] at hlo, T₀.ofThree hk0 hm0, κdec, Q, F, η,
    by exact_mod_cast hκ₀, by exact_mod_cast hrate₀, hQdef, hQθ, hFdef, hηdef, hQ, hF, hη,
    fun P₀ hγ hα₀ hε1 => ?_⟩
  obtain ⟨β₀, hβ₀, HC⟩ := Hu P₀ hγ hα₀ hε1
  refine ⟨β₀, hβ₀, fun k hk => ?_⟩
  obtain ⟨Tk, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hTk0, hTm0, hC, hFl, hcov,
    hroom, Hcls⟩ := HC k hk
  rw [hcol] at hC
  have hm1 : Tk.m₀ = 1 := hTm0.trans hm0
  refine ⟨Tk.ofThree (hTk0.trans hk0) hm1, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ',
    hC, hFl, hcov, hroom, ?_⟩
  intro N₁ _ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ S hS
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have G := Hcls N₁ (by rw [hm1]; simpa using h3N) hN₁ ν hν0 (by simpa using hν) β hβ p₁ hp0
    (by rw [e]; exact hp₁) (ϱ := rhoSep Tk.m₁) (rhoSepG_three _).symm S hS
  obtain ⟨Jr, G'⟩ := G
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN₃ hm7 hCm
  have hidxG : (((5 * 3 + 13) * 3 ^ 4 : ℕ) : ℝ) +
      (4 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 3 + ((3 : ℕ) : ℝ)) * ((3 : ℕ) : ℝ) ≤
      (((3 - 2 : ℕ)) : ℝ) * ((3 : ℕ) : ℝ) ^ (C.m₀ + 1) := by
    have h := index_condition_shift_collar hm7 (show (327 : ℝ) ≤ 1431 by norm_num)
    rw [hcol]
    norm_num at h ⊢
    linarith
  have hminG : rhoSepG 3 3 Tk.m₁ ≤ Balaban.LargeField.minSep 3 (3 ^ (Tk.m₁ + 4)) := by
    rw [rhoSepG_three]; exact rhoSep_le_minSep_of_four Tk.m₁_four
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, G''⟩ := @G' C z 𝒯E h𝒯 P Dom hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN₃ (by omega) 4 (by omega) hidxG hminG hCm
  rw [hcol] at hBs
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, ?_⟩
  intro hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hE hεnum
  have h27 : ∀ a b : ℝ, ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * ((2 : ℕ) : ℝ) * a / b) = 27 * a / b := by
    intro a b
    norm_num
    ring
  have h18 : (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = 18 := by norm_num
  simp only [h27, h18] at G''
  exact @G'' hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hE hεnum

end Balaban.Inhabited
