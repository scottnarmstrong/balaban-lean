/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Chain
public import Balaban.Localization.DecoupledBackgroundLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The composite function of Lemma DL (background part) as an analytic function of the data

With `F₁` the analytic function of Theorem I-4b (`i4b_analytic`) and `F_k` that of Theorem 7.2
(`theorem72_analytic`), the composite
`𝒯(s; Θ) = 𝓔(X; ψ(𝔹_j(X), 𝔹_k(X); ψ(𝔹_k(X), 𝔹_{k+1}; Θ, s)))` is `Fan 𝓔 F₁ F_k X₁ Θ s`
(`D1raw`, `D2raw`); on the realizable data it is computed through `point_facts`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Matrix

section Fan

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂}

variable (Gp Gk Gj) in
/-- The raw datum of `𝔹_k(X)` obtained by composing the background field with `Θ = q.2`. -/
noncomputable def D1raw (a : ℕ → ℝ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (q : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N) : RawData d L (N₁ * L ^ m₁) K N :=
  (fun x i => composeField Gk Gp a (F₁ q).1 q.2.1 x i,
    fun x i => by classical exact if x ∈ Gk.Ω 1 then q.2.2 x i else 0)

variable (Gp Gk Gj) in
/-- The raw datum of `𝔹_j(X)` obtained by composing the background field of `𝔹_k(X)`. -/
noncomputable def D2raw (a : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (p : RawData d L (N₁ * L ^ m₁) K N) : RawData d L (N₁ * L ^ m₁) K N :=
  (fun x i => composeField Gj Gk a (Fk p).1 p.1 x i,
    fun x i => by classical exact if x ∈ Gj.Ω 1 then p.2 x i else 0)

theorem D1raw_rawOf (hP : Precedes Gk Gp) (a : ℕ → ℝ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (s : DecParams Gp) (D : BgData Gp N) :
    D1raw Gp Gk a F₁ (s, rawOf D) = rawOf (composeData hP a (F₁ (s, rawOf D)).1 D) := rfl

theorem D2raw_rawOf (hq : Precedes Gj Gk) (a : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (D : BgData Gk N) :
    D2raw Gk Gj a Fk (rawOf D) = rawOf (composeData hq a (Fk (rawOf D)).1 D) := rfl

/-- The numerical and geometric hypotheses of Lemma DL (background part). -/
structure BgSetting (N : ℕ) (Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁) (Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂)
    (a₁ ν c BG κ r₀ eps δ₃ : ℝ) (X₀ X₁f : Finset (CTorus d L N₁ m₁ K)) (j : ℕ) : Prop where
  hS : DecSpecs d L c BG
  Sp : DGSetting Gp (compWeight L a₁) ν
  ha₁ : 0 < a₁
  HBp : BgHyp d L K ϱ (compWeight L a₁) ν
  HBk : BgHyp d L K ϱ₁ (compWeight L a₁) ν
  HBj : BgHyp d L K ϱ₂ (compWeight L a₁) ν
  hP : Precedes Gk Gp
  hq : Precedes Gj Gk
  colk : ∀ z ∈ collar Gk, z ∈ Gp.Ω 1
  colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1
  hκ : 0 < κ
  hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁
  num : ChainNum d L N m₁ BG κ r₀ eps δ₃
  dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀
  hN : ∀ x ∈ X₀, x ∈ Gp.Ω 1 → ∀ y : CTorus d L N₁ m₁ K,
    Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y < r₀ * (L : ℝ) ^ m₁ * Gp.spacing x → y ∈ X₁f
  hr : r₀ * (L : ℝ) ^ m₁ ≤ ϱ - 1
  hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀
  dep : ∀ x ∈ dataSites Gk, ∀ y ∈ composeDep Gk Gp x, y ∈ X₁f
  hj : j ≤ K

variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}

/-- **The point facts of Lemma DL.**  For realizable data `Θ = D ∈ Ξ^c_K(𝔹_{k+1}; 1, ε')` and
`s` in the polydisc (`‖s_P‖ < e^κ`, `s = 1` off the parameter cubes) the composite is computed
through the analytic functions `F₁`, `F_k`, and its argument lies in `Ξ^c_j(𝔹_j(X); C₀, ε₂)`. -/
theorem point_facts (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
      s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D) :
    ∃ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ),
      IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α ∧ F₁ (s, rawOf D) = (φ, α) ∧
      XiCData Gk (compWeight L a₁) ν K 1 (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃)
        (composeData hB.hP (compWeight L a₁) φ D) ∧
      D1raw Gp Gk (compWeight L a₁) F₁ (s, rawOf D) =
        rawOf (composeData hB.hP (compWeight L a₁) φ D) ∧
      D2raw Gk Gj (compWeight L a₁) Fk (rawOf (composeData hB.hP (compWeight L a₁) φ D)) =
        rawOf (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) (composeData hB.hP (compWeight L a₁) φ D))
          (composeData hB.hP (compWeight L a₁) φ D)) ∧
      XiCData Gj (compWeight L a₁) ν j (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃)
        (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) (composeData hB.hP (compWeight L a₁) φ D))
          (composeData hB.hP (compWeight L a₁) φ D)) := by
  have hd0 : 0 < d := by have := hB.HBp.hd; omega
  have hκ0 := hB.hκ.le
  have hE1 : 1 ≤ Real.exp κ := Real.one_le_exp hκ0
  have hc1 := one_le_xiC1 d
  have hε := hB.num.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hDom := xiCData_inDomainC hB.HBp hB.num.small1 hD
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hB.num.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hB.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC hB.HBp hδ0 hδ0' hδ1 hDom
  have hsle : ∀ P, ‖s P‖ ≤ Real.exp κ := fun P => (hs P).le
  have hone : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ ≤ Real.exp κ := fun P => by
    simpa using hE1
  obtain ⟨φ, α, hI, -⟩ := i4b_exists_unique hB.hS hB.Sp hB.HBp hB.hκ.le hB.hM hsle hδ0 le_rfl
    hδ0' hδ1 hνε hDom
  obtain ⟨φ1, α1, hI1, -⟩ := i4b_exists_unique hB.hS hB.Sp hB.HBp hB.hκ.le hB.hM hone hδ0 le_rfl
    hδ0' hδ1 hνε hDom
  have hst := i5_stage1 hB.hS hB.Sp hB.ha₁ hB.HBp hB.HBk hB.hP hB.colk hB.hκ.le hB.hM hB.num
    hB.dsX₀ hB.hN hB.hr hB.hr₀ hsle hs1 hD hI hI1
  have hFeq : F₁ (s, rawOf D) = (φ, α) := hF₁ s D hs hU φ α hI
  have hD1 : D1raw Gp Gk (compWeight L a₁) F₁ (s, rawOf D) =
      rawOf (composeData hB.hP (compWeight L a₁) φ D) := by
    rw [D1raw_rawOf, hFeq]
  have hUk := xiCData_unionC hst
  have hFk' := hFk _ hUk
  refine ⟨φ, α, hI, hFeq, hst, hD1, ?_, ?_⟩
  · rw [D2raw_rawOf, hFk']
  · exact i5_stage2 hB.ha₁ hB.HBk hB.HBj hB.hq hB.colj hB.num.small₂ hB.num.th2 hB.hj hst

/-- At `s ≡ 1` the decoupled background field is the background field of Theorem 5.2. -/
theorem decBg_one_eq (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D) {φ : Gp.Ω 1 × Fin N → ℂ} {α : Gp.Ω 1 → ℂ}
    (h1 : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) (fun _ => 1) D φ α) :
    bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D = φ := by
  have hd0 : 0 < d := by have := hB.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hB.num.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hDom := xiCData_inDomainC hB.HBp hB.num.small1 hD
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hB.num.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hB.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  exact (i4b_one hB.hS hB.Sp hB.HBp hB.hκ.le hB.hM hδ0 le_rfl hδ0' hδ1 hνε hDom h1).2.1

end Fan

end Balaban.Localization
