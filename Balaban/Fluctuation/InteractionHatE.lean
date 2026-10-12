/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionHatLC
public import Balaban.Fluctuation.InteractionHatF
public import Balaban.Fluctuation.InteractionETerm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The `δ𝓔'`-part of the localized interaction in the variable `ψ̂`

An old term `E` of the effective action, composed with the fluctuation datum, is a functional of
the decoupled objects: with `(φ, α) = F₁(s, Θ)` and `δφ = Sol(s, …)`,

`E(D2raw (D1rawFl F₁ Sol s (Θ, ψ')))`, `D1rawFl = (composeField φ Ψ + composeField δφ ψ', h)`,

so it is `Φ_E(φ, δφ, (Θ, ψ'))` with `Φ_E` analytic on the realizable triples with layer-constant
fluctuation (`eTermFun_analytic`).  `i5_functional_hatLC` expands it with terms local in `ψ̂`
(`eterm_locInt_hat`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix Set Metric

section EHat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

variable (Gp Gk Hm) in
/-- The raw datum of `𝔹_k(X)` composed from the triple `(φ, δφ, (Θ, ψ'))`:
`ψ(𝔹_k(X), 𝔹_{k+1}; Θ) + δψ(𝔹_k(X), 𝔹_k; ψ')` (`D1rawFl` with the objects of the triple). -/
noncomputable def d1Triple (a : ℕ → ℝ) (φ : Gp.Ω 1 × Fin N → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ)
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) :
    RawData d L (N₁ * L ^ m₁) (k + 1) N :=
  (fun x i => composeField Gk Gp a φ u.1.1 x i + composeField Gk Hm a δφ u.2 x i,
    fun x i => by classical exact if x ∈ Gk.Ω 1 then u.1.2 x i else 0)

variable (Gp Gk Gj Hm) in
/-- **An old term as a functional of the decoupled objects**:
`Φ_E(φ, δφ, (Θ, ψ')) = E(D2raw Fk (d1Triple φ δφ (Θ, ψ')))`. -/
noncomputable def eTermFun (a : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) :
    ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ :=
  fun pa δφ u => E (D2raw Gk Gj a Fk (d1Triple Gp Gk Hm a pa.1 δφ u))

theorem d1Triple_D1rawFl (a : ℕ → ℝ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (s : Dec2.DecParams (coverOf Gp))
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) :
    D1rawFl Gp Gk Hm a F₁ Sol s u =
      d1Triple Gp Gk Hm a (F₁ (s, u.1)).1 (Sol (s, flEdat Gp Hm (F₁ (s, u.1)) u.1.1 u.2)).1 u :=
  rfl

end EHat

section Chain

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The triple of a datum at `s ≡ 1` is realizable**: for `D ∈ Ξ^c` and a layer-constant
fluctuation `ψ'` in the ball, `((bgFieldC D, bgMultC D), flFieldOne D ψ', (Θ, ψ')) ∈ FlRealLC`. -/
theorem triple_one_mem (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hψ : ψ' ∈ FlBallLC Hm δ₁) :
    ((bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D),
      flFieldOne Gp Hm BG₂ κ a₁ ν D ψ', (rawOf D, ψ')) ∈
      FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ := by
  classical
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  obtain ⟨F₁, -, hF₁⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  obtain ⟨Sol, -, hSolprop⟩ := Dec2.i4a_analytic (N := N) hC.hS2.fam hC.hS2.an
    hC.SM.toCoverBase hC.hκ.le hC.hM2 false hB0 hC.δ₁_pos.le hC.B_le hC.δ₁_le
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ :=
    fun P => by simpa using hE1
  have hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
      (fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) ⟨P, hP⟩ = 1 := fun P hP hPn => rfl
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
    point_facts_core hC hF₁ hSolprop hsx hs1 hD hψ.1
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  obtain ⟨-, hφ1, hα1⟩ := i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ0 le_rfl hδ0' hδ1
    hνε hDom hI
  obtain ⟨hfld, hfix, hs6, -, -, huniq⟩ := hSolprop ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
    flEdat Gp Hm (φ, α) D.Ψ ψ') hsx hstrict
  have hmult := flMult_spec (C := coverOf Gp) (Hm := Hm) (a := compWeight L a₁) (ν := ν)
    (ρ := c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) (s := fun _ : ↥(cubeIdx Gp) => (1 : ℂ))
    (e := flEdat Gp Hm (φ, α) D.Ψ ψ') ⟨hs6, hfix⟩ (fun δα' h => huniq δα' h.1 h.2)
  have hfl : flFieldOne Gp Hm BG₂ κ a₁ ν D ψ' = δφ := by
    have hSol1 : (Sol ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
        flEdat Gp Hm (φ, α) D.Ψ ψ')).1 = δφ := congrArg Prod.fst hSeq
    unfold flFieldOne flField
    rw [hφ1, hα1]
    exact (congrArg (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν
      (fun _ : ↥(cubeIdx Gp) => (1 : ℂ))) (flEdat Gp Hm (φ, α) D.Ψ ψ').2.1
      (flEdat Gp Hm (φ, α) D.Ψ ψ').1 (pertSource Hm (compWeight L a₁)
      (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.1 (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.2)) hmult).trans
      (hfld.symm.trans hSol1)
  rw [hφ1, hα1, hfl]
  exact ⟨hmem, hψ.2⟩

end Chain

section ChainE

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The facts at a realizable triple with layer-constant fluctuation**: the composed datum of
`𝔹_k(X)` is the datum `flDatum`, in `Ξ^c`, its background composition lies in `Ξ^c(𝔹_j(X))`. -/
theorem eTerm_chain (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (ht : t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :
    ∃ (D : BgData Gp N) (ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
      (hlc : IsLayerConstant Hm ψ'), t.2.2 = (rawOf D, ψ') ∧
      XiCData Gk (compWeight L a₁) ν (k + 1) 1
        (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
        (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc) ∧
      d1Triple Gp Gk Hm (compWeight L a₁) t.1.1 t.2.1 t.2.2 =
        rawOf (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc) ∧
      D2raw Gk Gj (compWeight L a₁) Fk
          (rawOf (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc)) =
        rawOf (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc))
          (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc)) ∧
      XiCData Gj (compWeight L a₁) ν j (scaledC0 d)
        (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
        (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc))
          (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc)) := by
  classical
  obtain ⟨⟨s, D, ψ', δα, hs, hs1, hD, hψ, hI, ht22, hδ, hfix, hsm1, hsm2, hsup⟩, hlc⟩ := ht
  have hlc' : IsLayerConstant Hm ψ' := by rw [ht22] at hlc; exact hlc
  have hd0 : 0 < d := by have := hB.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hB.num.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hB.hS.fam.2.1 hd0).le hδ0.le)
  obtain ⟨F₁, -, hF₁⟩ := i4b_analytic hB.hS hB.Sp hB.HBp hB.hκ.le hB.hM
  obtain ⟨Sol, -, hSolprop⟩ := Dec2.i4a_analytic (N := N) hF.hS2.fam hF.hS2.an
    hF.SM.toCoverBase hB.hκ.le hF.hM2 false hB0 hF.num.δ₁_pos.le hF.num.B_le hF.num.δ₁_le
  obtain ⟨φ, α, δφ, hI', hFeq, hstrict, hδφ, hX3, hrawD, hD2, hX2⟩ :=
    point_facts_fl hB hF hF₁ hFk hSolprop hs hs1 hD hψ hlc'
  have hDom := xiCData_inDomainC hB.HBp hB.num.small1 hD
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hB.num.c7le.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC hB.HBp hδ0 hδ0' hB.num.c7le hDom
  have h1 : (φ, α) = t.1 := hFeq.symm.trans (hF₁ s D hs hU t.1.1 t.1.2 hI)
  have hφt : t.1.1 = φ := (congrArg Prod.fst h1).symm
  have hαt : t.1.2 = α := (congrArg Prod.snd h1).symm
  have hδt : t.2.1 = δφ := by
    have ht1 : t.1 = (φ, α) := h1.symm
    obtain ⟨hfld, -, -, -, -, huniq⟩ := hSolprop (s, flEdat Gp Hm (φ, α) D.Ψ ψ') hs hstrict
    rw [ht1] at hδ hfix
    have hδα : δα = (Sol (s, flEdat Gp Hm (φ, α) D.Ψ ψ')).2 := huniq δα hsm1 hfix
    rw [hδ, hδα, ← hfld]
    exact hδφ
  refine ⟨D, ψ', hlc', ht22, ?_⟩
  rw [hφt, hδt]
  refine ⟨hX3, ?_, hD2, hX2⟩
  rw [ht22, ← hrawD]
  change _ = d1Triple Gp Gk Hm (compWeight L a₁) (F₁ (s, rawOf D)).1
    (Sol (s, flEdat Gp Hm (F₁ (s, rawOf D)) D.Ψ ψ')).1 (rawOf D, ψ')
  rw [hFeq, hδφ]

end ChainE

section Props

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **Analyticity of the old-term functional on the realizable triples.** -/
theorem eTermFun_analytic (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hE : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl))) :
    AnalyticOnNhd ℂ (fun t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =>
      eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2)
      (FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) := by
  classical
  intro t ht
  obtain ⟨D, ψ', hlc, ht22, hX3, hD1, hD2, hX2⟩ := eTerm_chain hB hF hFk ht
  set g : (((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N :=
    fun t' => d1Triple Gp Gk Hm (compWeight L a₁) t'.1.1 t'.2.1 t'.2.2 with hg
  have hφ : ∀ r, AnalyticAt ℂ (fun q : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) × (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) => q.1.1 r) t := fun r =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Gp.Ω 1 × Fin N => ℂ) r).analyticAt _).comp
      (analyticAt_fst.comp analyticAt_fst)
  have hδ : ∀ r, AnalyticAt ℂ (fun q : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) × (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) => q.2.1 r) t := fun r =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Hm.Ω 1 × Fin N => ℂ) r).analyticAt _).comp
      (analyticAt_fst.comp analyticAt_snd)
  have hΨ : ∀ y jj, AnalyticAt ℂ (fun q : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) × (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) => q.2.2.1.1 y jj) t := fun y jj =>
    (analyticAt_rawΨ y jj t.2.2.1).comp_of_eq
      (analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)) rfl
  have hψ : ∀ y jj, AnalyticAt ℂ (fun q : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) × (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) => q.2.2.2 y jj) t := fun y jj =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) jj).analyticAt _).comp
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ (k + 1) =>
        Fin N → ℂ) y).analyticAt _).comp (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)))
  have ha2 : AnalyticAt ℂ g t := by
    refine AnalyticAt.prod (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
      (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
    · exact (analyticAt_composeField (G := Gk) (G' := Gp) (q := t) (compWeight L a₁)
        (fun q => q.1.1) (fun q => q.2.2.1.1) hφ hΨ x i).add
        (analyticAt_composeField (G := Gk) (G' := Hm) (q := t) (compWeight L a₁)
        (fun q => q.2.1) (fun q => q.2.2.2) hδ hψ x i)
    · by_cases hx : x ∈ Gk.Ω 1
      · simp only [hx, ↓reduceIte]
        exact (analyticAt_rawh x i t.2.2.1).comp_of_eq
          (analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)) rfl
      · simp only [hx, ↓reduceIte]
        exact analyticAt_const
  have hmem : g t ∈ {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)} :=
    ⟨_, xiCData_unionC hX3, hD1⟩
  have ha3 : AnalyticAt ℂ (fun q => Fk (g q)) t := (hFkan _ hmem).comp ha2
  have ha4 : AnalyticAt ℂ (fun q => D2raw Gk Gj (compWeight L a₁) Fk (g q)) t :=
    analyticAt_D2raw (Gj := Gj) (compWeight L a₁) Fk g ha2 ha3
  refine (hE _ ?_).comp ha4
  show D2raw Gk Gj (compWeight L a₁) Fk (d1Triple Gp Gk Hm (compWeight L a₁) t.1.1 t.2.1 t.2.2) ∈ _
  rw [hD1, hD2]
  exact ⟨_, hX2, rfl⟩

/-- **The bound of the old-term functional on the realizable triples.** -/
theorem eTermFun_bound (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ} {B : ℝ}
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ‖E r‖ ≤ B)
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (ht : t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :
    ‖eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2‖ ≤ B := by
  obtain ⟨D, ψ', hlc, ht22, hX3, hD1, hD2, hX2⟩ := eTerm_chain hB hF hFk ht
  show ‖E (D2raw Gk Gj (compWeight L a₁) Fk
    (d1Triple Gp Gk Hm (compWeight L a₁) t.1.1 t.2.1 t.2.2))‖ ≤ B
  rw [hD1, hD2]
  exact hEb _ ⟨_, hX2, rfl⟩

/-- **Locality of the old-term functional**: it reads `φ`, `δφ`, `Ψ`, `h` and `ψ'` only at the
dependency sets of the data sites of `𝔹_k(X)`, which lie in `X₁`. -/
theorem eTermFun_local (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {t t' : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (hφ : ∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) →
      ∀ i, t.1.1 (y, i) = t'.1.1 (y, i))
    (hδ : ∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) →
      ∀ i, t.2.1 (y, i) = t'.2.1 (y, i))
    (hag : agreeOn (thickSet Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))) t.2.2.1 t'.2.2.1)
    (hψ : ∀ y ∈ psiThick (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))), t.2.2.2 y = t'.2.2.2 y) :
    eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2 =
      eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t'.1 t'.2.1 t'.2.2 := by
  classical
  have hX₁Ω : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(Gp.Ω 1) := fun x hx =>
    X1_subset_Omega1 hcov (hX₁ ▸ hx)
  have hXthick : ∀ y ∈ X₁f, t.2.2.1.1 y = t'.2.2.1.1 y ∧ t.2.2.1.2 y = t'.2.2.1.2 y := fun y hy =>
    hag y (Or.inl (Finset.mem_coe.2 hy))
  refine congrArg E (congrArg (D2raw Gk Gj (compWeight L a₁) Fk) ?_)
  refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
  · show composeField Gk Gp (compWeight L a₁) t.1.1 t.2.2.1.1 x i +
        composeField Gk Hm (compWeight L a₁) t.2.1 t.2.2.2 x i =
      composeField Gk Gp (compWeight L a₁) t'.1.1 t'.2.2.1.1 x i +
        composeField Gk Hm (compWeight L a₁) t'.2.1 t'.2.2.2 x i
    by_cases hx : x ∈ dataSites Gk
    · congr 1
      · refine composeField_congr (G := Gk) (G' := Gp) (compWeight L a₁) (fun y hy jj => ?_)
          (fun jj => congrFun (hXthick x (hB.dep x hx x (self_mem_composeDep x))).1 jj) i
        have hyX := hB.dep x hx y hy
        have hyΩ : y ∈ Gp.Ω 1 := hX₁Ω (Finset.mem_coe.2 hyX)
        rw [svec_of_mem' t.1.1 hyΩ jj, svec_of_mem' t'.1.1 hyΩ jj]
        exact hφ ⟨y, hyΩ⟩ (Finset.mem_coe.2 hyX) jj
      · refine composeField_congr (G := Gk) (G' := Hm) (compWeight L a₁) (fun y hy jj => ?_)
          (fun jj => congrFun (hψ x (Or.inl (Finset.mem_coe.2 (hF.depm x hx x
            (self_mem_composeDep x))))) jj) i
        have hyX := hF.depm x hx y hy
        by_cases hyΩ : y ∈ Hm.Ω 1
        · rw [svec_of_mem' t.2.1 hyΩ jj, svec_of_mem' t'.2.1 hyΩ jj]
          exact hδ ⟨y, hyΩ⟩ (Finset.mem_coe.2 hyX) jj
        · rw [svec_of_not_mem Hm t.2.1 hyΩ jj, svec_of_not_mem Hm t'.2.1 hyΩ jj]
    · rw [composeField_of_not_mem _ _ _ hx, composeField_of_not_mem _ _ _ hx,
        composeField_of_not_mem _ _ _ hx, composeField_of_not_mem _ _ _ hx]
  · show (if x ∈ Gk.Ω 1 then t.2.2.1.2 x i else 0) = (if x ∈ Gk.Ω 1 then t'.2.2.1.2 x i else 0)
    by_cases hx : x ∈ Gk.Ω 1
    · simp only [hx, ↓reduceIte]
      have hxd : x ∈ dataSites Gk := (mem_dataSites Gk).2 (Or.inl hx)
      exact congrFun (hXthick x (hB.dep x hxd x (self_mem_composeDep x))).2 i
    · simp [hx]

end Props

section Value

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The old-term functional at the triple of a datum is the composite `flComp`.** -/
theorem eTermFun_value (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hψ : ψ' ∈ FlBallLC Hm δ₁) :
    eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
          bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
        (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') (rawOf D, ψ') =
      flComp hB hF E (rawOf D, ψ') := by
  classical
  have hC := flCore_of hB hF
  have hmem := triple_one_mem (X₁f := X₁f) hC hD hψ
  obtain ⟨D', ψ'', hlc, ht22, -, hD1, hD2, -⟩ := eTerm_chain hB hF hFk hmem
  obtain ⟨hr, hψe⟩ := Prod.mk.inj ht22
  have hDD : D = D' := BgData.eq_of_raw hr
  subst hDD
  subst hψe
  rw [flComp_rawOf hB hF E hD hψ.2]
  show E (D2raw Gk Gj (compWeight L a₁) Fk (d1Triple Gp Gk Hm (compWeight L a₁) _ _ _)) = _
  rw [hD1, hD2]
  rfl

end Value

section EngineE

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **An old term along the fluctuation expands over the domains `Y ⊃ X₁`, with terms local in
`ψ̂`** (the hat version of `i5_fluct`). -/
theorem eterm_expansion_hat (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X)) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        flComp hB hF E (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHat hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  classical
  obtain ⟨Fk, hFkan, hFk⟩ := theorem72_analytic (G := Gk) (a := compWeight L a₁) (ν := ν) hB.HBk
  have hC := flCore_of hB hF
  obtain ⟨Ev, h1', h2', h3', h4'⟩ := i5_functional_hatLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁
    hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb
    (Φ := eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E)
    (eTermFun_analytic hB hF hFkan hFk hEan)
    (fun t ht => eTermFun_bound hB hF hFk hEbd ht)
    (Z := ↑X₁f) (Zα := ∅) subset_rfl (fun x hx => absurd hx (Set.notMem_empty x))
    (fun t _ t' _ hφ _ hδ hag hψ => eTermFun_local hB hF hcov hX₁ Fk E hφ hδ hag hψ)
  refine ⟨Ev, fun D hD ψh hψh => ?_, h2', h3', h4'⟩
  rw [← h1' D hD ψh hψh]
  exact (eTermFun_value hB hF hFk E hD
    (hatLift_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hD hψh)).symm

end EngineE

section ELoc

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The `δ𝓔'`-term of one old term in the variable `ψ̂`** (hat version of `eterm_locInt`). -/
theorem eterm_locInt_hat (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp hB hF E)) ω x₀ w σ Θ)
        (fun Y => Mω * ((Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X
          - 2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
  classical
  obtain ⟨Ev, hsum, hloc, hbd, hanY⟩ := eterm_expansion_hat hB hF hk hG hG' cc hcψ hMX hdm hα hsm
    hδ₁ hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb hEan hEbd
  refine ⟨Ev, ?_⟩
  exact locInt_dir1 (S := XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
    (B := hatBall (N := N) Gp cψ)
    (f := hatFun Gp a₁ ν eps hG' cc (flComp hB hF E))
    (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
      (X1 Gp m₀ j 𝒦X)) (Evs := Ev)
    (b := fun Y => Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y))
    (AgΘ := fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
    (AgF := AgHatF Gp hG') (Rσ := Rσ) hR₁ hω hωc hMω hωb hr
    (isOpen_hatBall cψ) (fun Y => (hanY Y).mono (Set.prod_mono le_rfl (hatBall_subset cψ)))
    (fun Y u hu => hbd Y u ⟨hu.1, hatBall_subset cψ hu.2⟩)
    (fun Y a a' c' c'' p q ha hb y hy i => by simp [ha y hy i, hb y hy i])
    (fun Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2' =>
      hloc Y (Θ, z) ⟨hΘ, hatBall_subset cψ hz⟩ (Θ', z') ⟨hΘ', hatBall_subset cψ hz'⟩ ⟨h1', h2'⟩)
    (fun Θ hΘ ψh hψ => by
      obtain ⟨D, hD, rfl⟩ := hΘ
      rw [hatFun_rawOf hG' cc _ hD]
      exact hsum D hD ψh (hatBall_subset cψ hψ))

end ELoc

section EFamily

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps : ℝ}

/-- **The `δ𝓔'`-part for a finite family of old terms, in the variable `ψ̂`** (hat version of
`eterms_locInt`). -/
theorem eterms_locInt_hat {τι : Type*} [DecidableEq τι] (𝒯 : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {Gk : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {Gj : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
    {r₀ δ₃ : ℝ} {X₀ X₁f : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {j m₀ : τι → ℕ}
    {X 𝒦X : τι → Set (CTorus d L N₁ m₁ (k + 1))} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (hB : ∀ τ ∈ 𝒯, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (j τ))
    (hF : ∀ τ ∈ 𝒯, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : ∀ τ ∈ 𝒯, CovSetup Gp (m₀ τ) (j τ) (X τ) (𝒦X τ))
    (hX₁ : ∀ τ ∈ 𝒯, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ τ) (j τ) (𝒦X τ))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ τ ∈ 𝒯, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X τ) ∧ MeetsOne (m₀ τ) (j τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L (m₀ τ) m₁ (j τ)) E₀ = treeLenCovOne (m₀ τ) (j τ) (X τ))
    {κdec κ₀ : ℝ} {Eb : τι → ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ τ ∈ 𝒯, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ τ) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hEb : ∀ τ ∈ 𝒯, 0 ≤ Eb τ) {E : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (E τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ ∈ 𝒯, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E τ r‖ ≤ Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀ τ) (j τ) (X τ)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (𝒴 : τι → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : τι → Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯.biUnion 𝒴)
        (fun Y x₀ w σ Θ => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then T τ Y x₀ w σ Θ else 0)
        (fun x₀ w σ Θ => ∑ τ ∈ 𝒯, if h : τ ∈ 𝒯 then
          dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ Θ
          else 0)
        (fun Y => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne (m₀ τ) (j τ)
          (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r) else 0)
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
  classical
  have hex : ∀ τ, ∃ (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ), τ ∈ 𝒯 →
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp (m₀ τ) (X1 Gp (m₀ τ) (j τ) (𝒦X τ)))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => if h : τ ∈ 𝒯 then
          dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ Θ
          else 0)
        (fun Y => Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne (m₀ τ) (j τ)
          (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
    intro τ
    by_cases hτ : τ ∈ 𝒯
    · obtain ⟨Ev, hEv⟩ := eterm_locInt_hat (hB τ hτ) (hF τ hτ) hk hG hG' cc hcψ hMX hdm hα hsm hδ₁
        (hcov τ hτ) (hX₁ τ hτ) hconn hrow (hopt τ hτ) hκ₀ hκdec hκ h1 (hlog τ hτ) (hEb τ hτ)
        (hEan τ hτ) (hEbd τ hτ) hωc hR₁ hω hMω hωb hr (Rσ := Rσ)
      exact ⟨Ev, fun _ => by simpa [hτ] using hEv⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hτ⟩
  choose Ev hEv using hex
  exact ⟨fun τ => polymerDomains (fun i : ParIdx Gp (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =>
      i.1.1) Gp (m₀ τ) (X1 Gp (m₀ τ) (j τ) (𝒦X τ)),
    fun τ Y x₀ w σ Θ => dirTerm (Ev τ Y) ω x₀ w σ Θ, LocInt.finsum 𝒯 (fun τ hτ => hEv τ hτ)⟩

/-- **The `𝓜`-terms of the source along the fluctuation, in the variable `ψ̂`** (hat version of
`mterms_locInt`). -/
theorem mterms_locInt_hat {τι : Type*} [DecidableEq τι] (𝒯 : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {Gk : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {Gj : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
    {r₀ δ₃ : ℝ} {X₀ X₁f : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {j m₀ : τι → ℕ}
    {X 𝒦X : τι → Set (CTorus d L N₁ m₁ (k + 1))} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (ys : τι → CTorus d L N₁ m₁ (k + 1)) (is : τι → Fin N) (hys : ∀ τ ∈ 𝒯, ys τ ∈ X₁f τ)
    (hB : ∀ τ ∈ 𝒯, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (j τ))
    (hF : ∀ τ ∈ 𝒯, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : ∀ τ ∈ 𝒯, CovSetup Gp (m₀ τ) (j τ) (X τ) (𝒦X τ))
    (hX₁ : ∀ τ ∈ 𝒯, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ τ) (j τ) (𝒦X τ))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ τ ∈ 𝒯, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X τ) ∧ MeetsOne (m₀ τ) (j τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L (m₀ τ) m₁ (j τ)) E₀ = treeLenCovOne (m₀ τ) (j τ) (X τ))
    {κdec κ₀ : ℝ} {Eb : τι → ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ τ ∈ 𝒯, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ τ) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hEb : ∀ τ ∈ 𝒯, 0 ≤ Eb τ) {E : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (E τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ ∈ 𝒯, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E τ r‖ ≤ Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀ τ) (j τ) (X τ)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (𝒴 : τι → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : τι → Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯.biUnion 𝒴)
        (fun Y x₀ w σ p => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then p.2 (ys τ) (is τ) * T τ Y x₀ w σ p.1 else 0)
        (fun x₀ w σ p => ∑ τ ∈ 𝒯, if h : τ ∈ 𝒯 then
          p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
            (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ p.1 else 0)
        (fun Y => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then 1 * (Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne
          (m₀ τ) (j τ) (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r)) else 0)
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (AgHatF Gp hG') := by
  classical
  have hex : ∀ τ, ∃ (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ), τ ∈ 𝒯 →
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp (m₀ τ) (X1 Gp (m₀ τ) (j τ) (𝒦X τ)))
        (fun Y x₀ w σ p => p.2 (ys τ) (is τ) * dirTerm (Ev Y) ω x₀ w σ p.1)
        (fun x₀ w σ p => if h : τ ∈ 𝒯 then
          p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
            (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ p.1 else 0)
        (fun Y => 1 * (Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne (m₀ τ) (j τ)
          (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r)))
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (AgHatF Gp hG') := by
    intro τ
    by_cases hτ : τ ∈ 𝒯
    · obtain ⟨Ev, hEv⟩ := eterm_locInt_hat (hB τ hτ) (hF τ hτ) hk hG hG' cc hcψ hMX hdm hα hsm hδ₁
        (hcov τ hτ) (hX₁ τ hτ) hconn hrow (hopt τ hτ) hκ₀ hκdec hκ h1 (hlog τ hτ) (hEb τ hτ)
        (hEan τ hτ) (hEbd τ hτ) hωc hR₁ hω hMω hωb hr (Rσ := Rσ)
      refine ⟨Ev, fun _ => ?_⟩
      have := hEv.mulAmp (SG := l1Ball d L N₁ m₁ (k + 1) N) (amp := fun g => g (ys τ) (is τ))
        (Ma := 1)
        ((analyticOnNhd_coord (ys τ) (is τ)).mono (Set.subset_univ _))
        (fun g hg => norm_le_of_mem_l1Ball hg (ys τ) (is τ))
        (AgG := fun Y g g' => ∀ x ∈ Y, g x = g' x) (by
          intro Y hY g _ g' _ hag
          have hyY : ys τ ∈ Y := subset_of_mem_polymerDomains hY (by
            rw [← hX₁ τ hτ]; exact hys τ hτ)
          exact congrFun (hag _ hyY) _)
      simpa [hτ] using this
    · exact ⟨fun _ _ => 0, fun h => absurd h hτ⟩
  choose Ev hEv using hex
  exact ⟨fun τ => polymerDomains (fun i : ParIdx Gp (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =>
      i.1.1) Gp (m₀ τ) (X1 Gp (m₀ τ) (j τ) (𝒦X τ)),
    fun τ Y x₀ w σ Θ => dirTerm (Ev τ Y) ω x₀ w σ Θ, LocInt.finsum 𝒯 (fun τ hτ => hEv τ hτ)⟩

end EFamily

end Balaban.Localization
