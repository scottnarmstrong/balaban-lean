/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionHatE

/-!
# The composed step data of a label (`LocalClassDensityIrrelStepChart`)

The label functionals of the class chain are read only at the composed data of the step: for a
realizable triple `t ∈ FlRealLC` (decoupled background `φ_{k+1}(s)`, fluctuation field `δφ(s)`,
step datum `Θ` and layer-constant fluctuation `ψ'`), at the datum
`D2raw Gk Gj a Fk (d1Triple Gp Gk Hm a t)` of `𝔹_j(X)`, the composition (6.2) into `𝔹_j(X)` of
the background of the composed datum of `𝔹_k(X)` (P1 Lemma 2.1: `ψ^{(j)}_k`).

* `d2raw_d1Triple_mem_xiCRaw`: these data lie in the label chart
  `Ξ^c_j(𝔹_j(X); b, b²ε + K₂δ₃ + K₂δ_fl)` (`eTerm_chain_of_one_le`).
* `eTermFun_analytic_of_set`: the old-term functional `eTermFun … E` is analytic on the realizable
  triples as soon as `E` is analytic on a set containing the composed data; the label chart is not
  needed.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Localization

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

/-- **The composed step data lie in the label chart**: for a realizable triple `t` with
layer-constant fluctuation, the composed datum of `𝔹_j(X)` lies in
`Ξ^c_j(𝔹_j(X); b, b²ε + K₂δ₃ + K₂δ_fl)`, for every composition constant `1 ≤ b ≤ C₀`. -/
theorem d2raw_d1Triple_mem_xiCRaw {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (ht : t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :
    D2raw Gk Gj (compWeight L a₁) Fk (d1Triple Gp Gk Hm (compWeight L a₁) t.1.1 t.2.1 t.2.2) ∈
      XiCRaw Gj (compWeight L a₁) ν j b (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) := by
  obtain ⟨D, ψ', hlc, -, -, hD1, hD2, hX2⟩ := eTerm_chain_of_one_le hb₁ hbC hB hF hFk ht
  rw [hD1, hD2]
  exact ⟨_, hX2, rfl⟩

/-- **Analyticity of the old-term functional on the realizable triples, from analyticity at the
composed data.**  If `E` is analytic on a set `𝒮` containing the composed data
`D2raw Gk Gj a Fk (d1Triple … t)` of the realizable triples `t`, then `eTermFun … E` is analytic
on the realizable triples.  The composed datum is analytic in the triple: each of its coordinates is
`eTermFun` of a coordinate functional (`eTermFun_analytic_of_one_le`). -/
theorem eTermFun_analytic_of_set {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    {𝒮 : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)} (hE : AnalyticOnNhd ℂ E 𝒮)
    (h𝒮 : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      D2raw Gk Gj (compWeight L a₁) Fk (d1Triple Gp Gk Hm (compWeight L a₁) t.1.1 t.2.1 t.2.2) ∈
        𝒮) :
    AnalyticOnNhd ℂ (fun t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =>
      eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2)
      (FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) := by
  intro t ht
  have hc1 : ∀ y i, AnalyticAt ℂ (fun t' : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) × (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =>
      (D2raw Gk Gj (compWeight L a₁) Fk
        (d1Triple Gp Gk Hm (compWeight L a₁) t'.1.1 t'.2.1 t'.2.2)).1 y i) t := fun y i =>
    eTermFun_analytic_of_one_le hb₁ hbC hB hF hFkan hFk
      (E := fun r : RawData d L (N₁ * L ^ m₁) (k + 1) N => r.1 y i)
      (fun r _ => analyticAt_rawΨ y i r) t ht
  have hc2 : ∀ y i, AnalyticAt ℂ (fun t' : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) × (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =>
      (D2raw Gk Gj (compWeight L a₁) Fk
        (d1Triple Gp Gk Hm (compWeight L a₁) t'.1.1 t'.2.1 t'.2.2)).2 y i) t := fun y i =>
    eTermFun_analytic_of_one_le hb₁ hbC hB hF hFkan hFk
      (E := fun r : RawData d L (N₁ * L ^ m₁) (k + 1) N => r.2 y i)
      (fun r _ => analyticAt_rawh y i r) t ht
  have hg : AnalyticAt ℂ (fun t' : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) × (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =>
      D2raw Gk Gj (compWeight L a₁) Fk
        (d1Triple Gp Gk Hm (compWeight L a₁) t'.1.1 t'.2.1 t'.2.2)) t :=
    (analyticAt_pi_iff.2 fun y => analyticAt_pi_iff.2 fun i => hc1 y i).prod
      (analyticAt_pi_iff.2 fun y => analyticAt_pi_iff.2 fun i => hc2 y i)
  exact AnalyticAt.comp (g := E) (x := t) (f := fun t' : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) × (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =>
      D2raw Gk Gj (compWeight L a₁) Fk
        (d1Triple Gp Gk Hm (compWeight L a₁) t'.1.1 t'.2.1 t'.2.2)) (hE _ (h𝒮 t ht)) hg

end Balaban.Fluctuation
