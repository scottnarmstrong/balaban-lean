/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionHatE

/-!
# The composed charts of the old terms (the data an old term is read at)

An old term of a label is read by the step at the composed data `D2raw Gk Gj Fk (d1Triple …)` of
its realizable triples: the step's datum, decoupled and fluctuated, lies in the chart
`Ξ^c_K(Gk; 1, e)` of the level-`k` local set `Gk` (on the torus of level `K = k + 1`), and the old
term reads its composition into its own generating set `Gj` (`eTerm_chain_of_one_le`).  The bound of
the irrelevant parts of P1 (3.128) is a bound at such composed data (smooth at the scale of the
level of `Gk` on the layers of `Gj`), not on the whole chart `Ξ^c_j(Gj; b, e)` of the level of the
term.

* `composedChart Gj a ν j b e`: the data composed into `Gj` from the chart `Ξ^c_K(G; 1, e)` of a
  generating set `G` that `Gj` precedes (collar of `Gj` in `Ω₁(G)`, the standing hypotheses at
  `G`), lying in the chart `Ξ^c_j(Gj; b, e)`;
* `composedChart_subset_xiCRaw`;
* `d2raw_d1Triple_mem_composedChart`: the composed data of the realizable triples lie in it;
* `eTermFun_bound_composed`: the bound of the old-term functional on the realizable triples from
  the bound of the term on its composed chart (the bound on the chart `Ξ^c_j(Gj; b, e)`, as in
  `eTermFun_bound_of_one_le`, is the special case through `composedChart_subset_xiCRaw`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation

section Def

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **The composed chart of a term generator** `Gj` (level `j`, composition constant `b`, radius
`e`): the raw data `ψ(Gj, G; φ_G(D), D)` composed into `Gj` from a datum `D` of the chart
`Ξ^c_K(G; 1, e)` of a generating set `G` that `Gj` precedes, with the collar of `Gj` in `Ω₁(G)` and
the standing hypotheses of the background theory at `G`, which lie in the chart
`Ξ^c_j(Gj; b, e)`. -/
def composedChart (Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ) (j : ℕ)
    (b e : ℝ) : Set (RawData d L (N₁ * L ^ m₁) K N) :=
  {r | ∃ (ϱ₁ : ℝ) (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁) (hq : Precedes Gj G),
    (∀ z ∈ collar Gj, z ∈ G.Ω 1) ∧ BgHyp d L K ϱ₁ a ν ∧
    ∃ D : BgData G N, XiCData G a ν K 1 e D ∧
      XiCData Gj a ν j b e (composeData hq a (bgFieldC G a ν (bgC0 d L N) D) D) ∧
      r = rawOf (composeData hq a (bgFieldC G a ν (bgC0 d L N) D) D)}

variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {j : ℕ} {b e : ℝ}

/-- The composed chart lies in the chart `Ξ^c_j(Gj; b, e)`. -/
theorem composedChart_subset_xiCRaw :
    (composedChart (N := N) Gj a ν j b e) ⊆ XiCRaw Gj a ν j b e := by
  rintro r ⟨ϱ₁, G, hq, _, _, D, _, hX, rfl⟩
  exact ⟨_, hX, rfl⟩

end Def

section Read

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

/-- **The composed data of the realizable triples lie in the composed chart** of the term
generator (from the chain `eTerm_chain_of_one_le`: the fluctuated datum of `Gk` lies in
`Ξ^c_{k+1}(Gk; 1, e)` and its composition into `Gj` in `Ξ^c_j(Gj; b, e)`). -/
theorem d2raw_d1Triple_mem_composedChart {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
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
      composedChart Gj (compWeight L a₁) ν j b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) := by
  obtain ⟨D, ψ', hlc, -, hX1, hD1, hD2, hX2⟩ := eTerm_chain_of_one_le hb₁ hbC hB hF hFk ht
  rw [hD1, hD2]
  exact ⟨ϱ₁, Gk, hB.hq, hB.colj, hB.HBk, _, hX1, hX2, rfl⟩

/-- **The bound of the old-term functional on the realizable triples from the bound of the term on
its composed chart** (P1 (3.128) read at the data of the step). -/
theorem eTermFun_bound_composed {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ} {B : ℝ}
    (hEb : ∀ r ∈ composedChart Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ‖E r‖ ≤ B)
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (ht : t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :
    ‖eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2‖ ≤ B :=
  hEb _ (d2raw_d1Triple_mem_composedChart hb₁ hbC hB hF hFk ht)

end Read

end Balaban.Localization
