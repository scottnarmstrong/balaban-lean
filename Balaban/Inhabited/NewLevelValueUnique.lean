module

public import Balaban.Fluctuation.InteractionHatE

/-!
# Uniqueness of the old-term functional for two pinned background fields

The old-term functional `eTermFun … Fk E` reads the background field `Fk` only at the composed data
of the realizable triples, where `Fk` is the background field of the union domain.  Two fields with
this property give the same functional on the realizable triples.
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

/-- **The old-term functional agrees for two background fields with the pin of the union domain**,
at every realizable triple with layer-constant fluctuation. -/
theorem eTermFun_unique {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {Fk Fk' : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (hFk' : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk' (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (ht : t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :
    eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2 =
      eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk' E t.1 t.2.1 t.2.2 := by
  obtain ⟨D, ψ', hlc, -, -, h1, h2, -⟩ := eTerm_chain_of_one_le hb₁ hbC hB hF hFk ht
  obtain ⟨D', ψ'', hlc', -, -, h1', h2', -⟩ := eTerm_chain_of_one_le hb₁ hbC hB hF hFk' ht
  have heq := BgData.eq_of_raw (h1.symm.trans h1')
  unfold eTermFun
  rw [h1, h2]
  rw [← heq] at h2'
  rw [h2']

end Balaban.Fluctuation
