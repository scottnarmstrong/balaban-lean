/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.FlDatumTransport
public import Balaban.Polymer.BgFieldTransport
public import Balaban.Fluctuation.InteractionHatE

/-!
# The old-term functional on two tori

`eTermFun_twoTorus`: for realizable triples `t`, `t'` of two tori whose decoupled background field,
fluctuation field, raw datum and fluctuation correspond under a site map `σ` on a region `R`, the
old-term functionals `eTermFun … Fk E` and `eTermFun … Fk' E'` agree, when

* the generating sets `Gp, Gk, Hm, Gj` correspond on `R` (`GSCorr`) and `Gk` is isomorphic to `Gk'`
  on `R` (`GSIso`: the localized sets of corresponding polymers),
* `Fk`, `Fk'` have the pin of the union domain, and
* the old terms agree on raw data that agree under `σ` on `R`.  This last premise is the box form of
  the torus independence of the small-field data (D8, the `TorusIndep` clause of the input class);
  it is discharged by the inherited D8 of `sfSucc_core`.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Fluctuation
  Balaban.SmallField

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L]
  {ϱ ϱ' ϱ₁ ϱ₁' ϱ₂ ϱ₂' ϱm ϱm' : ℝ}

/-- **The old-term functional at corresponding realizable triples.** -/
theorem eTermFun_twoTorus
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    {Gp' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ'}
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {Gk' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ₁'}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
    {Gj' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ₂'}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'}
    {a₁ ν c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {j : ℕ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {X₀' X₁f' : Finset (CTorus d L N₁' m₁ (k + 1))}
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hB' : BgSetting N Gp' Gk' Gj' a₁ ν c BG κ r₀ eps δ₃ X₀' X₁f' j)
    (hF' : FlSetting N Gp' Gk' Hm' a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f')
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    {Fk' : RawData d L (N₁' * L ^ m₁) (k + 1) N → (Gk'.Ω 1 × Fin N → ℂ) × (Gk'.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (hFk' : ∀ D : BgData Gk' N, InUnionDomainC Gk' (bgC0 d L N) (bgC1 d L N) ν D →
      Fk' (rawOf D) = (bgFieldC Gk' (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk' (compWeight L a₁) ν (bgC0 d L N) D))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    (E' : RawData d L (N₁' * L ^ m₁) (k + 1) N → ℂ)
    {σ : Torus d ((N₁ * L ^ m₁) * L ^ (k + 1)) → Torus d ((N₁' * L ^ m₁) * L ^ (k + 1))}
    {R : Set (Torus d ((N₁ * L ^ m₁) * L ^ (k + 1)))}
    (hGk : GSCorr Gk Gk' σ R) (hGp : GSCorr Gp Gp' σ R) (hHm : GSCorr Hm Hm' σ R)
    (hGj : GSCorr Gj Gj' σ R) (hiso : GSIso (compWeight L a₁) ν Gk Gk' σ R)
    (hblk : ∀ z ∈ R, z ∈ Gk.Ω 1 →
      (∀ y ∈ Gk.blk (Gk.layerIndex z) z, y ∈ R) ∧ (∀ y ∈ Gp.blk (Gp.layerIndex z) z, y ∈ R) ∧
      (∀ y ∈ Hm.blk (Hm.layerIndex z) z, y ∈ R))
    (hblk2 : ∀ z ∈ R, z ∈ Gj.Ω 1 →
      (∀ y ∈ Gj.blk (Gj.layerIndex z) z, y ∈ R) ∧ (∀ y ∈ Gk.blk (Gk.layerIndex z) z, y ∈ R))
    (hE : ∀ (r : RawData d L (N₁ * L ^ m₁) (k + 1) N) (r' : RawData d L (N₁' * L ^ m₁) (k + 1) N),
      (∀ z ∈ R, r.1 z = r'.1 (σ z) ∧ r.2 z = r'.2 (σ z)) → E' r' = E r)
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    {t' : ((Gp'.Ω 1 × Fin N → ℂ) × (Gp'.Ω 1 → ℂ)) × (Hm'.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ))}
    (ht : t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁)
    (ht' : t' ∈ FlRealLC Gp' Hm' a₁ ν BG κ eps X₁f' BG₂ δ₁)
    (hφ : ∀ y ∈ R, ∀ (hy : y ∈ Gp.Ω 1) (hy' : σ y ∈ Gp'.Ω 1) (i : Fin N),
      t'.1.1 (⟨σ y, hy'⟩, i) = t.1.1 (⟨y, hy⟩, i))
    (hδ : ∀ y ∈ R, ∀ (hy : y ∈ Hm.Ω 1) (hy' : σ y ∈ Hm'.Ω 1) (i : Fin N),
      t'.2.1 (⟨σ y, hy'⟩, i) = t.2.1 (⟨y, hy⟩, i))
    (hraw : ∀ y ∈ R, t'.2.2.1.1 (σ y) = t.2.2.1.1 y ∧ t'.2.2.1.2 (σ y) = t.2.2.1.2 y)
    (hψ : ∀ y ∈ R, t'.2.2.2 (σ y) = t.2.2.2 y) :
    eTermFun Gp' Gk' Gj' Hm' (compWeight L a₁) Fk' E' t'.1 t'.2.1 t'.2.2 =
      eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2 := by
  obtain ⟨D, ψ₁, hlc, ht2, -, h1, h2, -⟩ := eTerm_chain_of_one_le le_rfl (one_le_scaledC0 d) hB hF hFk ht
  obtain ⟨D', ψ₁', hlc', ht2', -, h1', h2', -⟩ :=
    eTerm_chain_of_one_le le_rfl (one_le_scaledC0 d) hB' hF' hFk' ht'
  have e1 : t.2.2.1 = rawOf D := by rw [ht2]
  have e1' : t'.2.2.1 = rawOf D' := by rw [ht2']
  have e2 : t.2.2.2 = ψ₁ := by rw [ht2]
  have e2' : t'.2.2.2 = ψ₁' := by rw [ht2']
  have hD0 : ∀ y ∈ R, D'.Ψ (σ y) = D.Ψ y ∧ D'.h (σ y) = D.h y := by
    intro y hy
    have := hraw y hy
    rw [e1, e1'] at this
    exact this
  have hψ0 : ∀ y ∈ R, ψ₁' (σ y) = ψ₁ y := by
    intro y hy
    have := hψ y hy
    rwa [e2, e2'] at this
  have hflc := fun z (hz : z ∈ R) (i : Fin N) =>
    flDatum_corr hGk hGp hHm hB.hP hF.hPm hB'.hP hF'.hPm (compWeight L a₁) hlc hlc' hφ hδ hD0 hψ0
      hblk hz i
  have hDfl : ∀ z ∈ R, (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ₁ hlc).Ψ z =
        (flDatum Gk' hB'.hP hF'.hPm (compWeight L a₁) t'.1.1 t'.2.1 D' ψ₁' hlc').Ψ (σ z) ∧
      (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ₁ hlc).h z =
        (flDatum Gk' hB'.hP hF'.hPm (compWeight L a₁) t'.1.1 t'.2.1 D' ψ₁' hlc').h (σ z) :=
    fun z hz => ⟨funext fun i => (hflc z hz i).1.symm, funext fun i => (hflc z hz i).2.symm⟩
  have hbg := bgFieldC_of_gsIso hiso hDfl (bgC0 d L N)
  unfold eTermFun
  rw [h1, h2, h1', h2']
  refine hE _ _ fun z hz => ⟨funext fun i => ?_, funext fun i => ?_⟩
  · exact (composeData_corr hGj hGk hB.hq hB'.hq (compWeight L a₁)
      (fun y hy hy1 hy2 i => hbg.1 ⟨y, hy1⟩ hy2 i)
      (fun y hy => ⟨(hDfl y hy).1.symm, (hDfl y hy).2.symm⟩) hblk2 hz i).1.symm
  · exact (composeData_corr hGj hGk hB.hq hB'.hq (compWeight L a₁)
      (fun y hy hy1 hy2 i => hbg.1 ⟨y, hy1⟩ hy2 i)
      (fun y hy => ⟨(hDfl y hy).1.symm, (hDfl y hy).2.symm⟩) hblk2 hz i).2.symm

end Balaban.Polymer.TwoTorusStep
