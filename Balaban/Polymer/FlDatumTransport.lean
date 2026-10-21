/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.ComposeFieldTransport
public import Balaban.Localization.I5FluctChain

/-!
# The datum of `𝔹_k(X)` with the fluctuation at corresponding sites of two tori

`flDatum_corr`: the data `flDatum` of two tori (background composition perturbed by the composed
fluctuation) agree under a site map `σ` on a set `R` of sites, when the generating sets correspond
on `R` (`GSCorr`), the decoupled background field, the fluctuation field, the data and the
fluctuation correspond on `R`, and `R` contains the blocks read by the compositions.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale

variable {d L N₁ N₁' m₁ K N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ₁ ϱ₁' ϱ₂ ϱ₂' ϱ₃ ϱ₃' : ℝ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁} {Gk' : GeneratingSet d L (N₁' * L ^ m₁) K ϱ₁'}
  {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂} {Gp' : GeneratingSet d L (N₁' * L ^ m₁) K ϱ₂'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₃} {Hm' : GeneratingSet d L (N₁' * L ^ m₁) K ϱ₃'}
  {σ : Torus d ((N₁ * L ^ m₁) * L ^ K) → Torus d ((N₁' * L ^ m₁) * L ^ K)}

/-- **The datum `flDatum` at corresponding sites.** -/
theorem flDatum_corr {R : Set (Torus d ((N₁ * L ^ m₁) * L ^ K))}
    (hGk : GSCorr Gk Gk' σ R) (hGp : GSCorr Gp Gp' σ R) (hHm : GSCorr Hm Hm' σ R)
    (hP : Precedes Gk Gp) (hPm : Precedes Gk Hm) (hP' : Precedes Gk' Gp') (hPm' : Precedes Gk' Hm')
    (a : ℕ → ℝ)
    {φ : Gp.Ω 1 × Fin N → ℂ} {φ₂ : Gp'.Ω 1 × Fin N → ℂ}
    {δφ : Hm.Ω 1 × Fin N → ℂ} {δφ₂ : Hm'.Ω 1 × Fin N → ℂ}
    {D : BgData Gp N} {D₂ : BgData Gp' N}
    {ψ' : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ}
    {ψ₂' : Torus d ((N₁' * L ^ m₁) * L ^ K) → Fin N → ℂ}
    (hlc : IsLayerConstant Hm ψ') (hlc₂ : IsLayerConstant Hm' ψ₂')
    (hφ : ∀ y ∈ R, ∀ (hy : y ∈ Gp.Ω 1) (hy' : σ y ∈ Gp'.Ω 1) (i : Fin N),
      φ₂ (⟨σ y, hy'⟩, i) = φ (⟨y, hy⟩, i))
    (hδ : ∀ y ∈ R, ∀ (hy : y ∈ Hm.Ω 1) (hy' : σ y ∈ Hm'.Ω 1) (i : Fin N),
      δφ₂ (⟨σ y, hy'⟩, i) = δφ (⟨y, hy⟩, i))
    (hD : ∀ y ∈ R, D₂.Ψ (σ y) = D.Ψ y ∧ D₂.h (σ y) = D.h y)
    (hψ : ∀ y ∈ R, ψ₂' (σ y) = ψ' y)
    (hblk : ∀ z ∈ R, z ∈ Gk.Ω 1 →
      (∀ y ∈ Gk.blk (Gk.layerIndex z) z, y ∈ R) ∧ (∀ y ∈ Gp.blk (Gp.layerIndex z) z, y ∈ R) ∧
      (∀ y ∈ Hm.blk (Hm.layerIndex z) z, y ∈ R))
    {z : Torus d ((N₁ * L ^ m₁) * L ^ K)} (hz : z ∈ R) (i : Fin N) :
    (flDatum Gk' hP' hPm' a φ₂ δφ₂ D₂ ψ₂' hlc₂).Ψ (σ z) i = (flDatum Gk hP hPm a φ δφ D ψ' hlc).Ψ z i
      ∧ (flDatum Gk' hP' hPm' a φ₂ δφ₂ D₂ ψ₂' hlc₂).h (σ z) i =
        (flDatum Gk hP hPm a φ δφ D ψ' hlc).h z i := by
  classical
  constructor
  · rw [flDatum_Ψ, flDatum_Ψ]
    have hzD := hD z hz
    congr 1
    · refine composeField_corr a hGk hGp hz (fun h => hP.mem_Ω1 h) ?_ ?_ hzD.1 ?_ i
      · intro h y hy i
        obtain ⟨-, hb, -⟩ := hblk z hz h
        exact svec_corr ((hGp.mem_iff y (hb y hy))) (fun hy1 hy2 j => hφ y (hb y hy) hy1 hy2 j) i
      · intro h y hy i
        obtain ⟨hb, -, -⟩ := hblk z hz h
        exact svec_corr ((hGp.mem_iff y (hb y hy))) (fun hy1 hy2 j => hφ y (hb y hy) hy1 hy2 j) i
      · intro _ j
        exact barField_corr (hGp.mem_iff z hz) j (fun h1 h2 => hφ z hz h1 h2 j)
          (fun _ => (congrFun hzD.1 j))
    · refine composeField_corr a hGk hHm hz (fun h => hPm.mem_Ω1 h) ?_ ?_ (hψ z hz) ?_ i
      · intro h y hy i
        obtain ⟨-, -, hb⟩ := hblk z hz h
        exact svec_corr ((hHm.mem_iff y (hb y hy))) (fun hy1 hy2 j => hδ y (hb y hy) hy1 hy2 j) i
      · intro h y hy i
        obtain ⟨hb, -, -⟩ := hblk z hz h
        exact svec_corr ((hHm.mem_iff y (hb y hy))) (fun hy1 hy2 j => hδ y (hb y hy) hy1 hy2 j) i
      · intro _ j
        exact barField_corr (hHm.mem_iff z hz) j (fun h1 h2 => hδ z hz h1 h2 j)
          (fun _ => (congrFun (hψ z hz) j))
  · rw [flDatum_h, flDatum_h]
    simp only [composeData]
    by_cases h : z ∈ Gk.Ω 1
    · have h' : σ z ∈ Gk'.Ω 1 := (hGk.mem_iff z hz).2 h
      simp only [h, h', ite_true]
      exact congrFun (hD z hz).2 i
    · have h' : σ z ∉ Gk'.Ω 1 := fun h2 => h ((hGk.mem_iff z hz).1 h2)
      simp only [h, h', ite_false]

end Balaban.Polymer.TwoTorusStep
