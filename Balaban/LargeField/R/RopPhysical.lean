/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RhoZeroPhysical
public import Balaban.LargeField.R.ZeroDomainSepRho
import Mathlib

/-!
# The operation `R` with the physical-mass reference density (Definition III.8.3, Lemma III.8.4)

* `R_normalization_ripe`: Lemma III.8.4 (massless reference density) for the ripe components of an actual history,
  with the joint measurability discharged by `measurable_famRho` (W208) in W210's `R_normalization_ripe_of_measurable`.
* `famRhoPhysical`, `famDecompPhysical`: the `RDecomp` of the physical reference densities `rhoZeroPhysical`
  (P7 (3.1), Definition III.8.1) for a family of ripe components, `Rop_famDecompPhysical_apply` (P7 (1.6)),
  `famRhoPhysical_eq_rhoZeroPhysical` (independence of the other components: `rhoZeroPhysical_congr`).
* `R_normalizationPhysical`: `∫ R[ρ] = ∫ ρ` with the physical common denominator.  Premises: those of
  `R_normalization` (integrability of `ρ`, the parameter conditions of `denominator_eq`, the geometry) and the
  physical-mass premises `0 ≤ ν`, `h` a real unit vector, `β ν L^{-k(d-2)} ≤ E`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Balaban Balaban.Multiscale Balaban.Background MeasureTheory

namespace Balaban.LargeField

section Fam

variable (N : ℕ) {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] [NeZero N] {ϱ : ℝ} {ι : Type} [Fintype ι]
  (G : ι → GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k)
  (b0 : ι → Torus d (N₀ * L ^ (k - k))) (w : ι → Fin d → ℕ)
  (hw1 : ∀ c i, 1 ≤ w c i) (hwD : ∀ c i, w c i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  (X : ι → Set (Torus d (N₀ * L ^ (k - k))))
  (hXreg : ∀ c, box (b0 c) (w c) ∪ shellOut (box (b0 c) (w c)) ⊆ X c)
  (hsep : ∀ c c', c ≠ c' → Disjoint (X c) (box (b0 c') (w c')))
  (hΩ : ∀ c, OverTop (G c) (box (b0 c) (w c) ∪ shellOut (box (b0 c) (w c))))
  (hdata : ∀ c, ∀ x ∈ dataSites (G c), jBlock d L N₀ k k x ∈ X c) (H : BgHyp d L k ϱ a 0)
  (δ : ι → ℝ) (hδ : ∀ c, 0 < δ c)
  (hδc : ∀ c, δ c ≤ psiZeroC11 N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H)

local notation "Kc[" c "]" => psiZeroK N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H

open Classical in
/-- **The physical reference density of the component `c` as a function of `(ψ_k↾Z₀(c), ψ_k↾(⋃_{c'∈σ} Z₀(c'))ᶜ)`**
(Definition III.8.1 with the mass term of P7 (3.1)); `0` off the tube. -/
noncomputable def famRhoPhysical (σ : Finset ι) (ν : ℝ) (h : Fin N → ℝ) (β p0 : ℝ) (c : ι)
    (y : ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ) (u : SuppSpace (zb b0 w c) N) : ℝ :=
  if hT : FamTube N G b0 w X δ c (famOut N b0 w X hXreg hsep σ y) then
    rhoZeroPhysical (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hT
      ν h β p0 u
  else 0

/-- **The `RDecomp` of the physical reference densities** (Definition III.8.3): that of `famDecomp` with the
densities `famRhoPhysical`. -/
noncomputable def famDecompPhysical (σ : Finset ι) (ν : ℝ) (h : Fin N → ℝ) (β p0 : ℝ) :
    RDecomp (volume.restrict (famTubeSet N G b0 w X δ)) :=
  { famDecomp N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 with
    r := fun c u y => famRhoPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h β p0
      c.1 y u }

/-- **Independence (Lemma III.1.5, used in Lemma III.8.4)**: for `ψ_k` in the tube, `ρ^{ph}_{k,0}(Z)` read through the
outside variables is the physical reference density of `ψ_k` itself. -/
theorem famRhoPhysical_eq_rhoZeroPhysical (σ : Finset ι) (ν : ℝ) (h : Fin N → ℝ) (β p0 : ℝ) (c : ι)
    {ψ : BlockField d L N₀ k N} (hψ : FamTube N G b0 w X δ c ψ) :
    famRhoPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h β p0 c
        (famEquiv N b0 w X hXreg hsep σ ψ).2 =
      rhoZeroPhysical (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hψ
        ν h β p0 := by
  have hT := (fam_tube_iff N G b0 w X hXreg hsep δ σ ψ c).1 hψ
  funext u
  unfold famRhoPhysical
  simp only [hT, ↓reduceDIte]
  exact congrFun (rhoZeroPhysical_congr (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H
    (hδ c) (hδc c) hψ hT (fun z hz => (famOut_eq_of_mem N b0 w X hXreg hsep σ ψ c hz).symm) ν h β p0) u

/-- Good fibres: under the parameter conditions of `denominator_eq` and the physical-mass premises, the density is
integrable with positive integral on every fibre in the tube. -/
theorem famRhoPhysical_good (σ : Finset ι) {ν : ℝ} (hν : 0 ≤ ν) (h : Fin N → ℝ) (hh : ∑ i, h i ^ 2 = 1)
    {β p0 E : ℝ} (hβ : 0 < β) (hE : β * (ν / (L : ℝ) ^ (k * (d - 2))) ≤ E) {c : ι}
    (hp0 : 1 ≤ cSix d D Kc[c] * p0)
    (hrad : Kc[c] * δ c + 5 * zeroRadius (cSix d D Kc[c]) β p0 ≤ etaDen d L N D)
    {y : ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ}
    (hy : FamTube N G b0 w X δ c (famOut N b0 w X hXreg hsep σ y)) :
    Integrable (famRhoPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h β p0 c y)
        volume ∧
      0 < ∫ u, famRhoPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h β p0 c y u := by
  have hfun : famRhoPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h β p0 c y =
      rhoZeroPhysical (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hy
        ν h β p0 := by
    funext u
    simp only [famRhoPhysical, hy, ↓reduceDIte]
  rw [hfun]
  obtain ⟨hint, hpos, -⟩ := integral_rhoZeroPhysical_bounds (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c)
    (hΩ c) (hdata c) H (hδ c) (hδc c) hy hν h hh hβ hE hp0 hrad
  exact ⟨hint, hpos⟩

/-- **The joint measurability of the physical reference densities** in `(ψ_k↾Z₀(c), y)`. -/
theorem measurable_famRhoPhysical (σ : Finset ι) (ν : ℝ) (h : Fin N → ℝ) {β p0 : ℝ} (hβ : 0 < β) (c : ι)
    (hp0 : 1 ≤ cSix d D Kc[c] * p0)
    (hrad : Kc[c] * δ c + 5 * zeroRadius (cSix d D Kc[c]) β p0 ≤ etaDen d L N D) :
    Measurable (fun p : SuppSpace (zb b0 w c) N × (ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ) =>
      famRhoPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h β p0 c p.2 p.1) := by
  have hm' := measurable_rhoZeroPhysicalTot (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c)
    (hdata c) H (hδ c) (hδc c) ν h hβ hp0 hrad
  have hout : Measurable (famOut N b0 w X hXreg hsep σ) := famOut_measurable N b0 w X hXreg hsep σ
  have h2 := hm'.comp (measurable_fst.prodMk (hout.comp measurable_snd))
  convert h2 using 1
  funext p
  by_cases hT : FamTube N G b0 w X δ c (famOut N b0 w X hXreg hsep σ p.2)
  · simp only [famRhoPhysical, rhoZeroPhysicalTot, Function.comp, hT, dite_true]
  · simp only [famRhoPhysical, rhoZeroPhysicalTot, Function.comp, hT, dite_false]

/-- **Lemma III.8.4 (normalization) with the physical reference densities**: `∫ R^{ph}[ρ] = ∫ ρ` over `Ψ̃`.
Premises: integrability of `ρ`, the geometry (`hsep` and the ripe data), the parameter conditions of
`denominator_eq` (`hβ`, `hp0`, `hrad`) and the physical-mass data (`0 ≤ ν`, `h` a real unit vector,
`β ν L^{-k(d-2)} ≤ E`; the latter two give the positivity and integrability of the common denominators, W193's
`real_mass_cost`). -/
theorem R_normalizationPhysical (σ : Finset ι) {ν : ℝ} (hν : 0 ≤ ν) (h : Fin N → ℝ) (hh : ∑ i, h i ^ 2 = 1)
    {β p0 E : ℝ} (hβ : 0 < β) (hE : β * (ν / (L : ℝ) ^ (k * (d - 2))) ≤ E)
    (hp0 : ∀ c ∈ σ, 1 ≤ cSix d D Kc[c] * p0)
    (hrad : ∀ c ∈ σ, Kc[c] * δ c + 5 * zeroRadius (cSix d D Kc[c]) β p0 ≤ etaDen d L N D)
    {ρ : BlockField d L N₀ k N → ℝ} (hρ : Integrable ρ (volume.restrict (famTubeSet N G b0 w X δ))) :
    Integrable (Rop (famDecompPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h β p0) ρ)
        (volume.restrict (famTubeSet N G b0 w X δ)) ∧
      ∫ ψ, Rop (famDecompPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h β p0) ρ ψ
          ∂(volume.restrict (famTubeSet N G b0 w X δ)) =
        ∫ ψ, ρ ψ ∂(volume.restrict (famTubeSet N G b0 w X δ)) := by
  have hS := measurableSet_famOut_tube N G b0 w X hXreg hsep δ σ
  refine R_normalization_ae (famDecompPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h
    β p0) hρ ?_ ?_ ?_ ?_
  · intro c
    exact measurable_famRhoPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h hβ c.1
      (hp0 c.1 c.2) (hrad c.1 c.2)
  · intro c u y
    show 0 ≤ famRhoPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h β p0 c.1 y u
    unfold famRhoPhysical
    split_ifs
    · exact rhoZeroPhysical_nonneg (G c.1) a hd hk (b0 c.1) (w c.1) (hw1 c.1) (hwD c.1) hm (hXreg c.1) (hΩ c.1)
        (hdata c.1) H (hδ c.1) (hδc c.1) _ ν h β p0 u
    · exact le_rfl
  · refine (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun y hy c => ?_)
    exact (famRhoPhysical_good N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ hν h hh hβ hE
      (hp0 c.1 c.2) (hrad c.1 c.2) (hy c.1)).1
  · refine (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun y hy c => ?_)
    exact (famRhoPhysical_good N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ hν h hh hβ hE
      (hp0 c.1 c.2) (hrad c.1 c.2) (hy c.1)).2

/-- **The operation `R` with the physical reference densities** (P7 (1.6)): at a field in the tube,
`R[ρ](ψ_k) = ∏_Z ρ^{ph}_{k,0}(Z)(ψ_k↾Z₀) · (∫ dψ_k↾𝒵_{σ,0} ρ) / ∏_Z ∫ dψ_k↾Z₀ ρ^{ph}_{k,0}(Z)`. -/
theorem Rop_famDecompPhysical_apply (σ : Finset ι) (ν : ℝ) (h : Fin N → ℝ) (β p0 : ℝ)
    (ρ : BlockField d L N₀ k N → ℝ) {ψ : BlockField d L N₀ k N} (hψ : ψ ∈ famTubeSet N G b0 w X δ) :
    Rop (famDecompPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h β p0) ρ ψ =
      (∏ c : σ, rhoZeroPhysical (G c.1) a hd hk (b0 c.1) (w c.1) (hw1 c.1) (hwD c.1) hm (hXreg c.1) (hΩ c.1)
          (hdata c.1) H (hδ c.1) (hδc c.1) (hψ c.1) ν h β p0 (restrictSupp (zb b0 w c.1) ψ)) *
        ((∫ x, ρ ((famEquiv N b0 w X hXreg hsep σ).symm (x, (famEquiv N b0 w X hXreg hsep σ ψ).2))
            ∂(Measure.pi fun c : σ => (volume : Measure (SuppSpace (zb b0 w c.1) N)))) /
          ∏ c : σ, ∫ u, rhoZeroPhysical (G c.1) a hd hk (b0 c.1) (w c.1) (hw1 c.1) (hwD c.1) hm (hXreg c.1)
            (hΩ c.1) (hdata c.1) H (hδ c.1) (hδc c.1) (hψ c.1) ν h β p0 u) := by
  have hr : ∀ c : σ, famRhoPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h β p0 c.1
      (famEquiv N b0 w X hXreg hsep σ ψ).2 =
      rhoZeroPhysical (G c.1) a hd hk (b0 c.1) (w c.1) (hw1 c.1) (hwD c.1) hm (hXreg c.1) (hΩ c.1) (hdata c.1) H
        (hδ c.1) (hδc c.1) (hψ c.1) ν h β p0 := fun c =>
    famRhoPhysical_eq_rhoZeroPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h β p0 c.1
      (hψ c.1)
  have key : Rop (famDecompPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h β p0) ρ ψ =
      (∏ c : σ, famRhoPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h β p0 c.1
        (famEquiv N b0 w X hXreg hsep σ ψ).2 (restrictSupp (zb b0 w c.1) ψ)) *
        ((∫ x, ρ ((famEquiv N b0 w X hXreg hsep σ).symm (x, (famEquiv N b0 w X hXreg hsep σ ψ).2))
            ∂(Measure.pi fun c : σ => (volume : Measure (SuppSpace (zb b0 w c.1) N)))) /
          ∏ c : σ, ∫ u, famRhoPhysical N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ ν h β p0 c.1
            (famEquiv N b0 w X hXreg hsep σ ψ).2 u) := rfl
  rw [key]
  simp only [hr]

end Fam

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M] {k : ℕ}

/-- **Lemma III.8.4 (normalization) for the ripe components of a history**, unconditional in the measurability: W210's
`R_normalization_ripe_of_measurable` with `hmeas` discharged by W208's `measurable_famRho` (massless reference density). -/
theorem R_normalization_ripe (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) (hkK : k ≤ K)
    (N : ℕ) [NeZero N] {ϱ : ℝ} {ι : Type} [Fintype ι] (Zc : ι → H.Comp k) (hZc : Function.Injective Zc)
    (G : ι → GeneratingSet S.d S.L (S.M * n k) k ϱ) (a : ℕ → ℝ) {D : ℕ} (hd : 2 ≤ S.d) (hk : 1 ≤ k)
    (b0 : ι → Torus S.d (S.M * n k * S.L ^ (k - k))) (w : ι → Fin S.d → ℕ)
    (hw1 : ∀ c i, 1 ≤ w c i) (hwD : ∀ c i, w c i ≤ D) (hm : D + 2 ≤ S.M * n k * S.L ^ (k - k))
    (hbx : ∀ c, ∀ x : Torus S.d (S.M * n k * S.L ^ k),
      (jBlock S.d S.L (S.M * n k) k k x ∈ box (b0 c) (w c) ↔
        blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k (Zc c)))
    (hΩ : ∀ c, OverTop (G c) (box (b0 c) (w c) ∪ shellOut (box (b0 c) (w c))))
    (hdU : ∀ c, ∀ x ∈ dataSites (G c), cubeMap n S.L S.M k k x ∈ bdryUnb H (Zc c))
    (Hbg : BgHyp S.d S.L k ϱ a 0) (δ : ι → ℝ) (hδ : ∀ c, 0 < δ c)
    (hδc : ∀ c, δ c ≤ psiZeroC11 N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm
      (H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (hΩ c) (H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg)
    (σ : Finset ι) {β p0 : ℝ} (hβ : 0 < β)
    (hp0 : ∀ c ∈ σ, 1 ≤ cSix S.d D
      (psiZeroK N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (H.ripeX_hXreg hR hkK hk (Zc c) (hbx c))
        (hΩ c) (H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg) * p0)
    (hrad : ∀ c ∈ σ, psiZeroK N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm
        (H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (hΩ c) (H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg * δ c +
      5 * zeroRadius (cSix S.d D
        (psiZeroK N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (H.ripeX_hXreg hR hkK hk (Zc c) (hbx c))
          (hΩ c) (H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg)) β p0 ≤ etaDen S.d S.L N D)
    {ρ : BlockField S.d S.L (S.M * n k) k N → ℝ}
    (hρ : Integrable ρ (volume.restrict (famTubeSet N G b0 w (fun c => H.ripeX (Zc c)) δ))) :
    Integrable (Rop (famDecomp N G a hd hk b0 w hw1 hwD hm (fun c => H.ripeX (Zc c))
        (fun c => H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (H.zeroDomain_hsep hkK hk Zc hZc b0 w hbx) hΩ
        (fun c => H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg δ hδ hδc σ β p0) ρ)
        (volume.restrict (famTubeSet N G b0 w (fun c => H.ripeX (Zc c)) δ)) ∧
      ∫ ψ, Rop (famDecomp N G a hd hk b0 w hw1 hwD hm (fun c => H.ripeX (Zc c))
        (fun c => H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (H.zeroDomain_hsep hkK hk Zc hZc b0 w hbx) hΩ
        (fun c => H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg δ hδ hδc σ β p0) ρ ψ
          ∂(volume.restrict (famTubeSet N G b0 w (fun c => H.ripeX (Zc c)) δ)) =
        ∫ ψ, ρ ψ ∂(volume.restrict (famTubeSet N G b0 w (fun c => H.ripeX (Zc c)) δ)) :=
  R_normalization_of_measurable N G a hd hk b0 w hw1 hwD hm (fun c => H.ripeX (Zc c))
    (fun c => H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (H.zeroDomain_hsep hkK hk Zc hZc b0 w hbx) hΩ
    (fun c => H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg δ hδ hδc σ hβ hp0 hrad hρ
    (fun c => measurable_famRho N G a hd hk b0 w hw1 hwD hm (fun c => H.ripeX (Zc c))
      (fun c => H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (H.zeroDomain_hsep hkK hk Zc hZc b0 w hbx) hΩ
      (fun c => H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg δ hδ hδc σ hβ c.1 (hp0 c.1 c.2) (hrad c.1 c.2))

end RegionHistory

end Balaban.LargeField
