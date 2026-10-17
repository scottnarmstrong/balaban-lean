/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RopConcrete
public import Balaban.LargeField.R.RTransportDensity
public import Balaban.LargeField.R.RTransportFactor
import Mathlib

/-!
# The operation `R` with the reference density restricted to the component (Definition III.8.1, P7 (1.5)-(1.6))

`famDecompRestricted` is the instance of the generic decomposition `famDecompOf` (`RopConcrete.lean`) for the
reference densities `ρ^Z_{k,0}(Z) = χ_{Z₀} exp(-β₀ A_Z)` of `rhoZeroRestricted`: the action restricted to the removed
component `Z` (`actionZ`), not the action on all of `Ω₁(𝔹_k(U_k))`.

* `famRhoRestricted`: the restricted density as a function of `(ψ_k↾Z₀(c), ψ_k↾(⋃_{c∈σ} Z₀(c))ᶜ)`; `0` off the tube.
* `famDecompRestricted`: the `RDecomp` with these densities.
* Characterization of the density (the equations of P7 (1.5)): `famRhoRestricted_eq_of_cutoff` (the value
  `exp(-β₀ A_Z(ψ_k↾Z₀ = u, ψ_k))` on the cutoff `χ_{Z₀}`), `famRhoRestricted_eq_zero_of_not_cutoff`,
  `famRhoRestricted_eq_zero_of_not_tube`, `famRhoRestricted_eq_rhoZeroRestricted` (independence of the variables
  of the other components).
* `R_normalization_famDecompRestricted` (Lemma III.8.4), `Rop_famDecompRestricted_apply` (P7 (1.6)),
  `Rop_famDecompRestricted_factor` (factorization over separated components, with the densities of the removed kernel
  and no hypothesis `hrfam`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background MeasureTheory ActionConv

section Loc

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)

theorem dataRH_congr {ψ ψ' : BlockField d L N₀ k N} (h : Fin N → ℝ)
    (hψ : ∀ x ∈ dataSites G, ψ (jBlock d L N₀ k k x) = ψ' (jBlock d L N₀ k k x)) :
    dataRH G ψ h = dataRH G ψ' h := by
  have hΨ : (dataRH G ψ h).Ψ = (dataRH G ψ' h).Ψ := by
    rw [dataRH_Ψ, dataRH_Ψ, dataR_congr G hψ]
  have hh : (dataRH G ψ h).h = (dataRH G ψ' h).h := rfl
  cases hA : dataRH G ψ h
  cases hB : dataRH G ψ' h
  rw [hA, hB] at hΨ hh
  simp only at hΨ hh
  subst hΨ hh
  rfl

/-- The restricted action reads the field only at the blocks over the data sites. -/
theorem actionZ_congr (Zr : Region G) (ν : ℝ) (h : Fin N → ℝ) {ψ ψ' : BlockField d L N₀ k N}
    (hψ : ∀ x ∈ dataSites G, ψ (jBlock d L N₀ k k x) = ψ' (jBlock d L N₀ k k x)) :
    actionZ G a Zr ν h ψ = actionZ G a Zr ν h ψ' := by
  rw [actionZ_eq, actionZ_eq, dataRH_congr G h hψ, dataR_congr G hψ]

variable [NeZero N] {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **Locality of the restricted reference density**: `ρ^Z_{k,0}(Z)` as a function of `u = ψ_k↾Z₀` depends on the
outside field `ψ_k` only through `ψ_k↾(X ∖ Z₀)`. -/
theorem rhoZeroRestricted_congr {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk ψk' : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (hψk' : TubeOn G (X \ box b0 w) δ ψk') (Zr : Region G) (ν : ℝ)
    (h : Fin N → ℝ) (hXψ : ∀ z ∈ X \ box b0 w, ψk z = ψk' z) (β0 p0 : ℝ) :
    rhoZeroRestricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk' Zr ν h β0 p0 =
      rhoZeroRestricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0 := by
  funext u
  have hbX : ∀ z ∈ box b0 w, z ∈ X := fun z hz => hXreg (Or.inl hz)
  have hps := psiZero_congr G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hψk' hXψ
  have hcut : ZeroCutoff (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk')
      (zeroRadius (cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)) (betaK d L k β0) p0) u ↔
      ZeroCutoff (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk)
      (zeroRadius (cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)) (betaK d L k β0) p0) u := by
    unfold ZeroCutoff
    refine forall_congr' fun z => ?_
    have hz : (z : Torus d (N₀ * L ^ (k - k))) ∈ X := hbX _ (mem_boxFinset.1 z.2)
    rw [hps _ hz]
  have hact : actionZ G a Zr ν h (mergeField (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) ψk' u) =
      actionZ G a Zr ν h (mergeField (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) ψk u) := by
    refine actionZ_congr G a Zr ν h fun x hx => ?_
    have hxX := hdata x hx
    by_cases hz : jBlock d L N₀ k k x ∈ box b0 w
    · have hz' := mem_boxFinset.2 hz
      funext i
      rw [mergeField_of_mem hz' i, mergeField_of_mem hz' i]
    · have hz' : jBlock d L N₀ k k x ∉ boxFinset (L := L) (N₀ := N₀) (k := k) b0 w :=
        fun hh => hz (mem_boxFinset.1 hh)
      rw [mergeField_of_not_mem hz', mergeField_of_not_mem hz']
      exact (hXψ _ ⟨hxX, hz⟩).symm
  unfold rhoZeroRestricted rhoZeroRestrictedWith chiZeroCut
  rw [hact]
  by_cases hc : ZeroCutoff (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk)
      (zeroRadius (cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)) (betaK d L k β0) p0) u
  · simp [hc, hcut.2 hc]
  · simp [hc, mt hcut.1 hc]

end Loc

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
  (Zr : ∀ c, Region (G c))

local notation "Kc[" c "]" => psiZeroK N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H

open Classical in
/-- **The restricted reference density of the component `c` as a function of `(ψ_k↾Z₀(c), ψ_k↾(⋃_{c'∈σ} Z₀(c'))ᶜ)`**
(Definition III.8.1, P7 (1.5)): `rhoZeroRestricted` (the action restricted to `Z`, `Zr c` the region of the component
in the generating set `G c`) for the field with outside data `y` and zero on the components; `0` off the tube. -/
noncomputable def famRhoRestricted (σ : Finset ι) (ν : ℝ) (h : Fin N → ℝ) (β0 p0 : ℝ) (c : ι)
    (y : ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ) (u : SuppSpace (zb b0 w c) N) : ℝ :=
  if hT : FamTube N G b0 w X δ c (famOut N b0 w X hXreg hsep σ y) then
    rhoZeroRestricted (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hT
      (Zr c) ν h β0 p0 u
  else 0

/-- **The `RDecomp` of the restricted reference densities** (Definition III.8.3 with P7 (1.5)): `famDecompOf` with the
densities `famRhoRestricted`. -/
noncomputable def famDecompRestricted (σ : Finset ι) (ν : ℝ) (h : Fin N → ℝ) (β0 p0 : ℝ) :
    RDecomp (volume.restrict (famTubeSet N G b0 w X δ)) :=
  famDecompOf N G b0 w X hXreg hsep δ σ
    (fun c y u => famRhoRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h β0 p0
      c.1 y u)

/-- **Independence**: for `ψ_k` in the tube, the restricted density read through the outside variables is the
restricted reference density of `ψ_k` itself. -/
theorem famRhoRestricted_eq_rhoZeroRestricted (σ : Finset ι) (ν : ℝ) (h : Fin N → ℝ) (β0 p0 : ℝ) (c : ι)
    {ψ : BlockField d L N₀ k N} (hψ : FamTube N G b0 w X δ c ψ) :
    famRhoRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h β0 p0 c
        (famEquiv N b0 w X hXreg hsep σ ψ).2 =
      rhoZeroRestricted (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hψ
        (Zr c) ν h β0 p0 := by
  have hT := (fam_tube_iff N G b0 w X hXreg hsep δ σ ψ c).1 hψ
  funext u
  unfold famRhoRestricted
  simp only [hT, ↓reduceDIte]
  exact congrFun (rhoZeroRestricted_congr (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H
    (hδ c) (hδc c) hψ hT (Zr c) ν h (fun z hz => (famOut_eq_of_mem N b0 w X hXreg hsep σ ψ c hz).symm) β0 p0) u

/-- **P7 (1.5), on the cutoff**: for `ψ_k` in the tube and `u = ψ_k↾Z₀` in the cutoff `χ_{Z₀}` (radius
`C₆ β_k^{-1/2} p₀` about `ψ⁰_k`), `ρ_{k,0}(Z) = exp(-β₀ A_Z)` of the field `ψ_k` with `ψ_k↾Z₀ = u`. -/
theorem famRhoRestricted_eq_of_cutoff (σ : Finset ι) (ν : ℝ) (h : Fin N → ℝ) (β0 p0 : ℝ) (c : ι)
    {ψ : BlockField d L N₀ k N} (hψ : FamTube N G b0 w X δ c ψ) (u : SuppSpace (zb b0 w c) N)
    (hu : ZeroCutoff (psiZero N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c)
      (hδc c) hψ) (zeroRadius (cSix d D Kc[c]) (betaK d L k β0) p0) u) :
    famRhoRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h β0 p0 c
        (famEquiv N b0 w X hXreg hsep σ ψ).2 u =
      Real.exp (-β0 * actionZ (G c) a (Zr c) ν h (mergeField (zb b0 w c) ψ u)) := by
  rw [famRhoRestricted_eq_rhoZeroRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h
    β0 p0 c hψ]
  exact rhoZeroRestrictedWith_of_cutoff (Zr c) ν h _ _ _ _ β0 p0 u hu

/-- **P7 (1.5), off the cutoff**: the restricted density vanishes outside `χ_{Z₀}`. -/
theorem famRhoRestricted_eq_zero_of_not_cutoff (σ : Finset ι) (ν : ℝ) (h : Fin N → ℝ) (β0 p0 : ℝ) (c : ι)
    {ψ : BlockField d L N₀ k N} (hψ : FamTube N G b0 w X δ c ψ) (u : SuppSpace (zb b0 w c) N)
    (hu : ¬ ZeroCutoff (psiZero N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c)
      (hδc c) hψ) (zeroRadius (cSix d D Kc[c]) (betaK d L k β0) p0) u) :
    famRhoRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h β0 p0 c
        (famEquiv N b0 w X hXreg hsep σ ψ).2 u = 0 := by
  rw [famRhoRestricted_eq_rhoZeroRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h
    β0 p0 c hψ]
  exact rhoZeroRestrictedWith_eq_zero (Zr c) ν h _ _ _ _ β0 p0 u hu

/-- Off the tube the density is `0` (a null set of outside data). -/
theorem famRhoRestricted_eq_zero_of_not_tube (σ : Finset ι) (ν : ℝ) (h : Fin N → ℝ) (β0 p0 : ℝ) (c : ι)
    (y : ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ)
    (hy : ¬ FamTube N G b0 w X δ c (famOut N b0 w X hXreg hsep σ y)) (u : SuppSpace (zb b0 w c) N) :
    famRhoRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h β0 p0 c y u = 0 := by
  simp [famRhoRestricted, hy]

/-- Good fibres: integrable with positive integral on every fibre in the tube. -/
theorem famRhoRestricted_good (σ : Finset ι) {ν : ℝ} (h : Fin N → ℝ) (ha : ∀ j, 0 ≤ a j) (hν : 0 ≤ ν)
    {β0 p0 : ℝ} (hβ0 : 0 < β0) {c : ι}
    (hp0 : 1 ≤ cSix d D Kc[c] * p0)
    (hrad : Kc[c] * δ c + 5 * zeroRadius (cSix d D Kc[c]) (betaK d L k β0) p0 ≤ etaDen d L N D)
    {y : ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ}
    (hy : FamTube N G b0 w X δ c (famOut N b0 w X hXreg hsep σ y)) :
    Integrable (famRhoRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h β0 p0 c y)
        volume ∧
      0 < ∫ u, famRhoRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h β0 p0 c y u := by
  have hfun : famRhoRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h β0 p0 c y =
      rhoZeroRestricted (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H (hδ c) (hδc c) hy
        (Zr c) ν h β0 p0 := by
    funext u
    simp only [famRhoRestricted, hy, ↓reduceDIte]
  rw [hfun]
  exact integrable_rhoZeroRestricted (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H
    (hδ c) (hδc c) hy (Zr c) h ha hν hβ0 hp0 hrad

/-- The joint measurability of the restricted reference densities in `(ψ_k↾Z₀(c), y)`. -/
theorem measurable_famRhoRestricted (σ : Finset ι) (ν : ℝ) (h : Fin N → ℝ) {β0 p0 : ℝ} (hβ0 : 0 < β0) (c : ι)
    (hp0 : 1 ≤ cSix d D Kc[c] * p0)
    (hrad : Kc[c] * δ c + 5 * zeroRadius (cSix d D Kc[c]) (betaK d L k β0) p0 ≤ etaDen d L N D) :
    Measurable (fun p : SuppSpace (zb b0 w c) N × (ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ) =>
      famRhoRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h β0 p0 c p.2 p.1) := by
  have hm' := measurable_rhoZeroRestrictedTot N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c)
    (hdata c) H (hδ c) (hδc c) (Zr c) ν h hβ0 hp0 hrad
  have hout : Measurable (famOut N b0 w X hXreg hsep σ) := famOut_measurable N b0 w X hXreg hsep σ
  have h2 := hm'.comp (measurable_fst.prodMk (hout.comp measurable_snd))
  convert h2 using 1
  funext p
  by_cases hT : FamTube N G b0 w X δ c (famOut N b0 w X hXreg hsep σ p.2)
  · simp only [famRhoRestricted, Function.comp, hT, dite_true]
  · simp only [famRhoRestricted, Function.comp, hT, dite_false]

/-- **Lemma III.8.4 (normalization) with the restricted reference densities**: `∫ R[ρ] = ∫ ρ` over `Ψ̃`. -/
theorem R_normalization_famDecompRestricted (σ : Finset ι) {ν : ℝ} (h : Fin N → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hν : 0 ≤ ν) {β0 p0 : ℝ} (hβ0 : 0 < β0)
    (hp0 : ∀ c ∈ σ, 1 ≤ cSix d D Kc[c] * p0)
    (hrad : ∀ c ∈ σ, Kc[c] * δ c + 5 * zeroRadius (cSix d D Kc[c]) (betaK d L k β0) p0 ≤ etaDen d L N D)
    {ρ : BlockField d L N₀ k N → ℝ} (hρ : Integrable ρ (volume.restrict (famTubeSet N G b0 w X δ))) :
    Integrable (Rop (famDecompRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h
        β0 p0) ρ) (volume.restrict (famTubeSet N G b0 w X δ)) ∧
      ∫ ψ, Rop (famDecompRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h
          β0 p0) ρ ψ ∂(volume.restrict (famTubeSet N G b0 w X δ)) =
        ∫ ψ, ρ ψ ∂(volume.restrict (famTubeSet N G b0 w X δ)) := by
  refine R_normalization_famDecompOf N G b0 w X hXreg hsep δ σ _ ?_ ?_ ?_ hρ
  · intro c
    exact measurable_famRhoRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h hβ0
      c.1 (hp0 c.1 c.2) (hrad c.1 c.2)
  · intro c y u
    unfold famRhoRestricted
    split_ifs
    · exact rhoZeroRestrictedWith_nonneg _ _ _ _ _ _ _ _ _ _
    · exact le_rfl
  · intro y hy c
    exact famRhoRestricted_good N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ h ha hν hβ0
      (hp0 c.1 c.2) (hrad c.1 c.2) (hy c.1)

/-- **The operation `R` with the restricted reference densities** (P7 (1.6)): at a field in the tube,
`R[ρ](ψ_k) = ∏_Z ρ^Z_{k,0}(Z)(ψ_k↾Z₀) · (∫ dψ_k↾𝒵_{σ,0} ρ) / ∏_Z ∫ dψ_k↾Z₀ ρ^Z_{k,0}(Z)`. -/
theorem Rop_famDecompRestricted_apply (σ : Finset ι) (ν : ℝ) (h : Fin N → ℝ) (β0 p0 : ℝ)
    (ρ : BlockField d L N₀ k N → ℝ) {ψ : BlockField d L N₀ k N} (hψ : ψ ∈ famTubeSet N G b0 w X δ) :
    Rop (famDecompRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h β0 p0) ρ ψ =
      (∏ c : σ, rhoZeroRestricted (G c.1) a hd hk (b0 c.1) (w c.1) (hw1 c.1) (hwD c.1) hm (hXreg c.1) (hΩ c.1)
          (hdata c.1) H (hδ c.1) (hδc c.1) (hψ c.1) (Zr c.1) ν h β0 p0 (restrictSupp (zb b0 w c.1) ψ)) *
        ((∫ x, ρ ((famEquiv N b0 w X hXreg hsep σ).symm (x, (famEquiv N b0 w X hXreg hsep σ ψ).2))
            ∂(Measure.pi fun c : σ => (volume : Measure (SuppSpace (zb b0 w c.1) N)))) /
          ∏ c : σ, ∫ u, rhoZeroRestricted (G c.1) a hd hk (b0 c.1) (w c.1) (hw1 c.1) (hwD c.1) hm (hXreg c.1)
            (hΩ c.1) (hdata c.1) H (hδ c.1) (hδc c.1) (hψ c.1) (Zr c.1) ν h β0 p0 u) := by
  have hr : ∀ c : σ, famRhoRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h β0 p0
      c.1 (famEquiv N b0 w X hXreg hsep σ ψ).2 =
      rhoZeroRestricted (G c.1) a hd hk (b0 c.1) (w c.1) (hw1 c.1) (hwD c.1) hm (hXreg c.1) (hΩ c.1) (hdata c.1) H
        (hδ c.1) (hδc c.1) (hψ c.1) (Zr c.1) ν h β0 p0 := fun c =>
    famRhoRestricted_eq_rhoZeroRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h β0
      p0 c.1 (hψ c.1)
  have key := Rop_famDecompOf_apply N G b0 w X hXreg hsep δ σ
    (fun c y u => famRhoRestricted N G a hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h β0 p0
      c.1 y u) ρ ψ
  refine key.trans ?_
  simp only [hr]

end Fam

end Balaban.LargeField
