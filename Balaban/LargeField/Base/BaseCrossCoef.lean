/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseCrossValue
public import Balaban.Polymer.TwoTorusEv

/-!
# The coefficient of a family of cells on a level set and on a local generating set

A family `Cs` of cubes of the cover of `Gl` whose interaction cubes lie in a deep set `T` is carried to the
family `Cs.image (crossCubeMap Gp d0)` of cubes of the cover of the level set `Gp`; the coefficients of a
functional of the decoupled background of the two systems agree
(`bgFunctional_coef_relabel_cross`, from `bgFunctional_value_cross` and the relabelling of coefficients
`coef_relabel_injOn`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField Balaban.Green Balaban.Analysis

section Relabel

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱl : ℝ}
  (Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl)
  (Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)

open Classical in
/-- The map from the cubes of the cover of `Gl` to those of `Gp`: the identity on the common cubes, a
fixed cube `d0` elsewhere. -/
noncomputable def crossCubeMap (d0 : ↥(coverOf Gp).cubeIdx) : ↥(coverOf Gl).cubeIdx → ↥(coverOf Gp).cubeIdx :=
  fun P => if h : P.1 ∈ (coverOf Gp).cubeIdx then ⟨P.1, h⟩ else d0

theorem crossCubeMap_of_mem (d0 : ↥(coverOf Gp).cubeIdx) {P : ↥(coverOf Gl).cubeIdx}
    (h : P.1 ∈ (coverOf Gp).cubeIdx) : crossCubeMap Gl Gp d0 P = ⟨P.1, h⟩ := by
  classical
  unfold crossCubeMap
  simp only [h, ↓reduceDIte]

theorem crossCubeMap_cubeMap (d0 : ↥(coverOf Gp).cubeIdx) (d0l : ↥(coverOf Gl).cubeIdx)
    {i : ↥(coverOf Gl).cubeIdx} (h : i.1 ∈ (coverOf Gp).cubeIdx) :
    crossCubeMap Gp Gl d0l (crossCubeMap Gl Gp d0 i) = i := by
  rw [crossCubeMap_of_mem Gl Gp d0 h]
  rw [crossCubeMap_of_mem Gp Gl d0l (show (⟨i.1, h⟩ : ↥(coverOf Gp).cubeIdx).1 ∈ (coverOf Gl).cubeIdx from i.2)]

variable {a : ℕ → ℝ} {ν : ℝ}

theorem crossCubeMap_hvv (hG' : IsLevel Gp (k + 1)) (d0 : ↥(coverOf Gp).cubeIdx)
    {Cs : Finset ↥(coverOf Gl).cubeIdx}
    (hmem : ∀ i ∈ Cs, (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ (coverOf Gp).cubeIdx)
    {s : Dec2.DecParams (coverOf Gl)} {s' : Dec2.DecParams (coverOf Gp)}
    (hsupp : ∀ i : ↥(coverOf Gl).cubeIdx, i ∉ Cs → s i = 0)
    (hs' : ∀ P, P ∉ Cs.image (crossCubeMap Gl Gp d0) → s' P = 0)
    (hss' : ∀ i ∈ Cs, s' (crossCubeMap Gl Gp d0 i) = s i) :
    ∀ P : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1), P.2 ∈ Gl.Ω (k + 1) →
      Dec2.extS (coverOf Gl) s P = Dec2.extS (coverOf Gp) s' P := by
  classical
  intro P hP
  by_cases hPl : P ∈ (coverOf Gl).cubeIdx
  · have hPp : P ∈ (coverOf Gp).cubeIdx := (level_mem_cubeIdx_iff_of_mem_top hG' hP).2 hPl
    unfold Dec2.extS
    simp only [hPl, hPp, ↓reduceDIte]
    by_cases hPC : (⟨P, hPl⟩ : ↥(coverOf Gl).cubeIdx) ∈ Cs
    · have := hss' _ hPC
      rw [crossCubeMap_of_mem Gl Gp d0 (hmem _ hPC)] at this
      exact this.symm
    · rw [hsupp _ hPC]
      by_contra hne
      have hP' : (⟨P, hPp⟩ : ↥(coverOf Gp).cubeIdx) ∈ Cs.image (crossCubeMap Gl Gp d0) := by
        by_contra hn
        exact hne (hs' _ hn).symm
      obtain ⟨i, hi, hie⟩ := Finset.mem_image.1 hP'
      rw [crossCubeMap_of_mem Gl Gp d0 (hmem i hi)] at hie
      have hiP : (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) = P := Subtype.mk.inj hie
      exact hPC (by
        have : i = ⟨P, hPl⟩ := Subtype.ext hiP
        exact this ▸ hi)
  · have hPp : P ∉ (coverOf Gp).cubeIdx := fun h => hPl ((level_mem_cubeIdx_iff_of_mem_top hG' hP).1 h)
    unfold Dec2.extS
    simp only [hPl, hPp, ↓reduceDIte]

theorem crossCubeMap_actl {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} {Cs : Finset ↥(coverOf Gl).cubeIdx}
    {s : Dec2.DecParams (coverOf Gl)} (hsupp : ∀ i : ↥(coverOf Gl).cubeIdx, i ∉ Cs → s i = 0)
    (hCT : ∀ i ∈ Cs, ∀ x ∈ intBox (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)), x ∈ T) :
    ∀ q ∈ (coverOf Gl).cubeIdx, (coverOf Gl).sProd (Dec2.extS _ s) q ≠ 0 →
      ∀ x ∈ intBox q, x ∈ T := by
  classical
  intro q hq hne
  have hq0 : Dec2.extS (coverOf Gl) s q ≠ 0 := fun h0 =>
    hne (Finset.prod_eq_zero (self_mem_Qset hq) h0)
  have hqC : (⟨q, hq⟩ : ↥(coverOf Gl).cubeIdx) ∈ Cs := by
    by_contra hn
    apply hq0
    unfold Dec2.extS
    simp only [hq, ↓reduceDIte]
    exact hsupp _ hn
  exact hCT ⟨q, hq⟩ hqC

theorem crossCubeMap_actp (d0 : ↥(coverOf Gp).cubeIdx) {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {Cs : Finset ↥(coverOf Gl).cubeIdx}
    (hmem : ∀ i ∈ Cs, (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ (coverOf Gp).cubeIdx)
    {s' : Dec2.DecParams (coverOf Gp)}
    (hs' : ∀ P, P ∉ Cs.image (crossCubeMap Gl Gp d0) → s' P = 0)
    (hCT : ∀ i ∈ Cs, ∀ x ∈ intBox (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)), x ∈ T) :
    ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS _ s') q ≠ 0 →
      ∀ x ∈ intBox q, x ∈ T := by
  classical
  intro q hq hne
  have hq0 : Dec2.extS (coverOf Gp) s' q ≠ 0 := fun h0 =>
    hne (Finset.prod_eq_zero (self_mem_Qset hq) h0)
  have hqC : (⟨q, hq⟩ : ↥(coverOf Gp).cubeIdx) ∈ Cs.image (crossCubeMap Gl Gp d0) := by
    by_contra hn
    apply hq0
    unfold Dec2.extS
    simp only [hq, ↓reduceDIte]
    exact hs' _ hn
  obtain ⟨i, hi, hie⟩ := Finset.mem_image.1 hqC
  rw [crossCubeMap_of_mem Gl Gp d0 (hmem i hi)] at hie
  have hiq : (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) = q := Subtype.mk.inj hie
  intro x hx
  exact hCT i hi x (hiq ▸ hx)

/-- **The coefficients of a functional of the decoupled background agree on a level set and on a local
generating set.**  Let `Cs` be a family of cubes of the cover of `Gl` whose interaction cubes lie in a
set `T` whose `8 L^{k+1+m₁}`-neighbourhood lies in the top layer of `Gl`, and let two data of the union
domains of `Gl`, `Gp` agree on `approxDep` of the sites of the neighbourhood `Y` of `T`.  If `Fel`, `Fep`
read the same seed `seed ⊆ T`, the coefficient of `Cs` for `Gl` equals that of its image for `Gp`. -/
theorem bgFunctional_coef_relabel_cross (hG' : IsLevel Gp (k + 1)) (hm₁ : 2 ≤ m₁)
    {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sl : Dec2.CoverBase (coverOf Gl) Gl a ν Kc Cx) (Sp : Dec2.CoverBase (coverOf Gp) Gp a ν Kc Cx)
    (HBl : BgHyp d L (k + 1) ϱl a ν) (HBp : BgHyp d L (k + 1) ϱ a ν) {κ : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {Fl : Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    {Fp : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hFl : ∀ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl a ν (rho4 d L N BG κ) s D φ α →
          Fl (s, (D.Ψ, D.h)) = (φ, α))
    (hFp : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp a ν (rho4 d L N BG κ) s D φ α →
          Fp (s, (D.Ψ, D.h)) = (φ, α))
    {D : BgData Gl N} {D' : BgData Gp N}
    (hDu : InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDu' : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D')
    {Fel : ((Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)) → ℂ}
    {Fep : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → ℂ}
    (hfl : AnalyticOnNhd ℂ (fun s => Fel (Fl (s, (D.Ψ, D.h))))
      (polydisc (0 : Dec2.DecParams (coverOf Gl)) (fun _ => Real.exp κ)))
    (Cs : Finset ↥(coverOf Gl).cubeIdx) (d0 : ↥(coverOf Gp).cubeIdx)
    {T Y : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} (hTY : T ⊆ Y)
    (hdepth : ∀ z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1), (∃ t ∈ T, supDist z t ≤ 8 * L ^ (k + 1 + m₁)) → z ∈ Gl.Ω (k + 1))
    (hYT : ∀ y ∈ Y, ∃ t ∈ T, supDist y t ≤ 2 * L ^ (k + 1))
    (hresY : ∀ x ∈ T, ∀ y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1), supDist x y ≤ L ^ (k + 1) → y ∈ Y)
    (hCT : ∀ i ∈ Cs, ∀ x ∈ intBox (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)), x ∈ T)
    (hdat : ∀ y ∈ Y, y ∈ Gl.Ω 1 → ∀ z ∈ approxDep Gl y, D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z)
    {seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} (hseed : seed ⊆ T) (hFe : ReadsSeedCross Gl Gp seed Fel Fep) :
    coef (fun s' => Fep (Fp (s', (D'.Ψ, D'.h)))) (Cs.image (crossCubeMap Gl Gp d0)) =
      coef (fun s => Fel (Fl (s, (D.Ψ, D.h)))) Cs := by
  classical
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have htop : ∀ i ∈ Cs, (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)).2 ∈ Gl.Ω (k + 1) := fun i hi =>
    hdepth _ ⟨_, hCT i hi _ (Localization.base_mem_intBox _), by rw [supDist_self]; exact Nat.zero_le _⟩
  have hmem : ∀ i ∈ Cs, (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ (coverOf Gp).cubeIdx := fun i hi =>
    (level_mem_cubeIdx_iff_of_mem_top hG' (htop i hi)).2 i.2
  have hinj : Set.InjOn (crossCubeMap Gl Gp d0) (Cs : Set ↥(coverOf Gl).cubeIdx) := by
    intro i hi j hj hij
    rw [crossCubeMap_of_mem Gl Gp d0 (hmem i hi), crossCubeMap_of_mem Gl Gp d0 (hmem j hj)] at hij
    exact Subtype.ext (Subtype.mk.inj hij)
  refine Balaban.Polymer.TwoTorusStep.coef_relabel_injOn hR (crossCubeMap Gl Gp d0) hinj hfl ?_
  intro s hs s' hs' hss'
  have hsb : ∀ P, ‖s P‖ < Real.exp κ := hs.2
  have hsupp : ∀ i : ↥(coverOf Gl).cubeIdx, i ∉ Cs → s i = 0 := fun i hi => hs.1 i hi
  have hsb' : ∀ P, ‖s' P‖ < Real.exp κ := by
    intro P
    by_cases hP : P ∈ Cs.image (crossCubeMap Gl Gp d0)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP
      rw [hss' i hi]; exact hsb i
    · rw [hs' P hP, norm_zero]; exact Real.exp_pos κ
  exact (bgFunctional_value_cross Gl Gp hG' hm₁ hS Sl Sp HBl HBp hκ.le hM hFl hFp hDu hDu' hsb hsb'
    hTY hdepth hYT hresY (crossCubeMap_hvv Gl Gp hG' d0 hmem hsupp hs' hss')
    (crossCubeMap_actl Gl hsupp hCT) (crossCubeMap_actp Gl Gp d0 hmem hs' hCT) hdat hseed hFe).symm

end Relabel

end Balaban.LargeField.Base
