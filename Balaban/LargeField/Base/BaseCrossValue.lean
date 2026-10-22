/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseCrossAgree
public import Balaban.LargeField.Base.BaseBgFunctional

/-!
# A functional of the decoupled background, on a level set and on a local generating set

For a level set `Gp` and a generating set `Gl` at the same top level, the background maps
`Fp (s', θ')` and `Fl (s, θ)` of the two pairs are the decoupled backgrounds (`hF`).  If the
parameters `s`, `s'` agree on the top layer of `Gl` and their active cubes have their interaction
cubes inside `T`, if the data agree on `approxDep` of the neighbourhood `Y` of `T`, and if two
functionals `Fel`, `Fep` of the backgrounds read the same seed `seed ⊆ T` (`ReadsSeedCross`), then
`Fel (Fl (s, θ)) = Fep (Fp (s', θ'))` (`bgFunctional_value_cross`), and the coefficients of the two
functions of a common parameter agree (`bgFunctional_coef_cross`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField Balaban.Green Balaban.Analysis

section Cross

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱl : ℝ}
  (Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl)
  (Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)

/-- Two functionals of the backgrounds on two generating sets read the same seed: they take the same
value on backgrounds that agree at the sites of the seed. -/
def ReadsSeedCross (seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
    (Fel : ((Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)) → ℂ)
    (Fep : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → ℂ) : Prop :=
  ∀ (u : (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)) (u' : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)),
    (∀ (y : Gl.Ω 1) (y' : Gp.Ω 1), (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) = y' →
      (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ seed → ∀ i, u.1 (y, i) = u'.1 (y', i)) →
    (∀ (x : Gl.Ω 1) (x' : Gp.Ω 1), (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) = x' →
      (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ seed → u.2 x = u'.2 x') →
    Fel u = Fep u'

/-- **Inhabitation**: a functional that reads a seed on one generating set reads it, against itself,
in the cross sense. -/
theorem readsSeedCross_self {seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {Fe : ((Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)) → ℂ} (h : ReadsSeed Gl seed Fe) :
    ReadsSeedCross Gl Gl seed Fe Fe := fun u u' h1 h2 =>
  h u u' (fun y hy i => h1 y y rfl hy i) (fun x hx => h2 x x rfl hx)

variable {a : ℕ → ℝ} {ν : ℝ}

/-- **A functional of the decoupled background takes the same value on a level set and on a local
generating set.**  Let `Gp` be a level set, `Gl` a generating set at the same top level, `Fl`, `Fp` the
background maps of the two pairs (`hFl`, `hFp`), `T` a set whose `8 L^{k+1+m₁}`-neighbourhood lies in the
top layer of `Gl`, `Y ⊇ T` a neighbourhood of `T`.  For parameters `s`, `s'` of the open polydisc that
agree on the top layer of `Gl` and whose active cubes have their interaction cubes inside `T`, and data
of the union domain that agree on `approxDep` of the sites of `Y`, two functionals reading the same
seed `seed ⊆ T` take the same value. -/
theorem bgFunctional_value_cross (hG' : IsLevel Gp (k + 1)) (hm₁ : 2 ≤ m₁)
    {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sl : Dec2.CoverBase (coverOf Gl) Gl a ν Kc Cx) (Sp : Dec2.CoverBase (coverOf Gp) Gp a ν Kc Cx)
    (HBl : BgHyp d L (k + 1) ϱl a ν) (HBp : BgHyp d L (k + 1) ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
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
    {v : Dec2.DecParams (coverOf Gl)} {v' : Dec2.DecParams (coverOf Gp)}
    (hv : ∀ P, ‖v P‖ < Real.exp κ) (hv' : ∀ P, ‖v' P‖ < Real.exp κ)
    {T Y : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} (hTY : T ⊆ Y)
    (hdepth : ∀ z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1), (∃ t ∈ T, supDist z t ≤ 8 * L ^ (k + 1 + m₁)) → z ∈ Gl.Ω (k + 1))
    (hYT : ∀ y ∈ Y, ∃ t ∈ T, supDist y t ≤ 2 * L ^ (k + 1))
    (hresY : ∀ x ∈ T, ∀ y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1), supDist x y ≤ L ^ (k + 1) → y ∈ Y)
    (hvv : ∀ P : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1), P.2 ∈ Gl.Ω (k + 1) →
      Dec2.extS (coverOf Gl) v P = Dec2.extS (coverOf Gp) v' P)
    (hactl : ∀ q ∈ (coverOf Gl).cubeIdx, (coverOf Gl).sProd (Dec2.extS _ v) q ≠ 0 →
      ∀ x ∈ intBox q, x ∈ T)
    (hactp : ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS _ v') q ≠ 0 →
      ∀ x ∈ intBox q, x ∈ T)
    (hdat : ∀ y ∈ Y, y ∈ Gl.Ω 1 → ∀ z ∈ approxDep Gl y, D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z)
    {seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} (hseed : seed ⊆ T)
    {Fel : ((Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)) → ℂ}
    {Fep : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → ℂ} (hFe : ReadsSeedCross Gl Gp seed Fel Fep) :
    Fel (Fl (v, (D.Ψ, D.h))) = Fep (Fp (v', (D'.Ψ, D'.h))) := by
  classical
  obtain ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hD⟩ := hDu
  obtain ⟨δ', ε', hδ0', hδε', hε', hδ', hνε', hD'⟩ := hDu'
  obtain ⟨φ, α, hsol, -, -⟩ := Dec2.i4b_exists_unique hS Sl HBl hκ hM (fun P => (hv P).le) hδ0 hδε
    hε hδ hνε hD
  obtain ⟨φ', α', hsol', -, -⟩ := Dec2.i4b_exists_unique hS Sp HBp hκ hM (fun P => (hv' P).le) hδ0'
    hδε' hε' hδ' hνε' hD'
  rw [hFl v D hv ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hD⟩ φ α hsol,
    hFp v' D' hv' ⟨δ', ε', hδ0', hδε', hε', hδ', hνε', hD'⟩ φ' α' hsol']
  obtain ⟨hα, hφ⟩ := decBg_cross_level hG' hm₁ hS Sl Sp HBl HBp hκ hM (fun P => (hv P).le)
    (fun P => (hv' P).le) hδ0 hδε hε hδ hνε hδ0' hδε' hε' hδ' hνε' hD hD' hTY hdepth hYT hresY hvv
    hactl hactp hdat hsol hsol'
  refine hFe _ _ (fun y y' hyy hy i => ?_) (fun x x' hxx hx => ?_)
  · have hy' : (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Gp.Ω 1 := hyy ▸ y'.2
    have e : y' = ⟨y, hy'⟩ := Subtype.ext hyy.symm
    rw [e]
    exact (hφ y y.2 hy' (hTY (hseed hy)) i).symm
  · have hx' : (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Gp.Ω 1 := hxx ▸ x'.2
    have e : x' = ⟨x, hx'⟩ := Subtype.ext hxx.symm
    rw [e]
    exact (hα x x.2 hx' (hseed hx)).symm

/-- **The coefficients of the background functional agree on a level set and on a local generating
set.**  For a common parameter space `ι ∋ w` mapped into the parameters of the two covers by `τ`, `σ`,
and a family `C ⊆ ι`, the hypotheses of `bgFunctional_value_cross` for `v = τ w`, `v' = σ w`, at every
`w` of `supN C R` (`R > 1`), give the equality of the coefficients
`coef_C (w ↦ Fel (Fl (τ w, θ))) = coef_C (w ↦ Fep (Fp (σ w, θ')))`. -/
theorem bgFunctional_coef_cross (hG' : IsLevel Gp (k + 1)) (hm₁ : 2 ≤ m₁)
    {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sl : Dec2.CoverBase (coverOf Gl) Gl a ν Kc Cx) (Sp : Dec2.CoverBase (coverOf Gp) Gp a ν Kc Cx)
    (HBl : BgHyp d L (k + 1) ϱl a ν) (HBp : BgHyp d L (k + 1) ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
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
    {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Finset ι) {R : ℝ} (hR : 1 < R)
    (τ : (ι → ℂ) → Dec2.DecParams (coverOf Gl)) (σ : (ι → ℂ) → Dec2.DecParams (coverOf Gp))
    (hv : ∀ w ∈ supN C R, ∀ P, ‖τ w P‖ < Real.exp κ)
    (hv' : ∀ w ∈ supN C R, ∀ P, ‖σ w P‖ < Real.exp κ)
    {T Y : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} (hTY : T ⊆ Y)
    (hdepth : ∀ z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1), (∃ t ∈ T, supDist z t ≤ 8 * L ^ (k + 1 + m₁)) → z ∈ Gl.Ω (k + 1))
    (hYT : ∀ y ∈ Y, ∃ t ∈ T, supDist y t ≤ 2 * L ^ (k + 1))
    (hresY : ∀ x ∈ T, ∀ y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1), supDist x y ≤ L ^ (k + 1) → y ∈ Y)
    (hvv : ∀ w ∈ supN C R, ∀ P : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1), P.2 ∈ Gl.Ω (k + 1) →
      Dec2.extS (coverOf Gl) (τ w) P = Dec2.extS (coverOf Gp) (σ w) P)
    (hactl : ∀ w ∈ supN C R, ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd (Dec2.extS _ (τ w)) q ≠ 0 → ∀ x ∈ intBox q, x ∈ T)
    (hactp : ∀ w ∈ supN C R, ∀ q ∈ (coverOf Gp).cubeIdx,
      (coverOf Gp).sProd (Dec2.extS _ (σ w)) q ≠ 0 → ∀ x ∈ intBox q, x ∈ T)
    (hdat : ∀ y ∈ Y, y ∈ Gl.Ω 1 → ∀ z ∈ approxDep Gl y, D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z)
    {seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} (hseed : seed ⊆ T)
    {Fel : ((Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)) → ℂ}
    {Fep : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → ℂ} (hFe : ReadsSeedCross Gl Gp seed Fel Fep) :
    coef (fun w => Fel (Fl (τ w, (D.Ψ, D.h)))) C = coef (fun w => Fep (Fp (σ w, (D'.Ψ, D'.h)))) C :=
  coef_congr_near hR fun w hw =>
    bgFunctional_value_cross Gl Gp hG' hm₁ hS Sl Sp HBl HBp hκ hM hFl hFp hDu hDu' (hv w hw)
      (hv' w hw) hTY hdepth hYT hresY (hvv w hw) (hactl w hw) (hactp w hw) hdat hseed hFe

end Cross

end Balaban.LargeField.Base
