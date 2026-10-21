/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelTermsBgRot
public import Balaban.Inhabited.NewLevelObjectsBgLocal
public import Balaban.Inhabited.E0CoeffFamilyRotBlock
public import Balaban.Inhabited.E0CoeffFamilyRotAct
public import Balaban.Fluctuation.Prop33SymmDef

/-!
# Spin covariance of the objects of the new level recomputed on a local generating set

P3 pp. 78-79 (route R-LOC, the form of (A4)): the zero-source activities, and the terms of the
block energies and of the old terms, recomputed on a background generating set `Gb` with the
canonical transport, are covariant under a real rotation of the parameter and of the block
variables.

* `rotFld_lin`: the spin rotation of a combination of hat variables;
* `zeroTermBg_canon_rot`, `zeroActBg_canon_rot`: the zero-source terms and activities of a label
  with the margin in `Gb` (`evDecBg_canon_rot` along the rays, the block energies being invariant);
* `blockEvBg_canon_rot`: the terms of the block energies at the rotated datum and hat variable (the
  input of the congruence lemma `e1MarkGParamGBgOn_congr_of_terms`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.LargeField Balaban.Polymer Finset Matrix

section Lin

/-- The spin rotation of a combination of hat variables. -/
theorem rotFld_lin {ι : Type*} {N : ℕ} (R : Matrix (Fin N) (Fin N) ℂ) (a b : ℂ)
    (x w : ι × Fin N → ℂ) : rotFld R (a • x + b • w) = a • rotFld R x + b • rotFld R w := by
  rw [DecEquiv.rotFld_add, rotFld_smul', rotFld_smul']

end Lin

section Rot

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {Kc Cx : ℝ}

open Classical in
/-- **Spin covariance of the terms of a block energy recomputed on `Gb`**: for a block `z` whose
region `X₁(z)` lies in the top layer of `Gb`, `evDecBg … (blockEnergyFun … z) … Y` at the rotated
datum and the rotated hat variable equals its value at the datum and the hat variable. -/
theorem blockEvBg_canon_rot {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L S.a₁) S.ν Kc Cx)
    {κ eps c₂ BG₂ δ₁ Kf Cf : ℝ} (hC : FlCore N Gb Hm S.a₁ S.ν c BG κ eps Kf Cf c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gb) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ), IsDecBg Gb (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gb) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX₁top : ∀ x ∈ X₁f, x ∈ Gb.Ω (k + 1))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Qᵀ * Q = 1) (Zb : Finset (unitPts Gb)) {um tm : ℂ}
    (hW : (‖um‖ + ‖tm‖) * markedRad d L N k S.a₁ κ cψ cc < δ₁)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) {D : BgData Gb N}
    (hD : XiCData Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps D) {ψh : unitPts S.G' × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    evDecBg S.G' X₁f m₀ j 𝒦X Gb S.a₁ S.ν (BgTransport.canon S.G' Gb N) cc F₁ Sol
        (blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k z) Zb um tm Y
        (rotRaw (cmat Q) (rawOf D), (BgTransport.canon S.G' Gb N).res (rotFld (cmat Q) ψh)) =
      evDecBg S.G' X₁f m₀ j 𝒦X Gb S.a₁ S.ν (BgTransport.canon S.G' Gb N) cc F₁ Sol
        (blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k z) Zb um tm Y
        (rawOf D, (BgTransport.canon S.G' Gb N).res ψh) :=
  evDecBg_canon_rot S hS Sb hC S.hk1 hHm cc hcψ hMX hmar hα hsm hF₁ hSol hX₁top hQ
    (fun bg δφ u _ _ => energyBlock_rot (isRealOrth_ofReal hQ).1 _ S.ν k bg.2 δφ u.2 z) Zb hW Y hD
    hψh

open Classical in
/-- **Spin covariance of the zero-source terms recomputed on `Gb`** (P3 pp. 78-79): for a label `Y`
with the margin in `Gb` and a ray inside the box `|ψ̂| ≤ c_ψ`, the zero-source term `zeroTermBg` at
the rotated datum and the rotated ray equals its value at the datum and the ray. -/
theorem zeroTermBg_canon_rot {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L S.a₁) S.ν Kc Cx)
    {κ eps c₂ BG₂ δ₁ Kf Cf : ℝ} (hC : FlCore N Gb Hm S.a₁ S.ν c BG κ eps Kf Cf c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {m₀ : ℕ}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    (hX₁ : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV z) (𝒦XV z))
    {F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁ : ∀ z (s : DecParams Gb) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ), IsDecBg Gb (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ z (s, rawOf D) = (φ, α))
    {Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ z (p : Dec2.DecParams (coverOf Gb) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol z p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2))
    (hδ₁c : markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (ω : ℂ → ℂ) {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hYm : LabelMargin Gb Y)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (x₀ w : unitPts S.G' × Fin N → ℂ) (σ : ℂ) (hσx : ∀ q, ‖σ‖ * ‖x₀ q‖ < cψ)
    {D : BgData Gb N} (hD : XiCData Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps D) :
    zeroTermBg S Gb (BgTransport.canon S.G' Gb N) X₁V jV 𝒦XV m₀ F₁ Sol ω Y
        (rotFld (cmat Q) x₀) (rotFld (cmat Q) w) σ (rotRaw (cmat Q) (rawOf D)) =
      zeroTermBg S Gb (BgTransport.canon S.G' Gb N) X₁V jV 𝒦XV m₀ F₁ Sol ω Y x₀ w σ
        (rawOf D) := by
  have hW : (‖(1 : ℂ)‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ := by
    rw [norm_one, norm_zero, add_zero, one_mul]
    exact hδ₁c
  unfold zeroTermBg
  refine congrArg (fun x => -(S.β : ℂ) * x) (Finset.sum_congr rfl fun z _ => ?_)
  by_cases hY : Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z)
  · simp only [hY, ↓reduceIte]
    have htop : ∀ x ∈ X₁V z, x ∈ Gb.Ω (k + 1) := fun x hx =>
      hYm.subset x (subset_polyDom hY (by rw [← hX₁ z]; exact hx))
    obtain ⟨r, hr, hseg⟩ := exists_segment_of_norm_lt (w := w) hσx
    refine rayTerm_dl3_congr_of_line_of ω fun t ht => ⟨r, hr, fun τ hτ => ?_⟩
    show evDecBg S.G' (X₁V z) m₀ (jV z) (𝒦XV z) Gb S.a₁ S.ν (BgTransport.canon S.G' Gb N)
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ z) (Sol z)
        (blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k z) ∅ 1 0 Y
        (rotRaw (cmat Q) (rawOf D), (BgTransport.canon S.G' Gb N).res
          ((σ * (t : ℂ)) • rotFld (cmat Q) x₀ + τ • rotFld (cmat Q) w)) =
      evDecBg S.G' (X₁V z) m₀ (jV z) (𝒦XV z) Gb S.a₁ S.ν (BgTransport.canon S.G' Gb N)
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ z) (Sol z)
        (blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k z) ∅ 1 0 Y
        (rawOf D, (BgTransport.canon S.G' Gb N).res ((σ * (t : ℂ)) • x₀ + τ • w))
    rw [← rotFld_lin]
    exact blockEvBg_canon_rot S hS Sb hC hHm _ hcψ hMX hmar hα hsm (hF₁ z) (hSol z) htop z hQ ∅ hW Y
      hD (hseg t ht τ hτ)
  · simp only [hY, ↓reduceIte]

open Classical in
/-- **Spin covariance of the zero-source activities recomputed on `Gb`** (P3 pp. 78-79): for a
label `Y` with the margin in `Gb`, `2 ρ ≤ c_ψ`, a real orthogonal `Q` with its isometry `e` of the
block variables, two parameters `θ`, `θ'` of `Gb` with `θ'.raw = Q θ.raw`, `θ.raw = rawOf D` in the
chart, and a configuration `Φ` of the step's carrier,
`zeroActBg … θ' u Y (e Φ) = zeroActBg … θ u Y Φ`. -/
theorem zeroActBg_canon_rot {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L S.a₁) S.ν Kc Cx)
    {κ eps c₂ BG₂ δ₁ Kf Cf : ℝ} (hC : FlCore N Gb Hm S.a₁ S.ν c BG κ eps Kf Cf c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {m₀ : ℕ}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    (hX₁ : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV z) (𝒦XV z))
    {F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁ : ∀ z (s : DecParams Gb) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ), IsDecBg Gb (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ z (s, rawOf D) = (φ, α))
    {Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ z (p : Dec2.DecParams (coverOf Gb) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol z p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2))
    (hδ₁c : markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (ω : ℂ → ℂ) {ρ : ℝ} (hρp : S.p₁ ≤ ρ) (hρc : 2 * ρ ≤ cψ) (hp : 0 < S.p₁)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hYm : LabelMargin Gb Y)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (e : Rn N ≃ₗᵢ[ℝ] Rn N)
    (he : ∀ x : Rn N, e x = WithLp.toLp 2 (Q *ᵥ x.ofLp)) {θ θ' : physParamBg N Gb}
    {D : BgData Gb N} (hD : XiCData Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps D)
    (hθD : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D)
    (hθθ' : (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) =
      rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) (u : ℂ)
    {Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b} (hΦ : Φ ∈ physCarrier S m₀ hp) :
    zeroActBg S Gb (BgTransport.canon S.G' Gb N) X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps θ' u Y
        (fun b x => e (Φ b x)) =
      zeroActBg S Gb (BgTransport.canon S.G' Gb N) X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps θ u Y Φ := by
  have hρ : 0 < ρ := lt_of_lt_of_le hp hρp
  have hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps := ⟨D, hD, hθD⟩
  have hθ' : (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps := by
    rw [hθθ']; exact rotRaw_mem hQ hθ
  by_cases hu : ‖u‖ < 2
  · rw [zeroActBg_of_mem S Gb _ X₁V jV 𝒦XV m₀ F₁ Sol ω hp eps hθ' hu Y (fun b x => e (Φ b x)),
      zeroActBg_of_mem S Gb _ X₁V jV 𝒦XV m₀ F₁ Sol ω hp eps hθ hu Y Φ,
      hatOf_rot S m₀ hp e he hρp hΦ, hθθ', hθD]
    refine congrArg (fun x => u ^ 2 * x) ?_
    refine zeroTermBg_canon_rot S hS Sb hC hHm hcψ hMX hmar hα hsm hX₁ hF₁ hSol hδ₁c ω hYm hQ _ _
      u (fun q => ?_) hD
    have hq : ‖S.hatOf m₀ ρ hp Φ q‖ ≤ ρ := S.hatOf_mem m₀ hρ hp Φ q
    calc ‖u‖ * ‖S.hatOf m₀ ρ hp Φ q‖ ≤ ‖u‖ * ρ := mul_le_mul_of_nonneg_left hq (norm_nonneg u)
      _ < 2 * ρ := mul_lt_mul_of_pos_right hu hρ
      _ ≤ cψ := hρc
  · rw [zeroActBg_of_not S Gb _ X₁V jV 𝒦XV m₀ F₁ Sol ω hp eps (fun h => hu h.2) Y
        (fun b x => e (Φ b x)),
      zeroActBg_of_not S Gb _ X₁V jV 𝒦XV m₀ F₁ Sol ω hp eps (fun h => hu h.2) Y Φ]

end Rot

end Balaban.Inhabited
