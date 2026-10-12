/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionSymmRot
public import Balaban.Localization.DecEquivLatBg
public import Balaban.SmallField.XiLatSymm
public import Balaban.LargeField.Characteristic.RegSymm
public import Balaban.Localization.DecEquivTerms

/-!
# Lattice-symmetry covariance of the decoupled background map `F₁`

For a lattice symmetry `S : LatSymm Gp Gp σ` of the generating set compatible with the cover
(`CoverSymm`) and with the blocks (`BlockSymm`):

* `xiCData_sym`: `Ξ^c_n` data are carried to `Ξ^c_n` data;
* `F₁_sym`: `F₁ (s ∘ τ⁻¹, σΘ) = (φ_{k+1}(s) ∘ σ⁻¹, α_{k+1}(s) ∘ σ⁻¹)`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix
  Balaban.Fluctuation

section Data

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
variable {g : Equiv.Perm (CTorus d L N₁ m₁ K)}

/-- **`Ξ^c_n(𝔹; σ, ε)` is stable under lattice symmetries of the datum.** -/
theorem xiCData_sym (S : LatSymm G G g) {n : ℕ} {σ ε : ℝ} {D : BgData G N}
    (h : XiCData G a ν n σ ε D) : XiCData G a ν n σ ε (S.sym D) := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hX, hR⟩ := h
  exact ⟨fun y => Ψ₀ (g.symm y), h₀, fun y => Ψ'' (g.symm y), fun y => h'' (g.symm y),
    xiC_sym S a ν hX, realizesC_sym S hR⟩

end Data

section Background

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ}
variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **Lattice-symmetry covariance of the decoupled background**:
`F₁ (s ∘ τ⁻¹, σ Θ) = (φ_{k+1}(s) ∘ σ⁻¹, α_{k+1}(s) ∘ σ⁻¹)` for a lattice symmetry `σ` of `Gp`
compatible with the cover and the blocks, and `Θ` a datum of `Ξ^c_K(𝔹; 1, ε)`. -/
theorem F₁_sym
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {g : Equiv.Perm (CTorus d L N₁ m₁ K)} (S : LatSymm Gp Gp g)
    (CS : DecEquiv.CoverSymm (coverOf Gp) g) (B : DecEquiv.BlockSymm Gp g)
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D) :
    F₁ (CS.par s, rawOf (S.sym D)) =
      (S.fld (F₁ (s, rawOf D)).1, S.mul (F₁ (s, rawOf D)).2) := by
  obtain ⟨hU, φ, α, hI, hFeq⟩ := bg_point hC hF₁ hs hD
  rw [hFeq]
  have hU' := (S.inUnionDomainC_sym_iff D).2 hU
  have hI' := (DecEquiv.isDecBg_sym_iff S CS B (rho4 d L N BG κ) s D φ α).2 hI
  have hs' : ∀ P, ‖CS.par s P‖ < Real.exp κ := fun P => hs _
  exact hF₁ (CS.par s) (S.sym D) hs' hU' _ _ hI'

end Background

section Terms

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ}
variable {m₀ : ℕ} {σ : Equiv.Perm (CTorus d L N₁ m₁ K)}

/-- A lattice symmetry acts on raw data `(Ψ, h̃)` by `∘ σ⁻¹`. -/
def symRaw (σ : Equiv.Perm (CTorus d L N₁ m₁ K)) (Θ : RawData d L (N₁ * L ^ m₁) K N) :
    RawData d L (N₁ * L ^ m₁) K N := (fun y => Θ.1 (σ.symm y), fun y => Θ.2 (σ.symm y))

theorem rawOf_sym (S : LatSymm Gp Gp σ) (D : BgData Gp N) :
    rawOf (S.sym D) = symRaw σ (rawOf D) := rfl

/-- A lattice symmetry acts on the data `u = (Θ, ψ')` of the expansion. -/
def symU (σ : Equiv.Perm (CTorus d L N₁ m₁ K))
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) :
    RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) :=
  (symRaw σ u.1, DecEquiv.symSite σ u.2)

theorem symU_mem (S : LatSymm Gp Gp σ) (Sm : LatSymm Hm Hm σ)
    {u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) :
    symU σ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁ := by
  obtain ⟨⟨D, hD, hDu⟩, hψ⟩ := hu
  refine ⟨⟨S.sym D, xiCData_sym S hD, ?_⟩, fun x hx => ?_⟩
  · rw [rawOf_sym, ← hDu]; rfl
  · obtain ⟨y, rfl⟩ := σ.surjective x
    have := hψ y ((Sm.mem_dataSites y).1 hx)
    simpa [symU, DecEquiv.symSite] using this

section ParEquiv

theorem disjoint_pset_iff (CS : DecEquiv.CoverSymm (coverOf Gp) σ) (P : PolymerSymm Gp m₀ σ CS.τ)
    (q : ℕ × CTorus d L N₁ m₁ K) (X : Set (CTorus d L N₁ m₁ K)) :
    Disjoint (Pset m₁ (CS.τ q)) (σ '' X) ↔ Disjoint (Pset m₁ q) X := by
  rw [← P.image_pset q, Set.disjoint_image_iff σ.injective]

/-- **The relabelling of the decoupling parameters** of a polymer system by a symmetry. -/
def parEquiv (CS : DecEquiv.CoverSymm (coverOf Gp) σ) (P : PolymerSymm Gp m₀ σ CS.τ)
    {X₁ X₁' : Set (CTorus d L N₁ m₁ K)} (hX : X₁' = σ '' X₁) :
    ParIdx Gp X₁ ≃ ParIdx Gp X₁' where
  toFun i := ⟨⟨CS.τ i.1.1, (CS.idx i.1.1).2 i.1.2⟩, by
    subst hX; exact (disjoint_pset_iff CS P _ _).2 i.2⟩
  invFun j := ⟨⟨CS.τ.symm j.1.1, (CS.idx _).1 (by rw [Equiv.apply_symm_apply]; exact j.1.2)⟩, by
    subst hX
    exact (disjoint_pset_iff CS P (CS.τ.symm j.1.1) X₁).1 (by simpa using j.2)⟩
  left_inv i := by apply Subtype.ext; apply Subtype.ext; simp
  right_inv j := by apply Subtype.ext; apply Subtype.ext; simp

theorem extParams_sym (CS : DecEquiv.CoverSymm (coverOf Gp) σ)
    (P : PolymerSymm Gp m₀ σ CS.τ) {X₁ X₁' : Set (CTorus d L N₁ m₁ K)} (hX : X₁' = σ '' X₁)
    (s' : ParIdx Gp X₁' → ℂ) :
    extParams Gp X₁' s' = CS.par (extParams Gp X₁ (s' ∘ parEquiv CS P hX)) := by
  classical
  subst hX
  funext P'
  have hQ : CS.τ (CS.τ.symm P'.1) = P'.1 := by simp
  unfold DecEquiv.CoverSymm.par extParams
  by_cases h : Disjoint (Pset m₁ P'.1) (σ '' X₁)
  · have h2 : Disjoint (Pset m₁ (CS.τ.symm P'.1)) X₁ :=
      (disjoint_pset_iff CS P (CS.τ.symm P'.1) X₁).1 (by rw [hQ]; exact h)
    simp only [h, h2, ↓reduceDIte]
    simp only [Function.comp, parEquiv, Equiv.coe_fn_mk]
    congr 1
    apply Subtype.ext; apply Subtype.ext
    exact hQ.symm
  · have h2 : ¬ Disjoint (Pset m₁ (CS.τ.symm P'.1)) X₁ := fun h2 =>
      h (by rw [← hQ]; exact (disjoint_pset_iff CS P (CS.τ.symm P'.1) X₁).2 h2)
    simp only [h, h2, ↓reduceDIte]

end ParEquiv

section TermSym

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **The function expanded for a background functional is transported by a lattice symmetry** at
the points of the unit polydisc: `F_{σX}(σu, s') = F_X(u, s' ∘ κ)`. -/
theorem fnOfDec_sym
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol Sol' : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (S : LatSymm Gp Gp σ) (CS : DecEquiv.CoverSymm (coverOf Gp) σ) (B : DecEquiv.BlockSymm Gp σ)
    (P : PolymerSymm Gp m₀ σ CS.τ) {X₁f X₁f' : Finset (CTorus d L N₁ m₁ K)}
    (hX : (↑X₁f' : Set (CTorus d L N₁ m₁ K)) = σ '' (↑X₁f : Set (CTorus d L N₁ m₁ K)))
    {Φb : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) u,
      Φb (S.fld bg.1, S.mul bg.2) (symU σ u) = Φb bg u)
    {u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁)
    {s' : ParIdx Gp (↑X₁f' : Set (CTorus d L N₁ m₁ K)) → ℂ} (hs : s' ∈ unitCube _) :
    fnOfDec Gp Hm X₁f' F₁ Sol' (fun bg _ u => Φb bg u) (symU σ u) s' =
      fnOfDec Gp Hm X₁f F₁ Sol (fun bg _ u => Φb bg u) u (s' ∘ parEquiv CS P hX) := by
  obtain ⟨⟨D, hD, hDu⟩, hψ⟩ := hu
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hs1 : ∀ i, ‖(s' ∘ parEquiv CS P hX) i‖ < Real.exp κ := fun i =>
    lt_of_le_of_lt (hs _) hE1
  have hsx : ∀ Q, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s' ∘ parEquiv CS P hX) Q‖ <
      Real.exp κ := norm_extParams_lt hE1 hs1
  have hu1 : u.1 = rawOf D := hDu
  have hF := F₁_sym hC hF₁ S CS B hsx hD
  unfold fnOfDec
  show Φb (F₁ (extParams Gp (↑X₁f' : Set (CTorus d L N₁ m₁ K)) s', (symU σ u).1)) (symU σ u) = _
  show _ = Φb (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s' ∘ parEquiv CS P hX), u.1)) u
  rw [extParams_sym CS P hX s']
  have e : (symU σ u).1 = rawOf (S.sym D) := by
    show symRaw σ u.1 = rawOf (S.sym D)
    rw [hu1]; rfl
  rw [e, hF, hu1, ← hΦ _ u]

omit hC in
/-- A function jointly analytic on `S × polydisc` is analytic on the polydisc for fixed data. -/
theorem analytic_slice {U ι : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] [Fintype ι]
    {Fn : U → (ι → ℂ) → ℂ} {Sset : Set U} {R : ℝ}
    (h : AnalyticOnNhd ℂ (fun p : U × (ι → ℂ) => Fn p.1 p.2)
      (Sset ×ˢ polydisc (0 : ι → ℂ) (fun _ => R)))
    {u : U} (hu : u ∈ Sset) :
    AnalyticOnNhd ℂ (Fn u) (polydisc (0 : ι → ℂ) (fun _ => R)) := by
  intro s hs
  exact (h (u, s) ⟨hu, hs⟩).comp (g := fun p : U × (ι → ℂ) => Fn p.1 p.2)
    (f := fun s' : ι → ℂ => (u, s')) ((analyticAt_const (𝕜 := ℂ)).prod (analyticAt_id (𝕜 := ℂ)))

/-- **Lattice-symmetry covariance of the expansion terms of a background functional**:
`𝓔(σ X, σ Y)(σ u) = 𝓔(X, Y)(u)` whenever `Φ(σφ, σα; σu) = Φ(φ, α; u)`, `σ` is a lattice symmetry of
`Gp` compatible with the cover, the blocks and the polymers, and the parameter sets satisfy
`X₁' = σ X₁`. -/
theorem evTerm_sym
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol Sol' : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (S : LatSymm Gp Gp σ) (Sm : LatSymm Hm Hm σ) (CS : DecEquiv.CoverSymm (coverOf Gp) σ)
    (B : DecEquiv.BlockSymm Gp σ) (P : PolymerSymm Gp m₀ σ CS.τ)
    {X₁f X₁f' : Finset (CTorus d L N₁ m₁ K)}
    (hX : (↑X₁f' : Set (CTorus d L N₁ m₁ K)) = σ '' (↑X₁f : Set (CTorus d L N₁ m₁ K)))
    {Φb : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) u,
      Φb (S.fld bg.1, S.mul bg.2) (symU σ u) = Φb bg u)
    (hana : AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
          (CTorus d L N₁ m₁ K → Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
        fnOfDec Gp Hm X₁f F₁ Sol (fun bg _ u => Φb bg u) p.1 p.2)
        ((XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) ×ˢ
          polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) (fun _ => Real.exp κ)))
    (hana' : AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
          (CTorus d L N₁ m₁ K → Fin N → ℂ)) × (ParIdx Gp (↑X₁f' : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
        fnOfDec Gp Hm X₁f' F₁ Sol' (fun bg _ u => Φb bg u) p.1 p.2)
        ((XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) ×ˢ
          polydisc (0 : ParIdx Gp (↑X₁f' : Set (CTorus d L N₁ m₁ K)) → ℂ) (fun _ => Real.exp κ)))
    (X₁ Y : Set (CTorus d L N₁ m₁ K))
    {u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) :
    evTerm (fun i : ParIdx Gp (↑X₁f' : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ (σ '' X₁)
        (fnOfDec Gp Hm X₁f' F₁ Sol' (fun bg _ u => Φb bg u)) (σ '' Y) (symU σ u) =
      evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ X₁
        (fnOfDec Gp Hm X₁f F₁ Sol (fun bg _ u => Φb bg u)) Y u :=
  evTerm_relabel (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
    (fun i : ParIdx Gp (↑X₁f' : Set (CTorus d L N₁ m₁ K)) => i.1.1) (parEquiv CS P hX)
    (Real.one_lt_exp_iff.2 hC.hκ) P S (fun _ => rfl) X₁ Y
    (analytic_slice hana hu) (analytic_slice hana' (symU_mem S Sm hu))
    (fun _ hs' => fnOfDec_sym hC hF₁ S CS B P hX hΦ hu hs')

end TermSym

end Terms

end Balaban.Localization
