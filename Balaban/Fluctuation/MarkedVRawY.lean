/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.PhysicalVRawY
public import Balaban.Fluctuation.MarkedEvJoint

/-!
# Exact locality of the marked block energy and of the marked coefficient `evDec`

`marked_vblock_fan_local_rawY` is `vblock_fan_local_rawY` for the block energy along the masked
tangent `markedHatPsiF … Zm um tm`: the hat variables and the raw data agree on the component
itself (`agreeOn`, not `thickSet`), the marks `(um, tm)` and the mask `Zm` are the same on both
sides.  `evDec_local_rawY` is the resulting locality of the coefficient `evDec` of the expansion
for the same agreement relation (the sharp form of clause 2 of `MarkedBlockExpansionDecPair`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.Polymer Finset Matrix

section MarkedVRaw

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- The geometry of a component `Y = compY C` of the decoupling: it is a non-neighbouring component
of `Vset X₁ 𝒞 ∩ Ω₁`, the cut parameters equal `1` off the blocks of `X₁`, equal `0` on the blocks
of `X₁` not in the marked family, and agree on the cubes lying in `Y` when the parameters agree on
the marked cubes inside `Y`. -/
theorem compY_geometry (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (C : Finset (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))))
    (s s' : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
    (hs0 : ∀ i ∉ C, s i = 0) (hs0' : ∀ i ∉ C, s' i = 0)
    (hag : ∀ i ∈ C, Pset m₁ i.1.1 ⊆ compY
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
      (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C → s i = s' i)
    (Y : Finset (CTorus d L N₁ m₁ (k + 1)))
    (hmemY : ∀ x, x ∈ Y ↔ x ∈ compY
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
      (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) :
    IsNnComp ((Vset X₁f (C.image
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1))).filter
      fun x => x ∈ Gp.Ω 1) Y ∧
    (∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁f →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P = 1 ∧
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P = 1) ∧
    (∀ P ∈ parCubes Gp X₁f, P ∉ C.image
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P = 0 ∧
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P = 0) ∧
    (∀ P ∈ C.image
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1),
      SubI Gp (cubeP P) Y →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P =
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P) := by
  classical
  set cmap : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℕ × CTorus d L N₁ m₁ (k + 1) :=
    fun i => i.1.1 with hcc
  have hs1 := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s
  have hs1' := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s'
  set Yc : Set (CTorus d L N₁ m₁ (k + 1)) := compY cmap (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C
    with hYc
  set 𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1)) := C.image cmap with h𝒞
  have hcc_mem : ∀ i, cmap i ∈ cubeIdx Gp := fun i => i.1.2
  have hX₁Ω : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(Gp.Ω 1) := fun x hx =>
    X1_subset_Omega1 hcov (hX₁ ▸ hx)
  have hPatchΩ : patchUnion (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) (fun i => Pset m₁ (cmap i)) C ⊆
      ↑(Gp.Ω 1) := by
    intro x hx
    rcases hx with hx | hx
    · exact hX₁Ω hx
    · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
      exact Pset_subset_Omega1 hcov (hcc_mem i) hxi
  have hYsub : Yc ⊆ patchUnion (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) (fun i => Pset m₁ (cmap i)) C :=
    componentOf_subset _ (fun _ h => Or.inl h)
  have hYnn : IsNnComp ((Vset X₁f 𝒞).filter fun x => x ∈ Gp.Ω 1) Y := by
    refine ⟨fun x hx => ?_, fun x hx y hy hadj => ?_⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter]
      exact ⟨(mem_Vset_iff cmap C).2 (hYsub hxY), hPatchΩ (hYsub hxY)⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter] at hy
      exact (hmemY y).2 (compY_closed hxY ((mem_Vset_iff cmap C).1 hy.1) hadj)
  have hdisj_of : ∀ P : ↥(cubeIdx Gp), P.1 ∈ parCubes Gp X₁f →
      Disjoint (Pset m₁ P.1) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) := by
    intro P hP
    by_contra hnd
    have hsub := Pset_subset_of_not_disjoint (hX₁ ▸ hcov.polySetup) P.2 hnd
    unfold parCubes at hP
    rw [Finset.mem_filter] at hP
    apply hP.2
    intro y hy
    have := hsub (mem_cubeP.1 hy)
    exact Finset.mem_coe.1 this
  have hs1E : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁f →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P = 1 ∧
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P = 1 := by
    intro P hP hPn
    unfold extS
    simp only [hP, ↓reduceDIte]
    exact ⟨hs1 P hP hPn, hs1' P hP hPn⟩
  have hs0E : ∀ P ∈ parCubes Gp X₁f, P ∉ 𝒞 →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P = 0 ∧
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P = 0 := by
    intro P hP hP𝒞
    have hPc : P ∈ cubeIdx Gp := (Finset.mem_filter.1 hP).1
    have hd := hdisj_of ⟨P, hPc⟩ hP
    unfold extS
    simp only [hPc, ↓reduceDIte]
    have hi : (⟨⟨P, hPc⟩, hd⟩ : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))) ∉ C :=
      fun hi => hP𝒞 (Finset.mem_image.2 ⟨_, hi, rfl⟩)
    rw [show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s ⟨P, hPc⟩ =
        s ⟨⟨P, hPc⟩, hd⟩ from extParams_par s ⟨⟨P, hPc⟩, hd⟩,
      show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s' ⟨P, hPc⟩ =
        s' ⟨⟨P, hPc⟩, hd⟩ from extParams_par s' ⟨⟨P, hPc⟩, hd⟩]
    exact ⟨hs0 _ hi, hs0' _ hi⟩
  have hagE : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P =
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P := by
    intro P hP𝒞 hSub
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP𝒞
    have hsub : Pset m₁ (cmap i) ⊆ Yc := by
      intro x hx
      have hxΩ : x ∈ Gp.Ω 1 := Pset_subset_Omega1 hcov (hcc_mem i) hx
      exact (hmemY x).1 (hSub ⟨x, hxΩ⟩ (mem_cubeP.2 hx))
    have := hag i hi hsub
    unfold extS
    simp only [hcc_mem i, ↓reduceDIte]
    rw [show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s ⟨cmap i, hcc_mem i⟩ = s i from
        extParams_par s i,
      show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s' ⟨cmap i, hcc_mem i⟩ = s' i from
        extParams_par s' i]
    exact this
  exact ⟨hYnn, hs1E, hs0E, hagE⟩

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **Exact locality of the marked potential summand (`blockEnergyFun` along the masked tangent).**
This is `vblock_fan_local_rawY` with the hat field `hatPsiF` replaced by the masked tangent
`markedHatPsiF … Zm um tm`, for marks with `(‖um‖ + ‖tm‖) · B < δ₁` (the ball hypothesis `hδ`).
The agreement relation is sharp: raw data agree on the component `Yc` itself and the hat variables
at the unit points of its sites.  The mask `Zm` and the marks are the same on both sides. -/
theorem marked_vblock_fan_local_rawY (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1))
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ) (Zm : Finset (unitPts Gp)) (um tm : ℂ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (hZ : readSites Hm k z ⊆ ↑X₁f)
    (hBM : BlockMargin Gp X₁f
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1)))) :
    LocalityAEOn (Real.exp κ)
      (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => Pset m₁ i.1.1)
      (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun C u u' => agreeOn (compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) u.1 u'.1 ∧
        ∀ y ∈ compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C,
          ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i))
      (fun u s => (blockEnergyFun Gp Hm (compWeight L a₁) ν k z)
        (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
        (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
          flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
            u.1.1 (markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
        (u.1, markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)) := by
  classical
  rintro C ⟨u, ψh⟩ ⟨u', ψh₂⟩ ⟨⟨D, hD, rfl⟩, hψh⟩ ⟨⟨D', hD', rfl⟩, hψh₂⟩ s s' hs hs' hag hAg
  obtain ⟨hAgΘ, hAgψ⟩ := hAg
  set cmap : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℕ × CTorus d L N₁ m₁ (k + 1) :=
    fun i => i.1.1 with hcc
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs.2 i)
  have hsx' : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s' P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs'.2 i)
  have hs1 := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s
  have hs1' := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s'
  have hψ : markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh ∈ FlBall Hm δ₁ :=
    (markedHatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hF₁ hsx hD hψh Zm hδ).1
  have hψ₂ : markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') (rawOf D') ψh₂ ∈ FlBall Hm δ₁ :=
    (markedHatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hF₁ hsx' hD' hψh₂ Zm hδ).1
  set ψ := markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
    (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh with hψdef
  set ψ₂ := markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
    (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') (rawOf D') ψh₂ with hψ₂def
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
    point_facts_core hC hF₁ hSol hsx hs1 hD hψ
  obtain ⟨φ', α', δφ', δα', hI', hFeq', hstrict', hSeq', hmem'⟩ :=
    point_facts_core hC hF₁ hSol hsx' hs1' hD' hψ₂
  show (blockEnergyFun Gp Hm (compWeight L a₁) ν k z)
      (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
          D.Ψ ψ)).1 (rawOf D, ψ) =
    (blockEnergyFun Gp Hm (compWeight L a₁) ν k z)
      (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', rawOf D'))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s',
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', rawOf D'))
          D'.Ψ ψ₂)).1 (rawOf D', ψ₂)
  rw [hFeq, hFeq', hSeq, hSeq']
  set Yc : Set (CTorus d L N₁ m₁ (k + 1)) := compY cmap (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C
    with hYc
  set Y : Finset (CTorus d L N₁ m₁ (k + 1)) := Finset.univ.filter (· ∈ Yc) with hY
  set 𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1)) := C.image cmap with h𝒞
  have hmemY : ∀ x, x ∈ Y ↔ x ∈ Yc := fun x => by simp [hY]
  have hcc_mem : ∀ i, cmap i ∈ cubeIdx Gp := fun i => i.1.2
  obtain ⟨hYnn, hs1E, hs0E, hagE⟩ := compY_geometry hcov hX₁ C _ _
    (fun i hi => hs.1 i hi) (fun i hi => hs'.1 i hi) hag Y hmemY
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hDom' := xiCData_inDomainC hC.HBp hC.small1 hD'
  have hdataY : ∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gp.Ω 1 → D.h z = D'.h z) := fun z hz => by
    have := hAgΘ z ((hmemY z).1 hz)
    exact ⟨this.1, fun _ => this.2⟩
  obtain ⟨hαSY, -⟩ := i4b_local_of_agree_on_component hC.hS hC.Sp hconn hC.HBp hC.hκ.le hC.hM
    (fun P => (hsx P).le) (fun P => (hsx' P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom hDom' hG' hYnn
    hs1E hs0E hagE hdataY hI hI'
  have h𝒞' : ∀ P ∈ 𝒞, P ∈ cubeIdx Gp := by
    intro P hP
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hP
    exact hcc_mem i
  have hOp := hC.SM.toCoverBase.toOpSetting.toGreen
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  obtain ⟨hfld, hfix, hs6, hsK, hdp, huniq⟩ :=
    hSol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, flEdat Gp Hm (φ, α) D.Ψ ψ)
      hsx hstrict
  obtain ⟨hfld', hfix', hs6', hsK', hdp', huniq'⟩ :=
    hSol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', flEdat Gp Hm (φ', α') D'.Ψ ψ₂)
      hsx' hstrict'
  have Hh : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α) (barField Gp D.Ψ φ) ψ 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ :=
    StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict
  have Hh' : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α') (barField Gp D'.Ψ φ') ψ₂ 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ :=
    StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict'
  have hX₁cell : IsCellUnion (L ^ (k + 1)) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) := by
    rw [hX₁]; exact X1_isCellUnion_unit hcov.hN
  have hh : ∀ b : unitPts Gp, UnitOut Gp Y b → ∀ i, ψh (b, i) = ψh₂ (b, i) := by
    intro b hb i
    obtain ⟨x, -, hxb⟩ := (mem_unitPts Gp).1 b.2
    have hxΩ : x ∈ Gp.Ω 1 := by rw [hG'.Ω_one]; exact Finset.mem_univ _
    have hxY : x ∈ Y := hb ⟨x, hxΩ⟩ (by simp only [hxb])
    have hbx : b = unitPt hG' x := Subtype.ext hxb.symm
    rw [hbx]
    exact hAgψ x ((hmemY x).1 hxY) i
  have hψY := markedHatPsiF_rows hC hk hG' cc hconn hMX hdm hα hsm hF₁ hsx hsx' hD hD' hYnn hs1E
    hs0E hagE hX₁cell h𝒞' hdataY ψh ψh₂ hh Zm um tm
  have h1 : (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
      flEdat Gp Hm (φ, α) D.Ψ ψ)).1 = δφ := congrArg Prod.fst hSeq
  have h2 : (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s',
      flEdat Gp Hm (φ', α') D'.Ψ ψ₂)).1 = δφ' := congrArg Prod.fst hSeq'
  have h1' : (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
      flEdat Gp Hm (φ, α) D.Ψ ψ)).2 = δα := congrArg Prod.snd hSeq
  have h2' : (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s',
      flEdat Gp Hm (φ', α') D'.Ψ ψ₂)).2 = δα' := congrArg Prod.snd hSeq'
  rw [h1'] at hfld hfix hs6
  rw [h2'] at hfld' hfix' hs6'
  have hflc := fluct_correction_rows_marked_of_ball hC hk hG' hG cc hconn hrow hMX hdm hα hsm hF₁
    hsx hsx' hD hD' hYnn hs1E hs0E hagE hX₁cell h𝒞' hdataY ψh ψh₂ hh Zm um tm hI hI' Hh Hh'
    hfix hs6 hfix' hs6'
  have hδeq : ∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i, δφ (y, i) = δφ' (y, i) := by
    intro y hy i
    rw [← h1, ← h2, hfld, hfld']
    exact hflc.2 y hy i
  have hZY : ∀ y ∈ readSites Hm k z, y ∈ Yc := fun y hy =>
    subset_compY (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C (hZ hy)
  have hXY' : ∀ x ∈ X₁f, x ∈ Y := fun x hx => (hmemY x).2 (subset_compY
    (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C (Finset.mem_coe.2 hx))
  have hαeq : ∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) → α y = α' y := by
    intro y hy
    obtain ⟨z, hz, hyz, hQ, hhat⟩ := hBM y hy y.2
    refine hαSY y (Finset.mem_biUnion.2 ⟨z, Finset.mem_filter.2 ⟨hz, ?_, ?_⟩, hyz⟩)
    · intro P hP hPpar
      exact absurd hPpar (hQ P hP)
    · intro x hx
      exact hXY' _ (hhat x hx)
  exact blockEnergyFun_local_sharp (Gp := Gp) (Hm := Hm) (compWeight L a₁) ν k z
    (t := ((φ, α), δφ, (rawOf D, ψ))) (t' := ((φ', α'), δφ', (rawOf D', ψ₂)))
    (fun y hy => hαeq y hy)
    (fun y hy i => hδeq y ((hmemY _).2 (hZY _ hy)) i)
    (fun y hy => hψY y ((hmemY y).2 (hZY y (readSites_of_blockSites hy))))

/-- **Exact locality of the marked coefficient `evDec`.**  For a pair `(F₁, Sol)` with the defining
properties and marks `(um, tm)` in the bidisc, the coefficient `evDec … Zm um tm Y` takes equal values
on two data of `XiCRaw × ball` whose raw parts agree on `Y` itself (`agreeOn Y`) and whose hat
variables agree at the unit points of the sites of `Y`.  This is the sharp form of clause 2 of
`MarkedBlockExpansionDecPair`.  Proof: `evDec` is a sum of Taylor coefficients `coef` over
connected families `C` with `Ysites C = Y`; `coef_congr_of_agree_on` with the fan locality
`marked_vblock_fan_local_rawY` for the relation on `compY C ⊆ Y`. -/
theorem evDec_local_rawY (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1))
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ) (Zm : Finset (unitPts Gp)) (um tm : ℂ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (hZ : readSites Hm k z ⊆ ↑X₁f)
    (hBM : BlockMargin Gp X₁f
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
      {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
    (hu' : u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
      {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
    (hag : agreeOn Y u.1 u'.1)
    (hagψ : ∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) :
    evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
        um tm Y u =
      evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
        um tm Y u' := by
  classical
  set c : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℕ × CTorus d L N₁ m₁ (k + 1) :=
    fun i => i.1.1 with hcdef
  have hc : ∀ i, c i ∈ cubeIdx Gp := fun i => i.1.2
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hloc := marked_vblock_fan_local_rawY hC hk hG hG' cc hcψ Zm um tm hMX hdm hα hsm hum hcov
    hX₁ hconn hrow hF₁ hSol z hZ hBM
  have hsub : ∀ C : Finset (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))),
      compY c (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C ⊆
        Ysites Gp m₀ c (X1 Gp m₀ j 𝒦X) C := by
    intro C
    have e1 : compY c (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C =
        compY c (X1 Gp m₀ j 𝒦X) C := congrArg (fun S => compY c S C) hX₁
    rw [e1]; exact compY_subset_Ysites hcov.hU hcov.hN hc _ C
  have hloc' := hloc
  have e2 : compY c (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = compY c (X1 Gp m₀ j 𝒦X) :=
    congrArg (fun S => compY c S) hX₁
  rw [e2] at hloc'
  unfold evDec evTerm
  refine Finset.sum_congr rfl fun C hC' => ?_
  obtain ⟨-, hY⟩ := (mem_connFams c).1 hC'
  refine coef_congr_of_agree_on (S := XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
    {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}) hE1 hloc' C hu hu' ?_
  have hYC : compY c (X1 Gp m₀ j 𝒦X) C ⊆ Y := by
    rw [← hY, ← e2]; exact hsub C
  exact ⟨agreeOn_mono hYC hag, fun y hy i => hagψ y (hYC hy) i⟩

end MarkedVRaw

end Balaban.Localization
