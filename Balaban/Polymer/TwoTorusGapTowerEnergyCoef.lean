/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerEnergyMarks

/-!
# The energy coefficient of a root under the recentring map, given the domain labels (blocker 7)

* `sitesOf_image_cubeMap_sym`, `sitesOf_image_recentred`: the sites of the recentred cubes.
* `gsumCoeff_blockSplit_recentred`: the interpolation coefficient `gsumCoeff` of the two steps is
  carried along the recentred cube map `σB⁻¹ ∘ cubeMap ∘ σA` (`gsumCoeff_transport` with
  `integral_blockSplit_recentred`), given the correspondence of the active labels, of their
  activities and of the marks.
* `gsumCoeff_e1_recentred_of_domainLabels`: the recentred form of
  `gsumCoeff_e1_twoTorus_of_domainLabels`: the energy coefficient of the root `z` at the blocks `T`
  and of the root `bc (z + τA) - τB` at the recentred blocks agree, given a correspondence of the
  domain labels and of their activities; the bridge labels and the marks correspond by
  `mem_bridgeFamily_recentred_iff`, `preimage_recentred` and `e1MarkGParamG_recentred`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.Localization.DecEquiv Balaban.Inhabited Balaban.Inhabited.LevelStep MeasureTheory

section CoefRec

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "𝔅A" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
  Set.univ
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "σAc" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
  (K := k + 1) (m₀ := m₀) (Equiv.addRight tA)
set_option hygiene false in
local notation "σBi" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁') (m₁ := m₁)
  (K := k + 1) (m₀ := m₀) (Equiv.addRight tB)⁻¹

/-- The sites of the image of a set of cubes under a paving symmetry are the image of its sites. -/
theorem sitesOf_image_cubeMap_sym {K m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)) :
    sitesOf (T.image (Balaban.Fluctuation.cubeMap r)) = r '' sitesOf T := by
  rw [← sitesOf_cubeAct hN hr]
  congr 1

/-- **The sites of the recentred cubes** are the recentred sites. -/
theorem sitesOf_image_recentred {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (hnL : 2 * R + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1)) (T : Finset (𝔅A))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) :
    sitesOf (T.image (fun b => σBi (σc (σAc b)))) = (fun x => bm (x + tA) - tB) '' sitesOf T := by
  have hσA := genSymm_mem_pavingSymGroup (GenSymm.translate (n := k + 1) (m₀ := m₀) tA htA)
  have hσB := genSymm_mem_pavingSymGroup (GenSymm.translate (n := k + 1) (m₀ := m₀) tB htB)
  have hT1 : ∀ x ∈ sitesOf (T.image σAc), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    rw [sitesOf_image_cubeMap_sym hN hσA]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb, hxb⟩ := mem_sitesOf.1 hx
    exact hT b hb x hxb
  rw [show (fun b => σBi (σc (σAc b))) = σBi ∘ (σc ∘ σAc) from rfl, ← Finset.image_image,
    ← Finset.image_image, sitesOf_image_cubeMap_sym hN' (inv_mem hσB),
    sitesOf_image_cubeMap hN hN' le_rfl hnL _ hT1, sitesOf_image_cubeMap_sym hN hσA,
    image_recentred]
  rfl

/-- **The interpolation coefficient of the step under the recentring map.**  `gsumCoeff_transport` for
the block measures of the two steps, the recentred cube map `rc = σB⁻¹ ∘ cubeMap ∘ σA` (injective on
the cubes whose translates lie in the box) and the relation "block variables agree at the unit
points of `x` and of `φ x = bm (x + tA) - tB` for `x + tA` in the box"; the integrals correspond by
`integral_blockSplit_recentred`. -/
theorem gsumCoeff_blockSplit_recentred (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (hn : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb']
    (Lab : CubeLabels m₀ (k + 1) Set.univ Lb) (Lab' : CubeLabels m₀ (k + 1) Set.univ Lb')
    {εH κH κ0 Kc εH' κH' κ0' Kc' : ℝ}
    (A : ℂ → LabelAct Lab ((SA).blockSplit m₀ hp).Ωb εH κH κ0 Kc)
    (A' : ℂ → LabelAct Lab' ((SB).blockSplit m₀ hp').Ωb εH' κH' κ0' Kc')
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] (y0 : ι → Lb) (y0' : ι' → Lb')
    (G : ι → ℂ → (∀ c, ((SA).blockSplit m₀ hp).Ωb c) → ℂ)
    (G' : ι' → ℂ → (∀ c, ((SB).blockSplit m₀ hp').Ωb c) → ℂ)
    (hGdep : ∀ i u, DepOn (blocksOf m₀ (k + 1) Set.univ (Lab.ysite (y0 i))) (G i u))
    (T : Finset (𝔅A))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    (P : Lb → Prop) (P' : Lb' → Prop)
    (hA0 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, ¬ P y → ∀ Φ, (A (s : ℂ)).H y Φ = 0)
    (hA0' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y', ¬ P' y' → ∀ Φ', (A' (s : ℂ)).H y' Φ' = 0)
    (ψ : ∀ y, P y → blocksOf m₀ (k + 1) Set.univ (Lab.ysite y) ⊆ T → Lb')
    (hψP : ∀ y hP hy, P' (ψ y hP hy))
    (hψb : ∀ y hP hy, blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (ψ y hP hy)) =
      (blocksOf m₀ (k + 1) Set.univ (Lab.ysite y)).image (fun b => σBi (σc (σAc b))))
    (hψinj : ∀ y₁ hP₁ hy₁ y₂ hP₂ hy₂, ψ y₁ hP₁ hy₁ = ψ y₂ hP₂ hy₂ → y₁ = y₂)
    (hψsurj : ∀ y', P' y' → blocksOf m₀ (k + 1) Set.univ (Lab'.ysite y') ⊆
      T.image (fun b => σBi (σc (σAc b))) → ∃ y hP hy, ψ y hP hy = y')
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y hP hy,
      ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) →
        Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm (x + tA) - tB)))
          ⟨unitPt (SB).hG' (bm (x + tA) - tB), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
        (A' (s : ℂ)).H (ψ y hP hy) Φ' = (A (s : ℂ)).H y Φ)
    (κ : ∀ i, blocksOf m₀ (k + 1) Set.univ (Lab.ysite (y0 i)) ⊆ T → ι')
    (hκb : ∀ i hi, blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (y0' (κ i hi))) =
      (blocksOf m₀ (k + 1) Set.univ (Lab.ysite (y0 i))).image (fun b => σBi (σc (σAc b))))
    (hκinj : ∀ i₁ hi₁ i₂ hi₂, κ i₁ hi₁ = κ i₂ hi₂ → i₁ = i₂)
    (hκsurj : ∀ i', blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (y0' i')) ⊆
      T.image (fun b => σBi (σc (σAc b))) → ∃ i hi, κ i hi = i')
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i hi,
      ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) →
        Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm (x + tA) - tB)))
          ⟨unitPt (SB).hG' (bm (x + tA) - tB), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
        G' (κ i hi) (s : ℂ) Φ' = G i (s : ℂ) Φ) :
    gsumCoeff ((SB).blockSplit m₀ hp').μ Lab' A' y0' G' (T.image (fun b => σBi (σc (σAc b)))) =
      gsumCoeff ((SA).blockSplit m₀ hp).μ Lab A y0 G T := by
  have hσA := genSymm_mem_pavingSymGroup (GenSymm.translate (n := k + 1) (m₀ := m₀) tA htA)
  have hσB := genSymm_mem_pavingSymGroup (GenSymm.translate (n := k + 1) (m₀ := m₀) tB htB)
  have hσ : Set.InjOn (fun b => σBi (σc (σAc b))) (T : Set (𝔅A)) := by
    intro b₁ hb₁ b₂ hb₂ h
    have h1 := cubeMap_injective_sym hN' (inv_mem hσB) h
    have hR : ∀ b ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (σAc b).1 := fun b hb => by
      rw [cubeMap_translate_val hN tA htA]
      exact hT b hb b.1 (mem_box_self _ (cellSide_pos m₀ m₁ (k + 1)))
    have h2 := congrArg Subtype.val h1
    rw [cubeMap_val, cubeMap_val] at h2
    exact cubeMap_injective_sym hN hσA (Subtype.ext (boxMap_inj
      (hm' := (by omega : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))) (hR b₁ hb₁) (hR b₂ hb₂) h2))
  refine gsumCoeff_transport _ _ Lab Lab' A A' y0 y0' G G' hGdep _ T hσ _
    (fun Z hZ F F' hF hFF => ?_) P P' hA0 hA0' ψ hψP hψb hψinj hψsurj hA κ hκb hκinj hκsurj hG
  have hSSA := LatSymm.ofTranslateLevel (SA).hG' tA
    (fun μ => (pow_dvd_pow L (by omega)).trans (htA μ))
  have hSSB := LatSymm.ofTranslateLevel (SB).hG' tB
    (fun μ => (pow_dvd_pow L (by omega)).trans (htB μ))
  have hUA := Balaban.Fluctuation.unitBlockPres_of_genSymm
    (GenSymm.translate (n := k + 1) (m₀ := m₀) tA htA)
  have hUB := Balaban.Fluctuation.unitBlockPres_of_genSymm
    (GenSymm.translate (n := k + 1) (m₀ := m₀) tB htB)
  exact integral_blockSplit_recentred hN2 hk νS β p₁ δ hn hn' (SA).hG' (SB).hG' hp hp' hSSA hUA
    hSSB hUB Z (fun b hb => hT b (hZ hb)) hF hFF

set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "tAz" => (fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))
set_option hygiene false in
local notation "tBz" => (fun μ => ((zv μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))
set_option hygiene false in
local notation "τA" => (fun μ => ((((tAz μ).val / L ^ (k + 1) : ℕ)) :
  ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))))
set_option hygiene false in
local notation "τB" => (fun μ => ((((tBz μ).val / L ^ (k + 1) : ℕ)) :
  ZMod (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))))
set_option hygiene false in
local notation "σc1" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  (m₀ := 1) hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "σAc1" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
  (K := k + 1) (m₀ := 1) (Equiv.addRight tAz)
set_option hygiene false in
local notation "σBi1" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁') (m₁ := m₁)
  (K := k + 1) (m₀ := 1) (Equiv.addRight tBz)⁻¹

/-- **The energy coefficient of a root under the recentring map, given the domain labels.**  As
`gsumCoeff_e1_twoTorus_of_domainLabels` for the recentring map `φ x = bm (x + tA) - tB` (integer
recentring vector `zv`, multiple of the cell side): for the root `z` and the set `T` of blocks whose
translates lie in the box, the coefficient of the root `bc (z + τA) - τB` at the recentred blocks
equals the coefficient of `z` at `T`.  The bridge labels correspond by
`mem_bridgeFamily_recentred_iff`, `blocksOf_recentred`, `image_recentred_inj` and
`preimage_recentred`, the marks by `e1MarkGParamG_recentred`, and the cluster expansion by
`gsumCoeff_blockSplit_recentred`. -/
theorem gsumCoeff_e1_recentred_of_domainLabels
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hC : FlCore N (GA) (HA) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : TA → DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : TB → DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α))
    {Sol : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : TB → Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small (HA) (Sol b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2))
    (hSol' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Small (HB) (Sol' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' b p).2))
    (hd : 0 < d) (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁') (hm₁ : 1 ≤ m₁)
    (zv : Fin d → ℤ) (hz : ∀ μ, ((cellSide L 1 m₁ (k + 1) : ℕ) : ℤ) ∣ zv μ)
    (z : TA) {R : ℕ} (hw : L * cellSide L 1 m₁ (k + 1) ≤ 2 * R + 1)
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hzc : InBox d (R / L ^ (k + 1)) (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) (z + τA))
    (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz))
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps)
    (hraw : RawBoxAgree {w | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
      (symRaw (Equiv.addRight tAz) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))
      (symRaw (Equiv.addRight tBz) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N)))
    {ρ : ℝ} (hρ : 0 < ρ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (hum : ∀ u : ℂ, ‖u‖ ≤ 1 →
      ‖u‖ * markedRad d L N k 1 κ ρ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (hGdep : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z}) (u : ℂ),
      DepOn (blocksOf 1 (k + 1) Set.univ i.1) (e1MarkGParamG (SA) F₁ Sol ρ hp z eps θ i u))
    (hL2 : 2 ≤ L) (hdom : ∀ b, ∀ Y ∈ e1DomG (SA) b, IsDj 1 (k + 1) Y)
    (hdom' : ∀ b, ∀ Y ∈ e1DomG (SB) b, IsDj 1 (k + 1) Y)
    {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb']
    (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb)
    (Lab₀' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ
      Lb')
    {εH κH κ0 Kc εH' κH' κ0' Kc' : ℝ} (hεH : 0 ≤ εH) (hκ0 : aEnt d L + 2 ≤ κ0)
    (hεH' : 0 ≤ εH') (hκ0' : aEnt d L + 2 ≤ κ0')
    (A : physParam N (SA) → ℂ → LabelAct Lab₀ ((SA).blockSplit 1 hp).Ωb εH κH κ0 Kc)
    (A' : physParam N (SB) → ℂ → LabelAct Lab₀' ((SB).blockSplit 1 hp').Ωb εH' κH' κ0' Kc')
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz))
    (ψ₀ : ∀ y, blocksOf 1 (k + 1) Set.univ (Lab₀.ysite y) ⊆ T → Lb')
    (hψ₀b : ∀ y hy, blocksOf 1 (k + 1) Set.univ (Lab₀'.ysite (ψ₀ y hy)) =
      (blocksOf 1 (k + 1) Set.univ (Lab₀.ysite y)).image (fun b => σBi1 (σc1 (σAc1 b))))
    (hψ₀inj : ∀ y₁ hy₁ y₂ hy₂, ψ₀ y₁ hy₁ = ψ₀ y₂ hy₂ → y₁ = y₂)
    (hψ₀surj : ∀ y', blocksOf 1 (k + 1) Set.univ (Lab₀'.ysite y') ⊆
      T.image (fun b => σBi1 (σc1 (σAc1 b))) → ∃ y hy, ψ₀ y hy = y')
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y hy,
      ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz) →
        Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bm (x + tAz) - tBz)))
          ⟨unitPt (SB).hG' (bm (x + tAz) - tBz), rfl⟩ =
          Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
        (A' θ' (s : ℂ)).H (ψ₀ y hy) Φ' = (A θ (s : ℂ)).H y Φ) :
    gsumCoeff ((SB).blockSplit 1 hp').μ
        (commonLabels Lab₀' hN' hL2 (fun _ => Set.univ) (e1DomG (SB)) hdom')
        (commonAct A' hN' hL2 (fun _ => Set.univ) (e1DomG (SB)) hdom' hεH' hκ0' θ')
        (fun i' => commonAnchor Lb' (fun _ => Set.univ) (e1DomG (SB)) (bc (z + τA) - τB) i')
        (fun i' u Φ' => e1MarkGParamG (SB) F₁' Sol' ρ hp' (bc (z + τA) - τB) eps θ' i' u Φ')
        (T.image (fun b => σBi1 (σc1 (σAc1 b)))) =
      gsumCoeff ((SA).blockSplit 1 hp).μ
        (commonLabels Lab₀ hN hL2 (fun _ => Set.univ) (e1DomG (SA)) hdom)
        (commonAct A hN hL2 (fun _ => Set.univ) (e1DomG (SA)) hdom hεH hκ0 θ)
        (fun i => commonAnchor Lb (fun _ => Set.univ) (e1DomG (SA)) z i)
        (fun i u Φ => e1MarkGParamG (SA) F₁ Sol ρ hp z eps θ i u Φ) T := by
  classical
  obtain ⟨hnF, hn1, -, hnH⟩ := gapMargins_of_width hL2 le_rfl hm₁ hw hn20
  obtain ⟨hnF', hn1', -, hnH'⟩ := gapMargins_of_width hL2 le_rfl hm₁ hw hn20'
  have hcs : cellSide L 1 m₁ (k + 1) ≤ L * cellSide L 1 m₁ (k + 1) := cellSide_le_mul
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hKa : L ^ (k + 1) ≤ L * cellSide L 1 m₁ (k + 1) := by
    unfold cellSide
    calc L ^ (k + 1) ≤ L ^ ((k + 1) + 1 + m₁) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ L * L ^ ((k + 1) + 1 + m₁) := Nat.le_mul_of_pos_left _ (by omega)
  have htA : ∀ μ, L ^ ((k + 1) + 1 + m₁) ∣ (tAz μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ)
  have htB : ∀ μ, L ^ ((k + 1) + 1 + m₁) ∣ (tBz μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)
  have hnL : 2 * R + L * cellSide L 1 m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hnL' : 2 * R + L * cellSide L 1 m₁ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  -- the bridge labels of `z` with blocks in `T` lie in the recentred box
  have hiR : ∀ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z},
      blocksOf 1 (k + 1) Set.univ i.1 ⊆ T →
        ∀ y ∈ i.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tAz) := by
    intro i hi y hy
    have hDj := bridgeFamily_isDj hN hL2 hdom z i.1 i.2
    have hs := sitesOf_blocksOf hN (le_refl (k + 1)) isPiUnion_univ_aux hDj.2.1
    have hy' : y ∈ sitesOf (blocksOf 1 (k + 1) Set.univ i.1) := by rw [hs]; exact ⟨hy, trivial⟩
    obtain ⟨b, hb, hyb⟩ := mem_sitesOf.1 hy'
    exact hT b (hi hb) y hyb
  have hκmem : ∀ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z},
      blocksOf 1 (k + 1) Set.univ i.1 ⊆ T →
        (fun x => bm (x + tAz) - tBz) '' i.1 ∈
          bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SB)) (bc (z + τA) - τB) :=
    fun i hi => (mem_bridgeFamily_recentred_iff (ϱ := ϱ) hGA hGB hN hN' tAz tBz htA htB hn1 hn1'
      hnF hnF' hnH hnH' z hzc (Nat.mul_div_le R _) hroot (hiR i hi)).2 i.2
  refine gsumCoeff_blockSplit_recentred hN2 hk νS β p₁ δ hN hN' tAz tBz htA htB (by omega)
    (by omega) hp hp'
    (commonLabels Lab₀ hN hL2 (fun _ => Set.univ) (e1DomG (SA)) hdom)
    (commonLabels Lab₀' hN' hL2 (fun _ => Set.univ) (e1DomG (SB)) hdom')
    (commonAct A hN hL2 (fun _ => Set.univ) (e1DomG (SA)) hdom hεH hκ0 θ)
    (commonAct A' hN' hL2 (fun _ => Set.univ) (e1DomG (SB)) hdom' hεH' hκ0' θ')
    (fun i => commonAnchor Lb (fun _ => Set.univ) (e1DomG (SA)) z i)
    (fun i' => commonAnchor Lb' (fun _ => Set.univ) (e1DomG (SB)) (bc (z + τA) - τB) i')
    (fun i u Φ => e1MarkGParamG (SA) F₁ Sol ρ hp z eps θ i u Φ)
    (fun i' u Φ' => e1MarkGParamG (SB) F₁' Sol' ρ hp' (bc (z + τA) - τB) eps θ' i' u Φ')
    hGdep T hT (fun y => y.isLeft = true) (fun y => y.isLeft = true) ?_ ?_
    (fun y => match y with
      | Sum.inl y₀ => fun _ hy => Sum.inl (ψ₀ y₀ hy)
      | Sum.inr _ => fun hP _ => absurd hP (by simp)) ?_ ?_ ?_ ?_ ?_
    (fun i hi => ⟨(fun x => bm (x + tAz) - tBz) '' i.1, hκmem i hi⟩) ?_ ?_ ?_ ?_
  · intro s _ y hy Φ
    cases y with
    | inl y₀ => exact absurd rfl hy
    | inr r => rfl
  · intro s _ y hy Φ
    cases y with
    | inl y₀ => exact absurd rfl hy
    | inr r => rfl
  · intro y hP hy
    cases y with
    | inl y₀ => rfl
    | inr r => exact absurd hP (by simp)
  · intro y hP hy
    cases y with
    | inl y₀ => exact hψ₀b y₀ hy
    | inr r => exact absurd hP (by simp)
  · intro y₁ hP₁ hy₁ y₂ hP₂ hy₂ h
    cases y₁ with
    | inl a =>
      cases y₂ with
      | inl b => exact congrArg Sum.inl (hψ₀inj a hy₁ b hy₂ (Sum.inl_injective h))
      | inr r => exact absurd hP₂ (by simp)
    | inr r => exact absurd hP₁ (by simp)
  · intro y' hP' hy'
    cases y' with
    | inl a =>
      obtain ⟨y, hy, rfl⟩ := hψ₀surj a hy'
      exact ⟨Sum.inl y, rfl, hy, rfl⟩
    | inr r => exact absurd hP' (by simp)
  · intro s hs y hP hy Φ Φ' hR
    cases y with
    | inl y₀ => exact hA s hs y₀ hy Φ Φ' hR
    | inr r => exact absurd hP (by simp)
  · intro i hi
    show blocksOf 1 (k + 1) Set.univ ((fun x => bm (x + tAz) - tBz) '' i.1) =
      (blocksOf 1 (k + 1) Set.univ i.1).image (fun b => σBi1 (σc1 (σAc1 b)))
    exact blocksOf_recentred hN hN' tAz tBz htA htB (by omega) (by omega) (hiR i hi)
  · intro i₁ hi₁ i₂ hi₂ h
    exact Subtype.ext (image_recentred_inj (by omega) tAz tBz (hiR i₁ hi₁) (hiR i₂ hi₂)
      (congrArg Subtype.val h))
  · intro i' hi'
    change blocksOf 1 (k + 1) Set.univ i'.1 ⊆ T.image (fun b => σBi1 (σc1 (σAc1 b))) at hi'
    obtain ⟨Y, hYR, hYimg, hYT⟩ := preimage_recentred hN hN' tAz tBz htA htB hnL hnL' hT
      (bridgeFamily_isDj hN' hL2 hdom' _ i'.1 i'.2) hi'
    have hYmem : Y ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z :=
      (mem_bridgeFamily_recentred_iff (ϱ := ϱ) hGA hGB hN hN' tAz tBz htA htB hn1 hn1' hnF hnF'
        hnH hnH' z hzc (Nat.mul_div_le R _) hroot hYR).1 (by rw [hYimg]; exact i'.2)
    exact ⟨⟨Y, hYmem⟩, hYT, Subtype.ext hYimg⟩
  · intro s hs i hi Φ Φ' hR
    have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
    exact e1MarkGParamG_recentred hN2 hk νS β p₁ δ hC hC' hGA hGB hMX hmar hαK hsm hF₁ hF₁' hSol
      hSol' hd hL2 hm₁ hN hN' zv hz z hw hn20 hn20' hzc hroot i
      ⟨_, hκmem i hi⟩ rfl (hiR i hi) θ θ' hθ hθ' hraw hρ hp hp' Φ Φ' hR (by linarith) (hum _ hs1)

end CoefRec

end Balaban.Polymer.TwoTorusStep
