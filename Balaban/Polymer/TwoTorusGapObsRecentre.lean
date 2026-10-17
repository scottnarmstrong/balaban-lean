/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapObsSymTilt
public import Balaban.Polymer.TwoTorusGapIdentSite

/-!
# The coefficient of the observable under the recentring map (item 24, blocker 7)

The recentring map of the gap-scale closeness is `φ x = bm (x + tA) - tB`: translate the first
torus by `tA`, move to the second torus by the box map, translate by `-tB`.  The block measures of
the two steps correspond along `φ` on the cubes whose translate lies in the box.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory
  Balaban.Localization.DetUnitIncidence Balaban.Inhabited Balaban.Inhabited.LevelStep

section Recentre

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ιu" b:max => (Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _) : unitPts (GB))

/-- **The unit-point map of the recentring.**  The unit point of the recentred site is the image of
the unit point under `unitAct_B⁻¹ ∘ ιu ∘ unitAct_A`. -/
theorem unitPt_recentred {R : ℕ}
    (hn : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {tA : CTorus d L N₁ m₁ (k + 1)} {tB : CTorus d L N₁' m₁ (k + 1)}
    (SSA : LatSymm (GA) (GA) (Equiv.addRight tA)) (hUA : UnitBlockPres (Equiv.addRight tA))
    (SSB : LatSymm (GB) (GB) (Equiv.addRight tB)) (hUB : UnitBlockPres (Equiv.addRight tB))
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) :
    unitPt hGB (bm (x + tA) - tB) =
      (unitAct (GB) SSB hUB).symm (ιu (unitAct (GA) SSA hUA (unitPt hGA x))) := by
  have e1 : unitAct (GA) SSA hUA (unitPt hGA x) = unitPt hGA (x + tA) :=
    unitPt_sym hGA SSA hUA x
  rw [e1, unitImage_unitPt hn hGA hGB hx, unitAct_symm_unitPt hGB SSB hUB (bm (x + tA))]
  congr 1
  simp [sub_eq_add_neg]

set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ

/-- **The block measures on two tori under the recentring map.**  The integrals of corresponding
functions of the block variables agree: a function `F` of the blocks `Z` whose sites, translated by
`tA`, lie in the box of radius `R`, and `F'` with `F' Φ' = F Φ` whenever `Φ'` at the unit point of
`φ x = bm (x + tA) - tB` equals `Φ` at the unit point of `x`, for the sites `x` with `x + tA` in the
box. -/
theorem integral_blockSplit_recentred (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hn : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    {tA : CTorus d L N₁ m₁ (k + 1)} {tB : CTorus d L N₁' m₁ (k + 1)}
    (SSA : LatSymm (GA) (GA) (Equiv.addRight tA)) (hUA : UnitBlockPres (Equiv.addRight tA))
    (SSB : LatSymm (GB) (GB) (Equiv.addRight tB)) (hUB : UnitBlockPres (Equiv.addRight tB))
    (Z : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ))
    (hZ : ∀ b ∈ Z, ∀ x ∈ box b.1 (cellSide L m₀ m₁ (k + 1)),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    {F : (∀ c, ((SA).blockSplit m₀ hp).Ωb c) → ℂ} (hF : DepOn Z F)
    {F' : (∀ c, ((SB).blockSplit m₀ hp').Ωb c) → ℂ}
    (hFF : ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) →
        Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm (x + tA) - tB)))
          ⟨unitPt (SB).hG' (bm (x + tA) - tB), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) → F' Φ' = F Φ) :
    ∫ Φ', F' Φ' ∂(Measure.pi ((SB).blockSplit m₀ hp').μ) =
      ∫ Φ, F Φ ∂(Measure.pi ((SA).blockSplit m₀ hp).μ) := by
  classical
  have : IsProbabilityMeasure (fluctMeasure1 N p₁) := isProbabilityMeasure_fluctMeasure1 N hp
  rw [integral_blockSplit_eq (SB) m₀ hp' F', integral_blockSplit_eq (SA) m₀ hp F]
  let ι : (SA).U → (SB).U := fun u =>
    (unitAct (GB) SSB hUB).symm ⟨bU (unitAct (GA) SSA hUA u : UnitTorus d L N₁ m₁ k),
      mem_unitPts_levelTop (N₁ := N₁') (ϱ := ϱ) _⟩
  have hι : ∀ x : CTorus d L N₁ m₁ (k + 1), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) →
      unitPt (SB).hG' (bm (x + tA) - tB) = ι (unitPt (SA).hG' x) :=
    fun x hx => unitPt_recentred hn hGA hGB SSA hUA SSB hUB hx
  have key : ∀ x' : (SB).U → Rn N,
      F' (fun _ u => x' u.1) = F (fun _ u => x' (ι u.1)) := by
    intro x'
    refine hFF _ _ (fun x hx => ?_)
    exact congrArg x' (hι x hx)
  simp_rw [key]
  let W : Finset (SA).U := Finset.univ.filter fun u => (SA).cellOf m₀ u ∈ Z
  have hsite : ∀ u ∈ W, ∃ x : CTorus d L N₁ m₁ (k + 1), unitBlock x = (u : UnitTorus d L N₁ m₁ k) ∧
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) := by
    intro u hu
    obtain ⟨x, hxu, hxb⟩ := exists_site_of_unitPt (SA) m₀ u
    exact ⟨x, hxu, hZ _ (Finset.mem_filter.1 hu).2 x hxb⟩
  have hinj : Set.InjOn ι W := by
    intro u₁ hu₁ u₂ hu₂ h
    obtain ⟨x₁, hx₁u, hx₁⟩ := hsite u₁ hu₁
    obtain ⟨x₂, hx₂u, hx₂⟩ := hsite u₂ hu₂
    have hu₁' : u₁ = unitPt (SA).hG' x₁ := Subtype.ext hx₁u.symm
    have hu₂' : u₂ = unitPt (SA).hG' x₂ := Subtype.ext hx₂u.symm
    have e1 : unitAct (GA) SSA hUA u₁ = unitPt hGA (x₁ + tA) :=
      (congrArg (unitAct (GA) SSA hUA) hu₁').trans (unitPt_sym hGA SSA hUA x₁)
    have e2 : unitAct (GA) SSA hUA u₂ = unitPt hGA (x₂ + tA) :=
      (congrArg (unitAct (GA) SSA hUA) hu₂').trans (unitPt_sym hGA SSA hUA x₂)
    have h1v : bU (↑(unitAct (GA) SSA hUA u₁) : UnitTorus d L N₁ m₁ k) =
        bU (↑(unitAct (GA) SSA hUA u₂) : UnitTorus d L N₁ m₁ k) :=
      congrArg Subtype.val ((unitAct (GB) SSB hUB).symm.injective h)
    rw [e1, e2] at h1v
    have h2 := unitPt_eq_of_unitImage_eq hn hn' hGA hGB hx₁ hx₂ (Subtype.ext h1v)
    exact (unitAct (GA) SSA hUA).injective (e1.trans (h2.trans e2.symm))
  have hdep : DepOn (Ω := fun _ : (SA).U => Rn N) W
      (fun x : (SA).U → Rn N => F (fun _ u => x u.1)) := by
    intro x y hxy
    refine hF _ _ (fun b hb => ?_)
    funext u
    refine hxy u.1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    rw [u.2]; exact hb
  exact integral_pi_comp_of_injOn (fluctMeasure1 N p₁) ι W hinj hdep

end Recentre

end Balaban.Polymer.TwoTorusStep
