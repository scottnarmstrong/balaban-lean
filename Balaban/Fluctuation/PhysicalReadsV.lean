/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionHatV
public import Balaban.Fluctuation.RowsHat
public import Balaban.Localization.FootprintFl
public import Balaban.Localization.SupportMargin
import Mathlib.Tactic.Ring

/-!
# Support facts for the sites read by the potential summand `V` (FOOTPRINT.md, section 3, row V)

The block functional of `vblock_expansion_hat` is `blockEnergyOne`: for a datum `D` it is
`energyBlock` evaluated at the multiplier `α = bgMultC D`, the fluctuation correction
`δφ = flFieldOne D ψ'` and the fluctuation variable `ψ'`.  The landed density is

```
energyDensity x =
  (if x ∈ Ω₁(Hm) then ½ (a_n / L^{2n}) ∑ᵢ (ψ' x i - blockMean δφ x i)² else 0)
  + ½ (∑_μ ∑ᵢ (δφ (x + e_μ) i - δφ x i)² + ν ∑ᵢ (δφ x i)² + α x ∑ᵢ (δφ x i)²).
```

So the functional reads exactly three kinds of data, and no background field
`φ_{k+1}` at all:

* the multiplier `α` at the sites `x` of the block (`blockSites`);
* the correction `δφ` at the sites of `readSites` (the block, its right neighbours, the `k`-block
  of `Hm` through each site of the block);
* the variable `ψ'` at the sites `x` of the block.

This file proves, for each kind, that its reads stay in the component `Y₁`.

* `multiplier_reads_subset` (T1): from `BlockMargin`, the residual footprint `resDep Gp x` of each
  multiplier site lies in `X₁ ⊆ Y₁`.
* `fluct_corr_dichotomy` (T2, T4): for a decoupled parameter vector which vanishes on the
  parameter cubes outside the polymer, at every site `u ∈ Y₁` either the correction vanishes, or
  `u ∈ S_Y^F` and the footprints `resDep Gp u` and `approxDep Gp w` (`w` a row site of `Hm` at `u`)
  lie in `Y₁`.  This covers the block, the right neighbours and the `k`-block alike, each read of
  the background being a read of `δφ`; there are no background-only read sites in `V`.
* `energyDensity_psi_expand`, `energyDensity_of_corr_zero` (T3): the term quadratic in `ψ'(x)`,
  `½ (a_n / L^{2n}) ∑ᵢ ψ'(x)ᵢ²`, is present whatever `δφ` is; it is the whole density when the
  correction vanishes on the sites read.  `completeBlocks_of_labels`, `psi_block_unitOut`: the
  hat variable it reads is on the complete top block of `x`, which lies in `Y₁`.
* `vblock_reads_covered` (T5): the three statements together.

This file proves support facts only.  The sharp locality theorem for the `V` expansion (the
parallel version of `vblock_expansion_hat`) and the `E`, `F`, `ν` summands are separate packages.
-/

@[expose] public section

namespace Balaban.Fluctuation.PhysicalReadsV

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Finset Matrix

section Multiplier

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **T1.**  Let `Gp` have full level.  If each multiplier site of `Zα` lies in the interaction box
of a centre whose thickened box lies in `X₁` (`BlockMargin`), then the residual footprint
`resDep Gp x` of every multiplier site lies in `X₁`. -/
theorem multiplier_reads_subset_X1 (hG : IsLevel Gp (k + 1))
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {Zα : Set (CTorus d L N₁ m₁ (k + 1))}
    (hmar : BlockMargin Gp X₁f Zα) {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ Zα) :
    resDep Gp x ⊆ X₁f := by
  obtain ⟨z, hz, hxz, -, hsub⟩ := hmar x hx (by rw [hG.Ω_one]; exact Finset.mem_univ _)
  intro v hv
  exact hsub ⟨v, by rw [hG.Ω_one]; exact Finset.mem_univ _⟩ (resDep_subset_hatBox hG hz hxz hv)

/-- **T1 (`multiplier_reads_subset`).**  The same with the component: if `X₁ ⊆ Y₁` then
`resDep Gp x ⊆ Y₁` for every multiplier site `x`. -/
theorem multiplier_reads_subset (hG : IsLevel Gp (k + 1))
    {X₁f Y : Finset (CTorus d L N₁ m₁ (k + 1))} (hXY : X₁f ⊆ Y)
    {Zα : Set (CTorus d L N₁ m₁ (k + 1))}
    (hmar : BlockMargin Gp X₁f Zα) {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ Zα) :
    resDep Gp x ⊆ Y :=
  (multiplier_reads_subset_X1 hG hmar hx).trans hXY

end Multiplier

section Correction

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a : ℕ → ℝ} {ν : ℝ}

/-- **The support of the decoupled Green operator on `Y`.**  Let `(Y, A)` be a union of components
of the incidence graph and `u` a parameter vector vanishing on the parameter cubes outside `𝒞`.
If `(G_u(α) f)(x) ≠ 0` at a site `x ∈ Y`, then `x ∈ S_Y^F`. -/
theorem Gs_mulVec_ne_zero_mem_SYF {C : DecCover d L N₁ m₁ (k + 1)}
    {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} (S : Dec2.FootLocalGeom C)
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {A : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hY : Dec2.IsIncUnion C H a ν X₁ 𝒞 Y A) {u : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hu : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → u P = 0) {α : H.Ω 1 → ℂ} {f : H.Ω 1 → ℂ}
    {x : H.Ω 1} (hxY : (x : CTorus d L N₁ m₁ (k + 1)) ∈ Y)
    (hx : (Dec2.Gs C H a ν α u *ᵥ f) x ≠ 0) :
    (x : CTorus d L N₁ m₁ (k + 1)) ∈ Dec2.SYF C H a ν X₁ 𝒞 Y := by
  classical
  have hc := Dec2.dg5_support_fp S u f x hx
  unfold Dec2.Core at hc
  obtain ⟨z, hzZ, hxz⟩ := Finset.mem_biUnion.1 hc
  have hzZ' := Finset.mem_filter.1 hzZ
  exact Dec2.fp_vanish hY hu hzZ'.1 hzZ'.2 (coreBox_subset_box hxz) hxY

/-- **The correction vanishes or lies in `S_Y^F`** (the field `δφ = G_s(α₀ + δα)(F_s - δα φ₀)` in
the form `dphi`).  At a site `y ∈ Y`, a nonzero component of the correction forces
`y ∈ S_Y^F`. -/
theorem svec_dphi_ne_zero_mem_SYF {C : DecCover d L N₁ m₁ (k + 1)}
    {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} (S : Dec2.FootLocalGeom C)
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {A : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hY : Dec2.IsIncUnion C H a ν X₁ 𝒞 Y A) {s : Dec2.DecParams C}
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → Dec2.extS C s P = 0)
    {α₀ δα : H.Ω 1 → ℂ} {φ₀ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    {Fs : H.Ω 1 × Fin N → ℂ} {y : CTorus d L N₁ m₁ (k + 1)} (hyY : y ∈ Y) {i : Fin N}
    (h : svec H (dphi H (Dec2.decG C H a ν s) α₀ φ₀ Fs δα) y i ≠ 0) :
    y ∈ Dec2.SYF C H a ν X₁ 𝒞 Y := by
  classical
  by_cases hy : y ∈ H.Ω 1
  · rw [svec_of_mem H _ ⟨y, hy⟩ i] at h
    unfold dphi at h
    rw [liftOp_mulVec] at h
    exact Gs_mulVec_ne_zero_mem_SYF (a := a) (ν := ν) S hY hs0 (x := ⟨y, hy⟩) hyY h
  · exact absurd (svec_of_not_mem H _ hy i) h

variable (Hm) in
/-- **T2 and T4 (`fluct_corr_dichotomy`).**  Let `Gp` have level `k + 1`, `Hm` level `k`, and let
`Y` be a nearest-neighbour component of `V(𝒞) ∩ Ω₁(Gp)`.  For a decoupled parameter vector `s`
which vanishes on the parameter cubes outside `𝒞`, and any `Hm`-field of the form
`δφ = dphi (G_s) α₀ φ₀ F δα` (the fluctuation correction), at every site `y ∈ Y` and component `i`:
either `δφ(y)ᵢ = 0`, or `y ∈ S_Y^F` and the footprint `resDep Gp y` of the residual and the
footprint `approxDep Gp w` of every row site `w` of `Hm` at `y` lie in `Y`. -/
theorem fluct_corr_dichotomy (hGp : IsLevel Gp (k + 1)) (hHm : IsLevel Hm k)
    (S : DGSetting Gp a ν) (hconn : HatConn Gp)
    (hrow : RowInHat (coverOf Gp) Hm a ν)
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (h𝒞 : ∀ P ∈ 𝒞, P ∈ (coverOf Gp).cubeIdx)
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    {s : Dec2.DecParams (coverOf Gp)}
    (hs0 : ∀ P ∈ (coverOf Gp).parCubes X₁, P ∉ 𝒞 → Dec2.extS (coverOf Gp) s P = 0)
    (α₀ δα : Hm.Ω 1 → ℂ) (φ₀ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (Fs : Hm.Ω 1 × Fin N → ℂ) {y : CTorus d L N₁ m₁ (k + 1)} (hyY : y ∈ Y) (i : Fin N) :
    svec Hm (dphi Hm (Dec2.decG (coverOf Gp) Hm a ν s) α₀ φ₀ Fs δα) y i = 0 ∨
      (y ∈ Dec2.SYF (coverOf Gp) Hm a ν X₁ 𝒞 Y ∧ resDep Gp y ⊆ Y ∧
        ∀ w ∈ resSites Hm y, approxDep Gp w ⊆ Y) := by
  classical
  by_cases h0 : svec Hm (dphi Hm (Dec2.decG (coverOf Gp) Hm a ν s) α₀ φ₀ Fs δα) y i = 0
  · exact Or.inl h0
  · right
    have SL : Dec2.CoverLocal (coverOf Gp) Gp a ν (Dec2.selfKc d L) (Cchi d L) :=
      Dec2.coverLocal_self S
    have hsubΩ : ∀ x, x ∈ Hm.Ω 1 → x ∈ Gp.Ω 1 := fun x _ => by
      rw [hGp.Ω_one]; exact Finset.mem_univ _
    obtain ⟨A, hIU, -⟩ := incUnion_of_nnComp SL hconn hsubΩ hrow h𝒞 hY
    have hSYF := svec_dphi_ne_zero_mem_SYF (a := a) (ν := ν) ⟨SL.chi_supp⟩ hIU hs0 hyY h0
    exact ⟨hSYF, fluct_footprint_subset hGp hHm S hconn hY hSYF⟩

end Correction

section Quadratic

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}

/-- **The term of the density quadratic in `ψ'(x)`**: `½ (a_n / L^{2n}) ∑ᵢ ψ'(x)ᵢ²`. -/
noncomputable def psiSqTerm (a : ℕ → ℝ) (n : ℕ) (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (x : CTorus d L N₁ m₁ K) : ℂ :=
  (((1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) * ∑ i, ψ' x i * ψ' x i

/-- **T3.**  For `x ∈ Ω₁(Hm)` the density is the term quadratic in `ψ'(x)`, plus a term linear in
`ψ'(x)` times the block mean of the correction, plus the density at `ψ' = 0`.  The quadratic term
does not involve `δφ` or `α`. -/
theorem energyDensity_psi_expand (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) (α : Gp.Ω 1 → ℂ)
    (δφ : Hm.Ω 1 × Fin N → ℂ) (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ Hm.Ω 1) :
    energyDensity Gp Hm a ν n α δφ ψ' x =
      energyDensity Gp Hm a ν n α δφ (fun _ _ => 0) x + psiSqTerm a n ψ' x -
        (((a n / ((L : ℝ) ^ n) ^ 2 : ℝ)) : ℂ) *
          ∑ i, ψ' x i * blockMean Hm n (fun y => svec Hm δφ y i) x := by
  classical
  have key : ∑ i, (ψ' x i - blockMean Hm n (fun y => svec Hm δφ y i) x) *
        (ψ' x i - blockMean Hm n (fun y => svec Hm δφ y i) x) =
      ∑ i, (0 - blockMean Hm n (fun y => svec Hm δφ y i) x) *
        (0 - blockMean Hm n (fun y => svec Hm δφ y i) x) + ∑ i, ψ' x i * ψ' x i -
      2 * ∑ i, ψ' x i * blockMean Hm n (fun y => svec Hm δφ y i) x := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold energyDensity psiSqTerm
  simp only [hx, ↓reduceIte]
  rw [key]
  push_cast
  ring

/-- **T3.**  If the correction vanishes at the sites read, the density is the quadratic term
alone (on `Ω₁(Hm)`; zero off it): it is present outside the core. -/
theorem energyDensity_of_corr_zero (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) (α : Gp.Ω 1 → ℂ)
    (δφ : Hm.Ω 1 × Fin N → ℂ) (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ)
    {x : CTorus d L N₁ m₁ K}
    (hδ : ∀ y : CTorus d L N₁ m₁ K,
      (y = x ∨ (∃ μ : Fin d, y = x + Pi.single μ 1) ∨ y ∈ Hm.blk n x) →
      ∀ i, svec Hm δφ y i = 0) :
    energyDensity Gp Hm a ν n α δφ ψ' x =
      if x ∈ Hm.Ω 1 then psiSqTerm a n ψ' x else 0 := by
  classical
  have hbm : ∀ i, blockMean Hm n (fun y => svec Hm δφ y i) x = 0 := by
    intro i
    unfold blockMean
    rw [Finset.sum_eq_zero fun y hy => hδ y (Or.inr (Or.inr hy)) i, mul_zero]
  have h0 := fun i => hδ x (Or.inl rfl) i
  have h1 := fun μ i => hδ (x + Pi.single μ 1) (Or.inr (Or.inl ⟨μ, rfl⟩)) i
  unfold energyDensity psiSqTerm
  simp only [hbm, h0, h1]
  split_ifs <;> simp

end Quadratic

section Blocks

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {m₀ : ℕ}
variable {ι : Type*} {c : ι → ℕ × CTorus d L N₁ m₁ (k + 1)}

/-- **The label `Y₁ = compY` is a union of complete top blocks** (via `labels_unitBlock_dichotomy`):
`CompleteBlocks Gp Y`. -/
theorem completeBlocks_of_labels {j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hN : L ^ m₀ ∣ N₁) (hG : IsLevel Gp (k + 1)) (hc : ∀ i, c i ∈ cubeIdx Gp) (C : Finset ι)
    {Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : ∀ x, x ∈ Y ↔ x ∈ compY c (X1 Gp m₀ j 𝒦X) C) : CompleteBlocks Gp Y := by
  intro y y' hyY hb
  rw [unitBlock1_unitBlock, unitBlock1_unitBlock] at hb
  rcases (labels_unitBlock_dichotomy (m₀ := m₀) (j := j) (𝒦X := 𝒦X) hN hG hc C
    (y : CTorus d L N₁ m₁ (k + 1))).1 with h | h
  · exact (hY _).2 (h hb)
  · exact absurd ((hY _).1 hyY) (fun hh => Set.disjoint_left.1 h (show _ = _ from rfl) hh)

/-- **T3, the hat variable read by `ψ'(x)`.**  For a site `x` of `Y₁` the unit points of its complete
top block (`UnitOut`) all have their block inside `Y₁`: `ψ'(x) = liftC (cc • C^{1/2} ψ̂)(x)` reads
`ψ̂` only on blocks inside `Y₁` (this is the input `hout` of `hatPsiF_rows_of_bgAgree`). -/
theorem psi_block_unitOut (hG : IsLevel Gp (k + 1)) {Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcomp : CompleteBlocks Gp Y) {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ Y) :
    UnitOut Gp Y (unitPt hG x) := fun y' hy' => hcomp ⟨x, (hG x).1⟩ y' hx hy'

end Blocks

section Ledger

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a : ℕ → ℝ} {ν : ℝ} {m₀ j : ℕ}
variable {ι : Type*} {c : ι → ℕ × CTorus d L N₁ m₁ (k + 1)}

/-- **T5, the read ledger of the `V`-block functional.**  Under the typing data of
`vblock_expansion_hat` (full levels, the setting `DGSetting Gp a ν`, `HatConn`, `RowInHat`,
`hZ : readSites Hm k z ⊆ X₁`, `hmar : BlockMargin`) and the component hypothesis (`Y₁ = compY` of
the polymer `C` over `X₁ = X1`, a nearest-neighbour component of `V(𝒞) ∩ Ω₁`), every read of the
functional is covered:

1. each multiplier site `x` of the block has `resDep Gp x ⊆ Y₁`;
2. at each site `u` of `readSites Hm k z` and each component `i`, the correction
   `δφ(u)ᵢ = svec (dphi (G_s) α₀ φ₀ F δα) u i` of a decoupled parameter vector `s` vanishing off
   the polymer vanishes, or `u ∈ S_Y^F` with `resDep Gp u ⊆ Y₁` and `approxDep Gp w ⊆ Y₁` for the
   `Hm` row sites `w` of `u`;
3. `Y₁` is a union of complete top blocks, and each site `x` of the block has its unit block
   inside `Y₁` (`UnitOut`), which is where `ψ'(x)` reads the hat variable.

The functional reads no background field other than through `δφ`; so the neighbours and the
`Hm`-block sites need no margin beyond `hZ`. -/
theorem vblock_reads_covered (hGp : IsLevel Gp (k + 1)) (hHm : IsLevel Hm k)
    (S : DGSetting Gp a ν) (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm a ν)
    {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {X₁f Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (C : Finset ι) (hc : ∀ i, c i ∈ cubeIdx Gp) (hN : L ^ m₀ ∣ N₁)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hmemY : ∀ x, x ∈ Y ↔ x ∈ compY c (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C)
    (hY : IsNnComp ((Vset X₁f (C.image c)).filter fun x => x ∈ Gp.Ω 1) Y)
    {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
    (hZ : readSites Hm k z ⊆ ↑X₁f)
    (hmar : BlockMargin Gp X₁f
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    {s : Dec2.DecParams (coverOf Gp)}
    (hs0 : ∀ P ∈ (coverOf Gp).parCubes X₁f, P ∉ C.image c → Dec2.extS (coverOf Gp) s P = 0)
    (α₀ δα : Hm.Ω 1 → ℂ) (φ₀ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (Fs : Hm.Ω 1 × Fin N → ℂ) :
    (∀ x ∈ blockSites d L N₁ m₁ (k + 1) k z, resDep Gp x ⊆ Y) ∧
    (∀ u ∈ readSites Hm k z, ∀ i : Fin N,
      svec Hm (dphi Hm (Dec2.decG (coverOf Gp) Hm a ν s) α₀ φ₀ Fs δα) u i = 0 ∨
        (u ∈ Dec2.SYF (coverOf Gp) Hm a ν X₁f (C.image c) Y ∧ resDep Gp u ⊆ Y ∧
          ∀ w ∈ resSites Hm u, approxDep Gp w ⊆ Y)) ∧
    CompleteBlocks Gp Y ∧
    (∀ x ∈ blockSites d L N₁ m₁ (k + 1) k z, UnitOut Gp Y (unitPt hGp x)) := by
  have hXY : ∀ x ∈ X₁f, x ∈ Y := fun x hx =>
    (hmemY x).2 (subset_compY (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C (Finset.mem_coe.2 hx))
  have hXYs : X₁f ⊆ Y := fun x hx => hXY x hx
  have hblk : ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k z, x ∈ X₁f := fun x hx =>
    Finset.mem_coe.1 (hZ ⟨x, hx, Or.inl rfl⟩)
  have hcomp : CompleteBlocks Gp Y :=
    completeBlocks_of_labels hN hGp hc C (fun x => by rw [hmemY x, hX₁])
  have h𝒞 : ∀ P ∈ C.image c, P ∈ (coverOf Gp).cubeIdx := by
    intro P hP
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hP
    exact hc i
  refine ⟨fun x hx => ?_, fun u hu i => ?_, hcomp, fun x hx => ?_⟩
  · exact multiplier_reads_subset hGp hXYs hmar (Finset.mem_coe.2 hx)
  · exact fluct_corr_dichotomy Hm hGp hHm S hconn hrow h𝒞 hY hs0 α₀ δα φ₀ Fs
      (hXY u (Finset.mem_coe.1 (hZ hu))) i
  · exact psi_block_unitOut hGp hcomp (hXY x (hblk x hx))

end Ledger

end Balaban.Fluctuation.PhysicalReadsV
