/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.FootprintFl
public import Balaban.Localization.I5FluctSol
public import Balaban.Localization.PolymerGeometry
public import Balaban.Fluctuation.InteractionEngine
public import Balaban.Fluctuation.InteractionFPart
public import Balaban.Fluctuation.Prop33Nu

/-!
# Support facts for the source summand `F` and the mass summand `ν`

The fluctuation correction `δφ_m` is the decoupled Green output `liftOp (G_s(A)) (F_s - δα φ₀)`
(`flField`, `flFieldOne`).  This file proves the dichotomy on which the sharp locality of the two
summands rests, at a site `y` of the old support:

* (out) if `y` is outside the active core `Dec2.Core` of the fluctuation operator, then
  `δφ_m(y) = 0` in every component (`dphi_svec_eq_zero_of_not_mem_core`,
  `flField_svec_eq_zero_of_not_mem_core`, `flFieldOne_svec_eq_zero_of_not_mem_core`); hence the
  site functional `siteFun` of `F` vanishes and the density `nuDensity` of `ν` vanishes
  (`siteFun_eq_zero_of_not_mem_core`, `nuDensity_eq_zero_of_not_mem_core`);
* (in) if `y` is in the core, there is an active centre `z` with `y ∈ coreBox z ⊆ intBox z`
  (`exists_centre_of_mem_core`); if `y` lies in the component `Y₁` and the parameters vanish
  on the parameter cubes outside `𝒞`, then `y ∈ Dec2.SYF` (`mem_SYF_of_mem_core`), and the
  residual footprint of `y` and the approximate-field footprint at each `Hm`-row site of `y`
  lie in `Y₁` (`reads_subset_of_mem_core`).

The combined statements are `fsite_dichotomy` and `nu_site_dichotomy`.  The raw reads of `F`
and `ν` (the source amplitude `g(y)` and the raw `h(x)`) are at sites of `X₁ ⊆ Y₁`
(`raw_site_mem_comp`).

The sharp locality theorems for the expansions of `F` and `ν` (the physical versions of
`fsite_expansion_hat` and `nublock_expansion_hat`) and the `V`, `E` summands are separate
packages; nothing here concerns them.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset Matrix

section Out

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱm : ℝ}
variable {C : DecCover d L N₁ m₁ K} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm} {a : ℕ → ℝ} {ν : ℝ}

/-- **(out), the Green output.**  For the decoupled Green operator `𝒢 = G_s(·)`, the vector
`δφ = liftOp 𝒢(α₀ + δα) (F_s - δα φ₀)` vanishes at every site outside the core `Core(ℛ)` of the
parameter vector. -/
theorem dphi_svec_eq_zero_of_not_mem_core (S : Dec2.FootLocalGeom C) (s : Dec2.DecParams C)
    (α₀ : Hm.Ω 1 → ℂ) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (Fs : Hm.Ω 1 × Fin N → ℂ)
    (δα : Hm.Ω 1 → ℂ) {y : CTorus d L N₁ m₁ K}
    (hy : y ∉ Dec2.Core C (Dec2.extS C s)) (i : Fin N) :
    svec Hm (dphi Hm (Dec2.decG C Hm a ν s) α₀ φ₀ Fs δα) y i = 0 := by
  by_cases hyΩ : y ∈ Hm.Ω 1
  · rw [svec_of_mem' _ hyΩ, dphi, liftOp_mulVec]
    by_contra hne
    exact hy (Dec2.dg5_support_fp S (Dec2.extS C s) _ ⟨y, hyΩ⟩ hne)
  · exact svec_of_not_mem Hm _ hyΩ i

/-- **(out), the fluctuation field.**  `δφ_m(s)` vanishes at every site outside the core. -/
theorem flField_svec_eq_zero_of_not_mem_core (S : Dec2.FootLocalGeom C) (ρ : ℝ)
    (s : Dec2.DecParams C) (e : Edat Hm N) {y : CTorus d L N₁ m₁ K}
    (hy : y ∉ Dec2.Core C (Dec2.extS C s)) (i : Fin N) :
    svec Hm (flField C Hm a ν ρ s e) y i = 0 :=
  dphi_svec_eq_zero_of_not_mem_core S s _ _ _ _ hy i

end Out

section OutOne

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a₁ ν BG₂ κ : ℝ}

/-- **(out), the field of the expansions.**  The fluctuation field `flFieldOne` (parameter
vector `s ≡ 1`) vanishes at every site outside `Core (coverOf Gp)` for the all-ones parameters. -/
theorem flFieldOne_svec_eq_zero_of_not_mem_core (D : BgData Gp N)
    (ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) {y : CTorus d L N₁ m₁ (k + 1)}
    (hy : y ∉ Dec2.Core (coverOf Gp) (Dec2.extS (coverOf Gp) fun _ => 1)) (i : Fin N) :
    svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') y i = 0 :=
  flField_svec_eq_zero_of_not_mem_core (Dec2.footLocalGeom_coverOf Gp) _ _ _ hy i

/-- The site functional `siteFun` of `F` vanishes at a site where `δφ` vanishes. -/
theorem siteFun_eq_zero_of_svec {y : CTorus d L N₁ m₁ (k + 1)} {i : Fin N}
    (pa : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) (δφ : Hm.Ω 1 × Fin N → ℂ)
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))
    (h : svec Hm δφ y i = 0) : siteFun Gp Hm y i pa δφ u = 0 := h

/-- **(out), `F`.**  The site functional `siteFun` at the fluctuation field vanishes outside the
core. -/
theorem siteFun_eq_zero_of_not_mem_core (D : BgData Gp N)
    (ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) {y : CTorus d L N₁ m₁ (k + 1)}
    (hy : y ∉ Dec2.Core (coverOf Gp) (Dec2.extS (coverOf Gp) fun _ => 1)) (i : Fin N)
    (pa : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) :
    siteFun Gp Hm y i pa (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') u = 0 :=
  siteFun_eq_zero_of_svec pa _ u (flFieldOne_svec_eq_zero_of_not_mem_core D ψ' hy i)

/-- The mass density `nuDensity` vanishes at a site where `δφ` vanishes: both of its terms carry
a factor `δφ(x)`. -/
theorem nuDensity_eq_zero_of_svec (δφ : Hm.Ω 1 × Fin N → ℂ) (φ₁ : Gp.Ω 1 × Fin N → ℂ)
    (hh : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) {x : CTorus d L N₁ m₁ (k + 1)}
    (h : ∀ i, svec Hm δφ x i = 0) : nuDensity Gp Hm δφ φ₁ hh x = 0 := by
  unfold nuDensity
  exact Finset.sum_eq_zero fun i _ => by rw [h i]; ring

/-- **(out), `ν`.**  The mass density `nuDensity` at the fluctuation field vanishes outside the
core, whatever the background field `φ₁` and the raw field `hh`. -/
theorem nuDensity_eq_zero_of_not_mem_core (D : BgData Gp N)
    (ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (φ₁ : Gp.Ω 1 × Fin N → ℂ)
    (hh : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∉ Dec2.Core (coverOf Gp) (Dec2.extS (coverOf Gp) fun _ => 1)) :
    nuDensity Gp Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') φ₁ hh x = 0 :=
  nuDensity_eq_zero_of_svec _ _ _ fun i => flFieldOne_svec_eq_zero_of_not_mem_core D ψ' hx i

end OutOne

section In

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a : ℕ → ℝ} {ν : ℝ}

/-- **(in), the centre.**  A site of the core lies in the core box of an active centre of the
cover, hence in its interaction box. -/
theorem exists_centre_of_mem_core {C : DecCover d L N₁ m₁ (k + 1)}
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {y : CTorus d L N₁ m₁ (k + 1)}
    (hy : y ∈ Dec2.Core C s) :
    ∃ z ∈ C.cubeIdx, C.sProd s z ≠ 0 ∧ y ∈ coreBox z ∧ y ∈ intBox z := by
  classical
  unfold Dec2.Core at hy
  obtain ⟨z, hz, hyz⟩ := Finset.mem_biUnion.1 hy
  obtain ⟨hzc, hzs⟩ := Finset.mem_filter.1 hz
  exact ⟨z, hzc, hzs, hyz, coreBox_subset_box hyz⟩

/-- **(in), the fluctuation box.**  Let `Y` be a nearest-neighbour component of
`V(𝒞) ∩ Ω₁(Gp)` and let the parameter vector `s` vanish on the parameter cubes of `X₁` outside
`𝒞`.  A site `y ∈ Y ∩ Ω₁(Hm)` of the core lies in `S_Y^F`: the centre of the core is eligible,
the component dichotomy puts its thickened box in `Y`, and the footprint of the centre for `Hm`
(its box and the rows of `Hm` there) lies in the thickened box. -/
theorem mem_SYF_of_mem_core (hGp : IsLevel Gp (k + 1)) (hHm : IsLevel Hm k)
    (S : DGSetting Gp a ν) (hconn : HatConn Gp)
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hs0 : ∀ P ∈ (coverOf Gp).parCubes X₁, P ∉ 𝒞 → s P = 0)
    {y : CTorus d L N₁ m₁ (k + 1)} (hyc : y ∈ Dec2.Core (coverOf Gp) s) (hyΩ : y ∈ Hm.Ω 1)
    (hyY : y ∈ Y) : y ∈ Dec2.SYF (coverOf Gp) Hm a ν X₁ 𝒞 Y := by
  classical
  obtain ⟨z, hz, hact, -, hyb⟩ := exists_centre_of_mem_core hyc
  have hE : Dec2.EligC (coverOf Gp) X₁ 𝒞 z := Dec2.eligC_of_active hs0 hz hact
  have hdich := Dec2.hdich_aux (Dec2.coverLocal_self S) hconn hY z hz hE.2
  have hsub : SubI Gp (hatBox z) Y := by
    rcases hdich with h | h
    · exact h
    · exact absurd hyY (h ⟨y, by rw [hGp.Ω_one]; exact Finset.mem_univ _⟩
        (box_subset_hatBox z hyb))
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hle : (L : ℝ) ^ k ≤ (L : ℝ) ^ (k + 1) := pow_le_pow_right₀ hL1 (Nat.le_succ k)
  have hhat : ∀ w, w ∈ hatBox z → w ∈ Y := fun w hw =>
    hsub ⟨w, by rw [hGp.Ω_one]; exact Finset.mem_univ _⟩ hw
  refine Finset.mem_biUnion.2 ⟨z, Finset.mem_filter.2 ⟨hz, hE, ⟨⟨y, hyΩ⟩, hyb⟩, ?_⟩, hyb⟩
  rintro x ⟨b, hb, rfl | ⟨w, hw, rfl⟩⟩
  · exact hhat _ (box_subset_hatBox z hb)
  · apply hhat
    have hu := mem_resSites_of_entry_ne_zero hw
    exact approxDep_subset_hatBox_of_near hGp hz hb
      (fun μ => (resSites_coord_bound hHm hu μ).mono hle) (mem_approxDep_self _)

/-- **(in), the reads.**  For a site `y` of `S_Y^F` the residual footprint `resDep Gp y` and the
approximate-field footprint `approxDep Gp u` at each `Hm`-row site `u` of `y` lie in `Y`. -/
theorem reads_subset_of_mem_SYF (hGp : IsLevel Gp (k + 1)) (hHm : IsLevel Hm k)
    (S : DGSetting Gp a ν) (hconn : HatConn Gp)
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : y ∈ Dec2.SYF (coverOf Gp) Hm a ν X₁ 𝒞 Y) :
    y ∈ Y ∧ resDep Gp y ⊆ Y ∧ (∀ u ∈ resSites Hm y, approxDep Gp u ⊆ Y) ∧
      y ∈ SY Gp X₁ 𝒞 Y ∧ approxDep Gp y ⊆ Y := by
  have h := fluct_footprint_subset hGp hHm S hconn hY hy
  have hSY := SYF_subset_SY_level (Hm := Hm) hGp S hconn hY hy
  have hap := (footprint_subset_component hGp X₁ 𝒞 Y).2 y hSY y (mem_resSites_self _)
  exact ⟨hap (mem_approxDep_self _), h.1, h.2, hSY, hap⟩

/-- **(in), the reads of a core site.**  Under the hypotheses of `mem_SYF_of_mem_core`, the
residual footprint of `y` and the approximate-field footprint at each `Hm`-row site of `y` lie
in `Y`. -/
theorem reads_subset_of_mem_core (hGp : IsLevel Gp (k + 1)) (hHm : IsLevel Hm k)
    (S : DGSetting Gp a ν) (hconn : HatConn Gp)
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hs0 : ∀ P ∈ (coverOf Gp).parCubes X₁, P ∉ 𝒞 → s P = 0)
    {y : CTorus d L N₁ m₁ (k + 1)} (hyc : y ∈ Dec2.Core (coverOf Gp) s) (hyΩ : y ∈ Hm.Ω 1)
    (hyY : y ∈ Y) :
    resDep Gp y ⊆ Y ∧ ∀ u ∈ resSites Hm y, approxDep Gp u ⊆ Y :=
  fluct_footprint_subset hGp hHm S hconn hY
    (mem_SYF_of_mem_core hGp hHm S hconn hY hs0 hyc hyΩ hyY)

end In

section Dichotomy

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a : ℕ → ℝ} {ν : ℝ}

/-- **The dichotomy for `δφ_m` at a site of the component** (used for `F` at `y ∈ X₁f` and for
`ν` at the sites of `blockSites k z ⊆ X₁f`).  Let `Y` be a nearest-neighbour component of
`V(𝒞) ∩ Ω₁(Gp)`, let `s` be a fluctuation parameter vector vanishing off `𝒞` on the parameter
cubes of `X₁`, and let `y ∈ Y`.  Then either `δφ_m(s)(y) = 0` in every component, or `y ∈ S_Y^F`
and the reads of `y` lie in `Y`.

The hypotheses on `s` and `y ∈ Y` are exactly what eligibility of the centre needs: that
`y ∈ X₁f` implies `y ∈ Y` is `raw_site_mem_comp`, but the statement is about the marked
parameters `s` of the term `(Y, 𝒞)`, not the physical value `s ≡ 1` (which is zero-free and so
eligible only if every parameter cube of `X₁` lies in `𝒞`). -/
theorem fsite_dichotomy (hGp : IsLevel Gp (k + 1)) (hHm : IsLevel Hm k)
    (S : DGSetting Gp a ν) (hconn : HatConn Gp)
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (ρ : ℝ) (s : Dec2.DecParams (coverOf Gp)) (e : Edat Hm N)
    (hs0 : ∀ P ∈ (coverOf Gp).parCubes X₁, P ∉ 𝒞 → Dec2.extS (coverOf Gp) s P = 0)
    {y : CTorus d L N₁ m₁ (k + 1)} (hyY : y ∈ Y) :
    (∀ i, svec Hm (flField (coverOf Gp) Hm a ν ρ s e) y i = 0) ∨
      (y ∈ Dec2.SYF (coverOf Gp) Hm a ν X₁ 𝒞 Y ∧ resDep Gp y ⊆ Y ∧
        ∀ u ∈ resSites Hm y, approxDep Gp u ⊆ Y) := by
  by_cases hyc : y ∈ Dec2.Core (coverOf Gp) (Dec2.extS (coverOf Gp) s)
  · by_cases hyΩ : y ∈ Hm.Ω 1
    · have h := mem_SYF_of_mem_core hGp hHm S hconn hY hs0 hyc hyΩ hyY
      exact Or.inr ⟨h, fluct_footprint_subset hGp hHm S hconn hY h⟩
    · exact Or.inl fun i => svec_of_not_mem Hm _ hyΩ i
  · exact Or.inl fun i => flField_svec_eq_zero_of_not_mem_core
      (Dec2.footLocalGeom_coverOf Gp) ρ s e hyc i

/-- **The `F` form of the dichotomy**: the site functional `siteFun` at the fluctuation field
vanishes, or the site lies in `S_Y^F` with its reads in `Y`. -/
theorem fsite_dichotomy_siteFun (hGp : IsLevel Gp (k + 1)) (hHm : IsLevel Hm k)
    (S : DGSetting Gp a ν) (hconn : HatConn Gp)
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (ρ : ℝ) (s : Dec2.DecParams (coverOf Gp)) (e : Edat Hm N)
    (hs0 : ∀ P ∈ (coverOf Gp).parCubes X₁, P ∉ 𝒞 → Dec2.extS (coverOf Gp) s P = 0)
    {y : CTorus d L N₁ m₁ (k + 1)} (hyY : y ∈ Y) (i : Fin N)
    (pa : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) :
    siteFun Gp Hm y i pa (flField (coverOf Gp) Hm a ν ρ s e) u = 0 ∨
      (y ∈ Dec2.SYF (coverOf Gp) Hm a ν X₁ 𝒞 Y ∧ resDep Gp y ⊆ Y ∧
        ∀ u ∈ resSites Hm y, approxDep Gp u ⊆ Y) :=
  (fsite_dichotomy hGp hHm S hconn hY ρ s e hs0 hyY).imp_left fun h => h i

/-- **The `ν` form of the dichotomy**: the mass density at the fluctuation field vanishes, or the
site lies in `S_Y^F` with its reads in `Y`; moreover the background factor `φ_s(x) - h(x)` is
then read inside `Y` (`reads_subset_of_mem_SYF`: `x ∈ S_Y^F ⊆ S_Y`, so `resDep Gp x ⊆ Y` and
`approxDep Gp x ⊆ Y`). -/
theorem nu_site_dichotomy (hGp : IsLevel Gp (k + 1)) (hHm : IsLevel Hm k)
    (S : DGSetting Gp a ν) (hconn : HatConn Gp)
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (ρ : ℝ) (s : Dec2.DecParams (coverOf Gp)) (e : Edat Hm N)
    (hs0 : ∀ P ∈ (coverOf Gp).parCubes X₁, P ∉ 𝒞 → Dec2.extS (coverOf Gp) s P = 0)
    {x : CTorus d L N₁ m₁ (k + 1)} (hxY : x ∈ Y)
    (φ₁ : Gp.Ω 1 × Fin N → ℂ) (hh : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    nuDensity Gp Hm (flField (coverOf Gp) Hm a ν ρ s e) φ₁ hh x = 0 ∨
      (x ∈ Dec2.SYF (coverOf Gp) Hm a ν X₁ 𝒞 Y ∧ x ∈ Y ∧ resDep Gp x ⊆ Y ∧
        approxDep Gp x ⊆ Y ∧ ∀ u ∈ resSites Hm x, approxDep Gp u ⊆ Y) := by
  rcases fsite_dichotomy hGp hHm S hconn hY ρ s e hs0 hxY with h | ⟨h, -⟩
  · exact Or.inl (nuDensity_eq_zero_of_svec _ _ _ h)
  · obtain ⟨h1, h2, h3, -, h5⟩ := reads_subset_of_mem_SYF hGp hHm S hconn hY h
    exact Or.inr ⟨h, h1, h2, h5, h3⟩

end Dichotomy

end Balaban.Localization
