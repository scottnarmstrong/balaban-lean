/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RowsHat
public import Balaban.Localization.FootprintFl
public import Balaban.Localization.RowsFl
public import Balaban.Localization.SupportMargin
public import Balaban.Fluctuation.HatLabelsDep

/-!
# Composition of the row-local theorems: from raw data on the component to the hat variable

Chains the row-local results of FOOTPRINT, section 2, items 3 to 5 (`SPLIT.md`, section 1).  For two
admissible data that agree on the component `Y₁` and two hat variables that agree on the unit blocks
of `Y₁`, the square-root image `hatSqrtF` and the hat-shifted field `hatPsiF` agree on `Y₁`; nothing
is required outside `Y₁`.

* `rowsCov_R_subset_resSites`, `bgAgree_of_agree_on_component`: the conclusion of the row-local
  background theorem (multipliers equal on `S_Y`, decoupled field equal on the sites `R(S_Y)` read by
  the `x`-variant rows) from agreement of the raw data on `Y₁` alone.  The `x`-variant rows at a site
  of `S_Y` read only sites of `resSites` (the site, its neighbours, its block), whose approximate
  field depends on `Y₁` only (`footprint_subset_component`).  The sites read by the `x`-variant need
  not be sites read by `H_D` (an entry of `H_D` may vanish where the `x`-variant entry does not),
  so the inclusion used is into `resSites`, not into `RowSite`.
* `completeBlocks_of_isNnComp`: at a whole-lattice level `k + 1`, a union `Y₁` of nearest-neighbour
  components of `X₁ ∪ ⋃_{P ∈ 𝒞} P` is a union of complete blocks (`CompleteBlocks`), when `X₁` is a
  union of complete cells of side `L ^ (k+1)`; the notion `CompleteBlocks` (equal `unitBlock1 ∘
  unitBlock`) is the cell `SameCell (L ^ (k+1))`.
* `hatSqrtF_rows`, `hatPsiF_rows`: the composed hat theorems.
* `fluct_correction_rows_of_agree_on_component`: raw agreement on `Y₁` and hat agreement on its unit
  blocks give agreement of the fluctuation correction (multiplier on `S_Y^F`, `dphi` on `Y₁`), the
  data of `i4a_local_fpS_rows_level` being `α₀ = flAlpha α`, `φ₀ = barField Ψ φ`, `δΨ = hatPsiF`,
  `f₁ = 0` (`flEdat`).  The sites `RowF` read by `H⁻_D` at `S_Y^F` lie in `resSites Hm` of a site
  of `S_Y^F`, where `fluct_footprint_subset` puts the approximate-field footprint inside `Y₁`.
* `hatOf_agree_unitOut`: agreement of two block configurations on `blocksOf m₀ (k+1) univ Y` (the
  hypothesis of `HatLabelsDirect.DirectTerms.ag`) gives agreement of the hat variables on the unit
  blocks of `Y₁ ⊆ Y`, when `Y` is a union of complete cells of side `cellSide L m₀ m₁ (k+1)`.

Facts found while composing: (i) the sites read by the `x`-variant rows need not be sites read by
`H_D` (an entry may vanish for `H_D` and not for the `x`-variant), so `rowsCov_R` is not contained
in `RowSite`; both lie in `resSites`, and that inclusion is what is used.  (ii) The cells of
`blocksOf` have side `cellSide L m₀ m₁ (k+1) = L ^ (k+1+m₀+m₁)`, those of `CompleteBlocks` side
`L ^ (k+1)`; `hatOf_agree_unitOut` needs `Y` to be a union of cells of the larger side.  The
component `compY` is only a union of cells of side `L ^ (k+1+m₁)` (`compY_isCellUnion`), the set
`Ysites` of side `cellSide` (`Ysites_isCellUnion`); so the hat hypothesis in the `blocksOf` form is
obtained for `Y = Ysites ⊇ Y₁`, not for `Y = Y₁`.

The physical-reads lemmas, the fan/engine congruence (FOOTPRINT item 7) and `PhysicalSharpLoc` are
separate packages and are not proved here.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.Polymer Finset Matrix

section Bg

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- The sites read by the `x`-variant rows at `S_Y` (and `S_Y` itself) lie in `resSites` of a site of
`S_Y`: the site, its nearest neighbours and its block. -/
theorem rowsCov_R_subset_resSites {a : ℕ → ℝ} {aT ν : ℝ} {α : Gp.Ω 1 → ℂ}
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {u : CTorus d L N₁ m₁ (k + 1)} (hu : u ∈ rowsCov_R Gp a aT ν α X₁ 𝒞 Y) :
    ∃ z ∈ SY Gp X₁ 𝒞 Y, u ∈ resSites Gp z := by
  classical
  rcases hu with hu | ⟨z, y, hz, rfl, x₀, -, hne⟩
  · exact ⟨u, hu, mem_resSites_self _⟩
  · refine ⟨z, hz, ?_⟩
    by_contra hn
    apply hne
    unfold resSites at hn
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
      not_or, not_exists] at hn
    obtain ⟨hxy, ⟨hblk, hp⟩, hm⟩ := hn
    exact xDirichlet_entry_eq_zero (G := Gp) (a := a) (aT := aT) (x₀ := x₀) (ν := ν) α hxy
      (fun μ => ⟨fun e => hp μ e.symm, fun e => hm μ e.symm⟩) hblk

/-- **The background field from raw data on the component.**  At a whole-lattice generating set of
level `k + 1`, if the raw data agree on `Y₁`, the multipliers of the decoupled backgrounds agree on
`S_Y` and the fields agree at every site whose approximate-field footprint lies in `Y₁`. -/
theorem bgField_of_agree_on_component
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn Gp) (hG : IsLevel Gp (k + 1))
    {s s' : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁ → extS Gp s P = 1 ∧ extS Gp s' P = 1)
    (hs0 : ∀ P ∈ parCubes Gp X₁, P ∉ 𝒞 → extS Gp s P = 0 ∧ extS Gp s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y → extS Gp s P = extS Gp s' P)
    (hdata : ∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gp.Ω 1 → D.h z = D'.h z)) :
    ∀ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ) (φ₂ : Gp.Ω 1 × Fin N → ℂ)
      (α₂ : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
      IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D' φ₂ α₂ →
      (∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY Gp X₁ 𝒞 Y → α x = α₂ x) ∧
      (∀ y : Gp.Ω 1, approxDep Gp (y : CTorus d L N₁ m₁ (k + 1)) ⊆ Y →
          ∀ i, φ (y, i) = φ₂ (y, i)) := by
  classical
  intro φ α φ₂ α₂ hI hI₂
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
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
  obtain ⟨hα, hcorr, -, -⟩ := i4b_local_of_agree_on_component hC.hS hC.Sp hconn hC.HBp hC.hκ.le
    hC.hM (fun P => (hs P).le) (fun P => (hs' P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom hDom' hG hY
    hs1 hs0 hag hdata hI hI₂
  refine ⟨hα, fun y happ i => ?_⟩
  have hyY : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y := happ (mem_approxDep_self _)
  have hphi : approxField Gp (compWeight L a₁) ν D.Ψ D.h y =
      approxField Gp (compWeight L a₁) ν D'.Ψ D'.h y :=
    approxField_congr fun w hw => hdata w (happ hw)
  have := hcorr y hyY i
  rw [hphi] at this
  linear_combination this

/-- **T1.  The hypothesis `hbg` of `hatSqrtF_rows_of_bgAgree` from raw-data agreement on `Y₁`.**
At a whole-lattice generating set of level `k + 1`, if the raw data `D, D'` agree on `Y₁` (`Ψ` on
`Y₁`, `h` on `Y₁ ∩ Ω₁`), then the decoupled backgrounds `(φ, α)`, `(φ₂, α₂)` have multipliers equal on
`S_Y` and fields equal on `R(S_Y)`. -/
theorem bgAgree_of_agree_on_component
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn Gp) (hG : IsLevel Gp (k + 1))
    {s s' : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁ → extS Gp s P = 1 ∧ extS Gp s' P = 1)
    (hs0 : ∀ P ∈ parCubes Gp X₁, P ∉ 𝒞 → extS Gp s P = 0 ∧ extS Gp s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y → extS Gp s P = extS Gp s' P)
    (hdata : ∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gp.Ω 1 → D.h z = D'.h z)) :
    ∀ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ) (φ₂ : Gp.Ω 1 × Fin N → ℂ)
      (α₂ : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
      IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D' φ₂ α₂ →
      (∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY Gp X₁ 𝒞 Y → α x = α₂ x) ∧
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈
          rowsCov_R Gp (compWeight L a₁) a₁ ν α X₁ 𝒞 Y → ∀ i, φ (y, i) = φ₂ (y, i)) := by
  classical
  intro φ α φ₂ α₂ hI hI₂
  obtain ⟨hα, hf⟩ := bgField_of_agree_on_component hC hconn hG hs hs' hD hD' hY hs1 hs0 hag hdata
    φ α φ₂ α₂ hI hI₂
  refine ⟨hα, fun y hy i => ?_⟩
  obtain ⟨z, hz, hyz⟩ := rowsCov_R_subset_resSites hy
  exact hf y ((footprint_subset_component hG X₁ 𝒞 Y).2 z hz _ hyz) i

end Bg

section Blocks

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- A union of nearest-neighbour components of a union of complete cells is a union of complete
cells (a cell is connected). -/
theorem isCellUnion_of_isNnComp {K a : ℕ} (ha0 : 0 < a) (hdvd : a ∣ (N₁ * L ^ m₁) * L ^ K)
    {Z Y : Finset (CTorus d L N₁ m₁ K)} (hZ : IsCellUnion a (Z : Set (CTorus d L N₁ m₁ K)))
    (hY : IsNnComp Z Y) : IsCellUnion a (Y : Set (CTorus d L N₁ m₁ K)) := by
  intro x hx y hy
  have hxY : x ∈ Y := Finset.mem_coe.1 hx
  have hxZ : x ∈ (Z : Set (CTorus d L N₁ m₁ K)) := Finset.mem_coe.2 (hY.1 hxY)
  have hcb : cbase a y = cbase a x := (sameCell_iff_cbase_eq ha0).1 hy
  have hsub : box (cbase a x) a ⊆ (Z : Set (CTorus d L N₁ m₁ K)) := by
    intro z hz
    exact hZ x hxZ z ((sameCell_iff_cbase_eq ha0).2 (cbase_eq_of_mem_box hdvd (aligned_cbase x) hz))
  have hpath := chain_in_box _ _ _ hsub (mem_box_cbase ha0 x) (hcb ▸ mem_box_cbase ha0 y)
  rw [Finset.mem_coe]
  clear hy hcb
  induction hpath with
  | refl => exact hxY
  | tail _ hs ih => exact hY.2 _ ih _ (Finset.mem_coe.1 hs.2.2) hs.1.2

/-- A union of complete cells of side `L ^ (k+1)` consists of complete blocks. -/
theorem completeBlocks_of_cellUnion {Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsCellUnion (L ^ (k + 1)) (Y : Set (CTorus d L N₁ m₁ (k + 1)))) :
    CompleteBlocks Gp Y := by
  intro y y' hy hb
  rw [unitBlock1_unitBlock, unitBlock1_unitBlock] at hb
  exact Finset.mem_coe.1 (hY y (Finset.mem_coe.2 hy) y' (sameCell_of_jBlock_eq le_rfl hb))

/-- **T2.  `CompleteBlocks` for the component.**  At a whole-lattice generating set of level `k + 1`,
if `X₁` is a union of complete cells of side `L ^ (k+1)` and the marked centres lie in `cubeIdx Gp`
(hence at level `k + 1`), then every union `Y` of nearest-neighbour components of
`X₁ ∪ ⋃_{P ∈ 𝒞} P` (`IsNnComp`) is a union of complete `(k+1)`-blocks. -/
theorem completeBlocks_of_isNnComp (hG : IsLevel Gp (k + 1))
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hX₁ : IsCellUnion (L ^ (k + 1)) (X₁ : Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒞 : ∀ P ∈ 𝒞, P ∈ cubeIdx Gp)
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y) :
    CompleteBlocks Gp Y := by
  classical
  have hfil : (Vset X₁ 𝒞).filter (fun x => x ∈ Gp.Ω 1) = Vset X₁ 𝒞 :=
    Finset.filter_true_of_mem fun x _ => by rw [hG.Ω_one]; exact Finset.mem_univ _
  rw [hfil] at hY
  have hP : ∀ P ∈ 𝒞, IsCellUnion (L ^ (k + 1)) (cubeP P : Set (CTorus d L N₁ m₁ (k + 1))) := by
    intro P hP x hx y hy
    have h1 : P.1 = k + 1 := level_eq_of_mem_cubeIdx hG (h𝒞 P hP)
    have h2 := mem_cubeP.1 (Finset.mem_coe.1 hx)
    exact Finset.mem_coe.2 (mem_cubeP.2 (SameCell.trans
      (SameCell.mono (pow_dvd_pow L (by omega)) hy) h2))
  have hZ : IsCellUnion (L ^ (k + 1)) ((Vset X₁ 𝒞 : Finset _) : Set (CTorus d L N₁ m₁ (k + 1))) := by
    intro x hx y hy
    have hx' : x ∈ X₁ ∨ ∃ P ∈ 𝒞, x ∈ cubeP P := by
      simpa [Vset] using hx
    rcases hx' with hx' | ⟨P, hP', hx'⟩
    · have := hX₁ x (Finset.mem_coe.2 hx') y hy
      simp only [Vset, Finset.coe_union, Set.mem_union, Finset.mem_coe]
      exact Or.inl (Finset.mem_coe.1 this)
    · have := hP P hP' x (Finset.mem_coe.2 hx') y hy
      simp only [Vset, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_biUnion]
      exact Or.inr ⟨P, hP', Finset.mem_coe.1 this⟩
  have hdvd : L ^ (k + 1) ∣ (N₁ * L ^ m₁) * L ^ (k + 1) := Dvd.intro_left _ rfl
  exact completeBlocks_of_cellUnion
    (isCellUnion_of_isNnComp (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _) hdvd hZ hY)

/-- The physical `X₁ = X1 Gp m₀ j 𝒦X` is a union of complete cells of side `L ^ (k+1)` (it is one of
side `cellSide L m₀ m₁ (k+1) = L ^ (k+1+m₀+m₁)`). -/
theorem X1_isCellUnion_unit {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} (hN : L ^ m₀ ∣ N₁) :
    IsCellUnion (L ^ (k + 1)) (X1 Gp m₀ j 𝒦X) :=
  (X1_isCellUnion (G := Gp) (j := j) (𝒦X := 𝒦X) hN).mono_dvd
    (pow_dvd_pow L (by omega))

end Blocks

section Rows

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **T3.  Square-root image of the hat variable from raw data on the component.**  As
`hatSqrtF_local`, with the raw data agreeing on `Y` only (`hdata`), the hat variables agreeing at the
unit points of the blocks inside `Y`, and the conclusion at a unit point with block inside `Y`.
Besides the level `IsLevel Gp (k+1)`, the geometric premises are that `X₁` is a union of complete
cells of side `L ^ (k+1)` and that the marked centres lie in `cubeIdx Gp`. -/
theorem hatSqrtF_rows (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) (hG : IsLevel Gp (k + 1))
    (hconn : HatConn Gp)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s s' : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁ → extS Gp s P = 1 ∧ extS Gp s' P = 1)
    (hs0 : ∀ P ∈ parCubes Gp X₁, P ∉ 𝒞 → extS Gp s P = 0 ∧ extS Gp s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y → extS Gp s P = extS Gp s' P)
    (hX₁ : IsCellUnion (L ^ (k + 1)) (X₁ : Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒞 : ∀ P ∈ 𝒞, P ∈ cubeIdx Gp)
    (hdata : ∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gp.Ω 1 → D.h z = D'.h z))
    (ψh ψh' : unitPts Gp × Fin N → ℂ)
    {b : unitPts Gp} (hb : UnitOut Gp Y b)
    (hh : ∀ b' : unitPts Gp, UnitOut Gp Y b' → ∀ i, ψh (b', i) = ψh' (b', i)) (i : Fin N) :
    (hatSqrtF Gp a₁ ν F₁ s (rawOf D) *ᵥ ψh) (b, i) =
      (hatSqrtF Gp a₁ ν F₁ s' (rawOf D') *ᵥ ψh') (b, i) := by
  classical
  exact hatSqrtF_rows_of_bgAgree hC hk hconn hMX hmar hα hsm hF₁ hs hs' hD hD' hY hs1 hs0 hag
    (completeBlocks_of_isNnComp hG hX₁ h𝒞 hY)
    (bgAgree_of_agree_on_component hC hconn hG hs hs' hD hD' hY hs1 hs0 hag hdata)
    ψh ψh' hb hh i

/-- **T3.  The hat-shifted field on the component from raw data on the component.**  As
`hatPsiF_local`, with raw data agreeing on `Y` only and hat variables agreeing at the unit points of
the blocks inside `Y`; the conclusion is at the sites of `Y`. -/
theorem hatPsiF_rows (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (hconn : HatConn Gp)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s s' : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁ → extS Gp s P = 1 ∧ extS Gp s' P = 1)
    (hs0 : ∀ P ∈ parCubes Gp X₁, P ∉ 𝒞 → extS Gp s P = 0 ∧ extS Gp s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y → extS Gp s P = extS Gp s' P)
    (hX₁ : IsCellUnion (L ^ (k + 1)) (X₁ : Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒞 : ∀ P ∈ 𝒞, P ∈ cubeIdx Gp)
    (hdata : ∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gp.Ω 1 → D.h z = D'.h z))
    (ψh ψh' : unitPts Gp × Fin N → ℂ)
    (hh : ∀ b' : unitPts Gp, UnitOut Gp Y b' → ∀ i, ψh (b', i) = ψh' (b', i)) :
    ∀ y ∈ Y,
      hatPsiF Gp a₁ ν hG' cc F₁ s (rawOf D) ψh y = hatPsiF Gp a₁ ν hG' cc F₁ s' (rawOf D') ψh' y := by
  classical
  exact hatPsiF_rows_of_bgAgree hC hk hG' cc hconn hMX hmar hα hsm hF₁ hs hs' hD hD' hY hs1 hs0 hag
    (completeBlocks_of_isNnComp hG' hX₁ h𝒞 hY)
    (bgAgree_of_agree_on_component hC hconn hG' hs hs' hD hD' hY hs1 hs0 hag hdata)
    ψh ψh' hh

end Rows

section Fl

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **T5.  The fluctuation correction on the component from raw data and hat variables on the
component.**  In the physical fluctuation step (`flEdat`, `fan_local_fl`) the data of Theorem I-4a on
`H⁻ = Hm` are `α₀ = flAlpha α` (the multiplier of `Gp` restricted to `Ω₁(Hm)`), `φ₀ = barField Gp Ψ φ`
(the background field of `Gp` extended by the datum), `δΨ = ψ'` (the fluctuation field `hatPsiF`) and
`f₁ = 0`.  If the raw data agree on `Y` and the hat variables on the unit blocks inside `Y`, the
fluctuation corrections `δα, δα'` of the two problems agree on `S_Y^F` and the corrections `dphi`
agree on `Y`.  The hypotheses `Hh, Hh'` (the bounds of Theorem I-4a (b)), `hfix, hsm, hfix', hsm'` (the
fixed points) and `hrow` (the rows of `Hm` at the sites of an interaction cube stay in its thickened
cube) are the premises of the landed theorems; no agreement hypothesis is made for the background
field, the multiplier or the fluctuation field. -/
theorem fluct_correction_rows_of_agree_on_component
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG : IsLevel Gp (k + 1)) (hHm : IsLevel Hm k) (cc : ℂ)
    (hconn : HatConn Gp)
    (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s s' : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁ → extS Gp s P = 1 ∧ extS Gp s' P = 1)
    (hs0 : ∀ P ∈ parCubes Gp X₁, P ∉ 𝒞 → extS Gp s P = 0 ∧ extS Gp s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y → extS Gp s P = extS Gp s' P)
    (hX₁ : IsCellUnion (L ^ (k + 1)) (X₁ : Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒞 : ∀ P ∈ 𝒞, P ∈ cubeIdx Gp)
    (hdata : ∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gp.Ω 1 → D.h z = D'.h z))
    (ψh ψh' : unitPts Gp × Fin N → ℂ)
    (hh : ∀ b' : unitPts Gp, UnitOut Gp Y b' → ∀ i, ψh (b', i) = ψh' (b', i))
    {φ φ₂ : Gp.Ω 1 × Fin N → ℂ} {α α₂ : Gp.Ω 1 → ℂ}
    (hI : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α)
    (hI₂ : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D' φ₂ α₂)
    (Hh : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α) (barField Gp D.Ψ φ)
      (hatPsiF Gp a₁ ν hG cc F₁ s (rawOf D) ψh) 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁)
    (Hh' : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α₂) (barField Gp D'.Ψ φ₂)
      (hatPsiF Gp a₁ ν hG cc F₁ s' (rawOf D') ψh') 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁)
    {δα δα' : Hm.Ω 1 → ℂ}
    (hfix : Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν s false (flAlpha Gp Hm α)
      (barField Gp D.Ψ φ) (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s (rawOf D) ψh) 0)
      δα)
    (hsmδ : Small Hm δα (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)))
    (hfix' : Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν s' false (flAlpha Gp Hm α₂)
      (barField Gp D'.Ψ φ₂)
      (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s' (rawOf D') ψh') 0) δα')
    (hsmδ' : Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))) :
    (∀ x : Hm.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈
        Dec2.SYF (coverOf Gp) Hm (compWeight L a₁) ν X₁ 𝒞 Y → δα x = δα' x) ∧
    (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i : Fin N,
      dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s) (flAlpha Gp Hm α)
        (barField Gp D.Ψ φ)
        (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s (rawOf D) ψh) 0) δα (y, i) =
      dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s') (flAlpha Gp Hm α₂)
        (barField Gp D'.Ψ φ₂)
        (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s' (rawOf D') ψh') 0)
        δα' (y, i)) := by
  classical
  have hsubΩ : ∀ x, x ∈ Hm.Ω 1 → x ∈ Gp.Ω 1 := fun x hx => hC.hPmp.mem_Ω1 hx
  have SL : Dec2.CoverLocal (coverOf Gp) Gp (compWeight L a₁) ν (Dec2.selfKc d L) (Cchi d L) :=
    Dec2.coverLocal_self hC.Sp
  have hconn' : Dec2.HatConn (coverOf Gp) Gp := hconn
  have h𝒞c : ∀ P ∈ 𝒞, P ∈ (coverOf Gp).cubeIdx := h𝒞
  obtain ⟨A, hIU, hAcube⟩ := incUnion_of_nnComp SL hconn' hsubΩ hrow h𝒞c hY
  obtain ⟨hαSY, hφ⟩ := bgField_of_agree_on_component hC hconn hG hs hs' hD hD' hY hs1 hs0 hag
    hdata φ α φ₂ α₂ hI hI₂
  have hψ := hatPsiF_rows hC hk hG cc hconn hMX hmar hα hsm hF₁ hs hs' hD hD' hY hs1 hs0 hag hX₁
    h𝒞 hdata ψh ψh' hh
  have hDA : Dec2.RowsFl.DataAgreeRows Hm N (Dec2.SYF (coverOf Gp) Hm (compWeight L a₁) ν X₁ 𝒞 Y)
      (Dec2.RowsFl.RowF Hm (compWeight L a₁) ν (Dec2.SYF (coverOf Gp) Hm (compWeight L a₁) ν X₁ 𝒞 Y))
      (flAlpha Gp Hm α) (flAlpha Gp Hm α₂) (barField Gp D.Ψ φ) (barField Gp D'.Ψ φ₂)
      (hatPsiF Gp a₁ ν hG cc F₁ s (rawOf D) ψh) (hatPsiF Gp a₁ ν hG cc F₁ s' (rawOf D') ψh')
      (0 : Hm.Ω 1 × Fin N → ℂ) 0 := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx i => rfl⟩
    · have := hαSY ⟨x, hsubΩ x x.2⟩ (SYF_subset_SY_level hG hC.Sp hconn hY hx)
      show flAlpha Gp Hm α x = flAlpha Gp Hm α₂ x
      rw [flAlpha_of_prec hC.hPmp, flAlpha_of_prec hC.hPmp]
      exact this
    · have hxΩ := hsubΩ x x.2
      -- the sites of `R(S_Y^F)` read the approximate field only on `Y`
      have hres : ∀ u : Hm.Ω 1, (u : CTorus d L N₁ m₁ (k + 1)) ∈ Dec2.SYF (coverOf Gp) Hm
          (compWeight L a₁) ν X₁ 𝒞 Y → ∀ w ∈ resSites Hm (u : CTorus d L N₁ m₁ (k + 1)),
          approxDep Gp w ⊆ Y := fun u hu w hw =>
        (fluct_footprint_subset hG hHm hC.Sp hconn hY hu).2 w hw
      have hap : approxDep Gp (x : CTorus d L N₁ m₁ (k + 1)) ⊆ Y := by
        unfold Dec2.RowsFl.RowF at hx
        obtain ⟨-, u, hu, hxu⟩ := Finset.mem_filter.1 hx
        rcases hxu with hxu | ⟨w, hw, hxw⟩
        · rw [hxu]; exact hres u hu _ (mem_resSites_self _)
        · rw [hxw]; exact hres u hu _ (mem_resSites_of_entry_ne_zero hw)
      funext i
      show barField Gp D.Ψ φ x i = barField Gp D'.Ψ φ₂ x i
      simp only [barField, hxΩ, ↓reduceDIte]
      exact hφ ⟨x, hxΩ⟩ hap i
    · exact hψ x (Dec2.SYF_subset_Y hx)
  exact Dec2.RowsFl.i4a_local_fpS_rows_level hC.hS2.fam hC.SM hC.hκ.le hC.hM2
    (fun P => (hs P).le) (fun P => (hs' P).le) Hh Hh' hC.B_le hC.δ₁_le hIU hs1 hs0
    (fun P hP hPA => hag P hP (fun x hx => (hAcube P hPA).2 x hx)) hDA hHm hfix hsmδ hfix' hsmδ'

end Fl

end Balaban.Localization

namespace Balaban.Fluctuation

open Balaban.Localization Balaban.Polymer

section Hat

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)

/-- **T4.  The `blocksOf` form of the hat hypothesis.**  Let `Y` be a union of complete cells of side
`cellSide L m₀ m₁ (k+1)` and `Y₁ ⊆ Y`.  If two block configurations agree on the cubes of
`blocksOf m₀ (k+1) univ Y` (the hypothesis of `DirectTerms.ag`), their hat variables agree at every
unit point whose `(k+1)`-block lies in `Y₁` (`UnitOut S.G' Y₁`).  The cell-union property of `Y` is
needed: the hat variable at a unit point reads the whole cube of side `cellSide` containing it. -/
theorem StepSetting.hatOf_agree_unitOut (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    {Y₁ : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsCellUnion (cellSide L m₀ m₁ (k + 1)) Y) (hY₁ : (Y₁ : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ Y)
    (ρ : ℝ) (hp : 0 < S.p₁) (Φ Φ' : ∀ b, (S.blockSplit m₀ hp).Ωb b)
    (h : ∀ b ∈ blocksOf m₀ (k + 1) Set.univ Y, Φ b = Φ' b)
    {b : S.U} (hb : UnitOut S.G' Y₁ b) (i : Fin N) :
    S.hatOf m₀ ρ hp Φ (b, i) = S.hatOf m₀ ρ hp Φ' (b, i) := by
  classical
  obtain ⟨hxl, hxb⟩ := Classical.choose_spec ((mem_unitPts S.G').1 b.2)
  set x := Classical.choose ((mem_unitPts S.G').1 b.2) with hxdef
  have hxΩ : x ∈ S.G'.Ω 1 := S.G'.layer_subset (by omega) le_rfl hxl
  have hxY₁ : x ∈ Y₁ := hb ⟨x, hxΩ⟩ (by simp only [hxb])
  have hxY : x ∈ Y := hY₁ (Finset.mem_coe.2 hxY₁)
  have hc : S.cellOf m₀ b = cubeOfSite m₀ x := rfl
  have hcube : S.cellOf m₀ b ∈ blocksOf m₀ (k + 1) Set.univ Y := by
    rw [hc]
    refine mem_blocksOf.2 fun z hz => ?_
    have hcb : cbase (cellSide L m₀ m₁ (k + 1)) z = cbase (cellSide L m₀ m₁ (k + 1)) x :=
      cbase_eq_of_mem_box (cellSide_dvd hN le_rfl) (aligned_cbase x) hz
    exact hY x hxY z ((sameCell_iff_cbase_eq (cellSide_pos m₀ m₁ (k + 1))).2 hcb)
  have := h _ hcube
  simp only [StepSetting.hatOf]
  rw [this]

end Hat

end Balaban.Fluctuation
