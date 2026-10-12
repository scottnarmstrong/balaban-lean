/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RowsHat
public import Balaban.Localization.FootprintFl
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
* `hatOf_agree_unitOut`: agreement of two block configurations on `blocksOf m₀ (k+1) univ Y` (the
  hypothesis of `HatLabelsDirect.DirectTerms.ag`) gives agreement of the hat variables on the unit
  blocks of `Y₁ ⊆ Y`, when `Y` is a union of complete cells of side `cellSide L m₀ m₁ (k+1)`.

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
  refine ⟨hα, fun y hy i => ?_⟩
  obtain ⟨z, hz, hyz⟩ := rowsCov_R_subset_resSites hy
  have happ : approxDep Gp (y : CTorus d L N₁ m₁ (k + 1)) ⊆ Y :=
    (footprint_subset_component hG X₁ 𝒞 Y).2 z hz _ hyz
  have hyY : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y := happ (mem_approxDep_self _)
  have hphi : approxField Gp (compWeight L a₁) ν D.Ψ D.h y =
      approxField Gp (compWeight L a₁) ν D'.Ψ D'.h y :=
    approxField_congr fun w hw => hdata w (happ hw)
  have := hcorr y hyY i
  rw [hphi] at this
  linear_combination this

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

end Balaban.Localization
