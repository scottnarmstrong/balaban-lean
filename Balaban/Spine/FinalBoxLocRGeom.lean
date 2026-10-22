/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7SmallFieldC
public import Balaban.LargeField.R.WindowCollarGeom
public import Balaban.LargeField.Operators.QuietIndep
public import Balaban.LargeField.History.TopBlockTransport
public import Balaban.Green.FinalBoxLocRootSum
public import Balaban.Green.FinalBoxLocBoxConn
public import Balaban.Fluctuation.ClassOldTermSiteSums
public import Balaban.Spine.InheritedBound

/-!
# The blocks and the cells of the polymers of the class on the box (A6-3, item (L4))

A term `ℛ^{(k)}_n(X)` of the class reads the block field `ψ_k` on the `k`-blocks of its polymer
`X ∈ 𝒟_k` (a connected union of cells of side `M L^k`, `M = L^{m₀+m₁}`, of the Def-6 torus).  With
the macro cells of side `M` (in `k`-blocks) of the cut family, every cell of `X` is one macro cell.

* `sfBlockOf`: the `k`-block of a site (`sfLiftKC ψ x = ψ (sfBlockOf x)`), `sfBlockOf_val`,
  `sfBlockOf_eq_of_jBlock` (constant on the `k`-blocks of the Def-6 torus), `sfBlockOf_eq_or_adj`
  (neighbours lie in equal or adjacent blocks), `sfBlockOf_surj`;
* `blocksOf X`, `isAnimal_blocksOf`: the blocks of a polymer form a connected set;
* `cbase_eq_of_sfBlockOf_eq`, `macZ_sfBlockOf_eq_iff`: two sites in one block lie in one cell, and
  two sites lie in one cell iff their blocks lie in one macro cell;
* `macCellCount_blocksOf_le`: `#cells(blocks of X) ≤ c₁ (1 + d_k(X))` (`G1_cellCount`);
* `cellBase_mem_of_mem_blocksOf`: a polymer containing a site of a block contains the base of the
  cell of the block; `card_cellBases_macBoxF_le`: the blocks of a box lie in at most `16^d` cells.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.LargeField Balaban.LargeField.Def7 Balaban.Localization
  Balaban.Green Balaban.SmallField Finset

section Geom

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

/-- The `k`-block of a site of the Def-6 torus (the block read by `sfLiftKC`). -/
def sfBlockOf (x : Localization.CTorus S.d S.L C.N₁ m₁ k) : BlockAt S n M K k :=
  jBlock S.d S.L (M * n K) K k (bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT x))

theorem sfLiftKC_apply (ψC : BlockAt S n M K k → Fin N → ℂ)
    (x : Localization.CTorus S.d S.L C.N₁ m₁ k) :
    C.sfLiftKC ψC x = ψC (sfBlockOf C x) := rfl

theorem sfBlockOf_val (x : Localization.CTorus S.d S.L C.N₁ m₁ k) (μ : Fin S.d) :
    (sfBlockOf C x μ).val = (x μ).val / S.L ^ k := by
  have h1 : (sfBlockOf C x μ).val =
      ((bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT x)) μ).val / S.L ^ k := by
    unfold sfBlockOf jBlock
    exact blockCoord_val (side_eq C.hkK) _
  rw [h1]
  unfold bgToFine sfToBg
  rw [torusCast_val, torusCast_val]

theorem jBlock_self_val {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] (x : Torus d (N₀ * L ^ k))
    (μ : Fin d) : (jBlock d L N₀ k k x μ).val = (x μ).val / L ^ k := by
  unfold jBlock
  exact blockCoord_val (side_eq le_rfl) _

/-- The block of a site is constant on the `k`-blocks of the Def-6 torus. -/
theorem sfBlockOf_eq_of_jBlock {x x' : Localization.CTorus S.d S.L C.N₁ m₁ k}
    (h : jBlock S.d S.L (C.N₁ * S.L ^ m₁) k k x = jBlock S.d S.L (C.N₁ * S.L ^ m₁) k k x') :
    sfBlockOf C x = sfBlockOf C x' := by
  funext μ
  apply ZMod.val_injective
  rw [sfBlockOf_val, sfBlockOf_val, ← jBlock_self_val, ← jBlock_self_val, h]

/-- Neighbouring sites lie in equal or adjacent blocks. -/
theorem sfBlockOf_eq_or_adj {x y : Localization.CTorus S.d S.L C.N₁ m₁ k} (h : Nbr x y) :
    sfBlockOf C x = sfBlockOf C y ∨
      (Polymer.blockGraph S.d (M * n K * S.L ^ (K - k))).Adj (sfBlockOf C x) (sfBlockOf C y) := by
  set c : Localization.CTorus S.d S.L C.N₁ m₁ k → Torus S.d (M * n K * S.L ^ K) :=
    fun z => bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT z) with hc
  have hcadd : ∀ z (μ : Fin S.d), c (z + Pi.single μ 1) = c z + Pi.single μ 1 := by
    intro z μ
    simp only [hc, bgToFine, sfToBg, torusCast_add_single]
  have hadj : Multiscale.Adj (N₀ := M * n K) (L := S.L) (k := K) (c x) (c y) := by
    obtain ⟨μ, hμ | hμ⟩ := h
    · exact ⟨μ, Or.inl (by rw [hμ, hcadd])⟩
    · exact ⟨μ, Or.inr (by rw [hμ, hcadd])⟩
  exact jBlock_eq_or_adjT (N₀ := M * n K) C.hkK hadj

theorem blockSide_eq : M * n K * S.L ^ (K - k) = C.N₁ * S.L ^ m₁ := by
  have h1 := histScale_eq C.geo.hM C.hnn (le_refl k) C.hkK
  have hT := C.hT
  rw [Nat.sub_self, pow_zero, mul_one] at h1
  have hpos : 0 < S.L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) k
  rw [← h1]
  exact (Nat.eq_of_mul_eq_mul_right hpos hT).symm

/-- Every block is the block of a site. -/
theorem sfBlockOf_surj (b : BlockAt S n M K k) :
    ∃ x : Localization.CTorus S.d S.L C.N₁ m₁ k, sfBlockOf C x = b := by
  have hside := blockSide_eq C
  refine ⟨fun μ => (((b μ).val * S.L ^ k : ℕ) : ZMod (C.N₁ * S.L ^ m₁ * S.L ^ k)), ?_⟩
  funext μ
  apply ZMod.val_injective
  rw [sfBlockOf_val]
  have hb := ZMod.val_lt (b μ)
  have hpos : 0 < S.L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) k
  have hlt : (b μ).val * S.L ^ k < C.N₁ * S.L ^ m₁ * S.L ^ k := by
    rw [← hside]; exact Nat.mul_lt_mul_of_pos_right hb hpos
  rw [ZMod.val_cast_of_lt hlt, Nat.mul_div_cancel _ hpos]

/-- A site whose block is `b`. -/
noncomputable def boxLocBlockSite (b : BlockAt S n M K k) : Localization.CTorus S.d S.L C.N₁ m₁ k :=
  (sfBlockOf_surj C b).choose

theorem sfBlockOf_boxLocBlockSite (b : BlockAt S n M K k) : sfBlockOf C (boxLocBlockSite C b) = b :=
  (sfBlockOf_surj C b).choose_spec

open Classical in
/-- The blocks of a set of sites. -/
noncomputable def blocksOf (X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) :
    Finset (BlockAt S n M K k) :=
  (Finset.univ.filter fun x => x ∈ X).image (sfBlockOf C)

theorem mem_blocksOf {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} {b : BlockAt S n M K k} :
    b ∈ blocksOf C X ↔ ∃ x ∈ X, sfBlockOf C x = b := by
  classical
  unfold blocksOf
  simp

/-- **The blocks of a polymer form a connected set.** -/
theorem isAnimal_blocksOf {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    (hX : Def6.IsPolyDom C.m₀ k X) :
    Polymer.IsAnimal (Polymer.blockGraph S.d (M * n K * S.L ^ (K - k))) (blocksOf C X) := by
  obtain ⟨⟨x₀, hx₀⟩, -, hconn⟩ := hX
  rw [Polymer.isAnimal_iff]
  refine ⟨⟨sfBlockOf C x₀, (mem_blocksOf C).2 ⟨x₀, hx₀, rfl⟩⟩, fun b hb b' hb' => ?_⟩
  obtain ⟨x, hx, rfl⟩ := (mem_blocksOf C).1 hb
  obtain ⟨x', hx', rfl⟩ := (mem_blocksOf C).1 hb'
  refine (Relation.ReflTransGen.lift' (sfBlockOf C) (fun a a' ha => ?_)) x x' (hconn x hx x' hx')
  obtain ⟨ha1, ha2, ha3⟩ := ha
  change Relation.ReflTransGen _ (sfBlockOf C a) (sfBlockOf C a')
  rcases sfBlockOf_eq_or_adj C ha3 with he | hadj
  · rw [he]
  · exact Relation.ReflTransGen.single ⟨(mem_blocksOf C).2 ⟨a, ha1, rfl⟩,
      (mem_blocksOf C).2 ⟨a', ha2, rfl⟩, hadj⟩

theorem val_div_cellSide (m₀ : ℕ) (x : Localization.CTorus S.d S.L C.N₁ m₁ k) (μ : Fin S.d) :
    (x μ).val / cellSide S.L m₀ m₁ k = (sfBlockOf C x μ).val / S.L ^ (m₀ + m₁) := by
  rw [sfBlockOf_val, Nat.div_div_eq_div_mul, Def6.cellSide_eq_mul]

theorem cbase_eq_iff {d ℓ a : ℕ} [NeZero ℓ] (ha : 0 < a) {x x' : Torus d ℓ} :
    cbase a x = cbase a x' ↔ ∀ μ, (x μ).val / a = (x' μ).val / a := by
  constructor
  · intro h μ
    have h1 := congrArg (fun y : Torus d ℓ => (y μ).val) h
    simp only [cbase] at h1
    have hl : ∀ v : ZMod ℓ, a * (v.val / a) < ℓ := fun v =>
      lt_of_le_of_lt (Nat.mul_div_le v.val a) (ZMod.val_lt v)
    rw [ZMod.val_cast_of_lt (hl _), ZMod.val_cast_of_lt (hl _)] at h1
    exact Nat.eq_of_mul_eq_mul_left ha h1
  · intro h
    funext μ
    simp only [cbase]
    rw [h μ]

/-- **Two sites in one block lie in one cell.** -/
theorem cbase_eq_of_sfBlockOf_eq (m₀ : ℕ) {x x' : Localization.CTorus S.d S.L C.N₁ m₁ k}
    (h : sfBlockOf C x = sfBlockOf C x') :
    cbase (cellSide S.L m₀ m₁ k) x = cbase (cellSide S.L m₀ m₁ k) x' := by
  rw [cbase_eq_iff (cellSide_pos m₀ m₁ k)]
  intro μ
  rw [val_div_cellSide, val_div_cellSide, h]

theorem macCell_val_of_dvd {m Mc : ℕ} [NeZero m] (hMc : 0 < Mc) (hdvd : Mc ∣ m) (v : ZMod m) :
    (macCell m Mc v : ℕ) = v.val / Mc := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hle : Mc ≤ m := Nat.le_of_dvd hm hdvd
  have hK : macK m Mc = m / Mc := macK_eq_div hMc hle
  have hlt : v.val / Mc < m / Mc := Nat.div_lt_div_of_lt_of_dvd hdvd (ZMod.val_lt v)
  show min (v.val / Mc) (macK m Mc - 1) = v.val / Mc
  rw [hK]
  omega

/-- **Two sites lie in one cell iff their blocks lie in one macro cell** (macro side
`M = L^{m₀+m₁}` dividing the side of the block torus). -/
theorem macZ_sfBlockOf_eq_iff (m₀ : ℕ) (hdvd : S.L ^ (m₀ + m₁) ∣ M * n K * S.L ^ (K - k))
    {x x' : Localization.CTorus S.d S.L C.N₁ m₁ k} :
    macZ (d := S.d) (m := M * n K * S.L ^ (K - k)) (S.L ^ (m₀ + m₁)) (sfBlockOf C x) =
        macZ (S.L ^ (m₀ + m₁)) (sfBlockOf C x') ↔
      cbase (cellSide S.L m₀ m₁ k) x = cbase (cellSide S.L m₀ m₁ k) x' := by
  have hMc : 0 < S.L ^ (m₀ + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _
  rw [cbase_eq_iff (cellSide_pos m₀ m₁ k)]
  constructor
  · intro h μ
    have h1 := congrArg (fun z => ((z μ : Fin _) : ℕ)) h
    simp only [macZ] at h1
    rw [macCell_val_of_dvd hMc hdvd, macCell_val_of_dvd hMc hdvd] at h1
    rw [val_div_cellSide, val_div_cellSide]
    exact h1
  · intro h
    funext μ
    apply Fin.ext
    simp only [macZ]
    rw [macCell_val_of_dvd hMc hdvd, macCell_val_of_dvd hMc hdvd, ← val_div_cellSide,
      ← val_div_cellSide, h μ]

/-- Two sites in one cell lie in one macro cell (no divisibility needed). -/
theorem macZ_sfBlockOf_eq_of_cbase (m₀ : ℕ) {x x' : Localization.CTorus S.d S.L C.N₁ m₁ k}
    (h : cbase (cellSide S.L m₀ m₁ k) x = cbase (cellSide S.L m₀ m₁ k) x') :
    macZ (d := S.d) (m := M * n K * S.L ^ (K - k)) (S.L ^ (m₀ + m₁)) (sfBlockOf C x) =
      macZ (S.L ^ (m₀ + m₁)) (sfBlockOf C x') := by
  rw [cbase_eq_iff (cellSide_pos m₀ m₁ k)] at h
  funext μ
  apply Fin.ext
  simp only [macZ, macCell]
  rw [← val_div_cellSide, ← val_div_cellSide, h μ]

theorem cbase_cbase {d ℓ a : ℕ} [NeZero ℓ] (ha : 0 < a) (x : Torus d ℓ) :
    cbase a (cbase a x) = cbase a x := by
  rw [cbase_eq_iff ha]
  intro μ
  simp only [cbase]
  have hl : a * ((x μ).val / a) < ℓ :=
    lt_of_le_of_lt (Nat.mul_div_le (x μ).val a) (ZMod.val_lt (x μ))
  rw [ZMod.val_cast_of_lt hl, Nat.mul_div_cancel_left _ ha]

/-- **A polymer containing a site of a block contains the base of the cell of the block.** -/
theorem cellBase_mem_of_mem_blocksOf {m₀ : ℕ} (hN : S.L ^ m₀ ∣ C.N₁)
    {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hX : Def6.IsPolyDom m₀ k X)
    {b : BlockAt S n M K k} (hb : b ∈ blocksOf C X) :
    cbase (cellSide S.L m₀ m₁ k) (boxLocBlockSite C b) ∈ X := by
  obtain ⟨x, hx, hxb⟩ := (mem_blocksOf C).1 hb
  have he : cbase (cellSide S.L m₀ m₁ k) x = cbase (cellSide S.L m₀ m₁ k) (boxLocBlockSite C b) :=
    cbase_eq_of_sfBlockOf_eq C m₀ (by rw [hxb, sfBlockOf_boxLocBlockSite])
  rw [← he]
  have hDj := Def6.isDj_of_isPolyDom hX
  exact Def6.cell_subset_of_mem (le_refl k) hN hDj hx (mem_box_self _ (cellSide_pos m₀ m₁ k))

open Classical in
/-- **The macro cells of the blocks of a polymer**: `#cells(blocks of X) ≤ c₁ (1 + d_k(X))`. -/
theorem macCellCount_blocksOf_le {m₀ : ℕ} (hN : S.L ^ m₀ ∣ C.N₁)
    {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hX : Def6.IsPolyDom m₀ k X) :
    (macCellCount S.d (M * n K * S.L ^ (K - k)) (S.L ^ (m₀ + m₁)) (blocksOf C X) : ℝ) ≤
      Fluctuation.c1 S.d S.L * (1 + Def6.sizeJ m₀ k X) := by
  have hDj := Def6.isDj_of_isPolyDom hX
  have hcs := cellSide_pos (L := S.L) m₀ m₁ k
  set Xf := Finset.univ.filter fun x : Localization.CTorus S.d S.L C.N₁ m₁ k => x ∈ X with hXf
  -- the macro cells of the blocks are images of the cell bases
  have h1 : macCellCount S.d (M * n K * S.L ^ (K - k)) (S.L ^ (m₀ + m₁)) (blocksOf C X) ≤
      (Xf.image (cbase (cellSide S.L m₀ m₁ k))).card := by
    unfold macCellCount blocksOf
    refine Finset.card_le_card_of_surjOn
      (fun c => macZ (d := S.d) (m := M * n K * S.L ^ (K - k)) (S.L ^ (m₀ + m₁))
        (sfBlockOf C c)) ?_
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨cbase (cellSide S.L m₀ m₁ k) x, Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx),
      macZ_sfBlockOf_eq_of_cbase C m₀ (cbase_cbase hcs x)⟩
  -- the cell bases are aligned and their cells lie in `X`
  have h2 : (Xf.image (cbase (cellSide S.L m₀ m₁ k))).card ≤
      cellCount (cellSide S.L m₀ m₁ k) X := by
    unfold cellCount
    refine Finset.card_le_card fun c hc => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    have hxX : x ∈ X := (Finset.mem_filter.1 hx).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, aligned_cbase x,
      Def6.cell_subset_of_mem (le_refl k) hN hDj hxX⟩
  have hG1 := Fluctuation.G1_cellCount (m₀ := m₀) (j := k) hN (le_refl k) (Ω := Set.univ) (X := X)
    ⟨hDj, fun z hz => absurd (Set.mem_univ z) hz⟩
  rw [Set.inter_univ, Fluctuation.dcovMod_of_subset (Set.subset_univ X)] at hG1
  have h12 : (macCellCount S.d (M * n K * S.L ^ (K - k)) (S.L ^ (m₀ + m₁)) (blocksOf C X) : ℝ) ≤
      cellCount (cellSide S.L m₀ m₁ k) X := by exact_mod_cast h1.trans h2
  unfold Def6.sizeJ
  linarith

/-- **The blocks of a box lie in at most `16^d` cells** (macro side `M = L^{m₀+m₁}` dividing the
side of the block torus). -/
theorem card_cellBases_macBoxF_le {m₀ : ℕ} (hdvd : S.L ^ (m₀ + m₁) ∣ M * n K * S.L ^ (K - k))
    (l : MacIdx S.d (M * n K * S.L ^ (K - k)) (S.L ^ (m₀ + m₁))) :
    ((macBoxF S.d (M * n K * S.L ^ (K - k)) (S.L ^ (m₀ + m₁)) l).image
      (fun b => cbase (cellSide S.L m₀ m₁ k) (boxLocBlockSite C b))).card ≤ 16 ^ S.d := by
  classical
  have hMc : 0 < S.L ^ (m₀ + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _
  have : Nonempty (L1Torus S.d (M * n K * S.L ^ (K - k))) := ⟨(0 : Torus S.d _)⟩
  refine le_trans ?_ (macCellCount_macBoxF_le (N₀ := M * n K * S.L ^ (K - k)) hMc l)
  unfold macCellCount
  refine Finset.card_le_card_of_surjOn
    (fun z => cbase (cellSide S.L m₀ m₁ k) (boxLocBlockSite C
      (Function.invFunOn (macZ (d := S.d) (m := M * n K * S.L ^ (K - k)) (S.L ^ (m₀ + m₁)))
        ((macBoxF S.d (M * n K * S.L ^ (K - k)) (S.L ^ (m₀ + m₁)) l :
          Finset (L1Torus S.d (M * n K * S.L ^ (K - k)))) :
            Set (L1Torus S.d (M * n K * S.L ^ (K - k)))) z))) ?_
  intro c hc
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hc
  refine ⟨macZ (S.L ^ (m₀ + m₁)) b, Finset.mem_coe.2 (Finset.mem_image_of_mem _ hb), ?_⟩
  have hmem : macZ (d := S.d) (m := M * n K * S.L ^ (K - k)) (S.L ^ (m₀ + m₁)) b ∈
      macZ (S.L ^ (m₀ + m₁)) ''
        (macBoxF S.d (M * n K * S.L ^ (K - k)) (S.L ^ (m₀ + m₁)) l : Set _) :=
    ⟨b, Finset.mem_coe.2 hb, rfl⟩
  have hinv := Function.invFunOn_eq hmem
  simp only
  refine (macZ_sfBlockOf_eq_iff C m₀ hdvd).1 ?_
  rw [sfBlockOf_boxLocBlockSite, sfBlockOf_boxLocBlockSite]
  exact hinv

end Geom

end Balaban.RootFSpine
