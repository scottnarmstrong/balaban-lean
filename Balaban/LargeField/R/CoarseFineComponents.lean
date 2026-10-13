/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.SizeModExtendPull

/-!
# Coarse cubes and fine cells: the conversion for the fine lift `d7Pull`

Pure finite geometry (package `RExtraSize` of `notes/phase1/VMOD-38.md` §4).  Let `a` be the side
`L^{k+m₀+m₁}` of a scale-`k` cell of the fine torus of a frame `F`, and `cubeIdx F k` the map that
sends a fine site to the scale-`k` cube containing it.  With the tower condition
`n_i = L n_{i+1}` (`i < K`) and `k ≤ K`:

* `cellsIn_d7Pull_mem`: the cells of the fine lift `d7Pull F k Y` of a set `Y` of cubes are the
  aligned fine sites whose cube lies in `Y`;
* `cubeIdx_image_cellsIn`, `card_cellsIn_d7Pull`: `cubeIdx F k` maps the cell bases of the lift of
  `Y` bijectively onto `Y`; for a finite set `Y` the lift has exactly `|Y|` cells;
* `cAdj_iff_nnAdj`: two cell bases are adjacent (`CAdj`, differing by `a` in one coordinate) exactly
  when their cubes are nearest neighbours (`NNAdj`); there is no wrap-around caveat, because
  `cubeIdx` is injective on aligned sites (for `n_k = 1` or `2` both sides degenerate in the same
  way);
* `cellComps_d7Pull`: every cell-component of the lift of `Y` is the lift of a nearest-neighbour
  connected set of cubes contained in `Y`.

Nothing about the operation `R` is used here.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Localization Def7

private theorem nnAdj_symm_aux {d N : ℕ} {x y : Torus d N} (h : NNAdj x y) : NNAdj y x := by
  obtain ⟨μ, h | h⟩ := h
  exacts [⟨μ, Or.inr h⟩, ⟨μ, Or.inl h⟩]

section Conv

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K m₀ m₁ : ℕ} [NeZero S.L]
  (F : FineSizeFrame S n M K m₀ m₁)

omit [∀ k, NeZero (n k)] [NeZero S.L] in
private theorem cellSide_eq (F : FineSizeFrame S n M K m₀ m₁) (k : ℕ) : cellSide S.L m₀ m₁ k = S.L ^ k * M := by
  unfold cellSide; rw [F.hM, ← pow_add]; congr 1; ring

private theorem cellSide_dvd_side (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K) :
    cellSide S.L m₀ m₁ k ∣ (F.N₁ * S.L ^ m₁) * S.L ^ K :=
  ⟨n k, fine_side_eq F hnn hkK⟩

/-- The aligned fine site at the corner of the cube `q`. -/
noncomputable def cubeBase (k : ℕ) (q : Torus S.d (n k)) : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K :=
  fun μ => ((cellSide S.L m₀ m₁ k * (q μ).val : ℕ) : ZMod ((F.N₁ * S.L ^ m₁) * S.L ^ K))

variable (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
include hnn hkK

private theorem cubeBase_val (q : Torus S.d (n k)) (μ : Fin S.d) :
    (cubeBase F k q μ).val = cellSide S.L m₀ m₁ k * (q μ).val := by
  unfold cubeBase
  apply ZMod.val_natCast_of_lt
  rw [fine_side_eq F hnn hkK]
  exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) (cellSide_pos m₀ m₁ k)

theorem aligned_cubeBase (q : Torus S.d (n k)) :
    Aligned (cellSide S.L m₀ m₁ k) (cubeBase F k q) := by
  intro μ
  rw [cubeBase_val F hnn hkK]
  exact Nat.mul_mod_right _ _

theorem cubeIdx_cubeBase (q : Torus S.d (n k)) : cubeIdx F k (cubeBase F k q) = q := by
  funext μ
  rw [cubeIdx_apply, ← cellSide_eq F, cubeBase_val F hnn hkK,
    Nat.mul_div_cancel_left _ (cellSide_pos m₀ m₁ k)]
  exact ZMod.natCast_zmod_val _

theorem cubeIdx_cbase (z : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K) :
    cubeIdx F k (cbase (cellSide S.L m₀ m₁ k) z) = cubeIdx F k z := by
  obtain ⟨w, hw, hzw⟩ := mem_box_cbase (cellSide_pos (L := S.L) m₀ m₁ k) z
  have := cubeIdx_cell F hnn hkK (aligned_cbase z) hw
  rw [← hzw] at this
  exact this.symm

/-- **The cells of the fine lift of `Y`**: an aligned fine site is the base of a cell contained in
`d7Pull F k Y` exactly when its cube lies in `Y`. -/
theorem cellsIn_d7Pull_mem (Y : Set (Torus S.d (n k))) (t : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K) :
    t ∈ Fluctuation.cellsIn m₀ k (d7Pull F k Y) ↔
      Aligned (cellSide S.L m₀ m₁ k) t ∧ cubeIdx F k t ∈ Y := by
  rw [Fluctuation.mem_cellsIn]
  refine and_congr_right fun ht => ⟨fun h => h (mem_box_self t (cellSide_pos m₀ m₁ k)), ?_⟩
  rintro hY x ⟨w, hw, rfl⟩
  rw [d7Pull_iff, cubeIdx_cell F hnn hkK ht hw]
  exact hY

/-- **`cubeIdx F k` maps the cell bases of the fine lift of `Y` onto `Y`.** -/
theorem cubeIdx_image_cellsIn (Y : Set (Torus S.d (n k))) :
    cubeIdx F k '' (Fluctuation.cellsIn m₀ k (d7Pull F k Y) : Set (Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K)) = Y := by
  ext q
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ((cellsIn_d7Pull_mem F hnn hkK Y t).1 ht).2
  · intro hq
    refine ⟨cubeBase F k q, ?_, cubeIdx_cubeBase F hnn hkK q⟩
    rw [Finset.mem_coe, cellsIn_d7Pull_mem F hnn hkK]
    exact ⟨aligned_cubeBase F hnn hkK q, by rwa [cubeIdx_cubeBase F hnn hkK]⟩

/-- **The fine lift of a finite set `Y` of cubes has exactly `|Y|` cells.** -/
theorem card_cellsIn_d7Pull (Y : Finset (Torus S.d (n k))) :
    (Fluctuation.cellsIn m₀ k (d7Pull F k (Y : Set (Torus S.d (n k))))).card = Y.card := by
  refine Finset.card_bij (fun t _ => cubeIdx F k t) (fun t ht => ?_) (fun t ht t' ht' h => ?_)
    (fun q hq => ?_)
  · exact Finset.mem_coe.1 (((cellsIn_d7Pull_mem F hnn hkK _ t).1 ht).2)
  · exact cubeIdx_injOn F hnn hkK ((cellsIn_d7Pull_mem F hnn hkK _ t).1 ht).1
      ((cellsIn_d7Pull_mem F hnn hkK _ t').1 ht').1 h
  · refine ⟨cubeBase F k q, ?_, cubeIdx_cubeBase F hnn hkK q⟩
    rw [cellsIn_d7Pull_mem F hnn hkK]
    exact ⟨aligned_cubeBase F hnn hkK q, by simpa [cubeIdx_cubeBase F hnn hkK] using hq⟩

private theorem aligned_add_cell (μ : Fin S.d) {b : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K}
    (hb : Aligned (cellSide S.L m₀ m₁ k) b) :
    Aligned (cellSide S.L m₀ m₁ k) (b + natT (Pi.single μ (cellSide S.L m₀ m₁ k))) := by
  refine aligned_add_natT (cellSide_dvd_side F hnn hkK) hb fun ν => ?_
  by_cases h : ν = μ
  · subst h; simp
  · simp [h]

private theorem cubeIdx_add_cell (μ : Fin S.d) {b : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K}
    (hb : Aligned (cellSide S.L m₀ m₁ k) b) :
    cubeIdx F k (b + natT (Pi.single μ (cellSide S.L m₀ m₁ k))) =
      cubeIdx F k b + Pi.single μ 1 := by
  have hside := fine_side_eq F hnn hkK
  funext ν
  simp only [Pi.add_apply, cubeIdx_apply, natT_apply]
  rw [← cellSide_eq F]
  rw [blockIdx_add (nk := n k) (by rw [hside]) (b ν) _ (hb ν)]
  by_cases h : ν = μ
  · subst h
    simp [Nat.div_self (cellSide_pos m₀ m₁ k)]
  · simp [h]

/-- **Fine cell adjacency is coarse nearest-neighbour adjacency.**  For aligned fine sites `b`,
`b'` (cell bases), `b'` and `b` differ by one cell side in one coordinate (`CAdj`) exactly when
their cubes are nearest neighbours of the scale-`k` torus (`NNAdj`). -/
theorem cAdj_iff_nnAdj {b b' : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K}
    (hb : Aligned (cellSide S.L m₀ m₁ k) b) (hb' : Aligned (cellSide S.L m₀ m₁ k) b') :
    CAdj (cellSide S.L m₀ m₁ k) b b' ↔ NNAdj (cubeIdx F k b) (cubeIdx F k b') := by
  constructor
  · rintro ⟨μ, h | h⟩
    · exact ⟨μ, Or.inl (by rw [h, cubeIdx_add_cell F hnn hkK μ hb])⟩
    · exact ⟨μ, Or.inr (by rw [h, cubeIdx_add_cell F hnn hkK μ hb'])⟩
  · rintro ⟨μ, h | h⟩
    · refine ⟨μ, Or.inl (cubeIdx_injOn F hnn hkK hb' (aligned_add_cell F hnn hkK μ hb) ?_)⟩
      rw [h, cubeIdx_add_cell F hnn hkK μ hb]
    · refine ⟨μ, Or.inr (cubeIdx_injOn F hnn hkK hb (aligned_add_cell F hnn hkK μ hb') ?_)⟩
      rw [h, cubeIdx_add_cell F hnn hkK μ hb']

/-- **The cell-components of a fine lift are lifts of nearest-neighbour connected sets.**  Every
cell-component `Q` of `d7Pull F k Y` is `d7Pull F k Q₀` for a set `Q₀ ⊆ Y` of cubes that is
connected for the nearest-neighbour adjacency inside `Q₀`. -/
theorem cellComps_d7Pull (Y : Set (Torus S.d (n k)))
    {Q : Set (Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K)} (hQ : Q ∈ Fluctuation.cellComps m₀ k (d7Pull F k Y)) :
    ∃ Q₀ : Set (Torus S.d (n k)), Q₀ ⊆ Y ∧
      (∀ x ∈ Q₀, ∀ y ∈ Q₀,
        Relation.ReflTransGen (fun u v => u ∈ Q₀ ∧ v ∈ Q₀ ∧ NNAdj u v) x y) ∧
      Q = d7Pull F k Q₀ := by
  obtain ⟨b, hb, rfl⟩ := hQ
  set Q₀ : Set (Torus S.d (n k)) :=
    cubeIdx F k '' (Fluctuation.cellCompBases m₀ k (d7Pull F k Y) b :
      Set (Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K)) with hQ₀
  have hbases : ∀ t ∈ Fluctuation.cellCompBases m₀ k (d7Pull F k Y) b,
      t ∈ Fluctuation.cellsIn m₀ k (d7Pull F k Y) ∧
        Fluctuation.CellReach m₀ k (d7Pull F k Y) b t := fun t ht =>
    Fluctuation.mem_cellCompBases.1 ht
  refine ⟨Q₀, ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact ((cellsIn_d7Pull_mem F hnn hkK Y t).1 (hbases t ht).1).2
  · -- every cube of `Q₀` is joined to the cube of `b`
    have key : ∀ t, Fluctuation.CellReach m₀ k (d7Pull F k Y) b t →
        Relation.ReflTransGen (fun u v => u ∈ Q₀ ∧ v ∈ Q₀ ∧ NNAdj u v)
          (cubeIdx F k b) (cubeIdx F k t) := by
      intro t ht
      induction ht with
      | refl => exact Relation.ReflTransGen.refl
      | @tail m t' hab hbc ih =>
        obtain ⟨hadj, hm, ht'⟩ := hbc
        have hmb : m ∈ Fluctuation.cellCompBases m₀ k (d7Pull F k Y) b :=
          Fluctuation.mem_cellCompBases.2 ⟨hm, hab⟩
        have ht'b : t' ∈ Fluctuation.cellCompBases m₀ k (d7Pull F k Y) b :=
          Fluctuation.mem_cellCompBases.2 ⟨ht', hab.tail ⟨hadj, hm, ht'⟩⟩
        refine ih.tail ⟨⟨m, hmb, rfl⟩, ⟨t', ht'b, rfl⟩, ?_⟩
        exact (cAdj_iff_nnAdj F hnn hkK ((cellsIn_d7Pull_mem F hnn hkK Y m).1 hm).1
          ((cellsIn_d7Pull_mem F hnn hkK Y t').1 ht').1).1 hadj
    have hsymm : ∀ u v : Torus S.d (n k), (u ∈ Q₀ ∧ v ∈ Q₀ ∧ NNAdj u v) → (v ∈ Q₀ ∧ u ∈ Q₀ ∧ NNAdj v u) :=
      fun u v h => ⟨h.2.1, h.1, nnAdj_symm_aux h.2.2⟩
    rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩
    exact (rtg_symm hsymm (key t (hbases t ht).2)).trans
      (key t' (hbases t' ht').2)
  · ext x
    simp only [Fluctuation.cellComp, Set.mem_iUnion, Finset.mem_coe, d7Pull_iff, hQ₀,
      Set.mem_image]
    constructor
    · rintro ⟨t, ht, w, hw, rfl⟩
      exact ⟨t, ht, (cubeIdx_cell F hnn hkK ((cellsIn_d7Pull_mem F hnn hkK Y t).1
        (hbases t ht).1).1 hw).symm⟩
    · rintro ⟨t, ht, hx⟩
      have hal := ((cellsIn_d7Pull_mem F hnn hkK Y t).1 (hbases t ht).1).1
      have : t = cbase (cellSide S.L m₀ m₁ k) x :=
        cubeIdx_injOn F hnn hkK hal (aligned_cbase x) (by rw [cubeIdx_cbase F hnn hkK, hx])
      exact ⟨t, ht, by rw [this]; exact mem_box_cbase (cellSide_pos m₀ m₁ k) x⟩

end Conv

end Balaban.LargeField
