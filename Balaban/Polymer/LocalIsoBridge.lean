/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoOld
public import Balaban.Inhabited.E1MarkParamCommonG
import Mathlib.Tactic.Linarith

/-!
# Local generating sets on two tori: the bridge marks

The bridge mark `e1MarkGParamGBgOn` of a root recomputed on a local pair `(Gl, Gd)` with the
canonical transport is the rooted output `markedOutDec` of the corrected marks `decMarkCorrBg` of
the blocks, each a Taylor remainder in the first mark of the `t`-derivative of the term `evDecBg` of
the block energy.  For local pairs carried onto each other by the box map:

* `OmegaIso.maskPre_map`: the preimage masks of corresponding masks of the level sets correspond;
* `corrMark_congr`: the corrected mark of a function of the two marks reads the function only on the
  radius set;
* `OmegaIso.blockTermEq_twoTorus`: the term of the block energy of a block `b` at a label `Y` and of
  the block `bc b` at `bm '' Y` (steps `hatStepKG`, marks of the radius set);
* `OmegaIso.decMarkCorrBg_twoTorus`: the corrected marks of corresponding blocks;
* `markedOutSum_twoTorus`: the sums over the marked pairs of corresponding labels (the reindexing of
  `markedOutDec_twoTorus`, for any summands agreeing at corresponding pairs);
* `OmegaIso.markedOutBg_twoTorus`, `OmegaIso.e1MarkGParamGBgOn_twoTorus`: the rooted outputs and the
  bridge marks recomputed on corresponding local pairs (steps `hatStepKG`);
* `OmegaIso.maskPre_blockU_map`: the preimage masks of the root blocks.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Analysis Matrix Balaban.Inhabited

/-- **The corrected mark reads the function only on the radius set.**  If `E'` and `E` agree at
the marks `(v, t)` with `(‖v‖ + ‖t‖) m_R < δ₁`, the corrected marks
`∂_t E(u, ·)|₀ − ∂_t E(0, ·)|₀ − u ∂_v ∂_t E(v, ·)|₀` agree for `‖u‖ m_R < δ₁`. -/
theorem corrMark_congr {E E' : ℂ → ℂ → ℂ} {mR δ₁ : ℝ}
    (h : ∀ v t : ℂ, (‖v‖ + ‖t‖) * mR < δ₁ → E' v t = E v t) {um : ℂ}
    (hum : ‖um‖ * mR < δ₁) (hδ : 0 < δ₁) :
    deriv (E' um) 0 - deriv (E' 0) 0 - um * deriv (fun v => deriv (E' v) 0) 0 =
      deriv (E um) 0 - deriv (E 0) 0 - um * deriv (fun v => deriv (E v) 0) 0 := by
  have hd : ∀ v : ℂ, ‖v‖ * mR < δ₁ → deriv (E' v) 0 = deriv (E v) 0 := by
    intro v hv
    refine Filter.EventuallyEq.deriv_eq ?_
    have hopen : IsOpen {t : ℂ | (‖v‖ + ‖t‖) * mR < δ₁} :=
      isOpen_lt (by fun_prop) continuous_const
    have h0 : (0 : ℂ) ∈ {t : ℂ | (‖v‖ + ‖t‖) * mR < δ₁} := by
      show (‖v‖ + ‖(0 : ℂ)‖) * mR < δ₁
      rw [norm_zero, add_zero]
      exact hv
    filter_upwards [hopen.mem_nhds h0] with t ht
    exact h v t ht
  have h0 : ‖(0 : ℂ)‖ * mR < δ₁ := by rw [norm_zero, zero_mul]; exact hδ
  have hD : deriv (fun v => deriv (E' v) 0) 0 = deriv (fun v => deriv (E v) 0) 0 := by
    refine Filter.EventuallyEq.deriv_eq ?_
    have hopen : IsOpen {v : ℂ | ‖v‖ * mR < δ₁} := isOpen_lt (by fun_prop) continuous_const
    filter_upwards [hopen.mem_nhds h0] with v hv
    exact hd v hv
  rw [hd um hum, hd 0 h0, hD]

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱb ϱb' ϱm ϱm' : ℝ}

set_option hygiene false in
local notation "bk" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)
set_option hygiene false in
local notation "SA" => Balaban.Inhabited.LevelStep.hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k
  m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => Balaban.Inhabited.LevelStep.hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2
  k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "bk'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc'" => boxMap (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "domA" => fun b : TA => polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b))
  m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k b))
set_option hygiene false in
local notation "domB" => fun b : TB => polyDom (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b))
  m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k b))

/-- **The sum over the marked pairs of a label, on two tori.**  For a root `z` of the box and a
label `Y'` of the box of radius `R`, the marked pairs `(b, Y)` of `z` with bridge `Y'` (domains of
the local covers of the blocks) correspond to the marked pairs of `bc z` with bridge `bm '' Y'` by
`(b, Y) ↦ (bc b, bm '' Y)` (`markedPair_boxMap_iff`; the inverse through the box map back); hence the
sums of functions `g'`, `g` of the pairs agree when they agree at corresponding pairs (`hg`, asked
for the pairs of the first torus, whose domain and local cover lie in the box). -/
theorem markedOutSum_twoTorus {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (z : TA) {rc R : ℕ}
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z) (hrc : L ^ (k + 1) * rc ≤ R)
    (hroot : ∀ x ∈ rootSet m₀ z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y' : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY'R : ∀ y ∈ Y', InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * aK) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * aK) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnH : 2 * (R + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH' : 2 * (R + 2 * (L * aK)) + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    (g : TA → Set (CTorus d L N₁ m₁ (k + 1)) → ℂ) (g' : TB → Set (CTorus d L N₁' m₁ (k + 1)) → ℂ)
    (hg : ∀ q ∈ (markedIdx (fun _ : TA => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (domA)
        z).filter (fun q => bridge m₀ z q.2 = Y'),
      (∀ y ∈ q.2, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y) →
      (∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k q.1),
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) → g' (bc q.1) (bk '' q.2) = g q.1 q.2) :
    ∑ q ∈ (markedIdx (fun _ : TB => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (domB)
        (bc z)).filter (fun q => bridge m₀ (bc z) q.2 = bk '' Y'), g' q.1 q.2 =
      ∑ q ∈ (markedIdx (fun _ : TA => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (domA)
        z).filter (fun q => bridge m₀ z q.2 = Y'), g q.1 q.2 := by
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hKm : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_add_right _ _)
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have hcs2 : (L - 1) * aK ≤ L * aK := Nat.mul_le_mul_right _ (Nat.sub_le L 1)
  have hcm := coarse_margin (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (r := R) (by omega)
  -- the pairs of the first torus lie in the box
  have hpairA : ∀ q ∈ (markedIdx (fun _ : TA => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (domA) z).filter (fun q => bridge m₀ z q.2 = Y'),
      (∀ y ∈ q.2, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y) ∧
      (∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k q.1),
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) := by
    intro q hq
    obtain ⟨hq1, hbr⟩ := Finset.mem_filter.1 hq
    have hYd := ((mem_markedIdx (b := q.1) (Y := q.2)).1 hq1).1
    have hYR : ∀ y ∈ q.2, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y :=
      fun y hy => hY'R y (hbr ▸ subset_bridge m₀ z q.2 hy)
    exact ⟨hYR, fun x hx => hYR x (nbhd_subset_of_mem_polyDom hN _ hYd hx)⟩
  symm
  refine Finset.sum_nbij (fun q => (bc q.1, bk '' q.2)) (fun q hq => ?_)
    (fun q1 hq1 q2 hq2 h => ?_) (fun q' hq' => ?_) (fun q hq => ?_)
  · obtain ⟨hYR, hbR⟩ := hpairA q hq
    obtain ⟨hq1, hbr⟩ := Finset.mem_filter.1 hq
    exact Finset.mem_filter.2 ((markedPair_boxMap_iff (ϱ := ϱ) hN hN' hn hn' hnF hnF' hnH hnH' z hz
      hrc hroot hY'R q.1 q.2 hYR hbR).2 ⟨hq1, hbr⟩)
  · obtain ⟨hYR1, hbR1⟩ := hpairA q1 hq1
    obtain ⟨hYR2, hbR2⟩ := hpairA q2 hq2
    have hx1 : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (LocalCover.blockSite k q1.1) :=
      hbR1 _ (by rw [← LocalCover.coe_nbhdF]; exact LocalCover.mem_nbhdF_self m₀ _)
    have hx2 : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (LocalCover.blockSite k q2.1) :=
      hbR2 _ (by rw [← LocalCover.coe_nbhdF]; exact LocalCover.mem_nbhdF_self m₀ _)
    have hb1 := blockSite_boxMap (N₁' := N₁') le_rfl q1.1 (inBox_coarse_of_blockSite q1.1 hx1)
      (Nat.mul_div_le R _) (by omega)
    have hb2 := blockSite_boxMap (N₁' := N₁') le_rfl q2.1 (inBox_coarse_of_blockSite q2.1 hx2)
      (Nat.mul_div_le R _) (by omega)
    have h1 : bc q1.1 = bc q2.1 := congrArg Prod.fst h
    have h2 : bk '' q1.2 = bk '' q2.2 := congrArg Prod.snd h
    have hx : LocalCover.blockSite k q1.1 = LocalCover.blockSite k q2.1 := by
      have e : bk (LocalCover.blockSite k q1.1) = bk (LocalCover.blockSite k q2.1) := by
        rw [← hb1, ← hb2, h1]
      exact boxMap_inj (hm' := (by omega : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))) hx1 hx2 e
    refine Prod.ext ?_ (image_boxMap_inj (by omega) hYR1 hYR2 h2)
    rw [← LocalCover.jBlock_blockSite le_rfl q1.1, ← LocalCover.jBlock_blockSite le_rfl q2.1, hx]
  · obtain ⟨hq1, hbr⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hq')
    have hYd := ((mem_markedIdx (b := q'.1) (Y := q'.2)).1 hq1).1
    have hY'' : ∀ y ∈ q'.2, InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) y := by
      intro y hy
      have hy' := hbr ▸ subset_bridge m₀ (bc z) q'.2 hy
      obtain ⟨w, hw, rfl⟩ := hy'
      exact inBox_boxMap (by omega) (hY'R w hw)
    have hnb' : ∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k q'.1),
        InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) x :=
      fun x hx => hY'' x (nbhd_subset_of_mem_polyDom hN' _ hYd hx)
    have hx' : InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) (LocalCover.blockSite k q'.1) :=
      hnb' _ (by rw [← LocalCover.coe_nbhdF]; exact LocalCover.mem_nbhdF_self m₀ _)
    have hbc' := inBox_coarse_of_blockSite q'.1 hx'
    have hbcb : bc (bc' q'.1) = q'.1 := boxMap_boxMap hcm hbc'
    have hbA : InBox d (R / L ^ (k + 1)) (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) (bc' q'.1) :=
      inBox_boxMap hcm hbc'
    have hbs : LocalCover.blockSite k (bc (bc' q'.1)) = bk (LocalCover.blockSite k (bc' q'.1)) :=
      blockSite_boxMap le_rfl _ hbA (Nat.mul_div_le R _) (by omega)
    rw [hbcb] at hbs
    have hxA : LocalCover.blockSite k (bc' q'.1) = bk' (LocalCover.blockSite k q'.1) := by
      rw [hbs, boxMap_boxMap (by omega)
        (blockSite_inBox (N₁ := N₁) (by omega) _ hbA (Nat.mul_div_le R _))]
    have hnbA : ∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k (bc' q'.1)),
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
      rw [hxA, ← nbhd_image (N₁ := N₁') (N₁' := N₁) hN' hN (r := R) (by omega) (by omega) _ hnb'
        (fun y hy => hnb' y (cell_subset_nbhd _ hy))]
      rintro _ ⟨y, hy, rfl⟩
      exact inBox_boxMap (by omega) (hnb' y hy)
    have hYA : ∀ y ∈ bk' '' q'.2, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y := by
      rintro _ ⟨y, hy, rfl⟩
      exact inBox_boxMap (by omega) (hY'' y hy)
    have himg : bk '' (bk' '' q'.2) = q'.2 := image_image_boxMap (by omega) hY''
    have hmem := (markedPair_boxMap_iff (ϱ := ϱ) hN hN' hn hn' hnF hnF' hnH hnH' z hz hrc hroot hY'R
      (bc' q'.1) (bk' '' q'.2) hYA hnbA).1
    rw [hbcb, himg] at hmem
    refine ⟨(bc' q'.1, bk' '' q'.2), Finset.mem_coe.2 (Finset.mem_filter.2 (hmem ⟨hq1, hbr⟩)), ?_⟩
    show (bc (bc' q'.1), bk '' (bk' '' q'.2)) = q'
    rw [hbcb, himg]
  · obtain ⟨hYR, hbR⟩ := hpairA q hq
    exact (hg q hq hYR hbR).symm

namespace OmegaIso

variable {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Gb' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱb'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'} {ρ : ℕ}

/-- **The preimage masks of corresponding masks.**  If the unit points of the level sets at the
sites of the box of radius `ρ` lie in `Zm'` and `Zm` together, the preimage mask of `Zm'` on `Gb'`
is the image of that of `Zm` on `Gb` under the bijection of the unit points. -/
theorem maskPre_map (hI : OmegaIso Gb Gb' ρ) (hGA : IsLevel (GA) (k + 1))
    (hGB : IsLevel (GB) (k + 1)) {Zm : Finset (unitPts (GA))} {Zm' : Finset (unitPts (GB))}
    (hZm : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      (unitPt hGB (bk x) ∈ Zm' ↔ unitPt hGA x ∈ Zm)) :
    maskPre hGB Gb' Zm' = (maskPre hGA Gb Zm).map hI.unitEquiv.toEmbedding := by
  ext q'
  obtain ⟨b, rfl⟩ := hI.unitEquiv.surjective q'
  rw [show hI.unitEquiv b = hI.unitEquiv.toEmbedding b from rfl, Finset.mem_map' hI.unitEquiv.toEmbedding]
  obtain ⟨x, hx⟩ := exists_site b
  have h1 : (⟨((hI.unitEquiv.toEmbedding b : unitPts Gb') : UnitTorus d L N₁' m₁ k),
      mem_unitPts_of_isLevel hGB _⟩ : unitPts (GB)) = unitPt hGB (bk (x : CTorus d L N₁ m₁ (k + 1))) :=
    Subtype.ext (by
      show ((hI.unitEquiv b : unitPts Gb') : UnitTorus d L N₁' m₁ k) = _
      rw [hI.unitEquiv_site hx, coe_e]; rfl)
  have h2 : (⟨((b : unitPts Gb) : UnitTorus d L N₁ m₁ k), mem_unitPts_of_isLevel hGA _⟩ :
      unitPts (GA)) = unitPt hGA (x : CTorus d L N₁ m₁ (k + 1)) :=
    Subtype.ext (by rw [← hx]; rfl)
  simp only [maskPre, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h1, h2]
  exact hZm x (hI.boxG x x.2)

/-- **The term of the block energy of a block on two tori** (local pairs, steps `hatStepKG`).  For a
block `b` whose local cover lies in the box of radius `R`, a label `Y` of the box, parameters of the
two local charts whose raw data correspond on the box, the hat variables of block variables
corresponding at the unit points of the box, the masks `Zm`, `Zm'` and marks of the radius set, the
terms `evDecBg` of the block energy of `bc b` at `bm '' Y` and of `b` at `Y` agree. -/
theorem blockTermEq_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {c BG κ eps Kc' Cx' c₂ BG₂ δ₁ Kc Cx : ℝ}
    (hC : FlCore N Gb Hm (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hC' : FlCore N Gb' Hm' (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) (hHm' : Hm'.Ω (k + 1) = ∅)
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (Sb' : Dec2.CoverBase (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX' : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {F₁ : TA → DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₁' : TB → DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    (hF₁an : ∀ z, AnalyticOnNhd ℂ (F₁ z) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ z (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₁ z (s, rawOf D) = (φ, α))
    (hF₁' : ∀ z' (s : Dec2.DecParams (coverOf Gb')) (D : BgData Gb' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb' (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb'.Ω 1 × Fin N → ℂ)
        (α : Gb'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₁' z' (s, rawOf D) = (φ, α))
    {Sol : TA → Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : TB → Dec2.DecParams (coverOf Gb') × Edat Hm' N →
      (Hm'.Ω 1 × Fin N → ℂ) × (Hm'.Ω 1 → ℂ)}
    (hSolan : ∀ z, AnalyticOnNhd ℂ (Sol z) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ z (p : Dec2.DecParams (coverOf Gb) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol z p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2))
    (hSol' : ∀ z' (p : Dec2.DecParams (coverOf Gb') × Edat Hm' N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm' N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' z' p).1 = dphi Hm' (Dec2.decG (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol' z' p).2 ∧
        Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol' z' p).2 ∧
        Small Hm' (Sol' z' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm' (Sol' z' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm' (Sol' z' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm'.Ω 1 → ℂ, Small Hm' δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' →
            δα' = (Sol' z' p).2))
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁') {R : ℕ} (hρR : ρ ≤ R)
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L 1 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L 1 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnE : 2 * (R + L ^ k + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnE' : 2 * (R + L ^ k + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 <
      (N₁' * L ^ m₁) * L ^ (k + 1))
    (Zm : Finset (unitPts Gb)) {Zm' : Finset (unitPts Gb')}
    (hZm : Zm' = Zm.map hI.unitEquiv.toEmbedding)
    {θ : physParamBg N Gb} {θ' : physParamBg N Gb'}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb' (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hraw₁ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).1)
    (hraw₂ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).2)
    {ρh : ℝ} (hρh : 0 < ρh) (hρc : ρh ≤ cψ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Φ : ∀ b, ((SA).blockSplit 1 hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit 1 hp').Ωb b)
    (hΦ : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ' ((SB).cellOf 1 (unitPt hGB (bk x))) ⟨unitPt hGB (bk x), rfl⟩ =
        Φ ((SA).cellOf 1 (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩)
    (b : TA) (hX : ∀ x ∈ LocalCover.nbhd 1 (LocalCover.blockSite k b),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    {um t : ℂ} (hW : (‖um‖ + ‖t‖) *
      markedRad d L N k (SA).a₁ κ cψ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁) :
    evDecBg (SB).G' (LocalCover.nbhdF 1 (LocalCover.blockSite k (bc b))) 1 k
        (LocalCover.fam 1 (LocalCover.blockSite k (bc b))) Gb' (SB).a₁ (SB).ν
        (BgTransport.canon (SB).G' Gb' N) (((SB).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁' (bc b))
        (Sol' (bc b)) (blockEnergyFun Gb' Hm' (compWeight L (SB).a₁) (SB).ν k (bc b)) Zm' um t
        (bk '' Y) ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N),
          (BgTransport.canon (SB).G' Gb' N).res ((SB).hatOf 1 ρh hp' Φ')) =
      evDecBg (SA).G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
        (LocalCover.fam 1 (LocalCover.blockSite k b)) Gb (SA).a₁ (SA).ν
        (BgTransport.canon (SA).G' Gb N) (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ b) (Sol b)
        (blockEnergyFun Gb Hm (compWeight L (SA).a₁) (SA).ν k b) Zm um t Y
        ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N),
          (BgTransport.canon (SA).G' Gb N).res ((SA).hatOf 1 ρh hp Φ)) := by
  obtain ⟨D, hD, hDe⟩ := hθ
  obtain ⟨D', hD', hDe'⟩ := hθ'
  have hΨc : FieldCorr (ρ + 1) D.Ψ D'.Ψ := by
    intro z hz
    have := hraw₁ z hz
    rw [hDe, hDe'] at this
    exact this
  have hhc : FieldCorr (ρ + 1) D.h D'.h := by
    intro z hz
    have := hraw₂ z hz
    rw [hDe, hDe'] at this
    exact this
  have hhat := hatOf_boxMap hGA hGB hN2 hk νS β p₁ δ 1 ρh hp hp' Φ Φ' hΦ
  have hb : ∀ p, ‖(SA).hatOf 1 ρh hp Φ p‖ ≤ cψ := fun p => ((SA).hatOf_mem 1 hρh hp Φ p).trans hρc
  have hb' : ∀ p, ‖(SB).hatOf 1 ρh hp' Φ' p‖ ≤ cψ :=
    fun p => ((SB).hatOf_mem 1 hρh hp' Φ' p).trans hρc
  have hcs : (L - 1) * cellSide L 1 m₁ (k + 1) ≤ L * cellSide L 1 m₁ (k + 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le L 1)
  have hc1 : 1 ≤ 5 * (L * cellSide L 1 m₁ (k + 1)) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by norm_num)
      (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos 1 m₁ (k + 1))))
  have hs : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hzR : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (LocalCover.blockSite k b) :=
    hX _ (cell_subset_nbhd _ (LocalCover.mem_cell 1 _))
  have hz := inBox_coarse_of_blockSite b hzR
  have hbs : LocalCover.blockSite k (bc b) = bk (LocalCover.blockSite k b) :=
    blockSite_boxMap le_rfl b hz (Nat.mul_div_le R _) hs
  obtain ⟨hcov, hX₁, hcov', hX₁'⟩ := covSetup_localCover_image (ϱ := ϱ) hN hN' (j := k) le_rfl
    (R := R) (by omega) (LocalCover.blockSite k b) hX
  have hF := nbhdF_image_finset hN hN' (R := R) (by omega) (LocalCover.blockSite k b) hX
  have hXR : ∀ x ∈ LocalCover.nbhdF 1 (LocalCover.blockSite k b),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := fun x hx =>
    hX x (by rw [← LocalCover.coe_nbhdF]; exact hx)
  have hjb : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (LocalCover.blockSite k b) = b :=
    LocalCover.jBlock_blockSite le_rfl b
  have hjb' : jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bk (LocalCover.blockSite k b)) = bc b := by
    rw [← hbs]; exact LocalCover.jBlock_blockSite le_rfl (bc b)
  have hΦE : ∀ (t : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))
      (t' : ((Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)) × (Hm'.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ))),
      (∀ x, t'.1.2 (hI.e x) = t.1.2 x) → (∀ y i, t'.2.1 (hH.e y, i) = t.2.1 (y, i)) →
      FieldCorr (ρ + 1) t.2.2.2 t'.2.2.2 →
      blockEnergyFun Gb' Hm' (compWeight L (SA).a₁) (SA).ν k (bc b) t'.1 t'.2.1 t'.2.2 =
        blockEnergyFun Gb Hm (compWeight L (SA).a₁) (SA).ν k b t.1 t.2.1 t.2.2 := by
    intro t t' hα' hδ' hψ'
    have := hI.blockEnergyFun_eq hH (compWeight L (SA).a₁) (SA).ν (R := R + L ^ k) (by omega) hnE
      hnE' (inBox_mono (by omega) hzR) t t' hα' hδ' hψ'
    rwa [hjb, hjb'] at this
  have h := hI.evDecBg_canon_twoTorus hH hk hGA hGB (by show (1 / 2 : ℝ) ≤ 1; norm_num)
    (by show (1 : ℝ) ≤ 2; norm_num) hC hC' hHm hHm' hS Sb Sb' hMX hMX' hCx hmar hα hsm _ hcψ
    (hF₁an b) (hF₁ b) (hF₁' (bc b)) (hSolan b) (hSol b) (hSol' (bc b)) hcov hX₁ hcov' hX₁'
    (X₁g := ∅) (fun x hx => by simp at hx) (fun x hx => by simp at hx) hρR
    (fun x hx => hXR x hx) hYR hnS hnS' hnF hnF'
    (Φ := blockEnergyFun Gb Hm (compWeight L (SA).a₁) (SA).ν k b)
    (Φ' := blockEnergyFun Gb' Hm' (compWeight L (SA).a₁) (SA).ν k (bc b))
    ((blockEnergyFun_analytic (compWeight L (SA).a₁) (SA).ν k b).mono (Set.subset_univ _))
    (fun t _ t' _ _ hα' hδ' _ _ hψ' => hΦE t t' hα' hδ' hψ') Zm hW hD hD' hΨc hhc hb hb' hhat
  rw [hF, ← hbs, ← hZm] at h
  rw [hDe, hDe']
  exact h

/-- **The corrected marks of corresponding blocks on two tori** (local pairs, steps `hatStepKG`):
`decMarkCorrBg` of the block `bc b` at `bm '' Y` and of `b` at `Y`, for a first mark with
`‖u‖ m_R < δ₁` (`corrMark_congr` and `blockTermEq_twoTorus`). -/
theorem decMarkCorrBg_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {c BG κ eps Kc' Cx' c₂ BG₂ δ₁ Kc Cx : ℝ}
    (hC : FlCore N Gb Hm (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hC' : FlCore N Gb' Hm' (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) (hHm' : Hm'.Ω (k + 1) = ∅)
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (Sb' : Dec2.CoverBase (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX' : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {F₁ : TA → DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₁' : TB → DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    (hF₁an : ∀ z, AnalyticOnNhd ℂ (F₁ z) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ z (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₁ z (s, rawOf D) = (φ, α))
    (hF₁' : ∀ z' (s : Dec2.DecParams (coverOf Gb')) (D : BgData Gb' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb' (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb'.Ω 1 × Fin N → ℂ)
        (α : Gb'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₁' z' (s, rawOf D) = (φ, α))
    {Sol : TA → Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : TB → Dec2.DecParams (coverOf Gb') × Edat Hm' N →
      (Hm'.Ω 1 × Fin N → ℂ) × (Hm'.Ω 1 → ℂ)}
    (hSolan : ∀ z, AnalyticOnNhd ℂ (Sol z) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ z (p : Dec2.DecParams (coverOf Gb) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol z p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2))
    (hSol' : ∀ z' (p : Dec2.DecParams (coverOf Gb') × Edat Hm' N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm' N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' z' p).1 = dphi Hm' (Dec2.decG (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol' z' p).2 ∧
        Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol' z' p).2 ∧
        Small Hm' (Sol' z' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm' (Sol' z' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm' (Sol' z' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm'.Ω 1 → ℂ, Small Hm' δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' →
            δα' = (Sol' z' p).2))
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁') {R : ℕ} (hρR : ρ ≤ R)
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L 1 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L 1 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnE : 2 * (R + L ^ k + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnE' : 2 * (R + L ^ k + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 <
      (N₁' * L ^ m₁) * L ^ (k + 1))
    (Zm : Finset (unitPts Gb)) {Zm' : Finset (unitPts Gb')}
    (hZm : Zm' = Zm.map hI.unitEquiv.toEmbedding)
    {θ : physParamBg N Gb} {θ' : physParamBg N Gb'}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb' (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hraw₁ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).1)
    (hraw₂ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).2)
    {ρh : ℝ} (hρh : 0 < ρh) (hρc : ρh ≤ cψ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Φ : ∀ b, ((SA).blockSplit 1 hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit 1 hp').Ωb b)
    (hΦ : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ' ((SB).cellOf 1 (unitPt hGB (bk x))) ⟨unitPt hGB (bk x), rfl⟩ =
        Φ ((SA).cellOf 1 (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩)
    (b : TA) (hX : ∀ x ∈ LocalCover.nbhd 1 (LocalCover.blockSite k b),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    {um : ℂ} (hum : ‖um‖ *
      markedRad d L N k (SA).a₁ κ cψ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁) :
    decMarkCorrBg (SB) Gb' (BgTransport.canon (SB).G' Gb' N)
        (LocalCover.nbhdF 1 (LocalCover.blockSite k (bc b))) 1 k
        (LocalCover.fam 1 (LocalCover.blockSite k (bc b))) (SB).a₁ (SB).ν
        (((SB).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁' (bc b)) (Sol' (bc b))
        (blockEnergyFun Gb' Hm' (compWeight L (SB).a₁) (SB).ν k (bc b)) Zm' (bk '' Y) ρh hp'
        (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) um Φ' =
      decMarkCorrBg (SA) Gb (BgTransport.canon (SA).G' Gb N)
        (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
        (LocalCover.fam 1 (LocalCover.blockSite k b)) (SA).a₁ (SA).ν
        (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ b) (Sol b)
        (blockEnergyFun Gb Hm (compWeight L (SA).a₁) (SA).ν k b) Zm Y ρh hp
        (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) um Φ :=
  corrMark_congr (E := fun v t => evDecBg (SA).G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k b)) Gb (SA).a₁ (SA).ν
            (BgTransport.canon (SA).G' Gb N) (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ b) (Sol b)
            (blockEnergyFun Gb Hm (compWeight L (SA).a₁) (SA).ν k b) Zm v t Y
            ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N),
            (BgTransport.canon (SA).G' Gb N).res ((SA).hatOf 1 ρh hp Φ)))
    (E' := fun v t => evDecBg (SB).G' (LocalCover.nbhdF 1 (LocalCover.blockSite k (bc b))) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k (bc b))) Gb' (SB).a₁ (SB).ν
            (BgTransport.canon (SB).G' Gb' N) (((SB).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁' (bc b))
            (Sol' (bc b)) (blockEnergyFun Gb' Hm' (compWeight L (SB).a₁) (SB).ν k (bc b)) Zm' v t
            (bk '' Y) ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N),
            (BgTransport.canon (SB).G' Gb' N).res ((SB).hatOf 1 ρh hp' Φ')))
    (fun _ _ hvt => blockTermEq_twoTorus hN2 hk νS β p₁ δ hI hH hGA hGB hC hC' hHm hHm' hS Sb Sb'
      hMX hMX' hCx hmar hα hsm hcψ hF₁an hF₁ hF₁' hSolan hSol hSol' hN hN' hρR hnS hnS' hnF hnF'
      hnE hnE' Zm hZm hθ hθ' hraw₁ hraw₂ hρh hρc hp hp' Φ Φ' hΦ b hX hYR hvt) hum hC.δ₁_pos

/-- **The rooted outputs of the corrected marks on two tori** (local pairs, steps `hatStepKG`):
`markedOutDec` of the corrected marks of the blocks (`decMarkCorrTermBg`) of the root `bc z` at the
label `bm '' Y'` and of the root `z` at the label `Y'` of the box, for a first mark with
`‖u‖ m_R < δ₁` (`markedOutSum_twoTorus`, `deriv_decMarkCorrTermBg`, `decMarkCorrBg_twoTorus`). -/
theorem markedOutBg_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {c BG κ eps Kc' Cx' c₂ BG₂ δ₁ Kc Cx : ℝ}
    (hC : FlCore N Gb Hm (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hC' : FlCore N Gb' Hm' (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) (hHm' : Hm'.Ω (k + 1) = ∅)
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (Sb' : Dec2.CoverBase (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX' : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {F₁ : TA → DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₁' : TB → DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    (hF₁an : ∀ z, AnalyticOnNhd ℂ (F₁ z) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ z (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₁ z (s, rawOf D) = (φ, α))
    (hF₁' : ∀ z' (s : Dec2.DecParams (coverOf Gb')) (D : BgData Gb' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb' (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb'.Ω 1 × Fin N → ℂ)
        (α : Gb'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₁' z' (s, rawOf D) = (φ, α))
    {Sol : TA → Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : TB → Dec2.DecParams (coverOf Gb') × Edat Hm' N →
      (Hm'.Ω 1 × Fin N → ℂ) × (Hm'.Ω 1 → ℂ)}
    (hSolan : ∀ z, AnalyticOnNhd ℂ (Sol z) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ z (p : Dec2.DecParams (coverOf Gb) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol z p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2))
    (hSol' : ∀ z' (p : Dec2.DecParams (coverOf Gb') × Edat Hm' N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm' N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' z' p).1 = dphi Hm' (Dec2.decG (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol' z' p).2 ∧
        Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol' z' p).2 ∧
        Small Hm' (Sol' z' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm' (Sol' z' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm' (Sol' z' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm'.Ω 1 → ℂ, Small Hm' δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' →
            δα' = (Sol' z' p).2))
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁') {R : ℕ} (hρR : ρ ≤ R)
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L 1 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L 1 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnE : 2 * (R + L ^ k + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnE' : 2 * (R + L ^ k + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 <
      (N₁' * L ^ m₁) * L ^ (k + 1))
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnH : 2 * (R + 2 * (L * cellSide L 1 m₁ (k + 1))) + L * cellSide L 1 m₁ (k + 1) <
      (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH' : 2 * (R + 2 * (L * cellSide L 1 m₁ (k + 1))) + L * cellSide L 1 m₁ (k + 1) <
      (N₁' * L ^ m₁) * L ^ (k + 1))
    (Zm : Finset (unitPts Gb)) {Zm' : Finset (unitPts Gb')}
    (hZm : Zm' = Zm.map hI.unitEquiv.toEmbedding)
    {θ : physParamBg N Gb} {θ' : physParamBg N Gb'}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb' (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hraw₁ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).1)
    (hraw₂ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).2)
    {ρh : ℝ} (hρh : 0 < ρh) (hρc : ρh ≤ cψ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Φ : ∀ b, ((SA).blockSplit 1 hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit 1 hp').Ωb b)
    (hΦ : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ' ((SB).cellOf 1 (unitPt hGB (bk x))) ⟨unitPt hGB (bk x), rfl⟩ =
        Φ ((SA).cellOf 1 (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩)
    (z : TA) {rc : ℕ} (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z)
    (hrc : L ^ (k + 1) * rc ≤ R)
    (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y' : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY'R : ∀ y ∈ Y', InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    {u : ℂ} (hum : ‖u‖ *
      markedRad d L N k (SA).a₁ κ cψ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁) :
    markedOutDec 1 (fun _ : TB => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (e1DomG (SB))
        (bc z) (decMarkCorrTermBg (SB) Gb' (BgTransport.canon (SB).G' Gb' N)
          (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
          (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 (SB).a₁ (SB).ν
          (((SB).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁' Sol' Zm' ρh hp' ((SB).β : ℂ)
          (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) u Φ') (bk '' Y') =
      markedOutDec 1 (fun _ : TA => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG (SA)) z
        (decMarkCorrTermBg (SA) Gb (BgTransport.canon (SA).G' Gb N)
          (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
          (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 (SA).a₁ (SA).ν
          (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol Zm ρh hp ((SA).β : ℂ)
          (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) u Φ) Y' := by
  unfold markedOutDec
  refine markedOutSum_twoTorus (m₀ := 1) hN hN' z hz hrc hroot hY'R hn hn' hnF hnF' hnH hnH'
    (fun b Y => deriv (decMarkCorrTermBg (SA) Gb (BgTransport.canon (SA).G' Gb N)
      (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
      (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 (SA).a₁ (SA).ν
      (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol Zm ρh hp ((SA).β : ℂ)
      (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) u Φ b Y) 0)
    (fun b Y => deriv (decMarkCorrTermBg (SB) Gb' (BgTransport.canon (SB).G' Gb' N)
      (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
      (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 (SB).a₁ (SB).ν
      (((SB).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁' Sol' Zm' ρh hp' ((SB).β : ℂ)
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) u Φ' b Y) 0)
    (fun q _ hYR hbR => ?_)
  rw [deriv_decMarkCorrTermBg, deriv_decMarkCorrTermBg]
  exact congrArg₂ (· * ·) rfl (decMarkCorrBg_twoTorus hN2 hk νS β p₁ δ hI hH hGA hGB hC hC' hHm
    hHm' hS Sb Sb' hMX hMX' hCx hmar hα hsm hcψ hF₁an hF₁ hF₁' hSolan hSol hSol' hN hN' hρR hnS
    hnS' hnF hnF' hnE hnE' Zm hZm hθ hθ' hraw₁ hraw₂ hρh hρc hp hp' Φ Φ' hΦ q.1 hbR hYR hum)

/-- **The bridge marks recomputed on corresponding local pairs, on two tori** (steps `hatStepKG`,
gate on the local charts).  At parameters `θ`, `θ'` of the two local charts whose raw data
correspond on the box, block variables corresponding at the unit points of the box, a bridge label
`Y'` of the root `z` in the box and the bridge label `bm '' Y'` of `bc z`, and `‖u‖ ≤ 1`, the marks
`e1MarkGParamGBgOn` agree. -/
theorem e1MarkGParamGBgOn_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {c BG κ eps Kc' Cx' c₂ BG₂ δ₁ Kc Cx : ℝ}
    (hC : FlCore N Gb Hm (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hC' : FlCore N Gb' Hm' (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) (hHm' : Hm'.Ω (k + 1) = ∅)
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (Sb' : Dec2.CoverBase (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX' : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {F₁ : TA → DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₁' : TB → DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    (hF₁an : ∀ z, AnalyticOnNhd ℂ (F₁ z) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ z (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₁ z (s, rawOf D) = (φ, α))
    (hF₁' : ∀ z' (s : Dec2.DecParams (coverOf Gb')) (D : BgData Gb' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb' (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb'.Ω 1 × Fin N → ℂ)
        (α : Gb'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₁' z' (s, rawOf D) = (φ, α))
    {Sol : TA → Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : TB → Dec2.DecParams (coverOf Gb') × Edat Hm' N →
      (Hm'.Ω 1 × Fin N → ℂ) × (Hm'.Ω 1 → ℂ)}
    (hSolan : ∀ z, AnalyticOnNhd ℂ (Sol z) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ z (p : Dec2.DecParams (coverOf Gb) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol z p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2))
    (hSol' : ∀ z' (p : Dec2.DecParams (coverOf Gb') × Edat Hm' N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm' N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' z' p).1 = dphi Hm' (Dec2.decG (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol' z' p).2 ∧
        Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol' z' p).2 ∧
        Small Hm' (Sol' z' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm' (Sol' z' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm' (Sol' z' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm'.Ω 1 → ℂ, Small Hm' δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' →
            δα' = (Sol' z' p).2))
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁') {R : ℕ} (hρR : ρ ≤ R)
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L 1 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L 1 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnE : 2 * (R + L ^ k + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnE' : 2 * (R + L ^ k + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 <
      (N₁' * L ^ m₁) * L ^ (k + 1))
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnH : 2 * (R + 2 * (L * cellSide L 1 m₁ (k + 1))) + L * cellSide L 1 m₁ (k + 1) <
      (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH' : 2 * (R + 2 * (L * cellSide L 1 m₁ (k + 1))) + L * cellSide L 1 m₁ (k + 1) <
      (N₁' * L ^ m₁) * L ^ (k + 1))
    (Zm : Finset (unitPts Gb)) {Zm' : Finset (unitPts Gb')}
    (hZm : Zm' = Zm.map hI.unitEquiv.toEmbedding)
    {θ : physParamBg N Gb} {θ' : physParamBg N Gb'}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb' (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hraw₁ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).1)
    (hraw₂ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).2)
    {ρh ρh' : ℝ} (hρh' : ρh' = ρh) (hρh : 0 < ρh) (hρc : ρh ≤ cψ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Φ : ∀ b, ((SA).blockSplit 1 hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit 1 hp').Ωb b)
    (hΦ : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ' ((SB).cellOf 1 (unitPt hGB (bk x))) ⟨unitPt hGB (bk x), rfl⟩ =
        Φ ((SA).cellOf 1 (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩)
    (z : TA) {rc : ℕ} (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z)
    (hrc : L ^ (k + 1) * rc ≤ R)
    (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ : TA => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (e1DomG (SA)) z})
    (Y'' : {Y' // Y' ∈ bridgeFamily 1 (fun _ : TB => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1))))
      (e1DomG (SB)) (bc z)})
    (hYY : Y''.1 = bk '' Y'.1) (hY'R : ∀ y ∈ Y'.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    {u : ℂ} (hu : ‖u‖ ≤ 1)
    (hrad : markedRad d L N k (SA).a₁ κ cψ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    {epsG : ℝ} (hleG : eps ≤ epsG) :
    e1MarkGParamGBgOn (SB) Gb' (BgTransport.canon (SB).G' Gb' N) Zm' F₁' Sol' ρh' hp' (bc z) Gb' epsG
        θ' Y'' u Φ' =
      e1MarkGParamGBgOn (SA) Gb (BgTransport.canon (SA).G' Gb N) Zm F₁ Sol ρh hp z Gb epsG θ Y' u
        Φ := by
  subst ρh'
  have hu' : ‖u‖ < (17 / 16 : ℝ) := by linarith
  have hum : ‖u‖ * markedRad d L N k (SA).a₁ κ cψ
      (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ := by
    have := marks_lt_of_norm_le hu hrad hC.δ₁_pos
    rwa [norm_zero, add_zero] at this
  have hc1 : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L (SA).a₁) (SA).ν (k + 1) 1 epsG ∧ ‖u‖ < (17 / 16 : ℝ) :=
    ⟨xiCRaw_mono_radius hleG hθ, hu'⟩
  have hc2 : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb' (compWeight L (SB).a₁) (SB).ν (k + 1) 1 epsG ∧ ‖u‖ < (17 / 16 : ℝ) :=
    ⟨xiCRaw_mono_radius hleG hθ', hu'⟩
  unfold e1MarkGParamGBgOn
  rw [ite_eq_left hc1, ite_eq_left hc2, hYY]
  exact markedOutBg_twoTorus hN2 hk νS β p₁ δ hI hH hGA hGB hC hC' hHm hHm' hS Sb Sb' hMX hMX' hCx
    hmar hα hsm hcψ hF₁an hF₁ hF₁' hSolan hSol hSol' hN hN' hρR hnS hnS' hnF hnF' hnE hnE' hn hn'
    hnH hnH' Zm hZm hθ hθ' hraw₁ hraw₂ hρh hρc hp hp' Φ Φ' hΦ z hz hrc hroot hY'R hum

/-- **The preimage masks of the root blocks.**  For a root `z` of the coarse box with its block in
the box of radius `ρ`, the preimage of the root mask `blockU (bc z)` of the second step on `Gb'` is
the image of the preimage of `blockU z` on `Gb` (`maskPre_map`, `rootMask_bc`). -/
theorem maskPre_blockU_map (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) (hI : OmegaIso Gb Gb' ρ)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hnU : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnU' : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1)) (z : TA) {rc : ℕ}
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z) (hrc : L ^ (k + 1) * rc ≤ ρ) :
    maskPre (SB).hG' Gb' ((SB).blockU (bc z)) =
      (maskPre (SA).hG' Gb ((SA).blockU z)).map hI.unitEquiv.toEmbedding :=
  hI.maskPre_map hGA hGB (fun _ hx => rootMask_bc hnU hnU' hGA hGB z hz hrc hx)

end OmegaIso

end Balaban.Polymer.LocalIso
