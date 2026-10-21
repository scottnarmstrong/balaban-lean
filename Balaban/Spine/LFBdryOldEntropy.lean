/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFBdry
public import Balaban.Fluctuation.SizeModHoleRoot
public import Balaban.Fluctuation.LocalClassDensityFamilyIdx
public import Balaban.Fluctuation.DARateNumerics
public import Balaban.Localization.LedgerPacking
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The entropy of the re-expanded old boundary terms at one output label (leaf O5 of row (g2))

LFR Lemma IV.1.5 (iii); P6 p. 34 ("for a fixed `Y` we resum over the domains `X`. This contributes
the factor `K₀ M₁^d |Y ∩ Ω_{k+1}| ≤ …`"), (4.32)–(4.34); P3 (4.48)–(4.49) (the mark count).

An old boundary term `ℬ^{(k)}(X)` whose domain meets the new region `Ω_{k+1}` is re-expanded and
assigned output labels `Y` of scale `k + 1`; an assignment is the old label `X` together with a set
`J` of patches (`π'_{k+1}`-cubes rooted at active sites of `Y`).  This file proves, at the level of
the fine sites (`Fluctuation.DjModFin`, ruling R11), the counting that bounds the old part at one
output label once the coefficient of each assignment is bounded:

* `card_cellsIn_inter_le`: the `π_j`-cubes of `Y ∩ Ω'` number at most
  `L^d c₁ (1 + d^cov_{j+1}(Y mod Ω'^c))` ((G1) for `Y`, each cube of scale `j + 1` holding `L^d`
  cubes of scale `j`);
* `sum_exp_oldIn_le`: the old labels inside `Y` meeting `Ω'` satisfy
  `∑ e^{-κ₀ d^cov_j(X mod Ω^c)} ≤ L^d c₁ (1 + d^cov_{j+1}(Y)) K₀` (each contains a `π_j`-cube of
  `Y ∩ Ω'`; (G2) `G2_XFin` through `sum_exp_le_of_roots`);
* `patchesIn`, `card_patchesIn_le`: the patches of `Y`, at most `L^d c₁ (1 + d^cov_{j+1}(Y))`;
* `assignEnt`, `sum_exp_assign_le`: the entropy of the pairs `(X, J)`;
* `norm_sum_oldAssign_le`: the bound `‖∑_a T a‖ ≤ C_re · assignEnt · e^{-κ_o d^cov_{j+1}(Y)}` of the
  old part at `Y` from the re-expansion bound of each assignment, the lower bound of the old
  sizes, the size transfer and the entropy (`Balaban.RootFSpine.norm_sum_le_of_transfer`), for a
  family of coefficients attached to the pairs with weights of total at most `1` on each pair;
* `assignEnt_le_exp`: `assignEnt ≤ A e^{c d}`, the form in which the entropy is paid by the rate.

The coefficients themselves (the old terms re-expanded in the fluctuation integral) are not
constructed here; see `Spine/LFBdryOldAssign.lean` and `notes/phase1/SPINE.md`, row (g2).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

open Classical in
/-- The cell bases of `π_j`-cubes inside a set are its `cellCount`. -/
theorem card_cellsIn_eq_cellCount (Z : Set (CTorus d L N₁ m₁ K)) :
    (cellsIn (L := L) m₀ j Z).card = cellCount (cellSide L m₀ m₁ j) Z := by
  unfold cellsIn cellCount
  congr 1

/-- **The cell of a site of `Y ∩ Ω'`**, for a label `Y` of `DjModFin` at `Ω'` and `Ω'` a union of
`π_j`-cubes: the `π_j`-cube of the site lies in `Y ∩ Ω'`. -/
theorem DjModFin.cell_subset_inter (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Ω' Y : Set (CTorus d L N₁ m₁ K)}
    (hΩ' : IsPiUnion m₀ j Ω') (hY : DjModFin m₀ j Ω' Y) {y : CTorus d L N₁ m₁ K}
    (hy : y ∈ Y ∩ Ω') :
    box (cbase (cellSide L m₀ m₁ j) y) (cellSide L m₀ m₁ j) ⊆ Y ∩ Ω' := by
  obtain ⟨b, hb, hyb, hbY⟩ := hY.exists_box hy
  exact Set.subset_inter ((cell_subset_cube (cellSide_dvd (K := K) (m₁ := m₁) hN hj)
    (cellSide_pos m₀ m₁ j) hb hyb).trans hbY) (hΩ'.cell hN hj hy.2)

/-- A union of `π_{j+1}`-cubes is a union of `π_j`-cubes. -/
theorem IsPiUnion.of_succ (hN : L ^ m₀ ∣ N₁) (hj : j + 1 ≤ K) {Ω' : Set (CTorus d L N₁ m₁ K)}
    (h : IsPiUnion m₀ (j + 1) Ω') : IsPiUnion m₀ j Ω' := by
  refine (isPiUnion_iff_cell hN (Nat.le_of_succ_le hj)).2 fun z hz => ?_
  have hcell := h.cell hN hj hz
  rw [cellSide_succ] at hcell
  exact (cell_subset_cube (cellSide_dvd (K := K) (m₁ := m₁) hN (Nat.le_of_succ_le hj))
    (cellSide_pos m₀ m₁ j) (Localization.aligned_of_dvd (dvd_mul_left _ _) (aligned_cbase z))
    (mem_box_cbase (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j)) z)).trans
    hcell

/-- **The cells of scale `j` in `Y ∩ Ω'`**, for a label `Y` of `DjModFin` at the scale-`(j + 1)`
region `Ω'`: at most `L^d c₁ (1 + d^cov_{j+1}(Y mod Ω'^c))` (each cell of scale `j + 1` holds
`L^d` cells of scale `j`; (G1) for `Y`). -/
theorem card_cellsIn_inter_le (hN : L ^ m₀ ∣ N₁) (hj : j + 1 ≤ K)
    {Ω' Y : Set (CTorus d L N₁ m₁ K)} (hΩ' : IsPiUnion m₀ (j + 1) Ω')
    (hY : DjModFin m₀ (j + 1) Ω' Y) :
    ((cellsIn (L := L) m₀ j (Y ∩ Ω')).card : ℝ) ≤
      (L : ℝ) ^ d * (c1 d L * (1 + dcovMod m₀ (j + 1) Ω' Y)) := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (Nat.le_of_succ_le hj)
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have h1 : cellCount (cellSide L m₀ m₁ j) (Y ∩ Ω') ≤
      L ^ d * cellCount (L * cellSide L m₀ m₁ j) (Y ∩ Ω') :=
    cellCount_le_pow_mul_cellCount hdvd ha0 (Nat.pos_of_ne_zero (NeZero.ne L)) (fun y hy => by
      rw [← cellSide_succ]; exact hY.cell_subset_inter hN hj hΩ' hy)
  rw [← cellSide_succ] at h1
  have h2 := hY.cellCount_le hN hj
  rw [card_cellsIn_eq_cellCount]
  calc ((cellCount (cellSide L m₀ m₁ j) (Y ∩ Ω') : ℕ) : ℝ) ≤
        ((L ^ d * cellCount (cellSide L m₀ m₁ (j + 1)) (Y ∩ Ω') : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (L : ℝ) ^ d * (cellCount (cellSide L m₀ m₁ (j + 1)) (Y ∩ Ω') : ℝ) := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

open Classical in
/-- **(O5), the old labels inside an output label** (P6 p. 34, "for a fixed `Y` we resum over the
domains `X`"; LFR Lemma IV.1.5 (iii)).  For an output label `Y` of `DjModFin` at the new region
`Ω' ⊆ Ω` (scale `j + 1`), the labels `X` of `DjModFin` at the old region `Ω` (scale `j`) contained
in `Y` and meeting `Ω'` satisfy
`∑_X e^{-κ₀ d^cov_j(X mod Ω^c)} ≤ L^d c₁ (1 + d^cov_{j+1}(Y mod Ω'^c)) K₀`: each such `X` contains a
`π_j`-cube of `Y ∩ Ω'` (the cube of a site of `X ∩ Ω'`), and (G2) (`G2_XFin`) bounds the sum over
the labels containing one cube. -/
theorem sum_exp_oldIn_le (hN : L ^ m₀ ∣ N₁) (hj : j + 1 ≤ K)
    {Ω Ω' Y : Set (CTorus d L N₁ m₁ K)} (hΩ : IsPiUnion m₀ j Ω)
    (hΩ' : IsPiUnion m₀ (j + 1) Ω') (hΩΩ' : Ω' ⊆ Ω) (hY : DjModFin m₀ (j + 1) Ω' Y)
    {κ₀ : ℝ} (hκ : aEnt d L + 1 ≤ κ₀) :
    ∑ X ∈ Finset.univ.filter (fun X : Set (CTorus d L N₁ m₁ K) =>
        DjModFin m₀ j Ω X ∧ X ⊆ Y ∧ (X ∩ Ω').Nonempty),
      Real.exp (-κ₀ * dcovMod m₀ j Ω X) ≤
    (L : ℝ) ^ d * (c1 d L * (1 + dcovMod m₀ (j + 1) Ω' Y)) * K0 d L κ₀ := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (Nat.le_of_succ_le hj)
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hΩ'j := hΩ'.of_succ hN hj
  have h := sum_exp_le_of_roots hN (Nat.le_of_succ_le hj) hΩ (cellsIn m₀ j (Y ∩ Ω'))
    (fun r hr => by
      obtain ⟨hal, hsub⟩ := mem_cellsIn.1 hr
      exact ⟨hal, fun x hx => hΩΩ' (hsub hx).2⟩)
    hκ (fun X => X ⊆ Y ∧ (X ∩ Ω').Nonempty)
    (fun X hX hP => by
      obtain ⟨hXY, x, hxX, hxΩ'⟩ := hP
      obtain ⟨b, hb, hxb, hbX⟩ := hX.exists_box ⟨hxX, hΩΩ' hxΩ'⟩
      have hcX : box (cbase (cellSide L m₀ m₁ j) x) (cellSide L m₀ m₁ j) ⊆ X :=
        (cell_subset_cube hdvd ha0 hb hxb).trans hbX
      have hcΩ' := hΩ'j.cell hN (Nat.le_of_succ_le hj) hxΩ'
      exact ⟨cbase (cellSide L m₀ m₁ j) x, mem_cellsIn.2 ⟨aligned_cbase x,
        Set.subset_inter (hcX.trans hXY) hcΩ'⟩, hcX⟩)
  convert h.trans (mul_le_mul_of_nonneg_right (card_cellsIn_inter_le hN hj hΩ' hY)
    (K0_pos d L κ₀).le) using 3

open Classical in
/-- **The patches of a label** (P3 (4.44)–(4.48), modular form): the bases of the `π'_j`-cubes
meeting `Y ∩ Ω'`, the patches rooted at the active sites of `Y` of `transfer_patches`. -/
noncomputable def patchesIn (m₀ j : ℕ) (Ω' Y : Set (CTorus d L N₁ m₁ K)) :
    Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun p => Aligned (cellSide L m₀ m₁ j) p ∧
    (box p (L * cellSide L m₀ m₁ j) ∩ (Y ∩ Ω')).Nonempty

theorem mem_patchesIn {Ω' Y : Set (CTorus d L N₁ m₁ K)} {p : CTorus d L N₁ m₁ K} :
    p ∈ patchesIn m₀ j Ω' Y ↔ Aligned (cellSide L m₀ m₁ j) p ∧
      (box p (L * cellSide L m₀ m₁ j) ∩ (Y ∩ Ω')).Nonempty := by
  classical
  simp [patchesIn]

/-- **The number of patches of a label**: at most `L^d c₁ (1 + d^cov_j(Y mod Ω'^c))` (a patch
meets a `π_j`-cube of `Y ∩ Ω'`, a cube lies in at most `L^d` patches, and (G1)). -/
theorem card_patchesIn_le (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Ω' Y : Set (CTorus d L N₁ m₁ K)}
    (hΩ' : IsPiUnion m₀ j Ω') (hY : DjModFin m₀ j Ω' Y) :
    ((patchesIn m₀ j Ω' Y).card : ℝ) ≤ (L : ℝ) ^ d * (c1 d L * (1 + dcovMod m₀ j Ω' Y)) := by
  classical
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  set a := cellSide L m₀ m₁ j with ha
  let f : CTorus d L N₁ m₁ K → CTorus d L N₁ m₁ K := fun p =>
    if h : (box p (L * a) ∩ (Y ∩ Ω')).Nonempty then cbase a h.some else p
  have hf : ∀ p ∈ patchesIn m₀ j Ω' Y, f p ∈ cellsIn m₀ j (Y ∩ Ω') ∧ f p ∈ box p (L * a) := by
    intro p hp
    obtain ⟨hal, hne⟩ := mem_patchesIn.1 hp
    have hfp : f p = cbase a hne.some := by
      simp only [f]
      split_ifs with h
      · rfl
      · exact absurd hne h
    obtain ⟨hs1, hs2⟩ := hne.some_mem
    rw [hfp]
    refine ⟨mem_cellsIn.2 ⟨aligned_cbase _, hY.cell_subset_inter hN hj hΩ' hs2⟩, ?_⟩
    exact cell_subset_cube hdvd ha0 hal hs1 (mem_box_self _ ha0)
  have hcard := Finset.card_le_mul_card_image_of_maps_to (fun p hp => (hf p hp).1) (L ^ d)
    (fun γ hγ => by
      refine le_trans (Finset.card_le_card ?_)
        (card_cubes_containing hdvd ha0 (mem_cellsIn.1 hγ).1)
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, (mem_patchesIn.1 hp1).1, ?_⟩
      rw [← hp2]
      exact (hf p hp1).2)
  have h2 := card_cellsIn_eq_cellCount (L := L) (m₀ := m₀) (j := j) (Y ∩ Ω')
  have h3 := hY.cellCount_le hN hj
  rw [← h2] at h3
  calc ((patchesIn m₀ j Ω' Y).card : ℝ) ≤ ((L ^ d * (cellsIn m₀ j (Y ∩ Ω')).card : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = (L : ℝ) ^ d * ((cellsIn m₀ j (Y ∩ Ω')).card : ℝ) := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- The entropy constant of the assignments at an output label of size `D`:
`L^d c₁ (1 + D) K₀ exp(e^{-b} L^d c₁ (1 + D))` (the old labels inside the output label, `G2_XFin`;
the mark sets of its patches). -/
noncomputable def assignEnt (d L : ℕ) (α b D : ℝ) : ℝ :=
  (L : ℝ) ^ d * (c1 d L * (1 + D)) * K0 d L α *
    Real.exp (Real.exp (-b) * ((L : ℝ) ^ d * (c1 d L * (1 + D))))

open Classical in
/-- **(O5), the entropy of the assignments at one output label** (P6 p. 34: "for a fixed `Y` we
resum over the domains `X`"; P3 (4.49), the mark count).  The pairs `(X, J)` of an old label `X` of
`DjModFin` at `Ω` contained in the output label `Y` and meeting `Ω'`, and of a set `J` of patches of
`Y`, satisfy `∑ e^{-α d^cov_j(X mod Ω^c) - b |J|} ≤ assignEnt d L α b (d^cov_{j+1}(Y mod Ω'^c))`
for `α ≥ a_ent + 1`. -/
theorem sum_exp_assign_le (hN : L ^ m₀ ∣ N₁) (hj : j + 1 ≤ K)
    {Ω Ω' Y : Set (CTorus d L N₁ m₁ K)} (hΩ : IsPiUnion m₀ j Ω)
    (hΩ' : IsPiUnion m₀ (j + 1) Ω') (hΩΩ' : Ω' ⊆ Ω) (hY : DjModFin m₀ (j + 1) Ω' Y)
    {α b : ℝ} (hα : aEnt d L + 1 ≤ α) :
    ∑ a ∈ (Finset.univ.filter fun X : Set (CTorus d L N₁ m₁ K) =>
        DjModFin m₀ j Ω X ∧ X ⊆ Y ∧ (X ∩ Ω').Nonempty) ×ˢ (patchesIn m₀ (j + 1) Ω' Y).powerset,
      Real.exp (-α * dcovMod m₀ j Ω a.1 - b * a.2.card) ≤
    assignEnt d L α b (dcovMod m₀ (j + 1) Ω' Y) := by
  rw [Finset.sum_product]
  have e : ∀ (X : Set (CTorus d L N₁ m₁ K)) (J : Finset (CTorus d L N₁ m₁ K)),
      Real.exp (-α * dcovMod m₀ j Ω X - b * J.card) =
        Real.exp (-α * dcovMod m₀ j Ω X) * Real.exp (-b * J.card) := by
    intro X J
    rw [← Real.exp_add]; congr 1; ring
  simp_rw [e, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  unfold assignEnt
  have hmk := sum_exp_card_le (patchesIn m₀ (j + 1) Ω' Y) (patchesIn m₀ (j + 1) Ω' Y).powerset
    (fun C hC => Finset.mem_powerset.1 hC) b
  have hcard : ((patchesIn m₀ (j + 1) Ω' Y).card : ℝ) * Real.exp (-b) ≤
      Real.exp (-b) * ((L : ℝ) ^ d * (c1 d L * (1 + dcovMod m₀ (j + 1) Ω' Y))) := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (card_patchesIn_le hN hj hΩ' hY) (Real.exp_pos _).le
  refine mul_le_mul (sum_exp_oldIn_le hN hj hΩ hΩ' hΩΩ' hY hα)
    ((hmk.1.trans hmk.2).trans (Real.exp_le_exp.2 hcard))
    (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) ?_
  have := one_le_c1 d L
  have h1 : 0 ≤ 1 + dcovMod m₀ (j + 1) Ω' Y := by
    have := dcovMod_nonneg (m₀ := m₀) (j := j + 1) Ω' Y; linarith
  have := (K0_pos d L α).le
  positivity

open Classical in
/-- **The bound of the re-expanded old terms at one output label** (LFR Lemma IV.1.5 (iii); P6
(4.32)–(4.34); P3 (4.48)–(4.49)): `Balaban.RootFSpine.norm_sum_le_of_transfer` with the entropy
of the assignments (`sum_exp_assign_le`).  The coefficients `T a`, `a ∈ I`, are attached to pairs
`(X_a, J_a)`: an old label `X_a` of `DjModFin` at the region `Ω` of scale `j`, contained in the
output label `Y` and meeting the new region `Ω' ⊆ Ω`, and a set `J_a` of patches of `Y`; several
`a` may share a pair, with weights `ω a` of total at most `1` on each pair (the average over the
optimal covers of `X_a`).  Assume the re-expansion bound
`‖T a‖ ≤ ω a · C_re B₀ e^{-κ d_j(X_a)} e^{-κ_m |J_a|}`, a lower bound `D_min ≤ d_j(X_a)` with
`B₀ e^{-(κ/2) D_min} ≤ 1`, and the size transfer `d_{j+1}(Y) ≤ d_j(X_a)/L + c_G |J_a|`.  If
`κ/2 - κ_o/L ≥ a_ent + 1`, then
`‖∑_a T a‖ ≤ C_re · assignEnt d L (κ/2 - κ_o/L) (κ_m - κ_o c_G) (d_{j+1}(Y)) · e^{-κ_o d_{j+1}(Y)}`. -/
theorem norm_sum_oldAssign_le {ι : Type*} (hN : L ^ m₀ ∣ N₁) (hj : j + 1 ≤ K)
    {Ω Ω' Y : Set (CTorus d L N₁ m₁ K)} (hΩ : IsPiUnion m₀ j Ω)
    (hΩ' : IsPiUnion m₀ (j + 1) Ω') (hΩΩ' : Ω' ⊆ Ω) (hY : DjModFin m₀ (j + 1) Ω' Y)
    (I : Finset ι) (T : ι → ℂ) (Xa : ι → Set (CTorus d L N₁ m₁ K))
    (Ja : ι → Finset (CTorus d L N₁ m₁ K)) (ω : ι → ℝ)
    (hfib : ∀ p ∈ I.image (fun a => (Xa a, Ja a)),
      ∑ a ∈ I.filter (fun a => (Xa a, Ja a) = p), ω a ≤ 1)
    (hX : ∀ a ∈ I, DjModFin m₀ j Ω (Xa a) ∧ Xa a ⊆ Y ∧ (Xa a ∩ Ω').Nonempty)
    (hJ : ∀ a ∈ I, Ja a ⊆ patchesIn m₀ (j + 1) Ω' Y)
    {B₀ Cre κ κm κo Dmin : ℝ} (hCre : 0 ≤ Cre) (hB₀ : 0 ≤ B₀) (hκo : 0 ≤ κo)
    (hκ : aEnt d L + 1 ≤ κ / 2 - κo / L)
    (hT : ∀ a ∈ I, ‖T a‖ ≤ ω a * (Cre * B₀ * Real.exp (-κ * dcovMod m₀ j Ω (Xa a)) *
      Real.exp (-κm * (Ja a).card)))
    (hmin : ∀ a ∈ I, Dmin ≤ dcovMod m₀ j Ω (Xa a))
    (hB₀min : B₀ * Real.exp (-(κ / 2) * Dmin) ≤ 1)
    (hsize : ∀ a ∈ I, dcovMod m₀ (j + 1) Ω' Y ≤ dcovMod m₀ j Ω (Xa a) / L + cG d L * (Ja a).card) :
    ‖∑ a ∈ I, T a‖ ≤ Cre * assignEnt d L (κ / 2 - κo / L) (κm - κo * cG d L)
      (dcovMod m₀ (j + 1) Ω' Y) * Real.exp (-κo * dcovMod m₀ (j + 1) Ω' Y) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hκ0 : 0 ≤ κ := by
    have h1 := aEnt_nonneg d L
    have h2 : 0 ≤ κo / L := div_nonneg hκo hL.le
    linarith
  set f : ι → Set (CTorus d L N₁ m₁ K) × Finset (CTorus d L N₁ m₁ K) := fun a => (Xa a, Ja a)
    with hf
  set P := I.image f with hP
  have hmem : ∀ p ∈ P, ∃ a ∈ I, f a = p := fun p hp => Finset.mem_image.1 hp
  -- the sum regrouped by pairs
  rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := P)
    (fun a ha => Finset.mem_image_of_mem f ha)]
  refine Balaban.RootFSpine.norm_sum_le_of_transfer P
    (fun p => ∑ a ∈ I.filter (fun a => f a = p), T a) (fun p => dcovMod m₀ j Ω p.1)
    (fun p => (p.2.card : ℝ)) (κm := κm) (L := (L : ℝ)) (Cd := cG d L) hCre hB₀ hκ0 hκo ?_ ?_
    hB₀min ?_ ?_
  · intro p hp
    have hC : 0 ≤ Cre * B₀ * Real.exp (-κ * dcovMod m₀ j Ω p.1) *
        Real.exp (-κm * (p.2.card : ℝ)) := by positivity
    calc ‖∑ a ∈ I.filter (fun a => f a = p), T a‖
        ≤ ∑ a ∈ I.filter (fun a => f a = p), ‖T a‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ I.filter (fun a => f a = p), ω a * (Cre * B₀ *
            Real.exp (-κ * dcovMod m₀ j Ω p.1) * Real.exp (-κm * (p.2.card : ℝ))) := by
          refine Finset.sum_le_sum fun a ha => ?_
          obtain ⟨haI, hfa⟩ := Finset.mem_filter.1 ha
          have := hT a haI
          rw [← hfa]
          exact this
      _ = (∑ a ∈ I.filter (fun a => f a = p), ω a) * (Cre * B₀ *
            Real.exp (-κ * dcovMod m₀ j Ω p.1) * Real.exp (-κm * (p.2.card : ℝ))) := by
          rw [Finset.sum_mul]
      _ ≤ 1 * (Cre * B₀ * Real.exp (-κ * dcovMod m₀ j Ω p.1) *
            Real.exp (-κm * (p.2.card : ℝ))) := mul_le_mul_of_nonneg_right (hfib p hp) hC
      _ = _ := one_mul _
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := hmem p hp
    exact hmin a ha
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := hmem p hp
    exact hsize a ha
  · set S := (Finset.univ.filter fun X : Set (CTorus d L N₁ m₁ K) =>
      DjModFin m₀ j Ω X ∧ X ⊆ Y ∧ (X ∩ Ω').Nonempty) ×ˢ (patchesIn m₀ (j + 1) Ω' Y).powerset
    have hsub : P ⊆ S := by
      intro p hp
      obtain ⟨a, ha, rfl⟩ := hmem p hp
      obtain ⟨h1, h2, h3⟩ := hX a ha
      exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2, h3⟩,
        Finset.mem_powerset.2 (hJ a ha)⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => (Real.exp_pos _).le).trans
      (sum_exp_assign_le hN hj hΩ hΩ' hΩΩ' hY hκ)

/-- **The entropy constant in exponential form**: `assignEnt d L α b D ≤ A e^{c D}` with
`c = 1 + e^{-b} L^d c₁` and `A = L^d c₁ K₀ e^{c}` (`1 + D ≤ e^{D}`), for `D ≥ 0`. -/
theorem assignEnt_le_exp (α b : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    assignEnt d L α b D ≤ (L : ℝ) ^ d * c1 d L * K0 d L α *
      Real.exp (1 + Real.exp (-b) * ((L : ℝ) ^ d * c1 d L)) *
        Real.exp ((1 + Real.exp (-b) * ((L : ℝ) ^ d * c1 d L)) * D) := by
  unfold assignEnt
  have hc1 := one_le_c1 d L
  have hK := (K0_pos d L α).le
  have hD1 : 1 + D ≤ Real.exp D := by have := Real.add_one_le_exp D; linarith
  have hexp : Real.exp (Real.exp (-b) * ((L : ℝ) ^ d * (c1 d L * (1 + D)))) =
      Real.exp (Real.exp (-b) * ((L : ℝ) ^ d * c1 d L)) *
        Real.exp (Real.exp (-b) * ((L : ℝ) ^ d * c1 d L) * D) := by
    rw [← Real.exp_add]; congr 1; ring
  have hR : Real.exp (1 + Real.exp (-b) * ((L : ℝ) ^ d * c1 d L)) *
      Real.exp ((1 + Real.exp (-b) * ((L : ℝ) ^ d * c1 d L)) * D) =
      Real.exp D * Real.exp 1 * Real.exp (Real.exp (-b) * ((L : ℝ) ^ d * c1 d L)) *
        Real.exp (Real.exp (-b) * ((L : ℝ) ^ d * c1 d L) * D) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [hexp]
  have hpos : 0 ≤ (L : ℝ) ^ d * c1 d L * K0 d L α := by positivity
  have h1e : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  calc (L : ℝ) ^ d * (c1 d L * (1 + D)) * K0 d L α *
        (Real.exp (Real.exp (-b) * ((L : ℝ) ^ d * c1 d L)) *
          Real.exp (Real.exp (-b) * ((L : ℝ) ^ d * c1 d L) * D))
      = ((L : ℝ) ^ d * c1 d L * K0 d L α) * (1 + D) *
          (Real.exp (Real.exp (-b) * ((L : ℝ) ^ d * c1 d L)) *
            Real.exp (Real.exp (-b) * ((L : ℝ) ^ d * c1 d L) * D)) := by ring
    _ ≤ ((L : ℝ) ^ d * c1 d L * K0 d L α) * (Real.exp D * Real.exp 1) *
          (Real.exp (Real.exp (-b) * ((L : ℝ) ^ d * c1 d L)) *
            Real.exp (Real.exp (-b) * ((L : ℝ) ^ d * c1 d L) * D)) := by
        gcongr
        nlinarith [Real.exp_pos D]
    _ = _ := by
        rw [mul_assoc ((L : ℝ) ^ d * c1 d L * K0 d L α)
          (Real.exp (1 + Real.exp (-b) * ((L : ℝ) ^ d * c1 d L)))
          (Real.exp ((1 + Real.exp (-b) * ((L : ℝ) ^ d * c1 d L)) * D)), hR]
        ring

end Balaban.Fluctuation

