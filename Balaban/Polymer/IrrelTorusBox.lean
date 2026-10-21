/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.IrrelBoxTransfer
public import Balaban.SmallField.IrrelTorusDefectExpand
public import Balaban.Fluctuation.LocalClassLabels

/-!
# The torus irrelevant term on two tori

`irrelTorus_boxAgree`: the irrelevant part `ℰ^{(j)}_{irrel}(y, X; Ψ, h)` of the label `(j, y, X)` on the
torus `N₁` (`irrelTorus`) and the one of the image label `(j, boxMap y, boxMap '' X)` on the torus
`N₂` agree, when `X` is a polymer of `𝒟_j` in the centred box, away from the distinguished cell
`□(y)`, and the fields agree under `boxMap` on `X` and on the stencil `y + L^j e_μ`.  The proof
transports every ingredient: the term itself (`E_boxAgree`, the clause `TorusIndep`), its first and
second derivatives at the constant field (`fderiv_E_boxAgree`, `D2_E_boxAgree`), the sums over the
aligned sites of `X` (`sum_blk_boxMap`), the directions `δ_{(block x)} e_i` (`blockDir_boxMap`) and
the integer positions of the blocks (`unlift_sub_of_box`).

For `X = □(y)` the term contains the sum over *all* polymers of `𝒟_j` at `y` of the relevant
parts, which on a finite torus includes the polymers that wrap around it; that sum is not controlled
by the clause `TorusIndep` and is excluded here (`image_eq_cellBox_iff` identifies the case on the two
tori).
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep


open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.RootFSpine Balaban.Multiscale

section Arith

variable {d : ℕ}

theorem valMinAbs_sub_of_box {n r : ℕ} (hm : 2 * (2 * r) + 1 < n) {a b : Torus d n}
    (ha : InBox d r n a) (hb : InBox d r n b) (μ : Fin d) :
    ((a - b) μ).valMinAbs = (a μ).valMinAbs - (b μ).valMinAbs := by
  have e : ((a - b) μ) = (((a μ).valMinAbs - (b μ).valMinAbs : ℤ) : ZMod n) := by
    push_cast
    rfl
  rw [e]
  refine valMinAbs_intCast_of_abs_le (r := 2 * r) hm ?_
  have h1 := ha μ
  have h2 := hb μ
  rw [abs_le] at h1 h2 ⊢
  constructor <;> omega

theorem inBox_sub {n r : ℕ} (hm : 2 * (2 * r) + 1 < n) {a b : Torus d n}
    (ha : InBox d r n a) (hb : InBox d r n b) : InBox d (2 * r) n (a - b) := by
  intro μ
  rw [valMinAbs_sub_of_box hm ha hb μ]
  have h1 := ha μ
  have h2 := hb μ
  rw [abs_le] at h1 h2 ⊢
  constructor <;> omega

theorem boxMap_step {n n' r a : ℕ} {b : Torus d n} (μ : Fin d) (hn : 2 * r + (a + 1) < n)
    (hb : InBox d r n b) (hbw : InBox d r n (b + (a • Pi.single μ 1 : Torus d n))) :
    boxMap n n' (b + (a • Pi.single μ 1 : Torus d n)) =
      boxMap n n' b + (a • Pi.single μ 1 : Torus d n') := by
  have hw : (a • Pi.single μ 1 : Torus d n) = natT (fun ν => if ν = μ then a else 0) := by
    funext ν
    by_cases h : ν = μ
    · subst h; simp [natT]
    · simp [natT, h]
  have hw' : (a • Pi.single μ 1 : Torus d n') = natT (fun ν => if ν = μ then a else 0) := by
    funext ν
    by_cases h : ν = μ
    · subst h; simp [natT]
    · simp [natT, h]
  rw [hw] at hbw ⊢
  rw [hw']
  exact boxMap_add_natT (a := a + 1) hn (fun ν => by
    by_cases h : ν = μ <;> simp [h]) hb hbw

end Arith


section Unlift

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁]

/-- **The centred block coordinate of a site of the box**: the floor quotient of the centred
coordinate. -/
theorem unlift_eq_ediv {j : ℕ} (hj : j ≤ K) {r rc : ℕ} (hrc : r < L ^ j * rc)
    (hc : 2 * rc + 1 < N₁ * L ^ m₁ * L ^ (K - j)) {x : CTorus d L N₁ m₁ K}
    (hx : InBox d r ((N₁ * L ^ m₁) * L ^ K) x) (μ : Fin d) :
    unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) j x μ =
      (x μ).valMinAbs / ((L ^ j : ℕ) : ℤ) := by
  have ha : 0 < L ^ j := pow_pos (NeZero.pos L) j
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = (x μ).valMinAbs := ⟨_, rfl⟩
  have hxμ : x μ = ((ξ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ K)) := by rw [hξ, ZMod.coe_valMinAbs]
  have hξr : |ξ| ≤ r := by rw [hξ]; exact hx μ
  have hq : |ξ / ((L ^ j : ℕ) : ℤ)| ≤ rc := by
    have hapos : (0 : ℤ) < ((L ^ j : ℕ) : ℤ) := by exact_mod_cast ha
    have hrc' : (r : ℤ) < ((L ^ j : ℕ) : ℤ) * rc := by exact_mod_cast hrc
    rw [abs_le] at hξr ⊢
    constructor
    · exact (Int.le_ediv_iff_mul_le hapos).2 (by nlinarith)
    · exact (Int.ediv_lt_iff_lt_mul hapos).2 (by nlinarith) |>.le
  have e1 : jBlock d L (N₁ * L ^ m₁) K j x μ =
      (((ξ / ((L ^ j : ℕ) : ℤ) : ℤ)) : ZMod (N₁ * L ^ m₁ * L ^ (K - j))) := by
    show blockCoord (L ^ j) _ (x μ) = _
    rw [hxμ]
    exact blockCoord_intCast (side_eq hj) ha ξ
  show (jBlock d L (N₁ * L ^ m₁) K j x μ).valMinAbs = _
  rw [e1, valMinAbs_intCast_of_abs_le hc hq, hξ]


theorem unlift_sub_of_box {j : ℕ} (hj : j ≤ K) {R : ℕ}
    (hm : 8 * R + 3 * L ^ K < N₁ * L ^ m₁ * L ^ K) {x y : CTorus d L N₁ m₁ K}
    (hx : InBox d R ((N₁ * L ^ m₁) * L ^ K) x) (hy : InBox d R ((N₁ * L ^ m₁) * L ^ K) y)
    (μ : Fin d) :
    unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) j (x - y) μ =
      ((x μ).valMinAbs - (y μ).valMinAbs) / ((L ^ j : ℕ) : ℤ) := by
  have ha : 0 < L ^ j := pow_pos (NeZero.pos L) j
  have hLK : L ^ j ≤ L ^ K := Nat.pow_le_pow_right (NeZero.pos L) hj
  have hside : N₁ * L ^ m₁ * L ^ K = L ^ j * (N₁ * L ^ m₁ * L ^ (K - j)) := ell_eq (N₁ := N₁) hj
  have hrc : 2 * R < L ^ j * (2 * R / L ^ j + 1) := Nat.lt_mul_div_succ _ ha
  have hmul : L ^ j * (2 * R / L ^ j) ≤ 2 * R := Nat.mul_div_le _ _
  have hc : 2 * (2 * R / L ^ j + 1) + 1 < N₁ * L ^ m₁ * L ^ (K - j) := by
    refine Nat.lt_of_mul_lt_mul_left (a := L ^ j) ?_
    rw [← hside]
    nlinarith
  have hxy := inBox_sub (by omega) hx hy
  rw [unlift_eq_ediv hj (rc := 2 * R / L ^ j + 1) hrc hc hxy μ, valMinAbs_sub_of_box (by omega) hx hy μ]

end Unlift


section Cells

variable {d L N₁ N₂ m₁ K N : ℕ} [NeZero L] [NeZero N₁] [NeZero N₂]

set_option hygiene false in
local notation "n₁" => (N₁ * L ^ m₁) * L ^ K
set_option hygiene false in
local notation "n₂" => (N₂ * L ^ m₁) * L ^ K

/-- The `j`-block of a site of a polymer inside the box is inside the box. -/
theorem block_subset_box {m₀ j : ℕ} (hjK : j ≤ K) (hN₁ : L ^ m₀ ∣ N₁)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : IsPolyDom m₀ j X)
    {z : CTorus d L N₁ m₁ K} (hz : z ∈ X) :
    ∀ y ∈ box (cbase (L ^ j) z) (L ^ j), y ∈ X := by
  intro y hy
  have hd₁ : L ^ j ∣ (N₁ * L ^ m₁) * L ^ K := Dvd.dvd.mul_left (pow_dvd_pow L hjK) _
  exact Balaban.Fluctuation.blockUnion_of_isPolyDom_of_le hN₁ hjK hX z hz y
    (cbase_eq_of_mem_box hd₁ (aligned_cbase z) hy)

theorem aligned_boxMap_iff {a : ℕ} (ha : a ∣ n₁) (ha' : a ∣ n₂) {R : ℕ}
    {x : CTorus d L N₁ m₁ K} (hx : InBox d R n₁ x) (hm : 2 * R + 1 < n₂) :
    Aligned a (boxMap n₁ n₂ x) ↔ Aligned a x := by
  refine ⟨fun h => ?_, aligned_boxMap ha ha'⟩
  have := aligned_boxMap ha' ha h
  rwa [boxMap_boxMap hm hx] at this


/-- **The directions `δ_{(block x)} e_i` correspond under `boxMap`** on the polymer. -/
theorem blockDir_boxMap {m₀ j : ℕ} (hjK : j ≤ K) (hN₁ : L ^ m₀ ∣ N₁)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : IsPolyDom m₀ j X) {R : ℕ}
    (hXR : ∀ x ∈ X, InBox d R n₁ x) (hm₁ : 2 * R + L ^ j < n₁) (hm₂ : 2 * R + 1 < n₂)
    {x : CTorus d L N₁ m₁ K} (hxX : x ∈ X) (i : Fin N) {z : CTorus d L N₁ m₁ K} (hz : z ∈ X) :
    blockDir (N₁ := N₂) (m₁ := m₁) (k := K) (N := N) L j (boxMap n₁ n₂ x) i (boxMap n₁ n₂ z) =
      blockDir (N₁ := N₁) (m₁ := m₁) (k := K) (N := N) L j x i z := by
  classical
  have hd₁ : L ^ j ∣ n₁ := Dvd.dvd.mul_left (pow_dvd_pow L hjK) _
  have hd₂ : L ^ j ∣ n₂ := Dvd.dvd.mul_left (pow_dvd_pow L hjK) _
  have hcb : boxMap n₁ n₂ (cbase (L ^ j) z) = cbase (L ^ j) (boxMap n₁ n₂ z) :=
    cbase_boxMap hd₁ hd₂ (pow_pos (NeZero.pos L) j) hm₁ z
      (fun y hy => hXR y (block_subset_box hjK hN₁ hX hz y hy))
  have hcz : InBox d R n₁ (cbase (L ^ j) z) :=
    hXR _ (block_subset_box hjK hN₁ hX hz _ (mem_box_self _ (pow_pos (NeZero.pos L) j)))
  have hiff : cbase (L ^ j) (boxMap n₁ n₂ z) = boxMap n₁ n₂ x ↔ cbase (L ^ j) z = x := by
    rw [← hcb]
    exact ⟨fun h => boxMap_inj (hm' := hm₂) hcz (hXR x hxX) h, fun h => by rw [h]⟩
  funext i'
  simp only [blockDir, hiff]


open Classical in
/-- **The sum over the aligned sites of the image of a polymer** is the sum over the aligned sites
of the polymer. -/
theorem sum_blk_boxMap {j : ℕ} (hjK : j ≤ K) {X : Set (CTorus d L N₁ m₁ K)} {R : ℕ}
    (hXR : ∀ x ∈ X, InBox d R n₁ x) (hm₂ : 2 * R + 1 < n₂)
    (hinj : Set.InjOn (boxMap n₁ n₂) X) (F : CTorus d L N₂ m₁ K → ℂ) :
    ∑ x' ∈ Finset.univ.filter (fun x' => Aligned (L ^ j) x' ∧ x' ∈ boxMap n₁ n₂ '' X), F x' =
      ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X), F (boxMap n₁ n₂ x) := by
  have hd₁ : L ^ j ∣ n₁ := Dvd.dvd.mul_left (pow_dvd_pow L hjK) _
  have hd₂ : L ^ j ∣ n₂ := Dvd.dvd.mul_left (pow_dvd_pow L hjK) _
  have himg : Finset.univ.filter (fun x' => Aligned (L ^ j) x' ∧ x' ∈ boxMap n₁ n₂ '' X) =
      (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image (boxMap n₁ n₂) := by
    ext x'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨ha, x, hx, rfl⟩
      exact ⟨x, ⟨(aligned_boxMap_iff hd₁ hd₂ (hXR x hx) hm₂).1 ha, hx⟩, rfl⟩
    · rintro ⟨x, ⟨ha, hx⟩, rfl⟩
      exact ⟨(aligned_boxMap_iff hd₁ hd₂ (hXR x hx) hm₂).2 ha, x, hx, rfl⟩
  rw [himg, Finset.sum_image]
  intro a ha b hb hab
  exact hinj (Finset.mem_filter.1 ha).2.2 (Finset.mem_filter.1 hb).2.2 hab


/-- **The distinguished cell `□(y)` of the torus irrelevant term goes to the distinguished cell of
the image** (inside the box): `boxMap '' □(y) = □(boxMap y)`, and a polymer `X` is `□(y)` iff its
image is `□(boxMap y)`. -/
theorem image_eq_cellBox_iff {m₀ j : ℕ} (hjK : j ≤ K) (hN₁ : L ^ m₀ ∣ N₁) (hN₂ : L ^ m₀ ∣ N₂)
    {R : ℕ} (hm₁ : 2 * R + L * cellSide L m₀ m₁ j < n₁) (hm₂ : 2 * R + 1 < n₂)
    {y : CTorus d L N₁ m₁ K}
    (hcell : ∀ z ∈ box (cbase (cellSide L m₀ m₁ j) y -
      natT (fun _ => L / 2 * cellSide L m₀ m₁ j)) (L * cellSide L m₀ m₁ j),
      InBox d R n₁ z)
    {X : Set (CTorus d L N₁ m₁ K)} (hXR : ∀ x ∈ X, InBox d R n₁ x) :
    boxMap n₁ n₂ '' X = box (cbase (cellSide L m₀ m₁ j) (boxMap n₁ n₂ y) -
      natT (fun _ => L / 2 * cellSide L m₀ m₁ j)) (L * cellSide L m₀ m₁ j) ↔
    X = box (cbase (cellSide L m₀ m₁ j) y - natT (fun _ => L / 2 * cellSide L m₀ m₁ j))
      (L * cellSide L m₀ m₁ j) := by
  set cs := cellSide L m₀ m₁ j with hcs
  set w : Fin d → ℕ := fun _ => L / 2 * cs with hw
  set c₁ : CTorus d L N₁ m₁ K := cbase cs y - natT w with hc₁
  have hcs0 : 0 < cs := cellSide_pos m₀ m₁ j
  have hLcs : 0 < L * cs := Nat.mul_pos (NeZero.pos L) hcs0
  have hd₁ : cs ∣ n₁ := cellSide_dvd hN₁ hjK
  have hd₂ : cs ∣ n₂ := cellSide_dvd hN₂ hjK
  have hwlt : ∀ μ, w μ < L * cs := fun μ => by
    simp only [hw]
    exact Nat.mul_lt_mul_of_pos_right (Nat.div_lt_self (NeZero.pos L) (by omega)) hcs0
  have hbw : c₁ + natT w = cbase cs y := by simp only [hc₁]; abel
  have hb : InBox d R n₁ c₁ := hcell c₁ (mem_box_self c₁ hLcs)
  have hbw' : InBox d R n₁ (c₁ + natT w) := hcell _ (mem_box_add c₁ hwlt)
  have hstep := boxMap_add_natT (n' := N₂ * L ^ m₁ * L ^ K) (r := R) (a := L * cs) hm₁ hwlt hb hbw'
  -- the cell of `y` is inside the cell box
  have hcellsub : ∀ z ∈ box (cbase cs y) cs, InBox d R n₁ z := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hz
    refine hcell _ ⟨fun μ => w μ + v μ, fun μ => ?_, ?_⟩
    · have := hv μ
      have h2 : L / 2 + 1 ≤ L := by
        have := NeZero.pos L; omega
      have : (L / 2 + 1) * cs ≤ L * cs := Nat.mul_le_mul_right _ h2
      simp only [hw]
      nlinarith
    · show cbase cs y + natT v = c₁ + natT (w + v)
      rw [natT_add, ← add_assoc, hbw]
  have hcb : boxMap n₁ n₂ (cbase cs y) = cbase cs (boxMap n₁ n₂ y) :=
    cbase_boxMap hd₁ hd₂ hcs0 (by nlinarith [Nat.le_mul_of_pos_left cs (NeZero.pos L)]) y hcellsub
  have hbm : boxMap n₁ n₂ c₁ = cbase cs (boxMap n₁ n₂ y) -
      natT (fun _ => L / 2 * cs) := by
    rw [← hcb, ← hbw, hstep]; simp [hw]
  have himg : boxMap n₁ n₂ '' box c₁ (L * cs) = box (cbase cs (boxMap n₁ n₂ y) -
      natT (fun _ => L / 2 * cs)) (L * cs) := by
    rw [image_box_boxMap hm₁ hLcs hcell, hbm]
  have hinj : Set.InjOn (boxMap n₁ n₂) {z | InBox d R n₁ z} := fun a ha b hb hab =>
    boxMap_inj (hm' := hm₂) ha hb hab
  rw [← himg]
  exact ⟨fun h => ((hinj.image_eq_image_iff hXR hcell).1 h), fun h => by rw [h]⟩

end Cells

section Main

variable {d L N₁ N₂ m₁ K N : ℕ} [NeZero L] [NeZero N₁] [NeZero N₂] {ϱ : ℝ}

set_option hygiene false in
local notation "n₁" => (N₁ * L ^ m₁) * L ^ K
set_option hygiene false in
local notation "n₂" => (N₂ * L ^ m₁) * L ^ K
set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K)

open Classical in
/-- **The torus irrelevant term on two tori** (P1 (3.112)-(3.113), P4 (H.4)): away from the
distinguished cell `□(y)`, `ℰ_irrel^{(j)}(y, X; Ψ, h)` agrees with the term of the image polymer on the
second torus when the fields agree under `boxMap` on `X` and on the stencil `y + L^j e_μ`. -/
theorem irrelTorus_boxAgree {Tm : ∀ (M : ℕ) [NeZero M], Terms d L M m₁ K N ϱ} {m₀ j : ℕ}
    (hj1 : 1 ≤ j) (hjK : j ≤ K) (hT : TorusIndep m₀ Tm)
    (hlocB : ∀ j y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      (Tm N₂).E j y X Ψ h = (Tm N₂).E j y X Ψ' h')
    (hN₁ : L ^ m₀ ∣ N₁) (hN₂ : L ^ m₀ ∣ N₂) (hM8 : 8 ≤ L ^ (m₀ + m₁)) {R : ℕ}
    (hmar₁ : 8 * R + 3 * L ^ K + L * cellSide L m₀ m₁ j < n₁)
    (hmar₂ : 8 * R + 3 * L ^ K + L * cellSide L m₀ m₁ j < n₂)
    {y : CTorus d L N₁ m₁ K} {X : Set (CTorus d L N₁ m₁ K)} (hy : Aligned (L ^ j) y) (hyX : y ∈ X)
    (hX : IsPolyDom m₀ j X) (hXR : ∀ x ∈ X, InBox d R n₁ x)
    (hstep : ∀ μ : Fin d, InBox d R n₁ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ K)))
    (hcell : ∀ z ∈ box (cbase (cellSide L m₀ m₁ j) y -
      natT (fun _ => L / 2 * cellSide L m₀ m₁ j)) (L * cellSide L m₀ m₁ j), InBox d R n₁ z)
    (hne : X ≠ box (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j)
      (L * cellSide L m₀ m₁ j))
    (i₀ i₁ : Fin N) (Ψ h : Fld d L N₁ m₁ K N) (Ψ' h' : Fld d L N₂ m₁ K N)
    (hΨ : ∀ x ∈ X, Ψ' (bm x) = Ψ x)
    (hΨst : ∀ μ : Fin d, Ψ' (bm (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ K))) =
      Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ K)))
    (hh : ∀ x ∈ X, h' (bm x) = h x) :
    irrelTorus m₀ (Tm N₂) i₀ i₁ j (bm y) (bm '' X) Ψ' h' = irrelTorus m₀ (Tm N₁) i₀ i₁ j y X Ψ h := by
  have hLK : 0 < L ^ K := pow_pos (NeZero.pos L) K
  have hR₁ : 4 * R < n₁ := by omega
  have hR₂ : 4 * R < n₂ := by omega
  have hm₁ : 2 * R + L * cellSide L m₀ m₁ j < n₁ := by omega
  have hm₂ : 2 * R + 1 < n₂ := by omega
  have hm₁' : 2 * R + L ^ j < n₁ := by
    have : L ^ j ≤ L ^ K := Nat.pow_le_pow_right (NeZero.pos L) hjK
    omega
  have hne' : bm '' X ≠ box (cbase (cellSide L m₀ m₁ j) (bm y) -
      natT fun _ => L / 2 * cellSide L m₀ m₁ j) (L * cellSide L m₀ m₁ j) := fun h =>
    hne ((image_eq_cellBox_iff hjK hN₁ hN₂ (R := R) hm₁ hm₂ hcell hXR).1 h)
  have hinj := boxMap_injOn_of_box (X := X) hN₂ hM8 hR₂ hXR
  rw [irrelTorus_eq_expanded_filed, irrelTorus_eq_expanded_filed]
  simp only [hne, hne', ite_false, add_zero]
  simp only [sum_blk_boxMap hjK hXR hm₂ hinj]
  have hy1 : Ψ' (bm y) = Ψ y := hΨ y hyX
  have hy2 : h' (bm y) = h y := hh y hyX
  have hLj : L ^ j ≤ L ^ K := Nat.pow_le_pow_right (NeZero.pos L) hjK
  have hst : ∀ μ : Fin d, Ψ' (bm y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₂ m₁ K)) =
      Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ K)) := fun μ => by
    rw [← boxMap_step (a := L ^ j) μ (by omega) (hXR y hyX) (hstep μ)]
    exact hΨst μ
  have alg : ∀ (A A' B B' c c' S S' e e' H H' Q Q' S3 S3' : ℂ), A = A' → B = B' → c = c' →
      S = S' → e = e' → H = H' → Q = Q' → S3 = S3' →
      A - (B + c * S + e * H - 1 / 4 * Q) - 1 / 2 * S3 =
        A' - (B' + c' * S' + e' * H' - 1 / 4 * Q') - 1 / 2 * S3' := by
    intros; subst_vars; rfl
  have hE := fun (Ψ h : Fld d L N₁ m₁ K N) (Ψ' h' : Fld d L N₂ m₁ K N) hΨ hh =>
    E_boxAgree hj1 hjK hT hlocB hN₁ hN₂ hM8 hR₁ hR₂ hy hyX hX hXR Ψ h Ψ' h' hΨ hh
  have hconst : ∀ (i : Fin N), ∀ x ∈ X, (constFld (Pi.single i 1) : Fld d L N₂ m₁ K N) (bm x) =
      (constFld (Pi.single i 1) : Fld d L N₁ m₁ K N) x := fun _ _ _ => rfl
  have hDer : ∀ x ∈ X, ∀ i : Fin N,
      (fderiv ℂ (fun Ψ' => (Tm N₂).E j (bm y) (bm '' X) Ψ' (constFld (Pi.single i₀ 1)))
        (constFld (Pi.single i₀ 1))) (blockDir L j (bm x) i) =
      (fderiv ℂ (fun Ψ' => (Tm N₁).E j y X Ψ' (constFld (Pi.single i₀ 1)))
        (constFld (Pi.single i₀ 1))) (blockDir L j x i) := fun x hx i =>
    (fderiv_E_boxAgree hj1 hjK hT hlocB hN₁ hN₂ hM8 hR₁ hR₂ hy hyX hX hXR _ _
      (hconst i₀) (hconst i₀) (fun z hz => blockDir_boxMap hjK hN₁ hX hXR hm₁' hm₂ hx i hz)).symm
  have hD2 : ∀ x ∈ X, ∀ x' ∈ X, ∀ i : Fin N,
      Balaban.SmallField.D2 (fun Ψ' => (Tm N₂).E j (bm y) (bm '' X) Ψ' (constFld (Pi.single i₀ 1)))
        (constFld (Pi.single i₀ 1)) (blockDir L j (bm x) i) (blockDir L j (bm x') i) =
      Balaban.SmallField.D2 (fun Ψ' => (Tm N₁).E j y X Ψ' (constFld (Pi.single i₀ 1)))
        (constFld (Pi.single i₀ 1)) (blockDir L j x i) (blockDir L j x' i) := fun x hx x' hx' i =>
    (D2_E_boxAgree hj1 hjK hT hlocB hN₁ hN₂ hM8 hR₁ hR₂ hy hyX hX hXR _ _
      (hconst i₀) (hconst i₀) (fun z hz => blockDir_boxMap hjK hN₁ hX hXR hm₁' hm₂ hx i hz)
      (fun z hz => blockDir_boxMap hjK hN₁ hX hXR hm₁' hm₂ hx' i hz)).symm
  have hUn : ∀ x ∈ X, ∀ μ : Fin d, unlift (L := L) (N₁ := N₂) (m₁ := m₁) (k := K) j (bm x - bm y) μ =
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) j (x - y) μ := fun x hx μ => by
    rw [unlift_sub_of_box hjK (by omega) (inBox_boxMap hm₂ (hXR x hx))
      (inBox_boxMap hm₂ (hXR y hyX)) μ, unlift_sub_of_box hjK (by omega) (hXR x hx) (hXR y hyX) μ,
      valMinAbs_boxMap hm₂ (hXR x hx), valMinAbs_boxMap hm₂ (hXR y hyX)]
  refine alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hE Ψ h Ψ' h' hΨ hh
  · exact hE _ _ _ _ (hconst i₀) (hconst i₀)
  · rw [hy1]
  · exact Finset.sum_congr rfl fun x hx => hDer x (Finset.mem_filter.1 hx).2.2 i₀
  · rw [hy1, hy2]
  · exact (fderiv_E_boxAgree_h hj1 hjK hT hlocB hN₁ hN₂ hM8 hR₁ hR₂ hy hyX hX hXR _ _
      (hconst i₀) (hconst i₀) (hconst i₀)).symm
  · refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun μ' _ => ?_
    rw [hy1, hst, hst]
    congr 1
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun x' hx' => ?_
    have hx2 := (Finset.mem_filter.1 hx).2.2
    have hx3 := (Finset.mem_filter.1 hx').2.2
    rw [hD2 x hx2 x' hx3 i₁, hUn x hx2 μ, hUn x' hx3 μ, hUn x hx2 μ', hUn x' hx3 μ']
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hx2 := (Finset.mem_filter.1 hx).2.2
    rw [hDer x hx2 i₀, hΨ x hx2, hy1]

end Main

end Balaban.Polymer.TwoTorusStep
