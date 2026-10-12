/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledClose
public import Balaban.Localization.BoxConn

/-!
# (DG5), (DG5'): locality in terms of the parameters

* `inBox_half_iff_sameCell`: the `π¹`-cube of a centre is the box of half-width `M₁ ℓ_j / 2`;
  it is a union of cells, lies in `Ω₁` and is connected;
* `dg5`: (DG5) `G_s(A) f = 0` off `Core(ℛ)` and `G_s(A) f` on a nearest-neighbour component `Y'` of
  `Y(ℛ)` only depends on `f|_{Y'}`, `A|_{Y'}`, `s`;
* `dg5'`: (DG5') the termwise comparison for `s, s'` vanishing off `𝒞`.

Both rest on `Gs_local` and on the connectedness of the thickened interaction cubes inside `Ω₁`
(`HatConn`; automatic when `□̂_z ⊂ Ω₁`, a hypothesis on the generating set for layer-1 centres).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ}

/-- One coordinate of the half-width box. -/
theorem abs_lt_half_cell_iff {B : ℝ} (hB : 1 ≤ B) (m : ℤ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ B - 1) :
    |B * m + (r - (B - 1) / 2)| < 1 / 2 * B ↔ m = 0 := by
  constructor
  · intro h
    rw [abs_lt] at h
    by_contra hm
    rcases lt_or_gt_of_ne hm with hlt | hgt
    · have : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
      nlinarith [h.1, h.2]
    · have : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      nlinarith [h.1, h.2]
  · rintro rfl
    simp only [Int.cast_zero, mul_zero, zero_add]
    rw [abs_lt]
    constructor <;> nlinarith

theorem inBox_half_iff_sameCell {j : ℕ} (hj : j ≤ K) {y0 x : CTorus d L N₁ m₁ K}
    (hb : CubeBase m₁ j y0) :
    InBox m₁ j y0 (1 / 2 * (L : ℝ) ^ (j + m₁)) x ↔ SameCell (L ^ (j + m₁)) x y0 := by
  refine forall_congr' fun μ => ?_
  have hBpos : 0 < L ^ (j + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  obtain ⟨n, hn⟩ := pow_dvd_torusSide (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) j hj
  set B : ℕ := L ^ (j + m₁) with hBdef
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBpos
  have hBr : ((L : ℝ) ^ (j + m₁)) = (B : ℝ) := by rw [hBdef]; push_cast; rfl
  set a : ℕ := (x μ).val / B with ha
  set r : ℕ := (x μ).val % B with hr
  set b : ℕ := (y0 μ).val / B with hbdef
  have hx : (x μ).val = B * a + r := (Nat.div_add_mod _ _).symm
  have hy : (y0 μ).val = B * b := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hb μ))).symm
  have hrB : r < B := Nat.mod_lt _ hBpos
  have hNr : (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) = (B : ℝ) * n := by
    rw [hn]; push_cast; ring
  have hxr : ((x μ).val : ℝ) = (B : ℝ) * a + r := by exact_mod_cast hx
  have hyr : ((y0 μ).val : ℝ) = (B : ℝ) * b := by exact_mod_cast hy
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hr1 : (r : ℝ) ≤ B - 1 := by
    have : r + 1 ≤ B := hrB
    have : ((r + 1 : ℕ) : ℝ) ≤ B := by exact_mod_cast this
    push_cast at this; linarith
  have hxlt : (x μ).val < (N₁ * L ^ m₁) * L ^ K := ZMod.val_lt _
  have hylt : (y0 μ).val < (N₁ * L ^ m₁) * L ^ K := ZMod.val_lt _
  have hxlt' : (x μ).val < B * n := lt_of_lt_of_eq hxlt hn
  have hylt' : (y0 μ).val < B * n := lt_of_lt_of_eq hylt hn
  have han : a < n := (Nat.div_lt_iff_lt_mul hBpos).2 (by rw [Nat.mul_comm n B]; exact hxlt')
  have hbn : b < n := (Nat.div_lt_iff_lt_mul hBpos).2 (by rw [Nat.mul_comm n B]; exact hylt')
  have hai : (a : ℤ) < n := by exact_mod_cast han
  have hbi : (b : ℤ) < n := by exact_mod_cast hbn
  have ha0 : (0 : ℤ) ≤ a := Nat.cast_nonneg _
  have hb0 : (0 : ℤ) ≤ b := Nat.cast_nonneg _
  constructor
  · rintro ⟨p, hp⟩
    have e : ((x μ).val : ℝ) + p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
        (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2) =
        (B : ℝ) * ((a : ℤ) - (b : ℤ) + p * (n : ℤ) : ℤ) + ((r : ℝ) - ((B : ℝ) - 1) / 2) := by
      rw [hNr, hxr, hyr, hBr]; push_cast; ring
    rw [e, hBr, abs_lt_half_cell_iff hB1 _ hr0 hr1] at hp
    have h1 : (n : ℤ) ∣ (a : ℤ) - b := ⟨-p, by linarith⟩
    have h2 : |(a : ℤ) - b| < n := by
      rw [abs_lt]; constructor <;> linarith
    have h3 := Int.eq_zero_of_abs_lt_dvd h1 h2
    show a = b
    have : (a : ℤ) = b := by linarith
    exact_mod_cast this
  · intro h
    have hab : a = b := h
    refine ⟨0, ?_⟩
    have e : ((x μ).val : ℝ) + ((0 : ℤ) : ℝ) * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
        (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2) =
        (B : ℝ) * ((a : ℤ) - (b : ℤ) + (0 : ℤ) * (n : ℤ) : ℤ) + ((r : ℝ) - ((B : ℝ) - 1) / 2) := by
      rw [hxr, hyr, hBr]; push_cast; ring
    rw [e, hBr, abs_lt_half_cell_iff hB1 _ hr0 hr1]
    rw [hab]; ring

/-! ### Cubes, thickened cubes, components -/

open Classical in
/-- The `π¹`-cube of the centre `q`: the cell of side `M₁ ℓ_j` containing its base. -/
noncomputable def cubeP (q : ℕ × CTorus d L N₁ m₁ K) : Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun x => SameCell (L ^ (q.1 + m₁)) x q.2

theorem mem_cubeP {q : ℕ × CTorus d L N₁ m₁ K} {x : CTorus d L N₁ m₁ K} :
    x ∈ cubeP q ↔ SameCell (L ^ (q.1 + m₁)) x q.2 := by
  classical
  simp [cubeP]

/-- The thickened interaction cube `□̂_z`. -/
noncomputable def hatBox (q : ℕ × CTorus d L N₁ m₁ K) : Finset (CTorus d L N₁ m₁ K) :=
  boxSet m₁ q.1 q.2 (hatRad L m₁ q.1)

/-- The cube `C_z` of the support of `χ_z`. -/
noncomputable def coreBox (q : ℕ × CTorus d L N₁ m₁ K) : Finset (CTorus d L N₁ m₁ K) :=
  boxSet m₁ q.1 q.2 (3 / 2 * (L : ℝ) ^ (q.1 + m₁))

theorem box_subset_hatBox (q : ℕ × CTorus d L N₁ m₁ K) : intBox q ⊆ hatBox q := by
  intro x hx
  unfold hatBox
  rw [mem_boxSet]
  refine (mem_intBox.1 hx).mono ?_
  unfold hatRad
  have : (0 : ℝ) ≤ 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ q.1 := by positivity
  linarith

theorem coreBox_subset_box {q : ℕ × CTorus d L N₁ m₁ K} :
    coreBox q ⊆ intBox q := by
  intro x hx
  unfold coreBox at hx
  rw [mem_boxSet] at hx
  rw [mem_intBox]
  refine hx.mono ?_
  have : (0 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := by positivity
  linarith

/-- Nearest-neighbour connectedness inside the finite set `S`. -/
def ConnIn (S : Finset (CTorus d L N₁ m₁ K)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, Relation.ReflTransGen (stepIn S) x y

/-- `Y'` is a union of nearest-neighbour components of `Z`. -/
def IsNnComp (Z Y' : Finset (CTorus d L N₁ m₁ K)) : Prop :=
  Y' ⊆ Z ∧ ∀ x ∈ Y', ∀ y ∈ Z, Adj x y → y ∈ Y'

omit [NeZero N₁] [NeZero L] in
/-- **A connected set inside `Z` lies in a component or is disjoint from it.** -/
theorem connIn_dichotomy {S Z Y' : Finset (CTorus d L N₁ m₁ K)} (hS : ConnIn S) (hSZ : S ⊆ Z)
    (hY : IsNnComp Z Y') : S ⊆ Y' ∨ Disjoint S Y' := by
  by_cases h : ∃ x ∈ S, x ∈ Y'
  · left
    obtain ⟨x, hxS, hxY⟩ := h
    have key : ∀ y, Relation.ReflTransGen (stepIn S) x y → y ∈ Y' := by
      intro y hp
      induction hp with
      | refl => exact hxY
      | tail _ hstep ih =>
        obtain ⟨-, hb, hadj⟩ := hstep
        exact hY.2 _ ih _ (hSZ hb) hadj
    intro y hy
    exact key y (hS x hxS y hy)
  · right
    rw [Finset.disjoint_left]
    intro x hxS hxY
    exact h ⟨x, hxS, hxY⟩

theorem cubeP_eq_boxSet {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) :
    cubeP q = boxSet m₁ q.1 q.2 (1 / 2 * (L : ℝ) ^ (q.1 + m₁)) := by
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  ext x
  rw [mem_cubeP, mem_boxSet, inBox_half_iff_sameCell hmK hb]

theorem cubeP_subset_Ω (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ cubeP q) : x ∈ G.Ω 1 := by
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  have hxl : x ∈ G.layer q.1 :=
    (S.aligned.mem_layer_iff hm1 hmK (mem_cubeP.1 (by exact hx) |>.mono
      (pow_dvd_pow L (by omega : q.1 + m₁ ≤ q.1 + m₁)))).2 hl
  exact G.layer_subset hm1 hmK hxl

theorem cubeP_connIn (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) :
    ConnIn (cubeP q) := by
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  rw [cubeP_eq_boxSet hq]
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
  have hB : (2 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := by
    calc (2 : ℝ) ≤ L := by linarith
      _ = (L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (L : ℝ) ^ (q.1 + m₁) := pow_le_pow_right₀ (by linarith) (by omega)
  exact boxSet_connected q.2 (by linarith)

/-! ### (DG5) -/

open Classical in
/-- The sites of `□̂_z` that lie in `Ω₁`. -/
noncomputable def hatI (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (q : ℕ × CTorus d L N₁ m₁ K) :
    Finset (CTorus d L N₁ m₁ K) := (hatBox q).filter fun x => x ∈ G.Ω 1

/-- The thickened interaction cubes are nearest-neighbour connected inside `Ω₁` (automatic if
`□̂_z ⊂ Ω₁`; a regularity condition on the generating set at layer 1). -/
def HatConn (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) : Prop :=
  ∀ q ∈ cubeIdx G, ConnIn (hatI G q)

open Classical in
/-- `Z_ℛ = {z : 𝒬(z) ∩ ℛ = ∅}`, `ℛ = {P : s_P = 0}` (`sProd_ne_zero_iff`). -/
noncomputable def Zs (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (s : ℕ × CTorus d L N₁ m₁ K → ℂ) : Finset (ℕ × CTorus d L N₁ m₁ K) :=
  (cubeIdx G).filter fun z => sProd G s z ≠ 0

open Classical in
/-- `Y(ℛ) ∩ Ω₁`, `Y(ℛ) = ⋃_{z ∈ Z_ℛ} □̂_z`. -/
noncomputable def Yreg (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (s : ℕ × CTorus d L N₁ m₁ K → ℂ) : Finset (CTorus d L N₁ m₁ K) :=
  ((Zs G s).biUnion hatBox).filter fun x => x ∈ G.Ω 1

/-- `Core(ℛ) = ⋃_{z ∈ Z_ℛ} C_z`. -/
noncomputable def Core (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (s : ℕ × CTorus d L N₁ m₁ K → ℂ) : Finset (CTorus d L N₁ m₁ K) :=
  (Zs G s).biUnion coreBox

theorem sProd_ne_zero_iff (s : ℕ × CTorus d L N₁ m₁ K → ℂ) (z : ℕ × CTorus d L N₁ m₁ K) :
    sProd G s z ≠ 0 ↔ ∀ P ∈ Qset G z, s P ≠ 0 := by
  unfold sProd
  rw [Finset.prod_ne_zero_iff]

/-- **(DG5), support.** `G_s(A) f` vanishes outside `Core(ℛ)`. -/
theorem dg5_support (s : ℕ × CTorus d L N₁ m₁ K → ℂ) (f : G.Ω 1 → ℂ) (x : G.Ω 1)
    (hx : (Gs G a ν α s *ᵥ f) x ≠ 0) : (x : CTorus d L N₁ m₁ K) ∈ Core G s := by
  classical
  set g : G.Ω 1 → ℂ := (1 - Kcal G a ν α s)⁻¹ *ᵥ f with hg
  have e : Gs G a ν α s *ᵥ f = Gstar G a ν α s *ᵥ g := by
    rw [hg, Gs, ← Matrix.mulVec_mulVec]
  rw [e] at hx
  have h1 : zeroExt (G.Ω 1) (Gstar G a ν α s *ᵥ g) x ≠ 0 := by
    rw [zeroExt_of_mem' x.2]; exact hx
  rw [Gstar_apply] at h1
  obtain ⟨q, hq, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  have hc : sProd G s q ≠ 0 := left_ne_zero_of_mul hne
  have hchi : ((chi G q x : ℝ) : ℂ) ≠ 0 := by
    have := right_ne_zero_of_mul hne
    exact left_ne_zero_of_mul this
  have hchi' : chi G q x ≠ 0 := fun h0 => hchi (by simp [h0])
  unfold Core
  rw [Finset.mem_biUnion]
  refine ⟨q, Finset.mem_filter.2 ⟨hq, hc⟩, ?_⟩
  unfold coreBox
  rw [mem_boxSet]
  exact inBox_of_chi_ne_zero hchi'

/-- **(DG5), locality on a nearest-neighbour component.** -/
theorem dg5_local (S : DGSetting G a ν) (hconn : HatConn G) {α α' : G.Ω 1 → ℂ} (hα : AdmPot G α)
    (hα' : AdmPot G α') {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hU : IsUnit (1 - Kcal G a ν α s)) (hU' : IsUnit (1 - Kcal G a ν α' s))
    {Y' : Finset (CTorus d L N₁ m₁ K)} (hY : IsNnComp (Yreg G s) Y')
    (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' → α x = α' x)
    {f f' : G.Ω 1 → ℂ} (hf : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' → f x = f' x) :
    ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' →
      (Gs G a ν α s *ᵥ f) x = (Gs G a ν α' s *ᵥ f') x := by
  classical
  refine Gs_local S hα hα' hU hU' ?_ (fun _ _ _ => rfl) hA hf
  intro z hz hact
  have hzs : sProd G s z ≠ 0 := by rcases hact with h | h <;> exact h
  have hzZ : z ∈ Zs G s := Finset.mem_filter.2 ⟨hz, hzs⟩
  have hsub : hatI G z ⊆ Yreg G s := by
    intro x hx
    unfold hatI at hx
    rw [Finset.mem_filter] at hx
    unfold Yreg
    rw [Finset.mem_filter, Finset.mem_biUnion]
    exact ⟨⟨z, hzZ, hx.1⟩, hx.2⟩
  rcases connIn_dichotomy (hconn z hz) hsub hY with h | h
  · left
    intro x hx
    exact h (by
      unfold hatI
      rw [Finset.mem_filter]
      exact ⟨box_subset_hatBox z hx, x.2⟩)
  · right
    intro x hx hxY
    exact Finset.disjoint_left.1 h (by
      unfold hatI
      rw [Finset.mem_filter]
      exact ⟨box_subset_hatBox z hx, x.2⟩) hxY

/-! ### (DG5') -/

open Classical in
/-- The parameter cubes `𝔓`: the cubes of the cover that are not contained in `X₁`. -/
noncomputable def parCubes (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (X₁ : Finset (CTorus d L N₁ m₁ K)) : Finset (ℕ × CTorus d L N₁ m₁ K) :=
  (cubeIdx G).filter fun q => ¬ cubeP q ⊆ X₁

/-- `V(𝒞) = X₁ ∪ ⋃_{P ∈ 𝒞} P`. -/
noncomputable def Vset (X₁ : Finset (CTorus d L N₁ m₁ K)) (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)) :
    Finset (CTorus d L N₁ m₁ K) := X₁ ∪ 𝒞.biUnion cubeP

open Classical in
/-- `Z_Y = {z : 𝒬(z) ∩ 𝔓 ⊂ 𝒞, □̂_z ⊂ Y}`. -/
noncomputable def ZY (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (X₁ : Finset (CTorus d L N₁ m₁ K))
    (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)) (Y : Finset (CTorus d L N₁ m₁ K)) :
    Finset (ℕ × CTorus d L N₁ m₁ K) :=
  (cubeIdx G).filter fun z =>
    (∀ P ∈ Qset G z, P ∈ parCubes G X₁ → P ∈ 𝒞) ∧ SubI G (hatBox z) Y

/-- **(DG5'), termwise comparison.**  Let `𝒞 ⊂ cubeIdx`, `Y` a union of nearest-neighbour
components of `V(𝒞) ∩ Ω₁`; `s, s'` equal to `1` off `𝔓` and `0` on `𝔓 ∖ 𝒞`, agreeing on the cubes of
`𝒞` inside `Y`; `A = A'`, `f = f'` on `Y`.  Then `G_s(A) f = G_{s'}(A') f'` on
`Core_Y = ⋃_{z ∈ Z_Y} C_z`. -/
theorem dg5' (S : DGSetting G a ν) (hconn : HatConn G) {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1) Y)
    {α α' : G.Ω 1 → ℂ} (hα : AdmPot G α) (hα' : AdmPot G α')
    {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hU : IsUnit (1 - Kcal G a ν α s)) (hU' : IsUnit (1 - Kcal G a ν α' s'))
    (hs1 : ∀ P ∈ cubeIdx G, P ∉ parCubes G X₁ → s P = 1 ∧ s' P = 1)
    (hs0 : ∀ P ∈ parCubes G X₁, P ∉ 𝒞 → s P = 0 ∧ s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI G (cubeP P) Y → s P = s' P)
    (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → α x = α' x)
    {f f' : G.Ω 1 → ℂ} (hf : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → f x = f' x) :
    ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ (ZY G X₁ 𝒞 Y).biUnion coreBox →
      (Gs G a ν α s *ᵥ f) x = (Gs G a ν α' s' *ᵥ f') x := by
  classical
  -- active centres only see parameter cubes of `𝒞`
  have hact : ∀ (u : ℕ × CTorus d L N₁ m₁ K → ℂ), (∀ P ∈ parCubes G X₁, P ∉ 𝒞 → u P = 0) →
      ∀ z, sProd G u z ≠ 0 → ∀ P ∈ Qset G z, P ∈ parCubes G X₁ → P ∈ 𝒞 := by
    intro u hu z hz P hP hPP
    by_contra hPC
    exact (sProd_ne_zero_iff u z |>.1 hz) P hP (hu P hPP hPC)
  -- the thickened cube of an active centre lies in `V(𝒞) ∩ Ω₁`
  have hhat : ∀ z ∈ cubeIdx G, (∀ P ∈ Qset G z, P ∈ parCubes G X₁ → P ∈ 𝒞) →
      hatI G z ⊆ (Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1 := by
    intro z hz hP x hx
    unfold hatI at hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxh, hxΩ⟩ := hx
    obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hxΩ
    set n := G.layerIndex x with hn
    have hown := own_mem_cubeIdx S.aligned hn1 hnK hxl
    have hQ : (n, ownBase (n + m₁) x) ∈ Qset G z := by
      rw [mem_Qset]
      exact ⟨hown, x, ownBase_sameCell x, (mem_boxSet.1 hxh)⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hxΩ⟩
    unfold Vset
    rw [Finset.mem_union]
    by_cases hPP : (n, ownBase (n + m₁) x) ∈ parCubes G X₁
    · right
      rw [Finset.mem_biUnion]
      exact ⟨_, hP _ hQ hPP, mem_cubeP.2 (ownBase_sameCell x)⟩
    · left
      have : cubeP (n, ownBase (n + m₁) x) ⊆ X₁ := by
        by_contra hc
        exact hPP (Finset.mem_filter.2 ⟨hown, hc⟩)
      exact this (mem_cubeP.2 (ownBase_sameCell x))
  have hdich : ∀ z ∈ cubeIdx G, (sProd G s z ≠ 0 ∨ sProd G s' z ≠ 0) →
      SubI G (intBox z) Y ∨ DisjI G (intBox z) Y := by
    intro z hz hactive
    have hP : ∀ P ∈ Qset G z, P ∈ parCubes G X₁ → P ∈ 𝒞 := by
      rcases hactive with h | h
      · exact hact s (fun P hP hPC => (hs0 P hP hPC).1) z h
      · exact hact s' (fun P hP hPC => (hs0 P hP hPC).2) z h
    rcases connIn_dichotomy (hconn z hz) (hhat z hz hP) hY with h | h
    · left
      intro x hx
      exact h (by
        unfold hatI
        rw [Finset.mem_filter]
        exact ⟨box_subset_hatBox z hx, x.2⟩)
    · right
      intro x hx hxY
      exact Finset.disjoint_left.1 h (by
        unfold hatI
        rw [Finset.mem_filter]
        exact ⟨box_subset_hatBox z hx, x.2⟩) hxY
  have hagree : ∀ z ∈ cubeIdx G, SubI G (intBox z) Y → sProd G s z = sProd G s' z := by
    intro z hz hbox
    by_cases hactive : sProd G s z ≠ 0 ∨ sProd G s' z ≠ 0
    · have hP : ∀ P ∈ Qset G z, P ∈ parCubes G X₁ → P ∈ 𝒞 := by
        rcases hactive with h | h
        · exact hact s (fun P hP hPC => (hs0 P hP hPC).1) z h
        · exact hact s' (fun P hP hPC => (hs0 P hP hPC).2) z h
      -- the base point of `z` lies in `□_z ∩ Ω₁`, hence in `Y`
      obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hz
      have hbaseΩ : z.2 ∈ G.Ω 1 := G.layer_subset hm1 hmK hl
      have hbasebox : z.2 ∈ intBox z := by
        rw [mem_intBox]
        intro μ
        refine ⟨0, ?_⟩
        have hB : (1 : ℝ) ≤ (L : ℝ) ^ (z.1 + m₁) :=
          one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
        simp only [Int.cast_zero, zero_mul, add_zero]
        rw [abs_lt]
        constructor <;> nlinarith
      have hbaseY : z.2 ∈ Y := hbox ⟨z.2, hbaseΩ⟩ hbasebox
      have hhatY : hatI G z ⊆ Y := by
        rcases connIn_dichotomy (hconn z hz) (hhat z hz hP) hY with h | h
        · exact h
        · exfalso
          exact Finset.disjoint_left.1 h (by
            unfold hatI
            rw [Finset.mem_filter]
            exact ⟨box_subset_hatBox z hbasebox, hbaseΩ⟩) hbaseY
      unfold sProd
      refine Finset.prod_congr rfl fun P hPQ => ?_
      by_cases hPP : P ∈ parCubes G X₁
      · by_cases hPC : P ∈ 𝒞
        · obtain ⟨hPi, y, hy, hyhat⟩ := (mem_Qset).1 hPQ
          have hyP : y ∈ cubeP P := mem_cubeP.2 hy
          have hyΩ : y ∈ G.Ω 1 := cubeP_subset_Ω S hPi hyP
          have hyY : y ∈ Y := hhatY (by
            unfold hatI
            rw [Finset.mem_filter]
            exact ⟨mem_boxSet.2 hyhat, hyΩ⟩)
          have hsubV : cubeP P ⊆ (Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1 := by
            intro x hx
            rw [Finset.mem_filter]
            refine ⟨?_, cubeP_subset_Ω S hPi hx⟩
            unfold Vset
            rw [Finset.mem_union]
            right
            exact Finset.mem_biUnion.2 ⟨P, hPC, hx⟩
          have hsubY : SubI G (cubeP P) Y := by
            rcases connIn_dichotomy (cubeP_connIn S hPi) hsubV hY with h | h
            · intro x hx; exact h hx
            · exfalso; exact Finset.disjoint_left.1 h hyP hyY
          exact hag P hPC hsubY
        · rw [(hs0 P hPP hPC).1, (hs0 P hPP hPC).2]
      · rw [(hs1 P ((mem_Qset).1 hPQ).1 hPP).1, (hs1 P ((mem_Qset).1 hPQ).1 hPP).2]
    · push Not at hactive
      rw [hactive.1, hactive.2]
  intro x hx
  obtain ⟨z, hzZ, hxz⟩ := Finset.mem_biUnion.1 hx
  have hzZ' := Finset.mem_filter.1 hzZ
  have hsub := hzZ'.2.2
  have hxbox : (x : CTorus d L N₁ m₁ K) ∈ hatBox z := by
    refine box_subset_hatBox z (coreBox_subset_box hxz)
  have hxY : (x : CTorus d L N₁ m₁ K) ∈ Y := hsub x hxbox
  exact Gs_local S hα hα' hU hU' hdich hagree hA hf x hxY

end Balaban.Localization
