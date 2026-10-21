/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusResumRootF
public import Balaban.Polymer.TwoTorusGapTowerRootFBoxArith
public import Balaban.Polymer.TwoTorusGapTowerSitesAnimal
public import Balaban.Lattice.Blocks

/-!
# Fine sites and centred cells of the last-scale tori (A6-3 (d), blocker 7)

On the torus `ℤ/ℓ`, `ℓ = s K`, the blocks of side `s` are the cells of the block torus `ℤ/K`. A
cell is written by its centred representative `c ∈ (-K/2, K/2]^d` (`cellZ`), and a fine site `z` by
its *cell-aligned lift* `liftZ z = s · cellZ z + (z mod s) ∈ ℤ^d`, which maps the block of the cell
`c` onto the integer block `[s c, s c + s)^d`; its image in the torus is `z` (`cast_liftZ`). A set
`X` of centred cells determines the set of fine sites `sitesT X` whose cell lies in `X`; the polymers
of the torus are exactly the sets `sitesT X` for `X` the centred image of an animal of the block torus
(`isPolymer_iff_sitesT`), with `|sitesT X| = s^d |X|` (`card_sitesT`). A torus source `g` extends to
`ℤ^d` by `extZ g (liftZ z) = g z` (zero off the lifted sites).

The quarter box: a polymer that is the image of a finite set `A` of the box `4|y_μ| < ℓ` needs
`K ≥ 4` (`four_le_of_isPolymer_quarter`); a set of `ℤ^d` closed under the blocks of side `s ≥ 4` and
contained in the box has its cells in `|c_μ| ≤ K/4` (`quarter_of_blockClosed`).
-/

@[expose] public section

open Finset Balaban Balaban.Polymer Balaban.Polymer.TwoTorusStep

namespace Balaban.RootFSpine.LastScale

variable {d : ℕ}

/-- The centred cell of a fine site `z` of `ℤ/ℓ` for blocks of side `s`: the centred representative
in `ℤ/K` of `⌊z_μ / s⌋`. -/
def cellZ (s K : ℕ) {ℓ : ℕ} (z : Torus d ℓ) : Fin d → ℤ :=
  fun μ => ((((z μ).val / s : ℕ)) : ZMod K).valMinAbs

/-- The cell-aligned lift of a fine site: `s · cellZ z + (z_μ mod s)`. It maps the block of the cell
`c` onto the integer block `[s c, s c + s)^d`. -/
def liftZ (s K : ℕ) {ℓ : ℕ} (z : Torus d ℓ) : Fin d → ℤ :=
  fun μ => (s : ℤ) * cellZ s K z μ + (((z μ).val % s : ℕ) : ℤ)

/-- The fine sites of the torus whose centred cell lies in the set `X` of cells. -/
def sitesT (s K ℓ : ℕ) [NeZero ℓ] (X : Finset (Fin d → ℤ)) : Finset (Torus d ℓ) :=
  Finset.univ.filter fun z => cellZ s K z ∈ X

/-- The extension of a torus source `g` to `ℤ^d`: `g` at the lifted sites (`extZ g (liftZ z) = g z`),
zero elsewhere. -/
def extZ (s K ℓ : ℕ) {N : ℕ} (g : Torus d ℓ → Fin N → ℂ) : (Fin d → ℤ) → Fin N → ℂ :=
  fun y => if liftZ s K (fun μ => ((y μ : ℤ) : ZMod ℓ)) = y then
    g (fun μ => ((y μ : ℤ) : ZMod ℓ)) else 0

variable {s K ℓ : ℕ}

theorem cast_liftZ [NeZero ℓ] (hn : ℓ = s * K) (z : Torus d ℓ) :
    (fun μ => ((liftZ s K z μ : ℤ) : ZMod ℓ)) = z := by
  funext μ
  have hb : ((cellZ s K z μ : ℤ) : ZMod K) = ((((z μ).val / s : ℕ) : ℤ) : ZMod K) := by
    simp only [cellZ, ZMod.coe_valMinAbs, Int.cast_natCast]
  have hmod : cellZ s K z μ ≡ (((z μ).val / s : ℕ) : ℤ) [ZMOD K] :=
    (ZMod.intCast_eq_intCast_iff _ _ _).1 hb
  have hℓ : ((ℓ : ℕ) : ℤ) = (s : ℤ) * K := by rw [hn]; push_cast; ring
  have hmod2 : (s : ℤ) * cellZ s K z μ ≡ (s : ℤ) * (((z μ).val / s : ℕ) : ℤ) [ZMOD (ℓ : ℤ)] := by
    rw [hℓ]; exact Int.ModEq.mul_left' hmod
  have h3 : liftZ s K z μ ≡ (((z μ).val : ℕ) : ℤ) [ZMOD (ℓ : ℤ)] := by
    unfold liftZ
    have h4 := Int.ModEq.add_right ((((z μ).val % s : ℕ) : ℤ)) hmod2
    refine h4.trans ?_
    have : (s : ℤ) * (((z μ).val / s : ℕ) : ℤ) + (((z μ).val % s : ℕ) : ℤ) =
        (((z μ).val : ℕ) : ℤ) := by
      exact_mod_cast Nat.div_add_mod (z μ).val s
    rw [this]
  have h5 := (ZMod.intCast_eq_intCast_iff _ _ _).2 h3
  rw [h5]
  simp

theorem liftZ_injective [NeZero ℓ] (hn : ℓ = s * K) :
    Function.Injective (liftZ (d := d) s K (ℓ := ℓ)) := by
  intro z z' h
  rw [← cast_liftZ hn z, ← cast_liftZ hn z', h]

theorem liftZ_ediv (hs : 0 < s) (z : Torus d ℓ) (μ : Fin d) :
    liftZ s K z μ / (s : ℤ) = cellZ s K z μ := by
  unfold liftZ
  have hsz : (s : ℤ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [Int.mul_add_ediv_left _ _ hsz]
  have h0 : ((((z μ).val % s : ℕ) : ℤ)) / (s : ℤ) = 0 := by
    apply Int.ediv_eq_zero_of_lt
    · positivity
    · exact_mod_cast Nat.mod_lt _ hs
  rw [h0, add_zero]

theorem liftZ_cast [NeZero ℓ] (hn : ℓ = s * K) (hs : 0 < s) (hK : 0 < K) (y : Fin d → ℤ)
    (hy : ∀ μ, ((y μ / (s : ℤ) : ℤ) : ZMod K).valMinAbs = y μ / (s : ℤ)) :
    liftZ s K (fun μ => ((y μ : ℤ) : ZMod ℓ)) = y := by
  funext μ
  unfold liftZ cellZ
  have h1 : (((((y μ : ℤ) : ZMod ℓ).val / s : ℕ)) : ZMod K) = ((y μ / (s : ℤ) : ℤ) : ZMod K) := by
    have := val_div_cast_int hn hs hK (y μ)
    have h2 : (((((y μ : ℤ) : ZMod ℓ).val / s : ℕ)) : ZMod K) =
        ((((((y μ : ℤ) : ZMod ℓ).val / s : ℕ) : ℕ) : ℤ) : ZMod K) := (Int.cast_natCast _).symm
    rw [h2, this, ZMod.intCast_mod]
  rw [h1, hy μ]
  have hsz : (0 : ℤ) < s := by exact_mod_cast hs
  have h3 : (((((y μ : ℤ) : ZMod ℓ).val % s : ℕ)) : ℤ) = y μ % (s : ℤ) := by
    push_cast
    rw [ZMod.val_intCast]
    have hdvd : (s : ℤ) ∣ ((ℓ : ℕ) : ℤ) := ⟨K, by rw [hn]; push_cast; ring⟩
    exact Int.emod_emod_of_dvd _ hdvd
  rw [h3]
  exact Int.mul_ediv_add_emod _ _

theorem extZ_liftZ [NeZero ℓ] (hn : ℓ = s * K) {N : ℕ} (g : Torus d ℓ → Fin N → ℂ)
    (z : Torus d ℓ) : extZ s K ℓ g (liftZ s K z) = g z := by
  unfold extZ
  rw [cast_liftZ hn z]
  simp

theorem extZ_zero {N : ℕ} : extZ (d := d) s K ℓ (0 : Torus d ℓ → Fin N → ℂ) = 0 := by
  funext y
  unfold extZ
  split_ifs <;> rfl

/-- `2|y| < s K` for a fine point whose cell has `|c| ≤ K/4`. -/
theorem two_abs_lt_of_cell (hs : 0 < s) (hK : 2 ≤ K) {y : ℤ}
    (h : (y / (s : ℤ)).natAbs ≤ K / 4) : 2 * |y| < (s : ℤ) * K := by
  have hsz : (0 : ℤ) < s := by exact_mod_cast hs
  have h1 := Int.mul_ediv_self_le (x := y) hsz.ne'
  have h2 := Int.lt_mul_ediv_self_add (x := y) hsz
  set c := y / (s : ℤ)
  have hK4 : (4 : ℤ) * (K / 4 : ℕ) ≤ K := by
    have := Nat.mul_div_le K 4; exact_mod_cast (by omega : 4 * (K / 4) ≤ K)
  have hK2 : (2 : ℤ) * (K / 4 : ℕ) + 2 ≤ K := by
    have : 2 * (K / 4) + 2 ≤ K := by omega
    exact_mod_cast this
  have hc : |c| ≤ ((K / 4 : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast h
  obtain ⟨hcl, hcu⟩ := abs_le.1 hc
  set q : ℤ := ((K / 4 : ℕ) : ℤ)
  have e1 : (s : ℤ) * (-q) ≤ (s : ℤ) * c := mul_le_mul_of_nonneg_left hcl hsz.le
  have e2 : (s : ℤ) * c ≤ (s : ℤ) * q := mul_le_mul_of_nonneg_left hcu hsz.le
  have e3 : (s : ℤ) * (2 * q + 2) ≤ (s : ℤ) * K := mul_le_mul_of_nonneg_left hK2 hsz.le
  have e4 : (s : ℤ) * (4 * q) ≤ (s : ℤ) * K := mul_le_mul_of_nonneg_left hK4 hsz.le
  rcases abs_cases y with ⟨hy, _⟩ | ⟨hy, _⟩ <;> rw [hy] <;> nlinarith

theorem valMinAbs_cast_of_two_abs_lt {n : ℕ} [NeZero n] {y : ℤ} (h : 2 * |y| < (n : ℤ)) :
    ((y : ℤ) : ZMod n).valMinAbs = y := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  simp only [Set.mem_Ioc]
  rcases abs_cases y with ⟨hy, _⟩ | ⟨hy, _⟩ <;> rw [hy] at h <;> constructor <;> linarith

/-- The cell of the image of `y` in `ℤ/(s K)` is `y / s` when `|y / s| ≤ K / 4`. -/
theorem cellZ_cast (hn : ℓ = s * K) (hs : 0 < s) (hK : 2 ≤ K) (y : Fin d → ℤ)
    (hy : ∀ μ, (y μ / (s : ℤ)).natAbs ≤ K / 4) :
    cellZ s K (fun μ => ((y μ : ℤ) : ZMod ℓ)) = fun μ => y μ / (s : ℤ) := by
  funext μ
  exact cell_valMinAbs hn hs (r := K / 4) (by omega) (by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hy μ)

theorem mem_sitesT [NeZero ℓ] {X : Finset (Fin d → ℤ)} {z : Torus d ℓ} :
    z ∈ sitesT s K ℓ X ↔ cellZ s K z ∈ X := by
  simp [sitesT]

open Classical in
/-- The sets of centred cells of the animals of the block torus `ℤ/K`. -/
noncomputable def cellPolys (d K : ℕ) [NeZero K] : Finset (Finset (Fin d → ℤ)) :=
  ((Finset.univ : Finset (Finset (Torus d K))).filter fun Y => IsAnimal (blockGraph d K) Y).image
    fun Y => Y.image fun b μ => (b μ).valMinAbs

theorem mem_cellPolys [NeZero K] {X : Finset (Fin d → ℤ)} :
    X ∈ cellPolys d K ↔ ∃ Y, IsAnimal (blockGraph d K) Y ∧ X = Y.image fun b μ => (b μ).valMinAbs := by
  classical
  simp only [cellPolys, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨Y, hY, rfl⟩; exact ⟨Y, hY, rfl⟩
  · rintro ⟨Y, hY, rfl⟩; exact ⟨Y, hY, rfl⟩

theorem sitesT_image [NeZero ℓ] [NeZero K] (Y : Finset (Torus d K)) :
    sitesT s K ℓ (Y.image fun b μ => (b μ).valMinAbs) =
      Finset.univ.filter fun z : Torus d ℓ => blockMap s K z ∈ Y := by
  ext z
  simp only [mem_sitesT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, he⟩
    have : b = blockMap s K z := funext fun μ => ZMod.valMinAbs_inj.1 (congrFun he μ)
    rwa [← this]
  · intro h; exact ⟨_, h, rfl⟩

theorem card_sitesT [NeZero ℓ] [NeZero K] (hn : ℓ = s * K) (Y : Finset (Torus d K)) :
    (sitesT s K ℓ (Y.image fun b μ => (b μ).valMinAbs)).card =
      s ^ d * (Y.image fun b μ => (b μ).valMinAbs).card := by
  classical
  rw [sitesT_image, Finset.card_image_of_injective _ valMinAbs_cells_injective]
  have h1 : (Finset.univ.filter fun z : Torus d ℓ => blockMap s K z ∈ Y) =
      Y.biUnion fun b => blockFibre s K b := by
    ext z
    simp [mem_blockFibre]
  rw [h1, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl fun b _ => card_blockFibre hn b]
    simp [mul_comm]
  · intro b _ b' _ hbb'
    refine Finset.disjoint_left.2 fun x hx hx' => hbb' ?_
    rw [mem_blockFibre] at hx hx'
    rw [← hx, ← hx']

theorem isPolymer_sitesT_iff [NeZero ℓ] [NeZero K] (hn : ℓ = s * K) (hs : 0 < s)
    (Y : Finset (Torus d K)) :
    IsPolymer d ℓ s (sitesT s K ℓ (Y.image fun b μ => (b μ).valMinAbs)) ↔
      IsAnimal (blockGraph d K) Y :=
  isPolymer_cellsOf_iff hn hs Y

theorem image_cellZ_sitesT [NeZero ℓ] [NeZero K] (hn : ℓ = s * K) (hs : 0 < s)
    (Y : Finset (Torus d K)) :
    (sitesT s K ℓ (Y.image fun b μ => (b μ).valMinAbs)).image (cellZ s K) =
      Y.image fun b μ => (b μ).valMinAbs := by
  ext c
  simp only [Finset.mem_image, mem_sitesT]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact hz
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨x, hx⟩ := exists_site hn hs b
    refine ⟨x, ⟨b, hb, ?_⟩, ?_⟩ <;> · funext μ; simp only [cellZ]; rw [← hx]

theorem sitesT_injOn [NeZero ℓ] [NeZero K] (hn : ℓ = s * K) (hs : 0 < s) :
    Set.InjOn (sitesT (d := d) s K ℓ) (cellPolys d K : Set (Finset (Fin d → ℤ))) := by
  intro X hX X' hX' h
  obtain ⟨Y, -, rfl⟩ := mem_cellPolys.1 hX
  obtain ⟨Y', -, rfl⟩ := mem_cellPolys.1 hX'
  rw [← image_cellZ_sitesT hn hs Y, ← image_cellZ_sitesT hn hs Y']
  rw [h]

theorem isPolymer_iff_sitesT [NeZero ℓ] [NeZero K] (hn : ℓ = s * K) (hs : 0 < s)
    (Xf : Finset (Torus d ℓ)) :
    IsPolymer d ℓ s Xf ↔ ∃ X ∈ cellPolys d K, sitesT s K ℓ X = Xf := by
  constructor
  · intro h
    obtain ⟨Y, hY, -, hX⟩ := exists_animal_of_isPolymer hn hs h
    exact ⟨_, mem_cellPolys.2 ⟨Y, hY, rfl⟩, hX.symm⟩
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨Y, hY, rfl⟩ := mem_cellPolys.1 hX
    exact (isPolymer_sitesT_iff hn hs Y).2 hY

/-- A block of side `s ≥ 4` of `ℤ` inside the quarter box `4|y| < s K`: `K ≥ 4`, and the cell
`c` of the block has `|c| ≤ K / 4`. -/
theorem quarter_of_block (hs : 4 ≤ s) {c : ℤ}
    (h1 : 4 * |(s : ℤ) * c| < (s : ℤ) * K) (h2 : 4 * |(s : ℤ) * c + ((s : ℤ) - 1)| < (s : ℤ) * K) :
    4 ≤ K ∧ c.natAbs ≤ K / 4 := by
  have hsz : (4 : ℤ) ≤ s := by exact_mod_cast hs
  rcases le_or_gt 0 c with hc | hc
  · have hpos : 0 ≤ (s : ℤ) * c + ((s : ℤ) - 1) := by nlinarith
    rw [abs_of_nonneg hpos] at h2
    have key : (4 : ℤ) * (c + 1) ≤ K := by
      by_contra hk
      push Not at hk
      have hk' : (K : ℤ) ≤ 4 * c + 3 := by omega
      have := mul_le_mul_of_nonneg_left hk' (by linarith : (0 : ℤ) ≤ s)
      nlinarith
    have hn : (c.natAbs : ℤ) = c := Int.natAbs_of_nonneg hc
    constructor <;> omega
  · have hneg : (s : ℤ) * c < 0 := by nlinarith
    rw [abs_of_neg hneg] at h1
    have key : (4 : ℤ) * (-c) < K := by
      by_contra hk
      push Not at hk
      have := mul_le_mul_of_nonneg_left hk (by linarith : (0 : ℤ) ≤ s)
      nlinarith
    have hn : (c.natAbs : ℤ) = -c := by rw [Int.ofNat_natAbs_of_nonpos hc.le]
    constructor <;> omega

/-- In a set of `ℤ^d` closed under the blocks of side `s ≥ 4` and contained in the quarter box
`4|y_μ| < s K`, every point has `|y_μ / s| ≤ K / 4`, and `K ≥ 4`. -/
theorem quarter_of_blockClosed (hs : 4 ≤ s) {A : Finset (Fin d → ℤ)}
    (hcl : ∀ y ∈ A, ∀ y' : Fin d → ℤ, (∀ μ, y μ / (s : ℤ) = y' μ / (s : ℤ)) → y' ∈ A)
    (hA : ∀ y ∈ A, ∀ μ, 4 * |y μ| < (s : ℤ) * K) {y : Fin d → ℤ} (hy : y ∈ A) (μ : Fin d) :
    4 ≤ K ∧ (y μ / (s : ℤ)).natAbs ≤ K / 4 := by
  classical
  have hsz : (0 : ℤ) < s := by exact_mod_cast (by omega : 0 < s)
  set c := y μ / (s : ℤ)
  have hdiv1 : (s : ℤ) * c / (s : ℤ) = c := Int.mul_ediv_cancel_left _ hsz.ne'
  have hdiv2 : ((s : ℤ) * c + ((s : ℤ) - 1)) / (s : ℤ) = c := by
    rw [Int.mul_add_ediv_left _ _ hsz.ne', Int.ediv_eq_zero_of_lt (by linarith) (by linarith),
      add_zero]
  have hmem : ∀ v : ℤ, v / (s : ℤ) = c → Function.update y μ v ∈ A := fun v hv =>
    hcl y hy _ fun ν => by
      by_cases hν : ν = μ
      · subst hν; simp [hv, c]
      · simp [Function.update_of_ne hν]
  have h1 := hA _ (hmem _ hdiv1) μ
  have h2 := hA _ (hmem _ hdiv2) μ
  simp only [Function.update_self] at h1 h2
  exact quarter_of_block hs h1 h2

/-- A polymer of blocks of side `s ≥ 4` that is the image of a finite set of the quarter box of the
torus `ℤ/(s K)` needs `K ≥ 4`. -/
theorem four_le_of_isPolymer_quarter [NeZero ℓ] (hd : 0 < d) (hn : ℓ = s * K) (hs : 4 ≤ s)
    (A : Finset (Fin d → ℤ)) (hA : ∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ))
    (hP : IsPolymer d ℓ s (A.image fun y μ => ((y μ : ℤ) : ZMod ℓ))) : 4 ≤ K := by
  classical
  by_contra hK
  push Not at hK
  have hs0 : 0 < s := by omega
  have hK0 : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · exact absurd (by rw [hn, h0, mul_zero]) (NeZero.ne ℓ)
    · exact h0
  obtain ⟨x, hx⟩ := hP.1
  set μ₀ : Fin d := ⟨0, hd⟩
  set b := (x μ₀).val / s with hbdef
  have hb : b < K := by
    rw [hbdef, Nat.div_lt_iff_lt_mul hs0]
    exact lt_of_lt_of_eq (ZMod.val_lt (x μ₀)) (by rw [hn, mul_comm])
  set v : ℕ := if b = 0 then (if K = 1 then s / 2 else s - 1) else b * s with hvdef
  have hv : v / s = b := by
    rw [hvdef]
    split_ifs with h0 h1
    · rw [h0]; exact Nat.div_eq_of_lt (by omega)
    · rw [h0]; exact Nat.div_eq_of_lt (by omega)
    · exact Nat.mul_div_cancel _ hs0
  have hvl : v < ℓ := by
    rw [hn]
    have : v < (b + 1) * s := by
      rw [hvdef]; split_ifs with h0 h1
      · rw [h0]; omega
      · rw [h0]; omega
      · nlinarith
    calc v < (b + 1) * s := this
      _ ≤ K * s := Nat.mul_le_mul_right _ hb
      _ = s * K := by ring
  set x' : Torus d ℓ := Function.update x μ₀ ((v : ℕ) : ZMod ℓ) with hx'def
  have hx' : x' ∈ A.image fun y μ => ((y μ : ℤ) : ZMod ℓ) := by
    refine hP.2.1 x hx x' fun μ => ?_
    by_cases hμ : μ = μ₀
    · subst hμ
      simp only [hx'def, Function.update_self, ZMod.val_natCast, Nat.mod_eq_of_lt hvl, hv, hbdef]
    · simp [hx'def, Function.update_of_ne hμ]
  obtain ⟨a, ha, hax⟩ := Finset.mem_image.1 hx'
  have e : ((a μ₀ : ℤ) : ZMod ℓ) = ((v : ℕ) : ZMod ℓ) := by
    have := congrFun hax μ₀
    simpa [hx'def] using this
  have h4 := hA a ha μ₀
  have hvm : ((a μ₀ : ℤ) : ZMod ℓ).valMinAbs = a μ₀ :=
    valMinAbs_cast_of_two_abs_lt (by linarith [abs_nonneg (a μ₀)])
  rw [e] at hvm
  have hmin := ZMod.valMinAbs_natAbs_eq_min ((v : ℕ) : ZMod ℓ)
  rw [hvm, ZMod.val_natCast, Nat.mod_eq_of_lt hvl] at hmin
  have h4' : 4 * (a μ₀).natAbs < ℓ := by
    have : (4 : ℤ) * ((a μ₀).natAbs : ℤ) < ℓ := by rw [Int.natCast_natAbs]; exact h4
    exact_mod_cast this
  rw [hmin] at h4'
  have hmin' : 4 * v < ℓ ∨ 4 * (ℓ - v) < ℓ := by
    rcases le_total v (ℓ - v) with h | h
    · left; rw [min_eq_left h] at h4'; exact h4'
    · right; rw [min_eq_right h] at h4'; exact h4'
  have hvv : (b = 0 ∧ K = 1 ∧ v = s / 2) ∨ (b = 0 ∧ K ≠ 1 ∧ v = s - 1) ∨
      (1 ≤ b ∧ v = b * s) := by
    rw [hvdef]
    split_ifs with h0 h1
    · exact Or.inl ⟨h0, h1, rfl⟩
    · exact Or.inr (Or.inl ⟨h0, h1, rfl⟩)
    · exact Or.inr (Or.inr ⟨Nat.one_le_iff_ne_zero.2 h0, rfl⟩)
  clear_value v b x'
  subst hn
  interval_cases K <;> interval_cases b <;> omega

end Balaban.RootFSpine.LastScale
