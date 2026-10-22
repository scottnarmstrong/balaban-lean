/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFHistFactorSurj

/-!
# The separation of the component records as disjointness in the doubled torus (A6-4)

The operator gas of B2 (`Polymer/GasOpEq.lean`) declares two heavy objects compatible when their
supports `zs` are disjoint, while the history factorization (`Spine/FinalLFHistFactorSurj.lean`)
sums over the families of records whose cubes are pairwise at index distance `≥ ω_k` (`RecSep`).
A neighbourhood of radius `r` of the cubes of a record in `𝕋_k` cannot match that condition
exactly for every parity of `ω_k = 2⌊R_base λ²⌋ + L + 11`, so the sites of the gas carry, besides
the blocks, the sites of the doubled torus `𝕋_{2 n_k}` (with trivial variables), and the support of a
record contains the `(ω_k - 1)`-neighbourhood of the doubled image `2·c` of its cubes:

* `zDouble`, `tDouble`: the doubling `ZMod n → ZMod (2n)`, `𝕋_n → 𝕋_{2n}`, and
  `supDist_tDouble_le_iff`: `d(2x, 2y) ≤ 2m ↔ d(x, y) ≤ m`;
* `dblNbhd ω c`: the `(ω - 1)`-neighbourhood of `2·c` in `𝕋_{2n}`;
* **`disjoint_dblNbhd_iff`**: for `ω ≥ 1`, `dblNbhd ω c ∩ dblNbhd ω c' = ∅ ↔ d(c, c') ≥ ω`
  (the midpoint of `2x, 2y` in `𝕋_{2n}`, `exists_split`);
* `disjoint_disjSum_iff`: supports on a sum of two site types are disjoint iff both parts are;
* **`disjoint_supp_iff_sep`**, **`recSep_iff_disjoint`**: with supports `A_r ⊔ dblNbhd ω_k r.1`
  whose block parts are disjoint for separated records, the supports of a family are pairwise
  disjoint iff the family is `RecSep`.
-/

@[expose] public section

open Balaban Balaban.LargeField

namespace Balaban.RootFSpine

section Double

/-- **The doubling `ZMod n → ZMod (2n)`**, `a ↦ 2a` (an additive map, from `2n ≡ 0 mod 2n`). -/
noncomputable def zDouble (n : ℕ) : ZMod n →+ ZMod (2 * n) :=
  ZMod.lift n ⟨(2 : ℤ) • Int.castAddHom (ZMod (2 * n)), by
    have h : ((2 * n : ℕ) : ZMod (2 * n)) = 0 := ZMod.natCast_self _
    push_cast at h
    simpa [zsmul_eq_mul] using h⟩

theorem zDouble_val {n : ℕ} [NeZero n] (a : ZMod n) : (zDouble n a).val = 2 * a.val := by
  have e : a = ((a.val : ℤ) : ZMod n) := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have h2 : 2 * a.val < 2 * n := by have := ZMod.val_lt a; omega
  have h : zDouble n ((a.val : ℤ) : ZMod n) = ((2 * a.val : ℕ) : ZMod (2 * n)) := by
    rw [zDouble, ZMod.lift_coe]
    simp [zsmul_eq_mul]
  rw [← e] at h
  rw [h, ZMod.val_cast_of_lt h2]

/-- The cyclic norm doubles under the doubling. -/
theorem cycNorm_zDouble {n : ℕ} [NeZero n] (a : ZMod n) :
    cycNorm (2 * n) (zDouble n a) = 2 * cycNorm n a := by
  unfold cycNorm
  rw [zDouble_val]
  omega

/-- **The doubling of the torus** `𝕋_n → 𝕋_{2n}`, coordinatewise. -/
noncomputable def tDouble {d n : ℕ} (x : Torus d n) : Torus d (2 * n) := fun i => zDouble n (x i)

/-- The doubling doubles the index distance: `d(2x, 2y) ≤ 2m ↔ d(x, y) ≤ m`. -/
theorem supDist_tDouble_le_iff {d n : ℕ} [NeZero n] (x y : Torus d n) (m : ℕ) :
    supDist (tDouble x) (tDouble y) ≤ 2 * m ↔ supDist x y ≤ m := by
  simp only [supDist_le_iff, tDouble, ← map_sub, cycNorm_zDouble]
  exact forall_congr' fun i => by omega

open Classical in
/-- **The `(ω - 1)`-neighbourhood of the doubled image of `c`** in the doubled torus `𝕋_{2n}`. -/
noncomputable def dblNbhd {d n : ℕ} [NeZero n] (ω : ℕ) (c : Finset (Torus d n)) :
    Finset (Torus d (2 * n)) :=
  Finset.univ.filter fun w => ∃ x ∈ c, supDist (tDouble x) w ≤ ω - 1

/-- **Separation as disjointness in the doubled torus**: for `ω ≥ 1`, the `(ω - 1)`-neighbourhoods
of `2·c` and `2·c'` in `𝕋_{2n}` are disjoint iff the cubes of `c` and `c'` are pairwise at index
distance `≥ ω`. If `d(x, y) ≤ ω - 1`, the midpoint of `2x, 2y` lies in both neighbourhoods; if a point
lies in both, `2 d(x, y) = d(2x, 2y) ≤ 2(ω - 1)`. -/
theorem disjoint_dblNbhd_iff {d n ω : ℕ} [NeZero n] (hω : 1 ≤ ω) (c c' : Finset (Torus d n)) :
    Disjoint (dblNbhd ω c) (dblNbhd ω c') ↔ ∀ x ∈ c, ∀ y ∈ c', ω ≤ supDist x y := by
  classical
  rw [Finset.disjoint_left]
  constructor
  · intro h x hx y hy
    by_contra hlt
    push Not at hlt
    have h1 : supDist (tDouble x) (tDouble y) ≤ (ω - 1) + (ω - 1) := by
      have := (supDist_tDouble_le_iff x y (ω - 1)).2 (by omega)
      omega
    obtain ⟨w, hw1, hw2⟩ := exists_split h1
    exact h (Finset.mem_filter.2 ⟨Finset.mem_univ _, x, hx, hw1⟩)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, y, hy, by rw [supDist_comm]; exact hw2⟩)
  · intro h w hw hw'
    obtain ⟨x, hx, hxw⟩ := (Finset.mem_filter.1 hw).2
    obtain ⟨y, hy, hyw⟩ := (Finset.mem_filter.1 hw').2
    have h1 : supDist (tDouble x) (tDouble y) ≤ 2 * (ω - 1) := by
      have := supDist_triangle (tDouble x) w (tDouble y)
      rw [supDist_comm w] at this
      omega
    have h2 := (supDist_tDouble_le_iff x y (ω - 1)).1 h1
    have h3 := h x hx y hy
    omega

end Double

/-- Supports on a sum of two types of sites are disjoint iff both parts are. -/
theorem disjoint_disjSum_iff {α β : Type*} (A A' : Finset α) (D D' : Finset β) :
    Disjoint (A.disjSum D) (A'.disjSum D') ↔ Disjoint A A' ∧ Disjoint D D' := by
  simp only [Finset.disjoint_left, Finset.mem_disjSum]
  constructor
  · intro h
    exact ⟨fun a ha ha' => h (Or.inl ⟨a, ha, rfl⟩) (Or.inl ⟨a, ha', rfl⟩),
      fun b hb hb' => h (Or.inr ⟨b, hb, rfl⟩) (Or.inr ⟨b, hb', rfl⟩)⟩
  · rintro ⟨h1, h2⟩ x (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩) hx'
    · rcases hx' with ⟨a', ha', e⟩ | ⟨b', -, e⟩
      · cases e
        exact h1 ha ha'
      · cases e
    · rcases hx' with ⟨a', -, e⟩ | ⟨b', hb', e⟩
      · cases e
      · cases e
        exact h2 hb hb'

/-- **The supports of two heavy objects are disjoint iff their cubes are separated**: the support
is `A ⊔ dblNbhd ω c` (blocks and sites of the doubled torus), and the block parts of separated cubes
are disjoint. -/
theorem disjoint_supp_iff_sep {α : Type*} {d n ω : ℕ} [NeZero n] (hω : 1 ≤ ω) {A A' : Finset α}
    {c c' : Finset (Torus d n)}
    (hblk : (∀ x ∈ c, ∀ y ∈ c', ω ≤ supDist x y) → Disjoint A A') :
    Disjoint (A.disjSum (dblNbhd ω c)) (A'.disjSum (dblNbhd ω c')) ↔
      ∀ x ∈ c, ∀ y ∈ c', ω ≤ supDist x y := by
  rw [disjoint_disjSum_iff, disjoint_dblNbhd_iff hω]
  exact ⟨fun h => h.2, fun h => ⟨hblk h, h⟩⟩

/-- **`RecSep` as pairwise disjointness of the gas supports**: for block supports `A r` of the
records that are disjoint for records with separated cubes, a family of records is pairwise
`ω_k`-separated iff the supports `A r ⊔ dblNbhd ω_k r.1` are pairwise disjoint. -/
theorem recSep_iff_disjoint {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K k : ℕ}
    {α : Type*} (A : CRec S n M K k → Finset α)
    (hblk : ∀ r r', (∀ x ∈ r.1, ∀ y ∈ r'.1, S.omega k ≤ supDist x y) → Disjoint (A r) (A r'))
    (Γ : Finset (CRec S n M K k)) :
    RecSep k Γ ↔ ∀ r ∈ Γ, ∀ r' ∈ Γ, r ≠ r' →
      Disjoint ((A r).disjSum (dblNbhd (S.omega k) r.1))
        ((A r').disjSum (dblNbhd (S.omega k) r'.1)) := by
  have hω : 1 ≤ S.omega k := by
    have h := le_omegaW S.L S.Rb S.lam k
    rw [← Setting.omega_eq_omegaW] at h
    omega
  unfold RecSep
  exact forall₂_congr fun r _ => forall₂_congr fun r' _ => imp_congr_right fun _ =>
    (disjoint_supp_iff_sep hω (hblk r r')).symm

end Balaban.RootFSpine
