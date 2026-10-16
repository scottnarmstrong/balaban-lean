/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Region.Step
public import Balaban.Localization.PolymerGeometry
import Mathlib.Tactic.Linarith

/-!
# Holes of the region step are not unions of aligned `L`-boxes (blocker 3, leaf 0a)

`notes/phase1/VMOD-44.md` §5 asks whether every site of `Ω_K^c` lies in an aligned `L`-box
(a `π'_K`-cube, `box b L` with `Aligned L b`) contained in `Ω_K^c`.  The openings of the region
step use `L`-blocks `lblock L c` with *arbitrary* corner `c`, so the position of a face of the hole
is fixed by the radii alone, not by the lattice of aligned boxes.

* `hole_face_misaligned`: let `F` be a set with a flat face in the direction `i0`, that is
  `F ⊆ {f : f i0 ∈ e - [0,T]}` with a point `f₀ ∈ F`, `f₀ i0 = e`.  Let `Ω ⊆ (nbhd (m-1) F)ᶜ` contain
  every site that lies in an `L`-block at distance `≥ m` from `F`.  Then the hole site `z`, which
  is `f₀` moved by `m-1` in the direction `i0`, lies in `Ωᶜ`, and every aligned box containing
  `z` contains a site of `Ω`, unless `(e + m).val ≡ 0 (mod L)`.
* `omega_hole_face_misaligned`: the same for `Ω_K` of a region step without new `P`-cubes:
  `F = U'_k`, `m = ⌊R_k⌋ + 5` (`Ω'_K = Op_{ρ+2}(nbhd_3 U'_k)`, `nbhd_3` shifts the distance by 3).
  The hole is `nbhd_{ρ+4} U'_k` up to the `L - 1` layer, and its face is aligned only if
  `(e + ρ + 5) ≡ 0 (mod L)`, where `e` is the extreme coordinate of `U'_k`.
* `exists_step_hole_not_boxUnion`: a region step on `Torus d n1` (`L ∣ n1`, `L ≥ 8`) with one new
  cube `P = {0}` and `Z = ∅`, whose hole contains a site lying in no aligned `L`-box inside the
  hole.  So the statement of leaf 0a is false for the landed `RegionStep`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Localization

section Core

variable {d n : ℕ} [NeZero n]

omit [NeZero n] in
private theorem cycNorm_natCast_ge {k m : ℕ} (hm : 1 ≤ m) (h1 : m ≤ k) (h2 : k + m ≤ n) :
    m ≤ cycNorm n (k : ZMod n) := by
  have hk : k < n := by omega
  have hv : (k : ZMod n).val = k := by rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt hk
  unfold cycNorm
  rw [hv]
  omega

omit [NeZero n] in
private theorem supDist_update_le (f : Torus d n) (i0 : Fin d) (a : ZMod n) {k : ℕ}
    (h : cycNorm n (a - f i0) ≤ k) : supDist (Function.update f i0 a) f ≤ k := by
  refine supDist_le_iff.mpr fun i => ?_
  by_cases hi : i = i0
  · subst hi; simpa using h
  · simp [Function.update_of_ne hi, cycNorm]

/-- A hole with a flat face: every aligned box through the face site `z` contains a site of `Ω`,
unless the first site outside the face is aligned. -/
theorem hole_face_misaligned {L : ℕ} (hL : 0 < L) (hLn : L ∣ n)
    (F Ω : Set (Torus d n)) (i0 : Fin d) (m T : ℕ) (e : ZMod n) (hm : 1 ≤ m)
    (hn : T + 2 * m + L ≤ n)
    (hFface : ∀ f ∈ F, ∃ t : ℕ, t ≤ T ∧ f i0 = e - (t : ZMod n))
    (hΩ : Ω ⊆ (nbhd (m - 1) F)ᶜ)
    (hfar : ∀ y, (∃ c, y ∈ lblock L c ∧ ∀ x ∈ lblock L c, ∀ f ∈ F, m ≤ supDist x f) → y ∈ Ω)
    (f₀ : Torus d n) (hf₀ : f₀ ∈ F) (hf₀e : f₀ i0 = e)
    (hmis : (e + (m : ZMod n)).val % L ≠ 0) :
    Function.update f₀ i0 (e + ((m - 1 : ℕ) : ZMod n)) ∉ Ω ∧
      ∀ b : Torus d n, Aligned L b →
        Function.update f₀ i0 (e + ((m - 1 : ℕ) : ZMod n)) ∈ Localization.box b L →
          ∃ y ∈ Localization.box b L, y ∈ Ω := by
  set z : Torus d n := Function.update f₀ i0 (e + ((m - 1 : ℕ) : ZMod n)) with hz
  have hm1 : ((m - 1 : ℕ) : ZMod n) + 1 = (m : ZMod n) := by
    rw [← Nat.cast_succ]; congr 1; omega
  refine ⟨?_, ?_⟩
  · intro hzΩ
    apply hΩ hzΩ
    refine mem_nbhd.mpr ⟨f₀, hf₀, supDist_update_le f₀ i0 _ ?_⟩
    rw [hf₀e, add_sub_cancel_left, cycNorm_le_iff]
    exact ⟨((m - 1 : ℕ) : ℤ), by simp, by simp⟩
  · intro b hb hzb
    obtain ⟨w, hw, hzw⟩ := hzb
    have hzi : z i0 = e + ((m - 1 : ℕ) : ZMod n) := by simp [hz]
    have hwi : w i0 + 1 < L := by
      by_contra hcon
      have hEq : w i0 + 1 = L := by have := hw i0; omega
      have h1 : e + (m : ZMod n) = (b + natT (fun _ => L) : Torus d n) i0 := by
        have h2 : z i0 = b i0 + ((w i0 : ℕ) : ZMod n) := by
          have := congrFun hzw i0
          simpa using this
        rw [← hm1, ← add_assoc, ← hzi, h2]
        have : ((L : ℕ) : ZMod n) = ((w i0 : ℕ) : ZMod n) + 1 := by rw [← hEq]; push_cast; ring
        simp only [Pi.add_apply, natT_apply]
        rw [this]; ring
      apply hmis
      rw [h1, mod_of_aligned_add hLn hb i0]
      simp
    set y : Torus d n := Function.update z i0 (e + (m : ZMod n)) with hy
    have hyb : y ∈ Localization.box b L := by
      refine ⟨Function.update w i0 (w i0 + 1), fun μ => ?_, ?_⟩
      · by_cases hμ : μ = i0
        · subst hμ; simpa using hwi
        · simpa [Function.update_of_ne hμ] using hw μ
      · funext μ
        by_cases hμ : μ = i0
        · subst hμ
          have h2 : z μ = b μ + ((w μ : ℕ) : ZMod n) := by
            have := congrFun hzw μ
            simpa using this
          simp only [hy, Function.update_self, Pi.add_apply, natT_apply]
          rw [← hm1, ← add_assoc, ← hzi, h2]; push_cast; ring
        · have h2 : z μ = b μ + ((w μ : ℕ) : ZMod n) := by
            have := congrFun hzw μ
            simpa using this
          simp [hy, Function.update_of_ne hμ, h2]
    refine ⟨y, hyb, hfar y ⟨y, mem_lblock_self hL y, ?_⟩⟩
    rintro x ⟨v, hv, rfl⟩ f hf
    obtain ⟨t, ht, hft⟩ := hFface f hf
    refine le_trans ?_ (cycNorm_le_supDist _ _ i0)
    have hxf : (fun i => y i + (v i : ZMod n)) i0 - f i0 = (((m + v i0 + t : ℕ)) : ZMod n) := by
      simp only [hy, Function.update_self, hft]; push_cast; ring
    rw [hxf]
    have := hv i0
    exact cycNorm_natCast_ge hm (by omega) (by omega)

end Core

section Step

variable {d L n0 n1 : ℕ} [NeZero n1] {Rprev Rk : ℝ}

/-- The hole of a region step without new `P`-cubes has a misaligned face at every site of a flat
face of `U'_k` unless `(e + ⌊R_k⌋ + 5) ≡ 0 (mod L)`; here `e` is the extreme coordinate of `U'_k`
in the direction `i0`. -/
theorem omega_hole_face_misaligned (st : RegionStep d L n0 n1 Rprev Rk) (hL : 0 < L)
    (hLn : L ∣ n1) (hP : st.P = ∅) (i0 : Fin d) (e : ZMod n1) (T : ℕ)
    (hn : T + 2 * (⌊Rk⌋₊ + 5) + L ≤ n1)
    (hface : ∀ u ∈ st.Uprime, ∃ t : ℕ, t ≤ T ∧ u i0 = e - (t : ZMod n1))
    (u₀ : Torus d n1) (hu₀ : u₀ ∈ st.Uprime) (hu₀e : u₀ i0 = e)
    (hmis : (e + ((⌊Rk⌋₊ + 5 : ℕ) : ZMod n1)).val % L ≠ 0) :
    Function.update u₀ i0 (e + ((⌊Rk⌋₊ + 4 : ℕ) : ZMod n1)) ∉ st.Omega ∧
      ∀ b : Torus d n1, Aligned L b →
        Function.update u₀ i0 (e + ((⌊Rk⌋₊ + 4 : ℕ) : ZMod n1)) ∈ Localization.box b L →
          ∃ y ∈ Localization.box b L, y ∈ st.Omega := by
  have hOm : st.Omega = st.OmegaPrime := by
    unfold RegionStep.Omega Region.Omega
    rw [hP, nbhd_empty]
    exact openingIn_empty (L := L) 1 (opening_isLBlockUnion L _ _)
  rw [hOm]
  have key := hole_face_misaligned hL hLn st.Uprime st.OmegaPrime i0 (⌊Rk⌋₊ + 5) T e
    (by omega) hn hface ?_ ?_ u₀ hu₀ hu₀e hmis
  · have e4 : ⌊Rk⌋₊ + 5 - 1 = ⌊Rk⌋₊ + 4 := by omega
    rw [e4] at key
    exact key
  · intro y hy hy'
    have h1 := opening_disjoint_nbhd (L := L) (m := ⌊Rk⌋₊ + 2) (by omega) (nbhd 3 st.Uprime) y hy
    apply h1
    rw [nbhd_nbhd]
    have e4 : 3 + (⌊Rk⌋₊ + 2 - 1) = ⌊Rk⌋₊ + 5 - 1 := by omega
    rw [e4]; exact hy'
  · rintro y ⟨c, hyc, hc⟩
    refine ⟨c, hyc, le_setDist_iff.mpr fun x hx f hf => ?_⟩
    have := setDist_nbhd_ge (X := st.Uprime) (Y := lblock L c) 3 (k := ⌊Rk⌋₊ + 5)
      (fun u hu x hx => by rw [supDist_comm]; exact hc x hx u hu) f hf x hx
    rw [supDist_comm]; omega

end Step

section Witness

variable {d L n1 : ℕ} [NeZero n1]

/-- The hole of a single new cube `P = {0}` is the sup-ball of radius `3` about `0`.  For `L ≥ 8`
no aligned `L`-box contains `0` inside it: every aligned box through the face site `3 e_{i0}`
contains a site of `Ω`. -/
theorem single_cube_hole_not_boxUnion (i0 : Fin d) (hL : 8 ≤ L) (hLn : L ∣ n1)
    (hn : L + 8 ≤ n1) (Ω' : Set (Torus d n1)) (hΩ' : ∀ y, y ∈ Ω') :
    Function.update (0 : Torus d n1) i0 (((3 : ℕ) : ZMod n1)) ∉
        openingIn L 1 (nbhd 3 {(0 : Torus d n1)}) Ω' ∧
      ∀ b : Torus d n1, Aligned L b →
        Function.update (0 : Torus d n1) i0 (((3 : ℕ) : ZMod n1)) ∈ Localization.box b L →
          ∃ y ∈ Localization.box b L, y ∈ openingIn L 1 (nbhd 3 {(0 : Torus d n1)}) Ω' := by
  have hL0 : 0 < L := by omega
  have key := hole_face_misaligned hL0 hLn ({0} : Set (Torus d n1))
    (openingIn L 1 (nbhd 3 {(0 : Torus d n1)}) Ω') i0 4 0 0 (by omega) (by omega)
    (fun f hf => ⟨0, le_rfl, by rw [Set.mem_singleton_iff.mp hf]; simp⟩) ?_ ?_ 0
    rfl rfl ?_
  · simpa using key
  · intro y hy hy'
    have h1 := (openingIn_subset (L := L) (m := 1) le_rfl _ Ω' hy).2
    apply h1
    rw [nbhd_nbhd]
    have e4 : 3 + (1 - 1) = 4 - 1 := by norm_num
    rw [e4]; exact hy'
  · rintro y ⟨c, hyc, hc⟩
    refine ⟨c, hyc, fun x _ => hΩ' x, le_setDist_iff.mpr fun x hx f hf => ?_⟩
    have := setDist_nbhd_ge (X := ({0} : Set (Torus d n1))) (Y := lblock L c) 3 (k := 4)
      (fun u hu x hx => by rw [Set.mem_singleton_iff.mp hu, supDist_comm]; exact hc x hx 0 rfl)
      f hf x hx
    rw [supDist_comm]; omega
  · have hv : ((4 : ℕ) : ZMod n1).val = 4 := by
      rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
    simp only [zero_add]
    rw [hv, Nat.mod_eq_of_lt (by omega : 4 < L)]; omega

/-- **Leaf 0a, refuted.**  For `L ≥ 8`, `L ∣ n₁`, `L + 8 ≤ n₁` there is a region step (`Z = ∅`,
`P = {0}`, `Q = R = S = ∅`) whose hole `Ω_K^c` has a site lying in no aligned `L`-box contained in
`Ω_K^c`: every aligned box through it contains a site of `Ω_K`. -/
theorem exists_step_hole_not_boxUnion (i0 : Fin d) (hL : 8 ≤ L) (hLn : L ∣ n1)
    (hn : L + 8 ≤ n1) (Rprev Rk : ℝ) :
    ∃ st : RegionStep d L (L * n1) n1 Rprev Rk, st.P = {0} ∧
      ∃ z : Torus d n1, z ∉ st.Omega ∧ ∀ b : Torus d n1, Aligned L b →
        z ∈ Localization.box b L → ∃ y ∈ Localization.box b L, y ∈ st.Omega := by
  have hL0 : 0 < L := by omega
  have hU : Region.Uprime L n1 ⌊Rprev⌋₊ (∅ : Set (Torus d (L * n1))) = ∅ := by
    simp [Region.Uprime, Region.U, thick, nbhd_empty]
  have hOP : ∀ y : Torus d n1,
      y ∈ Region.OmegaPrime L ⌊Rk⌋₊ (Region.Uprime L n1 ⌊Rprev⌋₊ (∅ : Set (Torus d (L * n1)))) := by
    intro y
    rw [hU]
    refine ⟨y, mem_lblock_self hL0 y, ?_⟩
    rw [nbhd_empty, setDist_eq_top_iff.mpr (Or.inr rfl)]
    exact le_top
  refine ⟨⟨∅, {0}, ∅, ∅, ∅, fun y _ => hOP y, Set.empty_subset _, Set.empty_subset _,
    Set.empty_subset _⟩, rfl, Function.update (0 : Torus d n1) i0 (((3 : ℕ) : ZMod n1)), ?_⟩
  exact single_cube_hole_not_boxUnion i0 hL hLn hn _ hOP

end Witness

end Balaban.LargeField
