/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.GsSpecPoly
public import Balaban.SmallField.Def6v2Inhabited

/-!
# Block arithmetic for the equivariance of the minimal generating sets

Effect of translations by, and reflections about, a multiple of the block side on the block index
(`blockCoord_add_nat`, `blockCoord_flip`).
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.LargeField Finset

section Arith

variable {n b m s : ℕ}

theorem blockCoord_add_nat [NeZero n] (hn : n = b * m) (hb : b ∣ s) (a : ZMod n) :
    blockCoord b m (a + (s : ZMod n)) = blockCoord b m a + ((s / b : ℕ) : ZMod m) := by
  have hbpos : 0 < b := Nat.pos_of_ne_zero (fun h => NeZero.ne n (by simp [hn, h]))
  have e : a + (s : ZMod n) = ((a.val + s : ℕ) : ZMod n) := by simp
  have h1 := Nat.mod_mul_right_div_self (a.val + s) b m
  rw [← hn] at h1
  unfold blockCoord
  have h2 : (a.val + s) / b = a.val / b + s / b := by
    obtain ⟨σ, rfl⟩ := hb
    rw [Nat.mul_div_cancel_left _ hbpos, Nat.add_mul_div_left _ _ hbpos]
  rw [e, ZMod.val_natCast, h1, h2, ZMod.natCast_mod, Nat.cast_add]

theorem blockCoord_flip [NeZero n] (hn : n = b * m) (hb : b ∣ s) (a : ZMod n) :
    blockCoord b m ((s : ZMod n) - 1 - a) = ((s / b : ℕ) : ZMod m) - 1 - blockCoord b m a := by
  have hbpos : 0 < b := Nat.pos_of_ne_zero (fun h => NeZero.ne n (by simp [hn, h]))
  have hmpos : 0 < m := Nat.pos_of_ne_zero (fun h => NeZero.ne n (by simp [hn, h]))
  obtain ⟨σ, rfl⟩ := hb
  have hσ : b * σ / b = σ := Nat.mul_div_cancel_left _ hbpos
  rw [hσ]
  set q := a.val / b with hq
  set r := a.val % b with hr
  have hav : b * q + r = a.val := Nat.div_add_mod _ _
  have hrb : r < b := Nat.mod_lt _ hbpos
  have hqm : q < m := by
    rw [hq, Nat.div_lt_iff_lt_mul hbpos, mul_comm, ← hn]; exact ZMod.val_lt a
  obtain ⟨u, hu⟩ : ∃ u, u + 1 + q = σ + m := ⟨σ + m - 1 - q, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, v + 1 + r = b := ⟨b - 1 - r, by omega⟩
  have hN : b * u + v + a.val + 1 = b * σ + n := by
    have h5 : b * (u + 1 + q) = b * (σ + m) := by rw [hu]
    have h6 : n = b * m := hn
    nlinarith [h5, hav, h6, hv]
  have hNz : (((b * u + v : ℕ)) : ZMod n) = (b * σ : ℕ) - 1 - a := by
    have h2 : (((b * u + v + a.val + 1 : ℕ)) : ZMod n) = ((b * σ + n : ℕ) : ZMod n) := by rw [hN]
    push_cast at h2
    simp only [ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val] at h2
    push_cast
    linear_combination h2
  rw [← hNz]
  have hdiv : (b * u + v) / b = u := by
    rw [Nat.mul_add_div hbpos, Nat.div_eq_of_lt (by omega)]; simp
  have h1 := Nat.mod_mul_right_div_self (b * u + v) b m
  rw [← hn] at h1
  unfold blockCoord
  rw [ZMod.val_natCast, h1, hdiv, ZMod.natCast_mod, ← hq]
  have h3 : ((u + 1 + q : ℕ) : ZMod m) = ((σ + m : ℕ) : ZMod m) := by rw [hu]
  push_cast at h3
  simp only [ZMod.natCast_self, add_zero] at h3
  linear_combination h3

end Arith


section Cubes

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- The index of the `L ^ i`-block of a site of the class torus. -/
def cidx (i : ℕ) (x : CTorus d L N₁ m₁ k) : Torus d (N₁ * L ^ m₁ * L ^ (k - i)) :=
  blockMap (L ^ i) (N₁ * L ^ m₁ * L ^ (k - i)) x

/-- `g` preserves the distance of the block indices at every scale `i ≤ J`. -/
def CubeIso (J : ℕ) (g : Equiv.Perm (CTorus d L N₁ m₁ k)) : Prop :=
  ∀ i ≤ J, ∀ x y, supDist (cidx i (g x)) (cidx i (g y)) = supDist (cidx i x) (cidx i y)

omit [NeZero L] [NeZero N₁] in
theorem cubeIso_one (J : ℕ) : CubeIso J (1 : Equiv.Perm (CTorus d L N₁ m₁ k)) :=
  fun _ _ _ _ => rfl

omit [NeZero L] [NeZero N₁] in
theorem CubeIso.mul {J : ℕ} {g h : Equiv.Perm (CTorus d L N₁ m₁ k)} (hg : CubeIso J g)
    (hh : CubeIso J h) : CubeIso J (g * h) := fun i hi x y => by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hg i hi, hh i hi]

omit [NeZero L] [NeZero N₁] in
theorem CubeIso.inv {J : ℕ} {g : Equiv.Perm (CTorus d L N₁ m₁ k)} (hg : CubeIso J g) :
    CubeIso J g⁻¹ := fun i hi x y => by
  have := hg i hi (g⁻¹ x) (g⁻¹ y)
  simpa using this.symm

omit [NeZero L] [NeZero N₁] in
theorem side_eq_cidx {i : ℕ} (hik : i ≤ k) :
    N₁ * L ^ m₁ * L ^ k = L ^ i * (N₁ * L ^ m₁ * L ^ (k - i)) := side_eq hik

omit [NeZero L] [NeZero N₁] in
theorem supDist_congr {n n' : ℕ} {u v : Torus d n} {u' v' : Torus d n'}
    (h : ∀ ν, cycNorm n (u ν - v ν) = cycNorm n' (u' ν - v' ν)) : supDist u v = supDist u' v' :=
  Finset.sup_congr rfl fun ν _ => h ν

theorem cubeIso_transBy {J s : ℕ} (hJ : J ≤ k) (hs : ∀ i ≤ J, L ^ i ∣ s) (μ : Fin d) :
    CubeIso J (transBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ) := by
  intro i hi x y
  have hcoord : ∀ x ν, cidx i (transBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ x) ν =
      cidx i x ν + (if ν = μ then ((s / L ^ i : ℕ) : ZMod _) else 0) := by
    intro x ν
    unfold cidx
    simp only [blockMap_apply, transBy, Equiv.coe_addRight, Pi.add_apply, Pi.smul_apply,
      Pi.single_apply]
    by_cases h : ν = μ
    · simp only [h, ite_true, nsmul_eq_mul, mul_one]
      exact blockCoord_add_nat (side_eq_cidx (hi.trans hJ)) (hs i hi) _
    · simp [h, blockCoord]
  refine supDist_congr fun ν => ?_
  rw [hcoord, hcoord]
  congr 1
  ring

theorem cubeIso_flipBy {J s : ℕ} (hJ : J ≤ k) (hs : ∀ i ≤ J, L ^ i ∣ s) (μ : Fin d) :
    CubeIso J (flipBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ) := by
  intro i hi x y
  have hcoord : ∀ x ν, cidx i (flipBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ x) ν =
      if ν = μ then ((s / L ^ i : ℕ) : ZMod _) - 1 - cidx i x ν else cidx i x ν := by
    intro x ν
    unfold cidx
    simp only [blockMap_apply, flipBy, Equiv.coe_fn_mk, Function.update_apply]
    by_cases h : ν = μ
    · simp only [h, ite_true]
      exact blockCoord_flip (side_eq_cidx (hi.trans hJ)) (hs i hi) _
    · simp [h]
  refine supDist_congr fun ν => ?_
  rw [hcoord, hcoord]
  by_cases h : ν = μ
  · simp only [h, ite_true]
    rw [cycNorm_sub_comm]
    congr 1
    ring
  · simp [h]

omit [NeZero L] [NeZero N₁] in
theorem cubeIso_swapJ {J : ℕ} (μ ν : Fin d) :
    CubeIso J (swapJ (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) μ ν) := by
  intro i hi x y
  have hcoord : ∀ x κ, cidx i (swapJ (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) μ ν x) κ =
      cidx i x (Equiv.swap μ ν κ) := fun x κ => rfl
  refine le_antisymm (supDist_le_iff.2 fun κ => ?_) (supDist_le_iff.2 fun κ => ?_)
  · rw [hcoord, hcoord]; exact cycNorm_le_supDist _ _ _
  · have h := cycNorm_le_supDist
      (cidx i (swapJ (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) μ ν x))
      (cidx i (swapJ (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) μ ν y)) (Equiv.swap μ ν κ)
    rw [hcoord, hcoord, Equiv.swap_apply_self] at h
    exact h

/-- The group generated by translations by `s`, reflections about `s` and coordinate exchanges
preserves the block-index distances at all scales `i ≤ J` when `L ^ i ∣ s` for `i ≤ J`. -/
theorem cubeIso_of_mem_symGroupBy {J s : ℕ} (hJ : J ≤ k) (hs : ∀ i ≤ J, L ^ i ∣ s)
    {g : Equiv.Perm (CTorus d L N₁ m₁ k)} (hg : g ∈ symGroupBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s) :
    CubeIso J g := by
  unfold symGroupBy at hg
  refine Subgroup.closure_induction (p := fun g _ => CubeIso J g) ?_ (cubeIso_one J)
    (fun _ _ _ _ h1 h2 => h1.mul h2) (fun _ _ h => h.inv) hg
  rintro g ((⟨μ, rfl⟩ | ⟨μ, rfl⟩) | ⟨μ, ν, rfl⟩)
  · exact cubeIso_transBy hJ hs μ
  · exact cubeIso_flipBy hJ hs μ
  · exact cubeIso_swapJ μ ν


/-! ### The layers of the minimal set on the class torus, and their equivariance -/

/-- The layers of `𝔹_j(X)` by recursion on the class torus (`t = 0` is `Ω_j(X)`, the union of
the `𝒞_j`-cubes contained in `X`; `t + 1` is the `5 L`-neighbourhood in the block indices of
scale `j - (t + 1)`; P3 (4.4)-(4.6)). -/
def plAux (X : Set (CTorus d L N₁ m₁ k)) (j : ℕ) : ℕ → CTorus d L N₁ m₁ k → Prop
  | 0 => fun z => ∀ y, cidx j y = (cidx j z : Torus d (N₁ * L ^ m₁ * L ^ (k - j))) → y ∈ X
  | t + 1 => fun z => ∃ y, plAux X j t y ∧
      supDist (cidx (j - (t + 1)) z) (cidx (j - (t + 1)) y) ≤ 5 * L

theorem fineCubeIdx_torusCast (i : ℕ) (y : Torus d (1 * (N₁ * L ^ m₁) * L ^ k)) :
    fineCubeIdx 1 (N₁ * L ^ m₁) L k i y =
      cidx i (torusCast y : CTorus d L N₁ m₁ k) := by
  have hc : 1 * (N₁ * L ^ m₁) * L ^ k = N₁ * L ^ m₁ * L ^ k := by rw [Nat.one_mul]
  funext μ
  simp only [fineCubeIdx, cidx, blockMap_apply, blockCoord, torusCast_val hc, Nat.mul_one]

theorem mem_polyFinset_iff {X : Set (CTorus d L N₁ m₁ k)} (y : Torus d (1 * (N₁ * L ^ m₁) * L ^ k)) :
    y ∈ polyFinset X ↔ (torusCast y : CTorus d L N₁ m₁ k) ∈ X := by
  classical
  simp [polyFinset]

theorem minLayerAux_iff {j : ℕ} (X : Set (CTorus d L N₁ m₁ k)) (t : ℕ)
    (w : Torus d (1 * (N₁ * L ^ m₁) * L ^ k)) :
    w ∈ minLayerAux 1 (N₁ * L ^ m₁) L k j (polyFinset X) t ↔
      plAux X j t (torusCast w : CTorus d L N₁ m₁ k) := by
  have hc : 1 * (N₁ * L ^ m₁) * L ^ k = N₁ * L ^ m₁ * L ^ k := by rw [Nat.one_mul]
  induction t generalizing w with
  | zero =>
    simp only [minLayerAux, mem_cubeInterior, plAux, mem_polyFinset_iff, fineCubeIdx_torusCast]
    constructor
    · intro h y hy
      have := h (torusCast y) (by rwa [torusCast_torusCast hc.symm])
      rwa [torusCast_torusCast hc.symm] at this
    · intro h y hy
      exact h _ hy
  | succ t ih =>
    simp only [minLayerAux, mem_nearStep, plAux, fineCubeIdx_torusCast]
    constructor
    · rintro ⟨y, hy, hd⟩
      exact ⟨torusCast y, (ih y).1 hy, hd⟩
    · rintro ⟨y, hy, hd⟩
      refine ⟨torusCast y, (ih _).2 (by rwa [torusCast_torusCast hc.symm]), ?_⟩
      rwa [torusCast_torusCast hc.symm]

/-- **The layers of the minimal generating set on the class torus.** -/
theorem mem_polyGS_Ω_iff {j : ℕ} (hjk : j ≤ k) (X : Set (CTorus d L N₁ m₁ k)) (n : ℕ)
    (z : CTorus d L N₁ m₁ k) :
    z ∈ (polyGS hjk X).Ω n ↔ n ≤ j ∧ plAux X j (j - n) z := by
  classical
  unfold polyGS
  rw [mem_castG_Ω]
  show _ ∈ minLayer 1 (N₁ * L ^ m₁) L k j (polyFinset X) n ↔ _
  unfold minLayer
  by_cases hn : n ≤ j
  · simp only [hn, ite_true, true_and]
    rw [minLayerAux_iff]
    have hc : 1 * (N₁ * L ^ m₁) * L ^ k = N₁ * L ^ m₁ * L ^ k := by rw [Nat.one_mul]
    rw [torusCast_torusCast hc.symm]
  · simp [hn]

theorem cidx_eq_iff {i : ℕ} (x y : CTorus d L N₁ m₁ k) :
    cidx i x = cidx i y ↔ supDist (cidx i x) (cidx i y) = 0 := supDist_eq_zero.symm

theorem plAux_equiv {J : ℕ} {g : Equiv.Perm (CTorus d L N₁ m₁ k)} (hg : CubeIso J g)
    (X : Set (CTorus d L N₁ m₁ k)) {t : ℕ} (ht : t ≤ J) (z : CTorus d L N₁ m₁ k) :
    plAux (g '' X) J t (g z) ↔ plAux X J t z := by
  induction t generalizing z with
  | zero =>
    simp only [plAux]
    constructor
    · intro h y' hy'
      have h0 : cidx J (g y') = cidx J (g z) := by
        rw [cidx_eq_iff, hg J le_rfl, ← cidx_eq_iff]; exact hy'
      exact g.injective.mem_set_image.1 (h _ h0)
    · intro h y hy
      have h0 : cidx J (g.symm y) = cidx J z := by
        rw [cidx_eq_iff, ← hg J le_rfl, Equiv.apply_symm_apply, ← cidx_eq_iff]; exact hy
      exact ⟨g.symm y, h _ h0, by simp⟩
  | succ t ih =>
    simp only [plAux]
    have hi : J - (t + 1) ≤ J := Nat.sub_le _ _
    constructor
    · rintro ⟨y, hy, hd⟩
      refine ⟨g.symm y, (ih (by omega) _).1 (by simpa using hy), ?_⟩
      rw [← hg _ hi, Equiv.apply_symm_apply]
      exact hd
    · rintro ⟨y, hy, hd⟩
      refine ⟨g y, (ih (by omega) _).2 hy, ?_⟩
      rw [hg _ hi]
      exact hd

end Cubes

end Balaban.SmallField.GsSpec
