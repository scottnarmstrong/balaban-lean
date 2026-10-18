/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusLift
public import Balaban.LargeField.Background.TwoTorusOps
public import Balaban.LargeField.Background.StepGenSetsFlow

/-!
# The set operations of the generating sets, on integer lifts

For a set `A` of a torus `𝕋_m`, `pbZ m A` is the set of integer vectors `w` with `zcast m w ∈ A`.
The operations `cubeInterior`, `nearStep`, `minLayer`, `boundaryLayer`, `cubePre` and the
neighbourhoods `nbhd` of cubes of the generating sets of Definition II.2.4 become on these sets the
operations `cintZ`, `nearZ`, `layZ`, `bdLayZ`, `dilZ` of `TwoTorusOps.lean`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.LargeField

set_option linter.unusedSectionVars false

section Pb

variable {d : ℕ}

/-- The integer vectors whose image in `𝕋_m` lies in `A`. -/
def pbZ (m : ℕ) (A : Set (Torus d m)) : Set (Fin d → ℤ) := {w | zcast m w ∈ A}

theorem mem_pbZ {m : ℕ} {A : Set (Torus d m)} {w : Fin d → ℤ} : w ∈ pbZ m A ↔ zcast m w ∈ A :=
  Iff.rfl

theorem pbZ_inter {m : ℕ} (A B : Set (Torus d m)) : pbZ m (A ∩ B) = pbZ m A ∩ pbZ m B := rfl

theorem exists_rep {m : ℕ} [NeZero m] (y : Torus d m) : ∃ z : Fin d → ℤ, zcast m z = y := by
  refine ⟨fun μ => (((y μ).val : ℕ) : ℤ), ?_⟩
  funext μ
  simp [zcast]

theorem exists_lift_block {m P n : ℕ} (hm : m = P * n) (hP : 0 < P) (z₀ τ : Fin d → ℤ)
    (h : ∀ μ, (n : ℤ) ∣ z₀ μ / (P : ℤ) - τ μ) :
    ∃ z : Fin d → ℤ, zcast m z = zcast m z₀ ∧ ∀ μ, z μ / (P : ℤ) = τ μ := by
  choose k hk using h
  have hP' : (P : ℤ) ≠ 0 := by exact_mod_cast hP.ne'
  refine ⟨fun μ => z₀ μ + (P : ℤ) * (-(n * k μ)), ?_, fun μ => ?_⟩
  · rw [zcast_eq_iff]
    intro μ
    refine ⟨-k μ, ?_⟩
    rw [hm]; push_cast; ring
  · rw [Int.add_mul_ediv_left _ _ hP']
    have := hk μ
    linarith

end Pb

section Ops

variable {d M1 N₁ L q : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

theorem fineCubeIdx_zcast {n : ℕ} (hn : n ≤ q) (w : Fin d → ℤ) :
    fineCubeIdx M1 N₁ L q n (zcast (M1 * N₁ * L ^ q) w) =
      zcast (N₁ * L ^ (q - n)) (fun μ => w μ / ((L ^ n * M1 : ℕ) : ℤ)) :=
  blockMap_zcast (fine_eq_cube hn) (Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) n)
    (Nat.pos_of_ne_zero (NeZero.ne M1))) w

theorem pbZ_cubeInterior {j : ℕ} (hj : j ≤ q) (X : Finset (Torus d (M1 * N₁ * L ^ q))) :
    pbZ (M1 * N₁ * L ^ q) ((cubeInterior M1 N₁ L q j X : Finset _) : Set (Torus d (M1 * N₁ * L ^ q))) =
      cintZ (L ^ j * M1) (pbZ (M1 * N₁ * L ^ q) ((X : Finset _) : Set (Torus d (M1 * N₁ * L ^ q)))) := by
  have hP : 0 < L ^ j * M1 :=
    Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j) (Nat.pos_of_ne_zero (NeZero.ne M1))
  ext w
  simp only [mem_pbZ, Finset.mem_coe, mem_cubeInterior, cintZ, Set.mem_ofPred_eq]
  rw [fineCubeIdx_zcast hj]
  constructor
  · intro h z hz
    refine h (zcast _ z) ?_
    rw [fineCubeIdx_zcast hj]
    congr 1
    funext μ
    exact hz μ
  · intro h y hy
    obtain ⟨z₀, rfl⟩ := exists_rep y
    rw [fineCubeIdx_zcast hj] at hy
    have hd := (zcast_eq_iff _ _ _).1 hy
    obtain ⟨z, hzz, hz⟩ := exists_lift_block (n := N₁ * L ^ (q - j)) (fine_eq_cube hj) hP z₀
      (fun μ => w μ / ((L ^ j * M1 : ℕ) : ℤ)) hd
    rw [← hzz]
    exact h z hz

theorem pbZ_nearStep {n : ℕ} (hn : n ≤ q) (A : Finset (Torus d (M1 * N₁ * L ^ q))) :
    pbZ (M1 * N₁ * L ^ q) ((nearStep M1 N₁ L q n A : Finset _) : Set (Torus d (M1 * N₁ * L ^ q))) =
      nearZ (L ^ n * M1) (5 * L) (pbZ (M1 * N₁ * L ^ q) ((A : Finset _) : Set (Torus d (M1 * N₁ * L ^ q)))) := by
  have hP : 0 < L ^ n * M1 :=
    Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) n) (Nat.pos_of_ne_zero (NeZero.ne M1))
  ext w
  simp only [mem_pbZ, Finset.mem_coe, mem_nearStep, nearZ, Set.mem_ofPred_eq]
  rw [fineCubeIdx_zcast hn]
  constructor
  · rintro ⟨y, hyA, hy⟩
    obtain ⟨z₀, rfl⟩ := exists_rep y
    rw [fineCubeIdx_zcast hn, supDist_le_iff] at hy
    have hy' : ∀ μ, ∃ t : ℤ, |t| ≤ ((5 * L : ℕ) : ℤ) ∧
        ((t : ℤ) : ZMod (N₁ * L ^ (q - n))) =
          (((w μ / ((L ^ n * M1 : ℕ) : ℤ) - z₀ μ / ((L ^ n * M1 : ℕ) : ℤ) : ℤ)) :
            ZMod (N₁ * L ^ (q - n))) := by
      intro μ
      have := (cycNorm_le_iff _ _).1 (hy μ)
      obtain ⟨t, ht, htc⟩ := this
      refine ⟨t, by exact_mod_cast ht, ?_⟩
      rw [htc]
      simp [zcast]
    choose t ht htc using hy'
    obtain ⟨z, hzz, hz⟩ := exists_lift_block (n := N₁ * L ^ (q - n)) (fine_eq_cube hn) hP z₀
      (fun μ => w μ / ((L ^ n * M1 : ℕ) : ℤ) - t μ) (fun μ => by
        have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (htc μ)
        obtain ⟨a, ha⟩ := this
        exact ⟨-a, by linarith⟩)
    refine ⟨z, ?_, fun μ => ?_⟩
    · rw [hzz]; exact hyA
    · rw [hz μ]
      have := ht μ
      rw [show w μ / ((L ^ n * M1 : ℕ) : ℤ) - t μ - w μ / ((L ^ n * M1 : ℕ) : ℤ) = -t μ by ring,
        abs_neg]
      exact_mod_cast this
  · rintro ⟨z, hzA, hz⟩
    refine ⟨zcast _ z, hzA, ?_⟩
    rw [fineCubeIdx_zcast hn, supDist_le_iff]
    intro μ
    rw [cycNorm_le_iff]
    refine ⟨w μ / ((L ^ n * M1 : ℕ) : ℤ) - z μ / ((L ^ n * M1 : ℕ) : ℤ), ?_, ?_⟩
    · rw [abs_sub_comm]; exact_mod_cast hz μ
    · simp [zcast]

theorem pbZ_minLayerAux {j : ℕ} (hj : j ≤ q) (X : Finset (Torus d (M1 * N₁ * L ^ q))) :
    ∀ t : ℕ, t ≤ j →
      pbZ (M1 * N₁ * L ^ q) ((minLayerAux M1 N₁ L q j X t : Finset _) :
          Set (Torus d (M1 * N₁ * L ^ q))) =
        layZ L M1 j (pbZ (M1 * N₁ * L ^ q) ((X : Finset _) : Set (Torus d (M1 * N₁ * L ^ q)))) t := by
  intro t
  induction t with
  | zero => intro _; exact pbZ_cubeInterior hj X
  | succ t ih =>
    intro ht
    simp only [minLayerAux, layZ]
    rw [pbZ_nearStep (by omega), ih (by omega)]

theorem pbZ_minLayer {j : ℕ} (hj : j ≤ q) (X : Finset (Torus d (M1 * N₁ * L ^ q))) (n : ℕ) :
    pbZ (M1 * N₁ * L ^ q) ((minLayer M1 N₁ L q j X n : Finset _) :
        Set (Torus d (M1 * N₁ * L ^ q))) =
      minLayerZ L M1 j (pbZ (M1 * N₁ * L ^ q) ((X : Finset _) : Set (Torus d (M1 * N₁ * L ^ q)))) n := by
  unfold minLayer minLayerZ
  by_cases hn : n ≤ j
  · simp only [hn, ↓reduceIte]
    exact pbZ_minLayerAux hj X _ (by omega)
  · simp only [hn, ↓reduceIte, Finset.coe_empty]
    ext w; simp [pbZ]

theorem pbZ_boundaryLayer (k : ℕ) (W U Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1)))) (n : ℕ) :
    pbZ (M1 * N₁ * L ^ (k + 1)) ((boundaryLayer M1 N₁ L k W U Om n : Finset _) :
        Set (Torus d (M1 * N₁ * L ^ (k + 1)))) =
      bdLayZ L M1 k (pbZ (M1 * N₁ * L ^ (k + 1)) (W : Set _))
        (pbZ (M1 * N₁ * L ^ (k + 1)) (U : Set _)) (pbZ (M1 * N₁ * L ^ (k + 1)) (Om : Set _)) n := by
  unfold boundaryLayer bdLayZ
  rw [← pbZ_minLayer (Nat.le_succ k), ← pbZ_minLayer le_rfl]
  ext w
  simp [pbZ]

end Ops

section Coarse

variable {d : ℕ}

/-- The neighbourhood `nbhd r A` of a set of the coarse torus `𝕋_n`, on integer lifts. -/
theorem mem_nbhd_zcast {n : ℕ} [NeZero n] {r : ℕ} {A : Set (Torus d n)} (u : Fin d → ℤ) :
    zcast n u ∈ nbhd r A ↔ ∃ s : Fin d → ℤ, (∀ μ, |s μ| ≤ r) ∧ zcast n (u + s) ∈ A := by
  rw [mem_nbhd]
  constructor
  · rintro ⟨x, hxA, hx⟩
    obtain ⟨u', rfl⟩ := exists_rep x
    rw [supDist_le_iff] at hx
    have hx' : ∀ μ, ∃ t : ℤ, |t| ≤ (r : ℤ) ∧ ((t : ℤ) : ZMod n) = (u μ : ZMod n) - (u' μ : ZMod n) := by
      intro μ
      obtain ⟨t, ht, htc⟩ := (cycNorm_le_iff _ _).1 (hx μ)
      exact ⟨t, by exact_mod_cast ht, by rw [htc]; simp [zcast]⟩
    choose t ht htc using hx'
    refine ⟨fun μ => -t μ, fun μ => by simpa using ht μ, ?_⟩
    have : zcast n (u + fun μ => -t μ) = zcast n u' := by
      funext μ
      simp only [zcast, Pi.add_apply]
      push_cast
      rw [htc μ]
      ring
    rw [this]; exact hxA
  · rintro ⟨s, hs, hmem⟩
    refine ⟨zcast n (u + s), hmem, ?_⟩
    rw [supDist_le_iff]
    intro μ
    rw [cycNorm_le_iff]
    refine ⟨-s μ, by simpa using hs μ, ?_⟩
    simp [zcast]

end Coarse

section CubePb

variable {d M1 N₁ L q : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

theorem pbZ_cubePre {P n : ℕ} (hq : M1 * N₁ * L ^ q = P * n) (hP : 0 < P) (A : Set (Torus d n)) :
    pbZ (M1 * N₁ * L ^ q) ((cubePre M1 N₁ L q P n A : Finset _) :
        Set (Torus d (M1 * N₁ * L ^ q))) =
      {w | zcast n (fun μ => w μ / (P : ℤ)) ∈ A} := by
  ext w
  simp only [mem_pbZ, Finset.mem_coe, mem_cubePre, Set.mem_ofPred_eq]
  rw [blockMap_zcast hq hP]

theorem pbZ_cubePre_nbhd {P n : ℕ} [NeZero n] (hq : M1 * N₁ * L ^ q = P * n) (hP : 0 < P) (r : ℕ)
    (A : Set (Torus d n)) :
    pbZ (M1 * N₁ * L ^ q) ((cubePre M1 N₁ L q P n (nbhd r A) : Finset _) :
        Set (Torus d (M1 * N₁ * L ^ q))) =
      dilZ P r (pbZ (M1 * N₁ * L ^ q) ((cubePre M1 N₁ L q P n A : Finset _) :
        Set (Torus d (M1 * N₁ * L ^ q)))) := by
  have hP' : (P : ℤ) ≠ 0 := by exact_mod_cast hP.ne'
  rw [pbZ_cubePre hq hP, pbZ_cubePre hq hP]
  ext w
  simp only [Set.mem_ofPred_eq, dilZ]
  rw [mem_nbhd_zcast (fun μ => w μ / (P : ℤ))]
  constructor
  · rintro ⟨s, hs, hmem⟩
    refine ⟨s, hs, ?_⟩
    have : (fun μ => (w + shiftZ P s) μ / (P : ℤ)) = (fun μ => w μ / (P : ℤ)) + s := by
      funext μ
      simp only [Pi.add_apply, shiftZ]
      rw [Int.add_mul_ediv_left _ _ hP']
    rw [this]; exact hmem
  · rintro ⟨s, hs, hmem⟩
    refine ⟨s, hs, ?_⟩
    have : (fun μ => (w + shiftZ P s) μ / (P : ℤ)) = (fun μ => w μ / (P : ℤ)) + s := by
      funext μ
      simp only [Pi.add_apply, shiftZ]
      rw [Int.add_mul_ediv_left _ _ hP']
    rw [this] at hmem; exact hmem

theorem pbZ_cubePre_compl {P n : ℕ} (hq : M1 * N₁ * L ^ q = P * n) (hP : 0 < P) (A : Set (Torus d n)) :
    pbZ (M1 * N₁ * L ^ q) ((cubePre M1 N₁ L q P n Aᶜ : Finset _) :
        Set (Torus d (M1 * N₁ * L ^ q))) =
      (pbZ (M1 * N₁ * L ^ q) ((cubePre M1 N₁ L q P n A : Finset _) :
        Set (Torus d (M1 * N₁ * L ^ q))))ᶜ := by
  rw [pbZ_cubePre hq hP, pbZ_cubePre hq hP]
  ext w
  simp [Set.mem_ofPred_eq]

end CubePb

section Step

variable {d M1 c n1 L k n0 N : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} {ω : ℕ} {Zp : Set (Torus d n1)}

theorem fine_eq_P1 : M1 * (c * n1) * L ^ (k + 1) = (L ^ (k + 1) * (c * M1)) * n1 := by ring

theorem fine_eq_P0 (hn : n0 = L * n1) :
    M1 * (c * n1) * L ^ (k + 1) = (L ^ k * (c * M1)) * n0 := by rw [hn]; ring

theorem P1_pos : 0 < L ^ (k + 1) * (c * M1) :=
  Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
    (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne c)) (Nat.pos_of_ne_zero (NeZero.ne M1)))

theorem P0_pos : 0 < L ^ k * (c * M1) :=
  Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
    (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne c)) (Nat.pos_of_ne_zero (NeZero.ne M1)))

theorem pbZ_fineK1 (A : Set (Torus d n1)) :
    pbZ (M1 * (c * n1) * L ^ (k + 1)) ((fineK1 M1 c n1 L k A : Finset _) :
        Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))) =
      {w | zcast n1 (fun μ => w μ / ((L ^ (k + 1) * (c * M1) : ℕ) : ℤ)) ∈ A} :=
  pbZ_cubePre fine_eq_P1 P1_pos A

theorem pbZ_stepU (ρ : ℕ) (A : Set (Torus d n1)) :
    pbZ (M1 * (c * n1) * L ^ (k + 1)) ((stepU M1 c n1 L k ρ A : Finset _) :
        Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))) =
      dilZ (L ^ (k + 1) * (c * M1)) (ρ + 1) (pbZ (M1 * (c * n1) * L ^ (k + 1))
        ((fineK1 M1 c n1 L k A : Finset _) : Set (Torus d (M1 * (c * n1) * L ^ (k + 1))))) := by
  unfold stepU fineK1 thick
  exact pbZ_cubePre_nbhd fine_eq_P1 P1_pos _ _

theorem pbZ_stepW (hn : n0 = L * n1) (ρ' : ℕ) (Z : Set (Torus d n0)) :
    pbZ (M1 * (c * n1) * L ^ (k + 1)) ((stepW M1 c n1 L k ρ' Z : Finset _) :
        Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))) =
      dilZ (L ^ k * (c * M1)) (ρ' + 1) (dilZ (L ^ k * (c * M1)) (ρ' + 1)
        (pbZ (M1 * (c * n1) * L ^ (k + 1))
          ((fineK M1 c n1 L k n0 Z : Finset _) :
            Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))))ᶜ) := by
  unfold stepW fineK thick2 thick
  rw [pbZ_cubePre_nbhd (fine_eq_P0 hn) P0_pos, pbZ_cubePre_nbhd (fine_eq_P0 hn) P0_pos,
    pbZ_cubePre_compl (fine_eq_P0 hn) P0_pos]

/-- The layers `Ω_n` of the local boundary family, on integer lifts. -/
theorem pbZ_genBoundaryLocal_Ω (st : RegionStep d L n0 n1 Rprev Rk) (hc : 14 ≤ c)
    (hn : n0 = L * n1) (hL : 2 ≤ L) (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hω : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω)
    (hZ : st.Omegaᶜ ⊆ Zp) {Z' : Finset (Torus d n1)} (hZ' : Z' ∈ comps ω (finOf Zp)) (n : ℕ) :
    pbZ (M1 * (c * n1) * L ^ (k + 1))
        ((((genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ').Ω n : Finset _)) :
          Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))) =
      bdLayZ L M1 k
        (dilZ (L ^ k * (c * M1)) (⌊Rprev⌋₊ + 1) (dilZ (L ^ k * (c * M1)) (⌊Rprev⌋₊ + 1)
            (pbZ (M1 * (c * n1) * L ^ (k + 1))
              ((fineK M1 c n1 L k n0 st.Z : Finset _) :
                Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))))ᶜ) ∩
          dilZ (L ^ (k + 1) * (c * M1)) (⌊Rk⌋₊ + 1)
            (pbZ (M1 * (c * n1) * L ^ (k + 1))
              ((fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _) :
                Set (Torus d (M1 * (c * n1) * L ^ (k + 1))))))
        (dilZ (L ^ (k + 1) * (c * M1)) (⌊Rk⌋₊ + 1)
          (pbZ (M1 * (c * n1) * L ^ (k + 1))
            ((fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _) :
              Set (Torus d (M1 * (c * n1) * L ^ (k + 1))))))
        (pbZ (M1 * (c * n1) * L ^ (k + 1))
          ((fineK1 M1 c n1 L k st.Omega : Finset _) :
            Set (Torus d (M1 * (c * n1) * L ^ (k + 1))))) n := by
  unfold genBoundaryLocal
  rw [boundaryGenSet_Ω, pbZ_boundaryLayer]
  unfold stepWLoc
  rw [Finset.coe_inter, pbZ_inter, pbZ_stepU, pbZ_stepW hn]

end Step

end Balaban.RootFSpine
