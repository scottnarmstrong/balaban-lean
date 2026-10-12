module

public import Balaban.LargeField.Region.SymmAff
public import Balaban.LargeField.Operators.Symm
public import Balaban.LargeField.Budget.Fine
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Lattice Euclidean symmetries of the fine torus

A *lattice Euclidean symmetry* `σ : LatTorusSym S n M K` is a `TorusSym` whose action `ef` on the
fine torus is an affine lattice isometry (`AffIso`: a signed permutation of the coordinate directions
composed with a translation) which is *aligned*: the translation is a multiple of `M L^K` (for the
reflected directions, one less than a multiple), so that translations by multiples of `M L^K`,
reflections `x_μ ↦ c - 1 - x_μ` with `M L^K ∣ c` and permutations of the coordinates are covered.

Consequences (proved here): the block maps `blockMap P m` for `P ∣ M L^K` commute with `σ` up to
an affine lattice isometry of the quotient torus (`AffIso.blockMap_toFun`); in particular the
actions `ec j` on the cubes and `eb j` on the blocks are affine isometries (`isAff_ec`, `isAff_eb`),
commute with the coarsening of cubes (`ec_blockMap`), and the level-`q` tori (`torusCast`) carry
the same symmetry (`LatTorusSym.lev`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

/-- Nat arithmetic core of the aligned addition. -/
theorem div_add_aligned {P m A X V q α : ℕ} (hP : 0 < P) (hA : A = P * α)
    (hdm : P * m * q + V = A + X) : ((V / P : ℕ) : ZMod m) = (α : ZMod m) + ((X / P : ℕ) : ZMod m) := by
  have e2 : (A + X) / P = α + X / P := by
    rw [hA, Nat.mul_add_div hP]
  have e3 : (P * m * q + V) / P = m * q + V / P := by
    rw [show P * m * q = P * (m * q) by ring, Nat.mul_add_div hP]
  have : m * q + V / P = α + X / P := by rw [← e3, hdm, e2]
  have h2 : (((m * q + V / P : ℕ)) : ZMod m) = ((α + X / P : ℕ) : ZMod m) := by rw [this]
  push_cast at h2
  simpa using h2

theorem blockCoord_add_aligned {ℓ P m : ℕ} [NeZero ℓ] (hℓ : ℓ = P * m) (hP : 0 < P) {a : ZMod ℓ}
    (ha : P ∣ a.val) (x : ZMod ℓ) :
    blockCoord P m (a + x) = blockCoord P m a + blockCoord P m x := by
  unfold blockCoord
  obtain ⟨α, hα⟩ := ha
  have hv : (a + x).val = (a.val + x.val) % ℓ := ZMod.val_add a x
  have hdm := Nat.div_add_mod (a.val + x.val) ℓ
  rw [← hv] at hdm
  have hdm' : P * m * ((a.val + x.val) / ℓ) + (a + x).val = a.val + x.val := by
    rw [← hℓ]; exact hdm
  have h := div_add_aligned hP hα hdm'
  rw [h, hα, Nat.mul_div_cancel_left _ hP]


/-- Nat arithmetic core of the aligned reflection. -/
theorem div_sub_aligned {P m A X V t α : ℕ} (hP : 0 < P) (hA : A + 1 = P * α)
    (hdm : P * m * t + A = V + X) :
    ((V / P : ℕ) : ZMod m) = (α : ZMod m) - 1 - ((X / P : ℕ) : ZMod m) := by
  set b := X / P with hb
  set r := X % P with hr
  have hX : P * b + r = X := Nat.div_add_mod X P
  have hrP : r < P := Nat.mod_lt X hP
  have h1 : V + r + 1 + P * b = P * (m * t + α) := by
    have : P * (m * t + α) = P * m * t + P * α := by ring
    rw [this]; omega
  have hb' : b < m * t + α := by
    by_contra hcon
    push Not at hcon
    have : P * (m * t + α) ≤ P * b := Nat.mul_le_mul_left _ hcon
    omega
  obtain ⟨Q, hQ⟩ : ∃ Q, m * t + α = b + Q := ⟨m * t + α - b, by omega⟩
  have hQpos : 0 < Q := by omega
  have h2 : V + r + 1 = P * Q := by
    have : P * (m * t + α) = P * b + P * Q := by rw [hQ]; ring
    omega
  have h3 : V / P = Q - 1 := by
    apply Nat.div_eq_of_lt_le
    · obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have : P * (Q' + 1) = P * Q' + P := by ring
      nlinarith
    · obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have : P * (Q' + 1) = P * Q' + P := by ring
      nlinarith
  rw [h3]
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h4 : (((m * t + α : ℕ)) : ZMod m) = ((b + (Q' + 1) : ℕ) : ZMod m) := by rw [hQ]
  push_cast at h4
  simp at h4
  rw [h4]; ring

theorem blockCoord_sub_aligned {ℓ P m : ℕ} [NeZero ℓ] (hℓ : ℓ = P * m) (hP : 0 < P) {a : ZMod ℓ}
    (ha : P ∣ a.val + 1) (x : ZMod ℓ) :
    blockCoord P m (a - x) = blockCoord P m a - blockCoord P m x := by
  unfold blockCoord
  obtain ⟨α, hα⟩ := ha
  have hv : ((a - x) + x).val = ((a - x).val + x.val) % ℓ := ZMod.val_add (a - x) x
  rw [sub_add_cancel] at hv
  have hdm := Nat.div_add_mod ((a - x).val + x.val) ℓ
  rw [← hv] at hdm
  have hdm' : P * m * (((a - x).val + x.val) / ℓ) + a.val = (a - x).val + x.val := by
    rw [← hℓ]; exact hdm
  have h := div_sub_aligned hP hα hdm'
  rw [h]
  have hapos : 0 < α := by
    rcases Nat.eq_zero_or_pos α with h0 | h0
    · rw [h0] at hα; omega
    · exact h0
  have : a.val / P = α - 1 := by
    apply Nat.div_eq_of_lt_le
    · obtain ⟨α', rfl⟩ : ∃ α', α = α' + 1 := ⟨α - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have : P * (α' + 1) = P * α' + P := by ring
      nlinarith
    · obtain ⟨α', rfl⟩ : ∃ α', α = α' + 1 := ⟨α - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have : P * (α' + 1) = P * α' + P := by ring
      nlinarith
  rw [this]
  obtain ⟨α', rfl⟩ : ∃ α', α = α' + 1 := ⟨α - 1, by omega⟩
  simp


section Aligned

variable {d ℓ : ℕ}

/-- The translation of `A` is aligned to the blocks of side `P`: a multiple of `P` for the
preserved directions, one less than a multiple of `P` for the reflected ones. -/
def AffIso.Aligned (A : AffIso d ℓ) (P : ℕ) : Prop :=
  ∀ i, P ∣ (A.shift i).val + (if A.flip (A.perm.symm i) then 1 else 0)

/-- The affine isometry induced on the quotient torus. -/
def AffIso.coarse (A : AffIso d ℓ) (P m : ℕ) : AffIso d m :=
  ⟨A.perm, A.flip, blockMap P m A.shift⟩

theorem AffIso.blockMap_toFun [NeZero ℓ] {P m : ℕ} (A : AffIso d ℓ) (hℓ : ℓ = P * m) (hP : 0 < P)
    (hA : A.Aligned P) (x : Torus d ℓ) :
    blockMap P m (A.toFun x) = (A.coarse P m).toFun (blockMap P m x) := by
  funext i
  simp only [blockMap, AffIso.toFun, AffIso.coarse]
  by_cases hf : A.flip (A.perm.symm i)
  · have h1 := hA i
    simp only [hf, ↓reduceIte] at h1
    have : A.shift i + AffIso.sgn ℓ (A.flip (A.perm.symm i)) * x (A.perm.symm i) =
        A.shift i - x (A.perm.symm i) := by simp [AffIso.sgn, hf]; ring
    rw [this, blockCoord_sub_aligned hℓ hP h1]
    simp [AffIso.sgn, hf]; ring
  · have h1 := hA i
    simp only [hf, Bool.false_eq_true, ↓reduceIte, add_zero] at h1
    have : A.shift i + AffIso.sgn ℓ (A.flip (A.perm.symm i)) * x (A.perm.symm i) =
        A.shift i + x (A.perm.symm i) := by simp [AffIso.sgn, hf]
    rw [this, blockCoord_add_aligned hℓ hP h1]
    simp [AffIso.sgn, hf]

/-- Transport of an affine isometry along an equality of the side lengths. -/
def AffIso.cast {ℓ ℓ' : ℕ} (h : ℓ = ℓ') (A : AffIso d ℓ) : AffIso d ℓ' :=
  ⟨A.perm, A.flip, torusCast h A.shift⟩

theorem AffIso.cast_toFun {ℓ ℓ' : ℕ} (h : ℓ = ℓ') (A : AffIso d ℓ) (x : Torus d ℓ) :
    (A.cast h).toFun (torusCast h x) = torusCast h (A.toFun x) := by
  subst h; rfl

theorem AffIso.cast_aligned {ℓ ℓ' : ℕ} (h : ℓ = ℓ') (A : AffIso d ℓ) {P : ℕ}
    (hA : A.Aligned P) : (A.cast h).Aligned P := by
  subst h; exact hA

theorem AffIso.coarse_cast {ℓ ℓ' : ℕ} (h : ℓ = ℓ') (A : AffIso d ℓ) (P m : ℕ) :
    (A.cast h).coarse P m = A.coarse P m := by
  subst h; rfl

theorem torusCast_blockMap {ℓ ℓ' : ℕ} (h : ℓ = ℓ') (P m : ℕ) (x : Torus d ℓ) :
    blockMap P m (torusCast h x) = blockMap P m x := by
  subst h; rfl

end Aligned


section Struct

variable (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (M K : ℕ) [NeZero M] [NeZero S.L]

/-- A **lattice Euclidean symmetry** of the fine torus: a `TorusSym` whose action `ef` on the fine
torus is an affine lattice isometry (`aff`: signed permutation of the coordinate directions and
translation) aligned to the blocks of side `M L^K` (`align`: translations by multiples of `M L^K`,
reflections `x_μ ↦ c - 1 - x_μ` with `M L^K ∣ c`). -/
structure LatTorusSym extends TorusSym S n M K where
  /-- the affine lattice isometry -/
  aff : AffIso S.d (M * n K * S.L ^ K)
  ef_aff : ∀ x, ef x = aff.toFun x
  /-- translations/reflections by multiples of `M L^K` -/
  align : aff.Aligned (M * S.L ^ K)

/-- The identity symmetry. -/
def LatTorusSym.refl : LatTorusSym S n M K where
  ef := 1
  eb := fun _ => 1
  ec := fun _ => 1
  jblock := fun _ _ _ => rfl
  cube := fun _ _ _ => rfl
  dist := fun _ _ _ => rfl
  aff := ⟨1, fun _ => false, 0⟩
  ef_aff := fun x => by
    funext i; simp [AffIso.toFun, AffIso.sgn]; rfl
  align := fun i => by simp

/-- Hard rule 10: the structure is inhabited (by the identity). -/
theorem nonempty_latTorusSym : Nonempty (LatTorusSym S n M K) := ⟨LatTorusSym.refl S n M K⟩

variable {S n M K}

theorem LatTorusSym.aligned_of_dvd (σ : LatTorusSym S n M K) {P : ℕ} (h : P ∣ M * S.L ^ K) :
    σ.aff.Aligned P := fun i => dvd_trans h (σ.align i)

theorem LatTorusSym.blockMap_ef (σ : LatTorusSym S n M K) {P m : ℕ}
    (hℓ : M * n K * S.L ^ K = P * m) (hP : 0 < P) (hdiv : P ∣ M * S.L ^ K)
    (x : Torus S.d (M * n K * S.L ^ K)) :
    blockMap P m (σ.ef x) = (σ.aff.coarse P m).toFun (blockMap P m x) := by
  rw [σ.ef_aff]
  exact AffIso.blockMap_toFun σ.aff hℓ hP (σ.aligned_of_dvd hdiv) x

theorem dvd_pow_mul {j K : ℕ} (hjK : j ≤ K) (M L : ℕ) : L ^ j * M ∣ M * L ^ K := by
  rw [mul_comm M]
  exact Nat.mul_dvd_mul_right (pow_dvd_pow L hjK) M

theorem LatTorusSym.ec_eq (σ : LatTorusSym S n M K)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {j : ℕ} (hjK : j ≤ K) (y : Torus S.d (n j)) :
    σ.ec j y = (σ.aff.coarse (S.L ^ j * M) (n j)).toFun y := by
  obtain ⟨x, rfl⟩ := cubeMap_surjective (S := S) (n := n) (M := M) (K := K) hnn hjK y
  rw [← σ.cube j hjK x]
  have hpos : 0 < S.L ^ j * M := by
    have := NeZero.pos S.L; have := NeZero.pos M; positivity
  exact σ.blockMap_ef (fine_eq hnn hjK) hpos (dvd_pow_mul hjK M S.L) x

theorem LatTorusSym.isAff_ec (σ : LatTorusSym S n M K)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {j : ℕ} (hjK : j ≤ K) : IsAff (σ.ec j) :=
  ⟨σ.aff.coarse (S.L ^ j * M) (n j), σ.ec_eq hnn hjK⟩

theorem LatTorusSym.eb_eq (σ : LatTorusSym S n M K) {j : ℕ} (hjK : j ≤ K)
    (y : BlockAt S n M K j) :
    σ.eb j y = (σ.aff.coarse (S.L ^ j) (M * n K * S.L ^ (K - j))).toFun y := by
  obtain ⟨x, rfl⟩ := exists_site_in_block (S := S) (n := n) (M := M) hjK y
  rw [← σ.jblock j hjK x]
  have hpos : 0 < S.L ^ j := by have := NeZero.pos S.L; positivity
  have hdiv : S.L ^ j ∣ M * S.L ^ K := Dvd.dvd.mul_left (pow_dvd_pow S.L hjK) M
  exact σ.blockMap_ef (Multiscale.side_eq hjK) hpos hdiv x

theorem LatTorusSym.isAff_eb (σ : LatTorusSym S n M K) {j : ℕ} (hjK : j ≤ K) :
    IsAff (σ.eb j) :=
  ⟨σ.aff.coarse (S.L ^ j) (M * n K * S.L ^ (K - j)), σ.eb_eq hjK⟩

/-- The symmetry commutes with the coarsening of cubes. -/
theorem LatTorusSym.ec_blockMap (σ : LatTorusSym S n M K)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {j : ℕ} (hj : j + 1 ≤ K) (y : Torus S.d (n j)) :
    σ.ec (j + 1) (blockMap S.L (n (j + 1)) y) = blockMap S.L (n (j + 1)) (σ.ec j y) := by
  obtain ⟨x, rfl⟩ := cubeMap_surjective (S := S) (n := n) (M := M) (K := K) hnn (by omega : j ≤ K) y
  rw [cubeMap_succ hnn hj, ← σ.cube (j + 1) hj x, ← σ.cube j (by omega) x, cubeMap_succ hnn hj]

end Struct

end Balaban.LargeField
