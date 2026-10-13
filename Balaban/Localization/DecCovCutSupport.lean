/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledSqrt
public import Balaban.Localization.DecoupledXLocal
import Mathlib.Tactic.Linarith

/-!
# Support and component structure of `Gsx`, `decM`, `decPi` and `decCov`

First step of the cut factorization of the decoupled logarithm (DET-CUT-FACTOR of
`notes/phase1/ROOTDET.md` §2; statement in the module doc of `DecLogZero.lean`).

**The x-shift (T1).** The x-variant Green operator `Gsx` of `DecoupledX.lean` is *not* the
un-shifted `Gs` of `Decoupled.lean` at modified arguments: the shift `x` enters the operator
`H_{k,x}` through the averaging form (`xAvgMatrix` with the coefficients `xS1 (a k) x`,
`xS2 (a k) (aT / L²) x`, and the top-layer coefficient `aT`), not through the mass `ν` or the
potential `α`. So no identity `Gsx … = Gs …` at other arguments holds in general. The landed
support and locality theorems for `Gsx` itself are `dg5x_support` and `dg5x_local`
(`DecoupledXLocal.lean`), proved by the argument of `dg5_support`, `dg5_local`; the coefficient
`sProd s q` vanishes for inactive centres. Here they are used in matrix form.

Proved:

* `Gsx_apply_eq_zero_of_not_core`: `(Gsx … s) y y' = 0` unless `y` lies in `Core s`;
* `Gsx_apply_eq_zero_of_comp`: if `Y'` is a union of nearest-neighbour components of `Yreg s`,
  `y ∈ Y'`, `y' ∉ Y'`, then `(Gsx … s) y y' = 0` (and the dependence on the potential on `Y'` is
  `dg5x_local`, which is the landed statement and is not repeated);
* `Gsx_BD`: `Gsx` has no matrix elements between `Y'` and its complement; so `liftOp Gsx` too;
* `BD.inv`: the inverse of an invertible block-diagonal matrix is block diagonal;
* `decM_BD`, `decPi_BD`, `decCov_sub_BD`, `decCov_BD`: `decM`, its inverse, `decPi` and
  `decCov - covA`, under the explicit provisos below.

**Provisos.** (i) `H_{k,x}` (`xDirichletOperator`) has no matrix element `H y y'` with `y'` in
the core of `s` between `Y'` and its complement; this holds when `Y'` is a union of blocks of the
averaging form and the boundary of `Y'` has no nearest-neighbour bond into the core. (ii) the rows
of `Q` and of `P` respect a splitting `cκ` of the coarse index set: `Q κ y ≠ 0` implies
`cκ κ ↔ y ∈ Y'`, `P κ κ' ≠ 0` implies `cκ κ ↔ cκ κ'`. These are properties of the landed matrices
and are not proved here.

Not proved here: block diagonality of the whole `decLog` (the integral over `x` and the baseline
blocks), the forest bound and the hull count.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section BD

variable {ι ι' ι'' : Type*}

/-- `M` has no matrix element between sites with different labels (`c`, `c'` are predicates). -/
abbrev BD (c : ι → Prop) (c' : ι' → Prop) (M : Matrix ι ι' ℂ) : Prop :=
  ∀ i j, M i j ≠ 0 → (c i ↔ c' j)

theorem BD.mul [Fintype ι'] {c : ι → Prop} {c' : ι' → Prop} {c'' : ι'' → Prop}
    {M : Matrix ι ι' ℂ} {N : Matrix ι' ι'' ℂ} (hM : BD c c' M) (hN : BD c' c'' N) :
    BD c c'' (M * N) := by
  intro i j h
  rw [Matrix.mul_apply] at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact (hM i k (left_ne_zero_of_mul hk)).trans (hN k j (right_ne_zero_of_mul hk))

theorem BD.add {c : ι → Prop} {c' : ι' → Prop} {M N : Matrix ι ι' ℂ} (hM : BD c c' M)
    (hN : BD c c' N) : BD c c' (M + N) := by
  intro i j h
  by_cases h1 : M i j = 0
  · rw [Matrix.add_apply, h1, zero_add] at h; exact hN i j h
  · exact hM i j h1

theorem BD.neg {c : ι → Prop} {c' : ι' → Prop} {M : Matrix ι ι' ℂ} (hM : BD c c' M) :
    BD c c' (-M) := fun i j h => hM i j (by simpa using h)

theorem BD.sub {c : ι → Prop} {c' : ι' → Prop} {M N : Matrix ι ι' ℂ} (hM : BD c c' M)
    (hN : BD c c' N) : BD c c' (M - N) := by
  rw [sub_eq_add_neg]; exact hM.add hN.neg

theorem BD.smul {c : ι → Prop} {c' : ι' → Prop} {M : Matrix ι ι' ℂ} (r : ℂ) (hM : BD c c' M) :
    BD c c' (r • M) := fun i j h => hM i j (fun h0 => h (by simp [h0]))

theorem BD.one [DecidableEq ι] (c : ι → Prop) : BD c c (1 : Matrix ι ι ℂ) := by
  intro i j h
  by_cases hij : i = j
  · subst hij; exact Iff.rfl
  · exact absurd (Matrix.one_apply_ne hij) h

theorem BD.transpose {c : ι → Prop} {c' : ι' → Prop} {M : Matrix ι ι' ℂ} (hM : BD c c' M) :
    BD c' c Mᵀ := fun i j h => (hM j i h).symm

/-- **The inverse of an invertible block-diagonal matrix is block diagonal.** -/
theorem BD.inv [Fintype ι] [DecidableEq ι] {c : ι → Prop} {M : Matrix ι ι ℂ} (hM : BD c c M)
    (hU : IsUnit M) : BD c c M⁻¹ := by
  classical
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).1 hU
  set D : Matrix ι ι ℂ := Matrix.diagonal fun i => if c i then 1 else 0 with hD
  have hcomm : M * D = D * M := by
    ext i j
    rw [hD, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases h : M i j = 0
    · simp [h]
    · have := hM i j h
      by_cases hc : c i <;> simp_all
  have h2 : M⁻¹ * D = D * M⁻¹ := by
    calc M⁻¹ * D = M⁻¹ * (D * M) * M⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = M⁻¹ * (M * D) * M⁻¹ := by rw [hcomm]
      _ = D * M⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  intro i j h
  have e := congrFun (congrFun h2 i) j
  rw [hD, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  by_cases hi : c i <;> by_cases hj : c j <;> simp_all

theorem BD.liftOp {N : ℕ} [DecidableEq ι] {c : ι → Prop} {c' : ι' → Prop} [DecidableEq ι']
    {M : Matrix ι ι' ℂ} (hM : BD c c' M) :
    BD (fun p : ι × Fin N => c p.1) (fun p : ι' × Fin N => c' p.1)
      (fun p q => if p.2 = q.2 then M p.1 q.1 else 0) := by
  intro p q h
  by_cases hp : p.2 = q.2
  · simp only [hp, ite_true] at h; exact hM _ _ h
  · simp [hp] at h

end BD

section Gsx

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}
  {α : G.Ω 1 → ℂ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}

theorem mulVec_single_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (y y' : ι) :
    (M *ᵥ Pi.single y' (1 : ℂ)) y = M y y' := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- **T2.** `(Gsx … s) y y' = 0` unless `y` lies in the active core. -/
theorem Gsx_apply_eq_zero_of_not_core (y y' : G.Ω 1)
    (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∉ Core G s) : Gsx G a aT x ν α s y y' = 0 := by
  by_contra h
  refine hy (dg5x_support (a := a) (aT := aT) (x := x) (ν := ν) (α := α) s
    (Pi.single y' (1 : ℂ)) y ?_)
  rw [mulVec_single_apply]; exact h

theorem mem_Yreg_of_mem_core (y : G.Ω 1) (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Core G s) :
    (y : CTorus d L N₁ m₁ (k + 1)) ∈ Yreg G s := by
  classical
  unfold Core at hy
  rw [Finset.mem_biUnion] at hy
  obtain ⟨z, hz, hyz⟩ := hy
  unfold Yreg
  rw [Finset.mem_filter, Finset.mem_biUnion]
  exact ⟨⟨z, hz, box_subset_hatBox z (coreBox_subset_box hyz)⟩, y.2⟩

/-- **T3.** No matrix element of `Gsx` from a site of a union `Y'` of nearest-neighbour components
of `Yreg s` to a site outside it. -/
theorem Gsx_apply_eq_zero_of_comp (S : XSetting G a aT ν) (hx : 0 ≤ x) (hconn : HatConn G)
    (hα : AdmPot G α) (hU : IsUnit (1 - Kcalx G a aT x ν α s))
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
    {y y' : G.Ω 1} (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
    (hy' : (y' : CTorus d L N₁ m₁ (k + 1)) ∉ Y') : Gsx G a aT x ν α s y y' = 0 := by
  have h := dg5x_local S hx hconn hα hα hU hU hY (fun _ _ => rfl)
    (f := Pi.single y' (1 : ℂ)) (f' := 0) (fun z hz => by
      have : z ≠ y' := fun h => hy' (h ▸ hz)
      simp [this]) y hy
  rw [mulVec_single_apply] at h
  simpa using h

omit [NeZero N₁] [NeZero L] in
/-- The complement of a union of components inside `Yreg s` is again a union of components. -/
theorem isNnComp_sdiff {Z Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (h : IsNnComp Z Y') :
    IsNnComp Z (Z \ Y') := by
  classical
  refine ⟨Finset.sdiff_subset, fun u hu v hv hadj => ?_⟩
  rw [Finset.mem_sdiff] at hu ⊢
  refine ⟨hv, fun hvY => hu.2 ?_⟩
  exact h.2 v hvY u hu.1 hadj.symm

/-- **T3, block form.** `Gsx` has no matrix elements between a union `Y'` of components of
`Yreg s` and its complement (in both directions). -/
theorem Gsx_BD (S : XSetting G a aT ν) (hx : 0 ≤ x) (hconn : HatConn G)
    (hα : AdmPot G α) (hU : IsUnit (1 - Kcalx G a aT x ν α s))
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y') :
    BD (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') (Gsx G a aT x ν α s) := by
  classical
  intro y y' h
  have hcore : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Core G s := by
    by_contra hc; exact h (Gsx_apply_eq_zero_of_not_core y y' hc)
  have hyr := mem_Yreg_of_mem_core y hcore
  constructor
  · intro hy; by_contra hy'
    exact h (Gsx_apply_eq_zero_of_comp S hx hconn hα hU hY hy hy')
  · intro hy'; by_contra hy
    have hY2 := isNnComp_sdiff hY
    exact h (Gsx_apply_eq_zero_of_comp S hx hconn hα hU hY2
      (Finset.mem_sdiff.2 ⟨hyr, hy⟩) (fun hh => (Finset.mem_sdiff.1 hh).2 hy'))

/-- **T4 (a).** The lift of `Gsx` to `N`-vector fields has no cross elements. -/
theorem liftOp_Gsx_BD (S : XSetting G a aT ν) (hx : 0 ≤ x) (hconn : HatConn G)
    (hα : AdmPot G α) (hU : IsUnit (1 - Kcalx G a aT x ν α s))
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y') :
    BD (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (liftOp N (Gsx G a aT x ν α s)) :=
  BD.liftOp (Gsx_BD S hx hconn hα hU hY)

end Gsx

end Balaban.Localization
