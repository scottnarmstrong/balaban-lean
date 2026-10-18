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

/-! ### The dichotomy of the active thickened cubes

`HatConn G` (every thickened cube `□̂_q ∩ Ω₁` is nearest-neighbour connected) is used below only
through the following consequence, for a set `Y'` of sites and the active centres `q` (those with
`sProd s q ≠ 0`): `□̂_q ∩ Ω₁` lies in `Y'` or misses it.  The cores of the statements below take
this dichotomy as hypothesis.  It follows from the connectivity of the thickened cubes of the active
centres alone (`hatDich_of_isNnComp`), and it holds with no hypothesis for `Y' = Yreg s`
(`hatDich_Yreg`). -/

section HatDich

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {s : ℕ × CTorus d L N₁ m₁ K → ℂ}

/-- The sites in `Ω₁` of the thickened cube of an active centre lie in `Yreg`. -/
theorem hatI_subset_Yreg_of_active {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    (hs : sProd G s q ≠ 0) : hatI G q ⊆ Yreg G s := by
  classical
  intro y hy
  unfold hatI at hy
  rw [Finset.mem_filter] at hy
  unfold Yreg
  rw [Finset.mem_filter, Finset.mem_biUnion]
  exact ⟨⟨q, Finset.mem_filter.2 ⟨hq, hs⟩, hy.1⟩, hy.2⟩

/-- **The dichotomy from connectivity of the active thickened cubes.**  If the thickened cube of
every centre with non-zero cut factor is nearest-neighbour connected inside `Ω₁`, then it lies in a
union `Y'` of components of `Yreg s` or misses it. -/
theorem hatDich_of_isNnComp {Y' : Finset (CTorus d L N₁ m₁ K)}
    (hconn : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → ConnIn (hatI G q))
    (hY : IsNnComp (Yreg G s) Y') :
    ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → hatI G q ⊆ Y' ∨ Disjoint (hatI G q) Y' :=
  fun q hq hs => connIn_dichotomy (hconn q hq hs) (hatI_subset_Yreg_of_active hq hs) hY

/-- The dichotomy under `HatConn`. -/
theorem hatDich_of_hatConn {Y' : Finset (CTorus d L N₁ m₁ K)} (hconn : HatConn G)
    (hY : IsNnComp (Yreg G s) Y') :
    ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → hatI G q ⊆ Y' ∨ Disjoint (hatI G q) Y' :=
  hatDich_of_isNnComp (fun q hq _ => hconn q hq) hY

/-- The dichotomy holds for `Y' = Yreg s` with no hypothesis. -/
theorem hatDich_Yreg :
    ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → hatI G q ⊆ Yreg G s ∨ Disjoint (hatI G q) (Yreg G s) :=
  fun _ hq hs => Or.inl (hatI_subset_Yreg_of_active hq hs)

/-- The dichotomy passes to the complement of `Y'` in `Yreg s`. -/
theorem hatDich_sdiff {Y' : Finset (CTorus d L N₁ m₁ K)}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → hatI G q ⊆ Y' ∨ Disjoint (hatI G q) Y') :
    ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 →
      hatI G q ⊆ Yreg G s \ Y' ∨ Disjoint (hatI G q) (Yreg G s \ Y') := by
  intro q hq hs
  rcases hdich q hq hs with h | h
  · right
    exact Finset.disjoint_left.2 fun x hx hx' => (Finset.mem_sdiff.1 hx').2 (h hx)
  · left
    intro x hx
    exact Finset.mem_sdiff.2 ⟨hatI_subset_Yreg_of_active hq hs hx, Finset.disjoint_left.1 h hx⟩

/-- **The interaction cube of an active centre lies inside or outside `Y'`**, from the dichotomy
of its thickened cube (`□_q ⊆ □̂_q`). -/
theorem subI_or_disjI_of_hatDich {Y' : Finset (CTorus d L N₁ m₁ K)}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → hatI G q ⊆ Y' ∨ Disjoint (hatI G q) Y')
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) (hs : sProd G s q ≠ 0) :
    SubI G (intBox q) Y' ∨ DisjI G (intBox q) Y' := by
  classical
  have hmem : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ intBox q →
      (y : CTorus d L N₁ m₁ K) ∈ hatI G q := fun y hy => by
    unfold hatI
    rw [Finset.mem_filter]
    exact ⟨box_subset_hatBox q hy, y.2⟩
  rcases hdich q hq hs with h | h
  · exact Or.inl fun y hy => h (hmem y hy)
  · exact Or.inr fun y hy hyY => Finset.disjoint_left.1 h (hmem y hy) hyY

end HatDich

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

/-- **T3, core.** No matrix element of `Gsx` from a site of `Y'` to a site outside it, if the
thickened cube of every active centre lies in `Y'` or misses it. -/
theorem Gsx_apply_eq_zero_of_hatDich (S : XSetting G a aT ν) (hx : 0 ≤ x)
    (hα : AdmPot G α) (hU : IsUnit (1 - Kcalx G a aT x ν α s))
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → hatI G q ⊆ Y' ∨ Disjoint (hatI G q) Y')
    {y y' : G.Ω 1} (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
    (hy' : (y' : CTorus d L N₁ m₁ (k + 1)) ∉ Y') : Gsx G a aT x ν α s y y' = 0 := by
  have h := Gsx_local S hx hα hα hU hU (Y := Y')
    (fun q hq hne => by
      rcases hne with h | h <;> exact subI_or_disjI_of_hatDich hdich hq h)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (f := Pi.single y' (1 : ℂ)) (f' := 0) (fun z hz => by
      have : z ≠ y' := fun h => hy' (h ▸ hz)
      simp [this]) y hy
  rw [mulVec_single_apply] at h
  simpa using h

/-- **T3.** No matrix element of `Gsx` from a site of a union `Y'` of nearest-neighbour components
of `Yreg s` to a site outside it. -/
theorem Gsx_apply_eq_zero_of_comp (S : XSetting G a aT ν) (hx : 0 ≤ x) (hconn : HatConn G)
    (hα : AdmPot G α) (hU : IsUnit (1 - Kcalx G a aT x ν α s))
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
    {y y' : G.Ω 1} (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
    (hy' : (y' : CTorus d L N₁ m₁ (k + 1)) ∉ Y') : Gsx G a aT x ν α s y y' = 0 :=
  Gsx_apply_eq_zero_of_hatDich S hx hα hU (hatDich_of_hatConn hconn hY) hy hy'

omit [NeZero N₁] [NeZero L] in
/-- The complement of a union of components inside `Yreg s` is again a union of components. -/
theorem isNnComp_sdiff {Z Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (h : IsNnComp Z Y') :
    IsNnComp Z (Z \ Y') := by
  classical
  refine ⟨Finset.sdiff_subset, fun u hu v hv hadj => ?_⟩
  rw [Finset.mem_sdiff] at hu ⊢
  refine ⟨hv, fun hvY => hu.2 ?_⟩
  exact h.2 v hvY u hu.1 hadj.symm

/-- **T3, block form, core.** `Gsx` has no matrix elements between `Y'` and its complement (in
both directions), if the thickened cube of every active centre lies in `Y'` or misses it. -/
theorem Gsx_BD_of_hatDich (S : XSetting G a aT ν) (hx : 0 ≤ x)
    (hα : AdmPot G α) (hU : IsUnit (1 - Kcalx G a aT x ν α s))
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → hatI G q ⊆ Y' ∨ Disjoint (hatI G q) Y') :
    BD (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') (Gsx G a aT x ν α s) := by
  classical
  intro y y' h
  have hcore : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Core G s := by
    by_contra hc; exact h (Gsx_apply_eq_zero_of_not_core y y' hc)
  have hyr := mem_Yreg_of_mem_core y hcore
  constructor
  · intro hy; by_contra hy'
    exact h (Gsx_apply_eq_zero_of_hatDich S hx hα hU hdich hy hy')
  · intro hy'; by_contra hy
    exact h (Gsx_apply_eq_zero_of_hatDich S hx hα hU (hatDich_sdiff hdich)
      (Finset.mem_sdiff.2 ⟨hyr, hy⟩) (fun hh => (Finset.mem_sdiff.1 hh).2 hy'))

/-- **T3, block form.** `Gsx` has no matrix elements between a union `Y'` of components of
`Yreg s` and its complement (in both directions). -/
theorem Gsx_BD (S : XSetting G a aT ν) (hx : 0 ≤ x) (hconn : HatConn G)
    (hα : AdmPot G α) (hU : IsUnit (1 - Kcalx G a aT x ν α s))
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y') :
    BD (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') (Gsx G a aT x ν α s) :=
  Gsx_BD_of_hatDich S hx hα hU (hatDich_of_hatConn hconn hY)

/-- **T4 (a), core.** The lift of `Gsx` to `N`-vector fields has no cross elements, under the
dichotomy of the active thickened cubes. -/
theorem liftOp_Gsx_BD_of_hatDich (S : XSetting G a aT ν) (hx : 0 ≤ x)
    (hα : AdmPot G α) (hU : IsUnit (1 - Kcalx G a aT x ν α s))
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → hatI G q ⊆ Y' ∨ Disjoint (hatI G q) Y') :
    BD (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (liftOp N (Gsx G a aT x ν α s)) :=
  BD.liftOp (Gsx_BD_of_hatDich S hx hα hU hdich)

/-- **T4 (a).** The lift of `Gsx` to `N`-vector fields has no cross elements. -/
theorem liftOp_Gsx_BD (S : XSetting G a aT ν) (hx : 0 ≤ x) (hconn : HatConn G)
    (hα : AdmPot G α) (hU : IsUnit (1 - Kcalx G a aT x ν α s))
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y') :
    BD (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (liftOp N (Gsx G a aT x ν α s)) :=
  liftOp_Gsx_BD_of_hatDich S hx hα hU (hatDich_of_hatConn hconn hY)

end Gsx


section Cov

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}
  {α : G.Ω 1 → ℂ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {κ δ : ℝ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {κι : Type*} [Fintype κι] [DecidableEq κι]

theorem commK_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (φ : ι → Fin N → ℂ) (y y' : ι) (i : Fin N) :
    commK H φ y (y', i) = H y y' * (φ y i - φ y' i) := by
  unfold commK
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, fieldMul, liftOp, Fintype.sum_prod_type]
  simp [mul_sub, mul_comm]

theorem fieldMul_BD {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → Prop) (φ : ι → Fin N → ℂ) :
    BD (fun p : ι × Fin N => c p.1) c (fieldMul φ) := by
  intro p y h
  by_cases hp : p.1 = y
  · show c p.1 ↔ c y
    rw [hp]
  · simp [fieldMul, hp] at h

/-- The proviso (i), for the operator `H = H_{k,x}`: between a site `y` and a site `y'` of the
core of `s`, a non-zero matrix element of `H` does not cross the boundary of `Y'`. -/
abbrev HRespects (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ) (aT x ν : ℝ)
    (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
    (Y' : Finset (CTorus d L N₁ m₁ (k + 1))) : Prop :=
  ∀ y y' : G.Ω 1, xDirichletOperator G a aT x ν α y y' ≠ 0 →
    (y' : CTorus d L N₁ m₁ (k + 1)) ∈ Core G s →
    ((y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' ↔ (y' : CTorus d L N₁ m₁ (k + 1)) ∈ Y')

section BlocksCore

variable (S : XSetting G a aT ν) (hx : 0 ≤ x) (hα : AdmPot G α)
  (hU : IsUnit (1 - Kcalx G a aT x ν α s)) {Y' : Finset (CTorus d L N₁ m₁ (k + 1))}
  (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → hatI G q ⊆ Y' ∨ Disjoint (hatI G q) Y')
  (hH : HRespects G a aT x ν α s Y')
include S hx hα hU hdich hH

local notation "cY" => (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')

/-- The commutator term `K_x(φ₀) G` has no cross elements, under the dichotomy of the active
thickened cubes and the proviso `HRespects`. -/
theorem commK_Gsx_BD_of_hatDich :
    BD (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *
        liftOp N (Gsx G a aT x ν α s)) := by
  intro y q h
  rw [Matrix.mul_apply] at h
  obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := left_ne_zero_of_mul hp
  have h2 := right_ne_zero_of_mul hp
  have hG : Gsx G a aT x ν α s p.1 q.1 ≠ 0 := by
    intro h0; apply h2; simp [liftOp, h0]
  have hHp : xDirichletOperator G a aT x ν α y p.1 ≠ 0 := by
    intro h0; apply h1
    rw [show p = (p.1, p.2) from rfl, commK_apply, h0, zero_mul]
  have hcore : (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Core G s := by
    by_contra hc; exact hG (Gsx_apply_eq_zero_of_not_core p.1 q.1 hc)
  exact (hH y p.1 hHp hcore).trans (Gsx_BD_of_hatDich S hx hα hU hdich p.1 q.1 hG)

/-- `decM` has no cross elements (core). -/
theorem decM_BD_of_hatDich :
    BD (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (decM G a aT x ν α s φ) := by
  unfold decM constraintM
  exact ((fieldMul_BD cY _).transpose.mul (fieldMul_BD cY _)).sub
    ((commK_Gsx_BD_of_hatDich S hx hα hU hdich hH).mul (fieldMul_BD cY _))

/-- `decN` has no cross elements (core). -/
theorem decN_BD_of_hatDich :
    BD (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (decN G a aT x ν α s φ) := by
  unfold decN constraintN
  exact (fieldMul_BD cY _).transpose.sub (commK_Gsx_BD_of_hatDich S hx hα hU hdich hH)

/-- **T4 (b), core.** `decPi` has no matrix elements between `Y'` and its complement, if `decM`
is invertible. -/
theorem decPi_BD_of_hatDich (hM : IsUnit (decM G a aT x ν α s φ)) :
    BD (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (decPi G a aT x ν α s φ) := by
  unfold decPi
  exact (((liftOp_Gsx_BD_of_hatDich S hx hα hU hdich).mul (fieldMul_BD cY _)).mul
    ((decM_BD_of_hatDich S hx hα hU hdich hH).inv hM)).mul (decN_BD_of_hatDich S hx hα hU hdich hH)

/-- **T4, core.** `decCov - covA` has no cross elements, under the dichotomy of the active
thickened cubes and the provisos. -/
theorem decCov_sub_BD_of_hatDich (hM : IsUnit (decM G a aT x ν α s φ))
    (cκ : κι → Prop) (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decCov G a aT x ν α s φ Q P -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) := by
  have hPl : BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1) (liftOp N P) :=
    BD.liftOp hP
  have hA : BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) := by
    unfold covA
    exact ((BD.one _).sub hPl).smul _ |>.add (hPl.smul _)
  have hQl : BD (fun p : κι × Fin N => cκ p.1)
      (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y') (liftRect N Q) :=
    BD.liftOp hQ
  have hT := (liftOp_Gsx_BD_of_hatDich S hx hα hU hdich).sub
    (decPi_BD_of_hatDich S hx hα hU hdich hH hM)
  unfold decCov
  rw [add_sub_cancel_left]
  exact (((hA.mul hQl).mul hT).mul hQl.transpose |>.mul hA).smul _

end BlocksCore

section Blocks

variable (S : XSetting G a aT ν) (hx : 0 ≤ x) (hconn : HatConn G) (hα : AdmPot G α)
  (hU : IsUnit (1 - Kcalx G a aT x ν α s))
  {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
  (hH : HRespects G a aT x ν α s Y')
include S hx hconn hα hU hY hH

local notation "cY" => (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')

theorem commK_Gsx_BD :
    BD (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *
        liftOp N (Gsx G a aT x ν α s)) :=
  commK_Gsx_BD_of_hatDich S hx hα hU (hatDich_of_hatConn hconn hY) hH

theorem decM_BD :
    BD (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (decM G a aT x ν α s φ) :=
  decM_BD_of_hatDich S hx hα hU (hatDich_of_hatConn hconn hY) hH

theorem decN_BD :
    BD (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (decN G a aT x ν α s φ) :=
  decN_BD_of_hatDich S hx hα hU (hatDich_of_hatConn hconn hY) hH

/-- **T4 (b).** `decPi` has no matrix elements between `Y'` and its complement, if `decM` is
invertible (it is, under the standing hypotheses, by `decM_isUnit`). -/
theorem decPi_BD (hM : IsUnit (decM G a aT x ν α s φ)) :
    BD (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (decPi G a aT x ν α s φ) :=
  decPi_BD_of_hatDich S hx hα hU (hatDich_of_hatConn hconn hY) hH hM

/-- **T4.** The correction `liftOp Gsx - decPi` has no cross elements, so `decCov - covA` has none
either, given the provisos (ii) on `Q` and `P` (labels `cκ` of the coarse index set). -/
theorem decCov_sub_BD (hM : IsUnit (decM G a aT x ν α s φ))
    (cκ : κι → Prop) (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decCov G a aT x ν α s φ Q P -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) :=
  decCov_sub_BD_of_hatDich S hx hα hU (hatDich_of_hatConn hconn hY) hH hM cκ Q P hQ hP

end Blocks

/-- `decM` is invertible under `CovStanding` (`decM_isUnit`). -/
theorem CovStanding.decM_isUnit' {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}
    (H : CovStanding G a aT ν α κ s δ φ Q P) (hx : 0 ≤ x) :
    IsUnit (decM G a aT x ν α s φ) := by
  exact decM_isUnit (H.fam x hx) H.field H.nonneg H.small

/-- **T4, under the standing hypotheses, core**: the dichotomy of the active thickened cubes in
place of `HatConn` and the components. -/
theorem CovStanding.decCov_sub_BD_of_hatDich {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}
    (H : CovStanding G a aT ν α κ s δ φ Q P) (hx : 0 ≤ x)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → hatI G q ⊆ Y' ∨ Disjoint (hatI G q) Y')
    (hH : HRespects G a aT x ν α s Y') (cκ : κι → Prop)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decCov G a aT x ν α s φ Q P - covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) :=
  Balaban.Localization.decCov_sub_BD_of_hatDich (H.fam x hx).st hx (H.fam x hx).pot
    (H.fam x hx).isUnit_one_sub hdich hH (H.decM_isUnit' hx) cκ Q P hQ hP

/-- **T4, under the standing hypotheses.** Everything but the two provisos (`HRespects` for the
union `Y'` of components, and the splitting `cκ` of `Q`, `P`) follows from `CovStanding` and
`HatConn`. -/
theorem CovStanding.decCov_sub_BD {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}
    (H : CovStanding G a aT ν α κ s δ φ Q P) (hx : 0 ≤ x) (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
    (hH : HRespects G a aT x ν α s Y') (cκ : κι → Prop)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decCov G a aT x ν α s φ Q P - covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) :=
  H.decCov_sub_BD_of_hatDich hx (hatDich_of_hatConn hconn hY) hH cκ hQ hP

end Cov

end Balaban.Localization
