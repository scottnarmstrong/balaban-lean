/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivCoef
public import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The rooted Lemma AE for a term of a cut field (A6-3, box localization, core)

The last integral is localized term by term: a term `τ` of the exponent is evaluated at the field
`Φ(s, w) = φ₀ + T(s) w`, where `w` is the Gaussian variable, `φ₀` a centre, and `T(s)` a cut family
with parameters `s : ι → ℂ` on cells `i` with patches `P i` (P3 (4.41)-(4.47) for the expansion;
LOCALIZATION.md §4.1).  Nothing here fixes `φ₀` or `T`: the centre may be the constant saddle `h`
or a regional saddle, and `T` any family with the decoupling property below.

* `coef_congr_supported`: the coefficient `coef f C` only depends on `f` on the parameters of the
  open polydisc of radius `R > 1` that vanish off `C`.
* `coef_eq_zero_of_eq_cutTo`: if, on these parameters, `f` only depends on the parameters of a
  proper subset `A ⊂ C`, then `coef f C = 0`.
* `rootComp P S C`: the cells of `C` joined to the root set `S` by a chain of cells of `C` with
  overlapping patches; `IsRootedFamily P S C`: every cell of `C` is so joined.
* `CutDecoupling P R T`: on the polydisc of radius `R`, at parameters vanishing off `C`, the
  entries of `T(s)` vanish unless both sites lie in the region `patchReg P C` of `C`, and `T(s)`
  is the sum of its restrictions to two parts of `C` with disjoint regions.
* `rootedExpansion_linField`: for a term `τ` that reads the field only on `S`, analytic on a set
  containing the fields `Φ(s, w)`, with increments `‖τ u - τ φ₀‖ ≤ b` there,
  `τ(Φ(1, w)) = τ(φ₀) + ∑_{C ≠ ∅ rooted} coef_C(w)`, the coefficient of a non-rooted family
  vanishes, `coef_C(w)` depends on `w` only on `patchReg P C`, and
  `‖coef_C(w)‖ ≤ b e^{-(κ-1)|C|}` for `C ≠ ∅`.
-/

@[expose] public section

namespace Balaban.Green

open Finset Balaban.Localization Balaban.Analysis

section Coef

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The parameters restricted to `A`: `s` on `A` and `0` off `A`. -/
def cutTo (A : Finset ι) (s : ι → ℂ) : ι → ℂ := fun i => if i ∈ A then s i else 0

omit [Fintype ι] in
theorem cutTo_mem_supportedOn (A : Finset ι) (s : ι → ℂ) : cutTo A s ∈ supportedOn A :=
  fun i hi => by simp [cutTo, hi]

omit [Fintype ι] in
theorem cutTo_eq_self {A : Finset ι} {s : ι → ℂ} (hs : s ∈ supportedOn A) : cutTo A s = s := by
  funext i
  by_cases hi : i ∈ A
  · simp [cutTo, hi]
  · simp [cutTo, hi, hs i hi]

omit [Fintype ι] in
theorem cutTo_mem_polydisc {R : ℝ} (hR : 0 < R) (A : Finset ι) {s : ι → ℂ}
    (hs : s ∈ polydisc (0 : ι → ℂ) (fun _ => R)) :
    cutTo A s ∈ polydisc (0 : ι → ℂ) (fun _ => R) := fun i => by
  by_cases hi : i ∈ A
  · simpa [cutTo, hi] using hs i
  · simpa [cutTo, hi] using hR

omit [Fintype ι] in
theorem cutTo_cutTo_of_subset {A C : Finset ι} (hAC : A ⊆ C) (s : ι → ℂ) :
    cutTo A (cutTo C s) = cutTo A s := by
  funext i
  by_cases hi : i ∈ A
  · simp [cutTo, hi, hAC hi]
  · simp [cutTo, hi]

/-- **The coefficient only depends on the function on the parameters of the polydisc that vanish
off `C`.** -/
theorem coef_congr_supported {R : ℝ} (hR : 1 < R) {f g : (ι → ℂ) → ℂ} {C : Finset ι}
    (h : ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => R), s ∈ supportedOn C → f s = g s) :
    coef f C = coef g C := by
  have hR0 : 0 < R := by linarith
  calc coef f C = coef (fun s => f (cutTo C s)) C :=
        coef_congr fun w hw => by rw [cutTo_eq_self hw]
    _ = coef (fun s => g (cutTo C s)) C :=
        coef_congr_polydisc hR (fun s hs => h _ (cutTo_mem_polydisc hR0 C hs)
          (cutTo_mem_supportedOn C s)) C
    _ = coef g C := coef_congr fun w hw => by rw [cutTo_eq_self hw]

/-- **A coefficient vanishes when the function forgets a parameter of `C`.**  If on the parameters
of the polydisc of radius `R > 1` vanishing off `C` the function only sees the parameters of
`A`, and some `i₀ ∈ C` is not in `A`, then `coef f C = 0`. -/
theorem coef_eq_zero_of_eq_cutTo {R : ℝ} (hR : 1 < R) {f : (ι → ℂ) → ℂ} {A C : Finset ι}
    {i₀ : ι} (hi₀C : i₀ ∈ C) (hi₀A : i₀ ∉ A)
    (h : ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => R), s ∈ supportedOn C → f s = f (cutTo A s)) :
    coef f C = 0 := by
  rw [coef_congr_supported hR h]
  refine coef_eq_zero_of_inv hi₀C fun w _ τ => ?_
  congr 1
  funext i
  by_cases hi : i ∈ A
  · have : i ≠ i₀ := fun h => hi₀A (h ▸ hi)
    simp [cutTo, hi, Pi.single_eq_of_ne this]
  · simp [cutTo, hi]

omit [Fintype ι] in
/-- The coefficient of a constant at a nonempty family vanishes. -/
theorem coef_const_eq_zero [Fintype ι] (c : ℂ) {C : Finset ι} (hC : C.Nonempty) :
    coef (fun _ : ι → ℂ => c) C = 0 := by
  obtain ⟨i₀, hi₀⟩ := hC
  exact coef_eq_zero_of_inv hi₀ fun _ _ _ => rfl

omit [Fintype ι] in
/-- The coefficient of the empty family is the value at `0`. -/
theorem coef_empty [Fintype ι] (f : (ι → ℂ) → ℂ) : coef f ∅ = f 0 := by
  unfold coef
  have : (Finset.univ.toList.filter (· ∈ (∅ : Finset ι))) = [] := by simp
  rw [this]
  rfl

omit [Fintype ι] in
theorem pder_sub_const (i : ι) (f : (ι → ℂ) → ℂ) (c : ℂ) :
    pder i (fun s => f s - c) = pder i f := by
  funext s
  unfold pder
  exact deriv_sub_const (f := fun t : ℂ => f (s + t • (Pi.single i 1 : ι → ℂ))) c

/-- Subtracting a constant does not change the coefficient of a nonempty family. -/
theorem coef_sub_const {C : Finset ι} (hC : C.Nonempty) (f : (ι → ℂ) → ℂ) (c : ℂ) :
    coef (fun s => f s - c) C = coef f C := by
  unfold coef
  obtain ⟨i₀, hi₀⟩ := hC
  have hl : (Finset.univ.toList.filter (· ∈ C)) ≠ [] := by
    intro h
    have := mem_filter_toList.mpr hi₀
    rw [h] at this
    simp at this
  obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil hl
  rw [hal, pderList_cons, pderList_cons, pder_sub_const]

end Coef

section Root

variable {ι Ω : Type*} [DecidableEq ι]

/-- The region `⋃_{i ∈ A} P i` of a family of cells. -/
def patchReg (P : ι → Set Ω) (A : Finset ι) : Set Ω := {x | ∃ i ∈ A, x ∈ P i}

/-- Two cells of `C` whose patches meet. -/
def CellAdj (P : ι → Set Ω) (C : Finset ι) (i j : ι) : Prop :=
  i ∈ C ∧ j ∈ C ∧ (P i ∩ P j).Nonempty

/-- The cell `i` is joined to the root set `S` by a chain of cells of `C` with overlapping
patches, starting at a cell whose patch meets `S`. -/
def RootReach (P : ι → Set Ω) (S : Set Ω) (C : Finset ι) (i : ι) : Prop :=
  ∃ j ∈ C, (P j ∩ S).Nonempty ∧ Relation.ReflTransGen (CellAdj P C) j i

open Classical in
/-- **The rooted component** of `C`: its cells joined to `S` (`RootReach`). -/
noncomputable def rootComp (P : ι → Set Ω) (S : Set Ω) (C : Finset ι) : Finset ι :=
  C.filter (RootReach P S C)

/-- **A rooted family**: every cell is joined to the root set `S`. -/
def IsRootedFamily (P : ι → Set Ω) (S : Set Ω) (C : Finset ι) : Prop :=
  ∀ i ∈ C, RootReach P S C i

omit [DecidableEq ι] in
theorem rootComp_subset (P : ι → Set Ω) (S : Set Ω) (C : Finset ι) : rootComp P S C ⊆ C := by
  classical
  exact Finset.filter_subset _ _

omit [DecidableEq ι] in
theorem mem_rootComp {P : ι → Set Ω} {S : Set Ω} {C : Finset ι} {i : ι} :
    i ∈ rootComp P S C ↔ i ∈ C ∧ RootReach P S C i := by
  classical
  unfold rootComp
  exact Finset.mem_filter

omit [DecidableEq ι] in
theorem rootComp_eq_self_iff {P : ι → Set Ω} {S : Set Ω} {C : Finset ι} :
    rootComp P S C = C ↔ IsRootedFamily P S C := by
  constructor
  · intro h i hi
    rw [← h] at hi
    exact (mem_rootComp.1 hi).2
  · intro h
    exact Finset.Subset.antisymm (rootComp_subset P S C) fun i hi => mem_rootComp.2 ⟨hi, h i hi⟩

omit [DecidableEq ι] in
theorem isRootedFamily_empty (P : ι → Set Ω) (S : Set Ω) : IsRootedFamily P S ∅ := by
  intro i hi; simp at hi

omit [DecidableEq ι] in
/-- A cell whose patch meets a cell of the rooted component is in the rooted component. -/
theorem mem_rootComp_of_adj {P : ι → Set Ω} {S : Set Ω} {C : Finset ι} {i j : ι}
    (hi : i ∈ rootComp P S C) (hj : j ∈ C) (hij : (P i ∩ P j).Nonempty) :
    j ∈ rootComp P S C := by
  obtain ⟨hiC, k, hk, hkS, hki⟩ := mem_rootComp.1 hi
  exact mem_rootComp.2 ⟨hj, k, hk, hkS, hki.tail ⟨hiC, hj, hij⟩⟩

omit [DecidableEq ι] in
/-- A cell of `C` whose patch meets the root set is in the rooted component. -/
theorem mem_rootComp_of_meets {P : ι → Set Ω} {S : Set Ω} {C : Finset ι} {i : ι} (hi : i ∈ C)
    (hS : (P i ∩ S).Nonempty) : i ∈ rootComp P S C :=
  mem_rootComp.2 ⟨hi, i, hi, hS, Relation.ReflTransGen.refl⟩

/-- **The rooted component is separated from the rest of `C`.** -/
theorem disjoint_patchReg_rootComp (P : ι → Set Ω) (S : Set Ω) (C : Finset ι) :
    Disjoint (patchReg P (rootComp P S C)) (patchReg P (C \ rootComp P S C)) := by
  rw [Set.disjoint_left]
  rintro x ⟨i, hi, hxi⟩ ⟨j, hj, hxj⟩
  obtain ⟨hjC, hjA⟩ := Finset.mem_sdiff.1 hj
  exact hjA (mem_rootComp_of_adj hi hjC ⟨x, hxi, hxj⟩)

/-- **The rest of `C` misses the root set.** -/
theorem disjoint_root_patchReg_sdiff (P : ι → Set Ω) (S : Set Ω) (C : Finset ι) :
    Disjoint S (patchReg P (C \ rootComp P S C)) := by
  rw [Set.disjoint_left]
  rintro x hxS ⟨j, hj, hxj⟩
  obtain ⟨hjC, hjA⟩ := Finset.mem_sdiff.1 hj
  exact hjA (mem_rootComp_of_meets hjC ⟨x, hxj, hxS⟩)

omit [DecidableEq ι] in
theorem patchReg_mono {P : ι → Set Ω} {A B : Finset ι} (h : A ⊆ B) :
    patchReg P A ⊆ patchReg P B := fun _ ⟨i, hi, hx⟩ => ⟨i, h hi, hx⟩

omit [DecidableEq ι] in
theorem patchReg_empty (P : ι → Set Ω) : patchReg P (∅ : Finset ι) = ∅ := by
  ext x; simp [patchReg]

/-- **The vanishing of a non-rooted coefficient (abstract form).**  If on the parameters of the
polydisc of radius `R > 1` vanishing off `C` the function only sees the parameters of the rooted
component, the coefficient of a non-rooted family vanishes. -/
theorem coef_eq_zero_of_not_rooted [Fintype ι] {R : ℝ} (hR : 1 < R) {P : ι → Set Ω}
    {S : Set Ω} {C : Finset ι} {f : (ι → ℂ) → ℂ}
    (hf : ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => R), s ∈ supportedOn C →
      f s = f (cutTo (rootComp P S C) s))
    (hC : ¬ IsRootedFamily P S C) : coef f C = 0 := by
  have hne : ∃ i₀ ∈ C, i₀ ∉ rootComp P S C := by
    by_contra hcon
    push Not at hcon
    exact hC (rootComp_eq_self_iff.1 (Finset.Subset.antisymm (rootComp_subset P S C) hcon))
  obtain ⟨i₀, hi₀C, hi₀A⟩ := hne
  exact coef_eq_zero_of_eq_cutTo hR hi₀C hi₀A hf

end Root

section Field

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

/-- The cut field `Φ(s, w) = φ₀ + T(s) w`. -/
def linField (φ₀ : Ω → ℂ) (T : (ι → ℂ) → Ω → Ω → ℂ) (s : ι → ℂ) (w : Ω → ℂ) : Ω → ℂ :=
  fun x => φ₀ x + ∑ y, T s x y * w y

/-- **The decoupling property of a cut family** on the open polydisc of radius `R`:
* (supp) at parameters vanishing off `C`, an entry `T(s) x y` vanishes unless `x` and `y` lie in
  the region of `C`;
* (split) at such parameters, for `A ⊆ C` whose region misses the region of `C \ A`,
  `T(s) = T(s|_A) + T(s|_{C \ A})`. -/
structure CutDecoupling (P : ι → Set Ω) (R : ℝ) (T : (ι → ℂ) → Ω → Ω → ℂ) : Prop where
  supp : ∀ (C : Finset ι) (s : ι → ℂ), s ∈ polydisc (0 : ι → ℂ) (fun _ => R) →
    s ∈ supportedOn C → ∀ x y, T s x y ≠ 0 → x ∈ patchReg P C ∧ y ∈ patchReg P C
  split : ∀ (C A : Finset ι) (s : ι → ℂ), s ∈ polydisc (0 : ι → ℂ) (fun _ => R) →
    s ∈ supportedOn C → A ⊆ C → Disjoint (patchReg P A) (patchReg P (C \ A)) →
    ∀ x y, T s x y = T (cutTo A s) x y + T (cutTo (C \ A) s) x y

omit [Fintype ι] [Fintype Ω] in
/-- `CutDecoupling` is inhabited (the zero family). -/
theorem cutDecoupling_zero (P : ι → Set Ω) (R : ℝ) :
    CutDecoupling P R (fun _ _ _ => (0 : ℂ)) :=
  ⟨fun _ _ _ _ _ _ h => absurd rfl h, fun _ _ _ _ _ _ _ _ _ => by simp⟩

omit [Fintype ι] [Fintype Ω] in
theorem nonempty_cutDecoupling (P : ι → Set Ω) (R : ℝ) :
    Nonempty (CutDecoupling P R (fun _ _ _ => (0 : ℂ))) :=
  ⟨cutDecoupling_zero P R⟩

/-- A function of the field that only reads it on `S`. -/
def ReadsOn (S : Set Ω) (τ : (Ω → ℂ) → ℂ) : Prop :=
  ∀ u u' : Ω → ℂ, (∀ x ∈ S, u x = u' x) → τ u = τ u'

omit [Fintype Ω] in
theorem readsOn_const (S : Set Ω) (c : ℂ) : ReadsOn S (fun _ : Ω → ℂ => c) :=
  fun _ _ _ => rfl

omit [Fintype Ω] in
theorem ReadsOn.mono {S S' : Set Ω} {τ : (Ω → ℂ) → ℂ} (h : ReadsOn S τ) (hSS : S ⊆ S') :
    ReadsOn S' τ := fun u u' huu => h u u' fun x hx => huu x (hSS hx)

variable {P : ι → Set Ω} {R : ℝ} {T : (ι → ℂ) → Ω → Ω → ℂ}

omit [Fintype ι] [Fintype Ω] in
/-- At `s = 0` the cut family vanishes (the case `C = ∅` of `supp`). -/
theorem CutDecoupling.zero_apply (hT : CutDecoupling P R T) (hR : 0 < R) (x y : Ω) :
    T 0 x y = 0 := by
  by_contra h
  have h0 : (0 : ι → ℂ) ∈ polydisc (0 : ι → ℂ) (fun _ => R) := fun i => by simpa using hR
  obtain ⟨hx, -⟩ := hT.supp ∅ 0 h0 (fun _ _ => rfl) x y h
  rw [patchReg_empty] at hx
  exact hx

omit [Fintype ι] in
theorem linField_zero (hT : CutDecoupling P R T) (hR : 0 < R) (φ₀ w : Ω → ℂ) :
    linField φ₀ T 0 w = φ₀ := by
  funext x
  simp [linField, hT.zero_apply hR]

omit [Fintype ι] in
/-- **Locality in the variable.**  At parameters of the polydisc vanishing off `C`, the cut field
only depends on `w` on the region of `C`. -/
theorem linField_congr (hT : CutDecoupling P R T) {C : Finset ι} {s : ι → ℂ}
    (hs : s ∈ polydisc (0 : ι → ℂ) (fun _ => R)) (hsC : s ∈ supportedOn C) (φ₀ : Ω → ℂ)
    {w w' : Ω → ℂ} (hww : ∀ y ∈ patchReg P C, w y = w' y) :
    linField φ₀ T s w = linField φ₀ T s w' := by
  funext x
  simp only [linField]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : T s x y = 0
  · simp [h]
  · rw [hww y (hT.supp C s hs hsC x y h).2]

omit [Fintype ι] in
/-- **The rooted property of the cut field.**  At parameters of the polydisc vanishing off `C`,
the cut field on the root set `S` only sees the parameters of the rooted component. -/
theorem linField_eqOn_root (hT : CutDecoupling P R T) (hR : 0 < R) (S : Set Ω) {C : Finset ι}
    {s : ι → ℂ} (hs : s ∈ polydisc (0 : ι → ℂ) (fun _ => R)) (hsC : s ∈ supportedOn C)
    (φ₀ w : Ω → ℂ) :
    ∀ x ∈ S, linField φ₀ T s w x = linField φ₀ T (cutTo (rootComp P S C) s) w x := by
  intro x hx
  set A := rootComp P S C with hA
  have hAC : A ⊆ C := rootComp_subset P S C
  have hsplit := hT.split C A s hs hsC hAC (disjoint_patchReg_rootComp P S C)
  have hB0 : ∀ y, T (cutTo (C \ A) s) x y = 0 := by
    intro y
    by_contra h
    have hsB : cutTo (C \ A) s ∈ supportedOn (C \ A) := cutTo_mem_supportedOn _ _
    have hpB := cutTo_mem_polydisc hR (C \ A) hs
    exact Set.disjoint_left.1 (disjoint_root_patchReg_sdiff P S C) hx
      (hT.supp (C \ A) _ hpB hsB x y h).1
  simp only [linField]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hsplit x y, hB0 y, add_zero]

omit [DecidableEq ι] in
/-- Analyticity of the cut field in the parameters. -/
theorem analyticOnNhd_linField {U : Set (ι → ℂ)}
    (hTan : ∀ x y, AnalyticOnNhd ℂ (fun s => T s x y) U) (φ₀ w : Ω → ℂ) :
    AnalyticOnNhd ℂ (fun s => linField φ₀ T s w) U := by
  intro s hs
  refine analyticAt_pi_iff.2 fun x => ?_
  exact analyticAt_const.add (Finset.analyticAt_fun_sum _ fun y _ =>
    (hTan x y s hs).mul analyticAt_const)

/-- The coefficient of the term `τ` of the cut field at the family `C`. -/
noncomputable def rootedCoef (τ : (Ω → ℂ) → ℂ) (φ₀ : Ω → ℂ) (T : (ι → ℂ) → Ω → Ω → ℂ)
    (w : Ω → ℂ) (C : Finset ι) : ℂ :=
  coef (fun s => τ (linField φ₀ T s w)) C

/-- **The coefficients of a term are exactly local in the variable**: `coef_C(w)` only depends on
`w` on the region of `C` (no condition on `w` or `w'`). -/
theorem rootedCoef_congr (hT : CutDecoupling P R T) (hR : 1 < R) (τ : (Ω → ℂ) → ℂ)
    (φ₀ : Ω → ℂ) (C : Finset ι) {w w' : Ω → ℂ} (hww : ∀ y ∈ patchReg P C, w y = w' y) :
    rootedCoef τ φ₀ T w C = rootedCoef τ φ₀ T w' C :=
  coef_congr_supported hR fun s hs hsC => by rw [linField_congr hT hs hsC φ₀ hww]

/-- **The coefficient of a non-rooted family vanishes**, for a term reading the field on `S`. -/
theorem rootedCoef_eq_zero_of_not_rooted (hT : CutDecoupling P R T) (hR : 1 < R)
    {S : Set Ω} {τ : (Ω → ℂ) → ℂ} (hτ : ReadsOn S τ) (φ₀ w : Ω → ℂ) {C : Finset ι}
    (hC : ¬ IsRootedFamily P S C) : rootedCoef τ φ₀ T w C = 0 :=
  coef_eq_zero_of_not_rooted hR (fun s hs hsC =>
    hτ _ _ (linField_eqOn_root hT (by linarith) S hs hsC φ₀ w)) hC

theorem rootedCoef_empty (hT : CutDecoupling P R T) (hR : 0 < R) (τ : (Ω → ℂ) → ℂ)
    (φ₀ w : Ω → ℂ) : rootedCoef τ φ₀ T w ∅ = τ φ₀ := by
  unfold rootedCoef
  rw [coef_empty, linField_zero hT hR]

open Classical in
/-- **The rooted Lemma AE for a term of the cut field.**  Let `T` have the decoupling property
on the polydisc of radius `e^κ`, `κ ≥ 1`, with analytic entries; let `τ` read the field only on
`S`, be analytic on a set `U` containing the fields `Φ(s, w)` of the polydisc, with
`‖τ u - τ φ₀‖ ≤ b` on `U`.  Then
* `τ(Φ(1, w)) = τ(φ₀) + ∑_{C ≠ ∅ rooted} coef_C(w)`;
* `coef_C(w) = 0` unless `C` is rooted at `S`;
* `coef_C(w)` only depends on `w` on the region of `C`;
* `‖coef_C(w)‖ ≤ b e^{-(κ-1)|C|}` for `C ≠ ∅`. -/
theorem rootedExpansion_linField {κ : ℝ} (hκ : 1 ≤ κ)
    (hT : CutDecoupling P (Real.exp κ) T)
    (hTan : ∀ x y, AnalyticOnNhd ℂ (fun s => T s x y)
      (polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)))
    {S : Set Ω} {τ : (Ω → ℂ) → ℂ} (hτ : ReadsOn S τ) {U : Set (Ω → ℂ)}
    (hτan : AnalyticOnNhd ℂ τ U) (φ₀ w : Ω → ℂ)
    (hmem : ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), linField φ₀ T s w ∈ U)
    {b : ℝ} (hb : ∀ u ∈ U, ‖τ u - τ φ₀‖ ≤ b) :
    τ (linField φ₀ T (fun _ => 1) w) = τ φ₀ +
        ∑ C ∈ Finset.univ.filter (fun C : Finset ι => C.Nonempty ∧ IsRootedFamily P S C),
          rootedCoef τ φ₀ T w C ∧
      (∀ C, ¬ IsRootedFamily P S C → rootedCoef τ φ₀ T w C = 0) ∧
      (∀ C (w' : Ω → ℂ), (∀ y ∈ patchReg P C, w y = w' y) →
        rootedCoef τ φ₀ T w C = rootedCoef τ φ₀ T w' C) ∧
      (∀ C, C.Nonempty → ‖rootedCoef τ φ₀ T w C‖ ≤ b * Real.exp (-(κ - 1) * C.card)) := by
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 (by linarith)
  have hR0 : 0 < Real.exp κ := Real.exp_pos κ
  set f : (ι → ℂ) → ℂ := fun s => τ (linField φ₀ T s w) with hf
  have hfan : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) := fun s hs =>
    AnalyticAt.comp (g := τ) (f := fun s => linField φ₀ T s w) (hτan _ (hmem s hs))
      (analyticOnNhd_linField hTan φ₀ w s hs)
  have hzero : ∀ C, ¬ IsRootedFamily P S C → rootedCoef τ φ₀ T w C = 0 := fun C hC =>
    rootedCoef_eq_zero_of_not_rooted hT hR hτ φ₀ w hC
  have hbd : ∀ C, C.Nonempty → ‖rootedCoef τ φ₀ T w C‖ ≤ b * Real.exp (-(κ - 1) * C.card) := by
    intro C hC
    have hg : AnalyticOnNhd ℂ (fun s => f s - τ φ₀)
        (polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) := fun s hs =>
      (hfan s hs).sub analyticAt_const
    have h1 : rootedCoef τ φ₀ T w C = coef (fun s => f s - τ φ₀) C :=
      (coef_sub_const hC f (τ φ₀)).symm
    rw [h1]
    exact norm_coef_le_exp hκ hg (fun s hs => hb _ (hmem s hs)) C
  refine ⟨?_, hzero, fun C w' hww => rootedCoef_congr hT hR τ φ₀ C hww, hbd⟩
  have hsum := sum_coef_eq hR hfan
  change f 1 = _
  rw [hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun C : Finset ι => C.Nonempty)]
  have hnot : (Finset.univ.filter fun C : Finset ι => ¬ C.Nonempty) = {∅} := by
    ext C; simp [Finset.not_nonempty_iff_eq_empty]
  rw [hnot, Finset.sum_singleton, add_comm]
  congr 1
  · exact rootedCoef_empty hT hR0 τ φ₀ w
  · rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun C : Finset ι => C.Nonempty)
      (fun C => IsRootedFamily P S C)]
    rw [Finset.filter_filter]
    have h0 : ∑ C ∈ (Finset.univ.filter fun C : Finset ι => C.Nonempty).filter
        (fun C => ¬ IsRootedFamily P S C), coef f C = 0 :=
      Finset.sum_eq_zero fun C hC => hzero C (Finset.mem_filter.1 hC).2
    rw [h0, add_zero]
    rfl

end Field

end Balaban.Green
