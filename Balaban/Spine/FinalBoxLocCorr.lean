/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfUniv
public import Balaban.LargeField.R.RegionalAligned

/-!
# The boundary correction vanishes on the whole torus (finding (C) of A6-3 settled)

The second version of `ℰ^{(j)}` subtracts the restricted antisymmetric sum of P5 (1.8),
`corrSum`, with the coefficients `v^{(j)}_{1,2}(x - y)` of the coefficient data `vc`.  On the whole
torus both sums run over the `L^j`-aligned sites, a subgroup of the torus, and the pair term is a
sum of *differences* `c (F(x) - F(y))` with a coefficient depending on `x - y` only.  Hence the sum
vanishes for every translation-invariant coefficient, symmetric or not:
`∑_{y, x ∈ A} c(x - y) (F(x) - F(y)) = (∑_{z ∈ A} c(z)) (∑_x F(x) - ∑_y F(y)) = 0`.

* `sum_sum_transInv_sub_eq_zero`: the identity over a finite set closed under subtraction;
* `corrSum_transInv_eq_zero`: `corrSum` with translation-invariant coefficients over such a set;
* `EresJ2_univ_eq_Edens`, `EresK2_univ_eq_sum_Edens`: on the whole torus `ℰ^{(j)} = Edens_j` and
  `ℰ_k = ∑_{j ≤ k} Edens_j`, with no hypothesis on `vc` (the symmetric case
  `EresJ2_univ_of_symm` is not needed).
-/

@[expose] public section

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6

namespace Balaban.RootFSpine

section Group

variable {ι : Type*} [AddCommGroup ι]

/-- In a finite set closed under subtraction, `∑_{y ∈ A} c(x - y) = ∑_{z ∈ A} c(z)` for `x ∈ A`. -/
theorem sum_sub_left_eq {A : Finset ι} (hA : ∀ x ∈ A, ∀ y ∈ A, x - y ∈ A) (c : ι → ℂ) {x : ι}
    (hx : x ∈ A) : ∑ y ∈ A, c (x - y) = ∑ z ∈ A, c z := by
  refine Finset.sum_nbij' (fun y => x - y) (fun z => x - z) (fun y hy => hA x hx y hy)
    (fun z hz => hA x hx z hz) (fun y _ => by abel) (fun z _ => by abel) fun y _ => rfl

/-- In a finite set closed under subtraction, `∑_{x ∈ A} c(x - y) = ∑_{z ∈ A} c(z)` for `y ∈ A`. -/
theorem sum_sub_right_eq {A : Finset ι} (hA : ∀ x ∈ A, ∀ y ∈ A, x - y ∈ A) (c : ι → ℂ) {y : ι}
    (hy : y ∈ A) : ∑ x ∈ A, c (x - y) = ∑ z ∈ A, c z := by
  have h0 : (0 : ι) ∈ A := by simpa using hA y hy y hy
  have hneg : -y ∈ A := by simpa using hA 0 h0 y hy
  refine Finset.sum_nbij' (fun x => x - y) (fun z => z + y) (fun x hx => hA x hx y hy)
    (fun z hz => by simpa using hA z hz (-y) hneg) (fun x _ => by abel) (fun z _ => by abel)
    fun x _ => rfl

/-- **The sum of translation-invariant differences vanishes**:
`∑_{y ∈ A} ∑_{x ∈ A} c(x - y) (F(x) - F(y)) = 0` for a finite set `A` closed under subtraction. -/
theorem sum_sum_transInv_sub_eq_zero [DecidableEq ι] {A : Finset ι} (hA : ∀ x ∈ A, ∀ y ∈ A, x - y ∈ A)
    (c F : ι → ℂ) : ∑ y ∈ A, ∑ x ∈ A, c (x - y) * (F x - F y) = 0 := by
  have h1 : ∑ y ∈ A, ∑ x ∈ A, c (x - y) * F x = (∑ z ∈ A, c z) * ∑ x ∈ A, F x := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.sum_mul, sum_sub_left_eq hA c hx]
  have h2 : ∑ y ∈ A, ∑ x ∈ A, c (x - y) * F y = (∑ z ∈ A, c z) * ∑ y ∈ A, F y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [← Finset.sum_mul, sum_sub_right_eq hA c hy]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [h1, h2, sub_self]

end Group

section Corr

variable {d L N₁ m₁ k N : ℕ}

/-- **The restricted antisymmetric sum vanishes for translation-invariant coefficients** over a set
of sites closed under subtraction (for `A = B`): the pair term is
`c₁ (F₁(x) - F₁(y)) + c₂ (F₂(x) - F₂(y))`. -/
theorem corrSum_transInv_eq_zero (c₁ c₂ : Localization.CTorus d L N₁ m₁ k → ℂ) (νj : ℝ)
    {A : Finset (Localization.CTorus d L N₁ m₁ k)} (hA : ∀ x ∈ A, ∀ y ∈ A, x - y ∈ A)
    (ψ : Fld d L N₁ m₁ k N) (h : Fin N → ℂ) :
    corrSum (fun y x => c₁ (x - y)) (fun y x => c₂ (x - y)) νj A A ψ h = 0 := by
  unfold corrSum corrPair
  have e : ∀ y x : Localization.CTorus d L N₁ m₁ k,
      1 / 2 * c₁ (x - y) * (dot (ψ x) (ψ x) - dot (ψ y) (ψ y)) +
        c₂ (x - y) * ((νj : ℂ) * (dot h (unitDirC (ψ x)) - dot h (unitDirC (ψ y)))) =
      c₁ (x - y) * ((fun z => 1 / 2 * dot (ψ z) (ψ z)) x - (fun z => 1 / 2 * dot (ψ z) (ψ z)) y) +
        c₂ (x - y) * ((fun z => (νj : ℂ) * dot h (unitDirC (ψ z))) x -
          (fun z => (νj : ℂ) * dot h (unitDirC (ψ z))) y) := by
    intro y x; ring
  simp only [e, Finset.sum_add_distrib]
  rw [sum_sum_transInv_sub_eq_zero hA, sum_sum_transInv_sub_eq_zero hA, add_zero]

end Corr

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
  (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))

open Classical in
/-- The `L^j`-aligned sites of the Def-6 torus are closed under subtraction (`j ≤ k`). -/
theorem aligned_filter_sub_mem {j : ℕ} (hjk : j ≤ k) :
    ∀ x ∈ Finset.univ.filter (Localization.Aligned (S.L ^ j) :
        Localization.CTorus S.d S.L C.N₁ m₁ k → Prop),
      ∀ y ∈ Finset.univ.filter (Localization.Aligned (S.L ^ j) :
        Localization.CTorus S.d S.L C.N₁ m₁ k → Prop),
      x - y ∈ Finset.univ.filter (Localization.Aligned (S.L ^ j) :
        Localization.CTorus S.d S.L C.N₁ m₁ k → Prop) := by
  classical
  intro x hx y hy
  have hdvd : S.L ^ j ∣ C.N₁ * S.L ^ m₁ * S.L ^ k :=
    Dvd.dvd.mul_left (pow_dvd_pow _ hjk) _
  have : NeZero (S.L ^ j) := ⟨pow_ne_zero _ (NeZero.ne S.L)⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
  exact Balaban.LargeField.RegionalAligned.aligned_sub hdvd hx hy

open Classical in
/-- **`ℰ^{(j)}` on the whole torus is `Edens_j`** for every coefficient data `vc` and `j ≤ k`
(finding (C) of A6-3: the correction sum of the whole torus vanishes, because its coefficients are
translation invariant and the pair term is a difference). -/
theorem EresJ2_univ_eq_Edens {j : ℕ} (hjk : j ≤ k) :
    EresJ2 C vc Set.univ ψk hv j =
      Def6.Edens C.m₀ (C.sf.Tm C.N₁) j (C.psiJ Set.univ ψk hv j) (Def6.constFld (hC hv)) := by
  rw [EresJ2_univ C vc ψk hv j,
    corrSum_transInv_eq_zero (fun z => vc.v1 j (Def6.unlift j z)) (fun z => vc.v2 j (Def6.unlift j z))
      _ (aligned_filter_sub_mem C hjk) _ _, sub_zero]

/-- **`ℰ_k = ∑_{j ≤ k} Edens_j` on the whole torus**, for every coefficient data `vc`. -/
theorem EresK2_univ_eq_sum_Edens :
    EresK2 C vc Set.univ ψk hv =
      ∑ j ∈ Finset.Icc 1 k,
        Def6.Edens C.m₀ (C.sf.Tm C.N₁) j (C.psiJ Set.univ ψk hv j) (Def6.constFld (hC hv)) := by
  unfold EresK2
  exact Finset.sum_congr rfl fun j hj => EresJ2_univ_eq_Edens C vc ψk hv (Finset.mem_Icc.1 hj).2

end Ctx

end Balaban.RootFSpine
