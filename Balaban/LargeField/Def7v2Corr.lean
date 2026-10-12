/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2Source
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-7 v2, part 1: P5 (1.8)'s boundary correction -- DRAFT

**Draft, pending Roland's answer to Q13.**  CLASS-RULINGS-2 item 6 ("P5's boundary correction,
exactly identified").  P5 p. 489 (1.8) subtracts from `ℰ^{(j)}(Z_k^c)`
```
∑_{y ∈ Z_k^c ∩ T^{(j)}} ∑_{x ∈ (Z_k^c)^≈ ∩ T^{(j)}}
  { ½ v₁^{(j)}(y, x) [ψ_j²(x) - ψ_j²(y)] + v₂^{(j)}(y, x) ν_j h · [(ψ_j)₀(x) - (ψ_j)₀(y)] }.
```
* `unitDirC`: **the sitewise unit direction** `(ψ)₀ = ψ / (ψ·ψ)^{1/2}` (P1 p. 123 (3.13) for real
  fields, `unitDirC_real`), with the square-root branch equal to `1` at `e₁` (`unitDirC_single`),
  analytic where `ψ·ψ` is in the slit plane (`unitDirC_analyticAt`, the branch condition), a unit
  vector for the bilinear form (`unitDirC_dot`), `O(N)`-covariant (`unitDirC_rot`).  It is a
  sitewise direction, not a zero Fourier mode, and is not replaced by `ψ`.
* `blockDirV`, `v1Loc`, `v2Loc`: **the local coefficients of P1 p. 146 (3.106)** at the reference
  `(ψ, b) = (e₁, ν_j e₁)`, in the source form `Ẽ(y, X; ψ, b)` of the term (`Def6v2.SourceTerms`):
  `v₁(x, y, X) = D_{ψ(x)} Ẽ(y, X; e₁, ν_j e₁)[e₁]`,
  `v₂(x, y, X) = D_{b·e₂} D_{ψ(x)} Ẽ(y, X; e₁, ν_j e₁)[e₂]`
  (the derivative in the source coordinate `b` itself, P1's `∂_{vw}`, so no division by `v`).
* `v1T`, `v2T`: the sums of the local coefficients over all the polymers `X ∋ y` of `𝒟_j` on the
  **whole** torus `T^{(j)}` (the whole-lattice origin of the coefficients; the thermodynamic limit
  of P1 p. 147 (3.110) is the clause `D1Corr.v1_lim`, `v2_lim` of `Def7v2`).
* `corrPair`, `corrSum`: the pair term and **the restricted antisymmetric sum** over
  `y ∈ A`, `x ∈ B`; `corrSum_self_eq_zero`: for symmetric coefficients it vanishes when both sums
  run over the same set (the full torus double sum); on `A = Z_k^c ∩ T^{(j)}`,
  `B = (Z_k^c)^≈ ∩ T^{(j)}` it does not in general (`corrSum_singleton`).

P1 (3.106) also defines a transverse second-spin derivative `v₀`; P5 (1.8) uses `v₁`, `v₂` only.
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset Matrix

/-! ### The sitewise unit direction -/

section UnitDir

variable {N : ℕ}

/-- **The sitewise unit direction** `(ψ)₀ = ψ / (ψ·ψ)^{1/2}` (CLASS-RULINGS-2 item 6; P1 p. 123
(3.13): `(ψ_j)₀(x) = ψ_j(x)/|ψ_j(x)|` for real fields), the analytic continuation with the principal
square root (`sqrtC`, equal to `1` at `e₁`).  Draft pending Roland's answer to Q13. -/
noncomputable def unitDirC (v : Fin N → ℂ) : Fin N → ℂ := (sqrtC (dot v v))⁻¹ • v

theorem sqrtC_one : sqrtC 1 = 1 := sqrtC_eq (by norm_num) (by norm_num)

/-- The branch: `(e₁)₀ = e₁`. -/
theorem unitDirC_single (i₀ : Fin N) :
    unitDirC (Pi.single i₀ 1 : Fin N → ℂ) = Pi.single i₀ 1 := by
  unfold unitDirC
  rw [dot_single_left, Pi.single_eq_same, mul_one, sqrtC_one, inv_one, one_smul]

/-- For real fields it is `ψ / |ψ|` (P1 (3.13)). -/
theorem unitDirC_real (v : Fin N → ℝ) (hv : 0 < rn v) :
    unitDirC (fun i => (v i : ℂ)) = fun i => ((v i / rn v : ℝ) : ℂ) := by
  have hsq : rn v ^ 2 = ∑ i, v i ^ 2 := by
    unfold rn; exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hd : dot (fun i => (v i : ℂ)) (fun i => (v i : ℂ)) = (rn v : ℂ) * (rn v : ℂ) := by
    have : ((rn v ^ 2 : ℝ) : ℂ) = ((∑ i, v i ^ 2 : ℝ) : ℂ) := by rw [hsq]
    unfold dot
    push_cast at this
    rw [← sq, this]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hs : sqrtC (dot (fun i => (v i : ℂ)) (fun i => (v i : ℂ))) = (rn v : ℂ) :=
    sqrtC_eq hd.symm (by simpa using hv)
  unfold unitDirC
  rw [hs]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [div_eq_inv_mul]

theorem sqrtC_ne_zero {z : ℂ} (hz : z ≠ 0) : sqrtC z ≠ 0 := by
  intro h
  have := sqrtC_mul_self z
  rw [h, mul_zero] at this
  exact hz this.symm

/-- It is a unit vector for the bilinear form: `(ψ)₀ · (ψ)₀ = 1` where `ψ·ψ ≠ 0`. -/
theorem unitDirC_dot {v : Fin N → ℂ} (hv : dot v v ≠ 0) : dot (unitDirC v) (unitDirC v) = 1 := by
  unfold unitDirC
  rw [dot_smul_left, dot_smul_right]
  have h1 := sqrtC_mul_self (dot v v)
  have h2 := sqrtC_ne_zero hv
  field_simp
  rw [← sq] at h1
  exact h1.symm

theorem analyticAt_dot_self (v : Fin N → ℂ) : AnalyticAt ℂ (fun v : Fin N → ℂ => dot v v) v := by
  have h := Finset.analyticAt_sum (𝕜 := ℂ)
    (f := fun (l : Fin N) (v : Fin N → ℂ) => v l * v l) (c := v) Finset.univ
    (fun l _ => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) l).analyticAt v).mul
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) l).analyticAt v))
  have e : (∑ l : Fin N, fun v : Fin N → ℂ => v l * v l) = fun v => dot v v := by
    funext v; simp [Finset.sum_apply, dot]
  rwa [e] at h

/-- **The analytic branch** (item 6: "its branch condition"): `ψ ↦ (ψ)₀` is analytic where `ψ·ψ`
lies in the slit plane `ℂ ∖ (-∞, 0]`, in particular near every real nonzero vector. -/
theorem unitDirC_analyticAt {v : Fin N → ℂ} (hv : dot v v ∈ Complex.slitPlane) :
    AnalyticAt ℂ (unitDirC (N := N)) v := by
  have h1 : AnalyticAt ℂ (fun v : Fin N → ℂ => (dot v v) ^ (1 / 2 : ℂ)) v :=
    (analyticAt_dot_self v).cpow analyticAt_const hv
  have h2 : (dot v v) ^ (1 / 2 : ℂ) ≠ 0 := sqrtC_ne_zero (Complex.slitPlane_ne_zero hv)
  exact (h1.inv h2).smul analyticAt_id

/-- `O(N)`-covariance (complex orthogonal `R`): `(Rψ)₀ = R (ψ)₀`. -/
theorem unitDirC_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsOrth R) (v : Fin N → ℂ) :
    unitDirC (R *ᵥ v) = R *ᵥ unitDirC v := by
  unfold unitDirC
  rw [dot_mulVec_rot hR, Matrix.mulVec_smul]

end UnitDir

/-! ### The coefficients `v₁`, `v₂` of P1 (3.106) -/

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

open Classical in
/-- The direction "`δ_{(block x)} u`": the perturbation of `ψ` by the vector `u` on the `j`-block
based at `x` (the derivative `D_{ψ(x)}[u]` of a function of block-constant fields); for a
coordinate vector it is `Def6.blockDir` (`blockDirV_single`). -/
noncomputable def blockDirV (L j : ℕ) (x : Localization.CTorus d L N₁ m₁ k) (u : Fin N → ℂ) :
    Fld d L N₁ m₁ k N :=
  fun z => if cbase (L ^ j) z = x then u else 0

omit [NeZero L] [NeZero N₁] in
theorem blockDirV_single (j : ℕ) (x : Localization.CTorus d L N₁ m₁ k) (i : Fin N) :
    blockDirV L j x (Pi.single i 1) = blockDir L j x i := by
  funext z i'
  unfold blockDirV blockDir
  by_cases h : cbase (L ^ j) z = x
  · by_cases h' : i' = i
    · subst h'; simp [h]
    · simp [h, h']
  · simp [h]

/-- **`v₁(x, y, X; 1, v, 0) = D_{ψ(x)} Ẽ(y, X; e₁, v e₁)[e₁]`** (P1 p. 146 (3.106); CLASS-RULINGS-2
item 6), for the source form `Et = Ẽ(y, X; ·, ·)` of a term, `v = ν_j`. -/
noncomputable def v1Loc (Et : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ) (j : ℕ) (νj : ℝ)
    (e₁ : Fin N → ℂ) (x : Localization.CTorus d L N₁ m₁ k) : ℂ :=
  fderiv ℂ (fun ψ : Fld d L N₁ m₁ k N => Et ψ (constFld ((νj : ℂ) • e₁))) (constFld e₁)
    (blockDirV L j x e₁)

/-- **`v₂(x, y, X; 1, v, 0) = D_{b·e₂} D_{ψ(x)} Ẽ(y, X; e₁, v e₁)[e₂]`** (P1 p. 146 (3.106);
CLASS-RULINGS-2 item 6): the derivative in the transverse source coordinate `b·e₂` of the transverse
spin derivative, at the reference `(e₁, ν_j e₁)`. -/
noncomputable def v2Loc (Et : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ) (j : ℕ) (νj : ℝ)
    (e₁ e₂ : Fin N → ℂ) (x : Localization.CTorus d L N₁ m₁ k) : ℂ :=
  fderiv ℂ (fun b : Fin N → ℂ =>
      fderiv ℂ (fun ψ : Fld d L N₁ m₁ k N => Et ψ (constFld b)) (constFld e₁)
        (blockDirV L j x e₂))
    ((νj : ℂ) • e₁) e₂

open Classical in
/-- **`v₁^{(j)}(y, x)` on a torus**: the sum of the local coefficients over all the polymers
`X ∈ 𝒟_j`, `X ∋ y`, of the whole torus `T^{(j)}` (item 6: "sum these local coefficients over
`X ∋ y` on the whole `T^{(j)}`"). -/
noncomputable def v1T (m₀ : ℕ) (St : SourceTerms d L N₁ m₁ k N) (j : ℕ) (νj : ℝ) (e₁ : Fin N → ℂ)
    (y x : Localization.CTorus d L N₁ m₁ k) : ℂ :=
  ∑ᶠ X ∈ polysAt m₀ j y, v1Loc (St.E j y X) j νj e₁ x

open Classical in
/-- **`v₂^{(j)}(y, x)` on a torus** (whole-lattice origin, as `v1T`). -/
noncomputable def v2T (m₀ : ℕ) (St : SourceTerms d L N₁ m₁ k N) (j : ℕ) (νj : ℝ)
    (e₁ e₂ : Fin N → ℂ) (y x : Localization.CTorus d L N₁ m₁ k) : ℂ :=
  ∑ᶠ X ∈ polysAt m₀ j y, v2Loc (St.E j y X) j νj e₁ e₂ x

/-! ### The pair term and the restricted antisymmetric sum -/

/-- **The pair term of P5 (1.8)**:
`½ c₁ [ψ²(x) - ψ²(y)] + c₂ ν_j h · [(ψ)₀(x) - (ψ)₀(y)]`, with the sitewise unit direction
`(ψ)₀ = unitDirC` (not `ψ`), `c₁ = v₁^{(j)}(y, x)`, `c₂ = v₂^{(j)}(y, x)`, `h` the constant field. -/
noncomputable def corrPair (c₁ c₂ : ℂ) (νj : ℝ) (ψ : Fld d L N₁ m₁ k N) (h : Fin N → ℂ)
    (y x : Localization.CTorus d L N₁ m₁ k) : ℂ :=
  1 / 2 * c₁ * (dot (ψ x) (ψ x) - dot (ψ y) (ψ y)) +
    c₂ * ((νj : ℂ) * (dot h (unitDirC (ψ x)) - dot h (unitDirC (ψ y))))

/-- **The restricted antisymmetric sum of P5 (1.8)** over `y ∈ A`, `x ∈ B`
(`A = Z_k^c ∩ T^{(j)}`, `B = (Z_k^c)^≈ ∩ T^{(j)}`). -/
noncomputable def corrSum (v₁ v₂ : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℂ) (νj : ℝ)
    (A B : Finset (Localization.CTorus d L N₁ m₁ k)) (ψ : Fld d L N₁ m₁ k N) (h : Fin N → ℂ) : ℂ :=
  ∑ y ∈ A, ∑ x ∈ B, corrPair (v₁ y x) (v₂ y x) νj ψ h y x

omit [NeZero L] [NeZero N₁] in
/-- The pair term is antisymmetric under the exchange of the two sites (for the same
coefficients). -/
theorem corrPair_antisymm (c₁ c₂ : ℂ) (νj : ℝ) (ψ : Fld d L N₁ m₁ k N) (h : Fin N → ℂ)
    (y x : Localization.CTorus d L N₁ m₁ k) : corrPair c₁ c₂ νj ψ h y x = -corrPair c₁ c₂ νj ψ h x y := by
  unfold corrPair; ring

omit [NeZero L] [NeZero N₁] in
/-- **The correction vanishes after the full double sum** (item 6: "it vanishes after the full
torus double sum"): for symmetric coefficients `v(y, x) = v(x, y)`, the sum over `y, x ∈ A` is
zero.  On the restricted domains `A ≠ B` of P5 (1.8) it does not vanish in general: it cancels the
relevant and marginal boundary terms (P5 p. 490). -/
theorem corrSum_self_eq_zero {v₁ v₂ : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℂ}
    (hs₁ : ∀ y x, v₁ y x = v₁ x y) (hs₂ : ∀ y x, v₂ y x = v₂ x y) (νj : ℝ)
    (A : Finset (Localization.CTorus d L N₁ m₁ k)) (ψ : Fld d L N₁ m₁ k N) (h : Fin N → ℂ) :
    corrSum v₁ v₂ νj A A ψ h = 0 := by
  have key : corrSum v₁ v₂ νj A A ψ h = -corrSum v₁ v₂ νj A A ψ h := by
    unfold corrSum
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hs₁ x y, hs₂ x y]
    exact corrPair_antisymm _ _ _ _ _ _ _
  have h2 : (2 : ℂ) * corrSum v₁ v₂ νj A A ψ h = 0 := by linear_combination key
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

omit [NeZero L] [NeZero N₁] in
/-- On a restricted pair of domains the sum is a single pair term, in general nonzero. -/
theorem corrSum_singleton (v₁ v₂ : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℂ) (νj : ℝ)
    (y x : Localization.CTorus d L N₁ m₁ k) (ψ : Fld d L N₁ m₁ k N) (h : Fin N → ℂ) :
    corrSum v₁ v₂ νj {y} {x} ψ h = corrPair (v₁ y x) (v₂ y x) νj ψ h y x := by
  simp [corrSum]

omit [NeZero L] [NeZero N₁] in
/-- **The restricted sum does not vanish in general**: for `v₁ ≡ 1`, `v₂ ≡ 0` and a field with
`ψ²(x) ≠ ψ²(y)`, the sum over `{y} × {x}` is `½ (ψ²(x) - ψ²(y)) ≠ 0`. -/
theorem corrSum_ne_zero_example (νj : ℝ) (y x : Localization.CTorus d L N₁ m₁ k) (ψ : Fld d L N₁ m₁ k N)
    (h : Fin N → ℂ) (hne : dot (ψ x) (ψ x) ≠ dot (ψ y) (ψ y)) :
    corrSum (fun _ _ => 1) (fun _ _ => 0) νj {y} {x} ψ h ≠ 0 := by
  rw [corrSum_singleton]
  unfold corrPair
  simp only [mul_one, zero_mul, add_zero]
  exact mul_ne_zero (by norm_num) (sub_ne_zero.2 hne)

end Balaban.LargeField.Def7v2
