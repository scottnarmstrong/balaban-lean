/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocSum
public import Balaban.Localization.I5Param

/-!
# The local form on complex fields: analytic dependence, normalization, dilation (A6-3, (L4))

The gas layer needs the local terms as functions `Ŵ_Y(w, g)` of the *complex* Gaussian variable
`w`, normalized at the constant configuration (`Ŵ_Y(0, g) = 0`), with joint analytic dependence on
the dilation `t ↦ Ŵ_Y(t w, g)` and on the source `g` (ORCH-B, the parity argument of the gas
layer). The coefficients of the rooted Lemma AE take complex `w` already; here:

* `analyticAt_linField_joint`, `analyticOnNhd_rootedCoef_param`: a term `τ(g; u)` jointly analytic
  in an external parameter `g` and the field `u` on a set `V` containing the cut fields gives
  coefficients `(g, w) ↦ coef_C(τ(g; ·); w)` analytic on every set `D` of data whose cut fields lie
  in `V` (`analyticOnNhd_coef_of_analyticOnNhd`, I5Param);
* `rootedCoef_zero_var`: at `w = 0` the cut field is the centre and every coefficient of a nonempty
  family vanishes;
* `normAt`: the terms normalized at the centre, `τ_a(u) - τ_a(φ₀)`; `rootedCoef_normAt`: the
  coefficients of nonempty families are unchanged; `localFormOf_zero_var`: the local form of
  normalized terms vanishes at `w = 0`; `sum_localFormOf_normAt`: its sum is
  `∑_a (τ_a(φ₀ + T(1) w) - τ_a(φ₀))`;
* `analyticOnNhd_localFormOf_param`: the local form is analytic in `(g, w)` on `D`;
  `analyticOnNhd_comp_dilation`: along the dilations `(g, t) ↦ F(g, t w₀)`;
  `continuousOn_comp_ofReal`: the restriction to real `w` is continuous.
-/

@[expose] public section

namespace Balaban.Green

open Finset Balaban.Localization Balaban.Analysis

section Param

variable {ι Ω G : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
  [NormedAddCommGroup G] [NormedSpace ℂ G] {T : (ι → ℂ) → Ω → Ω → ℂ}

omit [DecidableEq ι] in
/-- The cut field is analytic jointly in an external parameter, the variable and the cut
parameters. -/
theorem analyticAt_linField_joint {U : Set (ι → ℂ)}
    (hTan : ∀ x y, AnalyticOnNhd ℂ (fun s => T s x y) U) (φ₀ : Ω → ℂ)
    {q : (G × (Ω → ℂ)) × (ι → ℂ)} (hq : q.2 ∈ U) :
    AnalyticAt ℂ (fun q : (G × (Ω → ℂ)) × (ι → ℂ) => (q.1.1, linField φ₀ T q.2 q.1.2)) q := by
  refine AnalyticAt.prod (((ContinuousLinearMap.fst ℂ G (Ω → ℂ)).comp
    (ContinuousLinearMap.fst ℂ (G × (Ω → ℂ)) (ι → ℂ))).analyticAt q) ?_
  refine analyticAt_pi_iff.2 fun x => ?_
  refine analyticAt_const.add (Finset.analyticAt_fun_sum _ fun y _ => ?_)
  refine AnalyticAt.mul ((hTan x y q.2 hq).comp analyticAt_snd) ?_
  exact ((ContinuousLinearMap.proj y).comp ((ContinuousLinearMap.snd ℂ G (Ω → ℂ)).comp
    (ContinuousLinearMap.fst ℂ (G × (Ω → ℂ)) (ι → ℂ)))).analyticAt q

/-- **The coefficients depend analytically on the data.**  If `τ(g; u)` is analytic in `(g, u)` on
`V`, and for the data `(g, w) ∈ D` the cut fields `φ₀ + T(s) w` of the polydisc of radius `R > 1`
lie in `V` (with `g`), then `(g, w) ↦ coef_C(τ(g; ·); w)` is analytic on `D`. -/
theorem analyticOnNhd_rootedCoef_param {R : ℝ} (hR : 1 < R)
    (hTan : ∀ x y, AnalyticOnNhd ℂ (fun s => T s x y) (polydisc (0 : ι → ℂ) (fun _ => R)))
    {τ : G → (Ω → ℂ) → ℂ} {V : Set (G × (Ω → ℂ))}
    (hτ : AnalyticOnNhd ℂ (fun p : G × (Ω → ℂ) => τ p.1 p.2) V) (φ₀ : Ω → ℂ)
    {D : Set (G × (Ω → ℂ))}
    (hmem : ∀ p ∈ D, ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => R), (p.1, linField φ₀ T s p.2) ∈ V)
    (C : Finset ι) :
    AnalyticOnNhd ℂ (fun p : G × (Ω → ℂ) => rootedCoef (τ p.1) φ₀ T p.2 C) D :=
  analyticOnNhd_coef_of_analyticOnNhd hR
    (Φ := fun q : (G × (Ω → ℂ)) × (ι → ℂ) => τ q.1.1 (linField φ₀ T q.2 q.1.2))
    (fun q hq => AnalyticAt.comp (g := fun p : G × (Ω → ℂ) => τ p.1 p.2)
      (f := fun q : (G × (Ω → ℂ)) × (ι → ℂ) => (q.1.1, linField φ₀ T q.2 q.1.2))
      (hτ _ (hmem q.1 hq.1 q.2 hq.2)) (analyticAt_linField_joint hTan φ₀ hq.2)) C

omit [Fintype ι] [DecidableEq ι] in
/-- At `w = 0` the cut field is the centre. -/
theorem linField_zero_var (φ₀ : Ω → ℂ) (s : ι → ℂ) : linField φ₀ T s 0 = φ₀ := by
  funext x
  simp [linField]

/-- **The coefficients vanish at `w = 0`** for nonempty families. -/
theorem rootedCoef_zero_var (τ : (Ω → ℂ) → ℂ) (φ₀ : Ω → ℂ) {C : Finset ι} (hC : C.Nonempty) :
    rootedCoef τ φ₀ T 0 C = 0 := by
  unfold rootedCoef
  simp only [linField_zero_var]
  exact coef_const_eq_zero _ hC

/-- **The terms normalized at the centre**: `τ_a(u) - τ_a(φ₀)`. -/
def normAt {A : Type*} (τ : A → (Ω → ℂ) → ℂ) (φ₀ : Ω → ℂ) : A → (Ω → ℂ) → ℂ :=
  fun a u => τ a u - τ a φ₀

omit [Fintype Ω] in
theorem normAt_self {A : Type*} (τ : A → (Ω → ℂ) → ℂ) (φ₀ : Ω → ℂ) (a : A) :
    normAt τ φ₀ a φ₀ = 0 :=
  sub_self _

/-- Normalizing a term does not change its coefficients at nonempty families. -/
theorem rootedCoef_normAt {A : Type*} (τ : A → (Ω → ℂ) → ℂ) (φ₀ : Ω → ℂ) (a : A) (w : Ω → ℂ)
    {C : Finset ι} (hC : C.Nonempty) :
    rootedCoef (normAt τ φ₀ a) φ₀ T w C = rootedCoef (τ a) φ₀ T w C :=
  coef_sub_const hC _ _

omit [Fintype ι] [DecidableEq ι] in
/-- **Analytic dependence along the dilations**: a function analytic on a set `D` of data
`(g, w)` is analytic in `(g, t)` at the dilations `(g, t w₀)` that lie in `D`. -/
theorem analyticOnNhd_comp_dilation {F : G × (Ω → ℂ) → ℂ} {D : Set (G × (Ω → ℂ))}
    (hF : AnalyticOnNhd ℂ F D) (w₀ : Ω → ℂ) {E : Set (G × ℂ)}
    (hE : ∀ q ∈ E, (q.1, q.2 • w₀) ∈ D) :
    AnalyticOnNhd ℂ (fun q : G × ℂ => F (q.1, q.2 • w₀)) E := by
  intro q hq
  refine AnalyticAt.comp (g := F) (f := fun q : G × ℂ => (q.1, q.2 • w₀)) (hF _ (hE q hq)) ?_
  refine AnalyticAt.prod analyticAt_fst ?_
  exact analyticAt_snd.smul analyticAt_const

omit [Fintype ι] [DecidableEq ι] in
/-- **Continuity on real variables**: a function analytic on a set `D` of complex data is continuous
in `(g, w)` for real `w` with `(g, w) ∈ D`. -/
theorem continuousOn_comp_ofReal {F : G × (Ω → ℂ) → ℂ} {D : Set (G × (Ω → ℂ))}
    (hF : AnalyticOnNhd ℂ F D) {E : Set (G × (Ω → ℝ))}
    (hE : ∀ q ∈ E, (q.1, fun x => (q.2 x : ℂ)) ∈ D) :
    ContinuousOn (fun q : G × (Ω → ℝ) => F (q.1, fun x => (q.2 x : ℂ))) E := by
  intro q hq
  refine ((hF _ (hE q hq)).continuousAt.comp (f := fun q : G × (Ω → ℝ) =>
    (q.1, fun x => (q.2 x : ℂ))) ?_).continuousWithinAt
  refine (continuous_fst.prodMk ?_).continuousAt
  exact continuous_pi fun x => Complex.continuous_ofReal.comp ((continuous_apply x).comp
    continuous_snd)

end Param

section Form

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {A : Type*} [Fintype A] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  {RA : A → Finset Λ} {PB : ι → Finset Λ} {φ₀ : Λ × Fin N → ℂ}
  {T : (ι → ℂ) → Λ × Fin N → Λ × Fin N → ℂ}

open Classical in
/-- **The local form of normalized terms vanishes at `w = 0`.** -/
theorem localFormOf_zero_var {τ : A → (Λ × Fin N → ℂ) → ℂ} (hτ : ∀ a, τ a φ₀ = 0)
    (Y : Finset Λ) : localFormOf τ RA PB φ₀ T Y 0 = 0 := by
  unfold localFormOf
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [hτ a, ite_self, zero_add]
  exact Finset.sum_eq_zero fun C hC => rootedCoef_zero_var _ _ (Finset.mem_filter.1 hC).2.1

open Classical in
/-- **The sum of the local form of the normalized terms**: `∑_Y W_Y(w) = ∑_a (τ_a(φ₀ + T(1) w) -
τ_a(φ₀))`, when every term has the rooted expansion at `w`. -/
theorem sum_localFormOf_normAt {τ : A → (Λ × Fin N → ℂ) → ℂ} {w : Λ × Fin N → ℂ}
    (hexp : ∀ a, τ a (linField φ₀ T (fun _ => 1) w) = τ a φ₀ +
      ∑ C ∈ Finset.univ.filter (fun C : Finset ι => C.Nonempty ∧
        IsRootedFamily (blockPatch N PB) (blockSites N (RA a)) C), rootedCoef (τ a) φ₀ T w C) :
    ∑ Y, localFormOf (normAt τ φ₀) RA PB φ₀ T Y w =
      ∑ a, (τ a (linField φ₀ T (fun _ => 1) w) - τ a φ₀) := by
  refine sum_localFormOf fun a => ?_
  rw [normAt_self, zero_add]
  change τ a (linField φ₀ T (fun _ => 1) w) - τ a φ₀ = _
  rw [hexp a, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun C hC => ?_
  exact (rootedCoef_normAt τ φ₀ a w (Finset.mem_filter.1 hC).2.1).symm

/-- **The local form is analytic in the data**: for terms `τ(g)_a(u)` analytic in `(g, u)` on `V`,
and data `D` whose cut fields lie in `V`, `(g, w) ↦ W_Y(g; w)` is analytic on `D`. -/
theorem analyticOnNhd_localFormOf_param {R : ℝ} (hR : 1 < R)
    (hT : CutDecoupling (blockPatch N PB) R T)
    (hTan : ∀ x y, AnalyticOnNhd ℂ (fun s => T s x y) (polydisc (0 : ι → ℂ) (fun _ => R)))
    {τ : G → A → (Λ × Fin N → ℂ) → ℂ} {V : Set (G × (Λ × Fin N → ℂ))}
    (hτ : ∀ a, AnalyticOnNhd ℂ (fun p : G × (Λ × Fin N → ℂ) => τ p.1 a p.2) V)
    {D : Set (G × (Λ × Fin N → ℂ))}
    (hmem : ∀ p ∈ D, ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => R), (p.1, linField φ₀ T s p.2) ∈ V)
    (Y : Finset Λ) :
    AnalyticOnNhd ℂ (fun p : G × (Λ × Fin N → ℂ) => localFormOf (τ p.1) RA PB φ₀ T Y p.2) D := by
  classical
  intro p hp
  unfold localFormOf
  refine Finset.analyticAt_fun_sum _ fun a _ => ?_
  refine AnalyticAt.add ?_ (Finset.analyticAt_fun_sum _ fun C _ =>
    analyticOnNhd_rootedCoef_param hR hTan (τ := fun g => τ g a) (hτ a) φ₀ hmem C p hp)
  by_cases hY : RA a = Y
  · simp only [hY, ↓reduceIte]
    have h0 : (0 : ι → ℂ) ∈ polydisc (0 : ι → ℂ) (fun _ => R) := fun i => by
      simp only [Pi.zero_apply, sub_zero, norm_zero]; linarith
    have hV : (p.1, φ₀) ∈ V := by
      have := hmem p hp 0 h0
      rwa [linField_zero hT (by linarith)] at this
    exact AnalyticAt.comp (g := fun p : G × (Λ × Fin N → ℂ) => τ p.1 a p.2)
      (f := fun p : G × (Λ × Fin N → ℂ) => (p.1, φ₀)) (hτ a _ hV)
      (analyticAt_fst.prod analyticAt_const)
  · simp only [hY, ↓reduceIte]
    exact analyticAt_const

end Form

end Balaban.Green
