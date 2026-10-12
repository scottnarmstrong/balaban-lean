/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.LayerDictionary

/-!
# The first `g`-derivative of the generating function `ℱ_k` of Def-6

`fderiv_Fcomp_zero`: for a representation in the class (`IsSF`, through its clause `analyticM`)
and a point `(ψ_k, h)` with the composed pairs `(ψ_k^{(j)}, h)` in the domains `Ξ^c_j(𝔹_j(X); 1,
ε_j)` of all polymers, the first `g`-derivative of `ℱ_k = Fcomp` at `g = 0` is
`⟨u, φ_k + ∑_j ℳ^{(j)}(ψ_k^{(j)}, h, 0)⟩`: the first-order part of (H.7) used in Lemma 2.2.
The product rule at `g = 0` applies because `Floc` is `⟨g, ℳ(g)⟩` with `ℳ` analytic at `g = 0`.
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
open Balaban.SmallField.Def6 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

section FirstOrder

variable {P : Consts} {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρ : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ} {Ek : ℝ}

/-- The vector `ℳ^{(j)}(x; ψ, h, g)` is differentiable in `g` at `g = 0` at a point `(ψ, h)` in
all the polymer domains. -/
theorem differentiableAt_Mloc (hsf : IsSF P β ν a Tm ρ Ek) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (x : CTorus d L N₁ m₁ k) {ψ h : Fld d L N₁ m₁ k N}
    (hdom : ∀ X, IsPolyDom P.m₀ j X →
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) ψ h)
    (i : Fin N) : DifferentiableAt ℂ (fun g => Mloc P.m₀ Tm j x ψ h g i) 0 := by
  classical
  have hfin : (polysAt P.m₀ j x).Finite := Set.toFinite _
  have hfun : (fun g => Mloc P.m₀ Tm j x ψ h g i) =
      fun g => ∑ X ∈ hfin.toFinset, Tm.M j x X ψ h g i := by
    funext g
    simp only [Mloc]
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_apply]
  rw [hfun]
  refine DifferentiableAt.fun_sum fun X hX => ?_
  have hXm := hfin.mem_toFinset.1 hX
  have hana := hsf.analyticM j hj1 hjk x X hXm.1 hXm.2
  have hq : ((ψ, h, (0 : Fld d L N₁ m₁ k N)) : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N ×
      Fld d L N₁ m₁ k N) ∈ {p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N |
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) p.1 p.2.1 ∧
        l1 p.2.2 < 1} := by
    refine ⟨hdom X hXm.1, ?_⟩
    simp [l1, Multiscale.vn]
  have hA := hana _ hq
  have hline : AnalyticAt ℂ (fun g : Fld d L N₁ m₁ k N => ((ψ, h, g) : Fld d L N₁ m₁ k N ×
      Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N)) 0 := by
    fun_prop
  have hcomp : AnalyticAt ℂ ((fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
      Tm.M j x X p.1 p.2.1 p.2.2) ∘ (fun g : Fld d L N₁ m₁ k N => ((ψ, h, g) : Fld d L N₁ m₁ k N ×
      Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N))) 0 := AnalyticAt.comp_of_eq hA hline rfl
  have hproj := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).analyticAt
    ((Tm.M j x X ψ h) 0)
  exact (hproj.comp hcomp).differentiableAt

/-- The coordinate functional `g ↦ g(x)_i`. -/
noncomputable def coordCLM (x : CTorus d L N₁ m₁ k) (i : Fin N) :
    Fld d L N₁ m₁ k N →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ k => Fin N → ℂ) x)

omit [NeZero L] [NeZero N₁] in
@[simp] theorem coordCLM_apply (x : CTorus d L N₁ m₁ k) (i : Fin N) (g : Fld d L N₁ m₁ k N) :
    coordCLM x i g = g x i := rfl

/-- **The first `g`-derivative of `ℱ_k` at `g = 0`**: `⟨u, φ_k + ∑_j ℳ^{(j)}(ψ_k^{(j)}, h, 0)⟩`,
the first-order part of (H.7). -/
theorem fderiv_Fcomp_zero (hsf : IsSF P β ν a Tm ρ Ek) (D : BgData (topGS d L N₁ m₁ k ϱ) N)
    (hdom : ∀ j, 1 ≤ j → j ≤ k → ∀ X, IsPolyDom P.m₀ j X →
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).1
        (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).2)
    (u : Fld d L N₁ m₁ k N) :
    fderiv ℂ (Fcomp P.m₀ Tm (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) D) 0 u =
      ∑ x, ∑ i, u x i *
        (svec (topGS d L N₁ m₁ k ϱ) (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k))
          (bgMass L k (β k) (ν k)) D) x i +
          ∑ j ∈ Finset.Icc 1 k, Mloc P.m₀ Tm j x
            (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).1
            (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).2 0 i) := by
  set c : CTorus d L N₁ m₁ k → Fin N → ℂ := fun x i =>
    svec (topGS d L N₁ m₁ k ϱ) (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k))
      (bgMass L k (β k) (ν k)) D) x i with hc
  set m : ℕ → CTorus d L N₁ m₁ k → Fin N → Fld d L N₁ m₁ k N → ℂ := fun j x i g =>
    Mloc P.m₀ Tm j x (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).1
      (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).2 g i with hm
  have hFeq : Fcomp P.m₀ Tm (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) D =
      fun g => ∑ x, ∑ i, (g x i * c x i + ∑ j ∈ Finset.Icc 1 k, g x i * m j x i g) := by
    funext g
    simp only [Fcomp, Floc, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  -- the derivative of each summand
  have hℓ : ∀ (x : CTorus d L N₁ m₁ k) (i : Fin N),
      HasFDerivAt (fun g : Fld d L N₁ m₁ k N => g x i) (coordCLM x i) 0 := fun x i =>
    (coordCLM x i).hasFDerivAt
  have hterm : ∀ (x : CTorus d L N₁ m₁ k) (i : Fin N),
      HasFDerivAt (fun g : Fld d L N₁ m₁ k N =>
        g x i * c x i + ∑ j ∈ Finset.Icc 1 k, g x i * m j x i g)
        (c x i • coordCLM x i + ∑ j ∈ Finset.Icc 1 k, m j x i 0 • coordCLM x i) 0 := by
    intro x i
    have h1 : HasFDerivAt (fun g : Fld d L N₁ m₁ k N => g x i * c x i)
        (c x i • coordCLM x i) 0 := (hℓ x i).mul_const (c x i)
    have h2 : ∀ j ∈ Finset.Icc 1 k, HasFDerivAt
        (fun g : Fld d L N₁ m₁ k N => g x i * m j x i g) (m j x i 0 • coordCLM x i) 0 := by
      intro j hj
      have hj' := Finset.mem_Icc.1 hj
      have hmd : HasFDerivAt (fun g => m j x i g) (fderiv ℂ (fun g => m j x i g) 0) 0 :=
        (differentiableAt_Mloc hsf hj'.1 hj'.2 x (hdom j hj'.1 hj'.2) i).hasFDerivAt
      have := (hℓ x i).mul hmd
      exact (show HasFDerivAt (fun g : Fld d L N₁ m₁ k N => g x i * m j x i g) _ 0 from
        this).congr_fderiv (by ext v; simp)
    have h3 := HasFDerivAt.fun_sum h2
    have h4 := h1.add h3
    exact h4
  have hall := HasFDerivAt.fun_sum (u := Finset.univ) fun x _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => hterm x i
  rw [hFeq]
  rw [hall.fderiv]
  simp only [_root_.sum_apply, _root_.add_apply, _root_.smul_apply, coordCLM_apply,
    smul_eq_mul, hc, hm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun j _ => mul_comm _ _

omit [NeZero L] [NeZero N₁] in
theorem sum_sum_single {α : Type*} [Fintype α] [DecidableEq α] (f : α → Fin N → ℂ) (x : α)
    (i : Fin N) : ∑ x', ∑ i', (Pi.single x (Pi.single i 1) : α → Fin N → ℂ) x' i' * f x' i' =
      f x i := by
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro i' _ hi'; simp [Pi.single_eq_of_ne hi']
    · simp
  · intro x' _ hx'; simp [Pi.single_eq_of_ne hx']
  · simp

/-- **Lemma 2.2, (O4) at first order**: given the composition identity and the point `(ψ_k, h)`
in the polymer domains, the first-order clause of (O4) (`fderiv ℱ_k (0) = ⟨·, M_k⟩`) holds iff
`∑_j 𝓜^{(j)} = ∑_j ℳ^{(j)}(·, 0)`: the layer's vectors `M^{(j)}` are exactly the first-order
terms of (H.7) up to the shift by `μ_j φ_j`. -/
theorem fderiv_Fcomp_iff (hsf : IsSF P β ν a Tm ρ Ek) (Ot : ObsTerms d L N₁ m₁ k N)
    (D : BgData (topGS d L N₁ m₁ k ϱ) N)
    (hdom : ∀ j, 1 ≤ j → j ≤ k → ∀ X, IsPolyDom P.m₀ j X →
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).1
        (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).2)
    (hcomp : ∀ j, 1 ≤ j → j ≤ k → ∀ (x : CTorus d L N₁ m₁ k) (i : Fin N),
      phiLevel (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D x i =
        svec (topGS d L N₁ m₁ k ϱ) (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k))
          (bgMass L k (β k) (ν k)) D) x i) :
    (∀ u : Fld d L N₁ m₁ k N,
      fderiv ℂ (Fcomp P.m₀ Tm (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) D) 0 u =
        ∑ x, ∑ i, u x i * Mk P β ν a Ot D x i) ↔
    ∀ (x : CTorus d L N₁ m₁ k) (i : Fin N),
      ∑ j ∈ Finset.Icc 1 k, Mscript P β ν a Ot D j x i =
        ∑ j ∈ Finset.Icc 1 k, Mloc P.m₀ Tm j x
          (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).1
          (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).2 0 i := by
  classical
  simp_rw [fderiv_Fcomp_zero hsf D hdom]
  constructor
  · intro h x i
    have h1 := h (Pi.single x (Pi.single i 1))
    rw [sum_sum_single (fun x i => svec (topGS d L N₁ m₁ k ϱ) (bgField (topGS d L N₁ m₁ k ϱ)
      (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) D) x i +
        ∑ j ∈ Finset.Icc 1 k, Mloc P.m₀ Tm j x
          (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).1
          (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).2 0 i) x i,
      sum_sum_single (fun x i => Mk P β ν a Ot D x i) x i] at h1
    exact ((first_order_iff P β ν a Tm Ot D hcomp x i).1 h1.symm)
  · intro h u
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    rw [((first_order_iff P β ν a Tm Ot D hcomp x i).2 (h x i))]

end FirstOrder

end Balaban.Observables
