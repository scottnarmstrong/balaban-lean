/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRLiftGeom
public import Balaban.LargeField.Base.KF0FRBox
import Mathlib.Tactic.Linarith

/-!
# `KF0FRLift`: the terms of route FR on two tori (route FR, (T))

`notes/phase1/KF0-FR.md` (T). A term of the torus of side `n` whose base site lies in the box
`InBox R₀` is carried to the term of the torus of side `n'` at the image of its base site
(`frTau`). When `2(R₀ + 2R + 2) + 1 < n, n'`:

* `frSupp_frTau`: its support is the image of the support;
* `frField_boxMap`, `sum_frQ_boxMap`: the whitened field and the defect rows are carried over
  (`kf0CR_torus_eq`, `frQ_torus_eq`);
* `frF_frTau`: the term is the same function of the configuration, for configurations and sources
  that agree through `boxMap` on the support.
-/

@[expose] public section

open MeasureTheory Balaban.Green Balaban.Polymer

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

local notation "E" => EuclideanSpace ℝ (Fin N)

variable {d n n' : ℕ} [NeZero n] [NeZero n']

/-- The term at the image of the base site. -/
def frTau (n' : ℕ) : FRTerm d n → FRTerm d n'
  | Sum.inl x => Sum.inl (boxMap n n' x)
  | Sum.inr (x, μ) => Sum.inr (boxMap n n' x, μ)

omit [NeZero n] [NeZero n'] in
theorem frBase_frTau (t : FRTerm d n) : frBase (frTau n' t) = boxMap n n' (frBase t) := by
  rcases t with x | ⟨x, μ⟩ <;> rfl

theorem frSupp_frTau {R R₀ : ℕ} (h1 : 2 * (R₀ + 2 * R + 2) + 1 < n)
    (h2 : 2 * (R₀ + 2 * R + 2) + 1 < n') {t : FRTerm d n} (ht : InBox d R₀ n (frBase t)) :
    frSupp R (frTau n' t) = (frSupp R t).image (boxMap n n') := by
  rcases t with x | ⟨x, μ⟩
  · rw [frSupp_eq_torusBall, frSupp_eq_torusBall]
    exact (torusBall_image_boxMap (r := 2 * R + 1) (by omega) (by omega) ht).symm
  · rw [frSupp_eq_torusBall, frSupp_eq_torusBall]
    exact (torusBall_image_boxMap (r := R + 1) (by omega) (by omega) ht).symm

/-- The sites of the support of a term with base site in the box lie in a larger box. -/
theorem inBox_of_mem_frSupp {R R₀ : ℕ} (h1 : 2 * (R₀ + 2 * R + 2) + 1 < n) {t : FRTerm d n}
    (ht : InBox d R₀ n (frBase t)) {y : Torus d n} (hy : y ∈ frSupp R t) :
    InBox d (R₀ + 2 * R + 2) n y := by
  have := inBox_of_mem_torusBall (r := 2 * R + 1) (by omega) ht
    (mem_torusBall.2 (torusDist_frBase_le hy))
  exact fun ν => (this ν).trans (by omega)

/-- **The whitened field is carried over.** -/
theorem frField_boxMap {β ν : ℝ} {R R₁ : ℕ} (h1 : 2 * (R₁ + R) + 1 < n)
    (h2 : 2 * (R₁ + R) + 1 < n') {x : Torus d n} (hx : InBox d R₁ n x)
    {ψ : Torus d n → perp h} {ψ' : Torus d n' → perp h}
    (hψ : ∀ y ∈ torusBall x R, ψ' (boxMap n n' y) = ψ y) :
    frField d n' β ν R ψ' (boxMap n n' x) = frField d n β ν R ψ x := by
  unfold frField matAct
  refine sum_torusBall_boxMap (r := R) h1 h2 hx _ _ (fun y hy => ?_) (fun y' hy' => ?_)
    (fun y hy => ?_)
  · have : kf0CR d n ν R x y = 0 := kf0CR_eq_zero_of_lt (by
      rw [mem_torusBall] at hy; linarith)
    simp [Matrix.smul_apply, this]
  · have : kf0CR d n' ν R (boxMap n n' x) y' = 0 := kf0CR_eq_zero_of_lt (by
      rw [mem_torusBall] at hy'; linarith)
    simp [Matrix.smul_apply, this]
  · have hd := torusDisp_boxMap (n' := n') (R₁ := R₁) (r := R) h1 (by omega) hx
      (mem_torusBall.1 hy)
    rw [Matrix.smul_apply, Matrix.smul_apply, hψ y hy,
      kf0CR_torus_eq ν (m := n') (m' := n) (by omega) (by omega) hd]

/-- **The defect rows are carried over.** -/
theorem sum_frQ_boxMap {ν : ℝ} {R R₁ : ℕ} (h1 : 2 * (R₁ + (2 * R + 1)) + 1 < n)
    (h2 : 2 * (R₁ + (2 * R + 1)) + 1 < n') {x : Torus d n} (hx : InBox d R₁ n x)
    {ψ : Torus d n → perp h} {ψ' : Torus d n' → perp h}
    (hψ : ∀ y ∈ torusBall x (2 * R + 1 : ℕ), ψ' (boxMap n n' y) = ψ y) :
    ∑ y', frQ d n' ν R (boxMap n n' x) y' * inner ℝ (ψ' (boxMap n n' x) : E) (ψ' y' : E) =
      ∑ y, frQ d n ν R x y * inner ℝ (ψ x : E) (ψ y : E) := by
  have hxx : x ∈ torusBall x (2 * R + 1 : ℕ) := by
    rw [mem_torusBall, torusDist_self_eq]; positivity
  refine sum_torusBall_boxMap (r := 2 * R + 1) h1 h2 hx _ _ (fun y hy => ?_) (fun y' hy' => ?_)
    (fun y hy => ?_)
  · have : frQ d n ν R x y = 0 := frQ_eq_zero_of_lt (by
      rw [mem_torusBall] at hy; push_cast at hy ⊢; linarith)
    simp [this]
  · have : frQ d n' ν R (boxMap n n' x) y' = 0 := frQ_eq_zero_of_lt (by
      rw [mem_torusBall] at hy'; push_cast at hy' ⊢; linarith)
    simp [this]
  · have hd := torusDisp_boxMap (n' := n') (R₁ := R₁) (r := 2 * R + 1) h1 (by omega) hx
      (mem_torusBall.1 hy)
    rw [hψ y hy, hψ x hxx, frQ_torus_eq ν (m := n') (m' := n) (by omega) (by omega) hd]

/-- **A term is the same function of configurations that agree through `boxMap`.** -/
theorem frF_frTau (hh : ‖h‖ = 1) {β ν ε : ℝ} {R R₀ : ℕ} (h1 : 2 * (R₀ + 2 * R + 2) + 1 < n)
    (h2 : 2 * (R₀ + 2 * R + 2) + 1 < n') {g : Torus d n → Fin N → ℂ}
    {g' : Torus d n' → Fin N → ℂ} {t : FRTerm d n} (ht : InBox d R₀ n (frBase t))
    {ω : Torus d n → perp h × Bool} {ω' : Torus d n' → perp h × Bool}
    (hω : ∀ y ∈ frSupp R t, ω' (boxMap n n' y) = ω y)
    (hg : g' (boxMap n n' (frBase t)) = g (frBase t)) :
    frF h hh β ν ε R g' (frTau n' t) ω' = frF h hh β ν ε R g t ω := by
  rcases t with x | ⟨x, μ⟩
  all_goals simp only [frBase] at ht hg
  · have hS : ∀ y, torusDist d n x y ≤ (2 * R + 1 : ℕ) → ω' (boxMap n n' y) = ω y := by
      intro y hy
      refine hω y ?_
      simp only [frSupp, Finset.mem_filter, Finset.mem_univ, true_and]
      push_cast at hy
      exact hy
    have hx0 : x ∈ torusBall x (2 * R + 1 : ℕ) := by
      rw [mem_torusBall, torusDist_self_eq]; positivity
    have hu : frField d n' β ν R (frPsi h ω') (boxMap n n' x) = frField d n β ν R (frPsi h ω) x :=
      frField_boxMap h (R₁ := R₀) (by omega) (by omega) ht fun y hy => by
        simp only [frPsi]
        rw [hS y (by rw [mem_torusBall] at hy; push_cast at hy ⊢; linarith)]
    have hQ := sum_frQ_boxMap h (ν := ν) (R := R) (R₁ := R₀) (by omega) (by omega) ht
      (ψ := frPsi h ω) (ψ' := frPsi h ω') fun y hy => by
        simp only [frPsi]; rw [hS y (mem_torusBall.1 hy)]
    have hσ : frSig h ω' (boxMap n n' x) = frSig h ω x := by
      simp only [frSig]; rw [hS x (mem_torusBall.1 hx0)]
    show frSite h hh β ν ε R g' (boxMap n n' x) ω' = frSite h hh β ν ε R g x ω
    unfold frSite
    rw [hu, hσ, hg, hQ]
  · have hS : ∀ y, torusDist d n x y ≤ (R + 1 : ℕ) → ω' (boxMap n n' y) = ω y := by
      intro y hy
      refine hω y ?_
      simp only [frSupp, Finset.mem_filter, Finset.mem_univ, true_and]
      push_cast at hy
      exact hy
    set e : Torus d n := x + Pi.single μ 1
    have he1 := torusDist_add_single_le_one x μ
    have hebox : InBox d (R₀ + 1) n e :=
      inBox_of_mem_torusBall (r := 1) (by omega) ht (mem_torusBall.2 (by exact_mod_cast he1))
    have hxbox : InBox d (R₀ + 1) n x := fun ν => (ht ν).trans (by omega)
    have hstep : boxMap n n' e = boxMap n n' x + Pi.single μ 1 :=
      (KF0Lift.boxMap_step_iff (R := R₀ + 1) (by omega) (by omega) hxbox hebox μ).1 rfl
    have hux : frField d n' β ν R (frPsi h ω') (boxMap n n' x) = frField d n β ν R (frPsi h ω) x :=
      frField_boxMap h (R₁ := R₀) (by omega) (by omega) ht fun y hy => by
        simp only [frPsi]
        rw [hS y (by rw [mem_torusBall] at hy; push_cast at hy ⊢; linarith)]
    have hue : frField d n' β ν R (frPsi h ω') (boxMap n n' e) = frField d n β ν R (frPsi h ω) e :=
      frField_boxMap h (R₁ := R₀ + 1) (by omega) (by omega) hebox fun y hy => by
        simp only [frPsi]
        rw [hS y (by
          rw [mem_torusBall] at hy
          have := torusDist_triangle_gen x e y
          push_cast at hy ⊢; linarith)]
    have hσx : frSig h ω' (boxMap n n' x) = frSig h ω x := by
      simp only [frSig]; rw [hS x (by rw [torusDist_self_eq]; positivity)]
    have hσe : frSig h ω' (boxMap n n' e) = frSig h ω e := by
      simp only [frSig]; rw [hS e (by push_cast; linarith)]
    show frBond h β ν R (boxMap n n' x) μ ω' = frBond h β ν R x μ ω
    unfold frBond
    rw [← hstep, hux, hue, hσx, hσe]

end

end Balaban.LargeField.KF0FR
