/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Complex.Basic

/-!
# Transfer of derivatives along a pair of linear maps

Let `f₁ = Λ ∘ f₂ ∘ T` and `f₂ = Λ' ∘ f₁ ∘ T'` with `T T' T = T` (linear maps `T`, `T'` between
normed spaces).  Then `D f₁ (p) = Λ ∘ D f₂ (T p) ∘ T` (`fderiv_transfer`).  The scalar corollaries
(`fderiv_eq_of_transfer`, `D2_eq_of_transfer`) compare the first and second derivatives of two
functions that read the same data, at points and directions that agree after the restriction `T T'`.
They are used for the terms of the small-field class on two tori, which are functions of the same
finite data (the field on a polymer) in different ambient spaces.
-/

@[expose] public section


namespace Balaban.Polymer

variable {E E' F F' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E'] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup F']
  [NormedSpace ℂ F']

/-- If `f (x + p) = f (x + q)` for all `x`, then `f` has the same derivative at `p` and at `q`, and
is differentiable at one of them iff at the other. -/
theorem fderiv_eq_of_shift {f : E → F} {p q : E} (h : ∀ x, f (x + p) = f (x + q)) :
    fderiv ℂ f p = fderiv ℂ f q ∧ (DifferentiableAt ℂ f p ↔ DifferentiableAt ℂ f q) := by
  have e : (fun x => f (x + p)) = fun x => f (x + q) := funext h
  refine ⟨?_, ?_⟩
  · have h1 := fderiv_comp_add_right (𝕜 := ℂ) (f := f) (x := 0) p
    have h2 := fderiv_comp_add_right (𝕜 := ℂ) (f := f) (x := 0) q
    rw [e] at h1
    rw [zero_add] at h1 h2
    rw [← h1, h2]
  · have h1 := differentiableAt_comp_add_right (𝕜 := ℂ) (f := f) (x := 0) p
    have h2 := differentiableAt_comp_add_right (𝕜 := ℂ) (f := f) (x := 0) q
    rw [e] at h1
    rw [zero_add] at h1 h2
    rw [← h1, h2]

/-- **Transfer of Fréchet derivatives along a pair of linear maps.**  Let `f₁ = Λ ∘ f₂ ∘ T` and
`f₂ = Λ' ∘ f₁ ∘ T'` with `T T' T = T`.  Then `D f₁ (p) = Λ ∘ D f₂ (T p) ∘ T`. -/
theorem fderiv_transfer {f₁ : E → F} {f₂ : E' → F'} (T : E →L[ℂ] E') (T' : E' →L[ℂ] E)
    (Λ : F' →L[ℂ] F) (Λ' : F →L[ℂ] F') (hTT : ∀ x, T (T' (T x)) = T x)
    (h₁ : ∀ x, f₁ x = Λ (f₂ (T x))) (h₂ : ∀ y, f₂ y = Λ' (f₁ (T' y))) (p : E) :
    fderiv ℂ f₁ p = Λ.comp ((fderiv ℂ f₂ (T p)).comp T) := by
  set P : E → E := fun x => T' (T x) with hP
  have hf1P : ∀ x, f₁ (P x) = f₁ x := fun x => by
    rw [h₁, h₁]; simp only [hP, hTT]
  have hPP : ∀ x, P (P x) = P x := fun x => by
    simp only [hP]; rw [hTT]
  have hshift : ∀ x, f₁ (x + p) = f₁ (x + P p) := fun x => by
    have a1 : f₁ (x + p) = f₁ (P (x + p)) := (hf1P _).symm
    have a2 : f₁ (x + P p) = f₁ (P (x + P p)) := (hf1P _).symm
    have a3 : P (x + p) = P (x + P p) := by
      simp only [hP, map_add, hTT]
    rw [a1, a2, a3]
  obtain ⟨hd, hdiff⟩ := fderiv_eq_of_shift hshift
  have hTP : T (P p) = T p := by simp only [hP]; rw [hTT]
  by_cases hf : DifferentiableAt ℂ f₂ (T p)
  · have hc : DifferentiableAt ℂ (f₂ ∘ T) p :=
      DifferentiableAt.comp (𝕜 := ℂ) p (g := f₂) (f := T) hf T.differentiableAt
    have e1 : f₁ = Λ ∘ (f₂ ∘ T) := funext h₁
    rw [e1, fderiv_comp p Λ.differentiableAt hc, ContinuousLinearMap.fderiv,
      fderiv_comp p hf T.differentiableAt, ContinuousLinearMap.fderiv]
  · have hnd : ¬ DifferentiableAt ℂ f₁ p := by
      intro hd1
      apply hf
      have hd2 : DifferentiableAt ℂ f₁ (P p) := hdiff.1 hd1
      have : DifferentiableAt ℂ (fun y => Λ' (f₁ (T' y))) (T p) := by
        have : DifferentiableAt ℂ (fun y => f₁ (T' y)) (T p) :=
          DifferentiableAt.comp (𝕜 := ℂ) (T p) (g := f₁) (f := T') (by
            show DifferentiableAt ℂ f₁ (T' (T p)); exact hd2) T'.differentiableAt
        exact Λ'.differentiableAt.comp (T p) this
      have e2 : f₂ = fun y => Λ' (f₁ (T' y)) := funext h₂
      rw [e2]; exact this
    rw [fderiv_zero_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hf]
    ext x; simp


/-- The scalar form: `f₁ = f₂ ∘ T` and `f₂ = f₁ ∘ T'` with `T T' T = T` give
`D f₁ (p) v = D f₂ (T p) (T v)`. -/
theorem fderiv_transfer_apply {f₁ : E → ℂ} {f₂ : E' → ℂ} (T : E →L[ℂ] E') (T' : E' →L[ℂ] E)
    (hTT : ∀ x, T (T' (T x)) = T x)
    (h₁ : ∀ x, f₁ x = f₂ (T x)) (h₂ : ∀ y, f₂ y = f₁ (T' y)) (p v : E) :
    fderiv ℂ f₁ p v = fderiv ℂ f₂ (T p) (T v) := by
  have := fderiv_transfer (f₁ := f₁) (f₂ := f₂) T T' (ContinuousLinearMap.id ℂ ℂ)
    (ContinuousLinearMap.id ℂ ℂ) hTT (fun x => by simpa using h₁ x) (fun y => by simpa using h₂ y) p
  rw [this]; rfl

/-- The second derivative along a pair of linear maps. -/
theorem D2_transfer {f₁ : E → ℂ} {f₂ : E' → ℂ} (T : E →L[ℂ] E') (T' : E' →L[ℂ] E)
    (hTT : ∀ x, T (T' (T x)) = T x) (hT'T' : ∀ y, T' (T (T' y)) = T' y)
    (h₁ : ∀ x, f₁ x = f₂ (T x)) (h₂ : ∀ y, f₂ y = f₁ (T' y)) (c v w : E) :
    fderiv ℂ (fderiv ℂ f₁) c v w = fderiv ℂ (fderiv ℂ f₂) (T c) (T v) (T w) := by
  have g1 : ∀ x, fderiv ℂ f₁ x = (ContinuousLinearMap.compL ℂ E E' ℂ).flip T
      (fderiv ℂ f₂ (T x)) := fun x => by
    ext v
    exact fderiv_transfer_apply T T' hTT h₁ h₂ x v
  have g2 : ∀ y, fderiv ℂ f₂ y = (ContinuousLinearMap.compL ℂ E' E ℂ).flip T'
      (fderiv ℂ f₁ (T' y)) := fun y => by
    ext v
    exact fderiv_transfer_apply T' T hT'T' h₂ h₁ y v
  have := fderiv_transfer (f₁ := fderiv ℂ f₁) (f₂ := fderiv ℂ f₂) T T'
    ((ContinuousLinearMap.compL ℂ E E' ℂ).flip T) ((ContinuousLinearMap.compL ℂ E' E ℂ).flip T')
    hTT g1 g2 c
  rw [this]; rfl


/-- A function that factors through an idempotent linear map `R` has the derivative of its
restriction: `D f (p) v = D f (R p) (R v)`. -/
theorem fderiv_of_idem {f : E → ℂ} (R : E →L[ℂ] E) (hRR : ∀ x, R (R x) = R x)
    (hf : ∀ x, f x = f (R x)) (p v : E) : fderiv ℂ f p v = fderiv ℂ f (R p) (R v) :=
  fderiv_transfer_apply R R (fun x => by rw [hRR, hRR]) hf hf p v

/-- The second derivative of a function that factors through an idempotent linear map. -/
theorem D2_of_idem {f : E → ℂ} (R : E →L[ℂ] E) (hRR : ∀ x, R (R x) = R x)
    (hf : ∀ x, f x = f (R x)) (c v w : E) :
    fderiv ℂ (fderiv ℂ f) c v w = fderiv ℂ (fderiv ℂ f) (R c) (R v) (R w) :=
  D2_transfer R R (fun x => by rw [hRR, hRR]) (fun x => by rw [hRR, hRR]) hf hf c v w

/-- **Derivatives of two functions related by `f₁ = f₂ ∘ T`, `f₂ = f₁ ∘ T'`**, at points and
directions that agree after the restriction `T T'`. -/
theorem fderiv_eq_of_transfer {f₁ : E → ℂ} {f₂ : E' → ℂ} (T : E →L[ℂ] E') (T' : E' →L[ℂ] E)
    (hTT : ∀ x, T (T' (T x)) = T x) (h₁ : ∀ x, f₁ x = f₂ (T x)) (h₂ : ∀ y, f₂ y = f₁ (T' y))
    {p : E} {q : E'} {v : E} {w : E'} (hp : T p = T (T' q)) (hv : T v = T (T' w)) :
    fderiv ℂ f₁ p v = fderiv ℂ f₂ q w := by
  rw [fderiv_transfer_apply T T' hTT h₁ h₂ p v, hp, hv]
  have hR : ∀ x, f₂ x = f₂ ((T.comp T') x) := fun x => by
    simp only [ContinuousLinearMap.comp_apply]; rw [← h₁ (T' x), ← h₂ x]
  have hRR : ∀ x, (T.comp T') ((T.comp T') x) = (T.comp T') x := fun x => by
    simp only [ContinuousLinearMap.comp_apply]; rw [hTT]
  exact (fderiv_of_idem (T.comp T') hRR hR q w).symm

/-- **Second derivatives of two functions related by `f₁ = f₂ ∘ T`, `f₂ = f₁ ∘ T'`.** -/
theorem D2_eq_of_transfer {f₁ : E → ℂ} {f₂ : E' → ℂ} (T : E →L[ℂ] E') (T' : E' →L[ℂ] E)
    (hTT : ∀ x, T (T' (T x)) = T x) (hT'T' : ∀ y, T' (T (T' y)) = T' y)
    (h₁ : ∀ x, f₁ x = f₂ (T x)) (h₂ : ∀ y, f₂ y = f₁ (T' y))
    {p : E} {q : E'} {v v' : E} {w w' : E'} (hp : T p = T (T' q)) (hv : T v = T (T' w))
    (hv' : T v' = T (T' w')) :
    fderiv ℂ (fderiv ℂ f₁) p v v' = fderiv ℂ (fderiv ℂ f₂) q w w' := by
  rw [D2_transfer T T' hTT hT'T' h₁ h₂ p v v', hp, hv, hv']
  have hR : ∀ x, f₂ x = f₂ ((T.comp T') x) := fun x => by
    simp only [ContinuousLinearMap.comp_apply]; rw [← h₁ (T' x), ← h₂ x]
  have hRR : ∀ x, (T.comp T') ((T.comp T') x) = (T.comp T') x := fun x => by
    simp only [ContinuousLinearMap.comp_apply]; rw [hTT]
  exact (D2_of_idem (T.comp T') hRR hR q w w').symm

end Balaban.Polymer
