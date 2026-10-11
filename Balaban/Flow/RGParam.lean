/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.RGEquations

/-!
# The renormalization-group equations with a data-dependent linear part

Balaban P4 Section 5, in the form needed by the small-field step (`notes/phase1/SMALLFIELD.md`
§3.4, review S-03): the lower triangular matrix `A(p)` of (5.21) depends analytically on the data
`p`.

* `exists_rg_solution_triangular_param` (L1): existence, uniqueness, analyticity of the solution
  of `A(p) ξ + c(ξ,p) = f(ξ,p)`;
* `rg_solution_real` (L2): the solution is real for real data (conjugation symmetry);
* `fixedPoint_dist_le` (Lemma 3.3): stability of the fixed point of a contraction.
-/

@[expose] public section

open Metric Set

namespace Balaban.Flow

section Param

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The explicit inverse of a lower triangular `3 × 3` matrix, by forward substitution. -/
noncomputable def triInv (A : Matrix (Fin 3) (Fin 3) ℂ) (z : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![z 0 / A 0 0, (z 1 - A 1 0 * (z 0 / A 0 0)) / A 1 1,
    (z 2 - A 2 0 * (z 0 / A 0 0) - A 2 1 * ((z 1 - A 1 0 * (z 0 / A 0 0)) / A 1 1)) / A 2 2]

theorem triInv_add (A : Matrix (Fin 3) (Fin 3) ℂ) (u v : Fin 3 → ℂ) :
    triInv A (u + v) = triInv A u + triInv A v := by
  ext i
  fin_cases i <;> simp [triInv] <;> ring

theorem TriangularBounds.diag_ne {A : Matrix (Fin 3) (Fin 3) ℂ} {ε : ℝ}
    (hA : TriangularBounds A ε) : A 0 0 ≠ 0 ∧ A 1 1 ≠ 0 ∧ A 2 2 ≠ 0 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := hA.d0; rw [h] at this; norm_num at this
  · have := hA.d1; rw [h] at this; norm_num at this
  · have := hA.d2; rw [h] at this; norm_num at this

theorem TriangularBounds.mulVec_triInv {A : Matrix (Fin 3) (Fin 3) ℂ} {ε : ℝ}
    (hA : TriangularBounds A ε) (z : Fin 3 → ℂ) : A.mulVec (triInv A z) = z := by
  obtain ⟨h0, h1, h2⟩ := hA.diag_ne
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, triInv, hA.upper01, hA.upper02,
      hA.upper12] <;> field_simp <;> ring

theorem TriangularBounds.norm_triInv_le {A : Matrix (Fin 3) (Fin 3) ℂ} {ε : ℝ}
    (hA : TriangularBounds A ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (z : Fin 3 → ℂ) :
    ‖triInv A z‖ ≤ 42 * ‖z‖ :=
  hA.norm_le hε0 hε1 (hA.mulVec_triInv z)

theorem TriangularBounds.triInv_mulVec {A : Matrix (Fin 3) (Fin 3) ℂ} {ε : ℝ}
    (hA : TriangularBounds A ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (y : Fin 3 → ℂ) :
    triInv A (A.mulVec y) = y := by
  have h := hA.norm_le hε0 hε1 (y := triInv A (A.mulVec y) - y) (z := 0)
    (by rw [Matrix.mulVec_sub, hA.mulVec_triInv, sub_self])
  have : ‖triInv A (A.mulVec y) - y‖ = 0 := le_antisymm (by simpa using h) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- **(L1)** One step of the renormalization-group equations with an analytic, data-dependent
lower triangular linear part `A(p)` (review S-03).  `A` is analytic on `P` entrywise. -/
theorem exists_rg_solution_triangular_param {A : G → Matrix (Fin 3) (Fin 3) ℂ} {ε : ℝ}
    {P : Set G} (hP : IsOpen P) (hAan : ∀ i j, AnalyticOnNhd ℂ (fun p => A p i j) P)
    (hA : ∀ p ∈ P, TriangularBounds (A p) ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {c f : (Fin 3 → ℂ) × G → (Fin 3 → ℂ)}
    {κ η c₁₀ : ℝ} (hκ : 0 < κ) (hη : 0 ≤ η) (hc₁₀ : 0 < c₁₀)
    (hcond : 16 * (42 * η) * max (2 * (42 * κ)) (1 / c₁₀) ≤ 1)
    (hc : AnalyticOnNhd ℂ c (closedBall (0 : Fin 3 → ℂ) c₁₀ ×ˢ P))
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : Fin 3 → ℂ) c₁₀ ×ˢ P))
    (hcb : ∀ p ∈ P, ∀ ε' : ℝ, 0 ≤ ε' → ε' ≤ c₁₀ → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ ε' →
      ‖c (ξ, p)‖ ≤ κ * ε' ^ 2)
    (hfb : ∀ p ∈ P, ∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ c₁₀ → ‖f (ξ, p)‖ ≤ η) :
    ∃ ξs : G → (Fin 3 → ℂ),
      (∀ p ∈ P, ‖ξs p‖ ≤ rgRadius (42 * κ) c₁₀ ∧
        (A p).mulVec (ξs p) + c (ξs p, p) = f (ξs p, p) ∧
        (∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ rgRadius (42 * κ) c₁₀ →
          (A p).mulVec ξ + c (ξ, p) = f (ξ, p) → ξ = ξs p) ∧ ‖ξs p‖ ≤ 84 * η) ∧
      AnalyticOnNhd ℂ ξs P := by
  set S : Set ((Fin 3 → ℂ) × G) := closedBall (0 : Fin 3 → ℂ) c₁₀ ×ˢ P with hS
  have hAq : ∀ i j, AnalyticOnNhd ℂ (fun q : (Fin 3 → ℂ) × G => A q.2 i j) S := fun i j =>
    (hAan i j).comp analyticOnNhd_snd (fun q hq => hq.2)
  have hne : ∀ q ∈ S, A q.2 0 0 ≠ 0 ∧ A q.2 1 1 ≠ 0 ∧ A q.2 2 2 ≠ 0 :=
    fun q hq => (hA q.2 hq.2).diag_ne
  have hBan : ∀ g : (Fin 3 → ℂ) × G → (Fin 3 → ℂ), AnalyticOnNhd ℂ g S →
      AnalyticOnNhd ℂ (fun q => triInv (A q.2) (g q)) S := by
    intro g hg
    have hgi : ∀ i, AnalyticOnNhd ℂ (fun q => g q i) S := analyticOnNhd_pi_iff.mp hg
    have h0 : AnalyticOnNhd ℂ (fun q => g q 0 / A q.2 0 0) S :=
      (hgi 0).div (hAq 0 0) (fun q hq => (hne q hq).1)
    have h1 : AnalyticOnNhd ℂ (fun q => (g q 1 - A q.2 1 0 * (g q 0 / A q.2 0 0)) / A q.2 1 1) S :=
      ((hgi 1).sub ((hAq 1 0).mul h0)).div (hAq 1 1) (fun q hq => (hne q hq).2.1)
    have h2 : AnalyticOnNhd ℂ (fun q => (g q 2 - A q.2 2 0 * (g q 0 / A q.2 0 0) -
        A q.2 2 1 * ((g q 1 - A q.2 1 0 * (g q 0 / A q.2 0 0)) / A q.2 1 1)) / A q.2 2 2) S :=
      (((hgi 2).sub ((hAq 2 0).mul h0)).sub ((hAq 2 1).mul h1)).div (hAq 2 2)
        (fun q hq => (hne q hq).2.2)
    refine analyticOnNhd_pi_iff.mpr fun i => ?_
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have h42κ : 0 < 42 * κ := by positivity
  obtain ⟨ξs, hξs, hanal⟩ := exists_rg_solution (c := fun q => triInv (A q.2) (c q))
    (f := fun q => triInv (A q.2) (f q)) hP (κ := 42 * κ) (η := 42 * η) (c₁₀ := c₁₀) h42κ
    (by positivity) hc₁₀ hcond (hBan c hc) (hBan f hf)
    (fun p hp ε' h0 h1 ξ hξ => (hA p hp |>.norm_triInv_le hε0 hε1 _).trans (by
      have := hcb p hp ε' h0 h1 ξ hξ
      nlinarith))
    (fun p hp ξ hξ => (hA p hp |>.norm_triInv_le hε0 hε1 _).trans (by
      have := hfb p hp ξ hξ
      nlinarith))
  refine ⟨ξs, fun p hp => ?_, hanal⟩
  obtain ⟨h1, h2, h3, -, h5⟩ := hξs p hp
  refine ⟨h1, ?_, ?_, by linarith⟩
  · have := congrArg (A p).mulVec h2
    rw [Matrix.mulVec_add, (hA p hp).mulVec_triInv, (hA p hp).mulVec_triInv] at this
    exact this
  · intro ξ hξ h
    refine h3 ξ hξ ?_
    have := congrArg (triInv (A p)) h
    rwa [triInv_add, (hA p hp).triInv_mulVec hε0 hε1] at this

end Param

section Real

variable {G : Type*}

/-- Entrywise complex conjugation of a vector. -/
def conjVec (ξ : Fin 3 → ℂ) : Fin 3 → ℂ := fun i => starRingEnd ℂ (ξ i)

theorem norm_conjVec (ξ : Fin 3 → ℂ) : ‖conjVec ξ‖ = ‖ξ‖ := by
  simp [conjVec, Pi.norm_def]

theorem conjVec_involutive (ξ : Fin 3 → ℂ) : conjVec (conjVec ξ) = ξ := by
  ext i; simp [conjVec]

theorem conjVec_add (u v : Fin 3 → ℂ) : conjVec (u + v) = conjVec u + conjVec v := by
  ext i; simp [conjVec]

theorem mulVec_conjVec (M : Matrix (Fin 3) (Fin 3) ℂ) (ξ : Fin 3 → ℂ) :
    (M.map (starRingEnd ℂ)).mulVec (conjVec ξ) = conjVec (M.mulVec ξ) := by
  ext i
  simp [conjVec, Matrix.mulVec, dotProduct, map_sum]

/-- **(L2)** Reality of the solution.  If `ξs` solves the system at `p` and at `σ p` with
uniqueness in the closed ball of radius `r`, and the data have the conjugation symmetry
`A (σ p) = conj (A p)`, `c (conj ξ, σ p) = conj (c (ξ, p))`, `f (conj ξ, σ p) = conj (f (ξ, p))`,
then `ξs (σ p) = conj (ξs p)`. -/
theorem rg_solution_real {A : G → Matrix (Fin 3) (Fin 3) ℂ} {c f : (Fin 3 → ℂ) × G → (Fin 3 → ℂ)}
    {P : Set G} {r : ℝ} {ξs : G → (Fin 3 → ℂ)} {σ : G → G}
    (hσP : ∀ p ∈ P, σ p ∈ P)
    (hAσ : ∀ p ∈ P, A (σ p) = (A p).map (starRingEnd ℂ))
    (hcσ : ∀ p ∈ P, ∀ ξ, c (conjVec ξ, σ p) = conjVec (c (ξ, p)))
    (hfσ : ∀ p ∈ P, ∀ ξ, f (conjVec ξ, σ p) = conjVec (f (ξ, p)))
    (hsol : ∀ p ∈ P, ‖ξs p‖ ≤ r ∧ (A p).mulVec (ξs p) + c (ξs p, p) = f (ξs p, p) ∧
      ∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ r → (A p).mulVec ξ + c (ξ, p) = f (ξ, p) → ξ = ξs p)
    {p : G} (hp : p ∈ P) : ξs (σ p) = conjVec (ξs p) := by
  obtain ⟨h1, h2, -⟩ := hsol p hp
  obtain ⟨-, -, h3⟩ := hsol (σ p) (hσP p hp)
  symm
  refine h3 _ (by rw [norm_conjVec]; exact h1) ?_
  rw [hAσ p hp, mulVec_conjVec, hcσ p hp, hfσ p hp, ← conjVec_add, h2]

/-- A solution at a fixed point of `σ` is real. -/
theorem rg_solution_real_of_fixed {A : G → Matrix (Fin 3) (Fin 3) ℂ}
    {c f : (Fin 3 → ℂ) × G → (Fin 3 → ℂ)}
    {P : Set G} {r : ℝ} {ξs : G → (Fin 3 → ℂ)} {σ : G → G}
    (hσP : ∀ p ∈ P, σ p ∈ P)
    (hAσ : ∀ p ∈ P, A (σ p) = (A p).map (starRingEnd ℂ))
    (hcσ : ∀ p ∈ P, ∀ ξ, c (conjVec ξ, σ p) = conjVec (c (ξ, p)))
    (hfσ : ∀ p ∈ P, ∀ ξ, f (conjVec ξ, σ p) = conjVec (f (ξ, p)))
    (hsol : ∀ p ∈ P, ‖ξs p‖ ≤ r ∧ (A p).mulVec (ξs p) + c (ξs p, p) = f (ξs p, p) ∧
      ∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ r → (A p).mulVec ξ + c (ξ, p) = f (ξ, p) → ξ = ξs p)
    {p : G} (hp : p ∈ P) (hfix : σ p = p) (i : Fin 3) : (ξs p i).im = 0 := by
  have h := rg_solution_real hσP hAσ hcσ hfσ hsol hp
  rw [hfix] at h
  have := congrFun h i
  simp only [conjVec] at this
  exact Complex.conj_eq_iff_im.mp this.symm

end Real

section Stability

variable {E : Type*} [NormedAddCommGroup E]

/-- **Lemma 3.3** (stability of the fixed point).  If `Φ` is a `1/2`-contraction on `S` and `Φ'`
is within `δ` of `Φ` on `S`, then fixed points `ξ, ξ'` of `Φ, Φ'` in `S` satisfy
`‖ξ - ξ'‖ ≤ 2 δ`. -/
theorem fixedPoint_dist_le {S : Set E} {Φ Φ' : E → E} {δ : ℝ} {ξ ξ' : E}
    (hlip : ∀ x ∈ S, ∀ y ∈ S, ‖Φ x - Φ y‖ ≤ 1 / 2 * ‖x - y‖)
    (hclose : ∀ x ∈ S, ‖Φ x - Φ' x‖ ≤ δ) (hξ : ξ ∈ S) (hξ' : ξ' ∈ S)
    (hfix : Φ ξ = ξ) (hfix' : Φ' ξ' = ξ') : ‖ξ - ξ'‖ ≤ 2 * δ := by
  have h1 := hlip ξ hξ ξ' hξ'
  have h2 := hclose ξ' hξ'
  have e : ξ - ξ' = (Φ ξ - Φ ξ') + (Φ ξ' - Φ' ξ') := by rw [hfix, hfix']; abel
  have : ‖ξ - ξ'‖ ≤ 1 / 2 * ‖ξ - ξ'‖ + δ := by
    calc ‖ξ - ξ'‖ = ‖(Φ ξ - Φ ξ') + (Φ ξ' - Φ' ξ')‖ := by rw [← e]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add h1 h2)
  linarith

end Stability

end Balaban.Flow
