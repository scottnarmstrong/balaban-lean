/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# Descent of a trace-local analytic coefficient

Let `F` be a complex normed space, `V` a finite-dimensional complex normed space, and
`T : F →L[ℂ] V` a continuous linear trace.  Let `EA` be a complex subspace of `F` and `UA ⊆ F`
a set that is relatively open in `EA`.  Let `cA : F → ℂ` be analytic on `UA` as a function on the
space `EA`, bounded by `B` on `UA`, and exactly local: `T q = T q'` implies `cA q = cA q'` for
`q, q' ∈ UA`.  If every point `p` of a set `UB` has a point `q ∈ UA` with the same trace
(reachability), then there is a function `cB : F → ℂ` that agrees with `cA` at common traces, is
bounded by `B` on `UB`, and is analytic in a full neighbourhood in `F` of every point of `UB`.

The function is `g ∘ P ∘ T`, with `P` a linear projection of `V` onto `T(EA)` and `g` the
descended coefficient; analyticity comes from the affine local section
`p ↦ q₀ + S (T p - T q₀)`, where `S : V →L EA` is a linear right inverse of `T` on `T(EA)`
composed with `P`.  Neither a linear right inverse defined on the trace of the local space nor
openness of `T(UA)` in `T(EA)` is needed.
-/

public section

namespace Balaban

open Classical in
/-- Trace descent: see the module docstring. -/
theorem exists_traceDescent {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (T : F →L[ℂ] V) (EA : Submodule ℂ F) (UA UB : Set F) (cA : F → ℂ) (B : ℝ)
    (hUA : IsOpen (((↑) : EA → F) ⁻¹' UA))
    (hcA : AnalyticOnNhd ℂ (fun e : EA => cA e) (((↑) : EA → F) ⁻¹' UA))
    (hUAsub : UA ⊆ (EA : Set F))
    (hB : ∀ q ∈ UA, ‖cA q‖ ≤ B)
    (hloc : ∀ q ∈ UA, ∀ q' ∈ UA, T q = T q' → cA q = cA q')
    (hTR : ∀ p ∈ UB, ∃ q ∈ UA, T q = T p) :
    ∃ cB : F → ℂ, (∀ p ∈ UB, ∀ q ∈ UA, T q = T p → cB p = cA q) ∧
      (∀ p ∈ UB, ‖cB p‖ ≤ B) ∧ (∀ p ∈ UB, AnalyticAt ℂ cB p) := by
  -- the trace image of `EA`
  set W : Submodule ℂ V := EA.map (T : F →ₗ[ℂ] V) with hW
  -- linear section of `T` over `W`
  let TE : EA →ₗ[ℂ] W := (T : F →ₗ[ℂ] V).restrict (p := EA) (q := W)
    (fun x hx => Submodule.mem_map_of_mem hx)
  have hTE : Function.Surjective TE := by
    rintro ⟨w, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨S0, hS0⟩ := LinearMap.exists_rightInverse_of_surjective TE
    (LinearMap.range_eq_top.mpr hTE)
  obtain ⟨P0, hP0⟩ := LinearMap.exists_leftInverse_of_injective W.subtype
    (Submodule.ker_subtype W)
  -- `S : V →L EA`
  let S : V →ₗ[ℂ] EA := S0 ∘ₗ P0
  have hSc : Continuous S := LinearMap.continuous_of_finiteDimensional S
  let Pm : V →ₗ[ℂ] V := W.subtype ∘ₗ P0
  have hTS : ∀ v, T (S v : EA) = Pm v := by
    intro v
    have := congrArg (fun f => (f (P0 v) : V)) hS0
    simpa [TE, S, Pm] using this
  have hPW : ∀ w ∈ W, Pm w = w := by
    intro w hw
    have := LinearMap.congr_fun hP0 ⟨w, hw⟩
    show ((P0 w : W) : V) = w
    rw [show P0 w = ⟨w, hw⟩ by simpa using this]
  have hPmW : ∀ v, Pm v ∈ W := fun v => (P0 v).2
  have hPc : Continuous Pm := LinearMap.continuous_of_finiteDimensional Pm
  -- the descended coefficient
  let g : V → ℂ := fun w => if h : ∃ q ∈ UA, T q = w then cA h.choose else 0
  have hg : ∀ q ∈ UA, g (T q) = cA q := by
    intro q hq
    have h : ∃ q' ∈ UA, T q' = T q := ⟨q, hq, rfl⟩
    simp only [g, h, ↓reduceDIte]
    exact hloc _ h.choose_spec.1 q hq h.choose_spec.2
  have hfix : ∀ p ∈ UB, ∀ q ∈ UA, T q = T p → Pm (T p) = T p := by
    intro p _ q hq hqp
    exact hPW _ (hqp ▸ Submodule.mem_map_of_mem (hUAsub hq))
  refine ⟨fun p => g (Pm (T p)), ?_, ?_, ?_⟩
  · intro p hp q hq hqp
    simp only
    rw [hfix p hp q hq hqp, ← hqp]
    exact hg q hq
  · intro p hp
    obtain ⟨q, hq, hqp⟩ := hTR p hp
    have : g (Pm (T p)) = cA q := by
      rw [hfix p hp q hq hqp, ← hqp]; exact hg q hq
    simp only [this]
    exact hB q hq
  · intro p hp
    obtain ⟨q, hq, hqp⟩ := hTR p hp
    have hq' : q ∈ EA := hUAsub hq
    let q0 : EA := ⟨q, hq'⟩
    -- continuous affine map `F → EA`
    let ψ : F → EA := fun p' => q0 + S (T p' - T q)
    have hψlin : ψ = fun p' => q0 + (LinearMap.toContinuousLinearMap S) (T p' - T q) := rfl
    have hψa : AnalyticAt ℂ ψ p := by
      rw [hψlin]
      exact analyticAt_const.add
        (((LinearMap.toContinuousLinearMap S).analyticAt _).comp
          (((T.analyticAt p)).sub analyticAt_const))
    have hψp : ψ p = q0 := by simp [ψ, hqp]
    have hmem : q0 ∈ ((↑) : EA → F) ⁻¹' UA := hq
    have hevent : ∀ᶠ p' in nhds p, ψ p' ∈ ((↑) : EA → F) ⁻¹' UA := by
      apply hψa.continuousAt.eventually_mem
      rw [hψp]; exact hUA.mem_nhds hmem
    have han : AnalyticAt ℂ ((fun e : EA => cA e) ∘ ψ) p := by
      have := hcA (ψ p) (by rw [hψp]; exact hmem)
      exact this.comp hψa
    refine han.congr ?_
    filter_upwards [hevent] with p' hp'
    have hq1 : (ψ p' : F) ∈ UA := hp'
    have hT : T (ψ p' : F) = Pm (T p') := by
      have h1 : T ((q0 : EA) : F) = T q := rfl
      have hqW : T q ∈ W := Submodule.mem_map_of_mem hq'
      have h2 : T ((S (T p' - T q) : EA) : F) = Pm (T p' - T q) := hTS _
      have h3 : ((ψ p' : EA) : F) = ((q0 : EA) : F) + ((S (T p' - T q) : EA) : F) := rfl
      rw [h3, map_add, h1, h2, map_sub, hPW (T q) hqW]
      abel
    simp only [Function.comp]
    rw [← hT]
    exact (hg _ hq1).symm
