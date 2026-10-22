/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.Basic

/-!
# Second-order jets of complex functions at `0`

`IsJet f a b c` says that `f` is differentiable near `0` with derivative `g` which is differentiable
at `0`, and `f 0 = a`, `g 0 = b`, `g' 0 = c`: the 2-jet of `f` at `0` is `(a, b, c)`
(`c = f''(0)`).  Jets are closed under sums, products and finite sums (`IsJet.add`, `IsJet.mul`,
`IsJet.sum`), and analytic functions have jets (`isJet_of_analyticAt`).
-/

@[expose] public section

namespace Balaban.Flow

open Filter Topology

/-- `f` has the 2-jet `(a, b, c)` at `0`. -/
def IsJet (f : ℂ → ℂ) (a b c : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, (∀ᶠ s in 𝓝 (0 : ℂ), HasDerivAt f (g s) s) ∧ f 0 = a ∧ g 0 = b ∧ HasDerivAt g c 0

theorem IsJet.hasDerivAt {f : ℂ → ℂ} {a b c : ℂ} (h : IsJet f a b c) : HasDerivAt f b 0 := by
  obtain ⟨g, hg, -, hb, -⟩ := h
  have := hg.self_of_nhds
  rwa [hb] at this

theorem IsJet.deriv2 {f : ℂ → ℂ} {a b c : ℂ} (h : IsJet f a b c) : deriv (deriv f) 0 = c := by
  obtain ⟨g, hg, -, -, hc⟩ := h
  have : deriv f =ᶠ[𝓝 0] g := by
    filter_upwards [hg] with s hs using hs.deriv
  rw [this.deriv_eq]; exact hc.deriv

theorem IsJet.deriv1 {f : ℂ → ℂ} {a b c : ℂ} (h : IsJet f a b c) : deriv f 0 = b :=
  h.hasDerivAt.deriv

theorem IsJet.value {f : ℂ → ℂ} {a b c : ℂ} (h : IsJet f a b c) : f 0 = a := by
  obtain ⟨g, -, ha, -, -⟩ := h; exact ha

theorem isJet_const (k : ℂ) : IsJet (fun _ => k) k 0 0 :=
  ⟨fun _ => 0, Filter.Eventually.of_forall fun s => hasDerivAt_const s k, rfl, rfl,
    hasDerivAt_const _ _⟩

theorem isJet_id : IsJet (fun s => s) 0 1 0 :=
  ⟨fun _ => 1, Filter.Eventually.of_forall fun s => hasDerivAt_id s, rfl, rfl, hasDerivAt_const _ _⟩

theorem IsJet.add {f f' : ℂ → ℂ} {a b c a' b' c' : ℂ} (h : IsJet f a b c) (h' : IsJet f' a' b' c') :
    IsJet (fun s => f s + f' s) (a + a') (b + b') (c + c') := by
  obtain ⟨g, hg, ha, hb, hc⟩ := h
  obtain ⟨g', hg', ha', hb', hc'⟩ := h'
  refine ⟨fun s => g s + g' s, ?_, by simp [ha, ha'], by simp [hb, hb'], hc.add hc'⟩
  filter_upwards [hg, hg'] with s h1 h2 using h1.add h2

theorem IsJet.neg {f : ℂ → ℂ} {a b c : ℂ} (h : IsJet f a b c) :
    IsJet (fun s => -f s) (-a) (-b) (-c) := by
  obtain ⟨g, hg, ha, hb, hc⟩ := h
  refine ⟨fun s => -g s, ?_, by simp [ha], by simp [hb], hc.neg⟩
  filter_upwards [hg] with s h1 using h1.neg

theorem IsJet.sub {f f' : ℂ → ℂ} {a b c a' b' c' : ℂ} (h : IsJet f a b c) (h' : IsJet f' a' b' c') :
    IsJet (fun s => f s - f' s) (a - a') (b - b') (c - c') := by
  simpa [sub_eq_add_neg] using h.add h'.neg

theorem IsJet.mul {f f' : ℂ → ℂ} {a b c a' b' c' : ℂ} (h : IsJet f a b c) (h' : IsJet f' a' b' c') :
    IsJet (fun s => f s * f' s) (a * a') (b * a' + a * b') (c * a' + 2 * b * b' + a * c') := by
  obtain ⟨g, hg, ha, hb, hc⟩ := h
  obtain ⟨g', hg', ha', hb', hc'⟩ := h'
  have hf0 : HasDerivAt f b 0 := by have := hg.self_of_nhds; rwa [hb] at this
  have hf0' : HasDerivAt f' b' 0 := by have := hg'.self_of_nhds; rwa [hb'] at this
  refine ⟨fun s => g s * f' s + f s * g' s, ?_, by simp [ha, ha'], by simp [hb, hb', ha, ha'], ?_⟩
  · filter_upwards [hg, hg'] with s h1 h2 using h1.mul h2
  · have h3 := (hc.mul hf0').add (hf0.mul hc')
    refine h3.congr_deriv ?_
    rw [ha, ha', hb, hb']; ring

theorem IsJet.const_mul {f : ℂ → ℂ} {a b c : ℂ} (k : ℂ) (h : IsJet f a b c) :
    IsJet (fun s => k * f s) (k * a) (k * b) (k * c) := by
  have := (isJet_const k).mul h
  simpa using this

theorem IsJet.sum {ι : Type*} (t : Finset ι) {f : ι → ℂ → ℂ} {a b c : ι → ℂ}
    (h : ∀ i ∈ t, IsJet (f i) (a i) (b i) (c i)) :
    IsJet (fun s => ∑ i ∈ t, f i s) (∑ i ∈ t, a i) (∑ i ∈ t, b i) (∑ i ∈ t, c i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isJet_const 0
  | insert j t hj ih =>
    simp only [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IsJet.congr {f f' : ℂ → ℂ} {a b c : ℂ} (h : IsJet f a b c) (he : f =ᶠ[𝓝 0] f') :
    IsJet f' a b c := by
  obtain ⟨g, hg, ha, hb, hc⟩ := h
  refine ⟨g, ?_, by rw [← he.self_of_nhds]; exact ha, hb, hc⟩
  have : ∀ᶠ s in 𝓝 (0 : ℂ), f =ᶠ[𝓝 s] f' := he.eventually_nhds
  filter_upwards [hg, this] with s h1 h2 using h1.congr_of_eventuallyEq h2.symm

/-- Functions analytic at `0` have a 2-jet. -/
theorem isJet_of_analyticAt {f : ℂ → ℂ} (h : AnalyticAt ℂ f 0) :
    IsJet f (f 0) (deriv f 0) (deriv (deriv f) 0) := by
  refine ⟨deriv f, ?_, rfl, rfl, ?_⟩
  · have := h.eventually_analyticAt
    filter_upwards [this] with s hs using hs.differentiableAt.hasDerivAt
  · exact (h.deriv.differentiableAt).hasDerivAt

theorem IsJet.of_eq {f : ℂ → ℂ} {a b c a' b' c' : ℂ} (h : IsJet f a b c) (ha : a = a') (hb : b = b')
    (hc : c = c') : IsJet f a' b' c' := by subst ha hb hc; exact h

theorem IsJet.of_funext {f f' : ℂ → ℂ} {a b c : ℂ} (h : IsJet f a b c) (he : ∀ s, f s = f' s) :
    IsJet f' a b c := by
  have : f = f' := funext he
  rwa [← this]

end Balaban.Flow
