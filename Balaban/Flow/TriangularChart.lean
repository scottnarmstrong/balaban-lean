/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.Flow.RGInfty

/-!
# An open complex chart for triangular RG matrices

Pointwise bounds on a real datum do not provide the open complex parameter set
required by `rg_step_infty`. This lemma turns strict matrix margins at one datum
and structural equalities valid on an analytic domain into such a chart. The
strict margins and analytic domain for the physical matrix must be supplied by
the one-step successor calculation.
-/

@[expose] public section

open Filter Topology Set

namespace Balaban.Flow

/-- Complex-chart margin for a triangular matrix family. The diagonal `1,1`
and the `1,0` estimate may be non-strict when they hold structurally on the
whole analytic domain. -/
theorem exists_triangular_complex_chart {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {A : G → Matrix (Fin 3) (Fin 3) ℂ} {U : Set G} {p₀ : G} {ε : ℝ}
    (hU : IsOpen U) (hp₀ : p₀ ∈ U)
    (hAan : ∀ i j, AnalyticOnNhd ℂ (fun p => A p i j) U)
    (hzero : ∀ p ∈ U, A p 0 1 = 0 ∧ A p 0 2 = 0 ∧ A p 1 2 = 0)
    (hfixed : ∀ p ∈ U, 1 ≤ ‖A p 1 1‖ ∧ ‖A p 1 0‖ ≤ ε)
    (hd0 : 1 / 2 < ‖A p₀ 0 0‖) (hd2 : 1 / 4 < ‖A p₀ 2 2‖)
    (hl20 : ‖A p₀ 2 0‖ < 5 / 2 * ε) (hl21 : ‖A p₀ 2 1‖ < 3 / 2) :
    ∃ P : Set G, IsOpen P ∧ p₀ ∈ P ∧ P ⊆ U ∧
      (∀ i j, AnalyticOnNhd ℂ (fun p => A p i j) P) ∧
      ∀ p ∈ P, TriangularBounds (A p) ε := by
  have heU : ∀ᶠ p in 𝓝 p₀, p ∈ U := hU.mem_nhds hp₀
  have he0 : ∀ᶠ p in 𝓝 p₀, 1 / 2 < ‖A p 0 0‖ :=
    continuousAt_const.eventually_lt ((hAan 0 0 p₀ hp₀).continuousAt.norm) hd0
  have he2 : ∀ᶠ p in 𝓝 p₀, 1 / 4 < ‖A p 2 2‖ :=
    continuousAt_const.eventually_lt ((hAan 2 2 p₀ hp₀).continuousAt.norm) hd2
  have he20 : ∀ᶠ p in 𝓝 p₀, ‖A p 2 0‖ < 5 / 2 * ε :=
    ((hAan 2 0 p₀ hp₀).continuousAt.norm).eventually_lt continuousAt_const hl20
  have he21 : ∀ᶠ p in 𝓝 p₀, ‖A p 2 1‖ < 3 / 2 :=
    ((hAan 2 1 p₀ hp₀).continuousAt.norm).eventually_lt continuousAt_const hl21
  have hev : ∀ᶠ p in 𝓝 p₀, p ∈ U ∧ 1 / 2 < ‖A p 0 0‖ ∧
      1 / 4 < ‖A p 2 2‖ ∧ ‖A p 2 0‖ < 5 / 2 * ε ∧ ‖A p 2 1‖ < 3 / 2 := by
    filter_upwards [heU, he0, he2, he20, he21] with p hu h0 h2 h20 h21
    exact ⟨hu, h0, h2, h20, h21⟩
  obtain ⟨P, hP, hPopen, hp⟩ := eventually_nhds_iff.1 hev
  refine ⟨P, hPopen, hp, (fun p hp => (hP p hp).1), ?_, ?_⟩
  · intro i j p hp
    exact hAan i j p (hP p hp).1
  · intro p hp
    obtain ⟨hu, h0, h2, h20, h21⟩ := hP p hp
    obtain ⟨hz01, hz02, hz12⟩ := hzero p hu
    obtain ⟨hd1, hl10⟩ := hfixed p hu
    exact ⟨hz01, hz02, hz12, h0.le, hd1, h2.le, hl10, h20.le, h21.le⟩

end Balaban.Flow
