/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.MassResponseHyp
public import Balaban.LargeField.R.CoeffResponseHyp
public import Balaban.Background.Def5

/-!
# The mass response of the real background of a datum of the real domain (blocker 4)

`massResponse_real`: for a datum `D` of the real domain `Ψ̃(G; δ)` at the mass `ν` and an external
field of unit length, the backgrounds `bgFieldC G a ν` and `bgFieldC G a 0` of the same datum differ by
at most `K_w (m · 2)` in the weight-one supremum norms of the value and of the forward and
backward difference quotients, `m ≥ ν ℓ(x)²` on `Ω₁` (P6 (2.31) mass change, P7 (2.14)).
The domain at mass `0` is that at mass `ν` (`inDomainR_zero_mass`).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization Balaban.SmallField Finset

variable {d L N : ℕ} [NeZero L]

/-- The real domain at a mass `ν ≥ 0` is contained in the real domain at mass `0` (the clauses
(R3), (R4) have a factor `ν`). -/
theorem inDomainR_zero_mass {N₀ k : ℕ} [NeZero N₀] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
    {ν δ : ℝ} (hδ : 0 < δ) {D : BgData G N} (hD : InDomainR G ν δ D) : InDomainR G 0 δ D := by
  obtain ⟨Ψ, h, hP, hΨ, hh⟩ := hD
  refine ⟨Ψ, h, ⟨hP.layerConst, hP.r1, hP.r2, fun x _ => ?_, ?_⟩, hΨ, hh⟩
  · simpa using pow_pos hδ 2
  · simpa using pow_pos hδ 2

/-- **The mass response of the real background of one datum.** -/
theorem massResponse_real (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
        (a : ℕ → ℝ) (ν δ m : ℝ) (D : BgData G N),
        BgHyp d L K ϱ a ν → BgHyp d L K ϱ a 0 →
        2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1) →
        0 < δ → δ ≤ bgC1 d L N → InDomainR G ν δ D →
        bgK1 d L N * δ ≤ min (deltaStar d L N) δw →
        0 ≤ m → m * 2 ≤ min (deltaStar d L N) δw →
        (∀ x : G.Ω 1, ν * G.spacing (x : Torus d (N₁ * L ^ m₁ * L ^ K)) ^ 2 ≤ m) →
        (∀ x : G.Ω 1, ∑ i, ‖D.h x i‖ ^ 2 = 1) →
        (∀ (x : G.Ω 1) (i : Fin N), 1 * ‖(bgFieldC G a ν (bgC0 d L N) D -
            bgFieldC G a 0 (bgC0 d L N) D) (x, i)‖ ≤ Kw * (m * 2)) ∧
        (∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N), 1 * (G.spacing x *
          ‖svec G (bgFieldC G a ν (bgC0 d L N) D - bgFieldC G a 0 (bgC0 d L N) D)
            (x + Pi.single μ 1) i -
            svec G (bgFieldC G a ν (bgC0 d L N) D - bgFieldC G a 0 (bgC0 d L N) D) x i‖) ≤
          Kw * (m * 2)) ∧
        (∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N), 1 * (G.spacing x *
          ‖svec G (bgFieldC G a ν (bgC0 d L N) D - bgFieldC G a 0 (bgC0 d L N) D)
            (x - Pi.single μ 1) i -
            svec G (bgFieldC G a ν (bgC0 d L N) D - bgFieldC G a 0 (bgC0 d L N) D) x i‖) ≤
          Kw * (m * 2)) := by
  obtain ⟨Kw, δw, hK, hδ, H⟩ := massChange_sameData_response_unit (d := d) (L := L) N hd hL
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν δ m D Hν H0 hsepO hδ0 hδc hD hδs hm0 hm hsp hh
  have hd0 : 0 < d := by omega
  have hD0 := inDomainR_zero_mass hδ0 hD
  obtain ⟨φν, αν, hsν, hbν, huν, hunν, -, -⟩ := bg_real Hν hδ0 hδc hD
  obtain ⟨φ0, α0, hs0, hb0, hu0, hun0, -, -⟩ := bg_real H0 hδ0 hδc hD0
  obtain ⟨eν, -⟩ := bgFieldC_eq hsν huν
  obtain ⟨e0, -⟩ := bgFieldC_eq hs0 hu0
  rw [eν, e0]
  have hOp : Dec2.OpSetting G a 0 :=
    ⟨⟨H0.hd, H0.hL, H0.mass, H0.weights, hsepO⟩, H0.massLe⟩
  obtain ⟨-, -, -, hK1⟩ := bgC1_facts d L N hd0 hδc
  have hc6 := bgC0_le_c6 (d := d) (L := L) (N := N)
  have hδ0' : 0 ≤ bgK1 d L N * δ := by have := bgK1_pos d L N; positivity
  have hν0 : 0 ≤ ν := Hν.mass
  have hun : ∀ φ : G.Ω 1 × Fin N → ℂ, IsRealUnitField G φ → ∀ x : G.Ω 1, ∑ i, ‖φ (x, i)‖ ^ 2 = 1 :=
    fun φ hφ x => (hφ x).2
  have := (H a ν m (bgK1 d L N * δ) D hs0.1 hsν.1 hb0 hbν H0.green hOp hδ0' hδs
    (by linarith) hm0 hm hν0 hsp (hun φ0 hun0) (hun φν hunν) hh).1.2
  exact ⟨this.val, this.fwd, this.bwd⟩

end Balaban.LargeField.ActionConv
