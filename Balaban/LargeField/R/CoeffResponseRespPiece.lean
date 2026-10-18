/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseHyp
public import Balaban.Fluctuation.RenormExpBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The coefficient response at the backgrounds of one piece (P7 p. 500 (2.10)–(2.12))

`coeffChange_sameData_response` instantiated at the complex Euler–Lagrange backgrounds
`bgFieldC` of one datum `D` at two block coefficients `a₀`, `a₁` and one mass `ν`, with `D` in the
fixed-`h` class domain `Ξ^c_k(𝔹; 1, ε)` of both coefficients (`XiCOneReal`).  The premises of the
response are supplied by the background theorems:

* `IsEL`, `BgBounds` with the constant `K₁ C₁ ε` and `GreenSetting`: `XiCOne.bg`, `BgHyp.green`;
* `Dec2.OpSetting`: the fields of `BgHyp` and the separation of the generating set;
* the block read `‖Ψ - Q φ¹‖ ≤ 2 ε`: `XiCOneReal.factors`;
* `|φ⁰| ≤ 3/2`: `DataWit.vn_le` and the bound on `φ⁰ - Ψ`.

The conclusion is the weight-one supremum bound of `φ¹ - φ⁰` by `K_w (m · 2ε)`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization
  Balaban.SmallField Finset

variable {d L N : ℕ} [NeZero L]

/-- **The response at the backgrounds of one piece.**  There are `K_w, δ_w > 0` depending only on
`(d, L, N)` such that, for the datum `D` in the class domain of `a₀` and of `a₁` at one mass `ν`
and the standing hypotheses `BgHyp` of both coefficients, `m ≥ |a₁ - a₀|` on every layer, and
the separation of the generating set, the difference of the complex backgrounds satisfies the
weight-one supremum bounds with `K_w (m · 2ε)`. -/
theorem coeffResponse_piece (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₀ K : ℕ} [NeZero N₀] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ},
        (∃ N₁ m₁ : ℕ, N₀ = N₁ * L ^ m₁) →
        ∀ (a₀ a₁ : ℕ → ℝ) (ν ε m : ℝ) (D : BgData G N),
        BgHyp d L K ϱ a₀ ν → BgHyp d L K ϱ a₁ ν →
        2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1) →
        (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1 → 0 < ε → xiC1 d * ε ≤ bgC1 d L N →
        XiCOneReal G a₀ ν ε D → XiCOneReal G a₁ ν ε D →
        bgK1 d L N * (xiC1 d * ε) ≤ min (deltaStar d L N) δw →
        0 ≤ m →
        (∀ x : G.Ω 1, |a₁ (G.layerIndex (x : Torus d (N₀ * L ^ K))) -
          a₀ (G.layerIndex (x : Torus d (N₀ * L ^ K)))| ≤ m) →
        m * (2 * ε) ≤ min (deltaStar d L N) δw →
        (∀ (x : G.Ω 1) (i : Fin N), 1 * ‖(bgFieldC G a₁ ν (bgC0 d L N) D -
            bgFieldC G a₀ ν (bgC0 d L N) D) (x, i)‖ ≤ Kw * (m * (2 * ε))) ∧
        (∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N), 1 * (G.spacing x *
          ‖svec G (bgFieldC G a₁ ν (bgC0 d L N) D - bgFieldC G a₀ ν (bgC0 d L N) D)
            (x + Pi.single μ 1) i -
            svec G (bgFieldC G a₁ ν (bgC0 d L N) D - bgFieldC G a₀ ν (bgC0 d L N) D) x i‖) ≤
          Kw * (m * (2 * ε))) ∧
        (∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N), 1 * (G.spacing x *
          ‖svec G (bgFieldC G a₁ ν (bgC0 d L N) D - bgFieldC G a₀ ν (bgC0 d L N) D)
            (x - Pi.single μ 1) i -
            svec G (bgFieldC G a₁ ν (bgC0 d L N) D - bgFieldC G a₀ ν (bgC0 d L N) D) x i‖) ≤
          Kw * (m * (2 * ε))) := by
  obtain ⟨Kw, δw, hK, hδ, H⟩ := coeffChange_sameData_response (d := d) (L := L) N hd hL
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro N₀ K _ ϱ G hN a₀ a₁ ν ε m D H0 H1 hsepO hsm hε hc1 D0 D1 hsmall hm0 hm hmB
  obtain ⟨N₁, m₁, rfl⟩ := hN
  have : NeZero N₁ := ⟨left_ne_zero_of_mul (NeZero.ne (N₁ * L ^ m₁))⟩
  have hd0 : 0 < d := by omega
  obtain ⟨-, hs0, hb0, -⟩ := XiCOne.bg H0 hsm hε hc1 D0.xiCOne
  obtain ⟨-, hs1, hb1, -⟩ := XiCOne.bg H1 hsm hε hc1 D1.xiCOne
  have hOp : Dec2.OpSetting G a₀ ν :=
    ⟨⟨H0.hd, H0.hL, H0.mass, H0.weights, hsepO⟩, H0.massLe⟩
  have hδpos : 0 < xiC1 d * ε := by have := one_le_xiC1 d; positivity
  have hK1 : 0 < bgK1 d L N := bgK1_pos d L N
  have hδc1 : xiC1 d * ε ≤ bgC1 d L N := hc1
  obtain ⟨hδa, -, -, hK1c⟩ := bgC1_facts d L N hd0 hδc1
  have hc0 := bgC0_le (d := d) (L := L) (N := N)
  have hc6 := bgC0_le_c6 (d := d) (L := L) (N := N)
  have hδ1024 : xiC1 d * ε ≤ 1 / 1024 := (approxDelta_le d L hδa).1
  obtain ⟨W⟩ := DataWit.exists (D0.xiCOne.inDomainC H0 hsm)
  have hphi : ∀ x : G.Ω 1,
      vn (fun i => bgFieldC G a₀ ν (bgC0 d L N) D (x, i)) ≤ 3 / 2 := by
    intro x
    have hxd : (x : Torus d (N₁ * L ^ m₁ * L ^ K)) ∈ dataSites G :=
      (mem_dataSites G).2 (Or.inl x.2)
    have e : (fun i => bgFieldC G a₀ ν (bgC0 d L N) D (x, i)) =
        (fun i => bgFieldC G a₀ ν (bgC0 d L N) D (x, i) - D.Ψ x i) + D.Ψ x := by
      funext i; simp
    rw [e]
    have h1 := vn_add (fun i => bgFieldC G a₀ ν (bgC0 d L N) D (x, i) - D.Ψ x i) (D.Ψ x)
    have h2 := hb0.val x
    have h3 := W.vn_le hδpos hxd
    linarith
  have hB : ∀ (x : G.Ω 1) (i : Fin N), ‖D.Ψ x i -
      blockAvg G (bgFieldC G a₁ ν (bgC0 d L N) D) x i‖ ≤ 2 * ε := by
    intro x i
    have h1 := (XiCOneReal.factors H1 hε hsm hc1 D1).1 x x.2
    exact (norm_le_vn _ i).trans h1.le
  have hδ0 : 0 ≤ bgK1 d L N * (xiC1 d * ε) := by positivity
  have := (H a₀ a₁ ν m (2 * ε) (bgK1 d L N * (xiC1 d * ε)) D hs0.1 hs1.1 hb0 hb1
    H0.green hOp hδ0 hsmall (by linarith) hm0 (by linarith) hmB hm hB hphi).1.2
  exact ⟨this.val, this.fwd, this.bwd⟩

end Balaban.LargeField.ActionConv
