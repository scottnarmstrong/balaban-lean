/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysSourceResp
public import Balaban.LargeField.R.CoeffResponseRespPiece
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The response of one conversion step at the backgrounds of a piece (P7 p. 500 (2.10)–(2.12))

`jointChange_sameData_response` at the complex Euler–Lagrange backgrounds `bgFieldC` of one
datum `D` at `(a₀, ν₀)` and `(a₁, ν₁)`, with `D` in the fixed-`h` class domain of both.  The
supplied premises are those of `coeffResponse_piece`; the new ones are the mass change, written
as `ℓ(x)² (ν₁ - ν₀)² ≤ m_ν² ν₁`, and `ν₁ > 0`.  The conclusion is the weight-one supremum bounds
of `φ¹ - φ⁰` and of its difference quotients by `K_w · 2ε (m + m_ν)`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization
  Balaban.SmallField Finset

variable {d L N : ℕ} [NeZero L]

/-- The mass part of the joint source: `ℓ² |ν₁ - ν₀| |φ¹ - h| ≤ 2 ε m_ν`. -/
theorem massSource_joint_le {ℓ Δν ν₁ mν ε t : ℝ} (hν : 0 ≤ mν) (hε : 0 ≤ ε)
    (ht : 0 ≤ t) (hsq : ℓ ^ 2 * Δν ^ 2 ≤ mν ^ 2 * ν₁) (hr : ν₁ * ℓ ^ 2 * t ^ 2 ≤ 4 * ε ^ 2) :
    ℓ ^ 2 * (|Δν| * t) ≤ 2 * ε * mν := by
  have h0 : 0 ≤ ℓ ^ 2 * (|Δν| * t) := by positivity
  have h1 : (ℓ ^ 2 * (|Δν| * t)) ^ 2 ≤ (2 * ε * mν) ^ 2 := by
    have hs : |Δν| ^ 2 = Δν ^ 2 := sq_abs _
    have e : (ℓ ^ 2 * (|Δν| * t)) ^ 2 = (ℓ ^ 2 * Δν ^ 2) * (ℓ ^ 2 * t ^ 2) := by
      rw [mul_pow, mul_pow, hs]; ring
    rw [e]
    calc (ℓ ^ 2 * Δν ^ 2) * (ℓ ^ 2 * t ^ 2) ≤ (mν ^ 2 * ν₁) * (ℓ ^ 2 * t ^ 2) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = mν ^ 2 * (ν₁ * ℓ ^ 2 * t ^ 2) := by ring
      _ ≤ mν ^ 2 * (4 * ε ^ 2) := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = (2 * ε * mν) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ h0 (by positivity) (by norm_num)).1 h1

/-- **The response of one conversion step at the backgrounds of one piece.** -/
theorem jointResponse_piece (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₀ K : ℕ} [NeZero N₀] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ},
        (∃ N₁ m₁ : ℕ, N₀ = N₁ * L ^ m₁) →
        ∀ (a₀ a₁ : ℕ → ℝ) (ν₀ ν₁ ε m mν : ℝ) (D : BgData G N),
        BgHyp d L K ϱ a₀ ν₀ → BgHyp d L K ϱ a₁ ν₁ →
        2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1) →
        (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1 → 0 < ε → xiC1 d * ε ≤ bgC1 d L N →
        XiCOneReal G a₀ ν₀ ε D → XiCOneReal G a₁ ν₁ ε D →
        bgK1 d L N * (xiC1 d * ε) ≤ min (deltaStar d L N) δw →
        0 ≤ m → 0 ≤ mν → 0 < ν₁ →
        (∀ x : G.Ω 1, |a₁ (G.layerIndex (x : Torus d (N₀ * L ^ K))) -
          a₀ (G.layerIndex (x : Torus d (N₀ * L ^ K)))| ≤ m) →
        (∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 * (ν₁ - ν₀) ^ 2 ≤ mν ^ 2 * ν₁) →
        2 * ε * (m + mν) ≤ min (deltaStar d L N) δw →
        (∀ (x : G.Ω 1) (i : Fin N), 1 * ‖(bgFieldC G a₁ ν₁ (bgC0 d L N) D -
            bgFieldC G a₀ ν₀ (bgC0 d L N) D) (x, i)‖ ≤ Kw * (2 * ε * (m + mν))) ∧
        (∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N), 1 * (G.spacing x *
          ‖svec G (bgFieldC G a₁ ν₁ (bgC0 d L N) D - bgFieldC G a₀ ν₀ (bgC0 d L N) D)
            (x + Pi.single μ 1) i -
            svec G (bgFieldC G a₁ ν₁ (bgC0 d L N) D - bgFieldC G a₀ ν₀ (bgC0 d L N) D) x i‖) ≤
          Kw * (2 * ε * (m + mν))) ∧
        (∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N), 1 * (G.spacing x *
          ‖svec G (bgFieldC G a₁ ν₁ (bgC0 d L N) D - bgFieldC G a₀ ν₀ (bgC0 d L N) D)
            (x - Pi.single μ 1) i -
            svec G (bgFieldC G a₁ ν₁ (bgC0 d L N) D - bgFieldC G a₀ ν₀ (bgC0 d L N) D) x i‖) ≤
          Kw * (2 * ε * (m + mν))) := by
  obtain ⟨Kw, δw, hK, hδ, H⟩ := jointChange_sameData_response (d := d) (L := L) N hd hL
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro N₀ K _ ϱ G hN a₀ a₁ ν₀ ν₁ ε m mν D H0 H1 hsepO hsm hε hc1 D0 D1 hsmall hm0 hmν0 hν1
    hm hmν hSB
  obtain ⟨N₁, m₁, rfl⟩ := hN
  have : NeZero N₁ := ⟨left_ne_zero_of_mul (NeZero.ne (N₁ * L ^ m₁))⟩
  have hd0 : 0 < d := by omega
  obtain ⟨-, hs0, hb0, -⟩ := XiCOne.bg H0 hsm hε hc1 D0.xiCOne
  obtain ⟨-, hs1, hb1, -⟩ := XiCOne.bg H1 hsm hε hc1 D1.xiCOne
  have hOp : Dec2.OpSetting G a₀ ν₀ :=
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
      vn (fun i => bgFieldC G a₀ ν₀ (bgC0 d L N) D (x, i)) ≤ 3 / 2 := by
    intro x
    have hxd : (x : Torus d (N₁ * L ^ m₁ * L ^ K)) ∈ dataSites G :=
      (mem_dataSites G).2 (Or.inl x.2)
    have e : (fun i => bgFieldC G a₀ ν₀ (bgC0 d L N) D (x, i)) =
        (fun i => bgFieldC G a₀ ν₀ (bgC0 d L N) D (x, i) - D.Ψ x i) + D.Ψ x := by
      funext i; simp
    rw [e]
    have h1 := vn_add (fun i => bgFieldC G a₀ ν₀ (bgC0 d L N) D (x, i) - D.Ψ x i) (D.Ψ x)
    have h2 := hb0.val x
    have h3 := W.vn_le hδpos hxd
    linarith
  have hB : ∀ (x : G.Ω 1) (i : Fin N), ‖D.Ψ x i -
      blockAvg G (bgFieldC G a₁ ν₁ (bgC0 d L N) D) x i‖ ≤ 2 * ε := by
    intro x i
    have h1 := (XiCOneReal.factors H1 hε hsm hc1 D1).1 x x.2
    exact (norm_le_vn _ i).trans h1.le
  have hS : ∀ (x : G.Ω 1) (i : Fin N), G.spacing (x : Torus d (N₁ * L ^ m₁ * L ^ K)) ^ 2 *
      ‖qStar G (a₁ - a₀) (fun y j => D.Ψ y j -
          blockAvg G (bgFieldC G a₁ ν₁ (bgC0 d L N) D) y j) (x, i) -
        ((ν₁ - ν₀ : ℝ) : ℂ) * (bgFieldC G a₁ ν₁ (bgC0 d L N) D (x, i) - D.h x i)‖ ≤
      2 * ε * (m + mν) := by
    intro x i
    have h1 := coeffSource_bound (m := m) (Bh := 2 * ε) a₀ a₁ D
      (bgFieldC G a₁ ν₁ (bgC0 d L N) D) hm hB x i
    have hvn := (XiCOneReal.factors H1 hε hsm hc1 D1).2.2.1 x x.2
    have hsv : svec G (bgFieldC G a₁ ν₁ (bgC0 d L N) D) x i =
        bgFieldC G a₁ ν₁ (bgC0 d L N) D (x, i) := svec_of_mem G _ x i
    have hnorm : ‖bgFieldC G a₁ ν₁ (bgC0 d L N) D (x, i) - D.h x i‖ ≤
        vn (fun j => svec G (bgFieldC G a₁ ν₁ (bgC0 d L N) D) x j - D.h x j) := by
      have := norm_le_vn (fun j => svec G (bgFieldC G a₁ ν₁ (bgC0 d L N) D) x j - D.h x j) i
      simpa only [hsv] using this
    have h2 := massSource_joint_le (ℓ := G.spacing (x : Torus d (N₁ * L ^ m₁ * L ^ K)))
      (Δν := ν₁ - ν₀) hmν0 hε.le ((norm_nonneg _).trans hnorm)
      (hmν x) (by linarith [hvn, mul_comm ν₁ (G.spacing (x : Torus d (N₁ * L ^ m₁ * L ^ K)) ^ 2)])
    have h3 : G.spacing (x : Torus d (N₁ * L ^ m₁ * L ^ K)) ^ 2 *
        (|ν₁ - ν₀| * ‖bgFieldC G a₁ ν₁ (bgC0 d L N) D (x, i) - D.h x i‖) ≤ 2 * ε * mν := by
      refine le_trans ?_ h2
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnorm (abs_nonneg _))
        (by positivity)
    refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [h1, h3]
  have hδ0 : 0 ≤ bgK1 d L N * (xiC1 d * ε) := by positivity
  have hm2 : 0 ≤ 2 * ε * (m + mν) := by positivity
  have := (H a₀ a₁ ν₀ ν₁ (2 * ε * (m + mν)) (bgK1 d L N * (xiC1 d * ε)) D
    (φ0 := bgFieldC G a₀ ν₀ (bgC0 d L N) D) (φ1 := bgFieldC G a₁ ν₁ (bgC0 d L N) D)
    hs0.1 hs1.1 hb0 hb1 H0.green hOp hδ0 hsmall (by linarith) hm2 hSB hS hphi).2
  exact ⟨this.val, this.fwd, this.bwd⟩

end Balaban.LargeField.ActionConv
