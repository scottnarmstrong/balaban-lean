/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (D1), real data: `Ξ_k(𝔹; σ, ε) ⊆ Ψ̃(𝔹; C₄ η)`

* `Balaban.SmallField.xi_inPsiTilde`: the real data of `Ξ_k(𝔹; σ, ε)` lie in the data domain
  `Ψ̃(𝔹; δ)` with `δ = C₄(d) · η`, `η = (2d+1) σ ε`, `C₄(d) = 4d + 8`, if `(4d+6) η ≤ 1`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν σ ε : ℝ} {D : BgData G N}
  {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}

/-- **The collar sites** of a datum of `Ξ`: the field is within `σ ε` of a unit vector, and within
`2 σ ε / √ν` of `h₀`. -/
theorem collar_estimates (H : BgHyp d L k ϱ a ν) (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1)
    (hX : XiAt G a ν k σ ε D Ψ₀ h₀) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ collar G) :
    |rn (Ψ₀ x) - 1| ≤ σ * ε ∧ Real.sqrt ν * rn (fun i => Ψ₀ x i - h₀ i) ≤ 2 * (σ * ε) := by
  obtain ⟨hR, hDom, hb⟩ := hX
  obtain ⟨hφre, hunit⟩ := xi_unit H ⟨hR, hDom, hb⟩
  have hs := xi_smooth hσ hε hσ1 hb
  have hA : 0 ≤ σ * ε := (mul_pos hσ hε).le
  obtain ⟨hxn, y, hy, hadj⟩ := (mem_collar G).1 hx
  have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inr hx)
  have hxe : barVec G D.Ψ (bgField G a ν D) x = D.Ψ x := by
    funext i; simp [barVec, barField, hxn]
  have hv : vn (D.Ψ x) = rn (Ψ₀ x) := by
    have e : D.Ψ x = fun i => ((Ψ₀ x i : ℝ) : ℂ) := by funext i; exact hR.1 x hxd i
    rw [e, vn_ofReal]
  have h1 : vn (barVec G D.Ψ (bgField G a ν D) x - barVec G D.Ψ (bgField G a ν D) y) ≤ σ * ε := by
    have := hs.adj_grad hy hadj
    exact this.trans (div_le_self hA (G.spacing_ge_one y))
  have hy1 : vn (barVec G D.Ψ (bgField G a ν D) y) = 1 :=
    barVec_vn_eq_one hφre hunit D.Ψ hy
  refine ⟨?_, ?_⟩
  · have t1 := vn_triangle (barVec G D.Ψ (bgField G a ν D) x)
      (barVec G D.Ψ (bgField G a ν D) y) 0
    have t2 := vn_triangle (barVec G D.Ψ (bgField G a ν D) y)
      (barVec G D.Ψ (bgField G a ν D) x) 0
    have e1 : ∀ w : Fin N → ℂ, w - 0 = w := fun w => sub_zero w
    rw [e1, e1] at t1
    rw [e1, e1] at t2
    rw [vn_sub_comm (barVec G D.Ψ (bgField G a ν D) y)] at t2
    rw [hxe] at h1 t1 t2
    rw [← hv, abs_le]
    constructor <;> linarith
  · have hmass := (hb.mass ⟨y, hy⟩).le
    have hν := H.mass
    have hs1 : Real.sqrt ν * G.spacing x ≤ 1 := sqrt_mul_spacing_le_one hν H.massLe G x
    have hsq : Real.sqrt ν ≤ 1 := by
      have := G.spacing_ge_one x
      have h0 := Real.sqrt_nonneg ν
      nlinarith
    have h2 : rn (fun i => Ψ₀ x i - h₀ i) = vn (D.Ψ x - fun i => (h₀ i : ℂ)) := by
      have e : D.Ψ x - (fun i => (h₀ i : ℂ)) = (fun i => (Ψ₀ x i : ℂ)) - fun i => (h₀ i : ℂ) := by
        funext i; simp [hR.1 x hxd i]
      rw [e, vn_cast_sub]
    have hyφ : (fun i => bgField G a ν D (⟨y, hy⟩, i)) = barVec G D.Ψ (bgField G a ν D) y := by
      funext i; simp [barVec, barField, hy]
    have t := vn_triangle (D.Ψ x) (barVec G D.Ψ (bgField G a ν D) y) (fun i => (h₀ i : ℂ))
    have t' : vn (barVec G D.Ψ (bgField G a ν D) y - fun i => (h₀ i : ℂ)) =
        vn (fun i => bgField G a ν D (⟨y, hy⟩, i) - (h₀ i : ℂ)) := by
      rw [← hyφ]; rfl
    rw [t'] at t
    rw [h2]
    have hy' : Real.sqrt ν * vn (fun i => bgField G a ν D (⟨y, hy⟩, i) - (h₀ i : ℂ)) ≤ σ * ε := by
      refine le_trans ?_ hmass
      have := G.spacing_ge_one y
      nlinarith [mul_nonneg (Real.sqrt_nonneg ν) (vn_nonneg
        (fun i => bgField G a ν D (⟨y, hy⟩, i) - (h₀ i : ℂ)))]
    have h3 : Real.sqrt ν * vn (barVec G D.Ψ (bgField G a ν D) x - barVec G D.Ψ (bgField G a ν D) y)
        ≤ σ * ε := by
      calc _ ≤ 1 * (σ * ε) := mul_le_mul hsq h1 (vn_nonneg _) zero_le_one
        _ = _ := by ring
    rw [hxe] at h3
    calc Real.sqrt ν * vn (D.Ψ x - fun i => (h₀ i : ℂ))
        ≤ Real.sqrt ν * (vn (D.Ψ x - barVec G D.Ψ (bgField G a ν D) y) +
          vn (fun i => bgField G a ν D (⟨y, hy⟩, i) - (h₀ i : ℂ))) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg ν)
      _ = Real.sqrt ν * vn (D.Ψ x - barVec G D.Ψ (bgField G a ν D) y) +
          Real.sqrt ν * vn (fun i => bgField G a ν D (⟨y, hy⟩, i) - (h₀ i : ℂ)) := by ring
      _ ≤ 2 * (σ * ε) := by linarith

/-- The hypotheses `CompHyp` of the identity composition `𝔹 ≺ 𝔹` for a datum of `Ξ`. -/
theorem xi_compHyp (H : BgHyp d L k ϱ a ν) (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1) {n : ℕ}
    (hX : XiAt G a ν n σ ε D Ψ₀ h₀) :
    CompHyp G G a 1 (xiEta d σ ε) D.Ψ (bgField G a ν D) where
  prec := precedes_refl G
  θ_pos := one_pos
  η_nn := (xiEta_pos hσ hε).le
  gap := scaleGap_one (precedes_refl G)
  ratio := fun x hx => by
    have := weights_ne H _ (G.layerIndex_spec hx).1 (G.layerIndex_spec hx).2.1
    rw [div_self this]
    exact ⟨zero_le_one, le_rfl⟩
  layerConst := D.Ψ_layerConst
  bounds := xi_fieldBounds H hσ hε hσ1 hX

/-- The (R2)-type bound at a site of `Ω₁`: `| |Ψ|² - 1 | ≤ (2d+3) η`. -/
theorem xi_r2_site (H : BgHyp d L k ϱ a ν) (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1)
    (hsmall : (4 * d + 6) * xiEta d σ ε ≤ 1) (hX : XiAt G a ν k σ ε D Ψ₀ h₀)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    |rn (Ψ₀ x) ^ 2 - 1| ≤ (2 * d + 3) * xiEta d σ ε := by
  obtain ⟨hφre, -⟩ := xi_unit H hX
  have hηpos : 0 < xiEta d σ ε := xiEta_pos hσ hε
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have Hc := xi_compHyp H hσ hε hσ1 hX
  have ha := weights_ne H
  have hΨreal : ∀ x ∈ dataSites G, ∀ i, (D.Ψ x i).im = 0 := fun x hx i => by
    rw [hX.1.1 x hx i]; simp
  have h1 := Hc.re_r2 hφre hΨreal hx
  have e : (fun i => (compVec G G a (bgField G a ν D) D.Ψ x i).re) = Ψ₀ x := by
    funext i
    rw [compVec_self ha, hX.1.1 x ((mem_dataSites G).2 (Or.inl hx)) i]; simp
  rw [e] at h1
  refine h1.trans ?_
  nlinarith [mul_nonneg hd0 hηpos.le]

/-- **(D1), real data** (P1 Lemma 3.1 at `λ = ∞`; see the module docstring of `XiReal` for the
constant): the real data of `Ξ_k(𝔹; σ, ε)` lie in `Ψ̃(𝔹; C₄ η)`, `η = (2d+1) σ ε`,
`C₄ = 4d + 8`, provided `(4d+6) η ≤ 1` and `σ ≤ 1`. -/
theorem xi_inPsiTilde (H : BgHyp d L k ϱ a ν) (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1)
    (hsmall : (4 * d + 6) * xiEta d σ ε ≤ 1) (hX : XiAt G a ν k σ ε D Ψ₀ h₀) :
    InPsiTilde G ν (compC4 d * xiEta d σ ε) Ψ₀ h₀ := by
  have hX' := hX
  obtain ⟨hR, hDom, hb⟩ := hX
  obtain ⟨hφre, hunit⟩ := xi_unit H hX'
  set η := xiEta d σ ε with hηdef
  have hηpos : 0 < η := xiEta_pos hσ hε
  have hση : σ * ε ≤ η := le_xiEta hσ hε
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hC4 : compC4 d * η = (4 * d + 8) * η := rfl
  have ha := weights_ne H
  have Hc := xi_compHyp H hσ hε hσ1 hX'
  have hΨreal : ∀ x ∈ dataSites G, ∀ i, (D.Ψ x i).im = 0 := fun x hx i => by
    rw [hR.1 x hx i]; simp
  have hre : ∀ x ∈ dataSites G, ∀ i,
      (compVec G G a (bgField G a ν D) D.Ψ x i).re = Ψ₀ x i := fun x hx i => by
    rw [compVec_self ha, hR.1 x hx i]; simp
  have hmass : ∀ z : G.Ω 1, Real.sqrt ν * G.spacing z *
      vn (fun i => bgField G a ν D (z, i) - (h₀ i : ℂ)) ≤ η := fun z =>
    ((hb.mass z).le).trans hση
  have hsm1 : (2 * d + 3) * η ≤ 1 / 2 := by nlinarith
  have hs2 : (2 * d * (1 * η)) ^ 2 + 2 * 1 ^ 2 * 1 * η + (1 ^ 2) ^ 2 * η ^ 2 ≤ (2 * d + 3) * η := by
    nlinarith [mul_nonneg hd0 hηpos.le]
  have hB : ∀ z z', z ∈ dataSites G → z' ∈ dataSites G → Adj z z' →
      vn (barVec G D.Ψ (bgField G a ν D) z - barVec G D.Ψ (bgField G a ν D) z') ≤ η := by
    intro z z' hz hz' hadj
    by_cases hz2 : z ∈ G.Ω 1
    · rw [vn_sub_comm]; exact Hc.bond_out hz2 hadj
    · by_cases hz2' : z' ∈ G.Ω 1
      · exact Hc.bond_out hz2' hadj.symm
      · have hc : z ∈ collar G := ((mem_dataSites G).1 hz).resolve_left hz2
        have hc' : z' ∈ collar G := ((mem_dataSites G).1 hz').resolve_left hz2'
        have h1 := hb.collarBond z hc z' hc' hadj
        have e : barVec G D.Ψ (bgField G a ν D) z - barVec G D.Ψ (bgField G a ν D) z' =
            D.Ψ z - D.Ψ z' := by
          funext i; simp [barVec, barField, hz2, hz2']
        rw [e]
        exact (le_of_lt h1).trans hση
  refine ⟨realizes_layerConst hR, ?_, ?_, ?_, ?_⟩
  · -- (R1)
    intro x x' hxx'
    have h1 := Hc.interface hxx' hB
    rw [compVec_self ha, compVec_self ha] at h1
    rw [← realizes_vn hR hxx'.1 hxx'.2.1]
    have : 2 * ((2 * (d : ℝ) + 1) * (1 * η)) + η < compC4 d * η := by
      rw [hC4]; nlinarith
    linarith
  · -- (R2)
    intro x hx
    rcases (mem_dataSites G).1 hx with hx1 | hx1
    · have h1 := Hc.re_r2 hφre hΨreal hx1
      have e : (fun i => (compVec G G a (bgField G a ν D) D.Ψ x i).re) = Ψ₀ x := by
        funext i; exact hre x hx i
      rw [e, rn_sq_sum] at h1
      refine (h1.trans hs2).trans_lt ?_
      rw [hC4]; nlinarith
    · obtain ⟨h1, -⟩ := collar_estimates H hσ hε hσ1 hX' hx1
      have hr := rn_nonneg (Ψ₀ x)
      have : |∑ i, Ψ₀ x i ^ 2 - 1| = |rn (Ψ₀ x) - 1| * (rn (Ψ₀ x) + 1) := by
        rw [← rn_sq_sum, show rn (Ψ₀ x) ^ 2 - 1 = (rn (Ψ₀ x) - 1) * (rn (Ψ₀ x) + 1) by ring,
          abs_mul, abs_of_pos (by linarith : 0 < rn (Ψ₀ x) + 1)]
      rw [this]
      have hu : rn (Ψ₀ x) + 1 ≤ 3 := by
        have := (abs_le.1 h1).2
        nlinarith [mul_pos hσ hε, mul_le_mul_of_nonneg_right hσ1 hε.le]
      calc |rn (Ψ₀ x) - 1| * (rn (Ψ₀ x) + 1) ≤ (σ * ε) * 3 :=
          mul_le_mul h1 hu (by positivity) (mul_pos hσ hε).le
        _ < compC4 d * η := by rw [hC4]; nlinarith
  · -- (R3)
    intro x hx
    have hfin : ∀ {E b : ℝ}, 0 ≤ b → b ≤ (2 * d + 3) * η → E ≤ 2 * η → 0 ≤ E →
        ((1 / 2) * (b + E) ^ 2 + (1 / 2) * (σ * ε) ^ 2) ≤ (compC4 d * η) ^ 2 := by
      intro E b hb0 hb1 hE1 hE0
      have h1 : (b + E) ^ 2 ≤ ((2 * d + 5) * η) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by nlinarith) 2
      have h2 : (σ * ε) ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (mul_pos hσ hε).le hση 2
      rw [hC4]
      nlinarith [sq_nonneg η, mul_nonneg hd0 hηpos.le, sq_nonneg (d * η)]
    have hhh := hnorm_layer H.mass hb x
    rcases (mem_dataSites G).1 hx with hx1 | hx1
    · have hb2 : (2 * d * (1 * η)) ^ 2 + 2 * 1 ^ 2 * 1 * η + (1 ^ 2) ^ 2 * η ^ 2 ≤ 1 / 2 :=
        hs2.trans hsm1
      have h1 := Hc.re_r3 hφre hΨreal H.mass H.massLe h₀ hmass hx1 hb2 hhh
      simp only [hre x hx] at h1
      exact h1.trans_le (hfin (E := 1 * η + 1 ^ 2 * η)
        (b := (2 * d * (1 * η)) ^ 2 + 2 * 1 ^ 2 * 1 * η + (1 ^ 2) ^ 2 * η ^ 2)
        (by positivity) hs2 (by linarith) (by positivity))
    · obtain ⟨h1, h2⟩ := collar_estimates H hσ hε hσ1 hX' hx1
      have hxn : x ∉ G.Ω 1 := ((mem_collar G).1 hx1).1
      have hl : G.layerIndex x = 0 := layerIndex_of_not_mem G hxn
      have hxc : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 = (Real.sqrt ν * G.spacing x) ^ 2 := by
        unfold GeneratingSet.spacing; rw [mul_pow, Real.sq_sqrt H.mass]
      have hs0 : 0 ≤ Real.sqrt ν * G.spacing x :=
        mul_nonneg (Real.sqrt_nonneg ν) ((G.spacing_ge_one x).trans' zero_le_one)
      have hsp : G.spacing x = 1 := by unfold GeneratingSet.spacing; rw [hl]; simp
      have hb2 : |rn (Ψ₀ x) ^ 2 - 1| ≤ 3 * η := by
        have hr0 := rn_nonneg (Ψ₀ x)
        have : |rn (Ψ₀ x) ^ 2 - 1| = |rn (Ψ₀ x) - 1| * (rn (Ψ₀ x) + 1) := by
          rw [show rn (Ψ₀ x) ^ 2 - 1 = (rn (Ψ₀ x) - 1) * (rn (Ψ₀ x) + 1) by ring,
            abs_mul, abs_of_pos (by linarith : 0 < rn (Ψ₀ x) + 1)]
        rw [this]
        have hu : rn (Ψ₀ x) + 1 ≤ 3 := by
          have := (abs_le.1 h1).2
          nlinarith [mul_pos hσ hε, mul_le_mul_of_nonneg_right hσ1 hε.le]
        calc _ ≤ (σ * ε) * 3 := mul_le_mul h1 hu (by linarith) (mul_pos hσ hε).le
          _ ≤ 3 * η := by linarith
      have hdist : Real.sqrt ν * G.spacing x * rn (fun i => Ψ₀ x i - h₀ i) ≤ 2 * η := by
        rw [hsp, mul_one]; linarith
      have hb3 : 3 * η ≤ 1 / 2 := by nlinarith
      have h3 := r3_core (Ψ := Ψ₀ x) (h0 := h₀) (b := 3 * η) (E := 2 * η) hs0
        (sqrt_mul_spacing_le_one H.mass H.massLe G x) hxc hb2 hb3 hdist hhh
      exact h3.trans_le (hfin (E := 2 * η) (b := 3 * η) (by positivity) (by nlinarith)
        le_rfl (by positivity))
  · -- (R4)
    refine hb.hnorm.trans_le ?_
    refine pow_le_pow_left₀ (mul_pos hσ hε).le ?_ 2
    rw [hC4]; nlinarith

end Balaban.SmallField
