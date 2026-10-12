/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiD1C
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (D1-j), real data: the level-`j` data domain `Ψ̃_{j|k}` and `Ξ_j ⊆ Ψ̃_{j|k}`

`notes/phase1/MASS-LEVEL.md` (P1 (3.13), (3.18)-(3.19)): for a level-`j` term, `j < k`, the norm
condition of the data domain uses the level-`j` mass `M_j = ν L^{2j}`, not `M_k = ν L^{2k}`.

* `Balaban.SmallField.InPsiTildeLevel`: `Ψ̃_{j|k}(𝔹; δ)`, the clauses of `InPsiTilde` with (R4)
  `ν L^{2j} |h·h - 1| < δ²`;
* `Balaban.SmallField.xi_inPsiTildeLevel`: **(D1-j) real**, `Ξ_j(𝔹; σ, ε) ⊆ Ψ̃_{j|k}(𝔹; C₄ η)` for
  `Ω_{j+1} = ∅`, `j ≤ k`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Defs

variable (G : GeneratingSet d L N₀ k ϱ)

/-- **The level-`j` real data domain `Ψ̃_{j|k}(𝔹; δ)`** (P1 (3.18); MASS-LEVEL.md §3): the clauses
(R1)-(R3) of `InPsiTilde` and (R4) with the level-`j` mass, `ν L^{2j} |h·h - 1| < δ²`.  For
`j = k` it is `InPsiTilde`. -/
structure InPsiTildeLevel (ν : ℝ) (j : ℕ) (δ : ℝ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ)
    (h : Fin N → ℝ) : Prop where
  layerConst : IsLayerConstant G Ψ
  r1 : ∀ x x', IsInterfacePair G x x' → rn (fun i => Ψ x i - Ψ x' i) < δ
  r2 : ∀ x ∈ dataSites G, |∑ i, Ψ x i ^ 2 - 1| < δ
  r3 : ∀ x ∈ dataSites G, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
    |1 - (∑ i, Ψ x i * h i) / rn (Ψ x)| < δ ^ 2
  r4 : ν * ((L : ℝ) ^ j) ^ 2 * |∑ i, h i ^ 2 - 1| < δ ^ 2

/-- **The level-`j` complex data domain `Ψ̃^c_{j|k}(𝔹; δ, ε)`**: the clauses of `InPsiTildeC` over
the level-`j` real domain. -/
structure InPsiTildeCLevel (ν : ℝ) (j : ℕ) (δ ε : ℝ)
    (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h : Fin N → ℝ)
    (Ψ' h' : Torus d (N₀ * L ^ k) → Fin N → ℂ) : Prop extends InPsiTildeLevel G ν j δ Ψ h where
  eps_pos : 0 < ε
  layerConst' : IsLayerConstant G Ψ'
  hLayerConst' : IsLayerConstant G h'
  c1 : ∀ x x', IsInterfacePair G x x' → vn (Ψ' x - Ψ' x') < δ
  c2a : ∀ x ∈ dataSites G, vn (Ψ' x) < ε + δ
  c2b : ∀ x ∈ dataSites G,
    ‖∑ i, ((Ψ x i : ℂ) + Ψ' x i) * ((Ψ x i : ℂ) + Ψ' x i) - ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ)‖ < δ
  c3a : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h' x) < δ ^ 2 / ε
  c3b : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
    ‖∑ i, ((Ψ x i / rn (Ψ x) : ℝ) : ℂ) * h' x i‖ < δ ^ 2

variable {G}

/-- For `j = k` the level-`j` real domain is `InPsiTilde`. -/
theorem inPsiTildeLevel_top_iff {ν δ : ℝ} {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h : Fin N → ℝ} :
    InPsiTildeLevel G ν k δ Ψ h ↔ InPsiTilde G ν δ Ψ h :=
  ⟨fun H => ⟨H.layerConst, H.r1, H.r2, H.r3, H.r4⟩,
    fun H => ⟨H.layerConst, H.r1, H.r2, H.r3, H.r4⟩⟩

theorem InPsiTildeLevel.mono {ν δ δ' : ℝ} {j : ℕ} {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ}
    {h : Fin N → ℝ} (H : InPsiTildeLevel G ν j δ Ψ h) (hδ : 0 ≤ δ) (hle : δ ≤ δ') :
    InPsiTildeLevel G ν j δ' Ψ h where
  layerConst := H.layerConst
  r1 x x' hxx' := (H.r1 x x' hxx').trans_le hle
  r2 x hx := (H.r2 x hx).trans_le hle
  r3 x hx := (H.r3 x hx).trans_le (pow_le_pow_left₀ hδ hle 2)
  r4 := H.r4.trans_le (pow_le_pow_left₀ hδ hle 2)

/-- Layer indices are at most `j` when `Ω_{j+1} = ∅`. -/
theorem layerIndex_le_of_Ω_empty (G : GeneratingSet d L N₀ k ϱ) {j : ℕ}
    (hΩ : G.Ω (j + 1) = ∅) (x : Torus d (N₀ * L ^ k)) : G.layerIndex x ≤ j := by
  by_cases hx : x ∈ G.Ω 1
  · obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
    by_contra hlt
    have := G.Ω_antitone (by omega : 1 ≤ j + 1) (by omega : j + 1 ≤ G.layerIndex x) (by omega)
      (G.mem_layer.1 hxl).1
    simp [hΩ] at this
  · rw [layerIndex_of_not_mem G hx]; exact Nat.zero_le _

end Defs

section D1j

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν σ ε : ℝ} {D : BgData G N}
  {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ} {φ : G.Ω 1 × Fin N → ℂ}
  {α : G.Ω 1 → ℂ}

/-- The level-`j` mass bound at a site of layer `m ≤ j`:
`ν L^{2m} | |h₀|² - 1 | < (σ ε)²`. -/
theorem hnorm_layer_level {j : ℕ} (hΩ : G.Ω (j + 1) = ∅) (hν : 0 ≤ ν)
    (hb : XiBounds G ν j σ ε D h₀ φ α) (x : Torus d (N₀ * L ^ k)) :
    ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < (σ * ε) ^ 2 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  refine lt_of_le_of_lt ?_ hb.hnorm
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
    (pow_le_pow_right₀ hL1 (layerIndex_le_of_Ω_empty G hΩ x)) 2) hν

/-- **The collar sites** of a datum of `Ξ`: the field is within `σ ε` of a unit vector, and within
`2 σ ε / √ν` of `h₀`. -/
theorem collar_estimates_level (H : BgHyp d L k ϱ a ν) {j : ℕ} (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1)
    (hX : XiAt G a ν j σ ε D Ψ₀ h₀) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ collar G) :
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

theorem xi_r2_site_level (H : BgHyp d L k ϱ a ν) {j : ℕ} (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1)
    (hsmall : (4 * d + 6) * xiEta d σ ε ≤ 1) (hX : XiAt G a ν j σ ε D Ψ₀ h₀)
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
theorem xi_inPsiTildeLevel (H : BgHyp d L k ϱ a ν) {j : ℕ} (hΩ : G.Ω (j + 1) = ∅) (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1)
    (hsmall : (4 * d + 6) * xiEta d σ ε ≤ 1) (hX : XiAt G a ν j σ ε D Ψ₀ h₀) :
    InPsiTildeLevel G ν j (compC4 d * xiEta d σ ε) Ψ₀ h₀ := by
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
    · obtain ⟨h1, -⟩ := collar_estimates_level H hσ hε hσ1 hX' hx1
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
    have hhh := hnorm_layer_level hΩ H.mass hb x
    rcases (mem_dataSites G).1 hx with hx1 | hx1
    · have hb2 : (2 * d * (1 * η)) ^ 2 + 2 * 1 ^ 2 * 1 * η + (1 ^ 2) ^ 2 * η ^ 2 ≤ 1 / 2 :=
        hs2.trans hsm1
      have h1 := Hc.re_r3 hφre hΨreal H.mass H.massLe h₀ hmass hx1 hb2 hhh
      simp only [hre x hx] at h1
      exact h1.trans_le (hfin (E := 1 * η + 1 ^ 2 * η)
        (b := (2 * d * (1 * η)) ^ 2 + 2 * 1 ^ 2 * 1 * η + (1 ^ 2) ^ 2 * η ^ 2)
        (by positivity) hs2 (by linarith) (by positivity))
    · obtain ⟨h1, h2⟩ := collar_estimates_level H hσ hε hσ1 hX' hx1
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


end D1j

end Balaban.SmallField
