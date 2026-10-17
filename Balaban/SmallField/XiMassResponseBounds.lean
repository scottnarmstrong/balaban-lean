/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiMassResponse
public import Balaban.SmallField.XiPerturb
public import Balaban.Background.CompositionDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The mass response of the class domain, the inequalities (decision D2(b), Step 2, part 2)

If the background field moves by an increment `δφ` with `‖δφ‖_* ≤ V` and the multiplier by `δα`
with `|δα|₂ ≤ V`, and the mass moves from `ν` to `μ ≤ (1 + s) ν` (`s ≥ 0`), then the inequalities of
`XiBounds` and `XiCBounds` hold at the mass `μ` with the radius `e'` as soon as
`(1 + s) e + 2 N V ≤ e'` (and the corresponding conditions for the quadratic terms).

* `xiBounds_massResponse`: `XiBounds` at `(μ, φ + δφ, α + δα)` from `XiBounds` at `(ν, φ, α)`;
* `xiCBounds_massResponse`: `XiCBounds` at `μ` for the increments `(δφ_r, δα_r)`, `(δφ_c, δα_c)`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Incr

variable {G : GeneratingSet d L N₀ k ϱ} {w : G.Ω 1 × Fin N → ℂ} {W : ℝ}

theorem incr_grad (hW : 0 ≤ W) (hs : SupBounds G w W) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) (m : Fin d) :
    vn (fun i => svec G w (x + Pi.single m 1) i - svec G w x i) ≤ N * (W / G.spacing x) ∧
      vn (fun i => svec G w (x - Pi.single m 1) i - svec G w x i) ≤ N * (W / G.spacing x) := by
  have hl : 0 < G.spacing x := spacing_pos G
  have hp : 0 ≤ W / G.spacing x := div_nonneg hW hl.le
  refine ⟨vn_le_card_mul hp fun i => (le_div_iff₀ hl).2 ?_,
    vn_le_card_mul hp fun i => (le_div_iff₀ hl).2 ?_⟩
  · rw [mul_comm]; exact hs.fwd x hx m i
  · rw [mul_comm]; exact hs.bwd x hx m i

theorem incr_lap (hW : 0 ≤ W) (hs : SupBounds G w W) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) :
    vn (fun i => ∑ m : Fin d, (svec G w (x + Pi.single m 1) i + svec G w (x - Pi.single m 1) i -
      2 * svec G w x i)) ≤ N * (W / G.spacing x ^ 2) := by
  have hl : 0 < G.spacing x ^ 2 := by have := spacing_pos G (x := x); positivity
  refine vn_le_card_mul (div_nonneg hW hl.le) fun i => (le_div_iff₀ hl).2 ?_
  have e : (∑ m : Fin d, (svec G w (x + Pi.single m 1) i + svec G w (x - Pi.single m 1) i -
      2 * svec G w x i)) = -∑ m : Fin d, (2 * svec G w x i - svec G w (x + Pi.single m 1) i -
        svec G w (x - Pi.single m 1) i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [e, norm_neg, mul_comm]
  exact hs.lap x hx i

theorem incr_val (hW : 0 ≤ W) (hs : SupBounds G w W) (y : Torus d (N₀ * L ^ k)) :
    vn (fun i => svec G w y i) ≤ N * W :=
  vn_le_card_mul hW fun i => hs.val y i

theorem incr_block (hW : 0 ≤ W) (hs : SupBounds G w W) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) : vn (fun i => blockAvg G w x i) ≤ N * W := by
  have hn := (G.layerIndex_spec hx).2.1
  exact vn_blockMean_le (G := G) hn (fun y i => svec G w y i) x (c := N * W)
    (fun y _ => incr_val hW hs y)

end Incr

section Real

variable {G : GeneratingSet d L N₀ k ϱ}

/-- **The inequalities of `Ξ_n` at the mass `μ`** from those at the mass `ν`, for the moved
background `(φ + δφ, α + δα)`. -/
theorem xiBounds_massResponse {ν μ s e e' V : ℝ} {n : ℕ} {Dr : BgData G N} {h₀ : Fin N → ℝ}
    {φ δφ : G.Ω 1 × Fin N → ℂ} {α δα : G.Ω 1 → ℂ} (hs : 0 ≤ s) (he : 0 < e) (hV : 0 ≤ V)
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ (1 + s) * ν) (hμ1 : μ * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (h1 : (1 + s) * e + N * V ≤ e') (h2 : e + V ≤ e')
    (hb : XiBounds G ν n 1 e Dr h₀ φ α) (hsup : SupBounds G δφ V) (hα : Small G δα V) :
    XiBounds G μ n 1 e' Dr h₀ (φ + δφ) (α + δα) := by
  have hNV : 0 ≤ (N : ℝ) * V := by positivity
  have hse : 0 ≤ s * e := mul_nonneg hs he.le
  have he1 : e + N * V ≤ e' := by linarith
  have hee' : e ≤ e' := by linarith
  have hee'' : (1 + s) * e ≤ e' := by linarith
  have hp : ∀ x : Torus d (N₀ * L ^ k), 0 < G.spacing x := fun x => spacing_pos G
  refine ⟨fun x hx m => ?_, fun x hx => ?_, fun x => ?_, fun x hx => ?_,
    fun z hz z' hz' hadj => ?_, fun z => ?_, ?_⟩
  · obtain ⟨o1, o2⟩ := hb.grad x hx m
    obtain ⟨g1, g2⟩ := incr_grad hV hsup hx m
    have key : 1 * e / G.spacing x + N * (V / G.spacing x) ≤ 1 * e' / G.spacing x := by
      rw [show (N : ℝ) * (V / G.spacing x) = (N * V) / G.spacing x by ring, ← add_div]
      exact div_le_div_of_nonneg_right (by linarith) (hp x).le
    simp only [barField_add]
    exact ⟨lt_of_le_of_lt (vn_add_diff _ _ _ _) (lt_of_lt_of_le (add_lt_add_of_lt_of_le o1 g1) key),
      lt_of_le_of_lt (vn_add_diff _ _ _ _) (lt_of_lt_of_le (add_lt_add_of_lt_of_le o2 g2) key)⟩
  · have o := hb.lap x hx
    have g := incr_lap hV hsup hx
    have hs2 : 0 < G.spacing x ^ 2 := by have := hp x; positivity
    have key : 1 ^ 2 * e / G.spacing x ^ 2 + N * (V / G.spacing x ^ 2) ≤
        1 ^ 2 * e' / G.spacing x ^ 2 := by
      rw [show (N : ℝ) * (V / G.spacing x ^ 2) = (N * V) / G.spacing x ^ 2 by ring, ← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hs2.le
    simp only [barField_add]
    exact lt_of_lt_of_le (lap_add (A := fun y i => barField G Dr.Ψ φ y i) (E := svec G δφ) x o g)
      key
  · have o := hb.mult x
    have hsp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
      have := hp (x : Torus d (N₀ * L ^ k)); positivity
    simp only [Pi.add_apply]
    calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x + δα x‖
        ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * (‖α x‖ + ‖δα x‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hsp
      _ = G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x‖ +
          G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖δα x‖ := by ring
      _ < 1 ^ 2 * e' := by
          have := hα x
          nlinarith
  · have o := hb.close x hx
    have t := incr_block hV hsup hx
    have e1 : (fun i => Dr.Ψ x i - blockAvg G (φ + δφ) x i) =
        (fun i => Dr.Ψ x i - blockAvg G φ x i) + fun i => -blockAvg G δφ x i := by
      funext i; simp only [blockAvg_add, Pi.add_apply]; ring
    rw [e1]
    have t1 := vn_add (fun i => Dr.Ψ x i - blockAvg G φ x i) (fun i => -blockAvg G δφ x i)
    have t2 := vn_neg (fun i => blockAvg G δφ x i)
    have : 1 ^ 2 * e ≤ 1 ^ 2 * e' - N * V := by linarith
    linarith
  · exact (hb.collarBond z hz z' hz' hadj).trans_le (by linarith)
  · have o := hb.mass z
    have hz1 : Real.sqrt μ * G.spacing (z : Torus d (N₀ * L ^ k)) ≤ 1 :=
      sqrt_mul_spacing_le_one hμ0 hμ1 G _
    have hsq : Real.sqrt μ ≤ (1 + s) * Real.sqrt ν := by
      have h1s : Real.sqrt μ ≤ Real.sqrt ((1 + s) * ν) := Real.sqrt_le_sqrt hμ
      rw [Real.sqrt_mul (by linarith)] at h1s
      refine h1s.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg ν))
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have e1 : (fun i => (φ + δφ) (z, i) - (h₀ i : ℂ)) =
        (fun i => φ (z, i) - (h₀ i : ℂ)) + fun i => δφ (z, i) := by
      funext i; simp only [Pi.add_apply]; ring
    rw [e1]
    have t1 := vn_add (fun i => φ (z, i) - (h₀ i : ℂ)) (fun i => δφ (z, i))
    have t2 : vn (fun i => δφ (z, i)) ≤ N * V := by
      have := incr_val hV hsup (z : Torus d (N₀ * L ^ k))
      simpa [svec_of_mem G δφ z] using this
    have hℓ := (hp (z : Torus d (N₀ * L ^ k)))
    have hA : 0 ≤ Real.sqrt μ * G.spacing (z : Torus d (N₀ * L ^ k)) := by positivity
    have hB : Real.sqrt μ * G.spacing (z : Torus d (N₀ * L ^ k)) ≤
        (1 + s) * (Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ k))) := by
      have := mul_le_mul_of_nonneg_right hsq hℓ.le
      linarith
    calc Real.sqrt μ * G.spacing (z : Torus d (N₀ * L ^ k)) *
          vn ((fun i => φ (z, i) - (h₀ i : ℂ)) + fun i => δφ (z, i))
        ≤ Real.sqrt μ * G.spacing (z : Torus d (N₀ * L ^ k)) *
          (vn (fun i => φ (z, i) - (h₀ i : ℂ)) + vn (fun i => δφ (z, i))) :=
          mul_le_mul_of_nonneg_left t1 hA
      _ = Real.sqrt μ * G.spacing (z : Torus d (N₀ * L ^ k)) *
            vn (fun i => φ (z, i) - (h₀ i : ℂ)) +
          Real.sqrt μ * G.spacing (z : Torus d (N₀ * L ^ k)) * vn (fun i => δφ (z, i)) := by ring
      _ < 1 * e' := by
          have a1 : Real.sqrt μ * G.spacing (z : Torus d (N₀ * L ^ k)) *
              vn (fun i => φ (z, i) - (h₀ i : ℂ)) ≤
              (1 + s) * (Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ k)) *
                vn (fun i => φ (z, i) - (h₀ i : ℂ))) := by
            have := mul_le_mul_of_nonneg_right hB (vn_nonneg (fun i => φ (z, i) - (h₀ i : ℂ)))
            linarith
          have a2 : (1 + s) * (Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ k)) *
              vn (fun i => φ (z, i) - (h₀ i : ℂ))) < (1 + s) * (1 * e) :=
            mul_lt_mul_of_pos_left o (by linarith)
          have a3 : Real.sqrt μ * G.spacing (z : Torus d (N₀ * L ^ k)) *
              vn (fun i => δφ (z, i)) ≤ N * V := by
            calc _ ≤ 1 * vn (fun i => δφ (z, i)) :=
                  mul_le_mul_of_nonneg_right hz1 (vn_nonneg _)
              _ ≤ N * V := by linarith
          nlinarith
  · have := massScale_aux (A := ((L : ℝ) ^ n) ^ 2) (B := |∑ i, h₀ i ^ 2 - 1|) hs hμ
      (by positivity) (abs_nonneg _) hb.hnorm
    exact this.trans_le (pow_le_pow_left₀ (by positivity) (by linarith) 2)

end Real

section Complex

variable {G : GeneratingSet d L N₀ k ϱ}

theorem bar_diff (Ψc Ψr : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φc φr δc δr : G.Ω 1 × Fin N → ℂ)
    (y : Torus d (N₀ * L ^ k)) (i : Fin N) :
    barField G Ψc (φc + δc) y i - barField G Ψr (φr + δr) y i =
      (barField G Ψc φc y i - barField G Ψr φr y i) + svec G (δc - δr) y i := by
  rw [barField_add, barField_add, svec_sub]; ring

/-- **The inequalities of `Ξ^c_n` at the mass `μ`** from those at the mass `ν`, for the moved
backgrounds `(φ_r + δφ_r, α_r + δα_r)` and `(φ_c + δφ_c, α_c + δα_c)`. -/
theorem xiCBounds_massResponse {ν μ s e e' V : ℝ} {Dr Dc : BgData G N}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φr φc δr δc : G.Ω 1 × Fin N → ℂ}
    {αr αc δαr δαc : G.Ω 1 → ℂ} (hs : 0 ≤ s) (he : 0 < e) (hV : 0 ≤ V)
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ (1 + s) * ν)
    (h1 : e + N * (V + V) ≤ e') (h2 : e + (V + V) ≤ e') (h3 : (1 + s) * e ≤ e')
    (h4 : (1 + s) * e ^ 2 + (1 + s) * N * V * e ≤ (1 * e') ^ 2)
    (hb : XiCBounds G ν 1 e Dr Dc Ψ'' h'' φr φc αr αc) (hsr : SupBounds G δr V)
    (hsc : SupBounds G δc V) (hαr : Small G δαr V) (hαc : Small G δαc V) :
    XiCBounds G μ 1 e' Dr Dc Ψ'' h'' (φr + δr) (φc + δc) (αr + δαr) (αc + δαc) := by
  have hW : 0 ≤ V + V := by linarith
  have hsw := hsc.sub hsr
  have hee' : e ≤ e' := by
    have : 0 ≤ (N : ℝ) * (V + V) := by positivity
    linarith
  have hp : ∀ x : Torus d (N₀ * L ^ k), 0 < G.spacing x := fun x => spacing_pos G
  refine ⟨fun x hx m => ?_, fun x hx => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_,
    fun z hz z' hz' hadj => ?_, fun x hx => ?_, fun x => ?_⟩
  · obtain ⟨o1, o2⟩ := hb.grad x hx m
    obtain ⟨g1, g2⟩ := incr_grad hW hsw hx m
    have key : 1 * e / G.spacing x + N * ((V + V) / G.spacing x) ≤ 1 * e' / G.spacing x := by
      rw [show (N : ℝ) * ((V + V) / G.spacing x) = (N * (V + V)) / G.spacing x by ring,
        ← add_div]
      exact div_le_div_of_nonneg_right (by linarith) (hp x).le
    simp only [bar_diff]
    exact ⟨lt_of_le_of_lt (vn_add_diff _ _ _ _) (lt_of_lt_of_le (add_lt_add_of_lt_of_le o1 g1) key),
      lt_of_le_of_lt (vn_add_diff _ _ _ _) (lt_of_lt_of_le (add_lt_add_of_lt_of_le o2 g2) key)⟩
  · have o := hb.lap x hx
    have g := incr_lap hW hsw hx
    have hs2 : 0 < G.spacing x ^ 2 := by have := hp x; positivity
    have key : 1 ^ 2 * e / G.spacing x ^ 2 + N * ((V + V) / G.spacing x ^ 2) ≤
        1 ^ 2 * e' / G.spacing x ^ 2 := by
      rw [show (N : ℝ) * ((V + V) / G.spacing x ^ 2) = (N * (V + V)) / G.spacing x ^ 2 by ring,
        ← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hs2.le
    simp only [bar_diff]
    exact lt_of_lt_of_le (lap_add (A := fun y i => barField G Dc.Ψ φc y i -
      barField G Dr.Ψ φr y i) (E := svec G (δc - δr)) x o g) key
  · have o := hb.mult x
    have hsp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
      have := hp (x : Torus d (N₀ * L ^ k)); positivity
    have e1 : (αc + δαc) x - (αr + δαr) x = (αc x - αr x) + (δαc x - δαr x) := by
      simp only [Pi.add_apply]; ring
    rw [e1]
    have t1 := norm_add_le (αc x - αr x) (δαc x - δαr x)
    have t2 := norm_sub_le (δαc x) (δαr x)
    have a1 := hαc x
    have a2 := hαr x
    calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖(αc x - αr x) + (δαc x - δαr x)‖
        ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
          (‖αc x - αr x‖ + (‖δαc x‖ + ‖δαr x‖)) :=
          mul_le_mul_of_nonneg_left (t1.trans (add_le_add_right t2 _)) hsp
      _ = G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖αc x - αr x‖ +
          (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖δαc x‖ +
            G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖δαr x‖) := by ring
      _ < 1 ^ 2 * e' := by nlinarith
  · have o := hb.val x
    have e1 : (fun i => (φc + δc) (x, i) - (φr + δr) (x, i)) =
        (fun i => φc (x, i) - φr (x, i)) + fun i => svec G (δc - δr) x i := by
      funext i; simp only [Pi.add_apply, svec_of_mem G]; simp only [Pi.sub_apply]; ring
    rw [e1]
    have t1 := vn_add (fun i => φc (x, i) - φr (x, i)) (fun i => svec G (δc - δr) x i)
    have t2 := incr_val hW hsw (x : Torus d (N₀ * L ^ k))
    linarith
  · have o := hb.close x hx
    have t := incr_block hW hsw hx
    have e1 : (fun i => Ψ'' x i - blockAvg G ((φc + δc) - (φr + δr)) x i) =
        (fun i => Ψ'' x i - blockAvg G (φc - φr) x i) + fun i => -blockAvg G (δc - δr) x i := by
      funext i
      have : (φc + δc) - (φr + δr) = (φc - φr) + (δc - δr) := by abel
      rw [this]; simp only [blockAvg_add, Pi.add_apply]; ring
    rw [e1]
    have t1 := vn_add (fun i => Ψ'' x i - blockAvg G (φc - φr) x i)
      (fun i => -blockAvg G (δc - δr) x i)
    have t2 := vn_neg (fun i => blockAvg G (δc - δr) x i)
    have : 1 ^ 2 * e ≤ 1 ^ 2 * e' - N * (V + V) := by linarith
    linarith
  · exact (hb.collarBond z hz z' hz' hadj).trans_le (by linarith)
  · have o := hb.hAbs x hx
    have e1 : (1 * e) ^ 2 / e = e := by field_simp
    have he' : 0 < e' := he.trans_le hee'
    have e2 : (1 * e') ^ 2 / e' = e' := by field_simp
    rw [e1] at o
    rw [e2]
    have hA : 0 ≤ ((L : ℝ) ^ G.layerIndex x) ^ 2 := by positivity
    have h5 : μ * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h'' x) ≤
        (1 + s) * (ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h'' x)) := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ hA) (vn_nonneg (h'' x))
      linarith
    have h6 : (1 + s) * (ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h'' x)) < (1 + s) * e :=
      mul_lt_mul_of_pos_left o (by linarith)
    linarith
  · have o := hb.hDot x
    have o2 := hb.hAbs x x.2
    have e1 : (1 * e) ^ 2 / e = e := by field_simp
    rw [e1] at o2
    set B : ℝ := ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 with hB
    have hB0 : 0 ≤ B := by positivity
    have esum : (∑ i, (φr + δr) (x, i) * h'' x i) =
        (∑ i, φr (x, i) * h'' x i) + ∑ i, δr (x, i) * h'' x i := by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [esum]
    have t1 := norm_add_le (∑ i, φr (x, i) * h'' x i) (∑ i, δr (x, i) * h'' x i)
    have t2 : ‖∑ i, δr (x, i) * h'' x i‖ ≤ (N * V) * vn (h'' x) := by
      refine (norm_dot_le (fun i => δr (x, i)) (h'' x)).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (vn_nonneg _)
      have := incr_val hV hsr (x : Torus d (N₀ * L ^ k))
      simpa [svec_of_mem G δr x] using this
    have hNV : 0 ≤ (N : ℝ) * V := by positivity
    have h5 : μ * B * ‖∑ i, φr (x, i) * h'' x i‖ ≤
        (1 + s) * (ν * B * ‖∑ i, φr (x, i) * h'' x i‖) := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ hB0) (norm_nonneg
        (∑ i, φr (x, i) * h'' x i))
      linarith
    have h6 : (1 + s) * (ν * B * ‖∑ i, φr (x, i) * h'' x i‖) < (1 + s) * (1 * e) ^ 2 :=
      mul_lt_mul_of_pos_left o (by linarith)
    have h7 : μ * B * vn (h'' x) ≤ (1 + s) * (ν * B * vn (h'' x)) := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ hB0) (vn_nonneg (h'' x))
      linarith
    have h8 : μ * B * ‖∑ i, δr (x, i) * h'' x i‖ ≤ (N * V) * ((1 + s) * e) := by
      calc μ * B * ‖∑ i, δr (x, i) * h'' x i‖ ≤ μ * B * ((N * V) * vn (h'' x)) :=
            mul_le_mul_of_nonneg_left t2 (mul_nonneg hμ0 hB0)
        _ = (N * V) * (μ * B * vn (h'' x)) := by ring
        _ ≤ (N * V) * ((1 + s) * (ν * B * vn (h'' x))) := mul_le_mul_of_nonneg_left h7 hNV
        _ ≤ (N * V) * ((1 + s) * e) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left o2.le (by linarith)) hNV
    calc μ * B * ‖(∑ i, φr (x, i) * h'' x i) + ∑ i, δr (x, i) * h'' x i‖
        ≤ μ * B * (‖∑ i, φr (x, i) * h'' x i‖ + ‖∑ i, δr (x, i) * h'' x i‖) :=
          mul_le_mul_of_nonneg_left t1 (mul_nonneg hμ0 hB0)
      _ = μ * B * ‖∑ i, φr (x, i) * h'' x i‖ + μ * B * ‖∑ i, δr (x, i) * h'' x i‖ := by ring
      _ < (1 * e') ^ 2 := by nlinarith

end Complex

end Balaban.SmallField
