/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiCompose
public import Balaban.SmallField.XiProps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (Ξ3) at the field level: the composed datum lies in `Ξ^c_j(𝔹; C₀ θ σ, ε)`

For a member `(Ψ₀ + Ψ'', h₀ + h'')` of `Ξ^c_k(𝔹'; 1, ε₀)` and `𝔹 ≺ 𝔹'` with the scale gap
`ℓ ≤ θ ℓ'` on `Ω₁` and on the collar (`θ = L^{j-k}`), the composed data (6.2) of the real datum
`D^r` (with the real background field `φ^r`) and of the complex datum `D^c` (with `φ^c`) lie in
`Ξ^c_j(𝔹; C₀ θ, ε₀)`, `C₀ = 8d + 12` (`scaledC0`; any constant `≥ 1` works, the one of (R-S) is
kept).  The fields `bgField`, `bgFieldC`, `bgMult`, `bgMultC` of the composed data are the
restrictions of those of `D^r`, `D^c` (Theorem 7.3), so each inequality of `XiBounds`/`XiCBounds`
for `𝔹` is the corresponding inequality for `𝔹'` with `1/ℓ' ≤ θ/ℓ` (the first-order and
mean-free conditions) or `κ ≤ θ²` (the closeness conditions `|Ψ - Qφ| < σ² ε`, which is the
discrepancy identity `Ψ_j - Q_n φ' = κ (Ψ' - Q_p φ')` of (6.2)).

* `Balaban.SmallField.xiBounds_compose`, `Balaban.SmallField.xiCBounds_compose`: the inequalities;
* `Balaban.SmallField.xiC_compose_at`: the composed data realize `Ξ^c_j`, for given witnesses;
* `Balaban.SmallField.xiC_compose`: **(Ξ3)** as a membership `XiC G a ν j (C₀ θ) ε₀ ...`.

The proofs use of `C₀` only `1 ≤ C₀`: they are the instances `c = C₀` of
`xiBounds_compose_of_one_le`, `xiCBounds_compose_of_one_le`, `xiC_compose_at_of_one_le` and
`xiC_compose_of_one_le`, which hold for every constant `c ≥ 1` with `Ξ^c_j(𝔹; c θ, ε₀)`.  At `c = 1`
and `θ = 1` (`𝔹 ≺ 𝔹'` on one torus) the composed datum lies in `Ξ^c_j(𝔹; 1, ε₀)` at the same
radius: this is P3 Lemma 4.1 (4.29) (printed p. 74) with the weight `a(𝔹, 𝔹') = ℓ/ℓ' ≤ 1` of (4.30)
bounded by `1`.  The collar bonds use the strict first-order bound at a site of `Ω'₁`
(`xiBounds_adj_lt`, `xiCBounds_adj_lt`).
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

theorem one_le_scaledC0 (d : ℕ) : 1 ≤ scaledC0 d := by
  unfold scaledC0
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

theorem one_lt_scaledC0 (d : ℕ) : 1 < scaledC0 d := by
  unfold scaledC0
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

section Numeric

theorem inv_scale_le {ε θ ℓ ℓ' c : ℝ} (hε : 0 ≤ ε) (hθ : 0 < θ) (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ')
    (hg : ℓ ≤ θ * ℓ') (hc : 1 ≤ c) : 1 * ε / ℓ' ≤ c * θ * ε / ℓ := by
  rw [div_le_div_iff₀ hℓ' hℓ]
  have h1 := mul_le_mul_of_nonneg_left hg hε
  have h2 : 0 ≤ (c - 1) * (θ * ε * ℓ') := by positivity
  nlinarith

theorem inv_scale_sq_le {ε θ ℓ ℓ' c : ℝ} (hε : 0 ≤ ε) (hθ : 0 < θ) (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ')
    (hg : ℓ ≤ θ * ℓ') (hc : 1 ≤ c) : 1 ^ 2 * ε / ℓ' ^ 2 ≤ (c * θ) ^ 2 * ε / ℓ ^ 2 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h0 : ℓ ^ 2 ≤ (θ * ℓ') ^ 2 := pow_le_pow_left₀ hℓ.le hg 2
  have h1 := mul_le_mul_of_nonneg_left h0 hε
  have h2 : 0 ≤ (c ^ 2 - 1) * (θ ^ 2 * ε * ℓ' ^ 2) := by
    have : 1 ≤ c ^ 2 := by nlinarith
    have : 0 ≤ c ^ 2 - 1 := by linarith
    positivity
  nlinarith

theorem sq_scale_le {x θ ℓ ℓ' c : ℝ} (hx : 0 ≤ x) (hℓ : 0 ≤ ℓ) (hg : ℓ ≤ θ * ℓ') (hc : 1 ≤ c)
    (hθ : 0 < θ) : ℓ ^ 2 * x ≤ (c * θ) ^ 2 * (ℓ' ^ 2 * x) := by
  have h0 : ℓ ^ 2 ≤ (θ * ℓ') ^ 2 := pow_le_pow_left₀ hℓ hg 2
  have h1 : (θ * ℓ') ^ 2 ≤ (c * θ) ^ 2 * ℓ' ^ 2 := by
    have : θ ≤ c * θ := by nlinarith
    have h3 := pow_le_pow_left₀ hθ.le this 2
    nlinarith [sq_nonneg ℓ']
  nlinarith [mul_le_mul_of_nonneg_right (h0.trans h1) hx]

end Numeric

section Geometry

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {a₁ θ : ℝ}

theorem spacing_gap_pos (G : GeneratingSet d L N₀ k ϱ) (x : Torus d (N₀ * L ^ k)) :
    0 < G.spacing x := by
  have := G.spacing_ge_one x
  linarith

/-- `0 ≤ κ ≤ θ²` for the coefficient `κ = (a_p / a_n) L^{2(n-p)}` of (6.2), under the scale gap. -/
theorem kap_bounds_of_gap (hL : 2 ≤ L) (ha₁ : 0 < a₁) (h : Precedes G G')
    (hg : ScaleGap G G' θ) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    0 ≤ kap G G' (compWeight L a₁) x ∧ kap G G' (compWeight L a₁) x ≤ θ ^ 2 := by
  obtain ⟨r0, r1⟩ := compWeight_ratio hL ha₁ (G.layerIndex_spec hx).1 (h.layerIndex_le hx)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hq0 : 0 ≤ ((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2 := by positivity
  have hq1 : ((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2 ≤ θ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hg' := hg x hx
    unfold GeneratingSet.spacing at hg'
    have h0 : (0 : ℝ) ≤ (L : ℝ) ^ G.layerIndex x := by positivity
    calc ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ (θ * (L : ℝ) ^ G'.layerIndex x) ^ 2 :=
          pow_le_pow_left₀ h0 hg' 2
      _ = _ := by ring
  unfold kap
  exact ⟨mul_nonneg r0 hq0, (mul_le_of_le_one_left hq0 r1).trans hq1⟩

/-- Layer powers under the scale gap: `(L^n)² ≤ θ² (L^p)²`. -/
theorem layer_sq_le (hg : ScaleGap G G' θ) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ θ ^ 2 * ((L : ℝ) ^ G'.layerIndex x) ^ 2 := by
  have hg' := hg x hx
  unfold GeneratingSet.spacing at hg'
  have h0 : (0 : ℝ) ≤ (L : ℝ) ^ G.layerIndex x := by
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    positivity
  calc ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ (θ * (L : ℝ) ^ G'.layerIndex x) ^ 2 :=
        pow_le_pow_left₀ h0 hg' 2
    _ = _ := by ring

theorem barField_composeData (h : Precedes G G') (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (D' : BgData G' N) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ dataSites G) (i : Fin N) :
    barField G (composeData h a φ' D').Ψ (h.restrictφ φ') y i = barField G' D'.Ψ φ' y i :=
  barField_compose h a φ' D'.Ψ hy i

theorem composeData_Ψ_of_mem (h : Precedes G G') (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (D' : BgData G' N) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (i : Fin N) :
    (composeData h a φ' D').Ψ x i =
      blockMean G (G.layerIndex x) (fun y => svec G' φ' y i) x +
        (kap G G' a x : ℂ) *
          (D'.Ψ x i - blockMean G' (G'.layerIndex x) (fun y => svec G' φ' y i) x) :=
  composeField_of_mem a φ' D'.Ψ hx i

theorem composeData_Ψ_of_collar (h : Precedes G G') (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (D' : BgData G' N) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ collar G) (i : Fin N) :
    (composeData h a φ' D').Ψ x i = barField G' D'.Ψ φ' x i :=
  composeField_of_collar a φ' D'.Ψ hx i

theorem composeData_h_of_mem (h : Precedes G G') (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (D' : BgData G' N) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (i : Fin N) :
    (composeData h a φ' D').h x i = D'.h x i := by
  show (if x ∈ G.Ω 1 then D'.h x i else 0 : ℂ) = _
  simp only [hx, ↓reduceIte]

/-- `Q_n` of the restriction is `Q_n` of the field on `Ω'₁`. -/
theorem blockAvg_restrict (h : Precedes G G') (φ' : G'.Ω 1 × Fin N → ℂ)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (i : Fin N) :
    blockAvg G (h.restrictφ φ') x i =
      blockMean G (G.layerIndex x) (fun y => svec G' φ' y i) x := by
  unfold blockAvg blockMean
  congr 1
  refine Finset.sum_congr rfl fun y hy => ?_
  have hy1 := (blk_mem_Ω1' h hx hy).1
  have hy2 := (blk_mem_Ω1' h hx hy).2
  show svec G (h.restrictφ φ') y i = svec G' φ' y i
  rw [svec_of_mem' (h.restrictφ φ') hy1, svec_of_mem' φ' hy2]
  rfl

theorem blockAvg_restrict_sub (h : Precedes G G') (φc φr : G'.Ω 1 × Fin N → ℂ)
    (Ψc Ψr : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (i : Fin N) :
    blockAvg G (h.restrictφ φc - h.restrictφ φr) x i =
      blockMean G (G.layerIndex x) (fun y => diffBar G' Ψc Ψr φc φr y i) x := by
  unfold blockAvg blockMean
  congr 1
  refine Finset.sum_congr rfl fun y hy => ?_
  have hy1 := (blk_mem_Ω1' h hx hy).1
  have hy2 := (blk_mem_Ω1' h hx hy).2
  rw [svec_of_mem' (h.restrictφ φc - h.restrictφ φr) hy1]
  show φc (h.incl ⟨y, hy1⟩, i) - φr (h.incl ⟨y, hy1⟩, i) = diffBar G' Ψc Ψr φc φr y i
  unfold diffBar
  rw [barVec_of_mem Ψc φc hy2, barVec_of_mem Ψr φr hy2]
  rfl

end Geometry

section Bounds

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {a₁ ν ε₀ θ : ℝ} {j : ℕ}
  {h₀ : Fin N → ℝ}

/-- **The strict first-order bound at a bond leaving `Ω₁`**: for `x ∈ Ω₁` and a neighbour `x'`
(also in the collar), `|φ̄(x') - φ̄(x)| < σ ε / ℓ(x)` (clause `grad` of `XiBounds`). -/
theorem xiBounds_adj_lt {G : GeneratingSet d L N₀ k ϱ} {ν σ ε : ℝ} {n : ℕ} {D : BgData G N}
    {h₀ : Fin N → ℝ} {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    (hb : XiBounds G ν n σ ε D h₀ φ α) {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (hadj : Adj x x') : vn (barVec G D.Ψ φ x' - barVec G D.Ψ φ x) < σ * ε / G.spacing x := by
  obtain ⟨μ, h | h⟩ := hadj
  · rw [h]; exact (hb.grad x hx μ).1
  · have := (hb.grad x hx μ).2
    have e : x - Pi.single μ 1 = x' := by rw [h]; simp
    rw [e] at this
    exact this

/-- **The strict first-order bound of the difference at a bond leaving `Ω₁`** (clause `grad` of
`XiCBounds`). -/
theorem xiCBounds_adj_lt {G : GeneratingSet d L N₀ k ϱ} {ν σ ε : ℝ} {Dr Dc : BgData G N}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φr φc : G.Ω 1 × Fin N → ℂ}
    {αr αc : G.Ω 1 → ℂ} (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc)
    {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hadj : Adj x x') :
    vn (diffBar G Dc.Ψ Dr.Ψ φc φr x' - diffBar G Dc.Ψ Dr.Ψ φc φr x) < σ * ε / G.spacing x := by
  obtain ⟨μ, h | h⟩ := hadj
  · rw [h]; exact (hb.grad x hx μ).1
  · have := (hb.grad x hx μ).2
    have e : x - Pi.single μ 1 = x' := by rw [h]; simp
    rw [e] at this
    exact this

/-- **The inequalities of `Ξ_j(𝔹; c θ, ε₀)` for the composed real datum, for every constant
`c ≥ 1`**, from those of `Ξ_k(𝔹'; 1, ε₀)` for the datum `D` (P3 Lemma 4.1 (4.29)).  At `c = 1` and
`θ = 1` the composition keeps the radius. -/
theorem xiBounds_compose_of_one_le {c : ℝ} (hc₁ : 1 ≤ c) (hL : 2 ≤ L) (ha₁ : 0 < a₁)
    (h : Precedes G G') (hε₀ : 0 < ε₀) (hθ0 : 0 < θ) (hjθ : (L : ℝ) ^ j = θ * (L : ℝ) ^ k)
    (hgap : ScaleGap G G' θ) (hcol : ∀ z ∈ collar G, z ∈ G'.Ω 1 ∧ 1 ≤ θ * G'.spacing z)
    {D : BgData G' N} {φ : G'.Ω 1 × Fin N → ℂ} {α : G'.Ω 1 → ℂ}
    (hb : XiBounds G' ν k 1 ε₀ D h₀ φ α) :
    XiBounds G ν j (c * θ) ε₀ (composeData h (compWeight L a₁) φ D) h₀
      (h.restrictφ φ) (h.restrictα α) where
  grad x hx μ := by
    obtain ⟨n1, n2⟩ := nbr_mem_dataSites hx μ
    have hx' : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    obtain ⟨g1, g2⟩ := hb.grad x (h.mem_Ω1 hx) μ
    have hle := inv_scale_le hε₀.le hθ0 (spacing_gap_pos G x) (spacing_gap_pos G' x) (hgap x hx)
      hc₁
    simp only [barField_composeData h (compWeight L a₁) φ D n1, barField_composeData h
      (compWeight L a₁) φ D n2, barField_composeData h (compWeight L a₁) φ D hx']
    exact ⟨g1.trans_le hle, g2.trans_le hle⟩
  lap x hx := by
    have hx' : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have hle := inv_scale_sq_le hε₀.le hθ0 (spacing_gap_pos G x) (spacing_gap_pos G' x)
      (hgap x hx) hc₁
    have e : (fun i => ∑ μ : Fin d, (barField G (composeData h (compWeight L a₁) φ D).Ψ
        (h.restrictφ φ) (x + Pi.single μ 1) i + barField G (composeData h (compWeight L a₁) φ D).Ψ
        (h.restrictφ φ) (x - Pi.single μ 1) i - 2 * barField G
        (composeData h (compWeight L a₁) φ D).Ψ (h.restrictφ φ) x i)) =
        fun i => ∑ μ : Fin d, (barField G' D.Ψ φ (x + Pi.single μ 1) i +
          barField G' D.Ψ φ (x - Pi.single μ 1) i - 2 * barField G' D.Ψ φ x i) := by
      funext i
      refine Finset.sum_congr rfl fun μ _ => ?_
      obtain ⟨m1, m2⟩ := nbr_mem_dataSites hx μ
      rw [barField_composeData h (compWeight L a₁) φ D m1,
        barField_composeData h (compWeight L a₁) φ D m2,
        barField_composeData h (compWeight L a₁) φ D hx']
    rw [e]
    exact (hb.lap x (h.mem_Ω1 hx)).trans_le hle
  mult x := by
    have h1 := hb.mult (h.incl x)
    have h2 := sq_scale_le (x := ‖α (h.incl x)‖) (norm_nonneg _) (spacing_gap_pos G x.1).le
      (hgap x.1 x.2) hc₁ hθ0
    have h3 : G'.spacing (h.incl x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α (h.incl x)‖ <
        1 ^ 2 * ε₀ := h1
    show G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α (h.incl x)‖ < _
    calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α (h.incl x)‖
        ≤ (c * θ) ^ 2 * (G'.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
          ‖α (h.incl x)‖) := h2
      _ < (c * θ) ^ 2 * (1 ^ 2 * ε₀) :=
        mul_lt_mul_of_pos_left h3 (pow_pos (mul_pos (by linarith) hθ0) 2)
      _ = _ := by ring
  close x hx := by
    obtain ⟨k0, k1⟩ := kap_bounds_of_gap hL ha₁ h hgap hx
    have e : (fun i => (composeData h (compWeight L a₁) φ D).Ψ x i - blockAvg G (h.restrictφ φ) x i) =
        fun i => ((kap G G' (compWeight L a₁) x : ℝ) : ℂ) * (D.Ψ x i - blockAvg G' φ x i) := by
      funext i
      rw [composeData_Ψ_of_mem h _ φ D hx i, blockAvg_restrict h φ hx i]
      have e2 : blockAvg G' φ x i = blockMean G' (G'.layerIndex x) (fun y => svec G' φ y i) x := rfl
      rw [e2]
      ring
    rw [e, vn_smul_real, abs_of_nonneg k0]
    have hc := hb.close x (h.mem_Ω1 hx)
    have hv := vn_nonneg (fun i => D.Ψ x i - blockAvg G' φ x i)
    have hc0 := hc₁
    calc kap G G' (compWeight L a₁) x * vn (fun i => D.Ψ x i - blockAvg G' φ x i)
        ≤ θ ^ 2 * vn (fun i => D.Ψ x i - blockAvg G' φ x i) :=
          mul_le_mul_of_nonneg_right k1 hv
      _ < θ ^ 2 * (1 ^ 2 * ε₀) := mul_lt_mul_of_pos_left hc (by positivity)
      _ ≤ (c * θ) ^ 2 * ε₀ := by
        have h3 : 1 ≤ c ^ 2 := by nlinarith
        have h4 : 0 ≤ θ ^ 2 * ε₀ := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h3 h4]
  collarBond z hz z' hz' hadj := by
    have hzc := (hcol z hz)
    have h1 := xiBounds_adj_lt hb hzc.1 hadj
    have h2 : 1 * ε₀ / G'.spacing z ≤ θ * ε₀ := by
      rw [div_le_iff₀ (spacing_gap_pos G' z)]
      nlinarith [mul_le_mul_of_nonneg_right hzc.2 hε₀.le]
    have hc1 := hc₁
    have e : (fun i => (composeData h (compWeight L a₁) φ D).Ψ z i -
        (composeData h (compWeight L a₁) φ D).Ψ z' i) =
        barVec G' D.Ψ φ z - barVec G' D.Ψ φ z' := by
      funext i
      rw [composeData_Ψ_of_collar h _ φ D hz i, composeData_Ψ_of_collar h _ φ D hz' i]
      rfl
    rw [e, vn_sub_comm]
    calc _ < θ * ε₀ := h1.trans_le h2
      _ ≤ c * θ * ε₀ := by nlinarith [mul_pos hθ0 hε₀]
  mass z := by
    have h1 := hb.mass (h.incl z)
    have hs := Real.sqrt_nonneg ν
    have hv := vn_nonneg (fun i => φ (h.incl z, i) - (h₀ i : ℂ))
    have hg := hgap z.1 z.2
    have hc1 := hc₁
    show Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ k)) *
      vn (fun i => φ (h.incl z, i) - (h₀ i : ℂ)) < _
    calc Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ k)) *
          vn (fun i => φ (h.incl z, i) - (h₀ i : ℂ))
        ≤ Real.sqrt ν * (θ * G'.spacing (z : Torus d (N₀ * L ^ k))) *
          vn (fun i => φ (h.incl z, i) - (h₀ i : ℂ)) := by gcongr
      _ = θ * (Real.sqrt ν * G'.spacing (z : Torus d (N₀ * L ^ k)) *
          vn (fun i => φ (h.incl z, i) - (h₀ i : ℂ))) := by ring
      _ < θ * (1 * ε₀) := mul_lt_mul_of_pos_left h1 hθ0
      _ ≤ c * θ * ε₀ := by nlinarith [mul_pos hθ0 hε₀]
  hnorm := by
    have h1 := hb.hnorm
    have hc1 := hc₁
    rw [hjθ]
    calc ν * (θ * (L : ℝ) ^ k) ^ 2 * |∑ i, h₀ i ^ 2 - 1|
        = θ ^ 2 * (ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, h₀ i ^ 2 - 1|) := by ring
      _ < θ ^ 2 * (1 * ε₀) ^ 2 := mul_lt_mul_of_pos_left h1 (by positivity)
      _ ≤ (c * θ * ε₀) ^ 2 := by
        have : θ * ε₀ ≤ c * θ * ε₀ := by nlinarith [mul_pos hθ0 hε₀]
        nlinarith [pow_le_pow_left₀ (mul_pos hθ0 hε₀).le this 2]

/-- The inequalities of `Ξ_j(𝔹; C₀ θ, ε₀)` for the composed real datum, from those of
`Ξ_k(𝔹'; 1, ε₀)` for the datum `D`. -/
theorem xiBounds_compose (hL : 2 ≤ L) (ha₁ : 0 < a₁) (h : Precedes G G')
    (hε₀ : 0 < ε₀) (hθ0 : 0 < θ) (hjθ : (L : ℝ) ^ j = θ * (L : ℝ) ^ k)
    (hgap : ScaleGap G G' θ) (hcol : ∀ z ∈ collar G, z ∈ G'.Ω 1 ∧ 1 ≤ θ * G'.spacing z)
    {D : BgData G' N} {φ : G'.Ω 1 × Fin N → ℂ} {α : G'.Ω 1 → ℂ}
    (hb : XiBounds G' ν k 1 ε₀ D h₀ φ α) :
    XiBounds G ν j (scaledC0 d * θ) ε₀ (composeData h (compWeight L a₁) φ D) h₀
      (h.restrictφ φ) (h.restrictα α) where
  grad x hx μ :=
    (xiBounds_compose_of_one_le (one_le_scaledC0 d) hL ha₁ h hε₀ hθ0 hjθ hgap hcol hb).grad x hx μ
  __ := xiBounds_compose_of_one_le (one_le_scaledC0 d) hL ha₁ h hε₀ hθ0 hjθ hgap hcol hb

/-- The displacement of the composed field: `ψ_j(φ^c, Ψ^c) - ψ_j(φ^r, Ψ^r)` (6.2). -/
noncomputable def composeDisp (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (a : ℕ → ℝ) (φc φr : G'.Ω 1 × Fin N → ℂ) (Ψc Ψr : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) (i : Fin N) : ℂ :=
  composeField G G' a φc Ψc x i - composeField G G' a φr Ψr x i

/-- **The inequalities of `Ξ^c_j(𝔹; c θ, ε₀)` for the composed complex datum, for every constant
`c ≥ 1`**, from those of `Ξ^c_k(𝔹'; 1, ε₀)` (P3 Lemma 4.1 (4.29)). -/
theorem xiCBounds_compose_of_one_le {c : ℝ} (hc₁ : 1 ≤ c) (hL : 2 ≤ L) (ha₁ : 0 < a₁)
    (h : Precedes G G') (hν : 0 ≤ ν)
    (hε₀ : 0 < ε₀) (hθ0 : 0 < θ) (hgap : ScaleGap G G' θ)
    (hcol : ∀ z ∈ collar G, z ∈ G'.Ω 1 ∧ 1 ≤ θ * G'.spacing z)
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {Dr Dc : BgData G' N} {φr φc : G'.Ω 1 × Fin N → ℂ} {αr αc : G'.Ω 1 → ℂ}
    (hR : Realizes Dr Ψ₀ h₀) (hC : RealizesC Dc Ψ₀ h₀ Ψ'' h'')
    (hb : XiCBounds G' ν 1 ε₀ Dr Dc Ψ'' h'' φr φc αr αc) :
    XiCBounds G ν (c * θ) ε₀ (composeData h (compWeight L a₁) φr Dr)
      (composeData h (compWeight L a₁) φc Dc)
      (composeDisp G G' (compWeight L a₁) φc φr Dc.Ψ Dr.Ψ) (hRes G h'')
      (h.restrictφ φr) (h.restrictφ φc) (h.restrictα αr) (h.restrictα αc) where
  grad x hx μ := by
    obtain ⟨n1, n2⟩ := nbr_mem_dataSites hx μ
    have hx' : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    obtain ⟨g1, g2⟩ := hb.grad x (h.mem_Ω1 hx) μ
    have hle := inv_scale_le hε₀.le hθ0 (spacing_gap_pos G x) (spacing_gap_pos G' x) (hgap x hx)
      hc₁
    simp only [barField_composeData h (compWeight L a₁) φr Dr n1, barField_composeData h
      (compWeight L a₁) φr Dr n2, barField_composeData h (compWeight L a₁) φr Dr hx',
      barField_composeData h (compWeight L a₁) φc Dc n1, barField_composeData h
      (compWeight L a₁) φc Dc n2, barField_composeData h (compWeight L a₁) φc Dc hx']
    exact ⟨g1.trans_le hle, g2.trans_le hle⟩
  lap x hx := by
    have hx' : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have hle := inv_scale_sq_le hε₀.le hθ0 (spacing_gap_pos G x) (spacing_gap_pos G' x)
      (hgap x hx) hc₁
    have e : (fun i => ∑ μ : Fin d,
        ((barField G (composeData h (compWeight L a₁) φc Dc).Ψ (h.restrictφ φc)
            (x + Pi.single μ 1) i -
          barField G (composeData h (compWeight L a₁) φr Dr).Ψ (h.restrictφ φr)
            (x + Pi.single μ 1) i) +
        (barField G (composeData h (compWeight L a₁) φc Dc).Ψ (h.restrictφ φc)
            (x - Pi.single μ 1) i -
          barField G (composeData h (compWeight L a₁) φr Dr).Ψ (h.restrictφ φr)
            (x - Pi.single μ 1) i) -
        2 * (barField G (composeData h (compWeight L a₁) φc Dc).Ψ (h.restrictφ φc) x i -
          barField G (composeData h (compWeight L a₁) φr Dr).Ψ (h.restrictφ φr) x i))) =
        fun i => ∑ μ : Fin d,
        ((barField G' Dc.Ψ φc (x + Pi.single μ 1) i - barField G' Dr.Ψ φr (x + Pi.single μ 1) i) +
        (barField G' Dc.Ψ φc (x - Pi.single μ 1) i - barField G' Dr.Ψ φr (x - Pi.single μ 1) i) -
        2 * (barField G' Dc.Ψ φc x i - barField G' Dr.Ψ φr x i)) := by
      funext i
      refine Finset.sum_congr rfl fun μ _ => ?_
      obtain ⟨m1, m2⟩ := nbr_mem_dataSites hx μ
      rw [barField_composeData h (compWeight L a₁) φr Dr m1,
        barField_composeData h (compWeight L a₁) φr Dr m2,
        barField_composeData h (compWeight L a₁) φr Dr hx',
        barField_composeData h (compWeight L a₁) φc Dc m1,
        barField_composeData h (compWeight L a₁) φc Dc m2,
        barField_composeData h (compWeight L a₁) φc Dc hx']
    rw [e]
    exact (hb.lap x (h.mem_Ω1 hx)).trans_le hle
  mult x := by
    have h1 := hb.mult (h.incl x)
    have h2 := sq_scale_le (x := ‖αc (h.incl x) - αr (h.incl x)‖) (norm_nonneg _)
      (spacing_gap_pos G x.1).le (hgap x.1 x.2) hc₁ hθ0
    show G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖αc (h.incl x) - αr (h.incl x)‖ < _
    calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖αc (h.incl x) - αr (h.incl x)‖
        ≤ (c * θ) ^ 2 * (G'.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
          ‖αc (h.incl x) - αr (h.incl x)‖) := h2
      _ < (c * θ) ^ 2 * (1 ^ 2 * ε₀) :=
        mul_lt_mul_of_pos_left h1 (pow_pos (mul_pos (by linarith) hθ0) 2)
      _ = _ := by ring
  val x := hb.val (h.incl x)
  close x hx := by
    obtain ⟨k0, k1⟩ := kap_bounds_of_gap hL ha₁ h hgap hx
    have hxd : x ∈ dataSites G' := (mem_dataSites G').2 (Or.inl (h.mem_Ω1 hx))
    have e : (fun i => composeDisp G G' (compWeight L a₁) φc φr Dc.Ψ Dr.Ψ x i -
        blockAvg G (h.restrictφ φc - h.restrictφ φr) x i) =
        fun i => ((kap G G' (compWeight L a₁) x : ℝ) : ℂ) *
          (Ψ'' x i - blockMean G' (G'.layerIndex x)
            (fun y => diffBar G' Dc.Ψ Dr.Ψ φc φr y i) x) := by
      funext i
      have h1 : composeDisp G G' (compWeight L a₁) φc φr Dc.Ψ Dr.Ψ x i =
          blockMean G (G.layerIndex x) (fun y => diffBar G' Dc.Ψ Dr.Ψ φc φr y i) x +
          (kap G G' (compWeight L a₁) x : ℂ) * ((Dc.Ψ x i - Dr.Ψ x i) -
            blockMean G' (G'.layerIndex x) (fun y => diffBar G' Dc.Ψ Dr.Ψ φc φr y i) x) :=
        compVec_sub_eq (Ψc := Dc.Ψ) (Ψr := Dr.Ψ) (φc := φc) (φr := φr) (compWeight L a₁) h hx i
      rw [h1, blockAvg_restrict_sub h φc φr Dc.Ψ Dr.Ψ hx i, psi''_eq hR hC hxd i]
      ring
    rw [e, vn_smul_real, abs_of_nonneg k0]
    have hc := xiC_mean hb (h.mem_Ω1 hx)
    have hv := vn_nonneg (fun i => Ψ'' x i - blockMean G' (G'.layerIndex x)
      (fun y => diffBar G' Dc.Ψ Dr.Ψ φc φr y i) x)
    have hc0 := hc₁
    calc kap G G' (compWeight L a₁) x * vn (fun i => Ψ'' x i - blockMean G' (G'.layerIndex x)
          (fun y => diffBar G' Dc.Ψ Dr.Ψ φc φr y i) x)
        ≤ θ ^ 2 * vn (fun i => Ψ'' x i - blockMean G' (G'.layerIndex x)
          (fun y => diffBar G' Dc.Ψ Dr.Ψ φc φr y i) x) :=
          mul_le_mul_of_nonneg_right k1 hv
      _ < θ ^ 2 * (1 ^ 2 * ε₀) := mul_lt_mul_of_pos_left hc (by positivity)
      _ ≤ (c * θ) ^ 2 * ε₀ := by
        have h3 : 1 ≤ c ^ 2 := by nlinarith
        have h4 : 0 ≤ θ ^ 2 * ε₀ := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h3 h4]
  collarBond z hz z' hz' hadj := by
    have hzc := (hcol z hz)
    have h1 := xiCBounds_adj_lt hb hzc.1 hadj
    have h2 : 1 * ε₀ / G'.spacing z ≤ θ * ε₀ := by
      rw [div_le_iff₀ (spacing_gap_pos G' z)]
      nlinarith [mul_le_mul_of_nonneg_right hzc.2 hε₀.le]
    have hc1 := hc₁
    have e : (fun i => composeDisp G G' (compWeight L a₁) φc φr Dc.Ψ Dr.Ψ z i -
        composeDisp G G' (compWeight L a₁) φc φr Dc.Ψ Dr.Ψ z' i) =
        diffBar G' Dc.Ψ Dr.Ψ φc φr z - diffBar G' Dc.Ψ Dr.Ψ φc φr z' := by
      funext i
      unfold composeDisp
      rw [composeField_of_collar _ _ _ hz i, composeField_of_collar _ _ _ hz' i,
        composeField_of_collar _ _ _ hz i, composeField_of_collar _ _ _ hz' i]
      rfl
    rw [e, vn_sub_comm]
    calc _ < θ * ε₀ := h1.trans_le h2
      _ ≤ c * θ * ε₀ := by nlinarith [mul_pos hθ0 hε₀]
  hAbs x hx := by
    have h1 := hb.hAbs x (h.mem_Ω1 hx)
    have hsq := layer_sq_le hgap hx
    have hv := vn_nonneg (h'' x)
    rw [hRes_of_mem h'' hx]
    have hc1 := hc₁
    have e1 : (1 * ε₀) ^ 2 / ε₀ = ε₀ := by field_simp
    have e2 : (c * θ * ε₀) ^ 2 / ε₀ = (c * θ) ^ 2 * ε₀ := by field_simp
    rw [e1] at h1
    rw [e2]
    calc ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h'' x)
        ≤ ν * (θ ^ 2 * ((L : ℝ) ^ G'.layerIndex x) ^ 2) * vn (h'' x) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hν) hv
      _ = θ ^ 2 * (ν * ((L : ℝ) ^ G'.layerIndex x) ^ 2 * vn (h'' x)) := by ring
      _ < θ ^ 2 * ε₀ := mul_lt_mul_of_pos_left h1 (by positivity)
      _ ≤ (c * θ) ^ 2 * ε₀ := by
        have h3 : 1 ≤ c ^ 2 := by nlinarith
        have h4 : 0 ≤ θ ^ 2 * ε₀ := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h3 h4]
  hDot x := by
    have h1 := hb.hDot (h.incl x)
    have hsq := layer_sq_le hgap x.2
    have hv := norm_nonneg (∑ i, φr (h.incl x, i) * h'' (x : Torus d (N₀ * L ^ k)) i)
    have hc1 := hc₁
    have e : (∑ i, (h.restrictφ φr) (x, i) * hRes G h'' (x : Torus d (N₀ * L ^ k)) i) =
        ∑ i, φr (h.incl x, i) * h'' (x : Torus d (N₀ * L ^ k)) i := by
      rw [hRes_of_mem h'' x.2]
      rfl
    rw [e]
    calc ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 *
          ‖∑ i, φr (h.incl x, i) * h'' (x : Torus d (N₀ * L ^ k)) i‖
        ≤ ν * (θ ^ 2 * ((L : ℝ) ^ G'.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) *
          ‖∑ i, φr (h.incl x, i) * h'' (x : Torus d (N₀ * L ^ k)) i‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hν) hv
      _ = θ ^ 2 * (ν * ((L : ℝ) ^ G'.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 *
          ‖∑ i, φr (h.incl x, i) * h'' (x : Torus d (N₀ * L ^ k)) i‖) := by ring
      _ < θ ^ 2 * (1 * ε₀) ^ 2 := mul_lt_mul_of_pos_left h1 (by positivity)
      _ ≤ (c * θ * ε₀) ^ 2 := by
        have : θ * ε₀ ≤ c * θ * ε₀ := by nlinarith [mul_pos hθ0 hε₀]
        nlinarith [pow_le_pow_left₀ (mul_pos hθ0 hε₀).le this 2]

/-- The inequalities of `Ξ^c_j(𝔹; C₀ θ, ε₀)` for the composed complex datum, from those of
`Ξ^c_k(𝔹'; 1, ε₀)`. -/
theorem xiCBounds_compose (hL : 2 ≤ L) (ha₁ : 0 < a₁) (h : Precedes G G') (hν : 0 ≤ ν)
    (hε₀ : 0 < ε₀) (hθ0 : 0 < θ) (hgap : ScaleGap G G' θ)
    (hcol : ∀ z ∈ collar G, z ∈ G'.Ω 1 ∧ 1 ≤ θ * G'.spacing z)
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {Dr Dc : BgData G' N} {φr φc : G'.Ω 1 × Fin N → ℂ} {αr αc : G'.Ω 1 → ℂ}
    (hR : Realizes Dr Ψ₀ h₀) (hC : RealizesC Dc Ψ₀ h₀ Ψ'' h'')
    (hb : XiCBounds G' ν 1 ε₀ Dr Dc Ψ'' h'' φr φc αr αc) :
    XiCBounds G ν (scaledC0 d * θ) ε₀ (composeData h (compWeight L a₁) φr Dr)
      (composeData h (compWeight L a₁) φc Dc)
      (composeDisp G G' (compWeight L a₁) φc φr Dc.Ψ Dr.Ψ) (hRes G h'')
      (h.restrictφ φr) (h.restrictφ φc) (h.restrictα αr) (h.restrictα αc) where
  grad x hx μ :=
    (xiCBounds_compose_of_one_le (one_le_scaledC0 d) hL ha₁ h hν hε₀ hθ0 hgap hcol hR hC
      hb).grad x hx μ
  __ := xiCBounds_compose_of_one_le (one_le_scaledC0 d) hL ha₁ h hν hε₀ hθ0 hgap hcol hR hC hb

end Bounds

section Assembly

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {a₁ ν ε₀ θ : ℝ} {j : ℕ}
  {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {Dr Dc : BgData G' N}

/-- The real part of a member of `Ξ_k(𝔹'; 1, ε₀)` is in the domain of Theorem 7.3. -/
theorem xiAt_unionR (H' : BgHyp d L k ϱ' (compWeight L a₁) ν) (hε₀ : 0 < ε₀)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε₀) ≤ 1) (hth : xiC1 d * ε₀ ≤ thm73C1 d L N)
    (hXr : XiAt G' (compWeight L a₁) ν k 1 ε₀ Dr Ψ₀ h₀) :
    InUnionDomainR G' (thm73C1 d L N) ν Dr := by
  have hs1 : (4 * d + 6) * ((2 * d + 1) * (1 * ε₀)) ≤ 1 := by simpa using hsmall
  have hP := xi_subset_psiTilde H' le_rfl hs1 ⟨one_pos, hε₀, Dr, hXr⟩
  have hc1 := one_le_xiC1 d
  exact ⟨xiC1 d * (1 * ε₀), by rw [one_mul]; positivity, by rw [one_mul]; exact hth,
    Ψ₀, h₀, hP, hXr.1.1, hXr.1.2⟩

/-- The complex datum of a member of `Ξ^c_k(𝔹'; 1, ε₀)` is in the domain of Theorem 7.3. -/
theorem xiC_unionC (H' : BgHyp d L k ϱ' (compWeight L a₁) ν) (hε₀ : 0 < ε₀)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε₀) ≤ 1) (hth : xiC1 d * ε₀ ≤ thm73C1 d L N)
    (hX : XiC G' (compWeight L a₁) ν k 1 ε₀ Ψ₀ h₀ Ψ'' h'')
    {Dc : BgData G' N} (hC : RealizesC Dc Ψ₀ h₀ Ψ'' h'') :
    InUnionDomainC G' (bgC0 d L N) (thm73C1 d L N) ν Dc := by
  have hd0 : 0 < d := by have := H'.hd; omega
  have hc1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * ε₀ := by positivity
  have hP := xiC_one_subset H' hsmall hX
  have hδ1 := (thm73_small (L := L) (N := N) hd0 hδ0 hth).1
  refine ⟨xiC1 d * ε₀, xiC1 d * ε₀, hδ0, le_rfl, hδ1.trans (bgC1_le_bgC0 d L N hd0), hth, ?_,
    Ψ₀, h₀, Ψ'', h'', hP, hC.1, hC.2⟩
  have := H'.massLe
  nlinarith [sq_nonneg (xiC1 d * ε₀)]

/-- **(Ξ3) at the field level, with witnesses, for every constant `c ≥ 1`.**  Let
`(Ψ₀ + Ψ'', h₀ + h'')` be a member of
`Ξ^c_k(𝔹'; 1, ε₀)` with real datum `D^r` and complex datum `D^c`, and `𝔹 ≺ 𝔹'` with the scale gap
`ℓ ≤ θ ℓ'` on `Ω₁` and on the collar, `L^j = θ L^k`.  Then the composed data
`composeData h a (bgField D^r) D^r` and `composeData h a (bgFieldC D^c) D^c` realize a member of
`Ξ^c_j(𝔹; c θ, ε₀)`: the real part `Ψ_j = Re ψ(φ^r, Ψ^r)` with `h₀`, the complex
displacement `ψ(φ^c, Ψ^c) - ψ(φ^r, Ψ^r)` and `h''|_{Ω₁}`.  Moreover `bgField`, `bgFieldC`,
`bgMult`, `bgMultC` of the composed data are the restrictions to `Ω₁` of those of `D^r`, `D^c`. -/
theorem xiC_compose_at_of_one_le {c : ℝ} (hc₁ : 1 ≤ c) (ha₁ : 0 < a₁)
    (H : BgHyp d L k ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L k ϱ' (compWeight L a₁) ν) (h : Precedes G G') (hε₀ : 0 < ε₀)
    (hθ0 : 0 < θ) (hjθ : (L : ℝ) ^ j = θ * (L : ℝ) ^ k) (hgap : ScaleGap G G' θ)
    (hcol : ∀ z ∈ collar G, z ∈ G'.Ω 1 ∧ 1 ≤ θ * G'.spacing z)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε₀) ≤ 1) (hth : xiC1 d * ε₀ ≤ thm73C1 d L N)
    (hXr : XiAt G' (compWeight L a₁) ν k 1 ε₀ Dr Ψ₀ h₀) (hC : RealizesC Dc Ψ₀ h₀ Ψ'' h'')
    (hDcU : InUnionDomainC G' (bgC0 d L N) (bgC1 d L N) ν Dc)
    (hb : XiCBounds G' ν 1 ε₀ Dr Dc Ψ'' h'' (bgField G' (compWeight L a₁) ν Dr)
      (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) (bgMult G' (compWeight L a₁) ν Dr)
      (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) Dc)) :
    XiAt G (compWeight L a₁) ν j (c * θ) ε₀
        (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν Dr) Dr)
        (fun x i => (composeField G G' (compWeight L a₁)
          (bgField G' (compWeight L a₁) ν Dr) Dr.Ψ x i).re) h₀ ∧
      RealizesC
        (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc)
        (fun x i => (composeField G G' (compWeight L a₁)
          (bgField G' (compWeight L a₁) ν Dr) Dr.Ψ x i).re) h₀
        (composeDisp G G' (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc)
          (bgField G' (compWeight L a₁) ν Dr) Dc.Ψ Dr.Ψ) (hRes G h'') ∧
      InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν
        (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc) ∧
      XiCBounds G ν (c * θ) ε₀
        (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν Dr) Dr)
        (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc)
        (composeDisp G G' (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc)
          (bgField G' (compWeight L a₁) ν Dr) Dc.Ψ Dr.Ψ) (hRes G h'')
        (bgField G (compWeight L a₁) ν
          (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν Dr) Dr))
        (bgFieldC G (compWeight L a₁) ν (bgC0 d L N)
          (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc))
        (bgMult G (compWeight L a₁) ν
          (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν Dr) Dr))
        (bgMultC G (compWeight L a₁) ν (bgC0 d L N)
          (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc)) ∧
      bgField G (compWeight L a₁) ν
          (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν Dr) Dr) =
        h.restrictφ (bgField G' (compWeight L a₁) ν Dr) ∧
      bgMult G (compWeight L a₁) ν
          (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν Dr) Dr) =
        h.restrictα (bgMult G' (compWeight L a₁) ν Dr) ∧
      bgFieldC G (compWeight L a₁) ν (bgC0 d L N)
          (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc) =
        h.restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) ∧
      bgMultC G (compWeight L a₁) ν (bgC0 d L N)
          (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc) =
        h.restrictα (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) Dc) := by
  have hL : 2 ≤ L := by have := H.hL; omega
  have hX : XiC G' (compWeight L a₁) ν k 1 ε₀ Ψ₀ h₀ Ψ'' h'' :=
    ⟨one_pos, hε₀, Dr, Dc, hXr, hC, hDcU, hb⟩
  have hDR := xiAt_unionR H' hε₀ hsmall hth hXr
  have hDC := xiC_unionC H' hε₀ hsmall hth hX hC
  obtain ⟨hDR', -, hfR, hmR⟩ := theorem73_real ha₁ H H' h hDR
  obtain ⟨hDC', hfC, hmC⟩ := theorem73_complex ha₁ H H' h hDC
  obtain ⟨hφre, -⟩ := xi_unit H' hXr
  have hΨre : ∀ x ∈ dataSites G', ∀ i, (Dr.Ψ x i).im = 0 := fun x hx i => by
    rw [hXr.1.1 x hx i]; simp
  have hRe : ∀ x i, composeField G G' (compWeight L a₁) (bgField G' (compWeight L a₁) ν Dr) Dr.Ψ x i =
      (((composeField G G' (compWeight L a₁) (bgField G' (compWeight L a₁) ν Dr) Dr.Ψ x i).re : ℝ) :
        ℂ) := fun x i => by
    rw [Complex.ext_iff]
    exact ⟨by simp, by simp [composeField_im h _ _ Dr.Ψ hφre hΨre x i]⟩
  have hRz : Realizes
      (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν Dr) Dr)
      (fun x i => (composeField G G' (compWeight L a₁)
          (bgField G' (compWeight L a₁) ν Dr) Dr.Ψ x i).re) h₀ :=
    ⟨fun x _ i => hRe x i, fun x hx i => by
      rw [composeData_h_of_mem h _ _ Dr hx i]; exact hXr.1.2 x (h.mem_Ω1 hx) i⟩
  refine ⟨⟨hRz, hDR', ?_⟩, ⟨fun x _ i => ?_, fun x hx i => ?_⟩, hDC', ?_, hfR, hmR, hfC, hmC⟩
  · rw [hfR, hmR]
    exact xiBounds_compose_of_one_le hc₁ hL ha₁ h hε₀ hθ0 hjθ hgap hcol hXr.2.2
  · show composeField G G' (compWeight L a₁) _ Dc.Ψ x i = _ + (composeField G G' _ _ Dc.Ψ x i - _)
    rw [← hRe x i]
    ring
  · rw [composeData_h_of_mem h _ _ Dc hx i, hC.2 x (h.mem_Ω1 hx) i, hRes_of_mem h'' hx]
  · rw [hfR, hmR, hfC, hmC]
    exact xiCBounds_compose_of_one_le hc₁ hL ha₁ h H.mass hε₀ hθ0 hgap hcol hXr.1 hC hb

/-- **(Ξ3) at the field level, with witnesses.**  Let `(Ψ₀ + Ψ'', h₀ + h'')` be a member of
`Ξ^c_k(𝔹'; 1, ε₀)` with real datum `D^r` and complex datum `D^c`, and `𝔹 ≺ 𝔹'` with the scale gap
`ℓ ≤ θ ℓ'` on `Ω₁` and on the collar, `L^j = θ L^k`.  Then the composed data
`composeData h a (bgField D^r) D^r` and `composeData h a (bgFieldC D^c) D^c` realize a member of
`Ξ^c_j(𝔹; C₀ θ, ε₀)`, `C₀ = 8d + 12`: the real part `Ψ_j = Re ψ(φ^r, Ψ^r)` with `h₀`, the complex
displacement `ψ(φ^c, Ψ^c) - ψ(φ^r, Ψ^r)` and `h''|_{Ω₁}`.  Moreover `bgField`, `bgFieldC`,
`bgMult`, `bgMultC` of the composed data are the restrictions to `Ω₁` of those of `D^r`, `D^c`. -/
theorem xiC_compose_at (ha₁ : 0 < a₁) (H : BgHyp d L k ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L k ϱ' (compWeight L a₁) ν) (h : Precedes G G') (hε₀ : 0 < ε₀)
    (hθ0 : 0 < θ) (hjθ : (L : ℝ) ^ j = θ * (L : ℝ) ^ k) (hgap : ScaleGap G G' θ)
    (hcol : ∀ z ∈ collar G, z ∈ G'.Ω 1 ∧ 1 ≤ θ * G'.spacing z)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε₀) ≤ 1) (hth : xiC1 d * ε₀ ≤ thm73C1 d L N)
    (hXr : XiAt G' (compWeight L a₁) ν k 1 ε₀ Dr Ψ₀ h₀) (hC : RealizesC Dc Ψ₀ h₀ Ψ'' h'')
    (hDcU : InUnionDomainC G' (bgC0 d L N) (bgC1 d L N) ν Dc)
    (hb : XiCBounds G' ν 1 ε₀ Dr Dc Ψ'' h'' (bgField G' (compWeight L a₁) ν Dr)
      (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) (bgMult G' (compWeight L a₁) ν Dr)
      (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) Dc)) :
    XiAt G (compWeight L a₁) ν j (scaledC0 d * θ) ε₀
        (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν Dr) Dr)
        (fun x i => (composeField G G' (compWeight L a₁)
          (bgField G' (compWeight L a₁) ν Dr) Dr.Ψ x i).re) h₀ ∧
      RealizesC
        (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc)
        (fun x i => (composeField G G' (compWeight L a₁)
          (bgField G' (compWeight L a₁) ν Dr) Dr.Ψ x i).re) h₀
        (composeDisp G G' (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc)
          (bgField G' (compWeight L a₁) ν Dr) Dc.Ψ Dr.Ψ) (hRes G h'') ∧
      InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν
        (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc) ∧
      XiCBounds G ν (scaledC0 d * θ) ε₀
        (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν Dr) Dr)
        (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc)
        (composeDisp G G' (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc)
          (bgField G' (compWeight L a₁) ν Dr) Dc.Ψ Dr.Ψ) (hRes G h'')
        (bgField G (compWeight L a₁) ν
          (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν Dr) Dr))
        (bgFieldC G (compWeight L a₁) ν (bgC0 d L N)
          (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc))
        (bgMult G (compWeight L a₁) ν
          (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν Dr) Dr))
        (bgMultC G (compWeight L a₁) ν (bgC0 d L N)
          (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc)) ∧
      bgField G (compWeight L a₁) ν
          (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν Dr) Dr) =
        h.restrictφ (bgField G' (compWeight L a₁) ν Dr) ∧
      bgMult G (compWeight L a₁) ν
          (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν Dr) Dr) =
        h.restrictα (bgMult G' (compWeight L a₁) ν Dr) ∧
      bgFieldC G (compWeight L a₁) ν (bgC0 d L N)
          (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc) =
        h.restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) ∧
      bgMultC G (compWeight L a₁) ν (bgC0 d L N)
          (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc) =
        h.restrictα (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) Dc) :=
  xiC_compose_at_of_one_le (one_le_scaledC0 d) ha₁ H H' h hε₀ hθ0 hjθ hgap hcol hsmall hth hXr hC
    hDcU hb

/-- **(Ξ3) at the field level for every constant `c ≥ 1`** (SMALLFIELD.md §1.7 (Ξ3); P3 Lemma 4.1
(4.29)): the composed datum of a member
of `Ξ^c_k(𝔹'; 1, ε₀)` lies in `Ξ^c_j(𝔹; c θ, ε₀)`, `θ = L^{j-k}`, for
`𝔹 ≺ 𝔹'` with the scale gap `ℓ ≤ θ ℓ'` on `Ω₁` and on the collar, provided `C₁ ε₀` is in the domain
of Theorem 7.3. -/
theorem xiC_compose_of_one_le {c : ℝ} (hc₁ : 1 ≤ c) (ha₁ : 0 < a₁)
    (H : BgHyp d L k ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L k ϱ' (compWeight L a₁) ν) (h : Precedes G G') (hε₀ : 0 < ε₀)
    (hθ0 : 0 < θ) (hjθ : (L : ℝ) ^ j = θ * (L : ℝ) ^ k) (hgap : ScaleGap G G' θ)
    (hcol : ∀ z ∈ collar G, z ∈ G'.Ω 1 ∧ 1 ≤ θ * G'.spacing z)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε₀) ≤ 1) (hth : xiC1 d * ε₀ ≤ thm73C1 d L N)
    (hX : XiC G' (compWeight L a₁) ν k 1 ε₀ Ψ₀ h₀ Ψ'' h'') :
    ∃ (Ψr : Torus d (N₀ * L ^ k) → Fin N → ℝ) (Ψj'' hj'' : Torus d (N₀ * L ^ k) → Fin N → ℂ),
      XiC G (compWeight L a₁) ν j (c * θ) ε₀ Ψr h₀ Ψj'' hj'' := by
  obtain ⟨-, -, Dr, Dc, hXr, hC, hDcU, hb⟩ := hX
  obtain ⟨h1, h2, h3, h4, -⟩ := xiC_compose_at_of_one_le hc₁ ha₁ H H' h hε₀ hθ0 hjθ hgap hcol hsmall
    hth hXr hC hDcU hb
  have hc1 : (0 : ℝ) < c := by linarith
  exact ⟨_, _, hRes G h'', by positivity, hε₀, _, _, h1, h2, h3, h4⟩

/-- **(Ξ3) at the field level** (SMALLFIELD.md §1.7 (Ξ3) and (R-S)): the composed datum of a member
of `Ξ^c_k(𝔹'; 1, ε₀)` lies in `Ξ^c_j(𝔹; C₀ θ, ε₀)`, `C₀ = 8d + 12`, `θ = L^{j-k}`, for
`𝔹 ≺ 𝔹'` with the scale gap `ℓ ≤ θ ℓ'` on `Ω₁` and on the collar, provided `C₁ ε₀` is in the domain
of Theorem 7.3. -/
theorem xiC_compose (ha₁ : 0 < a₁) (H : BgHyp d L k ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L k ϱ' (compWeight L a₁) ν) (h : Precedes G G') (hε₀ : 0 < ε₀)
    (hθ0 : 0 < θ) (hjθ : (L : ℝ) ^ j = θ * (L : ℝ) ^ k) (hgap : ScaleGap G G' θ)
    (hcol : ∀ z ∈ collar G, z ∈ G'.Ω 1 ∧ 1 ≤ θ * G'.spacing z)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε₀) ≤ 1) (hth : xiC1 d * ε₀ ≤ thm73C1 d L N)
    (hX : XiC G' (compWeight L a₁) ν k 1 ε₀ Ψ₀ h₀ Ψ'' h'') :
    ∃ (Ψr : Torus d (N₀ * L ^ k) → Fin N → ℝ) (Ψj'' hj'' : Torus d (N₀ * L ^ k) → Fin N → ℂ),
      XiC G (compWeight L a₁) ν j (scaledC0 d * θ) ε₀ Ψr h₀ Ψj'' hj'' :=
  xiC_compose_of_one_le (one_le_scaledC0 d) ha₁ H H' h hε₀ hθ0 hjθ hgap hcol hsmall hth hX

end Assembly

section Transport

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {a₁ ν ε₀ θ : ℝ}
  {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {Dr Dc : BgData G' N}

/-- On `Ω'₁` the zero extension of `bgFieldC` is the Hölder-extended field `bgFieldExt`. -/
theorem svec_bgFieldC_eq_ext (a : ℕ → ℝ) (ν c₀ : ℝ) (D : BgData G' N) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G'.Ω 1) (i : Fin N) :
    svec G' (bgFieldC G' a ν c₀ D) y i = bgFieldExt G' a ν c₀ D y i := by
  rw [svec_of_mem' _ hy]
  simp [bgFieldExt, hy]

/-- **Reduction of (Ξ4)**: on `Ω₁` the composed field (6.2) of the complex background field is the
block mean `Q_n F` of the Hölder-extended field `F = bgFieldExt` (the field whose Hölder seminorm is
bounded by `xiC_holder`) plus the corrector `κ (Ψ' - Q_p F)`. -/
theorem composeField_eq_blockMean_ext (h : Precedes G G') (a : ℕ → ℝ) (ν c₀ : ℝ)
    (D : BgData G' N) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (i : Fin N) :
    composeField G G' a (bgFieldC G' a ν c₀ D) D.Ψ x i =
      blockMean G (G.layerIndex x) (fun y => bgFieldExt G' a ν c₀ D y i) x +
        (kap G G' a x : ℂ) *
          (D.Ψ x i - blockMean G' (G'.layerIndex x) (fun y => bgFieldExt G' a ν c₀ D y i) x) := by
  obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec (h.mem_Ω1 hx)
  have hsub : ∀ y ∈ G'.blk (G'.layerIndex x) x, y ∈ G'.Ω 1 := fun y hy =>
    G'.layer_subset hp1 hpk ((G'.mem_layer_iff hp1 hpk (GeneratingSet.mem_blk.1 hy)).2 hxp)
  have hsubG : ∀ y ∈ G.blk (G.layerIndex x) x, y ∈ G'.Ω 1 := fun y hy =>
    (blk_mem_Ω1' h hx hy).2
  rw [composeField_of_mem a _ D.Ψ hx i]
  have e1 : blockMean G (G.layerIndex x) (fun y => svec G' (bgFieldC G' a ν c₀ D) y i) x =
      blockMean G (G.layerIndex x) (fun y => bgFieldExt G' a ν c₀ D y i) x := by
    unfold blockMean
    congr 1
    exact Finset.sum_congr rfl fun y hy => svec_bgFieldC_eq_ext a ν c₀ D (hsubG y hy) i
  have e2 : blockMean G' (G'.layerIndex x) (fun y => svec G' (bgFieldC G' a ν c₀ D) y i) x =
      blockMean G' (G'.layerIndex x) (fun y => bgFieldExt G' a ν c₀ D y i) x := by
    unfold blockMean
    congr 1
    exact Finset.sum_congr rfl fun y hy => svec_bgFieldC_eq_ext a ν c₀ D (hsub y hy) i
  rw [e1, e2]
  rfl

/-- **The corrector of (Ξ4)**: for a member of `Ξ^c_k(𝔹'; 1, ε₀)` the composed field differs from the
block mean `Q_n F` of `F = bgFieldExt` by at most `2 θ² ε₀`. -/
theorem composeField_sub_blockMean_ext_le (ha₁ : 0 < a₁) (hL : 2 ≤ L) (h : Precedes G G')
    (hθ : ScaleGap G G' θ)
    (hR : Realizes Dr Ψ₀ h₀) (hC : RealizesC Dc Ψ₀ h₀ Ψ'' h'')
    (hbr : XiBounds G' ν k 1 ε₀ Dr h₀ (bgField G' (compWeight L a₁) ν Dr)
      (bgMult G' (compWeight L a₁) ν Dr))
    (hb : XiCBounds G' ν 1 ε₀ Dr Dc Ψ'' h'' (bgField G' (compWeight L a₁) ν Dr)
      (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) (bgMult G' (compWeight L a₁) ν Dr)
      (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) Dc)) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) :
    vn (fun i => composeField G G' (compWeight L a₁)
        (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Dc.Ψ x i -
      blockMean G (G.layerIndex x)
        (fun y => bgFieldExt G' (compWeight L a₁) ν (bgC0 d L N) Dc y i) x) ≤
      2 * θ ^ 2 * ε₀ := by
  obtain ⟨k0, k1⟩ := kap_bounds_of_gap hL ha₁ h hθ hx
  set φr := bgField G' (compWeight L a₁) ν Dr with hφr
  set φc := bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc with hφc
  have hxd : x ∈ dataSites G' := (mem_dataSites G').2 (Or.inl (h.mem_Ω1 hx))
  have hQ : ∀ i, blockMean G' (G'.layerIndex x)
      (fun y => bgFieldExt G' (compWeight L a₁) ν (bgC0 d L N) Dc y i) x = blockAvg G' φc x i := by
    intro i
    unfold blockAvg blockMean
    congr 1
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec (h.mem_Ω1 hx)
    have hy1 : y ∈ G'.Ω 1 :=
      G'.layer_subset hp1 hpk ((G'.mem_layer_iff hp1 hpk (GeneratingSet.mem_blk.1 hy)).2 hxp)
    exact (svec_bgFieldC_eq_ext _ ν _ Dc hy1 i).symm
  have hba : ∀ i, blockAvg G' (φc - φr) x i = blockAvg G' φc x i - blockAvg G' φr x i := by
    intro i
    unfold blockAvg
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : y ∈ G'.Ω 1
    · simp [svec, zeroExt, hy]
    · simp [svec, zeroExt, hy]
  have e : (fun i => composeField G G' (compWeight L a₁) φc Dc.Ψ x i -
      blockMean G (G.layerIndex x)
        (fun y => bgFieldExt G' (compWeight L a₁) ν (bgC0 d L N) Dc y i) x) =
      fun i => ((kap G G' (compWeight L a₁) x : ℝ) : ℂ) *
        ((Dr.Ψ x i - blockAvg G' φr x i) + (Ψ'' x i - blockAvg G' (φc - φr) x i)) := by
    funext i
    rw [composeField_eq_blockMean_ext h _ ν _ Dc hx i, hQ i, hba i, psi''_eq hR hC hxd i]
    ring
  rw [e, vn_smul_real, abs_of_nonneg k0]
  have h1 := hbr.close x (h.mem_Ω1 hx)
  have h2 := hb.close x (h.mem_Ω1 hx)
  have h3 := vn_add (fun i => Dr.Ψ x i - blockAvg G' φr x i)
    (fun i => Ψ'' x i - blockAvg G' (φc - φr) x i)
  have hv := vn_nonneg (fun i => (Dr.Ψ x i - blockAvg G' φr x i) +
    (Ψ'' x i - blockAvg G' (φc - φr) x i))
  calc kap G G' (compWeight L a₁) x * vn (fun i => (Dr.Ψ x i - blockAvg G' φr x i) +
        (Ψ'' x i - blockAvg G' (φc - φr) x i))
      ≤ θ ^ 2 * vn (fun i => (Dr.Ψ x i - blockAvg G' φr x i) +
        (Ψ'' x i - blockAvg G' (φc - φr) x i)) := mul_le_mul_of_nonneg_right k1 hv
    _ ≤ θ ^ 2 * (2 * ε₀) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : vn (fun i => (Dr.Ψ x i - blockAvg G' φr x i) +
            (Ψ'' x i - blockAvg G' (φc - φr) x i)) ≤
            vn (fun i => Dr.Ψ x i - blockAvg G' φr x i) +
            vn (fun i => Ψ'' x i - blockAvg G' (φc - φr) x i) := h3
        linarith
    _ = 2 * θ ^ 2 * ε₀ := by ring

end Transport


