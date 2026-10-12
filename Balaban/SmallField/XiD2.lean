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
# (D2): `Ψ̃^c(𝔹; δ, ε) ⊆ Ξ^c(𝔹; 1, εb)` (P1 (3.21); Theorem 5.2 (3))

The data domain lies in the analyticity space once `εb ≥ ε + (2 K₁ + 1) δ`
(`K₁ = bgK1`, the constant of the bounds P2 (1.15)): the bounds of Theorem 5.2 (3) for the real
and the complex solution give the inequalities of `Ξ`; the closeness of the data to the
solutions gives the displacement inequalities.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

section Realization

variable (G)

/-- The datum realizing real raw data `(Ψ₀, h₀)`. -/
noncomputable def realData (Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (hΨ : IsLayerConstant G Ψ₀) : BgData G N :=
  BgData.clip G (fun x i => (Ψ₀ x i : ℂ)) (fun _ i => (h₀ i : ℂ))
    (fun n hn1 hnk x hx x' hx' => by
      funext i; exact congrArg (fun r : ℝ => (r : ℂ)) (congrFun (hΨ n hn1 hnk x hx x' hx') i))
    (fun _ _ _ _ _ _ _ => rfl)

/-- The datum realizing complex raw data `(Ψ₀ + Ψ'', h₀ + h'')`. -/
noncomputable def complexData (Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ) (hΨ : IsLayerConstant G Ψ₀)
    (hΨ'' : IsLayerConstant G Ψ'') (hh'' : IsLayerConstant G h'') : BgData G N :=
  BgData.clip G (fun x i => (Ψ₀ x i : ℂ) + Ψ'' x i) (fun x i => (h₀ i : ℂ) + h'' x i)
    (fun n hn1 hnk x hx x' hx' => by
      funext i
      show (Ψ₀ x' i : ℂ) + Ψ'' x' i = (Ψ₀ x i : ℂ) + Ψ'' x i
      rw [congrArg (fun r : ℝ => (r : ℂ)) (congrFun (hΨ n hn1 hnk x hx x' hx') i),
        congrFun (hΨ'' n hn1 hnk x hx x' hx') i])
    (fun n hn1 hnk x hx x' hx' => by
      funext i
      show (h₀ i : ℂ) + h'' x' i = (h₀ i : ℂ) + h'' x i
      rw [congrFun (hh'' n hn1 hnk x hx x' hx') i])

variable {G}

theorem realData_realizes {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    (hΨ : IsLayerConstant G Ψ₀) : Realizes (realData G Ψ₀ h₀ hΨ) Ψ₀ h₀ := by
  refine ⟨fun x hx i => ?_, fun x hx i => ?_⟩
  · simp [realData, BgData.clip, hx]
  · simp [realData, BgData.clip, hx]

theorem complexData_realizes {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hΨ : IsLayerConstant G Ψ₀)
    (hΨ'' : IsLayerConstant G Ψ'') (hh'' : IsLayerConstant G h'') :
    RealizesC (complexData G Ψ₀ h₀ Ψ'' h'' hΨ hΨ'' hh'') Ψ₀ h₀ Ψ'' h'' := by
  refine ⟨fun x hx i => ?_, fun x hx i => ?_⟩
  · simp [complexData, BgData.clip, hx]
  · simp [complexData, BgData.clip, hx]

end Realization

omit [NeZero N₀] [NeZero L] in
theorem vn_diff_diff (a b c e : Fin N → ℂ) :
    vn (fun i => (a i - b i) - (c i - e i)) ≤ vn (fun i => a i - c i) + vn (fun i => b i - e i) := by
  have h := vn_sub_le' (fun i => a i - c i) (fun i => b i - e i)
  have : (fun i => (a i - b i) - (c i - e i)) = fun i => (a i - c i) - (b i - e i) := by
    funext i; ring
  rw [this]; exact h

theorem blk_const {f : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hf : IsLayerConstant G f)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.blk (G.layerIndex x) x) : f y = f x := by
  obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
  exact hf _ hn1 hnk x hxl y hy

/-- The collar pairs are interface pairs. -/
theorem collar_interface {z z' : Torus d (N₀ * L ^ k)} (hz : z ∈ collar G) (hz' : z' ∈ collar G)
    (hadj : Adj z z') : IsInterfacePair G z z' := by
  have hzn : z ∉ G.Ω 1 := ((mem_collar G).1 hz).1
  have hzn' : z' ∉ G.Ω 1 := ((mem_collar G).1 hz').1
  refine ⟨(mem_dataSites G).2 (Or.inr hz), (mem_dataSites G).2 (Or.inr hz'),
    Or.inl (by rw [layerIndex_of_not_mem G hzn, layerIndex_of_not_mem G hzn']),
    z, by rw [blockSet_of_not_mem G hzn]; simp, z', by rw [blockSet_of_not_mem G hzn']; simp, hadj⟩

/-- The mean-closeness of the data to the solution: `|Ψ(x) - (Q φ)(x)| ≤ c`. -/
theorem close_of_bounds {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} {c : ℝ}
    (hb : BgBounds G D φ α c) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    vn (fun i => D.Ψ x i - blockAvg G φ x i) ≤ c := by
  obtain ⟨-, hnk, -⟩ := G.layerIndex_spec hx
  have h := vn_blockMean_sub_le (G := G) hnk (fun y i => svec G φ y i) x (D.Ψ x) (c := c)
    (fun y hy => by
      have hy1 := (blk_mem_Ω1' (precedes_refl G) hx hy).2
      have e : (fun i => svec G φ y i - D.Ψ x i) = fun i => φ (⟨y, hy1⟩, i) - D.Ψ y i := by
        funext i; rw [svec_of_mem' φ hy1, blk_const D.Ψ_layerConst hx hy]
      rw [e]; exact hb.val ⟨y, hy1⟩)
  have e := vn_sub_comm (fun i => blockMean G (G.layerIndex x) (fun y => svec G φ y i) x)
    (fun i => D.Ψ x i)
  exact e.symm.trans_le h

/-- **(D2), real data**: the real data domain lies in `Ξ(𝔹; 1, ε̄)` if `(K₁ + 1) δ ≤ εb`. -/
theorem psiTilde_subset_xiAt (H : BgHyp d L k ϱ a ν) {δ εb : ℝ} (hδ0 : 0 < δ)
    (hδc : δ ≤ bgC1 d L N) {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    (hP : InPsiTilde G ν δ Ψ₀ h₀) (hεb : (bgK1 d L N + 1) * δ ≤ εb) :
    XiAt G a ν k 1 εb (realData G Ψ₀ h₀ hP.layerConst) Ψ₀ h₀ := by
  have hK := bgK1_pos d L N
  have hKδ : 0 < bgK1 d L N * δ := mul_pos hK hδ0
  have hεb0 : 0 < εb := by nlinarith
  have hR := realData_realizes (h₀ := h₀) hP.layerConst
  set D := realData G Ψ₀ h₀ hP.layerConst with hD
  have hDom : InDomainR G ν δ D := ⟨Ψ₀, h₀, hP, hR.1, hR.2⟩
  have hDU : InUnionDomainR G (bgC1 d L N) ν D := ⟨δ, hδ0, hδc, hDom⟩
  obtain ⟨-, -, hsol, -, hbd⟩ := theorem71 H hDU
  have hb := hbd δ hδ0 hδc hDom
  refine ⟨hR, hDU, ?_⟩
  have hbig : bgK1 d L N * δ < εb := by nlinarith
  have hδεb : δ ≤ εb := by nlinarith
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x hx => ?_, fun z hz z' hz' hadj => ?_,
    fun z => ?_, ?_⟩
  · have h := hb.grad ⟨x, hx⟩ μ
    exact ⟨lt_of_le_of_lt h.1 (by rw [one_mul]; exact div_lt_div_of_pos_right hbig (by
      have := G.spacing_ge_one x; linarith)),
      lt_of_le_of_lt h.2 (by rw [one_mul]; exact div_lt_div_of_pos_right hbig (by
      have := G.spacing_ge_one x; linarith))⟩
  · have h := hb.lap ⟨x, hx⟩
    refine lt_of_le_of_lt h ?_
    rw [one_pow, one_mul]
    exact div_lt_div_of_pos_right hbig (by have := G.spacing_ge_one x; positivity)
  · have h := hb.alpha x
    rw [one_pow, one_mul]
    exact lt_of_le_of_lt h hbig
  · rw [one_pow, one_mul]
    exact lt_of_le_of_lt (close_of_bounds hb hx) hbig
  · have hip := collar_interface hz hz' hadj
    have h1 := hP.r1 z z' hip
    rw [one_mul]
    exact (realizes_vn hR hip.1 hip.2.1).trans_lt (h1.trans_le hδεb)
  · have h := mass_bound_spacing H hδ0 hδc hP hR.1 hR.2 hsol z
    have e : (fun i => bgField G a ν D (z, i) - D.h z i) =
        fun i => bgField G a ν D (z, i) - (h₀ i : ℂ) := by
      funext i; rw [hR.2 z z.2 i]
    rw [e] at h
    rw [one_mul]
    exact lt_of_le_of_lt h hbig
  · rw [one_mul]
    exact hP.r4.trans_le (pow_le_pow_left₀ hδ0.le hδεb 2)

/-- **(D2)** (P1 (3.21); Theorem 5.2 (3)): `Ψ̃^c(𝔹; δ, ε) ⊆ Ξ^c(𝔹; 1, ε̄)` if
`ε + (2 K₁ + 1) δ ≤ ε̄` (and `(δ, ε)` is admissible: `0 < δ ≤ ε ≤ c₀`, `δ ≤ c₁`,
`ν L^{2k} ε² ≤ δ²`), `K₁ = bgK1`.  (The notes have `ε + K₁ δ ≤ ε̄`; the factor `2K₁ + 1` comes
from comparing two solutions.) -/
theorem psiTildeC_subset_xiC (H : BgHyp d L k ϱ a ν) {δ ε εb : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδc : δ ≤ bgC1 d L N) (hνε : ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hP : InPsiTildeC G ν δ ε Ψ₀ h₀ Ψ'' h'') (hεb : ε + (2 * bgK1 d L N + 1) * δ ≤ εb) :
    XiC G a ν k 1 εb Ψ₀ h₀ Ψ'' h'' := by
  have hK := bgK1_pos d L N
  have hKδ : 0 < bgK1 d L N * δ := mul_pos hK hδ0
  have hε0 : 0 < ε := hδ0.trans_le hδε
  have hεb0 : 0 < εb := by nlinarith
  have hrealP := hP.toInPsiTilde
  have hxr := psiTilde_subset_xiAt (a := a) H hδ0 hδc hrealP (εb := εb) (by nlinarith)
  have hR := realData_realizes (h₀ := h₀) hP.layerConst
  have hC := complexData_realizes (h₀ := h₀) hP.layerConst hP.layerConst' hP.hLayerConst'
  set Dr := realData G Ψ₀ h₀ hP.layerConst with hDr
  set Dc := complexData G Ψ₀ h₀ Ψ'' h'' hP.layerConst hP.layerConst' hP.hLayerConst' with hDc
  have hDom : InDomainR G ν δ Dr := ⟨Ψ₀, h₀, hrealP, hR.1, hR.2⟩
  have hDcD : InDomainC G ν δ ε Dc := ⟨Ψ₀, h₀, Ψ'', h'', hP, hC.1, hC.2⟩
  have hDcU : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν Dc :=
    ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDcD⟩
  have hDU : InUnionDomainR G (bgC1 d L N) ν Dr := ⟨δ, hδ0, hδc, hDom⟩
  obtain ⟨-, -, hsolr, -, hbdr⟩ := theorem71 H hDU
  have hbr := hbdr δ hδ0 hδc hDom
  obtain ⟨-, hsolc, hbdc⟩ := theorem72 H hDcU
  have hbc := hbdc δ ε hδ0 hδε hε hδc hνε hDcD
  refine ⟨one_pos, hεb0, Dr, Dc, hxr, hC, hDcU, ?_⟩
  have hbig : 2 * (bgK1 d L N * δ) < εb := by nlinarith
  have hδεb : δ ≤ εb := by nlinarith
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_,
    fun z hz z' hz' hadj => ?_, fun x hx => ?_, fun x => ?_⟩
  · have h1 := hbc.grad ⟨x, hx⟩ μ
    have h2 := hbr.grad ⟨x, hx⟩ μ
    have hs : 0 < G.spacing x := by have := G.spacing_ge_one x; linarith
    have key : (2 * (bgK1 d L N * δ)) / G.spacing x < 1 * εb / G.spacing x := by
      rw [one_mul]; exact div_lt_div_of_pos_right hbig hs
    have e2 : 2 * (bgK1 d L N * δ) / G.spacing x =
        bgK1 d L N * δ / G.spacing x + bgK1 d L N * δ / G.spacing x := by ring
    refine ⟨lt_of_le_of_lt ((vn_diff_diff _ _ _ _).trans (add_le_add h1.1 h2.1)) ?_,
      lt_of_le_of_lt ((vn_diff_diff _ _ _ _).trans (add_le_add h1.2 h2.2)) ?_⟩ <;>
    · rw [← e2] at *; exact key
  · have h1 := hbc.lap ⟨x, hx⟩
    have h2 := hbr.lap ⟨x, hx⟩
    have hs : 0 < G.spacing x ^ 2 := by have := G.spacing_ge_one x; positivity
    have e : (fun i => ∑ μ : Fin d,
        ((barField G Dc.Ψ (bgFieldC G a ν (bgC0 d L N) Dc) (x + Pi.single μ 1) i -
            barField G Dr.Ψ (bgField G a ν Dr) (x + Pi.single μ 1) i) +
          (barField G Dc.Ψ (bgFieldC G a ν (bgC0 d L N) Dc) (x - Pi.single μ 1) i -
            barField G Dr.Ψ (bgField G a ν Dr) (x - Pi.single μ 1) i) -
          2 * (barField G Dc.Ψ (bgFieldC G a ν (bgC0 d L N) Dc) x i -
            barField G Dr.Ψ (bgField G a ν Dr) x i))) =
        fun i => (∑ μ : Fin d, (barField G Dc.Ψ (bgFieldC G a ν (bgC0 d L N) Dc) (x + Pi.single μ 1) i +
            barField G Dc.Ψ (bgFieldC G a ν (bgC0 d L N) Dc) (x - Pi.single μ 1) i -
            2 * barField G Dc.Ψ (bgFieldC G a ν (bgC0 d L N) Dc) x i)) -
          ∑ μ : Fin d, (barField G Dr.Ψ (bgField G a ν Dr) (x + Pi.single μ 1) i +
            barField G Dr.Ψ (bgField G a ν Dr) (x - Pi.single μ 1) i -
            2 * barField G Dr.Ψ (bgField G a ν Dr) x i) := by
      funext i; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun μ _ => by ring
    rw [e]
    refine lt_of_le_of_lt ((vn_sub_le' _ _).trans (add_le_add h1 h2)) ?_
    rw [one_pow, one_mul, ← add_div]
    exact div_lt_div_of_pos_right (by linarith) hs
  · have h1 := hbc.alpha x
    have h2 := hbr.alpha x
    have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
    calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖bgMultC G a ν (bgC0 d L N) Dc x -
          bgMult G a ν Dr x‖ ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
          (‖bgMultC G a ν (bgC0 d L N) Dc x‖ + ‖bgMult G a ν Dr x‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) hp
      _ = G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖bgMultC G a ν (bgC0 d L N) Dc x‖ +
          G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖bgMult G a ν Dr x‖ := by ring
      _ < 1 ^ 2 * εb := by rw [one_pow, one_mul]; linarith
  · -- val
    have hxd : (x : Torus d (N₀ * L ^ k)) ∈ dataSites G := (mem_dataSites G).2 (Or.inl x.2)
    have h1 := hbc.val x
    have h2 := hbr.val x
    have h3 := hP.c2a x hxd
    have t1 := vn_tri (fun i => bgFieldC G a ν (bgC0 d L N) Dc (x, i)) (fun i => Dc.Ψ x i)
      (fun i => bgField G a ν Dr (x, i))
    have t2 := vn_tri (fun i => Dc.Ψ x i) (fun i => Dr.Ψ x i) (fun i => bgField G a ν Dr (x, i))
    have e1 : (fun i => Dc.Ψ x i - Dr.Ψ x i) = Ψ'' x := by
      funext i; rw [psi''_eq hR hC hxd i]
    have e2 : vn (fun i => Dr.Ψ x i - bgField G a ν Dr (x, i)) =
        vn (fun i => bgField G a ν Dr (x, i) - Dr.Ψ x i) :=
      vn_sub_comm (fun i => bgField G a ν Dr (x, i)) (fun i => Dr.Ψ x i) |>.symm
    have e1' : vn (fun i => Dc.Ψ x i - Dr.Ψ x i) = vn (Ψ'' x) := by rw [e1]
    linarith
  · -- close
    have hn := (G.layerIndex_spec hx).2.1
    have h := vn_blockMean_sub_le (G := G) hn (fun y i => svec G (bgFieldC G a ν (bgC0 d L N) Dc -
        bgField G a ν Dr) y i) x (Ψ'' x) (c := 2 * (bgK1 d L N * δ)) (fun y hy => by
      have hy1 := (blk_mem_Ω1' (precedes_refl G) hx hy).2
      have hyd : y ∈ dataSites G := (mem_dataSites G).2 (Or.inl hy1)
      have e : (fun i => svec G (bgFieldC G a ν (bgC0 d L N) Dc - bgField G a ν Dr) y i - Ψ'' x i) =
          fun i => (bgFieldC G a ν (bgC0 d L N) Dc (⟨y, hy1⟩, i) - Dc.Ψ y i) -
            (bgField G a ν Dr (⟨y, hy1⟩, i) - Dr.Ψ y i) := by
        funext i
        rw [svec_of_mem' _ hy1, ← blk_const hP.layerConst' hx hy, psi''_eq hR hC hyd i]
        simp only [Pi.sub_apply]; ring
      rw [e]
      refine (vn_sub_le' _ _).trans ?_
      have := hbc.val ⟨y, hy1⟩
      have := hbr.val ⟨y, hy1⟩
      linarith)
    have e := vn_sub_comm (fun i => blockMean G (G.layerIndex x) (fun y => svec G
      (bgFieldC G a ν (bgC0 d L N) Dc - bgField G a ν Dr) y i) x) (Ψ'' x)
    rw [one_pow, one_mul]
    exact lt_of_le_of_lt (e.symm.trans_le h) hbig
  · -- collar bond
    have hip := collar_interface hz hz' hadj
    rw [one_mul]
    exact (hP.c1 z z' hip).trans_le hδεb
  · -- hAbs
    have h := hP.c3a x hx
    have h2 : δ ^ 2 / ε ≤ δ := by
      rw [div_le_iff₀ hε0]; nlinarith
    have e : (1 * εb) ^ 2 / εb = εb := by field_simp
    rw [e]
    nlinarith
  · -- hDot
    have hxd : (x : Torus d (N₀ * L ^ k)) ∈ dataSites G := (mem_dataSites G).2 (Or.inl x.2)
    obtain ⟨hδa, -⟩ := bgC1_facts d L N (by have := H.hd; omega) hδc
    have hδ1 : δ ≤ 1 / 1024 := (approxDelta_le d L hδa).1
    have hr2 := hP.r2 x hxd
    have hr0 := rn_nonneg (Ψ₀ x)
    have hsq : 1 / 2 ≤ rn (Ψ₀ x) ^ 2 := by
      rw [rn_sq_sum]
      have := (abs_lt.1 hr2).1
      linarith
    have hrpos : 0 < rn (Ψ₀ x) := by
      rcases hr0.eq_or_lt with h | h
      · rw [← h] at hsq; norm_num at hsq
      · exact h
    set r := rn (Ψ₀ x) with hrdef
    have h1r : |1 - r| ≤ δ := by
      have h2 : |1 - r ^ 2| = |1 - r| * (1 + r) := by
        rw [show 1 - r ^ 2 = (1 - r) * (1 + r) by ring, abs_mul,
          abs_of_pos (show (0 : ℝ) < 1 + r by linarith)]
      have h3 : |1 - r ^ 2| ≤ δ := by
        rw [abs_sub_comm, hrdef, rn_sq_sum]; exact hr2.le
      nlinarith [abs_nonneg (1 - r)]
    set u : Fin N → ℂ := fun i => ((Ψ₀ x i / r : ℝ) : ℂ) with hu
    set φ : Fin N → ℂ := fun i => bgField G a ν Dr (x, i) with hφ
    have hdist : vn (fun i => φ i - u i) ≤ bgK1 d L N * δ + δ := by
      have t := vn_tri φ (fun i => (Ψ₀ x i : ℂ)) u
      have e1 : vn (fun i => (Ψ₀ x i : ℂ) - u i) = |1 - r| := by
        rw [← vn_normalize_sub (Ψ₀ x) hrpos]
        exact vn_sub_comm (fun i => (Ψ₀ x i : ℂ)) u
      have e2 : vn (fun i => φ i - (Ψ₀ x i : ℂ)) ≤ bgK1 d L N * δ := by
        have h := hbr.val x
        have e : (fun i => φ i - (Ψ₀ x i : ℂ)) =
            fun i => bgField G a ν Dr (x, i) - Dr.Ψ x i := by
          funext i; simp [hφ, hR.1 x hxd i]
        rw [e]; exact h
      linarith
    have hc0 : 0 ≤ ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 := by
      have := H.mass; positivity
    have hAbs := hP.c3a x x.2
    have hε2 : δ ^ 2 / ε ≤ δ := by rw [div_le_iff₀ hε0]; nlinarith
    have hB := hP.c3b x x.2
    have hsplit : ∑ i, φ i * h'' x i = ∑ i, u i * h'' x i + ∑ i, (φ i - u i) * h'' x i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_; ring
    have hdot2 : ‖∑ i, (φ i - u i) * h'' x i‖ ≤ (bgK1 d L N * δ + δ) * vn (h'' x) :=
      (norm_dot_le _ _).trans (mul_le_mul hdist le_rfl (vn_nonneg _) (by positivity))
    have key : ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 *
        ‖∑ i, φ i * h'' x i‖ < δ ^ 2 + (bgK1 d L N * δ + δ) * δ := by
      rw [hsplit]
      calc _ ≤ ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 *
            (‖∑ i, u i * h'' x i‖ + ‖∑ i, (φ i - u i) * h'' x i‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) hc0
        _ = ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 * ‖∑ i, u i * h'' x i‖ +
            ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 *
              ‖∑ i, (φ i - u i) * h'' x i‖ := by ring
        _ < δ ^ 2 + (bgK1 d L N * δ + δ) * δ := by
            have h5 : ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 *
                ‖∑ i, (φ i - u i) * h'' x i‖ ≤ (bgK1 d L N * δ + δ) *
                  (ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 * vn (h'' x)) := by
              calc _ ≤ ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 *
                    ((bgK1 d L N * δ + δ) * vn (h'' x)) := mul_le_mul_of_nonneg_left hdot2 hc0
                _ = _ := by ring
            have h6 : (bgK1 d L N * δ + δ) *
                (ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 * vn (h'' x)) ≤
                (bgK1 d L N * δ + δ) * δ :=
              mul_le_mul_of_nonneg_left (hAbs.le.trans hε2) (by positivity)
            linarith
    refine key.trans_le ?_
    have hε'' : (2 * bgK1 d L N + 2) * δ ≤ εb := by nlinarith
    have h7 : δ ^ 2 + (bgK1 d L N * δ + δ) * δ ≤ ((2 * bgK1 d L N + 2) * δ) ^ 2 := by
      nlinarith [mul_pos hδ0 hδ0, mul_nonneg hK.le (mul_pos hδ0 hδ0).le]
    rw [one_mul]
    exact h7.trans (pow_le_pow_left₀ (by positivity) hε'' 2)

end Balaban.SmallField
