/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiCompose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The quadratic complex square estimate in scaled composition

The proof of scaled composition bounds the real and complex square deficits separately at
order theta squared. Their difference has the same order, although the field of ScaledPsiC
records a weaker estimate.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}
  {a : ℕ → ℝ} {a₁ ν δ ε η θ : ℝ} {j : ℕ}
  {Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h0 : Fin N → ℝ}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
  {φr φc : G'.Ω 1 × Fin N → ℂ}

/-- The complex square displacement of a composed datum has two powers of the scale gap. -/
theorem HypSle.comp_square_sharp
    (H : HypSle G G' a₁ ν δ ε η θ j Ψ0 h0 Ψ'' h'' φr φc)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    ‖∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i -
      ∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i‖
      ≤ θ ^ 2 * η * (2 * d + 10) := by
  have hP := H.hPC.toInPsiTilde
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hη6 : η ≤ 1 / 6 := by nlinarith [H.hsmall]
  have hδ0 := H.hδ
  have hMr : ∀ y ∈ G.blk (G.layerIndex x) x,
      vn (barVec G' (psiR Ψ0) φr y) ≤ 1 := fun y hy =>
    (barVec_vn_eq_one H.hφr H.hbr.unit _ (blk_mem_Ω1' H.prec hx hy).2).le
  have hMc : ∀ y ∈ G.blk (G.layerIndex x) x,
      vn (barVec G' (psiC Ψ0 Ψ'') φc y) ≤ 3 := by
    intro y hy
    have hy2 := (blk_mem_Ω1' H.prec hx hy).2
    have hyd : y ∈ dataSites G' := (mem_dataSites G').2 (Or.inl hy2)
    have e : barVec G' (psiC Ψ0 Ψ'') φc y =
        fun i => (φc (⟨y, hy2⟩, i) - psiC Ψ0 Ψ'' y i) + psiC Ψ0 Ψ'' y i := by
      funext i
      rw [barVec_of_mem _ φc hy2]
      ring
    rw [e]
    refine (vn_add' _ _).trans ?_
    have h1 := H.hbc.close ⟨y, hy2⟩
    have e2 : psiC Ψ0 Ψ'' y = fun i => (psiR Ψ0 y i) + Ψ'' y i := by
      funext i
      simp [psiC, psiR]
    have h2 : vn (psiC Ψ0 Ψ'' y) ≤ vn (psiR Ψ0 y) + vn (Ψ'' y) := by
      rw [e2]
      exact vn_add' _ _
    have h3 : vn (psiR Ψ0 y) ≤ 1 + δ := by
      have e3 : psiR Ψ0 y = fun i => (Ψ0 y i : ℂ) := rfl
      rw [e3, vn_ofReal]
      have hh := hP.r2 y hyd
      rw [← rn_sq_sum] at hh
      have h4 := rn_nonneg (Ψ0 y)
      have h5 := (abs_lt.1 hh).2
      by_contra hcon
      push Not at hcon
      nlinarith [sq_nonneg δ]
    have h6 := H.hPC.c2a y hyd
    have h7 : vn (fun i => φc (⟨y, hy2⟩, i) - psiC Ψ0 Ψ'' y i) ≤ η := h1
    linarith [H.hε1, H.hδη, hη6]
  have hc := H.hc.dot_sub_one hx hMc
  have hr := H.hr.dot_sub_one hx hMr
  have hc' : ‖∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i - 1‖ ≤
      (2 * d * (θ * η)) ^ 2 + 2 * θ ^ 2 * 3 * η + (θ ^ 2) ^ 2 * η ^ 2 := by
    simpa only [ccv] using hc
  have hr' : ‖∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i - 1‖ ≤
      (2 * d * (θ * η)) ^ 2 + 2 * θ ^ 2 * 1 * η + (θ ^ 2) ^ 2 * η ^ 2 := by
    simpa only [crv] using hr
  have e : ∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i -
      ∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i =
      (∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i - 1) -
      (∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i - 1) := by ring
  rw [e]
  calc
    _ ≤ ‖∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i - 1‖ +
        ‖∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i - 1‖ :=
      norm_sub_le _ _
    _ ≤ θ ^ 2 * η * (d + 7) + θ ^ 2 * η * (d + 3) := by
      have b3 := b2_le hd0 H.ηpos H.hθ0 H.hθ1 H.hsmall (M := 3)
      have b1 := b2_le hd0 H.ηpos H.hθ0 H.hθ1 H.hsmall (M := 1)
      nlinarith only [hc', hr', b3, b1]
    _ = θ ^ 2 * η * (2 * d + 10) := by ring

/-- The complex square displacement of a composed datum has two powers of the scale gap. -/
theorem HypS.comp_square_sharp
    (H : HypS G G' a₁ ν δ ε η θ j Ψ0 h0 Ψ'' h'' φr φc)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    ‖∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i -
      ∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i‖
      ≤ θ ^ 2 * η * (2 * d + 10) :=
  Balaban.SmallField.HypSle.comp_square_sharp H.toLe hx

/-- The sharp square displacement in the real-plus-complex coordinates of `ScaledPsiC`. -/
theorem HypSle.comp_square_scaled
    (H : HypSle G G' a₁ ν δ ε η θ j Ψ0 h0 Ψ'' h'' φr φc)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    ‖∑ i, (((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) +
        dPsi G G' a₁ φr φc Ψ0 Ψ'' x i) *
        (((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) +
          dPsi G G' a₁ φr φc Ψ0 Ψ'' x i) -
      ∑ i, (reR G G' a₁ φr Ψ0 x i : ℂ) * (reR G G' a₁ φr Ψ0 x i : ℂ)‖ <
      (scaledC0 d * θ) ^ 2 * η := by
  have hcastr : ∀ i, crv G G' a₁ φr Ψ0 x i =
      ((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) := fun i =>
    congrFun (H.real_crv x).eq_ofReal i
  have e0 : ∀ i, crv G G' a₁ φr Ψ0 x i +
      dPsi G G' a₁ φr φc Ψ0 Ψ'' x i = ccv G G' a₁ φc Ψ0 Ψ'' x i :=
    fun i => by simp [dPsi]
  simp only [← hcastr, e0]
  have hcoeff : 2 * (d : ℝ) + 10 < (scaledC0 d) ^ 2 := by
    unfold scaledC0
    nlinarith [sq_nonneg (d : ℝ)]
  calc
    _ ≤ θ ^ 2 * η * (2 * d + 10) := Balaban.SmallField.HypSle.comp_square_sharp H hx
    _ < θ ^ 2 * η * (scaledC0 d) ^ 2 :=
      mul_lt_mul_of_pos_left hcoeff (mul_pos (pow_pos H.hθ0 2) H.ηpos)
    _ = (scaledC0 d * θ) ^ 2 * η := by ring

/-- The sharp square displacement in the real-plus-complex coordinates of `ScaledPsiC`. -/
theorem HypS.comp_square_scaled
    (H : HypS G G' a₁ ν δ ε η θ j Ψ0 h0 Ψ'' h'' φr φc)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    ‖∑ i, (((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) +
        dPsi G G' a₁ φr φc Ψ0 Ψ'' x i) *
        (((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) +
          dPsi G G' a₁ φr φc Ψ0 Ψ'' x i) -
      ∑ i, (reR G G' a₁ φr Ψ0 x i : ℂ) * (reR G G' a₁ φr Ψ0 x i : ℂ)‖ <
      (scaledC0 d * θ) ^ 2 * η :=
  Balaban.SmallField.HypSle.comp_square_scaled H.toLe hx

/-- **A class chart supplies a scaled composition witness with the sharp complex square bound, at a
source level `n ≤ k`, at the realization of the chart** (core of
`xiC_scaledComposition_square_sharp_le`): the witness is the composition at the complex field
`φ^c = bgFieldC D^c` of a realization `D^c` of the member of the chart. -/
theorem xiC_scaledComposition_square_sharp_le_at (H' : BgHyp d L k ϱ' a ν)
    {a₁ ε₀ θ : ℝ} {j : ℕ}
    (hprec : Precedes G G') (hL : 2 ≤ L) (ha₁ : 0 < a₁)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hjθ : (L : ℝ) ^ j ≤ θ * (L : ℝ) ^ k)
    (hnj : ∀ x ∈ G.Ω 1, G.layerIndex x ≤ j) (hgap : ScaleGap G G' θ)
    (hcol : ∀ z ∈ collar G, z ∈ G'.Ω 1 ∧ 1 ≤ θ * G'.spacing z)
    (hsmall : (4 * d + 6) * (xiC1 d * ε₀) ≤ 1)
    (hX : XiC G' a ν k 1 ε₀ Ψ0 h0 Ψ'' h'') :
    ∃ Dc : BgData G' N, RealizesC Dc Ψ0 h0 Ψ'' h'' ∧ ∃ φr : G'.Ω 1 × Fin N → ℂ,
      ScaledPsiC G ν (scaledC0 d * θ) (xiC1 d * ε₀) j
        (reR G G' a₁ φr Ψ0) h0
        (dPsi G G' a₁ φr (bgFieldC G' a ν (bgC0 d L N) Dc) Ψ0 Ψ'') (hRes G h'') ∧
      (∀ x ∈ G.Ω 1,
        ‖∑ i, ccv G G' a₁ (bgFieldC G' a ν (bgC0 d L N) Dc) Ψ0 Ψ'' x i *
            ccv G G' a₁ (bgFieldC G' a ν (bgC0 d L N) Dc) Ψ0 Ψ'' x i -
          ∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i‖
          ≤ θ ^ 2 * (xiC1 d * ε₀) * (2 * d + 10)) ∧
      (∀ x ∈ G.Ω 1,
        ‖∑ i, (((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) +
            dPsi G G' a₁ φr (bgFieldC G' a ν (bgC0 d L N) Dc) Ψ0 Ψ'' x i) *
            (((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) +
              dPsi G G' a₁ φr (bgFieldC G' a ν (bgC0 d L N) Dc) Ψ0 Ψ'' x i) -
          ∑ i, (reR G G' a₁ φr Ψ0 x i : ℂ) * (reR G G' a₁ φr Ψ0 x i : ℂ)‖ <
          (scaledC0 d * θ) ^ 2 * (xiC1 d * ε₀)) ∧
      ∀ x i, crv G G' a₁ φr Ψ0 x i = ((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) := by
  have hc1 := one_le_xiC1 d
  have hε₀ := hX.2.1
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hC1a : 2 * (2 * (d : ℝ) + 1) ≤ xiC1 d := by unfold xiC1; nlinarith
  have hsmall' : (4 * d + 6) * ((2 * d + 1) * ε₀) ≤ 1 := by
    refine le_trans ?_ hsmall
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by
        have : (2 * (d : ℝ) + 1) ≤ xiC1 d := by linarith
        exact this) hε₀.le) (by positivity)
  have hP := xiC_one_subset H' hsmall' hX
  obtain ⟨-, -, Dr, Dc, hXr, hC, hDcU, hb⟩ := hX
  have hXr' := hXr
  obtain ⟨hR, hDomR, hbr⟩ := hXr
  set η := xiC1 d * ε₀ with hη
  have hηpos : 0 < η := by positivity
  have hη1 : η ≤ 1 := by nlinarith [mul_nonneg hd hηpos.le]
  have hEta : xiEta d 1 ε₀ ≤ η := by
    unfold xiEta
    rw [hη]
    have : (2 * (d : ℝ) + 1) ≤ xiC1 d := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this hε₀.le]
  have hEta2 : 2 * xiEta d 1 ε₀ ≤ η := by
    unfold xiEta
    rw [hη]
    nlinarith [mul_le_mul_of_nonneg_right hC1a hε₀.le]
  obtain ⟨hφre, hunr⟩ := xi_unit H' hXr'
  have hfr := fieldBounds_mono (xi_fieldBounds H' one_pos hε₀ le_rfl hXr') hEta
  have hfc := fieldBounds_mono (xiC_fieldBounds H' one_pos hε₀ le_rfl hXr' hC hDcU hb) hEta2
  let φr := bgField G' a ν Dr
  let φc := bgFieldC G' a ν (bgC0 d L N) Dc
  have HS : HypSle G G' a₁ ν η η η θ j Ψ0 h0 Ψ'' h'' φr φc :=
    { prec := hprec, hL := hL, ha₁ := ha₁, hθ0 := hθ0, hθ1 := hθ1,
      hjθ := hjθ, hnj := hnj, gap := hgap, hcol := hcol,
      hδ := hηpos, hδη := le_rfl, hηε := le_rfl, hε1 := hη1,
      hsmall := hsmall, hν := H'.mass, hνk := H'.massLe, hPC := hP,
      hφr := hφre
      hbr := fieldBounds_congr hfr
        (fun x hx => by funext i; simp [psiR, hR.1 x hx i])
      hmass := fun z => by
        have hh := (hbr.mass z).le
        rw [one_mul] at hh
        exact hh.trans (by nlinarith)
      hbc := fieldBounds_congr hfc (fun x hx => by funext i; simp [psiC])
      hdiff := fun z => (hb.val z).le.trans (by nlinarith) }
  refine ⟨Dc, hC, φr, scaledComposition_le HS, ?_, ?_,
    fun x i => congrFun (HS.real_crv x).eq_ofReal i⟩
  · intro x hx
    exact Balaban.SmallField.HypSle.comp_square_sharp HS hx
  · intro x hx
    rw [show bgFieldC G' a ν (bgC0 d L N) Dc = φc from rfl]
    have hcastr : ∀ i, crv G G' a₁ φr Ψ0 x i =
        ((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) := fun i =>
      congrFun (HS.real_crv x).eq_ofReal i
    have e0 : ∀ i, crv G G' a₁ φr Ψ0 x i +
        dPsi G G' a₁ φr φc Ψ0 Ψ'' x i = ccv G G' a₁ φc Ψ0 Ψ'' x i :=
      fun i => by simp [dPsi]
    simp only [← hcastr, e0]
    have hcoeff : 2 * (d : ℝ) + 10 < (scaledC0 d) ^ 2 := by
      unfold scaledC0
      nlinarith [sq_nonneg (d : ℝ)]
    calc
      _ ≤ θ ^ 2 * (xiC1 d * ε₀) * (2 * d + 10) :=
        Balaban.SmallField.HypSle.comp_square_sharp HS hx
      _ < θ ^ 2 * (xiC1 d * ε₀) * (scaledC0 d) ^ 2 :=
        mul_lt_mul_of_pos_left hcoeff (by positivity)
      _ = (scaledC0 d * θ) ^ 2 * (xiC1 d * ε₀) := by ring

/-- **A class chart supplies a scaled composition witness with the sharp complex square bound, at a
source level `n ≤ k`** (core of `xiC_scaledComposition_square_sharp`): the scale ratio enters as
`L^j ≤ θ L^k` (`HypSle`); for a source whose top layer on `Ω₁ ∪ C(Ω₁)` of `G` is `n`, `θ = L^{j-n}`.
The instance of `xiC_scaledComposition_square_sharp_le_at`. -/
theorem xiC_scaledComposition_square_sharp_le (H' : BgHyp d L k ϱ' a ν)
    {a₁ ε₀ θ : ℝ} {j : ℕ}
    (hprec : Precedes G G') (hL : 2 ≤ L) (ha₁ : 0 < a₁)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hjθ : (L : ℝ) ^ j ≤ θ * (L : ℝ) ^ k)
    (hnj : ∀ x ∈ G.Ω 1, G.layerIndex x ≤ j) (hgap : ScaleGap G G' θ)
    (hcol : ∀ z ∈ collar G, z ∈ G'.Ω 1 ∧ 1 ≤ θ * G'.spacing z)
    (hsmall : (4 * d + 6) * (xiC1 d * ε₀) ≤ 1)
    (hX : XiC G' a ν k 1 ε₀ Ψ0 h0 Ψ'' h'') :
    ∃ φr φc : G'.Ω 1 × Fin N → ℂ,
      ScaledPsiC G ν (scaledC0 d * θ) (xiC1 d * ε₀) j
        (reR G G' a₁ φr Ψ0) h0
        (dPsi G G' a₁ φr φc Ψ0 Ψ'') (hRes G h'') ∧
      (∀ x ∈ G.Ω 1,
        ‖∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i -
          ∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i‖
          ≤ θ ^ 2 * (xiC1 d * ε₀) * (2 * d + 10)) ∧
      (∀ x ∈ G.Ω 1,
        ‖∑ i, (((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) +
            dPsi G G' a₁ φr φc Ψ0 Ψ'' x i) *
            (((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) +
              dPsi G G' a₁ φr φc Ψ0 Ψ'' x i) -
          ∑ i, (reR G G' a₁ φr Ψ0 x i : ℂ) * (reR G G' a₁ φr Ψ0 x i : ℂ)‖ <
          (scaledC0 d * θ) ^ 2 * (xiC1 d * ε₀)) := by
  obtain ⟨Dc, -, φr, h1, h2, h3, -⟩ := xiC_scaledComposition_square_sharp_le_at H' hprec hL ha₁ hθ0
    hθ1 hjθ hnj hgap hcol hsmall hX
  exact ⟨φr, _, h1, h2, h3⟩

/-- A class chart supplies a scaled composition witness with the sharp complex square bound. -/
theorem xiC_scaledComposition_square_sharp (H' : BgHyp d L k ϱ' a ν)
    {a₁ ε₀ θ : ℝ} {j : ℕ}
    (hprec : Precedes G G') (hL : 2 ≤ L) (ha₁ : 0 < a₁)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hjθ : (L : ℝ) ^ j = θ * (L : ℝ) ^ k)
    (hnj : ∀ x ∈ G.Ω 1, G.layerIndex x ≤ j) (hgap : ScaleGap G G' θ)
    (hcol : ∀ z ∈ collar G, z ∈ G'.Ω 1 ∧ 1 ≤ θ * G'.spacing z)
    (hsmall : (4 * d + 6) * (xiC1 d * ε₀) ≤ 1)
    (hX : XiC G' a ν k 1 ε₀ Ψ0 h0 Ψ'' h'') :
    ∃ φr φc : G'.Ω 1 × Fin N → ℂ,
      ScaledPsiC G ν (scaledC0 d * θ) (xiC1 d * ε₀) j
        (reR G G' a₁ φr Ψ0) h0
        (dPsi G G' a₁ φr φc Ψ0 Ψ'') (hRes G h'') ∧
      (∀ x ∈ G.Ω 1,
        ‖∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i -
          ∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i‖
          ≤ θ ^ 2 * (xiC1 d * ε₀) * (2 * d + 10)) ∧
      (∀ x ∈ G.Ω 1,
        ‖∑ i, (((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) +
            dPsi G G' a₁ φr φc Ψ0 Ψ'' x i) *
            (((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) +
              dPsi G G' a₁ φr φc Ψ0 Ψ'' x i) -
          ∑ i, (reR G G' a₁ φr Ψ0 x i : ℂ) * (reR G G' a₁ φr Ψ0 x i : ℂ)‖ <
          (scaledC0 d * θ) ^ 2 * (xiC1 d * ε₀)) :=
  xiC_scaledComposition_square_sharp_le H' hprec hL ha₁ hθ0 hθ1 hjθ.le hnj hgap hcol hsmall hX

end Balaban.SmallField
