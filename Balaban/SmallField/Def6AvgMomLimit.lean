/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgMomTorus
public import Balaban.SmallField.Def6BridgeInfMoment

/-!
# Reynolds averaging: the second moment of `T∞` around an arbitrary centre

For a centre `y ∈ ℤ^d` the second moment of the cut-off terms of `T∞` through `y`,
`MomY y X' = ∑_{x,x' ∈ X'} B_{X'}^{(y)}(x,x') |x - x'|²`, satisfies `∑_{X'} MomY y X' = 0`
(`momY_tsum_zero`): it is the limit of the second-moment sums `momentSum` of the tori
(`LiftCtx.momentSum_shapes_centre`, `tendsto_shapeSum`), which tend to `0` by `RenormCond.moment`.

* `abs_valMinAbs_le`, `liftSq_ibase_sub_le`: the wrapped squared norm is at most the squared norm;
* `tensB_GE_eq_EauxC`: on a good torus the tensor of `GE` is that of the centre-`y` class term;
* `norm_mom_torus_le`: the Cauchy bound of the pair sum on a good torus.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Metric Set

section Elem

theorem abs_valMinAbs_le (n : ℕ) [NeZero n] (w : ℤ) :
    |ZMod.valMinAbs ((w : ℤ) : ZMod n)| ≤ |w| := by
  by_cases h : 2 * |w| < n
  · rw [valMinAbs_intCast_of_small h]
  · push Not at h
    set v := ZMod.valMinAbs ((w : ℤ) : ZMod n) with hvdef
    have h1 := ZMod.natAbs_valMinAbs_le ((w : ℤ) : ZMod n)
    have h2 : 2 * v.natAbs ≤ n := by
      have := Nat.div_mul_le_self n 2
      rw [← hvdef] at h1
      omega
    have hv : |v| = (v.natAbs : ℤ) := Int.abs_eq_natAbs v
    have h2' : (2 : ℤ) * |v| ≤ n := by rw [hv]; exact_mod_cast h2
    linarith

theorem poly_exp_tail' {s κ : ℝ} (hs : 0 ≤ s) :
    (1 + s) ^ 4 * Real.exp (-κ * s) ≤ 24 * Real.exp 1 * Real.exp (-(κ - 1) * s) := by
  have hpow : (1 + s) ^ 4 ≤ 24 * Real.exp (1 + s) := by
    have := Real.pow_div_factorial_le_exp (1 + s) (by linarith) 4
    rw [div_le_iff₀ (by norm_num)] at this
    norm_num [Nat.factorial] at this
    linarith
  have e1 : Real.exp (1 + s) * Real.exp (-κ * s) = Real.exp 1 * Real.exp (-(κ - 1) * s) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc (1 + s) ^ 4 * Real.exp (-κ * s) ≤ 24 * Real.exp (1 + s) * Real.exp (-κ * s) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = 24 * (Real.exp (1 + s) * Real.exp (-κ * s)) := by ring
    _ = 24 * Real.exp 1 * Real.exp (-(κ - 1) * s) := by rw [e1]; ring

end Elem

section Torus

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem liftSq_ibase_sub_le {j : ℕ} (z z' : Fin d → ℤ) :
    liftSq L j (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z -
      ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z') ≤ ∑ μ, (((z μ - z' μ : ℤ) : ℝ)) ^ 2 := by
  have : NeZero (N₁ * L ^ m₁ * L ^ k) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  unfold liftSq
  refine Finset.sum_le_sum fun μ _ => ?_
  have hL0 : (0 : ℝ) < (L : ℝ) ^ j := by
    have : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
    positivity
  have e1 : (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z -
      ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z') μ =
      ((((L ^ j : ℕ) : ℤ) * (z μ - z' μ) : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ k)) := by
    simp only [ibase, Pi.sub_apply]; push_cast; ring
  rw [e1]
  have h1 := abs_valMinAbs_le (N₁ * L ^ m₁ * L ^ k) (((L ^ j : ℕ) : ℤ) * (z μ - z' μ))
  have h2 : |((ZMod.valMinAbs ((((L ^ j : ℕ) : ℤ) * (z μ - z' μ) : ℤ) :
      ZMod (N₁ * L ^ m₁ * L ^ k)) : ℤ) : ℝ)| ≤ (L : ℝ) ^ j * |((z μ - z' μ : ℤ) : ℝ)| := by
    have := (Int.cast_le (R := ℝ)).2 h1
    rw [Int.cast_abs, Int.cast_abs] at this
    refine this.trans (le_of_eq ?_)
    push_cast
    rw [abs_mul, abs_of_pos hL0]
  rw [div_pow, div_le_iff₀ (by positivity), ← sq_abs]
  calc |((ZMod.valMinAbs ((((L ^ j : ℕ) : ℤ) * (z μ - z' μ) : ℤ) :
        ZMod (N₁ * L ^ m₁ * L ^ k)) : ℤ) : ℝ)| ^ 2
      ≤ ((L : ℝ) ^ j * |((z μ - z' μ : ℤ) : ℝ)|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    _ = ((z μ - z' μ : ℤ) : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2 := by rw [mul_pow, sq_abs]; ring

omit [NeZero L] [NeZero N₁] in
/-- Cauchy estimate for the tensor `tensB` of a function bounded and analytic on the ball. -/
theorem norm_tensB_le_of_ball {i₀ i₁ : Fin N} {ν ρ M : ℝ} {X : Finset (Site d)}
    {f : Cfg d N X → ℂ} (hρ : 0 < ρ) (hana : AnalyticOnNhd ℂ f (ball (refPt i₀ ν X) ρ))
    (hM : ∀ c ∈ ball (refPt i₀ ν X) ρ, ‖f c‖ ≤ M) (z z' : ↥X) :
    ‖tensB i₀ i₁ ν X f z z'‖ ≤ 4 * M / ρ ^ 2 := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM _ (mem_ball_self hρ))
  have h := norm_D2_le hρ hana hM (Pi.single (Sum.inl (z, i₁)) (1 : ℂ) : Cfg d N X)
    (Pi.single (Sum.inl (z', i₁)) (1 : ℂ) : Cfg d N X)
  have h1 := norm_single_one_le (Sum.inl (z, i₁) : Idx d N X)
  have h2 := norm_single_one_le (Sum.inl (z', i₁) : Idx d N X)
  unfold tensB
  refine h.trans ?_
  rw [div_le_div_iff_of_pos_right (by positivity)]
  nlinarith [mul_nonneg hM0 (norm_nonneg (Pi.single (Sum.inl (z, i₁)) (1 : ℂ) : Cfg d N X)),
    mul_le_mul h1 h2 (norm_nonneg _) zero_le_one]

variable (L m₁) in
/-- The constant of the pair-length bound around the centre `y`. -/
noncomputable def lenB (P : Consts) (y : Site d) : ℝ :=
  2 * ∑ μ, |(y μ : ℝ)| + 4 * d * ((L : ℝ) ^ (P.m₀ + m₁)) * Real.sqrt d * L +
    2 * d * ((L : ℝ) ^ (P.m₀ + m₁))

omit [NeZero L] in
theorem lenB_nonneg (P : Consts) (y : Site d) : 0 ≤ lenB (d := d) L m₁ P y := by
  unfold lenB
  have : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  positivity

variable (L m₁) in
/-- The constant of the second-moment bound of a shape through `y`. -/
noncomputable def momC (P : Consts) (ρ : ℝ) (y : Site d) : ℝ :=
  (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (4 * P.E₀ / ρ ^ 2) * lenB (d := d) L m₁ P y ^ 2

/-- **The distance of two blocks of a good shape through `y`**: `∑_μ |x_μ - x'_μ| ≤ B (1 + d)`. -/
theorem pair_len_le {P : Consts} {j : ℕ} (hjk : j ≤ k) {y : Site d} {X' : Finset (Site d)}
    (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (hy : y ∈ X')
    {x x' : Site d} (hx : x ∈ X') (hx' : x' ∈ X') :
    ∑ μ, |((x μ - x' μ : ℤ) : ℝ)| ≤ lenB (d := d) L m₁ P y *
      (1 + sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) := by
  set s := sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
    (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') with hs
  have hs0 : 0 ≤ s := by
    rw [hs]; unfold sizeJ; exact treeLenCovOne_nonneg _ _ _
  have hMb : (0 : ℝ) ≤ (L : ℝ) ^ (P.m₀ + m₁) := by positivity
  have hLn : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hcoord : ∀ μ, |((x μ - x' μ : ℤ) : ℝ)| ≤ 2 * |(y μ : ℝ)| +
      2 * ((L : ℝ) ^ (P.m₀ + m₁)) * (s + 2 * Real.sqrt d * L) := by
    intro μ
    have h1 := coord_le_of_good (m₀ := P.m₀) hjk hnw hpd hy hx μ
    have h2 := coord_le_of_good (m₀ := P.m₀) hjk hnw hpd hy hx' μ
    rw [← hs] at h1 h2
    simp only [Int.cast_abs] at h1 h2
    push_cast
    calc |((x μ : ℝ)) - (x' μ : ℝ)| ≤ |(x μ : ℝ)| + |(x' μ : ℝ)| := abs_sub _ _
      _ ≤ _ := by linarith
  calc ∑ μ, |((x μ - x' μ : ℤ) : ℝ)|
      ≤ ∑ μ : Fin d, (2 * |(y μ : ℝ)| + 2 * ((L : ℝ) ^ (P.m₀ + m₁)) * (s + 2 * Real.sqrt d * L)) :=
        Finset.sum_le_sum fun μ _ => hcoord μ
    _ = 2 * ∑ μ, |(y μ : ℝ)| + d * (2 * ((L : ℝ) ^ (P.m₀ + m₁)) * (s + 2 * Real.sqrt d * L)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp
    _ ≤ lenB (d := d) L m₁ P y * (1 + s) := by
        unfold lenB
        have hsq : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        have hy0 : 0 ≤ ∑ μ, |(y μ : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        nlinarith [mul_nonneg hd0 (mul_nonneg hMb hs0), mul_nonneg hy0 hs0,
          mul_nonneg (mul_nonneg hd0 hMb) (mul_nonneg hsq hLn),
          mul_nonneg (mul_nonneg (mul_nonneg hd0 hMb) (mul_nonneg hsq hLn)) hs0]

variable {P : Consts} {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ} {ρ : ℝ}

/-- **The Cauchy bound of a pair sum on a good torus**: for weights bounded by the squared distance,
`‖∑ B_{X'}(z,z') w(z,z')‖ ≤ C (1 + d)⁴ e^{-κ d}`. -/
theorem LiftCtx.norm_mom_torus_le (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (hN : L ^ P.m₀ ∣ N₁)
    (hE0 : 0 ≤ P.E₀) {i₀ i₁ : Fin N} {y : Site d} {X' : Finset (Site d)}
    (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (hy : y ∈ X')
    (w : ↥X' → ↥X' → ℂ) (hw : ∀ z z', ‖w z z'‖ ≤ ∑ μ, (((z.1 μ - z'.1 μ : ℤ) : ℝ)) ^ 2) :
    ‖∑ z : ↥X', ∑ z' : ↥X', tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
        (EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' * w z z'‖ ≤
      momC (d := d) L m₁ P ρ y *
        ((1 + sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
            (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) ^ 4 *
          Real.exp (-P.κ * sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
            (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))) := by
  have hjk := ctx.jk
  have hρ0 := ctx.rho_pos
  set s := sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
    (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') with hs
  have hs0 : 0 ≤ s := by
    rw [hs]; unfold sizeJ; exact treeLenCovOne_nonneg _ _ _
  set M : ℝ := P.E₀ * Real.exp (-P.κ * s) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hT : ∀ z z' : ↥X', ‖tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
      (EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X') z z'‖ ≤ 4 * M / ρ ^ 2 := fun z z' =>
    norm_tensB_le_of_ball hρ0 (fun c hc => ctx.analyticAt_EauxC i₀ hpd y hnw hy hc)
      (fun c hc => ctx.norm_EauxC_le i₀ hpd y hnw hy (ctx.mem_xiDom i₀ hpd hc)) z z'
  set Lb := lenB (d := d) L m₁ P y with hLb
  have hLb0 : 0 ≤ Lb := lenB_nonneg P y
  have hlen : ∀ z z' : ↥X', ∑ μ, (((z.1 μ - z'.1 μ : ℤ) : ℝ)) ^ 2 ≤ (Lb * (1 + s)) ^ 2 := by
    intro z z'
    calc ∑ μ, (((z.1 μ - z'.1 μ : ℤ) : ℝ)) ^ 2 = ∑ μ, |((z.1 μ - z'.1 μ : ℤ) : ℝ)| ^ 2 := by
          simp only [sq_abs]
      _ ≤ (∑ μ, |((z.1 μ - z'.1 μ : ℤ) : ℝ)|) ^ 2 :=
          Finset.sum_sq_le_sq_sum_of_nonneg fun μ _ => abs_nonneg _
      _ ≤ (Lb * (1 + s)) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg fun μ _ => abs_nonneg _)
            (pair_len_le hjk hnw hpd hy z.2 z'.2) 2
  have hcard := card_le_good (P := P) hjk hN hnw hpd
  rw [← hs] at hcard
  set C1 : ℝ := c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d with hC1
  have hC10 : 0 ≤ C1 := by
    have : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  calc ‖∑ z : ↥X', ∑ z' : ↥X', tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
        (EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' * w z z'‖
      ≤ ∑ z : ↥X', ∑ z' : ↥X', ‖tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
        (EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' * w z z'‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => norm_sum_le _ _)
    _ ≤ ∑ z : ↥X', ∑ z' : ↥X', (4 * M / ρ ^ 2) * (Lb * (1 + s)) ^ 2 := by
        refine Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun z' _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hT z z') ((hw z z').trans (hlen z z')) (norm_nonneg _) (by positivity)
    _ = (X'.card : ℝ) ^ 2 * ((4 * M / ρ ^ 2) * (Lb * (1 + s)) ^ 2) := by
        simp [Finset.sum_const]; ring
    _ ≤ (C1 * (1 + s)) ^ 2 * ((4 * M / ρ ^ 2) * (Lb * (1 + s)) ^ 2) := by
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) (by positivity)
    _ = momC (d := d) L m₁ P ρ y * ((1 + s) ^ 4 * Real.exp (-P.κ * s)) := by
        unfold momC
        rw [← hC1, ← hLb, hM]
        ring

end Torus

section Lim

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

variable (P β ν a Tm j) in
/-- **The second moment of the cut-off term of `T∞` through the centre `y`**:
`∑_{x,x' ∈ X'} B_{X'}^{(y)}(x,x') |x - x'|²`, with the tensor of the term `GE` at the centre `y`. -/
noncomputable def MomY (i₀ i₁ : Fin N) (y : Site d) (X' : Finset (Site d)) : ℂ :=
  ∑ z : ↥X', ∑ z' : ↥X', tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
    (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' * (∑ μ, (((z.1 μ - z'.1 μ : ℤ) : ℂ)) ^ 2)

variable (P ν Tm j) in
/-- The second-moment contribution of the shape `X'` through `y` on the `n`-th torus. -/
noncomputable def MomN (i₀ i₁ : Fin N) (y : Site d) (n : ℕ) (X' : Finset (Site d)) : ℂ :=
  haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  ∑ z : ↥X', ∑ z' : ↥X', tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
    (EauxC (Tm (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) y X') z z' *
    (liftSq L j (ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z.1 -
      ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z'.1) : ℂ)

theorem MomY_eq_zero {i₀ i₁ : Fin N} {y : Site d} {X' : Finset (Site d)}
    (h : ¬ (InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' ∧ y ∈ X')) :
    MomY P β ν a Tm j i₀ i₁ y X' = 0 := by
  unfold MomY
  refine Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun z' _ => ?_
  have : GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' = fun _ => 0 :=
    funext fun c => GE_eq_zero h _ c
  simp [tensB, D2, this]

section LimF

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N}
include hF hn

/-- On a good torus the tensor of `GE` is that of the centre-`y` class term. -/
theorem tensB_GE_eq_EauxC {y : Site d} {X' : Finset (Site d)} (hy : y ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') {n : ℕ}
    (hgood : GoodAt L m₁ k P.m₀ j X' n) (z z' : ↥X') :
    tensB i₀ i₁ (nuIdeal L k (ν k) j) X' (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' =
      tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
        (EauxC (Tm (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) y X') z z' := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have ctx := hF.ctxSeq hn i₀ n
  have hρ0 := ctx.rho_pos
  unfold tensB
  refine D2_congr_slice (GE_analyticAt hF hn hX hy (mem_ball_self hρ0))
    (ctx.analyticAt_EauxC i₀ hgood.2 y hgood.1 hy (mem_ball_self hρ0))
    (δ := liftRadius d L N P j / 2) (by linarith) fun s t hs ht => ?_
  set c : Cfg d N X' := refPt i₀ (nuIdeal L k (ν k) j) X' +
    s • (Pi.single (Sum.inl (z, i₁)) 1 : Cfg d N X') +
    t • (Pi.single (Sum.inl (z', i₁)) 1 : Cfg d N X') with hc
  have hcb : c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') (liftRadius d L N P j) := by
    rw [mem_ball, dist_eq_norm, hc, add_assoc, add_sub_cancel_left]
    refine lt_of_le_of_lt (norm_add_le _ _) ?_
    have e1 := norm_single_one_le (Sum.inl (z, i₁) : Idx d N X')
    have e2 := norm_single_one_le (Sum.inl (z', i₁) : Idx d N X')
    rw [norm_smul, norm_smul]
    nlinarith [norm_nonneg s, norm_nonneg t]
  exact GE_eq_EauxC hF hn hX hy hcb hgood

omit hn in
theorem momC_nonneg (y : Site d) : 0 ≤ momC (d := d) L m₁ P (liftRadius d L N P j) y := by
  have hE0 := hF.admissible.E₀_nonneg
  unfold momC
  have : 0 ≤ c1 d L := by unfold c1; positivity
  have h4 : 0 ≤ 4 * P.E₀ / liftRadius d L N P j ^ 2 := by positivity
  positivity

/-- **The bound of the contribution of a good shape on a torus.** -/
theorem MomN_bound {y : Site d} {n : ℕ} {X' : Finset (Site d)} (hy : y ∈ X')
    (hgood : GoodAt L m₁ k P.m₀ j X' n) :
    ‖MomN P ν Tm j i₀ i₁ y n X'‖ ≤
      (momC (d := d) L m₁ P (liftRadius d L N P j) y * (24 * Real.exp 1)) *
        Real.exp (-(P.κ - 1) * sizeSeq L m₁ k P.m₀ j X' n) := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have ctx := hF.ctxSeq hn i₀ n
  have hE0 := hF.admissible.E₀_nonneg
  have h := ctx.norm_mom_torus_le (torusSeq_dvd P.m₀ n) hE0 (i₀ := i₀) (i₁ := i₁) hgood.1 hgood.2 hy
    (fun z z' => (liftSq L j (ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z.1 -
      ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z'.1) : ℂ))
    (fun z z' => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun μ _ => sq_nonneg _)]
      exact liftSq_ibase_sub_le z.1 z'.1)
  unfold MomN
  refine h.trans ?_
  have hs0 : 0 ≤ sizeSeq L m₁ k P.m₀ j X' n := sizeSeq_nonneg P.m₀ j X' n
  have hp := poly_exp_tail' (κ := P.κ) hs0
  have hC := momC_nonneg hF (y := y) (L := L) (m₁ := m₁) (j := j)
  calc _ ≤ momC (d := d) L m₁ P (liftRadius d L N P j) y *
        (24 * Real.exp 1 * Real.exp (-(P.κ - 1) * sizeSeq L m₁ k P.m₀ j X' n)) :=
        mul_le_mul_of_nonneg_left hp hC
    _ = _ := by ring

/-- **The bound of the second moment of a polymer of `T∞` through `y`.** -/
theorem MomY_bound {y : Site d} {X' : Finset (Site d)} (hy : y ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') :
    ‖MomY P β ν a Tm j i₀ i₁ y X'‖ ≤
      (momC (d := d) L m₁ P (liftRadius d L N P j) y * (24 * Real.exp 1)) *
        Real.exp (-(P.κ - 1) * dInf L m₁ k P.m₀ j X') := by
  obtain ⟨n₀, hn₀⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  have hE0 := hF.admissible.E₀_nonneg
  refine bound_dInf hn₀ (norm_nonneg _) (by linarith [hn.hκ, aEnt_nonneg d L]) fun n hgood => ?_
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have ctx := hF.ctxSeq hn i₀ n
  have h := ctx.norm_mom_torus_le (torusSeq_dvd P.m₀ n) hE0 (i₀ := i₀) (i₁ := i₁) hgood.1 hgood.2 hy
    (fun z z' => ∑ μ, (((z.1 μ - z'.1 μ : ℤ) : ℂ)) ^ 2)
    (fun z z' => by
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun μ _ => ?_))
      rw [norm_pow, Complex.norm_intCast, sq_abs])
  have heq : MomY P β ν a Tm j i₀ i₁ y X' = ∑ z : ↥X', ∑ z' : ↥X', tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
      (EauxC (Tm (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) y X') z z' *
      (∑ μ, (((z.1 μ - z'.1 μ : ℤ) : ℂ)) ^ 2) := by
    unfold MomY
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
    rw [tensB_GE_eq_EauxC hF hn hy hX hgood z z']
  rw [heq]
  refine h.trans ?_
  have hs0 : 0 ≤ sizeSeq L m₁ k P.m₀ j X' n := sizeSeq_nonneg P.m₀ j X' n
  have hp := poly_exp_tail' (κ := P.κ) hs0
  have hC := momC_nonneg hF (y := y) (L := L) (m₁ := m₁) (j := j)
  calc _ ≤ momC (d := d) L m₁ P (liftRadius d L N P j) y *
        (24 * Real.exp 1 * Real.exp (-(P.κ - 1) * sizeSeq L m₁ k P.m₀ j X' n)) :=
        mul_le_mul_of_nonneg_left hp hC
    _ = _ := by ring

/-- On a good small torus the two contributions agree. -/
theorem MomN_eq_MomY {y : Site d} {n : ℕ} {X' : Finset (Site d)} (hy : y ∈ X')
    (hgood : GoodAt L m₁ k P.m₀ j X' n)
    (hsz : sizeSeq L m₁ k P.m₀ j X' n < tauY d L m₁ k P.m₀ j n y) :
    MomN P ν Tm j i₀ i₁ y n X' = MomY P β ν a Tm j i₀ i₁ y X' := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have hX := infPoly_of_small hn.hjk hy hgood hsz
  have hsmall := small_coords_of_tauY hn.hjk hy hgood hsz
  unfold MomN MomY
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
  rw [tensB_GE_eq_EauxC hF hn hy hX hgood z z']
  congr 1
  rw [liftSq_ibase_sub (fun μ => by
      have h1 := hsmall z.1 z.2 μ
      have h2 := hsmall z'.1 z'.2 μ
      have h3 := abs_nonneg (z.1 μ)
      have h4 := abs_nonneg (z'.1 μ)
      have h5 : |z.1 μ - z'.1 μ| ≤ |z.1 μ| + |z'.1 μ| := abs_sub _ _
      have h6 : (0 : ℤ) ≤ ((L * L ^ (P.m₀ + m₁) : ℕ) : ℤ) := Int.natCast_nonneg _
      omega) hn.hjk]
  push_cast
  rfl

/-- **The second moment of `T∞` through every centre vanishes** (CLASS-RULINGS Q-B, Q-C (2), at an
arbitrary centre `y`): the sum of the pair sums `MomY y X'` over the polymers of `T∞` through `y` is
the limit of the second-moment sums `momentSum` of the tori, which tend to `0` by the thermodynamic
condition `RenormCond.moment`. -/
theorem momY_tsum_zero (hne : i₁ ≠ i₀) (y : Site d) :
    ∑' X' : Finset (Site d), MomY P β ν a Tm j i₀ i₁ y X' = 0 := by
  have hC : 0 ≤ momC (d := d) L m₁ P (liftRadius d L N P j) y * (24 * Real.exp 1) := by
    have := momC_nonneg hF (y := y) (L := L) (m₁ := m₁) (j := j)
    positivity
  have hlim := tendsto_shapeSum (L := L) (m₁ := m₁) (k := k) (m₀ := P.m₀) (j := j) hn.hjk
    (κ := P.κ - 1) (by linarith [hn.hκ, aEnt_nonneg d L]) y (MomN P ν Tm j i₀ i₁ y)
    (MomY P β ν a Tm j i₀ i₁ y) hC
    (fun n X' hy hgood hsz => MomN_eq_MomY hF hn hy hgood hsz)
    (fun n X' hy hgood => MomN_bound hF hn hy hgood)
    (fun X' hy hX => MomY_bound hF hn hy hX)
    (fun X' h => MomY_eq_zero (fun h' => h ⟨h'.2, h'.1⟩))
  have hev : ∀ᶠ n in atTop, ∑ᶠ X' ∈ ShAt (d := d) L m₁ k P.m₀ j y n, MomN P ν Tm j i₀ i₁ y n X' =
      momentSeq Tm P j i₀ i₁ n := by
    filter_upwards [eventually_unlift_blockPt (L := L) (m₁ := m₁) (k := k) hn.hjk P.m₀ y] with n hn'
    have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
    have ctx := hF.ctxSeq hn i₀ n
    exact (ctx.momentSum_shapes_centre (torusSeq_dvd P.m₀ n) (i₀ := i₀) (i₁ := i₁) y hn').symm
  have hmom := (hF.renorm j hn.hj1 hn.hjk).moment i₀ i₁ hne.symm
  have hφ : Tendsto (fun n : ℕ => torusSeq L P.m₀ n - 1) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_id
    have := succ_le_torusSeq (L := L) P.m₀ n
    simp only [id]; omega
  have hcomp := hmom.comp hφ
  have hsub : Tendsto (momentSeq Tm P j i₀ i₁) atTop (nhds 0) := by
    refine hcomp.congr fun n => ?_
    have h1 : torusSeq L P.m₀ n - 1 + 1 = torusSeq L P.m₀ n := by
      have := succ_le_torusSeq (L := L) P.m₀ n; omega
    have : NeZero (torusSeq L P.m₀ n - 1 + 1) := ⟨Nat.succ_ne_zero _⟩
    have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
    simp only [Function.comp, momentSeq]
    exact momentSum_congr h1
  exact tendsto_nhds_unique hlim (hsub.congr' (hev.mono fun n h => h.symm))

end LimF

end Lim

end Balaban.SmallField.Def6
