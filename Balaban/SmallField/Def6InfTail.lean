/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6InfExpand

/-!
# Def-6: the tail lemma of CLASS-RULINGS Q-C (2)

On the `n`-th torus of the sequence the polymers (shapes `X'` of `liftPolys`) split into the *small*
ones (`SmallAt`: the covering size is below a threshold that grows with the torus) and the others.

* `goodAt_of_small`: a small good shape is good on every later torus (transfer, `Def6InfPoly`);
* `Sn_eq_Sinf`: on a torus on which the shape is good and small, its contribution `Sn` to the second
  moment is the contribution `Sinf` of the infinite-volume family (`liftSq_ibase_sub`: the wrapped
  squared norm of a difference of small block positions is the squared norm in `ℤ^d`);
* `norm_SnSeq_le`, `norm_tailAt_le`, `tendsto_tailAt`: the shapes that are not small contribute at most
  `C K0 e^{-τ_n}` to the second moment (the covering length of such a polymer is at least
  `τ_n ≍ R_n / M`, and the counting (G2) controls the number of polymers), so the contribution tends to
  `0`;
* `norm_moment_term_le`: the contribution of one polymer of a family satisfying the analytic
  premises is bounded by the counting weight.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Metric Set

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem valMinAbs_intCast_of_small {n : ℕ} [NeZero n] {w : ℤ} (hw : 2 * |w| < n) :
    ZMod.valMinAbs ((w : ℤ) : ZMod n) = w := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  have := abs_lt.1 (show |w * 2| < n by rw [abs_mul]; simp; omega)
  rw [Set.mem_Ioc]
  omega

/-- **The wrapped squared norm of a difference of two small block positions is the squared norm
in `ℤ^d`.** -/
theorem liftSq_ibase_sub {j : ℕ} {z z' : Fin d → ℤ}
    (h : ∀ μ, 2 * |z μ - z' μ| < ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ)) (hjk : j ≤ k) :
    liftSq L j (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z -
      ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z') =
      ∑ μ, (((z μ - z' μ : ℤ) : ℝ)) ^ 2 := by
  have : NeZero (N₁ * L ^ m₁ * L ^ k) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  unfold liftSq
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hp : 0 < L ^ j := pow_pos (NeZero.pos L) j
  have hf : ((N₁ * L ^ m₁ * L ^ k : ℕ) : ℤ) = ((L ^ j : ℕ) : ℤ) * ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
    exact_mod_cast side_eq hjk
  have hpz : (0 : ℤ) < ((L ^ j : ℕ) : ℤ) := by exact_mod_cast hp
  have e1 : (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z -
      ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z') μ =
      ((((L ^ j : ℕ) : ℤ) * (z μ - z' μ) : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ k)) := by
    simp only [ibase, Pi.sub_apply]; push_cast; ring
  have e2 : 2 * |((L ^ j : ℕ) : ℤ) * (z μ - z' μ)| < ((N₁ * L ^ m₁ * L ^ k : ℕ) : ℤ) := by
    rw [abs_mul, abs_of_pos hpz, hf]
    have := h μ
    nlinarith
  rw [e1, valMinAbs_intCast_of_small e2]
  push_cast
  have hL0 : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  have hL : ((L : ℝ) ^ j) ≠ 0 := by positivity
  congr 1
  field_simp


section Small

omit [NeZero L] in
theorem torusSeq_mono (m₀ : ℕ) {n n' : ℕ} (h : n ≤ n') : torusSeq L m₀ n ≤ torusSeq L m₀ n' := by
  unfold torusSeq
  exact Nat.mul_le_mul_left _ (by omega)

/-- **A good shape that is small on one torus is good on every later torus.** -/
theorem goodAt_of_small {m₀ j : ℕ} (hjk : j ≤ k) {X' : Finset (Fin d → ℤ)} {n n' : ℕ}
    (hn : GoodAt L m₁ k m₀ j X' n)
    (hs : ∀ z ∈ X', ∀ μ, 4 * (|z μ| + ((L * L ^ (m₀ + m₁) : ℕ) : ℤ) + 1) <
      ((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ)) (hnn : n ≤ n') :
    GoodAt L m₁ k m₀ j X' n' := by
  have : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
  have : NeZero (torusSeq L m₀ n') := ⟨torusSeq_ne_zero m₀ n'⟩
  have hmono : torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) ≤ torusSeq L m₀ n' * L ^ m₁ * L ^ (k - j) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (torusSeq_mono m₀ hnn))
  have hmz : ((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) ≤
      ((torusSeq L m₀ n' * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by exact_mod_cast hmono
  have hQ : (0 : ℤ) ≤ ((L * L ^ (m₀ + m₁) : ℕ) : ℤ) := Int.natCast_nonneg _
  have hpos : NeZero (torusSeq L m₀ n' * L ^ m₁ * L ^ (k - j)) := ⟨by
    have := torusSeq_ne_zero (L := L) m₀ n'
    have := NeZero.pos L
    positivity⟩
  refine ⟨?_, ?_⟩
  · intro z hz μ
    have h1 := hs z hz μ
    have h2 : 2 * |z μ| < ((torusSeq L m₀ n' * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
      have := abs_nonneg (z μ); omega
    exact valMinAbs_intCast_of_small h2
  · exact isPolyDom_transfer hjk (torusSeq_dvd m₀ n) (torusSeq_dvd m₀ n')
      (fun z hz μ => by have := hs z hz μ; omega)
      (fun z hz μ => by
        have := hs z hz μ
        have h3 := abs_nonneg (z μ)
        simp only [Nat.cast_zero]
        omega) hn.2

end Small


section SumDefs

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

/-- **The contribution of a polymer of `T∞` to the second moment** (the summand of
`SumConds.moment`). -/
noncomputable def Sinf (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (P : Consts) (j : ℕ)
    (i₀ i₁ : Fin N) (νj ρ : ℝ) (X' : Finset (Fin d → ℤ)) : ℂ :=
  ∑ z : ↥X', ∑ z' : ↥X', tensB i₀ i₁ νj X' (termLInf Tm P.m₀ j i₀ νj ρ X') z z' *
    (∑ μ, (((z.1 μ - z'.1 μ : ℤ) : ℂ)) ^ 2)

/-- **The contribution of a shape to the second moment of the `N₁`-torus**. -/
noncomputable def Sn {N₁ : ℕ} [NeZero N₁] (Tm : Terms d L N₁ m₁ k N ϱ) (j : ℕ) (i₀ i₁ : Fin N)
    (νj ρ : ℝ) (X' : Finset (Fin d → ℤ)) : ℂ :=
  ∑ z : ↥X', ∑ z' : ↥X', tensB i₀ i₁ νj X' (termL Tm j i₀ νj ρ X') z z' *
    (liftSq L j (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z.1 -
      ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z'.1) : ℂ)

/-- The contribution of a shape to the second moment of the `n`-th torus of the sequence. -/
noncomputable def SnSeq (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (P : Consts) (j : ℕ)
    (i₀ i₁ : Fin N) (νj ρ : ℝ) (n : ℕ) (X' : Finset (Fin d → ℤ)) : ℂ :=
  haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  Sn (Tm (torusSeq L P.m₀ n)) j i₀ i₁ νj ρ X'

/-- On a torus on which the polymer is good and small, the two contributions agree. -/
theorem Sn_eq_Sinf (hF : IsSFFamily P β ν a Tm ρd Ek) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {i₀ : Fin N} {X' : Finset (Fin d → ℤ)} (h0 : (0 : Fin d → ℤ) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') {n : ℕ}
    (hn : GoodAt L m₁ k P.m₀ j X' n) (i₁ : Fin N) (νj ρ : ℝ)
    (hs : ∀ z ∈ X', ∀ μ, 4 * (|z μ| + ((L * L ^ (P.m₀ + m₁) : ℕ) : ℤ) + 1) <
      ((torusSeq L P.m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ)) :
    SnSeq Tm P j i₀ i₁ νj ρ n X' = Sinf Tm P j i₀ i₁ νj ρ X' := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  unfold SnSeq Sn Sinf
  have heq : termLInf Tm P.m₀ j i₀ νj ρ X' =
      termL (Tm (torusSeq L P.m₀ n)) j i₀ νj ρ X' :=
    funext fun c => termLInf_eq hF.torusIndep hj1 hjk i₀ νj ρ h0 hX (torusSeq L P.m₀ n) hn.1 hn.2 c
  rw [heq]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
  congr 1
  rw [liftSq_ibase_sub (fun μ => by
      have h1 := hs z.1 z.2 μ
      have h2 := hs z'.1 z'.2 μ
      have h3 := abs_nonneg (z.1 μ)
      have h4 := abs_nonneg (z'.1 μ)
      have h5 : |z.1 μ - z'.1 μ| ≤ |z.1 μ| + |z'.1 μ| := abs_sub _ _
      have h6 : (0 : ℤ) ≤ ((L * L ^ (P.m₀ + m₁) : ℕ) : ℤ) := Int.natCast_nonneg _
      omega) hjk]
  push_cast
  rfl

end SumDefs


section Bounds

variable {d N : ℕ} {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)}

theorem PremisesCore.norm_tensB_le (hP : PremisesCore T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ)
    {X : Finset (Site d)} (hX : X ∈ T.polys) (z z' : ↥X) :
    ‖tensB i₀ i₁ ν X (T.term X) z z'‖ ≤ 4 * (E₀ * Real.exp (-κ * T.dist X)) / ρ ^ 2 := by
  have hana : AnalyticOnNhd ℂ (T.term X) (ball (refPt i₀ ν X) ρ) :=
    (hP.analytic X hX).mono (ball_subset_tube i₀ ν ρ X)
  have hM : ∀ y ∈ ball (refPt i₀ ν X) ρ, ‖T.term X y‖ ≤ E₀ * Real.exp (-κ * T.dist X) :=
    fun y hy => hP.bdd_tube X hX y (ball_subset_tube i₀ ν ρ X hy)
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X) :=
    le_trans (norm_nonneg _) (hM _ (mem_ball_self hρ))
  have h := norm_D2_le hρ hana hM (Pi.single (Sum.inl (z, i₁)) (1 : ℂ) : Cfg d N X)
    (Pi.single (Sum.inl (z', i₁)) (1 : ℂ) : Cfg d N X)
  have h1 := norm_single_one_le (Sum.inl (z, i₁) : Idx d N X)
  have h2 := norm_single_one_le (Sum.inl (z', i₁) : Idx d N X)
  unfold tensB
  refine h.trans ?_
  rw [div_le_div_iff_of_pos_right (by positivity)]
  nlinarith [mul_nonneg hM0 (norm_nonneg (Pi.single (Sum.inl (z, i₁)) (1 : ℂ) : Cfg d N X)),
    mul_le_mul h1 h2 (norm_nonneg _) zero_le_one]

/-- The contribution of one polymer to the second moment is bounded by the counting weight. -/
theorem PremisesCore.norm_moment_term_le (hP : PremisesCore T i₀ i₁ ν ρ E₀ κ A K₀ Dom)
    (hρ : 0 < ρ) (hE0 : 0 ≤ E₀) {X : Finset (Site d)} (hX : X ∈ T.polys) :
    ‖∑ z : ↥X, ∑ z' : ↥X, tensB i₀ i₁ ν X (T.term X) z z' *
        (∑ μ, (((z.1 μ - z'.1 μ : ℤ) : ℂ)) ^ 2)‖ ≤
      (16 * A ^ 2 * E₀ / ρ ^ 2) * wt κ X (T.dist X) := by
  have hd0 := hP.dist_nonneg X hX
  have hcard : 1 ≤ X.card := Finset.card_pos.mpr ⟨0, hP.zero_mem X hX⟩
  have hA0 : 0 ≤ A := by
    have h0 := hP.diam X hX 0 (hP.zero_mem X hX)
    simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero, Int.cast_zero] at h0
    by_contra hneg
    push Not at hneg
    nlinarith [mul_nonneg (le_refl (0:ℝ)) hd0]
  -- pairwise bound
  have hpair : ∀ z z' : ↥X, ‖tensB i₀ i₁ ν X (T.term X) z z' *
      (∑ μ, (((z.1 μ - z'.1 μ : ℤ) : ℂ)) ^ 2)‖ ≤
      (4 * (E₀ * Real.exp (-κ * T.dist X)) / ρ ^ 2) * (2 * (A * (1 + T.dist X))) ^ 2 := by
    intro z z'
    rw [norm_mul]
    have hs : ‖∑ μ, (((z.1 μ - z'.1 μ : ℤ) : ℂ)) ^ 2‖ ≤ (2 * (A * (1 + T.dist X))) ^ 2 := by
      calc ‖∑ μ, (((z.1 μ - z'.1 μ : ℤ) : ℂ)) ^ 2‖
          ≤ ∑ μ, ‖(((z.1 μ - z'.1 μ : ℤ) : ℂ)) ^ 2‖ := norm_sum_le _ _
        _ = ∑ μ, (|((z.1 μ - z'.1 μ : ℤ) : ℝ)|) ^ 2 := by
            refine Finset.sum_congr rfl fun μ _ => ?_
            rw [norm_pow]; congr 1
            rw [show (((z.1 μ - z'.1 μ : ℤ) : ℂ)) = (((z.1 μ - z'.1 μ : ℤ) : ℝ) : ℂ) by push_cast; rfl,
              Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (∑ μ, |((z.1 μ - z'.1 μ : ℤ) : ℝ)|) ^ 2 :=
            Finset.sum_sq_le_sq_sum_of_nonneg fun μ _ => abs_nonneg _
        _ ≤ (2 * (A * (1 + T.dist X))) ^ 2 := by
            have e1 := hP.diam X hX z.1 z.2
            have e2 := hP.diam X hX z'.1 z'.2
            have e3 : ∑ μ, |((z.1 μ - z'.1 μ : ℤ) : ℝ)| ≤
                ((∑ μ, |z.1 μ| : ℤ) : ℝ) + ((∑ μ, |z'.1 μ| : ℤ) : ℝ) := by
              push_cast
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_le_sum fun μ _ => ?_
              exact abs_sub _ _ |>.trans (by simp)
            have e4 : 0 ≤ ∑ μ, |((z.1 μ - z'.1 μ : ℤ) : ℝ)| :=
              Finset.sum_nonneg fun μ _ => abs_nonneg _
            exact pow_le_pow_left₀ e4 (by linarith) 2
    have ht := hP.norm_tensB_le (i₁ := i₁) hρ hX z z'
    exact mul_le_mul ht hs (norm_nonneg _) (by positivity)
  calc _ ≤ ∑ z : ↥X, ∑ z' : ↥X, ‖tensB i₀ i₁ ν X (T.term X) z z' *
        (∑ μ, (((z.1 μ - z'.1 μ : ℤ) : ℂ)) ^ 2)‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => norm_sum_le _ _)
    _ ≤ ∑ z : ↥X, ∑ z' : ↥X, (4 * (E₀ * Real.exp (-κ * T.dist X)) / ρ ^ 2) *
        (2 * (A * (1 + T.dist X))) ^ 2 :=
        Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun z' _ => hpair z z'
    _ = (X.card : ℝ) ^ 2 * ((4 * (E₀ * Real.exp (-κ * T.dist X)) / ρ ^ 2) *
        (2 * (A * (1 + T.dist X))) ^ 2) := by
        simp [Finset.sum_const]; ring
    _ ≤ (16 * A ^ 2 * E₀ / ρ ^ 2) * wt κ X (T.dist X) := by
        have hw := wt_ge (κ := κ) X hd0 hcard 2 2 le_rfl (by norm_num)
        have hρ2 : 0 < ρ ^ 2 := by positivity
        calc (X.card : ℝ) ^ 2 * ((4 * (E₀ * Real.exp (-κ * T.dist X)) / ρ ^ 2) *
              (2 * (A * (1 + T.dist X))) ^ 2)
            = (16 * A ^ 2 * E₀ / ρ ^ 2) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 2 *
                Real.exp (-κ * T.dist X)) := by ring
          _ ≤ (16 * A ^ 2 * E₀ / ρ ^ 2) * wt κ X (T.dist X) :=
              mul_le_mul_of_nonneg_left hw (by positivity)

end Bounds


section Tail

theorem poly_exp_tail {s τ κ κ₀ : ℝ} (hs : 0 ≤ s) (hτ : τ ≤ s) (hκ : κ₀ + 2 ≤ κ) :
    (1 + s) ^ 4 * Real.exp (-κ * s) ≤ 24 * Real.exp 1 * Real.exp (-τ) * Real.exp (-κ₀ * s) := by
  have hpow : (1 + s) ^ 4 ≤ 24 * Real.exp (1 + s) := by
    have := Real.pow_div_factorial_le_exp (1 + s) (by linarith) 4
    rw [div_le_iff₀ (by norm_num)] at this
    norm_num [Nat.factorial] at this
    linarith
  have e1 : Real.exp (1 + s) * Real.exp (-κ * s) =
      Real.exp 1 * Real.exp (-κ₀ * s) * Real.exp (-((κ - 1 - κ₀) * s)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-((κ - 1 - κ₀) * s)) ≤ Real.exp (-τ) := by
    apply Real.exp_le_exp.2; nlinarith
  calc (1 + s) ^ 4 * Real.exp (-κ * s) ≤ 24 * Real.exp (1 + s) * Real.exp (-κ * s) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = 24 * (Real.exp 1 * Real.exp (-κ₀ * s) * Real.exp (-((κ - 1 - κ₀) * s))) := by
        rw [mul_assoc, e1]
    _ ≤ 24 * (Real.exp 1 * Real.exp (-κ₀ * s) * Real.exp (-τ)) := by
        gcongr
    _ = 24 * Real.exp 1 * Real.exp (-τ) * Real.exp (-κ₀ * s) := by ring

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

theorem liftSq_le {j : ℕ} (hjk : j ≤ k) (x : CTorus d L N₁ m₁ k) :
    liftSq L j x ≤ d * (((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) / 2) ^ 2 := by
  have : NeZero (N₁ * L ^ m₁ * L ^ k) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  have hL0 : (0 : ℝ) < (L : ℝ) ^ j := by
    have : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
    positivity
  have hf : ((N₁ * L ^ m₁ * L ^ k : ℕ) : ℝ) =
      (L : ℝ) ^ j * ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) := by
    exact_mod_cast side_eq hjk
  unfold liftSq
  calc ∑ μ, ((ZMod.valMinAbs (x μ) : ℝ) / (L : ℝ) ^ j) ^ 2
      ≤ ∑ _μ : Fin d, (((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) / 2) ^ 2 := by
        refine Finset.sum_le_sum fun μ _ => ?_
        have h1 : ((ZMod.valMinAbs (x μ)).natAbs : ℝ) ≤ ((N₁ * L ^ m₁ * L ^ k : ℕ) : ℝ) / 2 := by
          have := ZMod.natAbs_valMinAbs_le (x μ)
          calc ((ZMod.valMinAbs (x μ)).natAbs : ℝ) ≤ ((N₁ * L ^ m₁ * L ^ k / 2 : ℕ) : ℝ) := by
                exact_mod_cast this
            _ ≤ ((N₁ * L ^ m₁ * L ^ k : ℕ) : ℝ) / 2 := Nat.cast_div_le
        have h2 : |(ZMod.valMinAbs (x μ) : ℝ)| ≤ ((N₁ * L ^ m₁ * L ^ k : ℕ) : ℝ) / 2 := by
          have : |(ZMod.valMinAbs (x μ) : ℝ)| = ((ZMod.valMinAbs (x μ)).natAbs : ℝ) := by
            rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
          rw [this]; exact h1
        rw [← sq_abs, abs_div, abs_of_pos hL0]
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        rw [div_le_iff₀ hL0]
        rw [hf] at h2
        linarith
    _ = d * (((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) / 2) ^ 2 := by simp


end Tail

section Seq

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

variable (L m₁ k) in
/-- The shapes `liftPolys` of the `n`-th torus of the sequence. -/
noncomputable def shapesAt (P : Consts) (j n : ℕ) : Finset (Finset (Fin d → ℤ)) :=
  haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  (liftPolys_finite (d := d) (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) P j).toFinset

theorem mem_shapesAt {P : Consts} {j n : ℕ} {X' : Finset (Fin d → ℤ)} :
    X' ∈ shapesAt L m₁ k P j n ↔ (0 : Fin d → ℤ) ∈ X' ∧ GoodAt L m₁ k P.m₀ j X' n := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  unfold shapesAt
  rw [Set.Finite.mem_toFinset]
  rfl

variable (L m₁ k) in
/-- The covering size threshold below which a shape is "small" relative to the `n`-th torus. -/
def SmallAt (P : Consts) (j : ℕ) (X' : Finset (Fin d → ℤ)) (n : ℕ) : Prop :=
  4 * (diamA d L P.m₀ m₁ * (1 + sizeSeq L m₁ k P.m₀ j X' n) + ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
    ((torusSeq L P.m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ)


theorem zsmall_of_smallAt {P : Consts} {j n : ℕ} (hjk : j ≤ k) {X' : Finset (Fin d → ℤ)}
    (hX : X' ∈ shapesAt L m₁ k P j n) (hs : SmallAt L m₁ k P j X' n) :
    ∀ z ∈ X', ∀ μ, 4 * (|z μ| + ((L * L ^ (P.m₀ + m₁) : ℕ) : ℤ) + 1) <
      ((torusSeq L P.m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have hmem := mem_shapesAt.1 hX
  have hlp : X' ∈ liftPolys (d := d) (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) P j :=
    ⟨hmem.1, hmem.2.1, hmem.2.2⟩
  intro z hz μ
  have h1 := liftPolys_diam hjk hlp hz
  have h2 : (|z μ| : ℤ) ≤ ∑ ν, |z ν| := Finset.single_le_sum (f := fun ν => |z ν|)
    (fun ν _ => abs_nonneg _) (Finset.mem_univ μ)
  have h3 : ((|z μ| : ℤ) : ℝ) ≤ diamA d L P.m₀ m₁ * (1 + sizeSeq L m₁ k P.m₀ j X' n) := by
    refine le_trans (by exact_mod_cast h2) h1
  unfold SmallAt at hs
  have h4 : (4 : ℝ) * ((|z μ| : ℤ) + ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((torusSeq L P.m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) := by linarith
  exact_mod_cast h4


variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

variable (d L m₁ k) in
/-- The lower bound of the covering size of a shape that is not small on the `n`-th torus. -/
noncomputable def tauAt (P : Consts) (j n : ℕ) : ℝ :=
  (((torusSeq L P.m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) - 4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4) /
      (4 * diamA d L P.m₀ m₁) - 1

variable (d L m₁) in
/-- The constant of the tail estimate. -/
noncomputable def tailConst (P : Consts) (ρ : ℝ) : ℝ :=
  (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * d *
    (4 * diamA d L P.m₀ m₁ + 4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 4) ^ 2 * P.E₀ / ρ ^ 2 *
    (24 * Real.exp 1)

omit [NeZero L] in
theorem diamA_pos (hd : 0 < d) (hL : 0 < L) (m₀ m₁ : ℕ) : 0 < diamA d L m₀ m₁ := by
  unfold diamA
  have : (0 : ℝ) < d := by exact_mod_cast hd
  have : (0 : ℝ) < L := by exact_mod_cast hL
  positivity


/-- The numerical conditions on the parameters used by the bridge. -/
structure MomNum (d L N k j : ℕ) [NeZero L] (ϱ : ℝ) (P : Consts) : Prop where
  hd : 3 ≤ d
  hL : 3 ≤ L
  hϱ : bgR0 d L ≤ ϱ
  hκ : aEnt d L + 3 ≤ P.κ
  hj1 : 1 ≤ j
  hjk : j ≤ k
  hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N)

/-- **The tail estimate for one shape**: a shape that is not small on the `n`-th torus contributes
at most `C e^{-τ_n} e^{-κ₀ d_j}` to the second moment of that torus. -/
theorem norm_SnSeq_le (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) (n : ℕ) {X' : Finset (Fin d → ℤ)}
    (hX : X' ∈ shapesAt L m₁ k P j n) (hns : ¬ SmallAt L m₁ k P j X' n) :
    ‖SnSeq Tm P j i₀ i₁ (nuIdeal L k (ν k) j) (liftRadius d L N P j) n X'‖ ≤
      tailConst d L m₁ P (liftRadius d L N P j) * Real.exp (-tauAt d L m₁ k P j n) *
        Real.exp (-(aEnt d L + 1) * sizeSeq L m₁ k P.m₀ j X' n) := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have hmem := mem_shapesAt.1 hX
  have hlp : X' ∈ liftPolys (d := d) (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) P j :=
    ⟨hmem.1, hmem.2.1, hmem.2.2⟩
  have hPn := hF.premisesCore (torusSeq L P.m₀ n) (torusSeq_dvd P.m₀ n) hn.hd hn.hL hn.hϱ hn.hκ
    hn.hj1 hn.hjk hn.hsmall hne
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  set ρ := liftRadius d L N P j with hρ
  set νj := nuIdeal L k (ν k) j with hνj
  set s := sizeSeq L m₁ k P.m₀ j X' n with hs
  have hs0 : 0 ≤ s := sizeSeq_nonneg P.m₀ j X' n
  have hA : 0 < diamA d L P.m₀ m₁ := diamA_pos (by have := hn.hd; omega) (NeZero.pos L) _ _
  set A := diamA d L P.m₀ m₁ with hAdef
  set Q : ℝ := ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) with hQ
  have hQ0 : 0 ≤ Q := Nat.cast_nonneg _
  set Rb : ℝ := ((torusSeq L P.m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) with hRb
  have hRb0 : 0 ≤ Rb := Nat.cast_nonneg _
  have hns' : Rb ≤ 4 * (A * (1 + s) + Q + 1) := by
    unfold SmallAt at hns
    exact not_lt.1 hns
  -- per pair bound
  have hpair : ∀ z z' : ↥X', ‖tensB i₀ i₁ νj X' (termL (Tm (torusSeq L P.m₀ n)) j i₀ νj ρ X') z z' *
      (liftSq L j (ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z.1 -
        ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z'.1) : ℂ)‖ ≤
      (4 * (P.E₀ * Real.exp (-P.κ * s)) / ρ ^ 2) * (d * (Rb / 2) ^ 2) := by
    intro z z'
    rw [norm_mul]
    have h1 := hPn.norm_tensB_le (i₁ := i₁) hρ0 hlp z z'
    have h2 := liftSq_le (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) hn.hjk
      (ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z.1 -
        ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z'.1)
    have h3 : 0 ≤ liftSq L j (ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z.1 -
        ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z'.1) :=
      Finset.sum_nonneg fun μ _ => sq_nonneg _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h3]
    exact mul_le_mul h1 h2 h3 (by
      have := hF.admissible.E₀_nonneg
      positivity)
  have hcardB := liftPolys_card_le (P := P) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) hn.hjk
    (torusSeq_dvd P.m₀ n) hlp
  set C1 : ℝ := c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d with hC1
  have hC10 : 0 ≤ C1 := by
    have : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  have hcard : (X'.card : ℝ) ≤ C1 * (1 + s) := hcardB
  set B₁ : ℝ := 4 * A + 4 * Q + 4 with hB₁
  have hRbB : Rb ≤ B₁ * (1 + s) := by
    have : 4 * (A * (1 + s) + Q + 1) ≤ B₁ * (1 + s) := by
      rw [hB₁]; nlinarith [mul_nonneg hA.le hs0, mul_nonneg hQ0 hs0]
    linarith
  have hτ : tauAt d L m₁ k P j n ≤ s := by
    unfold tauAt
    rw [← hAdef, ← hQ, ← hRb]
    have h4A : 0 < 4 * A := by positivity
    have : (Rb - 4 * Q - 4) / (4 * A) ≤ 1 + s := by
      rw [div_le_iff₀ h4A]; nlinarith
    linarith
  have hE0 := hF.admissible.E₀_nonneg
  -- the sum
  calc ‖SnSeq Tm P j i₀ i₁ νj ρ n X'‖
      ≤ ∑ z : ↥X', ∑ z' : ↥X', ‖tensB i₀ i₁ νj X' (termL (Tm (torusSeq L P.m₀ n)) j i₀ νj ρ X') z z' *
        (liftSq L j (ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z.1 -
          ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z'.1) : ℂ)‖ := by
        unfold SnSeq Sn
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => norm_sum_le _ _)
    _ ≤ ∑ z : ↥X', ∑ z' : ↥X', (4 * (P.E₀ * Real.exp (-P.κ * s)) / ρ ^ 2) * (d * (Rb / 2) ^ 2) :=
        Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun z' _ => hpair z z'
    _ = (X'.card : ℝ) ^ 2 * ((4 * (P.E₀ * Real.exp (-P.κ * s)) / ρ ^ 2) * (d * (Rb / 2) ^ 2)) := by
        simp [Finset.sum_const]; ring
    _ ≤ (C1 * (1 + s)) ^ 2 * ((4 * (P.E₀ * Real.exp (-P.κ * s)) / ρ ^ 2) *
          (d * (B₁ * (1 + s) / 2) ^ 2)) := by
        have h5 : 0 ≤ (4 * (P.E₀ * Real.exp (-P.κ * s)) / ρ ^ 2) := by positivity
        have h6 : (Rb / 2) ^ 2 ≤ (B₁ * (1 + s) / 2) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 2
        have h7 : (X'.card : ℝ) ^ 2 ≤ (C1 * (1 + s)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
        have h8 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        exact mul_le_mul h7 (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h6 h8) h5)
          (by positivity) (by positivity)
    _ = (C1 ^ 2 * d * B₁ ^ 2 * P.E₀ / ρ ^ 2) * ((1 + s) ^ 4 * Real.exp (-P.κ * s)) := by ring
    _ ≤ (C1 ^ 2 * d * B₁ ^ 2 * P.E₀ / ρ ^ 2) * (24 * Real.exp 1 *
          Real.exp (-tauAt d L m₁ k P j n) * Real.exp (-(aEnt d L + 1) * s)) := by
        refine mul_le_mul_of_nonneg_left (poly_exp_tail hs0 hτ (by linarith [hn.hκ])) ?_
        positivity
    _ = tailConst d L m₁ P ρ * Real.exp (-tauAt d L m₁ k P j n) * Real.exp (-(aEnt d L + 1) * s) := by
        unfold tailConst
        ring


open Classical in
/-- The tail of the second moment of the `n`-th torus: the contribution of the shapes that are not
small. -/
noncomputable def tailAt (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (P : Consts) (j : ℕ)
    (i₀ i₁ : Fin N) (n : ℕ) : ℂ :=
  ∑ X' ∈ (shapesAt L m₁ k P j n).filter (fun X' => ¬ SmallAt L m₁ k P j X' n),
    SnSeq Tm P j i₀ i₁ (nuIdeal L k (ν k) j) (liftRadius d L N P j) n X'

theorem norm_tailAt_le (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) (n : ℕ) :
    ‖tailAt (ν := ν) Tm P j i₀ i₁ n‖ ≤
      tailConst d L m₁ P (liftRadius d L N P j) * K0 d L (aEnt d L + 1) *
        Real.exp (-tauAt d L m₁ k P j n) := by
  classical
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  set S := (shapesAt L m₁ k P j n).filter (fun X' => ¬ SmallAt L m₁ k P j X' n) with hS
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  have hC0 : 0 ≤ tailConst d L m₁ P (liftRadius d L N P j) := by
    unfold tailConst
    have := hF.admissible.E₀_nonneg
    have : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  calc ‖tailAt (ν := ν) Tm P j i₀ i₁ n‖
      ≤ ∑ X' ∈ S, ‖SnSeq Tm P j i₀ i₁ (nuIdeal L k (ν k) j) (liftRadius d L N P j) n X'‖ :=
        norm_sum_le _ _
    _ ≤ ∑ X' ∈ S, tailConst d L m₁ P (liftRadius d L N P j) * Real.exp (-tauAt d L m₁ k P j n) *
        Real.exp (-(aEnt d L + 1) * sizeSeq L m₁ k P.m₀ j X' n) :=
        Finset.sum_le_sum fun X' hX' =>
          norm_SnSeq_le hF hn hne n (Finset.mem_filter.1 hX').1 (Finset.mem_filter.1 hX').2
    _ = tailConst d L m₁ P (liftRadius d L N P j) * Real.exp (-tauAt d L m₁ k P j n) *
        ∑ X' ∈ S, Real.exp (-(aEnt d L + 1) * sizeSeq L m₁ k P.m₀ j X' n) := by
        rw [Finset.mul_sum]
    _ ≤ tailConst d L m₁ P (liftRadius d L N P j) * Real.exp (-tauAt d L m₁ k P j n) *
        K0 d L (aEnt d L + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact exp_sum_le_at (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) hn.hjk
          (torusSeq_dvd P.m₀ n) le_rfl 0 S fun X' hX' => by
            have := mem_shapesAt.1 (Finset.mem_filter.1 hX').1
            exact ⟨this.1, this.2.1, this.2.2⟩
    _ = _ := by ring

theorem tendsto_tauAt (hd : 0 < d) (P : Consts) (j : ℕ) :
    Tendsto (tauAt d L m₁ k P j) atTop atTop := by
  have hA := diamA_pos hd (NeZero.pos L) P.m₀ m₁
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1 - 4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4) /
      (4 * diamA d L P.m₀ m₁) - 1) atTop atTop := by
    have h0 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 1 - 4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4)
        atTop atTop := by
      have := tendsto_atTop_add_const_right atTop (1 - 4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4) h0
      refine this.congr fun n => ?_
      ring
    have h3 := h2.atTop_div_const (by positivity : (0 : ℝ) < 4 * diamA d L P.m₀ m₁)
    exact tendsto_atTop_add_const_right atTop (-1) h3 |>.congr fun n => by ring
  refine tendsto_atTop_mono (fun n => ?_) h1
  unfold tauAt
  have hle : (n : ℝ) + 1 ≤ ((torusSeq L P.m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) := by
    have h := succ_le_torusSeq (L := L) P.m₀ n
    have h2 : torusSeq L P.m₀ n ≤ torusSeq L P.m₀ n * L ^ m₁ * L ^ (k - j) := by
      have h1' : 1 ≤ L ^ m₁ := Nat.one_le_pow _ _ (NeZero.pos L)
      have h2' : 1 ≤ L ^ (k - j) := Nat.one_le_pow _ _ (NeZero.pos L)
      calc torusSeq L P.m₀ n = torusSeq L P.m₀ n * 1 * 1 := by ring
        _ ≤ _ := by gcongr
    exact_mod_cast h.trans h2
  have h4A : 0 < 4 * diamA d L P.m₀ m₁ := by positivity
  have : ((n : ℝ) + 1 - 4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4) / (4 * diamA d L P.m₀ m₁) ≤
      (((torusSeq L P.m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) -
        4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4) / (4 * diamA d L P.m₀ m₁) :=
    div_le_div_of_nonneg_right (by linarith) h4A.le
  linarith

theorem tendsto_tailAt (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) :
    Tendsto (fun n => tailAt (ν := ν) Tm P j i₀ i₁ n) atTop (nhds 0) := by
  have hd0 : 0 < d := by have := hn.hd; omega
  have h1 : Tendsto (fun n => Real.exp (-tauAt d L m₁ k P j n)) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_tauAt hd0 P j)
  have h2 := h1.const_mul (tailConst d L m₁ P (liftRadius d L N P j) * K0 d L (aEnt d L + 1))
  rw [mul_zero] at h2
  refine squeeze_zero_norm (fun n => ?_) h2
  have := norm_tailAt_le hF hn hne n
  linarith

end Seq

end Balaban.SmallField.Def6
