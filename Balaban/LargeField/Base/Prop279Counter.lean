module

public import Balaban.LargeField.Base.BaseRecord
public import Balaban.LargeField.Base.SpinsNearBackground
public import Balaban.LargeField.Base.BaseSmallField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Two failed deductions about the base small-field proposition (BASE-KERNEL-4 §§2-3)

Lean counterexamples, so that the false deductions are not landed:

* `baseMargin_counterexample` (Counterexample 2.1): a `BaseRecord` with `P₁ = {p}`, `Q₁ = R₁ = S₁ = ∅`
  and unit spins with `χ'^{(0)} = 1` on every good cube and `χ'^{(0)} = 0` on `P₁`, but a tested bond of
  length `δ₀ - r/2 ∈ (δ₀ - 2r, δ₀)`.  The record and the strict old tests give no uniform margin; the
  correct statement is the support-local `chiPrimeZero_eq_one_of_margins`.
* `zero_input_kernel_eq_zero`, `positive_transform_pos` (Counterexample 3.1): the zero
  `BaseSmallFieldInput` (`zeroBaseSmallFieldInput`) has kernel `K_0 ≡ 0`, while the exact first
  transform (II.7.1) is the integral of a strictly positive integrand against a nonzero finite
  measure, hence strictly positive.  Inhabiting `BaseSmallFieldInput` proves nothing about the
  physical first step.
* `b0_bound_strictly_weaker`: `BaseSmallFieldInput.b0_bound` (constant `C_b B_0`) does not imply the
  source-strength bound of Lemma II.7.7 (b) (constant `C_b`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background

section Margin

variable {d N : ℕ}

/-- The unit vector `u = e_{i0}` of Counterexample 2.1. -/
noncomputable def cexU (i0 : Fin N) : Fin N → ℝ := fun i => if i = i0 then 1 else 0

/-- The unit vector `v` of (2.2) at distance `t` from `u`. -/
noncomputable def cexV (i0 i1 : Fin N) (t : ℝ) : Fin N → ℝ := fun i =>
  if i = i0 then 1 - t ^ 2 / 2 else if i = i1 then t * Real.sqrt (1 - t ^ 2 / 4) else 0

theorem sum_sq_two (i0 i1 : Fin N) (hne : i0 ≠ i1) (f : Fin N → ℝ)
    (h0 : ∀ i, i ≠ i0 → i ≠ i1 → f i = 0) : ∑ i, f i ^ 2 = f i0 ^ 2 + f i1 ^ 2 := by
  refine Finset.sum_eq_add i0 i1 hne (fun c _ hc => by rw [h0 c hc.1 hc.2]; ring)
    (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)

theorem cexU_unit (i0 i1 : Fin N) (hne : i0 ≠ i1) : ∑ i, cexU i0 i ^ 2 = 1 := by
  rw [sum_sq_two i0 i1 hne (cexU i0) (fun i h _ => by simp [cexU, h])]
  simp [cexU, hne.symm]

theorem cexV_unit (i0 i1 : Fin N) (hne : i0 ≠ i1) {t : ℝ} (ht : t ^ 2 / 4 ≤ 1) :
    ∑ i, cexV i0 i1 t i ^ 2 = 1 := by
  rw [sum_sq_two i0 i1 hne (cexV i0 i1 t) (fun i h h' => by simp [cexV, h, h'])]
  simp only [cexV, ite_true, hne.symm, ite_false]
  have : Real.sqrt (1 - t ^ 2 / 4) ^ 2 = 1 - t ^ 2 / 4 := Real.sq_sqrt (by linarith)
  rw [mul_pow, this]; ring

theorem cex_rn (i0 i1 : Fin N) (hne : i0 ≠ i1) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ^ 2 / 4 ≤ 1) :
    rn (fun i => cexU i0 i - cexV i0 i1 t i) = t := by
  unfold rn
  rw [sum_sq_two i0 i1 hne (fun i => cexU i0 i - cexV i0 i1 t i)
    (fun i h h' => by simp [cexU, cexV, h, h'])]
  simp only [cexU, cexV, ite_true, hne.symm, ite_false]
  have : Real.sqrt (1 - t ^ 2 / 4) ^ 2 = 1 - t ^ 2 / 4 := Real.sq_sqrt (by linarith)
  have e : (1 - (1 - t ^ 2 / 2)) ^ 2 + (0 - t * Real.sqrt (1 - t ^ 2 / 4)) ^ 2 = t ^ 2 := by
    nlinarith [this]
  rw [e, Real.sqrt_sq ht0]


variable (nn : ℕ → ℕ) (L M K : ℕ) [∀ k, NeZero (nn k)] [NeZero M] [NeZero L]

/-- **Counterexample 2.1 of BASE-KERNEL-4 (strict old tests have no uniform margin).**
Let `N ≥ 2`, `0 < δ₀ < 1/4`, `0 < r < δ₀/4`, on a torus with `d ≥ 1` and at least two fine sites
per side.  There are a base record with `P₁ = {p}`, `Q₁ = R₁ = S₁ = ∅`, unit spins `φ` and a block
field `θ` (regime (A)) such that every failed cube `c ∈ P₁` has `χ'^{(0)}(c) = 0` and every good
cube `c ∉ P₁` has `χ'^{(0)}(c) = 1` (so the old product (2.1) of Definition II.7.1 is nonzero), while
a tested bond has `δ₀ - 2r < |∂φ| < δ₀`.  Hence `BaseRecord` and `χ'^{(0)} = 1` off `P₁` do not imply
a margin of size `2r` on every good cube. -/
theorem baseMargin_counterexample (hN : 2 ≤ N) (hd : 0 < d) (hℓ : 1 < M * nn K * L ^ K)
    {δ₀ r : ℝ} (hδ : 0 < δ₀) (hδ4 : δ₀ < 1 / 4) (hr : 0 < r) (hr4 : r < δ₀ / 4)
    (ν : ℝ) (h : Fin N → ℝ) (Rk : ℝ) :
    ∃ (br : BaseRecord d L (nn 1) Rk)
      (φ : Torus d (M * nn K * L ^ K) → Fin N → ℝ)
      (θ : Torus d (M * nn K * L ^ (K - 1)) → Fin N → ℝ),
      (∃ p, br.P = {p}) ∧ br.Q = ∅ ∧ br.R = ∅ ∧ br.S = ∅ ∧
      (∀ x, ∑ i, φ x i ^ 2 = 1) ∧
      (∀ c ∈ br.P, chiPrimeZero nn L M K False ν δ₀ h c (φ, θ) = 0) ∧
      (∀ c, c ∉ br.P → chiPrimeZero nn L M K False ν δ₀ h c (φ, θ) = 1) ∧
      ∃ (x : Torus d (M * nn K * L ^ K)) (μ : Fin d),
        δ₀ - 2 * r < rn (fun i => φ (x + Pi.single μ 1) i - φ x i) ∧
        rn (fun i => φ (x + Pi.single μ 1) i - φ x i) < δ₀ := by
  classical
  have : Fact (1 < M * nn K * L ^ K) := ⟨hℓ⟩
  set i0 : Fin N := ⟨0, by omega⟩ with hi0
  set i1 : Fin N := ⟨1, by omega⟩ with hi1
  have hne : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  set t : ℝ := δ₀ - r / 2 with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have ht4 : t ^ 2 / 4 ≤ 1 := by rw [ht]; nlinarith
  have htlt : t < δ₀ := by rw [ht]; linarith
  set x0 : Torus d (M * nn K * L ^ K) := 0 with hx0
  set φ : Torus d (M * nn K * L ^ K) → Fin N → ℝ :=
    fun z => if z = x0 then cexV i0 i1 t else cexU i0 with hφ
  set p : Torus d (nn 1) := blockMap M (nn 1) (0 : Torus d (M * nn K * L ^ (K - 1))) with hp
  set θ : Torus d (M * nn K * L ^ (K - 1)) → Fin N → ℝ := fun y i =>
    spinAverage nn L M K φ y i +
      (if blockMap M (nn 1) y = p then (if i = i0 then 3 * δ₀ else 0) else 0) with hθ
  have hpair : ∀ a b, rn (fun i => φ a i - φ b i) = 0 ∨ rn (fun i => φ a i - φ b i) = t := by
    intro a b
    have hz : ∀ f : Fin N → ℝ, rn (fun i => f i - f i) = 0 := fun f => by simp [rn]
    have huv := cex_rn i0 i1 hne ht0 ht4
    by_cases ha : a = x0 <;> by_cases hb : b = x0
    · left; simp only [hφ, ha, hb, ite_true]; exact hz _
    · right; simp only [hφ, ha, hb, ite_true, ite_false]
      rw [rn_sub_comm']; exact huv
    · right; simp only [hφ, ha, hb, ite_true, ite_false]; exact huv
    · left; simp only [hφ, ha, hb, ite_false]; exact hz _
  have hbond : ∀ a b, rn (fun i => φ a i - φ b i) < δ₀ := by
    intro a b
    rcases hpair a b with h1 | h1 <;> rw [h1] <;> linarith
  have hbondProp : ∀ c, ChiBondProp nn L M K δ₀ φ c := fun c x μ _ => hbond _ _
  let br : BaseRecord d L (nn 1) Rk :=
    { P := {p}, Q := ∅, R := ∅, S := ∅
      Q_sub := Set.empty_subset _, R_sub := Set.empty_subset _, S_sub := Set.empty_subset _ }
  have hblockNe : ∀ c, c ≠ p → ChiBlockProp nn L M K δ₀ φ θ c := by
    intro c hc y hy
    have hyp : ¬ blockMap M (nn 1) y = p := fun h' => hc (hy ▸ h')
    have : (fun i => θ y i - spinAverage nn L M K φ y i) = fun _ => 0 := by
      funext i; simp [hθ, hyp]
    rw [this]; unfold rn; simp; linarith
  have hblockP : ¬ ChiBlockProp nn L M K δ₀ φ θ p := by
    intro hb
    have := hb 0 rfl
    have e : (fun i => θ 0 i - spinAverage nn L M K φ 0 i) =
        fun i => if i = i0 then 3 * δ₀ else 0 := by
      funext i; simp [hθ, ← hp]
    rw [e] at this
    have : rn (fun i : Fin N => if i = i0 then 3 * δ₀ else 0) = 3 * δ₀ := by
      unfold rn
      have : ∑ i : Fin N, (if i = i0 then 3 * δ₀ else 0) ^ 2 = (3 * δ₀) ^ 2 := by
        simp [Finset.sum_ite_eq']
      rw [this, Real.sqrt_sq (by linarith)]
    linarith
  refine ⟨br, φ, θ, ⟨p, rfl⟩, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x = x0
    · simp only [hφ, hx, ite_true]; exact cexV_unit i0 i1 hne ht4
    · simp only [hφ, hx, ite_false]; exact cexU_unit i0 i1 hne
  · intro c hc
    have hcp : c = p := hc
    rcases chiPrimeZero_eq_zero_or_one nn L M K False ν δ₀ h c (φ, θ) with h1 | h1
    · exact h1
    · exfalso
      have := ((chiPrimeZero_eq_one_iff nn L M K False ν δ₀ h c (φ, θ)).1 h1).1
      exact hblockP (hcp ▸ this)
  · intro c hc
    have hcp : c ≠ p := fun h' => hc h'
    rw [chiPrimeZero_eq_one_iff]
    exact ⟨hblockNe c hcp, hbondProp c, fun hF => absurd hF id⟩
  · refine ⟨x0, ⟨0, hd⟩, ?_⟩
    have hne' : x0 + Pi.single (⟨0, hd⟩ : Fin d) 1 ≠ x0 := by
      intro h'
      have := congrFun h' ⟨0, hd⟩
      simp [hx0] at this
    have e : (fun i => φ (x0 + Pi.single (⟨0, hd⟩ : Fin d) 1) i - φ x0 i) =
        fun i => cexU i0 i - cexV i0 i1 t i := by
      funext i; simp only [hφ, hne', ite_false, ite_true]
    rw [e, cex_rn i0 i1 hne ht0 ht4]
    constructor <;> rw [ht] <;> linarith

end Margin

/-! ### Counterexample 3.1: the zero input is not the first transformation -/

section ZeroInput

open MeasureTheory Balaban.Multiscale RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- The zero `BaseSmallFieldInput`: remainder `K̃^w_0 ≡ 0` and boundary exponent `b_0 ≡ 0`
(BASE-KERNEL-4 (3.1)). -/
noncomputable def zeroBaseSmallFieldInput (geo : Geo S n R M) (cs : OpConsts) (N k0 : ℕ)
    (hCb : 0 ≤ cs.Cb) (hB0 : 0 ≤ cs.B0) (hβ : 1 ≤ cs.beta 0) :
    BaseSmallFieldInput K k0 geo cs N := by
  have hlog : 0 ≤ Real.log (cs.beta 0) := Real.log_nonneg hβ
  exact
    { Kt := fun _ _ _ _ _ => 0
      b0 := fun _ _ _ _ _ => 0
      Kt_nonneg := fun _ _ _ _ _ => le_rfl
      Kt_meas := fun _ _ _ => measurable_const
      Kt_outside := fun _ _ _ _ _ _ _ => rfl
      Kt_dom := fun _ _ _ _ _ _ _ _ => rfl
      Kt_rot := fun _ _ _ _ _ _ => rfl
      euclid_K := by
        intro σ a a' hI hk o o' x x' hv ho hx
        classical
        simp [baseSumOf]
      b0_meas := fun _ _ _ => measurable_const
      b0_analytic := fun a o x hv g _ =>
        (analyticAt_const : AnalyticAt ℂ (fun _ : GIdx S n M K N → ℂ => (0 : ℂ)) g)
      b0_real := by intros; simp
      b0_supp := fun _ _ _ _ _ _ _ => rfl
      b0_rot := fun _ _ _ _ _ _ => rfl
      euclid_b := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
      b0_bound := by
        intro H hH Z' o x hv g hg hc
        simp only [norm_zero]
        have : 0 ≤ volScale S (0 + 1) {z | z ∈ (H.localHistory M K (0 + 1) Z').Z (0 + 1) ∧
              z ∉ (H.localHistory M K (0 + 1) Z').Z 0} := by
          unfold volScale; positivity
        positivity }

/-- **Counterexample 3.1, kernel side.**  The kernel of the zero input vanishes identically. -/
theorem zero_input_kernel_eq_zero {k0 : ℕ} (geo : Geo S n R M) (cs : OpConsts)
    (hCb : 0 ≤ cs.Cb) (hB0 : 0 ≤ cs.B0) (hβ : 1 ≤ cs.beta 0)
    (hz : 0 ≤ cs.z (0 + 1)) (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (a : LocalHistory S n M K) (o : OutT N R a (0 + 1)) (x : NewCfg N a 0)
    (hv : EuclideanSpace ℝ (Fin N)) :
    (baseKernel_of_input (zeroBaseSmallFieldInput (K := K) (k0 := k0) geo cs N hCb hB0 hβ)
      hz hc a).K o x hv = 0 := by
  classical
  show gaussProd N a 0 cs o x * baseSumOf cs a (fun _ _ _ _ => (0 : ℝ)) o x hv = 0
  simp [baseSumOf]

/-- **Counterexample 3.1, physical side (3.2).**  The transform of a strictly positive integrand
against a nonzero finite measure is strictly positive: `ρ_1(ψ) = ∫ t_0 e^{-β H} dσ > 0` because the
first Gaussian kernel and the Boltzmann weight are strictly positive and the product sphere measure
has positive finite mass. -/
theorem positive_transform_pos {α β : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (hμ : μ Set.univ ≠ 0) (f : α → β → ℝ) (hint : ∀ b, Integrable (f · b) μ)
    (hpos : ∀ a b, 0 < f a b) (b : β) : 0 < ∫ a, f a b ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun a => (hpos a b).le) (hint b)]
  have : Function.support (fun a => f a b) = Set.univ :=
    Set.eq_univ_of_forall fun a => (hpos a b).ne'
  rw [this]
  exact pos_iff_ne_zero.mpr hμ

end ZeroInput

/-! ### The weaker `b_0` bound -/

/-- `BaseSmallFieldInput.b0_bound` has the constant `C_b B_0` where Lemma II.7.7 (b) needs
`C_b`: for `C_b > 0` and `B_0 > 1` the former is strictly larger, so it does not imply the latter. -/
theorem b0_bound_strictly_weaker {Cb B0 β : ℝ} (hCb : 0 < Cb) (hB0 : 1 < B0) :
    Cb * Real.log β + Cb * B0 > Cb * (Real.log β + 1) := by
  nlinarith

end Balaban.LargeField
