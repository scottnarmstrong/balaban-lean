/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.LimitCauchy
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity


/-!
# G-5(c): the infinite-volume limits are genuine limits

`Balaban.Green.infiniteVolume_limits` produces subsequential limits of `a G Q*`, `Δ_tr` and `C_tr`
along tori of side `L M_n`.  Here we show (`Balaban.Green.infiniteVolume_limits_unique`) that for
every `ν ∈ [0, 2]` the entries converge along *every* sequence `M_n → ∞`, that the limits do not
depend on the sequence, and that they satisfy the decay and Lipschitz bounds.

Route (GREEN.md G-5(b), re-review F-18).  The entries of the inverses on the tori of sides
`L (j+1) L^k` and `L (j+1)` form Cauchy families (`Balaban.Green.fineKernelAt_cauchy`,
`Balaban.Green.deltaAt_cauchy`, `Balaban.Green.greenAt_cauchy`, from `Balaban.Green.LimitCauchy`):
two tori are compared through the Dirichlet Green function of a common cube of `ℤ^d`, using the
geometric resolvent identity and the domain-difference estimate of G-4, and the operators on the
common cube agree up to a small error.  A Cauchy family converges along every sequence to one
limit (`Balaban.Green.exists_tendsto_of_cauchy_pnat`).  The bounds follow from those of the
subsequential limits, which coincide with the limit.
-/

@[expose] public section

namespace Balaban.Green

open Filter Topology

/-- A Cauchy family indexed by `ℕ+` converges along every sequence tending to infinity, to a limit
independent of the sequence. -/
theorem exists_tendsto_of_cauchy_pnat (f : ℕ+ → ℝ)
    (hf : ∀ ε > 0, ∃ M₀ : ℕ+, ∀ M₁, M₀ ≤ M₁ → ∀ M₂, M₀ ≤ M₂ → |f M₁ - f M₂| ≤ ε) :
    ∃ l : ℝ, ∀ M : ℕ → ℕ+, Tendsto (fun n => ((M n : ℕ+) : ℕ)) atTop atTop →
      Tendsto (fun n => f (M n)) atTop (𝓝 l) := by
  have hcau : CauchySeq (fun n : ℕ => f (Nat.succPNat n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨M₀, hM₀⟩ := hf (ε / 2) (by positivity)
    refine ⟨(M₀ : ℕ), fun m hm n hn => ?_⟩
    have h1 : M₀ ≤ Nat.succPNat m := by
      rw [← PNat.coe_le_coe]; simp; omega
    have h2 : M₀ ≤ Nat.succPNat n := by
      rw [← PNat.coe_le_coe]; simp; omega
    rw [Real.dist_eq]
    have := hM₀ _ h1 _ h2
    linarith
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨l, fun M hM => ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := hf (ε / 2) (by positivity)
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.1 hl) (ε / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 hM (M₀ : ℕ))
  refine ⟨N₂, fun n hn => ?_⟩
  set m := max N₁ (M₀ : ℕ) with hm
  have h1 : M₀ ≤ Nat.succPNat m := by
    rw [← PNat.coe_le_coe]; simp; omega
  have h2 : M₀ ≤ M n := by
    rw [← PNat.coe_le_coe]; exact hN₂ n hn
  have h3 := hM₀ _ h2 _ h1
  have h4 := hN₁ m (le_max_left _ _)
  rw [Real.dist_eq] at h4 ⊢
  rw [abs_le] at h3
  rw [abs_lt] at h4 ⊢
  constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]

theorem exists_sqBox {d : ℕ} (u : Fin d → ℤ) : ∃ R : ℕ, u ∈ sqBox d R := by
  refine ⟨∑ μ, (u μ).natAbs, mem_sqBox.2 fun μ => ?_⟩
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Finset.single_le_sum (f := fun μ => (u μ).natAbs) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ μ)

theorem cauchy_pnat_of_nat {f : ℕ+ → ℝ}
    (h : ∀ ε > 0, ∃ j₀ : ℕ, ∀ j₁, j₀ ≤ j₁ → ∀ j₂, j₀ ≤ j₂ →
      |f (Nat.succPNat j₁) - f (Nat.succPNat j₂)| ≤ ε) :
    ∀ ε > 0, ∃ M₀ : ℕ+, ∀ M₁, M₀ ≤ M₁ → ∀ M₂, M₀ ≤ M₂ → |f M₁ - f M₂| ≤ ε := by
  intro ε hε
  obtain ⟨j₀, hj₀⟩ := h ε hε
  refine ⟨Nat.succPNat j₀, fun M₁ hM₁ M₂ hM₂ => ?_⟩
  have key : ∀ M : ℕ+, Nat.succPNat j₀ ≤ M → j₀ ≤ M.natPred := by
    intro M hM
    rw [← PNat.coe_le_coe] at hM
    simp only [Nat.succPNat_coe] at hM
    have := PNat.natPred_add_one M
    omega
  have := hj₀ M₁.natPred (key M₁ hM₁) M₂.natPred (key M₂ hM₂)
  rwa [PNat.succPNat_natPred, PNat.succPNat_natPred] at this

section Main

variable {d L k : ℕ} [NeZero L]

theorem fineKernelAt_cauchy (hd : 0 < d) {a ν : ℝ} (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (x y' : Fin d → ℤ) :
    ∀ ε > 0, ∃ M₀ : ℕ+, ∀ M₁, M₀ ≤ M₁ → ∀ M₂, M₀ ≤ M₂ →
      |fineKernelAt d L k M₁ ν a x y' - fineKernelAt d L k M₂ ν a x y'| ≤ ε := by
  apply cauchy_pnat_of_nat
  intro ε hε
  obtain ⟨R₁, hR₁⟩ := exists_sqBox x
  obtain ⟨R₂, hR₂⟩ := exists_sqBox y'
  obtain ⟨j₀, hj₀⟩ := fineKernel_cauchy (d := d) (L := L) (k := k) hd hν ha1 ha2 (max R₁ R₂) ε hε
  exact ⟨j₀, fun j₁ hj₁ j₂ hj₂ => hj₀ j₁ hj₁ j₂ hj₂ x (sqBox_mono (le_max_left _ _) hR₁) y'
    (sqBox_mono (le_max_right _ _) hR₂)⟩

theorem deltaAt_cauchy (hd : 0 < d) {a ν : ℝ} (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (y y' : Fin d → ℤ) :
    ∀ ε > 0, ∃ M₀ : ℕ+, ∀ M₁, M₀ ≤ M₁ → ∀ M₂, M₀ ≤ M₂ →
      |deltaAt d L k M₁ ν a y y' - deltaAt d L k M₂ ν a y y'| ≤ ε := by
  apply cauchy_pnat_of_nat
  intro ε hε
  obtain ⟨R₁, hR₁⟩ := exists_sqBox y
  obtain ⟨R₂, hR₂⟩ := exists_sqBox y'
  obtain ⟨j₀, hj₀⟩ := unitOperator_cauchy (d := d) (L := L) (k := k) hd hν ha1 ha2 (max R₁ R₂) ε hε
  exact ⟨j₀, fun j₁ hj₁ j₂ hj₂ => hj₀ j₁ hj₁ j₂ hj₂ y (sqBox_mono (le_max_left _ _) hR₁) y'
    (sqBox_mono (le_max_right _ _) hR₂)⟩

theorem greenAt_cauchy (hd : 0 < d) (hk : 1 ≤ k) {a a' ν : ℝ} (hν0 : 0 ≤ ν) (hν2 : ν ≤ 2)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (ha'1 : 1 / 2 ≤ a') (ha'2 : a' ≤ 2) (y y' : Fin d → ℤ) :
    ∀ ε > 0, ∃ M₀ : ℕ+, ∀ M₁, M₀ ≤ M₁ → ∀ M₂, M₀ ≤ M₂ →
      |greenAt d L k M₁ ν a a' y y' - greenAt d L k M₂ ν a a' y y'| ≤ ε := by
  apply cauchy_pnat_of_nat
  intro ε hε
  obtain ⟨R₁, hR₁⟩ := exists_sqBox y
  obtain ⟨R₂, hR₂⟩ := exists_sqBox y'
  obtain ⟨j₀, hj₀⟩ := coarseGreen_cauchy (d := d) (L := L) (k := k) hd hk hν0 hν2 ha1 ha2 ha'1
    ha'2 (max R₁ R₂) ε hε
  exact ⟨j₀, fun j₁ hj₁ j₂ hj₂ => hj₀ j₁ hj₁ j₂ hj₂ y (sqBox_mono (le_max_left _ _) hR₁) y'
    (sqBox_mono (le_max_right _ _) hR₂)⟩

/-- **G-5(c), uniqueness.**  The entries of `a G Q*`, `Δ_tr` and `C_tr` at sites of `ℤ^d` converge,
for every `ν ∈ [0, 2]`, along *every* sequence of tori of side `L M_n`, `M_n → ∞`; the limits do
not depend on the sequence, and satisfy the decay bounds of (a) and the Lipschitz bounds of (b)
(`Balaban.Green.infiniteVolume_limits`, whose statement this strengthens). -/
theorem infiniteVolume_limits_unique (hd : 0 < d) (hk : 1 ≤ k) {a a' : ℝ} (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (ha'1 : 1 / 2 ≤ a') (ha'2 : a' ≤ 2) :
    ∃ Kinf Dinf Cinf : ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ,
      (∀ M : ℕ → ℕ+, Tendsto (fun n => ((M n : ℕ+) : ℕ)) atTop atTop →
        ∀ ν ∈ Set.Icc (0 : ℝ) 2, ∀ y y',
        Tendsto (fun n => fineKernelAt d L k (M n) ν a y y') atTop (𝓝 (Kinf ν y y')) ∧
        Tendsto (fun n => deltaAt d L k (M n) ν a y y') atTop (𝓝 (Dinf ν y y')) ∧
        Tendsto (fun n => greenAt d L k (M n) ν a a' y y') atTop (𝓝 (Cinf ν y y'))) ∧
      (∀ ν ∈ Set.Icc (0 : ℝ) 2, ∀ y y',
        ∑ x ∈ intFibre (L ^ k) y, (Kinf ν x y') ^ 2 ≤ (((L ^ k : ℕ) : ℝ) ^ d) *
            (a * blockDecayConst d L * Real.exp (-(blockDecayRate d * l1IntDist d y y'))) ^ 2 ∧
        |Dinf ν y y'| ≤ (2 + 4 * blockDecayConst d L) *
            Real.exp (-(blockDecayRate d * l1IntDist d y y')) ∧
        |Cinf ν y y'| ≤ 2 * (trGamma d L)⁻¹ * Real.exp (-(trRate d L * l1IntDist d y y'))) ∧
      (∀ ν₁ ∈ Set.Icc (0 : ℝ) 2, ∀ ν₂ ∈ Set.Icc (0 : ℝ) 2, ∀ y y',
        ∑ x ∈ intFibre (L ^ k) y, (Kinf ν₁ x y' - Kinf ν₂ x y') ^ 2 ≤ (((L ^ k : ℕ) : ℝ) ^ d) *
            (a * (|ν₁ - ν₂| * massLipConst d L *
              Real.exp (-(blockDecayRate d / 2) * l1IntDist d y y'))) ^ 2 ∧
        |Dinf ν₁ y y' - Dinf ν₂ y y'| ≤ 4 * (|ν₁ - ν₂| * massLipConst d L *
            Real.exp (-(blockDecayRate d / 2) * l1IntDist d y y')) ∧
        |Cinf ν₁ y y' - Cinf ν₂ y y'| ≤ |ν₁ - ν₂| * coarseLipConst d L *
            Real.exp (-(lipRate d L / 4) * l1IntDist d y y')) := by
  classical
  have hKc : ∀ (ν : ℝ) (x y' : Fin d → ℤ), ∃ l : ℝ, ν ∈ Set.Icc (0 : ℝ) 2 →
      ∀ M : ℕ → ℕ+, Tendsto (fun n => ((M n : ℕ+) : ℕ)) atTop atTop →
        Tendsto (fun n => fineKernelAt d L k (M n) ν a x y') atTop (𝓝 l) := by
    intro ν x y'
    by_cases hν : ν ∈ Set.Icc (0 : ℝ) 2
    · obtain ⟨l, hl⟩ := exists_tendsto_of_cauchy_pnat (fun M => fineKernelAt d L k M ν a x y')
        (fineKernelAt_cauchy hd hν.1 ha1 ha2 x y')
      exact ⟨l, fun _ => hl⟩
    · exact ⟨0, fun h => absurd h hν⟩
  have hDc : ∀ (ν : ℝ) (x y' : Fin d → ℤ), ∃ l : ℝ, ν ∈ Set.Icc (0 : ℝ) 2 →
      ∀ M : ℕ → ℕ+, Tendsto (fun n => ((M n : ℕ+) : ℕ)) atTop atTop →
        Tendsto (fun n => deltaAt d L k (M n) ν a x y') atTop (𝓝 l) := by
    intro ν x y'
    by_cases hν : ν ∈ Set.Icc (0 : ℝ) 2
    · obtain ⟨l, hl⟩ := exists_tendsto_of_cauchy_pnat (fun M => deltaAt d L k M ν a x y')
        (deltaAt_cauchy hd hν.1 ha1 ha2 x y')
      exact ⟨l, fun _ => hl⟩
    · exact ⟨0, fun h => absurd h hν⟩
  have hCc : ∀ (ν : ℝ) (x y' : Fin d → ℤ), ∃ l : ℝ, ν ∈ Set.Icc (0 : ℝ) 2 →
      ∀ M : ℕ → ℕ+, Tendsto (fun n => ((M n : ℕ+) : ℕ)) atTop atTop →
        Tendsto (fun n => greenAt d L k (M n) ν a a' x y') atTop (𝓝 l) := by
    intro ν x y'
    by_cases hν : ν ∈ Set.Icc (0 : ℝ) 2
    · obtain ⟨l, hl⟩ := exists_tendsto_of_cauchy_pnat (fun M => greenAt d L k M ν a a' x y')
        (greenAt_cauchy hd hk hν.1 hν.2 ha1 ha2 ha'1 ha'2 x y')
      exact ⟨l, fun _ => hl⟩
    · exact ⟨0, fun h => absurd h hν⟩
  choose Kinf hKinf using hKc
  choose Dinf hDinf using hDc
  choose Cinf hCinf using hCc
  -- the bounds, from the subsequential limits
  have hM0 : Tendsto (fun n : ℕ => ((Nat.succPNat n : ℕ+) : ℕ)) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp) tendsto_id
  obtain ⟨φ, hφ, K', D', C', hconv, hbd, hlip⟩ :=
    infiniteVolume_limits (L := L) (k := k) hd hk ha1 ha2 ha'1 ha'2 (fun n => Nat.succPNat n) hM0
  have hMφ : Tendsto (fun n : ℕ => ((Nat.succPNat (φ n) : ℕ+) : ℕ)) atTop atTop :=
    hM0.comp hφ.tendsto_atTop
  have eK : ∀ ν ∈ Set.Icc (0 : ℝ) 2, ∀ x y', K' ν x y' = Kinf ν x y' := fun ν hν x y' =>
    tendsto_nhds_unique (hconv ν hν x y').1 (hKinf ν x y' hν (fun n => Nat.succPNat (φ n)) hMφ)
  have eD : ∀ ν ∈ Set.Icc (0 : ℝ) 2, ∀ x y', D' ν x y' = Dinf ν x y' := fun ν hν x y' =>
    tendsto_nhds_unique (hconv ν hν x y').2.1
      (hDinf ν x y' hν (fun n => Nat.succPNat (φ n)) hMφ)
  have eC : ∀ ν ∈ Set.Icc (0 : ℝ) 2, ∀ x y', C' ν x y' = Cinf ν x y' := fun ν hν x y' =>
    tendsto_nhds_unique (hconv ν hν x y').2.2
      (hCinf ν x y' hν (fun n => Nat.succPNat (φ n)) hMφ)
  refine ⟨Kinf, Dinf, Cinf, ?_, ?_, ?_⟩
  · intro M hM ν hν y y'
    exact ⟨hKinf ν y y' hν M hM, hDinf ν y y' hν M hM, hCinf ν y y' hν M hM⟩
  · intro ν hν y y'
    have h := hbd ν hν y y'
    simp only [eK ν hν, eD ν hν, eC ν hν] at h
    exact h
  · intro ν₁ hν₁ ν₂ hν₂ y y'
    have h := hlip ν₁ hν₁ ν₂ hν₂ y y'
    simp only [eK ν₁ hν₁, eK ν₂ hν₂, eD ν₁ hν₁, eD ν₂ hν₂, eC ν₁ hν₁, eC ν₂ hν₂] at h
    exact h

end Main

end Balaban.Green
