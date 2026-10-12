/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Theorem42
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 4.2, Step 4: the volume bound for `b_k` (FLUCTUATION.md §4.2, Step 4)

* `emptyTraceTerm_bound_of_input`: in the setting of `theorem42_of_input`, the terms with
  `Y ∩ Ω = ∅` (`emptyTraceTerm`, allocated to `b_k`) are bounded by `C_b K₀^{ms}` times the number
  of cubes `b ∈ 𝒬` outside `Ω`: the polymer domains of the cube `b` contain `b`
  (`base_mem_domain`), and the entropy sum (G2) through `b` (`multiscale_entropy`) bounds the
  absolute sum.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Analysis Balaban.Background

section Volume

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ j : ℕ)
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (c : ι → ℕ × CTorus d L N₁ m₁ K)
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]

open Classical in
/-- **The volume bound for the terms with `Y ∩ Ω = ∅`** (FLUCTUATION §4.2 Step 4, first
paragraph).  In the setting of `theorem42_of_input`, the internal complement terms
`b_k = ∑_b ∑_{Y ∩ Ω = ∅} 𝓔_b(Y)` are bounded by `C_b K₀` times the number of the cubes of `𝒬`
whose base lies outside `Ω` (a constant times the volume of the internal complement): a polymer
domain of a cube contains its base `b`, so the terms with `Y ∩ Ω = ∅` occur only for `b ∉ Ω`, and
for each such `b` the entropy sum (G2) through the point `b` bounds the absolute sum. -/
theorem emptyTraceTerm_bound_of_input (𝒬 : Finset (CTorus d L N₁ m₁ K))
    (Ω : Set (CTorus d L N₁ m₁ K))
    (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hϱ : (4 * d * L * (L : ℝ) ^ (m₀ + m₁) : ℝ) ≤ ϱ)
    (hS : ∀ b ∈ 𝒬, CovSetup G m₀ j (box b (L * cellSide L m₀ m₁ j)) {b})
    (hc : ∀ i, c i ∈ cubeIdx G) (hcinj : Function.Injective c)
    (hdisj : ∀ b ∈ 𝒬, ∀ i, Disjoint (Pset m₁ (c i))
      (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))))
    {κ κ₁ Cb : ℝ} (hκ : 3 ≤ κ)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁)
    (h1 : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2)
    (hCb : 0 ≤ Cb) (hκm : aMulti d L + 1 ≤ 2 * κ)
    {S : Set U} {act : CTorus d L N₁ m₁ K → U → ℂ}
    {F : CTorus d L N₁ m₁ K → U → (ι → ℂ) → ℂ}
    {Ag : Finset ι → U → U → Prop} {AgY : Set (CTorus d L N₁ m₁ K) → U → U → Prop}
    (hrefl : ∀ C u, u ∈ S → Ag C u u)
    (hlink : ∀ b ∈ 𝒬, ∀ C u u',
      AgY (Ysites G m₀ c (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))) C) u u' → Ag C u u')
    (R : DecoupledCubeResponse G m₀ j c 𝒬 S κ₁ Cb Ag act F) :
    ∀ u ∈ S, ‖emptyTraceTerm G m₀ j c 𝒬 Ω F u‖ ≤
      ((𝒬.filter fun b => b ∉ Ω).card : ℝ) * (Cb * K0Multi d L) := by
  intro u hu
  have hal : ∀ b ∈ 𝒬, Aligned (cellSide L m₀ m₁ j) b := fun b hb => (hS b hb).chosen.1 b rfl |>.1
  have hbd : ∀ b ∈ 𝒬, ∀ u ∈ S, ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁),
      ‖F b u s‖ ≤ Cb * Real.exp (-(κ - 1) * treeLenCovOne m₀ j
        (box b (L * cellSide L m₀ m₁ j))) := fun b hb u hu s hs => by
    rw [treeLenCovOne_box b (hal b hb)]; simpa using R.bound b hb u hu s hs
  have hexp : ∀ b ∈ 𝒬, _ := fun b hb => cube_expansion (c := c) (AgY := AgY) Ω (hS b hb) hd hL hc
    hcinj (hdisj b hb) (hopt_box b (hal b hb)) (κ₀ := 0) le_rfl (by linarith) hκ₁ h1 hlog hCb
    hrefl (hlink b hb) (R.analytic b hb) (hbd b hb) (R.loc b hb)
  have hev : ∀ b ∈ 𝒬, ∀ Y, ‖evTerm c G m₀ (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K)))
      (F b) Y u‖ ≤ Cb * Real.exp (-(2 * κ) * treeLenCov G m₀ Y) := by
    intro b hb Y
    have := (hexp b hb).2.2.1 Y u hu
    rw [treeLenCovOne_box b (hal b hb)] at this
    simpa using this
  unfold emptyTraceTerm
  refine (norm_sum_le _ _).trans ?_
  have hcube : ∀ b ∈ 𝒬, ‖∑ Y ∈ (polymerDomains c G m₀ (X1 G m₀ j
      ({b} : Set (CTorus d L N₁ m₁ K)))).filter (fun Y => Y ∩ Ω = ∅),
      evTerm c G m₀ (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))) (F b) Y u‖ ≤
      if b ∈ Ω then 0 else Cb * K0Multi d L := by
    intro b hb
    by_cases hbΩ : b ∈ Ω
    · simp only [hbΩ, ↓reduceIte]
      have : (polymerDomains c G m₀ (X1 G m₀ j
          ({b} : Set (CTorus d L N₁ m₁ K)))).filter (fun Y => Y ∩ Ω = ∅) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun Y hY hYΩ => ?_
        have hbY := (base_mem_domain (hS b hb) hY).1
        have : b ∈ Y ∩ Ω := ⟨hbY, hbΩ⟩
        rw [hYΩ] at this
        exact this
      rw [this]; simp
    · simp only [hbΩ, ↓reduceIte]
      have hK : 1 ≤ K := by have := (hS b hb).hjK; omega
      refine (norm_sum_le _ _).trans ?_
      have hMD : ∀ Y ∈ polymerDomains c G m₀ (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))),
          IsMultiDom G m₀ Y := fun Y hY =>
        polymerDomain_isMultiDom c (hS b hb) hd hc (hopt_box b (hal b hb)) hY
      calc ∑ Y ∈ (polymerDomains c G m₀ (X1 G m₀ j
            ({b} : Set (CTorus d L N₁ m₁ K)))).filter (fun Y => Y ∩ Ω = ∅),
            ‖evTerm c G m₀ (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))) (F b) Y u‖
          ≤ ∑ Y ∈ (polymerDomains c G m₀ (X1 G m₀ j
            ({b} : Set (CTorus d L N₁ m₁ K)))).filter (fun Y => Y ∩ Ω = ∅),
              Cb * Real.exp (-(2 * κ) * treeLenCov G m₀ Y) :=
            Finset.sum_le_sum fun Y _ => hev b hb Y
        _ = Cb * ∑ Y ∈ (polymerDomains c G m₀ (X1 G m₀ j
            ({b} : Set (CTorus d L N₁ m₁ K)))).filter (fun Y => Y ∩ Ω = ∅),
              Real.exp (-(2 * κ) * treeLenCov G m₀ Y) := by rw [Finset.mul_sum]
        _ ≤ Cb * K0Multi d L := by
            refine mul_le_mul_of_nonneg_left ?_ hCb
            refine le_trans ?_ (multiscale_entropy G m₀ (hS b hb).hN hϱ (x₀ := b)
              (κ := 2 * κ) hκm)
            refine (Finset.sum_le_sum_of_subset_of_nonneg ?_
              (fun _ _ _ => Real.exp_nonneg _))
            intro Y hY
            obtain ⟨hYm, -⟩ := Finset.mem_filter.1 hY
            exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hMD Y hYm,
              (base_mem_domain (hS b hb) hYm).1⟩
  calc ∑ b ∈ 𝒬, ‖∑ Y ∈ (polymerDomains c G m₀ (X1 G m₀ j
        ({b} : Set (CTorus d L N₁ m₁ K)))).filter (fun Y => Y ∩ Ω = ∅),
        evTerm c G m₀ (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K))) (F b) Y u‖
      ≤ ∑ b ∈ 𝒬, (if b ∈ Ω then 0 else Cb * K0Multi d L) := Finset.sum_le_sum hcube
    _ = ((𝒬.filter fun b => b ∉ Ω).card : ℝ) * (Cb * K0Multi d L) := by
        rw [← Finset.sum_filter_add_sum_filter_not 𝒬 (fun b => b ∉ Ω)]
        have e1 : ∑ b ∈ 𝒬.filter (fun b => b ∉ Ω), (if b ∈ Ω then 0 else Cb * K0Multi d L) =
            ((𝒬.filter fun b => b ∉ Ω).card : ℝ) * (Cb * K0Multi d L) := by
          rw [Finset.sum_congr rfl (g := fun _ => Cb * K0Multi d L) (fun b hb => by
            simp [(Finset.mem_filter.1 hb).2])]
          simp
        have e2 : ∑ b ∈ 𝒬.filter (fun b => ¬ b ∉ Ω), (if b ∈ Ω then 0 else Cb * K0Multi d L) = 0 :=
          Finset.sum_eq_zero fun b hb => by
            have : b ∈ Ω := by simpa using (Finset.mem_filter.1 hb).2
            simp [this]
        rw [e1, e2, add_zero]

end Volume

end Balaban.Fluctuation
