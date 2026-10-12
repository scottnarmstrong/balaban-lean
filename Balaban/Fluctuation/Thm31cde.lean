/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31Avg
public import Balaban.Fluctuation.MeasureInterp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 3.1 (c), (d), (e): the interpolation averages (FLUCTUATION.md §3.5)

(c) `𝓑''^{(k+1)} = ∫₀¹ du ⟨𝓑''^{(k)}⟩''_u`, (d) `ℛ'^{(k+1)} = ∫₀¹ du ⟨⋯⟩'_u`,
(e) `ℛ'^{(k+1)}_{n-1}` (P5 (3.2), (3.9), (3.11)) are all interpolation averages of a sum of marks in a
measure `Z_u⁻¹ e^{W(u)} dν_{p₁}` whose exponent is expanded by Proposition 3.3.  The objects
`𝓑^{(k)}`, `ℛ^{(k)}_n`, `Z_k`, `Ω_{k+1}` of the subdomain case are not defined in the repository
(`StepSetting` is the whole-lattice step, where they vanish), so the statements here are for the
abstract interpolation average `interpAvg` of the integrand of P5 (3.2), (3.9), (3.11), with the
stated sizes.  The conclusion is the sum over sets `S` of `π_{k+1}`-cubes with the rate `κ'`
(`κ_a` for (c), `κ_b` for (d), (e)).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

section Generic

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {X : Type*} [MeasurableSpace X]

/-- The interpolation average `∫₀¹ ⟨f(u)⟩_u du` for the measures `Z_u⁻¹ e^{W(u)} dν`. -/
noncomputable def interpAvg (ν : Measure X) (W : ℝ → X → ℂ) (f : ℝ → X → ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..1, avgFun ν W (f u) u

/-- The block structure of `ν`: the variable is the family of its restrictions to the cubes of
`𝕋` at scale `K`, and `ν` is the product of probability measures `ν_b`. -/
structure ProdSplit (ν : Measure X) (d L N₁ m₁ K m₀ : ℕ) [NeZero L] [NeZero N₁] where
  Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ → Type
  [ms : ∀ b, MeasurableSpace (Ωb b)]
  μ : ∀ b, Measure (Ωb b)
  [prob : ∀ b, IsProbabilityMeasure (μ b)]
  restr : X → ∀ b, Ωb b
  meas : Measurable restr
  map_eq : Measure.map restr ν = Measure.pi μ

attribute [instance] ProdSplit.ms ProdSplit.prob

theorem avgFun_eq_avgPi_gen {ν : Measure X} {m₀ : ℕ} (BS : ProdSplit ν d L N₁ m₁ K m₀)
    {Lb : Type*} [Fintype Lb] (W : ℝ → X → ℂ) (f : X → ℂ) (s : ℝ)
    (H : Lb → (∀ b, BS.Ωb b) → ℂ) (G : (∀ b, BS.Ωb b) → ℂ)
    (hHm : ∀ y, Measurable (H y)) (hGm : Measurable G)
    (hW : ∀ᵐ x ∂ν, W s x = ∑ y, H y (BS.restr x))
    (hf : ∀ᵐ x ∂ν, f x = G (BS.restr x)) :
    avgFun ν W f s = avgPi (K := K) (j := K) (Ω := Set.univ) BS.μ H G := by
  have hmeas : Measurable (fun Φ : ∀ b, BS.Ωb b => Complex.exp (∑ y, H y Φ)) :=
    Complex.measurable_exp.comp (Finset.measurable_sum _ fun y _ => hHm y)
  have hZ : partFun ν W s = ∫ Φ, Complex.exp (∑ y, H y Φ) ∂(Measure.pi BS.μ) := by
    rw [← BS.map_eq, integral_map BS.meas.aemeasurable hmeas.aestronglyMeasurable]
    unfold partFun
    refine integral_congr_ae ?_
    filter_upwards [hW] with x hx
    rw [hx]
  have hN : ∫ x, f x * Complex.exp (W s x) ∂ν =
      ∫ Φ, G Φ * Complex.exp (∑ y, H y Φ) ∂(Measure.pi BS.μ) := by
    rw [← BS.map_eq, integral_map (f := fun Φ => G Φ * Complex.exp (∑ y, H y Φ))
      BS.meas.aemeasurable (hGm.mul hmeas).aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [hW, hf] with x hx hfx
    rw [hx, hfx]
  unfold avgFun avgPi
  rw [hZ, hN]

/-- **Proposition 3.3 for an interpolation average in the variable `ψ̂`**: exponent `W(u)` and
integrand `f(u)` are, `ν`-a.e. and for `u ∈ [0,1]`, sums of block-local terms (holomorphic in `u`
on an open `𝒰 ⊃ [0,1]`), with the numerical hypotheses of Theorem 3.4. -/
structure InterpMarks (ν : Measure X) {m₀ : ℕ} (BS : ProdSplit ν d L N₁ m₁ K m₀)
    (W : ℝ → X → ℂ) (f : ℝ → X → ℂ) where
  Lb : Type
  [fin : Fintype Lb]
  Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ Lb
  ι : Type
  [finι : Fintype ι]
  nonempty : Nonempty ι
  εH : ℝ
  κH : ℝ
  κG : ℝ
  κ0 : ℝ
  κ' : ℝ
  Kc : ℝ
  F0 : ι → ℝ
  hN : L ^ m₀ ∣ N₁
  𝒰 : Set ℂ
  isOpen : IsOpen 𝒰
  seg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰
  A : ℂ → LabelAct Lab BS.Ωb εH κH κ0 Kc
  y0 : ι → Lb
  G : ι → ℂ → (∀ b, BS.Ωb b) → ℂ
  meas : ∀ i u, Measurable (G i u)
  dep : ∀ i u, DepOn (blocksOf m₀ K Set.univ (Lab.ysite (y0 i))) (G i u)
  bound : ∀ i u Φ, ‖G i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i))
  holA : ∀ y Φ, DifferentiableOn ℂ (fun u => (A u).H y Φ) 𝒰
  holG : ∀ i Φ, DifferentiableOn ℂ (fun u => G i u Φ) 𝒰
  hκ0 : aEnt d L + 1 ≤ κ0
  hKc : K0 d L κ0 + 1 ≤ Kc
  hεpos : 0 < εH
  hF0 : ∀ i, 0 < F0 i
  hκ' : 0 ≤ κ'
  hκG : κH ≤ κG
  hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH
  hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
    Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))
  hW : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
    W s x = ∑ y, (A (s : ℂ)).H y (BS.restr x)
  hF : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
    f s x = ∑ i, G i (s : ℂ) (BS.restr x)

attribute [instance] InterpMarks.fin InterpMarks.finι

open Classical in
/-- **A localization expansion of an interpolation average** (the common core of Theorem 3.1
(a), (c), (d), (e)); conditional on `InterpMarks`. -/
theorem interpAvg_expansion_of_input {ν : Measure X} {m₀ : ℕ}
    {BS : ProdSplit ν d L N₁ m₁ K m₀} {W : ℝ → X → ℂ} {f : ℝ → X → ℂ}
    (I : InterpMarks ν BS W f) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) → ℂ,
      interpAvg ν W f = ∑ T, E T ∧
      ∀ T, ‖E T‖ ≤ CPE d L I.Kc I.κH I.κ0 I.κ' *
          (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) * Real.exp (-I.κ' * dExt T) := by
  obtain ⟨-, hint, hbd⟩ := avg_integral_expansion BS.μ I.hN le_rfl
    (Ω := Set.univ) (j := K) (fun z _ => ⟨cbase (cellSide L m₀ m₁ K) z, aligned_cbase z,
      mem_box_cbase (cellSide_pos (L := L) m₀ m₁ K) z, Set.subset_univ _⟩)
    I.isOpen I.seg I.A I.y0 I.G I.meas I.dep I.bound I.holA I.holG I.hκ0 I.hKc I.hεpos
    I.nonempty I.hF0 I.hκ' I.hκG I.hκ I.hε
  refine ⟨fun T => ∫ s in (0 : ℝ)..1,
    Gsum BS.μ I.Lab (I.A (s : ℂ)).H I.y0 (fun i => I.G i (s : ℂ)) T, ?_, hbd⟩
  rw [← hint]
  unfold interpAvg
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  exact avgFun_eq_avgPi_gen BS _ _ s (I.A (s : ℂ)).H (fun Φ => ∑ i, I.G i (s : ℂ) Φ)
    (I.A (s : ℂ)).meas (Finset.measurable_sum _ fun i _ => I.meas i _) (I.hW s hs) (I.hF s hs)

/-- **Theorem 3.1 (c), (d), (e) with their sizes** (common form; the source rates are the choices
`κ' = κ_a` for (c) with `B = β_k^{-1}`, `κ' = κ_b` for (d) with `B = ½β_{k+1}^{-m-1}`, and
`κ' = κ_b` for (e) with `B = ½β_{k+1}^{-n}`): if the mark constant `C_PE ∑ F₀ e^{-κ₀𝗱}` is at most
`B`, then `⟨…⟩ = ∑_S E(S)` with `|E(S)| ≤ B e^{-κ' d_Ω(S)}`. -/
theorem interpAvg_expansion_bound {ν : Measure X} {m₀ : ℕ}
    {BS : ProdSplit ν d L N₁ m₁ K m₀} {W : ℝ → X → ℂ} {f : ℝ → X → ℂ}
    (I : InterpMarks ν BS W f) {B : ℝ}
    (hB : CPE d L I.Kc I.κH I.κ0 I.κ' *
      (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ B) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) → ℂ,
      interpAvg ν W f = ∑ T, E T ∧ ∀ T, ‖E T‖ ≤ B * Real.exp (-I.κ' * dExt T) := by
  obtain ⟨E, h1, h2⟩ := interpAvg_expansion_of_input I
  exact ⟨E, h1, fun T => (h2 T).trans (mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le)⟩

end Generic

section Parts

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {X : Type*} [MeasurableSpace X]
  {ν : Measure X} {m₀ : ℕ} {BS : ProdSplit ν d L N₁ m₁ K m₀} {W : ℝ → X → ℂ} {f : ℝ → X → ℂ}

/-- **Theorem 3.1 (c)**: `𝓑''^{(k+1)} = ∑_S 𝓑''(S)`, `|𝓑''(S)| ≤ β_k^{-1} e^{-κ_a d_Ω(S)}`,
conditional on `InterpMarks` for the integrand of P5 (3.2) (`𝓑''^{(k)}`-marks) and on the size
`C_PE K₀ β_k^{-3/2} ≤ β_k^{-1}` of the marks. -/
theorem thm31c_of_input (I : InterpMarks ν BS W f) {κa βk : ℝ} (hκa : I.κ' = κa)
    (hB : CPE d L I.Kc I.κH I.κ0 I.κ' *
      (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ βk⁻¹) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) → ℂ,
      interpAvg ν W f = ∑ T, E T ∧ ∀ T, ‖E T‖ ≤ βk⁻¹ * Real.exp (-κa * dExt T) := by
  subst hκa; exact interpAvg_expansion_bound I hB

/-- **Theorem 3.1 (d)**: `ℛ'^{(k+1)}_m = ∑_S ℛ'_m(S)`, `|ℛ'_m(S)| ≤ ½ β_{k+1}^{-m-1} e^{-κ_b d_Ω(S)}`,
conditional on `InterpMarks` for the integrand of P5 (3.9) and the size of the marks. -/
theorem thm31d_of_input (I : InterpMarks ν BS W f) {κb β' : ℝ} (m : ℕ) (hκb : I.κ' = κb)
    (hB : CPE d L I.Kc I.κH I.κ0 I.κ' *
      (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ (1 / 2) * β' ^ (-(m : ℤ) - 1)) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) → ℂ,
      interpAvg ν W f = ∑ T, E T ∧
      ∀ T, ‖E T‖ ≤ (1 / 2) * β' ^ (-(m : ℤ) - 1) * Real.exp (-κb * dExt T) := by
  subst hκb; exact interpAvg_expansion_bound I hB

/-- **Theorem 3.1 (e)**: the new part of `ℛ'^{(k+1)}_{n-1}`, `|ℛ'_{n-1}(S)| ≤ ½ β_{k+1}^{-n}
e^{-κ_b d_Ω(S)}`, conditional on `InterpMarks` for the integrand of P5 (3.11). -/
theorem thm31e_of_input (I : InterpMarks ν BS W f) {κb β' : ℝ} (n : ℕ) (hκb : I.κ' = κb)
    (hB : CPE d L I.Kc I.κH I.κ0 I.κ' *
      (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ (1 / 2) * β' ^ (-(n : ℤ))) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) → ℂ,
      interpAvg ν W f = ∑ T, E T ∧
      ∀ T, ‖E T‖ ≤ (1 / 2) * β' ^ (-(n : ℤ)) * Real.exp (-κb * dExt T) := by
  subst hκb; exact interpAvg_expansion_bound I hB

end Parts

end Balaban.Fluctuation
