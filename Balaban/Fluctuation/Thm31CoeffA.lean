/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31a
public import Balaban.Fluctuation.Thm31cde
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Canonical coefficients of Theorem 3.1 (a), (c), (d), (e) at a fixed step datum

The landed theorems `thm31a_of_input` and `interpAvg_expansion_of_input` assert the existence of a
coefficient family `E T` with `∑_T E T =` the quantity and `‖E T‖ ≤ B e^{-κ' d_Ω(T)}`.  Their proofs
construct the family by an explicit formula; this file names it.

* `gsumCoeff μ Lab A y0 G T` is the interpolation integral `∫₀¹ ∑ᵢ G*(Y₀ᵢ, T)(s) ds` of the
  local terms of the marked cluster expansion (Theorem 3.4), for activities `A(s)` and marks `Gᵢ(s)`.
* `interpCoeff I T` is this for the data of `InterpMarks I` (the term of Theorem 3.1 (c)-(e), and
  the interpolation part of (a)).
* `e1Coeff I D T = D.term T + interpCoeff I T` is the term of Theorem 3.1 (a): the determinant term
  of `DetExpansion` plus the interpolation term.

Theorems `interpCoeff_spec`, `thm31a_coeff`, ... state the landed conclusions for these definitions,
and `thm31a_of_input` is re-derived from `thm31a_coeff`.

## What the formulas read

| coefficient | reads |
| --- | --- |
| `interpCoeff I T` | `BS.μ`; `I.Lab`; `I.A s` (activities `H(Y; s, ·)`) for `s ∈ [0,1]` and the labels `Y`; `I.y0`; `I.G i s` for `s ∈ [0,1]`; nothing else (no bound, constant or exponent field) |
| `e1Coeff I D T` | the above, and `D.term T`; not `D.sum_eq`, `D.bound`, `κ''`, `cdet` |

Congruence (`gsumCoeff_congr`): the value at `T` depends on the activities only through the labels
`Y` with `blocksOf (Y ∩ Ω) ⊆ T`, and on each mark `Gᵢ` only when `blocksOf (Y₀ᵢ) ⊆ T`.  The
dependence on the *external* variables is through their restriction to `Ŷ(sitesOf T)`
(`gsumCoeff_ext_congr`); this is the lemma of `Pst_ext_congr`/`Gst_ext_congr`.

## Scope

These are coefficients at a *fixed* step datum.  Nothing here makes them functions of the fields of
the class, proves locality, analyticity or covariance in the external fields, or roots them at
polymers; no generating set is chosen.  (`OUTPUT.md`: `OUTPUT-PARAM-COEFF`, `OUTPUT-ROOT-EMBED`
remain open.)  For `T = ∅`, `e1Coeff I D ∅` is `D.term ∅ + interpCoeff I ∅`, where `interpCoeff I ∅`
is the interpolation integral of `Gst` on the empty set of cubes; the determinant term at `∅` is
whatever `D` prescribes (in `nonempty_detExpansion` it carries the entire determinant value), so the
formula does not place the root in the sites of `T`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.Background
  MeasureTheory

section Raw

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
  {Lb : Type*} [Fintype Lb] {ι : Type*} [Fintype ι]

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

/-- **The interpolation coefficient of a sum of marks** (the formula of
`interpAvg_expansion_of_input`): `T ↦ ∫₀¹ ∑ᵢ G*(Y₀ᵢ, T)(s) ds`, the integral of `Gsum` along the
activities `A(s)` and marks `Gᵢ(s)`. -/
noncomputable def gsumCoeff {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (Lab : CubeLabels m₀ j Ω Lb)
    {εH κH κ0 Kc : ℝ} (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G : ι → ℂ → (∀ b, Ωb b) → ℂ) (T : Finset 𝔅) : ℂ :=
  ∫ s in (0 : ℝ)..1, Gsum μ Lab (A (s : ℂ)).H y0 (fun i => G i (s : ℂ)) T

/-- **Congruence of `gsumCoeff` in the labels**: the coefficient at `T` is unchanged if the
activities agree (for `s ∈ [0,1]`) on every label whose cubes lie in `T`, and the marks agree
(for `s ∈ [0,1]`) whenever the cubes of their label lie in `T`. -/
theorem gsumCoeff_congr {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] {Lab : CubeLabels m₀ j Ω Lb}
    {εH κH κ0 Kc εH' κH' κ0' Kc' : ℝ}
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (A' : ℂ → LabelAct Lab Ωb εH' κH' κ0' Kc')
    (y0 : ι → Lb) (G G' : ι → ℂ → (∀ b, Ωb b) → ℂ) (T : Finset 𝔅)
    (hGdep : ∀ i s, DepOn (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G i s))
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, blocksOf m₀ j Ω (Lab.ysite y) ⊆ T →
      (A (s : ℂ)).H y = (A' (s : ℂ)).H y)
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i, blocksOf m₀ j Ω (Lab.ysite (y0 i)) ⊆ T →
      G i (s : ℂ) = G' i (s : ℂ)) :
    gsumCoeff μ Lab A y0 G T = gsumCoeff μ Lab A' y0 G' T := by
  unfold gsumCoeff
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  unfold Gsum
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Gst_congr μ μ (A (s : ℂ)) (A' (s : ℂ)).H _ T (hGdep i _) (fun _ _ => rfl)
    (hA s hs) (hG s hs i)

/-- **Congruence of `gsumCoeff` in the external variables**: if the activity of each label and each
mark depend on the external variable `θ` only through its restriction to the sites of the label,
then the coefficient at `T` depends on `θ` only through its restriction to `Ŷ(sitesOf T)`. -/
theorem gsumCoeff_ext_congr {E : Type*} {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κ0 Kc : ℝ}
    (A : (CTorus d L N₁ m₁ K → E) → ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G : (CTorus d L N₁ m₁ K → E) → ι → ℂ → (∀ b, Ωb b) → ℂ)
    (hdep : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y (θ θ' : CTorus d L N₁ m₁ K → E),
      (∀ z ∈ Lab.ysite y, θ z = θ' z) → (A θ (s : ℂ)).H y = (A θ' (s : ℂ)).H y)
    (hGdep : ∀ θ i s, DepOn (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G θ i s))
    (hGθ : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i (θ θ' : CTorus d L N₁ m₁ K → E),
      (∀ z ∈ Lab.ysite (y0 i), θ z = θ' z) → G θ i (s : ℂ) = G θ' i (s : ℂ))
    (T : Finset 𝔅) {θ θ' : CTorus d L N₁ m₁ K → E}
    (hagree : ∀ z ∈ Yhat Ω (sitesOf T), θ z = θ' z) :
    gsumCoeff μ Lab (A θ) y0 (G θ) T = gsumCoeff μ Lab (A θ') y0 (G θ') T := by
  unfold gsumCoeff
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  unfold Gsum
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Gst_ext_congr μ hN hj hΩ (fun θ => A θ (s : ℂ)) (hdep s hs) (y0 i)
    (fun θ => G θ i (s : ℂ)) (fun θ => hGdep θ i _) (hGθ s hs i) T hagree

end Raw

section Interp

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {X : Type*} [MeasurableSpace X]
  {ν : Measure X} {m₀ : ℕ} {BS : ProdSplit ν d L N₁ m₁ K m₀} {W : ℝ → X → ℂ} {f : ℝ → X → ℂ}

/-- **The canonical term `E(T)` of the interpolation average** (Theorem 3.1 (a) interpolation part,
(c), (d), (e)): `∫₀¹ ∑ᵢ G*(Y₀ᵢ, T)(s) ds`, with the label system, activities and marks of
`InterpMarks I`. -/
noncomputable def interpCoeff (I : InterpMarks ν BS W f) (T : Finset (CubeB (d := d) (L := L)
    (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)) : ℂ :=
  gsumCoeff BS.μ I.Lab I.A I.y0 I.G T

open Classical in
/-- `interpAvg_expansion_of_input` for the canonical coefficients `interpCoeff I`. -/
theorem interpCoeff_spec (I : InterpMarks ν BS W f) :
    interpAvg ν W f = ∑ T, interpCoeff I T ∧
    ∀ T, ‖interpCoeff I T‖ ≤ CPE d L I.Kc I.κH I.κ0 I.κ' *
        (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) * Real.exp (-I.κ' * dExt T) := by
  obtain ⟨-, hint, hbd⟩ := avg_integral_expansion BS.μ I.hN le_rfl
    (Ω := Set.univ) (j := K) (fun z _ => ⟨cbase (cellSide L m₀ m₁ K) z, aligned_cbase z,
      mem_box_cbase (cellSide_pos (L := L) m₀ m₁ K) z, Set.subset_univ _⟩)
    I.isOpen I.seg I.A I.y0 I.G I.meas I.dep I.bound I.holA I.holG I.hκ0 I.hKc I.hεpos
    I.nonempty I.hF0 I.hκ' I.hκG I.hκ I.hε
  refine ⟨?_, hbd⟩
  unfold interpCoeff gsumCoeff
  rw [← hint]
  unfold interpAvg
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  exact avgFun_eq_avgPi_gen BS _ _ s (I.A (s : ℂ)).H (fun Φ => ∑ i, I.G i (s : ℂ) Φ)
    (I.A (s : ℂ)).meas (Finset.measurable_sum _ fun i _ => I.meas i _) (I.hW s hs) (I.hF s hs)

open Classical in
/-- `interpAvg_expansion_of_input`, re-derived from `interpCoeff_spec`. -/
theorem interpAvg_expansion_of_interpCoeff (I : InterpMarks ν BS W f) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) → ℂ,
      interpAvg ν W f = ∑ T, E T ∧
      ∀ T, ‖E T‖ ≤ CPE d L I.Kc I.κH I.κ0 I.κ' *
          (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) * Real.exp (-I.κ' * dExt T) :=
  ⟨interpCoeff I, (interpCoeff_spec I).1, (interpCoeff_spec I).2⟩

open Classical in
/-- **Theorem 3.1 (c), (d), (e), canonical form**: under the size bound `B` of the marks. -/
theorem interpCoeff_bound (I : InterpMarks ν BS W f) {B : ℝ}
    (hB : CPE d L I.Kc I.κH I.κ0 I.κ' *
      (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ B) :
    interpAvg ν W f = ∑ T, interpCoeff I T ∧
      ∀ T, ‖interpCoeff I T‖ ≤ B * Real.exp (-I.κ' * dExt T) :=
  ⟨(interpCoeff_spec I).1, fun T =>
    ((interpCoeff_spec I).2 T).trans (mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le)⟩

open Classical in
/-- **Theorem 3.1 (c)** for `interpCoeff`. -/
theorem thm31c_coeff (I : InterpMarks ν BS W f) {κa βk : ℝ} (hκa : I.κ' = κa)
    (hB : CPE d L I.Kc I.κH I.κ0 I.κ' *
      (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ βk⁻¹) :
    interpAvg ν W f = ∑ T, interpCoeff I T ∧
      ∀ T, ‖interpCoeff I T‖ ≤ βk⁻¹ * Real.exp (-κa * dExt T) := by
  subst hκa; exact interpCoeff_bound I hB

open Classical in
/-- **Theorem 3.1 (d)** for `interpCoeff`. -/
theorem thm31d_coeff (I : InterpMarks ν BS W f) {κb β' : ℝ} (m : ℕ) (hκb : I.κ' = κb)
    (hB : CPE d L I.Kc I.κH I.κ0 I.κ' *
      (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ (1 / 2) * β' ^ (-(m : ℤ) - 1)) :
    interpAvg ν W f = ∑ T, interpCoeff I T ∧
      ∀ T, ‖interpCoeff I T‖ ≤ (1 / 2) * β' ^ (-(m : ℤ) - 1) * Real.exp (-κb * dExt T) := by
  subst hκb; exact interpCoeff_bound I hB

open Classical in
/-- **Theorem 3.1 (e)** for `interpCoeff`. -/
theorem thm31e_coeff (I : InterpMarks ν BS W f) {κb β' : ℝ} (n : ℕ) (hκb : I.κ' = κb)
    (hB : CPE d L I.Kc I.κH I.κ0 I.κ' *
      (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ (1 / 2) * β' ^ (-(n : ℤ))) :
    interpAvg ν W f = ∑ T, interpCoeff I T ∧
      ∀ T, ‖interpCoeff I T‖ ≤ (1 / 2) * β' ^ (-(n : ℤ)) * Real.exp (-κb * dExt T) := by
  subst hκb; exact interpCoeff_bound I hB

end Interp

section E1

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ} {m₀ : ℕ}
  {BS : BlockSplit S m₀} {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}

/-- **The canonical term `ℰ₀(z, T)` of Theorem 3.1 (a)** (whole-lattice case): the determinant term
`D.term T` of `-½ ∑_{y ∈ B(z)} tr 𝕃(y,y)` plus the interpolation term `interpCoeff I T` of the
integral of the marks. -/
noncomputable def e1Coeff (I : E1Marks S C BS z) {κ'' cdet : ℝ} (D : DetExpansion S m₀ z κ'' cdet)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) : ℂ :=
  D.term T + interpCoeff I T

open Classical in
/-- **Theorem 3.1 (a) for the canonical coefficients `e1Coeff`** (the three clauses of
`thm31a_of_input`: the interpolation part `E1loc`, the sum identity for `E0loc`, the bound). -/
theorem thm31a_coeff (I : E1Marks S C BS z) {κ'' cdet : ℝ} (hκ'' : I.κ' ≤ κ'')
    (D : DetExpansion S m₀ z κ'' cdet) :
    S.E1loc C z = ∑ T, interpCoeff I T ∧
    S.E0loc C z = ∑ T, e1Coeff I D T ∧
    ∀ T, ‖e1Coeff I D T‖ ≤ (CPE d L I.Kc I.κH I.κ0 I.κ' *
          (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) + cdet) *
        Real.exp (-I.κ' * dExt T) := by
  obtain ⟨h1, h2⟩ := interpCoeff_spec I
  refine ⟨h1, ?_, fun T => ?_⟩
  · unfold e1Coeff
    rw [Finset.sum_add_distrib, ← D.sum_eq, ← h1]
    rfl
  · unfold e1Coeff
    refine (norm_add_le _ _).trans ?_
    have hd : ‖D.term T‖ ≤ cdet * Real.exp (-I.κ' * dExt T) := by
      refine (D.bound T).trans ?_
      have hc : 0 ≤ cdet := by
        have := (D.bound T).trans' (norm_nonneg _)
        rcases le_or_gt 0 cdet with h | h
        · exact h
        · nlinarith [Real.exp_pos (-κ'' * dExt T)]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc
      nlinarith [dExt_nonneg (m₀ := m₀) (j := k + 1) (Ω := Set.univ) T]
    nlinarith [h2 T]

open Classical in
/-- `thm31a_of_input`, re-derived from `thm31a_coeff`: the landed existential statement is
witnessed by `e1Coeff I D`. -/
theorem thm31a_of_e1Coeff (I : E1Marks S C BS z) {κ'' cdet : ℝ} (hκ'' : I.κ' ≤ κ'')
    (D : DetExpansion S m₀ z κ'' cdet) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ,
      S.E0loc C z = ∑ T, E T ∧
      ∀ T, ‖E T‖ ≤ (CPE d L I.Kc I.κH I.κ0 I.κ' *
          (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) + cdet) *
        Real.exp (-I.κ' * dExt T) :=
  ⟨e1Coeff I D, (thm31a_coeff I hκ'' D).2.1, (thm31a_coeff I hκ'' D).2.2⟩

/-- The canonical term unfolds to the determinant term plus `gsumCoeff` of the data of `I`. -/
theorem e1Coeff_eq (I : E1Marks S C BS z) {κ'' cdet : ℝ} (D : DetExpansion S m₀ z κ'' cdet)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    e1Coeff I D T = D.term T + gsumCoeff BS.μ I.Lab I.A I.y0 I.G T := rfl

/-- **Congruence of `e1Coeff`**: on a common label system (`Lab`, `y0`), the coefficient at `T`
depends on the determinant term at `T` and on the activities and marks only through the labels whose
cubes lie in `T` (`gsumCoeff_congr`).  Two `E1Marks` with different label types are compared through
their data on a common label system; the statement is about the data `A, A', G, G'`. -/
theorem e1Coeff_congr (I : E1Marks S C BS z) {κ'' cdet : ℝ} (D : DetExpansion S m₀ z κ'' cdet)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    {εH' κH' κ0' Kc' : ℝ} (A' : ℂ → LabelAct I.Lab BS.Ωb εH' κH' κ0' Kc')
    (G' : I.ι → ℂ → (∀ b, BS.Ωb b) → ℂ) (dt : ℂ) (hD : D.term T = dt)
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y,
      blocksOf m₀ (k + 1) Set.univ (I.Lab.ysite y) ⊆ T → (I.A (s : ℂ)).H y = (A' (s : ℂ)).H y)
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i,
      blocksOf m₀ (k + 1) Set.univ (I.Lab.ysite (I.y0 i)) ⊆ T → I.G i (s : ℂ) = G' i (s : ℂ)) :
    e1Coeff I D T = dt + gsumCoeff BS.μ I.Lab A' I.y0 G' T := by
  rw [e1Coeff_eq, hD]
  exact congrArg _ (gsumCoeff_congr BS.μ I.A A' I.y0 I.G G' T I.dep hA hG)

end E1

end Balaban.Fluctuation
