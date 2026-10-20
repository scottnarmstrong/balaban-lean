/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.NewLevelCoeffBg
public import Balaban.Fluctuation.ParamMarkFamilyTrunc
public import Balaban.Inhabited.E0CoeffFamilyRotCoef

/-!
# The coefficient of a polymer recomputed from the labels inside it (`NewLevelCoeffLoc`)

P3 pp. 78-79: the term of the polymer `T` recomputed on the generating set `𝔹_{k+1}(Y)` reads the
activities of the labels inside `T` and the marks of the anchors inside `T` only (the interpolation
coefficient at `T` depends on nothing else, `Gst_congr`).  The recomputed coefficient of `T`
(route R-LOC) is therefore written with the activities of the labels inside `T` and the marks of the
anchors inside `T`, each evaluated at the configuration restricted to the blocks of its label (a
fixed reference configuration `Φ₀` off them), and `0` for the other labels and anchors.  This
form is a formula of the parameter at every parameter, it is the coefficient of a bundled
`ParamMarkFamily` on the analyticity chart (`paramMarkFamily_trunc` with the class of the labels
inside `T`), and it agrees with the step's coefficient at matched data through the step's own
locality.

* `InPoly T Y`: the blocks of `Y` lie in `T`;
* `locAct`: the activities of the labels inside `T` at the restricted configuration, `0` otherwise;
* `newLevelCoeffLoc`: the formula `newLevelCoeffBg` with `locAct` and the truncated restricted marks
  `truncMark … (InPoly T)`; `newLevelCoeffLoc_eq` unfolds it;
* `newLevelCoeffBg_eq_loc_of_agree`: **the replacement identity with the local formula** (the form
  of (A5)): the coefficient of a bundled system equals the local formula of functions that agree
  with it on the labels and anchors inside `T`;
* `newLevelCoeffLoc_congr`: two local formulas whose determinant parts agree and whose activities and
  marks agree on the labels and anchors inside `T` are equal (the form of (A3));
* `newLevelCoeffLoc_eq_gsumCoeff`: on a bundled family whose activities are `locAct`, the local
  formula is the determinant part plus `gsumCoeff` (the form of (A1), (A2), (A4));
* `newLevelCoeffLoc_analyticOnNhd`, `norm_newLevelCoeffLoc_le`: analyticity and bound of the local
  formula from the fields of the activities and marks of the labels inside `T`;
* `newLevelCoeffLoc_rot`: covariance of the local formula under a measure-preserving equivalence of
  the block variables fixing `Φ₀`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.Background
  MeasureTheory

section Loc

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
  Set.univ

/-- **The labels inside a polymer `T`**: the blocks of `Y` lie in `T`. -/
def InPoly (T : Finset 𝔅) (Y : Set (CTorus d L N₁ m₁ (k + 1))) : Prop :=
  blocksOf 1 (k + 1) Set.univ Y ⊆ T

variable {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ →
  Type*} {Lb : Type*} {ι : Type*} {E : Type*}

/-- **The activities of the labels inside `T` at the restricted configuration**: `H θ u y` at the
configuration restricted to the blocks of `y` (`Φ₀` off them) when the blocks of `y` lie in `T`,
`0` otherwise. -/
noncomputable def locAct (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ Lb) (T : Finset 𝔅) (Φ₀ : ∀ b, Ωb b)
    (H : E → ℂ → Lb → (∀ b, Ωb b) → ℂ) : E → ℂ → Lb → (∀ b, Ωb b) → ℂ :=
  fun θ u y Φ => truncAct Lab (InPoly T) H θ u y
    (restrConf (blocksOf 1 (k + 1) Set.univ (Lab.ysite y)) Φ₀ Φ)

theorem locAct_of_pos (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ Lb) {T : Finset 𝔅} (Φ₀ : ∀ b, Ωb b)
    (H : E → ℂ → Lb → (∀ b, Ωb b) → ℂ) (θ : E) (u : ℂ) {y : Lb} (hy : InPoly T (Lab.ysite y))
    (Φ : ∀ b, Ωb b) : locAct Lab T Φ₀ H θ u y Φ =
      H θ u y (restrConf (blocksOf 1 (k + 1) Set.univ (Lab.ysite y)) Φ₀ Φ) := by
  classical
  unfold locAct
  rw [truncAct_of_pos Lab H θ u hy]

theorem locAct_of_neg (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ Lb) {T : Finset 𝔅} (Φ₀ : ∀ b, Ωb b)
    (H : E → ℂ → Lb → (∀ b, Ωb b) → ℂ) (θ : E) (u : ℂ) {y : Lb} (hy : ¬ InPoly T (Lab.ysite y))
    (Φ : ∀ b, Ωb b) : locAct Lab T Φ₀ H θ u y Φ = 0 := by
  classical
  unfold locAct
  rw [truncAct_of_neg Lab H θ u hy]

variable {ϱb : ℝ} (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb)
  [∀ b, MeasurableSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
  [Fintype Lb] [Fintype ι]

/-- **The coefficient of a polymer `T` recomputed from the labels inside it** (P3 pp. 78-79): the
formula `newLevelCoeffBg` on `Gb` whose activities are those of the labels inside `T` at the
restricted configuration (`locAct`) and whose marks are those of the anchors inside `T` at the
configuration restricted to the blocks of the anchor (`truncMark … (InPoly T)`). -/
noncomputable def newLevelCoeffLoc (a : ℕ → ℝ) (aT ν ρ : ℝ) (Zb : Finset (unitPts Gb))
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb)
    (Φ₀ : ∀ b, Ωb b) (H : physParamBg N Gb → ℂ → Lb → (∀ b, Ωb b) → ℂ) (y0 : ι → Lb)
    (G : physParamBg N Gb → ι → ℂ → (∀ b, Ωb b) → ℂ) (θ : physParamBg N Gb) (T : Finset 𝔅) :
    ℂ :=
  newLevelCoeffBg Gb μ a aT ν ρ Zb Lab (locAct Lab T Φ₀ H) y0
    (truncMark Lab (InPoly T) y0 Φ₀ G) θ T

/-- The local formula unfolded: the determinant part plus the interpolation integral of the
local activities and the truncated restricted marks. -/
theorem newLevelCoeffLoc_eq (a : ℕ → ℝ) (aT ν ρ : ℝ) (Zb : Finset (unitPts Gb))
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb)
    (Φ₀ : ∀ b, Ωb b) (H : physParamBg N Gb → ℂ → Lb → (∀ b, Ωb b) → ℂ) (y0 : ι → Lb)
    (G : physParamBg N Gb → ι → ℂ → (∀ b, Ωb b) → ℂ) (θ : physParamBg N Gb) (T : Finset 𝔅) :
    newLevelCoeffLoc Gb μ a aT ν ρ Zb Lab Φ₀ H y0 G θ T =
      newLevelDetBg Gb a aT ν ρ Zb θ T + ∫ s in (0 : ℝ)..1,
        Gsum μ Lab (locAct Lab T Φ₀ H θ (s : ℂ)) y0
          (fun i => truncMark Lab (InPoly T) y0 Φ₀ G θ i (s : ℂ)) T := rfl

/-- **The replacement identity with the local formula** (P3 p. 79; the form of (A5)): the
coefficient of a system with bundled activities `A` on `Gp` at `θ_p` equals the local formula on
`Gb` at `θ` of activities `H` and marks `G'` given as functions, when the determinant parts agree at
`T`, the activities agree (for `s ∈ [0, 1]`) on the labels inside `T` and the marks agree on the
anchors inside `T`; the step's marks are local (`hGdep`), and the step's activities are local
because they are bundled. -/
theorem newLevelCoeffBg_eq_loc_of_agree {ϱp : ℝ}
    (Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱp) (a : ℕ → ℝ) (aT ν ρ : ℝ)
    (Zp : Finset (unitPts Gp)) (Zb : Finset (unitPts Gb))
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb)
    {εH κH κ0 Kc : ℝ} (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G : ι → ℂ → (∀ b, Ωb b) → ℂ) (θp : physParamBg N Gp) (Φ₀ : ∀ b, Ωb b)
    (H : physParamBg N Gb → ℂ → Lb → (∀ b, Ωb b) → ℂ)
    (G' : physParamBg N Gb → ι → ℂ → (∀ b, Ωb b) → ℂ) (θ : physParamBg N Gb) (T : Finset 𝔅)
    (hdet : newLevelDetBg Gp a aT ν ρ Zp θp T = newLevelDetBg Gb a aT ν ρ Zb θ T)
    (hGdep : ∀ i s, DepOn (blocksOf 1 (k + 1) Set.univ (Lab.ysite (y0 i))) (G i s))
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y,
      blocksOf 1 (k + 1) Set.univ (Lab.ysite y) ⊆ T → (A (s : ℂ)).H y = H θ (s : ℂ) y)
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i,
      blocksOf 1 (k + 1) Set.univ (Lab.ysite (y0 i)) ⊆ T → G i (s : ℂ) = G' θ i (s : ℂ)) :
    newLevelDetBg Gp a aT ν ρ Zp θp T + gsumCoeff μ Lab A y0 G T =
      newLevelCoeffLoc Gb μ a aT ν ρ Zb Lab Φ₀ H y0 G' θ T := by
  unfold newLevelCoeffLoc
  refine newLevelCoeffBg_eq_of_agree Gb μ Gp a aT ν ρ Zp Zb Lab A y0 G θp _ _ θ T hdet hGdep
    (fun s hs y hy => ?_) (fun s hs i hi => ?_)
  · funext Φ
    rw [locAct_of_pos Lab Φ₀ H θ (s : ℂ) hy, ← hA s hs y hy]
    exact ((A (s : ℂ)).dep y _ _ (restrConf_agree _ Φ₀ Φ)).symm
  · funext Φ
    rw [truncMark_of_pos Lab y0 Φ₀ G' θ (s : ℂ) hi, ← hG s hs i hi]
    exact (hGdep i (s : ℂ) _ _ (restrConf_agree _ Φ₀ Φ)).symm

/-- **The local formula reads the labels and anchors inside `T` only** (the form of (A3)): two local
formulas at `θ` and `θ'` whose determinant parts agree at `T`, whose activities agree (for
`s ∈ [0, 1]`, at every configuration) on the labels inside `T` and whose marks agree on the anchors
inside `T` are equal. -/
theorem newLevelCoeffLoc_congr (a : ℕ → ℝ) (aT ν ρ : ℝ) (Zb : Finset (unitPts Gb))
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb)
    (Φ₀ : ∀ b, Ωb b) (H H' : physParamBg N Gb → ℂ → Lb → (∀ b, Ωb b) → ℂ) (y0 : ι → Lb)
    (G G' : physParamBg N Gb → ι → ℂ → (∀ b, Ωb b) → ℂ) (θ θ' : physParamBg N Gb)
    (T : Finset 𝔅)
    (hdet : newLevelDetBg Gb a aT ν ρ Zb θ T = newLevelDetBg Gb a aT ν ρ Zb θ' T)
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, InPoly T (Lab.ysite y) → ∀ Φ,
      H θ (s : ℂ) y Φ = H' θ' (s : ℂ) y Φ)
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i, InPoly T (Lab.ysite (y0 i)) → ∀ Φ,
      G θ i (s : ℂ) Φ = G' θ' i (s : ℂ) Φ) :
    newLevelCoeffLoc Gb μ a aT ν ρ Zb Lab Φ₀ H y0 G θ T =
      newLevelCoeffLoc Gb μ a aT ν ρ Zb Lab Φ₀ H' y0 G' θ' T := by
  classical
  rw [newLevelCoeffLoc_eq, newLevelCoeffLoc_eq, hdet]
  refine congrArg (fun x => newLevelDetBg Gb a aT ν ρ Zb θ' T + x)
    (intervalIntegral.integral_congr fun s hs => ?_)
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hA' : locAct Lab T Φ₀ H θ (s : ℂ) = locAct Lab T Φ₀ H' θ' (s : ℂ) := by
    funext y Φ
    by_cases hy : InPoly T (Lab.ysite y)
    · rw [locAct_of_pos Lab Φ₀ H θ _ hy, locAct_of_pos Lab Φ₀ H' θ' _ hy]
      exact hA s hs y hy _
    · rw [locAct_of_neg Lab Φ₀ H θ _ hy, locAct_of_neg Lab Φ₀ H' θ' _ hy]
  have hG' : (fun i => truncMark Lab (InPoly T) y0 Φ₀ G θ i (s : ℂ)) =
      fun i => truncMark Lab (InPoly T) y0 Φ₀ G' θ' i (s : ℂ) := by
    funext i
    by_cases hi : InPoly T (Lab.ysite (y0 i))
    · rw [truncMark_of_pos Lab y0 Φ₀ G θ _ hi, truncMark_of_pos Lab y0 Φ₀ G' θ' _ hi]
      funext Φ
      exact hG s hs i hi _
    · rw [truncMark_of_neg Lab y0 Φ₀ G θ _ hi, truncMark_of_neg Lab y0 Φ₀ G' θ' _ hi]
  show Gsum μ Lab (locAct Lab T Φ₀ H θ (s : ℂ)) y0
      (fun i => truncMark Lab (InPoly T) y0 Φ₀ G θ i (s : ℂ)) T =
    Gsum μ Lab (locAct Lab T Φ₀ H' θ' (s : ℂ)) y0
      (fun i => truncMark Lab (InPoly T) y0 Φ₀ G' θ' i (s : ℂ)) T
  rw [hA', hG']

/-- **On a bundled family with the local activities the local formula is the determinant part plus
`gsumCoeff`.** -/
theorem newLevelCoeffLoc_eq_gsumCoeff (a : ℕ → ℝ) (aT ν ρ : ℝ) (Zb : Finset (unitPts Gb))
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb)
    (Φ₀ : ∀ b, Ωb b) (H : physParamBg N Gb → ℂ → Lb → (∀ b, Ωb b) → ℂ) (y0 : ι → Lb)
    (G : physParamBg N Gb → ι → ℂ → (∀ b, Ωb b) → ℂ) (T : Finset 𝔅) {εH κH κ0 Kc : ℝ}
    (A : physParamBg N Gb → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (hAH : ∀ θ u y Φ, (A θ u).H y Φ = locAct Lab T Φ₀ H θ u y Φ) (θ : physParamBg N Gb) :
    newLevelCoeffLoc Gb μ a aT ν ρ Zb Lab Φ₀ H y0 G θ T =
      newLevelDetBg Gb a aT ν ρ Zb θ T +
        gsumCoeff μ Lab (A θ) y0 (truncMark Lab (InPoly T) y0 Φ₀ G θ) T := by
  rw [newLevelCoeffLoc_eq, gsumCoeff_eq_integral]
  refine congrArg (fun x => newLevelDetBg Gb a aT ν ρ Zb θ T + x)
    (intervalIntegral.integral_congr fun s _ => ?_)
  have h : (A θ (s : ℂ)).H = locAct Lab T Φ₀ H θ (s : ℂ) := by
    funext y Φ
    exact hAH θ (s : ℂ) y Φ
  simp only [h]

open Classical in
/-- **Analyticity and bound of the local formula** (the form of (A1), (A2)): if the activities of the
labels inside `T` are measurable, bounded by `ε_H e^{-κ_H 𝗱(y)}`, analytic in `(θ, u)` on `V × 𝒰` at
every configuration and continuous in the configuration on `V × 𝒰`, with the entropy of the labels,
and the marks of the anchors inside `T` have the fields of a `ParamMarkFamily` with the bounds
`F₀ᵢ e^{-κ_G 𝗱(y0 i)}`, then under the numerical conditions of Theorem 3.4 the local formula is
analytic on `V` where its determinant part is, and differs from its determinant part by at most
`CPE · ∑ᵢ F₀ᵢ e^{-κ₀ 𝗱(y0 i)} · e^{-κ' d_ext(T)}` on `V`. -/
theorem newLevelCoeffLoc_analytic_bound [∀ b, TopologicalSpace (Ωb b)]
    [∀ b, OpensMeasurableSpace (Ωb b)] [∀ b, SecondCountableTopology (Ωb b)]
    (hN : L ^ 1 ∣ N₁) (a : ℕ → ℝ) (aT ν ρ : ℝ) (Zb : Finset (unitPts Gb))
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb)
    (Φ₀ : ∀ b, Ωb b) (H : physParamBg N Gb → ℂ → Lb → (∀ b, Ωb b) → ℂ) (y0 : ι → Lb)
    (G : physParamBg N Gb → ι → ℂ → (∀ b, Ωb b) → ℂ) (T : Finset 𝔅)
    {εH κH κ0 Kc κG κ' : ℝ} {F0 : ι → ℝ}
    (hmeas : ∀ θ u y, InPoly T (Lab.ysite y) → Measurable (H θ u y))
    (hbd : ∀ θ u y Φ, InPoly T (Lab.ysite y) → ‖H θ u y Φ‖ ≤ εH * Real.exp (-κH * Lab.dl y))
    (hent : ∀ b : 𝔅, ∑ y : Lb, (if box b.1 (cellSide L 1 m₁ (k + 1)) ⊆ Lab.ysite y then
      Real.exp (-κ0 * Lab.dl y) else 0) ≤ Kc)
    {V : Set (physParamBg N Gb)} {𝒰 : Set ℂ} {Q : Set (∀ b, Ωb b)}
    (hV : IsOpen V) (hU : IsOpen 𝒰) (hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰)
    (hQ : IsCompact Q) (hQm : MeasurableSet Q) (hcar : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q)
    (hhol : ∀ y, InPoly T (Lab.ysite y) → ∀ Φ,
      AnalyticOnNhd ℂ (fun p : physParamBg N Gb × ℂ => H p.1 p.2 y Φ) (V ×ˢ 𝒰))
    (hcont : ∀ y, InPoly T (Lab.ysite y) → ∀ θ ∈ V, ∀ u ∈ 𝒰, Continuous (H θ u y))
    (hGmeas : ∀ θ i u, InPoly T (Lab.ysite (y0 i)) → Measurable (G θ i u))
    (hGbd : ∀ θ i u Φ, InPoly T (Lab.ysite (y0 i)) →
      ‖G θ i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i)))
    (hGhol : ∀ i, InPoly T (Lab.ysite (y0 i)) → ∀ Φ,
      AnalyticOnNhd ℂ (fun p : physParamBg N Gb × ℂ => G p.1 i p.2 Φ) (V ×ˢ 𝒰))
    (hGcont : ∀ i, InPoly T (Lab.ysite (y0 i)) → ∀ θ ∈ V, ∀ u ∈ 𝒰, Continuous (G θ i u))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hι : Nonempty ι) (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hdet : AnalyticOnNhd ℂ (fun θ => newLevelDetBg Gb a aT ν ρ Zb θ T) V) :
    AnalyticOnNhd ℂ (fun θ => newLevelCoeffLoc Gb μ a aT ν ρ Zb Lab Φ₀ H y0 G θ T) V ∧
      ∀ θ ∈ V, ‖newLevelCoeffLoc Gb μ a aT ν ρ Zb Lab Φ₀ H y0 G θ T‖ ≤
        ‖newLevelDetBg Gb a aT ν ρ Zb θ T‖ + CPE d L Kc κH κ0 κ' *
          (∑ i, F0 i * Real.exp (-κ0 * Lab.dl (y0 i))) * Real.exp (-κ' * dExt T) := by
  obtain ⟨A, hAH, ⟨hfam⟩⟩ := paramMarkFamily_trunc μ Lab (InPoly T) Φ₀ H hmeas hbd hεpos.le
    hent y0 G κG F0 (fun i => (hF0 i).le) hV hU hseg hQ hQm hcar hhol hcont hGmeas hGbd
    hGhol hGcont
  have hΩ : IsPiUnion 1 (k + 1) (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))) := isPiUnion_univ_K
  have heq : ∀ θ, newLevelCoeffLoc Gb μ a aT ν ρ Zb Lab Φ₀ H y0 G θ T =
      newLevelDetBg Gb a aT ν ρ Zb θ T +
        gsumCoeff μ Lab (A θ) y0 (truncMark Lab (InPoly T) y0 Φ₀ G θ) T :=
    newLevelCoeffLoc_eq_gsumCoeff Gb μ a aT ν ρ Zb Lab Φ₀ H y0 G T A (fun θ u y Φ => hAH θ u y Φ)
  refine ⟨fun θ hθ => ?_, fun θ hθ => ?_⟩
  · have h := (hdet θ hθ).add
      (gsumCoeff_analyticOnNhd μ hN le_rfl hΩ hfam hκ0 hKc hεpos hF0 hκ' hκG hκ hε T θ hθ)
    exact h.congr (Filter.Eventually.of_forall fun θ' => (heq θ').symm)
  · rw [heq θ]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    exact norm_gsumCoeff_le μ hN le_rfl hΩ A y0 (truncMark Lab (InPoly T) y0 Φ₀ G) V
      hfam.meas (fun θ i u => truncMark_dep Lab (InPoly T) y0 Φ₀ G θ i u) hfam.bound hκ0 hKc
      hεpos hι hF0 hκ' hκG hκ hε T θ hθ

open Classical in
/-- **Covariance of the local formula** (the form of (A4)): let `E` be a blockwise
measure-preserving equivalence of the block variables fixing the reference configuration `Φ₀`, and
`Q` an almost sure set of configurations closed under the restriction to sets of blocks.  If the
determinant parts at `θ'` and `θ` agree at `T`, the activities of the labels inside `T` satisfy
`H θ' s y (E Φ) = H θ s y Φ` and the marks of the anchors inside `T` satisfy
`G θ' i s (E Φ) = G θ i s Φ` for `s ∈ [0, 1]`, `Φ ∈ Q`, and both are bundled on the analyticity data
of `newLevelCoeffLoc_analytic_bound` at every parameter, then the local formulas at `θ'` and `θ`
agree. -/
theorem newLevelCoeffLoc_rot (a : ℕ → ℝ) (aT ν ρ : ℝ) (Zb : Finset (unitPts Gb))
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb)
    (Φ₀ : ∀ b, Ωb b) (H : physParamBg N Gb → ℂ → Lb → (∀ b, Ωb b) → ℂ) (y0 : ι → Lb)
    (G : physParamBg N Gb → ι → ℂ → (∀ b, Ωb b) → ℂ) (T : Finset 𝔅) {εH κH κ0 Kc : ℝ}
    (A : physParamBg N Gb → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (hAH : ∀ θ u y Φ, (A θ u).H y Φ = locAct Lab T Φ₀ H θ u y Φ)
    (E : ∀ b, Ωb b ≃ᵐ Ωb b) (hE : ∀ b, MeasurePreserving (E b) (μ b) (μ b))
    (hE₀ : ∀ b, E b (Φ₀ b) = Φ₀ b) {Q : Set (∀ b, Ωb b)} (hQ : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q)
    (hQr : ∀ Φ ∈ Q, ∀ S : Finset 𝔅, restrConf S Φ₀ Φ ∈ Q) {θ θ' : physParamBg N Gb}
    (hdet : newLevelDetBg Gb a aT ν ρ Zb θ' T = newLevelDetBg Gb a aT ν ρ Zb θ T)
    (hH : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, InPoly T (Lab.ysite y) → ∀ Φ ∈ Q,
      H θ' (s : ℂ) y (fun b => E b (Φ b)) = H θ (s : ℂ) y Φ)
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i, InPoly T (Lab.ysite (y0 i)) → ∀ Φ ∈ Q,
      G θ' i (s : ℂ) (fun b => E b (Φ b)) = G θ i (s : ℂ) Φ) :
    newLevelCoeffLoc Gb μ a aT ν ρ Zb Lab Φ₀ H y0 G θ' T =
      newLevelCoeffLoc Gb μ a aT ν ρ Zb Lab Φ₀ H y0 G θ T := by
  have hres : ∀ (S : Finset 𝔅) (Φ : ∀ b, Ωb b),
      restrConf S Φ₀ (fun b => E b (Φ b)) = fun b => E b (restrConf S Φ₀ Φ b) := by
    intro S Φ
    funext b
    unfold restrConf
    split_ifs
    · rfl
    · exact (hE₀ b).symm
  rw [newLevelCoeffLoc_eq_gsumCoeff Gb μ a aT ν ρ Zb Lab Φ₀ H y0 G T A hAH θ',
    newLevelCoeffLoc_eq_gsumCoeff Gb μ a aT ν ρ Zb Lab Φ₀ H y0 G T A hAH θ, hdet]
  refine congrArg (fun x => newLevelDetBg Gb a aT ν ρ Zb θ T + x) ?_
  refine Balaban.Polymer.TwoTorusStep.gsumCoeff_rot μ Lab (A θ) (A θ') y0
    (truncMark Lab (InPoly T) y0 Φ₀ G θ) (truncMark Lab (InPoly T) y0 Φ₀ G θ')
    (fun i u => truncMark_dep Lab (InPoly T) y0 Φ₀ G θ i u) T E hE hQ
    (fun s hs y Φ hΦ => ?_) (fun s hs i Φ hΦ => ?_)
  · rw [hAH, hAH]
    by_cases hy : InPoly T (Lab.ysite y)
    · rw [locAct_of_pos Lab Φ₀ H θ' _ hy, locAct_of_pos Lab Φ₀ H θ _ hy, hres]
      exact hH s hs y hy _ (hQr Φ hΦ _)
    · rw [locAct_of_neg Lab Φ₀ H θ' _ hy, locAct_of_neg Lab Φ₀ H θ _ hy]
  · by_cases hi : InPoly T (Lab.ysite (y0 i))
    · rw [truncMark_of_pos Lab y0 Φ₀ G θ' _ hi, truncMark_of_pos Lab y0 Φ₀ G θ _ hi]
      show G θ' i (s : ℂ) (restrConf _ Φ₀ fun b => E b (Φ b)) = G θ i (s : ℂ) (restrConf _ Φ₀ Φ)
      rw [hres]
      exact hG s hs i hi _ (hQr Φ hΦ _)
    · rw [truncMark_of_neg Lab y0 Φ₀ G θ' _ hi, truncMark_of_neg Lab y0 Φ₀ G θ _ hi]

end Loc

end Balaban.Fluctuation
