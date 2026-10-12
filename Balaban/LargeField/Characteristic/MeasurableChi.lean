module

public import Balaban.LargeField.Characteristic.Measurable
public import Balaban.LargeField.Characteristic.Functions
import Mathlib.Tactic.Linarith

/-!
# Measurability of the characteristic functions (Part II, Lemma II.3.3)

Each characteristic function of Definition II.3.2 is the indicator of a Borel set of real
configurations (`measurableSet_chiKProp`, `measurableSet_chiPrimeNewProp`,
`measurableSet_chiPrimeOldProp`, `measurableSet_chiFluctProp`), hence a Borel function
(`measurable_chiK`, `measurable_chiNext`, `measurable_chiPrimeNew`, `measurable_chiPrimeOld`,
`measurable_chiFluct`), and so are the products over cube sets (`measurable_cubeProd`,
`measurable_cubeProdCompl`). The hypothesis `BgHyp` is the standing hypothesis of Theorem 5.2 on
the generating set, the weights `a` and the mass `μ`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background MeasureTheory

set_option linter.unusedSectionVars false

theorem measurable_charFn {X : Type*} [MeasurableSpace X] {P : X → Prop}
    (h : MeasurableSet {x | P x}) : Measurable (charFn P) :=
  measurable_const.indicator h

theorem measurable_cubeProd {d n : ℕ} {X : Type*} [MeasurableSpace X] {χ : Torus d n → X → ℝ}
    (hχ : ∀ y, Measurable (χ y)) (A : Finset (Torus d n)) : Measurable (cubeProd χ A) := by
  unfold cubeProd
  exact Finset.measurable_prod _ fun y _ => hχ y

theorem measurable_cubeProdCompl {d n : ℕ} {X : Type*} [MeasurableSpace X]
    {χ : Torus d n → X → ℝ} (hχ : ∀ y, Measurable (χ y)) (A : Finset (Torus d n)) :
    Measurable (cubeProdCompl χ A) := by
  unfold cubeProdCompl
  exact Finset.measurable_prod _ fun y _ => measurable_const.sub (hχ y)

section Chi

variable {d M1 N₁ L N : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

/-- The coordinates of the single-scale lifted data are continuous in the configuration. -/
theorem realFamily_cubeData {q : ℕ} (h : Fin N → ℝ) (c n : ℕ) (y0 : Torus d n) :
    RealFamily (fun ψ : BlockCfg d (M1 * N₁) L q q N => cubeData (M1 := M1) (N₁ := N₁)
      (L := L) (q := q) h c n y0 ψ) h where
  real := by
    intro ψ x i
    unfold cubeData liftSingle BgData.clip
    by_cases hx : x ∈ dataSites (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0)
    · simp [hx, blockLift, BlockCfg.toC]
    · simp [hx]
  hconst := by
    intro ψ x hx i
    unfold cubeData
    rw [liftSingle_h _ _ _ hx]
  Ψc := by
    intro x i
    unfold cubeData liftSingle BgData.clip
    by_cases hx : x ∈ dataSites (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0)
    · simp only [hx, ↓reduceIte, blockLift, BlockCfg.toC]
      exact Complex.continuous_ofReal.comp
        ((continuous_apply i).comp (continuous_apply (jBlock d L (M1 * N₁) q q x)))
    · simp [hx]
      exact continuous_const
  hc := by
    intro x i
    unfold cubeData
    by_cases hx : x ∈ (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0).Ω 1
    · simp only [liftSingle_h _ _ _ hx]
      exact continuous_const
    · simp only [(liftSingle _ _ _).h_zero x hx]
      exact continuous_const

/-- **Lemma II.3.3 (measurability)**: `{χ_q(□) = 1}` is Borel. -/
theorem measurableSet_chiKProp {q : ℕ} (a : ℕ → ℝ) (μ δ : ℝ) (h : Fin N → ℝ) (c n : ℕ)
    (H : BgHyp d L q (minSep L M1) a μ) (y0 : Torus d n) :
    MeasurableSet {ψ : BlockCfg d (M1 * N₁) L q q N | ChiKProp a μ δ h c n y0 ψ} :=
  measurableSet_reg H (realFamily_cubeData h c n y0) δ _ _

theorem measurable_chiK {q : ℕ} (a : ℕ → ℝ) (μ δ : ℝ) (h : Fin N → ℝ) (c n : ℕ)
    (H : BgHyp d L q (minSep L M1) a μ) (y0 : Torus d n) :
    Measurable (chiK (M1 := M1) (N₁ := N₁) (L := L) (q := q) (N := N) a μ δ h c n y0) :=
  measurable_charFn (measurableSet_chiKProp a μ δ h c n H y0)

/-- **Lemma II.3.3 (measurability)** for `χ_{k+1}(□')`. -/
theorem measurable_chiNext (k : ℕ) (a : ℕ → ℝ) (μ δ : ℝ) (h : Fin N → ℝ) (c n : ℕ)
    (H : BgHyp d L (k + 1) (minSep L M1) a μ) (y0 : Torus d n) :
    Measurable (chiNext (M1 := M1) (N₁ := N₁) (L := L) (N := N) a μ δ h c n k y0) :=
  measurable_chiK a μ δ h c n H y0


section Mixed

variable {k : ℕ} {c n : ℕ} (hm : N₁ * L ^ (k + 1 - (k + 1)) = c * n) (y0 : Torus d n)
  (Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1))))
  (hOm : IsBlockUnion L (M1 * N₁) (k + 1) (k + 1) Om) (h : Fin N → ℝ)

theorem realFamily_mixedData :
    RealFamily (fun p : BlockCfg d (M1 * N₁) L (k + 1) k N × BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N =>
      mixedData h hm y0 Om hOm p.1 p.2) h where
  real := by
    intro p x i
    unfold mixedData liftMixed BgData.clip
    by_cases hx : x ∈ dataSites (genCubeMixed hm y0 Om hOm)
    · by_cases hxO : x ∈ Om <;> simp [hx, hxO, mixedLift, blockLift, BlockCfg.toC]
    · simp [hx]
  hconst := by
    intro p x hx i
    unfold mixedData
    rw [liftMixed_h _ _ _ _ _ _ hx]
  Ψc := by
    intro x i
    unfold mixedData liftMixed BgData.clip
    by_cases hx : x ∈ dataSites (genCubeMixed hm y0 Om hOm)
    · by_cases hxO : x ∈ Om
      · simp only [hx, ↓reduceIte, mixedLift, hxO, blockLift, BlockCfg.toC]
        exact Complex.continuous_ofReal.comp
          ((continuous_apply i).comp
            ((continuous_apply (jBlock d L (M1 * N₁) (k + 1) (k + 1) x)).comp continuous_snd))
      · simp only [hx, ↓reduceIte, mixedLift, hxO, blockLift, BlockCfg.toC]
        exact Complex.continuous_ofReal.comp
          ((continuous_apply i).comp
            ((continuous_apply (jBlock d L (M1 * N₁) (k + 1) k x)).comp continuous_fst))
    · simp [hx]
      exact continuous_const
  hc := by
    intro x i
    unfold mixedData
    by_cases hx : x ∈ (genCubeMixed hm y0 Om hOm).Ω 1
    · simp only [liftMixed_h _ _ _ _ _ _ hx]
      exact continuous_const
    · simp only [(liftMixed _ _ _ _ _ _).h_zero x hx]
      exact continuous_const

/-- **Lemma II.3.3 (measurability)**: `{χ'_{k+1}(□') = 1}` is Borel. -/
theorem measurableSet_chiPrimeNewProp (a : ℕ → ℝ) (μ δ νk : ℝ)
    (H : BgHyp d L (k + 1) (minSep L M1) a μ) :
    MeasurableSet {p : BlockCfg d (M1 * N₁) L (k + 1) k N ×
        BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N | ChiPrimeNewProp a μ δ νk h hm y0 Om hOm p.1 p.2} :=
  measurableSet_regMixed H (realFamily_mixedData hm y0 Om hOm h) _ νk δ _ _ _

theorem measurable_chiPrimeNew (a : ℕ → ℝ) (μ δ νk : ℝ)
    (H : BgHyp d L (k + 1) (minSep L M1) a μ) :
    Measurable (chiPrimeNew a μ δ νk h hm y0 Om hOm) :=
  measurable_charFn (measurableSet_chiPrimeNewProp hm y0 Om hOm h a μ δ νk H)

end Mixed

section OldFluct

variable {k : ℕ} (c n : ℕ) (y0 : Torus d n)

theorem measurable_blockSumQ_coord (x : Torus d (M1 * N₁ * L ^ (k + 1))) (i : Fin N) :
    Measurable fun ψ : BlockCfg d (M1 * N₁) L (k + 1) k N => blockSumQ ψ x i := by
  unfold blockSumQ
  exact measurable_const.mul (Finset.measurable_sum _ fun y' _ =>
    (measurable_pi_apply i).comp (measurable_pi_apply y'))

/-- **Lemma II.3.3 (measurability)**: `{χ'^{(k)}(□') = 1}` is Borel. -/
theorem measurableSet_chiPrimeOldProp (δ : ℝ) :
    MeasurableSet {p : BlockCfg d (M1 * N₁) L (k + 1) k N ×
        BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N |
      ChiPrimeOldProp (M1 := M1) (N₁ := N₁) (L := L) δ c n y0 p.1 p.2} := by
  unfold ChiPrimeOldProp
  refine measurableSet_forall_lt_meas (ι := Torus d (M1 * N₁ * L ^ (k + 1)))
    (f := fun x (p : BlockCfg d (M1 * N₁) L (k + 1) k N ×
      BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N) => rn (fun i => p.2 (jBlock d L (M1 * N₁) (k + 1) (k + 1) x) i -
      blockSumQ p.1 x i)) (fun x => measurable_rn fun i => ?_) _ fun _ => 2 * δ
  refine Measurable.sub ?_ ?_
  · exact (measurable_pi_apply i).comp ((measurable_pi_apply _).comp measurable_snd)
  · exact (measurable_blockSumQ_coord x i).comp measurable_fst

theorem measurable_chiPrimeOld (δ : ℝ) :
    Measurable (chiPrimeOld (M1 := M1) (N₁ := N₁) (L := L) (k := k) (N := N) δ c n y0) :=
  measurable_charFn (measurableSet_chiPrimeOldProp c n y0 δ)

/-- **Lemma II.3.3 (measurability)**: `{χ^{(k)}(□') = 1}` is Borel. -/
theorem measurableSet_chiFluctProp (p1 : ℝ) :
    MeasurableSet {ψ' : BlockCfg d (M1 * N₁) L (k + 1) k N |
      ChiFluctProp (M1 := M1) (N₁ := N₁) (L := L) c n y0 p1 ψ'} := by
  unfold ChiFluctProp
  exact measurableSet_forall_lt_meas (ι := Torus d (M1 * N₁ * L ^ (k + 1)))
    (f := fun x (ψ' : BlockCfg d (M1 * N₁) L (k + 1) k N) => rn (ψ' (jBlock d L (M1 * N₁) (k + 1) k x)))
    (fun x => measurable_rn fun i =>
      (measurable_pi_apply i).comp (measurable_pi_apply _)) _ fun _ => p1

theorem measurable_chiFluct (p1 : ℝ) :
    Measurable (chiFluct (M1 := M1) (N₁ := N₁) (L := L) (k := k) (N := N) c n y0 p1) :=
  measurable_charFn (measurableSet_chiFluctProp c n y0 p1)

end OldFluct

end Chi

end Balaban.LargeField
