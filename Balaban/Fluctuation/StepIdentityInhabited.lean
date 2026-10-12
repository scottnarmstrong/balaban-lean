/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepIdentity
public import Balaban.SmallField.Def6Inhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Witnesses for the input structures of Proposition 2.6

* `nonempty_stepSetting`: a step datum exists (`D' = 0`, `G'` the whole-lattice set of level `k + 1`);
* `nonempty_realClassTerms`: `RealClassTerms` holds for the zero effective action and every real
  source `g`, for every step datum in the domain of Theorem 7.1;
* `stepRegular_of_beta_zero`, `stepNonvanishing_of_beta_zero`: `StepRegular` and
  `StepNonvanishing` hold for the zero effective action and the source `g = 0` when the exponents
  vanish (`β = 0`), so the structures are not contradictory.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The zero effective action as a class on the step torus (`ℰ = ℳ = 0`, `E_k = 0`). -/
noncomputable def zeroClass (d L N₁ m₁ k N : ℕ) [NeZero L] [NeZero N₁] (ϱ : ℝ) :
    StepClass d L N₁ m₁ k N ϱ where
  m₀ := 0
  Tm := zeroTerms d L N₁ m₁ (k + 1) N ϱ
  Ek := 0

/-- A step datum exists: `θ = 0`. -/
theorem nonempty_stepSetting (hk1 : 1 ≤ k) (a₁ ν β p₁ δ : ℝ) :
    Nonempty (StepSetting d L N₁ m₁ k N ϱ) :=
  ⟨{ G' := levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) le_rfl
     hk1 := hk1
     hG' := isLevel_levelGS (by omega) le_rfl
     D' := { Ψ := fun _ _ => 0, h := fun _ _ => 0
             Ψ_layerConst := fun _ _ _ _ _ _ _ => rfl
             h_layerConst := fun _ _ _ _ _ _ _ => rfl
             Ψ_zero := fun _ _ => rfl, h_zero := fun _ _ => rfl }
     h₀ := fun _ => 0
     hh₀ := fun _ _ => by simp
     a₁ := a₁, ν := ν, β := β, p₁ := p₁, δ := δ }⟩

theorem EcompAt_zero (m₀ : ℕ) (a : ℕ → ℝ) (ν : ℝ) {K j : ℕ} (hj : j ≤ K)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) N) :
    EcompAt m₀ (zeroTerms d L N₁ m₁ K N ϱ) a ν hj D = 0 := by
  simp [EcompAt, Edens_zero]

theorem FcompAt_zero_eq (m₀ : ℕ) (a : ℕ → ℝ) (ν : ℝ) {K j : ℕ} (hj : j ≤ K)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) N)
    (g : Fld d L N₁ m₁ K N) :
    FcompAt m₀ (zeroTerms d L N₁ m₁ K N ϱ) a ν hj D g =
      ∑ x : CTorus d L N₁ m₁ K, ∑ i, g x i *
        svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
          (bgField (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν D)
          x i := by
  simp [FcompAt, Floc_zero]

/-- **`RealClassTerms` is inhabited**: the zero effective action with a real source. -/
theorem nonempty_realClassTerms (S : StepSetting d L N₁ m₁ k N ϱ)
    (H : BgHyp d L (k + 1) ϱ S.a S.ν) (g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) :
    Nonempty (S.RealClassTerms (zeroClass d L N₁ m₁ k N ϱ) (fun x i => (g x i : ℂ))) := by
  refine ⟨⟨fun ψ _ => ?_, fun ψ hψ => ?_⟩⟩
  · show (EcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) (S.dataU ψ)).im = 0
    rw [EcompAt_zero]; simp
  · show (FcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) (S.dataU ψ)
      (fun x i => (g x i : ℂ))).im = 0
    have hreal := (theorem71 H hψ).2.1
    rw [FcompAt_zero_eq, Complex.im_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hx : x ∈ (stepG d L N₁ m₁ k ϱ).Ω 1
    · rw [svec_of_mem (stepG d L N₁ m₁ k ϱ) _ ⟨x, hx⟩ i]
      simp [(hreal ⟨x, hx⟩).1 i]
    · rw [svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hx i]; simp

theorem Wone_zero_of_beta (S : StepSetting d L N₁ m₁ k N ϱ) (hβ : S.β = 0) (s : ℝ) (x : S.E) :
    S.Wone (zeroClass d L N₁ m₁ k N ϱ) s x = 0 := by
  unfold StepSetting.Wone StepSetting.dE
  show -(S.β : ℂ) * _ + (EcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _ -
    EcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _) = 0
  rw [hβ, EcompAt_zero, EcompAt_zero]; simp

theorem Wtwo_zero_class (S : StepSetting d L N₁ m₁ k N ϱ) (t : ℝ) (x : S.E) :
    S.Wtwo (zeroClass d L N₁ m₁ k N ϱ) 0 t x = 0 := by
  unfold StepSetting.Wtwo StepSetting.dF
  show FcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _ 0 -
    FcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _ 0 = 0
  rw [FcompAt_zero_eq, FcompAt_zero_eq]
  simp

theorem isC1Family_zero {X : Type*} [MeasurableSpace X] :
    IsC1Family (Set.univ : Set ℝ) (fun (_ : ℝ) (_ : X) => (0 : ℂ)) (fun _ _ => 0) where
  isOpen := isOpen_univ
  Icc_subset := Set.subset_univ _
  measurable _ _ := measurable_const
  measurable' _ _ := measurable_const
  hasDerivAt _ _ _ := hasDerivAt_const _ _
  continuousOn _ := continuousOn_const
  bound := ⟨0, fun _ _ _ => by simp⟩

/-- **`StepRegular` is not contradictory**: for the zero effective action, the source `g = 0` and
vanishing exponents (`β = 0`). -/
theorem stepRegular_of_beta_zero (S : StepSetting d L N₁ m₁ k N ϱ) (hβ : S.β = 0) :
    S.StepRegular (zeroClass d L N₁ m₁ k N ϱ) 0 := by
  refine ⟨Set.univ, fun _ _ => 0, fun _ _ => 0, ?_, ?_⟩
  · have : S.WoneT (zeroClass d L N₁ m₁ k N ϱ) = fun _ _ => 0 := by
      funext s x
      unfold StepSetting.WoneT
      simp [Wone_zero_of_beta S hβ]
    rw [this]; exact isC1Family_zero
  · have : S.WtwoT (zeroClass d L N₁ m₁ k N ϱ) 0 = fun _ _ => 0 := by
      funext s x
      unfold StepSetting.WtwoT
      simp [Wtwo_zero_class]
    rw [this]; exact isC1Family_zero

/-- **`StepNonvanishing` is not contradictory**: same parameters, with `p₁ > 0`
(`Z_{s,t} = ν_{p₁}(1) = 1`). -/
theorem stepNonvanishing_of_beta_zero (S : StepSetting d L N₁ m₁ k N ϱ) (hβ : S.β = 0)
    (hp₁ : 0 < S.p₁) : S.StepNonvanishing (zeroClass d L N₁ m₁ k N ϱ) 0 := by
  have : IsProbabilityMeasure S.nuFl := isProbabilityMeasure_fluctMeasure S.U N hp₁
  have hZ : ∀ s t : ℝ, S.Zst (zeroClass d L N₁ m₁ k N ϱ) 0 s t = 1 := by
    intro s t
    unfold StepSetting.Zst partFun₂
    simp [Wone_zero_of_beta S hβ, Wtwo_zero_class]
  exact ⟨fun s _ => by rw [hZ]; exact one_ne_zero, fun t _ => by rw [hZ]; exact one_ne_zero⟩

end Balaban.Fluctuation
