/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityH

/-!
# The new local densities at a block datum with an arbitrary field (blocker 6, item (2))

The landed new local densities `E1locC`, `E0locC`, `M0C` (P4 (2.53), (2.56)-(2.60)) are defined for
a `StepSetting`, whose block datum has the real constant field `h₀`.  This file defines the same
objects for a block datum `θ = H.D'` with an arbitrary complex field (`StepSettingH`), by the same
formulas with the landed complex constructions at `θ`:

* the background `(φ_{k+1}, α_{k+1}) = (bgFieldC, bgMultC)` of `θ`, the square root
  `C^{(k)1/2} = hatCovSqrt θ`, the substitution `ψ' = β_k^{-1/2} C^{(k)1/2} ψ̂` (`hatField`);
* the critical point `ψ^{(k)}(θ)` on the unit lattice (`psi0H`, the restriction of `composeData`);
* the old datum `(ψ, h)` with the field of `θ` (`dataUCH`);
* `Phi1H` (`Φ₁(ψ') = -β_k V^{(k)}(ψ') + δℰ_k(ψ')`, P4 (2.56)), `E1locH` (`ℰ₁^{(k+1)}(z)`, the formula
  (2.8) with the scalar product restricted to `B_{k+1}(z)`), `E0locH`
  (`ℰ₀^{(k+1)}(z) = -½ Σ_{y ∈ B(z)} tr 𝕃(y,y) + ℰ₁^{(k+1)}(z)`, `𝕃 = decLog` at the background of
  `θ`), `M0H` (`ℳ₀^{(k+1)}(y; g)`, P4 (2.53)).

**Characterization.**  On the fibre (`θ.h ≡ h₀`) every object is the landed one:
`psi0H_fibre`, `Phi1H_fibre`, `shift_fibre`, `E1locH_fibre`, `E0locH_fibre`, `M0H_fibre`.  Off the
fibre they are the values of the analytic representatives of `LocalClassDensityHRep`
(`JointRep.E1locJ_datum`, `JointRep.E0locJ_datum`, `JointRep.M0J_datum`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Matrix

namespace StepSettingH

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (H : StepSettingH S) (C : StepClass d L N₁ m₁ k N ϱ)

/-- **The critical point `ψ^{(k)}(θ)` (2.1) on the unit lattice** at the block datum `θ = H.D'`
(any field): the value at a site of each unit block of the spin of `composeData` of the complex
background of `θ` and of `θ`.  It is `psi0C` for the block datum `θ`. -/
noncomputable def psi0H : S.EC := fun q =>
  (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ (unitRep (G' := S.G') q.1) q.2

/-- **`Φ₁(ψ') = -β_k V^{(k)}(ψ') + δℰ_k(ψ')`** (P4 (2.56); the exponent `W₁(1, ·)` as a function
of the complex shift) at the block datum `θ = H.D'`: the interaction `V^{(k)}` (2.4) at the complex
background of `θ` and the change of the composite `ℰ_k` (H.2) of the class `C` between the old
data `(ψ^{(k)}(θ) + ψ', θ.h)` and `(ψ^{(k)}(θ), θ.h)` (`dataUCH`).  It is `Phi1C` for the block
datum `θ`. -/
noncomputable def Phi1H (y : S.EC) : ℂ :=
  -(S.β : ℂ) * interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
      (compTangent S.hG S.hG' (le_refl (k + 1)) S.a (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
        H.D' (H.dataUCH (H.psi0H + y)))
      (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (H.dataUCH (H.psi0H + y)) -
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) +
    (EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (H.dataUCH (H.psi0H + y)) -
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (H.dataUCH H.psi0H))

/-- **`ℰ₁^{(k+1)}(z)` (P4 (2.56)-(2.60)) at the block datum `θ = H.D'`**:
`∫₀¹ ds ∫ dμ_{s,0} DΦ₁(s ψ')[1_{B(z)} ψ']` with `ψ' = β_k^{-1/2} C^{(k)1/2}(θ) ψ̂`
(`hatField (hatCovSqrt θ)`), `dμ_{s,0} ∝ e^{Φ₁(s ψ')} dν_{p₁}`.  It is `E1locC` for the block datum
`θ`. -/
noncomputable def E1locH (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) : ℂ :=
  ∫ s in (0 : ℝ)..1, avgFun S.nuFl
    (fun s x => H.Phi1H C ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (yhat x)))
    (fun x => (fderiv ℂ (H.Phi1H C)
        ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (yhat x)))
      (S.maskUC z (S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (yhat x)))) s

/-- **`ℰ₀^{(k+1)}(z) = -½ Σ_{y ∈ B(z)} tr 𝕃(y,y) + ℰ₁^{(k+1)}(z)`** (P4 (2.56)) at the block
datum `θ = H.D'`, with `𝕃 = log 𝒜` the decoupled logarithm `decLog` at `s = 1` and at the complex
background of `θ`.  It is `E0locC` for the block datum `θ`. -/
noncomputable def E0locH (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) : ℂ :=
  -(1 / 2 : ℂ) * ∑ y ∈ S.blockU z, ∑ i,
      decLog S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D') (fun _ => 1)
        (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) (unitQ S.G') (unitP S.G')
        (y, i) (y, i) +
    H.E1locH C z

/-- **`ℳ₀^{(k+1)}(y; g)_i` (P4 (2.53)) at the block datum `θ = H.D'`**:
`β_k^{1/2} ∫₀¹ dt ∫ dμ_{1,t} ∂_t ℳ_k(y; ψ^{(k)}(θ) + t ψ', θ.h, g)_i`, with the exponents
`W₁(1, ·) = Φ₁(ψ')` and `W₂(t, ·) = ℱ_k(ψ^{(k)} + t ψ', g) - ℱ_k(ψ^{(k)}, g)` at the old data with
the field of `θ`.  It is `M0C` for the block datum `θ`. -/
noncomputable def M0H (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    ℂ :=
  ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
    ∫ t in (0 : ℝ)..1, avgFun₂ S.nuFl
      (fun s x => H.Phi1H C ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (yhat x)))
      (fun t x =>
        FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
            (H.dataUCH (H.psi0H + (t : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (yhat x)))
            g -
          FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (H.dataUCH H.psi0H) g)
      (fun x => deriv (fun r : ℝ => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
        (H.dataUCH (H.psi0H + (r : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (yhat x)))
        g y i) t) 1 t

/-! ### On the fibre the objects are the landed ones -/

section Fibre

variable (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ))

theorem psi0H_fibre : (S.withDatumH D).psi0H = (S.withDatum D hD).psi0C := rfl

/-- On the fibre the substitution `ψ' = β_k^{-1/2} C^{(k)1/2} ψ̂` is the landed `shiftUC`. -/
theorem shift_fibre (x : S.E) :
    S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x) = (S.withDatum D hD).shiftUC x := by
  have h := (S.withDatum D hD).covSqrtC_eq_hatCovSqrt
  show ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (hatCovSqrt S.G' S.a₁ S.ν D *ᵥ yhat x) =
    ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • ((S.withDatum D hD).covSqrtC *ᵥ yhat x)
  rw [h]
  rfl

/-- On the fibre `Φ₁` is the landed `Phi1C`. -/
theorem Phi1H_fibre : (S.withDatumH D).Phi1H C = (S.withDatum D hD).Phi1C C := by
  funext y
  unfold Phi1H StepSetting.Phi1C StepSetting.VkC StepSetting.dEC
  rw [dataUCH_fibre D hD, dataUCH_fibre D hD, psi0H_fibre D hD]
  rfl

/-- On the fibre the exponent of `μ_{s,0}` is the landed `WoneC`. -/
theorem wone_fibre (s : ℝ) (x : S.E) :
    (S.withDatumH D).Phi1H C ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)) =
      (S.withDatum D hD).WoneC C s x := by
  rw [Phi1H_fibre C D hD, shift_fibre D hD]
  rfl

/-- **On the fibre `ℰ₁^{(k+1)}(z)` is the landed `E1locC`.** -/
theorem E1locH_fibre (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    (S.withDatumH D).E1locH C z = (S.withDatum D hD).E1locC C z := by
  unfold E1locH StepSetting.E1locC
  have hW : (fun (s : ℝ) (x : S.E) => (S.withDatumH D).Phi1H C
      ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν (S.withDatumH D).D') (yhat x))) =
      (S.withDatum D hD).WoneC C := funext fun s => funext fun x => wone_fibre C D hD s x
  rw [hW]
  refine intervalIntegral.integral_congr fun s _ => ?_
  congr 1
  funext x
  change (fderiv ℂ ((S.withDatumH D).Phi1H C)
      ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)))
      (S.maskUC z (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x))) = _
  rw [Phi1H_fibre C D hD, shift_fibre D hD]
  rfl

/-- **On the fibre `ℰ₀^{(k+1)}(z)` is the landed `E0locC`.** -/
theorem E0locH_fibre (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    (S.withDatumH D).E0locH C z = (S.withDatum D hD).E0locC C z := by
  unfold E0locH StepSetting.E0locC
  rw [E1locH_fibre C D hD]
  rfl

/-- **On the fibre `ℳ₀^{(k+1)}(y; g)_i` is the landed `M0C`.** -/
theorem M0H_fibre (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    (S.withDatumH D).M0H C g y i = (S.withDatum D hD).M0C C g y i := by
  unfold M0H StepSetting.M0C
  have hW : (fun (s : ℝ) (x : S.E) => (S.withDatumH D).Phi1H C
      ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν (S.withDatumH D).D') (yhat x))) =
      (S.withDatum D hD).WoneC C := funext fun s => funext fun x => wone_fibre C D hD s x
  have hpath : ∀ (r : ℝ) (x : S.E),
      (S.withDatumH D).dataUCH ((S.withDatumH D).psi0H +
        (r : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν (S.withDatumH D).D') (yhat x)) =
      (S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC r x) := by
    intro r x
    rw [dataUCH_fibre D hD]
    change (S.withDatum D hD).dataUC ((S.withDatumH D).psi0H +
        (r : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)) = _
    rw [shift_fibre D hD, psi0H_fibre D hD]
    rfl
  have hcrit : (S.withDatumH D).dataUCH (S.withDatumH D).psi0H =
      (S.withDatum D hD).dataUC (S.withDatum D hD).psi0C := by
    rw [dataUCH_fibre D hD, psi0H_fibre D hD]
  have hW2 : (fun (t : ℝ) (x : S.E) =>
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
          ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H +
            (t : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν (S.withDatumH D).D') (yhat x))) g -
        FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
          ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H) g) =
      (S.withDatum D hD).WtwoC C g := by
    funext t x
    rw [hpath t x, hcrit]
    rfl
  refine congrArg (fun w : ℂ => ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * w) ?_
  refine intervalIntegral.integral_congr fun t _ => ?_
  refine avgFun₂_congr_ae (Filter.Eventually.of_forall fun x => congrFun (congrFun hW 1) x)
    (Filter.Eventually.of_forall fun x => congrFun (congrFun hW2 t) x)
    (Filter.Eventually.of_forall fun x => ?_)
  exact congrArg (fun F : ℝ → ℂ => deriv F t) (funext fun r => by rw [hpath r x]; rfl)

end Fibre

end StepSettingH

end Balaban.Fluctuation
