/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepIdentityFibre
public import Balaban.Fluctuation.StepComplexObs
public import Balaban.Fluctuation.StepComplexLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The step identity at a chart datum for a general class member

For a class `C` of the step of the shared tower `T` and a datum `D′` of the chart
`Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀`, Proposition 2.6 with the local sums substituted:
`TstepC = exp [-β A^η_{k+1} + ℰ_k(ψ^{(k)}) - E''' |T₁| + ℱ_k(ψ^{(k)}, g) + ∑_z ℰ₀(z)
  + β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i]`.

The premises of the zero-class theorem `stepIdentity_zeroClass_withDatum_of_nonvanishingG`
that do not depend on the datum are supplied by the tower, as there.  The premises that the zero
class discharges by vanishing of its terms are explicit hypotheses here: the class regularity
`ClassRegularC C g` (analyticity of the old terms along the path), its local and observable forms
`ClassRegularObsC C g`, and the nonvanishing of the partition functions (or the complex activity
bound).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Set

/-- **Proposition 2.6 at a chart datum of the fibre for a general class member, with the local
sums substituted.**  At a scale of the tower `T`, for a datum `D′` of the chart with constant field
`h₀`, a source `g` and a class `C` with the regularity `ClassRegularC C g`, `ClassRegularObsC C g`
and the nonvanishing of the partition functions of the step with the datum `D′`:
the exponent is `-β A^η_{k+1} + ℰ_k(ψ^{(k)}) - E''' |T₁| + ℱ_k(ψ^{(k)}, g) + ∑_z ℰ₀(z)
  + β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i`, all objects those of the step with the datum and the
class `C`. -/
theorem stepIdentity_class_withDatum_of_nonvanishingG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin)
    {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (Dsc : StepScaleDataG T k hk N₁ ν β p₁) (hβ : 0 < β) (hp₁ : 0 < p₁)
    (D' : BgData (T.step k hk N₁ ν β p₁).G' N)
    (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hX : XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
      (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D')
    (C : StepClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
    (g : Fld d L N₁ T.m₁ (k + 1) N)
    (hreg : ((T.step k hk N₁ ν β p₁).withDatum D' hDh).ClassRegularC C g)
    (hregObs : ((T.step k hk N₁ ν β p₁).withDatum D' hDh).ClassRegularObsC C g)
    (hnv : ((T.step k hk N₁ ν β p₁).withDatum D' hDh).StepNonvanishingC C g) :
    ((T.step k hk N₁ ν β p₁).withDatum D' hDh).TstepC C g =
      Complex.exp (-((T.step k hk N₁ ν β p₁).β : ℂ) *
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).AnewC +
        EcompAtC C.m₀ C.Tm (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν (Nat.le_succ k)
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).psiKdC -
        (((T.step k hk N₁ ν β p₁).withDatum D' hDh).Eppp C : ℂ) *
          (((T.step k hk N₁ ν β p₁).withDatum D' hDh).nU : ℂ) +
        FcompAtC C.m₀ C.Tm (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν (Nat.le_succ k)
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).psiKdC g +
        ∑ z : RootIdx d L N₁ T.m₁ (k + 1),
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).E0locC C z +
        (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
            g y i * ((T.step k hk N₁ ν β p₁).withDatum D' hDh).M0C C g y i) := by
  have hbU : (T.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) :=
    hatStepKG_betaU T.hN (by have := T.hd; omega) k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hbU0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hδ : Real.sqrt (N : ℝ) * ((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ *
        lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))) < T.t := by
    have h := Dsc.fl_radius
    have hn : ‖(((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ =
        (T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) := by
      rw [Complex.norm_real, Real.norm_of_nonneg]
      rw [hbU]; exact Real.rpow_nonneg hbU0.le _
    rw [hn] at h
    exact h
  have hlt : ((T.step k hk N₁ ν β p₁).withDatum D' hDh).p₁ <
      lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
    have h := Dsc.ray_margin
    have hl := Dsc.r_pos
    show p₁ < _
    nlinarith
  have hp : 0 < ((T.step k hk N₁ ν β p₁).withDatum D' hDh).p₁ := hp₁
  have hβS : 0 < ((T.step k hk N₁ ν β p₁).withDatum D' hDh).β := hβ
  have h26 := ((T.step k hk N₁ ν β p₁).withDatum D' hDh).prop26C_class C (δc := T.δc) (R := 2)
    (pp := lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) Dsc.core T.large_block
    T.dom_margin T.coer_margin T.δc_small one_pos T.c7_cap (by norm_num) T.bg1_cap hβS hp hlt hδ
    hX g hreg hnv
  have hE := ((T.step k hk N₁ ν β p₁).withDatum D' hDh).sum_E0locC C hp g
    hregObs.toClassRegularLocC hnv
  have hF := ((T.step k hk N₁ ν β p₁).withDatum D' hDh).F0C_eq_pair C hp hβS g hregObs hnv
  rw [h26, ← hE, hF]
  rfl

end Balaban.Inhabited
