/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexProp26J
public import Balaban.Fluctuation.StepRegFamily

/-!
# Regularity of the zero-class joint step at a free datum

The two interpolation exponents are smooth along the real ray at every datum of the complex
chart. The class terms vanish identically, so their analyticity needs no field restriction.
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Fluctuation Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 MeasureTheory Set

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp)

/-- The two truncated interpolation exponents of the zero class form C¹ families at any
datum of the complex chart. -/
theorem isC1Family_zeroClass_freeDatum (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (D : BgData S.G' N) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (g : Fld d L N₁ m₁ (k + 1) N) :
    ∃ (U : Set ℝ) (W₁' W₂' : ℝ → S.E → ℂ),
      IsC1Family U
        (fun s x => if chiFl S.U N S.p₁ x = 1 then
          Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, (s : ℂ) • yhat x) else 0) W₁' ∧
      IsC1Family U
        (fun t x => if chiFl S.U N S.p₁ x = 1 then
          Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) g (rawOf D, (t : ℂ) • yhat x) else 0) W₂' := by
  have hpath : ContDiff ℝ ⊤ (fun q : ℝ × S.E =>
      (rawOf D, (q.1 : ℂ) • yhat q.2)) := by
    refine contDiff_const.prodMk (contDiff_pi.2 fun p => ?_)
    have hs : ContDiff ℝ ⊤ (fun q : ℝ × S.E => (q.1 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_fst
    have hx : ContDiff ℝ ⊤ (fun q : ℝ × S.E => ((q.2 p.1 p.2 : ℝ) : ℂ)) := by
      have h : ContDiff ℝ ⊤ (fun q : ℝ × S.E => q.2 p.1 p.2) := by fun_prop
      exact Complex.ofRealCLM.contDiff.comp h
    simpa only [yhat, Pi.smul_apply, smul_eq_mul] using hs.mul hx
  have hΘ : rawOf D ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps := ⟨D, hX, rfl⟩
  have h₁ : ∀ q : ℝ × S.E, |q.1| * ‖q.2‖ < pp →
      ContDiffAt ℝ 1
        (fun q : ℝ × S.E => Jr.W1 (zeroClass d L N₁ m₁ k N ϱ)
          (rawOf D, (q.1 : ℂ) • yhat q.2)) q := by
    intro q hq
    have hb : ∀ p, ‖((q.1 : ℂ) • yhat q.2) p‖ ≤ pp :=
      smul_yhat_le (S := S) (pp := pp) hq.le
    have han := Jr.analyticAt_W1 (zeroClass d L N₁ m₁ k N ϱ) hΘ hb
      (fun j _ => analyticAt_Edens_zeroClass j _)
      (fun j _ => analyticAt_Edens_zeroClass j _)
    have hc : ContDiffAt ℝ ⊤ (Jr.W1 (zeroClass d L N₁ m₁ k N ϱ))
        (rawOf D, (q.1 : ℂ) • yhat q.2) :=
      (han.contDiffAt (n := ⊤)).restrict_scalars ℝ
    exact (hc.comp q hpath.contDiffAt).of_le (by norm_num)
  have h₂ : ∀ q : ℝ × S.E, |q.1| * ‖q.2‖ < pp →
      ContDiffAt ℝ 1
        (fun q : ℝ × S.E => Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) g
          (rawOf D, (q.1 : ℂ) • yhat q.2)) q := by
    intro q hq
    have hb : ∀ p, ‖((q.1 : ℂ) • yhat q.2) p‖ ≤ pp :=
      smul_yhat_le (S := S) (pp := pp) hq.le
    have han := Jr.analyticAt_W2 (zeroClass d L N₁ m₁ k N ϱ) hΘ hb g
      (fun j _ => analyticAt_Floc_zeroClass g j _)
      (fun j _ => analyticAt_Floc_zeroClass g j _)
    have hc : ContDiffAt ℝ ⊤ (Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) g)
        (rawOf D, (q.1 : ℂ) • yhat q.2) :=
      (han.contDiffAt (n := ⊤)).restrict_scalars ℝ
    exact (hc.comp q hpath.contDiffAt).of_le (by norm_num)
  obtain ⟨U₁, hU₁⟩ := S.isC1Family_trunc hp₁ hlt h₁
  obtain ⟨U₂, hU₂⟩ := S.isC1Family_trunc hp₁ hlt h₂
  have hU₁' : IsC1Family (U₁ ∩ U₂)
      (S.truncF fun q : ℝ × S.E => Jr.W1 (zeroClass d L N₁ m₁ k N ϱ)
        (rawOf D, (q.1 : ℂ) • yhat q.2))
      (S.dtruncF fun q : ℝ × S.E => Jr.W1 (zeroClass d L N₁ m₁ k N ϱ)
        (rawOf D, (q.1 : ℂ) • yhat q.2)) := by
    refine ⟨hU₁.isOpen.inter hU₂.isOpen,
      fun s hs => ⟨hU₁.Icc_subset hs, hU₂.Icc_subset hs⟩,
      fun s hs => hU₁.measurable s hs.1,
      fun s hs => hU₁.measurable' s hs.1,
      fun x s hs => hU₁.hasDerivAt x s hs.1,
      hU₁.continuousOn, ?_⟩
    obtain ⟨M, hM⟩ := hU₁.bound
    exact ⟨M, fun x s hs => hM x s hs.1⟩
  have hU₂' : IsC1Family (U₁ ∩ U₂)
      (S.truncF fun q : ℝ × S.E => Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) g
        (rawOf D, (q.1 : ℂ) • yhat q.2))
      (S.dtruncF fun q : ℝ × S.E => Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) g
        (rawOf D, (q.1 : ℂ) • yhat q.2)) := by
    refine ⟨hU₁.isOpen.inter hU₂.isOpen,
      fun s hs => ⟨hU₁.Icc_subset hs, hU₂.Icc_subset hs⟩,
      fun s hs => hU₂.measurable s hs.2,
      fun s hs => hU₂.measurable' s hs.2,
      fun x s hs => hU₂.hasDerivAt x s hs.2,
      hU₂.continuousOn, ?_⟩
    obtain ⟨M, hM⟩ := hU₂.bound
    exact ⟨M, fun x s hs => hM x s hs.2⟩
  exact ⟨U₁ ∩ U₂, _, _, hU₁', hU₂'⟩

/-- A complex activity bound gives the two joint nonvanishing statements on the constant-field
fibre of the chart. -/
theorem nonvanishing_zeroClass_fibre_of_activityBoundC
    (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ))
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (g : Fld d L N₁ m₁ (k + 1) N)
    (I : StepActivityBoundC (S.withDatum D hD) (zeroClass d L N₁ m₁ k N ϱ) g) :
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∫ x : S.E, Complex.exp
        (Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, (s : ℂ) • yhat x)) ∂S.nuFl) ≠ 0) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∫ x : S.E, Complex.exp
        (Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, yhat x) +
          Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) g
            (rawOf D, (t : ℂ) • yhat x)) ∂S.nuFl) ≠ 0) := by
  constructor
  · intro s hs
    have hz := I.ZstC_ne_zero (Or.inl ⟨hs, rfl⟩)
    have heq : (∫ x : S.E, Complex.exp
        (Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, (s : ℂ) • yhat x)) ∂S.nuFl) =
        (S.withDatum D hD).ZstC (zeroClass d L N₁ m₁ k N ϱ) g s 0 := by
      unfold StepSetting.ZstC partFun₂
      refine integral_congr_ae ?_
      filter_upwards [Jr.ae_W1_path (zeroClass d L N₁ m₁ k N ϱ) hp₁ hle D hD hX hs] with x hx
      rw [hx, (S.withDatum D hD).WtwoC_zero (zeroClass d L N₁ m₁ k N ϱ) g x, add_zero]
    rw [heq]
    exact hz
  · intro t ht
    have hz := I.ZstC_ne_zero (Or.inr ⟨rfl, ht⟩)
    have heq : (∫ x : S.E, Complex.exp
        (Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, yhat x) +
          Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) g
            (rawOf D, (t : ℂ) • yhat x)) ∂S.nuFl) =
        (S.withDatum D hD).ZstC (zeroClass d L N₁ m₁ k N ϱ) g 1 t := by
      unfold StepSetting.ZstC partFun₂
      refine integral_congr_ae ?_
      filter_upwards [Jr.ae_W1_one (zeroClass d L N₁ m₁ k N ϱ) hp₁ hle D hD hX,
        Jr.ae_W2_path (zeroClass d L N₁ m₁ k N ϱ) hp₁ hle D hD hX g ht]
        with x hx₁ hx₂
      rw [hx₁, hx₂]
    rw [heq]
    exact hz

end Balaban.Fluctuation.StepSetting.JointRep
