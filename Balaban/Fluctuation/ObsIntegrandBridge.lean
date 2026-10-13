/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31b
public import Balaban.Fluctuation.ObsMarksAssembly
public import Balaban.Fluctuation.ExpSourceChart

/-!
# Transport of an `ObsMarks` record along an almost-everywhere equal integrand

Only the field `hF` of `ObsMarks` mentions the integrand `f`.  If `f' s x = f s x` for almost every
`x`, for every `s ∈ [0,1]`, the record for `f` gives the record for `f'` with every other field
unchanged.  The tilt family and the unconditional record are not treated here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory

section Transport

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {X : Type*} [MeasurableSpace X]
  {ν : Measure X} {m₀ : ℕ} {BS : ProdSplit ν d L N₁ m₁ K m₀} {W : ℝ → X → ℂ} {f f' : ℝ → X → ℂ}
  {bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ}

/-- The record for an almost-everywhere equal integrand `f'`: all fields except `hF` are those of
`I`. -/
def ObsMarks.congr_f (I : ObsMarks ν BS W f bx)
    (h : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν, f s x = f' s x) :
    ObsMarks ν BS W f' bx :=
  { I with
    hF := fun s hs => by
      filter_upwards [I.hF s hs, h s hs] with x hx hx'
      rw [← hx', hx] }

end Transport

/-! ### The integrand of the consumer along the ray, at the zero class -/

section ZeroClassRay

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer Balaban.Background
  Balaban.SmallField Balaban.SmallField.Def6 Filter Topology

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)
variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc pp : ℝ}

namespace StepSetting.JointRep

variable {S} (Jr : S.JointRep eps pp)
variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
  (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
  (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
  (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
    c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
  (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)

include Jr hC ha₁ H hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ hδ₁ in
/-- **The consumer's function along the ray, at the zero class and the step's own datum.**  For a
real `t` with `|t| ‖x‖ ≤ p⁺ ≤ c_ψ`, the component `(y, i)` of `ℳ_k` at the datum
`dataUC (psiAtC t x)` is the constant `ℳ-part` `φ_{k+1}|(y,i)` of the step datum plus the site value
of `flFieldOne` along the hat ray `t ψ̂(x)`. -/
theorem McompAtC_zero_path (hpc : pp ≤ cψ) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) (x : S.E) {t : ℝ}
    (ht : |t| * ‖x‖ ≤ pp) :
    McompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psiAtC t x)) g y i =
      svec (stepG d L N₁ m₁ k ϱ)
        ((S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')) y i +
      svec (stepG d L N₁ m₁ k ϱ)
        (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν S.D'
          (hatLift S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.D'
            ((t : ℂ) • yhat x))) y i := by
  have hz : ∀ p, ‖((t : ℂ) • yhat x) p‖ ≤ pp := smul_yhat_le ht
  have h1 := Jr.FJ_sub_restrict_eq_flFieldOne hC ha₁ H hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm
    hα hsm hcψ hδ₁ hpc hX hz
  have h2 := Jr.FJ_eq hX (ψh := (t : ℂ) • yhat x) hz
  rw [← S.psiAtC_eq_psiHat] at h2
  have hsub : ∀ (A B : (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ),
      svec (stepG d L N₁ m₁ k ϱ) (A - B) y i =
        svec (stepG d L N₁ m₁ k ϱ) A y i - svec (stepG d L N₁ m₁ k ϱ) B y i := by
    intro A B
    by_cases hm : y ∈ (stepG d L N₁ m₁ k ϱ).Ω 1
    · rw [svec_of_mem (stepG d L N₁ m₁ k ϱ) _ ⟨y, hm⟩ i,
        svec_of_mem (stepG d L N₁ m₁ k ϱ) _ ⟨y, hm⟩ i,
        svec_of_mem (stepG d L N₁ m₁ k ϱ) _ ⟨y, hm⟩ i]
      rfl
    · rw [svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hm i, svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hm i,
        svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hm i]
      simp
  have h3 := hsub (Jr.FJ (rawOf S.D', (t : ℂ) • yhat x)).1
    ((S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D'))
  rw [h1] at h3
  have h4 := McompAtC_zero_eq (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (N := N) (ϱ := ϱ)
    (zeroClass d L N₁ m₁ k N ϱ).m₀ S.a S.ν (K := k + 1) (j := k) (Nat.le_succ k)
    (S.dataUC (S.psiAtC t x)) g y i
  refine h4.trans ?_
  rw [h2] at h3
  simp only at h3
  rw [h3]
  ring

end StepSetting.JointRep

end ZeroClassRay

end Balaban.Fluctuation
