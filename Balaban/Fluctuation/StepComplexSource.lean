/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexObs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The complex step with a source, for the class with zero old terms (FLUCTUATION.md §2.6)

For the class with zero old terms the source term of the complex step is
`δℱ_k(t ψ', g) = ⟨g, φ_k(ψ^{(k)}(θ) + t ψ') - φ_k(ψ^{(k)}(θ))⟩₁` with the complex small solution
`φ_k = bgFieldC`.  On the complex chart of RAY-CHART §1 the small solution is smooth along the ray
(`contDiffAt_bgFieldC_path`: Theorem 7.2, analyticity, composed with the path; the argument of
`contDiffAt_VjointC`), which gives the regularity inputs of the complex step for every source `g`:

* `classRegularC_zeroClass`: `ClassRegularC` for the zero class and every source `g`
  (`classRegularC_zeroClass_zero` is the case `g = 0`);
* `classRegularObsC_zeroClass`: `ClassRegularObsC` for the zero class and every source (rule 10);
* `prop26C_zeroClass`, `prop26C_zeroClass_of_activity`: Proposition 2.6 at a complex block datum of
  the chart, for the zero class and every source, given `StepNonvanishingC` (resp.
  `StepActivityBoundC`);
* `sum_E0locC_zeroClass`, `F0C_eq_pair_zeroClass`: the local identities of `StepComplexLocal`,
  `StepComplexObs` for the zero class, given `StepNonvanishingC`;
* `exists_activityBoundC_zeroClass_source`: for a complex block datum of the chart there are a
  radius `p > 0` and a size `γ > 0` such that the step with `p₁ = p` satisfies `StepActivityBoundC`
  for the zero class and every source `g` with `sup |g| ≤ γ` (the exponent
  `-β_k V^{(k)} + δℱ_k(·, g)` is small on the support of `ν_p`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Balaban.Polymer Finset MeasureTheory Set

section ZeroClass

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- On the whole-lattice generating set `𝔹_k` the extension `svec` of a field is the field. -/
theorem StepSetting.svec_stepG (φ : (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    svec (stepG d L N₁ m₁ k ϱ) φ y i = φ (⟨y, (S.hG y).1⟩, i) :=
  svec_of_mem _ φ ⟨y, (S.hG y).1⟩ i

/-- For the zero effective action, `ℳ_k = φ_k` (the complex small solution). -/
theorem McompAtC_zero_eq (m₀ : ℕ) (a : ℕ → ℝ) (ν : ℝ) {K j : ℕ} (hj : j ≤ K)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) N)
    (g : Fld d L N₁ m₁ K N) (y : CTorus d L N₁ m₁ K) (i : Fin N) :
    McompAtC m₀ (zeroTerms d L N₁ m₁ K N ϱ) a ν hj D g y i =
      svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν
          (bgC0 d L N) D) y i := by
  simp [McompAtC, Mloc_zero]

/-- For the zero effective action, `δℱ_k(ψ', g) = ⟨g, φ_k(ψ) - φ_k(ψ^{(k)})⟩₁` with the complex
small solution. -/
theorem dFC_zeroClass (g : Fld d L N₁ m₁ (k + 1) N) (ψ : S.EC) :
    S.dFC (zeroClass d L N₁ m₁ k N ϱ) g ψ =
      (∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i, g y i *
        svec (stepG d L N₁ m₁ k ϱ)
          (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC ψ)) y i) -
      ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i, g y i *
        svec (stepG d L N₁ m₁ k ϱ)
          (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC S.psi0C)) y i := by
  unfold StepSetting.dFC
  show FcompAtC 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _ g -
    FcompAtC 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _ g = _
  rw [FcompAtC_zero_eq, FcompAtC_zero_eq]

/-- For the zero effective action the truncated component of `ℳ_k` on the path is the truncated
component of the complex small solution `φ_k(ψ^{(k)} + t ψ')`; it does not depend on the source. -/
theorem mcompCT_zeroClass (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1))
    (i : Fin N) :
    S.mcompCT (zeroClass d L N₁ m₁ k N ϱ) g y i =
      S.truncF (fun q : ℝ × S.E => svec (stepG d L N₁ m₁ k ϱ)
        (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psiAtC q.1 q.2)))
        y i) := by
  funext r x
  unfold StepSetting.mcompCT StepSetting.truncF
  show (if chiFl S.U N S.p₁ x = 1 then McompAtC 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν
    (Nat.le_succ k) (S.dataUC (S.psiAtC r x)) g y i else 0) = _
  rw [McompAtC_zero_eq]

/-- For the zero effective action the truncated source exponent is linear in the source, with the
truncated components of the small solution as coefficients. -/
theorem WtwoCT_zeroClass_eq_sum (g : Fld d L N₁ m₁ (k + 1) N) (t : ℝ) (x : S.E) :
    S.WtwoCT (zeroClass d L N₁ m₁ k N ϱ) g t x =
      ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i, g y i *
        (S.mcompCT (zeroClass d L N₁ m₁ k N ϱ) 0 y i t x -
          S.mcompCT (zeroClass d L N₁ m₁ k N ϱ) 0 y i 0 x) := by
  by_cases hx : chiFl S.U N S.p₁ x = 1
  · rw [S.WtwoCT_of_chi _ g t x hx]
    simp only [mcompCT_zeroClass, StepSetting.truncF, hx, ↓reduceIte]
    unfold StepSetting.WtwoC
    rw [dFC_zeroClass, S.psiAtC_zero, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · simp [StepSetting.WtwoCT, mcompCT_zeroClass, StepSetting.truncF, hx]

end ZeroClass

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-! ### The small solution along the ray, and the class regularity for every source -/

section Plus

variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 ≤ S.β) {pp : ℝ} (hpp : 0 < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The complex small solution `φ_k(ψ)` of the old spin is smooth along the ray**:
`(s, ψ̂) ↦ φ_k(ψ^{(k)}(θ) + s ψ')` is `C^∞` on `{|s| ‖ψ̂‖ < p⁺}`, for a complex block datum of the
chart (Theorem 7.2, analyticity, composed with the smooth path; the argument of
`contDiffAt_VjointC`). -/
theorem contDiffAt_bgFieldC_path {q : ℝ × S.E} (hq : |q.1| * ‖q.2‖ < pp) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
      (S.dataUC (S.psiAtC q.1 q.2))) q := by
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := stepG d L N₁ m₁ k ϱ) (a := S.a) (ν := S.ν)
    (N := N) hC.HBp
  have hdomC := S.dataUC_psiAtC_inUnionDomainC_plus hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁
    hD hq
  have hFat : AnalyticAt ℂ F (S.rawUC (S.psiAtC q.1 q.2)) :=
    hF _ ⟨S.dataUC (S.psiAtC q.1 q.2), hdomC, (S.dataUC_raw _).symm⟩
  have hFc : ContDiffAt ℝ ⊤ F (S.rawUC (S.psiAtC q.1 q.2)) :=
    (hFat.contDiffAt (n := ⊤)).restrict_scalars ℝ
  have hG1 : ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => F (S.rawUC (S.psiAtC q.1 q.2))) q :=
    hFc.comp q S.contDiff_rawUC_psiAtC.contDiffAt
  have h1 : ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => (F (S.rawUC (S.psiAtC q.1 q.2))).1) q :=
    contDiff_fst.contDiffAt.comp q hG1
  refine h1.congr_of_eventuallyEq ?_
  have hopen : IsOpen {q : ℝ × S.E | |q.1| * ‖q.2‖ < pp} :=
    isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hq] with q' hq'
  have hdomC' := S.dataUC_psiAtC_inUnionDomainC_plus hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp
    hδ₁ hD hq'
  have hFq := hFe (S.dataUC (S.psiAtC q'.1 q'.2)) hdomC'
  rw [S.dataUC_raw] at hFq
  rw [hFq]

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- Every component of the complex small solution `φ_k(ψ^{(k)}(θ) + s ψ')` is smooth along the
ray. -/
theorem contDiffAt_svec_bgFieldC_path {q : ℝ × S.E} (hq : |q.1| * ‖q.2‖ < pp)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => svec (stepG d L N₁ m₁ k ϱ)
      (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psiAtC q.1 q.2)))
      y i) q := by
  have h := S.contDiffAt_bgFieldC_path hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hq
  simp only [S.svec_stepG]
  exact contDiffAt_pi.1 h _

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The source exponent of the complex step, for the zero class and every source, is a `C¹`
family on a neighbourhood of `[0,1]`, bounded with its derivative, on the support of `ν_{p₁}`**
(needs `p₁ < p⁺`). -/
theorem isC1Family_WtwoCT_zeroClass (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (g : Fld d L N₁ m₁ (k + 1) N) :
    ∃ (U : Set ℝ) (F' : ℝ → S.E → ℂ),
      IsC1Family U (S.WtwoCT (zeroClass d L N₁ m₁ k N ϱ) g) F' := by
  obtain ⟨U, hU⟩ := S.isC1Family_trunc
    (f := fun q : ℝ × S.E => S.WtwoC (zeroClass d L N₁ m₁ k N ϱ) g q.1 q.2) hp₁ hlt
    (fun q hq => by
      have hf : (fun q : ℝ × S.E => S.WtwoC (zeroClass d L N₁ m₁ k N ϱ) g q.1 q.2) =
          fun q => (∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i, g y i *
            svec (stepG d L N₁ m₁ k ϱ) (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
              (S.dataUC (S.psiAtC q.1 q.2))) y i) -
            ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i, g y i *
              svec (stepG d L N₁ m₁ k ϱ) (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
                (S.dataUC S.psi0C)) y i := by
        funext q
        unfold WtwoC
        rw [dFC_zeroClass]
      rw [hf]
      refine ContDiffAt.sub (ContDiffAt.sum fun y _ => ContDiffAt.sum fun i _ => ?_)
        contDiffAt_const
      exact contDiffAt_const.mul
        ((S.contDiffAt_svec_bgFieldC_path hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hq
          y i).of_le (by exact_mod_cast le_top)))
  exact ⟨U, _, hU⟩

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **`ClassRegularC` for the class with zero old terms and every source `g`**, at a block datum of
the complex chart (`p₁ < p⁺`): `δℰ_k = 0`, and `δℱ_k(t ψ', g) = ⟨g, φ_k(ψ^{(k)} + t ψ') -
φ_k(ψ^{(k)})⟩₁` is smooth along the ray.  (`classRegularC_zeroClass_zero` is the case `g = 0`, at
every step datum.) -/
theorem classRegularC_zeroClass (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (g : Fld d L N₁ m₁ (k + 1) N) : S.ClassRegularC (zeroClass d L N₁ m₁ k N ϱ) g := by
  obtain ⟨U, F', hF⟩ := S.isC1Family_WtwoCT_zeroClass hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp
    hδ₁ hD hp₁ hlt g
  refine ⟨⟨U, fun _ _ => 0, F', ?_, hF⟩⟩
  rw [dECT_zeroClass]
  exact isC1Family_zero.restrict hF.isOpen (Set.subset_univ _) hF.Icc_subset

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The components of `ℳ_k = φ_k` on the path of the complex step, for the zero class, are `C¹`
families on a neighbourhood of `[0,1]`**, bounded with their derivatives on the support of
`ν_{p₁}`. -/
theorem isC1Family_mcompCT_zeroClass (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    ∃ (U : Set ℝ) (M' : ℝ → S.E → ℂ),
      IsC1Family U (S.mcompCT (zeroClass d L N₁ m₁ k N ϱ) g y i) M' := by
  obtain ⟨U, hU⟩ := S.isC1Family_trunc
    (f := fun q : ℝ × S.E => svec (stepG d L N₁ m₁ k ϱ)
      (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psiAtC q.1 q.2))) y i)
    hp₁ hlt (fun q hq =>
      (S.contDiffAt_svec_bgFieldC_path hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hq
        y i).of_le (by exact_mod_cast le_top))
  rw [mcompCT_zeroClass]
  exact ⟨U, _, hU⟩

end Plus

/-! ### The local identities and Proposition 2.6 for the zero class and every source -/

section Public

variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) {pp : ℝ} (hlt : S.p₁ < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ hD in
/-- **`ClassRegularObsC` holds for the class with zero old terms and every source `g`** (rule 10),
at every block datum of the complex chart (real or not), `β > 0`, `p₁ < p⁺`. -/
theorem classRegularObsC_zeroClass (g : Fld d L N₁ m₁ (k + 1) N) :
    S.ClassRegularObsC (zeroClass d L N₁ m₁ k N ϱ) g :=
  { toClassRegularLocC := S.classRegularLocC_zeroClass hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ
      (hp₁.trans hlt) hδ₁ hD hlt
    mcomp := fun y i => S.isC1Family_mcompCT_zeroClass hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ.le
      (hp₁.trans hlt) hδ₁ hD hp₁ hlt g y i }

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ hD in
/-- **Proposition 2.6 at a complex block datum, for the class with zero old terms and every
source `g`**: for a block datum of the chart `Ξ^c(𝔹_{k+1}; 1, ε)` (real or not),
`TstepC = exp [-β_k A^η_{k+1} + ℰ_k(ψ^{(k)}) - E'''_k |T^{(k)}_1| + ℱ_k(ψ^{(k)}, g) + ℰ₀ + ℱ₀(g)]`
as soon as `Z_{s,0}, Z_{1,t} ≠ 0` (`StepNonvanishingC`); the class regularity is
`classRegularC_zeroClass`. -/
theorem prop26C_zeroClass (g : Fld d L N₁ m₁ (k + 1) N)
    (hnv : S.StepNonvanishingC (zeroClass d L N₁ m₁ k N ϱ) g) :
    S.TstepC (zeroClass d L N₁ m₁ k N ϱ) g = Complex.exp (-(S.β : ℂ) * S.AnewC +
      EcompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
        (Nat.le_succ k) S.psiKdC - (S.Eppp (zeroClass d L N₁ m₁ k N ϱ) : ℂ) * (S.nU : ℂ) +
      FcompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
        (Nat.le_succ k) S.psiKdC g + S.E0C (zeroClass d L N₁ m₁ k N ϱ) +
      S.F0C (zeroClass d L N₁ m₁ k N ϱ) g) :=
  S.prop26C_class _ hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ hD g
    (S.classRegularC_zeroClass hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ.le (hp₁.trans hlt) hδ₁ hD hp₁
      hlt g) hnv

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ hD in
/-- Proposition 2.6 at a complex block datum for the zero class and every source, with the activity
bound of the complex step as the input. -/
theorem prop26C_zeroClass_of_activity (g : Fld d L N₁ m₁ (k + 1) N)
    (hact : StepActivityBoundC S (zeroClass d L N₁ m₁ k N ϱ) g) :
    S.TstepC (zeroClass d L N₁ m₁ k N ϱ) g = Complex.exp (-(S.β : ℂ) * S.AnewC +
      EcompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
        (Nat.le_succ k) S.psiKdC - (S.Eppp (zeroClass d L N₁ m₁ k N ϱ) : ℂ) * (S.nU : ℂ) +
      FcompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
        (Nat.le_succ k) S.psiKdC g + S.E0C (zeroClass d L N₁ m₁ k N ϱ) +
      S.F0C (zeroClass d L N₁ m₁ k N ϱ) g) :=
  S.prop26C_zeroClass hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ hD g
    (stepNonvanishingC_of_activityBoundC hact)

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ hD in
/-- **`∑_z ℰ₀^{(k+1)}(z) = ℰ₀^{(k+1)}` for the complex step and the zero class**, at a block datum
of the complex chart, given `StepNonvanishingC`. -/
theorem sum_E0locC_zeroClass (g : Fld d L N₁ m₁ (k + 1) N)
    (hnv : S.StepNonvanishingC (zeroClass d L N₁ m₁ k N ϱ) g) :
    ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      S.E0locC (zeroClass d L N₁ m₁ k N ϱ) z = S.E0C (zeroClass d L N₁ m₁ k N ϱ) :=
  S.sum_E0locC _ hp₁ g (S.classRegularLocC_zeroClass hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ
    (hp₁.trans hlt) hδ₁ hD hlt) hnv

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ hD in
/-- **`ℱ₀^{(k+1)}(g) = ⟨g, β_k^{-1/2} ℳ₀^{(k+1)}(g)⟩₁` for the complex step and the zero class**, at
a block datum of the complex chart, for every source `g`, given `StepNonvanishingC`. -/
theorem F0C_eq_pair_zeroClass (g : Fld d L N₁ m₁ (k + 1) N)
    (hnv : S.StepNonvanishingC (zeroClass d L N₁ m₁ k N ϱ) g) :
    S.F0C (zeroClass d L N₁ m₁ k N ϱ) g = ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin N,
        g y i * S.M0C (zeroClass d L N₁ m₁ k N ϱ) g y i :=
  S.F0C_eq_pair _ hp₁ hβ g
    (S.classRegularObsC_zeroClass hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁ hD g) hnv

end Public

/-! ### The activity bound for a small source -/

section Small

variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 < S.β) {pp : ℝ} (hpp : 0 < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The activity bound of the complex step at a complex datum of the chart, for a small radius
and a small source** (non-vacuity of `StepActivityBoundC` with a nonzero source and no realness of
the datum): there are a radius `0 < p < p⁺` and a size `γ > 0` such that the step with `p₁ = p`
satisfies `StepActivityBoundC` for the class with zero old terms and every source `g` with
`|g(y,i)| ≤ γ` (the exponent `-β_k V^{(k)}(s ψ') + ⟨g, φ_k(ψ^{(k)} + t ψ') - φ_k(ψ^{(k)})⟩₁` is
below the cluster threshold on the support of `ν_p`). -/
theorem exists_activityBoundC_zeroClass_source :
    ∃ p γ : ℝ, 0 < p ∧ p < pp ∧ 0 < γ ∧ ∀ g : Fld d L N₁ m₁ (k + 1) N, (∀ y i, ‖g y i‖ ≤ γ) →
      Nonempty (StepActivityBoundC (S.withRadius p) (zeroClass d L N₁ m₁ k N ϱ) g) := by
  classical
  have hT0 := stepActivityThreshold_pos d L N₁ m₁ (k + 1)
  set T : ℝ := stepActivityThreshold d L N₁ m₁ (k + 1) with hT
  obtain ⟨p, hp0, hppp, -, hsmallV⟩ := S.exists_small_radiusC hC hMX hdm hα hsm ha₁ hc7 hR hsmR
    hβ hpp hδ₁ hD (ε := T / (2 * S.β)) (by positivity)
  set S' := S.withRadius p with hS'
  have hp1 : 0 < S'.p₁ := hp0
  obtain ⟨U, V', hV⟩ := S'.isC1Family_WVCT (pp := pp) hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ.le hpp
    hδ₁ hD hp1 hppp
  -- the components of the small solution on the path, with their bounds
  choose Um M' hMC using fun (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
    S'.isC1Family_mcompCT_zeroClass (pp := pp) hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ.le hpp hδ₁ hD
      hp1 hppp 0 y i
  choose Mb hMb using fun y i => (hMC y i).bound
  have hIcc : ∀ y i, Icc (0 : ℝ) 1 ⊆ Um y i := fun y i => (hMC y i).Icc_subset
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have hMb0 : ∀ y i, 0 ≤ Mb y i := fun y i =>
    (norm_nonneg _).trans ((hMb y i) 0 0 (hIcc y i h0I)).1
  set Bs : ℝ := ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin N, 2 * Mb y i with hBs
  have hBs0 : 0 ≤ Bs := Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun i _ => by
    have := hMb0 y i; positivity
  set γ : ℝ := T / (2 * (Bs + 1)) with hγ
  have hγ0 : 0 < γ := by positivity
  refine ⟨p, γ, hp0, hppp, hγ0, fun g hg => ?_⟩
  obtain ⟨U₂, F', hF⟩ := S'.isC1Family_WtwoCT_zeroClass (pp := pp) hC hMX hdm hα hsm ha₁ hc7 hR
    hsmR hβ.le hpp hδ₁ hD hp1 hppp g
  have hW1 : ∀ s, S'.WoneCT (zeroClass d L N₁ m₁ k N ϱ) s = S'.WVCT s := by
    intro s
    funext x
    rw [S'.WoneCT_eq_add, dECT_zeroClass]
    simp
  have hW2b : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖S'.WtwoCT (zeroClass d L N₁ m₁ k N ϱ) g t x‖ ≤ T / 2 := by
    intro t ht x
    rw [WtwoCT_zeroClass_eq_sum]
    have h1 : ‖∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i, g y i *
        (S'.mcompCT (zeroClass d L N₁ m₁ k N ϱ) 0 y i t x -
          S'.mcompCT (zeroClass d L N₁ m₁ k N ϱ) 0 y i 0 x)‖ ≤ γ * Bs := by
      rw [hBs, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
      rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul]
      refine mul_le_mul (hg y i) ?_ (norm_nonneg _) hγ0.le
      have ha := ((hMb y i) x t (hIcc y i ht)).1
      have hb := ((hMb y i) x 0 (hIcc y i h0I)).1
      calc _ ≤ ‖S'.mcompCT (zeroClass d L N₁ m₁ k N ϱ) 0 y i t x‖ +
            ‖S'.mcompCT (zeroClass d L N₁ m₁ k N ϱ) 0 y i 0 x‖ := norm_sub_le _ _
        _ ≤ 2 * Mb y i := by linarith
    refine h1.trans ?_
    rw [hγ]
    have : T / (2 * (Bs + 1)) * Bs = T / 2 * (Bs / (Bs + 1)) := by field_simp
    rw [this]
    have h2 : Bs / (Bs + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    calc T / 2 * (Bs / (Bs + 1)) ≤ T / 2 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = T / 2 := mul_one _
  have hW1b : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, ‖S'.WVCT s x‖ ≤ T / 2 := by
    intro s hs x
    unfold StepSetting.WVCT
    by_cases hx : chiFl S'.U N S'.p₁ x = 1
    · simp only [hx, ↓reduceIte]
      have hxn : ‖x‖ < p := (chiFl_eq_one_iff hp1 x).1 hx
      have h := hsmallV x hxn s hs
      have hβ' : |S'.β| = S.β := abs_of_pos hβ
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, hβ']
      show S.β * ‖S.VkC (S.psiAtC s x)‖ ≤ _
      calc S.β * ‖S.VkC (S.psiAtC s x)‖ ≤ S.β * (T / (2 * S.β)) :=
            mul_le_mul_of_nonneg_left h.le hβ.le
        _ = T / 2 := by field_simp
    · simp only [hx, ↓reduceIte, norm_zero]
      positivity
  refine stepActivityBoundC_of_small S' _ g hp1 (fun q hq => ?_) (fun q hq x => ?_)
  · rw [hW1 q.1]
    exact (hV.measurable q.1 (hV.Icc_subset (mem_Icc_of_mem_stepSegments hq).1)).add
      (hF.measurable q.2 (hF.Icc_subset (mem_Icc_of_mem_stepSegments hq).2))
  · rw [hW1 q.1]
    refine (norm_add_le _ _).trans ?_
    have h1 := hW1b q.1 (mem_Icc_of_mem_stepSegments hq).1 x
    have h2 := hW2b q.2 (mem_Icc_of_mem_stepSegments hq).2 x
    linarith

end Small

end StepSetting

end Balaban.Fluctuation
