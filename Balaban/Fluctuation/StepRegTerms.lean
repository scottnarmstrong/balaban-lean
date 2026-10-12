/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepRegCompose
public import Balaban.SmallField.Def6Inhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The three regularity inputs of the step from analyticity of the class terms

* `StepTermsAnalytic C A μ ε`: the Def-6 clauses `analyticE`, `analyticM` of `IsSF` for the terms of
  the step class: `ℰ^{(j)}(y, X; ·)` and `ℳ^{(j)}(x, X; ·)` are analytic on `Ξ^c_j(𝔹_j(X); 1, ε_j)`
  (resp. times `{‖g‖₁ < 1}`).  It follows from `IsSF` (`stepTermsAnalytic_of_isSF`) and is inhabited
  (`nonempty_stepTermsAnalytic`);
* `RayInDomain`: the composition-domain inclusion, the single remaining input: the pairs
  `(ψ_k^{(j)}, h)` of the composed data of `ψ^{(k)} + s ψ'` lie in the domains of the terms for
  `|s| ‖ψ̂‖ < p⁺`;
* `classRegular_of_analytic`, `classRegularLoc_of_analytic`, `classRegularObs_of_analytic`: the named
  inputs `ClassRegular`, `ClassRegularLoc`, `ClassRegularObs` follow from `RayData`,
  `StepTermsAnalytic` and `RayInDomain`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set Matrix

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {pp : ℝ}

/-- **The terms of the step class are analytic on their domains** (Def-6 clauses `analyticE`,
`analyticM`, restricted to the levels `1 ≤ j ≤ k` of the old action), for the kernel sequence `A`,
mass `μ` and radii `ε_j` of the domains `Ξ^c_j(𝔹_j(X); 1, ε_j)`. -/
structure _root_.Balaban.Fluctuation.StepTermsAnalytic (C : StepClass d L N₁ m₁ k N ϱ)
    (A : ℕ → ℝ) (μ : ℝ) (ε : ℕ → ℝ) : Prop where
  analyticE : ∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom C.m₀ j X → y ∈ X →
    AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      C.Tm.E j y X p.1 p.2) {p | XiDom (C.Tm.gs j X) A μ j (ε j) p.1 p.2}
  analyticM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom C.m₀ j X → x ∈ X →
    AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
        Fld d L N₁ m₁ (k + 1) N => C.Tm.M j x X p.1 p.2.1 p.2.2)
      {p | XiDom (C.Tm.gs j X) A μ j (ε j) p.1 p.2.1 ∧ l1 p.2.2 < 1}

end StepSetting

/-- `StepTermsAnalytic` is a consequence of the Def-6 class clauses `IsSF` (on the step torus). -/
theorem stepTermsAnalytic_of_isSF {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (C : StepClass d L N₁ m₁ k N ϱ) {P : Consts} {β ν a : ℕ → ℝ}
    {ρ : (CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) → (Fin N → ℝ) →
      (CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) → ℝ} {Ek : ℝ}
    (hm : C.m₀ = P.m₀) (h : IsSF P β ν a C.Tm ρ Ek) :
    StepTermsAnalytic C (aIdeal L (k + 1) (a (k + 1))) (bgMass L (k + 1) (β (k + 1)) (ν (k + 1)))
      (fun j => P.eps d L j) where
  analyticE j h1 hjk y X hX hy := h.analyticE j h1 (hjk.trans (Nat.le_succ k)) y X (hm ▸ hX) hy
  analyticM j h1 hjk x X hX hx := h.analyticM j h1 (hjk.trans (Nat.le_succ k)) x X (hm ▸ hX) hx

/-- `StepTermsAnalytic` is inhabited: the zero effective action. -/
theorem nonempty_stepTermsAnalytic {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (A : ℕ → ℝ) (μ : ℝ) (ε : ℕ → ℝ) :
    Nonempty (StepTermsAnalytic (zeroClass d L N₁ m₁ k N ϱ) A μ ε) :=
  ⟨⟨fun _ _ _ _ _ _ _ => analyticOnNhd_const, fun _ _ _ _ _ _ _ => analyticOnNhd_const⟩⟩

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {pp : ℝ}
  (C : StepClass d L N₁ m₁ k N ϱ)

/-- **The composition-domain inclusion** (the single domain input): for `|s| ‖ψ̂‖ < p⁺` and every
level `1 ≤ j ≤ k`, the pair `(ψ_k^{(j)}, h)` of (H.2) of the datum of `ψ^{(k)} + s ψ'` lies in the
domain `Ξ^c_j(𝔹_j(X); 1, ε_j)` of every polymer term of level `j`; and the source satisfies
`‖g‖₁ < 1`. -/
structure RayInDomain (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    (g : Fld d L N₁ m₁ (k + 1) N) (A : ℕ → ℝ) (μ : ℝ) (ε : ℕ → ℝ) (pp : ℝ) : Prop where
  hg : l1 g < 1
  dom : ∀ q : ℝ × S.E, |q.1| * ‖q.2‖ < pp → ∀ j, 1 ≤ j → j ≤ k → ∀ X, IsPolyDom C.m₀ j X →
    XiDom (C.Tm.gs j X) A μ j (ε j) (S.pairRay (N := N) j q).1 (S.pairRay (N := N) j q).2

section Analytic

variable {g : Fld d L N₁ m₁ (k + 1) N} {A : ℕ → ℝ} {μ : ℝ} {ε : ℕ → ℝ}
  (R : S.RayData pp) (hT : StepTermsAnalytic C A μ ε) (hD : S.RayInDomain C g A μ ε pp)

include hT hD R in
theorem contDiffAt_Eterm {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {q : ℝ × S.E}
    (hq : |q.1| * ‖q.2‖ < pp) (y : CTorus d L N₁ m₁ (k + 1))
    (X : Set (CTorus d L N₁ m₁ (k + 1))) (hX : IsPolyDom C.m₀ j X) (hy : y ∈ X) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E =>
      C.Tm.E j y X (S.pairRay (N := N) j q).1 (S.pairRay (N := N) j q).2) q := by
  have hat := hT.analyticE j hj1 hjk y X hX hy _ (hD.dom q hq j hj1 hjk X hX)
  have h1 : ContDiffAt ℝ ⊤ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      C.Tm.E j y X p.1 p.2) (S.pairRay (N := N) j q) :=
    (hat.contDiffAt (n := ⊤)).restrict_scalars ℝ
  exact h1.comp q (R.contDiffAt_pairRay hjk hq)

include hT hD R in
theorem contDiffAt_Mterm {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {q : ℝ × S.E}
    (hq : |q.1| * ‖q.2‖ < pp) (x : CTorus d L N₁ m₁ (k + 1))
    (X : Set (CTorus d L N₁ m₁ (k + 1))) (hX : IsPolyDom C.m₀ j X) (hx : x ∈ X) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E =>
      C.Tm.M j x X (S.pairRay (N := N) j q).1 (S.pairRay (N := N) j q).2 g) q := by
  have hat := hT.analyticM j hj1 hjk x X hX hx
    ((S.pairRay (N := N) j q).1, (S.pairRay (N := N) j q).2, g)
    ⟨hD.dom q hq j hj1 hjk X hX, hD.hg⟩
  have h1 : ContDiffAt ℝ ⊤ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
      Fld d L N₁ m₁ (k + 1) N => C.Tm.M j x X p.1 p.2.1 p.2.2)
      ((S.pairRay (N := N) j q).1, (S.pairRay (N := N) j q).2, g) :=
    (hat.contDiffAt (n := ⊤)).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ⊤ (fun q : ℝ × S.E =>
      ((S.pairRay (N := N) j q).1, (S.pairRay (N := N) j q).2, g)) q :=
    (R.contDiffAt_pairRay hjk hq).fst.prodMk
      ((R.contDiffAt_pairRay hjk hq).snd.prodMk contDiffAt_const)
  exact h1.comp q h2

include hT hD R in
theorem contDiffAt_Edens {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {q : ℝ × S.E}
    (hq : |q.1| * ‖q.2‖ < pp) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E =>
      Edens C.m₀ C.Tm j (S.pairRay (N := N) j q).1 (S.pairRay (N := N) j q).2) q := by
  classical
  unfold Edens
  refine ContDiffAt.sum fun y _ => ?_
  unfold Eloc
  have hfin : (polysAt C.m₀ j y).Finite := Set.toFinite _
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine ContDiffAt.sum fun X hX => ?_
  have hX' : X ∈ polysAt C.m₀ j y := hfin.mem_toFinset.1 hX
  exact contDiffAt_Eterm C R hT hD hj1 hjk hq y X hX'.1 hX'.2

include hT hD R in
theorem contDiffAt_Mloc {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {q : ℝ × S.E}
    (hq : |q.1| * ‖q.2‖ < pp) (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E =>
      Mloc C.m₀ C.Tm j x (S.pairRay (N := N) j q).1 (S.pairRay (N := N) j q).2 g i) q := by
  classical
  unfold Mloc
  have hfin : (polysAt C.m₀ j x).Finite := Set.toFinite _
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_apply]
  refine ContDiffAt.sum fun X hX => ?_
  have hX' : X ∈ polysAt C.m₀ j x := hfin.mem_toFinset.1 hX
  exact (contDiffAt_pi.1 (contDiffAt_Mterm C R hT hD hj1 hjk hq x X hX'.1 hX'.2)) i

include hT hD R in
/-- **The composite energy `ℰ_k` along the ray is smooth.** -/
theorem contDiffAt_EcompRay {q : ℝ × S.E} (hq : |q.1| * ‖q.2‖ < pp) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E =>
      EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU (S.psiAt q.1 q.2))) q := by
  unfold EcompAt
  refine ContDiffAt.sum fun j hj => ?_
  obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
  exact contDiffAt_Edens C R hT hD hj1 hjk hq

include hT hD R in
/-- **The vector `ℳ_k` along the ray is smooth componentwise.** -/
theorem contDiffAt_McompRay {q : ℝ × S.E} (hq : |q.1| * ‖q.2‖ < pp)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E =>
      McompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU (S.psiAt q.1 q.2)) g y i) q := by
  unfold McompAt
  refine (R.contDiffAt_bgComp y i hq).add (ContDiffAt.sum fun j hj => ?_)
  obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
  exact contDiffAt_Mloc C R hT hD hj1 hjk hq y i

end Analytic

end StepSetting

end Balaban.Fluctuation
