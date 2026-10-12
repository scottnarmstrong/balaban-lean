/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2One
public import Balaban.Localization.DecoupledSolveAnalytic

/-!
# Theorem I-4a (b): analytic dependence on `(s, data)`, for a cover `C` and an operator `H`

The abstract core `exists_analytic_core` with the parameter space `DecParams C × Edat H N` and the
family `α ↦ G_s(α)` of the pair `(C, H)`, whose entries are analytic in `(s, α)` (`dg4_analytic`).
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}

/-- **Analyticity of the entries of `G_s(A)`** (the conclusion of `dg4_analytic` with the
constant `c`). -/
def AnSpec (d L : ℕ) [NeZero L] (Kc Cx c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, CoverBase C H a ν Kc Cx →
      ∀ {κ : ℝ}, 0 ≤ κ → c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ x y : H.Ω 1, AnalyticOnNhd ℂ
        (fun p : DecParams C × (H.Ω 1 → ℂ) => Gs C H a ν p.2 (extS C p.1) x y)
        {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
          ∀ z, ‖p.2 z‖ < coerciveConst d / (2 * (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2)}

theorem AnSpec.mono_c {d L : ℕ} [NeZero L] {c c' : ℝ} (h : AnSpec d L Kc Cx c) (hc : c ≤ c') :
    AnSpec d L Kc Cx c' := by
  refine ⟨h.1.trans hc, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S κ hκ hM x y
  exact h.2 C H S hκ (le_trans (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le) hM) x y

theorem anSpec_exists {d L : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) (hCx : 0 ≤ Cx) : ∃ c : ℝ, AnSpec d L Kc Cx c := by
  obtain ⟨c, hc, Hh⟩ := dg4_analytic (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  refine ⟨c, hc, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S κ hκ hM x y
  exact Hh C H S hκ hM x y



omit [NeZero N₁] [NeZero L] in
theorem isOpen_param_lt {κ : ℝ} : IsOpen {s : DecParams C | ∀ P, ‖s P‖ < Real.exp κ} :=
  isOpen_forall_lt (f := fun (P : C.cubeIdx) (s : DecParams C) => ‖s P‖)
    (c := fun _ => Real.exp κ) fun P => by fun_prop

/-- **Theorem I-4a (b): analyticity in `(s, data)`.**  On the open set of parameters
`|s_P| < e^{κ₁}` and data satisfying (P1)--(P4) (strictly), the solution
`(δφ(s), δα(s))` of Theorem I-4a is a complex-analytic function of `(s, φ₀, α₀, δΨ, f₁)`, and it
has the properties of `i4a_exists_unique`. -/
theorem i4a_analytic {cstar BG : ℝ} (hF : FamSpec d L Kc Cx cstar BG) (hA : AnSpec d L Kc Cx cstar)
    (S : CoverBase C H a ν Kc Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (ιU : Bool) {δ₀ δ₁ : ℝ}
    (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)) :
    ∃ sol : DecParams C × Edat H N → (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ),
      AnalyticOnNhd ℂ sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧ StrictDataM H N ιU δ₀ δ₁ p.2} ∧
      ∀ p : DecParams C × Edat H N, (∀ P, ‖p.1 P‖ < Real.exp κ) → StrictDataM H N ιU δ₀ δ₁ p.2 →
        (sol p).1 = dphi H (decG C H a ν p.1) p.2.2.1 p.2.1
          (pertSource H a p.2.2.2.1 p.2.2.2.2) (sol p).2 ∧
        DecFixed C H a ν p.1 ιU p.2.2.1 p.2.1 (pertSource H a p.2.2.2.1 p.2.2.2.2) (sol p).2 ∧
        Small H (sol p).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) ∧
        Small H (sol p).2 (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        SupBounds H (sol p).1 (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        (∀ δα' : H.Ω 1 → ℂ, Small H δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) →
          DecFixed C H a ν p.1 ιU p.2.2.1 p.2.1 (pertSource H a p.2.2.2.1 p.2.2.2.2) δα' →
          δα' = (sol p).2) := by
  have hd0 : 0 < d := by have := S.hd; omega
  set B : ℝ := famConst d L BG κ with hB
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB0 : 0 ≤ B := by have := famConst_ge_one (L := L) hF.2.1 κ hd0; linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hC := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ h0 h1 hδ₀ hδ₁
  have hle1 : δ₀ ≤ 1 := hδ₀.trans (by
    have := (min_le_right (min (cTau' d L N B / 3) (Γ / 4))
      (min (min 1 (c6' d L N B Γ / (2 * cN' d L N B))) (cTau' d L N B / (3 * cF d L))))
    exact this.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hPo : IsOpen {p : DecParams C × Edat H N | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM H N ιU δ₀ δ₁ p.2} := by
    have h1' := (isOpen_param_lt (C := C) (κ := κ)).preimage (continuous_fst (X := DecParams C)
      (Y := Edat H N))
    have h2' := (isOpen_strictDataM (G := H) (N := N) ιU δ₀ δ₁).preimage
      (continuous_snd (X := DecParams C) (Y := Edat H N))
    exact h1'.inter h2'
  have hyp : ∀ p : DecParams C × Edat H N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM H N ιU δ₀ δ₁ p.2 → DecHyp H a ν ιU p.2.2.1 p.2.1 p.2.2.2.1 p.2.2.2.2 δ₀ δ₁ :=
    fun p _ hp => StrictDataM.hyp S.toGreen h0 h1 hle1 hp
  have hfam : ∀ p : DecParams C × Edat H N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      GreenFamily H N (decG C H a ν p.1) B Γ := fun p hp =>
    (hF.2.2 C H S hκ hM (s := p.1) (fun P => (hp P).le) N).1.1
  have hc0 : 0 < coerciveConst d := by
    have := gamma1_pos hd0; unfold gamma1 at this; linarith
  have aΨ : ∀ (p : DecParams C × Edat H N) y i,
      AnalyticAt ℂ (fun p : DecParams C × Edat H N => p.2.2.2.1 y i) p :=
    fun p y i => by fun_prop
  have af : ∀ (p : DecParams C × Edat H N) (y : H.Ω 1) i,
      AnalyticAt ℂ (fun p : DecParams C × Edat H N => p.2.2.2.2 (y, i)) p :=
    fun p y i => by fun_prop
  obtain ⟨ξs, hanal, hξs, hdφ⟩ := exists_analytic_core
    (P := {p : DecParams C × Edat H N | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM H N ιU δ₀ δ₁ p.2}) (γ := Γ) hPo (ιU := ιU)
    (fun p => decG C H a ν p.1) (fun p => dirichletOperator H a ν p.2.2.1) (fun p => p.2.2.1)
    (fun p => p.2.1) (fun p => pertSource H a p.2.2.2.1 p.2.2.2.2)
    (fun p hp => hfam p hp.1) (fun p hp => (hyp p hp.1 hp.2).setup) hC
    (fun y i p _ => by fun_prop) (fun y p _ => by fun_prop)
    (fun y i p _ => an_pertSource (G := H) a (q := p) (fun p : DecParams C × Edat H N => p.2.2.2.1)
      (fun p : DecParams C × Edat H N => p.2.2.2.2) (aΨ p) (af p) y i)
    (fun y z p _ => AnalyticAt.comp (g := fun α : H.Ω 1 → ℂ => dirichletOperator H a ν α y z)
      (f := fun p : DecParams C × Edat H N => p.2.2.1)
      (analyticAt_dirichletOperator_apply H a ν p.2.2.1 y z) (by fun_prop))
    (fun y z r hr => by
      have hadm : ∀ z' : H.Ω 1, ‖r.1 z'‖ <
          coerciveConst d / (2 * (H.spacing (z' : CTorus d L N₁ m₁ K)) ^ 2) := by
        intro z'
        have hz := hr.1 z'
        have hp : 0 < (H.spacing (z' : CTorus d L N₁ m₁ K)) ^ 2 := by
          have := spacing_pos H (x := (z' : CTorus d L N₁ m₁ K)); positivity
        rw [lt_div_iff₀ (by positivity)]
        have : gamma1 d = coerciveConst d / 2 := rfl
        rw [hΓdef, this] at hz
        nlinarith
      have h := hA.2 C H S hκ hM y z (r.2.1, r.1) ⟨hr.2.1, hadm⟩
      exact AnalyticAt.comp (g := fun p : DecParams C × (H.Ω 1 → ℂ) =>
        Gs C H a ν p.2 (extS C p.1) y z) (f := fun r : (H.Ω 1 → ℂ) × (DecParams C × Edat H N) =>
        (r.2.1, r.1)) h (by fun_prop))
  have hfixed : ∀ p : DecParams C × Edat H N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM H N ιU δ₀ δ₁ p.2 →
      DecFixed C H a ν p.1 ιU p.2.2.1 p.2.1 (pertSource H a p.2.2.2.1 p.2.2.2.2)
        (toAlpha H (ξs p)) ∧ Small H (toAlpha H (ξs p)) (c6' d L N B Γ) := by
    intro p hp1 hp2
    obtain ⟨hb, hfx, -⟩ := hξs p ⟨hp1, hp2⟩
    rw [mem_closedBall_zero_iff] at hb
    exact ⟨fixed_of_Smap_fixed hfx,
      small_toAlpha H (ξs p) (fun x => (norm_le_pi_norm (ξs p) x).trans hb)⟩
  refine ⟨fun p => (dphi H (decG C H a ν p.1) p.2.2.1 p.2.1 (pertSource H a p.2.2.2.1 p.2.2.2.2)
    (toAlpha H (ξs p)), toAlpha H (ξs p)), ?_, ?_⟩
  · intro p hp
    have hξy : ∀ y, AnalyticAt ℂ (fun p => ξs p y) p := fun y => analyticAt_pi_iff.1 (hanal p hp) y
    have hc : ∀ y : H.Ω 1, AnalyticAt ℂ (fun p : DecParams C × Edat H N =>
        toAlpha H (ξs p) y) p := by
      intro y
      unfold toAlpha
      exact (hξy y).div_const
    refine AnalyticAt.prod ?_ (analyticAt_pi_iff.2 hc)
    refine analyticAt_pi_iff.2 fun ⟨y, j⟩ => ?_
    exact hdφ y j p hp
  · intro p hp1 hp2
    obtain ⟨δα, hfix, hs6, hsK, hdp, huniq, -⟩ := i4a_exists_unique hF C H S hκ hM
      (s := p.1) (fun P => (hp1 P).le) (hyp p hp1 hp2) hδ₀ hδ₁
    obtain ⟨hfp, hsp⟩ := hfixed p hp1 hp2
    have heq : toAlpha H (ξs p) = δα := huniq _ hsp hfp
    simp only
    rw [heq]
    exact ⟨trivial, hfix, hs6, hsK, hdp, huniq⟩

end Balaban.Localization.Dec2
