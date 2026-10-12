/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledOne
public import Balaban.Background.ContractionAnalytic
public import Balaban.Background.ContractionCoreAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Analytic.Constructions

/-!
# Theorem I-4a (b): analytic dependence on `(s, data)`

The abstract core `exists_analytic_core` is applied with the parameter space
`Pr = DecParams G × Edat G N` (the parameters `s_P` of the cubes and the data
`(φ₀, α₀, δΨ, f₁)`) and the Green family `G_s(α)`, whose entries are analytic in `(s, α)`
(`dg4_analytic`).  The open set of parameters is `|s_P| < e^{κ₁}` together with the data satisfying
(P1)--(P4) with strict inequalities (in mode P without (P4)).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Strict

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- The strict data inequalities (P1)--(P3) (the first six conditions of `StrictData`). -/
def StrictDataP (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (N : ℕ) (δ₀ δ₁ : ℝ) (p : Edat G N) :
    Prop :=
  (∀ (x : G.Ω 1) (μ : Fin d),
      vn (p.1 ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - p.1 x) <
        δ₀ / G.spacing (x : CTorus d L N₁ m₁ K) ∧
      vn (p.1 ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) - p.1 x) <
        δ₀ / G.spacing (x : CTorus d L N₁ m₁ K)) ∧
  (∀ x : G.Ω 1, vn (fun i => ∑ μ : Fin d, (p.1 ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i +
      p.1 ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i - 2 * p.1 x i)) <
      δ₀ / G.spacing (x : CTorus d L N₁ m₁ K) ^ 2) ∧
  (∀ x : G.Ω 1, vn (p.1 x) < 3 / 2) ∧
  (∀ x : G.Ω 1, G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖p.2.1 x‖ < δ₀) ∧
  (∀ (x : G.Ω 1) (i : Fin N), G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖p.2.2.2 (x, i)‖ < δ₁) ∧
  (∀ x : dataSites G, vn (p.2.2.1 x) < δ₁)

/-- The strict data inequalities of Theorem I-4a in the mode `ιU`: (P4) only in mode U. -/
def StrictDataM (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (N : ℕ) (ιU : Bool) (δ₀ δ₁ : ℝ)
    (p : Edat G N) : Prop :=
  StrictDataP G N δ₀ δ₁ p ∧ (ιU = true →
    (∀ x : G.Ω 1, ‖gdef G p.1 x‖ < δ₁) ∧
    (∀ x : G.Ω 1, G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      ‖negLap (zeroExt (G.Ω 1) (gdef G p.1)) (x : CTorus d L N₁ m₁ K)‖ < δ₁))

theorem isOpen_strictDataP (δ₀ δ₁ : ℝ) : IsOpen {p : Edat G N | StrictDataP G N δ₀ δ₁ p} := by
  unfold StrictDataP
  simp only [Set.ofPred_and]
  exact (isOpen_strictData_aux1 δ₀).inter ((isOpen_strictData_aux2 δ₀).inter
    (isOpen_strictData_o3.inter ((isOpen_strictData_o4 δ₀).inter ((isOpen_strictData_o5 δ₁).inter
    (isOpen_strictData_o6 δ₁)))))

theorem isOpen_strictDataM (ιU : Bool) (δ₀ δ₁ : ℝ) :
    IsOpen {p : Edat G N | StrictDataM G N ιU δ₀ δ₁ p} := by
  cases ιU
  · have : {p : Edat G N | StrictDataM G N false δ₀ δ₁ p} = {p | StrictDataP G N δ₀ δ₁ p} := by
      ext p; simp [StrictDataM]
    rw [this]; exact isOpen_strictDataP δ₀ δ₁
  · have : {p : Edat G N | StrictDataM G N true δ₀ δ₁ p} =
        {p | StrictDataP G N δ₀ δ₁ p} ∩ ({p : Edat G N | ∀ x : G.Ω 1, ‖gdef G p.1 x‖ < δ₁} ∩
          {p : Edat G N | ∀ x : G.Ω 1, G.spacing (x : Torus d (N₁ * L ^ m₁ * L ^ K)) ^ 2 *
            ‖negLap (zeroExt (G.Ω 1) (gdef G p.1)) (x : Torus d (N₁ * L ^ m₁ * L ^ K))‖ < δ₁}) := by
      ext p; simp [StrictDataM]
    rw [this]
    exact (isOpen_strictDataP δ₀ δ₁).inter ((isOpen_strictData_o7 δ₁).inter (isOpen_strictData_o8 δ₁))

theorem StrictDataM.hyp {a : ℕ → ℝ} {ν : ℝ} {ιU : Bool} (S : GreenSetting G a ν) {δ₀ δ₁ : ℝ}
    (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁) (hle0 : δ₀ ≤ 1) {p : Edat G N}
    (hp : StrictDataM G N ιU δ₀ δ₁ p) :
    DecHyp G a ν ιU p.2.1 p.1 p.2.2.1 p.2.2.2 δ₀ δ₁ := by
  obtain ⟨⟨c1, c2, c3, c4, c5, c6⟩, c78⟩ := hp
  refine ⟨S, h0, h1, hle0, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx μ
    exact ⟨(c1 ⟨x, hx⟩ μ).1.le, (c1 ⟨x, hx⟩ μ).2.le⟩
  · intro x hx; exact (c2 ⟨x, hx⟩).le
  · intro x hx; exact (c3 ⟨x, hx⟩).le
  · intro x; exact (c4 x).le
  · intro x i; exact (c5 x i).le
  · intro x hx; exact (c6 ⟨x, hx⟩).le
  · intro h x; exact ((c78 h).1 x).le
  · intro h x; exact ((c78 h).2 x).le

end Strict

/-- **Analyticity of the entries of `G_s(A)`** (the conclusion of `dg4_analytic` with the
constant `c`). -/
def AnSpec (d L : ℕ) [NeZero L] (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {κ : ℝ}, 0 ≤ κ → c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ x y : G.Ω 1, AnalyticOnNhd ℂ
        (fun p : DecParams G × (G.Ω 1 → ℂ) => Gs G a ν p.2 (extS G p.1) x y)
        {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
          ∀ z, ‖p.2 z‖ < coerciveConst d / (2 * (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2)}

theorem AnSpec.mono_c {d L : ℕ} [NeZero L] {c c' : ℝ} (h : AnSpec d L c) (hc : c ≤ c') :
    AnSpec d L c' := by
  refine ⟨h.1.trans hc, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S κ hκ hM x y
  exact h.2 G S hκ (le_trans (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le) hM) x y

theorem anSpec_exists {d L : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) : ∃ c : ℝ, AnSpec d L c := by
  obtain ⟨c, hc, H⟩ := dg4_analytic (d := d) (L := L) hd hL
  refine ⟨c, hc, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S κ hκ hM x y
  exact H G S hκ hM x y

section Analytic

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem isOpen_param_lt {κ : ℝ} : IsOpen {s : DecParams G | ∀ P, ‖s P‖ < Real.exp κ} :=
  isOpen_forall_lt (f := fun (P : cubeIdx G) (s : DecParams G) => ‖s P‖)
    (c := fun _ => Real.exp κ) fun P => by fun_prop

/-- **Theorem I-4a (b): analyticity in `(s, data)`.**  On the open set of parameters
`|s_P| < e^{κ₁}` and data satisfying (P1)--(P4) (strictly), the solution
`(δφ(s), δα(s))` of Theorem I-4a is a complex-analytic function of `(s, φ₀, α₀, δΨ, f₁)`, and it
has the properties of `i4a_exists_unique`. -/
theorem i4a_analytic {cstar BG : ℝ} (hF : FamSpec d L cstar BG) (hA : AnSpec d L cstar)
    (S : DGSetting G a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (ιU : Bool) {δ₀ δ₁ : ℝ}
    (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)) :
    ∃ sol : DecParams G × Edat G N → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
      AnalyticOnNhd ℂ sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧ StrictDataM G N ιU δ₀ δ₁ p.2} ∧
      ∀ p : DecParams G × Edat G N, (∀ P, ‖p.1 P‖ < Real.exp κ) → StrictDataM G N ιU δ₀ δ₁ p.2 →
        (sol p).1 = dphi G (decG G a ν p.1) p.2.2.1 p.2.1
          (pertSource G a p.2.2.2.1 p.2.2.2.2) (sol p).2 ∧
        DecFixed G a ν p.1 ιU p.2.2.1 p.2.1 (pertSource G a p.2.2.2.1 p.2.2.2.2) (sol p).2 ∧
        Small G (sol p).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) ∧
        Small G (sol p).2 (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        SupBounds G (sol p).1 (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        (∀ δα' : G.Ω 1 → ℂ, Small G δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) →
          DecFixed G a ν p.1 ιU p.2.2.1 p.2.1 (pertSource G a p.2.2.2.1 p.2.2.2.2) δα' →
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
  have hPo : IsOpen {p : DecParams G × Edat G N | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM G N ιU δ₀ δ₁ p.2} := by
    have h1' := (isOpen_param_lt (G := G) (κ := κ)).preimage (continuous_fst (X := DecParams G)
      (Y := Edat G N))
    have h2' := (isOpen_strictDataM (G := G) (N := N) ιU δ₀ δ₁).preimage
      (continuous_snd (X := DecParams G) (Y := Edat G N))
    exact h1'.inter h2'
  have hyp : ∀ p : DecParams G × Edat G N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM G N ιU δ₀ δ₁ p.2 → DecHyp G a ν ιU p.2.2.1 p.2.1 p.2.2.2.1 p.2.2.2.2 δ₀ δ₁ :=
    fun p _ hp => StrictDataM.hyp S.toGreen h0 h1 hle1 hp
  have hfam : ∀ p : DecParams G × Edat G N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      GreenFamily G N (decG G a ν p.1) B Γ := fun p hp =>
    (hF.2.2 G S hκ hM (s := p.1) (fun P => (hp P).le) N).1.1
  have hc0 : 0 < coerciveConst d := by
    have := gamma1_pos hd0; unfold gamma1 at this; linarith
  have aΨ : ∀ (p : DecParams G × Edat G N) y i,
      AnalyticAt ℂ (fun p : DecParams G × Edat G N => p.2.2.2.1 y i) p :=
    fun p y i => by fun_prop
  have af : ∀ (p : DecParams G × Edat G N) (y : G.Ω 1) i,
      AnalyticAt ℂ (fun p : DecParams G × Edat G N => p.2.2.2.2 (y, i)) p :=
    fun p y i => by fun_prop
  obtain ⟨ξs, hanal, hξs, hdφ⟩ := exists_analytic_core
    (P := {p : DecParams G × Edat G N | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM G N ιU δ₀ δ₁ p.2}) (γ := Γ) hPo (ιU := ιU)
    (fun p => decG G a ν p.1) (fun p => dirichletOperator G a ν p.2.2.1) (fun p => p.2.2.1)
    (fun p => p.2.1) (fun p => pertSource G a p.2.2.2.1 p.2.2.2.2)
    (fun p hp => hfam p hp.1) (fun p hp => (hyp p hp.1 hp.2).setup) hC
    (fun y i p _ => by fun_prop) (fun y p _ => by fun_prop)
    (fun y i p _ => an_pertSource (G := G) a (q := p) (fun p : DecParams G × Edat G N => p.2.2.2.1)
      (fun p : DecParams G × Edat G N => p.2.2.2.2) (aΨ p) (af p) y i)
    (fun y z p _ => AnalyticAt.comp (g := fun α : G.Ω 1 → ℂ => dirichletOperator G a ν α y z)
      (f := fun p : DecParams G × Edat G N => p.2.2.1)
      (analyticAt_dirichletOperator_apply G a ν p.2.2.1 y z) (by fun_prop))
    (fun y z r hr => by
      have hadm : ∀ z' : G.Ω 1, ‖r.1 z'‖ <
          coerciveConst d / (2 * (G.spacing (z' : CTorus d L N₁ m₁ K)) ^ 2) := by
        intro z'
        have hz := hr.1 z'
        have hp : 0 < (G.spacing (z' : CTorus d L N₁ m₁ K)) ^ 2 := by
          have := spacing_pos G (x := (z' : CTorus d L N₁ m₁ K)); positivity
        rw [lt_div_iff₀ (by positivity)]
        have : gamma1 d = coerciveConst d / 2 := rfl
        rw [hΓdef, this] at hz
        nlinarith
      have h := hA.2 G S hκ hM y z (r.2.1, r.1) ⟨hr.2.1, hadm⟩
      exact AnalyticAt.comp (g := fun p : DecParams G × (G.Ω 1 → ℂ) =>
        Gs G a ν p.2 (extS G p.1) y z) (f := fun r : (G.Ω 1 → ℂ) × (DecParams G × Edat G N) =>
        (r.2.1, r.1)) h (by fun_prop))
  have hfixed : ∀ p : DecParams G × Edat G N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM G N ιU δ₀ δ₁ p.2 →
      DecFixed G a ν p.1 ιU p.2.2.1 p.2.1 (pertSource G a p.2.2.2.1 p.2.2.2.2)
        (toAlpha G (ξs p)) ∧ Small G (toAlpha G (ξs p)) (c6' d L N B Γ) := by
    intro p hp1 hp2
    obtain ⟨hb, hfx, -⟩ := hξs p ⟨hp1, hp2⟩
    rw [mem_closedBall_zero_iff] at hb
    exact ⟨fixed_of_Smap_fixed hfx,
      small_toAlpha G (ξs p) (fun x => (norm_le_pi_norm (ξs p) x).trans hb)⟩
  refine ⟨fun p => (dphi G (decG G a ν p.1) p.2.2.1 p.2.1 (pertSource G a p.2.2.2.1 p.2.2.2.2)
    (toAlpha G (ξs p)), toAlpha G (ξs p)), ?_, ?_⟩
  · intro p hp
    have hξy : ∀ y, AnalyticAt ℂ (fun p => ξs p y) p := fun y => analyticAt_pi_iff.1 (hanal p hp) y
    have hc : ∀ y : G.Ω 1, AnalyticAt ℂ (fun p : DecParams G × Edat G N =>
        toAlpha G (ξs p) y) p := by
      intro y
      unfold toAlpha
      exact (hξy y).div_const
    refine AnalyticAt.prod ?_ (analyticAt_pi_iff.2 hc)
    refine analyticAt_pi_iff.2 fun ⟨y, j⟩ => ?_
    exact hdφ y j p hp
  · intro p hp1 hp2
    obtain ⟨δα, hfix, hs6, hsK, hdp, huniq, -⟩ := i4a_exists_unique hF G S hκ hM
      (s := p.1) (fun P => (hp1 P).le) (hyp p hp1 hp2) hδ₀ hδ₁
    obtain ⟨hfp, hsp⟩ := hfixed p hp1 hp2
    have heq : toAlpha G (ξs p) = δα := huniq _ hsp hfp
    simp only
    rw [heq]
    exact ⟨trivial, hfix, hs6, hsK, hdp, huniq⟩

end Analytic

end Balaban.Localization
