/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.ContractionAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proposition 5.1 jointly analytic in the data and the mass

BACKGROUND.md §5.1 (Proposition 5.1), used in FLUCTUATION.md §3.6, Lemma 3.5 (ii)
(P4 (4.10)–(4.11)),
where the mass `ν_u = ν (1 + ξ₂) / (1 + ξ₃)` of the perturbed system depends on the complex
renormalization parameters `ξ`.

The mass enters `H_D(α) = -Δ^D + Q* a Q + ν + α` only through the diagonal, so a change of mass is
a constant shift of the multiplier (`dirichletOperator_mass_shift`):
`H_D^{(ν')}(α) = H_D^{(ν)}(α + (ν' - ν))`.  This identity gives the perturbed system a meaning for a
*complex* mass `m` (`IsPerturbedM`, the system with operator `H_D^{(0)}(α₀ + m)`), equal to the
landed system at every real mass (`isPerturbedM_ofReal`).  The contraction of Proposition 5.1 at a
real admissible reference mass `ν` absorbs the shift `m - ν` into the base multiplier, uniformly in
the mass.  Hence:

* `prop51_mass_exists_unique`: Proposition 5.1 with a complex mass `m` (existence, bounds `K₂ δ₁`,
  uniqueness in the class `|δα|₂ ≤ c₆`), under the hypotheses (P1)–(P4) for the shifted multiplier
  `α₀ + (m - ν)` at a reference mass `ν`;
* `prop51_mass_analytic`: the solution is a complex-analytic function of `(data, m)` jointly on the
  open set where the shifted data satisfy (P1)–(P4) strictly;
* `prop51_mass_analytic_uniform`: one function, analytic jointly in `(data, m)` on the union of
  these
  open sets over **all** admissible real reference masses `0 ≤ ν ≤ L^{-2k}` (the contraction
  constants of Proposition 5.1 do not depend on `ν` in this range).
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Shift

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The mass enters `-Δ + ν + Q* a Q` as `ν · 1`. -/
theorem fullMatrix_mass_shift (a : ℕ → ℝ) (ν ν' : ℝ) :
    fullMatrix G a ν' = fullMatrix G a ν + (ν' - ν) • (1 : Matrix _ _ ℝ) := by
  unfold fullMatrix latticeLaplacian
  have e : ((2 * d + ν' : ℝ)) • (1 : Matrix (Torus d (N₀ * L ^ k)) (Torus d (N₀ * L ^ k)) ℝ) =
      (2 * d + ν : ℝ) • (1 : Matrix _ _ ℝ) + (ν' - ν) • (1 : Matrix _ _ ℝ) := by
    rw [← add_smul]; congr 1; ring
  rw [e]
  abel

/-- **The mass shift**: `H_D^{(ν')}(α) = H_D^{(ν)}(α + (ν' - ν))`. -/
theorem dirichletOperator_mass_shift (a : ℕ → ℝ) (ν ν' : ℝ) (α : G.Ω 1 → ℂ) :
    dirichletOperator G a ν' α =
      dirichletOperator G a ν (α + fun _ => ((ν' - ν : ℝ) : ℂ)) := by
  ext i j
  simp only [dirichletOperator, fullMatrix_mass_shift G a ν ν', Green.restrictOp, Matrix.add_apply,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.diagonal_apply, Pi.add_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h; simp; ring
  · have h' : (i : Torus d (N₀ * L ^ k)) ≠ j := fun e => h (Subtype.ext e)
    simp [h, h']

theorem isPerturbed_mass_shift (a : ℕ → ℝ) (ν ν' : ℝ) (α₀ : G.Ω 1 → ℂ)
    (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (Fs δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ) :
    IsPerturbed G a ν' α₀ φ₀ Fs δφ δα ↔
      IsPerturbed G a ν (α₀ + fun _ => ((ν' - ν : ℝ) : ℂ)) φ₀ Fs δφ δα := by
  unfold IsPerturbed
  rw [dirichletOperator_mass_shift G a ν ν']

/-- **The perturbed system with a complex mass `m`**: (P-1), (P-2) for the operator
`H_D^{(0)}(α₀ + m) = -Δ^D + Q* a Q + m + α₀`. -/
def IsPerturbedM (a : ℕ → ℝ) (m : ℂ) (α₀ : G.Ω 1 → ℂ) (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (Fs δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ) : Prop :=
  IsPerturbed G a 0 (α₀ + fun _ => m) φ₀ Fs δφ δα

/-- The complex-mass system is the landed system at any real reference mass `ν` with the multiplier
shifted by `m - ν`. -/
theorem isPerturbedM_iff (a : ℕ → ℝ) (ν : ℝ) (m : ℂ) (α₀ : G.Ω 1 → ℂ)
    (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (Fs δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ) :
    IsPerturbedM G a m α₀ φ₀ Fs δφ δα ↔
      IsPerturbed G a ν (α₀ + fun _ => m - (ν : ℂ)) φ₀ Fs δφ δα := by
  unfold IsPerturbedM
  rw [isPerturbed_mass_shift G a 0 ν (α₀ + fun _ => m - (ν : ℂ))]
  have e : (α₀ + fun _ => m - (ν : ℂ)) + (fun _ => ((ν - 0 : ℝ) : ℂ)) = α₀ + fun _ => m := by
    funext x; simp only [Pi.add_apply, sub_zero]; ring
  rw [e]

/-- At a real mass the complex-mass system is the landed one. -/
theorem isPerturbedM_ofReal (a : ℕ → ℝ) (ν : ℝ) (α₀ : G.Ω 1 → ℂ)
    (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (Fs δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ) :
    IsPerturbedM G a (ν : ℂ) α₀ φ₀ Fs δφ δα ↔ IsPerturbed G a ν α₀ φ₀ Fs δφ δα := by
  rw [isPerturbedM_iff G a ν]
  have e : (α₀ + fun _ => (ν : ℂ) - (ν : ℂ)) = α₀ := by funext x; simp
  rw [e]

/-- The base field `φ₀` enters the perturbed system only on `Ω₁`. -/
theorem isPerturbedM_congr_base (a : ℕ → ℝ) (m : ℂ) (α₀ : G.Ω 1 → ℂ)
    {φ₀ φ₀' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (h : ∀ (x : G.Ω 1) i, φ₀ x i = φ₀' x i)
    (Fs δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ) :
    IsPerturbedM G a m α₀ φ₀ Fs δφ δα ↔ IsPerturbedM G a m α₀ φ₀' Fs δφ δα := by
  unfold IsPerturbedM IsPerturbed
  have e1 : (fun p : G.Ω 1 × Fin N => Fs p - δα p.1 * φ₀ p.1 p.2) =
      fun p => Fs p - δα p.1 * φ₀' p.1 p.2 := by
    funext p; rw [h]
  have e2 : ∀ x : G.Ω 1, (∑ i, (φ₀ x i + δφ (x, i)) * (φ₀ x i + δφ (x, i)) = 1) ↔
      (∑ i, (φ₀' x i + δφ (x, i)) * (φ₀' x i + δφ (x, i)) = 1) := by
    intro x; simp only [h]
  rw [e1]
  exact and_congr Iff.rfl (forall_congr' e2)

end Shift

section Exists

variable {G : GeneratingSet d L N₀ k ϱ}

/-- **Proposition 5.1 with a complex mass `m`.**  If the data `(φ₀, α₀ + (m - ν), δΨ, f₁)` satisfy
the hypotheses (P1)–(P4) at a real reference mass `ν` (`Prop51Hyp`), the complex-mass system has a
solution with `|δφ|₀, |∂δφ|₁, |Δ^D δφ|₂ ≤ K₂ δ₁`, `|δα|₂ ≤ K₂ δ₁`, unique in `|δα|₂ ≤ c₆`. -/
theorem prop51_mass_exists_unique (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} {m : ℂ} {α₀ : G.Ω 1 → ℂ}
    {φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {δΨ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {f₁ : G.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}
    (H : Prop51Hyp G a ν (α₀ + fun _ => m - (ν : ℂ)) φ₀ δΨ f₁ δ₀ δ₁) :
    ∃ (δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ),
      IsPerturbedM G a m α₀ φ₀ (pertSource G a δΨ f₁) δφ δα ∧
      Small G δα (cK2 d L N * δ₁) ∧ SupBounds G δφ (cK2 d L N * δ₁) ∧
      ∀ (δφ' : G.Ω 1 × Fin N → ℂ) (δα' : G.Ω 1 → ℂ),
        IsPerturbedM G a m α₀ φ₀ (pertSource G a δΨ f₁) δφ' δα' →
        Small G δα' (c6 d L N) → δφ' = δφ ∧ δα' = δα := by
  obtain ⟨δφ, δα, hP, hs, hsup, hu⟩ := prop51_exists_unique hd H
  refine ⟨δφ, δα, (isPerturbedM_iff G a ν m α₀ φ₀ _ _ _).2 hP, hs, hsup, fun δφ' δα' hP' hs' => ?_⟩
  exact hu δφ' δα' ((isPerturbedM_iff G a ν m α₀ φ₀ _ _ _).1 hP') hs'

variable (G) in
/-- The shift of the data of Proposition 5.1 by a complex mass `m` relative to the reference mass
`ν`: the base multiplier becomes `α₀ + (m - ν)`. -/
def massShift (N : ℕ) (ν : ℝ) (q : Edat G N × ℂ) : Edat G N :=
  (q.1.1, q.1.2.1 + (fun _ => q.2 - (ν : ℂ)), q.1.2.2)

theorem analyticAt_massShift (ν : ℝ) (q : Edat G N × ℂ) :
    AnalyticAt ℂ (massShift G N ν) q := by
  unfold massShift
  have h2 : AnalyticAt ℂ (fun q : Edat G N × ℂ => q.2) q := aa_snd' q
  refine AnalyticAt.prod (by fun_prop) (AnalyticAt.prod ?_ (by fun_prop))
  refine AnalyticAt.add (by fun_prop) ?_
  exact analyticAt_pi_iff.2 fun _ => h2.sub analyticAt_const

/-- **Proposition 5.1, analyticity** (`prop51_analytic`), with the additional conclusion that the
solution lies in the uniqueness class `|δα|₂ ≤ c₆` (it is the fixed point of the contraction in the
ball of radius `c₆`). -/
theorem prop51_analytic_small (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (S : GreenSetting G a ν)
    {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁) (hle0 : δ₀ ≤ deltaStar d L N)
    (hle1 : δ₁ ≤ deltaStar d L N) :
    ∃ sol : Edat G N → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
      AnalyticOnNhd ℂ sol {p | StrictData G N δ₀ δ₁ p} ∧
      ∀ p : Edat G N, StrictData G N δ₀ δ₁ p →
        IsPerturbed G a ν p.2.1 p.1 (pertSource G a p.2.2.1 p.2.2.2) (sol p).1 (sol p).2 ∧
        Small G (sol p).2 (cK2 d L N * δ₁) ∧ SupBounds G (sol p).1 (cK2 d L N * δ₁) ∧
        Small G (sol p).2 (c6 d L N) ∧
        ∀ (δφ' : G.Ω 1 × Fin N → ℂ) (δα' : G.Ω 1 → ℂ),
          IsPerturbed G a ν p.2.1 p.1 (pertSource G a p.2.2.1 p.2.2.2) δφ' δα' →
          Small G δα' (c6 d L N) → δφ' = (sol p).1 ∧ δα' = (sol p).2 := by
  have hPo := isOpen_strictData (G := G) (N := N) δ₀ δ₁
  have hC := coreHyp_small hd h0 h1 hle0 hle1
  have hyp := fun p (hp : StrictData G N δ₀ δ₁ p) => StrictData.hyp S h0 h1 hle0 hle1 hp
  have aΨ : ∀ (p : Edat G N) y i, AnalyticAt ℂ (fun p : Edat G N => p.2.2.1 y i) p :=
    fun p y i => by fun_prop
  have af : ∀ (p : Edat G N) (y : G.Ω 1) i, AnalyticAt ℂ (fun p : Edat G N => p.2.2.2 (y, i)) p :=
    fun p y i => by fun_prop
  obtain ⟨ξs, hanal, hξs, hdφ⟩ := exists_analytic_core
    (P := {p : Edat G N | StrictData G N δ₀ δ₁ p}) (γ := gamma1 d) hPo (ιU := true)
    (fun _ => greenD G a ν) (fun p => dirichletOperator G a ν p.2.1) (fun p => p.2.1)
    (fun p => p.1) (fun p => pertSource G a p.2.2.1 p.2.2.2) (fun _ _ => S.family (N := N))
    (fun p hp => (hyp p hp).setup) hC
    (fun y i p _ => by fun_prop) (fun y p _ => by fun_prop)
    (fun y i p _ => an_pertSource (G := G) a (q := p) (fun p : Edat G N => p.2.2.1)
      (fun p : Edat G N => p.2.2.2) (aΨ p) (af p) y i)
    (fun y z p _ => AnalyticAt.comp (g := fun α : G.Ω 1 → ℂ => dirichletOperator G a ν α y z)
      (f := fun p : Edat G N => p.2.1) (analyticAt_dirichletOperator_apply G a ν p.2.1 y z)
      (by fun_prop))
    (fun y z r hr => (analyticOnNhd_green_apply G hd S.mass S.weights y z r.1
      (alpha_mem_polydisc hr.1)).comp (aa_fst' r))
  have hfixed : ∀ p, StrictData G N δ₀ δ₁ p →
      IsPerturbed G a ν p.2.1 p.1 (pertSource G a p.2.2.1 p.2.2.2)
        (dphi G (greenD G a ν) p.2.1 p.1 (pertSource G a p.2.2.1 p.2.2.2) (toAlpha G (ξs p)))
        (toAlpha G (ξs p)) ∧ Small G (toAlpha G (ξs p)) (c6 d L N) := by
    intro p hp
    obtain ⟨hb, hfx, -⟩ := hξs p hp
    rw [mem_closedBall_zero_iff] at hb
    have hs := small_toAlpha G (ξs p) (fun x => (norm_le_pi_norm (ξs p) x).trans hb)
    exact ⟨perturbed_of_fixed S (hyp p hp).alpha0 hC.ρ_nn hC.poly hs (fixed_of_Smap_fixed hfx), hs⟩
  refine ⟨fun p => (dphi G (greenD G a ν) p.2.1 p.1 (pertSource G a p.2.2.1 p.2.2.2)
    (toAlpha G (ξs p)), toAlpha G (ξs p)), ?_, ?_⟩
  · intro p hp
    have hξy : ∀ y, AnalyticAt ℂ (fun p => ξs p y) p := fun y => analyticAt_pi_iff.1 (hanal p hp) y
    have hc : ∀ y : G.Ω 1, AnalyticAt ℂ (fun p : Edat G N => toAlpha G (ξs p) y) p := by
      intro y
      unfold toAlpha
      exact (hξy y).div_const
    refine AnalyticAt.prod ?_ (analyticAt_pi_iff.2 hc)
    refine analyticAt_pi_iff.2 fun ⟨y, j⟩ => ?_
    exact hdφ y j p hp
  · intro p hp
    obtain ⟨δφ, δα, hP, hs, hsup, huniq⟩ := prop51_exists_unique hd (hyp p hp)
    obtain ⟨hPs, hSs⟩ := hfixed p hp
    obtain ⟨e1, e2⟩ := huniq _ _ hPs hSs
    simp only
    rw [e1, e2]
    refine ⟨hP, hs, hsup, ?_, huniq⟩
    rw [← e2]
    exact hSs

/-- **Proposition 5.1, analyticity jointly in the data and the mass.**  Fix a real reference mass
`ν` with the standing hypotheses of the Green's function bounds.  On the open set of
`(data, m) = ((φ₀, α₀, δΨ, f₁), m)` whose shifted data `(φ₀, α₀ + (m - ν), δΨ, f₁)` satisfy
(P1)–(P4)
with strict inequalities, the solution `(δφ, δα)` of the complex-mass perturbed system (the unique
one with `|δα|₂ ≤ c₆`) is a complex-analytic function of `(data, m)`, with the bounds `K₂ δ₁`. -/
theorem prop51_mass_analytic (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (S : GreenSetting G a ν)
    {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁) (hle0 : δ₀ ≤ deltaStar d L N)
    (hle1 : δ₁ ≤ deltaStar d L N) :
    ∃ sol : Edat G N × ℂ → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
      AnalyticOnNhd ℂ sol {q | StrictData G N δ₀ δ₁ (massShift G N ν q)} ∧
      ∀ q : Edat G N × ℂ, StrictData G N δ₀ δ₁ (massShift G N ν q) →
        IsPerturbedM G a q.2 q.1.2.1 q.1.1 (pertSource G a q.1.2.2.1 q.1.2.2.2) (sol q).1
          (sol q).2 ∧
        Small G (sol q).2 (cK2 d L N * δ₁) ∧ SupBounds G (sol q).1 (cK2 d L N * δ₁) ∧
        Small G (sol q).2 (c6 d L N) ∧
        ∀ (δφ' : G.Ω 1 × Fin N → ℂ) (δα' : G.Ω 1 → ℂ),
          IsPerturbedM G a q.2 q.1.2.1 q.1.1 (pertSource G a q.1.2.2.1 q.1.2.2.2) δφ' δα' →
          Small G δα' (c6 d L N) → δφ' = (sol q).1 ∧ δα' = (sol q).2 := by
  obtain ⟨sol₀, han, hsol⟩ := prop51_analytic_small hd S h0 h1 hle0 hle1
  refine ⟨fun q => sol₀ (massShift G N ν q), fun q hq => ?_, fun q hq => ?_⟩
  · exact (han _ hq).comp (analyticAt_massShift ν q)
  · obtain ⟨hP, hs, hsup, hc6, hu⟩ := hsol _ hq
    refine ⟨(isPerturbedM_iff G a ν _ _ _ _ _ _).2 hP, hs, hsup, hc6, fun δφ' δα' hP' hs' => ?_⟩
    exact hu δφ' δα' ((isPerturbedM_iff G a ν _ _ _ _ _ _).1 hP') hs'

/-- The standing hypotheses of the Green's function bounds at another admissible mass. -/
theorem GreenSetting.withMass {a : ℕ → ℝ} {ν : ℝ} (S : GreenSetting G a ν) {ν' : ℝ}
    (h0 : 0 ≤ ν') (h1 : ν' * ((L : ℝ) ^ k) ^ 2 ≤ 1) : GreenSetting G a ν' where
  hd := S.hd
  hL := S.hL
  mass := h0
  massLe := h1
  weights := S.weights
  sep := S.sep

/-- **Proposition 5.1, analyticity uniformly in the mass.**  One function `sol` of
`(data, m)` is complex-analytic on the union, over all admissible real reference masses
`0 ≤ ν ≤ L^{-2k}`, of the open sets of `prop51_mass_analytic`; at every point of the set for `ν`
it is the solution of the complex-mass system with the bounds `K₂ δ₁`, unique in `|δα|₂ ≤ c₆`.
The contraction constants (`c₆`, `δ_*`, `K₂`) do not depend on the mass in this range. -/
theorem prop51_mass_analytic_uniform (hd : 0 < d) {a : ℕ → ℝ} {ν₀ : ℝ} (S : GreenSetting G a ν₀)
    {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁) (hle0 : δ₀ ≤ deltaStar d L N)
    (hle1 : δ₁ ≤ deltaStar d L N) :
    ∃ sol : Edat G N × ℂ → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
      AnalyticOnNhd ℂ sol {q | ∃ ν : ℝ, 0 ≤ ν ∧ ν * ((L : ℝ) ^ k) ^ 2 ≤ 1 ∧
        StrictData G N δ₀ δ₁ (massShift G N ν q)} ∧
      ∀ (ν : ℝ), 0 ≤ ν → ν * ((L : ℝ) ^ k) ^ 2 ≤ 1 →
        ∀ q : Edat G N × ℂ, StrictData G N δ₀ δ₁ (massShift G N ν q) →
        IsPerturbedM G a q.2 q.1.2.1 q.1.1 (pertSource G a q.1.2.2.1 q.1.2.2.2) (sol q).1
          (sol q).2 ∧
        Small G (sol q).2 (cK2 d L N * δ₁) ∧ SupBounds G (sol q).1 (cK2 d L N * δ₁) ∧
        Small G (sol q).2 (c6 d L N) ∧
        ∀ (δφ' : G.Ω 1 × Fin N → ℂ) (δα' : G.Ω 1 → ℂ),
          IsPerturbedM G a q.2 q.1.2.1 q.1.1 (pertSource G a q.1.2.2.1 q.1.2.2.2) δφ' δα' →
          Small G δα' (c6 d L N) → δφ' = (sol q).1 ∧ δα' = (sol q).2 := by
  classical
  -- the solution in the uniqueness class `|δα|₂ ≤ c₆`, chosen when it exists
  let Sol : Edat G N × ℂ → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) := fun q =>
    if h : ∃ s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
        IsPerturbedM G a q.2 q.1.2.1 q.1.1 (pertSource G a q.1.2.2.1 q.1.2.2.2) s.1 s.2 ∧
        Small G s.2 (c6 d L N)
      then h.choose else 0
  -- on the set of each reference mass, `Sol` is the analytic solution of that mass
  have key : ∀ (ν : ℝ) (h0ν : 0 ≤ ν) (h1ν : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1),
      ∃ sol : Edat G N × ℂ → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
        AnalyticOnNhd ℂ sol {q | StrictData G N δ₀ δ₁ (massShift G N ν q)} ∧
        ∀ q, StrictData G N δ₀ δ₁ (massShift G N ν q) → Sol q = sol q ∧
          (IsPerturbedM G a q.2 q.1.2.1 q.1.1 (pertSource G a q.1.2.2.1 q.1.2.2.2) (sol q).1
            (sol q).2 ∧
          Small G (sol q).2 (cK2 d L N * δ₁) ∧ SupBounds G (sol q).1 (cK2 d L N * δ₁) ∧
          Small G (sol q).2 (c6 d L N) ∧
          ∀ (δφ' : G.Ω 1 × Fin N → ℂ) (δα' : G.Ω 1 → ℂ),
            IsPerturbedM G a q.2 q.1.2.1 q.1.1 (pertSource G a q.1.2.2.1 q.1.2.2.2) δφ' δα' →
            Small G δα' (c6 d L N) → δφ' = (sol q).1 ∧ δα' = (sol q).2) := by
    intro ν h0ν h1ν
    obtain ⟨sol, han, hsol⟩ := prop51_mass_analytic hd (S.withMass h0ν h1ν) h0 h1 hle0 hle1
    refine ⟨sol, han, fun q hq => ⟨?_, hsol q hq⟩⟩
    obtain ⟨hP, -, -, hc6, hu⟩ := hsol q hq
    have hex : ∃ s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
        IsPerturbedM G a q.2 q.1.2.1 q.1.1 (pertSource G a q.1.2.2.1 q.1.2.2.2) s.1 s.2 ∧
        Small G s.2 (c6 d L N) := ⟨sol q, hP, hc6⟩
    have hc := hex.choose_spec
    have hSol : Sol q = hex.choose := by simp only [Sol, hex, ↓reduceDIte]
    obtain ⟨e1, e2⟩ := hu _ _ hc.1 hc.2
    rw [hSol]
    exact Prod.ext e1 e2
  refine ⟨Sol, ?_, fun ν h0ν h1ν q hq => ?_⟩
  · rintro q ⟨ν, h0ν, h1ν, hq⟩
    obtain ⟨sol, han, hsol⟩ := key ν h0ν h1ν
    have hopen : IsOpen {q : Edat G N × ℂ | StrictData G N δ₀ δ₁ (massShift G N ν q)} :=
      (isOpen_strictData δ₀ δ₁).preimage
        (continuous_iff_continuousAt.2 fun q => (analyticAt_massShift ν q).continuousAt)
    refine (han q hq).congr ?_
    filter_upwards [hopen.mem_nhds hq] with q' hq'
    exact ((hsol q' hq').1).symm
  · obtain ⟨sol, -, hsol⟩ := key ν h0ν h1ν
    obtain ⟨e, hprop⟩ := hsol q hq
    rw [e]
    exact hprop

end Exists

end Balaban.Background
