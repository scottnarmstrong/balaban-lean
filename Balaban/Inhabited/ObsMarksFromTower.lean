/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.PhysAmpFacts
public import Balaban.Fluctuation.ObsRayActivity
public import Balaban.Fluctuation.ObsScalarTilt
public import Balaban.Fluctuation.ObsMarksAssembly
public import Balaban.Fluctuation.ObsIntegrandBridge
public import Balaban.Inhabited.MarksNumericsFromTower
public import Balaban.Inhabited.ExpSourceChartFromTower
public import Balaban.Inhabited.SourceDirectTermsFromTower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The observable marks record of the zero-class step at the shared tower

The record `ObsMarks` for the integrand of the consumer `thm31bC_of_input_M0`, at every admissible
scale of one tower, for every source `g` of the `ℓ¹` ball, site `y` and spin `i`.  The only input
that is not proved here is holomorphy of the direct terms along the complex hat ray (`hray`).

* `obsRayAct_differentiableOn_of_ray`, `A_phys_differentiableOn_of_ray`: holomorphy of the ray
  activities and of `A_phys` on the disc `‖z‖ < 3/2`, from the ray clause of the direct terms.
* `exists_obsExtend`: extension of a label family to the observable labels `obsLab`, with
  transport of coefficients, label sum and holomorphy.
* `obsMarks_zeroClass_family_of_ray`: the record.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set
  Metric

/-! ### Holomorphy of the ray activities -/

section Hol

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {Λ F' : Type}
  [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
  {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a : ℝ} {Θ₀ Θg : Λ}
  {SΛ : Set Λ} {XW : Set (F' × F')} {val : F' → F' → ℂ → Λ → ℂ}
  {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}

/-- **Holomorphy of the ray activity** from the ray clause of the terms: if `z ↦ T_Y (z ψ, z ψ)`
is holomorphic on the disc `‖z‖ < 3/2` for every hat variable `ψ` of the disc, then so is each
coefficient of the activity (inside the disc the activity is the term at the scaled pair). -/
theorem obsRayAct_differentiableOn_of_ray
    (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF)
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    (hdom : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (h𝒴 : I.𝒴 = 𝒴)
    (hxwz : ∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ ψ ∈ hatDisk S.U N ρ, (emb (z • ψ), emb (z • ψ)) ∈ XW)
    (hAgF : ∀ (z : ℂ) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (ψ ψ' : S.U × Fin N → ℂ),
      AgF Y (emb ψ) (emb ψ') → AgF Y (emb (z • ψ)) (emb (z • ψ')))
    (hcont : DiagCont emb XW SΛ Rσ I.𝒴 I.T)
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ1 : 1 < Rσ) (hεU : 0 ≤ εU)
    {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc)
    (hray : ∀ Y ∈ I.𝒴, ∀ ψ ∈ hatDisk S.U N ρ,
      DifferentiableOn ℂ (fun z : ℂ => I.T Y (emb (z • ψ)) (emb (z • ψ)) 1 Θ₀)
        (ball (0 : ℂ) (3 / 2)))
    (y : {Y // Y ∈ 𝒴}) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    DifferentiableOn ℂ
      (fun z : ℂ => (obsRayAct S m₀ I hdom h𝒴 hxwz hAgF hcont hN hρ hRσ1 hεU hκ0 hKc z).H y Φ)
      (ball (0 : ℂ) (3 / 2)) := by
  refine (hray y.1 (h𝒴 ▸ y.2) _ (S.hatOf_mem m₀ hρ hp Φ)).congr fun z hz => ?_
  exact obsRayAct_H_of_lt S m₀ I hdom h𝒴 hxwz hAgF hcont hN hρ hRσ1 hεU hκ0 hKc
    (mem_ball_zero_iff.1 hz) y Φ

/-- **Holomorphy of `A_phys`** on the disc `‖z‖ < 3/2` from the ray clauses of the terms at the
two data (the summand `B₀(1)` is constant in `z`). -/
theorem A_phys_differentiableOn_of_ray
    (I₀ : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF)
    (Ig : DirectTerms S m₀ hp emb ρ Rσ εU a Θg SΛ XW val AgΘ AgF)
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} (hdom : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (h𝒴₀ : I₀.𝒴 = 𝒴) (h𝒴g : Ig.𝒴 = 𝒴)
    (hxwz : ∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ ψ ∈ hatDisk S.U N ρ, (emb (z • ψ), emb (z • ψ)) ∈ XW)
    (hAgF : ∀ (z : ℂ) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (ψ ψ' : S.U × Fin N → ℂ),
      AgF Y (emb ψ) (emb ψ') → AgF Y (emb (z • ψ)) (emb (z • ψ')))
    (hcont₀ : DiagCont emb XW SΛ Rσ I₀.𝒴 I₀.T) (hcontg : DiagCont emb XW SΛ Rσ Ig.𝒴 Ig.T)
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ1 : 1 < Rσ) (hεU : 0 ≤ εU)
    {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc)
    (hray₀ : ∀ Y ∈ I₀.𝒴, ∀ ψ ∈ hatDisk S.U N ρ,
      DifferentiableOn ℂ (fun z : ℂ => I₀.T Y (emb (z • ψ)) (emb (z • ψ)) 1 Θ₀)
        (ball (0 : ℂ) (3 / 2)))
    (hrayg : ∀ Y ∈ Ig.𝒴, ∀ ψ ∈ hatDisk S.U N ρ,
      DifferentiableOn ℂ (fun z : ℂ => Ig.T Y (emb (z • ψ)) (emb (z • ψ)) 1 Θg)
        (ball (0 : ℂ) (3 / 2)))
    (y : {Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    DifferentiableOn ℂ
      (fun z : ℂ => (A_phys S m₀ I₀ Ig hdom h𝒴₀ h𝒴g hxwz hAgF hcont₀ hcontg hN hρ hRσ1 hεU
        hκ0 hKc z).H y Φ) (ball (0 : ℂ) (3 / 2)) := by
  rcases y with y | y
  · have h : ∀ z : ℂ, (A_phys S m₀ I₀ Ig hdom h𝒴₀ h𝒴g hxwz hAgF hcont₀ hcontg hN hρ hRσ1 hεU
        hκ0 hKc z).H (Sum.inl y) Φ =
        (obsRayAct S m₀ I₀ hdom h𝒴₀ hxwz hAgF hcont₀ hN hρ hRσ1 hεU hκ0 hKc 1).H y Φ -
        (obsRayAct S m₀ I₀ hdom h𝒴₀ hxwz hAgF hcont₀ hN hρ hRσ1 hεU hκ0 hKc z).H y Φ :=
      fun z => LabelAct.sub_H _ _ y Φ
    simp only [h]
    exact (differentiableOn_const _).sub
      (obsRayAct_differentiableOn_of_ray S m₀ I₀ hdom h𝒴₀ hxwz hAgF hcont₀ hN hρ hRσ1 hεU hκ0
        hKc hray₀ y Φ)
  · exact obsRayAct_differentiableOn_of_ray S m₀ Ig hdom h𝒴g hxwz hAgF hcontg hN hρ hRσ1 hεU hκ0
      hKc hrayg y Φ

end Hol

/-! ### Extension to the observable labels -/

section Extend

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ} {Lb₀ : Type} [Fintype Lb₀]
  {Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
    Set.univ Lb₀}
  {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ → Type}
  [∀ b, MeasurableSpace (Ωb b)] {εb κH κ0 Kc : ℝ}

/-- **Extension of a label family to the observable labels** `obsLab Lab₀ _` (OBSPHYS §2).  The
labels of the domains `𝒴obs` and of the single cubes receive the activity `0`
(`LabelAct.extendZero`), the entropy constant becomes `Kc + K₀ + K₀`, and any constant above it
is allowed.  The coefficients of the old labels, the label sum and holomorphy on a set `𝒰` are
unchanged. -/
theorem exists_obsExtend (hN : L ^ m₀ ∣ N₁) (hκ0 : aEnt d L + 1 ≤ κ0) (hεb : 0 ≤ εb)
    {𝒴obs : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} (hdj : ∀ Y ∈ 𝒴obs, IsDj m₀ (k + 1) Y)
    {Kobs : ℝ} (hK : Kc + K0 d L κ0 + K0 d L κ0 ≤ Kobs)
    (A : ℂ → LabelAct Lab₀ Ωb εb κH κ0 Kc) :
    ∃ A' : ℂ → LabelAct (obsLab Lab₀ hdj) Ωb εb κH κ0 Kobs,
      (∀ t y Φ, (A' t).H (Sum.inl (Sum.inl y)) Φ = (A t).H y Φ) ∧
      (∀ t Φ, ∑ y, (A' t).H y Φ = ∑ y, (A t).H y Φ) ∧
      ∀ 𝒰 : Set ℂ, (∀ y Φ, DifferentiableOn ℂ (fun t => (A t).H y Φ) 𝒰) →
        ∀ y Φ, DifferentiableOn ℂ (fun t => (A' t).H y Φ) 𝒰 := by
  classical
  have h1 := entropy_thick (m₁ := m₁) (j := k + 1) (m₀ := m₀) hN le_rfl 𝒴obs hdj hκ0
  have h2 := cubeLabels_entropy (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
    (m₀ := m₀) (j := k + 1) hN le_rfl hκ0
  let E : ℂ → LabelAct (obsLab Lab₀ hdj) Ωb εb κH κ0 (Kc + K0 d L κ0 + K0 d L κ0) :=
    fun t => (((A t).extendZero (thickLabels 𝒴obs hdj) hεb (K0 d L κ0) h1).extendZero
      (cubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) (m₀ := m₀) (k + 1))
      hεb (K0 d L κ0) h2)
  refine ⟨fun t => (E t).mono hεb le_rfl le_rfl le_rfl hK, fun t y Φ => rfl, fun t Φ => ?_,
    fun 𝒰 hol y Φ => ?_⟩
  · show ∑ y, (E t).H y Φ = _
    exact (LabelAct.extendZero_total _ _ hεb _ h2 Φ).trans
      (LabelAct.extendZero_total _ _ hεb _ h1 Φ)
  · rcases y with (y | y) | y
    · exact hol y Φ
    · exact differentiableOn_const _
    · exact differentiableOn_const _

end Extend

/-! ### Scale arithmetic -/

section Numerics

/-- The activity prefactor `2 ε_U` obeys the tilt's form `ε ≤ C_U w³ / √b`, `w = (log b)^p`, for
`b ≥ e`, from the bound `C_E ℓ^{3p}/√b + C_F ℓ^p/√b`. -/
theorem obs_eps_le_tilt_form {CE CF ε b : ℝ} {p : ℕ} (hCF : 0 ≤ CF) (hb : Real.exp 1 ≤ b)
    (hε : ε ≤ CE * Real.log b ^ (3 * p) / Real.sqrt b + CF * Real.log b ^ p / Real.sqrt b) :
    ε ≤ (CE + CF) * obsW (p : ℝ) b ^ 3 / Real.sqrt b := by
  have hb0 : 0 < b := lt_of_lt_of_le (Real.exp_pos 1) hb
  have hlog : 1 ≤ Real.log b := (Real.le_log_iff_exp_le hb0).2 hb
  have hs0 : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hw : obsW (p : ℝ) b ^ 3 = Real.log b ^ (3 * p) := by
    rw [obsW_cube (p : ℝ) b (le_trans (Real.one_le_exp (by norm_num)) hb)]
    rw [show (3 * (p : ℝ)) = ((3 * p : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [hw]
  have hpow : Real.log b ^ p ≤ Real.log b ^ (3 * p) :=
    pow_le_pow_right₀ hlog (by omega)
  refine hε.trans ?_
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ hs0.le
  nlinarith [mul_le_mul_of_nonneg_left hpow hCF]

/-- `A₁ w` is the cutoff bound `pLog`. -/
theorem obsW_mul_eq_pLog {A₁ b : ℝ} {p : ℕ} :
    A₁ * obsW (p : ℝ) b = Balaban.Inhabited.pLog A₁ p b := by
  unfold Balaban.Inhabited.pLog obsW
  rw [Real.rpow_natCast]

/-- The bound on `B₂`: `C_PE · 8 Q δ (p₁/c_ψ)² (K₀+1) ≤ C₂ w²/b` for `p₁ ≤ A₁ w`,
`c_ψ = κ₁ √b`. -/
theorem obs_B2_le {CPE Q t K A₁ κ1 w b p₁ cψ : ℝ} (hCPE : 0 ≤ CPE) (hQt : 0 ≤ Q * t) (hK : 0 ≤ K)
    (hκ1 : 0 < κ1) (hb : 0 < b) (hp₁0 : 0 ≤ p₁) (hp₁ : p₁ ≤ A₁ * w)
    (hcψ : cψ = κ1 * Real.sqrt b) :
    CPE * (8 * (Q * t) * (p₁ / cψ) ^ 2 * K) ≤
      CPE * (8 * (Q * t) * (A₁ / κ1) ^ 2 * K) * w ^ 2 / b := by
  have hs0 : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hc0 : 0 < cψ := by rw [hcψ]; positivity
  have h1 : p₁ / cψ ≤ A₁ * w / cψ := div_le_div_of_nonneg_right hp₁ hc0.le
  have h2 : (p₁ / cψ) ^ 2 ≤ (A₁ * w / cψ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have h3 : (A₁ * w / cψ) ^ 2 = (A₁ / κ1) ^ 2 * w ^ 2 / b := by
    rw [hcψ, div_pow, mul_pow, mul_pow, Real.sq_sqrt hb.le]
    field_simp
  rw [h3] at h2
  have h4 : 0 ≤ CPE * (8 * (Q * t)) := by positivity
  calc CPE * (8 * (Q * t) * (p₁ / cψ) ^ 2 * K)
      = CPE * (8 * (Q * t)) * (p₁ / cψ) ^ 2 * K := by ring
    _ ≤ CPE * (8 * (Q * t)) * ((A₁ / κ1) ^ 2 * w ^ 2 / b) * K := by gcongr
    _ = _ := by ring

/-- The bound on `B₁`: `(Q t/c_ψ)(C_PE p₁/R_g) n K² E ≤ C₁ w⁴ b^{-1/2-s}`, with
`(1/R_g)(w/√b) = C_R w⁴ b^{-1/2-s}`. -/
theorem obs_B1_le {Q t CPE n K E A₁ κ1 w b p₁ cψ Rg X : ℝ} (hQt : 0 ≤ Q * t) (hCPE : 0 ≤ CPE)
    (hn : 0 ≤ n) (hE : 0 ≤ E) (hκ1 : 0 < κ1) (hb : 0 < b) (hRg : 0 < Rg)
    (hp₁ : p₁ ≤ A₁ * w)
    (hcψ : cψ = κ1 * Real.sqrt b) (hX : 1 / Rg * (w / Real.sqrt b) = X) :
    Q * t / cψ * (CPE * p₁ / Rg) * n * K ^ 2 * E ≤
      (Q * t / κ1 * CPE * A₁ * n * K ^ 2 * E) * X := by
  have hs0 : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hM : 0 ≤ Q * t / κ1 * CPE * n * K ^ 2 * E := by positivity
  have key : Q * t / cψ * (CPE * p₁ / Rg) * n * K ^ 2 * E =
      (Q * t / κ1 * CPE * n * K ^ 2 * E) * (p₁ * (1 / Rg * (1 / Real.sqrt b))) := by
    rw [hcψ]
    field_simp
  have h1 : p₁ * (1 / Rg * (1 / Real.sqrt b)) ≤ A₁ * X := by
    calc p₁ * (1 / Rg * (1 / Real.sqrt b)) ≤ (A₁ * w) * (1 / Rg * (1 / Real.sqrt b)) :=
          mul_le_mul_of_nonneg_right hp₁ (by positivity)
      _ = A₁ * (1 / Rg * (w / Real.sqrt b)) := by ring
      _ = A₁ * X := by rw [hX]
  rw [key]
  calc _ ≤ (Q * t / κ1 * CPE * n * K ^ 2 * E) * (A₁ * X) := mul_le_mul_of_nonneg_left h1 hM
    _ = _ := by ring

end Numerics

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Metric

section TowerG

open Classical in
/-- **The prefactor of `A_phys` at source radius `ρ`.**  As `obsRayEps_bound_fromTower`, on the slice
`ρ/β`: `2 ε_U ≤ C_E ℓ^{3p}/√b + ρ C_F ℓ^p/√b`, with `C_E, C_F` independent of `ρ`. -/
theorem obsRayEps_bound_fromTowerG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ CE CF : ℝ, 0 < CE ∧ 0 < CF ∧ ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 2 ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (ν : ℝ) (β : ℝ), β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
    p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → StepScaleDataG T k hk N₁ ν β p₁ →
    2 * (β * prop33EpsEtaScaled d L N T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (ρ / β)) ≤
      CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
        ρ * CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by
  classical
  have hd3 : 3 ≤ d := T.hd
  have hL3 : 3 ≤ L := T.hL
  have hN2 : 2 ≤ N := T.hN
  have hent := aEnt_nonneg d L
  have hc1 := one_le_c1 d L
  have ht0 := T.t_pos
  have hB0 := T.fam_nonneg
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = cK2' d L N (famConst d L T.BG₂ T.κ) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQdef]; exact cK2'_pos_general hB0
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 3 * c1 d L * (((L : ℕ) : ℝ) ^ (1 + T.m₁)) ^ d *
    ((L : ℝ) ^ d * (((N : ℝ) / 2) * (2 * (1 + Q) ^ 2 +
      ((d : ℝ) + 1 + rho4 d L N T.BG T.κ) * Q ^ 2) * T.t ^ 2)) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by
    rw [hPdef]
    have hρ4 := T.rho_nonneg
    positivity
  have hK0 : 0 < Q * T.t := mul_pos hQ0 ht0
  obtain ⟨β₁, hexpβ₁, hA'⟩ := sourceAmp_scale_general (d := d) (L := L) (N := N) (by omega) T.hL (by omega) (A₁ := A₁) (κ := T.κ) (t := T.t) hA p ht0
  obtain ⟨CE, hCE⟩ : ∃ x : ℝ, x = 4 * (P * (4 * A₁ / lvKappaG d L N T.κ T.t) ^ 3 + 1) := ⟨_, rfl⟩
  obtain ⟨CF, hCF⟩ : ∃ x : ℝ, x = 16 * A₁ * (Q * T.t) / lvKappaG d L N T.κ T.t := ⟨_, rfl⟩
  have hκ1 := lvKappaG_pos (by omega : 0 < d) T.hL (by omega : 1 ≤ N) T.κ ht0
  refine ⟨CE, CF, by rw [hCE]; positivity, by rw [hCF]; positivity, ?_⟩
  intro ρ hρ
  refine ⟨max 2 β₁, le_max_left _ _, ?_⟩
  intro k hk N₁ _ ν β hβ p₁ hp0 hp₁ D
  have hρ4 := T.rho_nonneg
  have hr0 := D.r_pos
  have hβ₁ : β₁ ≤ β := le_trans (le_max_right _ _) hβ
  have hβ2 : 2 ≤ β := le_trans (le_max_left _ _) hβ
  have hβ0 : 0 < β := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := T.hL; omega : 1 ≤ L)
  have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  have hbβ : β ≤ β * (L : ℝ) ^ (k * (d - 2)) := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hamp := (hA' (β * (L : ℝ) ^ (k * (d - 2))) (hβ₁.trans hbβ) p₁ hp0 hp₁).2 P (Q * T.t) ρ hP0 hK0.le hρ.le
  obtain ⟨εU, hεU⟩ : ∃ εU : ℝ, εU = β * prop33EpsEtaScaled d L N T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (ρ / β) := ⟨_, rfl⟩
  have hbU : (T.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) := hatStepKG_betaU T.hN (by omega) k T.m₁ _ hk ν β p₁ T.δ
  obtain ⟨hid, hpot, hterm0, hεle', hεpos⟩ := physAmp_facts (T.step k hk N₁ ν β p₁)
    (by omega) T.hL 1 (compWeight_one_mem T.hL hk) rfl hβ0 rfl hbU hQ0 ht0 hρ4 hr0 hρ hQdef hPdef hεU
  have hεle := hεle' _ hamp
  have hexp : Real.exp 1 ≤ β * (L : ℝ) ^ (k * (d - 2)) := le_trans hexpβ₁ (hβ₁.trans hbβ)
  have hℓ : 1 ≤ Real.log (β * (L : ℝ) ^ (k * (d - 2))) := (Real.le_log_iff_exp_le hb0).2 hexp
  have hε4 := sourceAmp_scale_four_general (A₁ := A₁) (κ₁ := lvKappaG d L N T.κ T.t) (P := P)
    (K := Q * T.t) (q := ρ) (CE := CE) (CF := CF) p hb0 (by linarith) hCE hCF hεle
  rw [← hεU]
  linarith

open Classical in
/-- **`obsMarks_zeroClass_at_of_ray_ksupp` at source radius `ρ`.**  The constants `C₁, C₂` do not
depend on `ρ`; for each `ρ > 0` the threshold `β₀` does (through the amplitude of the tilt, which is
`ε_U ≤ C_E w³/√b + ρ C_F w/√b`).  The slice is `ρ/β`, the sources `g` range over the `ℓ¹` ball of
radius `ρ`, and `hmemg` asks for the points `(rawOf S.D', g/β)` with `∑|g| < ρ`. -/
theorem obsMarks_zeroClass_at_of_ray_ksupp_rhoG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (hm₀ : T.m₀ = 1) :
  ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 2 ≤ β₀ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
  p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
  StepScaleDataG T k hk N₁ ν β p₁ →
  ∀ S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁), S = T.step k hk N₁ ν β p₁ →
  ∀ hpS : 0 < S.p₁,
      ∀ (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
          ℂ → (RawData d L (N₁ * L ^ T.m₁) (k + 1) N ×
            (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
        (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
        (Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
          ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
          (RawData d L (N₁ * L ^ T.m₁) (k + 1) N ×
            (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ),
      (hval : (∀ x w σ Θ, val x w σ Θ =
          (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
          (S.β : ℂ) * (∑ s : CTorus d L N₁ T.m₁ (k + 1) × Fin N, Θ.2 s.1 s.2 *
            dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi S.G' S.a₁ S.ν T.t
                (fun D ψ' => svec (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
                  (flFieldOne S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                    s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))) →
      (hcont : DiagCont (fun ψ : S.U × Fin N → ℂ => (ψ, ψ))
          (physXW S (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2 (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁))
          (physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) 2 𝒴 Tt) →
      (hI : (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
          ∃ I : DirectTerms S T.m₀ hpS (fun ψ => (ψ, ψ)) p₁ 2
              (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1) Θ
              (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
              (physXW S (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2 (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
              (physAgΘ S) (AgFDirPair S),
            I.𝒴 = 𝒴 ∧ I.T = Tt)) →
      (hmem0 : (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) ∈
          physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) →
      (hmemg : (∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < ρ →
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β))) →
      (hrayTt : (∀ Y ∈ 𝒴, ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
          ∀ ψ ∈ hatDisk S.U N p₁,
            DifferentiableOn ℂ (fun z : ℂ => Tt Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1 Θ)
              (ball (0 : ℂ) (3 / 2)))) →
  ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
    g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N ρ →
  ∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N),
        let C := zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁);
    ∃ I : ObsMarks S.nuFl (S.blockSplit 1 hpS)
      (fun r x => S.WoneC C 1 x + S.WtwoC C g r x)
      (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psiAtC z x)) g y i) r)
      (rootCube (m₀ := 1) (blockIndex y)),
      I.Kc = 4 * K0 d L T.κ0 + 2 ∧ I.κ0 = T.κ0 ∧
      I.κH = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.κh = 2 * T.κdec ∧ I.Rσ = obsRg CR s p (β * (L : ℝ) ^ (k * (d - 2))) ∧
      I.B1 ≤ C₁ * obsW p (β * (L : ℝ) ^ (k * (d - 2))) ^ 4 *
        (β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ) - s) ∧
      I.B2 ≤ C₂ * obsW p (β * (L : ℝ) ^ (k * (d - 2))) ^ 2 / (β * (L : ℝ) ^ (k * (d - 2))) ∧
      ∀ (j : I.ι1) (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1)
        1 (k + 1) Set.univ)),
        I.hker j T ≠ 0 → dOmega 1 (k + 1) Set.univ (sitesOf T) ≠ ⊤ := by
  classical
  have hd3 : 3 ≤ d := T.hd
  have hL3 : 3 ≤ L := T.hL
  have hN2 : 2 ≤ N := T.hN
  have hc1 := one_le_c1 d L
  have hK0 : 0 < K0 d L T.κ0 := T.marks_K0_pos
  have hκ0n := T.κ0_nonneg
  obtain ⟨κ1, hκ1def⟩ : ∃ κ1 : ℝ, κ1 = lvKappaG d L N T.κ T.t := ⟨_, rfl⟩
  have hκ1 : 0 < κ1 := hκ1def ▸ lvKappaG_pos (by omega : 0 < d) T.hL (by omega : 1 ≤ N) T.κ T.t_pos
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = cK2' d L N (famConst d L T.BG₂ T.κ) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQdef]; exact cK2'_pos_general T.fam_nonneg
  obtain ⟨Kobs, hKobs⟩ : ∃ Kobs : ℝ, Kobs = 4 * K0 d L T.κ0 + 2 := ⟨_, rfl⟩
  have hKobs0 : 0 < Kobs := by rw [hKobs]; linarith
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ : ℝ, Θ = stepTheta d L Kobs (2 * T.κdec - 1) T.κ0 T.κ' := ⟨_, rfl⟩
  have hΘ : 0 < Θ := by
    rw [hΘdef]; unfold stepTheta; positivity
  obtain ⟨CE, CF, hCE, hCF, hrho⟩ := obsRayEps_bound_fromTowerG_rho T hA p
  obtain ⟨CPEv, hCPEv⟩ : ∃ CPEv : ℝ, CPEv = CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ' := ⟨_, rfl⟩
  have hCPE0 : 0 ≤ CPEv := by rw [hCPEv]; unfold CPE; positivity
  obtain ⟨nn, hnn⟩ : ∃ nn : ℝ, nn = ((N * L ^ (d * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L :=
    ⟨_, rfl⟩
  have hnn0 : 0 ≤ nn := by rw [hnn]; positivity
  obtain ⟨EE, hEE⟩ : ∃ EE : ℝ, EE = Real.exp ((T.κ' - T.κ0) * cG d L) := ⟨_, rfl⟩
  refine ⟨Q * T.t / κ1 * CPEv * A₁ * CR * nn * Kobs ^ 2 * EE,
    CPEv * (8 * (Q * T.t) * (A₁ / κ1) ^ 2 * (K0 d L T.κ0 + 1)), ?_, ?_, ?_⟩
  · have := T.t_pos
    rw [hEE]; positivity
  · have := T.t_pos
    positivity
  intro ρ hρ
  obtain ⟨β₁, hβ₁, hbd⟩ := hrho ρ hρ
  obtain ⟨b₀, hb₀, hb⟩ := obsTilt_of_physAct.{0} (CR := CR) (CU := CE + ρ * CF) (s := s)
    (p := (p : ℝ)) (Θ := Θ) hCR (by positivity) hs0 hs hΘ
  refine ⟨max (max β₁ b₀) 3, ?_, ?_⟩
  · exact le_trans (by norm_num) (le_max_right _ _)
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp hp₁ D S hS _hpS val 𝒴 Tt hval hcont hI hmem0 hmemg hrayTt g hg y i C
  subst hS
  set S := T.step k hk N₁ ν β p₁ with hSdef
  have hβ₁' : β₁ ≤ β := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hβ
  have hβb₀ : b₀ ≤ β := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hβ
  have hβ3 : 3 ≤ β := le_trans (le_max_right _ _) hβ
  have hβ0 : 0 < β := by linarith
  have hβ1 : 1 ≤ β := by linarith
  have hν0 : 0 ≤ ν := hνpos.le
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := T.hL; omega : 1 ≤ L)
  have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  have hbβ : β ≤ β * (L : ℝ) ^ (k * (d - 2)) := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hbe : Real.exp 1 ≤ β * (L : ℝ) ^ (k * (d - 2)) := by
    have := Real.exp_one_lt_three
    linarith
  have hN3 : L ^ 1 ∣ N₁ := by rw [← hm₀]; exact h3N
  obtain ⟨R0⟩ := D.ray
  have hr0 := D.r_pos
  have hcψ0 := D.cψ_pos
  have hC := D.core
  have hD := D.xi
  have hKc : K0 d L T.κ0 ≤ K0 d L T.κ0 + 1 := by linarith
  have hpc1 : p₁ < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) :=
    p₁_lt_of_margin hp le_rfl (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 2) hr0
      D.ray_margin
  have hpc : 2 * p₁ < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
    have : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ := mul_pos hr0 hp
    linarith [D.ray_margin]
  rw [hm₀] at hI
  obtain ⟨I₀, h𝒴₀, hT₀⟩ := hI _ hmem0
  have hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y := fun Y hY => I₀.dom Y (h𝒴₀ ▸ hY)
  have hεpos : 0 < β * prop33EpsEtaScaled d L N T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (ρ / β) := by
    rw [sourceEta_scaled_identity d L N T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) ρ β hβ0.ne']
    have hc1' : (0 : ℝ) ≤ c1 d L := by linarith
    have h3 : (0 : ℝ) ≤ 3 * c1 d L := by linarith
    exact add_pos_of_nonneg_of_pos (by positivity) (div_pos (mul_pos hρ (mul_pos (cK2'_pos_general T.fam_nonneg) T.t_pos)) hr0)
  have hxwz : ∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ ψ ∈ hatDisk S.U N p₁,
      ((z • ψ, z • ψ), (z • ψ, z • ψ)) ∈
        physXW S (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2 (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) :=
    fun z hz ψ hψ => scaled_pair_mem_physXW S hψ hz (by norm_num)
      (by norm_num) hr0.le (D.ray_margin_scaled hp)
  have hAgF : ∀ (z : ℂ) (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
      (ψ ψ' : S.U × Fin N → ℂ),
      AgFDirPair S Y (ψ, ψ) (ψ', ψ') → AgFDirPair S Y (z • ψ, z • ψ) (z • ψ', z • ψ') :=
    fun z Y ψ ψ' h => agFDirPair_smul _ z Y ψ ψ' h
  have hcont₀ := hcont
  rw [← h𝒴₀, ← hT₀] at hcont₀
  have hRσ1 : (1 : ℝ) < 2 := by norm_num
  obtain ⟨Ig, h𝒴g, hTg⟩ := hI _ (hmemg g hg)
  have hcontg := hcont
  rw [← h𝒴g, ← hTg] at hcontg
  have hray₀ : ∀ Y ∈ I₀.𝒴, ∀ ψ ∈ hatDisk S.U N p₁,
      DifferentiableOn ℂ (fun z : ℂ => I₀.T Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1
        (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ))) (ball (0 : ℂ) (3 / 2)) := by
    rw [h𝒴₀, hT₀]
    exact fun Y hY ψ hψ => hrayTt Y hY _ hmem0 ψ hψ
  have hrayg : ∀ Y ∈ Ig.𝒴, ∀ ψ ∈ hatDisk S.U N p₁,
      DifferentiableOn ℂ (fun z : ℂ => Ig.T Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1
        (rawOf S.D', fun y i => g y i / (S.β : ℂ))) (ball (0 : ℂ) (3 / 2)) := by
    rw [h𝒴g, hTg]
    exact fun Y hY ψ hψ => hrayTt Y hY _ (hmemg g hg) ψ hψ
  have hphys : ∃ (εb : ℝ) (Ap : ℂ → LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom))
        (S.blockSplit 1 hp).Ωb εb (2 * T.κdec - 1) T.κ0
        (K0 d L T.κ0 + 1 + (K0 d L T.κ0 + 1))),
      0 < εb ∧ εb ≤ (CE + ρ * CF) * obsW (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) ^ 3 / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
      (∀ y Φ, DifferentiableOn ℂ (fun z => (Ap z).H y Φ) (ball (0 : ℂ) (3 / 2))) ∧
      ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
        S.WoneC C 1 x + S.WtwoC C g r x =
          ∑ y, (Ap (r : ℂ)).H y ((S.blockSplit 1 hp).restr x) := by
    refine ⟨_, fun z => A_phys S 1 I₀ Ig hdom h𝒴₀ h𝒴g hxwz hAgF hcont₀ hcontg hN3 hp hRσ1
      hεpos.le T.κ0_ent hKc z, lt_max_of_lt_left (add_pos hεpos hεpos), ?_, ?_, ?_⟩
    · refine (max_add_self_eq hεpos.le).trans_le ?_
      exact obs_eps_le_tilt_form (CF := ρ * CF) (mul_pos hρ hCF).le hbe (hbd k hk N₁ ν β hβ₁' p₁ hp hp₁ D)
    · exact fun y Φ => A_phys_differentiableOn_of_ray S 1 I₀ Ig hdom h𝒴₀ h𝒴g hxwz hAgF hcont₀
        hcontg hN3 hp hRσ1 hεpos.le T.κ0_ent hKc hray₀ hrayg y Φ
    · intro r hr
      exact (ae_sum_A_phys_eq_WoneC_add_WtwoC S hC R0 D.p_lt hD T.c7_cap (R := 2) le_rfl
        T.bg1_cap T.t_cap T.bg0_cap T.cK2_cap T.cK2'_cap T.large_block T.dom_margin
        T.coer_margin T.δc_small hp hcψ0.le hpc1 D.fl_radius g le_rfl I₀ Ig hval hdom h𝒴₀ h𝒴g
        hxwz hAgF hcont₀ hcontg hN3 hp hRσ1 hεpos.le T.κ0_ent hKc hr).mono fun x hx => hx.symm
  obtain ⟨εb, Ap, hεb0, hεbb, hAhol, hAW⟩ := hphys
  have hcovers := D.covers
  rw [hm₀] at hcovers
  obtain ⟨hV, hF⟩ := hcovers
  obtain ⟨hcov, hX₁, hopt, hΔ, hy⟩ := hF (y, i)
  have hdj := obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) S hC.HBp.hd hcov hopt
  have hK : K0 d L T.κ0 + 1 + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0 ≤ Kobs := by
    rw [hKobs]; linarith
  obtain ⟨A', hA'H, hA'sum, hA'hol⟩ := exists_obsExtend hN3 T.κ0_ent hεb0.le hdj hK Ap
  have hseg : ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → (r : ℂ) ∈ ball (0 : ℂ) (3 / 2) := fun r hr => by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]
    linarith [hr.2]
  obtain ⟨hRg1, hRgΘ, hR0, hholt, hholσ, hzero, hWt⟩ := hb (β * (L : ℝ) ^ (k * (d - 2))) (hβb₀.trans hbβ)
    (S.blockSplit 1 hp) (obsLab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) hdj) A'
    (ball (0 : ℂ) (3 / 2)) (fun r x => S.WoneC C 1 x + S.WtwoC C g r x) hεbb hseg
    (hA'hol _ hAhol) (fun r hr => (hAW r hr).mono fun x hx => by rw [hx, hA'sum])
  have hq : p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) ≤ 1 / 4 := by
    rw [div_le_iff₀ hcψ0]
    have : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ := mul_pos hr0 hp
    linarith [D.ray_margin]
  have hκ0h : T.κ0 ≤ 2 * T.κdec := by
    have := T.marks_κ0_le_κH; linarith
  obtain ⟨I, hIKc, hIκH, -, hIκ0, hIκ', hIεH, hIRσ, hIκh, -, -, -, hIB2, hIB1, hIsupp⟩ :=
    obsMarks_of_tilt_ksupp S hC hk (isLevel_lvLowG hk) ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ0
      T.large_block T.dom_margin T.coer_margin T.δc_small D.fl_radius hcov hX₁ (hatConn_lvTopG T.hL)
      (rowInHat_lvG hk (dgSetting_lvG T.hd T.hL T.m₁_four hN hν0 hν)) hopt hΔ T.κ0_nonneg T.κdec_lower
      (by exact_mod_cast T.κ_lower) T.κ_one (by simpa [hm₀] using T.κ_log) y hy i hp hq
      ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) T.κ0_ent hκ0h S.D' hD
      (fun r x => S.WoneC C 1 x + S.WtwoC C g r x) (T.marks_κG_le) (ball (0 : ℂ) (3 / 2)) hRg1
      isOpen_ball hseg subset_rfl
      (obsScalarTilt (obsRg CR s p (β * (L : ℝ) ^ (k * (d - 2)))) hR0 (ball (0 : ℂ) (3 / 2)) A')
      hholt hholσ hzero hWt (by rw [hKobs]; linarith) (mul_pos (by linarith) hεb0)
      T.marks_hκ' T.marks_κ0_le_κ' T.marks_hκ (by rw [hΘdef] at hRgΘ; exact hRgΘ)
  -- the joint representative and the consumer's integrand
  have hHB := bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hν0 hν
  have hmem := compWeight_one_mem T.hL hk
  have hCs : 0 ≤ covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ :=
    covSupConstC_nonneg (by omega) (by omega) (by linarith [hmem.1]) T.κ
  have hbU : 0 ≤ S.betaU := R0.betaU_pos.le
  have hδp : Real.sqrt (N : ℝ) *
      (S.betaU ^ (-(1 / 2 : ℝ)) *
        (covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ * (2 * p₁))) < T.t := by
    refine lt_of_le_of_lt ?_ D.fl_radius
    rw [S.norm_betaU_rpow (show 0 ≤ β by linarith)]
    have hb := Real.rpow_nonneg hbU (-(1 / 2 : ℝ))
    have hs := Real.sqrt_nonneg (N : ℝ)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpc.le hCs) hb) hs
  obtain ⟨Jr⟩ := S.nonempty_jointRep (pp := 2 * p₁) hC T.large_block T.dom_margin T.coer_margin
    T.δc_small one_pos T.c7_cap (R := 2) (by norm_num) T.bg1_cap (by
      show 0 ≤ β
      linarith) (by linarith) hδp
  refine ⟨ObsMarks.toConsumer Jr hC one_pos hHB T.c7_cap (R := 2) le_rfl T.bg1_cap T.t_cap
    T.bg0_cap T.cK2_cap T.cK2'_cap T.large_block T.dom_margin T.coer_margin T.δc_small
    hcψ0.le D.fl_radius hp D.p_lt hpc hD g y i (S.blockSplit 1 hp) I, ?_⟩
  have hcψ : lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) = κ1 * Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by
    rw [hκ1def]; exact lvCpsiG_eq _ _ _ _ _ _
  have hp₁w : p₁ ≤ A₁ * obsW (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) := by
    rw [obsW_mul_eq_pLog]; exact hp₁
  have hb1 : 1 < β * (L : ℝ) ^ (k * (d - 2)) := by linarith [Real.exp_one_gt_d9, Real.add_one_le_exp 1]
  have hw0 : 0 ≤ obsW (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) := (obsW_pos _ _ hb1).le
  refine ⟨?_, hIκ0, hIκH, hIκ', hIκh, hIRσ, ?_, ?_, hIsupp⟩
  · show I.Kc = _
    rw [hIKc, hKobs]
  · show I.B1 ≤ _
    rw [hIB1]
    have hRgpos : 0 < obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) := by linarith
    have hX := obsRg_inv_amp (CR := CR) (s := s) (p := (p : ℝ)) hCR hb1
    have hmin : Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) ≤ EE := by
      rw [hEE]
      refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ (by unfold cG; positivity))
      linarith [min_le_right (2 * T.κdec) T.κ']
    have hQt : 0 ≤ cK2' d L N (famConst d L T.BG₂ T.κ) * T.t :=
      mul_nonneg (cK2'_pos_general T.fam_nonneg).le T.t_pos.le
    have hmain := obs_B1_le (Q := cK2' d L N (famConst d L T.BG₂ T.κ)) (t := T.t)
      (CPE := CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ') (n := nn) (K := Kobs)
      (E := Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L)) (A₁ := A₁) (κ1 := κ1)
      (w := obsW (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) (b := β * (L : ℝ) ^ (k * (d - 2))) (p₁ := p₁)
      (cψ := lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) (Rg := obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))))
      (X := CR * obsW (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) ^ 4 * (β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ) - s))
      hQt (hCPEv ▸ hCPE0) hnn0 (Real.exp_pos _).le hκ1 hb0 hRgpos hp₁w hcψ hX
    rw [← hnn]
    refine le_trans hmain ?_
    have hQ' : Q = cK2' d L N (famConst d L T.BG₂ T.κ) := hQdef
    have hb' : 0 ≤ (β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ) - s) := Real.rpow_nonneg hb0.le _
    have hc0 : 0 ≤ Q * T.t / κ1 * CPEv * A₁ * nn * Kobs ^ 2 := by
      have := T.t_pos
      positivity
    calc _ = (Q * T.t / κ1 * CPEv * A₁ * nn * Kobs ^ 2 *
            Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L)) *
          (CR * obsW (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) ^ 4 * (β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ) - s)) := by
          rw [hQ', hCPEv]
      _ ≤ (Q * T.t / κ1 * CPEv * A₁ * nn * Kobs ^ 2 * EE) *
          (CR * obsW (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) ^ 4 * (β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ) - s)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin hc0)
            (mul_nonneg (mul_nonneg hCR.le (pow_nonneg hw0 4)) hb')
      _ = _ := by ring
  · show I.B2 ≤ _
    refine hIB2.trans ?_
    have hmain := obs_B2_le (CPE := CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ')
      (Q := cK2' d L N (famConst d L T.BG₂ T.κ)) (t := T.t) (K := K0 d L T.κ0 + 1) (A₁ := A₁)
      (κ1 := κ1) (w := obsW (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) (b := β * (L : ℝ) ^ (k * (d - 2))) (p₁ := p₁)
      (cψ := lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) (hCPEv ▸ hCPE0)
      (mul_nonneg (cK2'_pos_general T.fam_nonneg).le T.t_pos.le) (by linarith) hκ1 hb0 hp.le hp₁w hcψ
    rw [hQdef, hCPEv]
    exact hmain

end TowerG

open Classical in
/-- **The prefactor of `A_phys` at source radius `ρ`.**  As `obsRayEps_bound_fromTower`, on the slice
`ρ/β`: `2 ε_U ≤ C_E ℓ^{3p}/√b + ρ C_F ℓ^p/√b`, with `C_E, C_F` independent of `ρ`. -/
theorem obsRayEps_bound_fromTower_rho {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ CE CF : ℝ, 0 < CE ∧ 0 < CF ∧ ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 2 ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (ν : ℝ) (β : ℝ), β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
    p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
    2 * (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / β)) ≤
      CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        ρ * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) := by
  obtain ⟨CE, CF, hCE, hCF, h⟩ := obsRayEps_bound_fromTowerG_rho T.toG hA p
  refine ⟨CE, CF, hCE, hCF, fun ρ hρ => ?_⟩
  obtain ⟨β₀, hβ₀, h⟩ := h ρ hρ
  refine ⟨β₀, hβ₀, fun k hk N₁ _ ν β hβ p₁ hp0 hp₁ D => ?_⟩
  have e : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have := h k hk N₁ ν β hβ p₁ hp0 (by rw [e]; exact hp₁) (T.scaleDataG_of_fixed D)
  rw [e] at this
  exact this

open Classical in
/-- **`obsMarks_zeroClass_at_of_ray_ksupp` at source radius `ρ`.**  The constants `C₁, C₂` do not
depend on `ρ`; for each `ρ > 0` the threshold `β₀` does (through the amplitude of the tilt, which is
`ε_U ≤ C_E w³/√b + ρ C_F w/√b`).  The slice is `ρ/β`, the sources `g` range over the `ℓ¹` ball of
radius `ρ`, and `hmemg` asks for the points `(rawOf S.D', g/β)` with `∑|g| < ρ`. -/
theorem obsMarks_zeroClass_at_of_ray_ksupp_rho {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
  ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 2 ≤ β₀ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁), S = T.step k hk N₁ ν β p₁ →
  ∀ hpS : 0 < S.p₁,
      ∀ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
        (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
          (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ),
      (hval : (∀ x w σ Θ, val x w σ Θ =
          (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
          (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
            dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi S.G' S.a₁ S.ν T.t
                (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                    s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))) →
      (hcont : DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
          (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
          (physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) 2 𝒴 Tt) →
      (hI : (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
          ∃ I : DirectTerms S 1 hpS (fun ψ => (ψ, ψ)) p₁ 2
              (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1) Θ
              (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
              (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
              (physAgΘ S) (AgFDirPair S),
            I.𝒴 = 𝒴 ∧ I.T = Tt)) →
      (hmem0 : (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
          physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) →
      (hmemg : (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < ρ →
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β))) →
      (hrayTt : (∀ Y ∈ 𝒴, ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
          ∀ ψ ∈ hatDisk S.U 2 p₁,
            DifferentiableOn ℂ (fun z : ℂ => Tt Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1 Θ)
              (ball (0 : ℂ) (3 / 2)))) →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 ρ →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
        let C := zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁);
    ∃ I : ObsMarks S.nuFl (S.blockSplit 1 hpS)
      (fun r x => S.WoneC C 1 x + S.WtwoC C g r x)
      (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psiAtC z x)) g y i) r)
      (rootCube (m₀ := 1) (blockIndex y)),
      I.Kc = 4 * K0 3 3 T.κ0 + 2 ∧ I.κ0 = T.κ0 ∧
      I.κH = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.κh = 2 * T.κdec ∧ I.Rσ = obsRg CR s p (β * 3 ^ k) ∧
      I.B1 ≤ C₁ * obsW p (β * 3 ^ k) ^ 4 *
        (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) ∧
      I.B2 ≤ C₂ * obsW p (β * 3 ^ k) ^ 2 / (β * 3 ^ k) ∧
      ∀ (j : I.ι1) (T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1)
        1 (k + 1) Set.univ)),
        I.hker j T ≠ 0 → dOmega 1 (k + 1) Set.univ (sitesOf T) ≠ ⊤ := by
  obtain ⟨C₁, C₂, hC₁, hC₂, h⟩ := obsMarks_zeroClass_at_of_ray_ksupp_rhoG T.toG hA p hCR hs0 hs rfl
  refine ⟨C₁, C₂, hC₁, hC₂, fun ρ hρ => ?_⟩
  obtain ⟨β₀, hβ₀, h⟩ := h ρ hρ
  refine ⟨β₀, hβ₀, fun k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp hp₁ D => ?_⟩
  have e : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have G := h k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ p₁ hp
    (by rw [e]; exact hp₁) (T.scaleDataG_of_fixed D)
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans e
  subst hϱ' hb'
  intro G
  exact G

open Classical in
/-- **`obsMarks_zeroClass_at_of_ray` with the kernel support**: moreover `I.hker j T` vanishes
unless `dOmega 1 (k+1) univ (sitesOf T) ≠ ⊤`. -/
theorem obsMarks_zeroClass_at_of_ray_ksupp {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
  ∃ β₀ C₁ C₂ : ℝ, 2 ≤ β₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁), S = T.step k hk N₁ ν β p₁ →
  ∀ hpS : 0 < S.p₁,
      ∀ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
        (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
          (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ),
      (hval : (∀ x w σ Θ, val x w σ Θ =
          (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
          (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
            dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi S.G' S.a₁ S.ν T.t
                (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                    s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))) →
      (hcont : DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
          (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
          (physSΛEta S S.a₁ S.ν T.t (1 / S.β)) 2 𝒴 Tt) →
      (hI : (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
          ∃ I : DirectTerms S 1 hpS (fun ψ => (ψ, ψ)) p₁ 2
              (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)) (2 * T.κdec - 1) Θ
              (physSΛEta S S.a₁ S.ν T.t (1 / S.β))
              (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
              (physAgΘ S) (AgFDirPair S),
            I.𝒴 = 𝒴 ∧ I.T = Tt)) →
      (hmem0 : (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
          physSΛEta S S.a₁ S.ν T.t (1 / S.β)) →
      (hmemg : (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β))) →
      (hrayTt : (∀ Y ∈ 𝒴, ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
          ∀ ψ ∈ hatDisk S.U 2 p₁,
            DifferentiableOn ℂ (fun z : ℂ => Tt Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1 Θ)
              (ball (0 : ℂ) (3 / 2)))) →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
        let C := zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁);
    ∃ I : ObsMarks S.nuFl (S.blockSplit 1 hpS)
      (fun r x => S.WoneC C 1 x + S.WtwoC C g r x)
      (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psiAtC z x)) g y i) r)
      (rootCube (m₀ := 1) (blockIndex y)),
      I.Kc = 4 * K0 3 3 T.κ0 + 2 ∧ I.κ0 = T.κ0 ∧
      I.κH = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.κh = 2 * T.κdec ∧ I.Rσ = obsRg CR s p (β * 3 ^ k) ∧
      I.B1 ≤ C₁ * obsW p (β * 3 ^ k) ^ 4 *
        (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) ∧
      I.B2 ≤ C₂ * obsW p (β * 3 ^ k) ^ 2 / (β * 3 ^ k) ∧
      ∀ (j : I.ι1) (T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1)
        1 (k + 1) Set.univ)),
        I.hker j T ≠ 0 → dOmega 1 (k + 1) Set.univ (sitesOf T) ≠ ⊤ := by
  obtain ⟨C₁, C₂, h2, h3, h⟩ := obsMarks_zeroClass_at_of_ray_ksupp_rho T hA p hCR hs0 hs
  obtain ⟨β₀, h1, h⟩ := h 1 one_pos
  exact ⟨β₀, C₁, C₂, h1, h2, h3, h⟩

open Classical in
/-- **The observable marks record of the zero-class step at ONE scale, from the ray premise at that
scale.**  The thresholds `β₀, C₁, C₂` come first, and do not depend on the scale or on the witness.
For every scale with `β ≥ β₀`, `p₁ ≤ pLog A₁ p (β 3^k)` and `StepScaleData`, and every witness
`val, 𝒴, Tt` carrying the clauses of the direct-terms construction at that scale (the value formula
`hval`, diagonal continuity `hcont`, the `DirectTerms` instances `hI`, the memberships `hmem0`,
`hmemg` of the two source points, and the ray clause `hrayTt` on `hatDisk S.U 2 p₁`), every source
`g` of the `ℓ¹` ball, site `y` and spin `i` carry one `ObsMarks` record with the bounds
`B₁ ≤ C₁ w⁴ b^{-1/2-s}`, `B₂ ≤ C₂ w²/b` (`b = β 3^k`, `w = (log b)^p`).  The record's type does
not mention the witness; the witness enters the proof only. -/
theorem obsMarks_zeroClass_at_of_ray {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
  ∃ β₀ C₁ C₂ : ℝ, 2 ≤ β₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁), S = T.step k hk N₁ ν β p₁ →
  ∀ hpS : 0 < S.p₁,
      ∀ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
        (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
          (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ),
      (hval : (∀ x w σ Θ, val x w σ Θ =
          (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
          (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
            dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi S.G' S.a₁ S.ν T.t
                (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                    s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))) →
      (hcont : DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
          (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
          (physSΛEta S S.a₁ S.ν T.t (1 / S.β)) 2 𝒴 Tt) →
      (hI : (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
          ∃ I : DirectTerms S 1 hpS (fun ψ => (ψ, ψ)) p₁ 2
              (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)) (2 * T.κdec - 1) Θ
              (physSΛEta S S.a₁ S.ν T.t (1 / S.β))
              (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
              (physAgΘ S) (AgFDirPair S),
            I.𝒴 = 𝒴 ∧ I.T = Tt)) →
      (hmem0 : (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
          physSΛEta S S.a₁ S.ν T.t (1 / S.β)) →
      (hmemg : (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β))) →
      (hrayTt : (∀ Y ∈ 𝒴, ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
          ∀ ψ ∈ hatDisk S.U 2 p₁,
            DifferentiableOn ℂ (fun z : ℂ => Tt Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1 Θ)
              (ball (0 : ℂ) (3 / 2)))) →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
        let C := zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁);
    ∃ I : ObsMarks S.nuFl (S.blockSplit 1 hpS)
      (fun r x => S.WoneC C 1 x + S.WtwoC C g r x)
      (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psiAtC z x)) g y i) r)
      (rootCube (m₀ := 1) (blockIndex y)),
      I.Kc = 4 * K0 3 3 T.κ0 + 2 ∧ I.κ0 = T.κ0 ∧
      I.κH = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.κh = 2 * T.κdec ∧ I.Rσ = obsRg CR s p (β * 3 ^ k) ∧
      I.B1 ≤ C₁ * obsW p (β * 3 ^ k) ^ 4 *
        (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) ∧
      I.B2 ≤ C₂ * obsW p (β * 3 ^ k) ^ 2 / (β * 3 ^ k) := by

  obtain ⟨β₀, C₁, C₂, h1, h2, h3, h⟩ := obsMarks_zeroClass_at_of_ray_ksupp T hA p hCR hs0 hs
  refine ⟨β₀, C₁, C₂, h1, h2, h3, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp₁p hp₁ D S hS hpS val 𝒴 Tt hval hcont hI hmem0 hmemg
    hrayTt g hg y i C
  obtain ⟨I, e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := h k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp₁p hp₁ D S
    hS hpS val 𝒴 Tt hval hcont hI hmem0 hmemg hrayTt g hg y i
  exact ⟨I, e1, e2, e3, e4, e5, e6, e7, e8⟩

open Classical in
/-- **`obsMarks_zeroClass_family_of_ray_ksupp` at source radius `ρ`** (see
`obsMarks_zeroClass_at_of_ray_ksupp_rho`).  The ray premise `hray` is at the slice `ρ/β`, for
`max 1 ρ ≤ β`, and the conclusion has `ρ ≤ β₀`. -/
theorem obsMarks_zeroClass_family_of_ray_ksupp_rho {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ)
    (hray : ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, max 1 ρ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → StepScaleData T k hk N₁ ν β p₁ →
      ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁), S = T.step k hk N₁ ν β p₁ →
      ∀ hp : 0 < S.p₁,
      ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
        (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
          (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ),
        (∀ x w σ Θ, val x w σ Θ =
          (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
          (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
            dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi S.G' S.a₁ S.ν T.t
                (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                    s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
        DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
          (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
          (physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) 2 𝒴 Tt ∧
        (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
          ∃ I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
              (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1) Θ
              (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
              (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
              (physAgΘ S) (AgFDirPair S),
            I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
        (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
          physSΛEta S S.a₁ S.ν T.t (ρ / S.β) ∧
        (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < ρ →
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) ∧
        (∀ Y ∈ 𝒴, ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
          ∀ ψ ∈ hatDisk S.U 2 p₁,
            DifferentiableOn ℂ (fun z : ℂ => Tt Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1 Θ)
              (ball (0 : ℂ) (3 / 2)))) :
  ∃ β₀ C₁ C₂ : ℝ, 2 ≤ β₀ ∧ ρ ≤ β₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 ρ →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    let S := T.step k hk N₁ ν β p₁;
    let C := zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁);
    ∃ I : ObsMarks S.nuFl (S.blockSplit 1 hp)
      (fun r x => S.WoneC C 1 x + S.WtwoC C g r x)
      (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psiAtC z x)) g y i) r)
      (rootCube (m₀ := 1) (blockIndex y)),
      I.Kc = 4 * K0 3 3 T.κ0 + 2 ∧ I.κ0 = T.κ0 ∧
      I.κH = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.κh = 2 * T.κdec ∧ I.Rσ = obsRg CR s p (β * 3 ^ k) ∧
      I.B1 ≤ C₁ * obsW p (β * 3 ^ k) ^ 4 *
        (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) ∧
      I.B2 ≤ C₂ * obsW p (β * 3 ^ k) ^ 2 / (β * 3 ^ k) ∧
      ∀ (j : I.ι1) (T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1)
        1 (k + 1) Set.univ)),
        I.hker j T ≠ 0 → dOmega 1 (k + 1) Set.univ (sitesOf T) ≠ ⊤ := by
  obtain ⟨C₁, C₂, h2, h3, hat⟩ := obsMarks_zeroClass_at_of_ray_ksupp_rho T hA p hCR hs0 hs
  obtain ⟨β₀, hβ₀, hat⟩ := hat ρ hρ
  refine ⟨max β₀ ρ, C₁, C₂, le_trans hβ₀ (le_max_left _ _), le_max_right _ _, h2, h3, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp hp₁ D g hg y i S C
  have hβ0 : β₀ ≤ β := le_trans (le_max_left _ _) hβ
  have hβρ : ρ ≤ β := le_trans (le_max_right _ _) hβ
  obtain ⟨val, 𝒴, Tt, hval, hcont, hI, hmem0, hmemg, hrayTt⟩ :=
    hray k hk N₁ h3N hN ν hνpos hν β (max_le (by linarith) hβρ) p₁ hp D S rfl hp
  exact hat k hk N₁ h3N hN ν hνpos hν β hβ0 p₁ hp hp₁ D S rfl hp val 𝒴 Tt hval hcont hI hmem0
    hmemg hrayTt g hg y i

open Classical in
/-- **`obsMarks_zeroClass_family_of_ray` with the kernel support** (see
`obsMarks_zeroClass_at_of_ray_ksupp`). -/
theorem obsMarks_zeroClass_family_of_ray_ksupp {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2)
    (hray : ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, 1 ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → StepScaleData T k hk N₁ ν β p₁ →
      ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁), S = T.step k hk N₁ ν β p₁ →
      ∀ hp : 0 < S.p₁,
      ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
        (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
          (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ),
        (∀ x w σ Θ, val x w σ Θ =
          (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
          (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
            dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi S.G' S.a₁ S.ν T.t
                (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                    s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
        DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
          (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
          (physSΛEta S S.a₁ S.ν T.t (1 / S.β)) 2 𝒴 Tt ∧
        (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
          ∃ I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
              (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)) (2 * T.κdec - 1) Θ
              (physSΛEta S S.a₁ S.ν T.t (1 / S.β))
              (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
              (physAgΘ S) (AgFDirPair S),
            I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
        (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
          physSΛEta S S.a₁ S.ν T.t (1 / S.β) ∧
        (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β)) ∧
        (∀ Y ∈ 𝒴, ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
          ∀ ψ ∈ hatDisk S.U 2 p₁,
            DifferentiableOn ℂ (fun z : ℂ => Tt Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1 Θ)
              (ball (0 : ℂ) (3 / 2)))) :
  ∃ β₀ C₁ C₂ : ℝ, 2 ≤ β₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    let S := T.step k hk N₁ ν β p₁;
    let C := zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁);
    ∃ I : ObsMarks S.nuFl (S.blockSplit 1 hp)
      (fun r x => S.WoneC C 1 x + S.WtwoC C g r x)
      (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psiAtC z x)) g y i) r)
      (rootCube (m₀ := 1) (blockIndex y)),
      I.Kc = 4 * K0 3 3 T.κ0 + 2 ∧ I.κ0 = T.κ0 ∧
      I.κH = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.κh = 2 * T.κdec ∧ I.Rσ = obsRg CR s p (β * 3 ^ k) ∧
      I.B1 ≤ C₁ * obsW p (β * 3 ^ k) ^ 4 *
        (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) ∧
      I.B2 ≤ C₂ * obsW p (β * 3 ^ k) ^ 2 / (β * 3 ^ k) ∧
      ∀ (j : I.ι1) (T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1)
        1 (k + 1) Set.univ)),
        I.hker j T ≠ 0 → dOmega 1 (k + 1) Set.univ (sitesOf T) ≠ ⊤ := by
  obtain ⟨β₀, C₁, C₂, h1, -, h2, h3, h⟩ := obsMarks_zeroClass_family_of_ray_ksupp_rho T hA p hCR hs0
    hs 1 one_pos (fun k hk N₁ _ h3N hN ν hνpos hν β hβ => hray k hk N₁ h3N hN ν hνpos hν β
      (le_trans (le_max_left _ _) hβ))
  exact ⟨β₀, C₁, C₂, h1, h2, h3, h⟩

open Classical in
/-- **The observable marks record of the zero-class step at the shared tower, conditional on the
ray clause** (OBSPHYS §4).  For the tower `T`, `A₁, p, C_R, s`, there are `β₀, C₁, C₂` such that for
every admissible scale with `StepScaleData`, every source `g` of the `ℓ¹` ball, every site `y` and
spin `i`, there is one `ObsMarks` record with the exponent `W₁^C(1) + W₂^C(r; g)` and the integrand
of the consumer `thm31bC_of_input_M0` (the derivative in `r` of `McompAtC` at
`dataUC (psiAtC r x)`), the constants `κ₀, κ_H = 2κ_dec - 1, κ′, K_c = 4K₀ + 2, κ_h = 2κ_dec`,
`R_σ = b^s/(C_R (log b)^{3p})` and the bounds `B₁ ≤ C₁ w⁴ b^{-1/2-s}`, `B₂ ≤ C₂ w²/b`
(`b = β 3^k`, `w = (log b)^p`).

The single extra hypothesis `hray` is the output of the direct-terms construction
`sourceDirectTerms_scale_fromTower` (slice `q = 1`: the value formula `hval`, diagonal continuity,
the `DirectTerms` instances at every point of the slice, the two source points) for some
`val, 𝒴, Tt`, together with the **ray clause** for the same `Tt`: for every domain `Y ∈ 𝒴`, every
point `Θ` of the slice and every hat variable `ψ̂` of the disc of radius `p₁`,
`z ↦ Tt Y (z ψ̂, z ψ̂) (z ψ̂, z ψ̂) 1 Θ` is holomorphic on `‖z‖ < 3/2`. -/
theorem obsMarks_zeroClass_family_of_ray {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2)
    (hray : ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, 1 ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → StepScaleData T k hk N₁ ν β p₁ →
      ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁), S = T.step k hk N₁ ν β p₁ →
      ∀ hp : 0 < S.p₁,
      ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
        (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
          (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ),
        (∀ x w σ Θ, val x w σ Θ =
          (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
          (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
            dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi S.G' S.a₁ S.ν T.t
                (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                    s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
        DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
          (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
          (physSΛEta S S.a₁ S.ν T.t (1 / S.β)) 2 𝒴 Tt ∧
        (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
          ∃ I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
              (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)) (2 * T.κdec - 1) Θ
              (physSΛEta S S.a₁ S.ν T.t (1 / S.β))
              (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
              (physAgΘ S) (AgFDirPair S),
            I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
        (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
          physSΛEta S S.a₁ S.ν T.t (1 / S.β) ∧
        (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β)) ∧
        (∀ Y ∈ 𝒴, ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
          ∀ ψ ∈ hatDisk S.U 2 p₁,
            DifferentiableOn ℂ (fun z : ℂ => Tt Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1 Θ)
              (ball (0 : ℂ) (3 / 2)))) :
  ∃ β₀ C₁ C₂ : ℝ, 2 ≤ β₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    let S := T.step k hk N₁ ν β p₁;
    let C := zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁);
    ∃ I : ObsMarks S.nuFl (S.blockSplit 1 hp)
      (fun r x => S.WoneC C 1 x + S.WtwoC C g r x)
      (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psiAtC z x)) g y i) r)
      (rootCube (m₀ := 1) (blockIndex y)),
      I.Kc = 4 * K0 3 3 T.κ0 + 2 ∧ I.κ0 = T.κ0 ∧
      I.κH = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.κh = 2 * T.κdec ∧ I.Rσ = obsRg CR s p (β * 3 ^ k) ∧
      I.B1 ≤ C₁ * obsW p (β * 3 ^ k) ^ 4 *
        (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) ∧
      I.B2 ≤ C₂ * obsW p (β * 3 ^ k) ^ 2 / (β * 3 ^ k) := by

  obtain ⟨β₀, C₁, C₂, h1, h2, h3, h⟩ := obsMarks_zeroClass_family_of_ray_ksupp T hA p hCR hs0 hs hray
  refine ⟨β₀, C₁, C₂, h1, h2, h3, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp₁p hp₁ D g hg y i S C
  obtain ⟨I, e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := h k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp₁p hp₁ D g
    hg y i
  exact ⟨I, e1, e2, e3, e4, e5, e6, e7, e8⟩

end Balaban.Inhabited
