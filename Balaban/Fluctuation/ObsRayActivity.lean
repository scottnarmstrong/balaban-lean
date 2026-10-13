/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.PhysAmpFacts
public import Balaban.Inhabited.SourceActivityFromTower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The activities of the observable ray (`notes/phase1/OBSRAY.md` §3–§4)

For the direct terms `Tt` of the zero class at a chart point `Θ_e`, the complex-ray activity is

`B_e(z)_Y(Φ) = Tt Y (z ψ̂, z ψ̂) (z ψ̂, z ψ̂) 1 Θ_e`  for `‖z‖ < 3/2`, and `0` otherwise,

on the thick labels of the domain family, `ψ̂` the clamped hat field of the block configuration `Φ`.

* `scaled_pair_mem_physXW`: the scaled pair lies in the admissible set of the physical expansion
  (radius margin `(R_σ R₁ + r)(3/2)ρ < c_ψ`).
* `DirectTerms.norm_ray_le`: the bound `ε_U e^{-a 𝗱(Y)}` of the landed real activity.
* `obsRayAct`: the `LabelAct` family (measurable, local, bounded, zero outside the disc).
* `A_phys`: `(B₀(1) - B₀(z)) ⊕ B_g(z)`, with constants `max (ε_U + ε_U) ε_U` and `K_c + K_c`.
* `sum_obsRayAct`: the label sum of `B_e(z)` is the expanded function at the scaled pair.
* `dirTermSrc_smul_one`: the source terms at a scaled pair with `σ = 1` are the source terms at the
  unscaled pair with `σ = z`.

Holomorphy of `z ↦ B_e(z)_Y(Φ)` is not asserted here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set
  Metric

section Scaling

variable {Λ : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The directional derivative is homogeneous in the direction. -/
theorem lineD_smul_vec (f : E → ℂ) (v x : E) (s : ℂ) : lineD (s • v) f x = s * lineD v f x := by
  unfold lineD
  have h : (fun t : ℂ => f (x + t • s • v)) = fun t : ℂ => (fun u : ℂ => f (x + u • v)) (s * t) := by
    funext t
    simp [smul_smul, mul_comm]
  rw [h]
  have h2 := deriv_comp_mul_left s (fun u : ℂ => f (x + u • v)) (0 : ℂ)
  simp only [mul_zero, smul_eq_mul] at h2
  exact h2

/-- **Scaled pair, `σ = 1`.**  The source terms at the pair `(s x, s w)` and `σ = 1` are those at
`(x, w)` and `σ = s`. -/
theorem dirTermSrc_smul_one (f : Λ × E → ℂ) (ω : ℂ → ℂ) (x w : E) (s : ℂ) (Θ : Λ) :
    dirTermSrc f ω (s • x) (s • w) 1 Θ = dirTermSrc f ω x w s Θ := by
  unfold dirTermSrc
  rw [one_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [lineD_smul_vec, smul_smul, one_mul]
  ring_nf

end Scaling

section Ray

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The scaled pair is admissible** (OBSRAY §3).  For a hat variable in the disc of radius `ρ`
and `‖z‖ < 3/2`, the diagonal pair `(z ψ̂, z ψ̂)` lies in `physXW`, provided the radius margin
`(R_σ R₁ + r)(3/2) ρ < c_ψ` holds. -/
theorem scaled_pair_mem_physXW (S : StepSetting d L N₁ m₁ k N ϱ) {ψ : S.U × Fin N → ℂ}
    {ρ Rσ R₁ r cψ : ℝ} (hψ : ψ ∈ hatDisk S.U N ρ) {z : ℂ} (hz : ‖z‖ < 3 / 2) (hRσ : 0 ≤ Rσ)
    (hR₁ : 0 ≤ R₁) (hr : 0 ≤ r) (hc : (Rσ * R₁ + r) * (3 / 2 * ρ) < cψ) :
    (((z • ψ, z • ψ), (z • ψ, z • ψ)) :
        ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) × ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ))) ∈
      physXW S cψ R₁ Rσ r := by
  have hd : z • ψ ∈ hatDisk S.U N (3 / 2 * ρ) := fun p => by
    show ‖z * ψ p‖ ≤ 3 / 2 * ρ
    rw [norm_mul]
    exact mul_le_mul hz.le (hψ p) (norm_nonneg _) (by norm_num)
  exact ⟨hatRaysO_pair S hd hRσ hR₁ hr hc, hatRaysO_pair S hd hRσ hR₁ hr hc⟩

variable (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {Λ F' : Type}
  [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]

section Bound

variable {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a : ℝ} {Θ₀ : Λ}
  {SΛ : Set Λ} {XW : Set (F' × F')} {val : F' → F' → ℂ → Λ → ℂ}
  {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}

/-- **The bound along the complex ray** (OBSRAY §3): at `σ = 1` and an admissible scaled pair, the
term of `Y` obeys the bound `ε_U e^{-a 𝗱(Y)}` of the landed real activity.  No maximum principle
is used: the pair is admissible and `1 < R_σ`. -/
theorem DirectTerms.norm_ray_le (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF)
    (hRσ1 : 1 < Rσ) {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : Y ∈ I.𝒴) {ψ : F'}
    (hψ : (ψ, ψ) ∈ XW) :
    ‖I.T Y ψ ψ 1 Θ₀‖ ≤ εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y) := by
  have h1 := I.loc.bound Y hY (ψ, ψ) hψ 1 (by simpa using hRσ1) Θ₀ I.mem
  have h2 : ‖(1 : ℂ)‖ * I.b Y ≤ εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y) := by
    rw [norm_one, one_mul]
    exact I.bd Y hY
  exact h1.trans h2

end Bound

section Act

variable {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a : ℝ} {Θ₀ : Λ}
  {SΛ : Set Λ} {XW : Set (F' × F')} {val : F' → F' → ℂ → Λ → ℂ}
  {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
  (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF)

/-- Measurability of the term along the scaled hat variable (the continuity `DiagCont` of the
diagonal terms, composed with the measurable map `Φ ↦ z ψ̂(Φ)`). -/
theorem DirectTerms.measurable_ray
    (hxwz : ∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ ψ ∈ hatDisk S.U N ρ, (emb (z • ψ), emb (z • ψ)) ∈ XW)
    (hcont : DiagCont emb XW SΛ Rσ I.𝒴 I.T) (hρ : 0 < ρ) (hRσ1 : 1 < Rσ)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : Y ∈ I.𝒴) {z : ℂ} (hz : ‖z‖ < 3 / 2) :
    Measurable (fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
      I.T Y (emb (z • S.hatOf m₀ ρ hp Φ)) (emb (z • S.hatOf m₀ ρ hp Φ)) 1 Θ₀) := by
  have hc := hcont Y hY 1 (by simpa using hRσ1) Θ₀ I.mem
  have hf : Continuous (fun ψ : hatDisk S.U N ρ => z • ψ.1) :=
    Continuous.const_smul continuous_subtype_val z
  have hcc : Continuous (fun ψ : hatDisk S.U N ρ => I.T Y (emb (z • ψ.1)) (emb (z • ψ.1)) 1 Θ₀) :=
    hc.comp_continuous hf (fun ψ => hxwz z hz ψ.1 ψ.2)
  exact hcc.measurable.comp (S.measurable_hatOf m₀ ρ hρ hp)

/-- Locality of the term along the scaled hat variable: it depends only on the blocks inside `Y`
(complex multiplication preserves the agreement relation of the terms). -/
theorem DirectTerms.dep_ray
    (hxwz : ∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ ψ ∈ hatDisk S.U N ρ, (emb (z • ψ), emb (z • ψ)) ∈ XW)
    (hAgF : ∀ (z : ℂ) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (ψ ψ' : S.U × Fin N → ℂ),
      AgF Y (emb ψ) (emb ψ') → AgF Y (emb (z • ψ)) (emb (z • ψ')))
    (hρ : 0 < ρ) (hRσ1 : 1 < Rσ)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : Y ∈ I.𝒴) {z : ℂ} (hz : ‖z‖ < 3 / 2) :
    DepOn (blocksOf m₀ (k + 1) Set.univ Y) (fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
      I.T Y (emb (z • S.hatOf m₀ ρ hp Φ)) (emb (z • S.hatOf m₀ ρ hp Φ)) 1 Θ₀) := by
  intro Φ Φ' h
  have hAg := hAgF z Y _ _ (I.ag Y hY Φ Φ' h)
  exact I.loc.loc Y hY (emb (z • S.hatOf m₀ ρ hp Φ), emb (z • S.hatOf m₀ ρ hp Φ))
    (hxwz z hz _ (S.hatOf_mem m₀ hρ hp Φ)) (emb (z • S.hatOf m₀ ρ hp Φ'),
      emb (z • S.hatOf m₀ ρ hp Φ')) (hxwz z hz _ (S.hatOf_mem m₀ hρ hp Φ')) 1
    (by simpa using hRσ1) Θ₀ I.mem Θ₀ I.mem (I.agΘ Y) hAg hAg

open Classical in
/-- **The activity along the complex observable ray** (OBSRAY §3).  On the thick labels of the
domain family of `I`, the activity of `Y` is `T_Y (z ψ̂, z ψ̂) (z ψ̂, z ψ̂) 1 Θ₀` for `‖z‖ < 3/2`
and `0` otherwise; prefactor `ε_U`, rate `a`, entropy bound `K_c ≥ K₀`, as the landed real
activity but with the prefactor `ε_U` instead of `R_σ ε_U`. -/
noncomputable def obsRayAct {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    (hdom : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (h𝒴 : I.𝒴 = 𝒴)
    (hxwz : ∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ ψ ∈ hatDisk S.U N ρ, (emb (z • ψ), emb (z • ψ)) ∈ XW)
    (hAgF : ∀ (z : ℂ) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (ψ ψ' : S.U × Fin N → ℂ),
      AgF Y (emb ψ) (emb ψ') → AgF Y (emb (z • ψ)) (emb (z • ψ')))
    (hcont : DiagCont emb XW SΛ Rσ I.𝒴 I.T)
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ1 : 1 < Rσ) (hεU : 0 ≤ εU)
    {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc) (z : ℂ) :
    LabelAct (thickLabels 𝒴 hdom) (S.blockSplit m₀ hp).Ωb εU a κ0 Kc where
  H Y Φ := if ‖z‖ < 3 / 2 then
    I.T Y.1 (emb (z • S.hatOf m₀ ρ hp Φ)) (emb (z • S.hatOf m₀ ρ hp Φ)) 1 Θ₀ else 0
  meas Y := by
    by_cases hz : ‖z‖ < 3 / 2
    · simp only [hz, ite_true]
      exact I.measurable_ray S m₀ hxwz hcont hρ hRσ1 (h𝒴 ▸ Y.2) hz
    · simp only [hz, ite_false]
      exact measurable_const
  dep Y := by
    by_cases hz : ‖z‖ < 3 / 2
    · simp only [hz, ite_true]
      exact I.dep_ray S m₀ hxwz hAgF hρ hRσ1 (h𝒴 ▸ Y.2) hz
    · simp only [hz, ite_false]
      intro _ _ _
      rfl
  bound Y Φ := by
    by_cases hz : ‖z‖ < 3 / 2
    · simp only [hz, ite_true]
      exact I.norm_ray_le S m₀ hRσ1 (h𝒴 ▸ Y.2) (hxwz z hz _ (S.hatOf_mem m₀ hρ hp Φ))
    · simp only [hz, ite_false, norm_zero]
      positivity
  entropy b := (entropy_thick hN le_rfl 𝒴 hdom hκ0 b).trans hKc

/-- **The label sum of the ray activity is the expanded function at the scaled pair.** -/
theorem sum_obsRayAct {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    (hdom : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (h𝒴 : I.𝒴 = 𝒴)
    (hxwz : ∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ ψ ∈ hatDisk S.U N ρ, (emb (z • ψ), emb (z • ψ)) ∈ XW)
    (hAgF : ∀ (z : ℂ) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (ψ ψ' : S.U × Fin N → ℂ),
      AgF Y (emb ψ) (emb ψ') → AgF Y (emb (z • ψ)) (emb (z • ψ')))
    (hcont : DiagCont emb XW SΛ Rσ I.𝒴 I.T)
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ1 : 1 < Rσ) (hεU : 0 ≤ εU)
    {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc) {z : ℂ} (hz : ‖z‖ < 3 / 2)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    ∑ y, (obsRayAct S m₀ I hdom h𝒴 hxwz hAgF hcont hN hρ hRσ1 hεU hκ0 hKc z).H y Φ =
      val (emb (z • S.hatOf m₀ ρ hp Φ)) (emb (z • S.hatOf m₀ ρ hp Φ)) 1 Θ₀ := by
  classical
  have h : ∑ y, (obsRayAct S m₀ I hdom h𝒴 hxwz hAgF hcont hN hρ hRσ1 hεU hκ0 hKc z).H y Φ =
      ∑ Y : {Y // Y ∈ 𝒴}, I.T Y.1 (emb (z • S.hatOf m₀ ρ hp Φ))
        (emb (z • S.hatOf m₀ ρ hp Φ)) 1 Θ₀ := by
    refine Finset.sum_congr rfl fun Y _ => ?_
    simp [obsRayAct, hz]
  rw [h, Finset.sum_coe_sort 𝒴 (fun Y => I.T Y (emb (z • S.hatOf m₀ ρ hp Φ))
    (emb (z • S.hatOf m₀ ρ hp Φ)) 1 Θ₀), ← h𝒴]
  exact (I.loc.sum (emb (z • S.hatOf m₀ ρ hp Φ), emb (z • S.hatOf m₀ ρ hp Φ))
    (hxwz z hz _ (S.hatOf_mem m₀ hρ hp Φ)) 1 (by simpa using hRσ1) Θ₀ I.mem).symm

/-- Outside the disc `‖z‖ < 3/2` the ray activity vanishes. -/
theorem obsRayAct_H_of_not_lt {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    (hdom : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (h𝒴 : I.𝒴 = 𝒴)
    (hxwz : ∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ ψ ∈ hatDisk S.U N ρ, (emb (z • ψ), emb (z • ψ)) ∈ XW)
    (hAgF : ∀ (z : ℂ) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (ψ ψ' : S.U × Fin N → ℂ),
      AgF Y (emb ψ) (emb ψ') → AgF Y (emb (z • ψ)) (emb (z • ψ')))
    (hcont : DiagCont emb XW SΛ Rσ I.𝒴 I.T)
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ1 : 1 < Rσ) (hεU : 0 ≤ εU)
    {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc) {z : ℂ} (hz : 3 / 2 ≤ ‖z‖)
    (y : {Y // Y ∈ 𝒴}) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    (obsRayAct S m₀ I hdom h𝒴 hxwz hAgF hcont hN hρ hRσ1 hεU hκ0 hKc z).H y Φ = 0 := by
  classical
  simp [obsRayAct, not_lt.2 hz]

/-- Inside the disc the ray activity is the term at the scaled pair. -/
theorem obsRayAct_H_of_lt {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    (hdom : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (h𝒴 : I.𝒴 = 𝒴)
    (hxwz : ∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ ψ ∈ hatDisk S.U N ρ, (emb (z • ψ), emb (z • ψ)) ∈ XW)
    (hAgF : ∀ (z : ℂ) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (ψ ψ' : S.U × Fin N → ℂ),
      AgF Y (emb ψ) (emb ψ') → AgF Y (emb (z • ψ)) (emb (z • ψ')))
    (hcont : DiagCont emb XW SΛ Rσ I.𝒴 I.T)
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ1 : 1 < Rσ) (hεU : 0 ≤ εU)
    {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc) {z : ℂ} (hz : ‖z‖ < 3 / 2)
    (y : {Y // Y ∈ 𝒴}) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    (obsRayAct S m₀ I hdom h𝒴 hxwz hAgF hcont hN hρ hRσ1 hεU hκ0 hKc z).H y Φ =
      I.T y.1 (emb (z • S.hatOf m₀ ρ hp Φ)) (emb (z • S.hatOf m₀ ρ hp Φ)) 1 Θ₀ := by
  classical
  simp [obsRayAct, hz]

end Act

section Phys

variable {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a : ℝ} {Θ₀ Θg : Λ}
  {SΛ : Set Λ} {XW : Set (F' × F')} {val : F' → F' → ℂ → Λ → ℂ}
  {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
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

/-- **The physical ray activity** (OBSRAY §3): `A_phys(z) = (B₀(1) - B₀(z)) ⊕ B_g(z)` on the labels
`(thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)`, with prefactor `max (ε_U + ε_U) ε_U` (`= 2 ε_U`, see
`max_add_self_eq`), rate `a`, entropy constant `K_c + K_c`.  `I₀` is the instance at the source
datum `(rawOf D', 0)` and `Ig` the one at `(rawOf D', g/β)`. -/
noncomputable def A_phys (z : ℂ) :
    LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit m₀ hp).Ωb
      (max (εU + εU) εU) a κ0 (Kc + Kc) :=
  ((obsRayAct S m₀ I₀ hdom h𝒴₀ hxwz hAgF hcont₀ hN hρ hRσ1 hεU hκ0 hKc 1).sub
      (obsRayAct S m₀ I₀ hdom h𝒴₀ hxwz hAgF hcont₀ hN hρ hRσ1 hεU hκ0 hKc z)).sum
    (obsRayAct S m₀ Ig hdom h𝒴g hxwz hAgF hcontg hN hρ hRσ1 hεU hκ0 hKc z)

/-- The prefactor `max (ε_U + ε_U) ε_U` is `2 ε_U` for `ε_U ≥ 0`. -/
theorem max_add_self_eq {ε : ℝ} (h : 0 ≤ ε) : max (ε + ε) ε = 2 * ε := by
  rw [max_eq_left (by linarith)]
  ring

/-- **The label sum of `A_phys`** at a disc point `‖z‖ < 3/2`: the expanded function at the unit
hat field at `Θ₀`, minus the one at `z ψ̂`, plus the one at `z ψ̂` at `Θg`. -/
theorem sum_A_phys {z : ℂ} (hz : ‖z‖ < 3 / 2) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    ∑ y, (A_phys S m₀ I₀ Ig hdom h𝒴₀ h𝒴g hxwz hAgF hcont₀ hcontg hN hρ hRσ1 hεU hκ0 hKc z).H y Φ =
      (val (emb ((1 : ℂ) • S.hatOf m₀ ρ hp Φ)) (emb ((1 : ℂ) • S.hatOf m₀ ρ hp Φ)) 1 Θ₀ -
        val (emb (z • S.hatOf m₀ ρ hp Φ)) (emb (z • S.hatOf m₀ ρ hp Φ)) 1 Θ₀) +
      val (emb (z • S.hatOf m₀ ρ hp Φ)) (emb (z • S.hatOf m₀ ρ hp Φ)) 1 Θg := by
  have h1 : ‖(1 : ℂ)‖ < 3 / 2 := by rw [norm_one]; norm_num
  unfold A_phys
  rw [LabelAct.sum_total]
  have e : ∑ y, ((obsRayAct S m₀ I₀ hdom h𝒴₀ hxwz hAgF hcont₀ hN hρ hRσ1 hεU hκ0 hKc 1).sub
      (obsRayAct S m₀ I₀ hdom h𝒴₀ hxwz hAgF hcont₀ hN hρ hRσ1 hεU hκ0 hKc z)).H y Φ =
      ∑ y, (obsRayAct S m₀ I₀ hdom h𝒴₀ hxwz hAgF hcont₀ hN hρ hRσ1 hεU hκ0 hKc 1).H y Φ -
      ∑ y, (obsRayAct S m₀ I₀ hdom h𝒴₀ hxwz hAgF hcont₀ hN hρ hRσ1 hεU hκ0 hKc z).H y Φ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => LabelAct.sub_H _ _ y Φ
  rw [e, sum_obsRayAct S m₀ I₀ hdom h𝒴₀ hxwz hAgF hcont₀ hN hρ hRσ1 hεU hκ0 hKc h1,
    sum_obsRayAct S m₀ I₀ hdom h𝒴₀ hxwz hAgF hcont₀ hN hρ hRσ1 hεU hκ0 hKc hz,
    sum_obsRayAct S m₀ Ig hdom h𝒴g hxwz hAgF hcontg hN hρ hRσ1 hεU hκ0 hKc hz]

end Phys

end Ray

section Identity

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The W identity for the physical ray activity** (OBSRAY §4, leaf 4).  Let `I₀`, `Ig` be
direct-label instances of one expanded function `val` at the source data `(rawOf D', 0)` and
`(rawOf D', g/β)`, with the value formula of `sourceDirectTerms_scale_fromTower` (the same witness
for both).  For real `t ∈ [0,1]`, `ν_{p₁}`-almost everywhere,

`∑_ℓ A_phys(t)_ℓ (restr x) = W₁^C(1, x) + W₂^C(t, x; g)`

for the zero class: the potential parts cancel in `B_g(t) - B₀(t)` (equal datum and hat pair, the
sources differ by `g/β`), the source part is `W₂(t)` by the landed ray identity of the source
functional (`Wtwo_zeroClass_eq_hat`, with `dirTermSrc_smul_one`), `B₀(1) = W₁(1)` by
`Wone_zeroClass_eq_hat`, and the real exponents are the complex ones almost everywhere
(`ae_exponentsC_eq`). -/
theorem ae_sum_A_phys_eq_WoneC_add_WtwoC
    (S : StepSetting d L N₁ m₁ k N ϱ) {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ} {pp : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (R0 : S.RayData pp) (hlt : S.p₁ < pp)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hp : 0 < S.p₁) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hpc : S.p₁ < cψ)
    (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)
    (g : Fld d L N₁ m₁ (k + 1) N)
    {m₀ : ℕ} {ρ Rσ εU a κ0 Kc' : ℝ} (hpρ : S.p₁ ≤ ρ)
    {SΛ : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    {XW : Set (((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) × ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)))}
    {val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
      ℂ → (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) → ℂ}
    {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) →
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) →
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) → Prop}
    {AgF : Set (CTorus d L N₁ m₁ (k + 1)) →
      ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → Prop}
    (I₀ : DirectTerms S m₀ hp (fun ψ => (ψ, ψ)) ρ Rσ εU a
      (rawOf S.D', (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) SΛ XW val AgΘ AgF)
    (Ig : DirectTerms S m₀ hp (fun ψ => (ψ, ψ)) ρ Rσ εU a
      (rawOf S.D', fun y i => g y i / (S.β : ℂ)) SΛ XW val AgΘ AgF)
    (hval : ∀ x w σ Θ, val x w σ Θ =
      (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight x.1 w.1 σ Θ.1 +
      (S.β : ℂ) * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, Θ.2 s.1 s.2 *
        dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (onXi S.G' S.a₁ S.ν eps
            (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
              (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
          (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} (hdom : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (h𝒴₀ : I₀.𝒴 = 𝒴) (h𝒴g : Ig.𝒴 = 𝒴)
    (hxwz : ∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ ψ ∈ hatDisk S.U N ρ,
      ((z • ψ, z • ψ), (z • ψ, z • ψ)) ∈ XW)
    (hAgF : ∀ (z : ℂ) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (ψ ψ' : S.U × Fin N → ℂ),
      AgF Y (ψ, ψ) (ψ', ψ') → AgF Y (z • ψ, z • ψ) (z • ψ', z • ψ'))
    (hcont₀ : DiagCont (fun ψ : S.U × Fin N → ℂ => (ψ, ψ)) XW SΛ Rσ I₀.𝒴 I₀.T)
    (hcontg : DiagCont (fun ψ : S.U × Fin N → ℂ => (ψ, ψ)) XW SΛ Rσ Ig.𝒴 Ig.T)
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ1 : 1 < Rσ) (hεU : 0 ≤ εU)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc') {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂S.nuFl, ∑ y, (A_phys S m₀ I₀ Ig hdom h𝒴₀ h𝒴g hxwz hAgF hcont₀ hcontg hN hρ hRσ1 hεU
        hκ0 hKc (t : ℂ)).H y ((S.blockSplit m₀ hp).restr x) =
      S.WoneC (zeroClass d L N₁ m₁ k N ϱ) 1 x + S.WtwoC (zeroClass d L N₁ m₁ k N ϱ) g t x := by
  have hρ' : 0 < ρ := hρ
  obtain ⟨h40, hr⟩ := S.margin_small R0.hδ0 R0.hβ hlt R0.hB5 R0.hp40 R0.hrad
  have hseg : ((1 : ℝ), t) ∈ stepSegments := Or.inr ⟨rfl, ht⟩
  have hex := S.ae_exponentsC_eq (zeroClass d L N₁ m₁ k N ϱ) R0.ha₁ R0.H R0.hδ'0 R0.hδ' R0.hD'R
    R0.hδ0 R0.hfam R0.hsm R0.hχu R0.hnorm R0.hβ hp R0.hB5 R0.hK2 h40 hr g _ hseg
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have htz : ‖(t : ℂ)‖ < 3 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    linarith [ht.2]
  filter_upwards [S.ae_hatOf_restr m₀ hρ hp hpρ, S.ae_ball hp, hex] with x hx hχ hxe
  have hW1 := S.Wone_zeroClass_eq_hat hC R0 hlt (StepSetting.baseDomain_of_rayData R0) hD hc7
    (lt_of_lt_of_le one_lt_two hR) hsmR hMX hdm hα hsm hp hcψ hpc hδ₁ h1 hχ
  have hW2 := S.Wtwo_zeroClass_eq_hat hC R0 hlt hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm
    hp hcψ hpc hδ₁ g ht hχ
  rw [sum_A_phys S m₀ I₀ Ig hdom h𝒴₀ h𝒴g hxwz hAgF hcont₀ hcontg hN hρ hRσ1 hεU hκ0 hKc htz, hx,
    hxe]
  simp only [one_smul]
  have e1 : val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) 1 (rawOf S.D', 0) =
      S.Wone (zeroClass d L N₁ m₁ k N ϱ) 1 x := by
    rw [← hW1, hval]
    simp
  have e2 : val ((t : ℂ) • S.hatC x, (t : ℂ) • S.hatC x) ((t : ℂ) • S.hatC x, (t : ℂ) • S.hatC x) 1
        (rawOf S.D', fun y i => g y i / (S.β : ℂ)) -
      val ((t : ℂ) • S.hatC x, (t : ℂ) • S.hatC x) ((t : ℂ) • S.hatC x, (t : ℂ) • S.hatC x) 1
        (rawOf S.D', (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =
      S.Wtwo (zeroClass d L N₁ m₁ k N ϱ) g t x := by
    rw [← hW2, hval, hval]
    simp only [dirTermSrc_smul_one, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    ring
  linear_combination e1 + e2

end Identity

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology

/-- **The radius margin at the ray `3/2`** (OBSRAY §2–§3): with `r = c_ψ / (2 p₁) - 4`, the landed
`StepScaleData.ray_margin` `(4 + r) p₁ < c_ψ` gives `(4 + r) (3/2) p₁ = 3 c_ψ / 4 < c_ψ`. -/
theorem StepScaleData.ray_margin_scaled {κmin : ℝ} {T : StepTower κmin} {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁) (hp : 0 < p₁) :
    ((2 : ℝ) * 2 + lvR T.κ T.t (β * 3 ^ k) p₁) * (3 / 2 * p₁) < lvCpsi T.κ T.t (β * 3 ^ k) :=
  lvRG_ray_margin_scaled 3 3 2 _ _ _ _ D.cψ_pos hp

/-- The pair-scaling `z ψ ↦` preserves the sharp paired agreement relation. -/
theorem agFDirPair_smul {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) (z : ℂ) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (ψ ψ' : S.U × Fin N → ℂ) (h : AgFDirPair S Y (ψ, ψ) (ψ', ψ')) :
    AgFDirPair S Y (z • ψ, z • ψ) (z • ψ', z • ψ') :=
  ⟨fun y hy i => by
      show z * ψ (unitPt S.hG' y, i) = z * ψ' (unitPt S.hG' y, i)
      have e : ψ (unitPt S.hG' y, i) = ψ' (unitPt S.hG' y, i) := h.1 y hy i
      rw [e],
    fun y hy i => by
      show z * ψ (unitPt S.hG' y, i) = z * ψ' (unitPt S.hG' y, i)
      have e : ψ (unitPt S.hG' y, i) = ψ' (unitPt S.hG' y, i) := h.2 y hy i
      rw [e]⟩

open Classical in
/-- **The observable-ray activity at the shared tower** (OBSRAY §3–§4, T1–T4).  For `S = T.step …`
and `D : StepScaleData T …` (`β ≥ 1`, no further threshold), let `val, 𝒴, Tt` be the direct terms of
`sourceDirectTerms_scale_fromTower` (slice `η = 1/β`), `ε_U` the physical amplitude.  Then there
are the label activities `A₀ z = B₀(z)` (at `(rawOf D', 0)`) and, for every source `g` of the
`ℓ¹` ball, `Ag z = B_g(z)` (at `(rawOf D', g/β)`), on the thick labels of `𝒴`, with prefactor
`ε_U`, rate `2 κ_dec - 1`, entropy constant `K₀(κ₀) + 1`, block split `S.blockSplit 1 hp`,
that are `Tt Y (zψ̂, zψ̂) (zψ̂, zψ̂) 1 Θ` for `‖z‖ < 3/2` and `0` otherwise, and whose physical
combination `(A₀ 1 - A₀ t) ⊕ Ag t` satisfies, for real `t ∈ [0,1]`, `ν_{p₁}`-almost everywhere,
`∑ (restr x) = W₁^C(1, x) + W₂^C(t, x; g)`.  Holomorphy in `z` is not asserted. -/
theorem obsRayActivity_fromTower {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β : ℝ) (hβ1 : 1 ≤ β)
    (p₁ : ℝ) (hp : 0 < p₁) (D : StepScaleData T k hk N₁ ν β p₁) :
    ∃ (val : (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
        (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
        ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
          (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
      (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
      (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
        (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
        ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
          (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
      (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y),
      (∀ x w σ Θ, val x w σ Θ =
        (-((T.step k hk N₁ ν β p₁).β : ℂ)) * raySrc3 (hatFun (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t (T.step k hk N₁ ν β p₁).hG'
          (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne (T.step k hk N₁ ν β p₁).hG (T.step k hk N₁ ν β p₁).hG' (le_refl (k + 1)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t)) taylorWeight
          x.1 w.1 σ Θ.1 +
        ((T.step k hk N₁ ν β p₁).β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
          dirTermSrc (hatFun (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t (T.step k hk N₁ ν β p₁).hG'
            (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t
              (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                (flFieldOne (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν D ψ')
                  s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
      0 < β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β) ∧
      ∃ A₀ : ℂ → LabelAct (thickLabels 𝒴 hdom) ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).Ωb
          (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
            (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β)) (2 * T.κdec - 1) T.κ0 (K0 3 3 T.κ0 + 1),
        (∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ y Φ, (A₀ z).H y Φ =
          Tt y.1 (z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ, z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ)
            (z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ, z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ) 1
            (rawOf (T.step k hk N₁ ν β p₁).D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))) ∧
        (∀ z : ℂ, 3 / 2 ≤ ‖z‖ → ∀ y Φ, (A₀ z).H y Φ = 0) ∧
        ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
        ∃ Ag : ℂ → LabelAct (thickLabels 𝒴 hdom) ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).Ωb
            (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
              (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β)) (2 * T.κdec - 1) T.κ0
            (K0 3 3 T.κ0 + 1),
          (∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ y Φ, (Ag z).H y Φ =
            Tt y.1 (z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ, z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ)
              (z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ, z • (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ) 1
              (rawOf (T.step k hk N₁ ν β p₁).D', fun y i => g y i / ((T.step k hk N₁ ν β p₁).β : ℂ))) ∧
          (∀ z : ℂ, 3 / 2 ≤ ‖z‖ → ∀ y Φ, (Ag z).H y Φ = 0) ∧
          ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂(T.step k hk N₁ ν β p₁).nuFl,
            ∑ y, (((A₀ 1).sub (A₀ (t : ℂ))).sum (Ag (t : ℂ))).H y
                (((T.step k hk N₁ ν β p₁).blockSplit 1 hp).restr x) =
              (T.step k hk N₁ ν β p₁).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) 1 x +
              (T.step k hk N₁ ν β p₁).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x := by
  classical
  obtain ⟨R0⟩ := D.ray
  have hr0 := D.r_pos
  have hcψ0 := D.cψ_pos
  have hC := D.core
  have hD := D.xi
  have hβ0 : 0 < β := by linarith
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  have hKc : K0 3 3 T.κ0 ≤ K0 3 3 T.κ0 + 1 := by linarith
  obtain ⟨val, 𝒴, Tt, hval, -, hcont, hI, hmem0, hmemg⟩ := sourceDirectTerms_scale_fromTower T k hk
    N₁ h3N hN ν hνpos hν β hβ1 p₁ 1 one_pos le_rfl D (T.step k hk N₁ ν β p₁) rfl hp
  obtain ⟨I₀, h𝒴₀, hT₀⟩ := hI _ hmem0
  have hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y := fun Y hY => I₀.dom Y (h𝒴₀ ▸ hY)
  have hεpos : 0 < β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β) := by
    exact sourceEta_scaled_pos 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t _ 1 β hβ0 one_pos hr0
      T.t_pos (cK2'_pos' T.fam_nonneg) (by linarith [one_le_c1 3 3])
  refine ⟨val, 𝒴, Tt, hdom, hval, hεpos, ?_⟩
  have hxwz : ∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ ψ ∈ hatDisk (T.step k hk N₁ ν β p₁).U 2 p₁,
      ((z • ψ, z • ψ), (z • ψ, z • ψ)) ∈
        physXW (T.step k hk N₁ ν β p₁) (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2
          (lvR T.κ T.t (β * 3 ^ k) p₁) :=
    fun z hz ψ hψ => scaled_pair_mem_physXW (T.step k hk N₁ ν β p₁) hψ hz (by norm_num)
      (by norm_num) hr0.le (D.ray_margin_scaled hp)
  have hAgF : ∀ (z : ℂ) (Y : Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
      (ψ ψ' : (T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ),
      AgFDirPair (T.step k hk N₁ ν β p₁) Y (ψ, ψ) (ψ', ψ') →
      AgFDirPair (T.step k hk N₁ ν β p₁) Y (z • ψ, z • ψ) (z • ψ', z • ψ') :=
    fun z Y ψ ψ' h => agFDirPair_smul _ z Y ψ ψ' h
  have hcont₀ := hcont
  rw [← h𝒴₀, ← hT₀] at hcont₀
  have hRσ1 : (1 : ℝ) < 2 := by norm_num
  have hpc : p₁ < lvCpsi T.κ T.t (β * 3 ^ k) :=
    p₁_lt_of_margin hp le_rfl hRσ1 hRσ1 hr0 D.ray_margin
  refine ⟨obsRayAct (T.step k hk N₁ ν β p₁) 1 I₀ hdom h𝒴₀ hxwz hAgF hcont₀ hN3 hp hRσ1 hεpos.le
      T.κ0_ent hKc, ?_, ?_, ?_⟩
  · intro z hz y Φ
    rw [obsRayAct_H_of_lt _ _ _ hdom h𝒴₀ hxwz hAgF hcont₀ hN3 hp hRσ1 hεpos.le T.κ0_ent hKc hz,
      hT₀]
  · intro z hz y Φ
    exact obsRayAct_H_of_not_lt _ _ _ hdom h𝒴₀ hxwz hAgF hcont₀ hN3 hp hRσ1 hεpos.le T.κ0_ent
      hKc hz y Φ
  · intro g hg
    obtain ⟨Ig, h𝒴g, hTg⟩ := hI _ (hmemg g hg)
    have hcontg := hcont
    rw [← h𝒴g, ← hTg] at hcontg
    refine ⟨obsRayAct (T.step k hk N₁ ν β p₁) 1 Ig hdom h𝒴g hxwz hAgF hcontg hN3 hp hRσ1
      hεpos.le T.κ0_ent hKc, ?_, ?_, ?_⟩
    · intro z hz y Φ
      rw [obsRayAct_H_of_lt _ _ _ hdom h𝒴g hxwz hAgF hcontg hN3 hp hRσ1 hεpos.le T.κ0_ent hKc hz,
        hTg]
    · intro z hz y Φ
      exact obsRayAct_H_of_not_lt _ _ _ hdom h𝒴g hxwz hAgF hcontg hN3 hp hRσ1 hεpos.le T.κ0_ent
        hKc hz y Φ
    · intro t ht
      exact ae_sum_A_phys_eq_WoneC_add_WtwoC (T.step k hk N₁ ν β p₁) hC R0 D.p_lt hD T.c7_cap
        (R := 2) le_rfl T.bg1_cap T.t_cap T.bg0_cap T.cK2_cap T.cK2'_cap T.large_block T.dom_margin
        T.coer_margin T.δc_small hp hcψ0.le hpc D.fl_radius g le_rfl I₀ Ig hval hdom h𝒴₀ h𝒴g
        hxwz hAgF hcont₀ hcontg hN3 hp hRσ1 hεpos.le T.κ0_ent hKc ht

open Classical in
/-- **The size of the prefactor of `A_phys`.**  With the constants `C_E, C_F` of
`sourceActivityC_scale_fromTower` (the same expressions), for `β` beyond one threshold and
`p₁ ≤ A₁ (log β 3^k)^p`, the prefactor `2 ε_U` of `A_phys` (`ε_U` the physical amplitude) obeys the
bound of the landed record (whose `ε_H = 4 ε_U`). -/
theorem obsRayEps_bound_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ CE CF : ℝ, 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (ν : ℝ) (β : ℝ), β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
    p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
    2 * (β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β)) ≤
      CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) := by
  classical
  have hent := aEnt_nonneg 3 3
  have hc1 := one_le_c1 3 3
  have ht0 := T.t_pos
  have hB0 := T.fam_nonneg
  have hκ0 := T.κ0_nonneg
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQdef]; exact cK2'_pos' hB0
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3 *
    (((3 : ℕ) : ℝ) ^ 3 * ((((2 : ℕ) : ℝ) / 2) * (2 * (1 + Q) ^ 2 +
      (((3 : ℕ) : ℝ) + 1 + rho4 3 3 2 T.BG T.κ) * Q ^ 2) * T.t ^ 2)) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by
    rw [hPdef]
    have hρ4 := T.rho_nonneg
    positivity
  have hK0 : 0 < Q * T.t := mul_pos hQ0 ht0
  obtain ⟨β₁, hexpβ₁, hA'⟩ := sourceAmp_scale (A₁ := A₁) (κ := T.κ) (t := T.t) hA p ht0
  refine ⟨max 2 β₁, srcCE A₁ T.κ T.t P, srcCF A₁ T.κ T.t (Q * T.t), le_max_left _ _,
    srcCE_pos hA ht0 hP0, srcCF_pos hA ht0 hK0, ?_⟩
  intro k hk N₁ _ ν β hβ p₁ hp0 hp₁ D
  have hρ4 := T.rho_nonneg
  have hr0 := D.r_pos
  have hβ₁ : β₁ ≤ β := le_trans (le_max_right _ _) hβ
  have hβ2 : 2 ≤ β := le_trans (le_max_left _ _) hβ
  have hβ0 : 0 < β := by linarith
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hbβ : β ≤ β * 3 ^ k := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * 3 ^ k := by positivity
  have hamp := (hA' (β * 3 ^ k) (hβ₁.trans hbβ) p₁ hp0 hp₁).2 P (Q * T.t) 1 hP0 hK0.le one_pos.le
  obtain ⟨εU, hεU⟩ : ∃ εU : ℝ, εU = β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β) := ⟨_, rfl⟩
  have hbU : (T.step k hk N₁ ν β p₁).betaU = β * 3 ^ k := hatStepK_betaU k T.m₁ hk ν β p₁ _
  obtain ⟨hid, hpot, hterm0, hεle', hεpos⟩ := physAmp_facts (T.step k hk N₁ ν β p₁)
    (by norm_num) le_rfl 1 (compWeight_three_mem hk) rfl hβ0 rfl hbU hQ0 ht0 hρ4 hr0 one_pos hQdef
    hPdef hεU
  have hεle := hεle' _ hamp
  have hexp : Real.exp 1 ≤ β * 3 ^ k := le_trans hexpβ₁ (hβ₁.trans hbβ)
  have hℓ : 1 ≤ Real.log (β * 3 ^ k) := (Real.le_log_iff_exp_le hb0).2 hexp
  have hε4 := sourceAmp_scale_four (A₁ := A₁) (κ := T.κ) (t := T.t) (P := P) (K := Q * T.t)
    (q := 1) p hb0 (by linarith) hεle
  rw [one_mul] at hε4
  rw [← hεU]
  linarith


end Balaban.Inhabited
