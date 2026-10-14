/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ActivityFamilyAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The physical and tilted observable activity as one family in the datum and the source

The landed observable theorem builds its activity `A_phys` separately for each source `g`.  Here
the activity is built from the ONE analytic family `A(e, u)` of
`activityFamilyAnalytic_fromTower`, with `e = (raw datum, source)`.

* `physAct A e t`: the label activity of `(A (e.1,0) 1 - A (e.1,0) t) ⊕ A e t`, on the labels
  `Lab.sum Lab`.  Its label sum is `∑ A((e.1,0),1) - ∑ A((e.1,0),t) + ∑ A(e,t)`, which is
  `W₁(1) + W₂(g, t)` of the step by the `W` identities of the family.
* `tiltAct A Rg hR 𝒰 e t σ`: the scalar tilt `obsScalarTilt` of `physAct A e`.
* `physAct_analyticOnNhd`, `tiltAct_analyticOnNhd`: joint analyticity in `(e, t)` and `(e, t, σ)`.
* `tiltAct_holt`, `tiltAct_holσ`, `tiltAct_zero`: the fields asked by the observable consumer,
  for every parameter `e`.
* `obsTiltFamily_fromTower`: at the tower, the identity of the label sum with
  `WoneC C 1 + WtwoC C g t` of the step `S.withDatum D` at every datum `D` of the fibre
  `h ≡ h₀` and every source `‖g‖₁ < q` (one null set), with the amplitude bound.
-/

@[expose] public section

namespace Balaban.Inhabited

open MeasureTheory Metric Balaban Balaban.Fluctuation Balaban.Localization Balaban.Polymer
  Balaban.SmallField Balaban.Multiscale Balaban.Background Balaban.Localization.LevelPair
  Balaban.Localization.I5Inhabited Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep

section Generic

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
variable {Lb : Type*} [Fintype Lb] {Lab : CubeLabels m₀ j Ω Lb} {εH κH κ0 Kc : ℝ}
  {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
  [∀ b, MeasurableSpace (Ωb b)] {E₁ E₂ : Type*}

/-- **The physical activity of the observable, from one family.**  For a family `A` over the
parameter `e = (datum, source)`, `physAct A e t` is `(A (e.1,0) 1 - A (e.1,0) t) ⊕ A e t` on the
labels `Lab.sum Lab`; its label sum is
`∑ A((e.1,0),1) - ∑ A((e.1,0),t) + ∑ A(e,t)`. -/
noncomputable def physAct [Zero E₂] (A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (e : E₁ × E₂) (t : ℂ) :
    LabelAct (Lab.sum Lab) Ωb (max (εH + εH) εH) κH κ0 (Kc + Kc) :=
  (((A (e.1, 0) 1).sub (A (e.1, 0) t)).sum (A e t))

/-- **The tilted activity of the observable, from one family**: the scalar tilt
`obsScalarTilt` of `physAct A e`. -/
noncomputable def tiltAct [Zero E₂] (A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (Rg : ℝ) (hR : 0 ≤ Rg) (𝒰 : Set ℂ) (e : E₁ × E₂) (t σ : ℂ) :
    LabelAct (Lab.sum Lab) Ωb (Rg * max (εH + εH) εH) κH κ0 (Kc + Kc) :=
  obsScalarTilt Rg hR 𝒰 (physAct A e) t σ

section Values

variable [Zero E₂] (A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)

theorem physAct_H_inl (e : E₁ × E₂) (t : ℂ) (y : Lb) (Φ : ∀ b, Ωb b) :
    (physAct A e t).H (Sum.inl y) Φ = (A (e.1, 0) 1).H y Φ - (A (e.1, 0) t).H y Φ := by
  simp [physAct]

theorem physAct_H_inr (e : E₁ × E₂) (t : ℂ) (y : Lb) (Φ : ∀ b, Ωb b) :
    (physAct A e t).H (Sum.inr y) Φ = (A e t).H y Φ := rfl

/-- The label sum of `physAct`. -/
theorem physAct_total (e : E₁ × E₂) (t : ℂ) (Φ : ∀ b, Ωb b) :
    ∑ y, (physAct A e t).H y Φ =
      ∑ y, (A (e.1, 0) 1).H y Φ - ∑ y, (A (e.1, 0) t).H y Φ + ∑ y, (A e t).H y Φ := by
  rw [Fintype.sum_sum_type]
  simp only [physAct_H_inl, physAct_H_inr, Finset.sum_sub_distrib]

theorem tiltAct_H (Rg : ℝ) (hR : 0 ≤ Rg) (𝒰 : Set ℂ) (e : E₁ × E₂) (t σ : ℂ) (y : Lb ⊕ Lb)
    (Φ : ∀ b, Ωb b) :
    (tiltAct A Rg hR 𝒰 e t σ).H y Φ = obsTiltFactor Rg 𝒰 t σ * (physAct A e t).H y Φ := rfl

/-- The tilt at `σ = 1` has the same label sum as `physAct`, for `t ∈ 𝒰` and `1 < Rg`. -/
theorem tiltAct_total_one {Rg : ℝ} (hR : 0 ≤ Rg) (hRg : 1 < Rg) {𝒰 : Set ℂ} {t : ℂ}
    (ht : t ∈ 𝒰) (e : E₁ × E₂) (Φ : ∀ b, Ωb b) :
    ∑ y, (tiltAct A Rg hR 𝒰 e t 1).H y Φ = ∑ y, (physAct A e t).H y Φ := by
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [tiltAct_H, obsTiltFactor_of_mem ht (by simpa using hRg), one_mul]

end Values

section Analytic

variable [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  {A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc} {V : Set (E₁ × E₂)} {R : ℝ}

/-- **Joint analyticity of the physical activity.**  If `(e, u) ↦ A(e, u)_y(Φ)` is analytic on
`V × ball 0 R` with `1 < R`, and the zero-source point `(e.1, 0)` lies in `V` for every `e ∈ V`,
then `(e, t) ↦ (physAct A e t)_y(Φ)` is analytic on `V × ball 0 R`, for every label of
`Lab.sum Lab` and every configuration. -/
theorem physAct_analyticOnNhd (hR : 1 < R) (hsub : ∀ e ∈ V, (e.1, (0 : E₂)) ∈ V)
    (h : ∀ (y : Lb) (Φ : ∀ b, Ωb b),
      AnalyticOnNhd ℂ (fun r : (E₁ × E₂) × ℂ => (A r.1 r.2).H y Φ) (V ×ˢ ball (0 : ℂ) R))
    (y : Lb ⊕ Lb) (Φ : ∀ b, Ωb b) :
    AnalyticOnNhd ℂ (fun r : (E₁ × E₂) × ℂ => (physAct A r.1 r.2).H y Φ)
      (V ×ˢ ball (0 : ℂ) R) := by
  have hL : AnalyticOnNhd ℂ
      (fun p : (E₁ × E₂) × ℂ => (((p.1.1, (0 : E₂)), p.2) : (E₁ × E₂) × ℂ)) Set.univ :=
    (((ContinuousLinearMap.fst ℂ E₁ E₂).prod (0 : E₁ × E₂ →L[ℂ] E₂)).prodMap
      (ContinuousLinearMap.id ℂ ℂ)).analyticOnNhd _
  have hL1 : AnalyticOnNhd ℂ
      (fun p : (E₁ × E₂) × ℂ => (((p.1.1, (0 : E₂)), (1 : ℂ)) : (E₁ × E₂) × ℂ)) Set.univ := by
    have h1 : AnalyticOnNhd ℂ (fun p : (E₁ × E₂) × ℂ => ((p.1.1, (0 : E₂)) : E₁ × E₂))
        Set.univ :=
      ((((ContinuousLinearMap.fst ℂ E₁ E₂).prod (0 : E₁ × E₂ →L[ℂ] E₂)).comp
        (ContinuousLinearMap.fst ℂ (E₁ × E₂) ℂ)).analyticOnNhd _)
    exact h1.prod (analyticOnNhd_const)
  have hmem0 : ∀ r ∈ V ×ˢ ball (0 : ℂ) R, (((r.1.1, (0 : E₂)), r.2) : (E₁ × E₂) × ℂ) ∈
      V ×ˢ ball (0 : ℂ) R := fun r hr => ⟨hsub r.1 hr.1, hr.2⟩
  have hmem1 : ∀ r ∈ V ×ˢ ball (0 : ℂ) R, (((r.1.1, (0 : E₂)), (1 : ℂ)) : (E₁ × E₂) × ℂ) ∈
      V ×ˢ ball (0 : ℂ) R := fun r hr => ⟨hsub r.1 hr.1, by simpa using hR⟩
  cases y with
  | inl y =>
    have hA0 := (h y Φ).comp (hL.mono (Set.subset_univ (V ×ˢ ball (0 : ℂ) R))) hmem0
    have hA1 := (h y Φ).comp (hL1.mono (Set.subset_univ (V ×ˢ ball (0 : ℂ) R))) hmem1
    have : (fun r : (E₁ × E₂) × ℂ => (physAct A r.1 r.2).H (Sum.inl y) Φ) =
        fun r => (A (r.1.1, 0) 1).H y Φ - (A (r.1.1, 0) r.2).H y Φ := by
      funext r
      exact physAct_H_inl A r.1 r.2 y Φ
    rw [this]
    exact hA1.sub hA0
  | inr y =>
    exact h y Φ

/-- Holomorphy in `t` of the physical activity at a fixed parameter `e ∈ V`. -/
theorem physAct_differentiableOn (hR : 1 < R) (hsub : ∀ e ∈ V, (e.1, (0 : E₂)) ∈ V)
    (h : ∀ (y : Lb) (Φ : ∀ b, Ωb b),
      AnalyticOnNhd ℂ (fun r : (E₁ × E₂) × ℂ => (A r.1 r.2).H y Φ) (V ×ˢ ball (0 : ℂ) R))
    {e : E₁ × E₂} (he : e ∈ V) (y : Lb ⊕ Lb) (Φ : ∀ b, Ωb b) :
    DifferentiableOn ℂ (fun t : ℂ => (physAct A e t).H y Φ) (ball (0 : ℂ) R) := by
  have hι : AnalyticOnNhd ℂ (fun t : ℂ => ((e, t) : (E₁ × E₂) × ℂ)) Set.univ :=
    (analyticOnNhd_const (v := e)).prod analyticOnNhd_id
  exact ((physAct_analyticOnNhd hR hsub h y Φ).comp (hι.mono (Set.subset_univ _))
    (fun t ht => ⟨he, ht⟩)).differentiableOn

/-- **Joint analyticity of the tilted activity** in `(e, t, σ)` on `V × (𝒰 × ball 0 Rg)`, for
an open `V` and an open `𝒰 ⊆ ball 0 R`. -/
theorem tiltAct_analyticOnNhd {Rg : ℝ} (hRg : 0 ≤ Rg) {𝒰 : Set ℂ} (hR : 1 < R)
    (hV : IsOpen V) (h𝒰 : IsOpen 𝒰) (h𝒰R : 𝒰 ⊆ ball (0 : ℂ) R)
    (hsub : ∀ e ∈ V, (e.1, (0 : E₂)) ∈ V)
    (h : ∀ (y : Lb) (Φ : ∀ b, Ωb b),
      AnalyticOnNhd ℂ (fun r : (E₁ × E₂) × ℂ => (A r.1 r.2).H y Φ) (V ×ˢ ball (0 : ℂ) R))
    (y : Lb ⊕ Lb) (Φ : ∀ b, Ωb b) :
    AnalyticOnNhd ℂ (fun r : (E₁ × E₂) × ℂ × ℂ => (tiltAct A Rg hRg 𝒰 r.1 r.2.1 r.2.2).H y Φ)
      (V ×ˢ (𝒰 ×ˢ ball (0 : ℂ) Rg)) := by
  have hM : AnalyticOnNhd ℂ (fun r : (E₁ × E₂) × ℂ × ℂ => ((r.1, r.2.1) : (E₁ × E₂) × ℂ))
      Set.univ :=
    ((ContinuousLinearMap.fst ℂ (E₁ × E₂) (ℂ × ℂ)).prod
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ (E₁ × E₂) (ℂ × ℂ)))
        ).analyticOnNhd _
  have h1 := (physAct_analyticOnNhd hR hsub h y Φ).comp
    (hM.mono (Set.subset_univ (V ×ˢ (𝒰 ×ˢ ball (0 : ℂ) Rg))))
    (fun r hr => ⟨hr.1, h𝒰R hr.2.1⟩)
  have hσ : AnalyticOnNhd ℂ (fun r : (E₁ × E₂) × ℂ × ℂ => r.2.2)
      (V ×ˢ (𝒰 ×ˢ ball (0 : ℂ) Rg)) :=
    (((ContinuousLinearMap.snd ℂ ℂ ℂ).comp
      (ContinuousLinearMap.snd ℂ (E₁ × E₂) (ℂ × ℂ))).analyticOnNhd _)
  refine (hσ.mul h1).congr (hV.prod (h𝒰.prod isOpen_ball)) fun r hr => ?_
  have hσn : ‖r.2.2‖ < Rg := by simpa using hr.2.2
  show r.2.2 * (physAct A r.1 r.2.1).H y Φ = obsTiltFactor Rg 𝒰 r.2.1 r.2.2 * _
  rw [obsTiltFactor_of_mem hr.2.1 hσn]

/-- **The fields of the consumer, uniformly in the parameter**: for every `e ∈ V` the tilted
activity is holomorphic in `t ∈ 𝒰` at `σ = 1`, holomorphic in `σ` on the disc, and vanishes at
`σ = 0`. -/
theorem tiltAct_fields {Rg : ℝ} (hRg : 0 ≤ Rg) (hRg1 : 1 < Rg) {𝒰 : Set ℂ}
    (hR : 1 < R) (h𝒰R : 𝒰 ⊆ ball (0 : ℂ) R) (hsub : ∀ e ∈ V, (e.1, (0 : E₂)) ∈ V)
    (h : ∀ (y : Lb) (Φ : ∀ b, Ωb b),
      AnalyticOnNhd ℂ (fun r : (E₁ × E₂) × ℂ => (A r.1 r.2).H y Φ) (V ×ˢ ball (0 : ℂ) R))
    {e : E₁ × E₂} (he : e ∈ V) :
    (∀ y Φ, DifferentiableOn ℂ (fun t => (tiltAct A Rg hRg 𝒰 e t 1).H y Φ) 𝒰) ∧
    (∀ t ∈ 𝒰, ∀ y Φ, DifferentiableOn ℂ (fun σ => (tiltAct A Rg hRg 𝒰 e t σ).H y Φ)
      (ball (0 : ℂ) Rg)) ∧
    (∀ t y Φ, (tiltAct A Rg hRg 𝒰 e t 0).H y Φ = 0) :=
  ⟨obsScalarTilt_holt hRg1 fun y Φ =>
      (physAct_differentiableOn hR hsub h he y Φ).mono h𝒰R,
    fun _ ht => obsScalarTilt_holσ (Aphys := physAct A e) ht,
    fun t y Φ => obsScalarTilt_zero (Aphys := physAct A e) t y Φ⟩

end Analytic

end Generic

section Tower

open Set

/-- At source radius `ρ` (`q ≤ ρ`, `max 1 ρ ≤ β`); the landed theorem is its `ρ = 1` corollary. **The physical and tilted observable activity of the step, as one family.**  At the shared
tower, for each admissible scale and each `Kc ≥ K₀`, the one analytic family `A` of
`activityFamilyAnalytic_fromTower` gives, with `e = (datum, source)` and `𝒰 = ball 0 (3/2)`:

* the amplitude `εH > 0` of `A`, with `2 εH` (the constant of `physAct A e`) at most
  `C_E ℓ^{3p}/√b + q C_F ℓ^p/√b`, `ℓ = log b`, `b = β 3^k`, for all `e` (so uniformly in the
  source ball of radius `q ≤ ρ`);
* joint analyticity of `(e, t) ↦ (physAct A e t)_y(Φ)` on `physVq × ball 0 2`, and of
  `(e, t, σ) ↦ (tiltAct A Rg _ 𝒰 e t σ)_y(Φ)` on `physVq × (𝒰 × ball 0 Rg)`;
* one null set outside of which, for every datum `D'` of the fibre `h ≡ h₀`, every source
  `‖g‖₁ < q` and every `t ∈ [0,1]`, `WoneC C 1 + WtwoC C g t` of `S.withDatum D'` is the label
  sum of `physAct A (rawOf D', g) t` and (for `1 < Rg`) that of `tiltAct … (rawOf D', g) t 1`;
* for every `e` of the chart `physVq` and `1 < Rg`: holomorphy in `t ∈ 𝒰` at `σ = 1`,
  holomorphy in `σ` on the disc `ball 0 Rg` at every `t ∈ 𝒰`, and vanishing at `σ = 0`.  The fixed `obsTiltFamily_fromTower` is its corollary. -/
theorem obsTiltFamily_fromTowerG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ (β₀ CE CF : ℝ), 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β → ∀ ρ : ℝ, max 1 ρ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → ∀ q : ℝ, 0 < q → q ≤ ρ →
      StepScaleDataG T k hk N₁ ν β p₁ →
      ∀ S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∀ {Kc : ℝ}, K0 d L T.κ0 ≤ Kc →
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
          Set.univ Lb) (εH : ℝ)
        (A : physParam N S → ℂ → LabelAct Lab (S.blockSplit T.m₀ hp).Ωb εH (2 * T.κdec - 1) T.κ0 Kc),
        0 < εH ∧
        2 * εH ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
          q * CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
        (∀ (y : Lb ⊕ Lb) (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
          AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => (physAct A r.1 r.2).H y Φ)
            (physVqRho S S.a₁ S.ν T.t ρ q ×ˢ ball (0 : ℂ) 2)) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg) (y : Lb ⊕ Lb) (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
          AnalyticOnNhd ℂ (fun r : physParam N S × ℂ × ℂ =>
            (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2)) r.1 r.2.1 r.2.2).H y Φ)
            (physVqRho S S.a₁ S.ν T.t ρ q ×ˢ (ball (0 : ℂ) (3 / 2) ×ˢ ball (0 : ℂ) Rg))) ∧
        (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
          ∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x', ∑ i, ‖g x' i‖ < q → ∀ t ∈ Icc (0 : ℝ) 1,
          (S.withDatum D' hDh).WoneC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) (1 : ℝ) x +
            (S.withDatum D' hDh).WtwoC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g t x =
          ∑ y, (physAct A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) (t : ℂ)).H y
            ((S.blockSplit T.m₀ hp).restr x) ∧
          ∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg →
          (S.withDatum D' hDh).WoneC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) (1 : ℝ) x +
            (S.withDatum D' hDh).WtwoC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g t x =
          ∑ y, (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2))
            ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) (t : ℂ) 1).H y
            ((S.blockSplit T.m₀ hp).restr x)) ∧
        (∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ (y : Lb ⊕ Lb) (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
          DifferentiableOn ℂ (fun t : ℂ => (physAct A e t).H y Φ) (ball (0 : ℂ) (3 / 2))) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg → ∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q,
          (∀ y Φ, DifferentiableOn ℂ
            (fun t => (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2)) e t 1).H y Φ)
            (ball (0 : ℂ) (3 / 2))) ∧
          (∀ t ∈ ball (0 : ℂ) (3 / 2), ∀ y Φ, DifferentiableOn ℂ
            (fun σ => (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2)) e t σ).H y Φ)
            (ball (0 : ℂ) Rg)) ∧
          (∀ t y Φ, (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2)) e t 0).H y Φ = 0)) := by
  classical
  obtain ⟨β₀, CE, CF, hβ₀, hCE, hCF, hfam⟩ := activityFamilyAnalytic_fromTowerG_rho T hA p
  refine ⟨β₀, CE, CF, hβ₀, hCE, hCF, ?_⟩
  intro k hk N₁ _ hLN hN ν hνpos hν β hβ ρ hρ p₁ hp0 hp₁ q hq0 hq D S hS hp Kc hKc
  have hH : BgHyp d L (k + 1) (rhoSepG d L T.m₁) (compWeight L S.a₁) S.ν := by
    subst hS
    exact bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hνpos.le hν
  obtain ⟨Jr, val, 𝒴, Tt, I, -, -, -, -, -, -, hF, hεU, hεpos, hε4, hrest⟩ :=
    hfam k hk N₁ hLN hN ν hνpos hν β hβ ρ hρ p₁ hp0 hp₁ q hq0 hq D S
      hS hp
  obtain ⟨A, -, hhol, -, -, -, -, -, h7, h8, -, -, -, -⟩ := hrest hKc
  have hsub : ∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ((e.1, 0) : physParam N S) ∈
      physVqRho S S.a₁ S.ν T.t ρ q := fun e he =>
    fst_zero_mem_physVqRho S (hq0.trans_le hq) (physVqRho_subset S _ _ _ _ _ he) hq0
  have hV := isOpen_physVqRho S S.a₁ S.ν T.t ρ q hH
  have h𝒰R : ball (0 : ℂ) (3 / 2) ⊆ ball (0 : ℂ) 2 := ball_subset_ball (by norm_num)
  have hR2 : (1 : ℝ) < 2 := by norm_num
  refine ⟨_, inferInstance, _, _, A, by linarith, by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun y Φ => physAct_analyticOnNhd hR2 hsub hhol y Φ
  · exact fun Rg hR y Φ => tiltAct_analyticOnNhd hR hR2 hV isOpen_ball h𝒰R hsub hhol y Φ
  · filter_upwards [h7, h8] with x hx7 hx8
    intro D' hDh hX g hg t ht
    have e7 := hx7 D' hDh hX 1 ⟨zero_le_one, le_rfl⟩
    have e8 := hx8 D' hDh hX g hg t ht
    simp only [Complex.ofReal_one, one_pow, one_mul] at e7
    have hphys : (S.withDatum D' hDh).WoneC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
        (1 : ℝ) x + (S.withDatum D' hDh).WtwoC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
        g t x = ∑ y, (physAct A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g)
          (t : ℂ)).H y ((S.blockSplit T.m₀ hp).restr x) := by
      rw [physAct_total]
      dsimp only
      rw [e7, e8]
      ring
    refine ⟨hphys, fun Rg hR hRg => ?_⟩
    rw [hphys, tiltAct_total_one A hR hRg
      (norm_ofReal_lt_of_mem ht (by norm_num : (1 : ℝ) < 3 / 2) |> fun h => by simpa using h)]
  · exact fun e he y Φ => (physAct_differentiableOn hR2 hsub hhol he y Φ).mono h𝒰R
  · exact fun Rg hR hRg e he => tiltAct_fields hR hRg hR2 h𝒰R hsub hhol he

/-- **The physical and tilted observable activity of the step, as one family.**  At the shared
tower, for each admissible scale and each `Kc ≥ K₀`, the one analytic family `A` of
`activityFamilyAnalytic_fromTower` gives, with `e = (datum, source)` and `𝒰 = ball 0 (3/2)`:

* the amplitude `εH > 0` of `A`, with `2 εH` (the constant of `physAct A e`) at most
  `C_E ℓ^{3p}/√b + q C_F ℓ^p/√b`, `ℓ = log b`, `b = β 3^k`, for all `e` (so uniformly in the
  source ball of radius `q ≤ 1`);
* joint analyticity of `(e, t) ↦ (physAct A e t)_y(Φ)` on `physVq × ball 0 2`, and of
  `(e, t, σ) ↦ (tiltAct A Rg _ 𝒰 e t σ)_y(Φ)` on `physVq × (𝒰 × ball 0 Rg)`;
* one null set outside of which, for every datum `D'` of the fibre `h ≡ h₀`, every source
  `‖g‖₁ < q` and every `t ∈ [0,1]`, `WoneC C 1 + WtwoC C g t` of `S.withDatum D'` is the label
  sum of `physAct A (rawOf D', g) t` and (for `1 < Rg`) that of `tiltAct … (rawOf D', g) t 1`;
* for every `e` of the chart `physVq` and `1 < Rg`: holomorphy in `t ∈ 𝒰` at `σ = 1`,
  holomorphy in `σ` on the disc `ball 0 Rg` at every `t ∈ 𝒰`, and vanishing at `σ = 0`.  The fixed `obsTiltFamily_fromTower` is its corollary. -/
theorem obsTiltFamily_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ (β₀ CE CF : ℝ), 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      StepScaleDataG T k hk N₁ ν β p₁ →
      ∀ S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∀ {Kc : ℝ}, K0 d L T.κ0 ≤ Kc →
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
          Set.univ Lb) (εH : ℝ)
        (A : physParam N S → ℂ → LabelAct Lab (S.blockSplit T.m₀ hp).Ωb εH (2 * T.κdec - 1) T.κ0 Kc),
        0 < εH ∧
        2 * εH ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
          q * CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
        (∀ (y : Lb ⊕ Lb) (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
          AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => (physAct A r.1 r.2).H y Φ)
            (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) 2)) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg) (y : Lb ⊕ Lb) (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
          AnalyticOnNhd ℂ (fun r : physParam N S × ℂ × ℂ =>
            (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2)) r.1 r.2.1 r.2.2).H y Φ)
            (physVq S S.a₁ S.ν T.t q ×ˢ (ball (0 : ℂ) (3 / 2) ×ˢ ball (0 : ℂ) Rg))) ∧
        (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
          ∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x', ∑ i, ‖g x' i‖ < q → ∀ t ∈ Icc (0 : ℝ) 1,
          (S.withDatum D' hDh).WoneC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) (1 : ℝ) x +
            (S.withDatum D' hDh).WtwoC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g t x =
          ∑ y, (physAct A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) (t : ℂ)).H y
            ((S.blockSplit T.m₀ hp).restr x) ∧
          ∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg →
          (S.withDatum D' hDh).WoneC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) (1 : ℝ) x +
            (S.withDatum D' hDh).WtwoC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g t x =
          ∑ y, (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2))
            ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) (t : ℂ) 1).H y
            ((S.blockSplit T.m₀ hp).restr x)) ∧
        (∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ (y : Lb ⊕ Lb) (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
          DifferentiableOn ℂ (fun t : ℂ => (physAct A e t).H y Φ) (ball (0 : ℂ) (3 / 2))) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg → ∀ e ∈ physVq S S.a₁ S.ν T.t q,
          (∀ y Φ, DifferentiableOn ℂ
            (fun t => (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2)) e t 1).H y Φ)
            (ball (0 : ℂ) (3 / 2))) ∧
          (∀ t ∈ ball (0 : ℂ) (3 / 2), ∀ y Φ, DifferentiableOn ℂ
            (fun σ => (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2)) e t σ).H y Φ)
            (ball (0 : ℂ) Rg)) ∧
          (∀ t y Φ, (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2)) e t 0).H y Φ = 0)) := by
  obtain ⟨β₀, CE, CF, hβ₀, hCE, hCF, H⟩ := obsTiltFamily_fromTowerG_rho T hA p
  refine ⟨β₀, CE, CF, hβ₀, hCE, hCF, ?_⟩
  intro k hk N₁ _ hLN hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq D S hS hp Kc hKc
  exact H k hk N₁ hLN hN ν hνpos hν β hβ 1 (by rw [max_self]; linarith) p₁ hp0 hp₁ q hq0 hq D S
    hS hp hKc


/-- At source radius `ρ` (`q ≤ ρ`, `max 1 ρ ≤ β`); the landed theorem is its `ρ = 1` corollary. **The physical and tilted observable activity of the step, as one family.**  At the shared
tower, for each admissible scale and each `Kc ≥ K₀`, the one analytic family `A` of
`activityFamilyAnalytic_fromTower` gives, with `e = (datum, source)` and `𝒰 = ball 0 (3/2)`:

* the amplitude `εH > 0` of `A`, with `2 εH` (the constant of `physAct A e`) at most
  `C_E ℓ^{3p}/√b + q C_F ℓ^p/√b`, `ℓ = log b`, `b = β 3^k`, for all `e` (so uniformly in the
  source ball of radius `q ≤ ρ`);
* joint analyticity of `(e, t) ↦ (physAct A e t)_y(Φ)` on `physVq × ball 0 2`, and of
  `(e, t, σ) ↦ (tiltAct A Rg _ 𝒰 e t σ)_y(Φ)` on `physVq × (𝒰 × ball 0 Rg)`;
* one null set outside of which, for every datum `D'` of the fibre `h ≡ h₀`, every source
  `‖g‖₁ < q` and every `t ∈ [0,1]`, `WoneC C 1 + WtwoC C g t` of `S.withDatum D'` is the label
  sum of `physAct A (rawOf D', g) t` and (for `1 < Rg`) that of `tiltAct … (rawOf D', g) t 1`;
* for every `e` of the chart `physVq` and `1 < Rg`: holomorphy in `t ∈ 𝒰` at `σ = 1`,
  holomorphy in `σ` on the disc `ball 0 Rg` at every `t ∈ 𝒰`, and vanishing at `σ = 0`. -/
theorem obsTiltFamily_fromTower_rho {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ (β₀ CE CF : ℝ), 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β → ∀ ρ : ℝ, max 1 ρ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ ρ →
      StepScaleData T k hk N₁ ν β p₁ →
      ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∀ {Kc : ℝ}, K0 3 3 T.κ0 ≤ Kc →
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ)
        (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 Kc),
        0 < εH ∧
        2 * εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        (∀ (y : Lb ⊕ Lb) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
          AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (physAct A r.1 r.2).H y Φ)
            (physVqRho S S.a₁ S.ν T.t ρ q ×ˢ ball (0 : ℂ) 2)) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg) (y : Lb ⊕ Lb) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
          AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ × ℂ =>
            (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2)) r.1 r.2.1 r.2.2).H y Φ)
            (physVqRho S S.a₁ S.ν T.t ρ q ×ˢ (ball (0 : ℂ) (3 / 2) ×ˢ ball (0 : ℂ) Rg))) ∧
        (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
          ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i, ‖g x' i‖ < q → ∀ t ∈ Icc (0 : ℝ) 1,
          (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (1 : ℝ) x +
            (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
          ∑ y, (physAct A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ)).H y
            ((S.blockSplit 1 hp).restr x) ∧
          ∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg →
          (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (1 : ℝ) x +
            (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
          ∑ y, (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2))
            ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ) 1).H y
            ((S.blockSplit 1 hp).restr x)) ∧
        (∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ (y : Lb ⊕ Lb) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
          DifferentiableOn ℂ (fun t : ℂ => (physAct A e t).H y Φ) (ball (0 : ℂ) (3 / 2))) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg → ∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q,
          (∀ y Φ, DifferentiableOn ℂ
            (fun t => (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2)) e t 1).H y Φ)
            (ball (0 : ℂ) (3 / 2))) ∧
          (∀ t ∈ ball (0 : ℂ) (3 / 2), ∀ y Φ, DifferentiableOn ℂ
            (fun σ => (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2)) e t σ).H y Φ)
            (ball (0 : ℂ) Rg)) ∧
          (∀ t y Φ, (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2)) e t 0).H y Φ = 0)) := by
  obtain ⟨β₀, CE, CF, hβ₀, hCE, hCF, H⟩ := obsTiltFamily_fromTowerG_rho T.toG hA p
  refine ⟨β₀, CE, CF, hβ₀, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ ρ hρ p₁ hp0 hp₁ q hq0 hq D S hS hp Kc hKc
  subst hS
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have hp' : 0 < (T.toG.step k hk N₁ ν β p₁).p₁ := hp
  have G := H k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ ρ hρ p₁ hp0
    (by rw [e]; exact hp₁) q hq0 hq (StepTower.scaleDataG_of_fixed T D)
    (T.toG.step k hk N₁ ν β p₁) rfl hp' hKc
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans (by rw [e])
  subst hϱ' hb'
  intro G
  exact G

/-- **The physical and tilted observable activity of the step, as one family.**  At the shared
tower, for each admissible scale and each `Kc ≥ K₀`, the one analytic family `A` of
`activityFamilyAnalytic_fromTower` gives, with `e = (datum, source)` and `𝒰 = ball 0 (3/2)`:

* the amplitude `εH > 0` of `A`, with `2 εH` (the constant of `physAct A e`) at most
  `C_E ℓ^{3p}/√b + q C_F ℓ^p/√b`, `ℓ = log b`, `b = β 3^k`, for all `e` (so uniformly in the
  source ball of radius `q ≤ 1`);
* joint analyticity of `(e, t) ↦ (physAct A e t)_y(Φ)` on `physVq × ball 0 2`, and of
  `(e, t, σ) ↦ (tiltAct A Rg _ 𝒰 e t σ)_y(Φ)` on `physVq × (𝒰 × ball 0 Rg)`;
* one null set outside of which, for every datum `D'` of the fibre `h ≡ h₀`, every source
  `‖g‖₁ < q` and every `t ∈ [0,1]`, `WoneC C 1 + WtwoC C g t` of `S.withDatum D'` is the label
  sum of `physAct A (rawOf D', g) t` and (for `1 < Rg`) that of `tiltAct … (rawOf D', g) t 1`;
* for every `e` of the chart `physVq` and `1 < Rg`: holomorphy in `t ∈ 𝒰` at `σ = 1`,
  holomorphy in `σ` on the disc `ball 0 Rg` at every `t ∈ 𝒰`, and vanishing at `σ = 0`. -/
theorem obsTiltFamily_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ (β₀ CE CF : ℝ), 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      StepScaleData T k hk N₁ ν β p₁ →
      ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∀ {Kc : ℝ}, K0 3 3 T.κ0 ≤ Kc →
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ)
        (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 Kc),
        0 < εH ∧
        2 * εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        (∀ (y : Lb ⊕ Lb) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
          AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (physAct A r.1 r.2).H y Φ)
            (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) 2)) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg) (y : Lb ⊕ Lb) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
          AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ × ℂ =>
            (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2)) r.1 r.2.1 r.2.2).H y Φ)
            (physVq S S.a₁ S.ν T.t q ×ˢ (ball (0 : ℂ) (3 / 2) ×ˢ ball (0 : ℂ) Rg))) ∧
        (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
          ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i, ‖g x' i‖ < q → ∀ t ∈ Icc (0 : ℝ) 1,
          (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (1 : ℝ) x +
            (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
          ∑ y, (physAct A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ)).H y
            ((S.blockSplit 1 hp).restr x) ∧
          ∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg →
          (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (1 : ℝ) x +
            (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
          ∑ y, (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2))
            ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ) 1).H y
            ((S.blockSplit 1 hp).restr x)) ∧
        (∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ (y : Lb ⊕ Lb) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
          DifferentiableOn ℂ (fun t : ℂ => (physAct A e t).H y Φ) (ball (0 : ℂ) (3 / 2))) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg → ∀ e ∈ physVq S S.a₁ S.ν T.t q,
          (∀ y Φ, DifferentiableOn ℂ
            (fun t => (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2)) e t 1).H y Φ)
            (ball (0 : ℂ) (3 / 2))) ∧
          (∀ t ∈ ball (0 : ℂ) (3 / 2), ∀ y Φ, DifferentiableOn ℂ
            (fun σ => (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2)) e t σ).H y Φ)
            (ball (0 : ℂ) Rg)) ∧
          (∀ t y Φ, (tiltAct A Rg hR (ball (0 : ℂ) (3 / 2)) e t 0).H y Φ = 0)) := by
  obtain ⟨β₀, CE, CF, hβ₀, hCE, hCF, H⟩ := obsTiltFamily_fromTower_rho T hA p
  refine ⟨β₀, CE, CF, hβ₀, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq D S hS hp Kc hKc
  exact H k hk N₁ h3N hN ν hνpos hν β hβ 1 (by rw [max_self]; linarith) p₁ hp0 hp₁ q hq0 hq D S
    hS hp hKc

end Tower

end Balaban.Inhabited
