/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgMomTorus
public import Balaban.LargeField.Def7v2

/-!
# The radial coefficient: `a_j` and `v₁^{(j)}` (Q13-GROUPED §1, `regionalRadialCoefficient`)

DICTIONARY_PLACEHOLDER
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Filter

section Line

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- A differentiable function has, along a line, the derivative `fderiv f p v`. -/
theorem hasDerivAt_line {f : E → ℂ} {p : E} (hf : DifferentiableAt ℂ f p) (v : E) :
    HasDerivAt (fun s : ℂ => f (p + s • v)) (fderiv ℂ f p v) 0 := by
  have h1 : HasDerivAt (fun s : ℂ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add p
  have h2 : HasFDerivAt f (fderiv ℂ f p) (p + (0 : ℂ) • v) := by
    simpa using hf.hasFDerivAt
  exact h2.comp_hasDerivAt 0 h1

/-- Two differentiable functions that agree along two lines have the same derivatives along them
(the chain rule through the reindexing `s ↦ p + s v ↦ q + s w`). -/
theorem fderiv_eq_of_line {f : E → ℂ} {g : F → ℂ} {p : E} {q : F} {v : E} {w : F}
    (hf : DifferentiableAt ℂ f p) (hg : DifferentiableAt ℂ g q)
    (h : ∀ s : ℂ, f (p + s • v) = g (q + s • w)) : fderiv ℂ f p v = fderiv ℂ g q w := by
  have h1 := hasDerivAt_line hf v
  have h2 := hasDerivAt_line hg w
  have : (fun s : ℂ => f (p + s • v)) = fun s : ℂ => g (q + s • w) := funext h
  rw [this] at h1
  exact h1.unique h2

end Line

section Termwise

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ}
  {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρd : (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ} {ρ : ℝ}

/-- **T2: the tensor `tensA` of the centre-`y` class term is the local coefficient `v1Loc`.**
For a polymer `X'` of the lift (`X'` does not wind, `Ypoly j X'` is a polymer of `𝒟_j`, `y ∈ X'`),
a block corner `u` whose centred position lies in `X'`, and a source form `Et` of the term in the
variable `b = ν_j h` (the shape of `D1Corr.src_pos`), the derivative of `EauxC` at the reference
point `(e_{i₀}, ν_j e_{i₀})` in the coordinate `ψ_{i₀}(unlift u)` is `v1Loc` at the block `u`. -/
theorem LiftCtx.tensA_EauxC_eq_v1Loc (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ : Fin N}
    {y : SmallField.Site d} {X' : Finset (SmallField.Site d)} (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (hy : y ∈ X')
    {u : Localization.CTorus d L N₁ m₁ k} (hu : Aligned (L ^ j) u)
    (huX : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u ∈ X')
    (Et : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (hEt : ∀ (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      Et Ψ (constFld b) = Tm.E j (blockPt j y) (Ypoly j X') Ψ
        (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b))) :
    tensA i₀ (nuIdeal L k (ν k) j) X' (EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X')
        ⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u, huX⟩ =
      v1Loc Et j (nuIdeal L k (ν k) j) (Pi.single i₀ 1) u := by
  have hjk := ctx.jk
  have hνj : 0 < nuIdeal L k (ν k) j := by
    have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have := ctx.nu_pos
    unfold nuIdeal; positivity
  have hνc : ((nuIdeal L k (ν k) j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
  have h2 : AnalyticAt ℂ (EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X')
      (refPt i₀ (nuIdeal L k (ν k) j) X') :=
    ctx.analyticAt_EauxC i₀ hpd y hnw hy (Metric.mem_ball_self ctx.rho_pos)
  have h1 := ctx.analyticAt_E i₀ (blockPt j y) hpd (blockPt_mem_Ypoly hjk hnw hy)
  have hEt' : (fun ψ : Fld d L N₁ m₁ k N =>
      Et ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ)))) =
      fun ψ => Tm.E j (blockPt j y) (Ypoly j X') ψ (eFld d L N₁ m₁ k N i₀) := by
    funext ψ
    rw [hEt, smul_smul, inv_mul_cancel₀ hνc, one_smul]
  unfold tensA v1Loc
  rw [hEt']
  refine fderiv_eq_of_line h2.differentiableAt h1.differentiableAt (fun s => ?_)
  have hcu : ∀ z : Localization.CTorus d L N₁ m₁ k,
      (cbase (L ^ j) z = u ↔ unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z =
        unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u) := fun z => by
    rw [cbase_eq_iff_jBlock hjk hu z, unlift_eq_iff]
  set c : Cfg d N X' := refPt i₀ (nuIdeal L k (ν k) j) X' +
    s • (Pi.single (Sum.inl (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u, huX⟩, i₀)) 1 :
      Cfg d N X') with hc
  have hf : fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' c =
      eFld d L N₁ m₁ k N i₀ + s • blockDirV L j u (Pi.single i₀ 1) := by
    funext z i
    by_cases hz : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z ∈ X'
    · simp only [fieldOf, hz, dite_true, hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply, refPt_inl, blockDirV, eFld, constFld, hcu z,
        Sum.inl.injEq, Prod.mk.injEq, Subtype.mk.injEq]
      by_cases h : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z =
          unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u <;>
        by_cases hi : i = i₀ <;> simp [h, hi]
    · have hu0 : blockDirV L j u (Pi.single i₀ 1 : Fin N → ℂ) z i = 0 := by
        have hne : ¬ cbase (L ^ j) z = u := fun h => hz ((hcu z).1 h ▸ huX)
        simp [blockDirV, hne]
      simp only [fieldOf, hz, dite_false, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eFld,
        constFld, hu0]
      ring
  have hh : hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (ν k) j) X' c =
      eFld d L N₁ m₁ k N i₀ := by
    funext z i
    simp only [hOf, hc, Pi.add_apply, Pi.smul_apply, eFld, constFld]
    rw [refPt_inr]
    simp only [Pi.single_apply, smul_eq_mul]
    simp only [reduceCtorEq, ite_false, mul_zero, add_zero]
    field_simp
  show Tm.E j (blockPt j y) (Ypoly j X') (fieldOf j i₀ X' c) (hOf (nuIdeal L k (ν k) j) X' c) = _
  rw [hf, hh]

end Termwise

end Balaban.LargeField.Def7v2
