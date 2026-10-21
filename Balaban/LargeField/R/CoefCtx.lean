/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RadialCoefficientAvg
public import Balaban.SmallField.Def6v2Birth
public import Balaban.SmallField.Def6v2BirthRadius

/-!
# The coefficient context: what the thermodynamic limit of `v₁`, `v₂` reads from the class

The landed limit of the radial coefficient (`RadialCoefficientLimit`) reads the class through
`LiftCtx`, which carries a member of `Def6.IsSF` (the landed domain, one background mass for all
levels).  The coefficient limit uses only the following facts about one torus and one level `j`:

* the term clauses of the class on a field domain `Dom` (analyticity, bound, locality, real
  rotation invariance);
* that the configurations of the ball of radius `ρ` around the reference point `(e_{i₀}, ν_j e_{i₀})`
  (in the variables `ψ`, `b = ν_j h`) lie in `Dom`;
* that `Dom` is invariant under real orthogonal matrices.

`CoefCtx` is this list.  `LiftCtx.coef` shows that the landed context is an instance;
`IsSFFamily2On` on the birth domains `sfDom` gives another one (`Birth.lean`), with the radius
divided by the factor `e²` between the birth mass of the level and the ideal mass of the current
scale.
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Filter Matrix Metric

section Ctx

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The coefficient context** at one torus `N₁` and one level `j`: the term clauses of the class on
the field domain `Dom`, the positivity of the ideal mass, the inclusion in `Dom` of the data
`(ψ, b = ν_j h)` of the ball of radius `ρ` around the reference point (stated for the block-constant
fields `ψ` within `ρ` of `e_{i₀}` and the sources `b` within `ρ` of `ν_j e_{i₀}`, and every
polymer `X` of `𝒟_j`), and the invariance of `Dom` under real orthogonal matrices. -/
structure CoefCtx (P : Consts) (νk : ℝ) (Dom : FieldDom d L N₁ m₁ k N ϱ)
    (Tm : Terms d L N₁ m₁ k N ϱ) (j : ℕ) (ρ : ℝ) : Prop where
  tc : SFTermClauses P Dom Tm
  j1 : 1 ≤ j
  jk : j ≤ k
  nu_pos : 0 < νk
  rho_pos : 0 < ρ
  dom : ∀ (i₀ : Fin N) (X : Set (Localization.CTorus d L N₁ m₁ k)), IsPolyDom P.m₀ j X →
    ∀ (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
    (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
    (∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x') →
    (∀ i, ‖b i - (nuIdeal L k νk j : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i‖ < ρ) →
    Dom.dom j (Tm.gs j X) Ψ (fun _ i => b i / (nuIdeal L k νk j : ℂ))
  rotDom : ∀ (Q : Matrix (Fin N) (Fin N) ℝ), Qᵀ * Q = 1 → ∀ (X : Set (Localization.CTorus d L N₁ m₁ k))
    (Ψ h : Fld d L N₁ m₁ k N), Dom.dom j (Tm.gs j X) Ψ h →
    Dom.dom j (Tm.gs j X) (rotField (cmat Q) Ψ) (rotField (cmat Q) h)

variable {P : Consts} {νk : ℝ} {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {j : ℕ} {ρ : ℝ}

theorem CoefCtx.nuj_pos (ctx : CoefCtx P νk Dom Tm j ρ) : 0 < nuIdeal L k νk j := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have := ctx.nu_pos
  unfold nuIdeal; positivity

/-- The ball around the reference point lies in the domain of the term. -/
theorem CoefCtx.ball_dom (ctx : CoefCtx P νk Dom Tm j ρ) (i₀ : Fin N) {X' : Finset (SmallField.Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) {c : Cfg d N X'}
    (hc : c ∈ ball (refPt i₀ (nuIdeal L k νk j) X') ρ) :
    Dom.dom j (Tm.gs j (Ypoly j X')) (fieldOf j i₀ X' c) (hOf (nuIdeal L k νk j) X' c) :=
  ctx.dom i₀ _ hX (fieldOf j i₀ X' c) (fun i => c (Sum.inr i))
    (fun x i => fieldOf_sub_le hc ctx.rho_pos.le x i) (fun _ _ h => fieldOf_block c h)
    (fun i => by
      have := (dist_le_pi_dist c (refPt i₀ (nuIdeal L k νk j) X') (Sum.inr i)).trans_lt
        (mem_ball.1 hc)
      rwa [dist_eq_norm, refPt_inr] at this)

/-- The constant field `e_{i₀}` with the source `ν_j e_{i₀}` lies in the domain of every polymer. -/
theorem CoefCtx.const_dom (ctx : CoefCtx P νk Dom Tm j ρ) (i₀ : Fin N)
    {X : Set (Localization.CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) :
    Dom.dom j (Tm.gs j X) (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) := by
  have hνc : ((nuIdeal L k νk j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ctx.nuj_pos.ne'
  have h := ctx.dom i₀ X hX (eFld d L N₁ m₁ k N i₀)
    (fun i => (nuIdeal L k νk j : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i)
    (fun x i => by simp [eFld, constFld, ctx.rho_pos.le]) (fun _ _ _ => rfl)
    (fun i => by simpa using ctx.rho_pos)
  have e : (fun (_ : Localization.CTorus d L N₁ m₁ k) (i : Fin N) =>
      (nuIdeal L k νk j : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i / (nuIdeal L k νk j : ℂ)) =
      eFld d L N₁ m₁ k N i₀ := by
    funext x i
    simp [eFld, constFld, hνc]
  rwa [e] at h

/-- The line `e_{i₀} + s δ_u e_{i₀}` lies in the domain of the term, for `|s| ≤ ρ`. -/
theorem CoefCtx.line_dom (ctx : CoefCtx P νk Dom Tm j ρ) (i₀ : Fin N)
    {X : Set (Localization.CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X)
    (u : Localization.CTorus d L N₁ m₁ k) {s : ℂ} (hs : ‖s‖ ≤ ρ) :
    Dom.dom j (Tm.gs j X) (eFld d L N₁ m₁ k N i₀ + s • blockDirV L j u (Pi.single i₀ 1))
      (eFld d L N₁ m₁ k N i₀) := by
  have hνc : ((nuIdeal L k νk j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ctx.nuj_pos.ne'
  have h := ctx.dom i₀ X hX (eFld d L N₁ m₁ k N i₀ + s • blockDirV L j u (Pi.single i₀ 1))
    (fun i => (nuIdeal L k νk j : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i)
    (fun z i => ?_) (fun z z' hz => ?_) (fun i => by simpa using ctx.rho_pos)
  · have e : (fun (_ : Localization.CTorus d L N₁ m₁ k) (i : Fin N) =>
        (nuIdeal L k νk j : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i / (nuIdeal L k νk j : ℂ)) =
        eFld d L N₁ m₁ k N i₀ := by
      funext x i
      simp [eFld, constFld, hνc]
    rwa [e] at h
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, eFld, constFld, add_sub_cancel_left]
    rw [norm_mul]
    calc ‖s‖ * ‖(blockDirV L j u (Pi.single i₀ 1 : Fin N → ℂ)) z i‖ ≤ ρ * 1 :=
          mul_le_mul hs (norm_blockDirV_single_le u i₀ z i) (norm_nonneg _) ctx.rho_pos.le
      _ = ρ := mul_one _
  · simp only [Pi.add_apply, Pi.smul_apply, eFld, constFld]
    unfold blockDirV
    rw [cbase_pow_eq_of_jBlock ctx.jk hz]

/-- Analyticity of the term in `ψ` at the constant reference field. -/
theorem CoefCtx.analyticAt_E (ctx : CoefCtx P νk Dom Tm j ρ) (i₀ : Fin N)
    (y : Localization.CTorus d L N₁ m₁ k) {X : Set (Localization.CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X) :
    AnalyticAt ℂ (fun ψ : Fld d L N₁ m₁ k N => Tm.E j y X ψ (eFld d L N₁ m₁ k N i₀))
      (eFld d L N₁ m₁ k N i₀) := by
  have h1 := ctx.tc.analyticE j ctx.j1 ctx.jk y X hX hy
    (eFld d L N₁ m₁ k N i₀, eFld d L N₁ m₁ k N i₀) (ctx.const_dom i₀ hX)
  have h2 : AnalyticAt ℂ (fun ψ : Fld d L N₁ m₁ k N => (ψ, eFld d L N₁ m₁ k N i₀))
      (eFld d L N₁ m₁ k N i₀) := AnalyticAt.prod analyticAt_id analyticAt_const
  exact AnalyticAt.comp (f := fun ψ : Fld d L N₁ m₁ k N => (ψ, eFld d L N₁ m₁ k N i₀)) h1 h2

/-- Analyticity of the centred term on the ball. -/
theorem CoefCtx.analyticAt_EauxC (ctx : CoefCtx P νk Dom Tm j ρ) (i₀ : Fin N)
    {X' : Finset (SmallField.Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (y : SmallField.Site d) (hnw : NonWind L N₁ m₁ k j X') (hy : y ∈ X') {u₀ : Cfg d N X'}
    (hu : u₀ ∈ ball (refPt i₀ (nuIdeal L k νk j) X') ρ) :
    AnalyticAt ℂ (EauxC Tm j i₀ (nuIdeal L k νk j) y X') u₀ := by
  have hE := ctx.tc.analyticE j ctx.j1 ctx.jk (blockPt j y) (Ypoly j X') hX
    (blockPt_mem_Ypoly ctx.jk hnw hy)
    (fieldOf j i₀ X' u₀, hOf (nuIdeal L k νk j) X' u₀) (ctx.ball_dom i₀ hX hu)
  exact AnalyticAt.comp (g := fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
    Tm.E j (blockPt j y) (Ypoly j X') p.1 p.2)
    (f := fun c : Cfg d N X' => ((fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' c,
      hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k νk j) X' c) :
        Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N)) (x := u₀) hE
    (analyticAt_fp j i₀ (nuIdeal L k νk j) X' u₀)

/-- The bound of the centred term on the ball. -/
theorem CoefCtx.norm_EauxC_le (ctx : CoefCtx P νk Dom Tm j ρ) (i₀ : Fin N)
    {X' : Finset (SmallField.Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (y : SmallField.Site d) (hnw : NonWind L N₁ m₁ k j X') (hy : y ∈ X') {c : Cfg d N X'}
    (hc : c ∈ ball (refPt i₀ (nuIdeal L k νk j) X') ρ) :
    ‖EauxC Tm j i₀ (nuIdeal L k νk j) y X' c‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly j X')) :=
  ctx.tc.boundE j ctx.j1 ctx.jk (blockPt j y) (Ypoly j X') hX (blockPt_mem_Ypoly ctx.jk hnw hy) _ _
    (ctx.ball_dom i₀ hX hc)

end Ctx

end Balaban.LargeField.Def7v2
