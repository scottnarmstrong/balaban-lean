/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormTermwiseCtx

/-!
# Lemma 3.2 (iii): the termwise bound, in the context of the landed analysis

In the context `CtxTw` (premises without (H.5), data (Σ1), (Σ2), a frame):

* `CtxTw.itw_eq`: `I(y,X) = Dlt X + (𝓔(y,X; ψ(y), b) - T_X)`, where `Dlt` is the landed per-term
  quantity (`𝓔 - 𝓔(const) - A_X + L_X`) and `L_X = -Φ_{y,X}`;
* `CtxTw.rem_bound`: `‖𝓔(y,X; ψ(y), b) - T_X‖ ≤ 12 |X| E₀ e^{-κ d_j(X)} (Z₀/ρ)²` (first-order
  Taylor remainder at the reference point, or the crude bound when `Z₀ > ρ/2`);
* `CtxTw.itw_bound_raw`: the per-term bound before the polynomial weights are absorbed.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

section CtxTw

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)} {ψ : Site d → Spin N} {b : Spin N}
  {σ ε K₂ : ℝ} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}

theorem CtxTw.uInv_eq (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) : uInv ψ = u :=
  c.frame.uInv_eq c.τle

theorem CtxTw.alpha_eq (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) :
    ((R.mulVec (ψ 0) - Pi.single i₀ 1 : Spin N) i₀) = uInv ψ - 1 := by
  rw [c.uInv_eq, c.frame.rot0]
  simp

theorem CtxTw.beta_eq (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) :
    ((R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) i₀) = vInv ψ b - ν := by
  have hu := c.frame.u_ne c.τle
  unfold vInv
  rw [c.uInv_eq, Pi.sub_apply, c.frame.mulVec_apply hu]
  simp

/-- The expansion of the potential term: `Ttw` is the first-order Taylor polynomial at the
reference point in the rotated variables. -/
theorem CtxTw.ttw_eq (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) (X : Finset (Site d)) :
    Ttw T i₀ ν X ψ b = T.term X (refPt i₀ ν X) +
      ((∑ x : ↥X, tensA i₀ ν X (T.term X) x) * ((R.mulVec (ψ 0) - Pi.single i₀ 1 : Spin N) i₀) +
        ((R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) i₀) *
          fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1)) := by
  rw [c.alpha_eq, c.beta_eq]
  unfold Ttw
  ring

theorem CtxTw.itw_eq (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) (X : Finset (Site d)) :
    Itw T i₀ i₁ ν X ψ b = Dlt T i₀ i₁ ν R ψ b X +
      (T.term X (pack X (fun _ => ψ 0) b) - Ttw T i₀ ν X ψ b) := by
  unfold Itw
  rw [c.frame.phitw_eq c.τle, Dlt_eq]
  ring

theorem CtxTw.rem_bound (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) :
    ‖T.term X (pack X (fun _ => ψ 0) b) - Ttw T i₀ ν X ψ b‖ ≤
      12 * (X.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X)) * (sZ0 N σ ε / ρ) ^ 2 := by
  have hρ := c.ρpos
  have hok := c.termOK hX
  have hM := c.hM hX
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by have := c.E0nn; positivity
  have hcard : (1 : ℝ) ≤ X.card := by exact_mod_cast c.card_pos hX
  have hz0 : 0 ≤ sZ0 N σ ε := by
    have := c.εpos; have := c.σpos; unfold sZ0 cC1; positivity
  by_cases hZ0 : sZ0 N σ ε ≤ ρ / 2
  · have h := c.potential_term hX hZ0
    rw [c.ttw_eq]
    have e : T.term X (pack X (fun _ => ψ 0) b) - (T.term X (refPt i₀ ν X) +
        ((∑ x : ↥X, tensA i₀ ν X (T.term X) x) * ((R.mulVec (ψ 0) - Pi.single i₀ 1 : Spin N) i₀) +
          ((R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) i₀) *
            fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1))) =
        T.term X (pack X (fun _ => ψ 0) b) - T.term X (refPt i₀ ν X) -
        ((∑ x : ↥X, tensA i₀ ν X (T.term X) x) * ((R.mulVec (ψ 0) - Pi.single i₀ 1 : Spin N) i₀) +
          ((R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) i₀) *
            fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1)) := by ring
    rw [e]
    refine h.trans ?_
    have : 0 ≤ M * (sZ0 N σ ε / ρ) ^ 2 := by positivity
    nlinarith
  · push Not at hZ0
    have hq : 1 / 2 < sZ0 N σ ε / ρ := by rw [lt_div_iff₀ hρ]; linarith
    -- the crude bound
    set α : ℂ := uInv ψ - 1 with hα
    set β : ℂ := vInv ψ b - ν with hβ
    have hαb : ‖α‖ ≤ sZ0 N σ ε := by
      rw [hα, c.uInv_eq]
      refine c.frame.u_close.trans ?_
      unfold sZ0 cC1
      have : 0 ≤ σ ^ 2 * ε := by have := c.εpos; positivity
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    have hβb : ‖β‖ ≤ sZ0 N σ ε := by
      rw [hβ, ← c.beta_eq]
      have h1 : ‖zcfg X i₀ ν ψ b R‖ ≤ sZ0 N σ ε := by unfold sZ0 cC1; exact c.zc_le X
      refine le_trans ?_ h1
      have := norm_le_pi_norm (zcfg X i₀ ν ψ b R) (Sum.inr i₀)
      simpa [zcfg, pack] using this
    have hg : ‖T.term X (pack X (fun _ => ψ 0) b)‖ ≤ M :=
      c.hyp.bdd_dom X hX ((fun _ => ψ 0), b) c.dat.mem_const
    have hv0 : ‖T.term X (refPt i₀ ν X)‖ ≤ M := hM _ (mem_ball_self hρ)
    have hs : ‖∑ x : ↥X, tensA i₀ ν X (T.term X) x‖ ≤ (X.card : ℝ) * (M / ρ) := by
      have := norm_sum_le_card _ fun x => hok.norm_tensA_le hM x
      rwa [Fintype.card_coe] at this
    have hd : ‖fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1)‖ ≤ M / ρ := by
      have h1 := norm_fderiv_apply_le hρ hok.analytic_ball hM
        (Pi.single (Sum.inr i₀) (1 : ℂ) : Cfg d N X)
      have h2 := norm_single_one_le (Sum.inr i₀ : Idx d N X)
      refine h1.trans ?_
      calc M * ‖(Pi.single (Sum.inr i₀) (1 : ℂ) : Cfg d N X)‖ / ρ ≤ M * 1 / ρ :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hM0) hρ.le
        _ = M / ρ := by rw [mul_one]
    have hT : ‖Ttw T i₀ ν X ψ b‖ ≤ M + sZ0 N σ ε * ((X.card : ℝ) * (M / ρ)) +
        sZ0 N σ ε * (M / ρ) := by
      unfold Ttw
      calc _ ≤ ‖T.term X (refPt i₀ ν X)‖ + ‖α * ∑ x : ↥X, tensA i₀ ν X (T.term X) x‖ +
            ‖β * fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1)‖ :=
              (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ M + sZ0 N σ ε * ((X.card : ℝ) * (M / ρ)) + sZ0 N σ ε * (M / ρ) := by
            rw [norm_mul, norm_mul]
            gcongr
    have hr : ‖T.term X (pack X (fun _ => ψ 0) b) - Ttw T i₀ ν X ψ b‖ ≤
        M + (M + sZ0 N σ ε * ((X.card : ℝ) * (M / ρ)) + sZ0 N σ ε * (M / ρ)) :=
      (norm_sub_le _ _).trans (add_le_add hg hT)
    refine hr.trans ?_
    set q : ℝ := sZ0 N σ ε / ρ with hqdef
    have e1 : sZ0 N σ ε * ((X.card : ℝ) * (M / ρ)) = (X.card : ℝ) * M * q := by
      rw [hqdef]; field_simp
    have e2 : sZ0 N σ ε * (M / ρ) = M * q := by rw [hqdef]; field_simp
    rw [e1, e2]
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q ≤ 2 * q ^ 2 := by nlinarith
    have hq2 : 1 ≤ 4 * q ^ 2 := by nlinarith
    have hP0 : 0 ≤ (X.card : ℝ) := by linarith
    calc M + (M + (X.card : ℝ) * M * q + M * q)
        ≤ 4 * M * q ^ 2 + (4 * M * q ^ 2 + (X.card : ℝ) * M * (2 * q ^ 2) + M * (2 * q ^ 2)) := by
          gcongr <;> nlinarith [mul_nonneg hM0 hq0]
      _ ≤ 12 * (X.card : ℝ) * M * q ^ 2 := by nlinarith [mul_nonneg hM0 (sq_nonneg q)]

theorem CtxTw.itw_bound_raw (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R)
    {Λ Kc α₁ Cs Ct : ℝ} (hCs0 : 0 ≤ Cs) (hCt0 : 0 ≤ Ct)
    (hα0 : 0 < α₁) (hα1 : α₁ < 1)
    (hCs : ∀ (M ρ ν σ r K₂ t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → ρ ≤ 1 → 0 < r →
      r ≤ Λ → 0 ≤ ν → ν ≤ σ ^ 2 → 1 ≤ t → 1 ≤ P → 0 ≤ K₂ → K₂ ≤ Kc * Sσ * (r * ρ) →
      SigPow σ α₁ Tσ Sσ →
      smallBnd N A M ρ ν σ (r * ρ) K₂ t P ≤ Cs * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hCt : ∀ (M ρ σ r t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → 0 < r → r ≤ Λ → 1 ≤ t →
      1 ≤ P → 1 < 2 * (cC1 N + cK1 N A) * t * σ * r → SigPow σ α₁ Tσ Sσ →
      tailBnd N A M ρ σ (r * ρ) t P ≤ Ct * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hεΛ : ε ≤ Λ * ρ) (hK : K₂ ≤ Kc * σ ^ (2 - α₁) * ε) {X : Finset (Site d)}
    (hX : X ∈ T.polys) :
    ‖Itw T i₀ i₁ ν X ψ b‖ ≤
      (Cs + Ct + 12 * cC1 N ^ 2) *
        (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / ρ) ^ 2) := by
  have hρ := c.ρpos
  have hd0 : 0 ≤ T.dist X := c.hyp.dist_nonneg X hX
  have h1 := c.dlt_bound_raw hCs0 hCt0 hα0 hα1 hCs hCt hεΛ hK hX
  have h2 := c.rem_bound hX
  have hP : (1 : ℝ) ≤ X.card := by exact_mod_cast c.card_pos hX
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X) := by have := c.E0nn; positivity
  have ht6 : (1 : ℝ) ≤ (1 + T.dist X) ^ 6 := one_le_pow₀ (by linarith)
  have hT0 : 0 ≤ σ ^ (3 - α₁) := (Real.rpow_pos_of_pos c.σpos _).le
  have hS := sigPow σ α₁ c.σpos c.σle hα0 hα1
  have hs4 : σ ^ 4 ≤ σ ^ (3 - α₁) := hS.quart
  have hsq : (sZ0 N σ ε / ρ) ^ 2 = cC1 N ^ 2 * (σ ^ 4 * (ε / ρ) ^ 2) := by
    unfold sZ0; field_simp
  have hC0 : 0 ≤ cC1 N := by unfold cC1; positivity
  have hr2 : 12 * (X.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X)) * (sZ0 N σ ε / ρ) ^ 2 ≤
      12 * cC1 N ^ 2 * (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / ρ) ^ 2) := by
    rw [hsq]
    have hq : 0 ≤ (ε / ρ) ^ 2 := sq_nonneg _
    have hPP : (X.card : ℝ) ≤ (X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6 := by nlinarith
    calc 12 * (X.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X)) * (cC1 N ^ 2 * (σ ^ 4 * (ε / ρ) ^ 2))
        = 12 * cC1 N ^ 2 * (E₀ * Real.exp (-κ * T.dist X) * (X.card : ℝ)) * (σ ^ 4 * (ε / ρ) ^ 2) := by
          ring
      _ ≤ 12 * cC1 N ^ 2 * (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
          (σ ^ (3 - α₁) * (ε / ρ) ^ 2) := by
          have : 0 ≤ 12 * cC1 N ^ 2 := by positivity
          gcongr
  rw [c.itw_eq]
  refine (norm_add_le _ _).trans ?_
  have hcomb : (Cs + Ct) * (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
      (σ ^ (3 - α₁) * (ε / ρ) ^ 2) +
      12 * cC1 N ^ 2 * (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / ρ) ^ 2) =
      (Cs + Ct + 12 * cC1 N ^ 2) *
        (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / ρ) ^ 2) := by ring
  rw [← hcomb]
  exact add_le_add h1 (h2.trans hr2)

end CtxTw

end Balaban.SmallField
