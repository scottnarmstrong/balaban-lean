/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormPinJet
public import Balaban.SmallField.RenormAnisoInhabited

/-!
# PIN-I6: the strong old-term bridge and inhabitation of the certificate

* `CtxAniso.pinJetTerm`, `CtxAniso.pinJet`: bounded analyticity of the old term on `TubeAniso`
  (`PremisesTermAniso`) implies the reference-jet certificate, so the landed anisotropic class is
  a special case of the corrected theorem (PIN-I6 §3, the "strong old-term bridge");
* `termwise_irrelevant_pin_of_aniso`: `termwise_irrelevant_aniso` recovered from
  `termwise_irrelevant_pin` through the bridge;
* `nonempty_pinJet`: the certificate is inhabited (hard rule 10) for the constant-term family
  `constTerms` and every admissible choice of the numerical parameters.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

section Bridge

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν r E₀ κ A K₀ Λ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)} {ψ : Site d → Spin N} {b : Spin N}
  {σ ε K₂ : ℝ} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}

/-- **The strong old-term bridge**: bounded analyticity of an old term on `TubeAniso` gives the
reference-jet certificate of that term. -/
theorem CtxAniso.pinJetTerm (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) :
    PinJetTerm T i₀ i₁ ν r E₀ κ A Λ ψ b σ ε R X := by
  have hr := c.rpos
  have han := c.analytic_poly hX
  have hM := c.hM hX
  have hne : i₁ ≠ i₀ := c.hyp.ne.symm
  refine ⟨⟨r ^ 2, c.termOK hX⟩, fun x => aniso_norm_tensA_le hr han hM x,
    fun x x' => aniso_norm_D2_basis_le hr han hM (anisoWt_inl _) (anisoWt_inl _),
    fun x x' => aniso_norm_D2_basis_le hr han hM (anisoWt_inl _) (anisoWt_inl _),
    fun x => aniso_norm_D2_basis_le hr han hM (anisoWt_inr_ne hne) (anisoWt_inl _), ?_,
    c.constant_potential_aniso hX⟩
  intro hs
  have hd0 : 0 ≤ T.dist X := c.hyp.dist_nonneg X hX
  set t : ℝ := 1 + T.dist X with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hσ := c.σpos
  have hε := c.εpos
  have hΛ := c.Λnn
  have hK1 : 0 ≤ cK1 N A := by unfold cK1; have := c.Ann; positivity
  have hCZ : 0 ≤ cZA N Λ := cZA_nonneg N hΛ
  have hτ0 : 0 ≤ σ ^ 2 * ε := by positivity
  have hD0 : 0 ≤ sD N A σ ε t := by unfold sD; positivity
  have hZ0n : 0 ≤ sZ0A N Λ σ ε := by unfold sZ0A; positivity
  have hDφ : ∀ x ∈ X, ‖rotDiff R ψ x‖ ≤ sD N A σ ε t := by
    intro x hx
    refine (c.rotDiff_le x).trans ?_
    unfold sD cK1
    have := c.l1_le hX hx
    have h2 : 0 ≤ σ * ε := by positivity
    calc (N : ℝ) * 40 * ((l1 x : ℝ) * (σ * ε)) ≤ N * 40 * (A * t * (σ * ε)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ h2) (by positivity)
          simpa [ht] using this
      _ = _ := by ring
  have hpk : anisoGauge i₀ r X (pack X (rotDiff R ψ) 0) ≤ sD N A σ ε t / r :=
    anisoGauge_pack_zero_le hr _ hD0 hDφ
  have hzc : anisoGauge i₀ r X (zcfg X i₀ ν ψ b R) ≤ sZ0A N Λ σ ε / r := c.zc_gauge_le X
  have hz : anisoGauge i₀ r X (zcfg X i₀ ν ψ b R + pack X (rotDiff R ψ) 0) ≤
      (sZ0A N Λ σ ε + sD N A σ ε t) / r := by
    rw [add_div]
    exact (anisoGauge_add_le _ _).trans (add_le_add hzc hpk)
  have hsum : sZ0A N Λ σ ε + sD N A σ ε t ≤ r / 2 := by
    refine le_trans ?_ hs
    unfold sZ0A sD
    have h1 : σ ^ 2 * ε ≤ t * σ * ε := by
      have : σ ≤ 1 := c.σle
      nlinarith [mul_pos hσ hε]
    nlinarith [mul_pos hσ hε, mul_nonneg hCZ (sub_nonneg.mpr h1)]
  have hZ : (sZ0A N Λ σ ε + sD N A σ ε t) / r ≤ 1 / 2 := by
    rw [div_le_iff₀ hr]; linarith
  have hZ0 : sZ0A N Λ σ ε / r ≤ 1 / 2 := by
    rw [div_le_iff₀ hr]; linarith
  have hpoly1 : rotCfgL R X (pack X ψ b) ∈ polyAniso i₀ ν r X := by
    rw [rotCfgL_pack, pack_rot_eq, refPt_add_mem_polyAniso_iff hr]
    linarith
  have hpoly2 : rotCfgL R X (pack X (fun _ => ψ 0) b) ∈ polyAniso i₀ ν r X := by
    rw [rotCfgL_pack, pack_const_rot_eq, refPt_add_mem_polyAniso_iff hr]
    linarith
  have e1 := c.term_rot hX hpoly1
  have e2 := c.term_rot hX hpoly2
  rw [rotCfgL_pack, pack_rot_eq] at e1
  rw [rotCfgL_pack, pack_const_rot_eq] at e2
  have hT := aniso_taylor_diff hr han hM (z := zcfg X i₀ ν ψ b R + pack X (rotDiff R ψ) 0)
    (zc := zcfg X i₀ ν ψ b R) (hz.trans hZ) (hzc.trans hZ0)
  rw [add_sub_cancel_left] at hT
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X) := by have := c.E0nn; positivity
  refine ⟨e1, e2, ?_, ?_⟩
  · refine hT.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (anisoGauge_nonneg _) hz 3)
        (by positivity)
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (anisoGauge_nonneg _) hzc 3)
        (by positivity)
  · refine (aniso_norm_D2_le hr han hM _ _).trans ?_
    have := mul_le_mul hzc hpk (anisoGauge_nonneg _) (le_trans (anisoGauge_nonneg _) hzc)
    calc 4 * (E₀ * Real.exp (-κ * T.dist X)) * anisoGauge i₀ r X (zcfg X i₀ ν ψ b R) *
          anisoGauge i₀ r X (pack X (rotDiff R ψ) 0)
        = 4 * (E₀ * Real.exp (-κ * T.dist X)) * (anisoGauge i₀ r X (zcfg X i₀ ν ψ b R) *
          anisoGauge i₀ r X (pack X (rotDiff R ψ) 0)) := by ring
      _ ≤ 4 * (E₀ * Real.exp (-κ * T.dist X)) * (sZ0A N Λ σ ε / r * (sD N A σ ε t / r)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring

/-- The certificate of the whole family from `PremisesTermAniso` (through `CtxAniso`). -/
theorem CtxAniso.pinJet (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R) :
    PinJet T i₀ i₁ ν r E₀ κ A Λ ψ b σ ε R :=
  ⟨fun _ hX => c.pinJetTerm hX⟩

end Bridge

/-- **The landed `termwise_irrelevant_aniso` is a special case of `termwise_irrelevant_pin`**:
its bound follows from the pin theorem through the bridge. -/
theorem termwise_irrelevant_pin_of_aniso (d N : ℕ) (A Λ Ksig α₁ : ℝ) (hA : 0 ≤ A) (hΛ : 1 ≤ Λ)
    (hKsig : 0 ≤ Ksig) (hα0 : 0 < α₁) (hα1 : α₁ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν r E₀ κ K₀ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom) (ψ : Site d → Spin N) (b : Spin N)
      (σ ε K₂ : ℝ) (_ : DataHypAniso Dom ν σ ε K₂ ψ b) (X : Finset (Site d)) (_ : X ∈ T.polys),
      0 < r → r ≤ 1 → 0 < ε → ε ≤ Λ * r → 0 < σ → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 → 0 ≤ ν →
      ν ≤ σ ^ 2 → 0 ≤ E₀ → K₂ ≤ Ksig * σ ^ (2 - α₁) * ε →
      ‖Itw T i₀ i₁ ν X ψ b‖ ≤
        C * E₀ * Real.exp (-(κ - 1) * T.dist X) * (σ ^ (3 - α₁) * (ε / r) ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := termwise_irrelevant_pin d N A Λ Ksig α₁ hA hΛ hKsig hα0 hα1
  refine ⟨C, hC0, ?_⟩
  intro T i₀ i₁ ν r E₀ κ K₀ Dom hP ψ b σ ε K₂ dat X hX hr hr1 hε hεΛ hσ hσ1 hτ hν hνσ hE0 hK
  obtain ⟨u, R, hF⟩ := exists_frame i₀ dat.toDataHyp hτ
  have c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R :=
    ⟨hP, dat, hF, hσ, hσ1, hε, hεΛ, hr, hr1, hν, hνσ, hE0, hA, hτ⟩
  exact hC T i₀ i₁ ν r E₀ κ K₀ Dom hP.toGeom ψ b σ ε K₂ dat X hX hr hr1 hε hεΛ hσ hσ1 hτ hν hνσ
    hE0 hK ⟨u, R, hF, c.pinJetTerm hX⟩

/-- **Hard rule 10**: the certificate (and the context it lives in) is inhabited for the
constant-term family and every admissible choice of the numerical parameters; the witness is the
image of `nonempty_ctxAniso` under the bridge. -/
theorem nonempty_pinJet (i₀ i₁ : Fin N) (h : i₀ ≠ i₁) (ν r E₀ κ A K₀ Λ σ ε K₂ : ℝ) (a : ℂ)
    (ha : ‖a‖ ≤ E₀) (hA : 0 ≤ A) (hK₀ : 1 ≤ K₀) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    (hεΛ : ε ≤ Λ * r) (hr : 0 < r) (hr1 : r ≤ 1) (hν : 0 ≤ ν) (hνσ : ν ≤ σ ^ 2)
    (hτ : σ ^ 2 * ε ≤ 1 / 4) (hK₂ : 0 ≤ K₂) :
    Nonempty (PinJet (constTerms d N a) i₀ i₁ ν r E₀ κ A Λ
      (fun _ : Site d => (Pi.single i₀ 1 : Spin N)) ((ν : ℂ) • Pi.single i₀ 1) σ ε 1) := by
  obtain ⟨c⟩ := nonempty_ctxAniso (d := d) i₀ i₁ h ν r E₀ κ A K₀ Λ σ ε K₂ a ha hA hK₀ hσ hσ1 hε
    hεΛ hr hr1 hν hνσ hτ hK₂
  exact ⟨c.pinJet⟩

end Balaban.SmallField
