/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoefD1Corr
public import Balaban.SmallField.Def6v2BirthRadius
public import Balaban.LargeField.Def7v2Class

/-!
# The coefficient context of the second-version class on the birth domains

A member of `IsSFFamily2On` on the birth domains `birthXiDom` (the domain `sfDom` of (D2)) gives a
`CoefCtx` at every level `1 ≤ j ≤ k` and every selected torus, with the radius

`ρ = δ² / (2 (N + 1) e²)`,  `δ = min (c₀, c₁, ε_j / (2 K₁ + 2))`:

the factor `e²` is the allowance between the birth mass `ν_j L^{-2j}` of the level and the ideal
mass of the current scale (`physMass_mul_sq_le_exp_nuIdeal`).  The only premise on the running
masses beyond `CoeffBounds` is the positivity `ν_j ≥ 0` of the mass of the level.

* `bgHyp_birth_of_class`: the standing hypotheses of the background theory at the birth mass;
* `coefCtx_birth`: the context;
* `coefFam_of_d2sf2`: the family along the tori `torusSeq L m₀ n`;
* `exists_d1CorrLim_of_d2sf2`: the coefficient data of a member of (D2).
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.LargeField.Def7 Balaban.Fluctuation Filter Matrix Metric

section Birth

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The standing hypotheses of the background theory at the birth mass** `ν_j L^{-2j}` of a level
`j ≤ k` of a member of the second version: the weights are those of the ideal flow, the mass is
nonnegative (a premise), and `ν_j L^{-2j} L^{2k} ≤ e² ν_k ≤ e² (7/8) L^{-2} ≤ 1`. -/
theorem bgHyp_birth_of_class {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ}
    (hP : P.Admissible d L) (hC : CoeffBounds d L k P β Rg.ν a) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hϱ : bgR0 d L ≤ ϱ) {j : ℕ} (hjk : j ≤ k) (hνj : 0 ≤ Rg.ν j) :
    BgHyp d L k ϱ (aIdeal L k (a k)) (physMass L j (Rg.ν j)) where
  hd := hd
  hL := hL
  hϱ := hϱ
  weights := fun _ hj hjk' => aIdeal_mem hL hC.a_ge hC.a_lt hj hjk'
  mass := by unfold physMass; positivity
  massLe := by
    have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
    have hLpos : (0 : ℝ) < L := by linarith
    have h1 := physMass_mul_sq_le_exp_nuIdeal hP (by omega : 2 ≤ L) hC hjk
    have hνk := hC.nu_le
    have hνb := hP.νbar_le
    have hexp : Real.exp 2 ≤ 8 := by
      have := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [h2]; nlinarith [Real.exp_pos 1]
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjk
    have hLt : (0 : ℝ) < (L : ℝ) ^ t := by positivity
    have e1 : ((L : ℝ) ^ (j + t)) ^ 2 = ((L : ℝ) ^ j) ^ 2 * ((L : ℝ) ^ t) ^ 2 := by
      rw [pow_add]; ring
    rw [e1, ← mul_assoc]
    have e2 : nuIdeal L (j + t) (Rg.ν (j + t)) j = Rg.ν (j + t) * (((L : ℝ) ^ t)⁻¹) ^ 2 := by
      unfold nuIdeal; rw [Nat.add_sub_cancel_left]
    rw [e2] at h1
    have h3 : physMass L j (Rg.ν j) * ((L : ℝ) ^ j) ^ 2 * ((L : ℝ) ^ t) ^ 2 ≤
        Real.exp 2 * (Rg.ν (j + t) * (((L : ℝ) ^ t)⁻¹) ^ 2) * ((L : ℝ) ^ t) ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have e3 : Real.exp 2 * (Rg.ν (j + t) * (((L : ℝ) ^ t)⁻¹) ^ 2) * ((L : ℝ) ^ t) ^ 2 =
        Real.exp 2 * Rg.ν (j + t) := by
      field_simp
    rw [e3] at h3
    refine h3.trans ?_
    have hinv : ((L : ℝ) ^ 2)⁻¹ ≤ 1 / 9 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; norm_num; nlinarith
    have hν8 : Rg.ν (j + t) ≤ 7 / 8 * (1 / 9) := by
      refine hνk.trans (hνb.trans ?_)
      exact mul_le_mul_of_nonneg_left hinv (by norm_num)
    have hν0 : 0 < Rg.ν (j + t) := hC.nu_pos
    nlinarith [Real.exp_pos 2]

/-- **The radius of the coefficient context on the birth domains**,
`δ² / (2 (N + 1) e²)` with `δ = min (c₀, c₁, ε_j / (2 K₁ + 2))`. -/
noncomputable def birthRadius (d L N : ℕ) [NeZero L] (P : Consts) (j : ℕ) : ℝ :=
  (min (min (bgC0 d L N) (bgC1 d L N)) (P.eps d L j / (2 * bgK1 d L N + 2))) ^ 2 /
    (2 * ((N : ℝ) + 1) * Real.exp 2)

theorem birthDelta_pos {P : Consts} (hP : P.Admissible d L) (hd : 3 ≤ d) (j : ℕ) :
    0 < min (min (bgC0 d L N) (bgC1 d L N)) (P.eps d L j / (2 * bgK1 d L N + 2)) := by
  have hd0 : 0 < d := by omega
  have hK := bgK1_pos d L N
  exact lt_min (lt_min (bgC0_pos d L N hd0) (bgC1_pos' hd0))
    (div_pos (eps_pos hP.α₀_pos j) (by positivity))

theorem birthRadius_pos {P : Consts} (hP : P.Admissible d L) (hd : 3 ≤ d) (j : ℕ) :
    0 < birthRadius d L N P j := by
  unfold birthRadius
  have := birthDelta_pos (N := N) hP hd j
  positivity

variable {N₁ : ℕ} [NeZero N₁]

/-- **The coefficient context of a member of the second version on the birth domain.** -/
theorem coefCtx_birth {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
    (hP : P.Admissible d L) (hC : CoeffBounds d L k P β Rg.ν a) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hϱ : bgR0 d L ≤ ϱ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hνj : 0 ≤ Rg.ν j)
    (hT : SFTermClauses P (birthXiDom (m₁ := m₁) (ϱ := ϱ) P Rg a N₁) Tm) :
    CoefCtx P (Rg.ν k) (birthXiDom (m₁ := m₁) (ϱ := ϱ) P Rg a N₁) Tm j (birthRadius d L N P j) := by
  have hBg := bgHyp_birth_of_class hP hC hd hL hϱ hjk hνj
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hδ0 := birthDelta_pos (N := N) hP hd j
  set δ := min (min (bgC0 d L N) (bgC1 d L N)) (P.eps d L j / (2 * bgK1 d L N + 2)) with hδ
  have hK := bgK1_pos d L N
  have hδc0 : δ ≤ bgC0 d L N := (min_le_left _ _).trans (min_le_left _ _)
  have hδc1 : δ ≤ bgC1 d L N := (min_le_left _ _).trans (min_le_right _ _)
  have hδε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j := by
    have h1 : δ ≤ P.eps d L j / (2 * bgK1 d L N + 2) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity), mul_comm] at h1
  have hρ0 := birthRadius_pos (N := N) hP hd j
  set ρ := birthRadius d L N P j with hρ
  have hνpos : 0 < nuIdeal L k (Rg.ν k) j := by
    have := hC.nu_pos
    unfold nuIdeal; positivity
  have hm := physMass_mul_sq_le_exp_nuIdeal hP (by omega : 2 ≤ L) hC hjk
  have hρ' : (N : ℝ) * (Real.exp 2 * ρ) < δ ^ 2 := by
    have : Real.exp 2 * ρ = δ ^ 2 / (2 * ((N : ℝ) + 1)) := by
      rw [hρ]; unfold birthRadius; rw [← hδ]
      field_simp
    rw [this]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [pow_pos hδ0 2]
  refine ⟨hT, hj1, hjk, hC.nu_pos, hρ0, ?_, ?_⟩
  · intro i₀ X hX Ψ b hΨ hΨb hb
    rw [birthXiDom_dom_iff]
    have hΩ := (hT.gs_spec j hj1 hjk X hX).2
    refine xiDom_of_close hBg hΩ hjk i₀ hδ0 hδc0 hδc1 (ρ := Real.exp 2 * ρ)
      (mul_pos (Real.exp_pos 2) hρ0) hρ' hδε Ψ (fun i => b i / (nuIdeal L k (Rg.ν k) j : ℂ))
      (fun x i => (hΨ x i).trans (le_mul_of_one_le_left hρ0.le
        (by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by norm_num)))) hΨb (fun i => ?_)
    have h1 := mass_mul_norm_div_le_allow (L := L) (μ := physMass L j (Rg.ν j))
      (νj := nuIdeal L k (Rg.ν k) j) (Λ := Real.exp 2) (j := j) hνpos (Real.exp_pos 2) hm (b i)
      ((Pi.single i₀ 1 : Fin N → ℂ) i)
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left (hb i).le (Real.exp_pos 2).le
  · intro Q hQ X Ψ h hd'
    rw [birthXiDom_dom_iff] at hd' ⊢
    exact xiDom_rot hQ hd'

/-- **The coefficient family of a member of (D2).**  For small-field data with (D2) (the second
version on the birth domains `sfDom`, along the read tori `L^{m₀} (n + 1)`), the constants with
`κ > a_ent + 1` and `ϱ ≥ R₀(d, L)`, a level `1 ≤ j ≤ k` with `ν_j ≥ 0`: the terms form a
coefficient family. -/
theorem coefFam_of_d2sf2 {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ} {fac : ℕ → ℝ}
    (h : D2SF2 P6 k0 sf fac) (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ)
    (hκ : aEnt d L + 1 < P6.κ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hνj : 0 ≤ sf.ν j) :
    CoefFam P6 (sf.ν k) (sfDom P6 k0 sf) sf.Tm j (birthRadius d L N P6 j) := by
  obtain ⟨ρsf, hF⟩ := h.sfClass
  refine ⟨fun n => ?_, hF.torusIndep, hF.admissible.E₀_nonneg, hκ⟩
  have : NeZero (torusSeq L P6.m₀ n) := ⟨torusSeq_ne_zero P6.m₀ n⟩
  exact coefCtx_birth hF.admissible hF.coeff hd hL hϱ hj1 hjk hνj
    (hF.torus (torusSeq L P6.m₀ n) (dvd_mul_right _ _)).terms

/-- **The coefficient data of a member of (D2) exist** (`D1CorrLim`): for small-field data with
(D2), the constants with `κ > a_ent + 1` and `ϱ ≥ R₀(d, L)`, nonnegative running masses and a
physical field of norm one. -/
theorem exists_d1CorrLim_of_d2sf2 {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ}
    {fac : ℕ → ℝ} (h : D2SF2 P6 k0 sf fac) (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ)
    (hκ : aEnt d L + 1 < P6.κ) (hν : ∀ j, 1 ≤ j → j ≤ k → 0 ≤ sf.ν j)
    (hv : EuclideanSpace ℝ (Fin N)) (hhv : ‖hv‖ = 1) :
    ∃ (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N) (vc : CorrCoef d),
      D1CorrLim P6.m₀ sf St hv vc :=
  exists_d1CorrLim (P := P6) sf (sfDom P6 k0 sf) hv hhv fun j hj1 hjk =>
    ⟨_, coefFam_of_d2sf2 h hd hL hϱ hκ hj1 hjk (hν j hj1 hjk)⟩

end Birth

end Balaban.LargeField.Def7v2
