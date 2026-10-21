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

omit [NeZero L] in
/-- **The standing hypotheses of the background theory at the birth mass** `ν_j L^{-2j}` of a level
`j ≤ k`: the weights are those of the ideal flow, the mass is nonnegative, and
`ν_j L^{-2j} L^{2k} ≤ 1` (`hcap`). -/
theorem bgHyp_birth {Pc : Consts} {ν a β : ℕ → ℝ}
    (hC : CoeffBounds d L k Pc β ν a) (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ) {j : ℕ}
    (hνj : 0 ≤ ν j) (hcap : physMass L j (ν j) * ((L : ℝ) ^ k) ^ 2 ≤ 1) :
    BgHyp d L k ϱ (aIdeal L k (a k)) (physMass L j (ν j)) where
  hd := hd
  hL := hL
  hϱ := hϱ
  weights := fun _ hj hjk' => aIdeal_mem hL hC.a_ge hC.a_lt hj hjk'
  mass := by unfold physMass; positivity
  massLe := hcap

/-- **The mass cap at the birth mass, from the allowance `e²`**: `ν_j L^{-2j} L^{2k} ≤ e² ν_k` and
`ν_k ≤ (7/8) L⁻²` give `ν_j L^{-2j} L^{2k} ≤ 1`. -/
theorem birth_cap_crude {Pc : Consts} {ν a β : ℕ → ℝ} (hγ : 0 < Pc.γ) (hc8 : 0 < Pc.c₈)
    (hC : CoeffBounds d L k Pc β ν a) (hL : 3 ≤ L) (hν8 : ν k ≤ 7 / 8 * ((L : ℝ) ^ 2)⁻¹) {j : ℕ}
    (hjk : j ≤ k) : physMass L j (ν j) * ((L : ℝ) ^ k) ^ 2 ≤ 1 := by
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have h1 := physMass_mul_sq_le_exp_nuIdeal_core hγ hc8 (by omega : 2 ≤ L) hC hjk
  have hexp : Real.exp 2 ≤ 8 := by
    have := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith [Real.exp_pos 1]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjk
  have hLt : (0 : ℝ) < (L : ℝ) ^ t := by positivity
  have e1 : ((L : ℝ) ^ (j + t)) ^ 2 = ((L : ℝ) ^ j) ^ 2 * ((L : ℝ) ^ t) ^ 2 := by
    rw [pow_add]; ring
  rw [e1, ← mul_assoc]
  have e2 : nuIdeal L (j + t) (ν (j + t)) j = ν (j + t) * (((L : ℝ) ^ t)⁻¹) ^ 2 := by
    unfold nuIdeal; rw [Nat.add_sub_cancel_left]
  rw [e2] at h1
  have h3 : physMass L j (ν j) * ((L : ℝ) ^ j) ^ 2 * ((L : ℝ) ^ t) ^ 2 ≤
      Real.exp 2 * (ν (j + t) * (((L : ℝ) ^ t)⁻¹) ^ 2) * ((L : ℝ) ^ t) ^ 2 :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have e3 : Real.exp 2 * (ν (j + t) * (((L : ℝ) ^ t)⁻¹) ^ 2) * ((L : ℝ) ^ t) ^ 2 =
      Real.exp 2 * ν (j + t) := by
    field_simp
  rw [e3] at h3
  refine h3.trans ?_
  have hinv : ((L : ℝ) ^ 2)⁻¹ ≤ 1 / 9 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; norm_num; nlinarith
  have hν8' : ν (j + t) ≤ 7 / 8 * (1 / 9) :=
    hν8.trans (mul_le_mul_of_nonneg_left hinv (by norm_num))
  have hν0 : 0 < ν (j + t) := hC.nu_pos
  nlinarith [Real.exp_pos 2]

/-- **The radius of the coefficient context on the birth domains**,
`δ² / (2 (N + 1) e²)` with `δ = min (c₀, c₁, ε_j / (2 K₁ + 2))`. -/
noncomputable def birthRadius (d L N : ℕ) [NeZero L] (P : Consts) (j : ℕ) : ℝ :=
  (min (min (bgC0 d L N) (bgC1 d L N)) (P.eps d L j / (2 * bgK1 d L N + 2))) ^ 2 /
    (2 * ((N : ℝ) + 1) * Real.exp 2)

theorem birthDelta_pos {P : Consts} (hα₀ : 0 < P.α₀) (hd : 3 ≤ d) (j : ℕ) :
    0 < min (min (bgC0 d L N) (bgC1 d L N)) (P.eps d L j / (2 * bgK1 d L N + 2)) := by
  have hd0 : 0 < d := by omega
  have hK := bgK1_pos d L N
  exact lt_min (lt_min (bgC0_pos d L N hd0) (bgC1_pos' hd0))
    (div_pos (eps_pos hα₀ j) (by positivity))

theorem birthRadius_pos {P : Consts} (hα₀ : 0 < P.α₀) (hd : 3 ≤ d) (j : ℕ) :
    0 < birthRadius d L N P j := by
  unfold birthRadius
  have := birthDelta_pos (N := N) (L := L) hα₀ hd j
  positivity

variable {N₁ : ℕ} [NeZero N₁]

/-- **The coefficient context of a member of the second version on the birth domain.** -/
theorem coefCtx_birth {P Pc : Consts} {Rg : Regime L} {β a : ℕ → ℝ}
    {Tm : Terms d L N₁ m₁ k N ϱ}
    (hγ : 0 < Pc.γ) (hc8 : 0 < Pc.c₈) (hα₀ : 0 < P.α₀) (hC : CoeffBounds d L k Pc β Rg.ν a)
    (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hϱ : bgR0 d L ≤ ϱ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hνj : 0 ≤ Rg.ν j)
    (hcap : physMass L j (Rg.ν j) * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (hT : SFTermClauses P (birthXiDom (m₁ := m₁) (ϱ := ϱ) P Rg a N₁) Tm) :
    CoefCtx P (Rg.ν k) (birthXiDom (m₁ := m₁) (ϱ := ϱ) P Rg a N₁) Tm j (birthRadius d L N P j) := by
  have hBg := bgHyp_birth hC hd hL hϱ hνj hcap
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hδ0 := birthDelta_pos (N := N) (L := L) hα₀ hd j
  set δ := min (min (bgC0 d L N) (bgC1 d L N)) (P.eps d L j / (2 * bgK1 d L N + 2)) with hδ
  have hK := bgK1_pos d L N
  have hδc0 : δ ≤ bgC0 d L N := (min_le_left _ _).trans (min_le_left _ _)
  have hδc1 : δ ≤ bgC1 d L N := (min_le_left _ _).trans (min_le_right _ _)
  have hδε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j := by
    have h1 : δ ≤ P.eps d L j / (2 * bgK1 d L N + 2) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity), mul_comm] at h1
  have hρ0 := birthRadius_pos (N := N) (L := L) hα₀ hd j
  set ρ := birthRadius d L N P j with hρ
  have hνpos : 0 < nuIdeal L k (Rg.ν k) j := by
    have := hC.nu_pos
    unfold nuIdeal; positivity
  have hm := physMass_mul_sq_le_exp_nuIdeal_core hγ hc8 (by omega : 2 ≤ L) hC hjk
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
  exact coefCtx_birth hF.admissible.γ_pos hF.admissible.c₈_pos hF.admissible.α₀_pos hF.coeff
    hd hL hϱ hj1 hjk hνj
    (birth_cap_crude hF.admissible.γ_pos hF.admissible.c₈_pos hF.coeff hL
      (hF.coeff.nu_le.trans hF.admissible.νbar_le) hjk)
    (hF.torus (torusSeq L P6.m₀ n) (dvd_mul_right _ _)).terms

/-- **The coefficient family of a member of (D2♭).**  As `coefFam_of_d2sf2`, for the second
version with the mass range `0 < ν_k ≤ 1`; the cap of the birth mass of the level is a premise. -/
theorem coefFam_of_sfflat2 {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ}
    (h : SFFlat2 P6 k0 sf) (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ)
    (hκ : aEnt d L + 1 < P6.κ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hνj : 0 ≤ sf.ν j)
    (hcap : physMass L j (sf.ν j) * ((L : ℝ) ^ k) ^ 2 ≤ 1) :
    CoefFam P6 (sf.ν k) (sfDom P6 k0 sf) sf.Tm j (birthRadius d L N P6 j) := by
  obtain ⟨ρsf, hF⟩ := h.torus
  refine ⟨fun n => ?_, h.torusIndep, h.admissible.E₀_nonneg, hκ⟩
  have : NeZero (torusSeq L P6.m₀ n) := ⟨torusSeq_ne_zero P6.m₀ n⟩
  exact coefCtx_birth (Pc := massOne P6) (Rg := (⟨k0, sf.ν⟩ : Regime L)) h.admissible.γ_pos
    h.admissible.c₈_pos h.admissible.α₀_pos h.coeff hd hL hϱ hj1 hjk hνj hcap
    (hF (torusSeq L P6.m₀ n) (dvd_mul_right _ _)).terms

/-- **The coefficient data of a member of (D2) exist** (`D1CorrLim`): for small-field data with
(D2), the constants with `κ > a_ent + 1` and `ϱ ≥ R₀(d, L)`, nonnegative running masses and a
physical field of norm one. -/
theorem d1CorrLim_of_d2sf2 {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ}
    {fac : ℕ → ℝ} (h : D2SF2 P6 k0 sf fac) (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ)
    (hκ : aEnt d L + 1 < P6.κ) (hν : ∀ j, 1 ≤ j → j ≤ k → 0 ≤ sf.ν j)
    (hv : EuclideanSpace ℝ (Fin N)) (hhv : ‖hv‖ = 1) :
    D1CorrLim P6.m₀ sf (corrSrc sf) hv (corrVc P6.m₀ sf) :=
  d1CorrLim_of_fams (P := P6) sf (sfDom P6 k0 sf) hv hhv fun j hj1 hjk =>
    ⟨_, coefFam_of_d2sf2 h hd hL hϱ hκ hj1 hjk (hν j hj1 hjk)⟩

/-- **The coefficient data of a member of (D2♭) exist** (`D1CorrLim`). -/
theorem d1CorrLim_of_sfflat2 {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ}
    (h : SFFlat2 P6 k0 sf) (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ)
    (hκ : aEnt d L + 1 < P6.κ) (hν : ∀ j, 1 ≤ j → j ≤ k → 0 ≤ sf.ν j)
    (hcap : ∀ j, 1 ≤ j → j ≤ k → physMass L j (sf.ν j) * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (hv : EuclideanSpace ℝ (Fin N)) (hhv : ‖hv‖ = 1) :
    D1CorrLim P6.m₀ sf (corrSrc sf) hv (corrVc P6.m₀ sf) :=
  d1CorrLim_of_fams (P := P6) sf (sfDom P6 k0 sf) hv hhv fun j hj1 hjk =>
    ⟨_, coefFam_of_sfflat2 h hd hL hϱ hκ hj1 hjk (hν j hj1 hjk) (hcap j hj1 hjk)⟩

end Birth

end Balaban.LargeField.Def7v2
