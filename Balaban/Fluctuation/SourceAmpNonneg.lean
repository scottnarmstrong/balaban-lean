/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.PhysAmpFacts
public import Balaban.Fluctuation.SourceFamilyRelative
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Nonnegativity of the step amplitudes; the source label activities over the chart

The landed `sourceFamilyRelative_scale` states its label-activity conclusions under the inner
premise `0 ≤ ε_U`, with `ε_U = β · prop33EpsEtaScaled … 0 0 (q/β)`, because no landed lemma gives the
sign of the source constant `cK2' · δ₁`.  This file proves the signs and the scale statement without
the premise.

* `cK2'_nonneg`: `0 ≤ cK2' d L N B` for `0 ≤ B`.
* `famConst_nonneg`: `0 ≤ famConst d L BG κ` for `0 ≤ BG` and `0 < d`.
* `cK2'_famConst_mul_nonneg`: `0 ≤ cK2' d L N (famConst d L BG₂ κ) · δ₁` for `0 ≤ BG₂`, `0 < d`,
  `0 ≤ δ₁`.
* `prop33EpsEtaScaled_nonneg`: `0 ≤ prop33EpsEtaScaled … 0 0 η` for `0 < r`, `0 ≤ η`, `0 ≤ δ₁` and
  the signs above; `beta_mul_prop33EpsEtaScaled_nonneg`: the same for `β · … (q/β)`.
* `Balaban.Inhabited.sourceFamilyRelative_scale_nonneg`: the statement of
  `sourceFamilyRelative_scale` at every scale, with `0 ≤ ε_U` part of the conclusion (so that the
  label activity family is defined without a premise), the amplitude bound
  `4 ε_U ≤ C_E (log β_k)^{3p}/√β_k + q C_F (log β_k)^p/√β_k` of `sourceAmp_scale`, and the signs of
  the constants.  The constants `BG, BG₂, κ` are hidden by the existential of the landed scale
  theorem, so its proof is re-run with the signs exposed.
* `Balaban.Inhabited.sourceFamilyRelative_nonneg_instance`: the case `k = 1`, `N₁ = 6`.

What is NOT proved here: the identification of the exponent on the chart (the value of `physVal` at
`(q, g/β)` with `JointRep.W1 + W2`) and the complex activity bound off the central real datum.  The
class enters only through the zero class of the landed theorems, so nothing depends on a choice of
generating sets of class terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background

section Signs

/-- `cK2'` is nonnegative for a nonnegative family constant. -/
theorem cK2'_nonneg (d L N : ℕ) [NeZero L] {B : ℝ} (hB : 0 ≤ B) : 0 ≤ cK2' d L N B := by
  have h1 := cA_ge d L N
  have h2 := cF_pos d L
  unfold cK2' cN'
  positivity

/-- `famConst` is nonnegative for `0 ≤ BG` and `0 < d` (it is at least `1`). -/
theorem famConst_nonneg (d L : ℕ) {BG : ℝ} (hBG : 0 ≤ BG) (hd : 0 < d) (κ : ℝ) :
    0 ≤ famConst d L BG κ := by
  have := famConst_ge_one (L := L) hBG κ hd
  linarith

/-- The source constant `cK2' · δ₁` is nonnegative. -/
theorem cK2'_famConst_mul_nonneg (d L N : ℕ) [NeZero L] {BG₂ κ δ₁ : ℝ} (hBG₂ : 0 ≤ BG₂)
    (hd : 0 < d) (hδ₁ : 0 ≤ δ₁) : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
  mul_nonneg (cK2'_nonneg d L N (famConst_nonneg d L hBG₂ hd κ)) hδ₁

/-- `cK2'` times `δ₁` is nonnegative from the sign of the family constant (the form the tower
supplies: `0 ≤ famConst d L BG₂ κ`). -/
theorem cK2'_famConst_mul_nonneg_of_famConst (d L N : ℕ) [NeZero L] {BG₂ κ δ₁ : ℝ}
    (hB : 0 ≤ famConst d L BG₂ κ) (hδ₁ : 0 ≤ δ₁) :
    0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
  mul_nonneg (cK2'_nonneg d L N hB) hδ₁

/-- **The amplitude of the zero class is nonnegative.**  For `0 < r`, `0 ≤ η`, `0 ≤ δ₁` and
`0 ≤ famConst d L BG₂ κ`, `prop33EpsEtaScaled … 0 0 η ≥ 0`. -/
theorem prop33EpsEtaScaled_nonneg (d L N m₁ n m₀ : ℕ) [NeZero L] {a₁ BG BG₂ κ δ₁ r η : ℝ}
    (hB : 0 ≤ famConst d L BG₂ κ) (hδ₁ : 0 ≤ δ₁) (hr : 0 < r) (hη : 0 ≤ η) :
    0 ≤ prop33EpsEtaScaled d L N m₁ n m₀ a₁ BG BG₂ κ δ₁ r 0 0 η := by
  have hc1 : 0 ≤ c1 d L := by have := one_le_c1 d L; linarith
  have hK := cK2'_famConst_mul_nonneg_of_famConst d L N (κ := κ) (δ₁ := δ₁) hB hδ₁
  unfold prop33EpsEtaScaled
  have h0 : 0 ≤ 3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
      ‖energyBdScaled d L N (compWeight L a₁) n (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁
        (rho4 d L N BG κ)‖ / r ^ 3 := by positivity
  have h1 : 0 ≤ η * (cK2' d L N (famConst d L BG₂ κ) * δ₁ + 0) / r := by
    rw [add_zero]; positivity
  have h2 : (0 : ℝ) * c1 d L * ((L : ℝ) ^ (n + 1)) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d / r = 0 := by
    simp
  rw [h2]
  linarith

/-- `0 ≤ β · prop33EpsEtaScaled … 0 0 (q/β)` for `0 < β`, `0 ≤ q`. -/
theorem beta_mul_prop33EpsEtaScaled_nonneg (d L N m₁ n m₀ : ℕ) [NeZero L]
    {a₁ BG BG₂ κ δ₁ r q β : ℝ} (hB : 0 ≤ famConst d L BG₂ κ) (hδ₁ : 0 ≤ δ₁) (hr : 0 < r)
    (hq : 0 ≤ q) (hβ : 0 < β) :
    0 ≤ β * prop33EpsEtaScaled d L N m₁ n m₀ a₁ BG BG₂ κ δ₁ r 0 0 (q / β) :=
  mul_nonneg hβ.le (prop33EpsEtaScaled_nonneg d L N m₁ n m₀ hB hδ₁ hr (div_nonneg hq hβ.le))

end Signs

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology Metric

section Scale

open Classical in
/-- **The source direct terms as a family over the relative chart, at every scale, without the
premise `0 ≤ ε_U`.**  The statement of `sourceFamilyRelative_scale` with the following changes.
The constants `BG, BG₂, κ` of the tower are carried with the sign `0 ≤ famConst 3 3 BG₂ κ`, and
`C_E, C_F > 0` are added.  The conclusion on the label activities begins with the proof
`hεU : 0 ≤ ε_U`, `ε_U = β · prop33EpsEtaScaled … 0 0 (q/β)`, and the amplitude bound
`4 ε_U ≤ C_E (log β_k)^{3p}/√β_k + q C_F (log β_k)^p/√β_k` (`β_k = β · 3^k`, from
`sourceAmp_scale`), and then, for every `K_c ≥ K₀`, the three facts about `labelActFamilyOn`
(joint analyticity on `physVq ×ˢ ball 0 2`, equality with `dtAct`, the term-value formula) with
the uniform bound of `LabelAct` (amplitude `2 ε_U`, rate `2 κ_dec - 1`).  The constants do not
depend on `k`, `N₁`, `ν`, `β`, `p₁`, `q`, `S`. -/
theorem sourceFamilyRelative_scale_nonneg {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10)) :
    ∃ (m₁ : ℕ) (t δ β₀ BG BG₂ κ CE CF : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < δ ∧ 0 < CE ∧ 0 < CF ∧
      0 ≤ famConst 3 3 BG₂ κ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ hp0 : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ S : StepSetting 3 3 N₁ m₁ k 2 (rhoSep m₁),
        S = hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ → ∀ hp : 0 < S.p₁,
        ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 × (CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
          (𝒴 : Finset (Set (CTorus 3 3 N₁ m₁ (k + 1))))
          (T : Set (CTorus 3 3 N₁ m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
            (RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 × (CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
          (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 m₁ k 1 S.a₁ BG BG₂ κ t
                  (lvR κ t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * κdec - 1)
                (rawOf S.D', (0 : CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ))
                (physSΛEta S S.a₁ S.ν t (q / S.β))
                (physXW S (lvCpsi κ t (β * 3 ^ k)) 2 2 (lvR κ t (β * 3 ^ k) p₁)) val (physAgΘ S)
                (AgFDirPair S)),
          I.𝒴 = 𝒴 ∧ I.T = T ∧
          ∃ hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
              (physVq S 1 ν t q),
            (∀ g : Fld 3 3 N₁ m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
              ∃ hg : (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) ∈ physVq S 1 ν t q,
                physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) =
                  (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∧
                (I.atThetaOn S 1 _ hF hg).𝒴 = 𝒴 ∧ (I.atThetaOn S 1 _ hF hg).T = T) ∧
            ∃ hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 m₁ k 1 S.a₁ BG BG₂ κ t
                  (lvR κ t (β * 3 ^ k) p₁) 0 0 (q / S.β),
              4 * (S.β * prop33EpsEtaScaled 3 3 2 m₁ k 1 S.a₁ BG BG₂ κ t
                  (lvR κ t (β * 3 ^ k) p₁) 0 0 (q / S.β)) ≤
                CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
                  q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
              ∀ {Kc : ℝ} (hKc : K0 3 3 κ0 ≤ Kc),
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
                  (labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    hκ0def.ge hKc r.1 r.2).H y Φ)
                  (physVq S 1 ν t q ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e (he : e ∈ physVq S 1 ν t q) (u : ℂ),
                labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    hκ0def.ge hKc e u =
                  dtAct S 1 (I.atThetaOn S 1 _ hF he)
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    hκ0def.ge hKc u) ∧
              (∀ e ∈ physVq S 1 ν t q, ∀ u : ℂ, ‖u‖ < 2 →
                ∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                (labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    hκ0def.ge hKc e u).H y Φ =
                  I.T y.1 (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ)
                    (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) := by
  classical
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht0, ⟨hC₀⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0⟩ :=
    tower_core_rates 2 (κ0 := κ0) (κdec := κdec) (by rw [hκ0def]) (by rw [hκdecdef]; linarith)
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have hκdec0 : 0 ≤ κdec := by linarith
    have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  obtain ⟨β₀t, hβ₀t, hitems⟩ := scale_C_items hA p m₁ h4 hbig κ ht0 hδ hsm hδ'0 hδ'a hδ'b hδ'c
  have hxi1 : xiC1 3 * t ≤ 1 := by
    have h1 := hC₀.c7le
    have h2 := c7_le_bgC1 3 3 2 BG κ
    have h3 := bgC1_le_small 3 3 2 (by norm_num)
    linarith
  have hρ4 : 0 ≤ rho4 3 3 2 BG κ := by
    have hd0 : 0 < 3 := by norm_num
    have hBG := hC₀.hS.fam.2.1
    have hB1 : 0 ≤ famConst 3 3 BG κ := by
      have := famConst_ge_one (L := 3) hBG κ hd0; linarith
    unfold rho4
    exact (c6'_pos hB1 (by have := gamma1_pos hd0; positivity)).le
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = cK2' 3 3 2 (famConst 3 3 BG₂ κ) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQdef]; exact cK2'_pos' hB0
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3 *
    (((3 : ℕ) : ℝ) ^ 3 * ((((2 : ℕ) : ℝ) / 2) * (2 * (1 + Q) ^ 2 +
      (((3 : ℕ) : ℝ) + 1 + rho4 3 3 2 BG κ) * Q ^ 2) * t ^ 2)) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by
    rw [hPdef]; positivity
  have hK0 : 0 < Q * t := mul_pos hQ0 ht0
  obtain ⟨β₁, hexpβ₁, hA'⟩ := sourceAmp_scale (A₁ := A₁) (κ := κ) (t := t) hA p ht0
  refine ⟨m₁, t, δ, max β₀t β₁, BG, BG₂, κ, srcCE A₁ κ t P, srcCF A₁ κ t (Q * t),
    le_trans hβ₀t (le_max_left _ _), ht0, hδ, srcCE_pos hA ht0 hP0, srcCF_pos hA ht0 hK0, hB0, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq S hS hp
  subst hS
  have hν0 : 0 ≤ ν := hνpos.le
  have hβt : β₀t ≤ β := le_trans (le_max_left _ _) hβ
  have hβ₁ : β₁ ≤ β := le_trans (le_max_right _ _) hβ
  have hβ2 : 2 ≤ β := le_trans hβ₀t hβt
  have hβ0 : 0 < β := by linarith
  have hβ1 : 1 ≤ β := by linarith
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hbβ : β ≤ β * 3 ^ k := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * 3 ^ k := by positivity
  obtain ⟨hcψ0, hr0, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems k hk N₁ hN ν hν0 hν β hβt p₁ hp0 hp₁
  have hexp : Real.exp 1 ≤ β * 3 ^ k := le_trans hexpβ₁ (hβ₁.trans hbβ)
  have hℓ : 1 ≤ Real.log (β * 3 ^ k) := (Real.le_log_iff_exp_le hb0).2 hexp
  have hamp := (hA' (β * 3 ^ k) (hβ₁.trans hbβ) p₁ hp0 hp₁).2 P (Q * t) q hP0 hK0.le hq0.le
  have hSD := dgSetting_lv (N₁ := N₁) (k := k) h4 hN hν0 hν
  have hHB := bgHyp_lv (k := k) m₁ hν0 hν
  have hC : FlCore 2 (lvTop N₁ m₁ k (rhoSep m₁)) (lvLow N₁ m₁ k (rhoSep m₁)) 1 ν c BG κ t
      (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t :=
    flCore_level_transfer hC₀ hSD (opSetting_lv h4 hN hν0 hν) (isLevel_lvLow hk) isLevel_lvTop hHB
  have hBh := hBh_of_xi (N := 2) (Gp := lvTop N₁ m₁ k (rhoSep m₁)) hHB hνpos hC.small1
    hC.eps_pos hxi1
  have hD : XiCData (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G' (compWeight 3 1) ν (k + 1) 1 t
      (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D' := by
    refine ⟨fun _ => unitVec hN2, unitVec hN2, 0, 0,
      exists_xiC hHB (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (massLe_lv hν) ht0, ?_, ?_⟩
    · intro x hx i
      have := unitBg_Ψ_of_mem (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2)).Ψ x i = _
      rw [this]; simp
    · intro x hx i
      have := unitBg_h_of_mem (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2)).h x i = _
      rw [this]; simp
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨hV, hF⟩ := LocalCover.levelLocalCover (N := 2) (lvLow N₁ m₁ k (rhoSep m₁)) hSD
    (isLevel_lvTop (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := rhoSep m₁)) (m₀ := 1) le_rfl hN3
  have hBh0 : (0 : ℝ) ≤ 1 + 2 / ν := by positivity
  have hη0 : 0 < q / β := div_pos hq0 hβ0
  -- the sign and the size of the amplitude
  have hbU : (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).betaU = β * 3 ^ k :=
    hatStepK_betaU k m₁ hk ν β p₁ δ
  obtain ⟨hid, hpot, hterm0, hεle', hεpos⟩ := physAmp_facts (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ)
    (by norm_num) le_rfl 1 (compWeight_three_mem hk) rfl hβ0 rfl hbU hQ0 ht0 hρ4 hr0 hq0 hQdef
    hPdef (εU := β * prop33EpsEtaScaled 3 3 2 m₁ k 1 1 BG BG₂ κ t
      (lvR κ t (β * 3 ^ k) p₁) 0 0 (q / β)) rfl
  have hεnn := hεpos.le
  have hεle := hεle' _ hamp
  have hε4 := sourceAmp_scale_four (A₁ := A₁) (κ := κ) (t := t) (P := P) (K := Q * t) (q := q) p
    hb0 (by linarith) hεle
  -- the direct terms
  obtain ⟨val, 𝒴, T, hval, hloc, hcont, hI⟩ := sourceDirectTerms_slice
    (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ)
    (ρ := p₁) (εU := β * prop33EpsEtaScaled 3 3 2 m₁ k 1 1 BG BG₂ κ t
      (lvR κ t (β * 3 ^ k) p₁) 0 0 (q / β))
    (Rσ := 2) (R₁ := 2) (r := lvR κ t (β * 3 ^ k) p₁) (R := 2) (m₀ := 1) (κdec := κdec)
    (κ₀ := κ0) (Bh := 1 + 2 / ν) (δc := δc) (cψ := lvCpsi κ t (β * 3 ^ k))
    (jV := fun _ => k) (XV := fun z => LocalCover.cube 1 k (LocalCover.blockSite k z))
    (𝒦XV := fun z => LocalCover.fam 1 (LocalCover.blockSite k z))
    (X₁V := fun z => LocalCover.nbhdF 1 (LocalCover.blockSite k z))
    (jF := fun _ => k) (XF := fun s => LocalCover.cube 1 k s.1)
    (𝒦XF := fun s => LocalCover.fam 1 s.1) (X₁F := fun s => LocalCover.nbhdF 1 s.1)
    (hC := hC) (hconn := hatConn_lvTop) (hrow := rowInHat_lv hk h4 hN hν0 hν)
    (hκ₀ := hκ0) (hκdec := hκdec) (hκ := by exact_mod_cast hκ) (h1 := h1)
    (hR₁ := by norm_num) (hr := hr0) (hcψ := hcψ0.le) (hMX := hMX) (hdm := hdm) (hα := hα)
    (hsmX := hsmX) (hδ₁ := hδ₁) (ha₁ := one_pos) (H := hHB) (hc7 := hc7) (hR := le_rfl)
    (hRs := g1) (hsmall := g2) (hnum := g3) (hnum' := g4) (hsm := g5)
    (hcovV := fun z => (hV z).1) (hX₁V := fun z => (hV z).2.1)
    (hoptV := fun z => (hV z).2.2.1) (hΔV := fun z => (hV z).2.2.2.1)
    (hlogV := fun _ => hlog) (hZV := fun z => (hV z).2.2.2.2.1)
    (hmarV := fun z => (hV z).2.2.2.2.2.1)
    (hcovF := fun s => (hF s).1) (hX₁F := fun s => (hF s).2.1)
    (hoptF := fun s => (hF s).2.2.1) (hΔF := fun s => (hF s).2.2.2.1)
    (hlogF := fun _ => hlog) (hyF := fun s => (hF s).2.2.2.2)
    (hBh0 := hBh0) (hBh := hBh) (hZν := fun z => (hV z).2.2.2.2.2.2)
    (hN := hN3) (hp := hp) (η := q / β) (hη0 := hη0) (hRσ := by norm_num) (hc := hc)
    (hεb := by
      have hnβ : ‖(((hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).β : ℝ) : ℂ)‖ = β := by
        rw [Complex.norm_real]; exact Real.norm_of_nonneg hβ0.le
      rw [hnβ, mul_comm]
      exact le_of_eq rfl)
  have hmem0 := mk_mem_physSΛEta (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 ν t hη0.le hD
  obtain ⟨I, h𝒴, hT'⟩ := hI _ hmem0
  have hF' := directTermsFamilyOn_scaled (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 (I := I)
    (a₁ := 1) (ν := ν) (eps := t) (β := β) (q := q)
    (by rw [h𝒴, hT']; exact hcont) (bgHyp_lv (k := k) m₁ hν0 hν) hβ1 hq
  refine ⟨val, 𝒴, T, I, h𝒴, hT', hF', ?_, hεnn, hε4, ?_⟩
  · intro g hg
    have hmem : ((⟨rawOf (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D', rawOf_mem_rawSub _⟩, g) :
        physParam 2 (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ)) ∈
        physVq (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 ν t q :=
      ⟨(hatStepK_physV k m₁ hk hνpos.le hν β p₁ δ ht0).2.1 g (by
        have := hg.trans_le hq
        exact this), hg⟩
    refine ⟨hmem, ?_, h𝒴, hT'⟩
    rw [physInclScaled_apply]
    refine Prod.ext rfl ?_
    funext y i
    push_cast
    ring
  · intro Kc hKc
    have hR : (0 : ℝ) ≤ 2 := by norm_num
    refine ⟨fun y Φ => labelActFamilyOn_analytic _ 1 _ hF' hN3 hp0 hR hεnn hκ0def.ge hKc y Φ,
      fun e he u => labelActFamilyOn_eq_dtAct _ 1 _ hF' hN3 hp0 hR hεnn hκ0def.ge hKc he u, ?_⟩
    intro e he u hu y Φ
    exact labelActFamilyOn_H _ 1 _ hF' hN3 hp0 hR hεnn hκ0def.ge hKc he hu y Φ

/-- **A non-vacuous instance with a nonzero source, without the premise.**  At `k = 1`, `N₁ = 6`,
the mass `nuW`, `q = 1` and every `β ≥ β₀`: the family over `physVq … 1 = physV` exists for the step
`hatStepK 1 m₁ _ nuW β (A₁ (log 3β)^p) δ`, the point with the central datum `rawOf S.D'` and the
nonzero source `g = ½ δ_{(0,0)}` lies in it, `0 ≤ ε_U`, and for every `K_c ≥ K₀` the label
activity family is jointly analytic on `physVq … 1 ×ˢ ball 0 2` and equals `dtAct` at every point. -/
theorem sourceFamilyRelative_nonneg_instance {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10)) :
    ∃ (m₁ : ℕ) (t δ β₀ BG BG₂ κ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < δ ∧ 0 ≤ famConst 3 3 BG₂ κ ∧
      (Pi.single 0 (Pi.single 0 (1 / 2)) : Fld 3 3 6 m₁ (1 + 1) 2) ≠ 0 ∧
      ∀ β : ℝ, β₀ ≤ β →
        ∀ S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁),
        S = hatStepK (N₁ := 6) 1 m₁ le_rfl nuW β (pLog A₁ p (β * 3 ^ 1)) δ →
        ∃ (hp : 0 < S.p₁) (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (6 * 3 ^ m₁) (1 + 1) 2 × (CTorus 3 3 6 m₁ (1 + 1) → Fin 2 → ℂ)) → ℂ)
          (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) (pLog A₁ p (β * 3 ^ 1)) 2
                (S.β * prop33EpsEtaScaled 3 3 2 m₁ 1 1 S.a₁ BG BG₂ κ t
                  (lvR κ t (β * 3 ^ 1) (pLog A₁ p (β * 3 ^ 1))) 0 0 (1 / S.β)) (2 * κdec - 1)
                (rawOf S.D', (0 : CTorus 3 3 6 m₁ (1 + 1) → Fin 2 → ℂ))
                (physSΛEta S S.a₁ S.ν t (1 / S.β))
                (physXW S (lvCpsi κ t (β * 3 ^ 1)) 2 2
                  (lvR κ t (β * 3 ^ 1) (pLog A₁ p (β * 3 ^ 1)))) val (physAgΘ S)
                (AgFDirPair S))
          (hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
            (physVq S 1 nuW t 1)),
          (⟨rawOf S.D', rawOf_mem_rawSub _⟩,
            (Pi.single 0 (Pi.single 0 (1 / 2)) : Fld 3 3 6 m₁ (1 + 1) 2)) ∈ physVq S 1 nuW t 1 ∧
          ∃ (hp0 : 0 < pLog A₁ p (β * 3 ^ 1))
            (hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 m₁ 1 1 S.a₁ BG BG₂ κ t
                  (lvR κ t (β * 3 ^ 1) (pLog A₁ p (β * 3 ^ 1))) 0 0 (1 / S.β)),
            ∀ {Kc : ℝ} (hKc : K0 3 3 κ0 ≤ Kc),
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
                  (labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ 6 by norm_num) hp0 (by norm_num) hεU
                    hκ0def.ge hKc r.1 r.2).H y Φ)
                  (physVq S 1 nuW t 1 ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e (he : e ∈ physVq S 1 nuW t 1) (u : ℂ),
                labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ 6 by norm_num) hp0 (by norm_num) hεU
                    hκ0def.ge hKc e u =
                  dtAct S 1 (I.atThetaOn S 1 _ hF he)
                    (show 3 ^ 1 ∣ 6 by norm_num) hp0 (by norm_num) hεU
                    hκ0def.ge hKc u) := by
  obtain ⟨m₁, t, δ, β₀, BG, BG₂, κ, CE, CF, hβ₀, ht, hδ, -, -, hB, h⟩ :=
    sourceFamilyRelative_scale_nonneg hA p hκ0def hκdecdef
  have hmem : (Pi.single 0 (Pi.single 0 (1 / 2)) : Fld 3 3 6 m₁ (1 + 1) 2) ∈
      l1Ball 3 3 6 m₁ (1 + 1) 2 := by
    show ∑ x, ∑ i, ‖(Pi.single 0 (Pi.single 0 (1 / 2)) : Fld 3 3 6 m₁ (1 + 1) 2) x i‖ < 1
    rw [l1_single_eq]
    norm_num
  refine ⟨m₁, t, δ, β₀, BG, BG₂, κ, hβ₀, ht, hδ, hB, ?_, ?_⟩
  · intro h0
    have := congrFun (congrFun h0 0) 0
    simp at this
  · intro β hβ S hS
    have hβ2 : 2 ≤ β := hβ₀.trans hβ
    have hb : 1 < β * 3 ^ 1 := by linarith
    have hp0 := pLog_pos hA p hb
    have hp : 0 < S.p₁ := by subst hS; exact hp0
    obtain ⟨val, 𝒴, T, I, -, -, hF, hpt, hεU, -, hlab⟩ := h 1 le_rfl 6 (by norm_num)
      (by norm_num) nuW nuW_pos (by unfold nuW; norm_num) β hβ _ hp0 le_rfl 1 one_pos le_rfl S
      hS hp
    obtain ⟨hg, -⟩ := hpt (Pi.single 0 (Pi.single 0 (1 / 2))) hmem
    exact ⟨hp, val, I, hF, hg, hp0, hεU, fun hKc => ⟨(hlab hKc).1, (hlab hKc).2.1⟩⟩

end Scale

end Balaban.Inhabited
