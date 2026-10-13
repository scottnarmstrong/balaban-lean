/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsFamilyJoint

/-!
# The observable coefficient family: the bound in the form of the coefficient theorem

`obsFamily_full_fromTower` bounds `obsCoeffParam` by `(B₁ + B₂) e^{-λ dExt T'}` with explicit
constants `B₁, B₂`.  Here `B₁ + B₂ ≤ C · obsPrefactor p s b` with `C` independent of the scale
(`obs_B1_add_B2_le_prefactor`), and the family statement is repackaged with the bound
`C · obsPrefactor p s (β 3^k) · e^{-(3/2) κ_dec dExt T'}` (`obsFamily_prefactor_fromTower`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep MeasureTheory Metric

/-- **The constants `B₁ + B₂` of the family bound are at most `C · obsPrefactor`.**  `B₁` and `B₂`
are the expressions of `obsFamily_full_fromTower` (with `p₁` for `S.p₁` and the sum over the
remainder labels, whose weighted entropy sum is bounded by `K₀ + 1`), at the scale `b > 1`
with `p₁ ≤ A₁ (log b)^p`.  The constant `C` depends only on the tower, `A₁`, `p`, `C_R`, `s`. -/
theorem obs_B1_add_B2_le_prefactor {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {CR s : ℝ} (hCR : 0 < CR) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 1 < b → ∀ p₁ : ℝ, 0 ≤ p₁ → p₁ ≤ pLog A₁ p b →
      ∀ (ι : Type) [Fintype ι] (dl : ι → ℝ),
      (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          (p₁ / lvCpsi T.κ T.t b) ^ 2 * Real.exp (-T.κ0 * dl r) ≤
        8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) * (p₁ / lvCpsi T.κ T.t b) ^ 2 *
          (K0 3 3 T.κ0 + 1)) →
      (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t b) *
          (CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' * p₁ / obsRg CR s (p : ℝ) b) *
          (((2 * 3 ^ (3 * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 3 3) *
          ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) +
        CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' *
          (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
            (p₁ / lvCpsi T.κ T.t b) ^ 2 * Real.exp (-T.κ0 * dl r)) ≤
        C * obsPrefactor p s b := by
  classical
  have hK0 := T.marks_K0_pos
  have hc1 : 0 < c1 3 3 := by linarith [one_le_c1 3 3]
  have ht := T.t_pos
  have hQ : 0 < cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) := cK2'_pos' T.fam_nonneg
  have hκ1 : 0 < lvKappa T.κ T.t := lvKappa_pos T.κ ht
  obtain ⟨CPEv, hCPEv⟩ : ∃ CPEv : ℝ, CPEv = CPE 3 3
      ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
      (2 * T.κdec - 1) T.κ0 T.κ' := ⟨_, rfl⟩
  have hCPE0 : 0 ≤ CPEv := by rw [hCPEv]; unfold CPE; positivity
  obtain ⟨nn, hnn⟩ : ∃ nn : ℝ, nn = ((2 * 3 ^ (3 * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 3 3 :=
    ⟨_, rfl⟩
  have hnn0 : 0 ≤ nn := by rw [hnn]; positivity
  obtain ⟨Ko, hKo⟩ : ∃ Ko : ℝ, Ko = (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 +
      K0 3 3 T.κ0 := ⟨_, rfl⟩
  obtain ⟨EE, hEE⟩ : ∃ EE : ℝ, EE = Real.exp ((T.κ' - T.κ0) * cG 3 3) := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) := ⟨_, rfl⟩
  have hκ'0 : min (2 * T.κdec) T.κ' - T.κ0 ≤ T.κ' - T.κ0 := by
    linarith [min_le_right (2 * T.κdec) T.κ']
  refine ⟨max (Q * T.t / lvKappa T.κ T.t * CPEv * A₁ * nn * Ko ^ 2 * EE * CR)
    (CPEv * (8 * (Q * T.t) * (A₁ / lvKappa T.κ T.t) ^ 2 * (K0 3 3 T.κ0 + 1))), ?_, ?_⟩
  · refine le_trans ?_ (le_max_right _ _)
    rw [hQdef] at *
    positivity
  intro b hb p₁ hp0 hp₁ ι _ dl hsum
  have hb0 : 0 < b := by linarith
  have hb1 : 1 < b := hb
  have hcψ : lvCpsi T.κ T.t b = lvKappa T.κ T.t * Real.sqrt b := lvCpsi_eq _ _ _
  have hp₁w : p₁ ≤ A₁ * obsW (p : ℝ) b := by
    rw [obsW_mul_eq_pLog]; exact hp₁
  have hw0 : 0 ≤ obsW (p : ℝ) b := (obsW_pos _ _ hb1).le
  have hwpos := obsW_pos (p : ℝ) b hb1
  have hRgpos : 0 < obsRg CR s (p : ℝ) b := by
    unfold obsRg; exact div_pos (Real.rpow_pos_of_pos hb0 _) (by positivity)
  have hX := obsRg_inv_amp (CR := CR) (s := s) (p := (p : ℝ)) hCR hb1
  have hbq : 0 ≤ b ^ (-(1 / 2 : ℝ) - s) := Real.rpow_nonneg hb0.le _
  have hQt : 0 ≤ cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t := by positivity
  have hmin : Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) ≤ EE := by
    rw [hEE]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hκ'0 (by unfold cG; positivity))
  have hKo0 : 0 ≤ Ko := by rw [hKo]; linarith
  have hmain := obs_B1_le (Q := cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ)) (t := T.t)
    (CPE := CPEv) (n := nn) (K := Ko)
    (E := Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3)) (A₁ := A₁)
    (κ1 := lvKappa T.κ T.t) (w := obsW (p : ℝ) b) (b := b) (p₁ := p₁)
    (cψ := lvCpsi T.κ T.t b) (Rg := obsRg CR s (p : ℝ) b)
    (X := CR * obsW (p : ℝ) b ^ 4 * b ^ (-(1 / 2 : ℝ) - s))
    hQt hCPE0 hnn0 (Real.exp_pos _).le hκ1 hb0 hRgpos hp₁w hcψ hX
  have hB2 := obs_B2_le (CPE := CPEv)
    (Q := cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ)) (t := T.t) (K := K0 3 3 T.κ0 + 1) (A₁ := A₁)
    (κ1 := lvKappa T.κ T.t) (w := obsW (p : ℝ) b) (b := b) (p₁ := p₁)
    (cψ := lvCpsi T.κ T.t b) hCPE0 hQt (by linarith) hκ1 hb0 hp0 hp₁w hcψ
  rw [← hCPEv, ← hnn, ← hKo]
  rw [hCPEv, hnn, hKo] at hmain
  rw [← hCPEv, ← hnn, ← hKo] at hmain
  have hS : CPEv * (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
      (p₁ / lvCpsi T.κ T.t b) ^ 2 * Real.exp (-T.κ0 * dl r)) ≤
      CPEv * (8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) * (p₁ / lvCpsi T.κ T.t b) ^ 2 *
        (K0 3 3 T.κ0 + 1)) := mul_le_mul_of_nonneg_left hsum hCPE0
  have hc0 : 0 ≤ Q * T.t / lvKappa T.κ T.t * CPEv * A₁ * nn * Ko ^ 2 := by
    rw [hQdef]; positivity
  have hP1 : 0 ≤ obsW (p : ℝ) b ^ 4 * b ^ (-(1 / 2 : ℝ) - s) := by positivity
  have hP2 : 0 ≤ obsW (p : ℝ) b ^ 2 / b := by positivity
  have hB1' : (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t b) *
          (CPEv * p₁ / obsRg CR s (p : ℝ) b) * nn * Ko ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) ≤
      (Q * T.t / lvKappa T.κ T.t * CPEv * A₁ * nn * Ko ^ 2 * EE * CR) *
        (obsW (p : ℝ) b ^ 4 * b ^ (-(1 / 2 : ℝ) - s)) := by
    refine hmain.trans ?_
    rw [hQdef]
    have : (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvKappa T.κ T.t * CPEv * A₁ * nn *
        Ko ^ 2 * Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3)) *
        (CR * obsW (p : ℝ) b ^ 4 * b ^ (-(1 / 2 : ℝ) - s)) ≤
        (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvKappa T.κ T.t * CPEv * A₁ * nn *
        Ko ^ 2 * EE) * (CR * obsW (p : ℝ) b ^ 4 * b ^ (-(1 / 2 : ℝ) - s)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin (by rw [← hQdef]; exact hc0))
        (by positivity)
    calc _ ≤ _ := this
      _ = _ := by ring
  have hB2' : CPEv * (8 * (Q * T.t) * (p₁ / lvCpsi T.κ T.t b) ^ 2 * (K0 3 3 T.κ0 + 1)) ≤
      CPEv * (8 * (Q * T.t) * (A₁ / lvKappa T.κ T.t) ^ 2 * (K0 3 3 T.κ0 + 1)) *
        (obsW (p : ℝ) b ^ 2 / b) := by
    rw [mul_div_assoc'] at *
    rw [← hQdef] at hB2
    exact hB2
  unfold obsPrefactor
  rw [← hQdef] at hS
  have a1 := mul_le_mul_of_nonneg_right (le_max_left
    (Q * T.t / lvKappa T.κ T.t * CPEv * A₁ * nn * Ko ^ 2 * EE * CR)
    (CPEv * (8 * (Q * T.t) * (A₁ / lvKappa T.κ T.t) ^ 2 * (K0 3 3 T.κ0 + 1)))) hP1
  have a2 := mul_le_mul_of_nonneg_right (le_max_right
    (Q * T.t / lvKappa T.κ T.t * CPEv * A₁ * nn * Ko ^ 2 * EE * CR)
    (CPEv * (8 * (Q * T.t) * (A₁ / lvKappa T.κ T.t) ^ 2 * (K0 3 3 T.κ0 + 1)))) hP2
  rw [hQdef] at hB1' hB2' hS a1 a2 ⊢
  nlinarith [hB1', hB2', hS, a1, a2]

open Classical in
/-- **The observable coefficient family, with the bound in the form of the coefficient theorem.**
The statement of `obsFamily_full_fromTower` (same labels, activity, `Ev`, analyticity, support,
locality, fibre value), with the bound clause replaced by
`‖obsCoeffParam … θ T'‖ ≤ C · obsPrefactor p s (β 3^k) · e^{-(3/2) κ_dec dExt T'}`, where `C`
depends only on the tower, `A₁`, `p`, `C_R`, `s` (it is chosen with the thresholds, before the
scale). -/
theorem obsFamily_prefactor_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF C : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 ≤ C ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ (Dsc : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0
          (K0 3 3 T.κ0 + 1)),
        2 * εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2)
          (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y),
            IsDj 1 (k + 1) Y),
        ∃ hR : 0 ≤ obsRg CR s (p : ℝ) (β * 3 ^ k),
          1 < obsRg CR s (p : ℝ) (β * 3 ^ k) ∧
          obsRg CR s (p : ℝ) (β * 3 ^ k) * max (εH + εH) εH ≤
            stepTheta 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
              (2 * T.κdec - 1) T.κ0 T.κ' ∧
          ∃ Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ,
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)})) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y)) ∧
      (∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S 1 hp Ev D (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsi T.κ T.t (β * 3 ^ k))
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / (lvCpsi T.κ T.t (β * 3 ^ k)))
          (2 * T.κdec) (rootCube (m₀ := 1) (blockIndex y)) ∧
        ObsRayIdentity S 1 hp
          (fun ψh => svec (lvLow N₁ T.m₁ k (rhoSep T.m₁))
            (flFieldOne S.G' (lvLow N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ 1 ν D
              (hatLift S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) D ψh)) y i) Ev D
          (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))) ∧
      ((∀ m : ObsMarkIdx S, Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ
        (obsLab (Lab.sum Lab) hdj)
        (fun θ t => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
          (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t 1)
        (fun _ : Unit => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
          (LocalCover.fam 1 y)) m)
        (fun _ _ _ => blockMarkC S 1 hp m.1 m.2) (2 * T.κdec - 1)
        (fun _ => S.p₁ * Real.exp ((2 * T.κdec - 1) * (obsLab (Lab.sum Lab) hdj).dl
          (obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)))
        (physVq S S.a₁ S.ν T.t q) (ball (0 : ℂ) (3 / 2)) (physCarrier S 1 hp))) ∧
      Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ (obsLab (Lab.sum Lab) hdj)
        (fun θ t => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
          (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t 1)
        (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
            (rootCube (m₀ := 1) (blockIndex y))))
        (obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t)) (2 * T.κdec - 1)
        (fun _ => 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2)
        (physVq S S.a₁ S.ν T.t q) (ball (0 : ℂ) (3 / 2)) (physCarrier S 1 hp))) ∧
      (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ),
      ((∀ (m : ObsMarkIdx S) (S' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
        (K := k + 1) 1 (k + 1) Set.univ)),
      AnalyticOnNhd ℂ (fun θ => markIntTerm (S.blockSplit 1 hp).μ ((fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ) θ)
        (obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (blockMarkC S 1 hp m.1 m.2) S')
        (physVq S S.a₁ S.ν T.t q)) ∧
    AnalyticOnNhd ℂ (fun θ => kernelMarkSum
      (fun m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
      (fun m S' => markIntTerm (S.blockSplit 1 hp).μ ((fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ) θ) (obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)
        (blockMarkC S 1 hp m.1 m.2) S') T') (physVq S S.a₁ S.ν T.t q) ∧
    AnalyticOnNhd ℂ (fun θ => gsumCoeff (S.blockSplit 1 hp).μ (obsLab (Lab.sum Lab) hdj)
      (fun t => (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ) θ t 1)
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))))
      (obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) T')
      (physVq S S.a₁ S.ν T.t q) ∧
    AnalyticOnNhd ℂ (fun θ => obsCoeffParam (S.blockSplit 1 hp).μ (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T')
      (physVq S S.a₁ S.ν T.t q) ∧
      (∀ θ ∈ (physVq S S.a₁ S.ν T.t q),
        ‖obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T'‖ ≤
      C * obsPrefactor p s (β * 3 ^ k) * Real.exp (-(3 / 2 * T.κdec) * dExt T')) ∧
      (∀ θ ∈ (physVq S S.a₁ S.ν T.t q),
        obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T' ≠ 0 →
        rootCube (m₀ := 1) (blockIndex y) ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')) ∧
      (∀ θ ∈ (physVq S S.a₁ S.ν T.t q), ∀ θ' ∈ (physVq S S.a₁ S.ν T.t q),
        agreeOn (thickSet S.G' (sitesOf T')) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) → (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) →
        obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T' =
        obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ' T'))) ∧
      ∀ (D : BgData S.G' 2) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i', ‖g x' i'‖ < q →
          (S.withDatum D hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
            ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ)
      ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) T'
    := by
  classical
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, hmain⟩ := obsFamily_full_fromTower T hA p hCR hs0 hs
  obtain ⟨C, hC0, hC⟩ := obs_B1_add_B2_le_prefactor T hA p hCR (s := s)
  refine ⟨β₀, CE, CF, C, h3, hCE, hCF, hC0, fun k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q
    hq0 hq1 Dsc S hS hp => ?_⟩
  obtain ⟨Lb, instLb, Lab, εH, hεH, A, hεb, hrest⟩ := hmain k hk N₁ h3N hN ν hνpos hν β hβ p₁
    hp0 hp₁ q hq0 hq1 Dsc S hS hp
  refine ⟨Lb, instLb, Lab, εH, hεH, A, hεb, fun y i hdj => ?_⟩
  obtain ⟨hR, h1, hεΘ, Ev, ha, hd, hb, hmk, hfam, hT', hv⟩ := hrest y i hdj
  refine ⟨hR, h1, hεΘ, Ev, ha, hd, hb, hmk, hfam, ⟨fun T' => ?_, hv⟩⟩
  obtain ⟨a1, a2, a3, a4, hbd, hsp, hlc⟩ := hT' T'
  refine ⟨a1, a2, a3, a4, fun θ hθ => ?_, hsp, hlc⟩
  have hb0 := hbd θ hθ
  have hβ3 : 3 ≤ β := le_trans h3 hβ
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hb1 : 1 < β * 3 ^ k := by nlinarith
  subst hS
  obtain ⟨hhalf, -⟩ := hmk _ Dsc.xi
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsum, -⟩ := hhalf
  have hB := hC (β * 3 ^ k) hb1 _ hp0.le hp₁ _ _ hsum
  rw [obsFamilyRate_eq_tower T] at hb0
  exact hb0.trans (mul_le_mul_of_nonneg_right hB (Real.exp_nonneg _))

end Balaban.Inhabited
