/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.SourceActivityFromTower
public import Balaban.Fluctuation.WoneChartIdentity
public import Balaban.Fluctuation.SourceFamilyRelative
public import Balaban.Inhabited.DAPhysicalTower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The source exponent as a label-activity sum

For the zero class, the exponent of the step is `W₁ + W₂` of a joint representation `Jr`.
The direct-term expansion and the free-datum `W₁` and `W₂` identities give a label activity
at every point of `physVRho`. The domain family and amplitude are independent of the datum
and source. The activity is assembled from the direct terms at
`physInclScaled (1/β) (e.1, 0)` and `physInclScaled (1/β) e` using `segAct` on the two
interpolation segments.

The previously established constant-`h₀` fibre theorem is a restriction of this family.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set
  Metric

section Fibre

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The constant-`h₀` fibre of the chart.**  The points of `physV` whose raw datum has the field
`h ≡ h₀` of the step; the complex part `Ψ` of the datum and the source are free.  This is the set on
which the step `S.withDatum D hD` is defined. -/
def physFibre (S : StepSetting d L N₁ m₁ k N ϱ) (a₁ ν eps : ℝ) : Set (physParam N S) :=
  {e | e ∈ physV S a₁ ν eps ∧
    ∀ y i, (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 y i = (S.h₀ i : ℂ)}

theorem physFibre_subset (S : StepSetting d L N₁ m₁ k N ϱ) (a₁ ν eps : ℝ) :
    physFibre S a₁ ν eps ⊆ physV S a₁ ν eps := fun _ h => h.1

end Fibre

section Shared

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {Λ F' : Type}
  [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]

/-- **`labelAct_of_directTerms` on a prescribed domain family.**  If the domain family of the
instance is `𝒴` then the activity lives on the labels `thickLabels 𝒴 hdom`. -/
theorem labelAct_of_directTerms_shared {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'}
    {ρ Rσ εU a : ℝ} {Θ₀ : Λ}
    {SΛ : Set Λ} {XW : Set (F' × F')} {val : F' → F' → ℂ → Λ → ℂ}
    {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
    {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
    (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF)
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
    {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc)
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} (hdom : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (h𝒴 : I.𝒴 = 𝒴) {ε' : ℝ} (hε' : ε' = Rσ * εU) :
    ∃ A : ℂ → LabelAct (thickLabels 𝒴 hdom) (S.blockSplit m₀ hp).Ωb ε' a κ0 Kc,
      (∀ u : ℂ, ‖u‖ < Rσ → ∀ Φ, ∑ y, (A u).H y Φ =
        val (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀) := by
  obtain ⟨A, -, hid⟩ := labelAct_of_directTerms S m₀ I hN hρ hRσ hεU hκ0 hKc
  subst h𝒴 hε'
  exact ⟨A, hid⟩

end Shared

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Set

open Classical in
/-- **The two-segment joint exponent has a label activity at every point of the open physical
chart, at the shared general tower, general `d`, `L`, `N`.**  The fixed
`sourceExponentFamily_fromTower_freeDatum_rho` is the case `d = L = 3`, `N = 2`.  The step is
`T.step k hk N₁ ν β p₁` (given up to the identification `ϱ = rhoSepG d L T.m₁` of the
separation), the block scale is `T.m₀` with `L ^ T.m₀ ∣ N₁`. -/
theorem sourceExponentFamily_fromTowerG_freeDatum_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ T.m₀ ∣ N₁) (hN : 5 < N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (ρ : ℝ) (hρ : 0 < ρ)
    (β : ℝ) (hβρ : max 1 ρ ≤ β)
    (p₁ : ℝ) (hp0 : 0 < p₁) (D : StepScaleDataG T k hk N₁ ν β p₁)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) (S : StepSetting d L N₁ T.m₁ k N ϱ)
    (hS : HEq S (T.step k hk N₁ ν β p₁)) (hp : 0 < S.p₁) :
    ∃ (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
      (hdom : ∀ Y ∈ 𝒴, IsDj T.m₀ (k + 1) Y) (εU : ℝ),
      εU = β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (ρ / β) ∧ 0 ≤ εU ∧
      ∀ Jr : S.JointRep T.t (2 * p₁), ∃ Aseg : ∀ e : physParam N S,
          e ∈ physVRho S S.a₁ S.ν T.t ρ → ℝ × ℝ →
          LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit T.m₀ hp).Ωb
            (4 * εU) (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1)),
        (∀ (e : physParam N S) (he : e ∈ physVRho S S.a₁ S.ν T.t ρ), ∀ p ∈ stepSegments,
          ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass d L N₁ T.m₁ k N ϱ)
                ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.1 : ℂ) • S.hatC x) +
              Jr.W2 (zeroClass d L N₁ T.m₁ k N ϱ) e.2
                ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.2 : ℂ) • S.hatC x) =
            ∑ y, (Aseg e he p).H y ((S.blockSplit T.m₀ hp).restr x)) ∧
        (∀ g : Fld d L N₁ T.m₁ (k + 1) N, g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N ρ →
          ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) ∈
              physVRho S S.a₁ S.ν T.t ρ,
            ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass d L N₁ T.m₁ k N ϱ) p.1 x +
                S.WtwoC (zeroClass d L N₁ T.m₁ k N ϱ) g p.2 x =
              ∑ y, (Aseg (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) he p).H y
                ((S.blockSplit T.m₀ hp).restr x)) := by
  classical
  subst hϱ
  have hS' : S = T.step k hk N₁ ν β p₁ := eq_of_heq hS
  subst hS'
  revert hp
  set S := T.step k hk N₁ ν β p₁ with hSdef
  intro hp
  have hd0 : 0 < d := by have := T.hd; omega
  have ht0 := T.t_pos
  have hr0 := D.r_pos
  have hβ1 : 1 ≤ β := le_trans (le_max_left _ _) hβρ
  have hβ0 : 0 < β := by linarith
  obtain ⟨val, 𝒴, Tt, hval, -, -, hI, hmem0, hmemg, -⟩ :=
    sourceDirectTerms_scale_fromTowerG_ray_rho T k hk N₁ hLN hN ν hνpos hν β ρ hρ hβρ p₁ ρ hρ
      le_rfl D S rfl hp
  obtain ⟨I₀, h𝒴₀, -⟩ := hI _ hmem0
  have hdom : ∀ Y ∈ 𝒴, IsDj T.m₀ (k + 1) Y := fun Y hY => I₀.dom Y (h𝒴₀ ▸ hY)
  -- the amplitude
  have hQ := cK2'_pos_general (d := d) (L := L) (N := N) (B := famConst d L T.BG₂ T.κ) T.fam_nonneg
  have hc1 := one_le_c1 d L
  set εU : ℝ := β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (ρ / β) with hεU
  have hεU0 : 0 ≤ εU :=
    (sourceEta_scaled_pos d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t _ ρ β hβ0 hρ hr0 ht0 hQ
      (by linarith)).le
  have hK0 : K0 d L T.κ0 ≤ K0 d L T.κ0 + 1 := by linarith
  have hRσ1 : (1 : ℝ) < 2 := by norm_num
  have hcfun : ∀ s : ℝ, ‖((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ)‖ ≤ 1 :=
    norm_ite_sq_le
  have hβS : 1 ≤ S.β := hβ1
  have hβS0 : 0 < S.β := hβ0
  refine ⟨𝒴, hdom, εU, hεU, hεU0, ?_⟩
  intro Jr
  have hex : ∀ e : physParam N S, e ∈ physVRho S S.a₁ S.ν T.t ρ →
      ∃ Ae : ℝ × ℝ → LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom))
          (S.blockSplit T.m₀ hp).Ωb (4 * εU) (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1)),
        ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
          Jr.W1 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
              ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.1 : ℂ) • S.hatC x) +
            Jr.W2 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) e.2
              ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.2 : ℂ) • S.hatC x) =
          ∑ y, (Ae p).H y ((S.blockSplit T.m₀ hp).restr x) := by
    intro e he
    have he1 : e ∈ physVqRho S S.a₁ S.ν T.t ρ ρ := ⟨he, he.2⟩
    have hmemE := physInclScaled_image_subset_rho S S.a₁ S.ν T.t hβρ le_rfl ⟨e, he1, rfl⟩
    have hmem0E : physInclScaled N S ((1 / S.β : ℝ) : ℂ) (e.1, 0) ∈
        physSΛEta S S.a₁ S.ν T.t (ρ / S.β) := by
      refine ⟨he.1, ?_⟩
      show (fun y i => ((1 / S.β : ℝ) : ℂ) * (0 : ℂ)) ∈ _
      simp only [mul_zero]
      refine ⟨by simp [l1Ball], ?_⟩
      simp only [norm_zero, Finset.sum_const_zero]
      exact (div_pos hρ hβS0).le
    obtain ⟨Ie, h𝒴e, -⟩ := hI _ hmemE
    obtain ⟨I0, h𝒴0, -⟩ := hI _ hmem0E
    have hεI : 0 ≤ S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (ρ / S.β) := hεU0
    obtain ⟨A0, hid0⟩ := labelAct_of_directTerms_shared S T.m₀ I0 hLN hp0
      (by norm_num : (0 : ℝ) ≤ 2) hεI T.κ0_ent hK0 hdom h𝒴0 (ε' := 2 * εU) rfl
    obtain ⟨Ag, hidg⟩ := labelAct_of_directTerms_shared S T.m₀ Ie hLN hp0
      (by norm_num : (0 : ℝ) ≤ 2) hεI T.κ0_ent hK0 hdom h𝒴e (ε' := 2 * εU) rfl
    have hε2 : 0 ≤ 2 * εU := by linarith
    have hE : 2 * εU + 2 * εU ≤ 2 * (2 * εU) := by linarith
    let c : ℝ → ℂ := fun s => ((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ)
    -- the value of the two segment sum in terms of `val`
    have hid_val : ∀ x : S.E, ‖x‖ < 2 * p₁ → ∀ s τ : ℝ, s ∈ Icc (0 : ℝ) 1 → τ ∈ Icc (0 : ℝ) 1 →
        Jr.W1 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
            ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (s : ℂ) • S.hatC x) +
          Jr.W2 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) e.2
            ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (τ : ℂ) • S.hatC x) =
        (s : ℂ) ^ 2 * val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (s : ℂ)
            (physInclScaled N S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) +
          (val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (τ : ℂ)
              (physInclScaled N S ((1 / S.β : ℝ) : ℂ) e) -
            val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (τ : ℂ)
              (physInclScaled N S ((1 / S.β : ℝ) : ℂ) (e.1, 0))) := by
      intro x hxn s τ hs hτ
      have hHB := bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hνpos.le hν
      have hpc : 2 * p₁ < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
        have hpos : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ := mul_pos hr0 hp0
        nlinarith [D.ray_margin]
      have hβne : (S.β : ℂ) ≠ 0 := by
        exact_mod_cast hβ0.ne'
      have hxb : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 →
          ∀ p, ‖((r : ℂ) • S.hatC x) p‖ ≤ 2 * p₁ := by
        intro r hr p
        exact (S.norm_smul_yhat_le_mul r x p).trans (by
          rw [abs_of_nonneg hr.1]
          exact (mul_le_of_le_one_left (norm_nonneg _) hr.2).trans hxn.le)
      obtain ⟨De, hXe, hq⟩ := he.1
      have hq' : (e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) = rawOf De := hq
      have hW1 : Jr.W1 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
          ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (s : ℂ) • S.hatC x) =
          (s : ℂ) ^ 2 * val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (s : ℂ)
            (physInclScaled N S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) := by
        rw [hq', hval, physInclScaled_zeroClass_eq, hq']
        simp only [Pi.zero_apply, zero_div, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
        exact Jr.W1_zeroClass_eq_hat_freeDatum De hXe D.core one_pos hHB T.c7_cap
          hk (R := 2) (by norm_num) T.bg1_cap T.large_block T.dom_margin
          T.coer_margin T.δc_small D.cψ_pos.le D.fl_radius hpc x hxn hs
      have hW2 : Jr.W2 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) e.2
          ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (τ : ℂ) • S.hatC x) =
          val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (τ : ℂ)
              (physInclScaled N S ((1 / S.β : ℝ) : ℂ) e) -
            val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (τ : ℂ)
              (physInclScaled N S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) := by
        rw [hq', physInclScaled_zeroClass_eq, physInclScaled_zeroClass_eq]
        have h0 : (fun y i => ((0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ) y i) /
            (S.β : ℂ)) = 0 := by funext y i; simp
        simpa only [h0, hq'] using
          (Jr.W2_eq_val_sub D.core one_pos hHB T.c7_cap (R := 2) le_rfl
            T.bg1_cap T.t_cap T.bg0_cap T.cK2_cap T.cK2'_cap T.large_block
            T.dom_margin T.coer_margin T.δc_small D.cψ_pos.le D.fl_radius
            hpc hXe e.2 hβne (S.hatC x) hxb hτ val hval)
      rw [hW1, hW2]
    refine ⟨fun p => (segAct A0 Ag hε2 hE c hcfun p).mono
      (by rw [max_self]; linarith) (by rw [max_self]; linarith) le_rfl le_rfl
      (by linarith), ?_⟩
    intro p hp'
    obtain ⟨hs1, ht1⟩ := mem_Icc_of_mem_stepSegments hp'
    filter_upwards [S.ae_hatOf_restr T.m₀ hp0 hp le_rfl, S.ae_ball hp] with x hx hχ
    have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp x).1 hχ
    have hxn2 : ‖x‖ < 2 * p₁ := by
      have : S.p₁ = p₁ := rfl
      linarith
    have key0 : ∀ u : ℝ, u ∈ Icc (0 : ℝ) 1 →
        ∑ y, (A0 (u : ℂ)).H y ((S.blockSplit T.m₀ hp).restr x) =
          val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (u : ℂ)
            (physInclScaled N S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) := by
      intro u hu
      rw [hid0 (u : ℂ) (norm_ofReal_lt_of_mem hu hRσ1)]
      simp only [hx]
    have keyg : ∀ u : ℝ, u ∈ Icc (0 : ℝ) 1 →
        ∑ y, (Ag (u : ℂ)).H y ((S.blockSplit T.m₀ hp).restr x) =
          val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (u : ℂ)
            (physInclScaled N S ((1 / S.β : ℝ) : ℂ) e) := by
      intro u hu
      rw [hidg (u : ℂ) (norm_ofReal_lt_of_mem hu hRσ1)]
      simp only [hx]
      rfl
    obtain ⟨s, t⟩ := p
    have hmono : ∀ y, ((segAct A0 Ag hε2 hE c hcfun (s, t)).mono
        (by rw [max_self]; linarith) (by rw [max_self]; linarith) le_rfl le_rfl
        (by linarith : (K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) ≤
          2 * (K0 d L T.κ0 + 1)) : LabelAct _ _ (4 * εU) _ _ _).H y =
        (segAct A0 Ag hε2 hE c hcfun (s, t)).H y := fun y => rfl
    simp only [hmono]
    by_cases h0 : t = 0
    · rw [segAct_total_zero _ _ _ _ _ _ (p := (s, t)) h0, hid_val x hxn2 s t hs1 ht1, key0 s hs1]
      subst h0
      have hz : val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) ((0 : ℝ) : ℂ)
          (physInclScaled N S ((1 / S.β : ℝ) : ℂ) e) =
          val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) ((0 : ℝ) : ℂ)
          (physInclScaled N S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) := by
        rw [hval, hval]
        simp [physInclScaled_apply, dirTermSrc]
      rw [hz, sub_self, add_zero]
      simp only [c, hs1, ite_true]
      push_cast
      rfl
    · have h1 : s = 1 := by
        rcases hp' with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact absurd h2 h0
        · exact h1
      subst h1
      rw [segAct_total_ne _ _ _ _ _ _ (p := (1, t)) h0, hid_val x hxn2 1 t hs1 ht1, key0 t ht1, keyg t ht1]
      have := key0 1 hs1
      rw [Complex.ofReal_one] at this ⊢
      rw [this]
      simp only [one_pow, one_mul]
      ring
  choose Aseg hAseg using hex
  refine ⟨Aseg, fun e he p hp' => hAseg e he p hp', ?_⟩
  intro g hg
  have hmemS : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) ∈
      physVRho S S.a₁ S.ν T.t ρ := ⟨⟨S.D', D.xi, rfl⟩, hg⟩
  refine ⟨hmemS, fun p hp' => ?_⟩
  obtain ⟨hs1, ht1⟩ := mem_Icc_of_mem_stepSegments hp'
  have hle : S.p₁ ≤ 2 * p₁ := by
    show p₁ ≤ 2 * p₁
    linarith
  filter_upwards [hAseg _ hmemS p hp',
    Jr.ae_W1_path (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) hp hle S.D' S.hh₀ D.xi hs1,
    Jr.ae_W2_path (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) hp hle S.D' S.hh₀ D.xi g ht1]
    with x h1 h2 h3
  have e1 : S.WoneC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) p.1 x = _ := h2.symm
  have e2 : S.WtwoC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g p.2 x = _ := h3.symm
  rw [e1, e2]
  exact h1

/-- The amplitude at the fixed tower `T.toG` agrees with the amplitude at the fixed tower `T`
(`d = L = 3`, `N = 2`, `m₀ = 1`): `β_k = β 3^{k(3-2)} = β 3^k`. -/
theorem sourceEps_toG_eq {κmin : ℝ} (T : StepTower κmin) (k : ℕ) (β p₁ r : ℝ) :
    β * prop33EpsEtaScaled 3 3 2 T.m₁ k T.toG.m₀ 1 T.toG.BG T.toG.BG₂ T.toG.κ T.toG.t
        (lvRG 3 3 2 T.toG.κ T.toG.t (β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2))) p₁) 0 0 r =
      β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 r := by
  have e : ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  rw [e]
  rfl

open Classical in
/-- **The activity supplied by the general tower applies to either interpolation segment at any
datum in the complex chart and any source in the radius-`ρ` ball.** -/
theorem sourceExponentFamily_fromTowerG_freeDatum_slice_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ T.m₀ ∣ N₁) (hN : 5 < N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1)
    (ρ : ℝ) (hρ : 0 < ρ) (β : ℝ) (hβρ : max 1 ρ ≤ β)
    (p₁ : ℝ) (hp0 : 0 < p₁) (D : StepScaleDataG T k hk N₁ ν β p₁)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) (S : StepSetting d L N₁ T.m₁ k N ϱ)
    (hS : HEq S (T.step k hk N₁ ν β p₁))
    (hp : 0 < S.p₁) (D' : BgData S.G' N)
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 T.t D')
    (g : Fld d L N₁ T.m₁ (k + 1) N)
    (hg : g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N ρ)
    (Jr : S.JointRep T.t (2 * p₁)) :
    ∃ (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
      (hdom : ∀ Y ∈ 𝒴, IsDj T.m₀ (k + 1) Y) (εU : ℝ),
      εU = β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (ρ / β) ∧ 0 ≤ εU ∧
      ∃ A : ℝ × ℝ → LabelAct
          ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit T.m₀ hp).Ωb
          (4 * εU) (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1)),
        ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
          Jr.W1 (zeroClass d L N₁ T.m₁ k N ϱ) (rawOf D', (p.1 : ℂ) • S.hatC x) +
            Jr.W2 (zeroClass d L N₁ T.m₁ k N ϱ) g (rawOf D', (p.2 : ℂ) • S.hatC x) =
            ∑ y, (A p).H y ((S.blockSplit T.m₀ hp).restr x) := by
  obtain ⟨𝒴, hdom, εU, hεU, hεU0, hfamily⟩ :=
    sourceExponentFamily_fromTowerG_freeDatum_rho T k hk N₁ hLN hN ν hνpos hν
      ρ hρ β hβρ p₁ hp0 D hϱ S hS hp
  obtain ⟨Aseg, hAseg, -⟩ := hfamily Jr
  let e : physParam N S := (⟨rawOf D', rawOf_mem_rawSub _⟩, g)
  have he : e ∈ physVRho S S.a₁ S.ν T.t ρ := ⟨⟨D', hX, rfl⟩, hg⟩
  exact ⟨𝒴, hdom, εU, hεU, hεU0, Aseg e he, hAseg e he⟩

open Classical in
/-- **The source exponent as a label-activity sum on the fibre `h ≡ h₀`, at the shared general
tower, at source radius `ρ`.**  The fixed `sourceExponentFamily_fromTower_rho` is the case
`d = L = 3`, `N = 2`. -/
theorem sourceExponentFamily_fromTowerG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ T.m₀ ∣ N₁) (hN : 5 < N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (ρ : ℝ) (hρ : 0 < ρ)
    (β : ℝ) (hβρ : max 1 ρ ≤ β)
    (p₁ : ℝ) (hp0 : 0 < p₁) (D : StepScaleDataG T k hk N₁ ν β p₁)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) (S : StepSetting d L N₁ T.m₁ k N ϱ)
    (hS : HEq S (T.step k hk N₁ ν β p₁)) (hp : 0 < S.p₁) :
    ∃ (Jr : S.JointRep T.t (2 * p₁)) (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
      (hdom : ∀ Y ∈ 𝒴, IsDj T.m₀ (k + 1) Y) (εU : ℝ),
      εU = β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (ρ / β) ∧ 0 ≤ εU ∧
      ∃ Aseg : ∀ e : physParam N S, e ∈ physFibreRho S S.a₁ S.ν T.t ρ → ℝ × ℝ →
          LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit T.m₀ hp).Ωb
            (4 * εU) (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1)),
        (∀ (e : physParam N S) (he : e ∈ physFibreRho S S.a₁ S.ν T.t ρ), ∀ p ∈ stepSegments,
          ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass d L N₁ T.m₁ k N ϱ)
                ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.1 : ℂ) • S.hatC x) +
              Jr.W2 (zeroClass d L N₁ T.m₁ k N ϱ) e.2
                ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.2 : ℂ) • S.hatC x) =
            ∑ y, (Aseg e he p).H y ((S.blockSplit T.m₀ hp).restr x)) ∧
        (∀ g : Fld d L N₁ T.m₁ (k + 1) N, g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N ρ →
          ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) ∈
              physFibreRho S S.a₁ S.ν T.t ρ,
            ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass d L N₁ T.m₁ k N ϱ) p.1 x +
                S.WtwoC (zeroClass d L N₁ T.m₁ k N ϱ) g p.2 x =
              ∑ y, (Aseg (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) he p).H y
                ((S.blockSplit T.m₀ hp).restr x)) := by
  obtain ⟨Jr, -, -⟩ := wone_chartIdentity_fromTowerG_rho T k hk N₁ ν hνpos hν β p₁ hp0 D hϱ S hS
  obtain ⟨𝒴, hdom, εU, hεU, hεU0, hfamily⟩ :=
    sourceExponentFamily_fromTowerG_freeDatum_rho T k hk N₁ hLN hN ν hνpos hν
      ρ hρ β hβρ p₁ hp0 D hϱ S hS hp
  obtain ⟨Aseg, hAseg, hslice⟩ := hfamily Jr
  refine ⟨Jr, 𝒴, hdom, εU, hεU, hεU0,
    (fun e he p => Aseg e he.1 p), ?_, ?_⟩
  · intro e he p hp'
    exact hAseg e he.1 p hp'
  · intro g hg
    obtain ⟨he, hval⟩ := hslice g hg
    refine ⟨⟨he, fun y i => ?_⟩, ?_⟩
    · subst hϱ
      have hS' : S = T.step k hk N₁ ν β p₁ := eq_of_heq hS
      subst hS'
      exact (T.step k hk N₁ ν β p₁).hh₀ y i
    · exact hval


open Classical in
/-- **The source exponent as a label-activity sum on the constant-`h₀` fibre, at the shared general
tower `T : StepTowerG d L N κmin`.**  The fixed `sourceExponentFamily_fromTower` is the case
`d = L = 3`, `N = 2`: see that statement for the content of the value and slice clauses. -/
theorem sourceExponentFamily_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ T.m₀ ∣ N₁) (hN : 5 < N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β : ℝ) (hβ1 : 1 ≤ β)
    (p₁ : ℝ) (hp0 : 0 < p₁) (D : StepScaleDataG T k hk N₁ ν β p₁)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) (S : StepSetting d L N₁ T.m₁ k N ϱ)
    (hS : HEq S (T.step k hk N₁ ν β p₁)) (hp : 0 < S.p₁) :
    ∃ (Jr : S.JointRep T.t (2 * p₁)) (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
      (hdom : ∀ Y ∈ 𝒴, IsDj T.m₀ (k + 1) Y) (εU : ℝ),
      εU = β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / β) ∧ 0 ≤ εU ∧
      ∃ Aseg : ∀ e : physParam N S, e ∈ physFibre S S.a₁ S.ν T.t → ℝ × ℝ →
          LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit T.m₀ hp).Ωb
            (4 * εU) (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1)),
        (∀ (e : physParam N S) (he : e ∈ physFibre S S.a₁ S.ν T.t), ∀ p ∈ stepSegments,
          ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass d L N₁ T.m₁ k N ϱ)
                ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.1 : ℂ) • S.hatC x) +
              Jr.W2 (zeroClass d L N₁ T.m₁ k N ϱ) e.2
                ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.2 : ℂ) • S.hatC x) =
            ∑ y, (Aseg e he p).H y ((S.blockSplit T.m₀ hp).restr x)) ∧
        (∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < 1 →
          ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) ∈
              physFibre S S.a₁ S.ν T.t,
            ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass d L N₁ T.m₁ k N ϱ) p.1 x +
                S.WtwoC (zeroClass d L N₁ T.m₁ k N ϱ) g p.2 x =
              ∑ y, (Aseg (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) he p).H y
                ((S.blockSplit T.m₀ hp).restr x)) :=
  sourceExponentFamily_fromTowerG_rho T k hk N₁ hLN hN ν hνpos hν 1 one_pos β
    (max_le hβ1 hβ1) p₁ hp0 D hϱ S hS hp

open Classical in
/-- The two-segment joint exponent has a label activity at every point of the open physical chart. -/
theorem sourceExponentFamily_fromTower_freeDatum_rho {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (ρ : ℝ) (hρ : 0 < ρ) (β : ℝ)
    (hβρ : max 1 ρ ≤ β)
    (p₁ : ℝ) (hp0 : 0 < p₁) (D : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁) :
    ∃ (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
      (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y) (εU : ℝ),
      εU = β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / β) ∧ 0 ≤ εU ∧
      ∀ Jr : S.JointRep T.t (2 * p₁), ∃ Aseg : ∀ e : physParam 2 S, e ∈ physVRho S S.a₁ S.ν T.t ρ → ℝ × ℝ →
          LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit 1 hp).Ωb
            (4 * εU) (2 * T.κdec - 1) T.κ0 (2 * (K0 3 3 T.κ0 + 1)),
        (∀ (e : physParam 2 S) (he : e ∈ physVRho S S.a₁ S.ν T.t ρ), ∀ p ∈ stepSegments,
          ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.1 : ℂ) • S.hatC x) +
              Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.2 : ℂ) • S.hatC x) =
            ∑ y, (Aseg e he p).H y ((S.blockSplit 1 hp).restr x)) ∧
        (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 ρ →
          ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) ∈
              physVRho S S.a₁ S.ν T.t ρ,
            ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) p.1 x +
                S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g p.2 x =
              ∑ y, (Aseg (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) he p).H y
                ((S.blockSplit 1 hp).restr x)) := by
  obtain ⟨𝒴, hdom, εU, hεU, hεU0, hfam⟩ :=
    sourceExponentFamily_fromTowerG_freeDatum_rho T.toG k hk N₁ (by simpa using h3N) hN ν hνpos
      (by simpa using hν) ρ hρ β hβρ p₁ hp0 (StepTower.scaleDataG_of_fixed T D)
      (rhoSepG_three _).symm S
      (by rw [hS]; exact (StepTower.toG_step_heq T k hk N₁ ν β p₁).symm) hp
  exact ⟨𝒴, hdom, εU, hεU.trans (sourceEps_toG_eq T k β p₁ _), hεU0, hfam⟩

open Classical in
/-- The activity supplied by the tower applies to either interpolation segment at any
datum in the complex chart and any source in the radius-`ρ` ball. -/
theorem sourceExponentFamily_freeDatum_slice_rho {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    (ρ : ℝ) (hρ : 0 < ρ) (β : ℝ) (hβρ : max 1 ρ ≤ β)
    (p₁ : ℝ) (hp0 : 0 < p₁) (D : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁) (D' : BgData S.G' 2)
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 T.t D')
    (g : Fld 3 3 N₁ T.m₁ (k + 1) 2)
    (hg : g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 ρ)
    (Jr : S.JointRep T.t (2 * p₁)) :
    ∃ (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
      (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y) (εU : ℝ),
      εU = β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / β) ∧ 0 ≤ εU ∧
      ∃ A : ℝ × ℝ → LabelAct
          ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit 1 hp).Ωb
          (4 * εU) (2 * T.κdec - 1) T.κ0 (2 * (K0 3 3 T.κ0 + 1)),
        ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
          Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
              (rawOf D', (p.1 : ℂ) • S.hatC x) +
            Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g
              (rawOf D', (p.2 : ℂ) • S.hatC x) =
            ∑ y, (A p).H y ((S.blockSplit 1 hp).restr x) := by
  obtain ⟨𝒴, hdom, εU, hεU, hεU0, hfam⟩ :=
    sourceExponentFamily_fromTowerG_freeDatum_slice_rho T.toG k hk N₁ (by simpa using h3N) hN ν
      hνpos (by simpa using hν) ρ hρ β hβρ p₁ hp0 (StepTower.scaleDataG_of_fixed T D)
      (rhoSepG_three _).symm S
      (by rw [hS]; exact (StepTower.toG_step_heq T k hk N₁ ν β p₁).symm) hp D' hX g hg Jr
  exact ⟨𝒴, hdom, εU, hεU.trans (sourceEps_toG_eq T k β p₁ _), hεU0, hfam⟩

open Classical in
theorem sourceExponentFamily_fromTower_rho {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (ρ : ℝ) (hρ : 0 < ρ) (β : ℝ)
    (hβρ : max 1 ρ ≤ β)
    (p₁ : ℝ) (hp0 : 0 < p₁) (D : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁) :
    ∃ (Jr : S.JointRep T.t (2 * p₁)) (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
      (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y) (εU : ℝ),
      εU = β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / β) ∧ 0 ≤ εU ∧
      ∃ Aseg : ∀ e : physParam 2 S, e ∈ physFibreRho S S.a₁ S.ν T.t ρ → ℝ × ℝ →
          LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit 1 hp).Ωb
            (4 * εU) (2 * T.κdec - 1) T.κ0 (2 * (K0 3 3 T.κ0 + 1)),
        (∀ (e : physParam 2 S) (he : e ∈ physFibreRho S S.a₁ S.ν T.t ρ), ∀ p ∈ stepSegments,
          ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.1 : ℂ) • S.hatC x) +
              Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.2 : ℂ) • S.hatC x) =
            ∑ y, (Aseg e he p).H y ((S.blockSplit 1 hp).restr x)) ∧
        (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 ρ →
          ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) ∈
              physFibreRho S S.a₁ S.ν T.t ρ,
            ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) p.1 x +
                S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g p.2 x =
              ∑ y, (Aseg (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) he p).H y
                ((S.blockSplit 1 hp).restr x)) := by
  obtain ⟨Jr, 𝒴, hdom, εU, hεU, hεU0, hfam⟩ :=
    sourceExponentFamily_fromTowerG_rho T.toG k hk N₁ (by simpa using h3N) hN ν hνpos
      (by simpa using hν) ρ hρ β hβρ p₁ hp0 (StepTower.scaleDataG_of_fixed T D)
      (rhoSepG_three _).symm S
      (by rw [hS]; exact (StepTower.toG_step_heq T k hk N₁ ν β p₁).symm) hp
  exact ⟨Jr, 𝒴, hdom, εU, hεU.trans (sourceEps_toG_eq T k β p₁ _), hεU0, hfam⟩

open Classical in
/-- **The source exponent as a label-activity sum on the constant-`h₀` fibre, at the shared tower.**
For the step `S = T.step k hk N₁ ν β p₁` of the tower `T` with a per-scale package `D` (and
`1 ≤ β`), there are a joint representation `Jr`, a domain family `𝒴` with its proof `hdom`, and for
every `e` of the fibre `physFibre S S.a₁ S.ν T.t` an activity `Aseg e he p` for `p` in `stepSegments`
on the labels `(thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)` (amplitude `4 ε_U`, rate
`2 κ_dec - 1`, `κ₀ = T.κ0`, entropy constant `2 (K₀(T.κ0) + 1)`) with:

1. the value clause: for every `p = (s,t)` of `stepSegments`, for `ν_{p₁}`-almost every `x`,
   `Jr.W1 (e.1, s ψ̂) + Jr.W2 e.2 (e.1, t ψ̂) = ∑_y (Aseg e he p).H y (restr x)`;
2. the slice clause: for every source `g` with `∑ |g| < 1` the point `(rawOf S.D', g)` is in the
   fibre and, for every `p` in `stepSegments`, `S.WoneC p.1 x + S.WtwoC g p.2 x =
   ∑_y (Aseg (rawOf S.D', g) _ p).H y (restr x)` almost everywhere (the `hW` of `StepActivityBoundC`
   on the same labels as `sourceActivityC_scale_fromTower`).

`ε_U = β · prop33EpsEtaScaled … (1/β)` is independent of `e`, and `0 ≤ ε_U`. -/
theorem sourceExponentFamily_fromTower {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β : ℝ) (hβ1 : 1 ≤ β)
    (p₁ : ℝ) (hp0 : 0 < p₁) (D : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁) :
    ∃ (Jr : S.JointRep T.t (2 * p₁)) (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
      (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y) (εU : ℝ),
      εU = β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β) ∧ 0 ≤ εU ∧
      ∃ Aseg : ∀ e : physParam 2 S, e ∈ physFibre S S.a₁ S.ν T.t → ℝ × ℝ →
          LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit 1 hp).Ωb
            (4 * εU) (2 * T.κdec - 1) T.κ0 (2 * (K0 3 3 T.κ0 + 1)),
        (∀ (e : physParam 2 S) (he : e ∈ physFibre S S.a₁ S.ν T.t), ∀ p ∈ stepSegments,
          ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.1 : ℂ) • S.hatC x) +
              Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.2 : ℂ) • S.hatC x) =
            ∑ y, (Aseg e he p).H y ((S.blockSplit 1 hp).restr x)) ∧
        (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
          ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) ∈
              physFibre S S.a₁ S.ν T.t,
            ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) p.1 x +
                S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g p.2 x =
              ∑ y, (Aseg (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) he p).H y
                ((S.blockSplit 1 hp).restr x)) := by
  have h := sourceExponentFamily_fromTower_rho T k hk N₁ h3N hN ν hνpos hν 1 one_pos β
    (max_le hβ1 hβ1)
    p₁ hp0 D S hS hp
  exact h

end Balaban.Inhabited
