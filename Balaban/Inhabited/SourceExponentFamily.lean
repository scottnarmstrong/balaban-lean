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
# The source exponent as a label-activity sum, on the constant-`h₀` fibre of the chart

For the zero class the exponent of the step is `W₁ + W₂` of a joint representation `Jr`.  Its value
in terms of the physical direct terms is known on the chart points `e` whose raw datum has the
constant field `h ≡ h₀` (`sourcePhysVal_jointRep_zero`), and its label-activity form is known only at
the datum of the step itself (`stepActivityBound_zeroClass_source_of_directTerms_exposed`).  Here
both are put together on the **fibre**
`V₀ = physFibre S a₁ ν ε = { e ∈ physV | e.1.2 ≡ h₀ }`.

**Why the fibre and not all of `physV`.**  The identification of `W₁` at a chart datum goes through
the step `S.withDatum D hD`, which exists only for data `D` with `D.h = h₀`; for a chart datum with
a non-constant complex field `h` there is no `StepSetting`, hence no `JointRep` identity.  The
source `g` and the complex part of the datum `Ψ` are free on the fibre.

At the shared tower `T` and a per-scale package `D` (the same data as
`sourceActivityC_scale_fromTower`), `sourceExponentFamily_fromTower` gives: one domain family `𝒴`,
one proof `hdom`, one label type `{Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}` with labels
`(thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)` and block split `S.blockSplit 1 hp`, and for every
`e ∈ V₀` a label activity `Aseg e he p` for the points `p` of `stepSegments`, which is `segAct`
of the activities of `labelAct_of_directTerms` at the points `physInclScaled (1/β) (e.1, 0)` and
`physInclScaled (1/β) e` (the same `𝒴` and terms at every point of the slice), such that

* (value clause) `Jr.W1 (e.1, s ψ̂) + Jr.W2 e.2 (e.1, t ψ̂) = ∑_y (Aseg e he (s,t)).H y (restr x)`
  for `ν_{p₁}`-almost every `x`, at every `(s,t)` of the two segments;
* (slice clause) at `e = (rawOf S.D', g)`, `∑ |g| < 1`, the left side is `S.WoneC s x + S.WtwoC g t x`,
  so `Aseg` is the `hW` of a `StepActivityBoundC` with the same labels as
  `sourceActivityC_scale_fromTower`.

All the activities have the one amplitude `4 ε_U`, `ε_U = β · prop33EpsEtaScaled … (1/β)`, which does
not depend on `e`, the rate `2 κ_dec - 1`, `κ₀ = T.κ0` and entropy constant `2 (K₀(T.κ0) + 1)`.
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
/-- **The source exponent as a label-activity sum on the constant-`h₀` fibre at radius `ρ`.**
The statement of `sourceExponentFamily_fromTower` with the sources `g` of `ℓ¹`-size `< ρ`
(`l1BallRho`), the fibre `physFibreRho` of the chart at radius `ρ`, the condition `max 1 ρ ≤ β` and
the amplitude `ε_U = β · prop33EpsEtaScaled … (ρ/β)`; the landed theorem is its case `ρ = 1`. -/
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
  classical
  subst hS
  set S := T.step k hk N₁ ν β p₁ with hSdef
  have ht0 := T.t_pos
  have hr0 := D.r_pos
  have hβ1 : 1 ≤ β := le_trans (le_max_left _ _) hβρ
  have hβ0 : 0 < β := by linarith
  obtain ⟨Jr, hJ1, hJ2⟩ := wone_chartIdentity_fromTower_rho T k hk N₁ ν hνpos hν β p₁ hp0 D S rfl
  obtain ⟨val, 𝒴, Tt, hval, -, -, hI, hmem0, hmemg⟩ := sourceDirectTerms_scale_fromTower_rho T k hk N₁
    h3N hN ν hνpos hν β ρ hρ hβρ p₁ ρ hρ le_rfl D S rfl hp
  obtain ⟨I₀, h𝒴₀, -⟩ := hI _ hmem0
  have hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y := fun Y hY => I₀.dom Y (h𝒴₀ ▸ hY)
  -- the amplitude
  have hQ := cK2'_pos' (B := famConst 3 3 T.BG₂ T.κ) T.fam_nonneg
  have hc1 := one_le_c1 3 3
  set εU : ℝ := β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / β) with hεU
  have hεU0 : 0 ≤ εU := by
    rw [hεU, sourceEta_scaled_identity 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) ρ β hβ0.ne']
    refine add_nonneg (mul_nonneg hβ0.le (div_nonneg ?_ (by positivity))) ?_
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
        (pow_nonneg (by positivity) _)) (norm_nonneg _)
    · exact div_nonneg (mul_nonneg hρ.le (mul_nonneg hQ.le ht0.le)) hr0.le
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  have hK0 : K0 3 3 T.κ0 ≤ K0 3 3 T.κ0 + 1 := by linarith
  have hRσ1 : (1 : ℝ) < 2 := by norm_num
  have hcfun : ∀ s : ℝ, ‖((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ)‖ ≤ 1 :=
    norm_ite_sq_le
  have hβS : 1 ≤ S.β := hβ1
  have hβS0 : 0 < S.β := hβ0
  have hex : ∀ e : physParam 2 S, e ∈ physFibreRho S S.a₁ S.ν T.t ρ →
      ∃ Ae : ℝ × ℝ → LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom))
          (S.blockSplit 1 hp).Ωb (4 * εU) (2 * T.κdec - 1) T.κ0 (2 * (K0 3 3 T.κ0 + 1)),
        ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
          Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
              ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.1 : ℂ) • S.hatC x) +
            Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
              ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.2 : ℂ) • S.hatC x) =
          ∑ y, (Ae p).H y ((S.blockSplit 1 hp).restr x) := by
    intro e he
    have he1 : e ∈ physVqRho S S.a₁ S.ν T.t ρ ρ := ⟨he.1, he.1.2⟩
    have hmemE := physInclScaled_image_subset_rho S S.a₁ S.ν T.t hβρ le_rfl ⟨e, he1, rfl⟩
    have hmem0E : physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) (e.1, 0) ∈
        physSΛEta S S.a₁ S.ν T.t (ρ / S.β) := by
      refine ⟨he.1.1, ?_⟩
      show (fun y i => ((1 / S.β : ℝ) : ℂ) * (0 : ℂ)) ∈ _
      simp only [mul_zero]
      refine ⟨by simp [l1Ball], ?_⟩
      simp only [norm_zero, Finset.sum_const_zero]
      exact (div_pos hρ hβS0).le
    obtain ⟨Ie, h𝒴e, -⟩ := hI _ hmemE
    obtain ⟨I0, h𝒴0, -⟩ := hI _ hmem0E
    have hεI : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
        (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (ρ / S.β) := hεU0
    obtain ⟨A0, hid0⟩ := labelAct_of_directTerms_shared S 1 I0 hN3 hp0
      (by norm_num : (0 : ℝ) ≤ 2) hεI T.κ0_ent hK0 hdom h𝒴0 (ε' := 2 * εU) rfl
    obtain ⟨Ag, hidg⟩ := labelAct_of_directTerms_shared S 1 Ie hN3 hp0
      (by norm_num : (0 : ℝ) ≤ 2) hεI T.κ0_ent hK0 hdom h𝒴e (ε' := 2 * εU) rfl
    have hε2 : 0 ≤ 2 * εU := by linarith
    have hE : 2 * εU + 2 * εU ≤ 2 * (2 * εU) := by linarith
    let c : ℝ → ℂ := fun s => ((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ)
    -- the value of the two segment sum in terms of `val`
    have hid_val : ∀ x : S.E, ‖x‖ < 2 * p₁ → ∀ s τ : ℝ, s ∈ Icc (0 : ℝ) 1 → τ ∈ Icc (0 : ℝ) 1 →
        Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
            ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) +
          Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
            ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (τ : ℂ) • S.hatC x) =
        (s : ℂ) ^ 2 * val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (s : ℂ)
            (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) +
          (val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (τ : ℂ)
              (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) e) -
            val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (τ : ℂ)
              (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) (e.1, 0))) := by
      intro x hxn s τ hs hτ
      have := @hJ2 0 0 0 Empty Empty _ _ (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
        (fun e => e.elim) (fun e => e.elim) (fun _ => ∅) (fun _ => ∅) (fun _ => 0)
        (fun e => e.elim) (fun e => e.elim) (fun _ => ∅) (fun _ => ∅) (fun _ => 0)
        (fun _ => 0) (fun _ => 0) ∅ ∅ (fun τ h => absurd h (by simp))
        (fun τ h => absurd h (by simp)) (fun e => e.elim) (fun e => e.elim)
        (fun τ h => absurd h (by simp)) (fun τ h => absurd h (by simp)) 0 rfl rfl rfl
        ρ e he.1 he.2 x hxn s τ hs hτ
      simp only [physVal_zeroClass_eq] at this
      simp only [hval]
      exact this
    refine ⟨fun p => (segAct A0 Ag hε2 hE c hcfun p).mono
      (by rw [max_self]; linarith) (by rw [max_self]; linarith) le_rfl le_rfl
      (by linarith), ?_⟩
    intro p hp'
    obtain ⟨hs1, ht1⟩ := mem_Icc_of_mem_stepSegments hp'
    filter_upwards [S.ae_hatOf_restr 1 hp0 hp le_rfl, S.ae_ball hp] with x hx hχ
    have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp x).1 hχ
    have hxn2 : ‖x‖ < 2 * p₁ := by
      have : S.p₁ = p₁ := rfl
      linarith
    have key0 : ∀ u : ℝ, u ∈ Icc (0 : ℝ) 1 →
        ∑ y, (A0 (u : ℂ)).H y ((S.blockSplit 1 hp).restr x) =
          val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (u : ℂ)
            (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) := by
      intro u hu
      rw [hid0 (u : ℂ) (norm_ofReal_lt_of_mem hu hRσ1)]
      simp only [hx]
    have keyg : ∀ u : ℝ, u ∈ Icc (0 : ℝ) 1 →
        ∑ y, (Ag (u : ℂ)).H y ((S.blockSplit 1 hp).restr x) =
          val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (u : ℂ)
            (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) e) := by
      intro u hu
      rw [hidg (u : ℂ) (norm_ofReal_lt_of_mem hu hRσ1)]
      simp only [hx]
      rfl
    obtain ⟨s, t⟩ := p
    have hmono : ∀ y, ((segAct A0 Ag hε2 hE c hcfun (s, t)).mono
        (by rw [max_self]; linarith) (by rw [max_self]; linarith) le_rfl le_rfl
        (by linarith : (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) ≤
          2 * (K0 3 3 T.κ0 + 1)) : LabelAct _ _ (4 * εU) _ _ _).H y =
        (segAct A0 Ag hε2 hE c hcfun (s, t)).H y := fun y => rfl
    simp only [hmono]
    by_cases h0 : t = 0
    · rw [segAct_total_zero _ _ _ _ _ _ (p := (s, t)) h0, hid_val x hxn2 s t hs1 ht1, key0 s hs1]
      subst h0
      have hz : val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) ((0 : ℝ) : ℂ)
          (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) e) =
          val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) ((0 : ℝ) : ℂ)
          (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) := by
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
  refine ⟨Jr, 𝒴, hdom, εU, hεU, hεU0, Aseg, fun e he p hp' => hAseg e he p hp', ?_⟩
  intro g hg
  have hmemS : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) ∈
      physFibreRho S S.a₁ S.ν T.t ρ := ⟨⟨⟨S.D', D.xi, rfl⟩, hg⟩, fun y i => S.hh₀ y i⟩
  refine ⟨hmemS, fun p hp' => ?_⟩
  obtain ⟨hs1, ht1⟩ := mem_Icc_of_mem_stepSegments hp'
  have hle : S.p₁ ≤ 2 * p₁ := by
    show p₁ ≤ 2 * p₁
    linarith
  filter_upwards [hAseg _ hmemS p hp',
    Jr.ae_W1_path (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) hp hle S.D' S.hh₀ D.xi hs1,
    Jr.ae_W2_path (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) hp hle S.D' S.hh₀ D.xi g ht1]
    with x h1 h2 h3
  have e1 : S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) p.1 x = _ := h2.symm
  have e2 : S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g p.2 x = _ := h3.symm
  rw [e1, e2]
  exact h1


open Classical in
/-- **The source exponent as a label-activity sum on the constant-`h₀` fibre, at the shared tower.**
For the step `S = T.step k hk N₁ ν β p₁` of the tower `T` with a per-scale package `D` (and
`1 ≤ β`), there are a joint representation `Jr`, a domain family `𝒴` with its proof `hdom`, and for
every `e` of the fibre `physFibreRho S S.a₁ S.ν T.t ρ` an activity `Aseg e he p` for `p` in `stepSegments`
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
