/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.PhysAmpFacts
public import Balaban.Inhabited.SourceExponentFamily
public import Balaban.Fluctuation.ObsRayActivity
public import Balaban.Inhabited.ObsUnconditional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The exponent family and the ray activities of a source witness, general tower

For `val, 𝒴, Tt` given with the value formula and an instance at every point of the slice
`η = ρ/β`, the exponent family on the constant-`h₀` fibre (joint representation `Jr`, activities
of amplitude `4 ε_U`) and the observable ray activities (amplitude `ε_U`).  These are the two
steps of `commonWitness_joint_fromTowerG_rho` that depend only on the witness.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Set

open Classical in
/-- **The exponent family for a given source witness, at source radius `ρ`, general tower.**
Given `val, 𝒴, Tt` with the value formula and an instance at every point of the slice `η = ρ/β`,
and `ε_U` the physical amplitude at that slice, there are a joint representation `Jr` and, at every
point of the constant-`h₀` fibre `physFibreRho … ρ`, an activity on the labels
`thickLabels 𝒴 ⊕ thickLabels 𝒴` of amplitude `4 ε_U` summing to `W₁(s) + W₂(t)` along the
segments.  The fixed `sourceWitness_exponent_of_witness_rho` is its corollary. -/
theorem sourceWitness_exponent_of_witnessG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ T.m₀ ∣ N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β ρ : ℝ) (hρ : 0 < ρ)
    (hβρ : max 1 ρ ≤ β) (p₁ : ℝ) (hp0 : 0 < p₁) (b : ℝ)
    (hb : b = β * (L : ℝ) ^ (k * (d - 2)))
    (D : StepScaleDataG T k hk N₁ ν β p₁) {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁)
    (S : StepSetting d L N₁ T.m₁ k N ϱ) (hS : HEq S (T.step k hk N₁ ν β p₁))
    (hp : 0 < S.p₁) :
    ∀ (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ℂ → (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
    (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
    (Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
        (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
    (hdom : ∀ Y ∈ 𝒴, IsDj T.m₀ (k + 1) Y)
    (_hval : ∀ x w σ Θ, val x w σ Θ =
        (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
        (S.β : ℂ) * (∑ s : CTorus d L N₁ T.m₁ (k + 1) × Fin N, Θ.2 s.1 s.2 *
          dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi S.G' S.a₁ S.ν T.t
              (fun D ψ' => svec (stepG d L N₁ T.m₁ k ϱ)
                (flFieldOne S.G' (stepG d L N₁ T.m₁ k ϱ) T.BG₂ T.κ S.a₁ S.ν D ψ')
                  s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))
    (_hI : ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
        ∃ I' : DirectTerms S T.m₀ hp (fun ψ => (ψ, ψ)) p₁ 2
            (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
              (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1) Θ
            (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
            (physXW S (lvCpsiG d L N T.κ T.t b) 2 2 (lvRG d L N T.κ T.t b p₁)) val
            (physAgΘ S) (AgFDirPair S),
          I'.𝒴 = 𝒴 ∧ I'.T = Tt)
    (εU : ℝ) (_hεU : εU = β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / β)) (_hεpos : 0 < εU),
    ∃ Jr : S.JointRep T.t (2 * p₁),
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
        (∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < ρ →
          ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) ∈
              physFibreRho S S.a₁ S.ν T.t ρ,
            ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass d L N₁ T.m₁ k N ϱ) p.1 x +
                S.WtwoC (zeroClass d L N₁ T.m₁ k N ϱ) g p.2 x =
              ∑ y, (Aseg (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) he p).H y
                ((S.blockSplit T.m₀ hp).restr x)) := by
  classical
  subst hϱ
  have hS' : S = T.step k hk N₁ ν β p₁ := eq_of_heq hS
  subst hb
  have hβ1 : 1 ≤ β := (le_max_left _ _).trans hβρ
  have hβ0 : 0 < β := by linarith
  subst hS'
  set S := T.step k hk N₁ ν β p₁ with hSdef
  intro val 𝒴 Tt hdom hval hI εU hεU hεpos
  subst hεU
  set εU : ℝ := β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (ρ / β) with hεU
  obtain ⟨Jr, hJ1, hJ2⟩ := wone_chartIdentity_fromTowerG_rho T k hk N₁ ν hνpos hν β p₁ hp0 D rfl S HEq.rfl
  have hεU0 : 0 ≤ εU := hεpos.le
  have hK0 : K0 d L T.κ0 ≤ K0 d L T.κ0 + 1 := by linarith
  have hRσ1 : (1 : ℝ) < 2 := by norm_num
  have hcfun : ∀ s : ℝ, ‖((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ)‖ ≤ 1 :=
    norm_ite_sq_le
  have hβS : 1 ≤ S.β := hβ1
  have hβS0 : 0 < S.β := hβ0
  have hex : ∀ e : physParam N S, e ∈ physFibreRho S S.a₁ S.ν T.t ρ →
      ∃ Ae : ℝ × ℝ → LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom))
          (S.blockSplit T.m₀ hp).Ωb (4 * εU) (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1)),
        ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
          Jr.W1 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
              ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.1 : ℂ) • S.hatC x) +
            Jr.W2 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) e.2
              ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.2 : ℂ) • S.hatC x) =
          ∑ y, (Ae p).H y ((S.blockSplit T.m₀ hp).restr x) := by
    intro e he
    have he1 : e ∈ physVqRho S S.a₁ S.ν T.t ρ ρ := ⟨he.1, he.1.2⟩
    have hmemE := physInclScaled_image_subset_rho S S.a₁ S.ν T.t hβρ le_rfl
      ⟨e, he1, rfl⟩
    have hmem0E : physInclScaled N S ((1 / S.β : ℝ) : ℂ) (e.1, 0) ∈
        physSΛEta S S.a₁ S.ν T.t (ρ / S.β) := by
      refine ⟨he.1.1, ?_⟩
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
  refine ⟨Jr, Aseg, fun e he p hp' => hAseg e he p hp', ?_⟩
  intro g hg
  have hmemS : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) ∈
      physFibreRho S S.a₁ S.ν T.t ρ := ⟨⟨⟨S.D', D.xi, rfl⟩, hg⟩, fun y i => S.hh₀ y i⟩
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

open Classical in
/-- **The observable ray activities for a given source witness, at source radius `ρ`, general
tower.**  With the slice `η = ρ/β` (`ε_U` is the amplitude there) containing `(rawOf S.D', 0)` and
`(rawOf S.D', g/β)` for `∑ |g| < ρ`: the ray activities `A₀`, `A_g` on the thick labels of `𝒴`
with terms `Tt` and amplitude `ε_U`, and the identity with `W₁ + W₂` for every `g` with
`∑ |g| < ρ`.  The fixed `sourceWitness_ray_of_witness_rho` is its corollary. -/
theorem sourceWitness_ray_of_witnessG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ T.m₀ ∣ N₁)
    (ν : ℝ) (β ρ : ℝ) (hβρ : max 1 ρ ≤ β) (p₁ : ℝ) (b : ℝ)
    (hb : b = β * (L : ℝ) ^ (k * (d - 2)))
    (D : StepScaleDataG T k hk N₁ ν β p₁) {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁)
    (S : StepSetting d L N₁ T.m₁ k N ϱ) (hS : HEq S (T.step k hk N₁ ν β p₁))
    (hp : 0 < S.p₁) :
    ∀ (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ℂ → (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
    (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
    (Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
        (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
    (hdom : ∀ Y ∈ 𝒴, IsDj T.m₀ (k + 1) Y)
    (_hval : ∀ x w σ Θ, val x w σ Θ =
        (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
        (S.β : ℂ) * (∑ s : CTorus d L N₁ T.m₁ (k + 1) × Fin N, Θ.2 s.1 s.2 *
          dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi S.G' S.a₁ S.ν T.t
              (fun D ψ' => svec (stepG d L N₁ T.m₁ k ϱ)
                (flFieldOne S.G' (stepG d L N₁ T.m₁ k ϱ) T.BG₂ T.κ S.a₁ S.ν D ψ')
                  s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))
    (_hcont : DiagCont (fun ψ : S.U × Fin N → ℂ => (ψ, ψ))
        (physXW S (lvCpsiG d L N T.κ T.t b) 2 2 (lvRG d L N T.κ T.t b p₁))
        (physSΛEta S S.a₁ S.ν T.t (ρ / S.β)) 2 𝒴 Tt)
    (_hI : ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β),
        ∃ I' : DirectTerms S T.m₀ hp (fun ψ => (ψ, ψ)) p₁ 2
            (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
              (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / S.β)) (2 * T.κdec - 1) Θ
            (physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
            (physXW S (lvCpsiG d L N T.κ T.t b) 2 2 (lvRG d L N T.κ T.t b p₁)) val
            (physAgΘ S) (AgFDirPair S),
          I'.𝒴 = 𝒴 ∧ I'.T = Tt)
    (_hmem0 : (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) ∈
      physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
    (_hmemg : ∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < ρ →
      (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (ρ / S.β))
    (εU : ℝ) (_hεU : εU = β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t b p₁) 0 0 (ρ / β)) (_hεpos : 0 < εU),
    0 < εU ∧ ∃ A₀ : ℂ → LabelAct (thickLabels 𝒴 hdom) (S.blockSplit T.m₀ hp).Ωb
          εU (2 * T.κdec - 1) T.κ0 (K0 d L T.κ0 + 1),
        (∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ y Φ, (A₀ z).H y Φ =
          Tt y.1 (z • S.hatOf T.m₀ p₁ hp Φ, z • S.hatOf T.m₀ p₁ hp Φ)
            (z • S.hatOf T.m₀ p₁ hp Φ, z • S.hatOf T.m₀ p₁ hp Φ) 1
            (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ))) ∧
        (∀ z : ℂ, 3 / 2 ≤ ‖z‖ → ∀ y Φ, (A₀ z).H y Φ = 0) ∧
        ∀ g : Fld d L N₁ T.m₁ (k + 1) N, g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N ρ →
        ∃ Ag : ℂ → LabelAct (thickLabels 𝒴 hdom) (S.blockSplit T.m₀ hp).Ωb
            εU (2 * T.κdec - 1) T.κ0 (K0 d L T.κ0 + 1),
          (∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ y Φ, (Ag z).H y Φ =
            Tt y.1 (z • S.hatOf T.m₀ p₁ hp Φ, z • S.hatOf T.m₀ p₁ hp Φ)
              (z • S.hatOf T.m₀ p₁ hp Φ, z • S.hatOf T.m₀ p₁ hp Φ) 1
              (rawOf S.D', fun y i => g y i / (S.β : ℂ))) ∧
          (∀ z : ℂ, 3 / 2 ≤ ‖z‖ → ∀ y Φ, (Ag z).H y Φ = 0) ∧
          ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
            ∑ y, (((A₀ 1).sub (A₀ (t : ℂ))).sum (Ag (t : ℂ))).H y
                (((S.blockSplit T.m₀ hp).restr x)) =
              S.WoneC (zeroClass d L N₁ T.m₁ k N ϱ) 1 x +
              S.WtwoC (zeroClass d L N₁ T.m₁ k N ϱ) g t x := by
  classical
  subst hϱ
  have hS' : S = T.step k hk N₁ ν β p₁ := eq_of_heq hS
  subst hb
  have hβ1 : 1 ≤ β := (le_max_left _ _).trans hβρ
  have hr0 := D.r_pos
  have hcψ0 := D.cψ_pos
  obtain ⟨R0⟩ := D.ray
  have hC := D.core
  have hD := D.xi
  subst hS'
  set S := T.step k hk N₁ ν β p₁ with hSdef
  intro val 𝒴 Tt hdom hval hcont hI hmem0 hmemg εU hεU hεpos
  subst hεU
  set εU : ℝ := β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ 1 T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (ρ / β) with hεU
  obtain ⟨I₀, h𝒴₀, hT₀⟩ := hI _ hmem0
  refine ⟨hεpos, ?_⟩
  have hKc : K0 d L T.κ0 ≤ K0 d L T.κ0 + 1 := by linarith
  have hxwz : ∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ ψ ∈ hatDisk (T.step k hk N₁ ν β p₁).U N p₁,
      ((z • ψ, z • ψ), (z • ψ, z • ψ)) ∈
        physXW (T.step k hk N₁ ν β p₁) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
          (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) :=
    fun z hz ψ hψ => scaled_pair_mem_physXW (T.step k hk N₁ ν β p₁) hψ hz (by norm_num)
      (by norm_num) hr0.le (D.ray_margin_scaled hp)
  have hAgF : ∀ (z : ℂ) (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
      (ψ ψ' : (T.step k hk N₁ ν β p₁).U × Fin N → ℂ),
      AgFDirPair (T.step k hk N₁ ν β p₁) Y (ψ, ψ) (ψ', ψ') →
      AgFDirPair (T.step k hk N₁ ν β p₁) Y (z • ψ, z • ψ) (z • ψ', z • ψ') :=
    fun z Y ψ ψ' h => agFDirPair_smul _ z Y ψ ψ' h
  have hcont₀ := hcont
  rw [← h𝒴₀, ← hT₀] at hcont₀
  have hRσ1 : (1 : ℝ) < 2 := by norm_num
  have hpc : p₁ < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) :=
    p₁_lt_of_margin hp le_rfl hRσ1 hRσ1 hr0 D.ray_margin
  refine ⟨obsRayAct (T.step k hk N₁ ν β p₁) T.m₀ I₀ hdom h𝒴₀ hxwz hAgF hcont₀ hLN hp hRσ1 hεpos.le
      T.κ0_ent hKc, ?_, ?_, ?_⟩
  · intro z hz y Φ
    rw [obsRayAct_H_of_lt _ _ _ hdom h𝒴₀ hxwz hAgF hcont₀ hLN hp hRσ1 hεpos.le T.κ0_ent hKc hz,
      hT₀]
  · intro z hz y Φ
    exact obsRayAct_H_of_not_lt _ _ _ hdom h𝒴₀ hxwz hAgF hcont₀ hLN hp hRσ1 hεpos.le T.κ0_ent
      hKc hz y Φ
  · intro g hg
    obtain ⟨Ig, h𝒴g, hTg⟩ := hI _ (hmemg g hg)
    have hcontg := hcont
    rw [← h𝒴g, ← hTg] at hcontg
    refine ⟨obsRayAct (T.step k hk N₁ ν β p₁) T.m₀ Ig hdom h𝒴g hxwz hAgF hcontg hLN hp hRσ1
      hεpos.le T.κ0_ent hKc, ?_, ?_, ?_⟩
    · intro z hz y Φ
      rw [obsRayAct_H_of_lt _ _ _ hdom h𝒴g hxwz hAgF hcontg hLN hp hRσ1 hεpos.le T.κ0_ent hKc hz,
        hTg]
    · intro z hz y Φ
      exact obsRayAct_H_of_not_lt _ _ _ hdom h𝒴g hxwz hAgF hcontg hLN hp hRσ1 hεpos.le T.κ0_ent
        hKc hz y Φ
    · intro t ht
      exact ae_sum_A_phys_eq_WoneC_add_WtwoC (T.step k hk N₁ ν β p₁) hC R0 D.p_lt hD T.c7_cap
        (R := 2) le_rfl T.bg1_cap T.t_cap T.bg0_cap T.cK2_cap T.cK2'_cap T.large_block T.dom_margin
        T.coer_margin T.δc_small hp hcψ0.le hpc D.fl_radius g le_rfl I₀ Ig hval hdom h𝒴₀ h𝒴g
        hxwz hAgF hcont₀ hcontg hLN hp hRσ1 hεpos.le T.κ0_ent hKc ht

end Balaban.Inhabited
