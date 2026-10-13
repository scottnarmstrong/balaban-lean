/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.SourceWitnessJoint
public import Balaban.Fluctuation.StepComplexSource
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The step identity of the zero class at every chart datum of the fibre `h ≡ h₀`

At a scale of the shared tower (`d = L = 3`, `N = 2`), write `S` for the step, `S[D′]` for the step
with the block datum `D′` (`S.withDatum D′ hDh`, `D′` a datum of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)`
with constant field `h₀`) and `C` for the class with zero old terms.

* `stepActivityBoundC_fibre_fromTower`: the witness of `sourceWitness_fromTower` (one domain family
  `𝒴`, one amplitude `ε_U`, one joint representation `Jr` and one family of segment activities
  `Aseg` on the fibre) gives, for every datum `D′` of the fibre and every source `g` with
  `∑ |g| < 1`, the activity record `StepActivityBoundC S[D′] C g`, with block scale `1`, the block
  split of the step, the labels `thickLabels 𝒴 ⊕ thickLabels 𝒴`, the activities
  `Aseg (rawOf D′, g)`, and the constants `ε_H = 4 ε_U`, `κ_H = 2 κ_dec - 1`, `κ₀`, `κ'`,
  `K_c = 2 (K₀ + 1)` of the record at the datum of the step.
* `stepNonvanishingC_fibre_fromTower`: hence `Z_{s,0} ≠ 0`, `Z_{1,t} ≠ 0` at every such `(D′, g)`.
* `stepIdentity_zeroClass_withDatum_of_nonvanishing`: at a scale of the tower, for a datum of the
  fibre at which the partition functions do not vanish, Proposition 2.6 with the local sums
  `ℰ₀ = ∑_z ℰ₀(z)` and `ℱ₀(g) = β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i` substituted.
* `stepIdentity_zeroClass_fibre_local_fromTower`: the identity at every datum of the fibre and
  every source of the unit ball,
  `TstepC = exp [-β A^η_{k+1} - E''' |T₁| + ℱ_k(ψ^{(k)}, g) + ∑_z ℰ₀(z)
    + β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i]`.
* `stepIdentity_zeroClass_fibre_of_values_fromTower`: the same identity with given values `E z` of
  `ℰ₀(z)` and `M y i` of `β_U^{-1/2} ℳ₀(y; g)_i` in the exponent, the form in which coefficient
  expansions are substituted.

The term `ℰ_k(ψ^{(k)})` of Proposition 2.6 vanishes for the zero class (`EcompAtC_zero`); the
normalization term `E''' |T₁|` does not (`E'''` contains the constants of the kernel and of the
fluctuation measure), and `ℱ_k(ψ^{(k)}, g)` is the pairing of the source with the complex small
solution (`FcompAtC_zero_eq`).

Each theorem is stated first for a general tower `T : StepTowerG d L N κmin` (names ending in `G`:
`stepActivityBoundC_fibre_fromTowerG`, `stepNonvanishingC_fibre_fromTowerG`,
`stepIdentity_zeroClass_withDatum_of_nonvanishingG`, `stepIdentity_zeroClass_fibre_local_fromTowerG`,
`stepIdentity_zeroClass_fibre_of_values_fromTowerG`); the statements for the fixed tower
(`d = L = 3`, `N = 2`) are corollaries.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Set

/-- For `b > 0`, if `m₀(y,i) = b^{1/2} m(y,i)` then
`b^{-1/2} ∑_{y,i} g(y,i) m₀(y,i) = ∑_{y,i} g(y,i) m(y,i)`. -/
theorem rpow_neg_half_mul_sum_pair {ι κ : Type*} [Fintype ι] [Fintype κ] {b : ℝ} (hb : 0 < b)
    (g m₀ m : ι → κ → ℂ) (h : ∀ y i, m₀ y i = ((b ^ (1 / 2 : ℝ) : ℝ) : ℂ) * m y i) :
    ((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ∑ y, ∑ i, g y i * m₀ y i = ∑ y, ∑ i, g y i * m y i := by
  have hcc : ((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((b ^ (1 / 2 : ℝ) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hb]
    norm_num
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h y i, ← mul_assoc, mul_comm _ (g y i), mul_assoc, ← mul_assoc _ _ (m y i), hcc, one_mul]

open Classical in
/-- **The activity record of the complex step at every chart datum of the fibre.**  Beyond the
threshold `β₀` of `sourceWitness_fromTowerG`, at every scale datum there are a domain family `𝒴`, an
amplitude `ε_U > 0` with `4 ε_U ≤ C_E (log b)^{3p}/√b + C_F (log b)^p/√b` (`b = β 3^k`), a joint
representation `Jr` and segment activities `Aseg e` for every point `e` of the fibre `h ≡ h₀` of
the chart (with their identity for the joint exponents `Jr.W1 + Jr.W2`), all chosen before the
datum and the source, such that for every datum `D′` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with
constant field `h₀` and every source `g` with `∑ |g| < 1`:
* the point `(rawOf D′, g)` lies in the fibre;
* on the two segments, `W₁(s, ψ̂) + W₂(t, ψ̂; g)` of the step with the datum `D′` is
  `ν_{p₁}`-almost everywhere the sum of the block activities `Aseg (rawOf D′, g) (s, t)`;
* there is a record `B : StepActivityBoundC S[D′] C g` with block scale `1`, the block split of the
  step, the labels `thickLabels 𝒴 ⊕ thickLabels 𝒴`, the activities `Aseg (rawOf D′, g)` and the
  constants `κ₀ = T.κ0`, `κ' = T.κ'`, `κ_H = 2 κ_dec - 1`, `K_c = 2 (K₀ + 1)`, `ε_H = 4 ε_U`.

The numerical fields of `B` are those of the record at the datum of the step; the identity for the
exponents is the one of `Aseg`, transported by `JointRep.ae_W1_path`, `ae_W2_path`. -/
theorem stepActivityBoundC_fibre_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ CE CF : ℝ, 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
    p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → StepScaleDataG T k hk N₁ ν β p₁ →
    ∀ (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)), S = T.step k hk N₁ ν β p₁ →
    ∀ (hp : 0 < S.p₁),
    ∃ (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1)))) (hdom : ∀ Y ∈ 𝒴, IsDj T.m₀ (k + 1) Y)
      (εU : ℝ), 0 < εU ∧
      4 * εU ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
        CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
      ∃ Jr : S.JointRep T.t (2 * p₁),
      ∃ Aseg : ∀ e : physParam N S, e ∈ physFibre S S.a₁ S.ν T.t → ℝ × ℝ →
          LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit T.m₀ hp).Ωb
            (4 * εU) (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1)),
        (∀ (e : physParam N S) (he : e ∈ physFibre S S.a₁ S.ν T.t), ∀ p ∈ stepSegments,
          ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
                ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.1 : ℂ) • S.hatC x) +
              Jr.W2 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) e.2
                ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (p.2 : ℂ) • S.hatC x) =
            ∑ y, (Aseg e he p).H y ((S.blockSplit T.m₀ hp).restr x)) ∧
        ∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
          ∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < 1 →
          ∃ he : ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) ∈
              physFibre S S.a₁ S.ν T.t,
            (∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
              (S.withDatum D' hDh).WoneC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) p.1 x +
                (S.withDatum D' hDh).WtwoC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g p.2 x =
              ∑ y, (Aseg (⟨rawOf D', rawOf_mem_rawSub _⟩, g) he p).H y
                ((S.blockSplit T.m₀ hp).restr x)) ∧
            ∃ B : StepActivityBoundC (S.withDatum D' hDh)
                (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g,
              B.m₀ = T.m₀ ∧ B.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧
              HEq B.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧
              HEq B.BS ((S.withDatum D' hDh).blockSplit T.m₀ hp) ∧
              B.κ0 = T.κ0 ∧ B.κ' = T.κ' ∧ B.κH = 2 * T.κdec - 1 ∧
              B.Kc = 2 * (K0 d L T.κ0 + 1) ∧ B.εH = 4 * εU ∧
              HEq B.A (Aseg (⟨rawOf D', rawOf_mem_rawSub _⟩, g) he) := by
  classical
  obtain ⟨CE, CF, hCE, hCF, H0⟩ := sourceWitness_fromTowerG_rho T hA p
  obtain ⟨β₀, h2, -, H⟩ := H0 1 one_pos
  refine ⟨β₀, CE, CF, h2, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS hp
  obtain ⟨val, 𝒴, Tt, hdom, -, εU, -, hεpos, hbd, hrec, ⟨Jr, Aseg, hAseg, -⟩, -⟩ :=
    H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS hp
  rw [one_mul] at hbd
  subst hS
  refine ⟨𝒴, hdom, εU, hεpos, hbd, Jr, Aseg, hAseg, ?_⟩
  intro D' hDh hX g hg
  have hN3 : L ^ T.m₀ ∣ N₁ := h3N
  have he : ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N (T.step k hk N₁ ν β p₁).G'), g) ∈
      physFibre (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν
        T.t := ⟨⟨⟨D', hX, rfl⟩, hg⟩, fun y i => hDh y i⟩
  have hle : (T.step k hk N₁ ν β p₁).p₁ ≤ 2 * p₁ := by
    show p₁ ≤ 2 * p₁
    linarith
  -- the identity of `Aseg` for the joint exponents, read at the step with the datum `D'`
  have hWid : ∀ p ∈ stepSegments, ∀ᵐ x ∂(T.step k hk N₁ ν β p₁).nuFl,
      ((T.step k hk N₁ ν β p₁).withDatum D' hDh).WoneC
          (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) p.1 x +
        ((T.step k hk N₁ ν β p₁).withDatum D' hDh).WtwoC
          (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g p.2 x =
      ∑ y, (Aseg (⟨rawOf D', rawOf_mem_rawSub _⟩, g) he p).H y
        (((T.step k hk N₁ ν β p₁).blockSplit T.m₀ hp).restr x) := by
    intro p hp'
    obtain ⟨hs1, ht1⟩ := mem_Icc_of_mem_stepSegments hp'
    filter_upwards [hAseg _ he p hp',
      Jr.ae_W1_path (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) hp hle D' hDh hX hs1,
      Jr.ae_W2_path (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) hp hle D' hDh hX g ht1]
      with x h1 h2 h3
    rw [← h2, ← h3]
    exact h1
  -- the numerical fields are those of the record at the datum of the step
  obtain ⟨BR, BC, -, -, -, -, -, -, -, -, -, e1, -, e2, hκHR, hκHC, hKcR, hKcC, hεRC, hεR⟩ :=
    hrec g hg
  have e3 : BC.κH = 2 * T.κdec - 1 := hκHC.trans hκHR
  have e4 : BC.Kc = 2 * (K0 d L T.κ0 + 1) := hKcC.trans hKcR
  have e5 : BC.εH = 4 * εU := hεRC.symm.trans hεR
  have n1 := BC.hκ0
  have n2 := BC.hKc
  have n3 := BC.hεpos
  have n4 := BC.hκ'
  have n5 := BC.hκ
  have n6 := BC.hε
  rw [e1] at n1
  rw [e1, e4] at n2
  rw [e5] at n3
  rw [e2] at n4
  rw [e2, e1, e3] at n5
  rw [e5, e4, e3, e1, e2] at n6
  exact ⟨he, hWid, { m₀ := T.m₀, hN := hN3, BS := (T.step k hk N₁ ν β p₁).blockSplit T.m₀ hp
                     Lb := {Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}
                     Lab := (thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)
                     εH := 4 * εU, κH := 2 * T.κdec - 1, κ0 := T.κ0, κ' := T.κ'
                     Kc := 2 * (K0 d L T.κ0 + 1)
                     A := Aseg (⟨rawOf D', rawOf_mem_rawSub _⟩, g) he
                     hκ0 := n1, hKc := n2, hεpos := n3, hκ' := n4, hκ := n5, hε := n6
                     hW := hWid },
    rfl, rfl, HEq.rfl, HEq.rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl⟩

/-- **Nonvanishing of the partition functions of the complex step at every chart datum of the
fibre.**  Beyond the threshold of `stepActivityBoundC_fibre_fromTowerG`, at every scale datum, for
every datum `D′` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and every source `g`
with `∑ |g| < 1`: `Z_{s,0} ≠ 0` and `Z_{1,t} ≠ 0` for `s, t ∈ [0,1]`, for the step with the datum
`D′` and the class with zero old terms. -/
theorem stepNonvanishingC_fibre_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 2 ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
    p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → StepScaleDataG T k hk N₁ ν β p₁ →
    ∀ (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)), S = T.step k hk N₁ ν β p₁ →
    ∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
      XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
      ∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < 1 →
      (S.withDatum D' hDh).StepNonvanishingC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g := by
  obtain ⟨β₀, CE, CF, h2, -, -, H⟩ := stepActivityBoundC_fibre_fromTowerG T hA p
  refine ⟨β₀, h2, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS D' hDh hX g hg
  have hp : 0 < S.p₁ := by rw [hS]; exact hp0
  obtain ⟨𝒴, hdom, εU, -, -, Jr, Aseg, -, hfib⟩ :=
    H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS hp
  obtain ⟨-, -, B, -⟩ := hfib D' hDh hX g hg
  exact stepNonvanishingC_of_activityBoundC B

/-- **Proposition 2.6 at a chart datum of the fibre, with the local sums substituted.**  At a
scale of the tower `T` with `β > 0`, `p₁ > 0`, for a datum `D′` of the chart
`Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and a source `g` at which the partition functions
of the step with the datum `D′` do not vanish on the two segments (`StepNonvanishingC`):
`TstepC = exp [-β A^η_{k+1} - E''' |T₁| + ℱ_k(ψ^{(k)}, g) + ∑_z ℰ₀(z)
  + β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i]`,
all objects being those of the step with the datum `D′` and the class with zero old terms.  The
premises of `prop26C_zeroClass`, `sum_E0locC_zeroClass` and `F0C_eq_pair_zeroClass` which do not
depend on the datum are supplied by the tower (`R = 2`, `p⁺ = lvCpsi`, `δ₁ = ε = T.t`); the term
`ℰ_k(ψ^{(k)})` is zero for this class. -/
theorem stepIdentity_zeroClass_withDatum_of_nonvanishingG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (Dsc : StepScaleDataG T k hk N₁ ν β p₁) (hβ : 0 < β) (hp₁ : 0 < p₁)
    (D' : BgData (T.step k hk N₁ ν β p₁).G' N)
    (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hX : XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
      (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D')
    (g : Fld d L N₁ T.m₁ (k + 1) N)
    (hnv : ((T.step k hk N₁ ν β p₁).withDatum D' hDh).StepNonvanishingC
      (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g) :
    ((T.step k hk N₁ ν β p₁).withDatum D' hDh).TstepC
        (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g =
      Complex.exp (-((T.step k hk N₁ ν β p₁).β : ℂ) *
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).AnewC -
        (((T.step k hk N₁ ν β p₁).withDatum D' hDh).Eppp
            (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) : ℂ) *
          (((T.step k hk N₁ ν β p₁).withDatum D' hDh).nU : ℂ) +
        FcompAtC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)).m₀
          (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)).Tm (T.step k hk N₁ ν β p₁).a
          (T.step k hk N₁ ν β p₁).ν (Nat.le_succ k)
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).psiKdC g +
        ∑ z : RootIdx d L N₁ T.m₁ (k + 1),
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).E0locC
            (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) z +
        (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
            g y i * ((T.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
              (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i) := by
  have hbU : (T.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) := hatStepKG_betaU T.hN (by have := T.hd; omega) k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hbU0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hδ : Real.sqrt (N : ℝ) * ((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ * lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))) < T.t := by
    have h := Dsc.fl_radius
    have hn : ‖(((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ =
        (T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) := by
      rw [Complex.norm_real, Real.norm_of_nonneg]
      rw [hbU]; exact Real.rpow_nonneg hbU0.le _
    rw [hn] at h
    exact h
  have hlt : ((T.step k hk N₁ ν β p₁).withDatum D' hDh).p₁ < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
    have h := Dsc.ray_margin
    have hl := Dsc.r_pos
    show p₁ < _
    nlinarith
  have hp : 0 < ((T.step k hk N₁ ν β p₁).withDatum D' hDh).p₁ := hp₁
  have hβS : 0 < ((T.step k hk N₁ ν β p₁).withDatum D' hDh).β := hβ
  have h26 := ((T.step k hk N₁ ν β p₁).withDatum D' hDh).prop26C_zeroClass (δc := T.δc) (R := 2)
    (pp := lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) Dsc.core T.large_block T.dom_margin T.coer_margin
    T.δc_small one_pos T.c7_cap (by norm_num) T.bg1_cap hβS hp hlt hδ hX g hnv
  have hE := ((T.step k hk N₁ ν β p₁).withDatum D' hDh).sum_E0locC_zeroClass (δc := T.δc) (R := 2)
    (pp := lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) Dsc.core T.large_block T.dom_margin T.coer_margin
    T.δc_small one_pos T.c7_cap (by norm_num) T.bg1_cap hβS hp hlt hδ hX g hnv
  have hF := ((T.step k hk N₁ ν β p₁).withDatum D' hDh).F0C_eq_pair_zeroClass (δc := T.δc) (R := 2)
    (pp := lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) Dsc.core T.large_block T.dom_margin T.coer_margin
    T.δc_small one_pos T.c7_cap (by norm_num) T.bg1_cap hβS hp hlt hδ hX g hnv
  have hE0 : EcompAtC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)).m₀
      (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)).Tm
      ((T.step k hk N₁ ν β p₁).withDatum D' hDh).a ((T.step k hk N₁ ν β p₁).withDatum D' hDh).ν
      (Nat.le_succ k) ((T.step k hk N₁ ν β p₁).withDatum D' hDh).psiKdC = 0 :=
    EcompAtC_zero _ _ _ _ _
  rw [h26, hE0, ← hE, hF]
  congr 1
  simp only [add_zero]
  rfl

/-- **The step identity of the zero class at every chart datum of the fibre and every source of
the unit ball, with the local energies and observables.**  Beyond the threshold of
`stepActivityBoundC_fibre_fromTowerG`, at every scale datum, for every datum `D′` of the chart
`Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and every source `g` with `∑ |g| < 1`:
`TstepC = exp [-β A^η_{k+1} - E''' |T₁| + ℱ_k(ψ^{(k)}, g) + ∑_z ℰ₀(z)
  + β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i]`
for the step with the datum `D′` and the class with zero old terms.  This is an equality of
exponentials; the normalization term `E''' |T₁|` is part of the exponent. -/
theorem stepIdentity_zeroClass_fibre_local_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 2 ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
    p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → StepScaleDataG T k hk N₁ ν β p₁ →
    ∀ (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)), S = T.step k hk N₁ ν β p₁ →
    ∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
      XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
      ∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < 1 →
      (S.withDatum D' hDh).TstepC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g =
        Complex.exp (-(S.β : ℂ) * (S.withDatum D' hDh).AnewC -
          ((S.withDatum D' hDh).Eppp (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) : ℂ) *
            ((S.withDatum D' hDh).nU : ℂ) +
          FcompAtC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)).m₀
            (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)).Tm S.a S.ν (Nat.le_succ k)
            (S.withDatum D' hDh).psiKdC g +
          ∑ z : RootIdx d L N₁ T.m₁ (k + 1),
            (S.withDatum D' hDh).E0locC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) z +
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
              g y i * (S.withDatum D' hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
                g y i) := by
  obtain ⟨β₀, h2, H⟩ := stepNonvanishingC_fibre_fromTowerG T hA p
  refine ⟨β₀, h2, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS D' hDh hX g hg
  have hnv := H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS D' hDh hX g hg
  subst hS
  exact stepIdentity_zeroClass_withDatum_of_nonvanishingG T Dsc (by linarith) hp0 D' hDh hX g hnv

/-- **The step identity of the zero class on the fibre, for given values of the local energies and
observables.**  Beyond the threshold of `stepActivityBoundC_fibre_fromTowerG`, at every scale datum,
for every datum `D′` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and every source
`g` with `∑ |g| < 1`: if `ℰ₀(z) = E z` for every root `z` and `ℳ₀(y; g)_i = β_U^{1/2} M y i` for
every site `(y, i)` (objects of the step with the datum `D′` and the class with zero old terms),
then
`TstepC = exp [-β A^η_{k+1} - E''' |T₁| + ℱ_k(ψ^{(k)}, g) + ∑_z E z + ∑_{y,i} g(y,i) M y i]`.
This is the form in which coefficient expansions of `ℰ₀(z)` and `β_U^{-1/2} ℳ₀(y; g)_i` (over any
index sets) are substituted; the factors `β_U^{-1/2}` and `β_U^{1/2}` cancel since
`β_U = β 3^k > 0`. -/
theorem stepIdentity_zeroClass_fibre_of_values_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 2 ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
    p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → StepScaleDataG T k hk N₁ ν β p₁ →
    ∀ (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)), S = T.step k hk N₁ ν β p₁ →
    ∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
      XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
      ∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < 1 →
      ∀ (E : RootIdx d L N₁ T.m₁ (k + 1) → ℂ) (M : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ),
        (∀ z, (S.withDatum D' hDh).E0locC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) z = E z) →
        (∀ y i, (S.withDatum D' hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i =
          ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * M y i) →
        (S.withDatum D' hDh).TstepC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g =
          Complex.exp (-(S.β : ℂ) * (S.withDatum D' hDh).AnewC -
            ((S.withDatum D' hDh).Eppp (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) : ℂ) *
              ((S.withDatum D' hDh).nU : ℂ) +
            FcompAtC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)).m₀
              (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)).Tm S.a S.ν (Nat.le_succ k)
              (S.withDatum D' hDh).psiKdC g +
            ∑ z : RootIdx d L N₁ T.m₁ (k + 1), E z +
            ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N, g y i * M y i) := by
  obtain ⟨β₀, h2, H⟩ := stepIdentity_zeroClass_fibre_local_fromTowerG T hA p
  refine ⟨β₀, h2, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS D' hDh hX g hg E M hE hM
  have hbU0 : 0 < S.betaU := by
    rw [hS, show (T.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) from
      hatStepKG_betaU T.hN (by have := T.hd; omega) k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ]
    have : 0 < β := by linarith
    have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rw [H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS D' hDh hX g hg,
    rpow_neg_half_mul_sum_pair hbU0 g _ M hM, Finset.sum_congr rfl fun z _ => hE z]

open Classical in
/-- **The activity record of the complex step at every chart datum of the fibre.**  Beyond the
threshold `β₀` of `sourceWitness_fromTower`, at every scale datum there are a domain family `𝒴`, an
amplitude `ε_U > 0` with `4 ε_U ≤ C_E (log b)^{3p}/√b + C_F (log b)^p/√b` (`b = β 3^k`), a joint
representation `Jr` and segment activities `Aseg e` for every point `e` of the fibre `h ≡ h₀` of
the chart (with their identity for the joint exponents `Jr.W1 + Jr.W2`), all chosen before the
datum and the source, such that for every datum `D′` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with
constant field `h₀` and every source `g` with `∑ |g| < 1`:
* the point `(rawOf D′, g)` lies in the fibre;
* on the two segments, `W₁(s, ψ̂) + W₂(t, ψ̂; g)` of the step with the datum `D′` is
  `ν_{p₁}`-almost everywhere the sum of the block activities `Aseg (rawOf D′, g) (s, t)`;
* there is a record `B : StepActivityBoundC S[D′] C g` with block scale `1`, the block split of the
  step, the labels `thickLabels 𝒴 ⊕ thickLabels 𝒴`, the activities `Aseg (rawOf D′, g)` and the
  constants `κ₀ = T.κ0`, `κ' = T.κ'`, `κ_H = 2 κ_dec - 1`, `K_c = 2 (K₀ + 1)`, `ε_H = 4 ε_U`.

The numerical fields of `B` are those of the record at the datum of the step; the identity for the
exponents is the one of `Aseg`, transported by `JointRep.ae_W1_path`, `ae_W2_path`. -/
theorem stepActivityBoundC_fibre_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ CE CF : ℝ, 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
    p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
    ∀ (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)), S = T.step k hk N₁ ν β p₁ →
    ∀ (hp : 0 < S.p₁),
    ∃ (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1)))) (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y)
      (εU : ℝ), 0 < εU ∧
      4 * εU ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
      ∃ Jr : S.JointRep T.t (2 * p₁),
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
        ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
          ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
          ∃ he : ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) ∈
              physFibre S S.a₁ S.ν T.t,
            (∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
              (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) p.1 x +
                (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g p.2 x =
              ∑ y, (Aseg (⟨rawOf D', rawOf_mem_rawSub _⟩, g) he p).H y
                ((S.blockSplit 1 hp).restr x)) ∧
            ∃ B : StepActivityBoundC (S.withDatum D' hDh)
                (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
              B.m₀ = 1 ∧ B.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧
              HEq B.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧
              HEq B.BS ((S.withDatum D' hDh).blockSplit 1 hp) ∧
              B.κ0 = T.κ0 ∧ B.κ' = T.κ' ∧ B.κH = 2 * T.κdec - 1 ∧
              B.Kc = 2 * (K0 3 3 T.κ0 + 1) ∧ B.εH = 4 * εU ∧
              HEq B.A (Aseg (⟨rawOf D', rawOf_mem_rawSub _⟩, g) he) := by
  classical
  obtain ⟨β₀, CE, CF, h2, hCE, hCF, H⟩ := stepActivityBoundC_fibre_fromTowerG T.toG hA p
  refine ⟨β₀, CE, CF, h2, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS hp
  subst hS
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have hp' : 0 < (T.toG.step k hk N₁ ν β p₁).p₁ := hp
  have G := H k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ p₁ hp0
    (by rw [e]; exact hp₁) (StepTower.scaleDataG_of_fixed T Dsc) (T.toG.step k hk N₁ ν β p₁) rfl hp'
  unfold StepTowerG.step at G
  revert G hp
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans (by rw [e])
  subst hϱ' hb'
  intro hp G
  exact G

/-- **Nonvanishing of the partition functions of the complex step at every chart datum of the
fibre.**  Beyond the threshold of `stepActivityBoundC_fibre_fromTower`, at every scale datum, for
every datum `D′` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and every source `g`
with `∑ |g| < 1`: `Z_{s,0} ≠ 0` and `Z_{1,t} ≠ 0` for `s, t ∈ [0,1]`, for the step with the datum
`D′` and the class with zero old terms. -/
theorem stepNonvanishingC_fibre_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 2 ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
    p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
    ∀ (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)), S = T.step k hk N₁ ν β p₁ →
    ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
      XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
      ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
      (S.withDatum D' hDh).StepNonvanishingC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g := by
  obtain ⟨β₀, h2, H⟩ := stepNonvanishingC_fibre_fromTowerG T.toG hA p
  refine ⟨β₀, h2, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS
  subst hS
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have G := H k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ p₁ hp0
    (by rw [e]; exact hp₁) (StepTower.scaleDataG_of_fixed T Dsc) (T.toG.step k hk N₁ ν β p₁) rfl
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans (by rw [e])
  subst hϱ' hb'
  intro G
  exact G

/-- **Proposition 2.6 at a chart datum of the fibre, with the local sums substituted.**  At a
scale of the tower `T` with `β > 0`, `p₁ > 0`, for a datum `D′` of the chart
`Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and a source `g` at which the partition functions
of the step with the datum `D′` do not vanish on the two segments (`StepNonvanishingC`):
`TstepC = exp [-β A^η_{k+1} - E''' |T₁| + ℱ_k(ψ^{(k)}, g) + ∑_z ℰ₀(z)
  + β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i]`,
all objects being those of the step with the datum `D′` and the class with zero old terms.  The
premises of `prop26C_zeroClass`, `sum_E0locC_zeroClass` and `F0C_eq_pair_zeroClass` which do not
depend on the datum are supplied by the tower (`R = 2`, `p⁺ = lvCpsi`, `δ₁ = ε = T.t`); the term
`ℰ_k(ψ^{(k)})` is zero for this class. -/
theorem stepIdentity_zeroClass_withDatum_of_nonvanishing {κmin : ℝ} (T : StepTower κmin)
    {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (Dsc : StepScaleData T k hk N₁ ν β p₁) (hβ : 0 < β) (hp₁ : 0 < p₁)
    (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hX : XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
      (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D')
    (g : Fld 3 3 N₁ T.m₁ (k + 1) 2)
    (hnv : ((T.step k hk N₁ ν β p₁).withDatum D' hDh).StepNonvanishingC
      (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g) :
    ((T.step k hk N₁ ν β p₁).withDatum D' hDh).TstepC
        (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g =
      Complex.exp (-((T.step k hk N₁ ν β p₁).β : ℂ) *
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).AnewC -
        (((T.step k hk N₁ ν β p₁).withDatum D' hDh).Eppp
            (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) : ℂ) *
          (((T.step k hk N₁ ν β p₁).withDatum D' hDh).nU : ℂ) +
        FcompAtC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)).m₀
          (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)).Tm (T.step k hk N₁ ν β p₁).a
          (T.step k hk N₁ ν β p₁).ν (Nat.le_succ k)
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).psiKdC g +
        ∑ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).E0locC
            (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z +
        (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
            g y i * ((T.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
              (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i) := by
  revert D' hDh hX g hnv
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have G := stepIdentity_zeroClass_withDatum_of_nonvanishingG T.toG
    (StepTower.scaleDataG_of_fixed T Dsc) hβ hp₁
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans (by rw [e])
  subst hϱ' hb'
  intro G
  exact G

/-- **The step identity of the zero class at every chart datum of the fibre and every source of
the unit ball, with the local energies and observables.**  Beyond the threshold of
`stepActivityBoundC_fibre_fromTower`, at every scale datum, for every datum `D′` of the chart
`Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and every source `g` with `∑ |g| < 1`:
`TstepC = exp [-β A^η_{k+1} - E''' |T₁| + ℱ_k(ψ^{(k)}, g) + ∑_z ℰ₀(z)
  + β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i]`
for the step with the datum `D′` and the class with zero old terms.  This is an equality of
exponentials; the normalization term `E''' |T₁|` is part of the exponent. -/
theorem stepIdentity_zeroClass_fibre_local_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 2 ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
    p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
    ∀ (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)), S = T.step k hk N₁ ν β p₁ →
    ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
      XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
      ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
      (S.withDatum D' hDh).TstepC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g =
        Complex.exp (-(S.β : ℂ) * (S.withDatum D' hDh).AnewC -
          ((S.withDatum D' hDh).Eppp (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) : ℂ) *
            ((S.withDatum D' hDh).nU : ℂ) +
          FcompAtC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)).m₀
            (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)).Tm S.a S.ν (Nat.le_succ k)
            (S.withDatum D' hDh).psiKdC g +
          ∑ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
            (S.withDatum D' hDh).E0locC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z +
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
              g y i * (S.withDatum D' hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                g y i) := by
  obtain ⟨β₀, h2, H⟩ := stepIdentity_zeroClass_fibre_local_fromTowerG T.toG hA p
  refine ⟨β₀, h2, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS
  subst hS
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have G := H k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ p₁ hp0
    (by rw [e]; exact hp₁) (StepTower.scaleDataG_of_fixed T Dsc) (T.toG.step k hk N₁ ν β p₁) rfl
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans (by rw [e])
  subst hϱ' hb'
  intro G
  exact G

/-- **The step identity of the zero class on the fibre, for given values of the local energies and
observables.**  Beyond the threshold of `stepActivityBoundC_fibre_fromTower`, at every scale datum,
for every datum `D′` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and every source
`g` with `∑ |g| < 1`: if `ℰ₀(z) = E z` for every root `z` and `ℳ₀(y; g)_i = β_U^{1/2} M y i` for
every site `(y, i)` (objects of the step with the datum `D′` and the class with zero old terms),
then
`TstepC = exp [-β A^η_{k+1} - E''' |T₁| + ℱ_k(ψ^{(k)}, g) + ∑_z E z + ∑_{y,i} g(y,i) M y i]`.
This is the form in which coefficient expansions of `ℰ₀(z)` and `β_U^{-1/2} ℳ₀(y; g)_i` (over any
index sets) are substituted; the factors `β_U^{-1/2}` and `β_U^{1/2}` cancel since
`β_U = β 3^k > 0`. -/
theorem stepIdentity_zeroClass_fibre_of_values_fromTower {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 2 ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
    p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
    ∀ (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)), S = T.step k hk N₁ ν β p₁ →
    ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
      XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
      ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
      ∀ (E : RootIdx 3 3 N₁ T.m₁ (k + 1) → ℂ) (M : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ),
        (∀ z, (S.withDatum D' hDh).E0locC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z = E z) →
        (∀ y i, (S.withDatum D' hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
          ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * M y i) →
        (S.withDatum D' hDh).TstepC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g =
          Complex.exp (-(S.β : ℂ) * (S.withDatum D' hDh).AnewC -
            ((S.withDatum D' hDh).Eppp (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) : ℂ) *
              ((S.withDatum D' hDh).nU : ℂ) +
            FcompAtC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)).m₀
              (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)).Tm S.a S.ν (Nat.le_succ k)
              (S.withDatum D' hDh).psiKdC g +
            ∑ z : RootIdx 3 3 N₁ T.m₁ (k + 1), E z +
            ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2, g y i * M y i) := by
  obtain ⟨β₀, h2, H⟩ := stepIdentity_zeroClass_fibre_of_values_fromTowerG T.toG hA p
  refine ⟨β₀, h2, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS
  subst hS
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have G := H k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ p₁ hp0
    (by rw [e]; exact hp₁) (StepTower.scaleDataG_of_fixed T Dsc) (T.toG.step k hk N₁ ν β p₁) rfl
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans (by rw [e])
  subst hϱ' hb'
  intro G
  exact G

end Balaban.Inhabited
