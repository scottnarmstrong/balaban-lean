/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ActivityFamilyAnalytic
public import Balaban.Inhabited.MarksNumericsFromTower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The zero-source activity family on the common labels of all roots, at the shared tower

The mark records `ParamMarkFamily` and `InterpMarks` (hence `E1MarksC`) need, for the exponent
`W₁` of the step, one activity family on one label system chosen before the root, holomorphic in a
complex interpolation parameter `u` on an open set containing `[0,1]`, analytic in the chart datum,
and summing to `W₁(s)` for real `s ∈ [0,1]`.  This file supplies that activity half.

Let `A = labelActFamilyOn … I hF` be the analytic family of `activityFamilyAnalytic_fromTower`
(entropy constant `2 (K₀ + 1)`).  The zero-source family is
`A⁰(e, u) = u² · A((e.1, 0), u)` for `‖u‖ < 2` (`zeroSourceAct A 2`), and it is extended by zero
to the common label system `commonLabels (thickLabels I.𝒴 I.dom) … reads dom` of the roots
(`commonAct`), for arbitrary bridge data `reads`, `dom` chosen after the family.

`zeroSourceActivity_common_fromTower` gives, for one choice of `Jr`, `val`, `I`, `hF`:

* the two fibre identities of `A` (`W₁` and `W₂`), so that the same witness serves the source
  activity and the marks;
* the numerical fields at the amplitude `ε_H = 2² · 2 ε_U` and the entropy constant
  `K_c′ = 2 (K₀ + 1) + rootUnionK = T.marksKc'`: `0 < ε_H`, the logarithmic bound, and
  `ε_H ≤ stepTheta 3 3 T.marksKc' (2 κ_dec − 1) T.κ0 T.κ'` (the field `hε` of the records; the rate
  fields are `StepTower.marks_hκ0`, `marks_hKc`, `marks_hκ'`, `marks_hκ`);
* for the common family `A⁰c`:
  `holA` of `ParamMarkFamily` on `V = physV` (all of it: complex `h` allowed) and
  `𝒰 = ball 0 2`, for every configuration; `holA` of `InterpMarks` at every `e ∈ physV`; `contA`;
  the label sum; `hW` at every datum `D` of the chart with `D.h ≡ h₀` for the exponent
  `(S.withDatum D).WoneC`, in particular `InterpMarks.hW` for `S.WoneC` at the datum of the step;
  the `ParamMarkFamily` with no marks over `physV`, `ball 0 2` and the compact carrier
  `physCarrier S 1 hp`; and, as an acceptance check of the activity fields, the record
  `InterpMarks` for the exponent `S.WoneC` and the zero integrand
  (`nonempty_interpMarks_zero_of_activity`).

**Parameter sets.**  `holA` and `contA` hold on the open set `physV × ball 0 2`: the zero-source
family reads only the datum coordinate of `e`, and `(e.1, 0)` lies in `physVq … q` for every
`e ∈ physV`.  The identity `hW` holds on the constant-`h₀` fibre only (where `S.withDatum D`
exists).  `ParamMarkFamily` contains no `hW` and needs the open set; `InterpMarks` is a record at
one datum.

The marks `G`, their fields `dep`, `bound`, `holG`, `contG`, `hF`, and `E1MarksC` are NOT here.
Zero class; independent of the choice of generators.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

section InterpZero

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {X : Type*} [MeasurableSpace X]

/-- **The activity half fills the record `InterpMarks`.**  An activity family `A` on labels `Lab`
with the identity `hW` for the exponent `W`, holomorphic in `u` on an open `𝒰 ⊃ [0,1]`, with the
numerical fields of the record, and any label `y₀`, give the record `InterpMarks ν BS W 0` for the
zero integrand: the activity is `A`, and there is one mark, equal to zero, anchored at `y₀`.
(Acceptance check of the activity fields only: the marks of a non-zero integrand are separate
data.) -/
theorem nonempty_interpMarks_zero_of_activity {ν : Measure X} {m₀ : ℕ}
    (BS : ProdSplit ν d L N₁ m₁ K m₀) (W : ℝ → X → ℂ) {Lb : Type} [Fintype Lb]
    {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ Lb}
    {εH κH κ0 κ' Kc : ℝ} (hN : L ^ m₀ ∣ N₁) {𝒰 : Set ℂ} (h𝒰 : IsOpen 𝒰)
    (hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰)
    (A : ℂ → LabelAct Lab BS.Ωb εH κH κ0 Kc) (y₀ : Lb)
    (holA : ∀ y Φ, DifferentiableOn ℂ (fun u => (A u).H y Φ) 𝒰)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH) (hκ' : 0 ≤ κ')
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hW : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
      W s x = ∑ y, (A (s : ℂ)).H y (BS.restr x)) :
    Nonempty (InterpMarks ν BS W (fun _ _ => (0 : ℂ))) :=
  ⟨{ Lb := Lb
     Lab := Lab
     ι := Unit
     nonempty := ⟨()⟩
     εH := εH
     κH := κH
     κG := κH
     κ0 := κ0
     κ' := κ'
     Kc := Kc
     F0 := fun _ => 1
     hN := hN
     𝒰 := 𝒰
     isOpen := h𝒰
     seg := hseg
     A := A
     y0 := fun _ => y₀
     G := fun _ _ _ => 0
     meas := fun _ _ => measurable_const
     dep := fun _ _ _ _ _ => rfl
     bound := fun _ _ _ => by
       simp only [norm_zero, one_mul]
       exact (Real.exp_pos _).le
     holA := holA
     holG := fun _ _ => differentiableOn_const _
     hκ0 := hκ0
     hKc := hKc
     hεpos := hεpos
     hF0 := fun _ => one_pos
     hκ' := hκ'
     hκG := le_rfl
     hκ := hκ
     hε := hε
     hW := hW
     hF := fun s _ => Filter.Eventually.of_forall fun x => by simp }⟩

end InterpZero

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Set Metric
open scoped Classical

/-- `K₀ ≤ 2 (K₀ + 1)`: the entropy constant of the base family of the mark records. -/
theorem StepTower.marks_K0_le {κmin : ℝ} (T : StepTower κmin) :
    K0 3 3 T.κ0 ≤ 2 * (K0 3 3 T.κ0 + 1) := by
  have := T.marks_K0_pos
  linarith

/-- **The zero-source activity family on the common labels, for a given source witness.**  The
statement of `zeroSourceActivity_common_fromTower` after its witness existential.  Let `val` be the
formula of the direct terms, `I` a `DirectTerms` record and `hF` a relative family over
`physVq … q`, with positive amplitude `ε_U`, and let `A = labelActFamilyOn … I hF` carry the
identities of `activityFamilyAnalytic_of_witness` used here (analyticity and continuity on
`physVq … q × ball 0 2`, the fibre identities for `W₁`, `W₂`, and the slice identity for `W₁`).
If `4 ε_U ≤ C_E (log b)^{3p}/√b + q C_F (log b)^p/√b` and `β` is at least the threshold of
`exists_beta0_marks` for `2 C_E`, `2 C_F`, then conclusions 1–8 of
`zeroSourceActivity_common_fromTower` hold for the family `A⁰c` built from `A`. -/
theorem zeroSourceActivity_common_of_witness {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) (p : ℕ) {CE CF : ℝ} (hCE : 0 < CE) (hCF : 0 < CF)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β : ℝ)
    (hβ : (exists_beta0_marks T hHull p (CE := 2 * CE) (CF := 2 * CF)
      (mul_nonneg zero_le_two hCE.le) (mul_nonneg zero_le_two hCF.le)).choose ≤ β)
    (p₁ : ℝ) (hp0 : 0 < p₁) (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1)
    (D : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁)
    (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
          (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
            (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1)
          (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
          (physSΛEta S S.a₁ S.ν T.t (q / S.β))
          (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
          (physAgΘ S) (AgFDirPair S))
    (hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
        (physVq S S.a₁ S.ν T.t q))
    (hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
            (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))
    (hεpos : 0 < S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
            (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))
    (hε4 : 4 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
            (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) ≤
        CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k))
    (Jr : S.JointRep T.t (2 * p₁))
    (hA' : ∃ A : physParam 2 S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit 1 hp).Ωb
              (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) (2 * T.κdec - 1) T.κ0
              (2 * (K0 3 3 T.κ0 + 1)),
        A = labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
              (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU T.κ0_ent
              T.marks_K0_le ∧
        (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
          AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (A r.1 r.2).H y Φ)
            (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) 2)) ∧
        (∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ u : ℂ, ‖u‖ < 2 → ∀ y : {Y // Y ∈ I.𝒴},
          Continuous ((A e u).H y)) ∧
        (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∀ s ∈ Icc (0 : ℝ) 1,
          Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
              ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) =
            (s : ℂ) ^ 2 * ∑ y, (A ((e.1, 0) : physParam 2 S) (s : ℂ)).H y
              ((S.blockSplit 1 hp).restr x)) ∧
        (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∑ x', ∑ i, ‖e.2 x' i‖ < q →
          ∀ t ∈ Icc (0 : ℝ) 1,
          Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
              ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (t : ℂ) • S.hatC x) =
            ∑ y, (A e (t : ℂ)).H y ((S.blockSplit 1 hp).restr x) -
              ∑ y, (A ((e.1, 0) : physParam 2 S) (t : ℂ)).H y
                ((S.blockSplit 1 hp).restr x)) ∧
        (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ s ∈ Icc (0 : ℝ) 1,
          (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
            (s : ℂ) ^ 2 * ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
              (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
              ((S.blockSplit 1 hp).restr x))) :
          0 < 2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) ≤
              2 * CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
                2 * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) ≤
              (stepOutputPhysical T hHull).theta ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) ≤
              stepTheta 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' ∧
          ∃ A : physParam 2 S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit 1 hp).Ωb
              (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) (2 * T.κdec - 1) T.κ0
              (2 * (K0 3 3 T.κ0 + 1)),
            A = labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                  (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU T.κ0_ent
                  T.marks_K0_le ∧
            (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∀ s ∈ Icc (0 : ℝ) 1,
              Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                  ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) =
                (s : ℂ) ^ 2 * ∑ y, (A ((e.1, 0) : physParam 2 S) (s : ℂ)).H y
                  ((S.blockSplit 1 hp).restr x)) ∧
            (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∑ x', ∑ i, ‖e.2 x' i‖ < q →
              ∀ t ∈ Icc (0 : ℝ) 1,
              Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                  ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (t : ℂ) • S.hatC x) =
                ∑ y, (A e (t : ℂ)).H y ((S.blockSplit 1 hp).restr x) -
                  ∑ y, (A ((e.1, 0) : physParam 2 S) (t : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
            ∀ {ι : Type} [Fintype ι] (reads : ι → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
              (dom : ι → Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
              (hdomR : ∀ b, ∀ Y ∈ dom b, IsDj 1 (k + 1) Y),
            ∃ A0 : physParam 2 S → ℂ → LabelAct
                (commonLabels (thickLabels I.𝒴 I.dom) (show 3 ^ 1 ∣ N₁ by simpa using h3N)
                  (by norm_num) reads dom hdomR) (S.blockSplit 1 hp).Ωb
                (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)))) (2 * T.κdec - 1) T.κ0 T.marksKc',
              A0 = commonAct (zeroSourceAct A 2 (by norm_num))
                  (show 3 ^ 1 ∣ N₁ by simpa using h3N) (by norm_num) reads dom hdomR
                  (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two ∧
              (∀ y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (A0 r.1 r.2).H y Φ)
                  (physV S S.a₁ S.ν T.t ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physV S S.a₁ S.ν T.t, ∀ y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                DifferentiableOn ℂ (fun u => (A0 e u).H y Φ) (ball (0 : ℂ) 2)) ∧
              (∀ y, ∀ e ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ ball (0 : ℂ) 2,
                Continuous ((A0 e u).H y)) ∧
              (∀ (e : physParam 2 S) (u : ℂ) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                ∑ y, (A0 e u).H y Φ =
                  sqFactor 2 u * ∑ y, (A ((e.1, 0) : physParam 2 S) u).H y Φ) ∧
              (∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
                ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                  (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                    ∑ y, (A0 ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (s : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                  ∑ y, (A0 ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                    (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ
                (commonLabels (thickLabels I.𝒴 I.dom) (show 3 ^ 1 ∣ N₁ by simpa using h3N)
                  (by norm_num) reads dom hdomR) A0
                (fun i : Empty => i.elim) (fun _ _ _ _ => (0 : ℂ)) 0 (fun i : Empty => i.elim)
                (physV S S.a₁ S.ν T.t) (ball (0 : ℂ) 2) (physCarrier S 1 hp)) ∧
              (∀ _y₀ : {Y // Y ∈ I.𝒴} ⊕ RootUnionLb 1 reads dom,
                Nonempty (InterpMarks S.nuFl (S.blockSplit 1 hp)
                  (S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) (fun _ _ => (0 : ℂ)))) := by
  classical
  obtain ⟨hβ₂, hmarks⟩ := (exists_beta0_marks T hHull p (CE := 2 * CE) (CF := 2 * CF)
    (mul_nonneg zero_le_two hCE.le) (mul_nonneg zero_le_two hCF.le)).choose_spec
  have hβ2 := hβ
  have hβ3 : 3 ≤ β := le_trans hβ₂ hβ2
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  have hR2 : (0 : ℝ) ≤ 2 := by norm_num
  have hH : BgHyp 3 3 (k + 1) (rhoSep T.m₁) (compWeight 3 S.a₁) S.ν := by
    subst hS
    exact bgHyp_lv (k := k) T.m₁ hνpos.le hν
  have hXi : XiCData S.G' S.a S.ν (k + 1) 1 T.t S.D' := by
    subst hS
    exact D.xi
  obtain ⟨A, hAeq, han, hcontA, hW1, hW2, hS1⟩ := hA'
  -- the size of the amplitude
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hb1 : (1 : ℝ) ≤ β * 3 ^ k := by nlinarith
  have hlog : 0 ≤ Real.log (β * 3 ^ k) := Real.log_nonneg hb1
  have hsq : 0 ≤ Real.sqrt (β * 3 ^ k) := Real.sqrt_nonneg _
  have hY0 : 0 ≤ CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) :=
    div_nonneg (mul_nonneg hCF.le (pow_nonneg hlog p)) hsq
  have hamp : 2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) ≤
      2 * CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        2 * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) := by
    have e1 : q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) =
        q * (CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k)) := by ring
    have e2 : 2 * CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) =
        2 * (CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k)) := by ring
    have e3 : 2 * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) =
        2 * (CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k)) := by ring
    have hqY := mul_le_of_le_one_left hY0 hq
    rw [e1] at hε4
    rw [e2, e3]
    linarith
  obtain ⟨hθ, hθ'⟩ := hmarks β k hβ2 _ hamp
  have hε0 : 0 < 2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) :=
    mul_pos (by norm_num) (mul_pos two_pos hεpos)
  refine ⟨hε0, hamp, hθ, hθ', A, hAeq, hW1, hW2, ?_⟩
  intro ι _ reads dom hdomR
  have hsub : ∀ e ∈ physV S S.a₁ S.ν T.t,
      ((e.1, 0) : physParam 2 S) ∈ physVq S S.a₁ S.ν T.t q :=
    fun e he => fst_zero_mem_physVq S he hq0
  have hV : IsOpen (physV (N := 2) S S.a₁ S.ν T.t) := isOpen_physV S S.a₁ S.ν T.t hH
  -- the fields of the zero-source family before the extension
  have han0 : ∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
      AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (zeroSourceAct A 2 hR2 r.1 r.2).H y Φ)
        (physV S S.a₁ S.ν T.t ×ˢ ball (0 : ℂ) 2) :=
    fun y Φ => zeroSourceAct_analyticOnNhd hR2 le_rfl hV hsub (han y Φ)
  have hcont0 : ∀ (y : {Y // Y ∈ I.𝒴}), ∀ e ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ ball (0 : ℂ) 2,
      Continuous ((zeroSourceAct A 2 hR2 e u).H y) := fun y e he u hu =>
    zeroSourceAct_continuous hR2 e u (hcontA _ (hsub e he) u (by simpa using hu) y)
  have hdiff0 : ∀ e ∈ physV S S.a₁ S.ν T.t, ∀ (y : {Y // Y ∈ I.𝒴})
      (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
      DifferentiableOn ℂ (fun u => (zeroSourceAct A 2 hR2 e u).H y Φ) (ball (0 : ℂ) 2) := by
    intro e he y Φ
    refine zeroSourceAct_differentiableOn hR2 le_rfl e ?_
    rw [hAeq]
    exact labelActFamilyOn_differentiableOn S 1 _ hF hN3 hp0 hR2 hεU T.κ0_ent T.marks_K0_le
      (hsub e he) y Φ
  have hWfib : ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
      XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
        (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
          ∑ y, (commonAct (zeroSourceAct A 2 hR2) hN3 (by norm_num) reads dom hdomR hε0.le
            T.κ0_two ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (s : ℂ)).H y
            ((S.blockSplit 1 hp).restr x) := by
    intro D' hDh hX g
    refine commonAct_hW_interp (zeroSourceAct A 2 hR2) hN3 (by norm_num) reads dom hdomR hε0.le
      T.κ0_two ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) ?_
    refine zeroSourceAct_hW hR2 one_lt_two _ ?_
    intro s hs
    filter_upwards [hS1] with x hx
    exact hx D' hDh hX s hs
  have hdiffc : ∀ e ∈ physV S S.a₁ S.ν T.t, ∀ y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
      DifferentiableOn ℂ (fun u => (commonAct (zeroSourceAct A 2 hR2) hN3 (by norm_num) reads dom
        hdomR hε0.le T.κ0_two e u).H y Φ) (ball (0 : ℂ) 2) :=
    fun e he y Φ => commonAct_holA_differentiableOn (zeroSourceAct A 2 hR2) hN3
      (by norm_num) reads dom hdomR hε0.le T.κ0_two e (fun y Φ => hdiff0 e he y Φ) y Φ
  have hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ ball (0 : ℂ) 2 := fun s hs => by
    rw [mem_ball_zero_iff]
    exact norm_ofReal_lt_of_mem hs one_lt_two
  have he₀ : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
      (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈ physV S S.a₁ S.ν T.t :=
    (mk_mem_physFibre S S.hh₀ hXi (g := 0) (by simp)).1
  refine ⟨_, rfl, ?_, hdiffc, ?_, ?_, hWfib, fun s hs => hWfib S.D' S.hh₀ hXi 0 s hs, ⟨?_⟩, ?_⟩
  · exact fun y Φ => commonAct_holA_analytic (zeroSourceAct A 2 hR2) hN3 (by norm_num) reads dom
      hdomR hε0.le T.κ0_two (Q := Set.univ) (fun y Φ _ => han0 y Φ) y Φ (Set.mem_univ _)
  · intro y e he u hu
    cases y with
    | inl y => exact hcont0 y e he u hu
    | inr y => exact continuous_const
  · intro e u Φ
    exact (commonAct_total (zeroSourceAct A 2 hR2) hN3 (by norm_num) reads dom hdomR hε0.le
      T.κ0_two e u Φ).trans (zeroSourceAct_total A 2 hR2 e u Φ)
  · exact paramMarkFamily_common (zeroSourceAct A 2 hR2) hN3 (by norm_num) reads dom hdomR hε0.le
      T.κ0_two (S.blockSplit 1 hp).μ (fun i : Empty => i.elim) (fun _ _ _ _ => (0 : ℂ)) 0
      (fun i : Empty => i.elim) (physV S S.a₁ S.ν T.t) (ball (0 : ℂ) 2) (physCarrier S 1 hp)
      hV isOpen_ball hseg
      (isCompact_physCarrier S 1 hp) (measurableSet_physCarrier S 1 hp)
      (ae_mem_physCarrier S 1 hp) (fun _ _ _ => measurable_const) (fun _ i _ _ => i.elim)
      (fun y Φ _ => han0 y Φ) (fun i _ _ => i.elim)
      (fun y e he u hu => (hcont0 y e he u hu).continuousOn) (fun i _ _ _ _ => i.elim)
  · exact fun y₀ => nonempty_interpMarks_zero_of_activity (S.blockSplit 1 hp) _ hN3 isOpen_ball
      hseg (commonAct (zeroSourceAct A 2 hR2) hN3 (by norm_num) reads dom hdomR hε0.le T.κ0_two
        ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))) y₀
      (fun y Φ => hdiffc _ he₀ y Φ) T.marks_hκ0 T.marks_hKc hε0 T.marks_hκ' T.marks_hκ hθ'
      (fun s hs => hWfib S.D' S.hh₀ hXi 0 s hs)


/-- **The zero-source activity family on the common labels of all roots, at the shared tower: the
activity half of `ParamMarkFamily` and `InterpMarks`.**  After the tower `T` (with
`stepHullMin ≤ κmin`) choose `β₀, C_E, C_F`.  For every scale, torus, mass, `β ≥ β₀`, cutoff
`0 < p₁ ≤ A₁ (log β_k)^p`, source radius `0 < q ≤ 1` and per-scale package, at the step
`S = T.step k hk N₁ ν β p₁` there is one choice of `Jr`, `val`, `I`, `hF` (as in
`activityFamilyAnalytic_fromTower`) such that, with `ε_U = β · prop33EpsEtaScaled … (q/β)`:

* `val` has the formula of the direct terms;
* (numerical fields) `0 < 2² · 2 ε_U`,
  `2² · 2 ε_U ≤ C_E (log β_k)^{3p}/√β_k + C_F (log β_k)^p/√β_k`, and `2² · 2 ε_U` is at most the
  threshold of the physical constants record and at most
  `stepTheta 3 3 T.marksKc' (2 κ_dec − 1) T.κ0 T.κ'`;
* for `A = labelActFamilyOn … I hF` with entropy constant `2 (K₀ + 1)`: almost everywhere, on the
  fibre `h ≡ h₀`, `Jr.W1 (e.1, s ψ̂) = s² ∑_y A((e.1, 0), s)_y` and
  `Jr.W2 e.2 (e.1, t ψ̂) = ∑_y A(e, t)_y − ∑_y A((e.1, 0), t)_y`;
* for every bridge data `reads`, `dom` (with `IsDj` domains), the family
  `A⁰c = commonAct (zeroSourceAct A 2) … reads dom` on the labels
  `commonLabels (thickLabels I.𝒴 I.dom) … reads dom`, with amplitude `2² · 2 ε_U`, rate
  `2 κ_dec − 1`, `κ₀ = T.κ0` and entropy constant `T.marksKc'`, satisfies
  1. (`holA` of `ParamMarkFamily`) `(e, u) ↦ A⁰c(e, u)_y(Φ)` is analytic on `physV × ball 0 2`
     for every label and every configuration;
  2. (`holA` of `InterpMarks`) `u ↦ A⁰c(e, u)_y(Φ)` is differentiable on `ball 0 2` for `e ∈ physV`;
  3. (`contA`) `Φ ↦ A⁰c(e, u)_y(Φ)` is continuous for `e ∈ physV`, `u ∈ ball 0 2`;
  4. `∑_y A⁰c(e, u)_y(Φ) = sqFactor 2 u · ∑_y A((e.1, 0), u)_y(Φ)`;
  5. (`hW` on the fibre) for every datum `D` of the chart with `D.h ≡ h₀`, every source coordinate
     `g` and `s ∈ [0,1]`: `(S.withDatum D).WoneC s ψ̂ = ∑_y A⁰c((rawOf D, g), s)_y` almost
     everywhere;
  6. (`InterpMarks.hW` for `S.WoneC`) `S.WoneC s ψ̂ = ∑_y A⁰c((rawOf S.D', 0), s)_y` almost
     everywhere, for `s ∈ [0,1]`;
  7. the `ParamMarkFamily` with no marks over `physV`, `ball 0 2` and `physCarrier S 1 hp`;
  8. (acceptance check of the activity fields of `InterpMarks`) for every common label `y₀` the
     record `InterpMarks S.nuFl (S.blockSplit 1 hp) S.WoneC 0` for the zero integrand exists (built
     with the activity `A⁰c` at the datum of the step, `𝒰 = ball 0 2`, `κ' = T.κ'` and one zero
     mark at `y₀`).  This is not `E1MarksC`, whose integrand is the masked derivative of `Φ₁`. -/
theorem zeroSourceActivity_common_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ hp0 : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      StepScaleData T k hk N₁ ν β p₁ →
      ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Jr : S.JointRep T.t (2 * p₁))
          (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
          (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1)
                (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
                (physSΛEta S S.a₁ S.ν T.t (q / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S))
          (hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
              (physVq S S.a₁ S.ν T.t q))
          (hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)),
          (∀ x w σ Θ, val x w σ Θ =
            (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ
                Θ.1 +
            (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
              dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                (onXi S.G' S.a₁ S.ν T.t
                  (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                    (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                      s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
          0 < 2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) ≤
              CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
                CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) ≤
              (stepOutputPhysical T hHull).theta ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) ≤
              stepTheta 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' ∧
          ∃ A : physParam 2 S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit 1 hp).Ωb
              (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) (2 * T.κdec - 1) T.κ0
              (2 * (K0 3 3 T.κ0 + 1)),
            A = labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                  (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU T.κ0_ent
                  T.marks_K0_le ∧
            (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∀ s ∈ Icc (0 : ℝ) 1,
              Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                  ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) =
                (s : ℂ) ^ 2 * ∑ y, (A ((e.1, 0) : physParam 2 S) (s : ℂ)).H y
                  ((S.blockSplit 1 hp).restr x)) ∧
            (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∑ x', ∑ i, ‖e.2 x' i‖ < q →
              ∀ t ∈ Icc (0 : ℝ) 1,
              Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                  ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (t : ℂ) • S.hatC x) =
                ∑ y, (A e (t : ℂ)).H y ((S.blockSplit 1 hp).restr x) -
                  ∑ y, (A ((e.1, 0) : physParam 2 S) (t : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
            ∀ {ι : Type} [Fintype ι] (reads : ι → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
              (dom : ι → Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
              (hdomR : ∀ b, ∀ Y ∈ dom b, IsDj 1 (k + 1) Y),
            ∃ A0 : physParam 2 S → ℂ → LabelAct
                (commonLabels (thickLabels I.𝒴 I.dom) (show 3 ^ 1 ∣ N₁ by simpa using h3N)
                  (by norm_num) reads dom hdomR) (S.blockSplit 1 hp).Ωb
                (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)))) (2 * T.κdec - 1) T.κ0 T.marksKc',
              A0 = commonAct (zeroSourceAct A 2 (by norm_num))
                  (show 3 ^ 1 ∣ N₁ by simpa using h3N) (by norm_num) reads dom hdomR
                  (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two ∧
              (∀ y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (A0 r.1 r.2).H y Φ)
                  (physV S S.a₁ S.ν T.t ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physV S S.a₁ S.ν T.t, ∀ y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                DifferentiableOn ℂ (fun u => (A0 e u).H y Φ) (ball (0 : ℂ) 2)) ∧
              (∀ y, ∀ e ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ ball (0 : ℂ) 2,
                Continuous ((A0 e u).H y)) ∧
              (∀ (e : physParam 2 S) (u : ℂ) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                ∑ y, (A0 e u).H y Φ =
                  sqFactor 2 u * ∑ y, (A ((e.1, 0) : physParam 2 S) u).H y Φ) ∧
              (∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
                ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                  (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                    ∑ y, (A0 ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (s : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                  ∑ y, (A0 ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                    (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ
                (commonLabels (thickLabels I.𝒴 I.dom) (show 3 ^ 1 ∣ N₁ by simpa using h3N)
                  (by norm_num) reads dom hdomR) A0
                (fun i : Empty => i.elim) (fun _ _ _ _ => (0 : ℂ)) 0 (fun i : Empty => i.elim)
                (physV S S.a₁ S.ν T.t) (ball (0 : ℂ) 2) (physCarrier S 1 hp)) ∧
              (∀ _y₀ : {Y // Y ∈ I.𝒴} ⊕ RootUnionLb 1 reads dom,
                Nonempty (InterpMarks S.nuFl (S.blockSplit 1 hp)
                  (S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) (fun _ _ => (0 : ℂ)))) := by
  classical
  obtain ⟨β₁, CE, CF, hβ₁, hCE, hCF, hfam⟩ := activityFamilyAnalytic_fromTower T hA p
  have hm := exists_beta0_marks T hHull p (CE := 2 * CE) (CF := 2 * CF)
    (mul_nonneg zero_le_two hCE.le) (mul_nonneg zero_le_two hCF.le)
  refine ⟨max β₁ hm.choose, 2 * CE, 2 * CF, le_trans hm.choose_spec.1 (le_max_right _ _),
    by linarith, by linarith, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq D S hS hp
  have hβ1 : β₁ ≤ β := le_trans (le_max_left _ _) hβ
  have hβ2 : hm.choose ≤ β := le_trans (le_max_right _ _) hβ
  obtain ⟨Jr, val, 𝒴, Tt, I, -, -, hval, -, -, -, hF, hεU, hεpos, hε4, hA'⟩ :=
    hfam k hk N₁ h3N hN ν hνpos hν β hβ1 p₁ hp0 hp₁ q hq0 hq D S hS hp
  obtain ⟨A, hAeq, han, hcontA, -, -, hW1, hW2, hS1, -, -, -, -, -⟩ := hA' T.marks_K0_le
  exact ⟨Jr, val, I, hF, hεU, hval, zeroSourceActivity_common_of_witness T hHull p hCE hCF k hk N₁
    h3N ν hνpos hν β hβ2 p₁ hp0 q hq0 hq D S hS hp val I hF hεU hεpos hε4 Jr
    ⟨A, hAeq, han, hcontA, hW1, hW2, hS1⟩⟩


/-- **Non-vacuity.**  For one tower `T : StepTower stepHullMin` (so that the hull condition holds),
at `k = 1`, `N₁ = 6`, `ν = 1/81`, `A₁ = 1`, `p = 0`, `p₁ = 1`, `q = 1` and one `β` above the
thresholds of `StepTower.scale` and of `zeroSourceActivity_common_fromTower`, the per-scale package
exists and the amplitude of the common zero-source family is positive and below the threshold
`stepTheta` at the enlarged entropy constant `T.marksKc'`. -/
example : ∃ (T : StepTower stepHullMin) (β : ℝ),
    Nonempty (StepScaleData T 1 le_rfl 6 (1 / 81) β 1) ∧
    ∃ εH : ℝ, 0 < εH ∧ εH ≤ stepTheta 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' := by
  obtain ⟨T⟩ := exists_stepTower stepHullMin
  obtain ⟨βray, -, hscale⟩ := T.scale (A₁ := 1) one_pos 0
  obtain ⟨β₀, CE, CF, -, -, -, h⟩ :=
    zeroSourceActivity_common_fromTower T le_rfl (A₁ := 1) one_pos 0
  have hν : (1 / 81 : ℝ) * 3 ^ (2 * (1 + 1)) ≤ 1 := by norm_num
  have hp₁ : (1 : ℝ) ≤ pLog 1 0 (max βray β₀ * 3 ^ 1) := by simp [pLog]
  obtain ⟨D⟩ := hscale 1 le_rfl 6 (by norm_num) (by norm_num) (1 / 81) (by norm_num) hν
    (max βray β₀) (le_max_left _ _) 1 one_pos hp₁
  obtain ⟨-, -, -, -, -, -, hpos, -, -, hθ, -⟩ := h 1 le_rfl 6 (by norm_num) (by norm_num) (1 / 81)
    (by norm_num) hν (max βray β₀) (le_max_right _ _) 1 one_pos hp₁ 1 one_pos le_rfl D _ rfl
    one_pos
  exact ⟨T, max βray β₀, ⟨D⟩, _, hpos, hθ⟩

end Balaban.Inhabited
