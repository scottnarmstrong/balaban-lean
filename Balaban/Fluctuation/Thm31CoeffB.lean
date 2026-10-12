/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31CoeffA
public import Balaban.Fluctuation.Thm31bStep
public import Balaban.Fluctuation.Thm31bWitness
public import Balaban.Fluctuation.Thm31WitnessMain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Canonical coefficients of Theorem 3.1 (b), and the coefficients on the landed instances

`obsCoeff I T = kernelMarkSum I.hker I.E1 T + I.Erem T` is the formula of the proof of
`thm31b_of_input`: the resummed products `h(i, T') E(i, S')` of the kernel with the interpolation
terms of the first-order marks (over `T' ∪ S' = T`), plus the interpolation term of the remainder
marks.  The theorems `thm31b_coeff`, `thm31b_coeff_M0` state the landed conclusions for it.

## What the formula reads

| coefficient | reads |
| --- | --- |
| `obsCoeff I T` | kernel values `I.hker i T'` for `T' ⊆ T`; for `S' ⊆ T` the first-order terms `markIntTerm BS.μ I.A (I.y1 i) (I.G1 i) S'`, i.e. `I.A s 1` (activities at `σ = 1`, `s ∈ [0,1]`), `I.Lab`, `I.y1`, `I.G1`; the remainder term `gsumCoeff` of `I.A · 1`, `I.yr`, `I.Gr`. It does not read `I.bx`, `Rσ`, the Schwarz data (`I.A` at `σ ≠ 1`), `I.hker` outside subsets of `T`, `B1`, `B2`, or any bound field. |

Congruence (`obsCoeff_congr`): the value at `T` is unchanged if the kernel agrees on subsets of `T`,
the activities (at `σ = 1`) agree on the labels whose cubes lie in `T`, and each mark agrees
whenever the cubes of its label lie in `T`.

The tables of `Thm31CoeffA` and this file give the exact inputs of the three coefficient families.

## Scope

Coefficients at a *fixed* step datum.  Nothing here makes them functions of the fields of the class,
proves locality, analyticity or covariance in the external fields, or roots them at polymers; no
generating set is chosen (`OUTPUT.md`: `OUTPUT-PARAM-COEFF`, `OUTPUT-ROOT-EMBED` remain open).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.SmallField.Def6 MeasureTheory Metric

section Raw

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
  {Lb : Type*} [Fintype Lb]

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

open Classical in
/-- **Congruence of `kernelMarkSum`**: the resummed term at `W` reads the kernel and the terms only on
subsets of `W`. -/
theorem kernelMarkSum_congr {ι : Type*} [Fintype ι] (h h' E E' : ι → Finset 𝔅 → ℂ) (W : Finset 𝔅)
    (hh : ∀ i T, T ⊆ W → h i T = h' i T) (hE : ∀ i S, S ⊆ W → E i S = E' i S) :
    kernelMarkSum h E W = kernelMarkSum h' E' W := by
  unfold kernelMarkSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun T _ =>
    Finset.sum_congr rfl fun S _ => ?_
  split_ifs with hTS
  · rw [hh i T (hTS ▸ Finset.subset_union_left), hE i S (hTS ▸ Finset.subset_union_right)]
  · rfl

/-- **Congruence of `markIntTerm`** in the labels: the `s`-integrated local term at `S` reads the
activities (at `σ = 1`) on labels with cubes in `S`, and the mark when its cubes lie in `S`. -/
theorem markIntTerm_congr {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] {Lab : CubeLabels m₀ j Ω Lb}
    {εH κH κ0 Kc εH' κH' κ0' Kc' : ℝ} (A : ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (A' : ℂ → ℂ → LabelAct Lab Ωb εH' κH' κ0' Kc') (y0 : Lb) {G G' : (∀ b, Ωb b) → ℂ}
    (S : Finset 𝔅) (hGdep : DepOn (blocksOf m₀ j Ω (Lab.ysite y0)) G)
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, blocksOf m₀ j Ω (Lab.ysite y) ⊆ S →
      (A (s : ℂ) 1).H y = (A' (s : ℂ) 1).H y)
    (hG : blocksOf m₀ j Ω (Lab.ysite y0) ⊆ S → G = G') :
    markIntTerm μ A y0 G S = markIntTerm μ A' y0 G' S := by
  unfold markIntTerm
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  exact Gst_congr μ μ (A (s : ℂ) 1) (A' (s : ℂ) 1).H _ S hGdep (fun _ _ => rfl) (hA s hs) hG

end Raw

section Obs

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {X : Type*} [MeasurableSpace X]
  {ν : Measure X} {m₀ : ℕ} {BS : ProdSplit ν d L N₁ m₁ K m₀} {W : ℝ → X → ℂ} {f : ℝ → X → ℂ}
  {bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ}

open Classical in
/-- **The canonical coefficient `m(T)` of Theorem 3.1 (b)**: the resummed first-order term
`∑ᵢ ∑_{T' ∪ S' = T} h(i,T') E₁(i,S')` plus the remainder term. -/
noncomputable def obsCoeff (I : ObsMarks ν BS W f bx) (T : Finset (CubeB (d := d) (L := L)
    (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)) : ℂ :=
  kernelMarkSum I.hker I.E1 T + I.Erem T

/-- The remainder term is the `gsumCoeff` of the remainder marks at `σ = 1`. -/
theorem ObsMarks.Erem_eq (I : ObsMarks ν BS W f bx) (T : Finset (CubeB (d := d) (L := L)
    (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)) :
    I.Erem T = gsumCoeff BS.μ I.Lab (fun t => I.A t 1) I.yr I.Gr T := rfl

open Classical in
/-- **Theorem 3.1 (b) for the canonical coefficients `obsCoeff`** (the conclusions of
`thm31b_of_input`). -/
theorem thm31b_coeff (I : ObsMarks ν BS W f bx) {κb : ℝ}
    (hκb : κb ≤ min I.κh I.κ' - I.κ0 - 1) :
    interpAvg ν W f = ∑ T, obsCoeff I T ∧ (∀ T, bx ∉ T → obsCoeff I T = 0) ∧
      ∀ T, ‖obsCoeff I T‖ ≤ (I.B1 + I.B2) * Real.exp (-κb * dExt T) := by
  have hR : 0 < I.Rσ := by linarith [I.hRσ]
  have hCPE : 0 ≤ CPE d L I.Kc I.κH I.κ0 I.κ' := by
    unfold CPE; have := one_le_c1 d L; positivity
  have hB1 : 0 ≤ I.B1 := by
    unfold ObsMarks.B1
    have := one_le_c1 d L
    have h0 : 0 ≤ CPE d L I.Kc I.κH I.κ0 I.κ' * I.Fm / I.Rσ :=
      div_nonneg (mul_nonneg hCPE I.hFm0) hR.le
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg I.hCh h0) (mul_nonneg I.hnmax
      (by linarith))) (sq_nonneg _)) (Real.exp_pos _).le
  have hB2 : 0 ≤ I.B2 := by
    unfold ObsMarks.B2
    exact mul_nonneg hCPE (Finset.sum_nonneg fun r _ =>
      mul_nonneg (I.hFr r).le (Real.exp_pos _).le)
  refine ⟨?_, fun T hT => ?_, fun T => ?_⟩
  · obtain ⟨hr1, hr2, -, -⟩ := I.rem_facts
    have hfirst : ∀ i : I.ι1, IntervalIntegrable
        (fun s : ℝ => avgPi BS.μ (I.A (s : ℂ) 1).H (I.G1 i)) MeasureTheory.volume 0 1 ∧
        (∫ s in (0 : ℝ)..1, avgPi BS.μ (I.A (s : ℂ) 1).H (I.G1 i)) = ∑ S, I.E1 i S :=
      fun i => markInt_expansion BS.μ I.hN le_rfl isPiUnion_univ_aux I.isOpen I.seg I.A (I.y1 i)
        (I.G1 i) (I.meas1 i) (I.dep1 i) (I.bound1 i) I.holt I.hκ0 I.hKc I.hεpos (I.hF1 i) I.hκ'
        I.hκG I.hκ I.hε
    have hsplit : interpAvg ν W f = ∫ s in (0 : ℝ)..1,
        (∑ i, (∑ T, I.hker i T) * avgPi BS.μ (I.A (s : ℂ) 1).H (I.G1 i) +
          avgPi BS.μ (I.A (s : ℂ) 1).H (fun Φ => ∑ r, I.Gr r (s : ℂ) Φ)) := by
      unfold interpAvg
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le zero_le_one] at hs
      exact I.avg_split hs
    have hint1 : IntervalIntegrable (fun s : ℝ => ∑ i, (∑ T, I.hker i T) *
        avgPi BS.μ (I.A (s : ℂ) 1).H (I.G1 i)) MeasureTheory.volume 0 1 := by
      have := IntervalIntegrable.sum (Finset.univ : Finset I.ι1) fun i _ =>
        (hfirst i).1.const_mul (∑ T, I.hker i T)
      convert this using 1
      ext s
      simp [Finset.sum_apply]
    rw [hsplit, intervalIntegral.integral_add hint1 hr1, hr2,
      intervalIntegral.integral_finsetSum fun i _ => (hfirst i).1.const_mul _]
    simp only [intervalIntegral.integral_const_mul]
    unfold obsCoeff
    rw [Finset.sum_add_distrib, kernelMarkSum_total]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hfirst i).2]
  · show kernelMarkSum I.hker I.E1 T + I.Erem T = 0
    rw [I.first_support T hT, (I.rem_facts).2.2.2 T hT, add_zero]
  · have hd := dExt_nonneg (m₀ := m₀) (j := K) (Ω := Set.univ) T
    have h1 := I.first_bound T
    have h2 := (I.rem_facts).2.2.1 T
    have hκe : min I.κh I.κ' ≤ I.κ' := min_le_right _ _
    have hκ0n : 0 ≤ I.κ0 := by linarith [aEnt_nonneg d L, I.hκ0]
    have e1 : Real.exp (-(min I.κh I.κ' - I.κ0 - 1) * dExt T) ≤ Real.exp (-κb * dExt T) :=
      Real.exp_le_exp.2 (by nlinarith)
    have e2 : Real.exp (-I.κ' * dExt T) ≤ Real.exp (-κb * dExt T) :=
      Real.exp_le_exp.2 (by nlinarith)
    show ‖kernelMarkSum I.hker I.E1 T + I.Erem T‖ ≤ _
    calc ‖kernelMarkSum I.hker I.E1 T + I.Erem T‖
        ≤ ‖kernelMarkSum I.hker I.E1 T‖ + ‖I.Erem T‖ := norm_add_le _ _
      _ ≤ I.B1 * Real.exp (-(min I.κh I.κ' - I.κ0 - 1) * dExt T) +
          I.B2 * Real.exp (-I.κ' * dExt T) := add_le_add h1 h2
      _ ≤ I.B1 * Real.exp (-κb * dExt T) + I.B2 * Real.exp (-κb * dExt T) :=
          add_le_add (mul_le_mul_of_nonneg_left e1 hB1) (mul_le_mul_of_nonneg_left e2 hB2)
      _ = _ := by ring

open Classical in
/-- `thm31b_of_input`, re-derived from `thm31b_coeff`. -/
theorem thm31b_of_obsCoeff (I : ObsMarks ν BS W f bx) {κb : ℝ}
    (hκb : κb ≤ min I.κh I.κ' - I.κ0 - 1) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) → ℂ,
      interpAvg ν W f = ∑ T, E T ∧ (∀ T, bx ∉ T → E T = 0) ∧
      ∀ T, ‖E T‖ ≤ (I.B1 + I.B2) * Real.exp (-κb * dExt T) :=
  ⟨obsCoeff I, (thm31b_coeff I hκb).1, (thm31b_coeff I hκb).2.1, (thm31b_coeff I hκb).2.2⟩

open Classical in
/-- **Congruence of `obsCoeff`**: the coefficient at `T` is unchanged under alternative kernel,
activities (at `σ = 1`) and marks on the labels of `I`, provided they agree with those of `I` on the
subsets of `T` (kernel), on labels with cubes in `T` (activities), and on marks whose label cubes lie
in `T`.  The right-hand side is the formula `obsCoeff` evaluated on the alternative data. -/
theorem obsCoeff_congr (I : ObsMarks ν BS W f bx) (T : Finset (CubeB (d := d) (L := L)
    (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ))
    {εH' κH' κ0' Kc' : ℝ} (A' : ℂ → ℂ → LabelAct I.Lab BS.Ωb εH' κH' κ0' Kc')
    (hker' : I.ι1 → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K
      Set.univ) → ℂ)
    (G1' : I.ι1 → (∀ b, BS.Ωb b) → ℂ) (Gr' : I.ιr → ℂ → (∀ b, BS.Ωb b) → ℂ)
    (hker : ∀ i T', T' ⊆ T → I.hker i T' = hker' i T')
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y,
      blocksOf m₀ K Set.univ (I.Lab.ysite y) ⊆ T → (I.A (s : ℂ) 1).H y = (A' (s : ℂ) 1).H y)
    (hG1 : ∀ i, blocksOf m₀ K Set.univ (I.Lab.ysite (I.y1 i)) ⊆ T → I.G1 i = G1' i)
    (hGr : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ r,
      blocksOf m₀ K Set.univ (I.Lab.ysite (I.yr r)) ⊆ T → I.Gr r (s : ℂ) = Gr' r (s : ℂ)) :
    obsCoeff I T = kernelMarkSum hker'
        (fun i S => markIntTerm BS.μ A' (I.y1 i) (G1' i) S) T +
      gsumCoeff BS.μ I.Lab (fun t => A' t 1) I.yr Gr' T := by
  have e1 : kernelMarkSum I.hker I.E1 T =
      kernelMarkSum hker' (fun i S => markIntTerm BS.μ A' (I.y1 i) (G1' i) S) T := by
    refine kernelMarkSum_congr _ _ _ _ T hker fun i S hS => ?_
    exact markIntTerm_congr BS.μ I.A A' (I.y1 i) S (I.dep1 i)
      (fun s hs y hy => hA s hs y (hy.trans hS)) (fun h => hG1 i (h.trans hS))
  have e2 : I.Erem T = gsumCoeff BS.μ I.Lab (fun t => A' t 1) I.yr Gr' T := by
    rw [ObsMarks.Erem_eq]
    exact gsumCoeff_congr BS.μ (fun t => I.A t 1) (fun t => A' t 1) I.yr I.Gr Gr' T
      (fun r u => I.depr r u) (fun s hs y hy => hA s hs y hy) hGr
  unfold obsCoeff
  rw [e1, e2]

end Obs

section Step

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **Theorem 3.1 (b) for the actual step, canonical form**: `S.M0 C g y i =
β_U^{1/2} ∑_T obsCoeff I T`, with the support and bound clauses. -/
theorem thm31b_coeff_M0 (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    {m₀ : ℕ} (BS : BlockSplit S m₀) (g : Fld d L N₁ m₁ (k + 1) N)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    {bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ}
    (I : ObsMarks S.nuFl BS (fun t x => S.Wone C 1 x + S.Wtwo C g t x)
      (fun t x => deriv (fun r => McompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
        (S.dataU (S.psiAt r x)) g y i) t) bx)
    {κb : ℝ} (hκb : κb ≤ min I.κh I.κ' - I.κ0 - 1) :
    S.M0 C g y i = ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T, obsCoeff I T ∧
      (∀ T, bx ∉ T → obsCoeff I T = 0) ∧
      ∀ T, ‖obsCoeff I T‖ ≤ (I.B1 + I.B2) * Real.exp (-κb * dExt T) := by
  obtain ⟨h1, h2, h3⟩ := thm31b_coeff I hκb
  refine ⟨?_, h2, h3⟩
  rw [← h1]
  rfl

end Step

section Witness

open Balaban.Localization.I5Inhabited Balaban.SmallField

/-- **The canonical coefficients on the landed instance of (a)** (`d = L = 3`, `N₁ = 6`, `k = 1`,
`N = 2`, zero class): with the `E1Marks` of `exists_e1Marks_datum` and the `DetExpansion` of
`nonempty_detExpansion`, `e1Coeff I D` satisfies the conclusions of `thm31a_coeff`.  Whether
`e1Coeff I D T` is nonzero for some `T` is not shown (the determinant value and the interpolation
integral are not evaluated). -/
theorem thm31a_coeff_witness :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)) (BS : BlockSplit S 0),
      0 < S.β ∧ 0 < S.p₁ ∧ Nonempty (S.RayData 2) ∧
      ∃ (I : E1Marks S (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) BS
          (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))))) (cdet : ℝ)
        (D : DetExpansion S 0 (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) I.κ' cdet),
        S.E0loc (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁))
            (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) = ∑ T, e1Coeff I D T ∧
        ∀ T, ‖e1Coeff I D T‖ ≤ (CPE 3 3 I.Kc I.κH I.κ0 I.κ' *
            (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) + cdet) *
          Real.exp (-I.κ' * dExt T) := by
  classical
  obtain ⟨m₁, S, BS, hβ, hp, -, hR, I, -⟩ := exists_e1Marks_datum (fun _ => 1) (fun _ _ => one_pos)
  obtain ⟨cdet, ⟨D⟩⟩ := nonempty_detExpansion S 0
    (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) (κ'' := I.κ') I.hκ'
  exact ⟨m₁, S, BS, hβ, hp, hR, I, cdet, D, (thm31a_coeff I le_rfl D).2.1,
    (thm31a_coeff I le_rfl D).2.2⟩

/-- **The canonical coefficients on the landed instance of (b)**: for every component `(y,i)`,
`M₀ = β_U^{1/2} ∑_T obsCoeff I T`, with the support and bound clauses at rate
`min(κ_h, κ') - κ₀ - 1`. -/
theorem thm31b_coeff_witness :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)) (g : Fld 3 3 6 m₁ 2 2)
      (BS : BlockSplit S 0),
      0 < S.β ∧ 0 < S.p₁ ∧ Nonempty (S.RayData 2) ∧
      ∀ (y : CTorus 3 3 6 m₁ 2) (i : Fin 2),
        ∃ I : ObsMarks S.nuFl BS
            (fun t x => S.Wone (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 1 x +
              S.Wtwo (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g t x)
            (fun t x => deriv (fun r => McompAt (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀
              (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm S.a S.ν (Nat.le_succ 1)
              (S.dataU (S.psiAt r x)) g y i) t) cube0,
          S.M0 (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g y i =
              ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T, obsCoeff I T ∧
          (∀ T, cube0 ∉ T → obsCoeff I T = 0) ∧
          ∀ T, ‖obsCoeff I T‖ ≤ (I.B1 + I.B2) *
            Real.exp (-(min I.κh I.κ' - I.κ0 - 1) * dExt T) := by
  obtain ⟨m₁, S, g, BS, hβ, hp, -, hR, -, hI⟩ := exists_obsMarks_datum
  refine ⟨m₁, S, g, BS, hβ, hp, hR, fun y i => ?_⟩
  obtain ⟨I⟩ := hI y i
  exact ⟨I, thm31b_coeff_M0 S _ BS g y i I (κb := min I.κh I.κ' - I.κ0 - 1) le_rfl⟩

end Witness

end Balaban.Fluctuation
