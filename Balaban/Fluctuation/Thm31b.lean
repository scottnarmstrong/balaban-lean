/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31bRem
public import Balaban.Fluctuation.Thm31bResum
public import Balaban.Fluctuation.Thm31cde
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 3.1 (b): the observable contribution, conditional on its input

FLUCTUATION.md §3.5 (b): `ℳ''₀(x;g)` is the average `∫₀¹ dt ∫ dμ_{1,t}` of an integrand split into
a first-order part `∑_y (H_k C^{1/2})(x,y) ψ̂(y)` (kernel `h(x,y;Y′)`, marks `ψ̂(y)` of mean zero)
and a remainder (a sum of marks).  `ObsMarks` is the named input: the conclusion of Proposition 3.3
for the actual observable integrand, including the analytic continuation in `σ` of the exponent
(P6 (4.63)) and the kernel expansion (P6 (4.62)).

`thm31b_of_input`: the integrand average is `∑_W E(W)` with
`|E(W)| ≤ B e^{-κ_b d_Ω(W)}`, `κ_b = min(κ_h, κ') - κ₀ - 1`, and `E(W) = 0` unless `W ∋ x`.
The three steps are: the marked terms vanish at `σ = 0` and gain `1/R_σ` by the Schwarz lemma
(`Thm31bVanish`, `Thm31bSchwarz`, `Thm31bFirst`); the products `h(i,T) G*(i,S)` are resummed over
the connected unions `T ∪ S` (`kernel_mark_resum`, `Thm31bResum`); the remainder is an interpolation
average (`Thm31bRem`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory Metric

section Obs

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {X : Type*} [MeasurableSpace X]

/-- **The named input for Theorem 3.1 (b)**: Proposition 3.3 for the observable integrand `f` in
the exponent `W` of `μ_{1,t}`.  `W(t) = ∑_y H(y;t,σ=1)` is block-local, with `H` holomorphic in `t`
(on `𝒰 ⊃ [0,1]`) and in `σ` (on the disc of radius `R_σ > 1`), vanishing at `σ = 0`; the integrand is
`∑_i (∑_T h(i,T)) ψ̂_i + (remainder marks)`, the `ψ̂_i` having mean zero for the block measure,
and the numerical hypotheses of Theorem 3.4 hold. -/
structure ObsMarks (ν : Measure X) {m₀ : ℕ} (BS : ProdSplit ν d L N₁ m₁ K m₀)
    (W : ℝ → X → ℂ) (f : ℝ → X → ℂ)
    (bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) where
  Lb : Type
  [fin : Fintype Lb]
  Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ Lb
  εH : ℝ
  κH : ℝ
  κG : ℝ
  κ0 : ℝ
  κ' : ℝ
  Kc : ℝ
  hN : L ^ m₀ ∣ N₁
  Rσ : ℝ
  hRσ : 1 < Rσ
  𝒰 : Set ℂ
  isOpen : IsOpen 𝒰
  seg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰
  A : ℂ → ℂ → LabelAct Lab BS.Ωb εH κH κ0 Kc
  holt : ∀ y Φ, DifferentiableOn ℂ (fun t => (A t 1).H y Φ) 𝒰
  holσ : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y Φ,
    DifferentiableOn ℂ (fun σ => (A (s : ℂ) σ).H y Φ) (ball (0 : ℂ) Rσ)
  zero : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y Φ, (A (s : ℂ) 0).H y Φ = 0
  hW : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
    W s x = ∑ y, (A (s : ℂ) 1).H y (BS.restr x)
  -- the first-order marks `ψ̂(y)`
  ι1 : Type
  [fin1 : Fintype ι1]
  y1 : ι1 → Lb
  G1 : ι1 → (∀ b, BS.Ωb b) → ℂ
  meas1 : ∀ i, Measurable (G1 i)
  dep1 : ∀ i, DepOn (blocksOf m₀ K Set.univ (Lab.ysite (y1 i))) (G1 i)
  F1 : ι1 → ℝ
  hF1 : ∀ i, 0 < F1 i
  bound1 : ∀ i Φ, ‖G1 i Φ‖ ≤ F1 i * Real.exp (-κG * Lab.dl (y1 i))
  mean1 : ∀ i, ∫ Φ, G1 i Φ ∂(Measure.pi BS.μ) = 0
  Fm : ℝ
  hFm : ∀ i, F1 i * Real.exp (-κ0 * Lab.dl (y1 i)) ≤ Fm
  -- the kernel `h(x,y;Y′)` and the cube of each mark
  bm : ι1 → CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ
  hbm : ∀ i, bm i ∈ blocksOf m₀ K Set.univ (Lab.ysite (y1 i))
  nmax : ℝ
  hnmax : 0 ≤ nmax
  hcount : ∀ c, ((Finset.univ.filter fun i => bm i = c).card : ℝ) ≤ nmax
  hker : ι1 → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) → ℂ
  Ch : ℝ
  κh : ℝ
  hCh : 0 ≤ Ch
  bound_h : ∀ i T, ‖hker i T‖ ≤ Ch * Real.exp (-κh * dExt T)
  supp_h : ∀ i T, bm i ∉ T → hker i T = 0
  x_h : ∀ i T, bx ∉ T → hker i T = 0
  hκh : κ0 ≤ κh
  hFm0 : 0 ≤ Fm
  -- the remainder marks
  ιr : Type
  [finr : Fintype ιr]
  nonemptyr : Nonempty ιr
  yr : ιr → Lb
  Gr : ιr → ℂ → (∀ b, BS.Ωb b) → ℂ
  measr : ∀ i u, Measurable (Gr i u)
  depr : ∀ i u, DepOn (blocksOf m₀ K Set.univ (Lab.ysite (yr i))) (Gr i u)
  Fr : ιr → ℝ
  hFr : ∀ i, 0 < Fr i
  boundr : ∀ i u Φ, ‖Gr i u Φ‖ ≤ Fr i * Real.exp (-κG * Lab.dl (yr i))
  holGr : ∀ i Φ, DifferentiableOn ℂ (fun u => Gr i u Φ) 𝒰
  x_r : ∀ i, bx ∈ blocksOf m₀ K Set.univ (Lab.ysite (yr i))
  -- Theorem 3.4 numerics
  hκ0 : aEnt d L + 1 ≤ κ0
  hKc : K0 d L κ0 + 1 ≤ Kc
  hεpos : 0 < εH
  hκ' : 0 ≤ κ'
  hκ0' : κ0 ≤ κ'
  hκG : κH ≤ κG
  hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH
  hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
    Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))
  -- the integrand
  hF : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
    f s x = ∑ i, (∑ T, hker i T) * G1 i (BS.restr x) + ∑ r, Gr r (s : ℂ) (BS.restr x)

attribute [instance] ObsMarks.fin ObsMarks.fin1 ObsMarks.finr


section Main

variable {ν : Measure X} {m₀ : ℕ} {BS : ProdSplit ν d L N₁ m₁ K m₀} {W : ℝ → X → ℂ} {f : ℝ → X → ℂ}
  {bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ}

open Classical in
theorem kernelMarkSum_total {ι : Type*} [Fintype ι]
    (h E : ι → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) → ℂ) :
    ∑ W, kernelMarkSum h E W = ∑ i, (∑ T, h i T) * (∑ S, E i S) := by
  unfold kernelMarkSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp [Finset.sum_ite_eq]

theorem ObsMarks.hAb (I : ObsMarks ν BS W f bx) (s : ℂ) (σ : ℂ) :
    ∀ y Φ, ‖(I.A s σ).H y Φ‖ ≤ I.εH := fun y Φ => ((I.A s σ).bound y Φ).trans (by
  have hκH : 0 ≤ I.κH := by
    linarith [aEnt_nonneg d L, one_le_c1 d L, I.hκ0, I.hκ, I.hκ']
  have : Real.exp (-I.κH * I.Lab.dl y) ≤ 1 := Real.exp_le_one_iff.2 (by
    nlinarith [I.Lab.dl_nonneg y, hκH])
  nlinarith [I.hεpos])

open Classical in
/-- **The split of the average**: at `σ = 1`, `⟨f(s)⟩_s = ∑ᵢ cᵢ ⟨ψ̂ᵢ⟩ + ⟨remainder⟩`. -/
theorem ObsMarks.avg_split (I : ObsMarks ν BS W f bx) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    avgFun ν W (f s) s =
      ∑ i, (∑ T, I.hker i T) * avgPi BS.μ (I.A (s : ℂ) 1).H (I.G1 i) +
        avgPi BS.μ (I.A (s : ℂ) 1).H (fun Φ => ∑ r, I.Gr r (s : ℂ) Φ) := by
  have hF0 : ∀ i, ∀ Φ, ‖(∑ T, I.hker i T) * I.G1 i Φ‖ ≤ ‖∑ T, I.hker i T‖ * I.F1 i := by
    intro i Φ
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ((I.bound1 i Φ).trans ?_) (norm_nonneg _)
    have hκG : 0 ≤ I.κG := by
      linarith [aEnt_nonneg d L, one_le_c1 d L, I.hκ0, I.hκ, I.hκ', I.hκG]
    have : Real.exp (-I.κG * I.Lab.dl (I.y1 i)) ≤ 1 := Real.exp_le_one_iff.2 (by
      nlinarith [I.Lab.dl_nonneg (I.y1 i), hκG])
    nlinarith [I.hF1 i]
  have hFr : ∀ r, ∀ Φ, ‖I.Gr r (s : ℂ) Φ‖ ≤ I.Fr r := by
    intro r Φ
    refine (I.boundr r _ Φ).trans ?_
    have hκG : 0 ≤ I.κG := by
      linarith [aEnt_nonneg d L, one_le_c1 d L, I.hκ0, I.hκ, I.hκ', I.hκG]
    have : Real.exp (-I.κG * I.Lab.dl (I.yr r)) ≤ 1 := Real.exp_le_one_iff.2 (by
      nlinarith [I.Lab.dl_nonneg (I.yr r), hκG])
    nlinarith [I.hFr r]
  have hmeasA : Measurable (fun Φ : ∀ b, BS.Ωb b => ∑ i, (∑ T, I.hker i T) * I.G1 i Φ) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (I.meas1 i)
  have hmeasR : Measurable (fun Φ : ∀ b, BS.Ωb b => ∑ r, I.Gr r (s : ℂ) Φ) :=
    Finset.measurable_sum _ fun r _ => I.measr r _
  have h1 := avgFun_eq_avgPi_gen BS W (f s) s (I.A (s : ℂ) 1).H
    (fun Φ => ∑ i, (∑ T, I.hker i T) * I.G1 i Φ + ∑ r, I.Gr r (s : ℂ) Φ)
    (I.A (s : ℂ) 1).meas (hmeasA.add hmeasR) (I.hW s hs) (I.hF s hs)
  rw [h1]
  have hbA : ∀ Φ, ‖∑ i, (∑ T, I.hker i T) * I.G1 i Φ‖ ≤ ∑ i, ‖∑ T, I.hker i T‖ * I.F1 i :=
    fun Φ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hF0 i Φ)
  have hbR : ∀ Φ, ‖∑ r, I.Gr r (s : ℂ) Φ‖ ≤ ∑ r, I.Fr r :=
    fun Φ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => hFr r Φ)
  rw [avgPi_add BS.μ (I.A (s : ℂ) 1).meas (I.hAb _ _) hmeasA hmeasR hbA hbR]
  congr 1
  rw [avgPi_sum BS.μ (I.A (s : ℂ) 1).meas (I.hAb _ _)
    (fun i Φ => (∑ T, I.hker i T) * I.G1 i Φ) (fun i => measurable_const.mul (I.meas1 i))
    (fun i => ‖∑ T, I.hker i T‖ * I.F1 i) hF0]
  exact Finset.sum_congr rfl fun i _ => avgPi_const_mul BS.μ _ _ _

open Classical in
/-- The `t`-integrated local term of the `i`-th first-order mark. -/
noncomputable def ObsMarks.E1 (I : ObsMarks ν BS W f bx) (i : I.ι1) (S : Finset
    (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)) : ℂ :=
  markIntTerm BS.μ I.A (I.y1 i) (I.G1 i) S

open Classical in
/-- The `t`-integrated local term of the remainder. -/
noncomputable def ObsMarks.Erem (I : ObsMarks ν BS W f bx) (S : Finset
    (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)) : ℂ :=
  ∫ s in (0 : ℝ)..1, Gsum BS.μ I.Lab (I.A (s : ℂ) 1).H I.yr (fun r => I.Gr r (s : ℂ)) S

theorem isPiUnion_univ_aux {m₀ : ℕ} :
    IsPiUnion m₀ K (Set.univ : Set (CTorus d L N₁ m₁ K)) :=
  fun z _ => ⟨cbase (cellSide L m₀ m₁ K) z, aligned_cbase z,
    mem_box_cbase (cellSide_pos (L := L) m₀ m₁ K) z, Set.subset_univ _⟩

/-- The constant of the first-order part. -/
noncomputable def ObsMarks.B1 (I : ObsMarks ν BS W f bx) : ℝ :=
  I.Ch * (CPE d L I.Kc I.κH I.κ0 I.κ' * I.Fm / I.Rσ) * (I.nmax * c1 d L) * I.Kc ^ 2 *
    Real.exp ((min I.κh I.κ' - I.κ0) * cG d L)

/-- The constant of the remainder. -/
noncomputable def ObsMarks.B2 (I : ObsMarks ν BS W f bx) : ℝ :=
  CPE d L I.Kc I.κH I.κ0 I.κ' * (∑ r, I.Fr r * Real.exp (-I.κ0 * I.Lab.dl (I.yr r)))

theorem ObsMarks.E1_bound (I : ObsMarks ν BS W f bx) (i : I.ι1) (S : Finset
    (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)) :
    ‖I.E1 i S‖ ≤ (CPE d L I.Kc I.κH I.κ0 I.κ' * I.Fm / I.Rσ) * Real.exp (-I.κ' * dExt S) := by
  have hR : 0 < I.Rσ := by linarith [I.hRσ]
  have hCPE : 0 ≤ CPE d L I.Kc I.κH I.κ0 I.κ' := by
    unfold CPE; have := one_le_c1 d L; positivity
  have hb := markInt_bound BS.μ I.hN le_rfl isPiUnion_univ_aux I.A (I.y1 i) (I.G1 i) (I.meas1 i)
    (I.dep1 i) (I.bound1 i) I.hκ0 I.hKc I.hεpos (I.hF1 i) I.hκ' I.hκG I.hκ I.hε I.hRσ I.holσ I.zero
    (I.mean1 i) S
  refine hb.trans ?_
  have : CPE d L I.Kc I.κH I.κ0 I.κ' * I.F1 i * Real.exp (-I.κ0 * I.Lab.dl (I.y1 i)) =
      CPE d L I.Kc I.κH I.κ0 I.κ' * (I.F1 i * Real.exp (-I.κ0 * I.Lab.dl (I.y1 i))) := by ring
  rw [this, div_eq_mul_inv, div_eq_mul_inv]
  have h2 := mul_le_mul_of_nonneg_left (I.hFm i) hCPE
  have h3 : 0 ≤ Real.exp (-I.κ' * dExt S) * I.Rσ⁻¹ := by positivity
  calc CPE d L I.Kc I.κH I.κ0 I.κ' * (I.F1 i * Real.exp (-I.κ0 * I.Lab.dl (I.y1 i))) *
        Real.exp (-I.κ' * dExt S) * I.Rσ⁻¹
      = (CPE d L I.Kc I.κH I.κ0 I.κ' * (I.F1 i * Real.exp (-I.κ0 * I.Lab.dl (I.y1 i)))) *
        (Real.exp (-I.κ' * dExt S) * I.Rσ⁻¹) := by ring
    _ ≤ (CPE d L I.Kc I.κH I.κ0 I.κ' * I.Fm) * (Real.exp (-I.κ' * dExt S) * I.Rσ⁻¹) :=
        mul_le_mul_of_nonneg_right h2 h3
    _ = _ := by ring

theorem ObsMarks.E1_support (I : ObsMarks ν BS W f bx) (i : I.ι1) (S : Finset
    (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)) (hS : I.bm i ∉ S) :
    I.E1 i S = 0 :=
  markIntTerm_support BS.μ I.hN le_rfl isPiUnion_univ_aux I.A (I.y1 i) (I.G1 i) (I.meas1 i)
    (I.dep1 i) (I.bound1 i) I.hκ0 I.hKc I.hεpos (I.hF1 i) I.hκ' I.hκG I.hκ I.hε S
    (fun hsub => hS (hsub (I.hbm i)))

theorem ObsMarks.first_bound (I : ObsMarks ν BS W f bx) (T : Finset
    (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)) :
    ‖kernelMarkSum I.hker I.E1 T‖ ≤
      I.B1 * Real.exp (-(min I.κh I.κ' - I.κ0 - 1) * dExt T) := by
  have hR : 0 < I.Rσ := by linarith [I.hRσ]
  have hCg : 0 ≤ CPE d L I.Kc I.κH I.κ0 I.κ' * I.Fm / I.Rσ := by
    have : 0 ≤ CPE d L I.Kc I.κH I.κ0 I.κ' := by
      unfold CPE; have := one_le_c1 d L; positivity
    exact div_nonneg (mul_nonneg this I.hFm0) hR.le
  exact kernel_mark_resum I.hN le_rfl I.bm I.hnmax I.hcount I.hker I.E1 I.hCh hCg I.bound_h
    I.supp_h I.E1_bound I.E1_support I.hκ0 I.hKc I.hκh I.hκ0' T

open Classical in
theorem ObsMarks.rem_facts (I : ObsMarks ν BS W f bx) :
    IntervalIntegrable (fun s : ℝ => avgPi BS.μ (I.A (s : ℂ) 1).H
      (fun Φ => ∑ r, I.Gr r (s : ℂ) Φ)) MeasureTheory.volume 0 1 ∧
    (∫ s in (0 : ℝ)..1, avgPi BS.μ (I.A (s : ℂ) 1).H (fun Φ => ∑ r, I.Gr r (s : ℂ) Φ)) =
      ∑ S, I.Erem S ∧
    (∀ S, ‖I.Erem S‖ ≤ I.B2 * Real.exp (-I.κ' * dExt S)) ∧
    (∀ S, bx ∉ S → I.Erem S = 0) := by
  obtain ⟨h1, h2⟩ := rem_integral_expansion BS.μ I.hN le_rfl isPiUnion_univ_aux I.isOpen I.seg
    (fun t => I.A t 1) I.yr I.Gr I.measr I.depr I.boundr I.holt I.holGr I.hκ0 I.hKc I.hεpos
    I.nonemptyr I.hFr I.hκ' I.hκG I.hκ I.hε
  obtain ⟨-, -, hb⟩ := avg_integral_expansion BS.μ I.hN le_rfl isPiUnion_univ_aux I.isOpen I.seg
    (fun t => I.A t 1) I.yr I.Gr I.measr I.depr I.boundr I.holt I.holGr I.hκ0 I.hKc I.hεpos
    I.nonemptyr I.hFr I.hκ' I.hκG I.hκ I.hε
  refine ⟨h1, h2, fun S => hb S, fun S hS => ?_⟩
  unfold ObsMarks.Erem
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (0 : ℂ)) (fun s _ =>
    rem_support BS.μ I.hN le_rfl isPiUnion_univ_aux (fun t => I.A t 1) I.yr I.Gr I.measr I.depr
      I.boundr I.hκ0 I.hKc I.hεpos I.hFr I.hκ' I.hκG I.hκ I.hε I.x_r S hS (s : ℂ))]
  simp

theorem ObsMarks.first_support (I : ObsMarks ν BS W f bx) (T : Finset
    (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)) (hT : bx ∉ T) :
    kernelMarkSum I.hker I.E1 T = 0 := by
  classical
  unfold kernelMarkSum
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun T' _ =>
    Finset.sum_eq_zero fun S' _ => ?_
  split_ifs with h
  · rw [I.x_h i T' (fun hb => hT (h ▸ Finset.mem_union_left _ hb)), zero_mul]
  · rfl

open Classical in
/-- **Theorem 3.1 (b), conditional on its input `ObsMarks`** (FLUCTUATION.md §3.5 (b)): the
integrand average `∫₀¹ dt ⟨f(t)⟩_{1,t}` equals `∑_W E(W)` with `E(W) = 0` unless `W ∋ x` and
`|E(W)| ≤ (B₁ + B₂) e^{-κ_b d_Ω(W)}` for every rate `κ_b ≤ min(κ_h, κ') - κ₀ - 1`
(`B₁` carries the factor `1/R_σ` of the Schwarz lemma, `B₂` is the remainder constant). -/
theorem thm31b_of_input (I : ObsMarks ν BS W f bx) {κb : ℝ}
    (hκb : κb ≤ min I.κh I.κ' - I.κ0 - 1) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) → ℂ,
      interpAvg ν W f = ∑ T, E T ∧ (∀ T, bx ∉ T → E T = 0) ∧
      ∀ T, ‖E T‖ ≤ (I.B1 + I.B2) * Real.exp (-κb * dExt T) := by
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
  refine ⟨fun T => kernelMarkSum I.hker I.E1 T + I.Erem T, ?_, fun T hT => ?_, fun T => ?_⟩
  · -- the value
    obtain ⟨hr1, hr2, -, -⟩ := I.rem_facts
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
    calc ‖kernelMarkSum I.hker I.E1 T + I.Erem T‖
        ≤ ‖kernelMarkSum I.hker I.E1 T‖ + ‖I.Erem T‖ := norm_add_le _ _
      _ ≤ I.B1 * Real.exp (-(min I.κh I.κ' - I.κ0 - 1) * dExt T) +
          I.B2 * Real.exp (-I.κ' * dExt T) := add_le_add h1 h2
      _ ≤ I.B1 * Real.exp (-κb * dExt T) + I.B2 * Real.exp (-κb * dExt T) :=
          add_le_add (mul_le_mul_of_nonneg_left e1 hB1) (mul_le_mul_of_nonneg_left e2 hB2)
      _ = _ := by ring

end Main

end Obs

end Balaban.Fluctuation
