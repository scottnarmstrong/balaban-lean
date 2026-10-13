/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.Thm31bPolymer
public import Balaban.Fluctuation.Thm31CoeffB
public import Balaban.Fluctuation.RootActiveSize
public import Balaban.Polymer.MarkedCubesVanish
import Mathlib.Tactic.Positivity

/-!
# Support of the canonical observable coefficients on polymer domains

For the canonical coefficients `obsCoeff I T = kernelMarkSum I.hker I.E1 T + I.Erem T` of
`Balaban.Fluctuation.Thm31CoeffB` we determine where they can be nonzero.

* `ObsMarks.Erem_eq_zero_of_not_isPolyDom`: the remainder term vanishes unless `sitesOf T` is a
  polymer domain.  No further input is needed.
* `ObsMarks.E1_eq_zero_of_dOmega_top`: each first-order term `E1 i S` vanishes when
  `dOmega (sitesOf S) = ⊤`, and it vanishes unless the cube `bm i` lies in `S`.
* `kernelMarkSum_eq_zero_of_dOmega_top`: the resummed sum `∑ᵢ ∑_{T ∪ S = W} h(i,T) E(i,S)` vanishes
  when `dOmega (sitesOf W) = ⊤`, provided every nonzero `h i T` has `bm i ∈ T` and finite
  `dOmega (sitesOf T)`, and likewise every nonzero `E i S`.  The reason: two sets with finite
  `dOmega` that share a cube have a union with finite `dOmega` (`finSet_union`).
* `ObsMarks.obsCoeff_eq_zero_of_not_isPolyDom_of_kernel_supp`: the same for `obsCoeff`, assuming
  that the kernel `I.hker i T` vanishes unless `dOmega (sitesOf T) ≠ ⊤`.
* `thm31b_coeff_M0_regroup_of_kernel_supp`: with that kernel support, the expansion of `M0` is
  regrouped on collar hulls with no remainder.

## What is not proved

The kernel support clause is not a field of `ObsMarks`: the record only bounds `I.hker i T` by
`Ch e^{-κh dExt T}`, and `dExt T` is the constant `Mbig` when `dOmega = ⊤`.  So it is an extra
premise here (`_of_kernel_supp`).  The record produced by `obsMarks_zeroClass_family` is stated
existentially and does not say that its kernel is `obsHker` of a family of domains in `𝒟_{k+1}`, so
the premise is not discharged at the tower.

The clauses of Theorem 3.1 (b) of `notes/phase1/FLUCTUATION.md` that remain open are those listed
in `Balaban.Inhabited.Thm31bPolymer`: termwise locality in the datum and the source, analyticity in
`g`, reality and symmetry, and the paper's prefactor.  The output rate `hullRate 3 3 (3/2 κ_dec)` is
positive only under a numerical condition on `κ_dec` (`hullRate_three_pos_iff`); it is not claimed.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited MeasureTheory Metric

section Generic

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

/-- A set of cubes that is not a polymer domain has `dOmega = ⊤`. -/
theorem dOmega_top_of_not_isPolyDom {T : Finset 𝔅} (hT : ¬ IsPolyDom m₀ K (sitesOf T)) :
    dOmega m₀ K Set.univ (sitesOf T) = ⊤ := by
  by_contra h
  rcases T.eq_empty_or_nonempty with rfl | hne
  · exact h dOmega_empty
  · exact hT (isPolyDom_iff_dOmega_ne_top.2 ⟨hne, h⟩)

open Classical in
/-- **Vanishing of the resummed sum off finite sets.**  If every nonzero `h i T` and every nonzero
`E i S` has `bm i` in its set and finite `dOmega`, then `kernelMarkSum h E W = 0` when
`dOmega (sitesOf W) = ⊤`. -/
theorem kernelMarkSum_eq_zero_of_dOmega_top {ι : Type*} [Fintype ι] (h E : ι → Finset 𝔅 → ℂ)
    (bm : ι → 𝔅)
    (hh : ∀ i T, h i T ≠ 0 → bm i ∈ T ∧ dOmega m₀ K Set.univ (sitesOf T) ≠ ⊤)
    (hE : ∀ i S, E i S ≠ 0 → bm i ∈ S ∧ dOmega m₀ K Set.univ (sitesOf S) ≠ ⊤)
    (W : Finset 𝔅) (hW : dOmega m₀ K Set.univ (sitesOf W) = ⊤) :
    kernelMarkSum h E W = 0 := by
  unfold kernelMarkSum
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun T _ =>
    Finset.sum_eq_zero fun S _ => ?_
  split_ifs with hTS
  · by_contra hne
    obtain ⟨hT1, hT2⟩ := hh i T (left_ne_zero_of_mul hne)
    obtain ⟨hS1, hS2⟩ := hE i S (right_ne_zero_of_mul hne)
    have hnd : ¬ Disjoint T S := Finset.not_disjoint_iff.2 ⟨bm i, hT1, hS1⟩
    have := finSet_union (m₀ := m₀) (j := K) (Ω := Set.univ) hnd hT2 hS2
    exact this (hTS ▸ hW)
  · rfl

end Generic

section Obs

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {X : Type*} [MeasurableSpace X]
  {ν : Measure X} {m₀ : ℕ} {BS : ProdSplit ν d L N₁ m₁ K m₀} {W : ℝ → X → ℂ} {f : ℝ → X → ℂ}
  {bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ}

/-- **The remainder term of `obsCoeff` vanishes off polymer domains.** -/
theorem ObsMarks.Erem_eq_zero_of_not_isPolyDom (I : ObsMarks ν BS W f bx) {T : Finset (CubeB
    (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)}
    (hT : ¬ IsPolyDom m₀ K (sitesOf T)) : I.Erem T = 0 := by
  rw [ObsMarks.Erem_eq]
  exact gsumCoeff_eq_zero_of_dOmega_top I.hN _ _ _ _ _ (dOmega_top_of_not_isPolyDom hT)

/-- **A first-order term vanishes when `dOmega = ⊤`.** -/
theorem ObsMarks.E1_eq_zero_of_dOmega_top (I : ObsMarks ν BS W f bx) (i : I.ι1) {S : Finset
    (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)}
    (hS : dOmega m₀ K Set.univ (sitesOf S) = ⊤) : I.E1 i S = 0 := by
  have h0 : (fun s : ℝ => Gst BS.μ I.Lab (I.A (s : ℂ) 1).H
      (blocksOf m₀ K Set.univ (I.Lab.ysite (I.y1 i))) (I.G1 i) S) = fun _ => 0 :=
    funext fun s => Gst_eq_zero_of_dOmega_top BS.μ I.hN le_rfl isPiUnion_univ_aux I.Lab _
      (I.y1 i) _ S hS
  show markIntTerm BS.μ I.A (I.y1 i) (I.G1 i) S = 0
  unfold markIntTerm
  rw [h0]
  simp

open Classical in
/-- **The first-order part of `obsCoeff` vanishes off polymer domains, given the kernel support.**
If `I.hker i T ≠ 0` implies that `dOmega (sitesOf T) ≠ ⊤`, then `kernelMarkSum I.hker I.E1 W = 0`
whenever `dOmega (sitesOf W) = ⊤`. -/
theorem ObsMarks.kernelMarkSum_eq_zero_of_kernel_supp (I : ObsMarks ν BS W f bx)
    (hker : ∀ i T, I.hker i T ≠ 0 → dOmega m₀ K Set.univ (sitesOf T) ≠ ⊤)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)}
    (hT : dOmega m₀ K Set.univ (sitesOf T) = ⊤) : kernelMarkSum I.hker I.E1 T = 0 :=
  kernelMarkSum_eq_zero_of_dOmega_top I.hker I.E1 I.bm
    (fun i T' h => ⟨by_contra fun hb => h (I.supp_h i T' hb), hker i T' h⟩)
    (fun i S h => ⟨by_contra fun hb => h (I.E1_support i S hb), fun h' =>
      h (I.E1_eq_zero_of_dOmega_top i h')⟩) T hT

/-- **`obsCoeff` vanishes off polymer domains, given the kernel support.** -/
theorem ObsMarks.obsCoeff_eq_zero_of_not_isPolyDom_of_kernel_supp (I : ObsMarks ν BS W f bx)
    (hker : ∀ i T, I.hker i T ≠ 0 → dOmega m₀ K Set.univ (sitesOf T) ≠ ⊤)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)}
    (hT : ¬ IsPolyDom m₀ K (sitesOf T)) : obsCoeff I T = 0 := by
  unfold obsCoeff
  rw [I.kernelMarkSum_eq_zero_of_kernel_supp hker (dOmega_top_of_not_isPolyDom hT),
    I.Erem_eq_zero_of_not_isPolyDom hT, add_zero]

end Obs

section Step

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **The canonical expansion of `M0`, regrouped on collar hulls with no remainder**, given the
kernel support.  `S.M0 C g y i = √β_U ∑_{X ∈ image detCollarHull} detCollarGrouped (obsCoeff I) X`;
the grouped terms are nonzero only on domains of `𝒟_{k+1}` containing the box of the root cube,
and satisfy the hull bound with constant `B1 + B2` and rate `κb`. -/
theorem thm31b_coeff_M0_regroup_of_kernel_supp (hL : 3 ≤ L) (S : StepSetting d L N₁ m₁ k N ϱ)
    (C : StepClass d L N₁ m₁ k N ϱ) {m₀ : ℕ} (BS : BlockSplit S m₀)
    (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    {bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ}
    (I : ObsMarks S.nuFl BS (fun t x => S.Wone C 1 x + S.Wtwo C g t x)
      (fun t x => deriv (fun r => McompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
        (S.dataU (S.psiAt r x)) g y i) t) bx)
    {κb : ℝ} (hκb : κb ≤ min I.κh I.κ' - I.κ0 - 1) (hκb0 : 0 ≤ κb)
    (hker : ∀ j T, I.hker j T ≠ 0 → dOmega m₀ (k + 1) Set.univ (sitesOf T) ≠ ⊤) :
    S.M0 C g y i = ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (K := k + 1) m₀ (k + 1) Set.univ))).image detCollarHull,
          detCollarGrouped (obsCoeff I) X ∧
      (∀ X : Set (CTorus d L N₁ m₁ (k + 1)), detCollarGrouped (obsCoeff I) X ≠ 0 →
        IsDj m₀ (k + 1) X ∧ box bx.1 (cellSide L m₀ m₁ (k + 1)) ⊆ X) ∧
      ∀ X : Set (CTorus d L N₁ m₁ (k + 1)), ‖detCollarGrouped (obsCoeff I) X‖ ≤
        hullConst d L κb (I.B1 + I.B2) * Real.exp (-hullRate d L κb * sizeJ m₀ (k + 1) X) := by
  obtain ⟨h1, h2, h3⟩ := thm31b_coeff_M0 S C BS g y i I hκb
  have hc : 0 ≤ I.B1 + I.B2 := by
    have h0 := (norm_nonneg (obsCoeff I ∅)).trans (h3 ∅)
    have he : 0 < Real.exp (-κb * dExt (∅ : Finset (CubeB (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ))) := Real.exp_pos _
    exact nonneg_of_mul_nonneg_left h0 he
  obtain ⟨e1, e2, e3⟩ := Inhabited.rooted_regroup_of_supp (m₀ := m₀) (K := k + 1) hL I.hN hc hκb0
    bx (obsCoeff I) h2
    (fun T hT => by
      by_contra hp
      exact hT (I.obsCoeff_eq_zero_of_not_isPolyDom_of_kernel_supp hker hp)) h3
  exact ⟨by rw [h1, e1], e2, e3⟩

end Step

end Balaban.Fluctuation
