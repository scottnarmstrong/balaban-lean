/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldDecInputE
public import Balaban.Fluctuation.ClassOldDecInputM
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The settings of the decoupled expansion with a localized ambient generator

For an inherited label `(j, y, X)` of a class member, the decoupled expansion
`eterm_expansion_hat_rawY` composes the old term with the backgrounds of three generating sets: the
new level `𝔹_{k+1} = Gp`, the ambient set `Gk` of level `k` and the term generator `Gj`.  In P3
(4.32) the ambient set is the minimal set `𝔹_k(X)` of (4.4)-(4.6) around `X`, with
`𝔹_j(X) ≺ 𝔹_k(X) ≺ 𝔹_k`, `Ω₁(𝔹_k(X)) ⊂ X₀` and `X₀^{~r₀} ⊂ X₁` ((4.7), (4.8)).

* `bgSetting_X₁f_eq_univ_of_termGen_univ`: the field `hq : Gj ≺ Gk` of `BgSetting` puts `Ω₁(Gj)` in
  the data sites of `Gk`, hence in `X₀`; so if the term generator has `Ω₁(Gj) = 𝕋` (the whole-level
  sets `levelGS j` of the landed classes, `bgSetting_X₁f_eq_univ_of_levelGS`), then `X₁f = 𝕋` for
  every ambient set `Gk` (the case `Gk = stepG` is `bgSetting_stepG_X₁f_eq_univ`).
* `torusDist_lt_of_mem_composeDep`: the sites read by a composition at a site `x` are within the
  radius `r₀ L^{m₁} L^K` of `x`.
* `bgSetting_localGk`, `flSetting_localGk`: `BgSetting` and `FlSetting` for an ambient set `Gk` at
  its own separation index, with `X₀ = dataSites Gk`, from base settings of the step (any other
  ambient set) and the facts on `Gk` that the settings mention: `bgR0 d L ≤ ϱ₁`, `Gj ≺ Gk`,
  `collar Gj ⊆ Ω₁(Gk)`, `Ω_{k+1}(Gk) = ∅` and the margin: the ball of radius `r₀ L^{m₁} L^{k+1}`
  about each data site of `Gk` lies in `X₁f`.
* `classOldDecLocal_expansion`, `classOldDecObsLocal_expansion`: the decoupled expansions of one
  inherited energy label and of one inherited observable label with the ambient set `Gk` and the
  fluctuation set `Hm` at their own separation indices.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₀ ϱ₁ ϱ₂ ϱm : ℝ}

section Refute

/-- **A whole term generator forces `X₁f = 𝕋`, for every ambient set.**  If the term generator `Gj`
of a `BgSetting` with a level generating set `Gp` has `Ω₁(Gj) = 𝕋`, then `X₁f` is the whole
torus: by `Gj ≺ Gk` every site is in `Ω₁(Gk)`, hence a data site of `Gk`, hence in `X₀`, and the
ball of `hN` about it contains the site itself. -/
theorem bgSetting_X₁f_eq_univ_of_termGen_univ
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG' : IsLevel Gp (k + 1))
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂} {a₁ ν c BG κ r₀ eps δ₃ : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hΩ : Gj.Ω 1 = Finset.univ) : X₁f = Finset.univ := by
  refine Finset.eq_univ_of_forall fun y => ?_
  have hyk : y ∈ Gk.Ω 1 :=
    hB.hq 1 le_rfl (by omega) (by rw [hΩ]; exact Finset.mem_univ y)
  have hy0 : y ∈ X₀ := hB.dsX₀ y ((mem_dataSites _).2 (Or.inl hyk))
  have hd : (3 : ℝ) ≤ d := by exact_mod_cast hB.Sp.hd
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hr : 0 < r₀ := lt_of_lt_of_le (by positivity) hB.hr₀
  have hsp : 0 < Gp.spacing y := by
    rw [hG'.spacing_eq]; positivity
  refine hB.hN y hy0 (by rw [hG'.Ω_one]; exact Finset.mem_univ _) y ?_
  rw [Green.torusDist_self_eq_zero]
  positivity

/-- **The whole-level term generators of the landed classes force `X₁f = 𝕋`.**  For the term
generator `levelGS j` (`1 ≤ j`), the generator of `zeroTerms`, `qTerms` and `pinTerms`, every
`BgSetting` with a level generating set `Gp` has `X₁f = 𝕋`, whatever the ambient set `Gk`. -/
theorem bgSetting_X₁f_eq_univ_of_levelGS
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG' : IsLevel Gp (k + 1))
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁} {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k + 1)
    {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N Gp Gk
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ₂) j hjk)
      a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j₁) :
    X₁f = Finset.univ :=
  bgSetting_X₁f_eq_univ_of_termGen_univ hG' hB (by simp [levelGS, hj1])

end Refute

section Margin

/-- The layer index of every site is at most the top level of the torus. -/
theorem layerIndex_le_top {K : ℕ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁)
    (x : CTorus d L N₁ m₁ K) : G.layerIndex x ≤ K := by
  classical
  unfold GeneratingSet.layerIndex
  split_ifs with h
  · exact (Classical.choose_spec h).2.1
  · exact Nat.zero_le _

/-- **The sites read by a composition are near the site.**  Every site `u` of `composeDep G G' x`
(the site `x` and the blocks of `x` in `G` and `G'`) is within the torus distance
`r₀ L^{m₁} L^K` of `x`, when `r₀ ≥ 4 d L³` and `d ≥ 1`. -/
theorem torusDist_lt_of_mem_composeDep {K : ℕ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
    {G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱm} {r₀ : ℝ} (hd : 1 ≤ d)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀) {x u : CTorus d L N₁ m₁ K} (hu : u ∈ composeDep G G' x) :
    Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x u < r₀ * (L : ℝ) ^ m₁ * (L : ℝ) ^ K := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hl : (1 : ℝ) ≤ (L : ℝ) ^ K := one_le_pow₀ hL1
  have hcoord : ∀ μ, ((Green.cycRep (x μ - u μ)).natAbs : ℝ) ≤ (L : ℝ) ^ K - 1 := fun μ =>
    natAbs_cycRep_le_of_coordNear
      (composeDep_coord_bound le_rfl hu (fun _ => layerIndex_le_top G x)
        (fun _ => layerIndex_le_top G' x) μ).symm
  have hsum : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x u ≤ d * ((L : ℝ) ^ K - 1) := by
    unfold Green.torusDist
    calc _ ≤ ∑ _μ : Fin d, ((L : ℝ) ^ K - 1) := Finset.sum_le_sum fun μ _ => hcoord μ
      _ = _ := by simp; ring
  have hlt := radius_lt (m₁ := m₁) hd1 hL1 hl hr₀
  have h3 : (d : ℝ) * ((L : ℝ) ^ K - 1) ≤ d * (3 * (L : ℝ) ^ K - 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

end Margin

section Settings

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₀}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₀' X₁f X₁f' : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

/-- Every generating set precedes a level generating set of the top level `k + 1`. -/
theorem precedes_of_isLevel_top (hG' : IsLevel Gp (k + 1)) : Precedes Gk Gp := by
  intro i hi1 hik x _
  have hxl := (GeneratingSet.mem_layer _).1 (hG'.mem_layer x)
  exact Gp.Ω_antitone hi1 hik (by omega) hxl.1

/-- A generating set with no layer `k + 1` precedes a level generating set of level `k`. -/
theorem precedes_of_isLevel_of_top_empty (hG : IsLevel Hm k) (htop : Gk.Ω (k + 1) = ∅) :
    Precedes Gk Hm := by
  intro i hi1 hik x hx
  by_cases hi : i ≤ k
  · have hxl := (GeneratingSet.mem_layer _).1 (hG.mem_layer x)
    exact Hm.Ω_antitone hi1 hi (by omega) hxl.1
  · have hik' : i = k + 1 := by omega
    subst hik'
    rw [htop] at hx
    exact absurd hx (Finset.notMem_empty x)

/-- **`BgSetting` for a localized ambient set `Gk`.**  From a base `BgSetting` of the step with any
ambient set `Gk0` and the same term generator `Gj` (the fields that do not mention the ambient set,
`X₀` or `X₁f` are taken from it), the setting holds for an ambient set `Gk` at its own separation
index `ϱ₁` with `X₀ = dataSites Gk`, given: `bgR0 d L ≤ ϱ₁` (the only premise of `BgHyp` on the
index), `Gj ≺ Gk`, `collar Gj ⊆ Ω₁(Gk)`, and the margin `hmar`: every site within the torus
distance `r₀ L^{m₁} L^{k+1}` of a data site of `Gk` lies in `X₁f` (P3 (4.8): `X₀^{~r₀} ⊂ X₁`).
`Gk ≺ Gp`, the collar of `Gk` and the reads `composeDep Gk Gp` follow. -/
theorem bgSetting_localGk (hB0 : BgSetting N Gp Gk0 Gj a₁ ν c BG κ r₀ eps δ₃ X₀' X₁f' j₁)
    (hG' : IsLevel Gp (k + 1)) (hϱ₁ : bgR0 d L ≤ ϱ₁) (hq : Precedes Gj Gk)
    (hcol : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    (hmar : ∀ x ∈ dataSites Gk, ∀ y : CTorus d L N₁ m₁ (k + 1),
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        r₀ * (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) → y ∈ X₁f) :
    BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ (dataSites Gk) X₁f j₁ where
  hS := hB0.hS
  Sp := hB0.Sp
  ha₁ := hB0.ha₁
  HBp := hB0.HBp
  HBk := { hB0.HBp with hϱ := hϱ₁ }
  HBj := hB0.HBj
  hP := precedes_of_isLevel_top hG'
  hq := hq
  colk := fun z _ => by rw [hG'.Ω_one]; exact Finset.mem_univ z
  colj := hcol
  hκ := hB0.hκ
  hM := hB0.hM
  num := hB0.num
  dsX₀ := fun _ hx => hx
  hN := fun x hx _ y hy => hmar x hx y (by rwa [hG'.spacing_eq] at hy)
  hr := hB0.hr
  hr₀ := hB0.hr₀
  dep := fun x hx y hy => hmar x hx y
    (torusDist_lt_of_mem_composeDep (by have := hB0.HBp.hd; omega) hB0.hr₀ hy)
  hj := hB0.hj

/-- **`FlSetting` for a localized ambient set `Gk`.**  From a base `FlSetting` of the step with
any ambient set `Gk0` (the fields that do not mention the ambient set or `X₁f`), a `BgSetting` for
`Gk` (its fields `dsX₀`, `hN` give the margin for the reads `composeDep Gk Hm`), a level-`k`
fluctuation set `Hm`, and `Ω_{k+1}(Gk) = ∅` (so `Gk ≺ Hm`). -/
theorem flSetting_localGk (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF0 : FlSetting N Gp Gk0 Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f')
    (hG' : IsLevel Gp (k + 1)) (hG : IsLevel Hm k) (htop : Gk.Ω (k + 1) = ∅) :
    FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f where
  hS2 := hF0.hS2
  SM := hF0.SM
  hM2 := hF0.hM2
  hPm := precedes_of_isLevel_of_top_empty hG htop
  hPmp := hF0.hPmp
  depm := fun x hx y hy => by
    refine hB.hN x (hB.dsX₀ x hx) (by rw [hG'.Ω_one]; exact Finset.mem_univ x) y ?_
    rw [hG'.spacing_eq]
    exact torusDist_lt_of_mem_composeDep (by have := hB.HBp.hd; omega) hB.hr₀ hy
  num := hF0.num

end Settings

section Expansion

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- **One inherited energy label expands over the decoupled domains, with a localized ambient
set.**  `classOldDec_expansion` with the ambient set `Gk` and the fluctuation set `Hm` at their own
separation indices `ϱ₁`, `ϱm` (a local set `𝔹_k(X)` has an index below the class index; SF3TYPE
T1).  Conclusion: `flComp hB hF Eτ = ∑_{Y ∈ polymerDomains(X₁)} Ev Y` with raw-`Y` locality, the
bound `β⁻¹ E₀ exp(-κ₀ d_j(X) - 2 κ_dec d(Y))` and analyticity. -/
theorem classOldDecLocal_expansion_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    {β : ℝ} (hβ : 0 < β) (hE₀ : 0 ≤ P.E₀) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} (hXp : IsPolyDom C.m₀ j X) (hy : y ∈ X)
    (hB : BgSetting N Gp Gk (C.Tm.gs j X) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp C.m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp C.m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne C.m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L C.m₀ m₁ j) E₀ = treeLenCovOne C.m₀ j X)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom j (C.Tm.gs j X) r.1 r.2) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        flComp hB hF (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
          (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp C.m₀ (X1 Gp C.m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ (β⁻¹ * P.E₀) *
          Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov Gp C.m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  obtain ⟨hEan, hEbd⟩ := classOldDecEnergy_chart_radius (N := N) C hm hcl hβ hκP hE₀ a₁ ν δ₃ eps δfl hj1
    hjk hXp hy hchart
  exact eterm_expansion_hat_rawY_of_one_le hb₁ hbC hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt
    hκ₀ hκdec hκ h1 hlog (mul_nonneg (inv_nonneg.2 hβ.le) hE₀) hEan hEbd

/-- **One inherited energy label expands over the decoupled domains, with a localized ambient
set.**  `classOldDec_expansion` with the ambient set `Gk` and the fluctuation set `Hm` at their own
separation indices `ϱ₁`, `ϱm` (a local set `𝔹_k(X)` has an index below the class index; SF3TYPE
T1).  Conclusion: `flComp hB hF Eτ = ∑_{Y ∈ polymerDomains(X₁)} Ev Y` with raw-`Y` locality, the
bound `β⁻¹ E₀ exp(-κ₀ d_j(X) - 2 κ_dec d(Y))` and analyticity. -/
theorem classOldDecLocal_expansion {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    {β : ℝ} (hβ : 0 < β) (hE₀ : 0 ≤ P.E₀) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} (hXp : IsPolyDom C.m₀ j X) (hy : y ∈ X)
    (hB : BgSetting N Gp Gk (C.Tm.gs j X) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp C.m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp C.m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne C.m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L C.m₀ m₁ j) E₀ = treeLenCovOne C.m₀ j X)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom j (C.Tm.gs j X) r.1 r.2) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        flComp hB hF (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
          (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp C.m₀ (X1 Gp C.m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ (β⁻¹ * P.E₀) *
          Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov Gp C.m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) :=
  classOldDecLocal_expansion_of_one_le (one_le_scaledC0 d) le_rfl C hm hcl hβ hE₀ hj1 hjk hXp hy hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hκP hchart


open Classical in
/-- **One inherited observable label expands over the decoupled domains, with a localized ambient
set.**  `classOldDecObs_expansion` (`Mτ(r) = ℳ^{(j)}_i(y, X; r.1, r.2, g)`, fixed source `g`) with
the ambient set `Gk` and the fluctuation set `Hm` at their own separation indices.  Bound
`c₉ (L^j)^{-((d-2)/2 + γ - α₁)} exp(-κ₀ d_j(X) - 2 κ_dec d(Y))`. -/
theorem classOldDecObsLocal_expansion_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    (hc₉ : 0 ≤ P.c₉) (g : Fld d L N₁ m₁ (k + 1) N) (hg : Def6.l1 g < 1) {j : ℕ}
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} (i : Fin N) (hXp : IsPolyDom C.m₀ j X) (hy : y ∈ X)
    (hB : BgSetting N Gp Gk (C.Tm.gs j X) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp C.m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp C.m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne C.m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L C.m₀ m₁ j) E₀ = treeLenCovOne C.m₀ j X)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom j (C.Tm.gs j X) r.1 r.2) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        flComp hB hF (fun r => C.Tm.M j y X r.1 r.2 g i)
          (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp C.m₀ (X1 Gp C.m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ (P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁)) *
          Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov Gp C.m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  obtain ⟨hEan, hEbd⟩ := classOldDecObs_chart C hm hcl hκP hc₉ g hg (compWeight L a₁) ν
    b (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) hj1 hjk i hXp hy
    hchart
  exact eterm_expansion_hat_rawY_of_one_le hb₁ hbC hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt
    hκ₀ hκdec hκ h1 hlog
    (mul_nonneg hc₉ (Real.rpow_nonneg (inv_nonneg.2 (pow_nonneg (Nat.cast_nonneg _) _)) _))
    hEan hEbd

/-- **One inherited observable label expands over the decoupled domains, with a localized ambient
set.**  `classOldDecObs_expansion` (`Mτ(r) = ℳ^{(j)}_i(y, X; r.1, r.2, g)`, fixed source `g`) with
the ambient set `Gk` and the fluctuation set `Hm` at their own separation indices.  Bound
`c₉ (L^j)^{-((d-2)/2 + γ - α₁)} exp(-κ₀ d_j(X) - 2 κ_dec d(Y))`. -/
theorem classOldDecObsLocal_expansion {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    (hc₉ : 0 ≤ P.c₉) (g : Fld d L N₁ m₁ (k + 1) N) (hg : Def6.l1 g < 1) {j : ℕ}
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} (i : Fin N) (hXp : IsPolyDom C.m₀ j X) (hy : y ∈ X)
    (hB : BgSetting N Gp Gk (C.Tm.gs j X) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp C.m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp C.m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne C.m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L C.m₀ m₁ j) E₀ = treeLenCovOne C.m₀ j X)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom j (C.Tm.gs j X) r.1 r.2) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        flComp hB hF (fun r => C.Tm.M j y X r.1 r.2 g i)
          (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp C.m₀ (X1 Gp C.m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ (P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁)) *
          Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov Gp C.m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) :=
  classOldDecObsLocal_expansion_of_one_le (one_le_scaledC0 d) le_rfl C hm hcl hc₉ g hg hj1 hjk i hXp hy hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hκP hchart


end Expansion

end Balaban.Fluctuation
