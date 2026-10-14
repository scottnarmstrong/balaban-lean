/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldLocalGk
public import Balaban.SmallField.LocalSuccessorRadius
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The local successor class against the landed step engine

P3 (4.46)-(4.47) (printed pp. 78-79) obtains the analyticity of a new term `ℰ(X, Y; ·)` on
`Ξ^c_{k+1}(𝔹_{k+1}(Y); 1, ε')` by recomputing the term with the local generating set
`𝔹_{k+1}(Y)` in place of `𝔹_{k+1}` and applying Lemma 4.2 on that set.  The landed engine cannot
be run on a local top set:

* `Localization.DGSetting.false_of_le_minSep`: the cover separation `4 d L M₁ ≤ ϱ` of
  `DGSetting` fails for every index `ϱ ≤ 5 L M₁` of `localB` (`4 d ≤ 5` is false);
* `Localization.BgSetting.index_ge`, `Localization.BgSetting.false_of_le_minSep`: `BgSetting`
  forces `ϱ ≥ 4 d L³ M₁ + 1` for the index of its top set (`hr`, `hr₀`), more than `5 L M₁`;
* `not_isLevel_localB`: the top set of the fan, hat and fluctuation theorems is `IsLevel`, and
  `localB j hj X hsep` is not `IsLevel` at `j` unless `X` is the whole torus;
* `not_bgSetting_localB`: no `BgSetting` has the top set `localB (k+1) _ Y hsep`.

The ratios `4 d / 5` and `4 d L² / 5` do not depend on `m₁` and grow with `L`.

The input side does work with a local class: the class of the step and the step itself may have
different separation indices.

* `bgSetting_localB_termGen`: a setting of the step with `𝔹_k = stepG` holds with the term
  generator `𝔹_j(X) = localB j _ X hsep` at the index `R₀(d, L)`;

* `classOldDecLocal_expansion_index`, `classOldDecObsLocal_expansion_index`: W754's expansions of
  one inherited label with the class `C` at its own index `ϱc` (the step at `ϱ`);
* `classOldDecLocal_expansion_localB`: for a class at the low index `R₀(d, L)` whose term
  generator at `(j, X)` is `𝔹_j(X) = localB j _ X hsep` and whose domain is `Ξ^c_j(𝔹_j(X); 1, ε_j)`, the chart hypothesis is the radius test `C₀² ε₂ ≤ ε_j` of a
  whole-level generator; no factor of the restriction route enters;
* `not_chartTest_newest`: that test (the same for a whole-level generator) is false at `j = k` for
  a chart radius `ε ≥ ε_{k+1}` when `2 L^α < C₀⁴` (`d = L = 3`): the composition chain of the landed
  expansion loses `C₀⁴` in radius, where P3 (4.29) loses nothing.
-/

@[expose] public section

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec
  Balaban.LargeField Finset

section Obstruction

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ : ℝ}

/-- **The cover separation of `DGSetting` fails at the index of a local generating set**:
`4 d L M₁ ≤ ϱ ≤ 5 L M₁` is impossible for `d ≥ 3` (`M₁ = L ^ m₁`). -/
theorem Balaban.Localization.DGSetting.false_of_le_minSep
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} (hS : DGSetting G a ν)
    (hsep : ϱ ≤ minSep L (L ^ m₁)) : False := by
  have h1 := hS.cover_sep
  have hd : (3 : ℝ) ≤ d := by exact_mod_cast hS.hd
  have hL : (3 : ℝ) ≤ L := by exact_mod_cast hS.hL
  unfold minSep at hsep
  push_cast at hsep
  have hM : 0 < (L : ℝ) * (L : ℝ) ^ m₁ := by positivity
  nlinarith

/-- **`BgSetting` forces a large index of the top set**: `4 d L³ M₁ + 1 ≤ ϱ` from `hr`
(`r₀ M₁ ≤ ϱ - 1`) and `hr₀` (`4 d L³ ≤ r₀`). -/
theorem Balaban.Localization.BgSetting.index_ge {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁} {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂}
    {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) :
    4 * d * (L : ℝ) ^ 3 * (L : ℝ) ^ m₁ + 1 ≤ ϱ := by
  have h1 := hB.hr
  have h2 := hB.hr₀
  have hM : 0 ≤ (L : ℝ) ^ m₁ := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h2 hM]

/-- **No `BgSetting` has a top set at an index of a local generating set** (`ϱ ≤ 5 L M₁`). -/
theorem Balaban.Localization.BgSetting.false_of_le_minSep
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁} {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂}
    {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hsep : ϱ ≤ minSep L (L ^ m₁)) : False :=
  hB.Sp.false_of_le_minSep hsep

namespace Balaban.Fluctuation

variable {k : ℕ} {ϱ' : ℝ}

/-- **A local generating set is not a whole level**: if some site lies outside `X`, then
`localB j hj X hsep` is not `IsLevel` at `j` (a site of the top layer `j` has its whole cube in
`X`, `mem_localB_Ω_top`). -/
theorem not_isLevel_localB {j : ℕ} {hj : j ≤ k} {X : Set (CTorus d L N₁ m₁ k)}
    {hsep : ϱ' ≤ minSep L (L ^ m₁)} {x : CTorus d L N₁ m₁ k} (hx : x ∉ X) :
    ¬ IsLevel (localB j hj X hsep) j := by
  intro h
  have hl := (GeneratingSet.mem_layer _).1 (h.mem_layer x)
  exact hx ((mem_localB_Ω_top x).1 hl.1 x rfl)

/-- **No `BgSetting` has the top set `𝔹_{k+1}(Y) = localB (k+1) _ Y hsep`**, at any index the
local generating set admits: the landed decoupled expansion cannot recompute a term with the local
generating set of an output label. -/
theorem not_bgSetting_localB {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    {hsep : ϱ' ≤ minSep L (L ^ m₁)}
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
    {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
    (hB : BgSetting N (localB (k + 1) le_rfl Y hsep) Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) :
    False :=
  hB.false_of_le_minSep hsep

end Balaban.Fluctuation

end Obstruction

namespace Balaban.Fluctuation

section Expansion

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱm ϱc : ℝ}
  {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **A local term generator in the setting of the step.**  From a `BgSetting` of the step with
the ambient set `𝔹_k = stepG` and any term generator, the setting holds with the term generator
`𝔹_j(X) = localB j hj X hsep` at the low index `R₀(d, L)`: `BgHyp` at that index, `𝔹_j(X) ≺ 𝔹_k`
(`localB_precedes_levelGS_of_le`) and the collar of `𝔹_j(X)` in `Ω₁(𝔹_k) = 𝕋`. -/
theorem bgSetting_localB_termGen {ϱ₂ : ℝ} {Gj0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
    {j : ℕ} (hB0 : BgSetting N Gp (stepG d L N₁ m₁ k ϱ₁) Gj0 a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hk1 : 1 ≤ k) (hjk : j ≤ k) {hj : j ≤ k + 1} {hsep : bgR0 d L ≤ minSep L (L ^ m₁)} :
    BgSetting N Gp (stepG d L N₁ m₁ k ϱ₁) (localB j hj X hsep) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j
    where
  hS := hB0.hS
  Sp := hB0.Sp
  ha₁ := hB0.ha₁
  HBp := hB0.HBp
  HBk := hB0.HBk
  HBj := { hB0.HBp with hϱ := le_rfl }
  hP := hB0.hP
  hq := localB_precedes_levelGS_of_le hjk (Nat.le_succ k)
  colk := hB0.colk
  colj := fun z _ => by simp [stepG, levelGS, hk1]
  hκ := hB0.hκ
  hM := hB0.hM
  num := hB0.num
  dsX₀ := hB0.dsX₀
  hN := hB0.hN
  hr := hB0.hr
  hr₀ := hB0.hr₀
  dep := hB0.dep
  hj := hB0.hj

open Classical in
/-- **One inherited energy label of a class at its own separation index expands over the
decoupled domains** (`classOldDecLocal_expansion` with the class `C` and its field domain at the
index `ϱc`, the step at `ϱ`).  The term generator `C.Tm.gs j X` enters only through `hB` and
`hchart`; the class index is free. -/
theorem classOldDecLocal_expansion_index {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱc}
    (C : StepClass d L N₁ m₁ k N ϱc) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
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
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  obtain ⟨hEan, hEbd⟩ := classOldDecEnergy_chart (N := N) C hm hcl hβ hκP hE₀ a₁ ν δ₃ eps δfl hj1
    hjk hXp hy hchart
  exact eterm_expansion_hat_rawY hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt
    hκ₀ hκdec hκ h1 hlog (mul_nonneg (inv_nonneg.2 hβ.le) hE₀) hEan hEbd

open Classical in
/-- **One inherited observable label of a class at its own separation index expands over the
decoupled domains** (`classOldDecObsLocal_expansion` with the class at the index `ϱc`). -/
theorem classOldDecObsLocal_expansion_index {P : Consts}
    {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱc}
    (C : StepClass d L N₁ m₁ k N ϱc) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
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
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  obtain ⟨hEan, hEbd⟩ := classOldDecObs_chart C hm hcl hκP hc₉ g hg (compWeight L a₁) ν
    (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) hj1 hjk i hXp hy
    hchart
  exact eterm_expansion_hat_rawY hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt
    hκ₀ hκdec hκ h1 hlog
    (mul_nonneg hc₉ (Real.rpow_nonneg (inv_nonneg.2 (pow_nonneg (Nat.cast_nonneg _) _)) _))
    hEan hEbd

open Classical in
/-- **One inherited energy label of a local class expands, at the radius test of a whole-level
generator.**  The class `C` is at the low index `R₀(d, L)` with domain `Ξ^c_j(𝔹_j(X); 1, ε_j)`
(`xiFieldDom … εseq`), and its term generator at `(j, X)` is `𝔹_j(X) = localB j _ X hsep`.  The
chart hypothesis of `classOldDecLocal_expansion_index` is replaced by
`C₀² (C₀² ε + K₂ δ₃ + K₂ δ_fl) ≤ ε_j` (`xiCRaw_localB_sub_xiFieldDom`), the same test as for the
whole-level generator `levelGS j` (`xiDom_of_xiCData`). -/
theorem classOldDecLocal_expansion_localB {P : Consts} {εseq : ℕ → ℝ}
    (C : StepClass d L N₁ m₁ k N (bgR0 d L)) (hm : P.m₀ = C.m₀)
    (hcl : SFTermClauses P
      (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N (bgR0 d L)) C.Tm)
    {β : ℝ} (hβ : 0 < β) (hE₀ : 0 ≤ P.E₀) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {hsep : bgR0 d L ≤ minSep L (L ^ m₁)}
    (hgs : C.Tm.gs j X = localB j (hjk.trans (Nat.le_succ k)) X hsep)
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
    (hε : scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ≤
      εseq j) :
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
  classOldDecLocal_expansion_index C hm hcl hβ hE₀ hj1 hjk hXp hy hB hF hk hG hG' cc hcψ hMX hdm
    hα hsm hδ₁ hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hκP
    (by rw [hgs]; exact xiCRaw_localB_sub_xiFieldDom hε)

/-- **The radius test of the chart hypothesis fails for the newest old terms.**  The test
`C₀² (C₀² ε + K₂ δ₃ + K₂ δ_fl) ≤ ε_j` of `classOldDecLocal_expansion_localB` (and of the
whole-level route through `xiDom_of_xiCData`) is false at `j = k` for the class sequence when the
chart radius is at least `ε_{k+1}` and `2 L^α < C₀⁴` (`not_chartTest_eps_succ`; e.g. `d = L = 3`). -/
theorem not_chartTest_newest {P : Consts} (hα₀ : 0 < P.α₀)
    (hK : 2 * (L : ℝ) ^ P.alpha d < scaledC0 d ^ 4) {eps δ₃ δfl : ℝ}
    (heps : P.eps d L (k + 1) ≤ eps) (hδ₃ : 0 ≤ δ₃) (hδfl : 0 ≤ δfl) :
    ¬ (scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ≤
      P.eps d L k) := by
  have hK2 : 0 ≤ xiK2 d L N := by
    unfold xiK2
    have := cK2_pos d L N
    positivity
  rw [add_assoc]
  exact not_chartTest_eps_succ P hα₀ hK k heps (by positivity)

end Expansion

end Balaban.Fluctuation
