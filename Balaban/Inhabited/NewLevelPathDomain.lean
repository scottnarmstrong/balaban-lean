/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelSymRoom
public import Balaban.Fluctuation.OldTermBirthDomain
public import Balaban.Fluctuation.GeneralClassPathAnalytic
public import Balaban.SmallField.GsSpecClass
public import Balaban.SmallField.GsSpecStrong

/-!
# The old densities are analytic along the path (the path premise of the class chain)

The class chain asks that the old densities `ℰ^{(j)} = Edens C.m₀ C.Tm j` be analytic at the composed
pairs `Jr.PJ j (Θ, ψ̂)` of the path (`ψ̂ = s ŷ(x)`), the pairs of the old spin composed on the
**whole-level** set `𝔹_j = levelGS j`.  Under ruling R13 the terms of the class are analytic on the
domains of their **local** generating sets `Tm.gs j X`, and the whole-level pair need not lie in
them.  It is not needed: a term depends only on the fields on its polymer `X` (`localE`), so it is
analytic at every pair that agrees on `X` with a pair of its domain (`analyticAt_of_agree_on`).
Such a pair is the old spin composed on the local set `Tm.gs j X` itself: it agrees with the
whole-level pair on `X`, which lies in the top layer `j` of `Tm.gs j X` (`GsSpecStrong`,
`composeField_eq_of_layerIndex`), and it lies in the chart `Ξ^c_j(Tm.gs j X; 1, ε + K₂δ₃ + K₂δ_fl)`
(`pathDatum_xiCData_of_room` at `Gj = Tm.gs j X`), hence in the birth-mass domain of the class under
the (DL-gap) (`xiCRaw_mem_birthXiDom`).

* `analyticAt_of_agree_on`, `composeField_eq_of_layerIndex`;
* `BgSetting.retarget`, `FlSetting.retarget`: the settings of the chain of the old terms at
  `(𝔹_k, Gj)` and `(𝔹_k, 𝔹_k)` (with `X₀ = X₁ = 𝕋`) from the settings of any label;
* `JointRep.analyticAt_Edens_path_of_birth`: the path premise from the local charts.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.Fluctuation

section Agree

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁]

open Classical in
/-- **A function of the fields on `X` is analytic at every pair agreeing on `X` with a pair where it
is analytic**: `f = f ∘ ι` for the affine map `ι` replacing the fields off `X` by those of `p''`. -/
theorem analyticAt_of_agree_on {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) → F}
    {X : Set (CTorus d L N₁ m₁ K)}
    (hloc : ∀ p p' : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ),
      (∀ x ∈ X, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → f p = f p')
    {p p'' : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (hp'' : AnalyticAt ℂ f p'') (hagree : ∀ x ∈ X, p.1 x = p''.1 x ∧ p.2 x = p''.2 x) :
    AnalyticAt ℂ f p := by
  set ι : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) →
      (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) :=
    fun q => (fun x i => if x ∈ X then q.1 x i else p''.1 x i,
      fun x i => if x ∈ X then q.2 x i else p''.2 x i) with hι
  have hfι : f = f ∘ ι := by
    funext q
    refine hloc q (ι q) fun x hx => ⟨?_, ?_⟩ <;> funext i <;> simp [hι, hx]
  have hιp : ι p = p'' := by
    refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
    · by_cases hx : x ∈ X
      · simp [hι, hx, (hagree x hx).1]
      · simp [hι, hx]
    · by_cases hx : x ∈ X
      · simp [hι, hx, (hagree x hx).2]
      · simp [hι, hx]
  have hfst : ∀ x i, AnalyticAt ℂ
      (fun q : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) => q.1 x i) p :=
    fun x i => by
      have h1 : AnalyticAt ℂ
          (fun q : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) => q.1 x) p :=
        analyticAt_pi_iff.1 analyticAt_fst x
      exact analyticAt_pi_iff.1 h1 i
  have hsnd : ∀ x i, AnalyticAt ℂ
      (fun q : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) => q.2 x i) p :=
    fun x i => by
      have h1 : AnalyticAt ℂ
          (fun q : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) => q.2 x) p :=
        analyticAt_pi_iff.1 analyticAt_snd x
      exact analyticAt_pi_iff.1 h1 i
  have hιan : AnalyticAt ℂ ι p := by
    refine AnalyticAt.prod (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
      (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
    · by_cases hx : x ∈ X
      · simp only [hx, ↓reduceIte]
        exact hfst x i
      · simp only [hx, ↓reduceIte]
        exact analyticAt_const
    · by_cases hx : x ∈ X
      · simp only [hx, ↓reduceIte]
        exact hsnd x i
      · simp only [hx, ↓reduceIte]
        exact analyticAt_const
  rw [hfι]
  exact AnalyticAt.comp_of_eq (hιp ▸ hp'') hιan hιp

/-- **The composed field at a site depends on the generating set only through its layer**: for
`x ∈ Ω₁(G) ∩ Ω₁(G'')` with the same layer index, the composed fields on `G` and `G''` agree at `x`
(the blocks do not depend on the generating set). -/
theorem composeField_eq_of_layerIndex {ϱ ϱ'' ϱ' : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {G'' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ''} {G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
    (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ) (Ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω 1) (hx'' : x ∈ G''.Ω 1)
    (hl : G.layerIndex x = G''.layerIndex x) (i : Fin N) :
    composeField G G' a φ' Ψ' x i = composeField G'' G' a φ' Ψ' x i := by
  rw [composeField_of_mem (G := G) (G' := G') a φ' Ψ' hx i,
    composeField_of_mem (G := G'') (G' := G') a φ' Ψ' hx'' i, hl]
  rfl

end Agree

section Retarget

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ ϱ₁' ϱ₂' ϱm : ℝ}
  {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
  {Gk' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁'} {Gj' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂'}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁} {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X₀' X₁f' : Finset (CTorus d L N₁ m₁ K)}
  {j' j : ℕ}

/-- **The background setting at another pair of generating sets**: the constants of a
`BgSetting` of `(Gp, Gk', Gj')` serve every pair `Gj ≺ Gk ≺ Gp` with the standing hypotheses and
the collars, with the whole torus as the sets `X₀`, `X₁` of the dependence. -/
theorem _root_.Balaban.Localization.BgSetting.retarget (hB : BgSetting N Gp Gk' Gj' a₁ ν c BG κ r₀ eps δ₃ X₀' X₁f' j')
    (HBk : BgHyp d L K ϱ₁ (compWeight L a₁) ν) (HBj : BgHyp d L K ϱ₂ (compWeight L a₁) ν)
    (hP : Precedes Gk Gp) (hq : Precedes Gj Gk) (colk : ∀ z ∈ collar Gk, z ∈ Gp.Ω 1)
    (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1) (hj : j ≤ K) :
    BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ Finset.univ Finset.univ j where
  hS := hB.hS
  Sp := hB.Sp
  ha₁ := hB.ha₁
  HBp := hB.HBp
  HBk := HBk
  HBj := HBj
  hP := hP
  hq := hq
  colk := colk
  colj := colj
  hκ := hB.hκ
  hM := hB.hM
  num := hB.num
  dsX₀ := fun x _ => Finset.mem_univ x
  hN := fun _ _ _ y _ => Finset.mem_univ y
  hr := hB.hr
  hr₀ := hB.hr₀
  dep := fun _ _ y _ => Finset.mem_univ y
  hj := hj

/-- **The fluctuation setting at another ambient set**: the constants of a `FlSetting` of
`(Gp, Gk', Hm)` serve every `Gk ≺ Hm`, with the whole torus as the set `X₁` of the dependence. -/
theorem _root_.Balaban.Localization.FlSetting.retarget (hF : FlSetting N Gp Gk' Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f')
    (hPm : Precedes Gk Hm) :
    FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl Finset.univ where
  hS2 := hF.hS2
  SM := hF.SM
  hM2 := hF.hM2
  hPm := hPm
  hPmp := hF.hPmp
  depm := fun _ _ y _ => Finset.mem_univ y
  num := hF.num

end Retarget

section Path

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The settings of the chain of the old terms at `(𝔹_k, Tm.gs j X)` and `(𝔹_k, 𝔹_k)`** from the
settings of any label of the step, for a class with the strong specification of its generating
sets: `Tm.gs j X ≺ 𝔹_k ≺ 𝔹_{k+1}`, and the collars of `𝔹_k`, `Tm.gs j X` lie in
`Ω₁(𝔹_{k+1}) = Ω₁(𝔹_k) = 𝕋`. -/
theorem settings_stepG_gs (S : StepSetting d L N₁ m₁ k N ϱ) {P : Consts}
    {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
    (hcl : SFTermClausesStrong P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ (k + 1))} (hX : IsPolyDom P.m₀ j X) {ϱ₁' ϱ₂' : ℝ}
    {Gk' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁'}
    {Gj' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂'}
    {c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X₀' X₁f' : Finset (CTorus d L N₁ m₁ (k + 1))}
    {j' : ℕ} (hB : BgSetting N S.G' Gk' Gj' S.a₁ S.ν c BG κ r₀ eps δ₃ X₀' X₁f' j')
    (hF : FlSetting N S.G' Gk' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl
      X₁f') :
    BgSetting N S.G' (stepG d L N₁ m₁ k ϱ) (Tm.gs j X) S.a₁ S.ν c BG κ r₀ eps δ₃ Finset.univ
        Finset.univ j ∧
      FlSetting N S.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂
        BG₂ δ₁ δfl Finset.univ := by
  have hS := hcl.gsStrong j hj1 (hjk.trans (Nat.le_succ k)) X hX
  refine ⟨hB.retarget hB.HBp hB.HBp (S.hG.precedes S.hG' (le_refl (k + 1)))
    (precedes_levelGS hS hjk (Nat.le_succ k)) (fun z _ => ?_) (fun z _ => ?_)
    (hjk.trans (Nat.le_succ k)), hF.retarget (precedes_refl _)⟩
  · rw [S.hG'.Ω_one]; exact Finset.mem_univ _
  · simp [stepG, levelGS, S.hk1]

open Classical in
/-- **The old densities are analytic along the path, from the local charts of the class**
(ruling R13; the premise `hE` of the class chain).  For a class on the birth-mass domain with the
strong specification of its generating sets, the settings of the chain of the old terms at
`(𝔹_k, Tm.gs j X)` for every term `(j, y, X)`, the fluctuation radius `δ₁` above the lifted hat
variables (`hδ₁`, radius `pp`), the step's weights equal to the class's (`hA`), the birth masses
`μ_j = ν (1 + t_j)`, `|t_j| ≤ τ`, the (DL-gap) at `E = ε + K₂δ₃ + K₂δ_fl` and the smallness of
`ε_j`: the density `ℰ^{(j)}` is analytic at the composed pair `Jr.PJ j (Θ, s ŷ(x))` of every datum
`Θ` of the chart, `s ∈ [0, 1]`, `‖x‖ ≤ pp`, `1 ≤ j ≤ k`. -/
theorem _root_.Balaban.Fluctuation.StepSetting.JointRep.analyticAt_Edens_path_of_birth [NeZero N] {S : StepSetting d L N₁ m₁ k N ϱ}
    {eps pp : ℝ} (Jr : S.JointRep eps pp) (C : StepClass d L N₁ m₁ k N ϱ) {P : Consts}
    (Rg : Regime L) (a : ℕ → ℝ) (hcl : SFTermClausesStrong P (birthXiDom P Rg a N₁) C.Tm)
    (hm : P.m₀ = C.m₀) {c BG κ Kc Cx c₂ BG₂ δ₁ δc δ₃ δfl r₀ : ℝ}
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁) (hβ : 0 < S.β)
    (hset : ∀ j, 1 ≤ j → j ≤ k → ∀ y X, Aligned (L ^ j) y → IsPolyDom C.m₀ j X → y ∈ X →
      BgSetting N S.G' (stepG d L N₁ m₁ k ϱ) (C.Tm.gs j X) S.a₁ S.ν c BG κ r₀ eps δ₃ Finset.univ
          Finset.univ j ∧
        FlSetting N S.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx
          c₂ BG₂ δ₁ δfl Finset.univ)
    (hA : aIdeal L (k + 1) (a (k + 1)) = compWeight L S.a₁)
    (H' : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν → ∀ j, 1 ≤ j → j ≤ k →
      BgHyp d L (k + 1) ϱ (compWeight L S.a₁) (physMass L j (Rg.ν j)))
    {τ r : ℝ} (hμ : ∀ j, 1 ≤ j → j ≤ k → ∃ t : ℝ, physMass L j (Rg.ν j) = S.ν * (1 + t) ∧ |t| ≤ τ)
    (hτr : τ < r) (hr : r ≤ 1 / 16) (he : 0 < eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
    (hDL : ∀ j, 1 ≤ j → j ≤ k → (2 * (eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) +
        2 * ((N : ℝ) + 1) * (cK2 d L N * (eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ^ 2)) *
      (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τ) ≤ P.eps d L j)
    (hsmε : ∀ j, 1 ≤ j → j ≤ k → (4 * d + 6) * ((2 * d + 1) * P.eps d L j) ≤ 1)
    (hc1ε : ∀ j, 1 ≤ j → j ≤ k → 4 * (xiC1 d * P.eps d L j) ≤ bgC1 d L N)
    (hKε : ∀ j, 1 ≤ j → j ≤ k → bgK1 d L N * (xiC1 d * P.eps d L j) + 3 * r ≤ deltaStar d L N)
    (hζε : ∀ j, 1 ≤ j → j ≤ k → 8 * P.eps d L j * r ≤ deltaStar d L N) :
    ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ pp → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)) := by
  intro D hD s hs x hx j hj
  obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
  have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
  have hψ₀ : ‖(s : ℂ) • yhat x‖ ≤ pp :=
    calc ‖(s : ℂ) • yhat x‖ ≤ |s| * ‖x‖ := StepSetting.JointRep.norm_smul_yhat_le (S := S) s x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
      _ ≤ pp := by rw [one_mul]; exact hx
  have hψh : ∀ p, ‖((s : ℂ) • yhat x) p‖ ≤ pp := fun p => (norm_le_pi_norm _ p).trans hψ₀
  have hPJ := Jr.PJ_dataUCH (S.withDatumH D) hD hψh j
  simp only at hPJ
  have hPJ' : Jr.PJ j (rawOf D, (s : ℂ) • yhat x) = _ := hPJ
  rw [hPJ']
  unfold Edens
  refine Finset.analyticAt_fun_sum _ fun y hy => ?_
  have hyA : Aligned (L ^ j) y := (Finset.mem_filter.1 hy).2
  unfold Eloc
  refine analyticAt_finsum_polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) C.m₀ j y
    (fun X (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) => C.Tm.E j y X p.1 p.2)
    fun X hX hyX => ?_
  obtain ⟨hBX, hF⟩ := hset j hj1 hjk y X hyA hX hyX
  have hX' : IsPolyDom P.m₀ j X := hm ▸ hX
  have hS := hcl.gsStrong j hj1 (hjk.trans (Nat.le_succ k)) X hX'
  have hXi := StepSym.pathDatum_xiCData_of_room Jr (flCore_of hBX hF) hMX hdm hα hsm hδ₁ hβ hBX
    hF hD hψh
  obtain ⟨t, ht, htb⟩ := hμ j hj1 hjk
  have hmem := (xiCRaw_mem_birthXiDom P Rg a hA hBX.HBp (H' hBX.HBp j hj1 hjk)
    (hS.noAbove (j + 1) (Nat.lt_succ_self j)) le_rfl he ht htb hτr hr
    (by rw [one_pow, one_mul]; exact hDL j hj1 hjk) (hsmε j hj1 hjk) (hc1ε j hj1 hjk)
    (hKε j hj1 hjk) (hζε j hj1 hjk) _ ⟨_, hXi, rfl⟩).1
  have hp'' := hcl.analyticE j hj1 (hjk.trans (Nat.le_succ k)) y X hX' hyX _ hmem
  refine analyticAt_of_agree_on (X := X)
    (fun p p' h => hcl.localE j y X p.1 p'.1 p.2 p'.2 h) hp'' fun z hz => ?_
  have hz1 : z ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j
      (hjk.trans (Nat.le_succ k))).Ω 1 := by simp [levelGS, hj1]
  have hz2 : z ∈ (C.Tm.gs j X).Ω 1 := Finset.mem_coe.1 (hS.subset hz)
  simp only [composedPairAtC, hjk, ↓reduceDIte, composedDataAtC, composeData, rawOf]
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · exact composeField_eq_of_layerIndex _ _ _ hz1 hz2 (hS.layerEq z hz).symm i
  · simp only [hz1, hz2, ↓reduceIte]
    rfl

end Path

end Balaban.Inhabited
