/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RopConcrete
import Mathlib
import Balaban.LargeField.R.PsiZeroAnalytic

/-!
# Measurability of the unconditional solution `ψ⁰_k` (Lemma III.3.3) and of the effective action on the tube

Conventions: the landed objects are used unchanged (massless reference of P7: `effAction` has `ν = 0`).

* `continuousOn_effAction`: the effective action is continuous on the tube `Ψ̃(𝔹; τ)`, `τ ≤ min (c₀, c₁)` (the Def-5
  background is analytic in the data, `contDiffOn_effAction`).
* `measurable_effTube`: the effective action, cut off to the open tube, is Borel measurable.
* `measurable_psiZeroFun`: the solution `ψ⁰_k` of (2.34), as a function of the outside field `ψ_k ∈ Ψ̃(X ∖ Z₀; δ)`,
  is Borel measurable.  Route: the graph `{(ψ_k, ψ) : ψ solves (2.34) for ψ_k}` is a Borel set (the quantifier over
  the competitors `ψ'` reduces to a countable dense family of competitors by continuity of `effAction` on the tube),
  it is the graph of a function (`psiZero_spec`), and a Borel graph over a Borel set of a Polish space is a Borel
  function (Lusin-Souslin, `measurable_piecewise_of_graph`).  This route does not need the constants of
  `psiZero_analytic_of_input` to be identified with `psiZeroK`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Balaban Balaban.Multiscale Balaban.Background MeasureTheory

namespace Balaban.LargeField

section Graph

open Classical in
/-- **A function with Borel graph is Borel** (Lusin-Souslin): if `Γ ⊆ α × β` is a Borel set whose section over
every point `a` of the Borel set `T` is the singleton `{g a}`, and whose projection lies in `T`, then `g` (extended by
a constant off `T`) is Borel measurable. -/
theorem measurable_piecewise_of_graph {α β : Type*} [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α]
    [BorelSpace α] [TopologicalSpace β] [PolishSpace β] [MeasurableSpace β] [BorelSpace β]
    {T : Set α} {Γ : Set (α × β)} (hΓ : MeasurableSet Γ) (hT : MeasurableSet T) (g : α → β) (b₀ : β)
    (hg : ∀ a ∈ T, ∀ b, (a, b) ∈ Γ ↔ b = g a) (hΓT : ∀ p ∈ Γ, p.1 ∈ T) :
    Measurable (fun a => if a ∈ T then g a else b₀) := by
  refine measurable_of_isOpen fun U hU => ?_
  have hs : MeasurableSet (Γ ∩ (Prod.snd ⁻¹' U)) := hΓ.inter (measurable_snd hU.measurableSet)
  have himg : MeasurableSet (Prod.fst '' (Γ ∩ (Prod.snd ⁻¹' U))) := by
    refine hs.image_of_continuousOn_injOn continuous_fst.continuousOn ?_
    rintro ⟨a, b⟩ ⟨h1, -⟩ ⟨a', b'⟩ ⟨h2, -⟩ (h : a = a')
    subst h
    have e1 := (hg a (hΓT _ h1) b).1 h1
    have e2 := (hg a (hΓT _ h2) b').1 h2
    simp [e1, e2]
  have heq : (fun a => if a ∈ T then g a else b₀) ⁻¹' U =
      Prod.fst '' (Γ ∩ (Prod.snd ⁻¹' U)) ∪ (Tᶜ ∩ {_a | b₀ ∈ U}) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_ofPred_eq]
    by_cases ha : a ∈ T
    · simp only [ha, ite_true, not_true, false_and, or_false]
      constructor
      · intro h
        exact ⟨(a, g a), ⟨(hg a ha _).2 rfl, h⟩, rfl⟩
      · rintro ⟨⟨a', b⟩, ⟨h1, h2⟩, rfl⟩
        have := (hg a' (hΓT _ h1) b).1 h1
        simpa [this] using h2
    · simp only [ha, ite_false, not_false_eq_true, true_and]
      constructor
      · intro h; exact Or.inr h
      · rintro (⟨⟨a', b⟩, ⟨h1, -⟩, rfl⟩ | h)
        · exact absurd (hΓT _ h1) ha
        · exact h
  rw [heq]
  exact himg.union (hT.compl.inter (MeasurableSet.const _))

end Graph

section Eff

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) [NeZero N]

theorem isOpen_tubeOn (X : Set (Torus d (N₀ * L ^ (k - k)))) (κ : ℝ) :
    IsOpen {ψ : BlockField d L N₀ k N | TubeOn G X κ ψ} :=
  isOpen_iff_mem_nhds.2 fun _ hψ => eventually_tubeOn G hψ

/-- **T1.  The effective action is continuous on the tube**: on `Ψ̃(𝔹; τ)`, `τ ≤ min (c₀, c₁)` (Theorem 5.2 (2): the
Def-5 background is analytic in the data, and the action is a polynomial in the fields). -/
theorem continuousOn_effAction (H : BgHyp d L k ϱ a 0) {τ : ℝ} (hτ : 0 < τ) (hτ0 : τ ≤ bgC0 d L N)
    (hτ1 : τ ≤ bgC1 d L N) :
    ContinuousOn (effAction G a) {ψ : BlockField d L N₀ k N | TubeOn G Set.univ τ ψ} :=
  (contDiffOn_effAction (n := 0) G H hτ hτ0 hτ1 (U := {ψ | TubeOn G Set.univ τ ψ}) (fun _ h => h)).continuousOn

open Classical in
/-- The effective action cut off to the tube `Ψ̃(𝔹; τ)` (`0` outside). -/
noncomputable def effTube (τ : ℝ) (ψ : BlockField d L N₀ k N) : ℝ :=
  if TubeOn G Set.univ τ ψ then effAction G a ψ else 0

theorem effTube_eq {τ : ℝ} {ψ : BlockField d L N₀ k N} (h : TubeOn G Set.univ τ ψ) :
    effTube G a τ ψ = effAction G a ψ := by
  simp [effTube, h]

theorem measurable_effTube (H : BgHyp d L k ϱ a 0) {τ : ℝ} (hτ : 0 < τ) (hτ0 : τ ≤ bgC0 d L N)
    (hτ1 : τ ≤ bgC1 d L N) : Measurable (effTube G a τ : BlockField d L N₀ k N → ℝ) := by
  classical
  have h := ContinuousOn.measurable_piecewise (s := {ψ : BlockField d L N₀ k N | TubeOn G Set.univ τ ψ})
    (f := effAction G a) (g := fun _ => (0 : ℝ)) (continuousOn_effAction G a H hτ hτ0 hτ1)
    continuous_const.continuousOn (measurableSet_tubeOn N G _ _)
  convert h using 1
  funext ψ
  simp [effTube, Set.piecewise]

end Eff

section Psi

variable (N : ℕ) {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)
  [NeZero N]

variable {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)

open Classical in
/-- **`ψ⁰_k` as a total function of the outside field** `ψ_k` (`0` off the tube `Ψ̃(X ∖ Z₀; δ)`). -/
noncomputable def psiZeroFun {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)
    (ψk : BlockField d L N₀ k N) : BlockField d L N₀ k N :=
  if h : TubeOn G (X \ box b0 w) δ ψk then
    psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc h
  else 0

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **T2/T3 core.  `ψ⁰_k` is a Borel function of the outside field** `ψ_k ∈ Ψ̃(X ∖ Z₀; δ)` (Lemma III.3.3), when the
tube `Ψ̃(X; K₆ δ)` of the solution lies in the domain `κ ≤ min (c₀, c₁)` of the Def-5 background (this follows from the
parameter condition `K₆ δ + 5 ρ ≤ etaDen` of `denominator_eq`). -/
theorem measurable_psiZeroFun {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)
    (hK0 : psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ ≤ bgC0 d L N)
    (hK1 : psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ ≤ bgC1 d L N) :
    Measurable (psiZeroFun N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc) := by
  classical
  set Zb := boxFinset (L := L) (N₀ := N₀) (k := k) b0 w with hZb
  set κ := psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ with hκdef
  have hκ : 0 < κ := mul_pos (psiZeroK_pos N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) hδ
  set E := BlockField d L N₀ k N with hE
  have hEffm : Measurable (effTube G a κ : E → ℝ) := measurable_effTube G a H hκ hK0 hK1
  have hcont := continuousOn_effAction G a H hκ hK0 hK1
  have hXU : ∀ ψ : E, TubeOn G X κ ψ → TubeOn G Set.univ κ ψ := fun ψ h => tubeOn_univ_of_data G hdata h
  have hmergeC : ∀ u : SuppSpace Zb N, Continuous fun ψk : E => mergeField Zb ψk u := fun u =>
    (continuous_mergeField (N := N) Zb).comp (Continuous.prodMk continuous_const continuous_id)
  have hmergeM : ∀ u : SuppSpace Zb N, Measurable fun p : E × E => mergeField Zb p.1 u := fun u =>
    (hmergeC u).measurable.comp measurable_fst
  obtain ⟨Dn, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (SuppSpace Zb N)
  let Γ : Set (E × E) := {p | TubeOn G (X \ box b0 w) δ p.1 ∧ PsiZeroSol G a b0 w X κ p.1 p.2}
  let Γ' : Set (E × E) :=
    ({p | TubeOn G (X \ box b0 w) δ p.1} ∩ {p | TubeOn G X κ p.2}) ∩
      ({p | ∀ z, z ∉ box b0 w → p.2 z = p.1 z} ∩
        ⋂ u ∈ Dn, {p | TubeOn G X κ (mergeField Zb p.1 u) → effTube G a κ p.2 ≤ effTube G a κ (mergeField Zb p.1 u)})
  have hΓ'm : MeasurableSet Γ' := by
    refine ((measurableSet_tubeOn N G _ _).preimage measurable_fst |>.inter
      ((measurableSet_tubeOn N G _ _).preimage measurable_snd)).inter ?_
    refine MeasurableSet.inter ?_ (MeasurableSet.biInter hDc fun u _ => ?_)
    · have : {p : E × E | ∀ z, z ∉ box b0 w → p.2 z = p.1 z} =
          ⋂ z, {p : E × E | z ∉ box b0 w → p.2 z = p.1 z} := by ext; simp
      rw [this]
      refine MeasurableSet.iInter fun z => measurableSet_imp _ fun _ => ?_
      exact measurableSet_eq_fun ((measurable_pi_apply z).comp measurable_snd)
        ((measurable_pi_apply z).comp measurable_fst)
    · have h1 : MeasurableSet {p : E × E | TubeOn G X κ (mergeField Zb p.1 u)} :=
        (measurableSet_tubeOn N G _ _).preimage (hmergeM u)
      have h2 : MeasurableSet {p : E × E | effTube G a κ p.2 ≤ effTube G a κ (mergeField Zb p.1 u)} :=
        measurableSet_le (hEffm.comp measurable_snd) (hEffm.comp (hmergeM u))
      have : {p : E × E | TubeOn G X κ (mergeField Zb p.1 u) →
          effTube G a κ p.2 ≤ effTube G a κ (mergeField Zb p.1 u)} =
          {p : E × E | TubeOn G X κ (mergeField Zb p.1 u)}ᶜ ∪
            {p : E × E | effTube G a κ p.2 ≤ effTube G a κ (mergeField Zb p.1 u)} := by
        ext p; simp [imp_iff_not_or]
      rw [this]
      exact h1.compl.union h2
  have hΓeq : Γ = Γ' := by
    ext p
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨⟨h1, h2⟩, h3, ?_⟩
      simp only [Set.mem_iInter]
      intro u _ htu
      have hag : ∀ z, z ∉ box b0 w → mergeField Zb p.1 u z = p.1 z := fun z hz =>
        mergeField_of_not_mem (fun h => hz (mem_boxFinset.1 h))
      have := h4 _ htu hag
      rwa [effTube_eq G a (hXU _ h2), effTube_eq G a (hXU _ htu)]
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨h1, h2, h3, fun ψ' hψ' hag => ?_⟩
      simp only [Set.mem_iInter] at h4
      set u' := restrictSupp Zb ψ' with hu'
      have hmerge : mergeField Zb p.1 u' = ψ' :=
        mergeField_restrict (fun z hz => hag z (fun h => hz (mem_boxFinset.2 h)))
      have hO : IsOpen {u : SuppSpace Zb N | TubeOn G X κ (mergeField Zb p.1 u)} :=
        (isOpen_tubeOn G X κ).preimage (contDiff_mergeField (n := 0) (Zf := Zb) p.1).continuous
      have hg : ContinuousOn (fun u : SuppSpace Zb N => effAction G a (mergeField Zb p.1 u))
          {u | TubeOn G X κ (mergeField Zb p.1 u)} :=
        hcont.comp (contDiff_mergeField (n := 0) (Zf := Zb) p.1).continuous.continuousOn fun u hu => hXU _ hu
      by_contra hlt
      push Not at hlt
      have hV := hg.isOpen_inter_preimage hO (isOpen_Iio (a := effAction G a p.2))
      have hu'V : u' ∈ {u : SuppSpace Zb N | TubeOn G X κ (mergeField Zb p.1 u)} ∩
          (fun u : SuppSpace Zb N => effAction G a (mergeField Zb p.1 u)) ⁻¹' Set.Iio (effAction G a p.2) := by
        refine ⟨?_, ?_⟩
        · show TubeOn G X κ (mergeField Zb p.1 u')
          rw [hmerge]; exact hψ'
        · show effAction G a (mergeField Zb p.1 u') < effAction G a p.2
          rw [hmerge]; exact hlt
      obtain ⟨u, huD, huV⟩ := hDd.exists_mem_open hV ⟨u', hu'V⟩
      have hle := h4 u huD huV.1
      rw [effTube_eq G a (hXU _ h2), effTube_eq G a (hXU _ huV.1)] at hle
      exact absurd huV.2 (not_lt.2 hle)
  have hΓm : MeasurableSet Γ := hΓeq ▸ hΓ'm
  have hfun : psiZeroFun N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc =
      fun ψk => if ψk ∈ {ψ : E | TubeOn G (X \ box b0 w) δ ψ} then
        psiZeroFun N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc ψk else 0 := by
    funext ψk
    by_cases h : TubeOn G (X \ box b0 w) δ ψk
    · simp [h]
    · simp [h, psiZeroFun]
  rw [hfun]
  refine measurable_piecewise_of_graph (T := {ψ : E | TubeOn G (X \ box b0 w) δ ψ}) hΓm
    (measurableSet_tubeOn N G _ _) _ 0 (fun ψk hψk b => ?_) (fun p hp => hp.1)
  have hψ : TubeOn G (X \ box b0 w) δ ψk := hψk
  obtain ⟨hsol, huniq⟩ := psiZero_spec N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψ
  have hz : psiZeroFun N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc ψk =
      psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψ := by
    simp [psiZeroFun, hψ]
  rw [hz]
  constructor
  · rintro ⟨-, hb⟩; exact huniq b hb
  · rintro rfl; exact ⟨hψ, hsol⟩

end Psi

end Balaban.LargeField
