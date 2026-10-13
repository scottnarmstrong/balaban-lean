/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusE1Coef
public import Balaban.Inhabited.ObsCoeffAnalytic

/-!
# The coefficient of the observable on two tori: transport along a map of blocks

The coefficient of the observable of one step (Theorem 3.1 (b)) is
`obsCoeffParam μ Aact y₁ G₁ h yᵣ Gᵣ θ T = kernelMarkSum (h θ) E T + gsumCoeff μ Lab (Aact θ · 1) yᵣ
(Gᵣ θ) T`, the resummed products `∑_i ∑_{T₁ ∪ S = T} h(i, T₁) E(i, S)` of the kernel with the
first-order terms `E(i, S) = ∫₀¹ G*(Y₁ᵢ, S)(s) ds` (`markIntTerm`), plus the coefficient of the
remainder marks.  This file carries it along a map `σ` of blocks injective on `T`, in the pattern of
`gsumCoeff_transport` (`TwoTorusE1Coef`).

## Main statements

* `subset_of_image_subset_image_of_injOn`, `sum_powerset_image_of_injOn`: images of subsets under a
  map injective on a finite set.
* `Gst_zero_mark`, `markIntTerm_eq_zero_of_not_subset`, `gsumCoeff_eq_subtype`: the local term of a
  zero mark vanishes, a first-order term vanishes unless the blocks of its label lie in `S`, and the
  marks that vanish may be removed from the coefficient.
* `kernelMarkSum_transport`: the resummed products along `σ`, given corresponding kernels and terms.
* `markIntTerm_transport`: the first-order terms along `σ` (from `Gst_transport`).
* `obsCoeffParam_transport`: the coefficient of the observable along `σ`, given the correspondences
  of the active labels and their activities, of the first-order labels, marks and kernel, and of the
  non-zero remainder marks.
* `obsCoeffParam_blockSplit_twoTorus`: the same for the block measures of the two steps, the
  blocks of the box (`cubeMap`) and agreement of the block variables at corresponding unit points
  of the box.

The correspondence of the first-order labels is a hypothesis.  For the labels of the landed
coefficient (`obsY1 = Sum.inr (obsCubeLab m₀ (obsMarkCube S m₀ i))`) it is not provable:
`obsCubeLab` is a `Classical.choose` among the one-cube labels containing the cube, and the choices
on two tori are unrelated.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory

/-! ### Images of subsets -/

section ImageSubset

variable {α β : Type*} [DecidableEq β] {σ : α → β} {S : Finset α}

/-- Under a map injective on `S`, inclusion of the images of subsets of `S` reflects inclusion. -/
theorem subset_of_image_subset_image_of_injOn (hσ : Set.InjOn σ (S : Set α)) {U V : Finset α}
    (hU : U ⊆ S) (hV : V ⊆ S) (h : U.image σ ⊆ V.image σ) : U ⊆ V := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 (h (Finset.mem_image_of_mem σ hx))
  rw [hσ (hV hy) (hU hx) hyx] at hy
  exact hy

/-- **Sums over the subsets of the image.**  For a map injective on `S`, the subsets of `σ '' S` are
the images of the subsets of `S`, each exactly once. -/
theorem sum_powerset_image_of_injOn {M : Type*} [AddCommMonoid M]
    (hσ : Set.InjOn σ (S : Set α)) (f : Finset β → M) :
    ∑ T' ∈ (S.image σ).powerset, f T' = ∑ T ∈ S.powerset, f (T.image σ) := by
  symm
  refine Finset.sum_nbij' (fun T => T.image σ) (fun T' => S.filter fun b => σ b ∈ T')
    (fun T hT => ?_) (fun T' hT' => ?_) (fun T hT => ?_) (fun T' hT' => ?_) (fun T _ => rfl)
  · exact Finset.mem_powerset.2 (Finset.image_subset_image (Finset.mem_powerset.1 hT))
  · exact Finset.mem_powerset.2 (Finset.filter_subset _ _)
  · have hTS := Finset.mem_powerset.1 hT
    ext x
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hxS, hx⟩
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 hx
      rw [hσ (hTS hy) hxS hyx] at hy
      exact hy
    · intro hx
      exact ⟨hTS hx, Finset.mem_image_of_mem σ hx⟩
  · have hTS := Finset.mem_powerset.1 hT'
    ext y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Finset.mem_filter.1 hx).2
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (hTS hy)
      exact ⟨x, Finset.mem_filter.2 ⟨hx, hy⟩, rfl⟩

end ImageSubset

/-! ### Vanishing terms -/

section Vanish

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
  {Lb : Type*} [Fintype Lb]

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

/-- **The local term of a zero mark vanishes**: `G*(S₀, S) = 0` for the mark `0` (the local term
does not depend on the mark parameter). -/
theorem Gst_zero_mark {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (Lab : CubeLabels m₀ j Ω Lb)
    (H : Lb → (∀ b, Ωb b) → ℂ) (S₀ S : Finset 𝔅) :
    Gst μ Lab H S₀ (fun _ => 0) S = 0 := by
  unfold Gst
  have hconst : Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
      (marksK μ Subtype.val (presum Lab H) (gMark S₀ fun _ => 0)) S =
      fun _ => Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
        (marksK μ Subtype.val (presum Lab H) (gMark S₀ fun _ => 0)) S 0 := by
    funext l
    unfold Ff
    refine PY_congr (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val S
      (fun x _ => ?_)
    unfold marksK mayerK mayerAct polyAct
    refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
    refine Finset.sum_congr rfl (fun C _ => Finset.prod_congr rfl (fun t _ => ?_))
    simp [Hlam, gMark]
  rw [hconst]
  simp [D1]

/-- **A first-order term vanishes unless the blocks of its label lie in `S`.** -/
theorem markIntTerm_eq_zero_of_not_subset {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] {Lab : CubeLabels m₀ j Ω Lb}
    {εH κH κ0 Kc : ℝ} (A : ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb)
    (G : (∀ b, Ωb b) → ℂ) {S : Finset 𝔅} (h : ¬ blocksOf m₀ j Ω (Lab.ysite y0) ⊆ S) :
    markIntTerm μ A y0 G S = 0 := by
  unfold markIntTerm
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ))
    (fun s _ => Gst_eq_zero_of_not_subset _ _ _ _ h)]
  simp

/-- **Vanishing marks may be removed from the coefficient.**  If the marks `G i` with `¬ Q i` vanish
for `s ∈ [0, 1]`, the coefficient `gsumCoeff` is that of the marks indexed by `{i // Q i}`. -/
theorem gsumCoeff_eq_subtype {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (Lab : CubeLabels m₀ j Ω Lb)
    {εH κH κ0 Kc : ℝ} (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) {ι : Type*} [Fintype ι]
    (y0 : ι → Lb) (G : ι → ℂ → (∀ b, Ωb b) → ℂ) (Q : ι → Prop)
    (hG0 : ∀ i, ¬ Q i → ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → G i (s : ℂ) = fun _ => 0)
    (T : Finset 𝔅) :
    gsumCoeff μ Lab A y0 G T =
      gsumCoeff μ Lab A (fun i : {i // Q i} => y0 i) (fun i => G i) T := by
  unfold gsumCoeff
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  unfold Gsum
  rw [← Finset.sum_filter_of_ne (p := Q) (fun i _ hne => by_contra fun hn => hne (by
    beta_reduce; rw [hG0 i hn s hs]; exact Gst_zero_mark _ _ _ _ _))]
  exact Finset.sum_subtype (Finset.univ.filter Q) (fun i => by simp)
    (fun i => Gst μ Lab (A (s : ℂ)).H (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G i (s : ℂ)) T)

end Vanish

/-! ### Transport of the kernel sums, the first-order terms and the coefficient -/

section Transport

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero L] [NeZero N₁] [NeZero N₁'] {m₀ j : ℕ}
  {Ω : Set (CTorus d L N₁ m₁ K)} {Ω' : Set (CTorus d L N₁' m₁ K)}
  {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb']

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω
local notation "𝔅'" => CubeB (L := L) (N₁ := N₁') (m₁ := m₁) (K := K) m₀ j Ω'

omit [NeZero N₁'] in
/-- The resummed products read only the subsets of `W`. -/
theorem kernelMarkSum_eq_sum_powerset {ι : Type*} [Fintype ι] (h E : ι → Finset 𝔅 → ℂ)
    (W : Finset 𝔅) :
    kernelMarkSum h E W = ∑ i, ∑ T ∈ W.powerset, ∑ S ∈ W.powerset,
      if T ∪ S = W then h i T * E i S else 0 := by
  unfold kernelMarkSum
  refine Finset.sum_congr rfl fun i _ => ?_
  symm
  rw [Finset.sum_subset (Finset.subset_univ W.powerset) (fun T _ hT => ?_)]
  · refine Finset.sum_congr rfl fun T _ => ?_
    refine Finset.sum_subset (Finset.subset_univ W.powerset) (fun S _ hS => ?_)
    refine ite_eq_right fun he => hS (Finset.mem_powerset.2 ?_)
    rw [← he]
    exact Finset.subset_union_right
  · refine Finset.sum_eq_zero fun S _ => ?_
    refine ite_eq_right fun he => hT (Finset.mem_powerset.2 ?_)
    rw [← he]
    exact Finset.subset_union_left

/-- **Transport of the resummed products** `∑_i ∑_{T ∪ S = W} h(i, T) E(i, S)`.  Let `σ` be
injective on `W`, let the indices `i` with `P i` correspond bijectively (`κ`) to the indices `i′`
with `P′ i′`, with corresponding kernels and terms on the subsets of `W`, and let the terms of the
other indices vanish on the subsets of `W` (resp. of `σ '' W`).  Then the resummed products at
`σ '' W` and at `W` agree. -/
theorem kernelMarkSum_transport {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (h E : ι → Finset 𝔅 → ℂ) (h' E' : ι' → Finset 𝔅' → ℂ)
    (σ : 𝔅 → 𝔅') (W : Finset 𝔅) (hσ : Set.InjOn σ (W : Set 𝔅))
    (P : ι → Prop) (P' : ι' → Prop)
    (hE0 : ∀ i, ¬ P i → ∀ S ⊆ W, E i S = 0)
    (hE0' : ∀ i', ¬ P' i' → ∀ S' ⊆ W.image σ, E' i' S' = 0)
    (κ : ∀ i, P i → ι') (hκP : ∀ i hi, P' (κ i hi))
    (hκinj : ∀ i₁ hi₁ i₂ hi₂, κ i₁ hi₁ = κ i₂ hi₂ → i₁ = i₂)
    (hκsurj : ∀ i', P' i' → ∃ i hi, κ i hi = i')
    (hh : ∀ i hi, ∀ T ⊆ W, h' (κ i hi) (T.image σ) = h i T)
    (hE : ∀ i hi, ∀ S ⊆ W, E' (κ i hi) (S.image σ) = E i S) :
    kernelMarkSum h' E' (W.image σ) = kernelMarkSum h E W := by
  rw [kernelMarkSum_eq_sum_powerset, kernelMarkSum_eq_sum_powerset]
  -- the inner sums of a corresponding pair of indices
  have hin : ∀ i hi, (∑ T' ∈ (W.image σ).powerset, ∑ S' ∈ (W.image σ).powerset,
      if T' ∪ S' = W.image σ then h' (κ i hi) T' * E' (κ i hi) S' else 0) =
      ∑ T ∈ W.powerset, ∑ S ∈ W.powerset, if T ∪ S = W then h i T * E i S else 0 := by
    intro i hi
    rw [sum_powerset_image_of_injOn hσ]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [sum_powerset_image_of_injOn hσ]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hT' := Finset.mem_powerset.1 hT
    have hS' := Finset.mem_powerset.1 hS
    have hiff : T.image σ ∪ S.image σ = W.image σ ↔ T ∪ S = W := by
      rw [← Finset.image_union]
      exact ⟨fun he => eq_of_image_eq_of_injOn hσ (Finset.union_subset hT' hS')
        (Finset.Subset.refl W) he, fun he => by rw [he]⟩
    by_cases hU : T ∪ S = W
    · rw [ite_eq_left (hiff.2 hU), ite_eq_left hU, hh i hi T hT', hE i hi S hS']
    · rw [ite_eq_right (fun h => hU (hiff.1 h)), ite_eq_right hU]
  -- the indices without a partner contribute zero
  have hz : ∀ i, ¬ P i → (∑ T ∈ W.powerset, ∑ S ∈ W.powerset,
      if T ∪ S = W then h i T * E i S else 0) = 0 := by
    intro i hi
    refine Finset.sum_eq_zero fun T _ => Finset.sum_eq_zero fun S hS => ?_
    rw [hE0 i hi S (Finset.mem_powerset.1 hS), mul_zero, ite_self]
  have hz' : ∀ i', ¬ P' i' → (∑ T' ∈ (W.image σ).powerset, ∑ S' ∈ (W.image σ).powerset,
      if T' ∪ S' = W.image σ then h' i' T' * E' i' S' else 0) = 0 := by
    intro i' hi'
    refine Finset.sum_eq_zero fun T' _ => Finset.sum_eq_zero fun S' hS' => ?_
    rw [hE0' i' hi' S' (Finset.mem_powerset.1 hS'), mul_zero, ite_self]
  rw [← Finset.sum_filter_of_ne (p := P') (fun i' _ hne => by_contra fun hn => hne (hz' i' hn)),
    ← Finset.sum_filter_of_ne (p := P) (fun i _ hne => by_contra fun hn => hne (hz i hn))]
  symm
  refine Finset.sum_bij (fun i hi => κ i (Finset.mem_filter.1 hi).2) (fun i hi => ?_)
    (fun i₁ hi₁ i₂ hi₂ he => hκinj i₁ _ i₂ _ he) (fun i' hi' => ?_)
    (fun i hi => (hin i _).symm)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hκP i _⟩
  · obtain ⟨i, hi, rfl⟩ := hκsurj i' (Finset.mem_filter.1 hi').2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, rfl⟩

/-- **Transport of a first-order term** `E(S) = ∫₀¹ G*(Y₀, S)(s) ds` (`markIntTerm`).  In the
setting of `Gst_transport` for the activities `A(s, 1)`, `s ∈ [0, 1]`, on the set `T` of blocks
(with `σ` injective on `T`): for a label `y₀` with blocks in `T` and a label `y₀′` with the image
blocks, and marks agreeing on related configurations, the first-order terms at `σ '' S` and at
`S ⊆ T` agree.  If the blocks of `y₀` do not lie in `S`, both terms vanish. -/
theorem markIntTerm_transport {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    {Ωb' : 𝔅' → Type*} [∀ b, MeasurableSpace (Ωb' b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (μ' : ∀ b, Measure (Ωb' b)) [∀ b, IsProbabilityMeasure (μ' b)]
    (Lab : CubeLabels m₀ j Ω Lb) (Lab' : CubeLabels m₀ j Ω' Lb')
    {εH κH κ0 Kc εH' κH' κ0' Kc' : ℝ}
    (A : ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (A' : ℂ → ℂ → LabelAct Lab' Ωb' εH' κH' κ0' Kc')
    (σ : 𝔅 → 𝔅') (T : Finset 𝔅) (hσ : Set.InjOn σ (T : Set 𝔅))
    (Rel : (∀ b, Ωb b) → (∀ b, Ωb' b) → Prop)
    (hint : ∀ Z ⊆ T, ∀ (F : (∀ b, Ωb b) → ℂ) (F' : (∀ b, Ωb' b) → ℂ), DepOn Z F →
      (∀ Φ Φ', Rel Φ Φ' → F' Φ' = F Φ) →
        ∫ Φ', F' Φ' ∂(Measure.pi μ') = ∫ Φ, F Φ ∂(Measure.pi μ))
    (P : Lb → Prop) (P' : Lb' → Prop)
    (hA0 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, ¬ P y → ∀ Φ, (A (s : ℂ) 1).H y Φ = 0)
    (hA0' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y', ¬ P' y' → ∀ Φ', (A' (s : ℂ) 1).H y' Φ' = 0)
    (ψ : ∀ y, P y → blocksOf m₀ j Ω (Lab.ysite y) ⊆ T → Lb')
    (hψP : ∀ y hP hy, P' (ψ y hP hy))
    (hψb : ∀ y hP hy, blocksOf m₀ j Ω' (Lab'.ysite (ψ y hP hy)) =
      (blocksOf m₀ j Ω (Lab.ysite y)).image σ)
    (hψinj : ∀ y₁ hP₁ hy₁ y₂ hP₂ hy₂, ψ y₁ hP₁ hy₁ = ψ y₂ hP₂ hy₂ → y₁ = y₂)
    (hψsurj : ∀ y', P' y' → blocksOf m₀ j Ω' (Lab'.ysite y') ⊆ T.image σ →
      ∃ y hP hy, ψ y hP hy = y')
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y hP hy,
      ∀ Φ Φ', Rel Φ Φ' → (A' (s : ℂ) 1).H (ψ y hP hy) Φ' = (A (s : ℂ) 1).H y Φ)
    {y0 : Lb} {y0' : Lb'} (hy0T : blocksOf m₀ j Ω (Lab.ysite y0) ⊆ T)
    (hy0b : blocksOf m₀ j Ω' (Lab'.ysite y0') = (blocksOf m₀ j Ω (Lab.ysite y0)).image σ)
    {G : (∀ b, Ωb b) → ℂ} {G' : (∀ b, Ωb' b) → ℂ}
    (hGdep : DepOn (blocksOf m₀ j Ω (Lab.ysite y0)) G) (hG : ∀ Φ Φ', Rel Φ Φ' → G' Φ' = G Φ)
    {S : Finset 𝔅} (hST : S ⊆ T) :
    markIntTerm μ' A' y0' G' (S.image σ) = markIntTerm μ A y0 G S := by
  by_cases hS0 : blocksOf m₀ j Ω (Lab.ysite y0) ⊆ S
  · unfold markIntTerm
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le zero_le_one] at hs
    show Gst μ' Lab' (A' (s : ℂ) 1).H (blocksOf m₀ j Ω' (Lab'.ysite y0')) G' (S.image σ) =
      Gst μ Lab (A (s : ℂ) 1).H (blocksOf m₀ j Ω (Lab.ysite y0)) G S
    rw [hy0b]
    refine Gst_transport μ μ' Lab Lab' (A (s : ℂ) 1).H (A' (s : ℂ) 1).H (A (s : ℂ) 1).dep σ S
      (hσ.mono (by exact_mod_cast hST)) Rel
      (fun Z hZ F F' hF hFF => hint Z (hZ.trans hST) F F' hF hFF) P P' (hA0 s hs) (hA0' s hs)
      (fun y hP hy => ψ y hP (hy.trans hST)) (fun y hP hy => hψP y hP _)
      (fun y hP hy => hψb y hP _) (fun y₁ hP₁ hy₁ y₂ hP₂ hy₂ he => hψinj y₁ hP₁ _ y₂ hP₂ _ he)
      (fun y' hP' hy' => ?_) (fun y hP hy => hA s hs y hP _) hS0 hGdep hG
    obtain ⟨y, hP, hyT, rfl⟩ := hψsurj y' hP' (hy'.trans (Finset.image_subset_image hST))
    refine ⟨y, hP, subset_of_image_subset_image_of_injOn hσ hyT hST ?_, rfl⟩
    rw [← hψb y hP hyT]
    exact hy'
  · rw [markIntTerm_eq_zero_of_not_subset _ _ _ _ hS0, markIntTerm_eq_zero_of_not_subset]
    rw [hy0b]
    exact fun h => hS0 (subset_of_image_subset_image_of_injOn hσ hy0T hST h)

/-- **Transport of the coefficient of the observable.**  Let `σ` be injective on the set `T` of
blocks and let `Rel` carry the integrals of functions of the blocks of `Z ⊆ T`.  Assume

* (activities) the activities `Aact θ s 1` (`s ∈ [0, 1]`) vanish on the inactive labels, the active
  labels with blocks in `T` correspond bijectively (`ψ`) to those with blocks in `σ '' T`, with
  image blocks and equal activities on related configurations;
* (first-order marks) the first-order labels `y₁ i` with blocks in `T` correspond bijectively (`κ₁`)
  to the labels `y₁′ i′` with blocks in `σ '' T`, with image blocks, the marks `G₁` agree on related
  configurations, and the kernels agree on the subsets of `T`;
* (remainder marks) the remainder marks with `¬ Qr i` vanish (on both sides), and the other labels
  `yᵣ i` with blocks in `T` correspond bijectively (`κᵣ`) to the labels `yᵣ′ i′` with `Qr′ i′` and
  blocks in `σ '' T`, with image blocks and marks agreeing on related configurations.

Then `obsCoeffParam … θ′ (σ '' T) = obsCoeffParam … θ T`.  The kernel part is
`kernelMarkSum_transport` with `markIntTerm_transport`; the remainder part is `gsumCoeff_transport`
for the non-vanishing marks (`gsumCoeff_eq_subtype`). -/
theorem obsCoeffParam_transport {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    {Ωb' : 𝔅' → Type*} [∀ b, MeasurableSpace (Ωb' b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (μ' : ∀ b, Measure (Ωb' b)) [∀ b, IsProbabilityMeasure (μ' b)]
    {Lab : CubeLabels m₀ j Ω Lb} {Lab' : CubeLabels m₀ j Ω' Lb'}
    {εH κH κ0 Kc εH' κH' κ0' Kc' : ℝ} {E E' : Type*}
    (Aact : E → ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (Aact' : E' → ℂ → ℂ → LabelAct Lab' Ωb' εH' κH' κ0' Kc')
    {ι ι' ιr ιr' : Type*} [Fintype ι] [Fintype ι'] [Fintype ιr] [Fintype ιr']
    (y1 : ι → Lb) (y1' : ι' → Lb') (G1 : ι → (∀ b, Ωb b) → ℂ) (G1' : ι' → (∀ b, Ωb' b) → ℂ)
    (hker : E → ι → Finset 𝔅 → ℂ) (hker' : E' → ι' → Finset 𝔅' → ℂ)
    (yr : ιr → Lb) (yr' : ιr' → Lb')
    (Gr : E → ιr → ℂ → (∀ b, Ωb b) → ℂ) (Gr' : E' → ιr' → ℂ → (∀ b, Ωb' b) → ℂ)
    (θ : E) (θ' : E')
    (σ : 𝔅 → 𝔅') (T : Finset 𝔅) (hσ : Set.InjOn σ (T : Set 𝔅))
    (Rel : (∀ b, Ωb b) → (∀ b, Ωb' b) → Prop)
    (hint : ∀ Z ⊆ T, ∀ (F : (∀ b, Ωb b) → ℂ) (F' : (∀ b, Ωb' b) → ℂ), DepOn Z F →
      (∀ Φ Φ', Rel Φ Φ' → F' Φ' = F Φ) →
        ∫ Φ', F' Φ' ∂(Measure.pi μ') = ∫ Φ, F Φ ∂(Measure.pi μ))
    -- the activities
    (P : Lb → Prop) (P' : Lb' → Prop)
    (hA0 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, ¬ P y → ∀ Φ, (Aact θ (s : ℂ) 1).H y Φ = 0)
    (hA0' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y', ¬ P' y' → ∀ Φ',
      (Aact' θ' (s : ℂ) 1).H y' Φ' = 0)
    (ψ : ∀ y, P y → blocksOf m₀ j Ω (Lab.ysite y) ⊆ T → Lb')
    (hψP : ∀ y hP hy, P' (ψ y hP hy))
    (hψb : ∀ y hP hy, blocksOf m₀ j Ω' (Lab'.ysite (ψ y hP hy)) =
      (blocksOf m₀ j Ω (Lab.ysite y)).image σ)
    (hψinj : ∀ y₁ hP₁ hy₁ y₂ hP₂ hy₂, ψ y₁ hP₁ hy₁ = ψ y₂ hP₂ hy₂ → y₁ = y₂)
    (hψsurj : ∀ y', P' y' → blocksOf m₀ j Ω' (Lab'.ysite y') ⊆ T.image σ →
      ∃ y hP hy, ψ y hP hy = y')
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y hP hy,
      ∀ Φ Φ', Rel Φ Φ' → (Aact' θ' (s : ℂ) 1).H (ψ y hP hy) Φ' = (Aact θ (s : ℂ) 1).H y Φ)
    -- the first-order marks and the kernel
    (hG1dep : ∀ i, DepOn (blocksOf m₀ j Ω (Lab.ysite (y1 i))) (G1 i))
    (κ1 : ∀ i, blocksOf m₀ j Ω (Lab.ysite (y1 i)) ⊆ T → ι')
    (hκ1b : ∀ i hi, blocksOf m₀ j Ω' (Lab'.ysite (y1' (κ1 i hi))) =
      (blocksOf m₀ j Ω (Lab.ysite (y1 i))).image σ)
    (hκ1inj : ∀ i₁ hi₁ i₂ hi₂, κ1 i₁ hi₁ = κ1 i₂ hi₂ → i₁ = i₂)
    (hκ1surj : ∀ i', blocksOf m₀ j Ω' (Lab'.ysite (y1' i')) ⊆ T.image σ → ∃ i hi, κ1 i hi = i')
    (hG1 : ∀ i hi, ∀ Φ Φ', Rel Φ Φ' → G1' (κ1 i hi) Φ' = G1 i Φ)
    (hkerT : ∀ i hi, ∀ T₁ ⊆ T, hker' θ' (κ1 i hi) (T₁.image σ) = hker θ i T₁)
    -- the remainder marks
    (Qr : ιr → Prop) (Qr' : ιr' → Prop)
    (hGr0 : ∀ i, ¬ Qr i → ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → Gr θ i (s : ℂ) = fun _ => 0)
    (hGr0' : ∀ i', ¬ Qr' i' → ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → Gr' θ' i' (s : ℂ) = fun _ => 0)
    (hGrdep : ∀ i u, DepOn (blocksOf m₀ j Ω (Lab.ysite (yr i))) (Gr θ i u))
    (κr : ∀ i, Qr i → blocksOf m₀ j Ω (Lab.ysite (yr i)) ⊆ T → ιr')
    (hκrQ : ∀ i hQ hi, Qr' (κr i hQ hi))
    (hκrb : ∀ i hQ hi, blocksOf m₀ j Ω' (Lab'.ysite (yr' (κr i hQ hi))) =
      (blocksOf m₀ j Ω (Lab.ysite (yr i))).image σ)
    (hκrinj : ∀ i₁ hQ₁ hi₁ i₂ hQ₂ hi₂, κr i₁ hQ₁ hi₁ = κr i₂ hQ₂ hi₂ → i₁ = i₂)
    (hκrsurj : ∀ i', Qr' i' → blocksOf m₀ j Ω' (Lab'.ysite (yr' i')) ⊆ T.image σ →
      ∃ i hQ hi, κr i hQ hi = i')
    (hGr : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i hQ hi,
      ∀ Φ Φ', Rel Φ Φ' → Gr' θ' (κr i hQ hi) (s : ℂ) Φ' = Gr θ i (s : ℂ) Φ) :
    obsCoeffParam μ' Aact' y1' G1' hker' yr' Gr' θ' (T.image σ) =
      obsCoeffParam μ Aact y1 G1 hker yr Gr θ T := by
  unfold obsCoeffParam
  congr 1
  · -- the kernel part
    refine kernelMarkSum_transport _ _ _ _ σ T hσ
      (fun i => blocksOf m₀ j Ω (Lab.ysite (y1 i)) ⊆ T)
      (fun i' => blocksOf m₀ j Ω' (Lab'.ysite (y1' i')) ⊆ T.image σ)
      (fun i hi S hS => markIntTerm_eq_zero_of_not_subset _ _ _ _ (fun h => hi (h.trans hS)))
      (fun i' hi' S' hS' => markIntTerm_eq_zero_of_not_subset _ _ _ _ (fun h => hi' (h.trans hS')))
      κ1 (fun i hi => ?_) hκ1inj hκ1surj hkerT (fun i hi S hS => ?_)
    · rw [hκ1b i hi]
      exact Finset.image_subset_image hi
    · exact markIntTerm_transport μ μ' Lab Lab' (Aact θ) (Aact' θ') σ T hσ Rel hint P P' hA0 hA0'
        ψ hψP hψb hψinj hψsurj hA hi (hκ1b i hi) (hG1dep i) (hG1 i hi) hS
  · -- the remainder part
    rw [gsumCoeff_eq_subtype μ Lab _ yr (Gr θ) Qr hGr0 T,
      gsumCoeff_eq_subtype μ' Lab' _ yr' (Gr' θ') Qr' hGr0' (T.image σ)]
    refine gsumCoeff_transport μ μ' Lab Lab' (fun t => Aact θ t 1) (fun t => Aact' θ' t 1)
      (fun i : {i // Qr i} => yr i) (fun i' : {i' // Qr' i'} => yr' i') (fun i => Gr θ i)
      (fun i' => Gr' θ' i') (fun i u => hGrdep i u) σ T hσ Rel hint P P' hA0 hA0' ψ hψP hψb
      hψinj hψsurj hA (fun i hi => ⟨κr i.1 i.2 hi, hκrQ i.1 i.2 hi⟩) (fun i hi => hκrb i.1 i.2 hi)
      (fun i₁ hi₁ i₂ hi₂ he => Subtype.ext (hκrinj i₁.1 i₁.2 hi₁ i₂.1 i₂.2 hi₂
        (congrArg Subtype.val he))) (fun i' hi' => ?_) (fun s hs i hi => hGr s hs i.1 i.2 hi)
    obtain ⟨i, hQ, hi, he⟩ := hκrsurj i'.1 i'.2 hi'
    exact ⟨⟨i, hQ⟩, hi, Subtype.ext he⟩

end Transport

/-! ### The coefficient of the observable for the block measures of two steps -/

section StepObs

open Balaban.Inhabited Balaban.Inhabited.LevelStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "𝔅A" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
  Set.univ
set_option hygiene false in
local notation "𝔅B" => CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
  Set.univ
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "RelB" => fun (Φ : ∀ c, ((SA).blockSplit m₀ hp).Ωb c)
  (Φ' : ∀ c, ((SB).blockSplit m₀ hp').Ωb c) =>
    ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ' ((SB).cellOf m₀ (unitPt hGB (bm x))) ⟨unitPt hGB (bm x), rfl⟩ =
        Φ ((SA).cellOf m₀ (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩

/-- **D2: the coefficient of the observable for the block measures of two steps.**
`obsCoeffParam_transport` for the block measures `(S.blockSplit m₀ hp).μ` of the two steps, the
correspondence `cubeMap` of the blocks, a set `T` of blocks inside the box of radius `R`, and the
relation "agreement of the block variables at corresponding unit points of the box"
(`RelB` in the proof); its integral hypothesis is `integral_blockSplit_twoTorus`.  What remains
as hypotheses are the correspondences of the active labels and their activities, of the
first-order labels, marks and kernel, and of the non-vanishing remainder marks.  Margin:
`2 R + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1), N₁′ L^m₁ L^(k+1)`. -/
theorem obsCoeffParam_blockSplit_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb']
    {Lab : CubeLabels m₀ (k + 1) Set.univ Lb} {Lab' : CubeLabels m₀ (k + 1) Set.univ Lb'}
    {εH κH κ0 Kc εH' κH' κ0' Kc' : ℝ} {E E' : Type*}
    (Aact : E → ℂ → ℂ → LabelAct Lab ((SA).blockSplit m₀ hp).Ωb εH κH κ0 Kc)
    (Aact' : E' → ℂ → ℂ → LabelAct Lab' ((SB).blockSplit m₀ hp').Ωb εH' κH' κ0' Kc')
    {ι ι' ιr ιr' : Type*} [Fintype ι] [Fintype ι'] [Fintype ιr] [Fintype ιr']
    (y1 : ι → Lb) (y1' : ι' → Lb')
    (G1 : ι → (∀ c, ((SA).blockSplit m₀ hp).Ωb c) → ℂ)
    (G1' : ι' → (∀ c, ((SB).blockSplit m₀ hp').Ωb c) → ℂ)
    (hker : E → ι → Finset (𝔅A) → ℂ) (hker' : E' → ι' → Finset (𝔅B) → ℂ)
    (yr : ιr → Lb) (yr' : ιr' → Lb')
    (Gr : E → ιr → ℂ → (∀ c, ((SA).blockSplit m₀ hp).Ωb c) → ℂ)
    (Gr' : E' → ιr' → ℂ → (∀ c, ((SB).blockSplit m₀ hp').Ωb c) → ℂ)
    (θ : E) (θ' : E')
    (T : Finset (𝔅A))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L m₀ m₁ (k + 1)),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    -- the activities
    (P : Lb → Prop) (P' : Lb' → Prop)
    (hA0 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, ¬ P y → ∀ Φ, (Aact θ (s : ℂ) 1).H y Φ = 0)
    (hA0' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y', ¬ P' y' → ∀ Φ',
      (Aact' θ' (s : ℂ) 1).H y' Φ' = 0)
    (ψ : ∀ y, P y → blocksOf m₀ (k + 1) Set.univ (Lab.ysite y) ⊆ T → Lb')
    (hψP : ∀ y hP hy, P' (ψ y hP hy))
    (hψb : ∀ y hP hy, blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (ψ y hP hy)) =
      (blocksOf m₀ (k + 1) Set.univ (Lab.ysite y)).image (σc))
    (hψinj : ∀ y₁ hP₁ hy₁ y₂ hP₂ hy₂, ψ y₁ hP₁ hy₁ = ψ y₂ hP₂ hy₂ → y₁ = y₂)
    (hψsurj : ∀ y', P' y' → blocksOf m₀ (k + 1) Set.univ (Lab'.ysite y') ⊆ T.image (σc) →
      ∃ y hP hy, ψ y hP hy = y')
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y hP hy, ∀ Φ Φ',
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf m₀ (unitPt hGB (bm x))) ⟨unitPt hGB (bm x), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩) →
      (Aact' θ' (s : ℂ) 1).H (ψ y hP hy) Φ' = (Aact θ (s : ℂ) 1).H y Φ)
    -- the first-order marks and the kernel
    (hG1dep : ∀ i, DepOn (blocksOf m₀ (k + 1) Set.univ (Lab.ysite (y1 i))) (G1 i))
    (κ1 : ∀ i, blocksOf m₀ (k + 1) Set.univ (Lab.ysite (y1 i)) ⊆ T → ι')
    (hκ1b : ∀ i hi, blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (y1' (κ1 i hi))) =
      (blocksOf m₀ (k + 1) Set.univ (Lab.ysite (y1 i))).image (σc))
    (hκ1inj : ∀ i₁ hi₁ i₂ hi₂, κ1 i₁ hi₁ = κ1 i₂ hi₂ → i₁ = i₂)
    (hκ1surj : ∀ i', blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (y1' i')) ⊆ T.image (σc) →
      ∃ i hi, κ1 i hi = i')
    (hG1 : ∀ i hi, ∀ Φ Φ',
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf m₀ (unitPt hGB (bm x))) ⟨unitPt hGB (bm x), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩) → G1' (κ1 i hi) Φ' = G1 i Φ)
    (hkerT : ∀ i hi, ∀ T₁ ⊆ T, hker' θ' (κ1 i hi) (T₁.image (σc)) = hker θ i T₁)
    -- the remainder marks
    (Qr : ιr → Prop) (Qr' : ιr' → Prop)
    (hGr0 : ∀ i, ¬ Qr i → ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → Gr θ i (s : ℂ) = fun _ => 0)
    (hGr0' : ∀ i', ¬ Qr' i' → ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → Gr' θ' i' (s : ℂ) = fun _ => 0)
    (hGrdep : ∀ i u, DepOn (blocksOf m₀ (k + 1) Set.univ (Lab.ysite (yr i))) (Gr θ i u))
    (κr : ∀ i, Qr i → blocksOf m₀ (k + 1) Set.univ (Lab.ysite (yr i)) ⊆ T → ιr')
    (hκrQ : ∀ i hQ hi, Qr' (κr i hQ hi))
    (hκrb : ∀ i hQ hi, blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (yr' (κr i hQ hi))) =
      (blocksOf m₀ (k + 1) Set.univ (Lab.ysite (yr i))).image (σc))
    (hκrinj : ∀ i₁ hQ₁ hi₁ i₂ hQ₂ hi₂, κr i₁ hQ₁ hi₁ = κr i₂ hQ₂ hi₂ → i₁ = i₂)
    (hκrsurj : ∀ i', Qr' i' → blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (yr' i')) ⊆ T.image (σc) →
      ∃ i hQ hi, κr i hQ hi = i')
    (hGr : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i hQ hi, ∀ Φ Φ',
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf m₀ (unitPt hGB (bm x))) ⟨unitPt hGB (bm x), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩) →
      Gr' θ' (κr i hQ hi) (s : ℂ) Φ' = Gr θ i (s : ℂ) Φ) :
    obsCoeffParam ((SB).blockSplit m₀ hp').μ Aact' y1' G1' hker' yr' Gr' θ' (T.image (σc)) =
      obsCoeffParam ((SA).blockSplit m₀ hp).μ Aact y1 G1 hker yr Gr θ T := by
  have hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hσ : Set.InjOn (σc) (T : Set (𝔅A)) := by
    intro b₁ hb₁ b₂ hb₂ h
    have hb₁R := hT b₁ hb₁ b₁.1 (mem_box_self _ (cellSide_pos m₀ m₁ (k + 1)))
    have hb₂R := hT b₂ hb₂ b₂.1 (mem_box_self _ (cellSide_pos m₀ m₁ (k + 1)))
    have h1 := congrArg Subtype.val h
    rw [cubeMap_val, cubeMap_val] at h1
    exact Subtype.ext (boxMap_inj (hm' := hm') hb₁R hb₂R h1)
  exact obsCoeffParam_transport _ _ Aact Aact' y1 y1' G1 G1' hker hker' yr yr' Gr Gr' θ θ' (σc) T
    hσ (RelB) (fun Z hZ F F' hF hFF => integral_blockSplit_twoTorus hN2 hk νS β p₁ δ hn hn' hGA
      hGB hp hp' Z (fun b hb => hT b (hZ hb)) hF hFF) P P' hA0 hA0' ψ hψP hψb hψinj hψsurj hA
    hG1dep κ1 hκ1b hκ1inj hκ1surj hG1 hkerT Qr Qr' hGr0 hGr0' hGrdep κr hκrQ hκrb hκrinj hκrsurj
    hGr

end StepObs

end Balaban.Polymer.TwoTorusStep
