/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCoeffTwoTorus
public import Balaban.Inhabited.NewLevelHTwoTorus
public import Balaban.Polymer.TwoTorusLabelBox

/-!
# The anchors of the marks of two systems of the new level on two tori

The anchors of the marks of a system are the bridge labels of the root and the marks of the old
terms (`NewLevelSystem.AnchorIdx`).

* `kappa_of_rel`: a partial bijection from a relation;
* `anchor_inl_corr`: the bridge anchors with blocks in a set `T` of the box correspond to those with
  blocks in `cubeMap '' T` (`bm`-images);
* `anchor_inr_corr`: the anchors of the marks of the old terms correspond (`(τ, Y) ↦ (e τ, bm '' Y)`
  along the partial index bijections of the old terms of the labels `Y` of the box), with the
  correspondence of the labels `jL`, the label cubes and the blocks of the bridges.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory Balaban.Polymer.TwoTorusStep

/-- **A partial bijection from a relation.** -/
theorem kappa_of_rel {ι ι' : Type*} (B : ι → Prop) (B' : ι' → Prop) (r : ι → ι' → Prop)
    (hex : ∀ i, B i → ∃ i', r i i')
    (hfun : ∀ i i₁ i₂, B i → r i i₁ → r i i₂ → i₁ = i₂)
    (hinj : ∀ i₁ i₂ i', B i₁ → B i₂ → r i₁ i' → r i₂ i' → i₁ = i₂)
    (hsurj : ∀ i', B' i' → ∃ i, B i ∧ r i i') :
    ∃ κ : (∀ i, B i → ι'), (∀ i hi, r i (κ i hi)) ∧
      (∀ i₁ h₁ i₂ h₂, κ i₁ h₁ = κ i₂ h₂ → i₁ = i₂) ∧ (∀ i', B' i' → ∃ i hi, κ i hi = i') := by
  classical
  refine ⟨fun i hi => Classical.choose (hex i hi), fun i hi => Classical.choose_spec (hex i hi),
    ?_, ?_⟩
  · intro i₁ h₁ i₂ h₂ h
    have h' : Classical.choose (hex i₁ h₁) = Classical.choose (hex i₂ h₂) := h
    have h2 := Classical.choose_spec (hex i₂ h₂)
    rw [← h'] at h2
    exact hinj i₁ i₂ _ h₁ h₂ (Classical.choose_spec (hex i₁ h₁)) h2
  · intro i' hi'
    obtain ⟨i, hi, hr⟩ := hsurj i' hi'
    exact ⟨i, hi, hfun i _ _ hi (Classical.choose_spec (hex i hi)) hr⟩


section Anchor

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  (m₀ := 1) hN hN' (le_refl (k + 1))

theorem NewLevelSystem.dom_iff {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (τ : NS.O.ι) :
    NS.Dom Y τ ↔ Y ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) := Iff.rfl

attribute [local irreducible] NewLevelSystem.Dom

/-- **The bridge anchors of the root correspond on two tori.** -/
theorem anchor_inl_corr
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : (SA).JointRep t pp} {C' : StepClass d L N₁' m₁ k N ϱ} {pp' : ℝ} {Jr' : (SB).JointRep t pp'} (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁')
    (hm₁ : 1 ≤ m₁)
    {rc R : ℕ}
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z) (hrc : L ^ (k + 1) * rc ≤ R) (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1)) (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    :
    ∃ φ : (∀ a : {Y' // Y' ∈ bridgeFamily 1
        (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
          (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG (SA)) z},
        blocksOf 1 (k + 1) Set.univ a.1 ⊆ T →
        {Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
          (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (e1DomG (SB)) (bc z)}),
      (∀ a ha, (φ a ha).1 = bm '' a.1) ∧
      (∀ a₁ h₁ a₂ h₂, φ a₁ h₁ = φ a₂ h₂ → a₁ = a₂) ∧
      (∀ b : {Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
          (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (e1DomG (SB)) (bc z)},
        blocksOf 1 (k + 1) Set.univ b.1 ⊆ T.image (σc) → ∃ a ha, φ a ha = b) := by
  classical
  obtain ⟨⟨hn1, hnS, hnF, hnH, hnM⟩, ⟨hn1', hnS', hnF', hnH', hnM'⟩⟩ :=
    twoTorus_margins_of_lt_min (R := R) (k := k) (m₀ := 1) (m₁ := m₁) hm₁ (lt_min hn hn')
  have hcs : cellSide L 1 m₁ (k + 1) ≤ L * cellSide L 1 m₁ (k + 1) := cellSide_le_mul
  have hm : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hc : 2 * R + cellSide L 1 m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hc' : 2 * R + cellSide L 1 m₁ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hr : 2 * R + L * cellSide L 1 m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hmem : ∀ a : {Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG (SA)) z},
      blocksOf 1 (k + 1) Set.univ a.1 ⊆ T →
      bm '' a.1 ∈ bridgeFamily 1 (fun _ : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (e1DomG (SB)) (bc z) :=
    fun a hi => (mem_bridgeFamily_boxMap_iff (ϱ := ϱ) hN hN' hn1 hn1' hnF hnF' hnH hnH' z hz hrc
      hroot (inBox_of_blocksOf_subset (Y := a.1) hN (bridgeFamily_isDj hN NS.hL NS.hdomE z a.1 a.2) hT hi)).2 a.2
  have hbox : ∀ a : {Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG (SA)) z},
      blocksOf 1 (k + 1) Set.univ a.1 ⊆ T → ∀ x ∈ a.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun a hi => inBox_of_blocksOf_subset (Y := a.1) hN
      (bridgeFamily_isDj hN NS.hL NS.hdomE z a.1 a.2) hT hi
  obtain ⟨φ, hφr, hφinj, hφsurj⟩ := kappa_of_rel
    (fun a : {Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG (SA)) z} =>
      blocksOf 1 (k + 1) Set.univ a.1 ⊆ T)
    (fun b : {Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (e1DomG (SB)) (bc z)} =>
      blocksOf 1 (k + 1) Set.univ b.1 ⊆ T.image (σc))
    (fun a b => b.1 = bm '' a.1)
    (fun a ha => ⟨⟨bm '' a.1, hmem a ha⟩, rfl⟩)
    (fun a b₁ b₂ _ h₁ h₂ => Subtype.ext (h₁.trans h₂.symm))
    (fun a₁ a₂ b h₁ h₂ r₁ r₂ => Subtype.ext (image_boxMap_inj (N₁' := N₁') hm' (hbox a₁ h₁)
      (hbox a₂ h₂) (r₁.symm.trans r₂)))
    (fun b hb => by
      obtain ⟨hYR, hYT, hYimg⟩ := exists_preimage_label hN hN' hm hm' hr hc hc' T hT
        (Y' := b.1) (bridgeFamily_isDj hN' NS'.hL NS'.hdomE (bc z) b.1 b.2) hb
      have hmem' : bm' '' b.1 ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
          (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG (SA)) z :=
        (mem_bridgeFamily_boxMap_iff (ϱ := ϱ) hN hN' hn1 hn1' hnF hnF' hnH hnH' z hz hrc hroot
          hYR).1 (by rw [hYimg]; exact b.2)
      exact ⟨⟨_, hmem'⟩, hYT, hYimg.symm⟩)
  exact ⟨φ, hφr, hφinj, hφsurj⟩

/-- The sets of the anchors of the marks lie in the box when the blocks of their bridges lie in `T`. -/
theorem anchor_inr_box
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : (SA).JointRep t pp} (NS : NewLevelSystem (SA) C z Jr)
    (hN : L ^ 1 ∣ N₁)
    {R : ℕ}
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (q : {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (fun τ => polyDom (SA).G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z})
    (h : blocksOf 1 (k + 1) Set.univ (bridge 1 z q.1.2) ⊆ T) :
    ∀ x ∈ bridge 1 z q.1.2, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
  inBox_of_blocksOf_subset hN (bridge_isDj hN z (NS.hdomC q.1.1 q.1.2 (mem_markedIdx.1 q.2).1)) hT h

/-- Likewise on the second torus. -/
theorem anchor_inr_box'
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C' : StepClass d L N₁' m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp' : ℝ} {Jr' : (SB).JointRep t pp'} (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁')
    {R : ℕ}
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hr : 2 * R + L * cellSide L 1 m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (q : {q // q ∈ markedIdx (fun _ : NS'.O.ι => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (fun τ => polyDom (SB).G' (NS'.O.X₁f τ) NS'.O.m₀ (NS'.O.jL τ) (NS'.O.𝒦X τ)) (bc z)})
    (h : blocksOf 1 (k + 1) Set.univ (bridge 1 (bc z) q.1.2) ⊆ T.image (σc)) :
    ∀ x ∈ bridge 1 (bc z) q.1.2, InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) x :=
  inBox_of_blocksOf_subset_image hN hN' hm' hr T hT
    (bridge_isDj hN' (bc z) (NS'.hdomC q.1.1 q.1.2 (mem_markedIdx.1 q.2).1)) h

/-- **The correspondence of the anchors of the marks along a family of index bijections.** -/
def AnchorRelInr {hN2 : 2 ≤ N} {hk : 1 ≤ k} {νS β p₁ δ : ℝ}
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ}
    {Jr : (SA).JointRep t pp} {C' : StepClass d L N₁' m₁ k N ϱ} {pp' : ℝ}
    {Jr' : (SB).JointRep t pp'}
    (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' (bc z) Jr') {R : ℕ}
    (eY : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) → ({τ // NS.Dom Y τ} ≃ {τ' // NS'.Dom (bm '' Y) τ'}))
    (q : {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (fun τ => polyDom (SA).G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) (q' : {q // q ∈ markedIdx (fun _ : NS'.O.ι => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (fun τ => polyDom (SB).G' (NS'.O.X₁f τ) NS'.O.m₀ (NS'.O.jL τ) (NS'.O.𝒦X τ)) (bc z)}) : Prop :=
  ∃ (hY : ∀ x ∈ q.1.2, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) (hτ : NS.Dom q.1.2 q.1.1),
    q'.1.2 = bm '' q.1.2 ∧ (eY q.1.2 hY ⟨q.1.1, hτ⟩).1 = q'.1.1

theorem anchor_inr_fun
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : (SA).JointRep t pp} {C' : StepClass d L N₁' m₁ k N ϱ} {pp' : ℝ} {Jr' : (SB).JointRep t pp'} (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    {R : ℕ}
    (eY : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) → ({τ // NS.Dom Y τ} ≃ {τ' // NS'.Dom (bm '' Y) τ'}))
    (q : {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (fun τ => polyDom (SA).G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) (q₁ q₂ : {q // q ∈ markedIdx (fun _ : NS'.O.ι => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (fun τ => polyDom (SB).G' (NS'.O.X₁f τ) NS'.O.m₀ (NS'.O.jL τ) (NS'.O.𝒦X τ)) (bc z)}) (h₁ : AnchorRelInr NS NS' eY q q₁)
    (h₂ : AnchorRelInr NS NS' eY q q₂) : q₁ = q₂ := by
  obtain ⟨hY, hτ, h1, h2⟩ := h₁
  obtain ⟨hY', hτ', h1', h2'⟩ := h₂
  exact Subtype.ext (Prod.ext (h2.symm.trans h2') (h1.trans h1'.symm))

theorem anchor_inr_inj
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : (SA).JointRep t pp} {C' : StepClass d L N₁' m₁ k N ϱ} {pp' : ℝ} {Jr' : (SB).JointRep t pp'} (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    {R : ℕ}
    (eY : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) → ({τ // NS.Dom Y τ} ≃ {τ' // NS'.Dom (bm '' Y) τ'}))
    (hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (q₁ q₂ : {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (fun τ => polyDom (SA).G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) (q' : {q // q ∈ markedIdx (fun _ : NS'.O.ι => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (fun τ => polyDom (SB).G' (NS'.O.X₁f τ) NS'.O.m₀ (NS'.O.jL τ) (NS'.O.𝒦X τ)) (bc z)}) (h₁ : AnchorRelInr NS NS' eY q₁ q')
    (h₂ : AnchorRelInr NS NS' eY q₂ q') : q₁ = q₂ := by
  obtain ⟨hY₁, hτ₁, h1₁, h2₁⟩ := h₁
  obtain ⟨hY₂, hτ₂, h1₂, h2₂⟩ := h₂
  have hYe : q₁.1.2 = q₂.1.2 :=
    image_boxMap_inj (N₁' := N₁') hm' hY₁ hY₂ (h1₁.symm.trans h1₂)
  have key : ∀ (Y₁ Y₂ : Set (CTorus d L N₁ m₁ (k + 1)))
      (hY₁ : ∀ x ∈ Y₁, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
      (hY₂ : ∀ x ∈ Y₂, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) (τ₁ τ₂ : NS.O.ι)
      (hτ₁ : NS.Dom Y₁ τ₁) (hτ₂ : NS.Dom Y₂ τ₂), Y₁ = Y₂ →
      (eY Y₁ hY₁ ⟨τ₁, hτ₁⟩).1 = (eY Y₂ hY₂ ⟨τ₂, hτ₂⟩).1 → τ₁ = τ₂ := by
    intro Y₁ Y₂ hY₁ hY₂ τ₁ τ₂ hτ₁ hτ₂ hY h
    subst hY
    exact congrArg Subtype.val ((eY Y₁ hY₁).injective (Subtype.ext h))
  exact Subtype.ext (Prod.ext (key _ _ hY₁ hY₂ _ _ hτ₁ hτ₂ hYe (h2₁.trans h2₂.symm)) hYe)

theorem anchor_inr_ex
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : (SA).JointRep t pp} {C' : StepClass d L N₁' m₁ k N ϱ} {pp' : ℝ} {Jr' : (SB).JointRep t pp'} (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    {rc R : ℕ}
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z) (hrc : L ^ (k + 1) * rc ≤ R)
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1)) (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hm₁ : 1 ≤ m₁)
    (eY : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) → ({τ // NS.Dom Y τ} ≃ {τ' // NS'.Dom (bm '' Y) τ'}))
    (q : {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (fun τ => polyDom (SA).G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) (hYR : ∀ x ∈ q.1.2, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    ∃ q', AnchorRelInr NS NS' eY q q' := by
  classical
  obtain ⟨⟨hn1, hnS, hnF, hnH, hnM⟩, ⟨hn1', hnS', hnF', hnH', hnM'⟩⟩ :=
    twoTorus_margins_of_lt_min (R := R) (k := k) (m₀ := 1) (m₁ := m₁) hm₁ (lt_min hn hn')
  obtain ⟨⟨τ, Y⟩, hq⟩ := q
  have hτ : NS.Dom Y τ := (NS.dom_iff Y τ).2 (mem_markedIdx.1 hq).1
  have hτ' := (eY Y hYR ⟨τ, hτ⟩).2
  have hq' : ((eY Y hYR ⟨τ, hτ⟩).1, bm '' Y) ∈ markedIdx
      (fun _ : NS'.O.ι => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1))))
      (fun τ' => polyDom (SB).G' (NS'.O.X₁f τ') NS'.O.m₀ (NS'.O.jL τ') (NS'.O.𝒦X τ'))
      (bc z) :=
    (markedIdx_boxMap_iff (N₁' := N₁') (m₁ := m₁) hn1 hn1' z hz hrc
      (dom := fun τ => polyDom (SA).G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
      (dom' := fun τ' => polyDom (SB).G' (NS'.O.X₁f τ') NS'.O.m₀ (NS'.O.jL τ') (NS'.O.𝒦X τ'))
      (b := τ) (b' := (eY Y hYR ⟨τ, hτ⟩).1) hYR
      (iff_of_true ((NS'.dom_iff _ _).1 hτ') ((NS.dom_iff _ _).1 hτ))).2 hq
  exact ⟨⟨(_, bm '' Y), hq'⟩, hYR, hτ, rfl, rfl⟩

theorem anchor_inr_surj
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : (SA).JointRep t pp} {C' : StepClass d L N₁' m₁ k N ϱ} {pp' : ℝ} {Jr' : (SB).JointRep t pp'} (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁')
    (hm₁ : 1 ≤ m₁)
    {rc R : ℕ}
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z) (hrc : L ^ (k + 1) * rc ≤ R) (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1)) (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (eY : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) → ({τ // NS.Dom Y τ} ≃ {τ' // NS'.Dom (bm '' Y) τ'}))
    
    (q' : {q // q ∈ markedIdx (fun _ : NS'.O.ι => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (fun τ => polyDom (SB).G' (NS'.O.X₁f τ) NS'.O.m₀ (NS'.O.jL τ) (NS'.O.𝒦X τ)) (bc z)})
    (hq' : blocksOf 1 (k + 1) Set.univ (bridge 1 (bc z) q'.1.2) ⊆ T.image (σc)) :
    ∃ q, blocksOf 1 (k + 1) Set.univ (bridge 1 z q.1.2) ⊆ T ∧
      AnchorRelInr NS NS' eY q q' := by
  classical
  obtain ⟨⟨hn1, hnS, hnF, hnH, hnM⟩, ⟨hn1', hnS', hnF', hnH', hnM'⟩⟩ :=
    twoTorus_margins_of_lt_min (R := R) (k := k) (m₀ := 1) (m₁ := m₁) hm₁ (lt_min hn hn')
  have hcs : cellSide L 1 m₁ (k + 1) ≤ L * cellSide L 1 m₁ (k + 1) := cellSide_le_mul
  have hm : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hc : 2 * R + cellSide L 1 m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hc' : 2 * R + cellSide L 1 m₁ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hr : 2 * R + L * cellSide L 1 m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hLa : 0 < L * cellSide L 1 m₁ (k + 1) :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos 1 m₁ (k + 1))
  obtain ⟨⟨τ', Y'⟩, hq'm⟩ := q'
  have hbr' : ∀ x ∈ bridge 1 (bc z) Y', InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) x :=
    anchor_inr_box' (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS' := NS') (hN := hN) (hN' := hN') (T := T) (hT := hT) (hr := hr) (hm' := hm') ⟨(τ', Y'), hq'm⟩ hq'
  obtain ⟨hB₀R, hB₀T, hB₀img⟩ := exists_preimage_label hN hN' hm hm' hr hc hc' T hT
    (Y' := bridge 1 (bc z) Y') (bridge_isDj hN' (bc z) (NS'.hdomC τ' Y' (mem_markedIdx.1 hq'm).1)) hq'
  have hY'R : ∀ x ∈ Y', InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) x :=
    fun x hx => hbr' x (subset_bridge 1 (bc z) Y' hx)
  have hYR : ∀ x ∈ bm' '' Y', InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    rintro _ ⟨x', hx', rfl⟩
    exact inBox_boxMap hm (hY'R x' hx')
  have hYimg : bm '' (bm' '' Y') = Y' :=
    image_image_boxMap (n' := (N₁ * L ^ m₁) * L ^ (k + 1)) hm hY'R
  have hτ'dom : NS'.Dom (bm '' (bm' '' Y')) τ' :=
    (NS'.dom_iff _ _).2 (by rw [hYimg]; exact (mem_markedIdx.1 hq'm).1)
  let x := (eY (bm' '' Y') hYR).symm ⟨τ', hτ'dom⟩
  have hxe : eY (bm' '' Y') hYR x = ⟨τ', hτ'dom⟩ := Equiv.apply_symm_apply _ _
  have hq : (x.1, bm' '' Y') ∈ markedIdx
      (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom (SA).G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z :=
    (markedIdx_boxMap_iff (N₁' := N₁') (m₁ := m₁) hn1 hn1' z hz hrc
      (dom := fun τ => polyDom (SA).G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
      (dom' := fun τ' => polyDom (SB).G' (NS'.O.X₁f τ') NS'.O.m₀ (NS'.O.jL τ') (NS'.O.𝒦X τ'))
      (b := x.1) (b' := τ') hYR
      (iff_of_true ((NS'.dom_iff _ _).1 hτ'dom) ((NS.dom_iff _ _).1 x.2))).1
      (by rw [hYimg]; exact hq'm)
  have hnH1 : 2 * (R + 2 * (L * cellSide L 1 m₁ (k + 1))) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by
    omega
  have hbz : bridge 1 z (bm' '' Y') = bm' '' bridge 1 (bc z) Y' := by
    have h1 : bm '' bridge 1 z (bm' '' Y') = bridge 1 (bc z) Y' := by
      rw [← bridge_image hN hN' hnH hnH' z hz hrc hroot hYR, hYimg]
    rw [← h1, image_image_boxMap hnH1 (inBox_of_mem_bridge (by omega) z hroot hYR)]
  refine ⟨⟨(x.1, bm' '' Y'), hq⟩, ?_, hYR, x.2, hYimg.symm, congrArg Subtype.val hxe⟩
  show blocksOf 1 (k + 1) Set.univ (bridge 1 z (bm' '' Y')) ⊆ T
  rw [hbz]
  exact hB₀T

/-- **The anchors of the marks of the old terms correspond on two tori.** -/
theorem anchor_inr_corr
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : (SA).JointRep t pp} {C' : StepClass d L N₁' m₁ k N ϱ} {pp' : ℝ} {Jr' : (SB).JointRep t pp'} (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁')
    (hm₁ : 1 ≤ m₁)
    {rc R : ℕ}
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z) (hrc : L ^ (k + 1) * rc ≤ R) (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1)) (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hE : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) → ∃ e : {τ // NS.Dom Y τ} ≃ {τ' // NS'.Dom (bm '' Y) τ'}, ∀ τ, NS'.O.jL (e τ).1 = NS.O.jL τ.1 ∧ NS'.O.X₁f (e τ).1 = (NS.O.X₁f τ.1).image bm)
    
    :
    ∃ ψ : (∀ q : {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (fun τ => polyDom (SA).G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}, blocksOf 1 (k + 1) Set.univ (bridge 1 z q.1.2) ⊆ T → {q // q ∈ markedIdx (fun _ : NS'.O.ι => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (fun τ => polyDom (SB).G' (NS'.O.X₁f τ) NS'.O.m₀ (NS'.O.jL τ) (NS'.O.𝒦X τ)) (bc z)}),
      (∀ q hq, (ψ q hq).1.2 = bm '' q.1.2 ∧
        (∀ x ∈ q.1.2, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) ∧ NS.Dom q.1.2 q.1.1 ∧
        NS'.O.jL (ψ q hq).1.1 = NS.O.jL q.1.1 ∧
        NS'.O.X₁f (ψ q hq).1.1 = (NS.O.X₁f q.1.1).image bm) ∧
      (∀ q₁ h₁ q₂ h₂, ψ q₁ h₁ = ψ q₂ h₂ → q₁ = q₂) ∧
      (∀ q' : {q // q ∈ markedIdx (fun _ : NS'.O.ι => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (fun τ => polyDom (SB).G' (NS'.O.X₁f τ) NS'.O.m₀ (NS'.O.jL τ) (NS'.O.𝒦X τ)) (bc z)},
        blocksOf 1 (k + 1) Set.univ (bridge 1 (bc z) q'.1.2) ⊆ T.image (σc) →
        ∃ q hq, ψ q hq = q') ∧
      (∀ q hq, blocksOf 1 (k + 1) Set.univ (bridge 1 (bc z) (ψ q hq).1.2) =
        (blocksOf 1 (k + 1) Set.univ (bridge 1 z q.1.2)).image (σc)) := by
  classical
  obtain ⟨⟨hn1, hnS, hnF, hnH, hnM⟩, ⟨hn1', hnS', hnF', hnH', hnM'⟩⟩ :=
    twoTorus_margins_of_lt_min (R := R) (k := k) (m₀ := 1) (m₁ := m₁) hm₁ (lt_min hn hn')
  have hcs : cellSide L 1 m₁ (k + 1) ≤ L * cellSide L 1 m₁ (k + 1) := cellSide_le_mul
  have hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hc : 2 * R + cellSide L 1 m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hc' : 2 * R + cellSide L 1 m₁ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  choose eY heY using hE
  obtain ⟨ψ, hψr, hψinj, hψsurj⟩ := kappa_of_rel
    (fun q : {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (fun τ => polyDom (SA).G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z} => blocksOf 1 (k + 1) Set.univ (bridge 1 z q.1.2) ⊆ T)
    (fun q' : {q // q ∈ markedIdx (fun _ : NS'.O.ι => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (fun τ => polyDom (SB).G' (NS'.O.X₁f τ) NS'.O.m₀ (NS'.O.jL τ) (NS'.O.𝒦X τ)) (bc z)} =>
      blocksOf 1 (k + 1) Set.univ (bridge 1 (bc z) q'.1.2) ⊆ T.image (σc))
    (AnchorRelInr NS NS' eY)
    (fun q hq => anchor_inr_ex (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS := NS) (NS' := NS') (hz := hz) (hrc := hrc) (hn := hn) (hn' := hn') (hm₁ := hm₁) (eY := eY) q
      (fun x hx => anchor_inr_box (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS := NS) (hN := hN) (T := T) (hT := hT) q hq x (subset_bridge 1 z q.1.2 hx)))
    (fun q q₁ q₂ _ h₁ h₂ => anchor_inr_fun (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS := NS) (NS' := NS') (eY := eY) q q₁ q₂ h₁ h₂)
    (fun q₁ q₂ q' _ _ h₁ h₂ => anchor_inr_inj (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS := NS) (NS' := NS') (eY := eY) (hm' := hm') q₁ q₂ q' h₁ h₂)
    (fun q' hq' => anchor_inr_surj (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS := NS) (NS' := NS') (hN := hN) (hN' := hN') (hm₁ := hm₁) (hz := hz) (hrc := hrc) (hroot := hroot) (hn := hn) (hn' := hn') (T := T) (hT := hT) (eY := eY) q' hq')
  refine ⟨ψ, ?_, hψinj, hψsurj, ?_⟩
  · intro q hq
    obtain ⟨hY, hτ, h2, h3⟩ := hψr q hq
    refine ⟨h2, hY, hτ, ?_, ?_⟩
    · rw [← h3]; exact (heY q.1.2 hY ⟨q.1.1, hτ⟩).1
    · rw [← h3]; exact (heY q.1.2 hY ⟨q.1.1, hτ⟩).2
  · intro q hq
    obtain ⟨hY, hτ, h2, h3⟩ := hψr q hq
    rw [h2, bridge_image hN hN' hnH hnH' z hz hrc hroot hY]
    exact blocksOf_image_boxMap hN hN' hc hc'
      (anchor_inr_box (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS := NS) (hN := hN) (T := T) (hT := hT) q hq)

end Anchor

end Balaban.Inhabited
