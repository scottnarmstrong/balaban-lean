/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCanon
public import Balaban.Inhabited.NewLevelCanonEquiv
public import Balaban.Inhabited.NewLevelHTwoTorus
public import Balaban.Polymer.BoxTransport
public import Balaban.Polymer.TwoTorusStepGeometry

/-!
# The canonical pins of the inherited levels

`CanonCover`: the canonical covering data of an old term as functions of `(j, y, X)` (the same
formula on every torus).  `OldTermsCanonPins S C O F`: the inherited levels `O` are canonically
indexed (`OldTermsCanon`) and the label cubes, the cover set, the generating sets and the radius of
every old term are those of `F` at `(jL τ, y τ, X τ)`.  The producer of a `NewLevelSystem` must prove
it (after R13).

`OldTermsCanonPins.exists_domEquiv`: two systems with canonical pins on two tori have the partial index
bijection `e` between the old terms whose domains contain the corresponding labels `Y`, `bm '' Y`, with
`jL`, `m₀` and the label cubes corresponding.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Polymer Balaban.Polymer.TwoTorusStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The canonical covering data of the old terms as functions of `(j, y, X)`.** -/
structure CanonCover (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] (ϱ ϱ₁ : ℝ) where
  X₁fC : ℕ → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
    Finset (CTorus d L N₁ m₁ (k + 1))
  𝒦XC : ℕ → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
    Set (CTorus d L N₁ m₁ (k + 1))
  GkC : ℕ → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
    GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁
  GjC : ℕ → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
    GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ
  ρC : ℝ

/-- **The inherited levels are canonically indexed and canonically covered.** -/
def OldTermsCanonPins (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ) {t : ℝ}
    (O : OldTermSystem S t) (F : CanonCover d L N₁ m₁ k ϱ O.ϱ₁) : Prop :=
  O.m₀ = C.m₀ ∧ ∃ (i₀ i₁ : Fin N) (y : O.ι → CTorus d L N₁ m₁ (k + 1))
    (X : O.ι → Set (CTorus d L N₁ m₁ (k + 1))),
    (∀ τ r, O.Eτ τ r = irrelTorus C.m₀ C.Tm i₀ i₁ (O.jL τ) (y τ) (X τ) r.1 r.2) ∧
    Set.BijOn (fun τ => (O.jL τ, y τ, X τ)) Set.univ (AdmPairs L N₁ m₁ k d C.m₀ k) ∧
    ∀ τ, O.X₁f τ = F.X₁fC (O.jL τ) (y τ) (X τ) ∧ O.𝒦X τ = F.𝒦XC (O.jL τ) (y τ) (X τ) ∧
      O.Gk τ = F.GkC (O.jL τ) (y τ) (X τ) ∧ O.Gj τ = F.GjC (O.jL τ) (y τ) (X τ) ∧ O.ρ = F.ρC

theorem OldTermsCanonPins.canon {S : StepSetting d L N₁ m₁ k N ϱ}
    {C : StepClass d L N₁ m₁ k N ϱ} {t : ℝ} {O : OldTermSystem S t}
    {F : CanonCover d L N₁ m₁ k ϱ O.ϱ₁} (h : OldTermsCanonPins S C O F) : OldTermsCanon S C O := by
  obtain ⟨h0, i₀, i₁, y, X, hE, hB, -⟩ := h
  exact ⟨h0, i₀, i₁, y, X, hE, hB⟩

variable {N₁' : ℕ} [NeZero N₁']

/-- **The partial index bijection of two canonically indexed families (core).**  As
`domEquiv_generic`, with the back correspondence `hAdm'` giving, for every `τ'` in the second domain,
a `τ` of the first domain with the corresponding labels (no premise on the other `τ`). -/
theorem domEquiv_generic_core {ι ι' T T' : Type*} (φ : T → T') (A : Set (ℕ × T × Set T))
    (A' : Set (ℕ × T' × Set T')) (Bx : T → Prop)
    (jL : ι → ℕ) (y : ι → T) (X : ι → Set T) (jL' : ι' → ℕ) (y' : ι' → T') (X' : ι' → Set T')
    (hB : Set.BijOn (fun τ => (jL τ, y τ, X τ)) Set.univ A)
    (hB' : Set.BijOn (fun τ => (jL' τ, y' τ, X' τ)) Set.univ A')
    (hφinj : Set.InjOn φ {x | Bx x})
    (Dom : ι → Prop) (Dom' : ι' → Prop)
    (hAdm : ∀ τ, Dom τ → (jL τ, φ (y τ), φ '' X τ) ∈ A')
    (hAdm' : ∀ τ', Dom' τ' → ∃ τ, Dom τ ∧ y' τ' = φ (y τ) ∧ X' τ' = φ '' X τ ∧ jL' τ' = jL τ)
    (hbox : ∀ τ, Dom τ → ∀ x ∈ insert (y τ) (X τ), Bx x)
    (hdom : ∀ τ τ', Dom τ → y' τ' = φ (y τ) → X' τ' = φ '' X τ → jL' τ' = jL τ → Dom' τ') :
    ∃ e : {τ // Dom τ} ≃ {τ' // Dom' τ'}, ∀ τ : {τ // Dom τ},
      y' (e τ).1 = φ (y τ.1) ∧ X' (e τ).1 = φ '' X τ.1 ∧ jL' (e τ).1 = jL τ.1 := by
  classical
  let Φ : ℕ × T × Set T → ℕ × T' × Set T' := fun q => (q.1, φ q.2.1, φ '' q.2.2)
  have hpair : ∀ τ τ', (jL' τ', y' τ', X' τ') = Φ (jL τ, y τ, X τ) ↔
      (y' τ' = φ (y τ) ∧ X' τ' = φ '' X τ ∧ jL' τ' = jL τ) := by
    intro τ τ'
    simp only [Φ, Prod.mk.injEq]
    tauto
  obtain ⟨e, he⟩ := partialEquiv_of_pairs (fun τ => (jL τ, y τ, X τ))
    (fun τ' => (jL' τ', y' τ', X' τ')) Φ Dom Dom' (fun a b h => hB'.2.1 (Set.mem_univ a) (Set.mem_univ b) h)
    (fun τ hτ => by
      obtain ⟨τ', hτ'⟩ := hB'.surjOn (hAdm τ hτ)
      exact ⟨τ', hτ'.2⟩)
    (fun τ τ' hτ h => by
      obtain ⟨h1, h2, h3⟩ := (hpair τ τ').1 h
      exact hdom τ τ' hτ h1 h2 h3)
    (fun τ' hτ' => by
      obtain ⟨τ, hτ, h1, h2, h3⟩ := hAdm' τ' hτ'
      exact ⟨τ, hτ, (hpair τ τ').2 ⟨h1, h2, h3⟩⟩)
    (fun τ₁ τ₂ h₁ h₂ h => by
      simp only [Φ, Prod.mk.injEq] at h
      obtain ⟨hj, hy, hX⟩ := h
      have hy' : y τ₁ = y τ₂ := hφinj (hbox τ₁ h₁ _ (Set.mem_insert _ _))
        (hbox τ₂ h₂ _ (Set.mem_insert _ _)) hy
      have hXe : X τ₁ = X τ₂ := by
        refine (Set.InjOn.image_eq_image_iff hφinj ?_ ?_).1 hX
        · exact fun x hx => hbox τ₁ h₁ x (Set.mem_insert_of_mem _ hx)
        · exact fun x hx => hbox τ₂ h₂ x (Set.mem_insert_of_mem _ hx)
      exact hB.injOn (Set.mem_univ τ₁) (Set.mem_univ τ₂) (by simp only [hj, hy', hXe]))
  exact ⟨e, fun τ => (hpair τ.1 (e τ).1).1 (he τ)⟩

/-- **The partial index bijection of two canonically indexed families (generic form).** -/
theorem domEquiv_generic {ι ι' T T' : Type*} (φ : T → T') (A : Set (ℕ × T × Set T))
    (A' : Set (ℕ × T' × Set T')) (Bx : T → Prop)
    (jL : ι → ℕ) (y : ι → T) (X : ι → Set T) (jL' : ι' → ℕ) (y' : ι' → T') (X' : ι' → Set T')
    (hB : Set.BijOn (fun τ => (jL τ, y τ, X τ)) Set.univ A)
    (hB' : Set.BijOn (fun τ => (jL' τ, y' τ, X' τ)) Set.univ A')
    (hφinj : Set.InjOn φ {x | Bx x})
    (Dom : ι → Prop) (Dom' : ι' → Prop)
    (hAdm : ∀ τ, Dom τ → (jL τ, φ (y τ), φ '' X τ) ∈ A')
    (hAdm' : ∀ τ', Dom' τ' → ∃ τ, y' τ' = φ (y τ) ∧ X' τ' = φ '' X τ ∧ jL' τ' = jL τ)
    (hbox : ∀ τ, Dom τ → ∀ x ∈ insert (y τ) (X τ), Bx x)
    (hdom : ∀ τ τ', Dom τ → y' τ' = φ (y τ) → X' τ' = φ '' X τ → jL' τ' = jL τ → Dom' τ')
    (hdom' : ∀ τ τ', Dom' τ' → y' τ' = φ (y τ) → X' τ' = φ '' X τ → jL' τ' = jL τ → Dom τ) :
    ∃ e : {τ // Dom τ} ≃ {τ' // Dom' τ'}, ∀ τ : {τ // Dom τ},
      y' (e τ).1 = φ (y τ.1) ∧ X' (e τ).1 = φ '' X τ.1 ∧ jL' (e τ).1 = jL τ.1 :=
  domEquiv_generic_core φ A A' Bx jL y X jL' y' X' hB hB' hφinj Dom Dom' hAdm
    (fun τ' hτ' => by
      obtain ⟨τ, h1, h2, h3⟩ := hAdm' τ' hτ'
      exact ⟨τ, hdom' τ τ' hτ' h1 h2 h3, h1, h2, h3⟩) hbox hdom

/-- **The partial index bijection of the old terms of two canonically pinned systems (core).**
As `exists_domEquiv_of_canon`, with the back correspondence `hAdm'` giving for every `τ'` of the
second domain a `τ` of the first domain with the corresponding labels, and no premise `hdom'`.  For the
label `Y` in the box and `Y' = bm '' Y`, the old terms whose domains contain `Y` correspond to those
whose domains contain `Y'`, with the same level and the label cubes of the images.  `y X`, `y' X'` are
the witnesses of the canonical indexing; the hypotheses are the box geometry of the pairs
(`hAdm`, `hAdm'`, `hbox`), the covers of the images (`hcov`) and the correspondence of the domains
(`hdom`, `hdom'`, from `polyDom_boxMap_iff`). -/
theorem exists_domEquiv_of_canon_core
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (NS' : NewLevelSystem S' C' z' Jr')
    {F : CanonCover d L N₁ m₁ k ϱ NS.O.ϱ₁} {F' : CanonCover d L N₁' m₁ k ϱ NS'.O.ϱ₁}
    (y : NS.O.ι → CTorus d L N₁ m₁ (k + 1)) (X : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (y' : NS'.O.ι → CTorus d L N₁' m₁ (k + 1)) (X' : NS'.O.ι → Set (CTorus d L N₁' m₁ (k + 1)))
    (hB : Set.BijOn (fun τ => (NS.O.jL τ, y τ, X τ)) Set.univ (AdmPairs L N₁ m₁ k d C.m₀ k))
    (hB' : Set.BijOn (fun τ => (NS'.O.jL τ, y' τ, X' τ)) Set.univ (AdmPairs L N₁' m₁ k d C'.m₀ k))
    (hX₁ : ∀ τ, NS.O.X₁f τ = F.X₁fC (NS.O.jL τ) (y τ) (X τ))
    (hX₁' : ∀ τ, NS'.O.X₁f τ = F'.X₁fC (NS'.O.jL τ) (y' τ) (X' τ))
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Y' : Set (CTorus d L N₁' m₁ (k + 1)))
    {R : ℕ} (hm : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hAdm : ∀ τ, NS.Dom Y τ → (NS.O.jL τ, boxMap ((N₁ * L ^ m₁) * L ^ (k + 1))
        ((N₁' * L ^ m₁) * L ^ (k + 1)) (y τ), (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1))
        ((N₁' * L ^ m₁) * L ^ (k + 1))) '' X τ) ∈ AdmPairs L N₁' m₁ k d C'.m₀ k)
    (hAdm' : ∀ τ', NS'.Dom Y' τ' → ∃ τ, NS.Dom Y τ ∧ y' τ' = boxMap ((N₁ * L ^ m₁) * L ^ (k + 1))
        ((N₁' * L ^ m₁) * L ^ (k + 1)) (y τ) ∧ X' τ' = (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1))
        ((N₁' * L ^ m₁) * L ^ (k + 1))) '' X τ ∧ NS'.O.jL τ' = NS.O.jL τ)
    (hbox : ∀ τ, NS.Dom Y τ → ∀ x ∈ insert (y τ) (X τ),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hcov : ∀ j y₀ X₀, (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      F'.X₁fC j (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1)) y₀)
        ((boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) '' X₀) =
      (F.X₁fC j y₀ X₀).image (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1))
        ((N₁' * L ^ m₁) * L ^ (k + 1))))
    (hdom : ∀ τ τ', NS.Dom Y τ → y' τ' = boxMap ((N₁ * L ^ m₁) * L ^ (k + 1))
        ((N₁' * L ^ m₁) * L ^ (k + 1)) (y τ) →
      X' τ' = (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) '' X τ →
      NS'.O.jL τ' = NS.O.jL τ → NS'.Dom Y' τ') :
    ∃ e : {τ // NS.Dom Y τ} ≃ {τ' // NS'.Dom Y' τ'}, ∀ τ : {τ // NS.Dom Y τ},
      NS'.O.jL (e τ).1 = NS.O.jL τ.1 ∧ NS'.O.X₁f (e τ).1 = (NS.O.X₁f τ.1).image
        (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) ∧
      y' (e τ).1 = boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1)) (y τ.1) ∧
      X' (e τ).1 = (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) ''
        X τ.1 := by
  obtain ⟨e, he⟩ := domEquiv_generic_core (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1))
    ((N₁' * L ^ m₁) * L ^ (k + 1))) (AdmPairs L N₁ m₁ k d C.m₀ k) (AdmPairs L N₁' m₁ k d C'.m₀ k)
    (fun x => InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) NS.O.jL y X NS'.O.jL y' X' hB hB'
    (fun a ha b hb hab => boxMap_inj (hm' := hm) ha hb hab) (NS.Dom Y) (NS'.Dom Y') hAdm hAdm'
    hbox hdom
  refine ⟨e, fun τ => ⟨(he τ).2.2, ?_, (he τ).1, (he τ).2.1⟩⟩
  obtain ⟨h1, h2, h3⟩ := he τ
  rw [hX₁' (e τ).1, h3, h1, h2, hcov _ _ _ (hbox τ.1 τ.2), hX₁]


/-- **The partial index bijection of the old terms of two canonically pinned systems.**  For the
label `Y` in the box and `Y' = bm '' Y`, the old terms whose domains contain `Y` correspond to those
whose domains contain `Y'`, with the same level and the label cubes of the images.  `y X`, `y' X'` are
the witnesses of the canonical indexing; the hypotheses are the box geometry of the pairs
(`hAdm`, `hAdm'`, `hbox`), the covers of the images (`hcov`) and the correspondence of the domains
(`hdom`, `hdom'`, from `polyDom_boxMap_iff`). -/
theorem exists_domEquiv_of_canon
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (NS' : NewLevelSystem S' C' z' Jr')
    {F : CanonCover d L N₁ m₁ k ϱ NS.O.ϱ₁} {F' : CanonCover d L N₁' m₁ k ϱ NS'.O.ϱ₁}
    (y : NS.O.ι → CTorus d L N₁ m₁ (k + 1)) (X : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (y' : NS'.O.ι → CTorus d L N₁' m₁ (k + 1)) (X' : NS'.O.ι → Set (CTorus d L N₁' m₁ (k + 1)))
    (hB : Set.BijOn (fun τ => (NS.O.jL τ, y τ, X τ)) Set.univ (AdmPairs L N₁ m₁ k d C.m₀ k))
    (hB' : Set.BijOn (fun τ => (NS'.O.jL τ, y' τ, X' τ)) Set.univ (AdmPairs L N₁' m₁ k d C'.m₀ k))
    (hX₁ : ∀ τ, NS.O.X₁f τ = F.X₁fC (NS.O.jL τ) (y τ) (X τ))
    (hX₁' : ∀ τ, NS'.O.X₁f τ = F'.X₁fC (NS'.O.jL τ) (y' τ) (X' τ))
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Y' : Set (CTorus d L N₁' m₁ (k + 1)))
    {R : ℕ} (hm : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hAdm : ∀ τ, NS.Dom Y τ → (NS.O.jL τ, boxMap ((N₁ * L ^ m₁) * L ^ (k + 1))
        ((N₁' * L ^ m₁) * L ^ (k + 1)) (y τ), (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1))
        ((N₁' * L ^ m₁) * L ^ (k + 1))) '' X τ) ∈ AdmPairs L N₁' m₁ k d C'.m₀ k)
    (hAdm' : ∀ τ', NS'.Dom Y' τ' → ∃ τ, y' τ' = boxMap ((N₁ * L ^ m₁) * L ^ (k + 1))
        ((N₁' * L ^ m₁) * L ^ (k + 1)) (y τ) ∧ X' τ' = (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1))
        ((N₁' * L ^ m₁) * L ^ (k + 1))) '' X τ ∧ NS'.O.jL τ' = NS.O.jL τ)
    (hbox : ∀ τ, NS.Dom Y τ → ∀ x ∈ insert (y τ) (X τ),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hcov : ∀ j y₀ X₀, (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      F'.X₁fC j (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1)) y₀)
        ((boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) '' X₀) =
      (F.X₁fC j y₀ X₀).image (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1))
        ((N₁' * L ^ m₁) * L ^ (k + 1))))
    (hdom : ∀ τ τ', NS.Dom Y τ → y' τ' = boxMap ((N₁ * L ^ m₁) * L ^ (k + 1))
        ((N₁' * L ^ m₁) * L ^ (k + 1)) (y τ) →
      X' τ' = (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) '' X τ →
      NS'.O.jL τ' = NS.O.jL τ → NS'.Dom Y' τ')
    (hdom' : ∀ τ τ', NS'.Dom Y' τ' → y' τ' = boxMap ((N₁ * L ^ m₁) * L ^ (k + 1))
        ((N₁' * L ^ m₁) * L ^ (k + 1)) (y τ) →
      X' τ' = (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) '' X τ →
      NS'.O.jL τ' = NS.O.jL τ → NS.Dom Y τ) :
    ∃ e : {τ // NS.Dom Y τ} ≃ {τ' // NS'.Dom Y' τ'}, ∀ τ : {τ // NS.Dom Y τ},
      NS'.O.jL (e τ).1 = NS.O.jL τ.1 ∧ NS'.O.X₁f (e τ).1 = (NS.O.X₁f τ.1).image
        (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) := by
  obtain ⟨e, he⟩ := exists_domEquiv_of_canon_core NS NS' y X y' X' hB hB' hX₁ hX₁' Y Y' hm hAdm
    (fun τ' hτ' => by
      obtain ⟨τ, h1, h2, h3⟩ := hAdm' τ' hτ'
      exact ⟨τ, hdom' τ τ' hτ' h1 h2 h3, h1, h2, h3⟩) hbox hcov hdom
  exact ⟨e, fun τ => ⟨(he τ).1, (he τ).2.1⟩⟩

end Balaban.Inhabited
