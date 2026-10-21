/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelClassE
public import Balaban.Polymer.PolyDomBoxMap

/-!
# The partial index bijection of the old terms of two canonically pinned systems, in the box

`domEquiv_of_canon_box`: for a label `Y` in the box and its image under `boxMap`, the old terms whose
domains contain `Y` correspond to those whose domains contain the image, with labels, levels and
label cubes the images under `boxMap`.
-/

@[expose] public section
namespace Balaban.Inhabited

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Polymer Balaban.Polymer.TwoTorusStep Balaban.Multiscale Balaban.Background
  Balaban.Inhabited.LevelStep

section Cover

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- The label cubes of an old term lie in every domain of its expansion. -/
theorem x1f_subset_of_mem_polyDom {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 G m₀ j 𝒦X)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : Y ∈ polyDom G X₁f m₀ j 𝒦X) :
    (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ Y := by
  rw [hX₁]
  exact subset_of_mem_polymerDomains hY

/-- **The polymer and the cover of a pair lie in the box when the pair lies in the domain of a label
of the box.** -/
theorem insert_subset_box_of_dom {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr) {F : CanonCover d L N₁ m₁ k ϱ NS.O.ϱ₁}
    {y : NS.O.ι → CTorus d L N₁ m₁ (k + 1)} {X : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hB : Set.BijOn (fun τ => (NS.O.jL τ, y τ, X τ)) Set.univ (AdmPairs L N₁ m₁ k d C.m₀ k))
    (hX₁ : ∀ τ, NS.O.X₁f τ = F.X₁fC (NS.O.jL τ) (y τ) (X τ))
    (hcX : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      insert y₀ X₀ ⊆ ↑(F.X₁fC j y₀ X₀))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} {R : ℕ}
    (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) {τ : NS.O.ι} (hτ : NS.Dom Y τ) :
    ∀ x ∈ insert (y τ) (X τ), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
  intro x hx
  have h1 := hcX _ _ _ (hB.mapsTo (Set.mem_univ τ)) hx
  rw [← hX₁ τ] at h1
  exact hYR x (x1f_subset_of_mem_polyDom (NS.OS.hX₁ τ) hτ (Finset.mem_coe.2 h1))

end Cover


section Iff

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))

/-- **The domains of corresponding old terms correspond under `boxMap`**, from the correspondence of
the label cubes. -/
theorem canonDom_iff
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (hGA : S.G' = levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) le_rfl)
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (hGB : S'.G' = levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) le_rfl)
    (NS' : NewLevelSystem S' C' z' Jr')
    (hm₀' : NS'.O.m₀ = NS.O.m₀) {R₂ : ℕ}
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYR : ∀ x ∈ Y, InBox d R₂ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (τ : NS.O.ι) (τ' : NS'.O.ι) (h3 : NS'.O.jL τ' = NS.O.jL τ)
    (hXi : NS'.O.X₁f τ' = (NS.O.X₁f τ).image bm)
    (hbxF : ∀ x ∈ NS.O.X₁f τ, InBox d R₂ ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    NS'.Dom (bm '' Y) τ' ↔ NS.Dom Y τ := by
  have hN : L ^ NS.O.m₀ ∣ N₁ := NS.OS.hN
  have hN' : L ^ NS.O.m₀ ∣ N₁' := by
    have := NS'.OS.hN
    rwa [hm₀'] at this
  have hX₁t := NS'.OS.hX₁ τ'
  have hX₁s := NS.OS.hX₁ τ
  rw [hm₀', h3, hGB] at hX₁t
  rw [hGA] at hX₁s
  have key := polyDom_boxMap_iff (N₁ := N₁) (N₁' := N₁') (ρ := R₂) (m₀ := NS.O.m₀)
    (jt := NS.O.jL τ) (k := k) (ϱ := ϱ) hN hN' hn hn' (Nat.succ_pos k) hX₁s hX₁t hXi hbxF
    (Y := Y) hYR
  unfold NewLevelSystem.Dom
  rw [hm₀', h3, hGB, hGA]
  exact key

/-- **The label cubes of corresponding terms correspond**, and those of the term of the box lie in
the box of radius `R₂`. -/
theorem canon_cover_corr
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (NS' : NewLevelSystem S' C' z' Jr')
    {F : CanonCover d L N₁ m₁ k ϱ NS.O.ϱ₁} {F' : CanonCover d L N₁' m₁ k ϱ NS'.O.ϱ₁}
    {y : NS.O.ι → CTorus d L N₁ m₁ (k + 1)} {X : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    {y' : NS'.O.ι → CTorus d L N₁' m₁ (k + 1)} {X' : NS'.O.ι → Set (CTorus d L N₁' m₁ (k + 1))}
    (hB : Set.BijOn (fun τ => (NS.O.jL τ, y τ, X τ)) Set.univ (AdmPairs L N₁ m₁ k d C.m₀ k))
    (hX₁ : ∀ τ, NS.O.X₁f τ = F.X₁fC (NS.O.jL τ) (y τ) (X τ))
    (hX₁' : ∀ τ, NS'.O.X₁f τ = F'.X₁fC (NS'.O.jL τ) (y' τ) (X' τ)) {R R₂ : ℕ}
    (hcloc : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      ∀ x ∈ F.X₁fC j y₀ X₀, InBox d R₂ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hcov : ∀ j y₀ X₀, (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      F'.X₁fC j (bm y₀) (bm '' X₀) = (F.X₁fC j y₀ X₀).image bm)
    (τ : NS.O.ι) (τ' : NS'.O.ι)
    (hbx : ∀ x ∈ insert (y τ) (X τ), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (h1 : y' τ' = bm (y τ)) (h2 : X' τ' = bm '' X τ) (h3 : NS'.O.jL τ' = NS.O.jL τ) :
    NS'.O.X₁f τ' = (NS.O.X₁f τ).image bm ∧
      ∀ x ∈ NS.O.X₁f τ, InBox d R₂ ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [hX₁' τ', h1, h2, h3, hcov _ _ _ hbx, ← hX₁ τ]
  · rw [hX₁ τ] at hx
    exact hcloc _ _ _ (hB.mapsTo (Set.mem_univ τ)) hbx x hx

theorem cellSide_le_of_le {m₀ m₁ j j' : ℕ} (h : j ≤ j') :
    cellSide L m₀ m₁ j ≤ cellSide L m₀ m₁ j' :=
  Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)

/-- **A pair of the box goes to a pair of the second torus** (the pairs `(j, y, X)` of the index set
of the old terms: aligned `y ∈ X`, `X` a polymer). -/
theorem admPairs_image {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {R : ℕ}
    (hr : 2 * R + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hr' : 2 * R + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ (k + 1))
    {y : CTorus d L N₁ m₁ (k + 1)} {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (h : (j, y, X) ∈ AdmPairs L N₁ m₁ k d m₀ k)
    (hbx : ∀ x ∈ insert y X, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    (j, boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1)) y,
      boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1)) '' X) ∈
      AdmPairs L N₁' m₁ k d m₀ k := by
  obtain ⟨hj1, hjk, hal, hpoly, hyX⟩ := h
  have hd₁ : L ^ j ∣ (N₁ * L ^ m₁) * L ^ (k + 1) :=
    Dvd.dvd.mul_left (pow_dvd_pow L (by omega)) _
  have hd₂ : L ^ j ∣ (N₁' * L ^ m₁) * L ^ (k + 1) :=
    Dvd.dvd.mul_left (pow_dvd_pow L (by omega)) _
  exact ⟨hj1, hjk, aligned_boxMap hd₁ hd₂ hal,
    isPolyDom_image hN hN' (by omega) hr hr' (fun x hx => hbx x (Set.mem_insert_of_mem _ hx)) hpoly,
    ⟨y, hyX, rfl⟩⟩


/-- **A pair of the second torus whose image lies in the box has a preimage pair in the box.** -/
theorem canon_back
    {m₀ : ℕ} {ι ι' : Type*} {jL : ι → ℕ} {y : ι → CTorus d L N₁ m₁ (k + 1)}
    {X : ι → Set (CTorus d L N₁ m₁ (k + 1))} {jL' : ι' → ℕ} {y' : ι' → CTorus d L N₁' m₁ (k + 1)}
    {X' : ι' → Set (CTorus d L N₁' m₁ (k + 1))} {m₀' : ℕ} (hm₀ : m₀' = m₀)
    (hB : Set.BijOn (fun τ => (jL τ, y τ, X τ)) Set.univ (AdmPairs L N₁ m₁ k d m₀ k))
    (hB' : Set.BijOn (fun τ => (jL' τ, y' τ, X' τ)) Set.univ (AdmPairs L N₁' m₁ k d m₀' k))
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {R : ℕ}
    (hm₁ : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hr₁ : ∀ j, j ≤ k → 2 * R + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hr₂ : ∀ j, j ≤ k → 2 * R + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ (k + 1))
    (τ' : ι')
    (hbx' : ∀ x ∈ insert (y' τ') (X' τ'), InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) x) :
    ∃ τ, (∀ x ∈ insert (y τ) (X τ), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) ∧
      y' τ' = bm (y τ) ∧ X' τ' = bm '' X τ ∧ jL' τ' = jL τ := by
  have hadm' : (jL' τ', y' τ', X' τ') ∈ AdmPairs L N₁' m₁ k d m₀ k := by
    have := hB'.mapsTo (Set.mem_univ τ')
    rwa [hm₀] at this
  have hjk : jL' τ' ≤ k := hadm'.2.1
  have hp := admPairs_image (N₁ := N₁') (N₁' := N₁) (m₀ := m₀) (j := jL' τ') hN' hN
    (hr₂ _ hjk) (hr₁ _ hjk) hadm' hbx'
  obtain ⟨τ, -, hτe⟩ := hB.surjOn hp
  simp only [Prod.mk.injEq] at hτe
  obtain ⟨hj, hy, hX⟩ := hτe
  have hy1 : y' τ' = bm (y τ) := by
    rw [hy, boxMap_boxMap hm₁ (hbx' _ (Set.mem_insert _ _))]
  have hX1 : X' τ' = bm '' X τ := by
    rw [hX]
    exact (image_image_boxMap (n' := (N₁ * L ^ m₁) * L ^ (k + 1)) hm₁
      (fun x hx => hbx' x (Set.mem_insert_of_mem _ hx))).symm
  refine ⟨τ, ?_, hy1, hX1, hj.symm⟩
  intro x hx
  rcases hx with rfl | hx
  · rw [hy]; exact inBox_boxMap hm₁ (hbx' _ (Set.mem_insert _ _))
  · rw [hX] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact inBox_boxMap hm₁ (hbx' w (Set.mem_insert_of_mem _ hw))

/-- **The pairs of the terms of the domains of a label of the box go to pairs of the second torus.** -/
theorem canon_dom_fwd
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr)
    {C' : StepClass d L N₁' m₁ k N ϱ}
    {F : CanonCover d L N₁ m₁ k ϱ NS.O.ϱ₁}
    {y : NS.O.ι → CTorus d L N₁ m₁ (k + 1)} {X : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hB : Set.BijOn (fun τ => (NS.O.jL τ, y τ, X τ)) Set.univ (AdmPairs L N₁ m₁ k d C.m₀ k))
    (hX₁ : ∀ τ, NS.O.X₁f τ = F.X₁fC (NS.O.jL τ) (y τ) (X τ))
    (hm₀ : NS.O.m₀ = C.m₀) (hC : C'.m₀ = C.m₀) (hN' : L ^ C.m₀ ∣ N₁')
    (hcX : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      insert y₀ X₀ ⊆ ↑(F.X₁fC j y₀ X₀))
    {R R₂ : ℕ} (hR : R ≤ R₂)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (τ : NS.O.ι) (hτ : NS.Dom Y τ) :
    (NS.O.jL τ, boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1)) (y τ),
      boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1)) '' X τ) ∈
      AdmPairs L N₁' m₁ k d C'.m₀ k := by
  have hLK : 0 < L * cellSide L NS.O.m₀ m₁ (k + 1) :=
    Nat.mul_pos (NeZero.pos L) (cellSide_pos NS.O.m₀ m₁ (k + 1))
  have hN : L ^ C.m₀ ∣ N₁ := by have := NS.OS.hN; rwa [hm₀] at this
  have hrr : ∀ j, j ≤ k → L * cellSide L C.m₀ m₁ j ≤ L * cellSide L NS.O.m₀ m₁ (k + 1) := by
    intro j hj
    rw [hm₀]
    exact Nat.mul_le_mul_left L (cellSide_le_of_le (by omega))
  have hjk : NS.O.jL τ ≤ k := (hB.mapsTo (Set.mem_univ τ)).2.1
  have hrj := hrr _ hjk
  have := admPairs_image (N₁' := N₁') (m₀ := C.m₀) (j := NS.O.jL τ) hN hN'
    (by omega) (by omega) (hB.mapsTo (Set.mem_univ τ))
    (insert_subset_box_of_dom NS hB hX₁ hcX hYR hτ)
  rwa [hC]

/-- **A term of the second torus whose domain contains the image of a label of the box is the
image of a term whose domain contains the label.** -/
theorem canon_dom_back
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (hGA : S.G' = levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) le_rfl)
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (hGB : S'.G' = levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) le_rfl)
    (NS' : NewLevelSystem S' C' z' Jr')
    {F : CanonCover d L N₁ m₁ k ϱ NS.O.ϱ₁} {F' : CanonCover d L N₁' m₁ k ϱ NS'.O.ϱ₁}
    {y : NS.O.ι → CTorus d L N₁ m₁ (k + 1)} {X : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    {y' : NS'.O.ι → CTorus d L N₁' m₁ (k + 1)} {X' : NS'.O.ι → Set (CTorus d L N₁' m₁ (k + 1))}
    (hB : Set.BijOn (fun τ => (NS.O.jL τ, y τ, X τ)) Set.univ (AdmPairs L N₁ m₁ k d C.m₀ k))
    (hB' : Set.BijOn (fun τ => (NS'.O.jL τ, y' τ, X' τ)) Set.univ (AdmPairs L N₁' m₁ k d C'.m₀ k))
    (hX₁ : ∀ τ, NS.O.X₁f τ = F.X₁fC (NS.O.jL τ) (y τ) (X τ))
    (hX₁' : ∀ τ, NS'.O.X₁f τ = F'.X₁fC (NS'.O.jL τ) (y' τ) (X' τ))
    (hm₀ : NS.O.m₀ = C.m₀) (hm₀' : NS'.O.m₀ = C'.m₀) (hC : C'.m₀ = C.m₀)
    (hcX' : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁' m₁ k d C'.m₀ k →
      insert y₀ X₀ ⊆ ↑(F'.X₁fC j y₀ X₀))
    {R R₂ : ℕ} (hR : R ≤ R₂)
    (hcloc : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      ∀ x ∈ F.X₁fC j y₀ X₀, InBox d R₂ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hcov : ∀ j y₀ X₀, (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      F'.X₁fC j (bm y₀) (bm '' X₀) = (F.X₁fC j y₀ X₀).image bm)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (τ' : NS'.O.ι) (hτ' : NS'.Dom (bm '' Y) τ') :
    ∃ τ, NS.Dom Y τ ∧ y' τ' = bm (y τ) ∧ X' τ' = bm '' X τ ∧ NS'.O.jL τ' = NS.O.jL τ := by
  have hLK : 0 < L * cellSide L NS.O.m₀ m₁ (k + 1) :=
    Nat.mul_pos (NeZero.pos L) (cellSide_pos NS.O.m₀ m₁ (k + 1))
  have hm₁ : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hm₂ : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hm₀e : NS'.O.m₀ = NS.O.m₀ := by rw [hm₀', hC, hm₀]
  have hN : L ^ C.m₀ ∣ N₁ := by have := NS.OS.hN; rwa [hm₀] at this
  have hN' : L ^ C.m₀ ∣ N₁' := by have := NS'.OS.hN; rwa [hm₀e, hm₀] at this
  have hrr : ∀ j, j ≤ k → L * cellSide L C.m₀ m₁ j ≤ L * cellSide L NS.O.m₀ m₁ (k + 1) := by
    intro j hj
    rw [hm₀]
    exact Nat.mul_le_mul_left L (cellSide_le_of_le (by omega))
  have hr₁ : ∀ j, j ≤ k → 2 * R + L * cellSide L C.m₀ m₁ j < (N₁ * L ^ m₁) * L ^ (k + 1) :=
    fun j hj => by have := hrr j hj; omega
  have hr₂ : ∀ j, j ≤ k → 2 * R + L * cellSide L C.m₀ m₁ j < (N₁' * L ^ m₁) * L ^ (k + 1) :=
    fun j hj => by have := hrr j hj; omega
  have hYR' : ∀ x ∈ bm '' Y, InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) x := by
    rintro _ ⟨x₀, hx₀, rfl⟩
    exact inBox_boxMap hm₂ (hYR x₀ hx₀)
  have hYR₂ : ∀ x ∈ Y, InBox d R₂ ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun x hx μ => (hYR x hx μ).trans (by exact_mod_cast hR)
  obtain ⟨τ, hbx, h1, h2, h3⟩ := canon_back (m₀ := C.m₀) (m₀' := C'.m₀) hC hB hB' hN hN' hm₁
    hr₁ hr₂ τ' (insert_subset_box_of_dom NS' hB' hX₁' hcX' hYR' hτ')
  obtain ⟨hXi, hbxF⟩ := canon_cover_corr NS NS' hB hX₁ hX₁' hcloc hcov τ τ' hbx h1 h2 h3
  exact ⟨τ, (canonDom_iff hGA NS hGB NS' hm₀e Y hYR₂ hn hn' τ τ' h3 hXi hbxF).1 hτ', h1, h2, h3⟩

/-- **The domains of corresponding terms correspond** (from the domain of the first). -/
theorem canon_dom_dom
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (hGA : S.G' = levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) le_rfl)
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (hGB : S'.G' = levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) le_rfl)
    (NS' : NewLevelSystem S' C' z' Jr')
    {F : CanonCover d L N₁ m₁ k ϱ NS.O.ϱ₁} {F' : CanonCover d L N₁' m₁ k ϱ NS'.O.ϱ₁}
    {y : NS.O.ι → CTorus d L N₁ m₁ (k + 1)} {X : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    {y' : NS'.O.ι → CTorus d L N₁' m₁ (k + 1)} {X' : NS'.O.ι → Set (CTorus d L N₁' m₁ (k + 1))}
    (hB : Set.BijOn (fun τ => (NS.O.jL τ, y τ, X τ)) Set.univ (AdmPairs L N₁ m₁ k d C.m₀ k))
    (hX₁ : ∀ τ, NS.O.X₁f τ = F.X₁fC (NS.O.jL τ) (y τ) (X τ))
    (hX₁' : ∀ τ, NS'.O.X₁f τ = F'.X₁fC (NS'.O.jL τ) (y' τ) (X' τ))
    (hm₀ : NS.O.m₀ = C.m₀) (hm₀' : NS'.O.m₀ = C'.m₀) (hC : C'.m₀ = C.m₀)
    (hcX : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      insert y₀ X₀ ⊆ ↑(F.X₁fC j y₀ X₀))
    {R R₂ : ℕ} (hR : R ≤ R₂)
    (hcloc : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      ∀ x ∈ F.X₁fC j y₀ X₀, InBox d R₂ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hcov : ∀ j y₀ X₀, (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      F'.X₁fC j (bm y₀) (bm '' X₀) = (F.X₁fC j y₀ X₀).image bm)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (τ : NS.O.ι) (τ' : NS'.O.ι) (hτ : NS.Dom Y τ) (h1 : y' τ' = bm (y τ))
    (h2 : X' τ' = bm '' X τ) (h3 : NS'.O.jL τ' = NS.O.jL τ) : NS'.Dom (bm '' Y) τ' := by
  have hLK : 0 < L * cellSide L NS.O.m₀ m₁ (k + 1) :=
    Nat.mul_pos (NeZero.pos L) (cellSide_pos NS.O.m₀ m₁ (k + 1))
  have hm₁ : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hm₂ : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hm₀e : NS'.O.m₀ = NS.O.m₀ := by rw [hm₀', hC, hm₀]
  have hN : L ^ C.m₀ ∣ N₁ := by have := NS.OS.hN; rwa [hm₀] at this
  have hN' : L ^ C.m₀ ∣ N₁' := by have := NS'.OS.hN; rwa [hm₀e, hm₀] at this
  have hrr : ∀ j, j ≤ k → L * cellSide L C.m₀ m₁ j ≤ L * cellSide L NS.O.m₀ m₁ (k + 1) := by
    intro j hj
    rw [hm₀]
    exact Nat.mul_le_mul_left L (cellSide_le_of_le (by omega))
  have hr₁ : ∀ j, j ≤ k → 2 * R + L * cellSide L C.m₀ m₁ j < (N₁ * L ^ m₁) * L ^ (k + 1) :=
    fun j hj => by have := hrr j hj; omega
  have hr₂ : ∀ j, j ≤ k → 2 * R + L * cellSide L C.m₀ m₁ j < (N₁' * L ^ m₁) * L ^ (k + 1) :=
    fun j hj => by have := hrr j hj; omega
  have hYR' : ∀ x ∈ bm '' Y, InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) x := by
    rintro _ ⟨x₀, hx₀, rfl⟩
    exact inBox_boxMap hm₂ (hYR x₀ hx₀)
  have hYR₂ : ∀ x ∈ Y, InBox d R₂ ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun x hx μ => (hYR x hx μ).trans (by exact_mod_cast hR)
  obtain ⟨hXi, hbxF⟩ := canon_cover_corr NS NS' hB hX₁ hX₁' hcloc hcov τ τ'
    (insert_subset_box_of_dom NS hB hX₁ hcX hYR hτ) h1 h2 h3
  exact (canonDom_iff hGA NS hGB NS' hm₀e Y hYR₂ hn hn' τ τ' h3 hXi hbxF).2 hτ

/-- **The partial index bijection of the old terms of two canonically pinned systems, in the box.**
For the label `Y` of the box of radius `R` and its image, the old terms whose domains contain `Y`
correspond to those whose domains contain `bm '' Y`: the labels, the levels and the label cubes of
corresponding terms are the images under `boxMap`.  Hypotheses: the pins; the cover of each pair
contains the polymer (`hcX`) and lies in the box of radius `R₂` when the polymer lies in that of
radius `R` (`hcloc`); the canonical covers of corresponding pairs correspond (`hcov`). -/
theorem domEquiv_of_canon_box
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (hGA : S.G' = levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) le_rfl)
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (hGB : S'.G' = levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) le_rfl)
    (NS' : NewLevelSystem S' C' z' Jr')
    {F : CanonCover d L N₁ m₁ k ϱ NS.O.ϱ₁} {F' : CanonCover d L N₁' m₁ k ϱ NS'.O.ϱ₁}
    (y : NS.O.ι → CTorus d L N₁ m₁ (k + 1)) (X : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (y' : NS'.O.ι → CTorus d L N₁' m₁ (k + 1)) (X' : NS'.O.ι → Set (CTorus d L N₁' m₁ (k + 1)))
    (hB : Set.BijOn (fun τ => (NS.O.jL τ, y τ, X τ)) Set.univ (AdmPairs L N₁ m₁ k d C.m₀ k))
    (hB' : Set.BijOn (fun τ => (NS'.O.jL τ, y' τ, X' τ)) Set.univ (AdmPairs L N₁' m₁ k d C'.m₀ k))
    (hX₁ : ∀ τ, NS.O.X₁f τ = F.X₁fC (NS.O.jL τ) (y τ) (X τ))
    (hX₁' : ∀ τ, NS'.O.X₁f τ = F'.X₁fC (NS'.O.jL τ) (y' τ) (X' τ))
    (hm₀ : NS.O.m₀ = C.m₀) (hm₀' : NS'.O.m₀ = C'.m₀) (hC : C'.m₀ = C.m₀)
    (hcX : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      insert y₀ X₀ ⊆ ↑(F.X₁fC j y₀ X₀))
    (hcX' : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁' m₁ k d C'.m₀ k →
      insert y₀ X₀ ⊆ ↑(F'.X₁fC j y₀ X₀))
    {R R₂ : ℕ} (hR : R ≤ R₂)
    (hcloc : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      ∀ x ∈ F.X₁fC j y₀ X₀, InBox d R₂ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hcov : ∀ j y₀ X₀, (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      F'.X₁fC j (bm y₀) (bm '' X₀) = (F.X₁fC j y₀ X₀).image bm)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    :
    ∃ e : {τ // NS.Dom Y τ} ≃ {τ' // NS'.Dom (bm '' Y) τ'}, ∀ τ : {τ // NS.Dom Y τ},
      NS'.O.jL (e τ).1 = NS.O.jL τ.1 ∧ NS'.O.X₁f (e τ).1 = (NS.O.X₁f τ.1).image bm ∧
      y' (e τ).1 = bm (y τ.1) ∧ X' (e τ).1 = bm '' X τ.1 := by
  have hLK : 0 < L * cellSide L NS.O.m₀ m₁ (k + 1) :=
    Nat.mul_pos (NeZero.pos L) (cellSide_pos NS.O.m₀ m₁ (k + 1))
  have hm₁ : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hm₂ : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hm₀e : NS'.O.m₀ = NS.O.m₀ := by rw [hm₀', hC, hm₀]
  have hN : L ^ C.m₀ ∣ N₁ := by have := NS.OS.hN; rwa [hm₀] at this
  have hN' : L ^ C.m₀ ∣ N₁' := by have := NS'.OS.hN; rwa [hm₀e, hm₀] at this
  have hrr : ∀ j, j ≤ k → L * cellSide L C.m₀ m₁ j ≤ L * cellSide L NS.O.m₀ m₁ (k + 1) := by
    intro j hj
    rw [hm₀]
    exact Nat.mul_le_mul_left L (cellSide_le_of_le (by omega))
  have hr₁ : ∀ j, j ≤ k → 2 * R + L * cellSide L C.m₀ m₁ j < (N₁ * L ^ m₁) * L ^ (k + 1) :=
    fun j hj => by have := hrr j hj; omega
  have hr₂ : ∀ j, j ≤ k → 2 * R + L * cellSide L C.m₀ m₁ j < (N₁' * L ^ m₁) * L ^ (k + 1) :=
    fun j hj => by have := hrr j hj; omega
  have hYR' : ∀ x ∈ bm '' Y, InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) x := by
    rintro _ ⟨x₀, hx₀, rfl⟩
    exact inBox_boxMap hm₂ (hYR x₀ hx₀)
  have hYR₂ : ∀ x ∈ Y, InBox d R₂ ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun x hx μ => (hYR x hx μ).trans (by exact_mod_cast hR)
  refine exists_domEquiv_of_canon_core NS NS' y X y' X' hB hB' hX₁ hX₁' Y (bm '' Y) hm₂ ?_ ?_
    (fun τ hτ => insert_subset_box_of_dom NS hB hX₁ hcX hYR hτ) hcov ?_
  · exact fun τ hτ => canon_dom_fwd NS hB hX₁ hm₀ hC hN' hcX hR Y hYR hn hn' τ hτ
  · exact fun τ' hτ' => canon_dom_back hGA NS hGB NS' hB hB' hX₁ hX₁' hm₀ hm₀' hC hcX' hR hcloc hcov Y hYR hn hn' τ' hτ'
  · exact fun τ τ' hτ h1 h2 h3 => canon_dom_dom hGA NS hGB NS' hB hX₁ hX₁' hm₀ hm₀' hC hcX hR hcloc hcov Y hYR hn hn' τ τ' hτ h1 h2 h3

end Iff

end Balaban.Inhabited
