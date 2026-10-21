/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftPoly

/-!
# Basic class geometry under the old torus equivalence

The physical-site equivalence identifies the old and successor descriptions of each
polymer. The top layer added by `liftOldGS` is empty.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- Two generating sets with the same layers are equal. -/
theorem gs_eq_of_Ω_eq {N₀ K : ℕ} [NeZero N₀]
    {G H : GeneratingSet d L N₀ K ϱ} (hΩ : G.Ω = H.Ω) : G = H := by
  cases G with
  | mk Ω top subset blockUnion separation =>
    cases H with
    | mk Ω' top' subset' blockUnion' separation' =>
      cases hΩ
      rfl

/-- The whole-lattice generating set at an inherited level is the lifted old one. -/
theorem liftOldGS_levelGS {j : ℕ} (hjk : j ≤ k) :
    liftOldGS (levelGS (d := d) (L := L) (N₁ := L * N₁) (m₁ := m₁)
      (k := k) (ϱ := ϱ) j hjk) =
      levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) j (Nat.le_succ_of_le hjk) := by
  apply gs_eq_of_Ω_eq
  funext i
  ext x
  by_cases hij : i ≤ j
  · have hik : i ≤ k := hij.trans hjk
    simp [liftOldGS_Ω, hik, levelGS, hij, liftOldSites]
  · by_cases hik : i ≤ k
    · simp [liftOldGS_Ω, hik, levelGS, hij, liftOldSites]
    · simp [liftOldGS, hik, levelGS, hij]

/-- The inherited generating set retains the strong specification on a transported polymer. -/
theorem liftOldGS_gsStrong {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (CTorus d L (L * N₁) m₁ k)}
    {G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ}
    (hG : GsSpecStrong j hjk X G) :
    GsSpecStrong j (Nat.le_succ_of_le hjk) (liftOldPoly X) (liftOldGS G) := by
  apply GsSpecCore.toStrong hj1 (Nat.le_succ_of_le hjk)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact (liftOldGS_mem_Ω G (hj1.trans hjk) z).2 (hG.subset hz)
  · intro i hji
    by_cases hik : i ≤ k
    · rw [liftOldGS_Ω G hik, hG.noAbove i hji]
      simp [liftOldSites]
    · simp [liftOldGS, hik]
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact (liftOldGS_mem_layer G hjk x).2 (hG.topLayer x hx)

/-- The `IsSF2.gsStrong` clause of inherited terms needs no field-domain comparison. -/
theorem liftOldTerms_gsStrong {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ}
    {Dom : FieldDom d L (L * N₁) m₁ k N ϱ}
    {Tm : Terms d L (L * N₁) m₁ k N ϱ}
    {ρ : (CTorus d L (L * N₁) m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
      (CTorus d L (L * N₁) m₁ k → Fin N → ℝ) → ℝ} {Ek : ℝ}
    (h : IsSF2 P Rg β a Dom Tm ρ Ek) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ (k + 1))} (hX : IsPolyDom P.m₀ j X) :
    GsSpecStrong j (Nat.le_succ_of_le hjk) X ((liftOldTerms Tm).gs j X) := by
  have hback : IsPolyDom (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k)
      P.m₀ j (oldTorusEquiv.symm '' X) := by
    apply (oldTorusEquiv_isPolyDom_iff (N₁ := N₁) (m₁ := m₁) (k := k)).2
    simpa [liftOldPoly, Set.image_image] using hX
  have hstrong := liftOldGS_gsStrong hj1 hjk (h.gsStrong j hj1 hjk _ hback)
  simpa [liftOldTerms, liftOldPoly, Set.image_image] using hstrong

/-- The polymer indexing set of `Eloc` and `Mloc` is transported by the site equivalence. -/
theorem liftOldPoly_mem_polysAt {m₀ j : ℕ}
    {y : CTorus d L (L * N₁) m₁ k}
    {X : Set (CTorus d L (L * N₁) m₁ k)} :
    X ∈ polysAt (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) m₀ j y ↔
      liftOldPoly X ∈ polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
        m₀ j (oldTorusEquiv y) := by
  simp only [polysAt, Set.mem_ofPred_eq, oldTorusEquiv_isPolyDom_iff,
    mem_liftOldPoly]
  simp

/-- Transport gives a bijection between polymers through corresponding sites. -/
theorem liftOldPoly_polysAt_eq {m₀ j : ℕ}
    (y : CTorus d L (L * N₁) m₁ k) :
    polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) m₀ j
        (oldTorusEquiv y) =
      liftOldPoly '' polysAt (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) m₀ j y := by
  ext Y
  constructor
  · intro hY
    refine ⟨oldTorusEquiv.symm '' Y, ?_, ?_⟩
    · apply (liftOldPoly_mem_polysAt (y := y)).2
      simpa [liftOldPoly, Set.image_image] using hY
    · simp [liftOldPoly, Set.image_image]
  · rintro ⟨X, hX, rfl⟩
    exact (liftOldPoly_mem_polysAt (y := y)).1 hX

omit [NeZero L] [NeZero N₁] in
private theorem liftOldPoly_injective :
    Function.Injective (liftOldPoly (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) := by
  intro X Y h
  have h' := congrArg (Set.image oldTorusEquiv.symm) h
  simpa [liftOldPoly, Set.image_image] using h'

/-- The local energy sum of inherited terms is the old sum on the physical torus. -/
theorem liftOldTerms_Eloc (m₀ j : ℕ) (Tm : Terms d L (L * N₁) m₁ k N ϱ)
    (y : CTorus d L (L * N₁) m₁ k)
    (Ψ h : Fld d L N₁ m₁ (k + 1) N) :
    Eloc m₀ (liftOldTerms Tm) j (oldTorusEquiv y) Ψ h =
      Eloc m₀ Tm j y (lowerNewField Ψ) (lowerNewField h) := by
  unfold Eloc
  rw [liftOldPoly_polysAt_eq y]
  have hinj : Set.InjOn liftOldPoly
      (polysAt (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) m₀ j y) :=
    fun _ _ _ _ hXY => liftOldPoly_injective hXY
  rw [finsum_mem_image (g := liftOldPoly) (f := fun Y =>
    (liftOldTerms Tm).E j (oldTorusEquiv y) Y Ψ h) hinj]
  apply finsum_mem_congr rfl
  intro X _
  rw [liftOldTerms_E]
  simp [liftOldPoly, Set.image_image]

/-- The local observable sum of inherited terms is the old sum on the physical torus. -/
theorem liftOldTerms_Mloc (m₀ j : ℕ) (Tm : Terms d L (L * N₁) m₁ k N ϱ)
    (x : CTorus d L (L * N₁) m₁ k)
    (Ψ h g : Fld d L N₁ m₁ (k + 1) N) :
    Mloc m₀ (liftOldTerms Tm) j (oldTorusEquiv x) Ψ h g =
      Mloc m₀ Tm j x (lowerNewField Ψ) (lowerNewField h) (lowerNewField g) := by
  unfold Mloc
  rw [liftOldPoly_polysAt_eq x]
  have hinj : Set.InjOn liftOldPoly
      (polysAt (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) m₀ j x) :=
    fun _ _ _ _ hXY => liftOldPoly_injective hXY
  rw [finsum_mem_image (g := liftOldPoly) (f := fun Y =>
    (liftOldTerms Tm).M j (oldTorusEquiv x) Y Ψ h g) hinj]
  apply finsum_mem_congr rfl
  intro X _
  rw [liftOldTerms_M]
  simp [liftOldPoly, Set.image_image]

/- The one-scale polymer size uses only the physical torus and the unchanged cell side. -/
omit [NeZero L] [NeZero N₁] in
theorem liftOldPoly_sizeJ (m₀ j : ℕ)
    (X : Set (CTorus d L (L * N₁) m₁ k)) :
    sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) m₀ j (liftOldPoly X) =
      sizeJ (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) m₀ j X := by
  let F : (n : ℕ) → Set (Torus d n) → ℝ := fun n Y =>
    sInf {c : ℝ | ∃ (𝒦 : Set (Torus d n)) (W : Finset (Torus d n))
        (E : Finset (Torus d n × Torus d n)),
      ((∀ b ∈ 𝒦, Aligned (cellSide L m₀ m₁ j) b ∧
          box b (L * cellSide L m₀ m₁ j) ⊆ Y) ∧
        ∀ z ∈ Y, ∃ b ∈ 𝒦, z ∈ box b (L * cellSide L m₀ m₁ j)) ∧
      ConnStruct W E ∧ (↑W ⊆ Y) ∧
      (∀ b ∈ 𝒦, ∃ x ∈ W, x ∈ box b (L * cellSide L m₀ m₁ j)) ∧
      c = bondCost (scaleW L m₀ m₁ j) E}
  have hF : ∀ {n n' : ℕ} (h : n = n') (Y : Set (Torus d n)),
      F n' (castT h '' Y) = F n Y := by
    intro n n' h Y
    cases h
    have hc : (castT (d := d) (rfl : n = n)) = (id : Torus d n → Torus d n) := rfl
    rw [hc, Set.image_id]
  change F ((N₁ * L ^ m₁) * L ^ (k + 1)) (liftOldPoly X) =
    F (((L * N₁) * L ^ m₁) * L ^ k) X
  rw [liftOldPoly, show (oldTorusEquiv : CTorus d L (L * N₁) m₁ k →
      CTorus d L N₁ m₁ (k + 1)) =
      castT (oldSide_eq_newSide (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) from
        funext oldTorusEquiv_apply]
  exact hF oldSide_eq_newSide X

end Balaban.Fluctuation
