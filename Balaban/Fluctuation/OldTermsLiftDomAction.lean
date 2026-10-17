/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftDomGeom

/-!
# The action and the sources of the background problem on a transported generating set

Under the relabeling `oldTorusEquiv` and an equivalence `e` of the sites of `Ω₁`, the source, the
block averages, the extension `φ̄` and the action of the variational problem on `liftOldGS G`
agree with those on `G`.  Hence the real minimizers correspond.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The sites of `Ω₁` of the old and the new generating set are in bijection through the physical
relabeling. -/
theorem exists_Ω_one_equiv (G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ) :
    ∃ e : G.Ω 1 ≃ (liftOldGS G).Ω 1,
      ∀ x, (e x : CTorus d L N₁ m₁ (k + 1)) = oldTorusEquiv (x : CTorus d L (L * N₁) m₁ k) :=
  ⟨Equiv.subtypeEquiv oldTorusEquiv (fun x => (liftOldGS_mem_Ω_le G (by omega) x).symm),
    fun _ => rfl⟩

variable {G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ}
  (e : G.Ω 1 ≃ (liftOldGS G).Ω 1)
  (he : ∀ x, (e x : CTorus d L N₁ m₁ (k + 1)) = oldTorusEquiv x)

include he

theorem liftOldGS_qStar (a : ℕ → ℝ) (Ψ : CTorus d L (L * N₁) m₁ k → Fin N → ℂ)
    (Ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (hΨ : ∀ x, Ψ' (oldTorusEquiv x) = Ψ x)
    (x : G.Ω 1) (i : Fin N) :
    qStar (liftOldGS G) a Ψ' (e x, i) = qStar G a Ψ (x, i) := by
  simp only [qStar, he, liftOldGS_layerIndex_all, hΨ]

theorem liftOldGS_boundaryTerm (Ψ : CTorus d L (L * N₁) m₁ k → Fin N → ℂ)
    (Ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (hΨ : ∀ x, Ψ' (oldTorusEquiv x) = Ψ x)
    (x : G.Ω 1) (i : Fin N) :
    boundaryTerm (liftOldGS G) Ψ' (e x, i) = boundaryTerm G Ψ (x, i) := by
  simp only [boundaryTerm, he, ← oldTorusEquiv_single, ← oldTorusEquiv_add, ← oldTorusEquiv_sub,
    liftOldGS_mem_collar, hΨ]

theorem liftOldGS_source (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (D' : BgData (liftOldGS G) N)
    (hΨ : ∀ x, D'.Ψ (oldTorusEquiv x) = D.Ψ x) (hh : ∀ x, D'.h (oldTorusEquiv x) = D.h x)
    (x : G.Ω 1) (i : Fin N) :
    source (liftOldGS G) a ν D' (e x, i) = source G a ν D (x, i) := by
  simp only [source, liftOldGS_qStar e he a D.Ψ D'.Ψ hΨ, liftOldGS_boundaryTerm e he D.Ψ D'.Ψ hΨ,
    he, hh]

omit he in
theorem layerIndex_le_k (x : CTorus d L (L * N₁) m₁ k) : G.layerIndex x ≤ k := by
  by_cases hx : x ∈ G.Ω 1
  · exact (G.layerIndex_spec hx).2.1
  · rw [layerIndex_of_not_mem G hx]; exact Nat.zero_le _

theorem liftOldGS_svec {φ : G.Ω 1 × Fin N → ℂ} {φ' : (liftOldGS G).Ω 1 × Fin N → ℂ}
    (hφ : ∀ x i, φ' (e x, i) = φ (x, i)) (y : CTorus d L (L * N₁) m₁ k) (i : Fin N) :
    svec (liftOldGS G) φ' (oldTorusEquiv y) i = svec G φ y i := by
  by_cases hy : y ∈ G.Ω 1
  · have hy' : oldTorusEquiv y ∈ (liftOldGS G).Ω 1 := (liftOldGS_mem_Ω_le G (by omega) y).2 hy
    have h1 := svec_of_mem G φ ⟨y, hy⟩ i
    have h2 := svec_of_mem (liftOldGS G) φ' ⟨oldTorusEquiv y, hy'⟩ i
    have h3 : (⟨oldTorusEquiv y, hy'⟩ : (liftOldGS G).Ω 1) = e ⟨y, hy⟩ := Subtype.ext (he ⟨_, _⟩).symm
    rw [h3] at h2
    have he' : (e ⟨y, hy⟩ : CTorus d L N₁ m₁ (k + 1)) = oldTorusEquiv y := he ⟨y, hy⟩
    rw [he'] at h2
    simp only at h1
    rw [h2, h1, hφ]
  · have hy' : oldTorusEquiv y ∉ (liftOldGS G).Ω 1 := by
      rwa [liftOldGS_mem_Ω_le G (by omega)]
    rw [svec_of_not_mem _ _ hy', svec_of_not_mem _ _ hy]

theorem liftOldGS_blockAvg {φ : G.Ω 1 × Fin N → ℂ} {φ' : (liftOldGS G).Ω 1 × Fin N → ℂ}
    (hφ : ∀ x i, φ' (e x, i) = φ (x, i)) (x : CTorus d L (L * N₁) m₁ k) (i : Fin N) :
    blockAvg (liftOldGS G) φ' (oldTorusEquiv x) i = blockAvg G φ x i := by
  unfold blockAvg
  rw [liftOldGS_layerIndex_all, liftOldGS_sum_blk G (layerIndex_le_k x)]
  simp only [liftOldGS_svec e he hφ]

theorem liftOldGS_barField {Ψ : CTorus d L (L * N₁) m₁ k → Fin N → ℂ}
    {Ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hΨ : ∀ x, Ψ' (oldTorusEquiv x) = Ψ x)
    {φ : G.Ω 1 × Fin N → ℂ} {φ' : (liftOldGS G).Ω 1 × Fin N → ℂ}
    (hφ : ∀ x i, φ' (e x, i) = φ (x, i)) (x : CTorus d L (L * N₁) m₁ k) (i : Fin N) :
    barField (liftOldGS G) Ψ' φ' (oldTorusEquiv x) i = barField G Ψ φ x i := by
  unfold barField
  by_cases hx : x ∈ G.Ω 1
  · have hx' : oldTorusEquiv x ∈ (liftOldGS G).Ω 1 := (liftOldGS_mem_Ω_le G (by omega) x).2 hx
    have h3 : (⟨oldTorusEquiv x, hx'⟩ : (liftOldGS G).Ω 1) = e ⟨x, hx⟩ := Subtype.ext (he ⟨_, _⟩).symm
    simp only [hx, hx', dite_true, h3, hφ]
  · have hx' : oldTorusEquiv x ∉ (liftOldGS G).Ω 1 := by
      rwa [liftOldGS_mem_Ω_le G (by omega)]
    simp only [hx, hx', dite_false, hΨ]

theorem liftOldGS_action (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (D' : BgData (liftOldGS G) N)
    (hΨ : ∀ x, D'.Ψ (oldTorusEquiv x) = D.Ψ x) (hh : ∀ x, D'.h (oldTorusEquiv x) = D.h x)
    {φ : G.Ω 1 × Fin N → ℂ} {φ' : (liftOldGS G).Ω 1 × Fin N → ℂ}
    (hφ : ∀ x i, φ' (e x, i) = φ (x, i)) :
    action (liftOldGS G) a ν D' φ' = action G a ν D φ := by
  unfold action
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · congr 1
    refine (Fintype.sum_equiv e _ _ fun x => ?_).symm
    simp only [he, liftOldGS_layerIndex_all, hΨ, liftOldGS_blockAvg e he hφ]
  · congr 1
    refine (Fintype.sum_equiv oldTorusEquiv _ _ fun x => ?_).symm
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [← oldTorusEquiv_single, ← oldTorusEquiv_add, liftOldGS_mem_Ω_le G (show 1 ≤ k + 1 by omega),
      liftOldGS_barField e he hΨ hφ]
  · congr 1
    refine (Fintype.sum_equiv e _ _ fun x => ?_).symm
    simp only [he, hφ, hh]

omit he in
theorem liftOldGS_isReal_iff (D : BgData G N) (D' : BgData (liftOldGS G) N)
    (hΨ : ∀ x, D'.Ψ (oldTorusEquiv x) = D.Ψ x) (hh : ∀ x, D'.h (oldTorusEquiv x) = D.h x) :
    D'.IsReal ↔ D.IsReal := by
  constructor
  · intro h x i
    rw [← hΨ, ← hh]; exact h _ i
  · intro h x' i
    obtain ⟨x, rfl⟩ := oldTorusEquiv.surjective x'
    rw [hΨ, hh]; exact h x i

omit he in
theorem liftOldGS_isRealUnitField_iff {φ : G.Ω 1 × Fin N → ℂ} {φ' : (liftOldGS G).Ω 1 × Fin N → ℂ}
    (hφ : ∀ x i, φ' (e x, i) = φ (x, i)) :
    IsRealUnitField (liftOldGS G) φ' ↔ IsRealUnitField G φ := by
  unfold IsRealUnitField
  constructor
  · intro h x
    have := h (e x)
    simpa only [hφ] using this
  · intro h x'
    obtain ⟨x, rfl⟩ := e.surjective x'
    simpa only [hφ] using h x

theorem liftOldGS_isMinimizer_iff (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N)
    (D' : BgData (liftOldGS G) N)
    (hΨ : ∀ x, D'.Ψ (oldTorusEquiv x) = D.Ψ x) (hh : ∀ x, D'.h (oldTorusEquiv x) = D.h x)
    {φ : G.Ω 1 × Fin N → ℂ} {φ' : (liftOldGS G).Ω 1 × Fin N → ℂ}
    (hφ : ∀ x i, φ' (e x, i) = φ (x, i)) :
    IsMinimizer (liftOldGS G) a ν D' φ' ↔ IsMinimizer G a ν D φ := by
  unfold IsMinimizer
  rw [liftOldGS_isReal_iff D D' hΨ hh, liftOldGS_isRealUnitField_iff e hφ]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h σ hσ => ?_, fun h σ' hσ' => ?_⟩)
  · have hσ' : ∀ x i, (fun p : (liftOldGS G).Ω 1 × Fin N => σ (e.symm p.1, p.2)) (e x, i) =
        σ (x, i) := by intro x i; simp
    have key := h (fun p => σ (e.symm p.1, p.2)) ((liftOldGS_isRealUnitField_iff e hσ').2 hσ)
    rwa [liftOldGS_action e he a ν D D' hΨ hh hφ, liftOldGS_action e he a ν D D' hΨ hh hσ'] at key
  · have hσ : ∀ x i, σ' (e x, i) = (fun p : G.Ω 1 × Fin N => σ' (e p.1, p.2)) (x, i) := fun _ _ => rfl
    have key := h (fun p => σ' (e p.1, p.2)) ((liftOldGS_isRealUnitField_iff e hσ).1 hσ')
    rwa [← liftOldGS_action e he a ν D D' hΨ hh hφ, ← liftOldGS_action e he a ν D D' hΨ hh hσ] at key

end Balaban.Fluctuation
