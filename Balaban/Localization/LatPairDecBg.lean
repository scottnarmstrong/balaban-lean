/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.LatPairBg

/-!
# The decoupled background field and multiplier between two generating sets

`decBg2_sym_pair`: the two-set form of `DecEquivLatBg.decBg2_sym` (the field and the multiplier are
the unique solution of `IsDecBg`, transported by `isDecBg2_sym_iff_pair`).
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {C C' : DecCover d L N₁ m₁ K} {H H' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
  {a : ℕ → ℝ} {ν : ℝ} {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (S : LatSymm H H' σ)
  {τ : Equiv.Perm (ℕ × CTorus d L N₁ m₁ K)} {τb : Equiv.Perm (ℕ × CTorus d L N₁ m₁ K)}

/-- **Lattice-symmetry covariance of the decoupled background field and multiplier between two
generating sets.** -/
theorem decBg2_sym_pair (hidx : ∀ q, τ q ∈ C'.cubeIdx ↔ q ∈ C.cubeIdx)
    (hchi : ∀ q x, C'.chi (τ q) (σ x) = C.chi q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ C'.Qset (τ q) ↔ q' ∈ C.Qset q)
    (hbidx : ∀ q, τb q ∈ blockIdx H' ↔ q ∈ blockIdx H) (hblayer : ∀ q, (τb q).1 = q.1)
    (hbump : ∀ q x, Background.bump (τb q).1 (τb q).2 (σ x) = Background.bump q.1 q.2 x)
    (hbbase : ∀ q ∈ blockIdx H,
      jBlock d L (N₁ * L ^ m₁) K q.1 (σ.symm (τb q).2) = jBlock d L (N₁ * L ^ m₁) K q.1 q.2)
    {s : Dec2.DecParams C} {s' : Dec2.DecParams C'}
    (hs : ∀ P, Dec2.extS C' s' (τ P) = Dec2.extS C s P) (ρ : ℝ) (D : BgData H N) :
    Dec2.decBgField C' H' a ν ρ s' (S.sym D) = S.fld (Dec2.decBgField C H a ν ρ s D) ∧
      Dec2.decBgMult C' H' a ν ρ s' (S.sym D) = S.mul (Dec2.decBgMult C H a ν ρ s D) := by
  classical
  have h0 : S.fld (0 : H.Ω 1 × Fin N → ℂ) = 0 := by funext p; simp [LatSymm.fld]
  have h0' : S.mul (0 : H.Ω 1 → ℂ) = 0 := rfl
  have hPQ : ∀ p : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ),
      Dec2.IsDecBg C H a ν ρ s D p.1 p.2 ↔
        Dec2.IsDecBg C' H' a ν ρ s' (S.sym D)
          ((S.fldEquiv.prodCongr S.mulEquiv) p).1 ((S.fldEquiv.prodCongr S.mulEquiv) p).2 :=
    fun p => (isDecBg2_sym_iff_pair S hidx hchi hbox hqset hbidx hblayer hbump hbbase hs ρ D
      p.1 p.2).symm
  constructor
  · have := dite_existsUnique_equiv (S.fldEquiv.prodCongr S.mulEquiv)
      (P := fun p => Dec2.IsDecBg C H a ν ρ s D p.1 p.2)
      (Q := fun p => Dec2.IsDecBg C' H' a ν ρ s' (S.sym D) p.1 p.2) hPQ
      (fun p => S.fld p.1) (fun p => p.1) (fun p => rfl) (S.fld 0)
    rw [h0] at this
    unfold Dec2.decBgField
    rw [← this]
    split_ifs <;> simp [h0]
  · have := dite_existsUnique_equiv (S.fldEquiv.prodCongr S.mulEquiv)
      (P := fun p => Dec2.IsDecBg C H a ν ρ s D p.1 p.2)
      (Q := fun p => Dec2.IsDecBg C' H' a ν ρ s' (S.sym D) p.1 p.2) hPQ
      (fun p => S.mul p.2) (fun p => p.2) (fun p => rfl) (S.mul 0)
    rw [h0'] at this
    unfold Dec2.decBgMult
    rw [← this]
    split_ifs <;> simp [h0']

end Balaban.Localization.DecEquiv
