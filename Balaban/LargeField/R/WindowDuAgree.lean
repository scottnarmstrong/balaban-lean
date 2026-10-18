/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDuBall
public import Balaban.LargeField.R.WindowLiftConv

/-!
# The reference datum agrees with the physical datum on the balls (blocker 4)

`du_eq_physical_of_fields`: a datum `Du` of the window generating set whose values on `Ω₁` are the
variables of the window point (`ψ_s` on the layer `s ≠ m'+1`, the output `o` on the layer `m'+1`),
read at the layer index of the window generating set, is the physical datum of the variable field
`ψ` (read at the layer index of the parent generating set) at every site where the two layer indices
agree.  `window_layer_eq_full_ball`: they agree on the ball `B(X_i, 2 L^{j_i} M)` around the region of
every piece.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.Background RegionHistory
  Balaban.LargeField.ActionConv Balaban.SmallField Balaban.Flow Balaban.Localization

section Agree

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K} {m' : ℕ} {Z : H.Comp (m' + 1)}
  {g : Geo S n R M}

/-- **The datum `Du` is the physical datum where the layer indices agree.** -/
theorem du_eq_physical_of_fields (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    {A : Set (InternalVars (H.localHistory M K (m' + 1) Z) (m' + 1))}
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1) A)
    (hv : EuclideanSpace ℝ (Fin N))
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hψ1 : ∀ b, ψ ⟨m' + 1, b⟩ = outField N o (torusCast (blk_eq_top H.F.hnn hmK le_rfl) b))
    (hψ0 : ∀ i (hi : i ≤ m') b, ψ ⟨i, b⟩ =
      subVarField N x i (torusCast (blk_eq_top H.F.hnn hmK (hi.trans (Nat.le_succ _))) b))
    (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N)
    (Fs : ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
    (Ft : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hFs : ∀ s y, Fs s y = subVarField N x s y) (hFt : ∀ y, Ft y = outField N o y)
    (hDu1 : ∀ y ∈ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1,
      ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y ≠ m' + 1 →
        ∀ i, Du.Ψ y i = ((Fs (((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y)
          (jBlock S.d S.L (M * n K) K
            (((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y)
            (torusCast (fine_eq_top H.F.hnn hmK).symm y)) i : ℝ) : ℂ))
    (hDu2 : ∀ y ∈ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1,
      ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y = m' + 1 →
        ∀ i, Du.Ψ y i = ((Ft (jBlock S.d S.L (M * n K) K (m' + 1)
          (torusCast (fine_eq_top H.F.hnn hmK).symm y)) i : ℝ) : ℂ))
    {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hy : y ∈ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1)
    (hyf : y ∈ (windowOfHistory H Z g hmK hW).full.Ω 1)
    (hlay : ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y =
      (windowOfHistory H Z g hmK hW).full.layerIndex y) :
    Du.Ψ y = (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW)
      (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ y := by
  classical
  have hyd : y ∈ dataSites ((windowOfHistory H Z g hmK hW).windowGenSet
      (windowOfHistory_hyp hmK hW)) := (mem_dataSites _).2 (Or.inl hy)
  funext i
  rw [physicalWindowData_Ψ _ _ _ ψ _ hyd i, inheritedField_eq_parentBlock,
    parentBlock_of_mem _ hyf, ← hlay]
  obtain ⟨hl1, hl2, -⟩ := ((windowOfHistory H Z g hmK hW).windowGenSet
    (windowOfHistory_hyp hmK hW)).layerIndex_spec hy
  have h1 := hDu1 y hy
  have h2 := hDu2 y hy
  generalize ((windowOfHistory H Z g hmK hW).windowGenSet
    (windowOfHistory_hyp hmK hW)).layerIndex y = ℓ at hl1 hl2 h1 h2 ⊢
  have hx0 : jBlock S.d S.L (M * n K) K ℓ (torusCast (fine_eq_top H.F.hnn hmK).symm y) =
      torusCast (blk_eq_top H.F.hnn hmK hl2)
        (jBlock S.d S.L (M * n (m' + 1)) (m' + 1) ℓ y) :=
    jBlock_torusCast hl2 (hl2.trans hmK) (fine_eq_top H.F.hnn hmK).symm _ y
  by_cases hℓ : ℓ = m' + 1
  · subst hℓ
    rw [h2 rfl i, hx0, hFt]
    unfold blockOf
    rw [hψ1]
  · have hℓ' : ℓ ≤ m' := by omega
    rw [h1 hℓ i, hx0, hFs]
    unfold blockOf
    rw [hψ0 ℓ hℓ']

end Agree

end Balaban.LargeField
