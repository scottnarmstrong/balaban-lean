/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.AgreeTransportKappa
public import Balaban.LargeField.History.LocalRegion

/-!
# Lineages and localized histories along `HAgr`

For region histories that agree up to the scale `m`, the descent relation, the lineages
`Lin_a(Z)` and the localized history `𝔥_k(Z)` of a component of `Z^pre_k`, `k ≤ m`, correspond under
`HAgr.cequiv`: `localHistory_eq`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-- Agreement is symmetric. -/
theorem HAgr.symm {m : ℕ} {H₁ H₂ : RegionHistory S n R k0 K} (h : HAgr m H₁ H₂) :
    HAgr m H₂ H₁ :=
  ⟨fun j hj => (h.step j hj).symm, fun j hj => (h.rem j hj).symm⟩

theorem _root_.Balaban.LargeField.RegionHistory.tailZ_zero (H : RegionHistory S n R k0 K) {k : ℕ}
    (Z : H.Comp k) : H.tailZ k Z 0 = ∅ := rfl

theorem _root_.Balaban.LargeField.RegionHistory.tailZ_succ (H : RegionHistory S n R k0 K) {k : ℕ}
    (Z : H.Comp k) (j : ℕ) : H.tailZ k Z (j + 1) =
      if j + 1 ≤ k ∧ j + 1 ≤ K then ((H.lin (j + 1) k Z : Finset (Torus S.d (n (j + 1)))) : Set _)
      else (emptyStep S n R j (H.tailZ k Z j)).Zpre (S.omega (j + 1)) (critOpt S k0 (j + 1)) := rfl

namespace HAgr

variable {m : ℕ} {H₁ H₂ : RegionHistory S n R k0 K} (h : HAgr m H₁ H₂)
include h

theorem cmap_symm {j : ℕ} (hj : j ≤ m) (c : H₁.Comp j) : h.symm.cmap hj (h.cmap hj c) = c :=
  Subtype.ext (by rw [h.symm.cmap_val, h.cmap_val])

theorem desc_map {a b : ℕ} {Y : H₁.Comp a} {Z : H₁.Comp b} (hd : H₁.Desc a b Y Z) (hb : b ≤ m) :
    H₂.Desc a b (h.cmap (hd.le.trans hb) Y) (h.cmap hb Z) := by
  revert hb
  induction hd with
  | refl Y => intro hb; exact Desc.refl _
  | step b Y' Y'' Y''' hd hrem hs ih =>
    intro hb
    exact Desc.step b _ (h.cmap (by omega) Y'') (h.cmap hb Y''') (ih (by omega))
      ((h.rem_iff (by omega) Y'').2 hrem) (by simpa [IsSucc, h.cmap_val] using hs)

theorem lin_eq {a b : ℕ} (hb : b ≤ m) (Z : H₁.Comp b) :
    H₂.lin a b (h.cmap hb Z) = H₁.lin a b Z := by
  ext x
  rw [mem_lin, mem_lin]
  constructor
  · rintro ⟨Y₂, hd, hx⟩
    have hab : a ≤ b := hd.le
    have hd' := h.symm.desc_map hd hb
    rw [h.cmap_symm hb Z] at hd'
    refine ⟨h.symm.cmap (hab.trans hb) Y₂, hd', ?_⟩
    rw [h.symm.cmap_val]; exact hx
  · rintro ⟨Y₁, hd, hx⟩
    refine ⟨h.cmap (hd.le.trans hb) Y₁, h.desc_map hd hb, ?_⟩
    rw [h.cmap_val]; exact hx

theorem tailZ_eq {k : ℕ} (hk : k ≤ m) (Z : H₁.Comp k) (j : ℕ) :
    H₂.tailZ k (h.cmap hk Z) j = H₁.tailZ k Z j := by
  induction j with
  | zero => rw [tailZ_zero, tailZ_zero]
  | succ j ih =>
    rw [tailZ_succ, tailZ_succ]
    by_cases hc : j + 1 ≤ k ∧ j + 1 ≤ K
    · simp only [hc, and_self, ite_true]
      rw [h.lin_eq hk Z]
    · simp only [hc, ite_false]
      rw [ih]

theorem locStep_eq {k : ℕ} (hk : k ≤ m) (Z : H₁.Comp k) (j : ℕ) :
    H₂.locStep k (h.cmap hk Z) j = H₁.locStep k Z j := by
  unfold RegionHistory.locStep
  by_cases hc : j < k ∧ j < K
  · simp only [hc, and_self, ite_true]
    rw [show H₂.step j = H₁.step j from (h.step j (by omega)).symm, h.lin_eq hk Z]
  · simp only [hc, ite_false]
    rw [h.tailZ_eq hk Z j]

theorem localHistory_eq {k : ℕ} (hk : k ≤ m) (M K' : ℕ) (Z : H₁.Comp k) :
    H₂.localHistory M K' k (h.cmap hk Z) = H₁.localHistory M K' k Z := by
  unfold RegionHistory.localHistory
  have e : ∀ j, (H₂.locRH k (h.cmap hk Z)).step j = (H₁.locRH k Z).step j :=
    fun j => h.locStep_eq hk Z j
  simp only [e, h.cmap_val]

end HAgr

end Balaban.RootFSpine
