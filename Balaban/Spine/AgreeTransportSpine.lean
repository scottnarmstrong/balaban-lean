/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.AgreeTransport
public import Balaban.Spine.BookMap

/-!
# Spines and books along `HAgr`

For region histories that agree up to the scale `m` (`HAgr m`), the canonical spines and the books
of the components at the scales `j ≤ m` correspond under `HAgr.cequiv`:
`spine_eq`, `bk_eq`, and therefore the kept events (`isKeptEvent_iff`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

theorem map_eq_singleton_iff {ι ι' : Type*} (e : ι ↪ ι') (s : Finset ι) (c : ι') :
    s.map e = {c} ↔ ∃ a, s = {a} ∧ e a = c := by
  constructor
  · intro h
    have hc : (s.map e).card = 1 := by rw [h]; rfl
    rw [Finset.card_map] at hc
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
    refine ⟨a, rfl, ?_⟩
    simpa using h
  · rintro ⟨a, rfl, rfl⟩
    simp

theorem _root_.Balaban.LargeField.RegionHistory.bk_succ (H : RegionHistory S n R k0 K) (j : ℕ)
    (Z' : H.Comp (j + 1)) :
    H.bk (j + 1) Z' = S.nextBook (j + 1) (H.parts j Z') (fun c => S.postBook k0 j (H.bk j c))
      (Z'.1 ∩ H.newCubes (j + 1)).card (H.spine (j + 1) Z') := rfl

namespace HAgr

variable {m : ℕ} {H₁ H₂ : RegionHistory S n R k0 K} (h : HAgr m H₁ H₂)
include h

theorem spineOK_iff {j : ℕ} (hj : j + 1 ≤ m) (Γs₁ : H₁.Comp j → Spine S.d)
    (Γs₂ : H₂.Comp j → Spine S.d) (hΓ : ∀ c, Γs₂ (h.cequiv (by omega) c) = Γs₁ c)
    (Z' : H₁.Comp (j + 1)) (Γ' : Spine S.d) :
    H₂.SpineOK j Γs₂ (h.cmap hj Z') Γ' ↔ H₁.SpineOK j Γs₁ Z' Γ' := by
  unfold RegionHistory.SpineOK
  rw [h.parts_eq hj Z', ← h.newCubes_eq (show j < m by omega), h.cmap_val]
  simp only [Finset.sum_map, Finset.card_map, map_eq_singleton_iff, Equiv.coe_toEmbedding, hΓ,
    forall_exists_index, and_imp]
  constructor
  · rintro ⟨a1, a2, a3, a4⟩
    refine ⟨a1, a2, fun hn c hc hl => ?_, a4⟩
    exact a3 hn _ c hc rfl (by simpa [hΓ] using hl)
  · rintro ⟨a1, a2, a3, a4⟩
    refine ⟨a1, a2, fun hn c₂ c₁ hc hec hl => ?_, a4⟩
    subst hec
    exact a3 hn c₁ hc (by simpa [hΓ] using hl)

theorem spineTarget_eq {j : ℕ} (hj : j + 1 ≤ m) (Γs₁ : H₁.Comp j → Spine S.d)
    (Γs₂ : H₂.Comp j → Spine S.d) (hΓ : ∀ c, Γs₂ (h.cequiv (by omega) c) = Γs₁ c)
    (Z' : H₁.Comp (j + 1)) :
    H₂.spineTarget j Γs₂ (h.cmap hj Z') = H₁.spineTarget j Γs₁ Z' := by
  classical
  unfold RegionHistory.spineTarget
  rw [h.parts_eq hj Z', ← h.newCubes_eq (show j < m by omega), h.cmap_val]
  simp only [Finset.sum_map, Finset.card_map, map_eq_singleton_iff, Equiv.coe_toEmbedding, hΓ]
  have hex : (∃ c, (∃ a, H₁.parts j Z' = {a} ∧ (h.cequiv (by omega)) a = c) ∧
      (Γs₂ c).length ≤ S.L) ↔ ∃ c, H₁.parts j Z' = {c} ∧ (Γs₁ c).length ≤ S.L := by
    constructor
    · rintro ⟨c₂, ⟨a, ha, rfl⟩, hl⟩
      exact ⟨a, ha, by simpa [hΓ] using hl⟩
    · rintro ⟨a, ha, hl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, by simpa [hΓ] using hl⟩
  simp only [hex]

theorem spineCan_iff {j : ℕ} (hj : j + 1 ≤ m) (Γs₁ : H₁.Comp j → Spine S.d)
    (Γs₂ : H₂.Comp j → Spine S.d) (hΓ : ∀ c, Γs₂ (h.cequiv (by omega) c) = Γs₁ c)
    (Z' : H₁.Comp (j + 1)) (Γ' : Spine S.d) :
    H₂.SpineCan j Γs₂ (h.cmap hj Z') Γ' ↔ H₁.SpineCan j Γs₁ Z' Γ' := by
  unfold RegionHistory.SpineCan
  rw [h.spineOK_iff hj Γs₁ Γs₂ hΓ, h.spineTarget_eq hj Γs₁ Γs₂ hΓ]

theorem nextSpine_eq {j : ℕ} (hj : j + 1 ≤ m) (Γs₁ : H₁.Comp j → Spine S.d)
    (Γs₂ : H₂.Comp j → Spine S.d) (hΓ : ∀ c, Γs₂ (h.cequiv (by omega) c) = Γs₁ c)
    (Z' : H₁.Comp (j + 1)) :
    H₂.nextSpine j Γs₂ (h.cmap hj Z') = H₁.nextSpine j Γs₁ Z' := by
  classical
  have hP : (fun Γ' => H₂.SpineCan j Γs₂ (h.cmap hj Z') Γ') =
      (fun Γ' => H₁.SpineCan j Γs₁ Z' Γ') :=
    funext fun Γ' => propext (h.spineCan_iff hj Γs₁ Γs₂ hΓ Z' Γ')
  unfold RegionHistory.nextSpine
  have key : ∀ (P₁ P₂ : Spine S.d → Prop), P₁ = P₂ →
      (if hh : ∃ Γ', P₁ Γ' then hh.choose else Spine.point 0) =
        (if hh : ∃ Γ', P₂ Γ' then hh.choose else Spine.point 0) := by
    rintro P₁ P₂ rfl; rfl
  exact key _ _ hP

theorem spine_eq : ∀ (j : ℕ) (hj : j ≤ m) (c : H₁.Comp j),
    H₂.spine j (h.cmap hj c) = H₁.spine j c
  | 0, _, c => (H₁.F.isEmpty_comp_zero.false c).elim
  | j + 1, hj, c => by
    show H₂.nextSpine j (H₂.spine j) (h.cmap hj c) = H₁.nextSpine j (H₁.spine j) c
    exact h.nextSpine_eq hj (H₁.spine j) (H₂.spine j) (fun c' => spine_eq j (by omega) c') c

theorem bk_eq : ∀ (j : ℕ) (hj : j ≤ m) (c : H₁.Comp j),
    H₂.bk j (h.cmap hj c) = H₁.bk j c
  | 0, _, c => (H₁.F.isEmpty_comp_zero.false c).elim
  | j + 1, hj, c => by
    rw [RegionHistory.bk_succ, RegionHistory.bk_succ, h.parts_eq hj c, nextBook_map]
    have hf : ((fun c' => S.postBook k0 j (H₂.bk j c')) ∘ (h.cequiv (by omega : j ≤ m)).toEmbedding) =
        fun c' => S.postBook k0 j (H₁.bk j c') := by
      funext c'
      simp only [Function.comp_apply, Equiv.coe_toEmbedding]
      exact congrArg (S.postBook k0 j) (bk_eq j (by omega) c')
    have hr : (↑(h.cmap hj c) ∩ H₂.newCubes (j + 1) : Finset _).card =
        (c.1 ∩ H₁.newCubes (j + 1) : Finset _).card := by
      rw [h.cmap_val, ← h.newCubes_eq (show j < m by omega)]
    rw [hf, hr, h.spine_eq (j + 1) hj c]

end HAgr

end Balaban.RootFSpine
