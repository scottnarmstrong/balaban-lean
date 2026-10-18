module

public import Balaban.LargeField.Operators.StepVacuumR5

/-!
# The volume of the vacuum regions of the creating step (R5 follow-up)

`stepVacuumVolume` is the total volume of the three regions
`Z_k^c ∖ Ω_{k+1}`, `Ω_{k+1} ∖ Ω″_{k+1}`, `Ω″_{k+1} ∩ Z_{k+1}` (P6 (3.2)).  These regions are
pairwise disjoint (for `Ω″_{k+1} ⊆ Ω_{k+1}`), but they do not partition `Z_{k+1} ∖ Z_k`: the first
region also contains the part of `Z_k^c` outside `Z_{k+1}`, the middle region is a neighbourhood
region that need not lie in `Z_{k+1}`, and the last region contains the part of `Ω″_{k+1}` lying
in `Z_k`.  The exact identity (with `Ω″_{k+1} ⊆ Ω_{k+1}`) is

`stepVacuumVolume = |Z_{k+1} ∖ Z_k|_k + |(Z_k^c ∖ Ω) ∖ Z_{k+1}|_k
  + |(Ω ∖ Ω″) ∖ (Z_{k+1} ∖ Z_k)|_k + |Ω″ ∩ Z_{k+1} ∩ Z_k|_k`.

In particular the volume is at least the volume of `Z_{k+1} ∖ Z_k`, with equality exactly when
the three excess sets have volume zero.  If `Z_{k+1} ⊆ Ω″_{k+1}` the volume is
`|Z_k^c ∖ Ω|_k + |Z_{k+1}|_k + |Ω ∖ Ω″|_k`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban RegionHistory

variable {S : Setting} {n : ℕ → ℕ} {M K : ℕ}

/-- The volume of a set of fine sites is nonnegative. -/
theorem volScale_nonneg {m : ℕ} (j : ℕ) (X : Set (Torus S.d m)) : 0 ≤ volScale S j X := by
  unfold volScale; positivity

/-- The volume is additive on disjoint sets. -/
theorem volScale_union_of_disjoint {m : ℕ} [NeZero m] (j : ℕ) {X Y : Set (Torus S.d m)}
    (h : Disjoint X Y) : volScale S j (X ∪ Y) = volScale S j X + volScale S j Y := by
  unfold volScale
  rw [Set.ncard_union_eq h (Set.toFinite _) (Set.toFinite _)]
  push_cast
  ring

/-- The volume is monotone. -/
theorem volScale_mono {m : ℕ} [NeZero m] (j : ℕ) {X Y : Set (Torus S.d m)} (h : X ⊆ Y) :
    volScale S j X ≤ volScale S j Y := by
  unfold volScale
  exact div_le_div_of_nonneg_right (Nat.cast_le.2 (Set.ncard_le_ncard h)) (by positivity)

/-- The three vacuum regions are pairwise disjoint, so `stepVacuumVolume` is the volume of
their union. -/
theorem stepVacuumVolume_eq_union [NeZero (M * n K * S.L ^ K)] (a : LocalHistory S n M K) (k : ℕ)
    (hsub : a.OmegaDD k ⊆ a.Omega k) :
    stepVacuumVolume a k =
      volScale S k (((a.Z k)ᶜ \ a.Omega k) ∪ (a.Omega k \ a.OmegaDD k) ∪
        (a.OmegaDD k ∩ a.Z (k + 1))) := by
  unfold stepVacuumVolume
  have h1 : Disjoint ((a.Z k)ᶜ \ a.Omega k) (a.Omega k \ a.OmegaDD k) :=
    Set.disjoint_left.2 fun x hx hx' => hx.2 hx'.1
  have h2 : Disjoint (((a.Z k)ᶜ \ a.Omega k) ∪ (a.Omega k \ a.OmegaDD k))
      (a.OmegaDD k ∩ a.Z (k + 1)) :=
    Set.disjoint_left.2 fun x hx hx' => by
      rcases hx with hx | hx
      · exact hx.2 (hsub hx'.1)
      · exact hx.2 hx'.1
  rw [volScale_union_of_disjoint k h2, volScale_union_of_disjoint k h1]

/-- **Exact identity for the volume of the vacuum regions.**  For a localized history with
`Ω″_{k+1} ⊆ Ω_{k+1}`, `stepVacuumVolume` is the volume of `Z_{k+1} ∖ Z_k` plus the volume of the
part of `Z_k^c ∖ Ω` outside `Z_{k+1}` plus the volume of the part of the annulus `Ω ∖ Ω″` outside
`Z_{k+1} ∖ Z_k` plus the volume of `Ω″ ∩ Z_{k+1} ∩ Z_k`. -/
theorem stepVacuumVolume_eq_add_excess [NeZero (M * n K * S.L ^ K)] (a : LocalHistory S n M K) (k : ℕ)
    (hsub : a.OmegaDD k ⊆ a.Omega k) :
    stepVacuumVolume a k =
      volScale S k (a.Z (k + 1) \ a.Z k) +
        volScale S k (((a.Z k)ᶜ \ a.Omega k) \ a.Z (k + 1)) +
          volScale S k ((a.Omega k \ a.OmegaDD k) \ (a.Z (k + 1) \ a.Z k)) +
            volScale S k (a.OmegaDD k ∩ a.Z (k + 1) ∩ a.Z k) := by
  classical
  set D := a.Z (k + 1) \ a.Z k with hD
  have hDsplit : D = (D \ a.Omega k) ∪ (D ∩ (a.Omega k \ a.OmegaDD k)) ∪
      ((a.OmegaDD k ∩ a.Z (k + 1)) \ a.Z k) := by
    ext x
    constructor
    · intro hx
      by_cases h1 : x ∈ a.Omega k
      · by_cases h2 : x ∈ a.OmegaDD k
        · exact Or.inr ⟨⟨h2, hx.1⟩, hx.2⟩
        · exact Or.inl (Or.inr ⟨hx, h1, h2⟩)
      · exact Or.inl (Or.inl ⟨hx, h1⟩)
    · rintro ((h | h) | h)
      · exact h.1
      · exact h.1
      · exact ⟨h.1.2, h.2⟩
  have hd1 : Disjoint (D \ a.Omega k) (D ∩ (a.Omega k \ a.OmegaDD k)) :=
    Set.disjoint_left.2 fun x hx hx' => hx.2 hx'.2.1
  have hd2 : Disjoint ((D \ a.Omega k) ∪ (D ∩ (a.Omega k \ a.OmegaDD k)))
      ((a.OmegaDD k ∩ a.Z (k + 1)) \ a.Z k) :=
    Set.disjoint_left.2 fun x hx hx' => by
      rcases hx with hx | hx
      · exact hx.2 (hsub hx'.1.1)
      · exact hx.2.2 hx'.1.1
  have hV : volScale S k D = volScale S k (D \ a.Omega k) +
      volScale S k (D ∩ (a.Omega k \ a.OmegaDD k)) +
        volScale S k ((a.OmegaDD k ∩ a.Z (k + 1)) \ a.Z k) := by
    conv_lhs => rw [hDsplit]
    rw [volScale_union_of_disjoint k hd2, volScale_union_of_disjoint k hd1]
  have hA : volScale S k ((a.Z k)ᶜ \ a.Omega k) =
      volScale S k (D \ a.Omega k) + volScale S k (((a.Z k)ᶜ \ a.Omega k) \ a.Z (k + 1)) := by
    rw [← volScale_union_of_disjoint k
      (Set.disjoint_left.2 fun x hx hx' => hx'.2 hx.1.1)]
    congr 1
    ext x
    constructor
    · intro hx
      by_cases h : x ∈ a.Z (k + 1)
      · exact Or.inl ⟨⟨h, hx.1⟩, hx.2⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (h | h)
      · exact ⟨h.1.2, h.2⟩
      · exact h.1
  have hB : volScale S k (a.Omega k \ a.OmegaDD k) =
      volScale S k (D ∩ (a.Omega k \ a.OmegaDD k)) +
        volScale S k ((a.Omega k \ a.OmegaDD k) \ D) := by
    rw [← volScale_union_of_disjoint k (Set.disjoint_left.2 fun x hx hx' => hx'.2 hx.1)]
    congr 1
    ext x
    constructor
    · intro hx
      by_cases h : x ∈ D
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (h | h)
      · exact h.2
      · exact h.1
  have hC : volScale S k (a.OmegaDD k ∩ a.Z (k + 1)) =
      volScale S k ((a.OmegaDD k ∩ a.Z (k + 1)) \ a.Z k) +
        volScale S k (a.OmegaDD k ∩ a.Z (k + 1) ∩ a.Z k) := by
    rw [← volScale_union_of_disjoint k (Set.disjoint_left.2 fun x hx hx' => hx.2 hx'.2)]
    congr 1
    ext x
    constructor
    · intro hx
      by_cases h : x ∈ a.Z k
      · exact Or.inr ⟨hx, h⟩
      · exact Or.inl ⟨hx, h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  unfold stepVacuumVolume
  rw [hV, hA, hB, hC]
  ring

/-- The volume of the vacuum regions is at least the removed volume `|Z_{k+1} ∖ Z_k|_k`. -/
theorem volScale_sdiff_le_stepVacuumVolume [NeZero (M * n K * S.L ^ K)] (a : LocalHistory S n M K) (k : ℕ)
    (hsub : a.OmegaDD k ⊆ a.Omega k) :
    volScale S k (a.Z (k + 1) \ a.Z k) ≤ stepVacuumVolume a k := by
  rw [stepVacuumVolume_eq_add_excess a k hsub]
  linarith [volScale_nonneg (S := S) k (((a.Z k)ᶜ \ a.Omega k) \ a.Z (k + 1)),
    volScale_nonneg (S := S) k ((a.Omega k \ a.OmegaDD k) \ (a.Z (k + 1) \ a.Z k)),
    volScale_nonneg (S := S) k (a.OmegaDD k ∩ a.Z (k + 1) ∩ a.Z k)]

/-- The vacuum volume equals `|Z_{k+1} ∖ Z_k|_k` exactly when the three excess sets have volume
zero. -/
theorem stepVacuumVolume_eq_sdiff_iff [NeZero (M * n K * S.L ^ K)] (a : LocalHistory S n M K) (k : ℕ)
    (hsub : a.OmegaDD k ⊆ a.Omega k) :
    stepVacuumVolume a k = volScale S k (a.Z (k + 1) \ a.Z k) ↔
      volScale S k (((a.Z k)ᶜ \ a.Omega k) \ a.Z (k + 1)) = 0 ∧
        volScale S k ((a.Omega k \ a.OmegaDD k) \ (a.Z (k + 1) \ a.Z k)) = 0 ∧
          volScale S k (a.OmegaDD k ∩ a.Z (k + 1) ∩ a.Z k) = 0 := by
  rw [stepVacuumVolume_eq_add_excess a k hsub]
  have h0 := volScale_nonneg (S := S) k (((a.Z k)ᶜ \ a.Omega k) \ a.Z (k + 1))
  have h1 := volScale_nonneg (S := S) k ((a.Omega k \ a.OmegaDD k) \ (a.Z (k + 1) \ a.Z k))
  have h2 := volScale_nonneg (S := S) k (a.OmegaDD k ∩ a.Z (k + 1) ∩ a.Z k)
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨h, h', h''⟩
    rw [h, h', h'']
    ring

/-- If `Z_{k+1} ⊆ Ω″_{k+1}` (as in the geometry, `Z^{(0)}_{k+1}` lies in `Ω″_{k+1}`), the volume
of the vacuum regions is `|Z_k^c ∖ Ω|_k + |Z_{k+1}|_k + |Ω ∖ Ω″|_k`. -/
theorem stepVacuumVolume_eq_of_Z_subset (a : LocalHistory S n M K) (k : ℕ)
    (hZ : a.Z (k + 1) ⊆ a.OmegaDD k) :
    stepVacuumVolume a k =
      volScale S k ((a.Z k)ᶜ \ a.Omega k) + volScale S k (a.Z (k + 1)) +
        volScale S k (a.Omega k \ a.OmegaDD k) := by
  unfold stepVacuumVolume
  have h3 : a.OmegaDD k ∩ a.Z (k + 1) = a.Z (k + 1) := Set.inter_eq_right.2 hZ
  rw [h3]
  ring

/-- For a localized history of a region history, the inclusion `Ω″_{k+1} ⊆ Ω_{k+1}` holds, so the
exact identity applies. -/
theorem localHistory_OmegaDD_subset_Omega [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
    (H : RegionHistory S n R k0 K) {m : ℕ} (Z : H.Comp m) (k : ℕ) :
    (H.localHistory M K m Z).OmegaDD k ⊆ (H.localHistory M K m Z).Omega k := by
  intro x hx
  exact ⟨((H.locRH m Z).step k).OmegaDD_subset_Omega hx.1, hx.2⟩

end Balaban.LargeField
