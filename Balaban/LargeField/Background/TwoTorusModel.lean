/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusOps
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The layers of the local boundary family are determined by the data near the component

On integer sets: let `𝒵` (the component `Z'`), `𝒦` (the region `Z_k`), `𝒪` (`Ω_{k+1}`) be sets with
the two locality properties of `Balaban/LargeField/Background/TwoTorusLocal.lean` (near `𝒵`, a point
of `𝒦` is in `𝒵`, and a point outside `𝒵` is in `𝒪`). If `𝒵`, `𝒦 ∩ 𝒵`, `𝒪 ∩ 𝒵` agree on a ball
about `w` with model sets `M𝒵`, `Mℛ`, `MℛΩ`, then `w` lies in the layer `Ω_n` of the boundary family
built from `(𝒵, 𝒦, 𝒪)` iff it lies in the layer built from the model sets
(`mem_bdLayZ_iff_model`, where `𝒦` is replaced by `Mℛ` and `𝒪` by `(M𝒵)ᶜ ∪ MℛΩ`).
-/

@[expose] public section

namespace Balaban.RootFSpine

variable {d : ℕ}

theorem abs_ediv_sub_le_of_abs_le {P : ℕ} (hP : 0 < P) {a b : ℤ} {j : ℕ}
    (h : |a - b| ≤ (P : ℤ) * j) : |a / (P : ℤ) - b / (P : ℤ)| ≤ j := by
  have hP' : (0 : ℤ) < P := by exact_mod_cast hP
  rw [abs_le] at h ⊢
  constructor
  · have h1 : b ≤ a + (P : ℤ) * j := by linarith [h.1]
    have h2 := Int.ediv_le_ediv hP' h1
    rw [Int.add_mul_ediv_left _ _ hP'.ne'] at h2
    linarith
  · have h1 : a ≤ b + (P : ℤ) * j := by linarith [h.2]
    have h2 := Int.ediv_le_ediv hP' h1
    rw [Int.add_mul_ediv_left _ _ hP'.ne'] at h2
    linarith

/-- A set that is constant on the cubes of side `P`. -/
def CubeConst (P : ℕ) (X : Set (Fin d → ℤ)) : Prop :=
  ∀ z z' : Fin d → ℤ, (∀ μ, z μ / (P : ℤ) = z' μ / (P : ℤ)) → (z ∈ X ↔ z' ∈ X)

theorem mem_dilZ_of_floor {P : ℕ} (hP : 0 < P) {X : Set (Fin d → ℤ)} (hX : CubeConst P X)
    {a e : ℕ} {z p : Fin d → ℤ} (hz : z ∈ dilZ P a X) (hzp : ∀ μ, |z μ / (P : ℤ) - p μ / (P : ℤ)| ≤ e) :
    p ∈ dilZ P (a + e) X := by
  have hP' : (P : ℤ) ≠ 0 := by exact_mod_cast hP.ne'
  obtain ⟨s, hs, hmem⟩ := hz
  refine ⟨fun μ => z μ / (P : ℤ) - p μ / (P : ℤ) + s μ, fun μ => ?_, ?_⟩
  · have h1 := hzp μ
    have h2 := hs μ
    have : |z μ / (P : ℤ) - p μ / (P : ℤ) + s μ| ≤ |z μ / (P : ℤ) - p μ / (P : ℤ)| + |s μ| :=
      abs_add_le _ _
    push_cast
    linarith
  · refine (hX _ _ (fun μ => ?_)).2 hmem
    simp only [Pi.add_apply, shiftZ]
    rw [Int.add_mul_ediv_left _ _ hP', Int.add_mul_ediv_left _ _ hP']
    ring

theorem mem_dilZ_dilZ_iff {P a : ℕ} {X Y : Set (Fin d → ℤ)} {z : Fin d → ℤ}
    (h : ∀ s s' : Fin d → ℤ, (∀ μ, |s μ| ≤ a) → (∀ μ, |s' μ| ≤ a) →
      (z + shiftZ P s + shiftZ P s' ∈ X ↔ z + shiftZ P s + shiftZ P s' ∈ Y)) :
    z ∈ dilZ P a (dilZ P a X) ↔ z ∈ dilZ P a (dilZ P a Y) := by
  constructor
  · rintro ⟨s, hs, s', hs', hmem⟩
    exact ⟨s, hs, s', hs', (h s s' hs hs').1 hmem⟩
  · rintro ⟨s, hs, s', hs', hmem⟩
    exact ⟨s, hs, s', hs', (h s s' hs hs').2 hmem⟩

theorem near_of_supp {L M1 k P1 ρ : ℕ} {X : Set (Fin d → ℤ)} {z w : Fin d → ℤ}
    (hz : z ∈ dilZ P1 (ρ + 1) X) (hzw : ∀ μ, |z μ - w μ| ≤ ((11 * (L ^ (k + 1) * M1) : ℕ) : ℤ)) :
    ∃ z'' ∈ X, ∀ μ, |z'' μ - w μ| ≤ ((12 * (L ^ (k + 1) * M1) + P1 * (ρ + 1) : ℕ) : ℤ) := by
  obtain ⟨s, hs, hmem⟩ := hz
  refine ⟨z + shiftZ P1 s, hmem, fun μ => ?_⟩
  have h1 : |(z + shiftZ P1 s) μ - w μ| ≤ |z μ - w μ| + |(P1 : ℤ) * s μ| := by
    have := abs_add_le (z μ - w μ) ((P1 : ℤ) * s μ)
    simpa [shiftZ, add_assoc, sub_eq_add_neg, add_comm, add_left_comm] using this
  have h2 : |(P1 : ℤ) * s μ| ≤ (P1 : ℤ) * (ρ + 1) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs μ) (by positivity)
  have h3 := hzw μ
  have h4 : (0 : ℤ) ≤ (L : ℤ) ^ (k + 1) * M1 := by positivity
  push_cast at h3 ⊢
  linarith

theorem mem_bdLayZ_iff_model {L M1 k P0 P1 ρ ρ' : ℕ} (hL : 2 ≤ L) (hM1 : 0 < M1) (hP0 : 0 < P0)
    (hP1 : P1 = L * P0) (hB : 12 * (L ^ (k + 1) * M1) + 2 ≤ P1) (hρ : ρ' ≤ ρ)
    {𝒵 𝒦 𝒪 M𝒵 Mℛ MℛΩ : Set (Fin d → ℤ)} (hc : CubeConst P1 𝒵)
    (locK : ∀ z ∈ dilZ P1 (ρ + 1 + (ρ' + 1)) 𝒵, z ∈ 𝒦 → z ∈ 𝒵)
    (locO : ∀ z ∈ dilZ P1 (ρ + 2) 𝒵, z ∉ 𝒵 → z ∈ 𝒪) {w : Fin d → ℤ}
    (hAZ : AgrB w (12 * (L ^ (k + 1) * M1) + P1 * (ρ + 1)) 𝒵 M𝒵)
    (hAR : AgrB w (12 * (L ^ (k + 1) * M1) + P1 * (ρ + 1)) (𝒦 ∩ 𝒵) Mℛ)
    (hAO : AgrB w (12 * (L ^ (k + 1) * M1) + P1 * (ρ + 1)) (𝒪 ∩ 𝒵) MℛΩ) (n : ℕ) :
    w ∈ bdLayZ L M1 k (dilZ P0 (ρ' + 1) (dilZ P0 (ρ' + 1) 𝒦ᶜ) ∩ dilZ P1 (ρ + 1) 𝒵)
        (dilZ P1 (ρ + 1) 𝒵) 𝒪 n ↔
      w ∈ bdLayZ L M1 k (dilZ P0 (ρ' + 1) (dilZ P0 (ρ' + 1) Mℛᶜ) ∩ dilZ P1 (ρ + 1) M𝒵)
        (dilZ P1 (ρ + 1) M𝒵) (M𝒵ᶜ ∪ MℛΩ) n := by
  have hP1pos : 0 < P1 := by rw [hP1]; exact Nat.mul_pos (by omega) hP0
  set B := 12 * (L ^ (k + 1) * M1) with hBdef
  by_cases hnear : ∃ z'' ∈ M𝒵, ∀ μ, |z'' μ - w μ| ≤ ((B + P1 * (ρ + 1) : ℕ) : ℤ)
  · -- near case: the inputs agree on the balls that are read
    have hU : AgrB w (0 + B) (dilZ P1 (ρ + 1) 𝒵) (dilZ P1 (ρ + 1) M𝒵) := by
      rw [zero_add]; exact AgrB.dil hAZ
    have hW : AgrB w (0 + B) (dilZ P0 (ρ' + 1) (dilZ P0 (ρ' + 1) 𝒦ᶜ) ∩ dilZ P1 (ρ + 1) 𝒵)
        (dilZ P0 (ρ' + 1) (dilZ P0 (ρ' + 1) Mℛᶜ) ∩ dilZ P1 (ρ + 1) M𝒵) := by
      rw [zero_add]
      intro z hz
      have hUz := (AgrB.dil hAZ) z hz
      simp only [Set.mem_inter_iff]
      by_cases hu : z ∈ dilZ P1 (ρ + 1) 𝒵
      · have hu' := hUz.1 hu
        simp only [hu, hu', and_true]
        refine mem_dilZ_dilZ_iff fun s s' hs hs' => ?_
        set p := z + shiftZ P0 s + shiftZ P0 s' with hp
        have hpz : ∀ μ, |p μ - z μ| ≤ (P1 : ℤ) * (ρ' + 1 : ℕ) := by
          intro μ
          have e1 : p μ - z μ = (P0 : ℤ) * s μ + (P0 : ℤ) * s' μ := by
            simp only [hp, Pi.add_apply, shiftZ]; ring
          rw [e1]
          have h1 : |(P0 : ℤ) * s μ + (P0 : ℤ) * s' μ| ≤ |(P0 : ℤ) * s μ| + |(P0 : ℤ) * s' μ| :=
            abs_add_le _ _
          have h2 : |(P0 : ℤ) * s μ| ≤ (P0 : ℤ) * (ρ' + 1 : ℕ) := by
            rw [abs_mul, abs_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs μ) (by positivity)
          have h3 : |(P0 : ℤ) * s' μ| ≤ (P0 : ℤ) * (ρ' + 1 : ℕ) := by
            rw [abs_mul, abs_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs' μ) (by positivity)
          have h4 : (P1 : ℤ) = (L : ℤ) * P0 := by rw [hP1]; push_cast; ring
          have h5 : (2 : ℤ) ≤ L := by exact_mod_cast hL
          have h6 : (0 : ℤ) ≤ (P0 : ℤ) * (ρ' + 1 : ℕ) := by positivity
          nlinarith
        have hfl : ∀ μ, |z μ / (P1 : ℤ) - p μ / (P1 : ℤ)| ≤ ((ρ' + 1 : ℕ) : ℤ) := by
          intro μ
          rw [abs_sub_comm]
          exact abs_ediv_sub_le_of_abs_le hP1pos (hpz μ)
        have hpnear := mem_dilZ_of_floor hP1pos hc hu (e := ρ' + 1) hfl
        have hpR : ∀ μ, |p μ - w μ| ≤ ((B + P1 * (ρ + 1) : ℕ) : ℤ) := by
          intro μ
          have h1 : |p μ - w μ| ≤ |p μ - z μ| + |z μ - w μ| := by
            have := abs_add_le (p μ - z μ) (z μ - w μ)
            simpa using this
          have h2 := hpz μ
          have h3 := hz μ
          have h4 : (P1 : ℤ) * (ρ' + 1 : ℕ) ≤ (P1 : ℤ) * (ρ + 1 : ℕ) :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.succ_le_succ hρ) (by positivity)
          push_cast at h2 h4 ⊢
          linarith
        have hK : p ∈ 𝒦 ↔ p ∈ Mℛ := by
          rw [← hAR p hpR]
          exact ⟨fun h => ⟨h, locK p hpnear h⟩, fun h => h.1⟩
        exact not_congr hK
      · have hu' : z ∉ dilZ P1 (ρ + 1) M𝒵 := fun h => hu (hUz.2 h)
        simp [hu, hu']
    have hO : AgrB w 0 𝒪 (M𝒵ᶜ ∪ MℛΩ) := by
      intro z hz
      have hzw : z = w := by
        funext μ
        have h0 := hz μ
        have h1 : |z μ - w μ| ≤ 0 := by exact_mod_cast h0
        have := abs_nonpos_iff.1 h1
        linarith
      subst hzw
      obtain ⟨z'', hz''M, hz''d⟩ := hnear
      have hz''Z : z'' ∈ 𝒵 := (hAZ z'' hz''d).2 hz''M
      have hwnear : z ∈ dilZ P1 (ρ + 2) 𝒵 := by
        refine ⟨fun μ => z'' μ / (P1 : ℤ) - z μ / (P1 : ℤ), fun μ => ?_, ?_⟩
        · have h1 : |z'' μ - z μ| ≤ (P1 : ℤ) * (ρ + 2 : ℕ) := by
            have := hz''d μ
            push_cast at this ⊢
            have h2 : (12 * (L ^ (k + 1) * M1) : ℤ) + 2 ≤ P1 := by exact_mod_cast hB
            nlinarith
          exact_mod_cast abs_ediv_sub_le_of_abs_le hP1pos h1
        · refine (hc _ _ (fun μ => ?_)).2 hz''Z
          simp only [Pi.add_apply, shiftZ]
          have hP' : (P1 : ℤ) ≠ 0 := by exact_mod_cast hP1pos.ne'
          rw [Int.add_mul_ediv_left _ _ hP']
          ring
      have h1 : z ∈ 𝒵 ↔ z ∈ M𝒵 := hAZ z (fun μ => by rw [sub_self, abs_zero]; exact Nat.cast_nonneg _)
      have h2 : z ∈ 𝒪 ∩ 𝒵 ↔ z ∈ MℛΩ := hAO z (fun μ => by rw [sub_self, abs_zero]; exact Nat.cast_nonneg _)
      simp only [Set.mem_union, Set.mem_compl_iff]
      rw [← h1, ← h2]
      constructor
      · intro h
        by_cases hz𝒵 : z ∈ 𝒵
        · exact Or.inr ⟨h, hz𝒵⟩
        · exact Or.inl hz𝒵
      · rintro (h | h)
        · exact locO z hwnear h
        · exact h.1
    have := AgrB.bdLay L M1 k hL hM1 hW hU hO n (R := 0)
    exact this w (fun μ => by simp)
  · -- far case: both sides are empty
    have hfarL : w ∉ bdLayZ L M1 k (dilZ P0 (ρ' + 1) (dilZ P0 (ρ' + 1) 𝒦ᶜ) ∩ dilZ P1 (ρ + 1) 𝒵)
        (dilZ P1 (ρ + 1) 𝒵) 𝒪 n := by
      intro h
      obtain ⟨z, hzU, hzd⟩ := bdLayZ_supp L M1 k hL hM1 (Set.inter_subset_right) n h
      obtain ⟨z'', hz''Z, hz''d⟩ := near_of_supp (L := L) (M1 := M1) (k := k) hzU hzd
      exact hnear ⟨z'', (hAZ z'' hz''d).1 hz''Z, hz''d⟩
    have hfarR : w ∉ bdLayZ L M1 k (dilZ P0 (ρ' + 1) (dilZ P0 (ρ' + 1) Mℛᶜ) ∩ dilZ P1 (ρ + 1) M𝒵)
        (dilZ P1 (ρ + 1) M𝒵) (M𝒵ᶜ ∪ MℛΩ) n := by
      intro h
      obtain ⟨z, hzU, hzd⟩ := bdLayZ_supp L M1 k hL hM1 (Set.inter_subset_right) n h
      obtain ⟨z'', hz''Z, hz''d⟩ := near_of_supp (L := L) (M1 := M1) (k := k) hzU hzd
      exact hnear ⟨z'', hz''Z, hz''d⟩
    exact ⟨fun h => absurd h hfarL, fun h => absurd h hfarR⟩

end Balaban.RootFSpine
