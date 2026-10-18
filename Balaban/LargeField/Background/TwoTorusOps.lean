/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Local set operations on integer lattice sets

The set operations that define the layers of the boundary generating sets (`cubeInterior`,
`nearStep`, neighbourhoods of cubes) are, on the integer lifts of the fine tori, the operations
`cintZ`, `nearZ`, `dilZ` below. Each reads the set only in a ball of explicit radius around the
point (`AgrB`-locality lemmas).
-/

@[expose] public section

namespace Balaban.RootFSpine

variable {d : ℕ}

/-- Translation of an integer vector by `P` times `s`. -/
def shiftZ (P : ℕ) (s : Fin d → ℤ) : Fin d → ℤ := fun μ => (P : ℤ) * s μ

/-- Neighbourhood by `r` cubes of side `P` of a union of cubes (`X` is read at the translates
`w + P s`, `|s| ≤ r`). -/
def dilZ (P r : ℕ) (X : Set (Fin d → ℤ)) : Set (Fin d → ℤ) :=
  {w | ∃ s : Fin d → ℤ, (∀ μ, |s μ| ≤ r) ∧ w + shiftZ P s ∈ X}

/-- The union of the cubes of side `P` whose index is within `r` of the index of a point of `X`. -/
def nearZ (P r : ℕ) (X : Set (Fin d → ℤ)) : Set (Fin d → ℤ) :=
  {w | ∃ z ∈ X, ∀ μ, |z μ / (P : ℤ) - w μ / (P : ℤ)| ≤ r}

/-- The union of the cubes of side `P` contained in `X`. -/
def cintZ (P : ℕ) (X : Set (Fin d → ℤ)) : Set (Fin d → ℤ) :=
  {w | ∀ z, (∀ μ, z μ / (P : ℤ) = w μ / (P : ℤ)) → z ∈ X}

/-- `X` and `Y` agree on the ball of radius `R` (sup norm) about `w`. -/
def AgrB (w : Fin d → ℤ) (R : ℕ) (X Y : Set (Fin d → ℤ)) : Prop :=
  ∀ z, (∀ μ, |z μ - w μ| ≤ R) → (z ∈ X ↔ z ∈ Y)

theorem AgrB.mono {w : Fin d → ℤ} {R R' : ℕ} {X Y : Set (Fin d → ℤ)} (h : AgrB w R X Y)
    (hR : R' ≤ R) : AgrB w R' X Y := fun z hz => h z fun μ => (hz μ).trans (by exact_mod_cast hR)

theorem AgrB.inter {w : Fin d → ℤ} {R : ℕ} {X Y X' Y' : Set (Fin d → ℤ)} (h : AgrB w R X Y)
    (h' : AgrB w R X' Y') : AgrB w R (X ∩ X') (Y ∩ Y') := fun z hz => by
  simp only [Set.mem_inter_iff]
  rw [h z hz, h' z hz]

theorem AgrB.union {w : Fin d → ℤ} {R : ℕ} {X Y X' Y' : Set (Fin d → ℤ)} (h : AgrB w R X Y)
    (h' : AgrB w R X' Y') : AgrB w R (X ∪ X') (Y ∪ Y') := fun z hz => by
  simp only [Set.mem_union]
  rw [h z hz, h' z hz]

theorem AgrB.compl {w : Fin d → ℤ} {R : ℕ} {X Y : Set (Fin d → ℤ)} (h : AgrB w R X Y) :
    AgrB w R Xᶜ Yᶜ := fun z hz => by
  simp only [Set.mem_compl_iff]
  rw [h z hz]

theorem AgrB.diff {w : Fin d → ℤ} {R : ℕ} {X Y X' Y' : Set (Fin d → ℤ)} (h : AgrB w R X Y)
    (h' : AgrB w R X' Y') : AgrB w R (X \ X') (Y \ Y') := fun z hz => by
  simp only [Set.mem_sdiff]
  rw [h z hz, h' z hz]

theorem AgrB.dil {w : Fin d → ℤ} {R P r : ℕ} {X Y : Set (Fin d → ℤ)}
    (h : AgrB w (R + P * r) X Y) : AgrB w R (dilZ P r X) (dilZ P r Y) := by
  intro z hz
  have key : ∀ s : Fin d → ℤ, (∀ μ, |s μ| ≤ r) → ∀ μ, |(z + shiftZ P s) μ - w μ| ≤ (R + P * r : ℕ) := by
    intro s hs μ
    have h1 := hz μ
    have h2 : |(P : ℤ) * s μ| ≤ (P : ℤ) * r := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hs μ) (by positivity)
    have h3 : |(z + shiftZ P s) μ - w μ| ≤ |z μ - w μ| + |(P : ℤ) * s μ| := by
      have := abs_add_le (z μ - w μ) ((P : ℤ) * s μ)
      simpa [shiftZ, add_assoc, sub_eq_add_neg, add_comm, add_left_comm] using this
    push_cast
    linarith
  constructor
  · rintro ⟨s, hs, hmem⟩
    exact ⟨s, hs, (h _ (key s hs)).1 hmem⟩
  · rintro ⟨s, hs, hmem⟩
    exact ⟨s, hs, (h _ (key s hs)).2 hmem⟩

theorem abs_ediv_sub_le {P : ℕ} (hP : 0 < P) {a b : ℤ} {r : ℕ} (h : |a / (P : ℤ) - b / (P : ℤ)| ≤ r) :
    |a - b| ≤ (P : ℤ) * (r + 1) := by
  have hP' : (0 : ℤ) < P := by exact_mod_cast hP
  have h1 := Int.emod_add_mul_ediv a (P : ℤ)
  have h2 := Int.emod_add_mul_ediv b (P : ℤ)
  have h3 := Int.emod_nonneg a hP'.ne'
  have h4 := Int.emod_lt_of_pos a hP'
  have h5 := Int.emod_nonneg b hP'.ne'
  have h6 := Int.emod_lt_of_pos b hP'
  have h7 : |(P : ℤ) * (a / (P : ℤ) - b / (P : ℤ))| ≤ (P : ℤ) * r := by
    rw [abs_mul, abs_of_pos hP']
    exact mul_le_mul_of_nonneg_left h hP'.le
  rw [abs_le] at h7 ⊢
  constructor <;> nlinarith [h7.1, h7.2]

theorem AgrB.near {w : Fin d → ℤ} {R P r : ℕ} (hP : 0 < P) {X Y : Set (Fin d → ℤ)}
    (h : AgrB w (R + P * (r + 1)) X Y) : AgrB w R (nearZ P r X) (nearZ P r Y) := by
  have key : ∀ z z' : Fin d → ℤ, (∀ μ, |z μ - w μ| ≤ R) → (∀ μ, |z' μ / (P : ℤ) - z μ / (P : ℤ)| ≤ r) →
      ∀ μ, |z' μ - w μ| ≤ (R + P * (r + 1) : ℕ) := by
    intro z z' hz hz' μ
    have h1 := abs_ediv_sub_le hP (hz' μ)
    have h2 : |z' μ - w μ| ≤ |z' μ - z μ| + |z μ - w μ| := by
      have := abs_add_le (z' μ - z μ) (z μ - w μ)
      simpa using this
    have h3 := hz μ
    push_cast
    linarith
  intro z hz
  constructor
  · rintro ⟨z', hz'X, hz'⟩
    exact ⟨z', (h z' (key z z' hz hz')).1 hz'X, hz'⟩
  · rintro ⟨z', hz'Y, hz'⟩
    exact ⟨z', (h z' (key z z' hz hz')).2 hz'Y, hz'⟩

theorem abs_ediv_eq_le {P : ℕ} (hP : 0 < P) {a b : ℤ} (h : a / (P : ℤ) = b / (P : ℤ)) :
    |a - b| ≤ (P : ℤ) := by
  have := abs_ediv_sub_le hP (a := a) (b := b) (r := 0) (by simp [h])
  simpa using this

theorem AgrB.cint {w : Fin d → ℤ} {R P : ℕ} (hP : 0 < P) {X Y : Set (Fin d → ℤ)}
    (h : AgrB w (R + P) X Y) : AgrB w R (cintZ P X) (cintZ P Y) := by
  have key : ∀ z z' : Fin d → ℤ, (∀ μ, |z μ - w μ| ≤ R) → (∀ μ, z' μ / (P : ℤ) = z μ / (P : ℤ)) →
      ∀ μ, |z' μ - w μ| ≤ (R + P : ℕ) := by
    intro z z' hz hz' μ
    have h1 := abs_ediv_eq_le hP (hz' μ)
    have h2 : |z' μ - w μ| ≤ |z' μ - z μ| + |z μ - w μ| := by
      have := abs_add_le (z' μ - z μ) (z μ - w μ)
      simpa using this
    have h3 := hz μ
    push_cast
    linarith
  intro z hz
  constructor
  · intro hzX z' hz'
    exact (h z' (key z z' hz hz')).1 (hzX z' hz')
  · intro hzY z' hz'
    exact (h z' (key z z' hz hz')).2 (hzY z' hz')

/-! ### The layers `Ω_n(X)` on integer lifts -/

/-- The recursion `minLayerAux` (P3 (4.5)-(4.6)) on integer sets: `t = 0` is the union of the
`𝒞_j`-cubes in `X`, and each step takes the cubes within `5 L` cubes of side `L^{j-(t+1)} M1`. -/
def layZ (L M1 j : ℕ) (X : Set (Fin d → ℤ)) : ℕ → Set (Fin d → ℤ)
  | 0 => cintZ (L ^ j * M1) X
  | t + 1 => nearZ (L ^ (j - (t + 1)) * M1) (5 * L) (layZ L M1 j X t)

/-- The layers `Ω_n(X)` of the minimal generating set `𝔹_j(X)` on integer sets. -/
def minLayerZ (L M1 j : ℕ) (X : Set (Fin d → ℤ)) (n : ℕ) : Set (Fin d → ℤ) :=
  if n ≤ j then layZ L M1 j X (j - n) else ∅

/-- The reading radius of `layZ L M1 j · t`. -/
def radL (L M1 j : ℕ) : ℕ → ℕ
  | 0 => L ^ j * M1
  | t + 1 => radL L M1 j t + (L ^ (j - (t + 1)) * M1) * (5 * L + 1)

/-- The displacement radius of `layZ L M1 j · t`. -/
def supL (L M1 j : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => supL L M1 j t + (L ^ (j - (t + 1)) * M1) * (5 * L + 1)

theorem radL_eq (L M1 j t : ℕ) : radL L M1 j t = L ^ j * M1 + supL L M1 j t := by
  induction t with
  | zero => simp [radL, supL]
  | succ t ih => simp only [radL, supL, ih]; ring

theorem supL_le (L M1 j : ℕ) (hL : 2 ≤ L) {t : ℕ} (ht : t ≤ j) :
    supL L M1 j t + 11 * (L ^ (j - t) * M1) ≤ 11 * (L ^ j * M1) := by
  induction t with
  | zero => simp [supL]
  | succ t ih =>
    have ih' := ih (by omega)
    have hj : j - t = (j - (t + 1)) + 1 := by omega
    rw [hj, pow_succ] at ih'
    simp only [supL]
    set p := L ^ (j - (t + 1)) * M1 with hp
    have e1 : L ^ (j - (t + 1)) * L * M1 = p * L := by rw [hp]; ring
    rw [e1] at ih'
    have hp0 : 0 ≤ p := Nat.zero_le _
    nlinarith

theorem radL_le (L M1 j : ℕ) (hL : 2 ≤ L) {t : ℕ} (ht : t ≤ j) :
    radL L M1 j t ≤ 12 * (L ^ j * M1) := by
  have := supL_le L M1 j hL ht
  rw [radL_eq]
  omega

theorem AgrB.lay {w : Fin d → ℤ} {R : ℕ} (L M1 j : ℕ) (hL : 0 < L) (hM1 : 0 < M1)
    {X Y : Set (Fin d → ℤ)} :
    ∀ t : ℕ, AgrB w (R + radL L M1 j t) X Y → AgrB w R (layZ L M1 j X t) (layZ L M1 j Y t) := by
  intro t
  induction t generalizing R with
  | zero =>
    intro h
    exact AgrB.cint (Nat.mul_pos (pow_pos hL _) hM1) h
  | succ t ih =>
    intro h
    simp only [layZ]
    refine AgrB.near (Nat.mul_pos (pow_pos hL _) hM1) ?_
    refine ih ?_
    refine h.mono (le_of_eq ?_)
    simp only [radL]
    ring

theorem AgrB.minLayer {w : Fin d → ℤ} {R : ℕ} (L M1 j : ℕ) (hL : 2 ≤ L) (hM1 : 0 < M1) (n : ℕ)
    {X Y : Set (Fin d → ℤ)} (h : AgrB w (R + 12 * (L ^ j * M1)) X Y) :
    AgrB w R (minLayerZ L M1 j X n) (minLayerZ L M1 j Y n) := by
  unfold minLayerZ
  by_cases hn : n ≤ j
  · simp only [hn, ↓reduceIte]
    refine AgrB.lay L M1 j (by omega) hM1 _ (h.mono ?_)
    have := radL_le L M1 j hL (t := j - n) (by omega)
    omega
  · simp only [hn, ↓reduceIte]
    intro z _
    exact Iff.rfl

theorem layZ_supp {w : Fin d → ℤ} (L M1 j : ℕ) (hL : 0 < L) (hM1 : 0 < M1) {X : Set (Fin d → ℤ)} :
    ∀ t : ℕ, w ∈ layZ L M1 j X t → ∃ z ∈ X, ∀ μ, |z μ - w μ| ≤ (supL L M1 j t : ℤ) := by
  intro t
  induction t generalizing w with
  | zero =>
    intro h
    refine ⟨w, h w fun μ => rfl, fun μ => by simp [supL]⟩
  | succ t ih =>
    intro h
    simp only [layZ] at h
    obtain ⟨z, hz, hzd⟩ := h
    obtain ⟨z', hz'X, hz'd⟩ := ih hz
    refine ⟨z', hz'X, fun μ => ?_⟩
    have h1 := abs_ediv_sub_le (Nat.mul_pos (pow_pos hL _) hM1) (hzd μ)
    have h2 : |z' μ - w μ| ≤ |z' μ - z μ| + |z μ - w μ| := by
      have := abs_add_le (z' μ - z μ) (z μ - w μ)
      simpa using this
    have h3 := hz'd μ
    simp only [supL]
    push_cast at h1 h3 ⊢
    nlinarith [h1, h2, h3]

theorem minLayerZ_supp {w : Fin d → ℤ} (L M1 j : ℕ) (hL : 2 ≤ L) (hM1 : 0 < M1)
    {X : Set (Fin d → ℤ)} (n : ℕ) (h : w ∈ minLayerZ L M1 j X n) :
    ∃ z ∈ X, ∀ μ, |z μ - w μ| ≤ ((11 * (L ^ j * M1) : ℕ) : ℤ) := by
  unfold minLayerZ at h
  by_cases hn : n ≤ j
  · simp only [hn, ↓reduceIte] at h
    obtain ⟨z, hz, hzd⟩ := layZ_supp L M1 j (by omega) hM1 _ h
    refine ⟨z, hz, fun μ => (hzd μ).trans ?_⟩
    have := supL_le L M1 j hL (t := j - n) (by omega)
    exact_mod_cast (by omega : supL L M1 j (j - n) ≤ 11 * (L ^ j * M1))
  · simp [hn] at h

/-- The layers of the boundary family `Ω_n = (Ω_n(W) ∖ Om) ∪ (Ω_n(U) ∩ Om)` on integer sets. -/
def bdLayZ (L M1 k : ℕ) (W U Om : Set (Fin d → ℤ)) (n : ℕ) : Set (Fin d → ℤ) :=
  (minLayerZ L M1 k W n \ Om) ∪ (minLayerZ L M1 (k + 1) U n ∩ Om)

theorem AgrB.bdLay {w : Fin d → ℤ} {R : ℕ} (L M1 k : ℕ) (hL : 2 ≤ L) (hM1 : 0 < M1)
    {W₁ W₂ U₁ U₂ Om₁ Om₂ : Set (Fin d → ℤ)}
    (hW : AgrB w (R + 12 * (L ^ (k + 1) * M1)) W₁ W₂)
    (hU : AgrB w (R + 12 * (L ^ (k + 1) * M1)) U₁ U₂) (hOm : AgrB w R Om₁ Om₂) (n : ℕ) :
    AgrB w R (bdLayZ L M1 k W₁ U₁ Om₁ n) (bdLayZ L M1 k W₂ U₂ Om₂ n) := by
  unfold bdLayZ
  have hle : L ^ k * M1 ≤ L ^ (k + 1) * M1 :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (Nat.le_succ k))
  refine AgrB.union (AgrB.diff ?_ hOm) (AgrB.inter ?_ hOm)
  · exact AgrB.minLayer L M1 k hL hM1 n (hW.mono (by omega))
  · exact AgrB.minLayer L M1 (k + 1) hL hM1 n hU

theorem bdLayZ_supp {w : Fin d → ℤ} (L M1 k : ℕ) (hL : 2 ≤ L) (hM1 : 0 < M1)
    {W U Om : Set (Fin d → ℤ)} (hWU : W ⊆ U) (n : ℕ) (h : w ∈ bdLayZ L M1 k W U Om n) :
    ∃ z ∈ U, ∀ μ, |z μ - w μ| ≤ ((11 * (L ^ (k + 1) * M1) : ℕ) : ℤ) := by
  have hle : L ^ k * M1 ≤ L ^ (k + 1) * M1 :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (Nat.le_succ k))
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · obtain ⟨z, hz, hzd⟩ := minLayerZ_supp L M1 k hL hM1 n h
    exact ⟨z, hWU hz, fun μ => (hzd μ).trans (by exact_mod_cast Nat.mul_le_mul_left 11 hle)⟩
  · exact minLayerZ_supp L M1 (k + 1) hL hM1 n h

end Balaban.RootFSpine
