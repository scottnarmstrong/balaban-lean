/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Expansion
public import Balaban.Localization.DecoupledBackgroundLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Glue between the polymer geometry (`Pset`, `X1`, `Ysites`) and the decoupled objects (`cubeP`,
`parCubes`, `DecParams`)

* `cell_subset_box`: a cell of side `a` through a point of an aligned box of side `R` (`a ∣ R`) lies
  in the box;
* `Pset_subset_of_not_disjoint`: a `π¹`-cube of a layer `n ≤ K` meeting a union `X₁` of aligned
  `π'_K`-cubes lies in `X₁` (so the parameter cubes are exactly the cubes disjoint from `X₁`);
* `ParIdx`, `extParams`: the index type of the decoupling parameters of Lemma AE (the cubes of the
  cover disjoint from `X₁`) and the extension of a vector `s ∈ ℂ^{ParIdx}` by `1` to the vector
  `DecParams G` of the decoupled objects.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset

section Cells

variable {d n : ℕ}

theorem cell_subset_box [NeZero n] {a R : ℕ} (ha : a ∣ n) (ha0 : 0 < a) (hR : a ∣ R)
    {b z : Torus d n} (hb : Aligned a b) (hz : z ∈ box b R) : box (cbase a z) a ⊆ box b R := by
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨R', rfl⟩ := hR
  rw [cbase_add ha hb]
  rintro x ⟨r, hr, rfl⟩
  refine ⟨(fun μ => w μ - w μ % a) + r, fun μ => ?_, ?_⟩
  · have h1 : w μ - w μ % a = a * (w μ / a) := by
      have := Nat.div_add_mod (w μ) a; omega
    have h2 : w μ / a < R' := by
      rw [Nat.div_lt_iff_lt_mul ha0, mul_comm]; exact hw μ
    simp only [Pi.add_apply]
    rw [h1]
    have := hr μ
    have h3 : a * (w μ / a) + a ≤ a * R' := by
      calc a * (w μ / a) + a = a * (w μ / a + 1) := by ring
        _ ≤ a * R' := Nat.mul_le_mul_left a h2
    omega
  · rw [natT_add, add_assoc]

theorem mem_box_cbase_of_sameCell [NeZero n] {s : ℕ} (hs : 0 < s) {x y : Torus d n}
    (h : ∀ μ, (y μ).val / s = (x μ).val / s) : y ∈ box (cbase s x) s := by
  have : cbase s y = cbase s x := by funext μ; simp only [cbase]; rw [h μ]
  rw [← this]; exact mem_box_cbase hs y

end Cells

section Par

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}

theorem aligned_of_dvd {n a s : ℕ} (hsa : s ∣ a) {b : Torus d n} (hb : Aligned a b) : Aligned s b :=
  fun μ => Nat.mod_eq_zero_of_dvd (hsa.trans (Nat.dvd_of_mod_eq_zero (hb μ)))

/-- A `π¹`-cube of a layer `n ≤ K` meeting a union `X₁` of aligned `π'_K`-cubes lies in `X₁`. -/
theorem Pset_subset_of_not_disjoint {X₁ : Set (CTorus d L N₁ m₁ K)} (hS : PolySetup G m₀ X₁)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) (h : ¬ Disjoint (Pset m₁ q) X₁) :
    Pset m₁ q ⊆ X₁ := by
  obtain ⟨⟨hq1, hqK⟩, -, -⟩ := (mem_cubeIdx G).1 hq
  obtain ⟨x, hxP, hxX⟩ := Set.not_disjoint_iff.1 h
  obtain ⟨b, hbal, hxb, hbX⟩ := hS.X₁_cubes x hxX
  have hs0 : 0 < L ^ (q.1 + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hsa : L ^ (q.1 + m₁) ∣ cellSide L m₀ m₁ K := by
    unfold cellSide; exact pow_dvd_pow L (by omega)
  have hsN : L ^ (q.1 + m₁) ∣ (N₁ * L ^ m₁) * L ^ K :=
    hsa.trans (cellSide_dvd (K := K) (m₁ := m₁) hS.hN le_rfl)
  intro y hyP
  have hyx : ∀ μ, (y μ).val / L ^ (q.1 + m₁) = (x μ).val / L ^ (q.1 + m₁) := fun μ =>
    (hyP μ).trans (hxP μ).symm
  have h1 := mem_box_cbase_of_sameCell hs0 hyx
  have h2 := cell_subset_box hsN hs0 (dvd_mul_of_dvd_right hsa L) (aligned_of_dvd hsa hbal) hxb h1
  exact hbX h2

/-- The decoupling parameters of Lemma AE: the cubes of the cover disjoint from `X₁`. -/
abbrev ParIdx (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (X₁ : Set (CTorus d L N₁ m₁ K)) : Type :=
  {i : ↥(cubeIdx G) // Disjoint (Pset m₁ i.1) X₁}

noncomputable instance (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (X₁ : Set (CTorus d L N₁ m₁ K)) : Fintype (ParIdx G X₁) := by
  classical exact Subtype.fintype _

noncomputable instance (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (X₁ : Set (CTorus d L N₁ m₁ K)) : DecidableEq (ParIdx G X₁) := Classical.decEq _

open Classical in
/-- The extension by `1` of a vector of decoupling parameters. -/
noncomputable def extParams (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (X₁ : Set (CTorus d L N₁ m₁ K)) (s : ParIdx G X₁ → ℂ) : DecParams G :=
  fun P => if h : Disjoint (Pset m₁ P.1) X₁ then s ⟨P, h⟩ else 1

theorem extParams_par {X₁ : Set (CTorus d L N₁ m₁ K)} (s : ParIdx G X₁ → ℂ) (i : ParIdx G X₁) :
    extParams G X₁ s i.1 = s i := by
  classical
  simp [extParams, i.2]

theorem extParams_nonpar {X₁ : Set (CTorus d L N₁ m₁ K)} (s : ParIdx G X₁ → ℂ)
    (P : ↥(cubeIdx G)) (h : ¬ Disjoint (Pset m₁ P.1) X₁) : extParams G X₁ s P = 1 := by
  classical
  simp [extParams, h]

theorem extParams_one {X₁ : Set (CTorus d L N₁ m₁ K)} :
    extParams G X₁ (1 : ParIdx G X₁ → ℂ) = fun _ => 1 := by
  classical
  funext P
  unfold extParams
  split_ifs <;> rfl

theorem norm_extParams_le {X₁ : Set (CTorus d L N₁ m₁ K)} {s : ParIdx G X₁ → ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hs : ∀ i, ‖s i‖ ≤ R) (P : ↥(cubeIdx G)) : ‖extParams G X₁ s P‖ ≤ R := by
  classical
  unfold extParams
  split_ifs with h
  · exact hs _
  · simpa using hR

theorem norm_extParams_lt {X₁ : Set (CTorus d L N₁ m₁ K)} {s : ParIdx G X₁ → ℂ} {R : ℝ}
    (hR : 1 < R) (hs : ∀ i, ‖s i‖ < R) (P : ↥(cubeIdx G)) : ‖extParams G X₁ s P‖ < R := by
  classical
  unfold extParams
  split_ifs with h
  · exact hs _
  · simpa using hR

theorem analyticAt_extParams {X₁ : Set (CTorus d L N₁ m₁ K)} (s : ParIdx G X₁ → ℂ) :
    AnalyticAt ℂ (extParams G X₁) s := by
  classical
  refine analyticAt_pi_iff.2 fun P => ?_
  unfold extParams
  by_cases h : Disjoint (Pset m₁ P.1) X₁
  · simp only [h, ↓reduceDIte]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ParIdx G X₁ => ℂ) ⟨P, h⟩).analyticAt s
  · simp only [h, ↓reduceDIte]
    exact analyticAt_const

end Par

end Balaban.Localization
