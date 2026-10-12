/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.ReflectionGreen
public import Balaban.Localization.Cover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The two cube regimes (NC3, Lemma R0)

An *aligned cube* of scale `m` (LOCALIZATION.md §1.3, §3.1) is the coordinate cube of side
`5 M₁ L^m = 5 L^(m + m₁)` with corner `c` (`L^(m + m₁) ∣ c`) whose central `M₁ L^m`-cell lies in
the layer `m`.  With the separation `ϱ ≥ 4 d L^(m₁ + 1)`:

* `Balaban.Reflection.AlignedCube.foldSetting`: if `m ≥ 2` the cube and its one-site collar lie in
  `Ω_{m-1} ⊆ Ω₁`, so the cube folds (`FoldSetting` for `q = min k (m + 1)`);
* `Balaban.Reflection.AlignedCube.noTop`: for every `m ≥ 1` the cube meets no `Ω_{q+1}`.
-/

@[expose] public section

namespace Balaban.Reflection

open Balaban Balaban.Multiscale Balaban.Localization

/-- The point of the torus `(ℤ/ℓℤ)^d` with chart coordinates `t` in the cube with corner `c`. -/
def chartPt (ℓ : ℕ) {d : ℕ} (c t : Fin d → ℕ) : Torus d ℓ := fun i => ((c i + t i : ℕ) : ZMod ℓ)

section Dist

variable {d ℓ : ℕ} [NeZero ℓ]

theorem natAbs_cycRep_single_le (μ i : Fin d) :
    (Green.cycRep ((Pi.single μ (1 : ZMod ℓ) : Torus d ℓ) i)).natAbs ≤ if i = μ then 1 else 0 := by
  by_cases h : i = μ
  · subst h
    simp only [Pi.single_eq_same, ↓reduceIte]
    have := Green.natAbs_cycRep_le_of_cast (1 : ZMod ℓ) 1 (by simp)
    simpa using this
  · simp [h, Green.natAbs_cycRep_zero]

theorem torusDist_add_single_le (x y : Torus d ℓ) (μ : Fin d) :
    Green.torusDist d ℓ (x + Pi.single μ 1) y ≤ Green.torusDist d ℓ x y + 1 := by
  unfold Green.torusDist
  have h1 : ∀ i, ((Green.cycRep ((x + (Pi.single μ 1 : Torus d ℓ)) i - y i)).natAbs : ℝ) ≤
      (Green.cycRep (x i - y i)).natAbs + (if i = μ then 1 else 0) := by
    intro i
    have e : (x + (Pi.single μ 1 : Torus d ℓ)) i - y i = (x i - y i) + (Pi.single μ 1 : Torus d ℓ) i := by
      simp only [Pi.add_apply]; ring
    rw [e]
    have := Green.natAbs_cycRep_add_le (x i - y i) ((Pi.single μ 1 : Torus d ℓ) i)
    have h2 := natAbs_cycRep_single_le (ℓ := ℓ) μ i
    have h3 : ((Green.cycRep ((x i - y i) + (Pi.single μ 1 : Torus d ℓ) i)).natAbs : ℝ) ≤
        (Green.cycRep (x i - y i)).natAbs + (Green.cycRep ((Pi.single μ 1 : Torus d ℓ) i)).natAbs :=
      by exact_mod_cast this
    have h4 : ((Green.cycRep ((Pi.single μ 1 : Torus d ℓ) i)).natAbs : ℝ) ≤ if i = μ then 1 else 0 := by
      split_ifs at h2 ⊢ <;> exact_mod_cast h2
    linarith
  calc _ ≤ ∑ i, (((Green.cycRep (x i - y i)).natAbs : ℝ) + (if i = μ then 1 else 0)) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = _ := by simp [Finset.sum_add_distrib]

theorem torusDist_sub_single_le (x y : Torus d ℓ) (μ : Fin d) :
    Green.torusDist d ℓ (x - Pi.single μ 1) y ≤ Green.torusDist d ℓ x y + 1 := by
  unfold Green.torusDist
  have h1 : ∀ i, ((Green.cycRep ((x - (Pi.single μ 1 : Torus d ℓ)) i - y i)).natAbs : ℝ) ≤
      (Green.cycRep (x i - y i)).natAbs + (if i = μ then 1 else 0) := by
    intro i
    have e : (x - (Pi.single μ 1 : Torus d ℓ)) i - y i = (x i - y i) + (-(Pi.single μ 1 : Torus d ℓ) i) := by
      simp only [Pi.sub_apply]; ring
    rw [e]
    have := Green.natAbs_cycRep_add_le (x i - y i) (-(Pi.single μ 1 : Torus d ℓ) i)
    rw [Green.natAbs_cycRep_neg] at this
    have h2 := natAbs_cycRep_single_le (ℓ := ℓ) μ i
    have h3 : ((Green.cycRep ((x i - y i) + (-(Pi.single μ 1 : Torus d ℓ) i))).natAbs : ℝ) ≤
        (Green.cycRep (x i - y i)).natAbs + (Green.cycRep ((Pi.single μ 1 : Torus d ℓ) i)).natAbs :=
      by exact_mod_cast this
    have h4 : ((Green.cycRep ((Pi.single μ 1 : Torus d ℓ) i)).natAbs : ℝ) ≤ if i = μ then 1 else 0 := by
      split_ifs at h2 ⊢ <;> exact_mod_cast h2
    linarith
  calc _ ≤ ∑ i, (((Green.cycRep (x i - y i)).natAbs : ℝ) + (if i = μ then 1 else 0)) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = _ := by simp [Finset.sum_add_distrib]

/-- Points of the cube `{c + t : t < 5B}^d` are within `3 d B` of the centre of its central cell. -/
theorem torusDist_cube_centre_le {B : ℕ} {c : Fin d → ℕ} {x : Torus d ℓ}
    (hx : x ∈ cubeSet ℓ (5 * B) c) :
    Green.torusDist d ℓ x (chartPt ℓ c fun _ => 2 * B) ≤ 3 * d * B := by
  unfold Green.torusDist
  have h := mem_cubeSet.1 hx
  have hi : ∀ i, ((Green.cycRep (x i - chartPt ℓ c (fun _ => 2 * B) i)).natAbs : ℝ) ≤ 3 * B := by
    intro i
    obtain ⟨t, ht, hxt⟩ := h i
    have e : x i - chartPt ℓ c (fun _ => 2 * B) i = (((t : ℤ) - 2 * B : ℤ) : ZMod ℓ) := by
      rw [hxt]; simp [chartPt]
    have := Green.natAbs_cycRep_le_of_cast _ _ e.symm
    have h2 : ((t : ℤ) - 2 * B).natAbs ≤ 3 * B := by omega
    exact_mod_cast this.trans h2
  calc _ ≤ ∑ _i : Fin d, (3 * (B : ℝ)) := Finset.sum_le_sum fun i _ => hi i
    _ = 3 * d * B := by simp; ring

end Dist

/-- **The aligned cube of scale `m`** (LOCALIZATION.md §1.3): corner `c` (`L^(m+m₁) ∣ c`), side
`5 L^(m+m₁) = s L^q`, `q = min k (m+1)`, a torus larger than the cube, the central cell in the layer
`m`, and the separation constant of the localization setting. -/
structure AlignedCube {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    (G : GeneratingSet d L N₀ k ϱ) (m₁ m q s : ℕ) (c : Fin d → ℕ) : Prop where
  one_le_m : 1 ≤ m
  m_le : m ≤ k
  one_le_m₁ : 1 ≤ m₁
  hq : q = min k (m + 1)
  hS : s * L ^ q = 5 * L ^ (m + m₁)
  dvd : ∀ i, L ^ (m + m₁) ∣ c i
  side : 5 * L ^ (m + m₁) < N₀ * L ^ k
  centre : chartPt (N₀ * L ^ k) c (fun _ => 2 * L ^ (m + m₁)) ∈ G.layer m
  rho : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ

namespace AlignedCube

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {m₁ m q s : ℕ} {c : Fin d → ℕ}

theorem cubeOf_eq (hc : AlignedCube G m₁ m q s c) :
    cubeOf N₀ L k q s c = cubeSet (N₀ * L ^ k) (5 * L ^ (m + m₁)) c := by
  unfold cubeOf
  rw [hc.hS]

theorem dist_le (hc : AlignedCube G m₁ m q s c) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ cubeOf N₀ L k q s c) :
    Green.torusDist d (N₀ * L ^ k) x (chartPt (N₀ * L ^ k) c fun _ => 2 * L ^ (m + m₁)) ≤
      3 * d * L ^ (m + m₁) := by
  rw [hc.cubeOf_eq] at hx
  exact_mod_cast torusDist_cube_centre_le hx

theorem noTop (hc : AlignedCube G m₁ m q s c) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ cubeOf N₀ L k q s c) : x ∉ G.Ω (q + 1) := by
  intro hxΩ
  have hqk : q ≤ k := hc.hq ▸ min_le_left _ _
  by_cases hk : q = k
  · rw [hk, G.top] at hxΩ
    exact absurd hxΩ (Finset.notMem_empty _)
  · have hq : q = m + 1 := by
      rw [hc.hq] at hk ⊢
      omega
    have hmk1 : m + 1 < k := by omega
    have hz := hc.centre
    rw [GeneratingSet.mem_layer] at hz
    have hsep := G.separation (m + 1) (by omega) hmk1 _ hz.2 x (by rw [hq] at hxΩ; exact hxΩ)
    have hd := hc.dist_le hx
    rw [Green.torusDist_comm_gen] at hsep
    have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    have hdist : Green.torusDist d (N₀ * L ^ k) x
        (chartPt (N₀ * L ^ k) c fun _ => 2 * L ^ (m + m₁)) ≤ 3 * d * (L : ℝ) ^ (m + m₁) := by
      exact_mod_cast hd
    have hcalc : 3 * (d : ℝ) * (L : ℝ) ^ (m + m₁) ≤ ϱ * (L : ℝ) ^ (m + 1) := by
      have h1 : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) * (L : ℝ) ^ (m + 1) ≤ ϱ * (L : ℝ) ^ (m + 1) :=
        mul_le_mul_of_nonneg_right hc.rho (by positivity)
      have hd0 : (0 : ℝ) ≤ d := by positivity
      have hLp : (0 : ℝ) < (L : ℝ) ^ (m + m₁) := by positivity
      have e : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) * (L : ℝ) ^ (m + 1) =
          4 * d * L ^ 2 * (L : ℝ) ^ (m + m₁) := by
        rw [pow_add, pow_add, pow_succ]; ring
      have hL2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL
      have := mul_nonneg (mul_nonneg hd0 hLp.le) (by linarith : (0 : ℝ) ≤ 4 * (L : ℝ) ^ 2 - 3)
      nlinarith
    linarith

/-- For `m ≥ 2` the cube and its one-site collar lie in `Ω_{m-1}`. -/
theorem mem_Ω_pred (hc : AlignedCube G m₁ m q s c) (hm2 : 2 ≤ m) {y : Torus d (N₀ * L ^ k)}
    (hy : Green.torusDist d (N₀ * L ^ k) y
      (chartPt (N₀ * L ^ k) c fun _ => 2 * L ^ (m + m₁)) ≤ 4 * d * (L : ℝ) ^ (m + m₁)) :
    y ∈ G.Ω (m - 1) := by
  have hz := (G.mem_layer.1 hc.centre).1
  rw [Green.torusDist_comm_gen] at hy
  exact mem_pred_cube m₁ G hc.rho hm2 hc.m_le hz hy

theorem foldSetting (hc : AlignedCube G m₁ m q s c) (hm2 : 2 ≤ m) : FoldSetting G q s c := by
  have hqk : q ≤ k := hc.hq ▸ min_le_left _ _
  have hq1 : 1 ≤ q := by rw [hc.hq]; have := hc.m_le; have := hc.one_le_m; omega
  have hqm : q ≤ m + 1 := hc.hq ▸ min_le_right _ _
  have hΩ : ∀ y, Green.torusDist d (N₀ * L ^ k) y
      (chartPt (N₀ * L ^ k) c fun _ => 2 * L ^ (m + m₁)) ≤ 4 * d * (L : ℝ) ^ (m + m₁) →
      y ∈ G.Ω 1 := fun y hy =>
    G.Ω_antitone le_rfl (by omega) (by have := hc.m_le; omega) (hc.mem_Ω_pred hm2 hy)
  refine ⟨hq1, hqk, ?_, ?_, ?_, ?_, ?_, fun x hx => hc.noTop hx⟩
  · have h5 : 0 < 5 * L ^ (m + m₁) := Nat.mul_pos (by norm_num) (L_pow_pos L _)
    rw [← hc.hS] at h5
    exact Nat.pos_of_mul_pos_right h5
  · rw [hc.hS]; exact hc.side
  · intro i
    exact (pow_dvd_pow L (by have := hc.one_le_m₁; omega)).trans (hc.dvd i)
  · intro x hx
    refine hΩ x ?_
    have := hc.dist_le hx
    have hd : (0 : ℝ) ≤ d * (L : ℝ) ^ (m + m₁) := by positivity
    calc _ ≤ ((3 * d * L ^ (m + m₁) : ℕ) : ℝ) := by exact_mod_cast this
      _ ≤ _ := by push_cast; nlinarith
  · intro x hx μ
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Fin.pos μ
    have hB1 : (1 : ℝ) ≤ (L : ℝ) ^ (m + m₁) :=
      one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
    have h0 : Green.torusDist d (N₀ * L ^ k) x
        (chartPt (N₀ * L ^ k) c fun _ => 2 * L ^ (m + m₁)) ≤ 3 * d * (L : ℝ) ^ (m + m₁) := by
      exact_mod_cast hc.dist_le hx
    have hle : 3 * (d : ℝ) * (L : ℝ) ^ (m + m₁) + 1 ≤ 4 * d * (L : ℝ) ^ (m + m₁) := by
      nlinarith
    exact ⟨hΩ _ ((torusDist_add_single_le _ _ μ).trans (by linarith)),
      hΩ _ ((torusDist_sub_single_le _ _ μ).trans (by linarith))⟩

end AlignedCube

end Balaban.Reflection
