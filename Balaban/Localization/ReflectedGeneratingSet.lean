/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Reflection
public import Balaban.Localization.CubeAligned
public import Balaban.Multiscale.GeneratingSet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The reflected generating set (NC3, Lemma R1)

Let `G` be a generating set of the torus `(ℤ/N₀ L^k ℤ)^d` and `□ = {c + t : t < S}^d`, `S = s L^q`,
a coordinate cube whose faces are `L^q`-aligned, `1 ≤ q ≤ k`, which lies (with its one-site collar)
in `Ω₁` and meets no `Ω_{q+1}` (`Balaban.Reflection.FoldSetting`).  The fold
`Balaban.Reflection.foldTo : (ℤ/2S ℤ)^d → □` (coordinatewise reflection, `foldMap`) pulls the layer
structure of `G|□` back to the doubled torus `(ℤ/(2s) L^q ℤ)^d`:

* `Balaban.Reflection.reflectedGS`: the **reflected generating set** `Ω*_j = F⁻¹(Ω_j)`,
  `1 ≤ j ≤ q`, `Ω*_{q+1} = ∅`, a `GeneratingSet d L (2 s) q ϱ`;
* `Balaban.Reflection.mem_layer_reflectedGS_iff`, `layerIndex_reflectedGS`, `spacing_reflectedGS`:
  the layer index and spacing of the reflected set are those of `G` at the folded point;
* `Balaban.Reflection.reflectedGS_Ω_one`: `Ω*_1` is the whole doubled torus;
* `Balaban.Reflection.foldTo_jBlock_eq`, `foldTo_injOn_jBlock`: the fold takes a `j`-block to a
  `j`-block and is injective on it, for `j ≤ q`.
-/

@[expose] public section

namespace Balaban.Reflection

open Balaban Balaban.Multiscale Balaban.Localization

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The fold `(ℤ/(2s) L^q ℤ)^d → (ℤ/N₀ L^k ℤ)^d` onto the cube with corner `c` and side `s L^q`. -/
def foldTo (N₀ L k q s : ℕ) (c : Fin d → ℕ) (p : Torus d (2 * s * L ^ q)) :
    Torus d (N₀ * L ^ k) :=
  foldMap (N₀ * L ^ k) (s * L ^ q) (2 * s * L ^ q) c p

/-- The cube `{c + t : t < s L^q}^d` of the torus `(ℤ/N₀ L^k ℤ)^d`. -/
noncomputable def cubeOf (N₀ L k q s : ℕ) [NeZero N₀] [NeZero L] (c : Fin d → ℕ) :
    Finset (Torus d (N₀ * L ^ k)) :=
  cubeSet (N₀ * L ^ k) (s * L ^ q) c

/-- **The cube-folding hypotheses** for a generating set `G`, depth `q` (`1 ≤ q ≤ k`), side
`s L^q` and corner `c` (`L^q ∣ c`): the cube is smaller than the torus, lies with its one-site
collar in `Ω₁`, and meets no `Ω_{q+1}`.  (These are consequences of the localization separation
hypotheses; see `Balaban.Reflection.cube_scale_regimes`.) -/
structure FoldSetting (G : GeneratingSet d L N₀ k ϱ) (q s : ℕ) (c : Fin d → ℕ) : Prop where
  one_le_q : 1 ≤ q
  q_le : q ≤ k
  s_pos : 0 < s
  side : s * L ^ q < N₀ * L ^ k
  dvd : ∀ i, L ^ q ∣ c i
  mem_Ω : ∀ x ∈ cubeOf N₀ L k q s c, x ∈ G.Ω 1
  collar : ∀ x ∈ cubeOf N₀ L k q s c, ∀ μ : Fin d,
    x + Pi.single μ 1 ∈ G.Ω 1 ∧ x - Pi.single μ 1 ∈ G.Ω 1
  noTop : ∀ x ∈ cubeOf N₀ L k q s c, x ∉ G.Ω (q + 1)

theorem L_pow_pos (L j : ℕ) [NeZero L] : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j

section Fold

variable {G : GeneratingSet d L N₀ k ϱ} {q s : ℕ} {c : Fin d → ℕ} [NeZero s]

theorem two_mul_side (L q s : ℕ) : 2 * s * L ^ q = 2 * (s * L ^ q) := by ring

theorem foldTo_mem_cubeOf (p : Torus d (2 * s * L ^ q)) :
    foldTo N₀ L k q s c p ∈ cubeOf N₀ L k q s c :=
  foldMap_mem_cubeSet (two_mul_side L q s) p

theorem foldTo_mem_Ω_one (h : FoldSetting G q s c) (p : Torus d (2 * s * L ^ q)) :
    foldTo N₀ L k q s c p ∈ G.Ω 1 :=
  h.mem_Ω _ (foldTo_mem_cubeOf p)

theorem foldTo_not_mem_Ω_top (h : FoldSetting G q s c) (p : Torus d (2 * s * L ^ q)) :
    foldTo N₀ L k q s c p ∉ G.Ω (q + 1) :=
  h.noTop _ (foldTo_mem_cubeOf p)

theorem foldTo_torusDist_le (h : FoldSetting G q s c) (p p' : Torus d (2 * s * L ^ q)) :
    Green.torusDist d (N₀ * L ^ k) (foldTo N₀ L k q s c p) (foldTo N₀ L k q s c p') ≤
      Green.torusDist d (2 * s * L ^ q) p p' :=
  torusDist_foldMap_le (two_mul_side L q s) (Nat.mul_pos h.s_pos (L_pow_pos L _)) p p'

omit [NeZero s] in
/-- Block arithmetic for `j ≤ q`. -/
theorem fold_block_arith (h : FoldSetting G q s c) {j : ℕ} (hj : j ≤ q) :
    s * L ^ q = L ^ j * (s * L ^ (q - j)) ∧ N₀ * L ^ k = L ^ j * (N₀ * L ^ (k - j)) ∧
      ∀ i, ∃ C, c i = L ^ j * C := by
  refine ⟨?_, side_eq (h.q_le |> hj.trans), ?_⟩
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hj
    simp only [Nat.add_sub_cancel_left, pow_add]
    ring
  · intro i
    obtain ⟨C, hC⟩ := h.dvd i
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hj
    exact ⟨L ^ t * C, by rw [hC, pow_add]; ring⟩

theorem foldTo_jBlock_eq (h : FoldSetting G q s c) {j : ℕ} (hj : j ≤ q)
    {p p' : Torus d (2 * s * L ^ q)}
    (hp : jBlock d L (2 * s) q j p = jBlock d L (2 * s) q j p') :
    jBlock d L N₀ k j (foldTo N₀ L k q s c p) = jBlock d L N₀ k j (foldTo N₀ L k q s c p') := by
  obtain ⟨h1, h2, h3⟩ := fold_block_arith h hj
  have hL : 0 < L ^ j := L_pow_pos L _
  have hcell := sameCell_of_jBlock_eq hj hp
  refine jBlock_eq_of_sameCell fun i => ?_
  exact foldMap_div_eq (two_mul_side L q s) hL h1 h2 h3 (fun i => hcell i) i

theorem foldTo_injOn_jBlock (h : FoldSetting G q s c) {j : ℕ} (hj : j ≤ q)
    {p p' : Torus d (2 * s * L ^ q)}
    (hp : jBlock d L (2 * s) q j p = jBlock d L (2 * s) q j p')
    (hF : foldTo N₀ L k q s c p = foldTo N₀ L k q s c p') : p = p' := by
  obtain ⟨h1, -, -⟩ := fold_block_arith h hj
  have hL : 0 < L ^ j := L_pow_pos L _
  have hcell := sameCell_of_jBlock_eq hj hp
  exact foldMap_injOn_block (two_mul_side L q s) hL h1 h.side (fun i => hcell i) hF

open scoped Classical in
/-- The domains of the reflected generating set: `Ω*_j = F⁻¹(Ω_j)` for `j ≤ q`, empty above. -/
noncomputable def reflΩ (G : GeneratingSet d L N₀ k ϱ) (q s : ℕ) [NeZero s] (c : Fin d → ℕ)
    (j : ℕ) : Finset (Torus d (2 * s * L ^ q)) :=
  if j ≤ q then Finset.univ.filter fun p => foldTo N₀ L k q s c p ∈ G.Ω j else ∅

theorem mem_reflΩ_iff {j : ℕ} (hj : j ≤ q) {p : Torus d (2 * s * L ^ q)} :
    p ∈ reflΩ G q s c j ↔ foldTo N₀ L k q s c p ∈ G.Ω j := by
  simp [reflΩ, hj]

theorem not_mem_reflΩ_of_lt {j : ℕ} (hj : q < j) (p : Torus d (2 * s * L ^ q)) :
    p ∉ reflΩ G q s c j := by
  simp [reflΩ, not_le.2 hj]

/-- **The reflected generating set** (Lemma R1): `Ω*_j = F⁻¹(Ω_j)` for `1 ≤ j ≤ q`,
`Ω*_{q+1} = ∅`, on the doubled torus `(ℤ/(2s) L^q ℤ)^d`, with the separation constant `ϱ` of `G`. -/
noncomputable def reflectedGS (G : GeneratingSet d L N₀ k ϱ) {q s : ℕ} [NeZero s]
    {c : Fin d → ℕ} (h : FoldSetting G q s c) : GeneratingSet d L (2 * s) q ϱ where
  Ω := reflΩ G q s c
  top := by
    ext p
    simp [reflΩ]
  subset := by
    intro j hj1 hjq p hp
    by_cases hj : j + 1 ≤ q
    · rw [mem_reflΩ_iff hj] at hp
      rw [mem_reflΩ_iff hjq]
      exact G.subset j hj1 (hjq.trans h.q_le) hp
    · exact absurd hp (not_mem_reflΩ_of_lt (by omega) p)
  blockUnion := by
    intro j hj1 hjq p p' hpp
    rw [mem_reflΩ_iff hjq, mem_reflΩ_iff hjq]
    exact G.blockUnion j hj1 (hjq.trans h.q_le) _ _ (foldTo_jBlock_eq h hjq hpp)
  separation := by
    intro j hj1 hjq p hp p' hp'
    have hj' : j + 1 ≤ q := hjq
    rw [mem_reflΩ_iff (by omega)] at hp
    rw [mem_reflΩ_iff hj'] at hp'
    exact (G.separation j hj1 (lt_of_lt_of_le hjq h.q_le) _ hp _ hp').trans_le (foldTo_torusDist_le h p p')

theorem reflectedGS_Ω (h : FoldSetting G q s c) (j : ℕ) :
    (reflectedGS G h).Ω j = reflΩ G q s c j := rfl

/-- `Ω*_1` is the whole doubled torus. -/
theorem mem_reflectedGS_Ω_one (h : FoldSetting G q s c) (p : Torus d (2 * s * L ^ q)) :
    p ∈ (reflectedGS G h).Ω 1 := by
  rw [reflectedGS_Ω, mem_reflΩ_iff h.one_le_q]
  exact foldTo_mem_Ω_one h p

theorem mem_reflectedGS_Ω_iff (h : FoldSetting G q s c) {j : ℕ} (hj : j ≤ q)
    (p : Torus d (2 * s * L ^ q)) :
    p ∈ (reflectedGS G h).Ω j ↔ foldTo N₀ L k q s c p ∈ G.Ω j := by
  rw [reflectedGS_Ω, mem_reflΩ_iff hj]

/-- The layers of the reflected set are the pull-backs of the layers of `G`, `1 ≤ j ≤ q`. -/
theorem mem_layer_reflectedGS_iff (h : FoldSetting G q s c) {j : ℕ} (hjq : j ≤ q)
    (p : Torus d (2 * s * L ^ q)) :
    p ∈ (reflectedGS G h).layer j ↔ foldTo N₀ L k q s c p ∈ G.layer j := by
  rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer, mem_reflectedGS_Ω_iff h hjq]
  by_cases hjq' : j + 1 ≤ q
  · rw [mem_reflectedGS_Ω_iff h hjq']
  · have : j = q := by omega
    subst this
    exact and_congr_right fun _ => ⟨fun _ => foldTo_not_mem_Ω_top h p,
      fun _ hmem => not_mem_reflΩ_of_lt (by omega) p hmem⟩

/-- The layer index of the reflected set at `p` is the layer index of `G` at the folded point. -/
theorem layerIndex_reflectedGS (h : FoldSetting G q s c) (p : Torus d (2 * s * L ^ q)) :
    (reflectedGS G h).layerIndex p = G.layerIndex (foldTo N₀ L k q s c p) := by
  obtain ⟨j1, j2, j3⟩ := (reflectedGS G h).layerIndex_spec (mem_reflectedGS_Ω_one h p)
  rw [mem_layer_reflectedGS_iff h j2] at j3
  exact G.layerIndex_eq j1 (j2.trans h.q_le) j3 |>.symm

theorem layerIndex_le (h : FoldSetting G q s c) (p : Torus d (2 * s * L ^ q)) :
    G.layerIndex (foldTo N₀ L k q s c p) ≤ q := by
  rw [← layerIndex_reflectedGS h]
  exact ((reflectedGS G h).layerIndex_spec (mem_reflectedGS_Ω_one h p)).2.1

/-- The spacing of the reflected set at `p` is the spacing of `G` at the folded point. -/
theorem spacing_reflectedGS (h : FoldSetting G q s c) (p : Torus d (2 * s * L ^ q)) :
    (reflectedGS G h).spacing p = G.spacing (foldTo N₀ L k q s c p) := by
  unfold GeneratingSet.spacing
  rw [layerIndex_reflectedGS h]

end Fold

end Balaban.Reflection
