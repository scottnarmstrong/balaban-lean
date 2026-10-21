/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.BgFieldTransport
public import Balaban.Polymer.ComposeFieldTransport
public import Balaban.Polymer.TwoTorusCubeOps

/-!
# `GSIso` from the correspondence of the domains `Ω_n`

For generating sets `G`, `H` of two step tori identified on a centred box by `boxMap`, if the domains
`Ω_n(G)` and `Ω_n(H)` correspond on the box of radius `ρ + 1` and `Ω₁` lies in the box of radius `ρ`,
then `G` and `H` are isomorphic in the sense of `GSIso`: the layers and the layer indices
correspond, the entries of `-Δ + ν + Q* a Q` at sites of `Ω₁` agree, and so do the sources of data
agreeing on the box of radius `ρ + 1`.  The generating sets of corresponding localized polymers
(`localB`) satisfy the correspondence of the domains.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.SmallField.Def6

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱ' : ℝ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)

/-- The layers correspond when the domains do. -/
theorem layer_corr_of_omega {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {H : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'} {x : CTorus d L N₁ m₁ K}
    (hΩ : ∀ n, 1 ≤ n → n ≤ K → (bm x ∈ H.Ω n ↔ x ∈ G.Ω n)) {n : ℕ} (h1 : 1 ≤ n) (hn : n ≤ K) :
    bm x ∈ H.layer n ↔ x ∈ G.layer n := by
  rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer, hΩ n h1 hn]
  by_cases h : n + 1 ≤ K
  · rw [hΩ (n + 1) (by omega) h]
  · have : n + 1 = K + 1 := by omega
    rw [this, G.top, H.top]
    simp

/-- The entries of `-Δ + ν` at corresponding sites of the box. -/
theorem latticeLaplacian_boxMap {ρ : ℕ} (ν : ℝ)
    (hn : 2 * (ρ + 1) + 1 < (N₁ * L ^ m₁) * L ^ K) (hn' : 2 * (ρ + 1) + 1 < (N₁' * L ^ m₁) * L ^ K)
    {x y : CTorus d L N₁ m₁ K} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y) :
    latticeLaplacian d ((N₁' * L ^ m₁) * L ^ K) ν (bm x) (bm y) =
      latticeLaplacian d ((N₁ * L ^ m₁) * L ^ K) ν x y := by
  rw [latticeLaplacian_apply, latticeLaplacian_apply]
  have e0 : bm x = bm y ↔ x = y :=
    ⟨boxMap_inj (hm' := (by omega : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ K)) hx hy,
      fun h => by rw [h]⟩
  have e1 : ∀ μ : Fin d, (bm y = bm x + Pi.single μ 1) ↔ (y = x + Pi.single μ 1) := fun μ =>
    (step_boxMap_iff (r := ρ) (by omega) (by omega) hx hy μ).symm
  have e2 : ∀ μ : Fin d, (bm x = bm y + Pi.single μ 1) ↔ (x = y + Pi.single μ 1) := fun μ =>
    (step_boxMap_iff (r := ρ) (by omega) (by omega) hy hx μ).symm
  simp only [e0, e1, e2]

/-- The entries of `Q* a Q` at corresponding sites of the box, from the correspondence of the
layers. -/
theorem avgMatrix_corr {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {H : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'} (a : ℕ → ℝ) {ρ : ℕ}
    (hn : 2 * ρ + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {x y : CTorus d L N₁ m₁ K} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y)
    (hlx : ∀ n, 1 ≤ n → n ≤ K → (bm x ∈ H.layer n ↔ x ∈ G.layer n))
    (hly : ∀ n, 1 ≤ n → n ≤ K → (bm y ∈ H.layer n ↔ y ∈ G.layer n)) :
    avgMatrix H a (bm x) (bm y) = avgMatrix G a x y := by
  unfold avgMatrix
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  refine Finset.sum_congr rfl fun n hnn => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hnn
  congr 1
  unfold layerProjMatrix
  have hj := jBlock_boxMap_iff (m₁ := m₁) (j := n) (K := K) h2 (by omega) (by omega) hx hy
  by_cases hxl : x ∈ G.layer n <;> by_cases hyl : y ∈ G.layer n
  · simp only [hxl, hyl, and_self, ite_true, (hlx n h1 h2).2 hxl, (hly n h1 h2).2 hyl]
    exact if_congr hj.symm rfl rfl
  · have : ¬ bm y ∈ H.layer n := fun h => hyl ((hly n h1 h2).1 h)
    simp [hyl, this]
  · have : ¬ bm x ∈ H.layer n := fun h => hxl ((hlx n h1 h2).1 h)
    simp [hxl, this]
  · have : ¬ bm x ∈ H.layer n := fun h => hxl ((hlx n h1 h2).1 h)
    simp [hxl, this]

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- Adjacency of sites of the box is preserved by the box map. -/
theorem adj_boxMap_iff {r : ℕ} (hn : 2 * r + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * r + 1 < (N₁' * L ^ m₁) * L ^ K) {a b : CTorus d L N₁ m₁ K}
    (ha : InBox d r ((N₁ * L ^ m₁) * L ^ K) a) (hb : InBox d r ((N₁ * L ^ m₁) * L ^ K) b) :
    Adj a b ↔ Adj (bm a) (bm b) := by
  constructor
  · rintro ⟨μ, h | h⟩
    · exact ⟨μ, Or.inl ((step_boxMap_iff (r := r) hn hn' ha hb μ).1 h)⟩
    · exact ⟨μ, Or.inr ((step_boxMap_iff (r := r) hn hn' hb ha μ).1 h)⟩
  · rintro ⟨μ, h | h⟩
    · exact ⟨μ, Or.inl ((step_boxMap_iff (r := r) hn hn' ha hb μ).2 h)⟩
    · exact ⟨μ, Or.inr ((step_boxMap_iff (r := r) hn hn' hb ha μ).2 h)⟩

/-- The collar corresponds when the domains do. -/
theorem collar_corr_of_omega {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {H : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'} {ρ : ℕ}
    (hn : 2 * (ρ + 1) + 1 < (N₁ * L ^ m₁) * L ^ K) (hn' : 2 * (ρ + 1) + 1 < (N₁' * L ^ m₁) * L ^ K)
    (hGbox : ∀ x ∈ G.Ω 1, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hHbox : ∀ x ∈ H.Ω 1, InBox d ρ ((N₁' * L ^ m₁) * L ^ K) x)
    (hΩ : ∀ x, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) x → (bm x ∈ H.Ω 1 ↔ x ∈ G.Ω 1))
    {x : CTorus d L N₁ m₁ K} (hx : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) x) :
    bm x ∈ collar H ↔ x ∈ collar G := by
  rw [mem_collar, mem_collar]
  constructor
  · rintro ⟨h1, w', hw', hadj⟩
    have hwb := hHbox w' hw'
    have hw : bm' w' ∈ G.Ω 1 := by
      rw [← hΩ _ (inBox_mono (Nat.le_succ ρ) (inBox_boxMap (by omega) hwb)),
        boxMap_boxMap (by omega) hwb]
      exact hw'
    refine ⟨fun h => h1 ((hΩ x hx).2 h), bm' w', hw, ?_⟩
    have hwA : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) (bm' w') :=
      inBox_mono (Nat.le_succ ρ) (inBox_boxMap (by omega) hwb)
    rw [adj_boxMap_iff (r := ρ + 1) hn hn' hwA hx, boxMap_boxMap (by omega) hwb]
    exact hadj
  · rintro ⟨h1, w, hw, hadj⟩
    have hwb := hGbox w hw
    have hwA : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) w := inBox_mono (Nat.le_succ ρ) hwb
    refine ⟨fun h => h1 ((hΩ x hx).1 h), bm w, (hΩ w hwA).2 hw, ?_⟩
    exact (adj_boxMap_iff (r := ρ + 1) hn hn' hwA hx).1 hadj

/-- **`GSIso` from the correspondence of the domains.** -/
theorem gsIso_of_omega {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {H : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'} (a : ℕ → ℝ) (ν : ℝ) {ρ : ℕ} (hK : 1 ≤ K)
    (hn : 2 * (ρ + 1) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ + 1) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (hGbox : ∀ x ∈ G.Ω 1, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hHbox : ∀ x ∈ H.Ω 1, InBox d ρ ((N₁' * L ^ m₁) * L ^ K) x)
    (hΩ : ∀ x, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) x → ∀ n, 1 ≤ n → n ≤ K →
      (bm x ∈ H.Ω n ↔ x ∈ G.Ω n)) :
    GSIso a ν G H bm {z | InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) z} := by
  classical
  have hGρ : ∀ x ∈ G.Ω 1, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) x :=
    fun x hx => inBox_mono (Nat.le_succ ρ) (hGbox x hx)
  have hmem : ∀ x ∈ G.Ω 1, bm x ∈ H.Ω 1 :=
    fun x hx => (hΩ x (hGρ x hx) 1 le_rfl hK).2 hx
  have hΩ1 : ∀ x, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) x → (bm x ∈ H.Ω 1 ↔ x ∈ G.Ω 1) :=
    fun x hx => hΩ x hx 1 le_rfl hK
  have hlay : ∀ x, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) x → ∀ n, 1 ≤ n → n ≤ K →
      (bm x ∈ H.layer n ↔ x ∈ G.layer n) := fun x hx n h1 h2 =>
    layer_corr_of_omega (fun m hm hmK => hΩ x hx m hm hmK) h1 h2
  have hidx : ∀ x ∈ G.Ω 1, H.layerIndex (bm x) = G.layerIndex x := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := G.layerIndex_spec hx
    exact H.layerIndex_eq h1 h2 ((hlay x (hGρ x hx) _ h1 h2).2 h3)
  have hsm1 : ∀ ρ' : ℕ, ρ' ≤ ρ + 1 → 2 * ρ' + 1 < (N₁ * L ^ m₁) * L ^ K ∧
      2 * ρ' + 1 < (N₁' * L ^ m₁) * L ^ K := fun ρ' h => ⟨by omega, by omega⟩
  refine ⟨hmem, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact boxMap_inj (hm' := (by omega : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ K)) (hGbox x hx)
      (hGbox y hy) hxy
  · intro x' hx'
    have hb := hHbox x' hx'
    have hxb : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (bm' x') := inBox_boxMap (by omega) hb
    refine ⟨bm' x', ?_, boxMap_boxMap (by omega) hb⟩
    refine (hΩ1 _ (inBox_mono (Nat.le_succ ρ) hxb)).1 ?_
    rw [boxMap_boxMap (by omega) hb]
    exact hx'
  · intro x hx
    unfold GeneratingSet.spacing
    rw [hidx x hx]
  · intro x y hx hy
    have hxb := hGbox x x.2
    have hyb := hGbox y y.2
    unfold dirichletOperator Green.restrictOp
    simp only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply,
      Pi.zero_apply, ite_self, add_zero]
    congr 1
    unfold fullMatrix
    rw [Matrix.add_apply, Matrix.add_apply,
      latticeLaplacian_boxMap ν (by omega) (by omega) hxb hyb,
      avgMatrix_corr a (by omega) (by omega) hxb hyb
        (fun n h1 h2 => hlay x (hGρ x x.2) n h1 h2) (fun n h1 h2 => hlay y (hGρ y y.2) n h1 h2)]
  · intro N D D' hD x hx i
    have hxb := hGbox x x.2
    have hxR : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K) := hGρ x x.2
    have hcol : ∀ z, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) z → (bm z ∈ collar H ↔ z ∈ collar G) :=
      fun z hz => collar_corr_of_omega (by omega) (by omega) hGbox hHbox hΩ1 hz
    unfold source qStar boundaryTerm
    dsimp only
    have e1 : H.layerIndex (bm (x : CTorus d L N₁ m₁ K)) = G.layerIndex (x : CTorus d L N₁ m₁ K) :=
      hidx x x.2
    have hD0 := hD x hxR
    have hsum : ∀ μ : Fin d,
        ((if bm (x : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∈ collar H then
            D'.Ψ (bm (x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i else 0) +
          (if bm (x : CTorus d L N₁ m₁ K) - Pi.single μ 1 ∈ collar H then
            D'.Ψ (bm (x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i else 0)) =
        ((if (x : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∈ collar G then
            D.Ψ ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i else 0) +
          (if (x : CTorus d L N₁ m₁ K) - Pi.single μ 1 ∈ collar G then
            D.Ψ ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i else 0)) := by
      intro μ
      have ha : bm ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) =
          bm (x : CTorus d L N₁ m₁ K) + Pi.single μ 1 :=
        boxMap_add_single (ρ := ρ) (by omega) (by omega) hxb μ
      have hb : bm ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) =
          bm (x : CTorus d L N₁ m₁ K) - Pi.single μ 1 :=
        boxMap_sub_single (ρ := ρ) (by omega) (by omega) hxb μ
      have hpa : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) :=
        inBox_add_single (by omega) hxb μ
      have hpb : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) :=
        inBox_sub_single (by omega) hxb μ
      simp only [← ha, ← hb, hcol _ hpa, hcol _ hpb, ← (hD _ hpa).1, ← (hD _ hpb).1]
    rw [e1, ← hD0.1, ← hD0.2]
    simp only [hsum]


/-- **`GSCorr` from the correspondence of the domains.** -/
theorem gsCorr_of_omega {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {H : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'} {ρ : ℕ} (hK : 1 ≤ K)
    (hn : 2 * (ρ + 1 + L ^ K) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ + 1 + L ^ K) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (hGbox : ∀ x ∈ G.Ω 1, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hHbox : ∀ x ∈ H.Ω 1, InBox d ρ ((N₁' * L ^ m₁) * L ^ K) x)
    (hΩ : ∀ x, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) x → ∀ n, 1 ≤ n → n ≤ K →
      (bm x ∈ H.Ω n ↔ x ∈ G.Ω n)) :
    GSCorr G H bm {z | InBox d ρ ((N₁ * L ^ m₁) * L ^ K) z} := by
  classical
  have hK1 : 1 ≤ L ^ K := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hΩ1 : ∀ x, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) x → (bm x ∈ H.Ω 1 ↔ x ∈ G.Ω 1) :=
    fun x hx => hΩ x hx 1 le_rfl hK
  have hlay : ∀ x, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) x → ∀ n, 1 ≤ n → n ≤ K →
      (bm x ∈ H.layer n ↔ x ∈ G.layer n) := fun x hx n h1 h2 =>
    layer_corr_of_omega (fun m hm hmK => hΩ x hx m hm hmK) h1 h2
  refine ⟨fun z hz => hΩ1 z (inBox_mono (Nat.le_succ ρ) hz), fun z hz => ?_, fun z hz => ?_⟩
  · exact collar_corr_of_omega (by omega) (by omega) hGbox hHbox hΩ1 (inBox_mono (Nat.le_succ ρ) hz)
  · have hz1 : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) z := inBox_mono (Nat.le_succ ρ) hz
    refine ⟨fun h => (hΩ1 z hz1).2 h, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := G.layerIndex_spec h
      exact H.layerIndex_eq h1 h2 ((hlay z hz1 _ h1 h2).2 h3)
    · obtain ⟨h1, h2, -⟩ := G.layerIndex_spec h
      have hbox : ∀ x ∈ box (cbase (L ^ G.layerIndex z) z) (L ^ G.layerIndex z),
          InBox d (ρ + L ^ G.layerIndex z) ((N₁ * L ^ m₁) * L ^ K) x :=
        fun x hx => inBox_of_mem_cell (a := L ^ G.layerIndex z) (by
          have := Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) h2
          omega) hz hx
      have hb := blk_image (r := ρ + L ^ G.layerIndex z) (j := G.layerIndex z)
        (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := 0) 1 hK)
        (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := 0) 1 hK) h2
        (by
          have := Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) h2
          omega) z hbox
      apply Finset.coe_injective
      rw [Finset.coe_image]
      exact hb
    · obtain ⟨h1, h2, -⟩ := G.layerIndex_spec h
      have hbox : ∀ x ∈ box (cbase (L ^ G.layerIndex z) z) (L ^ G.layerIndex z),
          InBox d (ρ + L ^ G.layerIndex z) ((N₁ * L ^ m₁) * L ^ K) x :=
        fun x hx => inBox_of_mem_cell (a := L ^ G.layerIndex z) (by
          have := Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) h2
          omega) hz hx
      intro a ha b hb hab
      have hbl : ∀ x ∈ G.blk (G.layerIndex z) z,
          InBox d (ρ + L ^ G.layerIndex z) ((N₁ * L ^ m₁) * L ^ K) x := by
        intro x hx
        refine hbox x ?_
        rw [← jBlock_eq_iff_mem_box h2]
        exact GeneratingSet.mem_blk.1 hx
      have := Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) h2
      exact boxMap_inj (hm' := (by omega : 2 * (ρ + L ^ G.layerIndex z) + 1 <
        (N₁' * L ^ m₁) * L ^ K)) (hbl a ha) (hbl b hb) hab

end Balaban.Polymer.TwoTorusStep
