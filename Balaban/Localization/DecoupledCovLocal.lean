/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovWeighted
public import Balaban.Localization.DecoupledFieldLocal
public import Balaban.Localization.DecoupledXLocal
public import Balaban.Localization.DecoupledCovUnit
public import Balaban.Localization.DecoupledCovariance

/-!
# I-4c (v): locality of `C^{1/2}(s)` and `𝕃(s)` on the unit lattice

LOCALIZATION.md §3.4, Theorem I-4c (v), in comparison form, for the concrete unit lattice
`unitQ`, `unitP`. If two inputs agree on the unit points of the output blocks and of the blocks
meeting `S_Y`, then `C_x(s) h` and `C_x(s') h'` agree at the unit points whose `(k+1)`-blocks lie in
`Y` (`decCov_local`), for every `x`, by a Neumann-series induction for `M_s⁻¹` from `dg5x'_inner`
(`decZ_local`); integrating in `x` gives `I4c_local_sqrt` and `I4c_local_log`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Rows

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x₀ ν : ℝ}

theorem latticeLaplacian_entry_eq_zero {ℓ : ℕ} [NeZero ℓ] (ν : ℝ) {x y : Torus d ℓ}
    (hxy : y ≠ x) (hnb : ∀ μ : Fin d, y ≠ x + Pi.single μ 1 ∧ y ≠ x - Pi.single μ 1) :
    latticeLaplacian d ℓ ν x y = 0 := by
  unfold latticeLaplacian
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sum_apply,
    Matrix.add_apply, Matrix.transpose_apply, shiftMatrix]
  have h1 : ∀ μ : Fin d, (if y = x + Pi.single μ 1 then (1 : ℝ) else 0) +
      (if x = y + Pi.single μ 1 then (1 : ℝ) else 0) = 0 := by
    intro μ
    have h2 : ¬ (y = x + Pi.single μ 1) := (hnb μ).1
    have h3 : ¬ (x = y + Pi.single μ 1) := by
      intro h; apply (hnb μ).2; rw [h]; simp
    simp [h2, h3]
  simp [Ne.symm hxy, h1]

theorem layerBlockMatrix_entry_eq_zero {j m : ℕ} {x y : Torus d (N₁ * L ^ m₁ * L ^ (k + 1))}
    (h : ¬ (x ∈ G.layer j ∧ y ∈ G.layer j ∧
      blockMap (L ^ m) ((N₁ * L ^ m₁) * L ^ (k + 1 - m)) x =
        blockMap (L ^ m) ((N₁ * L ^ m₁) * L ^ (k + 1 - m)) y)) :
    layerBlockMatrix G j m x y = 0 := by
  unfold layerBlockMatrix blockProjMatrix
  by_cases hl : x ∈ G.layer j ∧ y ∈ G.layer j
  · have : ¬ blockMap (L ^ m) ((N₁ * L ^ m₁) * L ^ (k + 1 - m)) x =
        blockMap (L ^ m) ((N₁ * L ^ m₁) * L ^ (k + 1 - m)) y := fun e => h ⟨hl.1, hl.2, e⟩
    simp [hl, this]
  · simp [hl]


theorem xAvgMatrix_entry_eq_zero (s₁ s₂ : ℝ) {x y : Torus d (N₁ * L ^ m₁ * L ^ (k + 1))}
    (hblk : y ∉ G.blk (G.layerIndex x) x) :
    xAvgMatrix G a s₁ s₂ x y = 0 := by
  have hj : ∀ j, 1 ≤ j → j ≤ k + 1 → x ∈ G.layer j → y ∈ G.layer j →
      jBlock d L (N₁ * L ^ m₁) (k + 1) j y = jBlock d L (N₁ * L ^ m₁) (k + 1) j x → False := by
    intro j hj1 hjk hx hy hb
    apply hblk
    rw [G.layerIndex_eq hj1 hjk hx, GeneratingSet.mem_blk]
    exact hb
  unfold xAvgMatrix
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  have t1 : ∀ j ∈ Finset.Icc 1 k, (a j / ((L : ℝ) ^ j) ^ 2) * layerBlockMatrix G j j x y = 0 := by
    intro j hjm
    have hj1 := (Finset.mem_Icc.1 hjm).1
    have hjk := (Finset.mem_Icc.1 hjm).2
    rw [layerBlockMatrix_entry_eq_zero, mul_zero]
    rintro ⟨hx, hy, hb⟩
    exact hj j hj1 (by omega) hx hy hb.symm
  rw [Finset.sum_eq_zero t1, zero_add]
  have t2 : layerBlockMatrix G (k + 1) k x y = 0 := by
    rw [layerBlockMatrix_entry_eq_zero]
    rintro ⟨hx, hy, hb⟩
    exact hj (k + 1) (by omega) le_rfl hx hy (jBlock_eq_of_unitBlock_eq hb.symm)
  have t3 : layerBlockMatrix G (k + 1) (k + 1) x y = 0 := by
    rw [layerBlockMatrix_entry_eq_zero]
    rintro ⟨hx, hy, hb⟩
    exact hj (k + 1) (by omega) le_rfl hx hy hb.symm
  rw [t2, t3]; simp


theorem xDirichlet_entry_eq_zero (α : G.Ω 1 → ℂ) {p q : G.Ω 1}
    (hxy : (q : CTorus d L N₁ m₁ (k + 1)) ≠ p)
    (hnb : ∀ μ : Fin d, (q : CTorus d L N₁ m₁ (k + 1)) ≠ (p : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1 ∧
      (q : CTorus d L N₁ m₁ (k + 1)) ≠ (p : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1)
    (hblk : (q : CTorus d L N₁ m₁ (k + 1)) ∉ G.blk (G.layerIndex (p : CTorus d L N₁ m₁ (k + 1))) p) :
    xDirichletOperator G a aT x₀ ν α p q = 0 := by
  have hpq : p ≠ q := fun h => hxy (by rw [h])
  unfold xDirichletOperator xFullMatrix
  simp only [Matrix.add_apply, Green.restrictOp, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.diagonal_apply, hpq, ↓reduceIte, add_zero]
  rw [latticeLaplacian_entry_eq_zero _ hxy hnb, xAvgMatrix_entry_eq_zero _ _ hblk]
  simp

/-- **The row of `H_{k,x}(α)` at a site of `□_z` lies in `□̂_z`.**  If `x ∈ □_z ∩ Ω₁` and
`H_{k,x}(α) x y ≠ 0` then `y ∈ □̂_z`. -/
theorem row_mem_hatBox_x (S : DGSetting G a ν) {z : ℕ × CTorus d L N₁ m₁ (k + 1)} (hz : z ∈ cubeIdx G)
    (α : G.Ω 1 → ℂ) {x : G.Ω 1} (hx : (x : CTorus d L N₁ m₁ (k + 1)) ∈ intBox z) {y : G.Ω 1}
    (h : xDirichletOperator G a aT x₀ ν α x y ≠ 0) : (y : CTorus d L N₁ m₁ (k + 1)) ∈ hatBox z := by
  classical
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
  have hLr : (1 : ℝ) ≤ L := by linarith
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ z.1 := one_le_pow₀ hLr
  have hbig : (1 : ℝ) ≤ 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ z.1 := by nlinarith
  by_contra hyH
  apply h
  apply xDirichlet_entry_eq_zero (G := G) (a := a) (aT := aT) (x₀ := x₀) (ν := ν) α
  · intro hyx
    exact hyH (hyx ▸ box_subset_hatBox z hx)
  · intro μ
    constructor
    · intro hyx
      have hw : ((x : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1) =
          (x : CTorus d L N₁ m₁ (k + 1)) + (intTorus (Pi.single μ (1 : ℤ)) : CTorus d L N₁ m₁ (k + 1)) := by
        congr 1
        funext ν'
        by_cases h' : ν' = μ <;> simp [intTorus_apply, h']
      refine hyH (hyx ▸ ?_)
      rw [hw]
      refine inBox_hat_of_add_int hx _ (B := 1) (fun ν' => ?_) (by linarith)
      by_cases h' : ν' = μ <;> simp [h']
    · intro hyx
      have hw : ((x : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1) =
          (x : CTorus d L N₁ m₁ (k + 1)) + (intTorus (Pi.single μ (-1 : ℤ)) : CTorus d L N₁ m₁ (k + 1)) := by
        funext ν'
        by_cases h' : ν' = μ <;> simp [intTorus_apply, h', sub_eq_add_neg]
      refine hyH (hyx ▸ ?_)
      rw [hw]
      refine inBox_hat_of_add_int hx _ (B := 1) (fun ν' => ?_) (by linarith)
      by_cases h' : ν' = μ <;> simp [h']
  · intro hy
    have hy' := G.mem_blk.1 hy
    obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec x.2
    have hnle := layer_le_of_mem_box S.cover_sep (by have := S.hL; omega) hz hn1 hnK hxl hx
    have hcell : SameCell (L ^ G.layerIndex (x : CTorus d L N₁ m₁ (k + 1)))
        (y : CTorus d L N₁ m₁ (k + 1)) x := sameCell_of_jBlock_eq hnK hy'
    have hlpos : 0 < L ^ G.layerIndex (x : CTorus d L N₁ m₁ (k + 1)) :=
      pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
    obtain ⟨w, hw, hwb⟩ := exists_int_of_sameCell hlpos hcell
    refine hyH ?_
    rw [hw]
    refine inBox_hat_of_add_int hx w (B := (L : ℝ) ^ (z.1 + 1)) (fun ν' => ?_) ?_
    · have h1 := hwb ν'
      have h3 : (((L ^ G.layerIndex (x : CTorus d L N₁ m₁ (k + 1)) : ℕ)) : ℝ) =
          (L : ℝ) ^ G.layerIndex (x : CTorus d L N₁ m₁ (k + 1)) := by push_cast; rfl
      rw [h3] at h1
      exact h1.le.trans (pow_le_pow_right₀ hLr hnle)
    · have : (L : ℝ) ^ (z.1 + 1) = L * (L : ℝ) ^ z.1 := by ring
      rw [this]
      nlinarith

end Rows

section Inner

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x₀ ν : ℝ}

/-- **(DG5'), the version with data agreeing on `S_Y` only.**  Let `Y` be a union of
nearest-neighbour components of `V(𝒞) ∩ Ω₁` and `S_Y = ⋃_{z ∈ Z_Y} □_z`.  If `A = A'` and `f = f'`
on `S_Y` (and the parameters are as in `dg5'`) then `G_s(A) f = G_{s'}(A') f'` on all of `Y ∩ Ω₁`. -/
theorem dg5x'_inner (S : XSetting G a aT ν) (hx : 0 ≤ x₀) (hconn : HatConn G)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1) Y)
    {α α' : G.Ω 1 → ℂ} (hα : AdmPot G α) (hα' : AdmPot G α')
    {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hU : IsUnit (1 - Kcalx G a aT x₀ ν α s)) (hU' : IsUnit (1 - Kcalx G a aT x₀ ν α' s'))
    (hs1 : ∀ P ∈ cubeIdx G, P ∉ parCubes G X₁ → s P = 1 ∧ s' P = 1)
    (hs0 : ∀ P ∈ parCubes G X₁, P ∉ 𝒞 → s P = 0 ∧ s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI G (cubeP P) Y → s P = s' P)
    (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → α x = α' x)
    {f f' : G.Ω 1 → ℂ}
    (hf : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → f x = f' x) :
    ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ Y →
      (Gsx G a aT x₀ ν α s *ᵥ f) x = (Gsx G a aT x₀ ν α' s' *ᵥ f') x := by
  classical
  have hact : ∀ z, (sProd G s z ≠ 0 ∨ sProd G s' z ≠ 0) →
      ∀ P ∈ Qset G z, P ∈ parCubes G X₁ → P ∈ 𝒞 := by
    intro z hz
    rcases hz with h | h
    · exact hact_aux s (fun P hP hPC => (hs0 P hP hPC).1) z h
    · exact hact_aux s' (fun P hP hPC => (hs0 P hP hPC).2) z h
  -- an active interaction cube inside `Y` has `z ∈ Z_Y`
  have hbase : ∀ z ∈ cubeIdx G, ∃ b : G.Ω 1, (b : CTorus d L N₁ m₁ (k + 1)) = z.2 ∧
      z.2 ∈ intBox z := by
    intro z hz
    obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hz
    have hbaseΩ : z.2 ∈ G.Ω 1 := G.layer_subset hm1 hmK hl
    refine ⟨⟨z.2, hbaseΩ⟩, rfl, ?_⟩
    rw [mem_intBox]
    intro μ
    refine ⟨0, ?_⟩
    have hB : (1 : ℝ) ≤ (L : ℝ) ^ (z.1 + m₁) :=
      one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
    simp only [Int.cast_zero, zero_mul, add_zero]
    rw [abs_lt]
    constructor <;> nlinarith
  have hhatY : ∀ z ∈ cubeIdx G, (sProd G s z ≠ 0 ∨ sProd G s' z ≠ 0) →
      SubI G (intBox z) Y → SubI G (hatBox z) Y := by
    intro z hz hactive hbox
    obtain ⟨b, hb, hbbox⟩ := hbase z hz
    have hbY : (b : CTorus d L N₁ m₁ (k + 1)) ∈ Y := hbox b (hb ▸ hbbox)
    rcases hdich_aux S.dg hconn hY z hz (hact z hactive) with h | h
    · exact h
    · exact absurd hbY (h b (hb ▸ box_subset_hatBox z hbbox))
  have hzY : ∀ z ∈ cubeIdx G, (sProd G s z ≠ 0 ∨ sProd G s' z ≠ 0) →
      SubI G (intBox z) Y → z ∈ ZY G X₁ 𝒞 Y := fun z hz hactive hbox =>
    Finset.mem_filter.2 ⟨hz, hact z hactive, hhatY z hz hactive hbox⟩
  have hdichT : ∀ z ∈ cubeIdx G, (sProd G s z ≠ 0 ∨ sProd G s' z ≠ 0) →
      SubI G (intBox z) (SY G X₁ 𝒞 Y) ∨ DisjI G (intBox z) (SY G X₁ 𝒞 Y) := by
    intro z hz hactive
    rcases hdich_aux S.dg hconn hY z hz (hact z hactive) with h | h
    · left
      intro x hx
      have hzZ : z ∈ ZY G X₁ 𝒞 Y := Finset.mem_filter.2 ⟨hz, hact z hactive, h⟩
      exact Finset.mem_biUnion.2 ⟨z, hzZ, hx⟩
    · right
      intro x hx hxT
      exact h x (box_subset_hatBox z hx) (SY_subset hxT)
  have hagreeT : ∀ z ∈ cubeIdx G, SubI G (intBox z) (SY G X₁ 𝒞 Y) → sProd G s z = sProd G s' z := by
    intro z hz hbox
    by_cases hactive : sProd G s z ≠ 0 ∨ sProd G s' z ≠ 0
    · have hP := hact z hactive
      have hboxY : SubI G (intBox z) Y := fun x hx => SY_subset (hbox x hx)
      have hhatYz := hhatY z hz hactive hboxY
      unfold sProd
      refine Finset.prod_congr rfl fun P hPQ => ?_
      by_cases hPP : P ∈ parCubes G X₁
      · by_cases hPC : P ∈ 𝒞
        · obtain ⟨hPi, y, hy, hyhat⟩ := (mem_Qset).1 hPQ
          have hyP : y ∈ cubeP P := mem_cubeP.2 hy
          have hyΩ : y ∈ G.Ω 1 := cubeP_subset_Ω S.dg hPi hyP
          have hyY : y ∈ Y := hhatYz ⟨y, hyΩ⟩ (mem_boxSet.2 hyhat)
          have hsubV : cubeP P ⊆ (Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1 := by
            intro x hx
            rw [Finset.mem_filter]
            refine ⟨?_, cubeP_subset_Ω S.dg hPi hx⟩
            unfold Vset
            rw [Finset.mem_union]
            right
            exact Finset.mem_biUnion.2 ⟨P, hPC, hx⟩
          have hsubY : SubI G (cubeP P) Y := by
            rcases connIn_dichotomy (cubeP_connIn S.dg hPi) hsubV hY with h | h
            · intro x hx; exact h hx
            · exfalso; exact Finset.disjoint_left.1 h hyP hyY
          exact hag P hPC hsubY
        · rw [(hs0 P hPP hPC).1, (hs0 P hPP hPC).2]
      · rw [(hs1 P ((mem_Qset).1 hPQ).1 hPP).1, (hs1 P ((mem_Qset).1 hPQ).1 hPP).2]
    · push Not at hactive
      rw [hactive.1, hactive.2]
  intro x hxY
  by_cases hxT : (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y
  · exact Gsx_local S hx hα hα' hU hU' hdichT hagreeT hA hf x hxT
  · -- outside `S_Y` both sides vanish
    have hz0 : ∀ {u : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {β : G.Ω 1 → ℂ} {g : G.Ω 1 → ℂ},
        (∀ P ∈ parCubes G X₁, P ∉ 𝒞 → u P = 0) →
        (Gsx G a aT x₀ ν β u *ᵥ g) x = 0 := by
      intro u β g hu
      by_contra hne
      have hc := dg5x_support (x := x₀) (α := β) (a := a) (aT := aT) (ν := ν) u g x hne
      unfold Core at hc
      obtain ⟨z, hzZ, hxz⟩ := Finset.mem_biUnion.1 hc
      have hzZ' := Finset.mem_filter.1 hzZ
      have hactive : sProd G u z ≠ 0 := hzZ'.2
      have hP := hact_aux u hu z hactive
      have hxbox : (x : CTorus d L N₁ m₁ (k + 1)) ∈ intBox z := coreBox_subset_box hxz
      rcases hdich_aux S.dg hconn hY z hzZ'.1 hP with h | h
      · exact hxT (Finset.mem_biUnion.2 ⟨z, Finset.mem_filter.2 ⟨hzZ'.1, hP, h⟩, hxbox⟩)
      · exact h x (box_subset_hatBox z hxbox) hxY
    rw [hz0 (fun P hP hPC => (hs0 P hP hPC).1), hz0 (fun P hP hPC => (hs0 P hP hPC).2)]


end Inner

section Neumann

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x₀ ν : ℝ}
variable {N : ℕ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

/-- The standing geometric hypotheses of the comparison form of locality. -/
structure LocHyp (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (X₁ : Finset (CTorus d L N₁ m₁ (k + 1))) (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1)))
    (Y : Finset (CTorus d L N₁ m₁ (k + 1))) (α : G.Ω 1 → ℂ)
    (s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) : Prop where
  conn : HatConn G
  nn : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1) Y
  pot : AdmPot G α
  s1 : ∀ P ∈ cubeIdx G, P ∉ parCubes G X₁ → s P = 1 ∧ s' P = 1
  s0 : ∀ P ∈ parCubes G X₁, P ∉ 𝒞 → s P = 0 ∧ s' P = 0
  ag : ∀ P ∈ 𝒞, SubI G (cubeP P) Y → s P = s' P

variable {α : G.Ω 1 → ℂ} {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}

theorem Gvec_local (S : XSetting G a aT ν) (hx : 0 ≤ x₀) (H : LocHyp G X₁ 𝒞 Y α s s')
    (hU : IsUnit (1 - Kcalx G a aT x₀ ν α s)) (hU' : IsUnit (1 - Kcalx G a aT x₀ ν α s'))
    {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → ∀ i, w (y, i) = w' (y, i)) :
    ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i,
      (liftOp N (Gsx G a aT x₀ ν α s) *ᵥ w) (y, i) =
        (liftOp N (Gsx G a aT x₀ ν α s') *ᵥ w') (y, i) := by
  intro y hy i
  rw [liftOp_mulVec, liftOp_mulVec]
  exact dg5x'_inner S hx H.conn H.nn H.pot H.pot hU hU' H.s1 H.s0 H.ag (fun _ _ => rfl)
    (f := fun b => w (b, i)) (f' := fun b => w' (b, i)) (fun b hb => hw b hb i) y hy

theorem row_in_Y (S : XSetting G a aT ν) {z y : G.Ω 1}
    (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y)
    (h : xDirichletOperator G a aT x₀ ν α z y ≠ 0) : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y := by
  classical
  unfold SY at hz
  obtain ⟨z0, hz0, hzz⟩ := Finset.mem_biUnion.1 hz
  have hz0' := Finset.mem_filter.1 hz0
  have := row_mem_hatBox_x S.dg hz0'.1 α hzz h
  exact hz0'.2.2 y this

theorem commK_apply_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} {ψ : ι → Fin N → ℂ}
    {u u' : ι × Fin N → ℂ} {z : ι}
    (h : ∀ y, H z y ≠ 0 → ∀ i, u (y, i) = u' (y, i)) :
    (commK H ψ *ᵥ u) z = (commK H ψ *ᵥ u') z := by
  rw [commK_mulVec, commK_mulVec]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
  by_cases h0 : H z y = 0
  · simp [h0]
  · rw [h y h0 i]


/-- Fixed points of two contractions that preserve agreement on a set `S` agree on `S`. -/
theorem fixed_point_agree (T T' : (G.Ω 1 → ℂ) → (G.Ω 1 → ℂ)) (v v' : G.Ω 1 → ℂ)
    (S : Set (G.Ω 1))
    (hc : ∀ u, agmonSource G 0 (fun _ => 0) (T u - v) ≤ (1 / 4) * agmonSource G 0 (fun _ => 0) (u - v))
    (hc' : ∀ u, agmonSource G 0 (fun _ => 0) (T' u - v') ≤
      (1 / 4) * agmonSource G 0 (fun _ => 0) (u - v'))
    (hag : ∀ u u', (∀ z ∈ S, u z = u' z) → ∀ z ∈ S, T u z = T' u' z) :
    ∀ z ∈ S, v z = v' z := by
  classical
  intro z hz
  set src := agmonSource G 0 (fun _ => 0) with hsrc
  -- the iterates
  let u : ℕ → G.Ω 1 → ℂ := fun n => T^[n] 0
  let u' : ℕ → G.Ω 1 → ℂ := fun n => T'^[n] 0
  have hagn : ∀ n, ∀ z ∈ S, u n z = u' n z := by
    intro n
    induction n with
    | zero => intro z _; rfl
    | succ n ih =>
      intro z hz
      have e1 : u (n + 1) = T (u n) := Function.iterate_succ_apply' T n 0
      have e2 : u' (n + 1) = T' (u' n) := Function.iterate_succ_apply' T' n 0
      rw [e1, e2]
      exact hag _ _ ih z hz
  have hbd : ∀ n, src (u n - v) ≤ (1 / 4) ^ n * src (0 - v) := by
    intro n
    induction n with
    | zero => simp [u]
    | succ n ih =>
      have e1 : u (n + 1) = T (u n) := Function.iterate_succ_apply' T n 0
      rw [e1]
      refine (hc _).trans ?_
      calc 1 / 4 * src (u n - v) ≤ 1 / 4 * ((1 / 4) ^ n * src (0 - v)) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by ring
  have hbd' : ∀ n, src (u' n - v') ≤ (1 / 4) ^ n * src (0 - v') := by
    intro n
    induction n with
    | zero => simp [u']
    | succ n ih =>
      have e1 : u' (n + 1) = T' (u' n) := Function.iterate_succ_apply' T' n 0
      rw [e1]
      refine (hc' _).trans ?_
      calc 1 / 4 * src (u' n - v') ≤ 1 / 4 * ((1 / 4) ^ n * src (0 - v')) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by ring
  have hpt : ∀ (f : G.Ω 1 → ℂ), ‖f z‖ ^ 2 ≤ src f := by
    intro f
    rw [hsrc, agmonSource_eq]
    simp only [mul_zero, Real.exp_zero, one_pow, mul_one]
    have h1 : 1 ≤ (G.spacing (z : CTorus d L N₁ m₁ (k + 1))) ^ 2 := by
      have := G.spacing_ge_one (z : CTorus d L N₁ m₁ (k + 1))
      nlinarith
    calc ‖f z‖ ^ 2 ≤ (G.spacing (z : CTorus d L N₁ m₁ (k + 1))) ^ 2 * ‖f z‖ ^ 2 := by
          nlinarith [sq_nonneg ‖f z‖]
      _ ≤ _ := Finset.single_le_sum (f := fun x : G.Ω 1 => (G.spacing (x : CTorus d L N₁ m₁ (k + 1))) ^ 2 *
            ‖f x‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ z)
  have hlim : ∀ (T0 : (G.Ω 1 → ℂ) → (G.Ω 1 → ℂ)) (w : ℕ → G.Ω 1 → ℂ) (vv : G.Ω 1 → ℂ) (C : ℝ),
      (∀ n, src (w n - vv) ≤ (1 / 4) ^ n * C) →
      Filter.Tendsto (fun n => w n z) Filter.atTop (nhds (vv z)) := by
    intro T0 w vv C h
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hC : 0 ≤ C := by
      have := h 0
      have h0 := agmonSource_nonneg G 0 (fun _ => 0) (w 0 - vv)
      simp only [pow_zero, one_mul] at this
      linarith
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (g := fun n : ℕ => (1 / 2 : ℝ) ^ n * Real.sqrt C) ?_
    · have h1 := hpt (w n - vv)
      have h2 : ‖w n z - vv z‖ ^ 2 ≤ ((1 / 2 : ℝ) ^ n * Real.sqrt C) ^ 2 := by
        calc ‖w n z - vv z‖ ^ 2 = ‖(w n - vv) z‖ ^ 2 := rfl
          _ ≤ src (w n - vv) := h1
          _ ≤ (1 / 4) ^ n * C := h n
          _ = ((1 / 2 : ℝ) ^ n * Real.sqrt C) ^ 2 := by
              rw [mul_pow, ← pow_mul, Real.sq_sqrt hC]
              congr 1
              rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
      exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2
    · have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_const
        (Real.sqrt C)
      simpa using this
  have h1 := hlim T u v (src (0 - v)) hbd
  have h2 := hlim T' u' v' (src (0 - v')) hbd'
  have h3 : Filter.Tendsto (fun n => u' n z) Filter.atTop (nhds (v z)) := by
    refine h1.congr fun n => ?_
    exact hagn n z hz
  exact tendsto_nhds_unique h3 h2


theorem decN_mulVec_eq (w : G.Ω 1 × Fin N → ℂ) :
    decN G a aT x₀ ν α s φ *ᵥ w = (fieldMul (restrictField G φ))ᵀ *ᵥ w -
      commK (xDirichletOperator G a aT x₀ ν α) (restrictField G φ) *ᵥ
        (liftOp N (Gsx G a aT x₀ ν α s) *ᵥ w) := by
  unfold decN constraintN
  rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec]

theorem decM_mulVec_eq (v : G.Ω 1 → ℂ) :
    decM G a aT x₀ ν α s φ *ᵥ v = (fieldMul (restrictField G φ))ᵀ *ᵥ (fieldMul (restrictField G φ) *ᵥ v) -
      commK (xDirichletOperator G a aT x₀ ν α) (restrictField G φ) *ᵥ
        (liftOp N (Gsx G a aT x₀ ν α s) *ᵥ (fieldMul (restrictField G φ) *ᵥ v)) := by
  unfold decM constraintM
  simp only [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

section ZLocal

variable (S : XSetting G a aT ν) (hx : 0 ≤ x₀) (H : LocHyp G X₁ 𝒞 Y α s s')
  (hU : IsUnit (1 - Kcalx G a aT x₀ ν α s)) (hU' : IsUnit (1 - Kcalx G a aT x₀ ν α s'))
include S hx H hU hU'

theorem decN_local {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → ∀ i, w (y, i) = w' (y, i))
    {z : G.Ω 1} (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y) :
    (decN G a aT x₀ ν α s φ *ᵥ w) z = (decN G a aT x₀ ν α s' φ *ᵥ w') z := by
  rw [decN_mulVec_eq, decN_mulVec_eq, Pi.sub_apply, Pi.sub_apply]
  have e1 : ((fieldMul (restrictField G φ))ᵀ *ᵥ w) z = ((fieldMul (restrictField G φ))ᵀ *ᵥ w') z := by
    rw [fieldMul_transpose_mulVec, fieldMul_transpose_mulVec]
    exact Finset.sum_congr rfl fun i _ => by rw [hw z hz i]
  have e2 : (commK (xDirichletOperator G a aT x₀ ν α) (restrictField G φ) *ᵥ
      (liftOp N (Gsx G a aT x₀ ν α s) *ᵥ w)) z =
      (commK (xDirichletOperator G a aT x₀ ν α) (restrictField G φ) *ᵥ
      (liftOp N (Gsx G a aT x₀ ν α s') *ᵥ w')) z :=
    commK_apply_eq (fun y hy i => Gvec_local S hx H hU hU' hw y (row_in_Y S hz hy) i)
  rw [e1, e2]

theorem decM_local {v v' : G.Ω 1 → ℂ}
    (hv : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → v y = v' y)
    {z : G.Ω 1} (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y) :
    (decM G a aT x₀ ν α s φ *ᵥ v) z = (decM G a aT x₀ ν α s' φ *ᵥ v') z := by
  rw [decM_mulVec_eq, decM_mulVec_eq, Pi.sub_apply, Pi.sub_apply]
  have e1 : ((fieldMul (restrictField G φ))ᵀ *ᵥ (fieldMul (restrictField G φ) *ᵥ v)) z =
      ((fieldMul (restrictField G φ))ᵀ *ᵥ (fieldMul (restrictField G φ) *ᵥ v')) z := by
    rw [fieldMul_transpose_mulVec, fieldMul_transpose_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fieldMul_mulVec, fieldMul_mulVec, hv z hz]
  have e2 : (commK (xDirichletOperator G a aT x₀ ν α) (restrictField G φ) *ᵥ
      (liftOp N (Gsx G a aT x₀ ν α s) *ᵥ (fieldMul (restrictField G φ) *ᵥ v))) z =
      (commK (xDirichletOperator G a aT x₀ ν α) (restrictField G φ) *ᵥ
      (liftOp N (Gsx G a aT x₀ ν α s') *ᵥ (fieldMul (restrictField G φ) *ᵥ v'))) z := by
    refine commK_apply_eq (fun y hy i => ?_)
    refine Gvec_local S hx H hU hU' (w := fieldMul (restrictField G φ) *ᵥ v)
      (w' := fieldMul (restrictField G φ) *ᵥ v') (fun y hy i => ?_) y (row_in_Y S hz hy) i
    rw [fieldMul_mulVec, fieldMul_mulVec, hv y hy]
  rw [e1, e2]

end ZLocal

section ZLocal2

variable {δ κ : ℝ} (S : XSetting G a aT ν) (hx : 0 ≤ x₀) (H : LocHyp G X₁ 𝒞 Y α s s')
  (D : XData G a aT ν x₀ α κ s) (D' : XData G a aT ν x₀ α κ s')
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
include S hx H D D' hφ hδ hsm

/-- **Locality of `Z_s = Ĝ_s - Π_s`** (the Neumann induction for `M_s⁻¹`). If `w = w'` on `S_Y`
then `Z_s w = Z_{s'} w'` on all of `Y ∩ Ω₁`. -/
theorem decZ_local {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → ∀ i, w (y, i) = w' (y, i)) :
    ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i,
      (decZ G a aT x₀ ν α s φ *ᵥ w) (y, i) = (decZ G a aT x₀ ν α s' φ *ᵥ w') (y, i) := by
  classical
  have hU := D.isUnit_one_sub
  have hU' := D'.isUnit_one_sub
  have H0 : XWeight G 0 (fun _ => 0) := D.weight_zero
  have H0' : XWeight G 0 (fun _ => 0) := D'.weight_zero
  have hMs := decM_isUnit D hφ hδ hsm
  have hMs' := decM_isUnit D' hφ hδ hsm
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hMs
  have hdet' := (Matrix.isUnit_iff_isUnit_det _).1 hMs'
  obtain ⟨v, hv⟩ : ∃ v : G.Ω 1 → ℂ, v = (decM G a aT x₀ ν α s φ)⁻¹ *ᵥ
      (decN G a aT x₀ ν α s φ *ᵥ w) := ⟨_, rfl⟩
  obtain ⟨v', hv'⟩ : ∃ v : G.Ω 1 → ℂ, v = (decM G a aT x₀ ν α s' φ)⁻¹ *ᵥ
      (decN G a aT x₀ ν α s' φ *ᵥ w') := ⟨_, rfl⟩
  have hMv : decM G a aT x₀ ν α s φ *ᵥ v = decN G a aT x₀ ν α s φ *ᵥ w := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hMv' : decM G a aT x₀ ν α s' φ *ᵥ v' = decN G a aT x₀ ν α s' φ *ᵥ w' := by
    rw [hv', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet', Matrix.one_mulVec]
  obtain ⟨T, hT⟩ : ∃ T : (G.Ω 1 → ℂ) → (G.Ω 1 → ℂ), T = fun u =>
      decN G a aT x₀ ν α s φ *ᵥ w + u - decM G a aT x₀ ν α s φ *ᵥ u := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T : (G.Ω 1 → ℂ) → (G.Ω 1 → ℂ), T = fun u =>
      decN G a aT x₀ ν α s' φ *ᵥ w' + u - decM G a aT x₀ ν α s' φ *ᵥ u := ⟨_, rfl⟩
  have hTv : ∀ u, T u - v = (u - v) - decM G a aT x₀ ν α s φ *ᵥ (u - v) := by
    intro u
    subst hT
    show decN G a aT x₀ ν α s φ *ᵥ w + u - decM G a aT x₀ ν α s φ *ᵥ u - v = _
    rw [Matrix.mulVec_sub, hMv]
    abel
  have hTv' : ∀ u, T' u - v' = (u - v') - decM G a aT x₀ ν α s' φ *ᵥ (u - v') := by
    intro u
    subst hT'
    show decN G a aT x₀ ν α s' φ *ᵥ w' + u - decM G a aT x₀ ν α s' φ *ᵥ u - v' = _
    rw [Matrix.mulVec_sub, hMv']
    abel
  have hS0 := agmonSource_nonneg G 0 (fun _ => 0)
  have hc : ∀ u, agmonSource G 0 (fun _ => 0) (T u - v) ≤
      (1 / 4) * agmonSource G 0 (fun _ => 0) (u - v) := by
    intro u
    rw [hTv]
    refine (decM_error_le D H0 hφ hδ (u - v)).trans ?_
    exact mul_le_mul_of_nonneg_right hsm (hS0 _)
  have hc' : ∀ u, agmonSource G 0 (fun _ => 0) (T' u - v') ≤
      (1 / 4) * agmonSource G 0 (fun _ => 0) (u - v') := by
    intro u
    rw [hTv']
    refine (decM_error_le D' H0' hφ hδ (u - v')).trans ?_
    exact mul_le_mul_of_nonneg_right hsm (hS0 _)
  have hag : ∀ u u' : G.Ω 1 → ℂ,
      (∀ z ∈ {z : G.Ω 1 | (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y}, u z = u' z) →
      ∀ z ∈ {z : G.Ω 1 | (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y}, T u z = T' u' z := by
    intro u u' huu z hz
    have hz' : (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y := hz
    subst hT hT'
    show (decN G a aT x₀ ν α s φ *ᵥ w + u - decM G a aT x₀ ν α s φ *ᵥ u) z =
      (decN G a aT x₀ ν α s' φ *ᵥ w' + u' - decM G a aT x₀ ν α s' φ *ᵥ u') z
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [decN_local S hx H hU hU' hw hz', huu z hz,
      decM_local S hx H hU hU' (fun y hy => huu y hy) hz']
  have hfix := fixed_point_agree T T' v v' {z : G.Ω 1 | (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y}
    hc hc' hag
  intro y hy i
  have hZ : ∀ (ss : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (ww : G.Ω 1 × Fin N → ℂ) (Mi : G.Ω 1 → ℂ),
      Mi = (decM G a aT x₀ ν α ss φ)⁻¹ *ᵥ (decN G a aT x₀ ν α ss φ *ᵥ ww) →
      decZ G a aT x₀ ν α ss φ *ᵥ ww = liftOp N (Gsx G a aT x₀ ν α ss) *ᵥ ww -
        liftOp N (Gsx G a aT x₀ ν α ss) *ᵥ (fieldMul (restrictField G φ) *ᵥ Mi) := by
    intro ss ww Mi hMi
    unfold decZ decPi
    rw [Matrix.sub_mulVec, hMi]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have e1 := Gvec_local S hx H hU hU' hw y hy i
  have e2 := Gvec_local S hx H hU hU' (w := fieldMul (restrictField G φ) *ᵥ v)
    (w' := fieldMul (restrictField G φ) *ᵥ v') (fun y hy i => by
      rw [fieldMul_mulVec, fieldMul_mulVec, hfix y hy]) y hy i
  rw [hZ s w v hv, hZ s' w' v' hv', Pi.sub_apply, Pi.sub_apply, e1, e2]

end ZLocal2

end Neumann

section UnitLocal

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x₀ ν : ℝ}
variable {N : ℕ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {α : G.Ω 1 → ℂ}
  {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}

/-- The unit points of `Λ` whose `(k+1)`-block (the `L`-block of the unit lattice) lies in `Y`. -/
def UnitOut (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (Y : Finset (CTorus d L N₁ m₁ (k + 1)))
    (b : unitPts G) : Prop :=
  ∀ y : G.Ω 1, unitBlock1 (unitBlock (y : CTorus d L N₁ m₁ (k + 1))) = unitBlock1 b.1 →
    (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y

/-- The unit points of `Λ` whose `(k+1)`-block meets `S_Y`. -/
def UnitIn (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))) (Y : Finset (CTorus d L N₁ m₁ (k + 1)))
    (b : unitPts G) : Prop :=
  ∃ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y ∧
    unitBlock1 (unitBlock (y : CTorus d L N₁ m₁ (k + 1))) = unitBlock1 b.1

omit [NeZero N₁] [NeZero L] in
theorem mulVec_apply_congr {ι κ' : Type*} [Fintype κ'] (M : Matrix ι κ' ℂ) (f f' : κ' → ℂ) (r : ι)
    (h : ∀ c, M r c ≠ 0 → f c = f' c) : (M *ᵥ f) r = (M *ᵥ f') r := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h0 : M r c = 0
  · simp [h0]
  · rw [h c h0]

theorem covA_apply_congr {ι : Type*} [Fintype ι] [DecidableEq ι] (c b x : ℝ) (Pm : Matrix ι ι ℂ)
    (h h' : ι → ℂ) (p : ι) (hp : h p = h' p) (hP : ∀ q, Pm p q ≠ 0 → h q = h' q) :
    (covA c b x Pm *ᵥ h) p = (covA c b x Pm *ᵥ h') p := by
  rw [covA_mulVec_eq, covA_mulVec_eq]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hp, mulVec_apply_congr Pm h h' p hP]

theorem unitP_ne_zero_imp {b b' : unitPts G} (h : unitP G b b' ≠ 0) :
    unitBlock1 b.1 = unitBlock1 b'.1 := by
  by_contra hne; apply h; simp [unitP, hne]

theorem unitQ_ne_zero_imp {b : unitPts G} {y : G.Ω 1} (h : unitQ G b y ≠ 0) :
    unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = b.1 := by
  by_contra hne; apply h; simp [unitQ, hne]

theorem liftOp_ne_zero_imp {ι : Type*} (A : Matrix ι ι ℂ) {p q : ι × Fin N}
    (h : liftOp N A p q ≠ 0) : p.2 = q.2 ∧ A p.1 q.1 ≠ 0 := by
  unfold liftOp at h
  by_cases hp : p.2 = q.2
  · simp only [hp, ↓reduceIte] at h; exact ⟨hp, h⟩
  · simp [hp] at h

theorem liftRect_ne_zero_imp {ι κ' : Type*} (A : Matrix ι κ' ℂ) {p : ι × Fin N} {q : κ' × Fin N}
    (h : liftRect N A p q ≠ 0) : p.2 = q.2 ∧ A p.1 q.1 ≠ 0 := by
  unfold liftRect at h
  by_cases hp : p.2 = q.2
  · simp only [hp, ↓reduceIte] at h; exact ⟨hp, h⟩
  · simp [hp] at h

theorem decCov_mulVec_eq (h : unitPts G × Fin N → ℂ) :
    decCov G a aT x₀ ν α s φ (unitQ G) (unitP G) *ᵥ h =
      covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h +
        (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ) •
          (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ
            (liftRect N (unitQ G) *ᵥ (decZ G a aT x₀ ν α s φ *ᵥ
              ((liftRect N (unitQ G))ᵀ *ᵥ
                (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h))))) := by
  unfold decCov decZ
  rw [Matrix.add_mulVec, Matrix.smul_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

section UnitLocal2

variable (S : XSetting G a aT ν) (hx : 0 ≤ x₀) (H : LocHyp G X₁ 𝒞 Y α s s')
  {δ κ : ℝ} (D : XData G a aT ν x₀ α κ s) (D' : XData G a aT ν x₀ α κ s')
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
include S hx H D D' hφ hδ hsm

/-- **I-4c (v) at fixed `x`: locality of `C_x(s)` on the unit lattice.** If the inputs agree on the
unit points at the output block and on the blocks meeting `S_Y`, then the outputs of `C_x(s)` and
`C_x(s')` agree at every unit point whose `(k+1)`-block lies in `Y`. -/
theorem decCov_local (h h' : unitPts G × Fin N → ℂ)
    (hh : ∀ b' : unitPts G, (UnitOut G Y b' ∨ UnitIn G X₁ 𝒞 Y b') → ∀ i, h (b', i) = h' (b', i)) :
    ∀ b : unitPts G, UnitOut G Y b → ∀ i,
      (decCov G a aT x₀ ν α s φ (unitQ G) (unitP G) *ᵥ h) (b, i) =
        (decCov G a aT x₀ ν α s' φ (unitQ G) (unitP G) *ᵥ h') (b, i) := by
  classical
  intro b hb i
  rw [decCov_mulVec_eq, decCov_mulVec_eq, Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
  -- the unit points of the output block
  have hbo : ∀ b3 : unitPts G, unitP G b b3 ≠ 0 → UnitOut G Y b3 := by
    intro b3 hP y hy
    exact hb y (hy.trans (unitP_ne_zero_imp hP).symm)
  -- first term
  have t0 : (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h) (b, i) =
      (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h') (b, i) := by
    refine covA_apply_congr _ _ _ _ _ _ _ (hh b (Or.inl hb) i) ?_
    rintro ⟨b3, j⟩ hq
    obtain ⟨hj, hP⟩ := liftOp_ne_zero_imp _ hq
    simp only at hj hP
    subst hj
    exact hh b3 (Or.inl (hbo b3 hP)) _
  -- the intermediate vectors
  have z1 : ∀ b2 : unitPts G, (∃ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y ∧
      unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = b2.1) → ∀ j,
      (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h) (b2, j) =
        (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h') (b2, j) := by
    rintro b2 ⟨y, hy, hyb⟩ j
    have hin : UnitIn G X₁ 𝒞 Y b2 := ⟨y, hy, by rw [hyb]⟩
    refine covA_apply_congr _ _ _ _ _ _ _ (hh b2 (Or.inr hin) j) ?_
    rintro ⟨b3, j'⟩ hq
    obtain ⟨hj, hP⟩ := liftOp_ne_zero_imp _ hq
    simp only at hj hP
    subst hj
    refine hh b3 (Or.inr ⟨y, hy, ?_⟩) _
    rw [hyb]; exact unitP_ne_zero_imp hP
  have z2 : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → ∀ j,
      ((liftRect N (unitQ G))ᵀ *ᵥ (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h)) (y, j) =
        ((liftRect N (unitQ G))ᵀ *ᵥ (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h')) (y, j) := by
    intro y hy j
    refine mulVec_apply_congr _ _ _ _ ?_
    rintro ⟨b2, j'⟩ hq
    rw [liftRect_transpose] at hq
    obtain ⟨hj, hQ⟩ := liftRect_ne_zero_imp _ hq
    simp only at hj hQ
    subst hj
    exact z1 b2 ⟨y, hy, unitQ_ne_zero_imp (by simpa using hQ)⟩ _
  have z3 := decZ_local S hx H D D' hφ hδ hsm z2
  have z4 : ∀ b3 : unitPts G, UnitOut G Y b3 → ∀ j,
      (liftRect N (unitQ G) *ᵥ (decZ G a aT x₀ ν α s φ *ᵥ
        ((liftRect N (unitQ G))ᵀ *ᵥ (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h))))
        (b3, j) =
      (liftRect N (unitQ G) *ᵥ (decZ G a aT x₀ ν α s' φ *ᵥ
        ((liftRect N (unitQ G))ᵀ *ᵥ (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h'))))
        (b3, j) := by
    intro b3 hb3 j
    refine mulVec_apply_congr _ _ _ _ ?_
    rintro ⟨y, j'⟩ hq
    obtain ⟨hj, hQ⟩ := liftRect_ne_zero_imp _ hq
    simp only at hj hQ
    subst hj
    exact z3 y (hb3 y (by rw [unitQ_ne_zero_imp hQ])) _
  have t1 : (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ
      (liftRect N (unitQ G) *ᵥ (decZ G a aT x₀ ν α s φ *ᵥ
        ((liftRect N (unitQ G))ᵀ *ᵥ (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h)))))
        (b, i) =
      (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ
      (liftRect N (unitQ G) *ᵥ (decZ G a aT x₀ ν α s' φ *ᵥ
        ((liftRect N (unitQ G))ᵀ *ᵥ (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h')))))
        (b, i) := by
    refine covA_apply_congr _ _ _ _ _ _ _ (z4 b hb i) ?_
    rintro ⟨b3, j⟩ hq
    obtain ⟨hj, hP⟩ := liftOp_ne_zero_imp _ hq
    simp only at hj hP
    subst hj
    exact z4 b3 (hbo b3 hP) _
  rw [t0, t1]

end UnitLocal2

section UnitIntegrals

open MeasureTheory Set

variable {δ κ : ℝ} (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α κ s)
  (hfam' : ∀ x, 0 ≤ x → XData G a aT ν x α κ s')
  (H : LocHyp G X₁ 𝒞 Y α s s')
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
include hfam hfam' H hφ hδ hsm

/-- **I-4c (v), locality of `C^{1/2}(s)`** (comparison form): for inputs agreeing on the unit points of
the output blocks and of the blocks meeting `S_Y`, the outputs at the unit points with
`(k+1)`-block in `Y` agree. -/
theorem I4c_local_sqrt (h h' : unitPts G × Fin N → ℂ)
    (hh : ∀ b' : unitPts G, (UnitOut G Y b' ∨ UnitIn G X₁ 𝒞 Y b') → ∀ i, h (b', i) = h' (b', i))
    {b : unitPts G} (hb : UnitOut G Y b) (i : Fin N) :
    (decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) *ᵥ h) (b, i) =
      (decCovSqrt G a aT ν α s' φ (unitQ G) (unitP G) *ᵥ h') (b, i) := by
  classical
  have Hs := (standing_pair hfam hφ hδ hsm).1
  have Hs' := (standing_pair hfam' hφ hδ hsm).1
  have S := (hfam 0 le_rfl).st
  have e1 := intMat_mulVec_apply (integrable_decSqrtInt Hs) h (b, i)
  have e2 := intMat_mulVec_apply (integrable_decSqrtInt Hs') h' (b, i)
  have e3 : ∫ x in Ioi (0:ℝ), (decSqrtInt G a aT ν α s φ (unitQ G) (unitP G) x *ᵥ h) (b, i) =
      ∫ x in Ioi (0:ℝ), (decSqrtInt G a aT ν α s' φ (unitQ G) (unitP G) x *ᵥ h') (b, i) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 ≤ x := (mem_Ioi.mp hx).le
    simp only [decSqrtInt, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [decCov_local S hx0 H (hfam x hx0) (hfam' x hx0) hφ hδ hsm h h' hh b hb i]
  simp only [decCovSqrt, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  rw [e1, e2, e3]

/-- **I-4c (v), locality of `𝕃(s)`**: the same statement for the logarithm. -/
theorem I4c_local_log (h h' : unitPts G × Fin N → ℂ)
    (hh : ∀ b' : unitPts G, (UnitOut G Y b' ∨ UnitIn G X₁ 𝒞 Y b') → ∀ i, h (b', i) = h' (b', i))
    {b : unitPts G} (hb : UnitOut G Y b) (i : Fin N) :
    (decLog G a aT ν α s φ (unitQ G) (unitP G) *ᵥ h) (b, i) =
      (decLog G a aT ν α s' φ (unitQ G) (unitP G) *ᵥ h') (b, i) := by
  classical
  have Hs := (standing_pair hfam hφ hδ hsm).1
  have Hs' := (standing_pair hfam' hφ hδ hsm).1
  have S := (hfam 0 le_rfl).st
  have hbo : ∀ b3 : unitPts G, unitP G b b3 ≠ 0 → UnitOut G Y b3 := by
    intro b3 hP y hy
    exact hb y (hy.trans (unitP_ne_zero_imp hP).symm)
  have e1 := intMat_mulVec_apply (integrable_decSub Hs) h (b, i)
  have e2 := intMat_mulVec_apply (integrable_decSub Hs') h' (b, i)
  have e3 : ∫ x in Ioi (0:ℝ), ((decCov G a aT x ν α s φ (unitQ G) (unitP G) -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) *ᵥ h) (b, i) =
      ∫ x in Ioi (0:ℝ), ((decCov G a aT x ν α s' φ (unitQ G) (unitP G) -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) *ᵥ h') (b, i) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 ≤ x := (mem_Ioi.mp hx).le
    have t0 : (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G)) *ᵥ h) (b, i) =
        (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G)) *ᵥ h') (b, i) := by
      refine covA_apply_congr _ _ _ _ _ _ _ (hh b (Or.inl hb) i) ?_
      rintro ⟨b3, j⟩ hq
      obtain ⟨hj, hP⟩ := liftOp_ne_zero_imp _ hq
      simp only at hj hP
      subst hj
      exact hh b3 (Or.inl (hbo b3 hP)) _
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Pi.sub_apply, Pi.sub_apply, t0,
      decCov_local S hx0 H (hfam x hx0) (hfam' x hx0) hφ hδ hsm h h' hh b hb i]
  have t1 : ((1 - liftOp N (unitP G)) *ᵥ h) (b, i) = ((1 - liftOp N (unitP G)) *ᵥ h') (b, i) := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Pi.sub_apply, Pi.sub_apply, Matrix.one_mulVec,
      Matrix.one_mulVec, hh b (Or.inl hb) i]
    congr 1
    refine mulVec_apply_congr _ _ _ _ ?_
    rintro ⟨b3, j⟩ hq
    obtain ⟨hj, hP⟩ := liftOp_ne_zero_imp _ hq
    simp only at hj hP
    subst hj
    exact hh b3 (Or.inl (hbo b3 hP)) _
  have t2 : (liftOp N (unitP G) *ᵥ h) (b, i) = (liftOp N (unitP G) *ᵥ h') (b, i) := by
    refine mulVec_apply_congr _ _ _ _ ?_
    rintro ⟨b3, j⟩ hq
    obtain ⟨hj, hP⟩ := liftOp_ne_zero_imp _ hq
    simp only at hj hP
    subst hj
    exact hh b3 (Or.inl (hbo b3 hP)) _
  simp only [decLog, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at t1 t2 ⊢
  rw [e1, e2, e3, t1, t2]

end UnitIntegrals

end UnitLocal

end Balaban.Localization
