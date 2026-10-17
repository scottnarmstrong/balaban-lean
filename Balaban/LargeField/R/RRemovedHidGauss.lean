/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidFree
public import Balaban.LargeField.R.RRemovedChainGaussMain
public import Balaban.LargeField.R.RRemovedHidGaussEq

/-!
# The Gaussian integral over the node coordinates of the regrouping (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, obstruction (2).  `lintegral_gauss_coords`: the integral of the
unrolled Gaussian product over the node coordinates of `exists_regroup_shell` (the outputs at the blocks of
`G₃`, the variables `x↾Nd`, the inner outputs `ψ'_m↾Z₀`) is at most the product of the suprema of the
densities of the fixed roots (the top Gaussian blocks of the tree group); `lintegral_gauss_unrolled` composed
with the measure preserving identification `exists_free_equiv` of the free nodes with the coordinates.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section GaussCoords

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **The Gaussian integral over the node coordinates.**  The fields `fld` (at the scales `≤ m'`) and `ft` (top
scale) are functions of the node coordinates `v = (outputs at `G₃`, `x↾Nd`, `ψ'_m↾Z₀)`: at a node variable the
field is the coordinate (`hfldn`), at a non-node block it does not depend on the node coordinates (`hfldb`),
at the top blocks it is the coordinate of `G₃` or `Z₀` or a value independent of `v` (tree group). -/
theorem lintegral_gauss_coords {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
    {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    (hnd0 : ∀ y : BlockAt S n M K 0, ¬ nd ⟨0, y⟩)
    (Z0 V2 G3 : Set (BlockAt S n M K (m' + 1))) (P2 : BlockAt S n M K (m' + 1) → Prop)
    (hV2 : ∀ y, y ∈ V2 → P2 y → y ∉ Z0)
    (hZ0g : Z0 ⊆ gaussBlocks (H.localHistory M K (m' + 1) Z) m')
    (hG3 : ∀ y, y ∈ G3 ↔ y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧ y ∉ Z0 ∧
      ¬ (y ∈ V2 ∧ P2 y))
    (Nd : Set ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A) [Fintype ↑Nd]
    (hNd : ∀ p, p ∈ Nd ↔ p.1.1.2.1 = VarKind.large ∧ nd ⟨(p.1.1.1 : ℕ), p.1.1.2.2⟩)
    (c z : ℕ → ℝ) (hc : ∀ j, k1 ≤ j → j < m' + 1 → 0 < c j)
    (hz : ∀ s, k1 < s → s ≤ m' + 1 → 0 < z s)
    (fld : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) ×
        ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) ×
          OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) →
      ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
    (ft : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) ×
        ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) ×
          OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) →
      BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hfldn : ∀ v (p : ↥Nd), fld v (p.1.1.1.1 : ℕ) p.1.1.1.2.2 = VarVal.toEuc (v.2.1 p))
    (hfldb : ∀ v v' s (y : BlockAt S n M K s), ¬ nd ⟨s, y⟩ → fld v s y = fld v' s y)
    (hftg : ∀ v (y : {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ G3}),
      ft v y.1 = v.1 y)
    (hftz : ∀ v (y : {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0}),
      ft v y.1 = v.2.2 y)
    (hftt : ∀ v v' y, y ∈ V2 → P2 y → ft v y = ft v' y) :
    ∫⁻ v, ENNReal.ofReal
        ((∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (m' + 1) =>
            ∃ c' ∈ H.ancFin (m' + 1) (m' + 1) Z,
              y ∈ gaussBlocks (H.localHistory M K (m' + 1) c') m'),
          z (m' + 1) ^ N * gaussDens (c m')
            (z (m' + 1) • ft v y - ((S.L : ℝ) ^ S.d)⁻¹ •
              ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K m' =>
                blockMap S.L (M * n K * S.L ^ (K - (m' + 1))) y' = y), fld v m' y')) *
        ∏ j ∈ Finset.Ico k1 m',
          ∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (j + 1) =>
              ∃ c' ∈ H.ancFin (j + 1) (m' + 1) Z,
                y ∈ gaussBlocks (H.localHistory M K (j + 1) c') j),
            z (j + 1) ^ N * gaussDens (c j)
              (z (j + 1) • fld v (j + 1) y - ((S.L : ℝ) ^ S.d)⁻¹ •
                ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K j =>
                  blockMap S.L (M * n K * S.L ^ (K - (j + 1))) y' = y), fld v j y')) ∂
        ((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)).prod
          ((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod
            (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) ≤
      ENNReal.ofReal ((c m' * z (m' + 1) ^ 2 / (2 * Real.pi)) ^ ((N : ℝ) / 2)) ^
        (Finset.univ.filter fun y : BlockAt S n M K (m' + 1) =>
          y ∈ V2 ∧ P2 y ∧ y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m').card := by
  classical
  have hrange : ∀ b, nd b → k1 + 1 ≤ b.1 ∧ b.1 ≤ m' + 1 := by
    rintro ⟨s, y⟩ h
    cases s with
    | zero => exact absurd h (hnd0 y)
    | succ j =>
      obtain ⟨h1, h2, -⟩ := (hnd j y).mp h
      exact ⟨by show k1 + 1 ≤ j + 1; omega, by show j + 1 ≤ m' + 1; omega⟩
  let hfin : Fintype {b : Σ s, BlockAt S n M K s // nd b} :=
    have := finite_graded_nodes (fun s => BlockAt S n M K s) nd (top := m' + 1)
      (fun b hb => (hrange b hb).2)
    Fintype.ofFinite _
  let hfinl : Fintype {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
      (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
        Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} :=
    have := finite_graded_leaves (fun s => BlockAt S n M K s)
      (fun s => blockMap S.L (M * n K * S.L ^ (K - (s + 1)))) nd (top := m' + 1)
      (fun b hb => (hrange b hb).2)
    Fintype.ofFinite _
  let Fx : {b : Σ s, BlockAt S n M K s // nd b} → Prop := fun i =>
    ∃ y : BlockAt S n M K (m' + 1), i.1 = ⟨m' + 1, y⟩ ∧ y ∈ V2 ∧ P2 y
  obtain ⟨ee, hEq, hEg, hEz, hEn⟩ := exists_free_equiv geo cs SD KD hk1 hm hq nd hnd hnd0 Z0 V2 G3 P2
    hV2 hZ0g hG3 Nd hNd Fx (fun i => Iff.rfl)
  let pa : {b : Σ s, BlockAt S n M K s // nd b} → {b : Σ s, BlockAt S n M K s // nd b} := fun b =>
    if h : nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧
        b.1.1 + 1 ≤ m' + 1 then
      ⟨⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩, h.1⟩ else b
  have hpa : ∀ b : {b : Σ s, BlockAt S n M K s // nd b},
      (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧ b.1.1 + 1 ≤ m' + 1 →
        (pa b).1 = ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩) ∧
      (¬ (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧
        b.1.1 + 1 ≤ m' + 1) → pa b = b) :=
    fun b => ⟨fun h => by simp only [pa, h, and_self, ↓reduceDIte], fun h => by simp only [pa, h, ↓reduceDIte]⟩
  have hFx' : ∀ i, Fx i → pa i = i := by
    intro i hi
    obtain ⟨y, hy, -⟩ := hi
    refine (hpa i).2 ?_
    have : i.1.1 = m' + 1 := by rw [hy]
    omega
  have hFxdef : ∀ i : {b : Σ s, BlockAt S n M K s // nd b},
      Fx i ↔ ∃ y : BlockAt S n M K (m' + 1), i.1 = ⟨m' + 1, y⟩ ∧ y ∈ V2 ∧ P2 y := fun i => Iff.rfl
  obtain ⟨B, e, el, -, -, -, hE⟩ := lintegral_gauss_coords_eq geo cs SD KD hk1 hm hq nd hnd hnd0 Z0 V2 G3 P2 hV2 hZ0g hG3 Nd hNd c z hc hz fld ft hfldn hfldb hftg hftz hftt pa hpa Fx hFxdef (ee.symm 0)
  rw [hE]
  refine le_trans (prod_forest_eq_le (m := S.L ^ S.d) (k1 := k1) (top := m' + 1) (N := N)
    (fun i : {b : Σ s, BlockAt S n M K s // nd b} => i.1.1) pa (by have := NeZero.pos S.L; positivity)
    (fun i => (hrange i.1 i.2).2) c z hc hz Fx B _) (le_of_eq ?_)
  have hroots : (Finset.univ.filter fun r : {b : Σ s, BlockAt S n M K s // nd b} =>
      pa r = r ∧ Fx r) = Finset.univ.filter Fx := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hFx' r h, h⟩⟩
  rw [hroots]
  have hval : ∀ r ∈ Finset.univ.filter Fx,
      ENNReal.ofReal ((c (r.1.1 - 1) * z r.1.1 ^ 2 / (2 * Real.pi)) ^ ((N : ℝ) / 2)) =
        ENNReal.ofReal ((c m' * z (m' + 1) ^ 2 / (2 * Real.pi)) ^ ((N : ℝ) / 2)) := by
    intro r hr
    obtain ⟨y, hy, -⟩ := (Finset.mem_filter.mp hr).2
    have : r.1.1 = m' + 1 := by rw [hy]
    rw [this]
    rfl
  rw [Finset.prod_congr rfl hval, Finset.prod_const]
  congr 1
  refine Finset.card_bij (fun r hr => Classical.choose (Finset.mem_filter.mp hr).2) ?_ ?_ ?_
  · intro r hr
    have h := Classical.choose_spec (Finset.mem_filter.mp hr).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2.1, h.2.2, ?_⟩
    obtain ⟨-, -, c', hc', hy⟩ := (hnd m' (Classical.choose (Finset.mem_filter.mp hr).2)).mp
      (by have := r.2; rw [h.1] at this; exact this)
    rw [ancFin_self] at hc'
    exact (Finset.mem_singleton.mp hc') ▸ hy
  · intro r1 hr1 r2 hr2 h12
    have e1 := (Classical.choose_spec (Finset.mem_filter.mp hr1).2).1
    have e2 := (Classical.choose_spec (Finset.mem_filter.mp hr2).2).1
    exact Subtype.ext (e1.trans ((congrArg (fun y => (⟨m' + 1, y⟩ : Σ s, BlockAt S n M K s)) h12).trans
      e2.symm))
  · intro y hy
    obtain ⟨-, hy1, hy2, hy3⟩ := Finset.mem_filter.mp hy
    have hn : nd ⟨m' + 1, y⟩ := (hnd m' y).mpr ⟨hk1, le_rfl, Z, by
      rw [ancFin_self]; exact Finset.mem_singleton_self _, hy3⟩
    refine ⟨⟨⟨m' + 1, y⟩, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨y, rfl, hy1, hy2⟩⟩, ?_⟩
    have h := Classical.choose_spec (⟨y, rfl, hy1, hy2⟩ : Fx ⟨⟨m' + 1, y⟩, hn⟩)
    exact eq_of_heq (Sigma.mk.inj_iff.mp h.1).2.symm

end GaussCoords

end Balaban.LargeField
