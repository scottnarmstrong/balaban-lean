/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidFree
public import Balaban.LargeField.R.RRemovedHidGaussEqNodes

/-!
# The exact Gaussian integral over the node coordinates of the regrouping (W938)

`notes/phase1/LF4R-PLAN.md` §8.5.  `lintegral_gauss_coords_eq`: the integral of the unrolled Gaussian product
over the node coordinates of `exists_regroup_shell` is, for block trees `B r` of the forest of the window, the
product over the fixed roots (the top Gaussian blocks of the tree group) of the composed Gaussian densities
`g_{P_r}(ψ_k(r) - 𝒬^♮_r ψ^G)` (`lintegral_gauss_unrolled_eq` composed with `exists_free_equiv`), and `1` at
the free roots.  `lintegral_gauss_coords` (the sup bound) is its application.
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
theorem lintegral_gauss_coords_eq {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
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
    (hftt : ∀ v v' y, y ∈ V2 → P2 y → ft v y = ft v' y)
    [hfin : Fintype {b : Σ s, BlockAt S n M K s // nd b}]
    [hfinl : Fintype {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
      (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
        Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1}]
    (pa : {b : Σ s, BlockAt S n M K s // nd b} → {b : Σ s, BlockAt S n M K s // nd b})
    (hpa : ∀ b : {b : Σ s, BlockAt S n M K s // nd b},
      (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧ b.1.1 + 1 ≤ m' + 1 →
        (pa b).1 = ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩) ∧
      (¬ (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧
        b.1.1 + 1 ≤ m' + 1) → pa b = b))
    (Fx : {b : Σ s, BlockAt S n M K s // nd b} → Prop) [DecidablePred Fx]
    (hFxdef : ∀ i : {b : Σ s, BlockAt S n M K s // nd b},
      Fx i ↔ ∃ y : BlockAt S n M K (m' + 1), i.1 = ⟨m' + 1, y⟩ ∧ y ∈ V2 ∧ P2 y)
    (v0 : OutPart N (Vblk R (H.localHistory M K (m' + 1) Z)
        (m' + 1)) (· ∈ G3) ×
        ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) ×
          OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) :
    ∃ (B : ∀ r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r},
        BlockTree (S.L ^ S.d) k1 r.1.1.1)
      (e : ∀ r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r},
        {i : {b : Σ s, BlockAt S n M K s // nd b} //
          pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] i = r.1} ≃ Fin ((B r).n + 1))
      (el : ∀ r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r},
        {l : {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
            (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
              Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} //
          pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] l.1.2 = r.1} ≃ Fin (B r).nLeaf),
      (∀ r, (e r ⟨r.1, iter_fixed pa r.2 _⟩ : ℕ) = 0) ∧
      (∀ r i, (B r).scale (e r i) = i.1.1.1) ∧
      (∀ r l, (B r).leafPar (el r l) = e r ⟨l.1.1.2, l.2⟩) ∧
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
            (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) =
      ∏ r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r}, (if Fx r.1 then ENNReal.ofReal
        (gaussDens ((B r).composedPrecision c z)
          ((fun b : {b : Σ s, BlockAt S n M K s // nd b} =>
              if h : b.1.1 = m' + 1 then ft v0 (h ▸ b.1.2) else 0) r.1 -
            (B r).composedMean z (fun x => (fun l : {q : (Σ s, BlockAt S n M K s) ×
                {b : Σ s, BlockAt S n M K s // nd b} //
              (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
                Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} => fld v0 l.1.1.1 l.1.1.2)
              ((el r).symm x).1))) else 1) := by
  classical
  obtain ⟨ee, hEq, hEg, hEz, hEn⟩ := exists_free_equiv geo cs SD KD hk1 hm hq nd hnd hnd0 Z0 V2 G3 P2
    hV2 hZ0g hG3 Nd hNd Fx hFxdef
  have hFx' : ∀ i, Fx i → pa i = i := by
    intro i hi
    obtain ⟨y, hy, -⟩ := (hFxdef i).mp hi
    refine (hpa i).2 ?_
    have : i.1.1 = m' + 1 := by rw [hy]
    omega
  let u : {b : Σ s, BlockAt S n M K s // nd b} → EuclideanSpace ℝ (Fin N) := fun b =>
    if h : b.1.1 = m' + 1 then ft v0 (h ▸ b.1.2) else 0
  have hZV : ∀ y, y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' →
      y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) := fun y hy =>
    ZBlk_mem_Vblk hm Z y (gaussBlocks_zblk hm Z hy)
  have hfldn' : ∀ (Ψ : {i : {b : Σ s, BlockAt S n M K s // nd b} // ¬ Fx i} →
      EuclideanSpace ℝ (Fin N)) j (y : BlockAt S n M K (j + 1)) (h : nd ⟨j + 1, y⟩), j + 1 ≤ m' →
      fld (ee.symm Ψ) (j + 1) y =
        if hF : Fx ⟨⟨j + 1, y⟩, h⟩ then u ⟨⟨j + 1, y⟩, h⟩ else Ψ ⟨⟨⟨j + 1, y⟩, h⟩, hF⟩ := by
    intro Ψ j y h hj
    obtain ⟨hkj, hjm, c', hc', hy⟩ := (hnd j y).mp h
    have hF : ¬ Fx ⟨⟨j + 1, y⟩, h⟩ := by
      intro hFF
      obtain ⟨y', hy', -⟩ := (hFxdef _).mp hFF
      have := (Sigma.mk.inj_iff.mp hy').1
      omega
    rw [dite_eq_right_of_eq_false (eq_false hF)]
    obtain ⟨hb, hA⟩ := node_var geo cs SD KD hkj hj hm hq hc'
      (gaussBlocks_zblk (by omega : j + 1 ≤ K) c' hy)
    have hpN : (⟨mkVar (H.localHistory M K (m' + 1) Z) (m' + 1) (j + 1) .large y (by omega) hb, hA⟩ :
        ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A) ∈ Nd := (hNd _).mpr ⟨rfl, h⟩
    have h1 := hfldn (ee.symm Ψ) ⟨_, hpN⟩
    have h2 := hEn (ee.symm Ψ) ⟨_, hpN⟩ ⟨⟨⟨j + 1, y⟩, h⟩, hF⟩ rfl
    rw [ee.apply_symm_apply] at h2
    exact h1.trans h2.symm
  have hft' : ∀ (Ψ : {i : {b : Σ s, BlockAt S n M K s // nd b} // ¬ Fx i} →
      EuclideanSpace ℝ (Fin N)) (y : BlockAt S n M K (m' + 1)) (h : nd ⟨m' + 1, y⟩),
      ft (ee.symm Ψ) y =
        if hF : Fx ⟨⟨m' + 1, y⟩, h⟩ then u ⟨⟨m' + 1, y⟩, h⟩ else Ψ ⟨⟨⟨m' + 1, y⟩, h⟩, hF⟩ := by
    intro Ψ y h
    by_cases hF : Fx ⟨⟨m' + 1, y⟩, h⟩
    · rw [dite_eq_left_of_eq_true (eq_true hF)]
      obtain ⟨y', hy', hy2⟩ := (hFxdef _).mp hF
      have h3 : y' = y := eq_of_heq (Sigma.mk.inj_iff.mp hy').2.symm
      subst h3
      refine (hftt _ v0 y' hy2.1 hy2.2).trans ?_
      simp [u]
    · rw [dite_eq_right_of_eq_false (eq_false hF)]
      obtain ⟨hkj, -, c', hc', hy⟩ := (hnd m' y).mp h
      rw [ancFin_self] at hc'
      have hcZ : c' = Z := Finset.mem_singleton.mp hc'
      subst hcZ
      have hnt : ¬ (y ∈ V2 ∧ P2 y) := fun ht => hF ((hFxdef _).mpr ⟨y, rfl, ht⟩)
      by_cases h0 : y ∈ Z0
      · have h4 := hftz (ee.symm Ψ) ⟨y, hZV y hy, h0⟩
        have h5 := hEz (ee.symm Ψ) ⟨y, hZV y hy, h0⟩ ⟨⟨⟨m' + 1, y⟩, h⟩, hF⟩ rfl
        rw [ee.apply_symm_apply] at h5
        exact h4.trans h5.symm
      · have h4 := hftg (ee.symm Ψ) ⟨y, hZV y hy, (hG3 y).mpr ⟨hy, h0, hnt⟩⟩
        have h5 := hEg (ee.symm Ψ) ⟨y, hZV y hy, (hG3 y).mpr ⟨hy, h0, hnt⟩⟩ ⟨⟨⟨m' + 1, y⟩, h⟩, hF⟩ rfl
        rw [ee.apply_symm_apply] at h5
        exact h4.trans h5.symm
  obtain ⟨B, e, el, he0, hsc, hleaf, hE⟩ := lintegral_gauss_unrolled_eq hk1 hm Z nd hnd hnd0 pa hpa c z hc hz
    Fx hFx' u (fun s y => fld v0 s y) (fun Ψ => fld (ee.symm Ψ)) (fun Ψ => ft (ee.symm Ψ))
    (fun Ψ s y h => hfldb _ _ s y h) hfldn' hft'
  refine ⟨B, e, el, he0, hsc, hleaf, Eq.trans ?_ hE⟩
  rw [← hEq.lintegral_comp_emb ee.measurableEmbedding]
  refine lintegral_congr fun v => ?_
  simp only [MeasurableEquiv.symm_apply_apply]

end GaussCoords

end Balaban.LargeField
