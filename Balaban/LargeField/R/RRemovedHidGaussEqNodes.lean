/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainGaussInt
public import Balaban.LargeField.R.RRemovedHidGaussEqForest

/-!
# The exact integral of the unrolled Gaussian product over the free nodes (W938)

`notes/phase1/LF4R-PLAN.md` §8.5.  `lintegral_gauss_unrolled_eq`: the integral of the unrolled Gaussian
product over the free nodes is, for block trees `B r` of the forest of the window (numberings `e r`, `el r`
respecting the scales `hsc` and the leaf parents `hleaf`), the product over the fixed roots of the composed
densities `g_{P_r}(u_r - 𝒬^♮_r ψ^G)` (`integral_window_comp`) with the leaf values `fldb`; the free roots
give `1`.  `lintegral_gauss_unrolled` (the sup bound) is its application.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section GaussEq

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

open Classical in
/-- **The integral of the unrolled Gaussian product over the free nodes, exactly.** -/
theorem lintegral_gauss_unrolled_eq {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K) (Z : H.Comp (m' + 1))
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    (hnd0 : ∀ y : BlockAt S n M K 0, ¬ nd ⟨0, y⟩)
    [Fintype {b : Σ s, BlockAt S n M K s // nd b}]
    [Fintype {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
      (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
        Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1}]
    (pa : {b : Σ s, BlockAt S n M K s // nd b} → {b : Σ s, BlockAt S n M K s // nd b})
    (hpa : ∀ b : {b : Σ s, BlockAt S n M K s // nd b},
      (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧ b.1.1 + 1 ≤ m' + 1 →
        (pa b).1 = ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩) ∧
      (¬ (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧
        b.1.1 + 1 ≤ m' + 1) → pa b = b))
    (c z : ℕ → ℝ) (hc : ∀ j, k1 ≤ j → j < m' + 1 → 0 < c j)
    (hz : ∀ s, k1 < s → s ≤ m' + 1 → 0 < z s)
    (Fx : {b : Σ s, BlockAt S n M K s // nd b} → Prop) [DecidablePred Fx]
    (hFx : ∀ i, Fx i → pa i = i)
    (u : {b : Σ s, BlockAt S n M K s // nd b} → EuclideanSpace ℝ (Fin N))
    (fldb : ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
    (fld : ({i : {b : Σ s, BlockAt S n M K s // nd b} // ¬ Fx i} → EuclideanSpace ℝ (Fin N)) →
      ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
    (ft : ({i : {b : Σ s, BlockAt S n M K s // nd b} // ¬ Fx i} → EuclideanSpace ℝ (Fin N)) →
      BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hfldb : ∀ Ψ s y, ¬ nd ⟨s, y⟩ → fld Ψ s y = fldb s y)
    (hfldn : ∀ Ψ j y (h : nd ⟨j + 1, y⟩), j + 1 ≤ m' → fld Ψ (j + 1) y =
      if hF : Fx ⟨⟨j + 1, y⟩, h⟩ then u ⟨⟨j + 1, y⟩, h⟩ else Ψ ⟨⟨⟨j + 1, y⟩, h⟩, hF⟩)
    (hft : ∀ Ψ y (h : nd ⟨m' + 1, y⟩), ft Ψ y =
      if hF : Fx ⟨⟨m' + 1, y⟩, h⟩ then u ⟨⟨m' + 1, y⟩, h⟩ else Ψ ⟨⟨⟨m' + 1, y⟩, h⟩, hF⟩) :
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
      ∫⁻ Ψ : {i : {b : Σ s, BlockAt S n M K s // nd b} // ¬ Fx i} → EuclideanSpace ℝ (Fin N),
      ENNReal.ofReal
        ((∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (m' + 1) =>
            ∃ c' ∈ H.ancFin (m' + 1) (m' + 1) Z,
              y ∈ gaussBlocks (H.localHistory M K (m' + 1) c') m'),
          z (m' + 1) ^ N * gaussDens (c m')
            (z (m' + 1) • ft Ψ y - ((S.L : ℝ) ^ S.d)⁻¹ •
              ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K m' =>
                blockMap S.L (M * n K * S.L ^ (K - (m' + 1))) y' = y), fld Ψ m' y')) *
        ∏ j ∈ Finset.Ico k1 m',
          ∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (j + 1) =>
              ∃ c' ∈ H.ancFin (j + 1) (m' + 1) Z,
                y ∈ gaussBlocks (H.localHistory M K (j + 1) c') j),
            z (j + 1) ^ N * gaussDens (c j)
              (z (j + 1) • fld Ψ (j + 1) y - ((S.L : ℝ) ^ S.d)⁻¹ •
                ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K j =>
                  blockMap S.L (M * n K * S.L ^ (K - (j + 1))) y' = y), fld Ψ j y'))
      ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) =
      ∏ r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r}, (if Fx r.1 then ENNReal.ofReal
        (gaussDens ((B r).composedPrecision c z) (u r.1 -
          (B r).composedMean z (fun x => (fun l : {q : (Σ s, BlockAt S n M K s) ×
              {b : Σ s, BlockAt S n M K s // nd b} //
            (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
              Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} => fldb l.1.1.1 l.1.1.2)
            ((el r).symm x).1))) else 1) := by
  classical
  obtain ⟨g1, g2, g3, g4⟩ := gauss_forest_data (H := H) Z nd hnd hnd0 hm pa hpa
  let ψΨ : ({i : {b : Σ s, BlockAt S n M K s // nd b} // ¬ Fx i} → EuclideanSpace ℝ (Fin N)) →
      (Σ s, BlockAt S n M K s) → EuclideanSpace ℝ (Fin N) := fun Ψ b =>
    if h : b.1 = m' + 1 then ft Ψ (h ▸ b.2) else fld Ψ b.1 b.2
  have hψ : ∀ Ψ s (y : BlockAt S n M K s), s ≤ m' → ψΨ Ψ ⟨s, y⟩ = fld Ψ s y := by
    intro Ψ s y hs
    have h : ¬ s = m' + 1 := by omega
    simp only [ψΨ, h, dite_false]
  have hψt : ∀ Ψ y, ψΨ Ψ ⟨m' + 1, y⟩ = ft Ψ y := by
    intro Ψ y
    simp only [ψΨ, dite_true]
  have hext : ∀ Ψ (i : {b : Σ s, BlockAt S n M K s // nd b}),
      ψΨ Ψ i.1 = if h : Fx i then u i else Ψ ⟨i, h⟩ := by
    intro Ψ i
    obtain ⟨⟨s, y⟩, hi⟩ := i
    have hr1 := g2 ⟨⟨s, y⟩, hi⟩
    have hr2 := g3 ⟨⟨s, y⟩, hi⟩
    simp only at hr1 hr2
    by_cases hs : s = m' + 1
    · subst hs
      rw [hψt]
      exact hft Ψ y hi
    · obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
      rw [hψ Ψ _ y (by omega)]
      exact hfldn Ψ j y hi (by omega)
  have hlf : ∀ Ψ (l : {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
      (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
        Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1}),
      fld Ψ l.1.1.1 l.1.1.2 = fldb l.1.1.1 l.1.1.2 := fun Ψ l => hfldb Ψ _ _ l.2.2
  have heq : ∀ Ψ, ENNReal.ofReal
      ((∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (m' + 1) =>
            ∃ c' ∈ H.ancFin (m' + 1) (m' + 1) Z,
              y ∈ gaussBlocks (H.localHistory M K (m' + 1) c') m'),
          z (m' + 1) ^ N * gaussDens (c m')
            (z (m' + 1) • ft Ψ y - ((S.L : ℝ) ^ S.d)⁻¹ •
              ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K m' =>
                blockMap S.L (M * n K * S.L ^ (K - (m' + 1))) y' = y), fld Ψ m' y')) *
        ∏ j ∈ Finset.Ico k1 m',
          ∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (j + 1) =>
              ∃ c' ∈ H.ancFin (j + 1) (m' + 1) Z,
                y ∈ gaussBlocks (H.localHistory M K (j + 1) c') j),
            z (j + 1) ^ N * gaussDens (c j)
              (z (j + 1) • fld Ψ (j + 1) y - ((S.L : ℝ) ^ S.d)⁻¹ •
                ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K j =>
                  blockMap S.L (M * n K * S.L ^ (K - (j + 1))) y' = y), fld Ψ j y')) =
      ENNReal.ofReal (∏ i : {b : Σ s, BlockAt S n M K s // nd b},
        z i.1.1 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) *
        gaussDens (c (i.1.1 - 1)) (z i.1.1 • ψΨ Ψ i.1 - ((S.L ^ S.d : ℕ) : ℝ)⁻¹ •
          ((∑ j ∈ Finset.univ.filter (fun j : {b : Σ s, BlockAt S n M K s // nd b} =>
              pa j ≠ j ∧ pa j = i), ψΨ Ψ j.1) +
            ∑ l ∈ Finset.univ.filter (fun l : {q : (Σ s, BlockAt S n M K s) ×
                {b : Σ s, BlockAt S n M K s // nd b} //
              (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
                Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} => l.1.2 = i),
              fldb l.1.1.1 l.1.1.2))) := by
    intro Ψ
    rw [gauss_prod_eq_nodes hk1 hm Z nd hnd hnd0 pa hpa c z (ψΨ Ψ) (fld Ψ) (ft Ψ) (hψ Ψ) (hψt Ψ)]
    simp only [hlf Ψ]
  obtain ⟨B, e, el, he0, hsc, hpar, hleaf, hE⟩ := lintegral_forest_nodes_eq (m := S.L ^ S.d) (k1 := k1)
    (top := m' + 1) (N := N)
    (fun i : {b : Σ s, BlockAt S n M K s // nd b} => i.1.1) pa
    (fun l : {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
      (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
        Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} => l.1.2)
    g1 g2 g4 (by have := NeZero.pos S.L; positivity) g3 c z hc hz Fx hFx u
    (fun l => fldb l.1.1.1 l.1.1.2) (fun Ψ i => ψΨ Ψ i.1) (fun Ψ i => hext Ψ i)
  refine ⟨B, e, el, he0, hsc, hleaf, ?_⟩
  calc _ = ∫⁻ Ψ : {i : {b : Σ s, BlockAt S n M K s // nd b} // ¬ Fx i} → EuclideanSpace ℝ (Fin N),
        ENNReal.ofReal (∏ i : {b : Σ s, BlockAt S n M K s // nd b},
          z i.1.1 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) *
          gaussDens (c (i.1.1 - 1)) (z i.1.1 • ψΨ Ψ i.1 - ((S.L ^ S.d : ℕ) : ℝ)⁻¹ •
            ((∑ j ∈ Finset.univ.filter (fun j : {b : Σ s, BlockAt S n M K s // nd b} =>
                pa j ≠ j ∧ pa j = i), ψΨ Ψ j.1) +
              ∑ l ∈ Finset.univ.filter (fun l : {q : (Σ s, BlockAt S n M K s) ×
                  {b : Σ s, BlockAt S n M K s // nd b} //
                (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
                  Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} => l.1.2 = i),
                fldb l.1.1.1 l.1.1.2)))
        ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) :=
        lintegral_congr heq
    _ = _ := hE

end GaussEq

end Balaban.LargeField
