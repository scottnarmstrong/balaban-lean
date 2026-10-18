/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowCloseNode

/-!
# The exact node integral of the window with the datum and the composed precision explicit (blocker 4, W964)

`notes/phase1/LF4R-PLAN.md` §9.  `exists_bgData_of_field_zero`: the datum `Ψ` of a generating set from a field on the blocks
of the history, with `h = 0` and `Ψ = 0` off `Ω₁` (the collar carries no data).  `window_node_integral_exact`:
`window_node_integral_pt` with the datum `D` pinned (`h = 0`, collar `0`, `Ω₁` values) and the composed precision
`β_k a^♮_z = (∑_y ϖ_j² w_y² / c_j)⁻¹` of the Gaussian chain over the nodes `y` below the root `z` explicit
(`BlockTree.composedPrecision` through the equivalence `e` of the node forest with the block tree).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory

section Zero

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L] {m' : ℕ}

open Classical in
/-- **The datum of a window generating set from a field on the blocks, with `h = 0` and the collar
values `cl`** (`cl` vanishes off the data sites; no data off `Ω₁ ∪ C(Ω₁)`). -/
theorem exists_bgData_of_field_collar (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hmK : m' + 1 ≤ K) {N : ℕ} {ϱ : ℝ}
    (G : GeneratingSet S.d S.L (M * n (m' + 1)) (m' + 1) ϱ)
    (fldv : ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
    (cl : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)) → Fin N → ℝ)
    (hcl : ∀ x, x ∉ dataSites G → ∀ i, cl x i = 0) :
    ∃ D : BgData G N, D.IsReal ∧ (∀ x i, D.h x i = 0) ∧
      (∀ x, x ∉ G.Ω 1 → ∀ i, D.Ψ x i = ((cl x i : ℝ) : ℂ)) ∧
      ∀ x ∈ G.Ω 1, ∀ i, D.Ψ x i =
        ((fldv (G.layerIndex x) (jBlock S.d S.L (M * n K) K (G.layerIndex x)
          (torusCast (fine_eq_top hnn hmK).symm x)) i : ℝ) : ℂ) := by
  obtain ⟨D1, hD1real, hD1⟩ := exists_bgData_of_field hnn hmK G fldv
  refine ⟨⟨fun x i => if x ∈ G.Ω 1 then D1.Ψ x i else ((cl x i : ℝ) : ℂ), fun _ _ => 0, ?_,
    fun _ _ _ _ _ _ _ => rfl, ?_, fun _ _ => rfl⟩, ?_, fun _ _ => rfl, ?_, ?_⟩
  · intro q hq1 hqk x hx x' hx'
    have hx'l : x' ∈ G.layer q := (G.mem_layer_iff hq1 hqk (GeneratingSet.mem_blk.1 hx')).2 hx
    have h1 : x ∈ G.Ω 1 := G.layer_subset hq1 hqk hx
    have h2 : x' ∈ G.Ω 1 := G.layer_subset hq1 hqk hx'l
    funext i
    simp only [h1, h2, ↓reduceIte]
    exact congrFun (D1.Ψ_layerConst q hq1 hqk x hx x' hx') i
  · intro x hx
    funext i
    have : x ∉ G.Ω 1 := fun h => hx ((mem_dataSites G).2 (Or.inl h))
    simp [this, hcl x hx i]
  · intro x i
    refine ⟨?_, by simp⟩
    by_cases hx : x ∈ G.Ω 1
    · simpa [hx] using (hD1real x i).1
    · simp [hx]
  · intro x hx i
    simp [hx]
  · intro x hx i
    simp only [hx, ↓reduceIte]
    exact hD1 x hx i

open Classical in
/-- **The datum of a window generating set from a field on the blocks, with `h = 0` and no data off `Ω₁`.** -/
theorem exists_bgData_of_field_zero (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hmK : m' + 1 ≤ K) {N : ℕ} {ϱ : ℝ}
    (G : GeneratingSet S.d S.L (M * n (m' + 1)) (m' + 1) ϱ)
    (fldv : ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N)) :
    ∃ D : BgData G N, D.IsReal ∧ (∀ x i, D.h x i = 0) ∧ (∀ x, x ∉ G.Ω 1 → ∀ i, D.Ψ x i = 0) ∧
      ∀ x ∈ G.Ω 1, ∀ i, D.Ψ x i =
        ((fldv (G.layerIndex x) (jBlock S.d S.L (M * n K) K (G.layerIndex x)
          (torusCast (fine_eq_top hnn hmK).symm x)) i : ℝ) : ℂ) := by
  obtain ⟨D, hr, hh, hc, hD⟩ := exists_bgData_of_field_collar hnn hmK G fldv (fun _ _ => 0)
    (fun _ _ _ => rfl)
  exact ⟨D, hr, hh, fun x hx i => by simpa using hc x hx i, hD⟩

end Zero

section Exact

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **The exact node integral of the window, the datum (collar values `cl`) and the composed precision
explicit.** -/
theorem window_node_integral_exact_collar {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
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
          OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))

    (hMS : M = S.M) (G : S.Good)
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    (h3 : 8 ≤ S.L * S.lateR (m' + 1)) (hW : H.RipeWindow (m' + 1) Z) (hk1def : S.k1 (m' + 1) = k1)
    (hZ0box : ∀ s : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)),
      torusCast (congrArg (· * n (m' + 1)) hMS)
        (blockMap (S.L ^ (m' + 1)) (M * n (m' + 1)) s) ∈ H.Zzero (m' + 1) Z →
        jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top H.F.hnn hm).symm s) ∈ Z0)
    (βk : ℝ) (hβ : 0 < βk)
    (cl : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)) → Fin N → ℝ)
    (hcl : ∀ x, x ∉ dataSites ((windowOfHistory H Z geo hm hW).windowGenSet
      (windowOfHistory_hyp (g := geo) hm hW)) → ∀ i, cl x i = 0) :
    ∃ (D : Background.BgData (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) N)
      (ψk : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) → Fin N → ℂ)
      (Zb : Finset (Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1)))))
      (aN : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) → ℝ),
      D.IsReal ∧
      (∀ zb, zb ∈ Zb ↔ ∃ y : BlockAt S n M K (m' + 1), y ∈ V2 ∧ P2 y ∧
        y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧
          zb = torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y) ∧
      (∀ zb ∈ Zb, 0 < βk * aN zb) ∧
      (∀ y : BlockAt S n M K (m' + 1), y ∈ V2 → P2 y →
        y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' → ∀ i,
          ψk (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y) i = ((ft v0 y i : ℝ) : ℂ)) ∧
      (∀ x ∈ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).Ω 1, (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x ≠ m' + 1 → ∀ i, D.Ψ x i =
        ((fld v0 ((windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x)
          (jBlock S.d S.L (M * n K) K ((windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x)
            (torusCast (fine_eq_top H.F.hnn hm).symm x)) i : ℝ) : ℂ)) ∧
      (∀ x ∈ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).Ω 1, (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x = m' + 1 → ∀ i, D.Ψ x i =
        ((ft v0 (jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top H.F.hnn hm).symm x)) i : ℝ) : ℂ)) ∧
      (∀ x i, D.h x i = 0) ∧ (∀ x, x ∉ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).Ω 1 → ∀ i, D.Ψ x i = ((cl x i : ℝ) : ℂ)) ∧
      (∀ y : BlockAt S n M K (m' + 1), y ∈ V2 → P2 y → y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' →
        ∀ b0 : {b : Σ s, BlockAt S n M K s // nd b}, b0.1 = ⟨m' + 1, y⟩ →
          βk * aN (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y) =
            (∑ b ∈ Finset.univ.filter (fun b : {b : Σ s, BlockAt S n M K s // nd b} =>
                pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] b = b0),
              varpi (m' + 1) z (b.1.1 - 1) ^ 2 * blockFrac (S.L ^ S.d) (m' + 1) b.1.1 ^ 2 / c (b.1.1 - 1))⁻¹) ∧
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
        ENNReal.ofReal (ActionConv.constNat N βk aN Zb *
          Real.exp (-(ActionConv.gaussNat (windowOfHistory H Z geo hm hW |>.windowGenSet
            (windowOfHistory_hyp (g := geo) hm hW)) (varpi (m' + 1) z) D.Ψ βk aN ψk Zb).re)) := by
  classical
  have hnn := H.F.hnn
  have hL : 2 ≤ S.L := H.F.ok.two_le_L
  have hR : ∀ j, 1 ≤ j → j < m' + 1 → S.Rb ≤ R j := fun j _ _ => geo.hRlow j
  have hk1p : 1 ≤ k1 := hk1def ▸ hW.k1_pos hm
  have hWh := windowOfHistory_hyp (g := geo) hm hW
  have hZk1 : ∀ x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)), x ∈ H.locFine Z M k1 →
      jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hm).symm x) ∈ Z0 := by
    subst hMS
    intro x hx
    have := locFine_subset_fineZzero G h18 h3 hm hW (x := x) (hk1def ▸ hx)
    exact hZ0box x this
  let W := windowOfHistory H Z geo hm hW
  have hWfull : ∀ j, W.full.Ω j = (H.locGen Z M hm H.F.ok.two_le_L (fun j _ _ => geo.hRlow j)).Ω j :=
    fun j => windowOfHistory_full_Ω H Z geo hm hW j
  have hWZ : W.Z = H.locFineFin Z (m' + 1) := windowOfHistory_Z H Z geo hm hW
  have hWZk1 : W.Zk1 = H.locFineFin Z k1 := by rw [windowOfHistory_Zk1, hk1def]
  let zbk : BlockAt S n M K (m' + 1) → Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) :=
    fun y => torusCast (blk_eq_top hnn hm (le_refl (m' + 1))).symm y
  let Zb : Finset (Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1)))) :=
    (Finset.univ.filter fun y : BlockAt S n M K (m' + 1) =>
      y ∈ V2 ∧ P2 y ∧ y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m').image zbk
  have hZb : ∀ zb, zb ∈ Zb ↔ ∃ y : BlockAt S n M K (m' + 1), y ∈ V2 ∧ P2 y ∧
      y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧ zb = zbk y := by
    intro zb
    simp only [Zb, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy.1, hy.2.1, hy.2.2, rfl⟩
    · rintro ⟨y, h1, h2, h3, rfl⟩; exact ⟨y, ⟨h1, h2, h3⟩, rfl⟩
  let ψk : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) → Fin N → ℂ := fun zb =>
    if h : ∃ y : BlockAt S n M K (m' + 1), y ∈ V2 ∧ P2 y ∧
        y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧ zbk y = zb then
      fun i => ((ft v0 (Classical.choose h) i : ℝ) : ℂ) else 0
  have hψk : ∀ y : BlockAt S n M K (m' + 1), y ∈ V2 → P2 y →
      y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' → ∀ i,
        ψk (zbk y) i = ((ft v0 y i : ℝ) : ℂ) := by
    intro y hyV hyP hyg i
    have h : ∃ y' : BlockAt S n M K (m' + 1), y' ∈ V2 ∧ P2 y' ∧
        y' ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧ zbk y' = zbk y := ⟨y, hyV, hyP, hyg, rfl⟩
    have := torusCast_injective _ (Classical.choose_spec h).2.2.2
    simp only [ψk, h, dite_true, this]
  let fldv : ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N) := fun s y =>
    if h : s = m' + 1 then ft v0 (h ▸ y) else fld v0 s y
  obtain ⟨D, hDreal, hDh, hD0, hD⟩ := exists_bgData_of_field_collar hnn hm (W.windowGenSet hWh) fldv cl hcl
  have hne : ∀ s (y : BlockAt S n M K s), s ≠ m' + 1 → fldv s y = fld v0 s y := by
    intro s y hs; simp only [fldv, hs, dite_false]
  have htop : ∀ j (hj : j = m' + 1) (xx : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))),
      fldv j (jBlock S.d S.L (M * n K) K j (torusCast (fine_eq_top hnn hm).symm xx)) =
        ft v0 (jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hm).symm xx)) := by
    intro j hj xx; subst hj; simp [fldv]
  let Ψ := D.Ψ
  have hΨ : ∀ y : BlockAt S n M K (m' + 1), y ∈ V2 → P2 y →
      y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' →
      ∀ s ∈ fib S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) (zbk y), ∀ i,
        Ψ s i = ((fld v0 ((H.locGen Z M hm H.F.ok.two_le_L (fun j _ _ => geo.hRlow j)).layerIndex s)
          (jBlock S.d S.L (M * n K) K
            ((H.locGen Z M hm H.F.ok.two_le_L (fun j _ _ => geo.hRlow j)).layerIndex s)
            (torusCast (fine_eq_top H.F.hnn hm).symm s)) i : ℝ) : ℂ) := by
    intro y hyV hyP hyg s hs i
    have hsY := (mem_fib_cast hnn hm (le_refl (m' + 1)) y s).mp hs
    have hyk1 : s ∉ H.locFine Z M k1 := fun hxl => by
      have := hZk1 s hxl
      rw [hsY] at this
      exact hV2 y hyV hyP this
    obtain ⟨hΩ, hlay⟩ := window_site_facts hnn hm hL hR hk1p hk1 W hWh hWfull hWZ hWZk1 hyg hsY hyk1
    have hΩloc : s ∈ (H.locGen Z M hm hL hR).Ω 1 :=
      (H.locGen Z M hm hL hR).Ω_antitone le_rfl hk1p (by omega)
        (mem_locGen_of_not_locFine hm hL hR hk1p hk1 hyk1)
    have hnotop := (gauss_top_site hnn hm hL hR hyg hsY).2
    have hlne : (H.locGen Z M hm hL hR).layerIndex s ≠ m' + 1 := fun heq => by
      have hl := ((H.locGen Z M hm hL hR).layerIndex_spec hΩloc).2.2
      rw [heq] at hl
      exact hnotop ((GeneratingSet.mem_layer _).mp hl).1
    have := hD s hΩ i
    rw [hlay] at this
    show D.Ψ s i = _
    rw [this, hne _ _ hlne]
  obtain ⟨B, e, el, he0, hsc, hleaf, hE⟩ := lintegral_gauss_coords_eq geo cs SD KD hk1 hm hq nd hnd hnd0
    Z0 V2 G3 P2 hV2 hZ0g hG3 Nd hNd c z hc hz fld ft hfldn hfldb hftg hftz hftt pa hpa Fx hFxdef v0
  have hnn := H.F.hnn
  have hL : 2 ≤ S.L := H.F.ok.two_le_L
  have hR : ∀ j, 1 ≤ j → j < m' + 1 → S.Rb ≤ R j := fun j _ _ => geo.hRlow j
  have hmpos : 0 < S.L ^ S.d := by have := NeZero.pos S.L; positivity
  have hgauss : ∀ y : BlockAt S n M K (m' + 1), nd ⟨m' + 1, y⟩ →
      y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' := by
    intro y h
    obtain ⟨-, -, c', hc', hg⟩ := (hnd m' y).mp h
    rw [ancFin_self] at hc'
    rwa [Finset.mem_singleton.mp hc'] at hg
  have hndg : ∀ y : BlockAt S n M K (m' + 1), y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' →
      nd ⟨m' + 1, y⟩ := fun y hy =>
    (hnd m' y).mpr ⟨hk1, le_rfl, Z, by rw [ancFin_self]; exact Finset.mem_singleton_self _, hy⟩
  have hrootY : ∀ r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r}, Fx r.1 →
      ∃ y : BlockAt S n M K (m' + 1), r.1.1 = ⟨m' + 1, y⟩ ∧ y ∈ V2 ∧ P2 y :=
    fun r h => (hFxdef r.1).mp h
  let ych : {r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r} // Fx r.1} →
      BlockAt S n M K (m' + 1) := fun r => Classical.choose (hrootY r.1 r.2)
  have hych : ∀ r : {r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r} // Fx r.1},
      r.1.1.1 = ⟨m' + 1, ych r⟩ ∧ ych r ∈ V2 ∧ P2 (ych r) :=
    fun r => Classical.choose_spec (hrootY r.1 r.2)
  let f : {r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r} // Fx r.1} →
      Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) := fun r =>
    torusCast (blk_eq_top hnn hm (le_refl (m' + 1))).symm (ych r)
  have hf : Function.Injective f := by
    intro r r' h
    have h1 := torusCast_injective _ h
    have h2 : r.1.1.1 = r'.1.1.1 := by rw [(hych r).1, (hych r').1, h1]
    exact Subtype.ext (Subtype.ext (Subtype.ext h2))
  have hZb' : ∀ x, x ∈ Zb ↔ ∃ r, f r = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hyV, hyP, hyg, rfl⟩ := (hZb x).mp hx
      let b : {b : Σ s, BlockAt S n M K s // nd b} := ⟨⟨m' + 1, y⟩, hndg y hyg⟩
      have hfix : pa b = b := (hpa b).2 (fun h => by
        have := h.2
        change m' + 1 + 1 ≤ m' + 1 at this
        omega)
      let r : {r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r} // Fx r.1} :=
        ⟨⟨b, hfix⟩, (hFxdef b).mpr ⟨y, rfl, hyV, hyP⟩⟩
      refine ⟨r, ?_⟩
      have h1 : (⟨m' + 1, y⟩ : Σ s, BlockAt S n M K s) = ⟨m' + 1, ych r⟩ := (hych r).1
      have h2 : y = ych r := eq_of_heq (Sigma.mk.inj_iff.mp h1).2
      show torusCast _ (ych r) = torusCast _ y
      rw [h2]
    · rintro ⟨r, rfl⟩
      obtain ⟨hr1, hr2, hr3⟩ := hych r
      refine (hZb _).mpr ⟨ych r, hr2, hr3, ?_, rfl⟩
      exact hgauss _ (by have := r.1.1.2; rwa [hr1] at this)
  have hPpos : ∀ r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r}, Fx r.1 →
      0 < (B r).composedPrecision c z := by
    intro r hr
    obtain ⟨y, hry, -⟩ := hrootY r hr
    have hrk : r.1.1.1 = m' + 1 := congrArg Sigma.fst hry
    exact (B r).composedPrecision_pos hmpos c z (fun s hs hle => hz s hs (by rw [← hrk]; exact hle))
      (fun j hj hlt => hc j hj (by rw [← hrk]; exact hlt))
  have hreal : ∀ zb ∈ Zb, ∀ i, (ψk zb i - ActionConv.compMeanT (W.windowGenSet hWh)
      (varpi (m' + 1) z) Ψ zb i).im = 0 := by
    intro zb hzb i
    obtain ⟨y, hyV, hyP, hyg, rfl⟩ := (hZb zb).mp hzb
    rw [Complex.sub_im, compMeanT_im_eq_zero (W.windowGenSet hWh) (varpi (m' + 1) z) Ψ _ i
      (fun s hs => by rw [hΨ y hyV hyP hyg s hs i]; exact Complex.ofReal_im _),
      hψk y hyV hyP hyg i, Complex.ofReal_im]
    simp
  have hμ : ∀ r : {r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r} // Fx r.1},
      (fun r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r} =>
        (fun b : {b : Σ s, BlockAt S n M K s // nd b} =>
            if h : b.1.1 = m' + 1 then ft v0 (h ▸ b.1.2) else 0) r.1 -
          (B r).composedMean z (fun x => (fun l : {q : (Σ s, BlockAt S n M K s) ×
              {b : Σ s, BlockAt S n M K s // nd b} //
            (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
              Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} => fld v0 l.1.1.1 l.1.1.2)
            ((el r).symm x).1)) r.1 =
        (WithLp.toLp 2 fun i => (ψk (f r) i - ActionConv.compMeanT (W.windowGenSet hWh)
          (varpi (m' + 1) z) Ψ (f r) i).re : EuclideanSpace ℝ (Fin N)) := by
    intro r
    obtain ⟨hr1, hr2, hr3⟩ := hych r
    have hyg : ych r ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' :=
      hgauss _ (by have := r.1.1.2; rwa [hr1] at this)
    have hyk1 : ∀ x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)),
        jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hm).symm x) = ych r →
          x ∉ H.locFine Z M k1 := fun x hx hxl => by
      have := hZk1 x hxl
      rw [hx] at this
      exact hV2 _ hr2 hr3 this
    have hzy := mem_fib_cast hnn hm (le_refl (m' + 1)) (ych r)
    have hGlay : ∀ s ∈ fib S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1)
        (torusCast (blk_eq_top hnn hm (le_refl (m' + 1))).symm (ych r)),
        (W.windowGenSet hWh).layerIndex s = (H.locGen Z M hm hL hR).layerIndex s := by
      intro s hs
      have hsY := (hzy s).mp hs
      obtain ⟨hZ, -⟩ := gauss_top_site hnn hm hL hR hyg hsY
      have hx : s ∈ W.Z \ W.Zk1 := Finset.mem_sdiff.mpr
        ⟨by rw [hWZ, RegionHistory.mem_locFineFin]; exact hZ,
         by rw [hWZk1, RegionHistory.mem_locFineFin]; exact hyk1 s hsY⟩
      exact (windowGenSet_layerIndex_eq_full W hWh hx).trans (layerIndex_congr W.full _ hWfull s)
    exact root_mean hnn hm hL hR hk1p hk1 nd hnd hnd0 pa hpa r.1 (ych r) hr1 (B r.1) (e r.1) (el r.1)
      (hsc r.1) (hleaf r.1) hyk1 _ hzy (W.windowGenSet hWh) hGlay z Ψ ψk (fun s y => fld v0 s y)
      (fun b => if h : b.1.1 = m' + 1 then ft v0 (h ▸ b.1.2) else 0)
      (fun s hs i => hΨ (ych r) hr2 hr3 hyg s hs i)
      (fun i => by
        have hut := ut_eq nd r.1.1 (ych r) hr1 (ft v0)
        simp only at hut ⊢
        rw [hut]
        exact hψk (ych r) hr2 hr3 hyg i)
  obtain ⟨aN, hP, hprod⟩ := ActionConv.prod_roots_eq_constNat_exp_of_inj
    (ρ := {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r}) (fun r => Fx r.1)
    (fun r => (B r).composedPrecision c z)
    (fun r => (fun b : {b : Σ s, BlockAt S n M K s // nd b} =>
            if h : b.1.1 = m' + 1 then ft v0 (h ▸ b.1.2) else 0) r.1 -
          (B r).composedMean z (fun x => (fun l : {q : (Σ s, BlockAt S n M K s) ×
              {b : Σ s, BlockAt S n M K s // nd b} //
            (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
              Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} => fld v0 l.1.1.1 l.1.1.2)
            ((el r).symm x).1))
    (W.windowGenSet hWh) (varpi (m' + 1) z) Ψ hβ ψk Zb f hf hZb' hPpos hreal hμ
  obtain ⟨aN, hP, hprod⟩ := ActionConv.prod_roots_eq_constNat_exp_of_inj
    (ρ := {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r}) (fun r => Fx r.1)
    (fun r => (B r).composedPrecision c z)
    (fun r => (fun b : {b : Σ s, BlockAt S n M K s // nd b} =>
            if h : b.1.1 = m' + 1 then ft v0 (h ▸ b.1.2) else 0) r.1 -
          (B r).composedMean z (fun x => (fun l : {q : (Σ s, BlockAt S n M K s) ×
              {b : Σ s, BlockAt S n M K s // nd b} //
            (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
              Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} => fld v0 l.1.1.1 l.1.1.2)
            ((el r).symm x).1))
    (W.windowGenSet hWh) (varpi (m' + 1) z) Ψ hβ ψk Zb f hf hZb' hPpos hreal hμ
  refine ⟨D, ψk, Zb, aN, hDreal, hZb, fun zb hzb => ?_, hψk, fun x hx hxl i => ?_, fun x hx hxl i => ?_,
    hDh, hD0, ?_, hE.trans (by convert hprod)⟩
  · obtain ⟨r, rfl⟩ := (hZb' zb).mp hzb
    rw [← hP r]
    exact hPpos r.1 r.2
  · show D.Ψ x i = _
    rw [hD x hx i, hne _ _ hxl]
  · show D.Ψ x i = _
    rw [hD x hx i, htop _ hxl x]
  · intro y hyV hyP hyg b0 hb0
    have hb01 : b0.1.1 = m' + 1 := by rw [hb0]
    have hfix : pa b0 = b0 := (hpa b0).2 (fun h => by have := h.2; omega)
    let r : {r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r} // Fx r.1} :=
      ⟨⟨b0, hfix⟩, (hFxdef b0).mpr ⟨y, hb0, hyV, hyP⟩⟩
    have hfr : f r = zbk y := by
      have h1 : (⟨m' + 1, y⟩ : Σ s, BlockAt S n M K s) = ⟨m' + 1, ych r⟩ := hb0.symm.trans (hych r).1
      have h2 : y = ych r := eq_of_heq (Sigma.mk.inj_iff.mp h1).2
      show torusCast _ (ych r) = torusCast _ y
      rw [h2]
    have e1 : βk * aN (zbk y) = (B r.1).composedPrecision c z := by
      rw [← hfr]; exact (hP r).symm
    refine e1.trans ?_
    unfold BlockTree.composedPrecision
    congr 1
    have hfun : (fun s : ℕ => varpi r.1.1.1.1 z (s - 1) ^ 2 * blockFrac (S.L ^ S.d) r.1.1.1.1 s ^ 2 / c (s - 1)) =
        fun s => varpi (m' + 1) z (s - 1) ^ 2 * blockFrac (S.L ^ S.d) (m' + 1) s ^ 2 / c (s - 1) := by
      have : r.1.1.1.1 = m' + 1 := hb01
      rw [this]
    calc ∑ i ∈ Finset.range ((B r.1).n + 1), varpi r.1.1.1.1 z ((B r.1).scale i - 1) ^ 2 *
          blockFrac (S.L ^ S.d) r.1.1.1.1 ((B r.1).scale i) ^ 2 / c ((B r.1).scale i - 1)
        = ∑ i : Fin ((B r.1).n + 1), varpi r.1.1.1.1 z ((B r.1).scale i - 1) ^ 2 *
          blockFrac (S.L ^ S.d) r.1.1.1.1 ((B r.1).scale i) ^ 2 / c ((B r.1).scale i - 1) :=
          Finset.sum_range _
      _ = ∑ j : {i : {b : Σ s, BlockAt S n M K s // nd b} //
            pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] i = b0},
            varpi r.1.1.1.1 z (j.1.1.1 - 1) ^ 2 * blockFrac (S.L ^ S.d) r.1.1.1.1 j.1.1.1 ^ 2 / c (j.1.1.1 - 1) := by
          refine (Fintype.sum_equiv (e r.1) _ _ fun j => ?_).symm
          simp only [hsc]
      _ = ∑ b ∈ Finset.univ.filter (fun b : {b : Σ s, BlockAt S n M K s // nd b} =>
            pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] b = b0),
            varpi (m' + 1) z (b.1.1 - 1) ^ 2 * blockFrac (S.L ^ S.d) (m' + 1) b.1.1 ^ 2 / c (b.1.1 - 1) := by
          rw [← Finset.sum_subtype (Finset.univ.filter (fun b : {b : Σ s, BlockAt S n M K s // nd b} =>
            pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] b = b0)) (by simp)
            (fun b => varpi r.1.1.1.1 z (b.1.1 - 1) ^ 2 * blockFrac (S.L ^ S.d) r.1.1.1.1 b.1.1 ^ 2 / c (b.1.1 - 1))]
          exact Finset.sum_congr rfl fun b _ => congrFun hfun b.1.1


open Classical in
/-- **The exact node integral of the window, the datum and the composed precision explicit.** -/
theorem window_node_integral_exact {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
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
          OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))

    (hMS : M = S.M) (G : S.Good)
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    (h3 : 8 ≤ S.L * S.lateR (m' + 1)) (hW : H.RipeWindow (m' + 1) Z) (hk1def : S.k1 (m' + 1) = k1)
    (hZ0box : ∀ s : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)),
      torusCast (congrArg (· * n (m' + 1)) hMS)
        (blockMap (S.L ^ (m' + 1)) (M * n (m' + 1)) s) ∈ H.Zzero (m' + 1) Z →
        jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top H.F.hnn hm).symm s) ∈ Z0)
    (βk : ℝ) (hβ : 0 < βk) :
    ∃ (D : Background.BgData (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) N)
      (ψk : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) → Fin N → ℂ)
      (Zb : Finset (Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1)))))
      (aN : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) → ℝ),
      D.IsReal ∧
      (∀ zb, zb ∈ Zb ↔ ∃ y : BlockAt S n M K (m' + 1), y ∈ V2 ∧ P2 y ∧
        y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧
          zb = torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y) ∧
      (∀ zb ∈ Zb, 0 < βk * aN zb) ∧
      (∀ y : BlockAt S n M K (m' + 1), y ∈ V2 → P2 y →
        y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' → ∀ i,
          ψk (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y) i = ((ft v0 y i : ℝ) : ℂ)) ∧
      (∀ x ∈ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).Ω 1, (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x ≠ m' + 1 → ∀ i, D.Ψ x i =
        ((fld v0 ((windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x)
          (jBlock S.d S.L (M * n K) K ((windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x)
            (torusCast (fine_eq_top H.F.hnn hm).symm x)) i : ℝ) : ℂ)) ∧
      (∀ x ∈ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).Ω 1, (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x = m' + 1 → ∀ i, D.Ψ x i =
        ((ft v0 (jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top H.F.hnn hm).symm x)) i : ℝ) : ℂ)) ∧
      (∀ x i, D.h x i = 0) ∧ (∀ x, x ∉ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).Ω 1 → ∀ i, D.Ψ x i = 0) ∧
      (∀ y : BlockAt S n M K (m' + 1), y ∈ V2 → P2 y → y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' →
        ∀ b0 : {b : Σ s, BlockAt S n M K s // nd b}, b0.1 = ⟨m' + 1, y⟩ →
          βk * aN (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y) =
            (∑ b ∈ Finset.univ.filter (fun b : {b : Σ s, BlockAt S n M K s // nd b} =>
                pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] b = b0),
              varpi (m' + 1) z (b.1.1 - 1) ^ 2 * blockFrac (S.L ^ S.d) (m' + 1) b.1.1 ^ 2 / c (b.1.1 - 1))⁻¹) ∧
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
        ENNReal.ofReal (ActionConv.constNat N βk aN Zb *
          Real.exp (-(ActionConv.gaussNat (windowOfHistory H Z geo hm hW |>.windowGenSet
            (windowOfHistory_hyp (g := geo) hm hW)) (varpi (m' + 1) z) D.Ψ βk aN ψk Zb).re)) := by
  obtain ⟨D, ψk, Zb, aN, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    window_node_integral_exact_collar geo cs SD KD hk1 hm hq nd hnd hnd0 Z0 V2 G3 P2 hV2 hZ0g hG3 Nd hNd c z hc hz fld ft hfldn hfldb hftg hftz hftt pa hpa Fx hFxdef v0 hMS G h18 h3 hW hk1def hZ0box βk hβ (fun _ _ => 0) (fun _ _ _ => rfl)
  exact ⟨D, ψk, Zb, aN, h1, h2, h3, h4, h5, h6, h7, fun x hx i => by simpa using h8 x hx i, h9, h10⟩

end Exact

end Balaban.LargeField
