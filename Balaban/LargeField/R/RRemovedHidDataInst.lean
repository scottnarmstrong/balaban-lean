/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidDataBg
public import Balaban.LargeField.R.RRemovedHidLeafWindow

/-!
# The exact node integral of the window of the history, data discharged (W944)

`notes/phase1/LF4R-PLAN.md` §8.5.  `window_node_integral_eq_of_history`: `window_node_integral_eq` for
`W = windowOfHistory H Z geo hm hW` with the hypotheses `hWfull`, `hWZ`, `hWZk1` (definitional),
`hZk1` (`locFine_subset_fineZzero`, from `hZ0box`: `Z₀` contains the fine set of `H.Zzero`, and the Setting hypotheses
`h18`, `h3`), `hZb` (`Zb` the image of the top Gaussian blocks of `V2 ∧ P2`), `hψk` (`ψ_k` the output `ft`) and `hΨ`
(`Ψ` the multiscale field `fld` from `exists_bgData_of_field`) discharged.  The conclusion carries the real datum `D`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section Facts

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' : ℕ}

/-- The sites of a top Gaussian block outside `Z_{k₁}` are in `Ω₁` of the window generating set, with the layer index
of `full`. -/
theorem window_site_facts (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L)
    (hR : ∀ j, 1 ≤ j → j < m' + 1 → S.Rb ≤ R j) {Z : H.Comp (m' + 1)} {k1 : ℕ} (hk1p : 1 ≤ k1)
    (hk1 : k1 ≤ m') {ϱ : ℝ} (W : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ) (hWh : W.Hyp)
    (hWfull : ∀ j, W.full.Ω j = (H.locGen Z M hmK hL hR).Ω j)
    (hWZ : W.Z = H.locFineFin Z (m' + 1)) (hWZk1 : W.Zk1 = H.locFineFin Z k1)
    {y : BlockAt S n M K (m' + 1)} (hy : y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m')
    {s : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hs : jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hmK).symm s) = y)
    (hyk1 : s ∉ H.locFine Z M k1) :
    s ∈ (W.windowGenSet hWh).Ω 1 ∧
      (W.windowGenSet hWh).layerIndex s = (H.locGen Z M hmK hL hR).layerIndex s := by
  obtain ⟨hZ, -⟩ := gauss_top_site hnn hmK hL hR hy hs
  have hx : s ∈ W.Z \ W.Zk1 := Finset.mem_sdiff.mpr
    ⟨by rw [hWZ, RegionHistory.mem_locFineFin]; exact hZ,
     by rw [hWZk1, RegionHistory.mem_locFineFin]; exact hyk1⟩
  refine ⟨?_, (windowGenSet_layerIndex_eq_full W hWh hx).trans (layerIndex_congr W.full _ hWfull s)⟩
  rw [windowGenSet_mem_iff_full W hWh hx (Finset.mem_sdiff.mp hx).1 1, hWfull]
  exact (H.locGen Z M hmK hL hR).Ω_antitone le_rfl hk1p (by omega)
    (mem_locGen_of_not_locFine hmK hL hR hk1p hk1 hyk1)

end Facts

section Inst

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
open Classical in
theorem window_node_integral_eq_of_history {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
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
  subst hMS
  have hnn := H.F.hnn
  have hL : 2 ≤ S.L := H.F.ok.two_le_L
  have hR : ∀ j, 1 ≤ j → j < m' + 1 → S.Rb ≤ R j := fun j _ _ => geo.hRlow j
  have hk1p : 1 ≤ k1 := hk1def ▸ hW.k1_pos hm
  have hWh := windowOfHistory_hyp (g := geo) hm hW
  have hZk1 : ∀ x : Torus S.d (S.M * n (m' + 1) * S.L ^ (m' + 1)), x ∈ H.locFine Z S.M k1 →
      jBlock S.d S.L (S.M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hm).symm x) ∈ Z0 := by
    intro x hx
    have := locFine_subset_fineZzero G h18 h3 hm hW (x := x) (hk1def ▸ hx)
    exact hZ0box x this
  let zbk : BlockAt S n S.M K (m' + 1) → Torus S.d (S.M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) :=
    fun y => torusCast (blk_eq_top hnn hm (le_refl (m' + 1))).symm y
  let Zb : Finset (Torus S.d (S.M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1)))) :=
    (Finset.univ.filter fun y : BlockAt S n S.M K (m' + 1) =>
      y ∈ V2 ∧ P2 y ∧ y ∈ gaussBlocks (H.localHistory S.M K (m' + 1) Z) m').image zbk
  have hZb : ∀ zb, zb ∈ Zb ↔ ∃ y : BlockAt S n S.M K (m' + 1), y ∈ V2 ∧ P2 y ∧
      y ∈ gaussBlocks (H.localHistory S.M K (m' + 1) Z) m' ∧ zb = zbk y := by
    intro zb
    simp only [Zb, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy.1, hy.2.1, hy.2.2, rfl⟩
    · rintro ⟨y, h1, h2, h3, rfl⟩; exact ⟨y, ⟨h1, h2, h3⟩, rfl⟩
  let ψk : Torus S.d (S.M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) → Fin N → ℂ := fun zb =>
    if h : ∃ y : BlockAt S n S.M K (m' + 1), y ∈ V2 ∧ P2 y ∧
        y ∈ gaussBlocks (H.localHistory S.M K (m' + 1) Z) m' ∧ zbk y = zb then
      fun i => ((ft v0 (Classical.choose h) i : ℝ) : ℂ) else 0
  have hψk : ∀ y : BlockAt S n S.M K (m' + 1), y ∈ V2 → P2 y →
      y ∈ gaussBlocks (H.localHistory S.M K (m' + 1) Z) m' → ∀ i,
        ψk (zbk y) i = ((ft v0 y i : ℝ) : ℂ) := by
    intro y hyV hyP hyg i
    have h : ∃ y' : BlockAt S n S.M K (m' + 1), y' ∈ V2 ∧ P2 y' ∧
        y' ∈ gaussBlocks (H.localHistory S.M K (m' + 1) Z) m' ∧ zbk y' = zbk y := ⟨y, hyV, hyP, hyg, rfl⟩
    have := torusCast_injective _ (Classical.choose_spec h).2.2.2
    simp only [ψk, h, dite_true, this]
  obtain ⟨D, hDreal, hD⟩ := exists_bgData_of_field hnn hm (windowOfHistory H Z geo hm hW |>.windowGenSet hWh)
    (fun s y => fld v0 s y)
  have hΨ : ∀ y : BlockAt S n S.M K (m' + 1), y ∈ V2 → P2 y →
      y ∈ gaussBlocks (H.localHistory S.M K (m' + 1) Z) m' →
      ∀ s ∈ fib S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1) (zbk y), ∀ i,
        D.Ψ s i = ((fld v0 ((H.locGen Z S.M hm H.F.ok.two_le_L (fun j _ _ => geo.hRlow j)).layerIndex s)
          (jBlock S.d S.L (S.M * n K) K
            ((H.locGen Z S.M hm H.F.ok.two_le_L (fun j _ _ => geo.hRlow j)).layerIndex s)
            (torusCast (fine_eq_top H.F.hnn hm).symm s)) i : ℝ) : ℂ) := by
    intro y hyV hyP hyg s hs i
    have hsY := (mem_fib_cast hnn hm (le_refl (m' + 1)) y s).mp hs
    have hyk1 : s ∉ H.locFine Z S.M k1 := fun hxl => by
      have := hZk1 s hxl
      rw [hsY] at this
      exact hV2 y hyV hyP this
    obtain ⟨hΩ, hlay⟩ := window_site_facts hnn hm hL hR hk1p hk1 (windowOfHistory H Z geo hm hW) hWh
      (windowOfHistory_full_Ω H Z geo hm hW) (windowOfHistory_Z H Z geo hm hW)
      (by rw [windowOfHistory_Zk1, hk1def]) hyg hsY hyk1
    have := hD s hΩ i
    rw [hlay] at this
    exact this
  obtain ⟨aN, hpos, hint⟩ := window_node_integral_eq geo cs SD KD hk1 hm hq nd hnd hnd0 Z0 V2 G3 P2
    hV2 hZ0g hG3 Nd hNd c z hc hz fld ft hfldn hfldb hftg hftz hftt pa hpa Fx hFxdef v0 hk1p hZk1
    (windowOfHistory H Z geo hm hW) hWh (windowOfHistory_full_Ω H Z geo hm hW)
    (windowOfHistory_Z H Z geo hm hW) (by rw [windowOfHistory_Zk1, hk1def]) βk hβ D.Ψ ψk Zb hZb hψk hΨ
  exact ⟨D, ψk, Zb, aN, hDreal, hZb, hpos, hint⟩

end Inst

end Balaban.LargeField
