/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidLeafFinal
public import Balaban.LargeField.R.RRemovedHidGaussEq
public import Balaban.LargeField.R.WindowOfHistory

/-!
# The exact node integral of the window is `const^♮ e^{-𝒢^♮}` (W942)

`notes/phase1/LF4R-PLAN.md` §8.5.  `window_node_integral_eq`: the exact integral over the node coordinates of the
regrouping (`lintegral_gauss_coords_eq`) equals `ofReal (constNat N β_k aN Zb · e^{-Re 𝒢^♮})` (`CancelIdentity.lean`)
for the window generating set `G = W.windowGenSet` of the history, the composed weights `aN z = (precision of the root
of z) / β_k` and the multiscale data `Ψ` of the window, given the data relations `hΨ` (`Ψ` is the field `fld` on the
layers of the sites of the fixed top blocks) and `hψk` (`ψ_k` is the output `ft`), the geometric hypothesis `hZk1`
(`Z_{k₁} ⊆ Z₀`) and the identification `hWfull`, `hWZ`, `hWZk1` of the window pieces with the localization of `Z`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section Window

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **The exact node integral of the window.** -/
theorem window_node_integral_eq {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
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
    (hk1p : 1 ≤ k1)
    (hZk1 : ∀ x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)), x ∈ H.locFine Z M k1 →
      jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top H.F.hnn hm).symm x) ∈ Z0)
    {ϱ : ℝ} (W : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ) (hWh : W.Hyp)
    (hWfull : ∀ j, W.full.Ω j = (H.locGen Z M hm H.F.ok.two_le_L (fun j _ _ => geo.hRlow j)).Ω j)
    (hWZ : W.Z = H.locFineFin Z (m' + 1)) (hWZk1 : W.Zk1 = H.locFineFin Z k1)
    (βk : ℝ) (hβ : 0 < βk)
    (Ψ : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)) → Fin N → ℂ)
    (ψk : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) → Fin N → ℂ)
    (Zb : Finset (Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1)))))
    (hZb : ∀ zb, zb ∈ Zb ↔ ∃ y : BlockAt S n M K (m' + 1), y ∈ V2 ∧ P2 y ∧
      y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧
        zb = torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y)
    (hψk : ∀ y : BlockAt S n M K (m' + 1), y ∈ V2 → P2 y →
      y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' → ∀ i,
        ψk (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y) i = ((ft v0 y i : ℝ) : ℂ))
    (hΨ : ∀ y : BlockAt S n M K (m' + 1), y ∈ V2 → P2 y →
      y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' →
      ∀ s ∈ fib S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y), ∀ i,
        Ψ s i = ((fld v0 ((H.locGen Z M hm H.F.ok.two_le_L (fun j _ _ => geo.hRlow j)).layerIndex s)
          (jBlock S.d S.L (M * n K) K ((H.locGen Z M hm H.F.ok.two_le_L (fun j _ _ => geo.hRlow j)).layerIndex s)
            (torusCast (fine_eq_top H.F.hnn hm).symm s)) i : ℝ) : ℂ)) :
    ∃ aN : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) → ℝ,
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
          Real.exp (-(ActionConv.gaussNat (W.windowGenSet hWh) (varpi (m' + 1) z) Ψ βk aN ψk Zb).re)) := by
  classical
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
  refine ⟨aN, fun zb hzb => ?_, hE.trans (by convert hprod)⟩
  obtain ⟨r, rfl⟩ := (hZb' zb).mp hzb
  rw [← hP r]
  exact hPpos r.1 r.2

end Window

section Instance

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) {k : ℕ} (Z : H.Comp k) {M : ℕ} [NeZero M] [NeZero S.L]
  (g : Geo S n R M) (hkK : k ≤ K) (hW : H.RipeWindow k Z)

/-- The hypotheses `hWfull`, `hWZ`, `hWZk1` of `window_node_integral_eq` hold for `windowOfHistory` (definitional). -/
theorem windowOfHistory_full_Ω (j : ℕ) :
    (windowOfHistory H Z g hkK hW).full.Ω j =
      (H.locGen Z M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j)).Ω j := rfl

theorem windowOfHistory_Z : (windowOfHistory H Z g hkK hW).Z = H.locFineFin Z k := rfl

theorem windowOfHistory_Zk1 :
    (windowOfHistory H Z g hkK hW).Zk1 = H.locFineFin Z (S.k1 k) := rfl

end Instance


end Balaban.LargeField
