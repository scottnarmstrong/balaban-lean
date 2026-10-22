/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BPrimeCubeBound

/-!
# The fields of the residual of `R` on the region of the P3 premises

On the region of `bPrime_pairs_aggregate_adm` (data within `τ` of real data of `Ψ̃(genWC Y; δ)`,
fields within `K₂' C₃ (δ + 5τ)` of the approximate field), the fields read by the roots are bounded
and the composed fields are near the unit sphere:

* `dot_near_of_xiDom`: on `Ξ^c_j(G; 1, ε)`, `|Ψ·Ψ - 1| ≤ 1/2` and `|Ψ| ≤ 2` at the data sites;
* `SFCtx.vn_liftWC_le`, `SFCtx.dot_liftWC_near`: the lift of data near a real datum;
* `SFCtx.vn_phiBarAt_le`: `|φ̄| ≤ 2 + c_b + τ`, `c_b` the bound of `nearField_close_real`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.GsSpec

section Xi

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **A field of `Ξ^c_j(G; 1, ε)` is near the unit sphere at the data sites**: `|Ψ·Ψ - 1| ≤ 1/2`
and `|Ψ| ≤ 2` (it is `Ψ_r + Ψ'` with `| |Ψ_r|² - 1 | < δ`, `|(Ψ_r + Ψ')² - Ψ_r²| < δ`,
`|Ψ'| < ε' + δ`, `δ ≤ ε' ≤ c₀ ≤ 1/16`). -/
theorem dot_near_of_xiDom {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν ε : ℝ}
    {j : ℕ} {Ψ h : Def6.Fld d L N₁ m₁ K N} (hX : Def6.XiDom G a ν j ε Ψ h)
    {x : Localization.CTorus d L N₁ m₁ K} (hx : x ∈ dataSites G) :
    ‖SmallField.dot (Ψ x) (Ψ x) - 1‖ ≤ 1 / 2 ∧ vn (Ψ x) ≤ 2 := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hΨ, -, hXi⟩ := hX
  obtain ⟨-, -, -, Dc, -, hC, hU, -⟩ := hXi
  obtain ⟨δ, ε', -, hδε, hεc, -, -, hDC⟩ := hU
  obtain ⟨Ψr, _, Ψ', _, hP, hD1, -⟩ := hDC
  have hval : ∀ i, Ψ x i = (Ψr x i : ℂ) + Ψ' x i := fun i => by
    rw [hΨ x i, ← hC.1 x hx i, hD1 x hx i]
  have hδ : δ ≤ 1 / 16 := hδε.trans (hεc.trans (bgC0_le d L N))
  have hε' : ε' ≤ 1 / 16 := hεc.trans (bgC0_le d L N)
  have he := hP.c2b x hx
  have hr2 := hP.r2 x hx
  have hc2a := hP.c2a x hx
  have hvec : Ψ x = (fun i => (Ψr x i : ℂ)) + Ψ' x := by
    funext i; rw [hval i]; rfl
  constructor
  · have e : SmallField.dot (Ψ x) (Ψ x) - 1 =
        (∑ i, ((Ψr x i : ℂ) + Ψ' x i) * ((Ψr x i : ℂ) + Ψ' x i) -
          ∑ i, (Ψr x i : ℂ) * (Ψr x i : ℂ)) + ((∑ i, Ψr x i ^ 2 - 1 : ℝ) : ℂ) := by
      unfold SmallField.dot
      simp only [hval]
      push_cast
      simp only [sq]
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    have := (abs_lt.1 hr2)
    have h2 : |∑ i, Ψr x i ^ 2 - 1| ≤ δ := le_of_lt hr2
    linarith
  · rw [hvec]
    refine (vn_add _ _).trans ?_
    rw [vn_ofReal]
    have hsum : ∑ i, Ψr x i ^ 2 ≤ (3 / 2) ^ 2 := by
      have := (abs_lt.1 hr2).2
      nlinarith
    have hrn : rn (Ψr x) ≤ 3 / 2 := by
      unfold rn
      calc Real.sqrt (∑ i, Ψr x i ^ 2) ≤ Real.sqrt ((3 / 2) ^ 2) := Real.sqrt_le_sqrt hsum
        _ = 3 / 2 := Real.sqrt_sq (by norm_num)
    linarith

end Xi

/-- The bound `c_b` of `nearField_close_real`: `|φ - φ_r| ≤ c_b` for the fields near the
approximate field. -/
noncomputable def nearCb (d L N : ℕ) [NeZero L] (BG κ δ τ : ℝ) : ℝ :=
  (N : ℝ) * (2 * (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * (δ + 5 * τ)))) +
    (δ + 5 * τ) + bgK1 d L N * (δ + 5 * τ)

namespace Def7.SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (Y : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N))

/-- **The lift of data near a real datum** is bounded by `2 + τ` and near the unit sphere at the
data sites (`δ ≤ 1/8`, `τ ≤ 1/16`). -/
theorem lift_near {ν δ τ : ℝ} (hδ : δ ≤ 1 / 8) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 16)
    {u : BlockAt S n M K k → Fin N → ℂ} (hu : C.RDataNear hv Y ν δ τ u)
    {x : Localization.CTorus S.d S.L C.N₁ m₁ k} (hx : x ∈ dataSites (C.genWC Y)) :
    vn (C.liftWC Y hv u x) ≤ 2 + τ ∧
      ‖SmallField.dot (C.liftWC Y hv u x) (C.liftWC Y hv u x) - 1‖ ≤ 1 / 2 := by
  obtain ⟨Ψ₀, hP, hD⟩ := hu
  set a : Fin N → ℂ := fun i => (Ψ₀ x i : ℂ) with ha
  have he : vn (C.liftWC Y hv u x - a) < τ := hD x hx
  have hr2 := hP.r2 x hx
  have hsum : ∑ i, Ψ₀ x i ^ 2 ≤ (3 / 2) ^ 2 := by
    have := (abs_lt.1 hr2).2
    nlinarith
  have hva : vn a ≤ 3 / 2 := by
    rw [ha, vn_ofReal]
    unfold rn
    calc Real.sqrt (∑ i, Ψ₀ x i ^ 2) ≤ Real.sqrt ((3 / 2) ^ 2) := Real.sqrt_le_sqrt hsum
      _ = 3 / 2 := Real.sqrt_sq (by norm_num)
  have hvl : vn (C.liftWC Y hv u x) ≤ 3 / 2 + τ := by
    have h := vn_add (C.liftWC Y hv u x - a) a
    rw [sub_add_cancel] at h
    linarith
  refine ⟨by linarith, ?_⟩
  have e : SmallField.dot (C.liftWC Y hv u x) (C.liftWC Y hv u x) - 1 =
      SmallField.dot (C.liftWC Y hv u x - a) (C.liftWC Y hv u x + a) +
        ((∑ i, Ψ₀ x i ^ 2 - 1 : ℝ) : ℂ) := by
    have h1 := RegionalArith.dot_sub_dot (C.liftWC Y hv u x) a
    have h2 : SmallField.dot a a = ((∑ i, Ψ₀ x i ^ 2 : ℝ) : ℂ) := by
      unfold SmallField.dot
      rw [ha]
      push_cast
      simp only [sq]
    rw [← h1, h2]
    push_cast
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h3 : ‖SmallField.dot (C.liftWC Y hv u x - a) (C.liftWC Y hv u x + a)‖ ≤ τ * (4 + τ) := by
    refine (norm_dot_le_vn _ _).trans ?_
    have h4 : vn (C.liftWC Y hv u x + a) ≤ 4 + τ := (vn_add _ _).trans (by linarith)
    exact mul_le_mul he.le h4 (vn_nonneg _) hτ0
  have h5 : |∑ i, Ψ₀ x i ^ 2 - 1| ≤ δ := le_of_lt hr2
  nlinarith

/-- **The background field `φ̄` on the region is bounded**: `|φ̄| ≤ 2 + c_b + τ` at a field near the
approximate field of data near a real datum. -/
theorem vn_phiBarAt_le {a₁ ν c BG κ : ℝ} (hS : Dec2.DecSpecs S.d S.L (Dec2.selfKc S.d S.L)
      (Cchi S.d S.L) c BG)
    (SG : DGSetting (C.genWC Y) (compWeight S.L a₁) ν)
    (HB : BgHyp S.d S.L k (minSep S.L C.geo.M1) (compWeight S.L a₁) ν) (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁) {δ τ : ℝ} (hδ0 : 0 < δ) (hτ0 : 0 ≤ τ)
    (hδ73 : δ ≤ thm73C1 S.d S.L N) (hδc : δ + 5 * τ ≤ c7 S.d S.L N BG κ)
    (hδ8 : δ ≤ 1 / 8) (hτ16 : τ ≤ 1 / 16) {u : BlockAt S n M K k → Fin N → ℂ}
    (hu : C.RDataNear hv Y ν δ τ u) {φ : (C.genWC Y).Ω 1 × Fin N → ℂ}
    (hφ : NearApprox (C.genWC Y) (compWeight S.L a₁) ν (C.dataWC Y hv u)
      (cK2' S.d S.L N (famConst S.d S.L BG κ) * (lemma53Const S.d S.L * (δ + 5 * τ))) φ)
    (z : BgT C.geo k) :
    vn (C.phiBarAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) z) ≤
      2 + nearCb S.d S.L N BG κ δ τ + τ := by
  classical
  have hu' := hu
  obtain ⟨Ψ₀, hP, hD⟩ := hu'
  have hDΨ : ∀ x ∈ dataSites (C.genWC Y),
      vn (fun i => (C.dataWC Y hv u).Ψ x i - (Ψ₀ x i : ℂ)) ≤ τ := fun x hx => by
    rw [C.dataWC_Ψ]; exact (hD x hx).le
  obtain ⟨hunit, hclose⟩ := nearField_close_real hS (Dec2.coverBase_self SG) HB hκ hM hδ0 hτ0
    hδ73 hδc hP (fun x hx i => C.dataWC_h Y hv u hx i) hDΨ hφ
  have hcb0 : 0 ≤ nearCb S.d S.L N BG κ δ τ := by
    have := (hclose 0)
    unfold nearCb
    linarith [vn_nonneg (svec (C.genWC Y) (φ - bgFieldC (C.genWC Y) (compWeight S.L a₁) ν
      (bgC0 S.d S.L N) (SmallField.realData (C.genWC Y) Ψ₀ (fun i => hv i) hP.layerConst)) 0)]
  have e : C.phiBarAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) z =
      fun i => barField (C.genWC Y) (C.liftWC Y hv u) φ
        (GsSpec.torusCast z : Localization.CTorus S.d S.L C.N₁ m₁ k) i :=
    funext fun i => C.phiBarAt_cast Y hv u φ z i
  rw [e]
  set x : Localization.CTorus S.d S.L C.N₁ m₁ k := GsSpec.torusCast z with hxdef
  by_cases hx : x ∈ (C.genWC Y).Ω 1
  · set φr := bgFieldC (C.genWC Y) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
      (SmallField.realData (C.genWC Y) Ψ₀ (fun i => hv i) hP.layerConst) with hφr
    have h1 : (fun i => barField (C.genWC Y) (C.liftWC Y hv u) φ x i) =
        svec (C.genWC Y) (φ - φr) x + svec (C.genWC Y) φr x := by
      funext i
      simp [barField, svec, zeroExt, hx]
    have h2 : vn (svec (C.genWC Y) φr x) = 1 := by
      have hsq : vn (svec (C.genWC Y) φr x) ^ 2 = 1 := by
        rw [vn_sq, ← (hunit ⟨x, hx⟩).2]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [svec, zeroExt, hx]
      nlinarith [vn_nonneg (svec (C.genWC Y) φr x)]
    rw [h1]
    refine (vn_add _ _).trans ?_
    have h3 := hclose x
    unfold nearCb
    linarith
  · have h1 : (fun i => barField (C.genWC Y) (C.liftWC Y hv u) φ x i) = C.liftWC Y hv u x := by
      funext i
      simp [barField, hx]
    rw [h1]
    by_cases hxd : x ∈ dataSites (C.genWC Y)
    · have := (C.lift_near Y hv hδ8 hτ0 hτ16 hu hxd).1
      linarith
    · have h0 : C.liftWC Y hv u x = 0 := by
        rw [← C.dataWC_Ψ]
        exact (C.dataWC Y hv u).Ψ_zero x hxd
      rw [h0, vn_zero]
      linarith

/-- The cube of `𝕋_k` of a site of the level-`k` torus is its block of side `L^k (c M₁)`. -/
theorem blockMap_eq_tCubeOfBg (x : BgT C.geo k) :
    blockMap (S.L ^ k * (C.geo.c * C.geo.M1)) (n k) x = C.tCubeOfBg x := by
  funext μ
  apply ZMod.val_injective
  have hside : C.geo.M1 * (C.geo.c * n k) * S.L ^ k = S.L ^ k * (C.geo.c * C.geo.M1) * n k := by
    ring
  rw [blockMap_apply, blockCoord_val hside, tCubeOfBg_val]
  congr 2
  exact C.geo.hM.symm

/-- **The sites of the cubes of `W` lie in `Ω₁` of `𝔹_k(W)`** (in its top layer). -/
theorem mem_genW_Ω_one (hk1 : 1 ≤ k) {x : BgT C.geo k} (hx : C.tCubeOfBg x ∈ W2 R Y) :
    x ∈ (C.genW Y).Ω 1 := by
  have hm : C.geo.c * n k * S.L ^ (k - k) = C.geo.c * n k := by simp
  have hU := isCubeUnion_cubePre (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L) (q := k)
    le_rfl hm (W2 R Y)
  have hk : x ∈ (C.genW Y).Ω k := by
    show x ∈ (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L) (c := C.geo.c) (n := n k)
      (le_refl k) (W2 R Y)).Ω k
    unfold genSF
    rw [minimalGenSet_Ω, minLayer_self, hU.cubeInterior_eq, mem_cubePre, C.blockMap_eq_tCubeOfBg]
    exact hx
  exact (C.genW Y).Ω_antitone le_rfl hk1 (by omega) hk

/-- **The sites of `Y^≈` lie in `Ω₁` of the transported `𝔹_k(W)`.** -/
theorem mem_genWC_Ω_one_of_thick (hk1 : 1 ≤ k) {s : Localization.CTorus S.d S.L C.N₁ m₁ k}
    (hs : s ∈ C.sset (thickY R Y)) : s ∈ (C.genWC Y).Ω 1 := by
  rw [mem_genWC_Ω]
  refine C.mem_genW_Ω_one Y hk1 ?_
  exact subset_nbhd _ _ hs

theorem mem_genWC_Ω_one_of_sset (hk1 : 1 ≤ k) {s : Localization.CTorus S.d S.L C.N₁ m₁ k}
    (hs : s ∈ C.sset Y) : s ∈ (C.genWC Y).Ω 1 :=
  C.mem_genWC_Ω_one_of_thick Y hk1 (subset_nbhd _ Y hs)

/-- The data on the `k`-block of a site of `Ω₁` is the lift at the site. -/
theorem psiLevelKOf_blkMap_eq_lift {x : BgT C.geo k} (hx : x ∈ (C.genW Y).Ω 1)
    (u : BlockAt S n M K k → Fin N → ℂ) :
    C.psiLevelKOf u k (blkMap S.d S.L (C.geo.M1 * (C.geo.c * n k)) k k x) =
      C.liftWC Y hv u (GsSpec.torusCast x) := by
  classical
  have hxW : x ∈ dataSites (C.genW Y) := (mem_dataSites _).2 (Or.inl hx)
  funext i
  unfold liftWC
  rw [castTField_apply, C.torusCast_torusCast_bg]
  unfold liftSingle BgData.clip
  simp only [hxW, ↓reduceIte]
  unfold psiLevelKOf singleScaleOf blockLift liftDataC
  simp only [le_refl, ↓reduceDIte]
  rfl

theorem mem_bgSet_iff (A : Set (Torus S.d (n k))) (x : BgT C.geo k) :
    x ∈ C.bgSet A ↔ C.tCubeOfBg x ∈ A := by
  classical
  simp [bgSet, tCubeOfBg]

/-- **The data on the blocks of `Y` are bounded** by `2 + τ` for data near a real datum. -/
theorem vn_psiLevelKOf_le (hk1 : 1 ≤ k) {ν δ τ : ℝ} (hδ : δ ≤ 1 / 8) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ 1 / 16) {u : BlockAt S n M K k → Fin N → ℂ} (hu : C.RDataNear hv Y ν δ τ u) :
    ∀ m ∈ Finset.Icc 1 k, ∀ y ∈ tBlocks S.d S.L (C.geo.M1 * (C.geo.c * n k)) k m
      (lam (levelGen (ϱ := (1 : ℝ)) k) m ∩ C.bgSet Y), vn (C.psiLevelKOf u m y) ≤ 2 + τ := by
  intro m hm y hy
  by_cases hmk : m = k
  · subst hmk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have hxY : C.tCubeOfBg x ∈ Y := (C.mem_bgSet_iff Y x).1 (Finset.mem_inter.1 hx).2
    have hxΩ := C.mem_genW_Ω_one Y hk1 (subset_nbhd _ _ (subset_nbhd _ _ hxY))
    rw [C.psiLevelKOf_blkMap_eq_lift Y hv hxΩ u]
    have hxC : (GsSpec.torusCast x : Localization.CTorus S.d S.L C.N₁ m₁ m) ∈
        dataSites (C.genWC Y) := by
      refine (mem_dataSites _).2 (Or.inl ?_)
      rw [mem_genWC_Ω, C.sfToBg_torusCast]
      exact hxΩ
    exact (C.lift_near Y hv hδ hτ0 hτ hu hxC).1
  · have h0 : C.psiLevelKOf u m y = 0 := by
      unfold psiLevelKOf singleScaleOf
      simp [hmk]
    rw [h0, vn_zero]
    linarith

/-- **The composed field of the top level is the lift** at the sites of `Ω₁` (positive weights). -/
theorem psiJAt_top_eq (hL : 2 ≤ S.L) {a₁ : ℝ} (ha₁ : 0 < a₁) (hw : C.weights = compWeight S.L a₁)
    (u : BlockAt S n M K k → Fin N → ℂ) (φ : (C.genWC Y).Ω 1 × Fin N → ℂ)
    {s : Localization.CTorus S.d S.L C.N₁ m₁ k} (hs : s ∈ (C.genWC Y).Ω 1) :
    C.psiJAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) k s = C.liftWC Y hv u s := by
  funext i
  rw [C.psiJAt_cast Y u hv φ le_rfl s i]
  change composeField (C.genWC Y) (C.genWC Y) C.weights φ (C.liftWC Y hv u) s i = _
  rw [composeField_of_mem _ _ _ hs]
  have hl := ((C.genWC Y).layerIndex_spec hs).1
  have hpos : C.weights ((C.genWC Y).layerIndex s) ≠ 0 := by
    rw [hw]; exact (Background.compWeight_pos hL ha₁ hl).ne'
  have hLp : ((S.L : ℝ) ^ (C.genWC Y).layerIndex s) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < S.L := by exact_mod_cast (show 0 < S.L by omega)
    positivity
  rw [div_self hpos, div_self hLp, one_mul]
  push_cast
  ring

/-- **The composed field of the top level near the unit sphere** (data near a real datum). -/
theorem psiJAt_top_near (hk1 : 1 ≤ k) (hL : 2 ≤ S.L) {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hw : C.weights = compWeight S.L a₁) {ν δ τ : ℝ} (hδ : δ ≤ 1 / 8) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ 1 / 16) {u : BlockAt S n M K k → Fin N → ℂ} (hu : C.RDataNear hv Y ν δ τ u)
    (φ : (C.genWC Y).Ω 1 × Fin N → ℂ) {s : Localization.CTorus S.d S.L C.N₁ m₁ k}
    (hs : s ∈ C.sset (thickY R Y)) :
    vn (C.psiJAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) k s) ≤ 2 + τ ∧
      ‖SmallField.dot (C.psiJAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) k s)
        (C.psiJAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) k s) - 1‖ ≤ 1 / 2 := by
  have hsΩ := C.mem_genWC_Ω_one_of_thick Y hk1 hs
  rw [C.psiJAt_top_eq Y hv hL ha₁ hw u φ hsΩ]
  exact C.lift_near Y hv hδ hτ0 hτ hu ((mem_dataSites _).2 (Or.inl hsΩ))

/-- **The `π'_j`-cube of a site, aligned in its cell, is a polymer of `𝒟_j`.** -/
theorem isPolyDom_cellCube (j : ℕ) (s : Localization.CTorus S.d S.L C.N₁ m₁ k) :
    Def6.IsPolyDom C.m₀ j (Localization.box (cbase (S.L * cellSide S.L C.m₀ m₁ j) s)
      (S.L * cellSide S.L C.m₀ m₁ j)) := by
  have hpA : Localization.Aligned (cellSide S.L C.m₀ m₁ j)
      (cbase (S.L * cellSide S.L C.m₀ m₁ j) s) := fun μ =>
    Nat.mod_eq_zero_of_dvd (dvd_trans (dvd_mul_left _ _)
      (Nat.dvd_of_mod_eq_zero (aligned_cbase s μ)))
  have h := Fluctuation.isDj_box (m₀ := C.m₀) hpA
  exact ⟨h.1, ⟨_, Fluctuation.chosenOne_box _ hpA⟩, h.2.2⟩

/-- The `π'_j`-cube of a site of `Y^≈` (`j < k`) lies in `Y^≈`. -/
theorem cellCube_subset (hMm : C.geo.c * C.geo.M1 = S.L ^ (C.m₀ + m₁)) (hN : S.L ^ C.m₀ ∣ C.N₁)
    {j : ℕ} (hj : j < k) (A : Set (Torus S.d (n k)))
    {s : Localization.CTorus S.d S.L C.N₁ m₁ k} (hs : s ∈ C.sset A) :
    Localization.box (cbase (S.L * cellSide S.L C.m₀ m₁ j) s) (S.L * cellSide S.L C.m₀ m₁ j) ⊆
      C.sset A := by
  intro y hy
  have hLc : S.L * cellSide S.L C.m₀ m₁ j = cellSide S.L C.m₀ m₁ (j + 1) := by
    unfold cellSide; rw [← pow_succ']; congr 1; ring
  have hdvd : S.L * cellSide S.L C.m₀ m₁ j ∣ (C.N₁ * S.L ^ m₁) * S.L ^ k := by
    rw [hLc]; exact cellSide_dvd hN (by omega)
  have hpos : 0 < S.L * cellSide S.L C.m₀ m₁ j :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) (cellSide_pos _ _ _)
  have h1 := (mem_box_cbase_iff hdvd hpos s y).1 hy
  have h2 : SameCell (cellSide S.L C.m₀ m₁ k) y s := h1.mono (by
    rw [hLc]; unfold cellSide; exact pow_dvd_pow _ (by omega))
  rw [C.cellSide_eq_blk hMm] at h2
  rw [mem_sset_iff_cube, (C.tCubeOfC_eq_iff y s).2 h2]
  exact hs

/-- **The composed field of a level `j < k` near the unit sphere** at the sites of `Y^≈`, for data
near a real datum and fields near the approximate field (by `sfTerm_nearCompose_xiDom` on the class
set of the `π'_j`-cube of the site). -/
theorem psiJAt_lt_near {P : Def6.Consts} {Dom : Def6v2.FieldDom S.d S.L C.N₁ m₁ k N ϱ}
    (hT : GsSpec.SFTermClausesStrong P Dom (C.sf.Tm C.N₁)) (hm0 : P.m₀ = C.m₀) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j < k) (hL : 3 ≤ S.L) (hN : S.L ^ C.m₀ ∣ C.N₁) (hlt : hatScale S.L m₁ ϱ < C.m₀)
    (hsep : ϱ ≤ minSep S.L (S.L ^ (m₁ + hatScale S.L m₁ ϱ)))
    (hMm : C.geo.c * C.geo.M1 = S.L ^ (C.m₀ + m₁)) (hm : m₁ + hatScale S.L m₁ ϱ + 3 ≤ C.m₀ + m₁)
    {a₁ ν c BG κ : ℝ} (hS : Dec2.DecSpecs S.d S.L (Dec2.selfKc S.d S.L) (Cchi S.d S.L) c BG)
    (SG : DGSetting (C.genWC Y) (compWeight S.L a₁) ν)
    (HB : BgHyp S.d S.L k (minSep S.L C.geo.M1) (compWeight S.L a₁) ν)
    (HBG : BgHyp S.d S.L k ϱ (compWeight S.L a₁) ν) (ha₁ : 0 < a₁) (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁) {δ τ : ℝ} (hδ0 : 0 < δ) (hτ0 : 0 ≤ τ)
    (hδ73 : δ ≤ thm73C1 S.d S.L N) (hδc : δ + 5 * τ ≤ c7 S.d S.L N BG κ)
    (hrad : decDomRad S.d S.L N BG κ δ τ ≤ bgC1 S.d S.L N) (hw : C.weights = compWeight S.L a₁)
    {u : BlockAt S n M K k → Fin N → ℂ} (hu : C.RDataNear hv Y ν δ τ u)
    {φ : (C.genWC Y).Ω 1 × Fin N → ℂ}
    (hφ : NearApprox (C.genWC Y) (compWeight S.L a₁) ν (C.dataWC Y hv u)
      (cK2' S.d S.L N (famConst S.d S.L BG κ) * (lemma53Const S.d S.L * (δ + 5 * τ))) φ)
    {s : Localization.CTorus S.d S.L C.N₁ m₁ k} (hs : s ∈ C.sset (thickY R Y)) :
    ‖SmallField.dot (C.psiJAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) j s)
        (C.psiJAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) j s) - 1‖ ≤ 1 / 2 ∧
      vn (C.psiJAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) j s) ≤ 2 := by
  obtain ⟨Ψ₀, hP, hD⟩ := hu
  set X := Localization.box (cbase (S.L * cellSide S.L C.m₀ m₁ j) s)
    (S.L * cellSide S.L C.m₀ m₁ j) with hXdef
  have hpoly := C.isPolyDom_cellCube j s
  have hpoly' : Def6.IsPolyDom P.m₀ j X := hm0 ▸ hpoly
  have hXT := C.cellCube_subset hMm hN hj (thickY R Y) hs
  have hspec := hT.gs_spec j hj1 hj.le X hpoly'
  have hHat : HatSpec C.m₀ j X ((C.sf.Tm C.N₁).gs j X) := hm0 ▸ hT.hat j hj1 hj.le X hpoly'
  have hDΨ : ∀ x ∈ dataSites (C.genWC Y),
      vn (fun i => (C.dataWC Y hv u).Ψ x i - (Ψ₀ x i : ℂ)) ≤ τ := fun x hx => by
    rw [C.dataWC_Ψ]; exact (hD x hx).le
  have hXi := C.sfTerm_nearCompose_xiDom Y hj1 hj hL hXT hpoly hN hspec.2 hHat hlt hsep hMm hm hS
    SG HB HBG ha₁ hκ hM hδ0 hτ0 hδ73 hδc hrad hP (D := C.dataWC Y hv u)
    (fun x hx i => C.dataWC_h Y hv u hx i) hDΨ hφ
  have hsX : s ∈ X := mem_box_cbase (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne S.L))
    (cellSide_pos _ _ _)) s
  have hsd : s ∈ dataSites ((C.sf.Tm C.N₁).gs j X) := (mem_dataSites _).2 (Or.inl (hspec.1 hsX))
  have hnear := dot_near_of_xiDom hXi hsd
  have e : (fun i => composeField (C.genWCj hj.le Y) (C.genWC Y) (compWeight S.L a₁) φ
      (C.dataWC Y hv u).Ψ s i) = C.psiJAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) j s := by
    funext i
    rw [C.psiJAt_cast Y u hv φ hj.le s i, hw, C.dataWC_Ψ]
    rfl
  rw [← e]
  exact hnear

theorem nearCb_nonneg {d L N : ℕ} [NeZero L] (hd : 0 < d) {BG : ℝ} (hBG : 0 ≤ BG) (κ : ℝ)
    {δ τ : ℝ} (hδ0 : 0 ≤ δ) (hτ0 : 0 ≤ τ) : 0 ≤ nearCb d L N BG κ δ τ := by
  have hfam : 0 ≤ famConst d L BG κ := by
    have := famConst_ge_one (L := L) hBG κ hd; linarith
  have hK2 := cK2'_nonneg (d := d) (L := L) (N := N) hfam
  have hC3 := lemma53Const_pos d L
  have hK1 := bgK1_ge_one d L N
  unfold nearCb
  have : 0 ≤ δ + 5 * τ := by linarith
  positivity

/-- The radius `δ + 5τ ≤ c₇` is at most `1/1024`. -/
theorem small_of_c7 {d L N : ℕ} [NeZero L] (hd : 0 < d) {BG κ δ τ : ℝ} (hBG : 0 ≤ BG)
    (hδ0 : 0 < δ) (hτ0 : 0 ≤ τ) (hδc : δ + 5 * τ ≤ c7 d L N BG κ) : δ + 5 * τ ≤ 1 / 1024 :=
  (approxDelta_le d L (bgC1_facts d L N hd
    (c7_facts (L := L) (N := N) hd hBG (by positivity) hδc).1).1).1

theorem mem_slitPlane_of_near {z : ℂ} (h : ‖z - 1‖ ≤ 1 / 2) : z ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  have h1 := (abs_le.1 (Complex.abs_re_le_norm (z - 1))).1
  rw [Complex.sub_re, Complex.one_re] at h1
  linarith

/-- **The root of a cube on the region of the P3 premises**: the slit-plane condition of its
analyticity and its bound `cubeBound` at `B = 2 + c_b + τ`. -/
theorem cubeRoot_region (hk1 : 1 ≤ k) (vc : Def7v2.CorrCoef S.d) (g : GIdx S n M K N → ℂ)
    (c : Torus S.d (n k)) {P : Def6.Consts} {Dom : Def6v2.FieldDom S.d S.L C.N₁ m₁ k N ϱ}
    (hT : GsSpec.SFTermClausesStrong P Dom (C.sf.Tm C.N₁)) (hm0 : P.m₀ = C.m₀) (hL : 3 ≤ S.L)
    (hN : S.L ^ C.m₀ ∣ C.N₁) (hlt : hatScale S.L m₁ ϱ < C.m₀)
    (hsep : ϱ ≤ minSep S.L (S.L ^ (m₁ + hatScale S.L m₁ ϱ)))
    (hMm : C.geo.c * C.geo.M1 = S.L ^ (C.m₀ + m₁)) (hm : m₁ + hatScale S.L m₁ ϱ + 3 ≤ C.m₀ + m₁)
    {a₁ ν c₀ BG κ : ℝ} (hS : Dec2.DecSpecs S.d S.L (Dec2.selfKc S.d S.L) (Cchi S.d S.L) c₀ BG)
    (SG : DGSetting (C.genWC Y) (compWeight S.L a₁) ν)
    (HB : BgHyp S.d S.L k (minSep S.L C.geo.M1) (compWeight S.L a₁) ν)
    (HBG : BgHyp S.d S.L k ϱ (compWeight S.L a₁) ν) (ha₁ : 0 < a₁) (hκ : 0 ≤ κ)
    (hM : c₀ * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁) {δ τ : ℝ} (hδ0 : 0 < δ) (hτ0 : 0 ≤ τ)
    (hδ73 : δ ≤ thm73C1 S.d S.L N) (hδc : δ + 5 * τ ≤ c7 S.d S.L N BG κ)
    (hrad : decDomRad S.d S.L N BG κ δ τ ≤ bgC1 S.d S.L N) (hw : C.weights = compWeight S.L a₁)
    {u : BlockAt S n M K k → Fin N → ℂ} (hu : C.RDataNear hv Y ν δ τ u)
    {φ : (C.genWC Y).Ω 1 × Fin N → ℂ}
    (hφ : NearApprox (C.genWC Y) (compWeight S.L a₁) ν (C.dataWC Y hv u)
      (cK2' S.d S.L N (famConst S.d S.L BG κ) * (lemma53Const S.d S.L * (δ + 5 * τ))) φ) :
    (∀ j ∈ Finset.Icc 1 k, ∀ s, C.tCubeOfC s = c → s ∈ C.sset (thickY R Y) →
      SmallField.dot (C.psiJAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) j s)
        (C.psiJAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) j s) ∈ Complex.slitPlane) ∧
    ‖Def7v2.cubeRoot C vc Y u hv g (castΩField C.coarseSide_eq (C.genW Y) φ) c‖ ≤
      C.cubeBound Y hv vc g c (2 + nearCb S.d S.L N BG κ δ τ + τ) := by
  have hd0 : 0 < S.d := by have := HB.hd; omega
  have hsmall := small_of_c7 (L := S.L) (N := N) hd0 hS.fam.2.1 hδ0 hτ0 hδc
  have hδ8 : δ ≤ 1 / 8 := by linarith
  have hτ16 : τ ≤ 1 / 16 := by linarith
  have hφB := C.vn_phiBarAt_le Y hv hS SG HB hκ hM hδ0 hτ0 hδ73 hδc hδ8 hτ16 hu hφ
  have hcb0 := nearCb_nonneg (L := S.L) (N := N) hd0 hS.fam.2.1 κ hδ0.le hτ0
  have hnear : ∀ j ∈ Finset.Icc 1 k, ∀ s, C.tCubeOfC s = c → s ∈ C.sset (thickY R Y) →
      vn (C.psiJAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) j s) ≤
          2 + nearCb S.d S.L N BG κ δ τ + τ ∧
        ‖SmallField.dot (C.psiJAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) j s)
          (C.psiJAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) j s) - 1‖ ≤ 1 / 2 := by
    intro j hj s _ hs
    obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
    rcases lt_or_eq_of_le hjk with hlt' | rfl
    · obtain ⟨h1, h2⟩ := C.psiJAt_lt_near Y hv hT hm0 hj1 hlt' hL hN hlt hsep hMm hm hS SG HB HBG
        ha₁ hκ hM hδ0 hτ0 hδ73 hδc hrad hw hu hφ hs
      exact ⟨by linarith, h1⟩
    · obtain ⟨h1, h2⟩ := C.psiJAt_top_near Y hv hk1 (by omega) ha₁ hw hδ8 hτ0 hτ16 hu φ hs
      exact ⟨by linarith, h2⟩
  refine ⟨fun j hj s hsc hs => mem_slitPlane_of_near (hnear j hj s hsc hs).2, ?_⟩
  refine C.norm_cubeRoot_le Y hv vc g c hφB (fun m hm y hy => ?_) hnear
  have := C.vn_psiLevelKOf_le Y hv hk1 hδ8 hτ0 hτ16 hu m hm y hy
  linarith

end Def7.SFCtx

end Balaban.LargeField
