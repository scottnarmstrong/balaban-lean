/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BPrimeCast
public import Balaban.LargeField.R.BPrimeDomain
public import Balaban.Fluctuation.HatSetGeom
public import Balaban.Fluctuation.OldTermsLiftHat
public import Balaban.Fluctuation.LocalClassDensityIrrelSupport
public import Balaban.LargeField.History.TopBlockTransport

/-!
# The local generating sets of the terms of `R` inside the top layer of `𝔹_j(W)`

The terms `ℰ^{(j)}(y, X)`, `ℳ^{(j)}(x, X)` of the small-field exponent on `Y` (Def-7, P5 (1.8),
(1.13)) have polymers `X ⊂ Y^≈` of the level `j ≤ k - 1`, and their generating sets are the cast
local sets `𝔹_j(X̂)` (ruling R13).  The data sites of `𝔹_j(X̂)` lie within
`11 L^{m₁'} L^j + 1 + ⌊L/2⌋ a_j` of `X`, which is below the side `L^k c M₁ = L^k L^{m₀+m₁}` of the
cubes of `𝕋_k` when `m₁' + 3 ≤ m₀ + m₁`; so they lie over cubes within one cube of `Y^≈`, hence in
`W = (Y^≈)^≈`, which is the top layer `j` of `𝔹_j(W)` (`genWCj`).

* `SFCtx.genWCj_mem_layer_iff`: the layer `j` of the transported `𝔹_j(W)` is the fine set of `W`;
* `SFCtx.dataSites_hat_mem_genWCj`: the data sites of the cast local set `𝔹_j(X̂)` of a polymer
  `X ⊂ Y^≈` lie in that layer;
* `SFCtx.genWCj_precedes`: `𝔹_j(W) ≺ 𝔹_k(W)` on the Def-6 torus;
* `SFCtx.sfTerm_nearCompose_xiDom`: **the domain estimate of the terms of `R`**: for a polymer
  `X ⊂ Y^≈` whose class generating set is `𝔹_j(X̂)` (`HatSpec`, no layer above `j`), the composed
  field of every field `φ` of `𝔹_k(W)` near the approximate field (in particular every decoupled
  background field of Theorem I-4b) lies in the chart `Ξ^c_j` of the class generating set.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.GsSpec Balaban.Fluctuation

namespace Def7.SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

/-- **The layer `j` of the transported `𝔹_j(W_k)` is the fine set of `W_k`** (`j < k`): a site lies
in it iff its cube of `𝕋_k` lies in `W = (Y^≈)^≈`. -/
theorem genWCj_mem_layer_iff (Y : Set (Torus S.d (n k))) {j : ℕ} (hj : j < k)
    (x : Localization.CTorus S.d S.L C.N₁ m₁ k) :
    x ∈ (C.genWCj hj.le Y).layer j ↔
      blockMap (S.L ^ k * (C.geo.c * C.geo.M1)) (n k) (sfToBg C.geo C.hT x) ∈ W2 R Y := by
  have hm : C.geo.c * n k * S.L ^ (k - k) = C.geo.c * n k := by simp
  have hU := (isCubeUnion_cubePre (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L) (q := k)
    le_rfl hm (W2 R Y)).of_le hj.le le_rfl
  rw [GeneratingSet.mem_layer]
  unfold genWCj
  rw [mem_castG_Ω, mem_castG_Ω, ← sfToBg_eq_torusCast]
  unfold genSF
  rw [minimalGenSet_Ω, minimalGenSet_Ω, minLayer_of_gt _ (Nat.lt_succ_self j), minLayer_self,
    hU.cubeInterior_eq, mem_cubePre]
  simp

/-- **The data sites of the local set `𝔹_j(X̂)` of a polymer `X ⊂ Y^≈` lie in the layer `j` of the
transported `𝔹_j(W_k)`** (`j < k`), when `M = c M₁ = L^{m₀+m₁}` and `m₁' + 3 ≤ m₀ + m₁` (the cubes
of the local set are finer than the cells of `𝒟_{k-1}` by `L³`). -/
theorem dataSites_hat_mem_genWCj (Y : Set (Torus S.d (n k))) {j : ℕ} (hj : j < k) (hL : 3 ≤ S.L)
    {N₁' m₁' : ℕ} [NeZero N₁'] (hc : N₁' * S.L ^ m₁' = C.N₁ * S.L ^ m₁) {ϱ₂ : ℝ}
    (hs₂ : ϱ₂ ≤ minSep S.L (S.L ^ m₁'))
    (hMm : C.geo.c * C.geo.M1 = S.L ^ (C.m₀ + m₁)) (hm : m₁' + 3 ≤ C.m₀ + m₁)
    {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hX : X ⊆ C.sset (thickY R Y))
    (hcell : ∀ z ∈ X, Localization.box (cbase (cellSide S.L C.m₀ m₁ j) z)
      (cellSide S.L C.m₀ m₁ j) ⊆ X) :
    ∀ x ∈ dataSites (castG hc (localB j hj.le
      {x' : Localization.CTorus S.d S.L N₁' m₁' k |
        (GsSpec.torusCast x' : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈ hatSet C.m₀ j X} hs₂)),
      x ∈ (C.genWCj hj.le Y).layer j := by
  intro x hx
  have hL2 : 2 ≤ S.L := by omega
  -- the chain `x → X̂ → X`
  obtain ⟨y', hy', hxy'⟩ := dataSites_castG_range hc _ _ (11 * S.L ^ m₁' * S.L ^ j + 1)
    (fun x hx => localB_dataSites_range hL2 hx) hx
  obtain ⟨w, hwX, hyw⟩ := exists_near_of_mem_hatSet hcell _ hy'
  set D := 11 * S.L ^ m₁' * S.L ^ j + 1 + S.L / 2 * cellSide S.L C.m₀ m₁ j with hD
  have hxw : supDist x w ≤ D := (supDist_triangle x _ w).trans (Nat.add_le_add hxy' hyw)
  -- the bound `D ≤ L^k c M₁`
  have hPD : D ≤ S.L ^ k * (C.geo.c * C.geo.M1) := by
    rw [hMm, hD]
    unfold cellSide
    have hLp : ∀ e, 1 ≤ S.L ^ e := fun e => Nat.one_le_pow _ _ (by omega)
    have h1 : 11 * S.L ^ m₁' * S.L ^ j + 1 ≤ 12 * S.L ^ (m₁' + j) := by
      rw [pow_add]; have := hLp (m₁' + j); rw [pow_add] at this; nlinarith
    have h2 : 12 * S.L ^ (m₁' + j) ≤ S.L ^ (j + C.m₀ + m₁) := by
      have e : S.L ^ (j + C.m₀ + m₁) = S.L ^ (m₁' + j) * S.L ^ (C.m₀ + m₁ - m₁') := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      have h27 : 27 ≤ S.L ^ (C.m₀ + m₁ - m₁') := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ S.L ^ 3 := Nat.pow_le_pow_left hL 3
          _ ≤ S.L ^ (C.m₀ + m₁ - m₁') := Nat.pow_le_pow_right (by omega) (by omega)
      have := hLp (m₁' + j)
      nlinarith
    have h3 : S.L / 2 * S.L ^ (j + C.m₀ + m₁) + S.L ^ (j + C.m₀ + m₁) ≤
        S.L * S.L ^ (j + C.m₀ + m₁) := by
      have : S.L / 2 + 1 ≤ S.L := by omega
      nlinarith [hLp (j + C.m₀ + m₁)]
    have h4 : S.L * S.L ^ (j + C.m₀ + m₁) ≤ S.L ^ k * S.L ^ (C.m₀ + m₁) := by
      rw [← pow_succ', ← pow_add]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    omega
  -- over the background torus
  have hxw' : supDist (sfToBg C.geo C.hT x) (sfToBg C.geo C.hT w) ≤ D := by
    rw [sfToBg_eq_torusCast, sfToBg_eq_torusCast, supDist_torusCast_val C.hT]
    exact hxw
  have hfine : C.geo.M1 * (C.geo.c * n k) * S.L ^ k = (S.L ^ k * (C.geo.c * C.geo.M1)) * n k := by
    ring
  have hblk := supDist_blockMap_le_one (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L) (q := k)
    hfine hPD _ _ hxw'
  have hwY : blockMap (S.L ^ k * (C.geo.c * C.geo.M1)) (n k) (sfToBg C.geo C.hT w) ∈
      thickY R Y := by
    have h := hX hwX
    change cubeMap n S.L M K k (bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT w)) ∈ thickY R Y
      at h
    rwa [cubeMap_bgToFine_gen C.geo C.hnn C.hkK k] at h
  rw [C.genWCj_mem_layer_iff Y hj]
  unfold W2
  exact mem_nbhd.2 ⟨_, hwY, hblk.trans (by omega)⟩

/-- **`𝔹_j(W_k) ≺ 𝔹_k(W_k)` on the Def-6 torus.** -/
theorem genWCj_precedes (Y : Set (Torus S.d (n k))) {j : ℕ} (hj : j ≤ k) :
    Precedes (C.genWCj hj Y) (C.genWC Y) := by
  have hm : C.geo.c * n k * S.L ^ (k - k) = C.geo.c * n k := by simp
  exact precedes_castG C.coarseSide_eq (genSF_precedes hj hm (W2 R Y))

/-- **The domain estimate of the terms of `R`.**  Let `X ⊂ Y^≈` be a polymer of `𝒟_j`, `1 ≤ j < k`,
whose class generating set `G` has no layer above `j` and is the local set `𝔹_j(X̂)` of ruling R13
(`HatSpec`, with the cube exponent `s = hatScale L m₁ ϱ < m₀` and the separation of the class),
and let `M = c M₁ = L^{m₀+m₁}`, `m₁ + s + 3 ≤ m₀ + m₁`.  With the decoupling hypotheses of the
transported `𝔹_k(W)` (`DGSetting`, `DecSpecs` of the self cover, `BgHyp`) and the standing
hypotheses of `G`, for data `D` of `𝔹_k(W)` within `τ` of real data `Ψ₀ ∈ Ψ̃(𝔹_k(W); δ)` (constant
field `h₀`) and every field `φ` near the approximate field, the composed field
`composeField(𝔹_j(W), 𝔹_k(W); φ, D.Ψ)` lies in `Ξ^c_j(G; 1, (2 K₁ + 2) r)`,
`r = decDomRad d L N BG κ δ τ` (`nearCompose_xiDom`). -/
theorem sfTerm_nearCompose_xiDom (Y : Set (Torus S.d (n k))) {j : ℕ} (hj1 : 1 ≤ j) (hj : j < k)
    (hL : 3 ≤ S.L) {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    (hX : X ⊆ C.sset (thickY R Y)) (hpoly : Def6.IsPolyDom C.m₀ j X) (hN : S.L ^ C.m₀ ∣ C.N₁)
    {G : GeneratingSet S.d S.L (C.N₁ * S.L ^ m₁) k ϱ} (hΩ : ∀ i, j < i → G.Ω i = ∅)
    (hHat : HatSpec C.m₀ j X G) (hlt : hatScale S.L m₁ ϱ < C.m₀)
    (hsep : ϱ ≤ minSep S.L (S.L ^ (m₁ + hatScale S.L m₁ ϱ)))
    (hMm : C.geo.c * C.geo.M1 = S.L ^ (C.m₀ + m₁)) (hm : m₁ + hatScale S.L m₁ ϱ + 3 ≤ C.m₀ + m₁)
    {a₁ ν c BG κ : ℝ} (hS : Dec2.DecSpecs S.d S.L (Dec2.selfKc S.d S.L) (Cchi S.d S.L) c BG)
    (SG : DGSetting (C.genWC Y) (compWeight S.L a₁) ν)
    (HB : BgHyp S.d S.L k (minSep S.L C.geo.M1) (compWeight S.L a₁) ν)
    (HBG : BgHyp S.d S.L k ϱ (compWeight S.L a₁) ν) (ha₁ : 0 < a₁) (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁) {δ τ : ℝ} (hδ0 : 0 < δ) (hτ0 : 0 ≤ τ)
    (hδ73 : δ ≤ thm73C1 S.d S.L N) (hδc : δ + 5 * τ ≤ c7 S.d S.L N BG κ)
    (hrad : decDomRad S.d S.L N BG κ δ τ ≤ bgC1 S.d S.L N)
    {Ψ₀ : Localization.CTorus S.d S.L C.N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    (hP : InPsiTilde (C.genWC Y) ν δ Ψ₀ h₀) {D : BgData (C.genWC Y) N}
    (hDh : ∀ x ∈ (C.genWC Y).Ω 1, ∀ i, D.h x i = (h₀ i : ℂ))
    (hDΨ : ∀ x ∈ dataSites (C.genWC Y), vn (fun i => D.Ψ x i - (Ψ₀ x i : ℂ)) ≤ τ)
    {φ : (C.genWC Y).Ω 1 × Fin N → ℂ}
    (hφ : NearApprox (C.genWC Y) (compWeight S.L a₁) ν D
      (cK2' S.d S.L N (famConst S.d S.L BG κ) * (lemma53Const S.d S.L * (δ + 5 * τ))) φ) :
    Def6.XiDom G (compWeight S.L a₁) ν j ((2 * bgK1 S.d S.L N + 2) * decDomRad S.d S.L N BG κ δ τ)
      (fun x i => composeField (C.genWCj hj.le Y) (C.genWC Y) (compWeight S.L a₁) φ D.Ψ x i)
      (fun _ i => (h₀ i : ℂ)) := by
  set s := hatScale S.L m₁ ϱ with hsdef
  -- the finer cube torus of the local sets
  have hdvd : S.L ^ s ∣ C.N₁ := (pow_dvd_pow S.L hlt.le).trans hN
  obtain ⟨N₁', hN₁'⟩ := hdvd
  have hN₁'0 : N₁' ≠ 0 := by
    rintro rfl
    exact NeZero.ne C.N₁ (by simpa using hN₁')
  have : NeZero N₁' := ⟨hN₁'0⟩
  have hc : N₁' * S.L ^ (m₁ + s) = C.N₁ * S.L ^ m₁ := by rw [hN₁', pow_add]; ring
  have hGeq := Fluctuation.HatSpec.eq_castLocalB hHat hlt hsep hj.le hc
  have hcell := cell_subset_of_isPolyDom hN hj.le hpoly
  have hlay : ∀ x ∈ dataSites G, x ∈ (C.genWCj hj.le Y).layer j := by
    rw [hGeq]
    exact C.dataSites_hat_mem_genWCj Y hj hL hc hsep hMm (by omega) hX hcell
  exact nearCompose_xiDom hS (Dec2.coverBase_self SG) HB HB HBG ha₁ hκ hM
    (C.genWCj_precedes Y hj.le) hj1 hj.le hΩ hlay hδ0 hτ0 hδ73 hδc hrad hP hDh hDΨ hφ

end Def7.SFCtx

end Balaban.LargeField
