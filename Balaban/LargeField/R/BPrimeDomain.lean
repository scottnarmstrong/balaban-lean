/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalDomCore
public import Balaban.Spine.FinalDomCompose
public import Balaban.SmallField.XiPerturb
public import Balaban.Localization.I5Xi
public import Balaban.Localization.Decoupled2Background
public import Balaban.LargeField.R.BPrimeRoot

/-!
# The data domain on a generating set lying in one layer of another

The terms of the residual of `R` are read at composed fields of the whole generating set
`𝔹_j(W)` of the step, but their domains (the class charts `Ξ^c_j`) are those of the local generating
sets `𝔹_j(X̂)` of their polymers.  Near a polymer deep in `W`, every data site of `𝔹_j(X̂)` lies in
the top layer `j` of `𝔹_j(W)`, where a field of the data domain of `𝔹_j(W)` is constant on the
`j`-blocks; the layers of `𝔹_j(X̂)` are at most `j`, so its blocks are finer.  Then the bounds of
the real data domain `Ψ̃(𝔹_j(W); δ)` give those of `Ψ̃(𝔹_j(X̂); δ)` with the same radius.

* `mem_blockSet_self`, `jBlock_eq_of_mem_blockSet`, `mem_layer_of_dataSites_restrict`: the blocks of
  the finer set;
* `isLayerConstant_restrict`: constancy on the blocks of every layer passes to the finer set;
* `inPsiTilde_restrict`: `Ψ̃(G₁; ν, δ) ⊆ Ψ̃(G; ν, δ)` for the fields, when the data sites of `G` lie in
  the layer `j` of `G₁` and the layers of `G` above `j` are empty;
* `decDomRad`, `nearCompose_xiDom`, `decCompose_xiDom`: **the composed decoupled data lie in the
  chart `Ξ^c_j` of the finer set** (the core: every field near the approximate field).  For data `D` of a top set `H` within `τ` of real data of `Ψ̃(H; δ)` (with the real constant
  field `h₀`), every decoupled background field `φ(s)` of `H`, `|s_P| ≤ e^{κ}` (Theorem I-4b),
  composed onto `G₁ ≺ H` and read on `G`, lies in `Ξ^c_j(G; 1, (2 K₁ + 2) r)`,
  `r = decDomRad … δ τ = O(δ + τ)`.  The real part is the composed field of the real background
  (Theorem 7.3, `inPsiTilde_composeField_bgFieldC`, restricted to `G`); the complex part is the
  composed field of `φ(s) - φ_r` and `D - D_r`, bounded through the I-4b bounds at `s` and at `1` and
  Theorem 5.2 (`theorem52_compare`), and enters through (Ξ2) (`perturb_inPsiTildeC`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.RootFSpine

section Restrict

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {G₁ : GeneratingSet d L (N₁ * L ^ m₁) k ϱ₁}

/-- A site lies in its own block. -/
theorem mem_blockSet_self (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) (x : CTorus d L N₁ m₁ k) :
    x ∈ blockSet G x := by
  classical
  unfold blockSet
  split_ifs
  · exact GeneratingSet.mem_blk.2 rfl
  · exact Finset.mem_singleton_self x

/-- **The blocks of a generating set with no layer above `j` are finer than the `j`-blocks.** -/
theorem jBlock_eq_of_mem_blockSet {j : ℕ} (hjk : j ≤ k) (hΩ : ∀ i, j < i → G.Ω i = ∅)
    {x y : CTorus d L N₁ m₁ k} (hy : y ∈ blockSet G x) :
    jBlock d L (N₁ * L ^ m₁) k j y = jBlock d L (N₁ * L ^ m₁) k j x := by
  classical
  unfold blockSet at hy
  split_ifs at hy with hx
  · exact jBlock_mono (layerIndex_le_of_empty hΩ hx) hjk (GeneratingSet.mem_blk.1 hy)
  · rw [Finset.mem_singleton.1 hy]

/-- A site in the `j`-block of a site of the layer `j` lies in the layer `j`. -/
theorem mem_layer_of_jBlock {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {x y : CTorus d L N₁ m₁ k}
    (hx : x ∈ G₁.layer j)
    (hy : jBlock d L (N₁ * L ^ m₁) k j y = jBlock d L (N₁ * L ^ m₁) k j x) : y ∈ G₁.layer j :=
  (G₁.mem_layer_iff hj1 hjk hy).2 hx

/-- **Constancy on the blocks of the layers passes to a finer set**: if the data sites of `G` lie
in the layer `j` of `G₁` and `G` has no layer above `j`, a field constant on the blocks of every
layer of `G₁` is constant on the blocks of every layer of `G`. -/
theorem isLayerConstant_restrict {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hΩ : ∀ i, j < i → G.Ω i = ∅) (hlay : ∀ x ∈ dataSites G, x ∈ G₁.layer j) {β : Type*}
    {F : CTorus d L N₁ m₁ k → β} (hF : IsLayerConstant G₁ F) : IsLayerConstant G F := by
  intro n hn1 hnk x hx x' hx'
  have hxΩ : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
  have hx₁ : x ∈ G₁.layer j := hlay x ((mem_dataSites G).2 (Or.inl hxΩ))
  have hnj : n ≤ j := by
    have := layerIndex_le_of_empty hΩ hxΩ
    rwa [G.layerIndex_eq hn1 hnk hx] at this
  have hb : jBlock d L (N₁ * L ^ m₁) k j x' = jBlock d L (N₁ * L ^ m₁) k j x :=
    jBlock_mono hnj hjk (GeneratingSet.mem_blk.1 hx')
  exact hF j hj1 hjk x hx₁ x' (GeneratingSet.mem_blk.2 hb)

/-- **The real data domain passes to a finer set lying in one layer**: if the data sites of `G` lie
in the layer `j` of `G₁` and `G` has no layer above `j`, then `Ψ̃(G₁; ν, δ) ⊆ Ψ̃(G; ν, δ)` (`ν ≥ 0`).
The interface pairs of `G` are read on neighbouring sites of the layer `j` of `G₁`, the bounds at
the data sites are those of `G₁`, and the mass condition (R3) is weaker on the finer blocks. -/
theorem inPsiTilde_restrict {N : ℕ} {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hΩ : ∀ i, j < i → G.Ω i = ∅) (hlay : ∀ x ∈ dataSites G, x ∈ G₁.layer j) {ν δ : ℝ}
    (hν : 0 ≤ ν) {Ψ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h : Fin N → ℝ}
    (hP : InPsiTilde G₁ ν δ Ψ h) : InPsiTilde G ν δ Ψ h := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  -- a site of the layer `j` of `G₁` is a data site of `G₁` of layer index `j`
  have hds : ∀ y, y ∈ G₁.layer j → y ∈ dataSites G₁ := fun y hy =>
    (mem_dataSites G₁).2 (Or.inl (G₁.layer_subset hj1 hjk hy))
  have hidx : ∀ y, y ∈ G₁.layer j → G₁.layerIndex y = j := fun y hy =>
    G₁.layerIndex_eq hj1 hjk hy
  -- the value at a site of a block of `G` is the value at the site
  have hval : ∀ x ∈ dataSites G, ∀ y ∈ blockSet G x, Ψ y = Ψ x ∧ y ∈ G₁.layer j := by
    intro x hx y hy
    have hb := jBlock_eq_of_mem_blockSet hjk hΩ hy
    exact ⟨hP.layerConst j hj1 hjk x (hlay x hx) y (GeneratingSet.mem_blk.2 hb),
      mem_layer_of_jBlock hj1 hjk (hlay x hx) hb⟩
  refine ⟨isLayerConstant_restrict hj1 hjk hΩ hlay hP.layerConst, fun x x' hp => ?_,
    fun x hx => hP.r2 x (hds x (hlay x hx)), fun x hx => ?_, hP.r4⟩
  · obtain ⟨hx, hx', -, y, hy, y', hy', hadj⟩ := hp
    obtain ⟨hyx, hy₁⟩ := hval x hx y hy
    obtain ⟨hyx', hy₁'⟩ := hval x' hx' y' hy'
    have hpair : IsInterfacePair G₁ y y' :=
      ⟨hds y hy₁, hds y' hy₁', Or.inl (by rw [hidx y hy₁, hidx y' hy₁']),
        y, mem_blockSet_self G₁ y, y', mem_blockSet_self G₁ y', hadj⟩
    rw [← hyx, ← hyx']
    exact hP.r1 y y' hpair
  · have hx₁ := hlay x hx
    refine lt_of_le_of_lt ?_ (hP.r3 x (hds x hx₁))
    have hl : G.layerIndex x ≤ G₁.layerIndex x := by
      rw [hidx x hx₁]
      by_cases hxΩ : x ∈ G.Ω 1
      · exact layerIndex_le_of_empty hΩ hxΩ
      · rw [layerIndex_of_not_mem G hxΩ]; exact Nat.zero_le _
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 hl) 2) hν

end Restrict

/-! ### The composed decoupled data on a finer set -/

/-- **The radius of the composed decoupled data**: `δ' + 5 (2 c + τ)` with `δ' = C₄ K₁ δ` the radius
of the real composed field and `c = N · 2 K₂' C₃ δ_c + δ_c + K₁ δ_c` the bound of `φ(s) - φ_r`,
`δ_c = δ + 5 τ` the radius of the data. -/
noncomputable def decDomRad (d L N : ℕ) [NeZero L] (BG κ δ τ : ℝ) : ℝ :=
  compC4 d * (bgK1 d L N * δ) + 5 * (2 * ((N : ℝ) * (2 * (cK2' d L N (famConst d L BG κ) *
    (lemma53Const d L * (δ + 5 * τ)))) + (δ + 5 * τ) + bgK1 d L N * (δ + 5 * τ)) + τ)

section Decoupled

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ : ℝ}

/-- **The composed data of a field near the approximate field lie in the chart `Ξ^c_j` of a finer
set** (the core of `decCompose_xiDom`).  As `decCompose_xiDom`, for every field `φ` of `H` within
`K₂' C₃ (δ + 5 τ)` of the approximate field of `D` (`NearApprox`, the range of the decoupled
background fields of Theorem I-4b). -/
theorem nearCompose_xiDom {C : DecCover d L N₁ m₁ k} {H : GeneratingSet d L (N₁ * L ^ m₁) k ϱ}
    {G₁ : GeneratingSet d L (N₁ * L ^ m₁) k ϱ₁} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ₂}
    {a₁ ν Kc Cx c BG κ : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase C H (compWeight L a₁) ν Kc Cx) (HB : BgHyp d L k ϱ (compWeight L a₁) ν)
    (HB₁ : BgHyp d L k ϱ₁ (compWeight L a₁) ν) (HBG : BgHyp d L k ϱ₂ (compWeight L a₁) ν)
    (ha₁ : 0 < a₁) (hκ : 0 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hP₁ : Precedes G₁ H) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hΩ : ∀ i, j < i → G.Ω i = ∅)
    (hlay : ∀ x ∈ dataSites G, x ∈ G₁.layer j) {δ τ : ℝ} (hδ0 : 0 < δ) (hτ0 : 0 ≤ τ)
    (hδ73 : δ ≤ thm73C1 d L N) (hδc : δ + 5 * τ ≤ c7 d L N BG κ)
    (hrad : decDomRad d L N BG κ δ τ ≤ bgC1 d L N)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ} (hP : InPsiTilde H ν δ Ψ₀ h₀)
    {D : BgData H N} (hDh : ∀ x ∈ H.Ω 1, ∀ i, D.h x i = (h₀ i : ℂ))
    (hDΨ : ∀ x ∈ dataSites H, vn (fun i => D.Ψ x i - (Ψ₀ x i : ℂ)) ≤ τ)
    {φs : H.Ω 1 × Fin N → ℂ}
    (hsups : NearApprox H (compWeight L a₁) ν D
      (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * (δ + 5 * τ))) φs) :
    Def6.XiDom G (compWeight L a₁) ν j ((2 * bgK1 d L N + 2) * decDomRad d L N BG κ δ τ)
      (fun x i => composeField G₁ H (compWeight L a₁) φs D.Ψ x i)
      (fun _ i => (h₀ i : ℂ)) := by
  have hd0 : 0 < d := by have := HB.hd; omega
  have hL2 : 2 ≤ L := by have := HB.hL; omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hK1 := bgK1_ge_one d L N
  have hC4 := compC4_ge d
  have hC3 := lemma53Const_pos d L
  have hBG : 0 ≤ BG := hS.fam.2.1
  have hfam : 0 ≤ famConst d L BG κ := by
    have := famConst_ge_one (L := L) hBG κ hd0; linarith
  have hK2 := cK2'_nonneg (d := d) (L := L) (N := N) hfam
  set δc := δ + 5 * τ with hδcdef
  have hδc0 : 0 < δc := by positivity
  obtain ⟨hδc1, -, hδc2⟩ := c7_facts (L := L) (N := N) hd0 hBG hδc0.le hδc
  have hδc0' : δc ≤ bgC0 d L N := hδc1.trans (bgC1_le_bgC0 d L N hd0)
  have hνε : ν * ((L : ℝ) ^ k) ^ 2 * δc ^ 2 ≤ δc ^ 2 := by
    have := HB.massLe; nlinarith [sq_nonneg δc]
  have hsmall := (bgC1_facts d L N hd0 hδc1).1
  have hδc1024 : δc ≤ 1 / 1024 := (approxDelta_le d L hsmall).1
  -- the real datum and its composed field (Theorem 7.3, real data)
  set Dr : BgData H N := SmallField.realData H Ψ₀ h₀ hP.layerConst with hDrdef
  have hRr := SmallField.realData_realizes (h₀ := h₀) hP.layerConst
  obtain ⟨hreal, hPG₁⟩ := inPsiTilde_composeField_bgFieldC (G := G₁) ha₁ HB₁ HB hP₁ hδ0 hδ73 hP
    (D' := Dr) hRr.1 hRr.2
  set f : CTorus d L N₁ m₁ k → Fin N → ℝ := fun x i => (composeField G₁ H (compWeight L a₁)
    (bgFieldC H (compWeight L a₁) ν (bgC0 d L N) Dr) Dr.Ψ x i).re with hf
  have hPG : InPsiTilde G ν (compC4 d * (bgK1 d L N * δ)) f h₀ :=
    inPsiTilde_restrict hj1 hjk hΩ hlay HB.mass hPG₁
  -- the data `D` lie in `Ψ̃^c(H; δ_c, δ_c)`
  have hδ14 : δ ≤ 1 / 4 := by
    have := (approxDelta_le d L (bgC1_facts d L N hd0
      (thm73_small (L := L) (N := N) hd0 hδ0 hδ73).1).1).1
    linarith
  have hτ1 : τ ≤ 1 := by linarith
  set δΨ : CTorus d L N₁ m₁ k → Fin N → ℂ := fun x i => D.Ψ x i - (Ψ₀ x i : ℂ) with hδΨ
  have hδΨc : IsLayerConstant H δΨ := by
    intro n hn1 hnk x hx x' hx'
    funext i
    show D.Ψ x' i - (Ψ₀ x' i : ℂ) = D.Ψ x i - (Ψ₀ x i : ℂ)
    rw [congrFun (D.Ψ_layerConst n hn1 hnk x hx x' hx') i,
      congrFun (hP.layerConst n hn1 hnk x hx x' hx') i]
  have hPC := perturb_inPsiTildeC hδ14 hτ0 hτ1 (inPsiTildeC_of_inPsiTilde hδ0 hP) hδΨc hDΨ
  have hW : InDomainC H ν δc δc D :=
    ⟨Ψ₀, h₀, _, _, hPC, fun x _ i => by simp [hδΨ], fun x hx i => by simp [hDh x hx i]⟩
  -- the decoupled fields at `s` and at `1`, the complex and the real backgrounds
  obtain ⟨φ1, α1, hI1, hu1, -, hsup1, -⟩ := Dec2.i4b_exists_unique hS Sb HB hκ hM
    (s := fun _ => 1) (fun P => by simpa using Real.one_le_exp hκ) hδc0 le_rfl hδc0' hδc hνε hW
  have hφ1 : Dec2.decBgField C H (compWeight L a₁) ν (rho4 d L N BG κ) (fun _ => 1) D = φ1 :=
    (Dec2.decBg_eq hI1 hu1).1
  have hUD : InUnionDomainC H (bgC0 d L N) (c7 d L N BG κ) ν D :=
    ⟨δc, δc, hδc0, le_rfl, hδc0', hδc, hνε, hW⟩
  have hφ1c : φ1 = bgFieldC H (compWeight L a₁) ν (bgC0 d L N) D := by
    rw [← hφ1]; exact decBgField_one_eq hS Sb HB hκ hM hUD
  obtain ⟨φc, αc, hsc, -, huc⟩ := theorem52_exists HB hδc0 le_rfl hδc0' hδc1 hνε hW
  have hφcC := (bgFieldC_eq hsc huc).1
  have hDrR : InDomainR H ν δ Dr := ⟨Ψ₀, h₀, hP, hRr.1, hRr.2⟩
  obtain ⟨φr, αr, hsr, -, hur, -⟩ := bg_real HB hδ0
    (thm73_small (L := L) (N := N) hd0 hδ0 hδ73).1 hDrR
  have hφrC := (bgFieldC_eq hsr hur).1
  let Wd : DataWit H ν δc δc D := ⟨Ψ₀, h₀, _, _, hPC, fun x _ i => by simp [hδΨ],
    fun x hx i => by simp [hDh x hx i]⟩
  have hcmp : ∀ z : H.Ω 1, vn (fun i => φc (z, i) - φr (z, i)) ≤ δc + bgK1 d L N * δc :=
    fun z => theorem52_compare HB hδc0 le_rfl hδc0' hδc1 hνε Wd Dr hRr.1 hRr.2 hsc hsr z
  -- the bound of `φ(s) - φ_r`
  set V := cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δc) with hV
  have hV0 : 0 ≤ V := by positivity
  set cb := (N : ℝ) * (2 * V) + δc + bgK1 d L N * δc with hcb
  have hcb0 : 0 ≤ cb := by positivity
  have hΔφ : ∀ y, vn (svec H (φs - φr) y) ≤ cb := by
    intro y
    by_cases hy : y ∈ H.Ω 1
    · have hs' : ∀ i, ‖φs (⟨y, hy⟩, i) - φ1 (⟨y, hy⟩, i)‖ ≤ 2 * V := fun i => by
        have h1 := hsups.val y i
        have h2 := hsup1.val y i
        simp only [svec, zeroExt, hy, ↓reduceDIte] at h1 h2
        calc ‖φs (⟨y, hy⟩, i) - φ1 (⟨y, hy⟩, i)‖
            ≤ ‖φs (⟨y, hy⟩, i) - approxField H (compWeight L a₁) ν D.Ψ D.h y i‖ +
              ‖φ1 (⟨y, hy⟩, i) - approxField H (compWeight L a₁) ν D.Ψ D.h y i‖ := by
                rw [← norm_neg (φ1 (⟨y, hy⟩, i) - _)]
                refine (norm_add_le _ _).trans_eq' ?_
                ring_nf
          _ ≤ 2 * V := by linarith
      have h1 : vn (fun i => φs (⟨y, hy⟩, i) - φ1 (⟨y, hy⟩, i)) ≤ N * (2 * V) :=
        vn_le_card_mul (by positivity) hs'
      have h2 : vn (fun i => φ1 (⟨y, hy⟩, i) - φr (⟨y, hy⟩, i)) ≤ δc + bgK1 d L N * δc := by
        rw [hφ1c, hφcC]; exact hcmp ⟨y, hy⟩
      have e : svec H (φs - φr) y =
          fun i => (φs (⟨y, hy⟩, i) - φ1 (⟨y, hy⟩, i)) + (φ1 (⟨y, hy⟩, i) - φr (⟨y, hy⟩, i)) := by
        funext i; simp [svec, zeroExt, hy]
      rw [e]
      refine (vn_add' _ _).trans ?_
      rw [hcb]; linarith
    · have e : svec H (φs - φr) y = 0 := by funext i; simp [svec, zeroExt, hy]
      rw [e, vn_zero]; exact hcb0
  -- the complex part of the composed field and its bound on `G`
  set Δ : CTorus d L N₁ m₁ k → Fin N → ℂ := fun x i =>
    composeField G₁ H (compWeight L a₁) (φs - φr) (D.Ψ - Dr.Ψ) x i with hΔdef
  have hDΨr : ∀ x ∈ dataSites H, vn ((D.Ψ - Dr.Ψ) x) ≤ τ := fun x hx => by
    have e : (D.Ψ - Dr.Ψ) x = fun i => D.Ψ x i - (Ψ₀ x i : ℂ) := by
      funext i
      show D.Ψ x i - Dr.Ψ x i = _
      rw [show Dr.Ψ x i = (Ψ₀ x i : ℂ) from hRr.1 x hx i]
    rw [e]; exact hDΨ x hx
  have hΔb : ∀ x ∈ dataSites G, vn (Δ x) ≤ 2 * cb + τ := fun x hx =>
    vn_composeField_le hL2 ha₁ hP₁ hcb0 hτ0 hΔφ hDΨr
      ((mem_dataSites G₁).2 (Or.inl (G₁.layer_subset hj1 hjk (hlay x hx))))
  have hΔlc : IsLayerConstant G Δ := by
    have hlc : IsLayerConstant H (D.Ψ - Dr.Ψ) := by
      intro n hn1 hnk x hx x' hx'
      funext i
      simp only [Pi.sub_apply]
      rw [congrFun (D.Ψ_layerConst n hn1 hnk x hx x' hx') i,
        congrFun (Dr.Ψ_layerConst n hn1 hnk x hx x' hx') i]
    exact isLayerConstant_restrict hj1 hjk hΩ hlay
      (composeField_layerConst hP₁ (compWeight L a₁) (φs - φr) hlc)
  -- the chart
  set r := decDomRad d L N BG κ δ τ with hr
  have hr' : r = compC4 d * (bgK1 d L N * δ) + 5 * (2 * cb + τ) := by
    rw [hr, decDomRad, hcb, hV]
  have hr0 : 0 < compC4 d * (bgK1 d L N * δ) := by positivity
  have hr1 : r ≤ bgC1 d L N := hrad
  have hrc0 : r ≤ bgC0 d L N := hr1.trans (bgC1_le_bgC0 d L N hd0)
  have hr1024 := (approxDelta_le d L (bgC1_facts d L N hd0 hr1).1).1
  have hδ'14 : compC4 d * (bgK1 d L N * δ) ≤ 1 / 4 := by
    have : 0 ≤ 5 * (2 * cb + τ) := by positivity
    linarith
  have hδ₃1 : 2 * cb + τ ≤ 1 := by
    have : 0 ≤ compC4 d * (bgK1 d L N * δ) := hr0.le
    linarith
  have hPCG := perturb_inPsiTildeC hδ'14 (by positivity) hδ₃1
    (inPsiTildeC_of_inPsiTilde hr0 hPG) hΔlc hΔb
  rw [← hr'] at hPCG
  have hrpos : 0 < r := by rw [hr']; positivity
  have hνr : ν * ((L : ℝ) ^ k) ^ 2 * r ^ 2 ≤ r ^ 2 := by
    have := HBG.massLe; nlinarith [sq_nonneg r]
  have hX := psiTildeC_subset_xiC HBG hrpos le_rfl hrc0 hr1 hνr hPCG
    (εb := (2 * bgK1 d L N + 2) * r) (by linarith)
  have hXj := xiC_level_mono hjk HBG.mass (by omega) hX
  refine ⟨f, h₀, fun x i => 0 + Δ x i, fun _ _ => 0, fun x i => ?_, fun x i => by simp, hXj⟩
  have e1 := composeField_sub (G := G₁) (G' := H) (compWeight L a₁) φr (φs - φr) Dr.Ψ D.Ψ x i
  rw [add_sub_cancel] at e1
  have e2 := hreal x i
  show composeField G₁ H (compWeight L a₁) φs D.Ψ x i = (f x i : ℂ) + (0 + Δ x i)
  have e3 : (f x i : ℂ) = composeField G₁ H (compWeight L a₁) φr Dr.Ψ x i := by
    show ((composeField G₁ H (compWeight L a₁)
      (bgFieldC H (compWeight L a₁) ν (bgC0 d L N) Dr) Dr.Ψ x i).re : ℂ) = _
    rw [← e2, hφrC]
  rw [zero_add, e3]
  show _ = _ + composeField G₁ H (compWeight L a₁) (φs - φr) (D.Ψ - Dr.Ψ) x i
  rw [← e1]
  ring

/-- **The composed decoupled data lie in the chart `Ξ^c_j` of a finer set.**  Let `H` be a
generating set with a decoupling cover `C` (Theorem I-4b: `DecSpecs`, `CoverBase`, `BgHyp`, `hM`),
`G₁ ≺ H` with the standing hypotheses `BgHyp`, and `G` a generating set with no layer above `j`
whose data sites lie in the layer `j` of `G₁` (all with the weights `compWeight L a₁` and the mass
`ν`).  Let the data `D` of `H` be within `τ` of real data `Ψ₀ ∈ Ψ̃(H; ν, δ)` on the data sites,
with `D.h = h₀` on `Ω₁`.  Then for every label vector `|s_P| ≤ e^κ` the composed field
`composeField(G₁, H; φ(s), D.Ψ)` of the decoupled background field `φ(s)`, with the constant field
`h₀`, lies in `Ξ^c_j(G; 1, (2 K₁ + 2) r)`, `r = decDomRad d L N BG κ δ τ`, under the smallness
`δ ≤ c_{7.3}`, `δ + 5 τ ≤ c₇` and `r ≤ c₁` (the instance of `nearCompose_xiDom`). -/
theorem decCompose_xiDom {C : DecCover d L N₁ m₁ k} {H : GeneratingSet d L (N₁ * L ^ m₁) k ϱ}
    {G₁ : GeneratingSet d L (N₁ * L ^ m₁) k ϱ₁} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ₂}
    {a₁ ν Kc Cx c BG κ : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase C H (compWeight L a₁) ν Kc Cx) (HB : BgHyp d L k ϱ (compWeight L a₁) ν)
    (HB₁ : BgHyp d L k ϱ₁ (compWeight L a₁) ν) (HBG : BgHyp d L k ϱ₂ (compWeight L a₁) ν)
    (ha₁ : 0 < a₁) (hκ : 0 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hP₁ : Precedes G₁ H) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hΩ : ∀ i, j < i → G.Ω i = ∅)
    (hlay : ∀ x ∈ dataSites G, x ∈ G₁.layer j) {δ τ : ℝ} (hδ0 : 0 < δ) (hτ0 : 0 ≤ τ)
    (hδ73 : δ ≤ thm73C1 d L N) (hδc : δ + 5 * τ ≤ c7 d L N BG κ)
    (hrad : decDomRad d L N BG κ δ τ ≤ bgC1 d L N)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ} (hP : InPsiTilde H ν δ Ψ₀ h₀)
    {D : BgData H N} (hDh : ∀ x ∈ H.Ω 1, ∀ i, D.h x i = (h₀ i : ℂ))
    (hDΨ : ∀ x ∈ dataSites H, vn (fun i => D.Ψ x i - (Ψ₀ x i : ℂ)) ≤ τ)
    {s : Dec2.DecParams C} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) :
    Def6.XiDom G (compWeight L a₁) ν j ((2 * bgK1 d L N + 2) * decDomRad d L N BG κ δ τ)
      (fun x i => composeField G₁ H (compWeight L a₁)
        (Dec2.decBgField C H (compWeight L a₁) ν (rho4 d L N BG κ) s D) D.Ψ x i)
      (fun _ i => (h₀ i : ℂ)) := by
  have hd0 : 0 < d := by have := HB.hd; omega
  have hBG : 0 ≤ BG := hS.fam.2.1
  set δc := δ + 5 * τ with hδcdef
  have hδc0 : 0 < δc := by positivity
  obtain ⟨hδc1, -, -⟩ := c7_facts (L := L) (N := N) hd0 hBG hδc0.le hδc
  have hδc0' : δc ≤ bgC0 d L N := hδc1.trans (bgC1_le_bgC0 d L N hd0)
  have hνε : ν * ((L : ℝ) ^ k) ^ 2 * δc ^ 2 ≤ δc ^ 2 := by
    have := HB.massLe; nlinarith [sq_nonneg δc]
  have hδ14 : δ ≤ 1 / 4 := by
    have := (approxDelta_le d L (bgC1_facts d L N hd0
      (thm73_small (L := L) (N := N) hd0 hδ0 hδ73).1).1).1
    linarith
  have hτ1 : τ ≤ 1 := by
    have := (approxDelta_le d L (bgC1_facts d L N hd0 hδc1).1).1
    linarith
  set δΨ : CTorus d L N₁ m₁ k → Fin N → ℂ := fun x i => D.Ψ x i - (Ψ₀ x i : ℂ) with hδΨ
  have hδΨc : IsLayerConstant H δΨ := by
    intro n hn1 hnk x hx x' hx'
    funext i
    show D.Ψ x' i - (Ψ₀ x' i : ℂ) = D.Ψ x i - (Ψ₀ x i : ℂ)
    rw [congrFun (D.Ψ_layerConst n hn1 hnk x hx x' hx') i,
      congrFun (hP.layerConst n hn1 hnk x hx x' hx') i]
  have hPC := perturb_inPsiTildeC hδ14 hτ0 hτ1 (inPsiTildeC_of_inPsiTilde hδ0 hP) hδΨc hDΨ
  have hW : InDomainC H ν δc δc D :=
    ⟨Ψ₀, h₀, _, _, hPC, fun x _ i => by simp [hδΨ], fun x hx i => by simp [hDh x hx i]⟩
  obtain ⟨φs, αs, hIs, hus, -, hsups, -⟩ := Dec2.i4b_exists_unique hS Sb HB hκ hM hs hδc0 le_rfl
    hδc0' hδc hνε hW
  rw [(Dec2.decBg_eq hIs hus).1]
  exact nearCompose_xiDom hS Sb HB HB₁ HBG ha₁ hκ hM hP₁ hj1 hjk hΩ hlay hδ0 hτ0 hδ73 hδc hrad hP
    hDh hDΨ hsups

end Decoupled

end Balaban.LargeField
