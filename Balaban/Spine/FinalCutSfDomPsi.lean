/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The domains of the terms of the small-field factor of a cut

A6-4 (`CutSfDomInput`, "A4-1i for cuts"). At a late scale (positive cube mass `ν L^{-2k}`) the
characteristic function `χ_k(Y)` of a cut `Y` tests the datum `Ψ = lift_k ψ_k` at **every** data site
of the background generating set `𝔹_k(W₂(Y))` (the direction test on `□^{∼ρ_k}`,
`parentPsi_dir_of_chiY_ne_zero`): `|Ψ(s) - h| < δ_k / √ν`. Hence:

* `inPsiTilde_genW_late`: the datum lies in the real domain `Ψ̃(𝔹_k(W₂(Y)); 3 δ_k / √ν)`, for every
  cut `Y` (no history enters);
* `psiSF_near_h`: on the fine set of `W₂(Y)` (top layer of `𝔹_j(W₂(Y))` and of `𝔹_k(W₂(Y))`) the
  inherited field `ψ^{(j)}_k` is real and within `3 (3 K₁ + 1) δ_k / √ν` of `h` (the background is
  within `K₁ · 3 δ_k / √ν` of the datum, `BgBounds.val`, and the composition weight is at most `1`);
* `psiExt`, `allSitesBounds_psiExt`, `xiDom_psiExt`: the inherited field on `W₂(Y)`, extended by `h`
  off `W₂(Y)`, satisfies the bounds of the data domain at every site, so it lies in the analyticity
  domain `Ξ^c_j(𝔹; 1, ε)` of every polymer chart; it equals the inherited field on `Y^≈`, which is
  all that the terms `ℰ^{(j)}(y, X)`, `ℳ^{(j)}(x, X)`, `X ⊆ Y^≈`, read (`localE`, `localM`);
* `liftExt`, `xiDom_liftExt`: the same for the lift of the block field on `Y` (the terms
  `ℛ^{(k)}_n(X)`, `X ⊆ Y`).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField
  Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Localization

namespace Balaban.RootFSpine

section Vec

variable {N : ℕ}

theorem rn_sub_comm (a b : Fin N → ℝ) : rn (fun i => a i - b i) = rn (fun i => b i - a i) := by
  unfold rn
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `|∑ a_i b_i| ≤ rn a · rn b`. -/
theorem abs_sum_mul_le_rn (a b : Fin N → ℝ) : |∑ i, a i * b i| ≤ rn a * rn b := by
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  rw [← rn_sq a, ← rn_sq b, ← mul_pow] at h1
  exact abs_le_of_sq_le_sq' h1 (mul_nonneg (rn_nonneg a) (rn_nonneg b)) |>.elim
    (fun h2 h3 => abs_le.2 ⟨h2, h3⟩)

/-- A vector within `t` of a unit vector has `|a · a - 1| ≤ 2 t + t²`. -/
theorem abs_sum_sq_sub_one_le (a h : Fin N → ℝ) (hh : ∑ i, h i ^ 2 = 1) {t : ℝ}
    (ht : rn (fun i => a i - h i) ≤ t) : |∑ i, a i ^ 2 - 1| ≤ 2 * t + t ^ 2 := by
  have hrnh : rn h = 1 := by unfold rn; rw [hh, Real.sqrt_one]
  have e : ∑ i, a i ^ 2 - 1 = 2 * ∑ i, (a i - h i) * h i + ∑ i, (a i - h i) ^ 2 := by
    have : ∑ i, a i ^ 2 = ∑ i, ((a i - h i) ^ 2 + 2 * ((a i - h i) * h i) + h i ^ 2) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [this, Finset.sum_add_distrib, Finset.sum_add_distrib, hh, ← Finset.mul_sum]
    ring
  rw [e]
  have h1 := abs_sum_mul_le_rn (fun i => a i - h i) h
  rw [hrnh, mul_one] at h1
  have h2 : ∑ i, (a i - h i) ^ 2 = rn (fun i => a i - h i) ^ 2 := (rn_sq _).symm
  have h0 := rn_nonneg (fun i => a i - h i)
  have h3 : rn (fun i => a i - h i) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ h0 ht 2
  rw [h2]
  have hs : |2 * ∑ i, (a i - h i) * h i| ≤ 2 * t := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hq : |rn (fun i => a i - h i) ^ 2| ≤ t ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact h3
  exact (abs_add_le _ _).trans (add_le_add hs hq)

end Vec

section Near

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

/-- **The composed field near a constant**: if `φ'` is within `c` of `z` on `Ω'₁` and `Ψ'` within
`c'` of `z` on `Ω'₁`, then the composed field `ψ(𝔹_j, 𝔹'_k; Ψ')` is within `2 c + c'` of `z` on
`Ω₁` (the blocks of the layers of `𝔹_j` and `𝔹'_k` lie in `Ω'₁`; `0 ≤ κ ≤ 1`). -/
theorem vn_composeField_sub_le (hL2 : 2 ≤ L) {a₁ : ℝ} (ha₁ : 0 < a₁) (h : Precedes G G')
    {c c' : ℝ} (z : Fin N → ℂ) {φ' : G'.Ω 1 × Fin N → ℂ} {Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hφ : ∀ y : G'.Ω 1, vn (fun i => φ' (y, i) - z i) ≤ c)
    (hΨ : ∀ y ∈ G'.Ω 1, vn (fun i => Ψ' y i - z i) ≤ c') {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) :
    vn (fun i => composeField G G' (compWeight L a₁) φ' Ψ' x i - z i) ≤ 2 * c + c' := by
  obtain ⟨hn1, hnk, hxn⟩ := G.layerIndex_spec hx
  have hx' := h.mem_Ω1 hx
  obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec hx'
  obtain ⟨k0, k1⟩ := compWeight_kappa_mem hL2 ha₁ hn1 (h.layerIndex_le hx)
  have hm1 : vn (fun i => blockMean G (G.layerIndex x) (fun y => svec G' φ' y i) x - z i) ≤ c := by
    refine vn_blockMean_sub_le (G := G) hnk (svec G' φ') x z (fun y hy => ?_)
    have hyl : y ∈ G.layer (G.layerIndex x) :=
      (G.mem_layer_iff hn1 hnk (GeneratingSet.mem_blk.1 hy)).2 hxn
    have hy1 : y ∈ G'.Ω 1 := h.mem_Ω1 (G.layer_subset hn1 hnk hyl)
    have e : (fun i => svec G' φ' y i - z i) = fun i => φ' (⟨y, hy1⟩, i) - z i :=
      funext fun i => by rw [svec_of_mem' φ' hy1 i]
    rw [e]
    exact hφ ⟨y, hy1⟩
  have hm2 : vn (fun i => blockMean G' (G'.layerIndex x) (fun y => svec G' φ' y i) x - z i) ≤
      c := by
    refine vn_blockMean_sub_le (G := G') hpk (svec G' φ') x z (fun y hy => ?_)
    have hyl : y ∈ G'.layer (G'.layerIndex x) :=
      (G'.mem_layer_iff hp1 hpk (GeneratingSet.mem_blk.1 hy)).2 hxp
    have hy1 : y ∈ G'.Ω 1 := G'.layer_subset hp1 hpk hyl
    have e : (fun i => svec G' φ' y i - z i) = fun i => φ' (⟨y, hy1⟩, i) - z i :=
      funext fun i => by rw [svec_of_mem' φ' hy1 i]
    rw [e]
    exact hφ ⟨y, hy1⟩
  have hΨx := hΨ x hx'
  have e : (fun i => composeField G G' (compWeight L a₁) φ' Ψ' x i - z i) = fun i =>
      (blockMean G (G.layerIndex x) (fun y => svec G' φ' y i) x - z i) +
        ((compWeight L a₁ (G'.layerIndex x) / compWeight L a₁ (G.layerIndex x) *
          (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2) : ℝ) : ℂ) *
          ((Ψ' x i - z i) -
            (blockMean G' (G'.layerIndex x) (fun y => svec G' φ' y i) x - z i)) := by
    funext i
    rw [composeField_of_mem _ φ' Ψ' hx i]
    ring
  rw [e]
  refine (vn_add' _ _).trans ?_
  rw [vn_smul_real, abs_of_nonneg k0]
  have h3 := vn_sub_le' (fun i => Ψ' x i - z i)
    (fun i => blockMean G' (G'.layerIndex x) (fun y => svec G' φ' y i) x - z i)
  have h4 := mul_le_mul k1 (h3.trans (add_le_add hΨx hm2)) (vn_nonneg _) zero_le_one
  linarith

end Near

section Sites

variable {d L N₀ q N : ℕ} [NeZero L]

/-- **The bounds at every site from the distance to a unit vector**: a real field constant on the
`j`-blocks within `t ≤ 1` of the unit vector `h` at every site, and a mass `m ≥ 0` with
`m L^{2q} ≤ 1` (`j ≤ q`), satisfies the bounds of the data domain at every site with radius
`4 t`. -/
theorem allSitesBounds_of_near {jj : ℕ} (hjq : jj ≤ q) {m t : ℝ} (hm : 0 ≤ m)
    (hmL : m * ((L : ℝ) ^ q) ^ 2 ≤ 1) (ht0 : 0 < t) (ht1 : t ≤ 1)
    {f : Torus d (N₀ * L ^ q) → Fin N → ℝ} {h₀ : Fin N → ℝ} (hh₀ : ∑ i, h₀ i ^ 2 = 1)
    (hblock : ∀ x x', jBlock d L N₀ q jj x = jBlock d L N₀ q jj x' → f x = f x')
    (hnear : ∀ x, rn (fun i => f x i - h₀ i) ≤ t) :
    AllSitesBounds jj m (4 * t) f h₀ where
  block := hblock
  adj x x' _ := by
    have h1 := hnear x
    have h2 := hnear x'
    rw [rn_sub_comm] at h2
    have := rn_triangle (f x) h₀ (f x')
    linarith
  sphere x := by
    have h1 := abs_sum_sq_sub_one_le (f x) h₀ hh₀ (hnear x)
    nlinarith
  dir x := by
    have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    have h1 := r3_of_dir hL1 hjq (f x) h₀ hh₀ hm
    have h0 := rn_nonneg (fun i => f x i - h₀ i)
    have h3 : rn (fun i => f x i - h₀ i) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ h0 (hnear x) 2
    have h4 : m * ((L : ℝ) ^ q) ^ 2 * rn (fun i => f x i - h₀ i) ^ 2 ≤
        rn (fun i => f x i - h₀ i) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hmL (sq_nonneg (rn (fun i => f x i - h₀ i)))
      linarith
    nlinarith

end Sites

section Geom

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- The fine set, on the background torus, of a set of cubes of the level-`k` torus. -/
noncomputable abbrev cubeSet (W : Set (Torus S.d (n (j + 1)))) : Finset (BgT C.geo (j + 1)) :=
  cubePre C.geo.M1 (C.geo.c * n (j + 1)) S.L (j + 1) (S.L ^ (j + 1) * (C.geo.c * C.geo.M1))
    (n (j + 1)) W

theorem mem_cubeSet {W : Set (Torus S.d (n (j + 1)))} {x : BgT C.geo (j + 1)} :
    x ∈ cubeSet C W ↔ blockMap (S.L ^ (j + 1) * (C.geo.c * C.geo.M1)) (n (j + 1)) x ∈ W :=
  mem_cubePre

theorem isCubeUnion_cubeSet {p : ℕ} (hp : p ≤ j + 1) (W : Set (Torus S.d (n (j + 1)))) :
    IsCubeUnion C.geo.M1 (C.geo.c * n (j + 1)) S.L (j + 1) p (cubeSet C W) := by
  have hm : C.geo.c * n (j + 1) * S.L ^ (j + 1 - (j + 1)) = C.geo.c * n (j + 1) := by simp
  exact (isCubeUnion_cubePre (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L)
    (q := j + 1) (le_refl _) hm W).of_le hp le_rfl

/-- The fine set of a set of cubes is a union of `p`-blocks, `p ≤ k`. -/
theorem cubeSet_block {p : ℕ} (hp : p ≤ j + 1) (W : Set (Torus S.d (n (j + 1))))
    {x x' : BgT C.geo (j + 1)}
    (h : jBlock S.d S.L (C.geo.M1 * (C.geo.c * n (j + 1))) (j + 1) p x =
      jBlock S.d S.L (C.geo.M1 * (C.geo.c * n (j + 1))) (j + 1) p x') :
    x ∈ cubeSet C W ↔ x' ∈ cubeSet C W :=
  (isCubeUnion_cubeSet C hp W).isBlockUnion hp x x' h

/-- **The fine set of `W` lies in every layer of `𝔹_j(W)`**: the `π_k`-cubes of `W` are unions of
`𝒞_j`-cubes. -/
theorem mem_genSF_Ω_of_cubeSet {jj m : ℕ} (hjk : jj ≤ j + 1) (hmj : m ≤ jj)
    (W : Set (Torus S.d (n (j + 1)))) {x : BgT C.geo (j + 1)} (hx : x ∈ cubeSet C W) :
    x ∈ (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
      (n := n (j + 1)) hjk W).Ω m := by
  show x ∈ minLayer C.geo.M1 (C.geo.c * n (j + 1)) S.L (j + 1) jj (cubeSet C W) m
  refine minLayer_antitone hmj ?_
  rw [minLayer_self, (isCubeUnion_cubeSet C hjk W).cubeInterior_eq]
  exact hx

/-- On the fine set of `W` the layer of `𝔹_j(W)` is the top layer `j`. -/
theorem layerIndex_genSF_of_cubeSet {jj : ℕ} (hj1 : 1 ≤ jj) (hjk : jj ≤ j + 1)
    (W : Set (Torus S.d (n (j + 1)))) {x : BgT C.geo (j + 1)} (hx : x ∈ cubeSet C W) :
    (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
      (n := n (j + 1)) hjk W).layerIndex x = jj := by
  set G := genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
    (n := n (j + 1)) hjk W with hG
  have htop : G.Ω (jj + 1) = ∅ := minLayer_of_gt _ (Nat.lt_succ_self _)
  have hl : x ∈ G.layer jj :=
    G.mem_layer.2 ⟨mem_genSF_Ω_of_cubeSet C hjk le_rfl W hx, by rw [htop]; simp⟩
  exact G.layerIndex_eq hj1 hjk hl

/-- The fine set of `Y` lies in the fine set of `W₂(Y)`. -/
theorem cubeSet_subset_W2 (Y : Set (Torus S.d (n (j + 1)))) :
    cubeSet C Y ⊆ cubeSet C (W2 R Y) := fun x hx => by
  rw [mem_cubeSet] at hx ⊢
  exact subset_nbhd _ _ (subset_nbhd _ _ hx)

omit [NeZero S.L] in
/-- The fine set of `Y^≈` lies in the fine set of `W₂(Y)`. -/
theorem thickY_subset_W2 (Y : Set (Torus S.d (n (j + 1)))) : thickY R Y ⊆ W2 R Y :=
  fun _ hx => subset_nbhd _ _ hx

/-- A site of the Def-6 torus is in the fine set `sset A` exactly when its image on the background
torus is in the fine set of `A`. -/
theorem mem_sset_iff (A : Set (Torus S.d (n (j + 1))))
    (x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) :
    x ∈ C.sset A ↔ sfToBg C.geo C.hT x ∈ cubeSet C A := by
  rw [mem_cubeSet]
  show cubeMap n S.L M K (j + 1) (bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT x)) ∈ A ↔ _
  rw [cubeMap_bgToFine C]

end Geom

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N (j + 1) m₁ ϱ)
  (hv : EuclideanSpace ℝ (Fin N)) (Y : Set (Torus S.d (n (j + 1))))
  (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))

/-- **The level-`k` datum of a cut in the real domain** (late scales): from `χ_Y(ψ_k) ≠ 0` and a
cube mass `ν L^{-2k}`, `0 < ν ≤ 1`, the field `parentPsi` lies in
`Ψ̃(𝔹_k(W₂(Y)); ν L^{-2k}, 3 δ_k / √ν)` at the unit vector `h`: every data site is within
`δ_k / √ν` of `h` (`parentPsi_dir_of_chiY_ne_zero`). -/
theorem inPsiTilde_genW_late (hL : 2 ≤ S.L) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hunit : ‖hv‖ = 1)
    (hδ : 0 < C.cs.delta (j + 1)) (he1 : C.cs.delta (j + 1) / Real.sqrt ν ≤ 1)
    (hμ : C.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν) (hχ : C.chiY Y ψk hv ≠ 0) :
    InPsiTilde (C.genW Y) (sfBgMassAt S.L (j + 1) ν) (3 * (C.cs.delta (j + 1) / Real.sqrt ν))
      (parentPsi C ψk) (fun i => hv i) := by
  set e : ℝ := C.cs.delta (j + 1) / Real.sqrt ν with he
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have he0 : 0 < e := div_pos hδ hsq
  have hsum : ∑ i, hv i ^ 2 = 1 := by rw [parent_sum_sq_eq_norm_sq, hunit]; norm_num
  have hdir : ∀ s ∈ dataSites (C.genW Y), rn (fun i => parentPsi C ψk s i - hv i) < e :=
    fun s hs => parentPsi_dir_of_chiY_ne_zero C hL Y ψk hv hχ hν hμ hs
  have hm0 : 0 ≤ sfBgMassAt S.L (j + 1) ν := by unfold sfBgMassAt physMass; positivity
  have hL1 : 1 ≤ S.L := by omega
  refine ⟨parentPsi_layerConst C Y ψk, fun x x' hp => ?_, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · have h1 := hdir x hp.1
    have h2 := hdir x' hp.2.1
    rw [rn_sub_comm] at h2
    have := rn_triangle (parentPsi C ψk x) (fun i => hv i) (parentPsi C ψk x')
    linarith
  · have h1 := abs_sum_sq_sub_one_le (parentPsi C ψk x) (fun i => hv i) hsum le_rfl
    have h2 := hdir x hx
    have h0 := rn_nonneg (fun i => parentPsi C ψk x i - hv i)
    nlinarith
  · have hmL : sfBgMassAt S.L (j + 1) ν * ((S.L : ℝ) ^ (j + 1)) ^ 2 = ν := physMass_mul_sq _ _
    refine lt_of_le_of_lt (r3_of_dir hL1 (layerIndex_le_k _ x) (parentPsi C ψk x)
      (fun i => hv i) hsum hm0) ?_
    rw [hmL]
    have h1 := hdir x hx
    have h0 := rn_nonneg (fun i => parentPsi C ψk x i - hv i)
    have h2 : rn (fun i => parentPsi C ψk x i - hv i) ^ 2 < e ^ 2 :=
      pow_lt_pow_left₀ h1 h0 two_ne_zero
    nlinarith
  · simp only [hsum, sub_self, abs_zero, mul_zero]
    positivity

/-- The datum of the cut, as `BgData`, realizes `parentPsi` on the data sites and `h` on `Ω₁`. -/
theorem inDomainR_genW_late (hL : 2 ≤ S.L) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hunit : ‖hv‖ = 1)
    (hδ : 0 < C.cs.delta (j + 1)) (he1 : C.cs.delta (j + 1) / Real.sqrt ν ≤ 1)
    (hμ : C.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν) (hχ : C.chiY Y ψk hv ≠ 0) :
    InDomainR (C.genW Y) (sfBgMassAt S.L (j + 1) ν) (3 * (C.cs.delta (j + 1) / Real.sqrt ν))
      (DfamY C hv Y ψk) :=
  ⟨parentPsi C ψk, fun i => hv i, inPsiTilde_genW_late C hv Y ψk hL hν hν1 hunit hδ he1 hμ hχ,
    fun x hx i => liftSingle_Ψ_eq_parentPsi C _ ψk hv hx i,
    fun x hx i => by unfold DfamY; rw [liftSingle_h _ _ _ hx]; rfl⟩

/-- **The inherited field of a cut is real, and near `h` on the first layer** (late scales): on
`Ω₁(𝔹_j(W₂(Y)))` the field `ψ^{(j)}_k` is within `(6 K₁ + 3) δ_k / √ν` of `h`. The background `φ_k`
is within `K₁ · 3 δ_k / √ν` of the datum (`BgBounds.val`), the datum within `δ_k / √ν` of `h`
(the direction test of `χ_Y` at every data site), and the composed field is within `2 c + c'`
(`vn_composeField_sub_le`). -/
theorem psiSF_real_near (hL : 2 ≤ S.L) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hunit : ‖hv‖ = 1)
    (hδ : 0 < C.cs.delta (j + 1)) (he1 : C.cs.delta (j + 1) / Real.sqrt ν ≤ 1)
    (hη : 3 * (C.cs.delta (j + 1) / Real.sqrt ν) ≤ thm73C1 S.d S.L N)
    (hμ : C.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (hμBg : C.cs.muBg (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    (hχ : C.chiY Y ψk hv ≠ 0) {jj : ℕ} (hj : jj ≤ j + 1) :
    (∀ x i, psiSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
      (n := n (j + 1)) C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N) hj
      (W2 R Y) (C.liftData ψk) (hC hv) x i = ((psiJReY C ψk hv Y hj x i : ℝ) : ℂ)) ∧
    ∀ x ∈ (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
        (n := n (j + 1)) hj (W2 R Y)).Ω 1,
      rn (fun i => psiJReY C ψk hv Y hj x i - hv i) ≤
        (6 * bgK1 S.d S.L N + 3) * (C.cs.delta (j + 1) / Real.sqrt ν) := by
  classical
  set e : ℝ := C.cs.delta (j + 1) / Real.sqrt ν with he
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have he0 : 0 < e := div_pos hδ hsq
  have hd : 0 < S.d := by have := HB.hd; omega
  have ha₁ : 0 < Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)) 1 := by
    have := (HB.weights 1 le_rfl (by omega)).1
    exact lt_of_lt_of_le (by norm_num) this
  have hw : C.weights = compWeight S.L (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)) 1) :=
    funext fun r => aIdeal_eq_compWeight hL (j + 1) (C.sf.a (j + 1)) r
  have HBc : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1)
      (compWeight S.L (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)) 1)) (sfBgMassAt S.L (j + 1) ν) := by
    rw [← hw, ← hμBg]; exact HB
  have hm : C.geo.c * n (j + 1) * S.L ^ (j + 1 - (j + 1)) = C.geo.c * n (j + 1) := by simp
  have hprec := genSF_precedes (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L)
    (c := C.geo.c) (n := n (j + 1)) hj hm (W2 R Y)
  have hP := inPsiTilde_genW_late C hv Y ψk hL hν hν1 hunit hδ he1 hμ hχ
  have h3e : 0 < 3 * e := by positivity
  obtain ⟨hreal, -⟩ := inPsiTilde_composeField_bgFieldC ha₁ HBc HBc hprec
    (D' := DfamY C hv Y ψk) h3e hη hP
    (fun x hx i => liftSingle_Ψ_eq_parentPsi C _ ψk hv hx i)
    (fun x hx i => by unfold DfamY; rw [liftSingle_h _ _ _ hx]; rfl)
  have hpsi : ∀ x i, psiSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
      (n := n (j + 1)) C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N) hj
      (W2 R Y) (C.liftData ψk) (hC hv) x i =
      composeField (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L)
          (c := C.geo.c) (n := n (j + 1)) hj (W2 R Y)) (C.genW Y)
        (compWeight S.L (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)) 1))
        (bgFieldC (C.genW Y) (compWeight S.L (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)) 1))
          (sfBgMassAt S.L (j + 1) ν) (bgC0 S.d S.L N) (DfamY C hv Y ψk))
        (DfamY C hv Y ψk).Ψ x i := by
    intro x i
    unfold psiSF bgSF DfamY
    rw [hw, hμBg]
  have hreal' : ∀ x i, psiSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L)
      (c := C.geo.c) (n := n (j + 1)) C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N) hj
      (W2 R Y) (C.liftData ψk) (hC hv) x i = ((psiJReY C ψk hv Y hj x i : ℝ) : ℂ) := by
    intro x i
    have h3 : psiJReY C ψk hv Y hj x i = (psiSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1))
        (L := S.L) (c := C.geo.c) (n := n (j + 1)) C.weights (C.cs.muBg (j + 1))
        (bgC0 S.d S.L N) hj (W2 R Y) (C.liftData ψk) (hC hv) x i).re := rfl
    rw [h3, hpsi x i]
    exact hreal x i
  refine ⟨hreal', fun x hx => ?_⟩
  -- the background is within `K₁ · 3 e` of the datum
  obtain ⟨hsm1, -, -, -, -⟩ := thm73_small (L := S.L) (N := N) hd h3e hη
  obtain ⟨φ, α, hs, hb, hu, -, -, -⟩ := bg_real HBc h3e hsm1
    (inDomainR_genW_late C hv Y ψk hL hν hν1 hunit hδ he1 hμ hχ)
  obtain ⟨hfC, -⟩ := bgFieldC_eq hs hu
  have hdir : ∀ s ∈ dataSites (C.genW Y), rn (fun i => parentPsi C ψk s i - hv i) < e :=
    fun s hs => parentPsi_dir_of_chiY_ne_zero C hL Y ψk hv hχ hν hμ hs
  have hΨ : ∀ y ∈ (C.genW Y).Ω 1,
      vn (fun i => (DfamY C hv Y ψk).Ψ y i - ((hv i : ℝ) : ℂ)) ≤ e := by
    intro y hy
    have hyd : y ∈ dataSites (C.genW Y) := (mem_dataSites _).2 (Or.inl hy)
    have e1 : (fun i => (DfamY C hv Y ψk).Ψ y i - ((hv i : ℝ) : ℂ)) =
        fun i => (((parentPsi C ψk y i - hv i : ℝ)) : ℂ) := by
      funext i
      rw [show (DfamY C hv Y ψk).Ψ y i = ((parentPsi C ψk y i : ℝ) : ℂ) from
        liftSingle_Ψ_eq_parentPsi C _ ψk hv hyd i]
      push_cast
      ring
    rw [e1, vn_ofReal]
    exact (hdir y hyd).le
  have hφ : ∀ y : (C.genW Y).Ω 1,
      vn (fun i => φ (y, i) - ((hv i : ℝ) : ℂ)) ≤ bgK1 S.d S.L N * (3 * e) + e := by
    intro y
    have h1 := hb.val y
    have h2 := hΨ y y.2
    have h3 : vn (fun i => φ (y, i) - ((hv i : ℝ) : ℂ)) ≤
        vn (fun i => φ (y, i) - (DfamY C hv Y ψk).Ψ y i) +
          vn (fun i => (DfamY C hv Y ψk).Ψ y i - ((hv i : ℝ) : ℂ)) :=
      vn_triangle (fun i => φ (y, i)) ((DfamY C hv Y ψk).Ψ y) (fun i => ((hv i : ℝ) : ℂ))
    linarith
  have key := vn_composeField_sub_le hL ha₁ hprec (fun i => ((hv i : ℝ) : ℂ)) hφ hΨ hx
  rw [← hfC] at key
  have e2 : (fun i => composeField (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L)
          (c := C.geo.c) (n := n (j + 1)) hj (W2 R Y)) (C.genW Y)
        (compWeight S.L (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)) 1))
        (bgFieldC (C.genW Y) (compWeight S.L (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)) 1))
          (sfBgMassAt S.L (j + 1) ν) (bgC0 S.d S.L N) (DfamY C hv Y ψk))
        (DfamY C hv Y ψk).Ψ x i - ((hv i : ℝ) : ℂ)) =
      fun i => (((psiJReY C ψk hv Y hj x i - hv i : ℝ)) : ℂ) := by
    funext i
    rw [← hpsi x i, hreal' x i]
    push_cast
    ring
  rw [e2, vn_ofReal] at key
  have hK1 := bgK1_ge_one S.d S.L N
  nlinarith

/-! ### The extensions by `h` -/

open Classical in
/-- **The inherited field of the cut, extended by `h`**: `ψ^{(j)}_k` on the fine set of `W₂(Y)`,
the constant field `h` elsewhere (Def-6 torus). -/
noncomputable def psiJExt (jj : ℕ) : Def6.Fld S.d S.L C.N₁ m₁ (j + 1) N := fun x =>
  if x ∈ C.sset (W2 R Y) then C.psiJ Y ψk hv jj x else Def6.constFld (hC hv) x

open Classical in
/-- **The lift of the block field on the cut, extended by `h`**: `ψ_k` on the fine set of `Y`, the
constant field `h` elsewhere (Def-6 torus). -/
noncomputable def liftExt : Def6.Fld S.d S.L C.N₁ m₁ (j + 1) N := fun x =>
  if x ∈ C.sset Y then sfLiftK C.geo C.hnn C.hkK C.hT ψk x else Def6.constFld (hC hv) x

/-- The fine set is monotone. -/
theorem sset_mono {A B : Set (Torus S.d (n (j + 1)))} (h : A ⊆ B) : C.sset A ⊆ C.sset B :=
  fun _ hx => h hx

/-- The extension agrees with the inherited field on the fine set of `Y^≈`. -/
theorem psiJExt_eq_of_mem {jj : ℕ} {x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)}
    (hx : x ∈ C.sset (thickY R Y)) : psiJExt C hv Y ψk jj x = C.psiJ Y ψk hv jj x := by
  have hx' : x ∈ C.sset (W2 R Y) := sset_mono C (thickY_subset_W2 Y) hx
  simp only [psiJExt, hx', ↓reduceIte]

/-- The extension agrees with the lift on the fine set of `Y`. -/
theorem liftExt_eq_of_mem {x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)} (hx : x ∈ C.sset Y) :
    liftExt C hv Y ψk x = sfLiftK C.geo C.hnn C.hkK C.hT ψk x := by
  simp only [liftExt, hx, ↓reduceIte]

/-- The extension of the inherited field is continuous in the block field on the domain. -/
theorem continuousOn_psiJExt
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    {jj : ℕ} (hj : jj ≤ j + 1) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      psiJExt C hv Y ψk jj) (DomSetY C hv Y (C.cs.muBg (j + 1))) := by
  refine continuousOn_pi.2 fun x => ?_
  by_cases hx : x ∈ C.sset (W2 R Y)
  · have e : (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
        psiJExt C hv Y ψk jj x) = fun ψk => C.psiJ Y ψk hv jj x := by
      funext ψk; simp only [psiJExt, hx, ↓reduceIte]
    rw [e]
    exact continuousOn_pi.2 fun i => continuousOn_psiJ_coordY C hv Y HB hj x i
  · have e : (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
        psiJExt C hv Y ψk jj x) = fun _ => Def6.constFld (hC hv) x := by
      funext ψk; simp only [psiJExt, hx, ↓reduceIte]
    rw [e]
    exact continuousOn_const

/-- The extension of the lift is continuous in the block field. -/
theorem continuous_liftExt :
    Continuous fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      liftExt C hv Y ψk := by
  refine continuous_pi fun x => ?_
  by_cases hx : x ∈ C.sset Y
  · have e : (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
        liftExt C hv Y ψk x) = fun ψk => sfLiftK C.geo C.hnn C.hkK C.hT ψk x := by
      funext ψk; simp only [liftExt, hx, ↓reduceIte]
    rw [e]
    exact continuous_apply x |>.comp (continuous_sfLiftK C)
  · have e : (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
        liftExt C hv Y ψk x) = fun _ => Def6.constFld (hC hv) x := by
      funext ψk; simp only [liftExt, hx, ↓reduceIte]
    rw [e]
    exact continuous_const

/-- The real field of the extended inherited field on the background torus. -/
noncomputable def psiJExtRe {jj : ℕ} (hj : jj ≤ j + 1) : BgT C.geo (j + 1) → Fin N → ℝ :=
  open Classical in fun s =>
    if s ∈ cubeSet C (W2 R Y) then psiJReY C ψk hv Y hj s else fun i => hv i

/-- The real field of the extended lift on the background torus. -/
noncomputable def liftExtRe : BgT C.geo (j + 1) → Fin N → ℝ :=
  open Classical in fun s => if s ∈ cubeSet C Y then parentPsi C ψk s else fun i => hv i

/-- **The extended inherited field on the support of `χ_Y`**: it is the real field `psiJExtRe` read
on the Def-6 torus, and `psiJExtRe` has the bounds of the data domain at every site with radius
`4 (6 K₁ + 3) δ_k / √ν`. -/
theorem psiJExt_allSites (hL : 2 ≤ S.L) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hunit : ‖hv‖ = 1)
    (hδ : 0 < C.cs.delta (j + 1))
    (ht1 : (6 * bgK1 S.d S.L N + 3) * (C.cs.delta (j + 1) / Real.sqrt ν) ≤ 1)
    (hη : 3 * (C.cs.delta (j + 1) / Real.sqrt ν) ≤ thm73C1 S.d S.L N)
    (hμ : C.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (hμBg : C.cs.muBg (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    (hχ : C.chiY Y ψk hv ≠ 0) {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) :
    psiJExt C hv Y ψk jj = (fun x i => ((psiJExtRe C hv Y ψk hj (torusCast C.hT x) i : ℝ) : ℂ)) ∧
    AllSitesBounds (N₀ := C.geo.M1 * (C.geo.c * n (j + 1))) (q := j + 1) jj
      (sfBgMassAt S.L (j + 1) ν)
      (4 * ((6 * bgK1 S.d S.L N + 3) * (C.cs.delta (j + 1) / Real.sqrt ν)))
      (psiJExtRe C hv Y ψk hj) (fun i => hv i) := by
  classical
  set e : ℝ := C.cs.delta (j + 1) / Real.sqrt ν with he
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have he0 : 0 < e := div_pos hδ hsq
  have hK1 := bgK1_ge_one S.d S.L N
  have he1 : e ≤ 1 := by nlinarith
  obtain ⟨hreal, hnear⟩ := psiSF_real_near C hv Y ψk hL hν hν1 hunit hδ he1 hη hμ hμBg HB hχ hj
  have hsum : ∑ i, hv i ^ 2 = 1 := by rw [parent_sum_sq_eq_norm_sq, hunit]; norm_num
  refine ⟨?_, ?_⟩
  · funext x i
    unfold psiJExt psiJExtRe
    have hmem : x ∈ C.sset (W2 R Y) ↔ torusCast C.hT x ∈ cubeSet C (W2 R Y) :=
      mem_sset_iff C (W2 R Y) x
    by_cases hx : x ∈ C.sset (W2 R Y)
    · simp only [hx, hmem.1 hx, ↓reduceIte]
      exact psiJ_eq_ofRealY C hv Y ψk hj hreal x i
    · have hx' : torusCast C.hT x ∉ cubeSet C (W2 R Y) := fun h => hx (hmem.2 h)
      simp only [hx, hx', ↓reduceIte, Def6.constFld, hC]
  · have hm0 : 0 ≤ sfBgMassAt S.L (j + 1) ν := by unfold sfBgMassAt physMass; positivity
    have hmL : sfBgMassAt S.L (j + 1) ν * ((S.L : ℝ) ^ (j + 1)) ^ 2 ≤ 1 := by
      rw [show sfBgMassAt S.L (j + 1) ν * ((S.L : ℝ) ^ (j + 1)) ^ 2 = ν from physMass_mul_sq _ _]
      exact hν1
    have ht0 : 0 < (6 * bgK1 S.d S.L N + 3) * e := by positivity
    refine allSitesBounds_of_near hj hm0 hmL ht0 ht1 hsum (fun x x' hb => ?_) (fun x => ?_)
    · have hiff := cubeSet_block C hj (W2 R Y) hb
      unfold psiJExtRe
      by_cases hx : x ∈ cubeSet C (W2 R Y)
      · have hx' := hiff.1 hx
        simp only [hx, hx', ↓reduceIte]
        set Gj := genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
          (n := n (j + 1)) hj (W2 R Y) with hGj
        have hm : C.geo.c * n (j + 1) * S.L ^ (j + 1 - (j + 1)) = C.geo.c * n (j + 1) := by simp
        have hprec := genSF_precedes (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L)
          (c := C.geo.c) (n := n (j + 1)) hj hm (W2 R Y)
        have hLC := composeField_layerConst hprec C.weights
          (bgSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
            (n := n (j + 1)) C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N) (W2 R Y)
            (C.liftData ψk) (hC hv))
          (DfamY C hv Y ψk).Ψ_layerConst
        have hidx := layerIndex_genSF_of_cubeSet C hj1 hj (W2 R Y) hx
        have hxl : x ∈ Gj.layer jj := by
          have := (Gj.layerIndex_spec (mem_genSF_Ω_of_cubeSet C hj hj1 (W2 R Y) hx)).2.2
          rwa [hidx] at this
        have hx'b : x' ∈ Gj.blk jj x := GeneratingSet.mem_blk.2 hb.symm
        have key := hLC jj hj1 hj x hxl x' hx'b
        funext i
        unfold psiJReY psiSF
        exact congrArg Complex.re (congrFun key i).symm
      · have hx' : x' ∉ cubeSet C (W2 R Y) := fun h => hx (hiff.2 h)
        simp only [hx, hx', ↓reduceIte]
    · unfold psiJExtRe
      by_cases hx : x ∈ cubeSet C (W2 R Y)
      · simp only [hx, ↓reduceIte]
        exact hnear x (mem_genSF_Ω_of_cubeSet C hj (le_refl 1 |>.trans hj1) (W2 R Y) hx)
      · simp only [hx, ↓reduceIte, sub_self]
        have : rn (fun _ : Fin N => (0 : ℝ)) = 0 := by unfold rn; simp
        rw [this]
        positivity

/-- **The extended lift on the support of `χ_Y`**: it is the real field `liftExtRe` read on the
Def-6 torus, and `liftExtRe` has the bounds of the data domain at every site (level `k`) with
radius `4 δ_k / √ν`. -/
theorem liftExt_allSites (hL : 2 ≤ S.L) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hunit : ‖hv‖ = 1)
    (hδ : 0 < C.cs.delta (j + 1)) (he1 : C.cs.delta (j + 1) / Real.sqrt ν ≤ 1)
    (hμ : C.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν) (hχ : C.chiY Y ψk hv ≠ 0) :
    liftExt C hv Y ψk = (fun x i => ((liftExtRe C hv Y ψk (torusCast C.hT x) i : ℝ) : ℂ)) ∧
    AllSitesBounds (N₀ := C.geo.M1 * (C.geo.c * n (j + 1))) (q := j + 1) (j + 1)
      (sfBgMassAt S.L (j + 1) ν) (4 * (C.cs.delta (j + 1) / Real.sqrt ν))
      (liftExtRe C hv Y ψk) (fun i => hv i) := by
  classical
  set e : ℝ := C.cs.delta (j + 1) / Real.sqrt ν with he
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have he0 : 0 < e := div_pos hδ hsq
  have hsum : ∑ i, hv i ^ 2 = 1 := by rw [parent_sum_sq_eq_norm_sq, hunit]; norm_num
  refine ⟨?_, ?_⟩
  · funext x i
    unfold liftExt liftExtRe
    have hmem : x ∈ C.sset Y ↔ torusCast C.hT x ∈ cubeSet C Y := mem_sset_iff C Y x
    by_cases hx : x ∈ C.sset Y
    · simp only [hx, hmem.1 hx, ↓reduceIte]
      unfold sfLiftK parentPsi sfToBg
      rw [jBlock_bgToFine C]
    · have hx' : torusCast C.hT x ∉ cubeSet C Y := fun h => hx (hmem.2 h)
      simp only [hx, hx', ↓reduceIte, Def6.constFld, hC]
  · have hm0 : 0 ≤ sfBgMassAt S.L (j + 1) ν := by unfold sfBgMassAt physMass; positivity
    have hmL : sfBgMassAt S.L (j + 1) ν * ((S.L : ℝ) ^ (j + 1)) ^ 2 ≤ 1 := by
      rw [show sfBgMassAt S.L (j + 1) ν * ((S.L : ℝ) ^ (j + 1)) ^ 2 = ν from physMass_mul_sq _ _]
      exact hν1
    refine allSitesBounds_of_near le_rfl hm0 hmL he0 he1 hsum (fun x x' hb => ?_) (fun x => ?_)
    · have hiff := cubeSet_block C le_rfl Y hb
      unfold liftExtRe
      by_cases hx : x ∈ cubeSet C Y
      · have hx' := hiff.1 hx
        simp only [hx, hx', ↓reduceIte]
        unfold parentPsi
        rw [hb]
      · have hx' : x' ∉ cubeSet C Y := fun h => hx (hiff.2 h)
        simp only [hx, hx', ↓reduceIte]
    · unfold liftExtRe
      by_cases hx : x ∈ cubeSet C Y
      · simp only [hx, ↓reduceIte]
        have hxd : x ∈ dataSites (C.genW Y) :=
          (mem_dataSites _).2 (Or.inl (mem_genSF_Ω_of_cubeSet C le_rfl (by omega) (W2 R Y)
            (cubeSet_subset_W2 C Y hx)))
        exact (parentPsi_dir_of_chiY_ne_zero C hL Y ψk hv hχ hν hμ hxd).le
      · simp only [hx, ↓reduceIte, sub_self]
        have : rn (fun _ : Fin N => (0 : ℝ)) = 0 := by unfold rn; simp
        rw [this]
        positivity

end Ctx

end Balaban.RootFSpine
