/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseBgClose
public import Balaban.LargeField.Characteristic.Stencil
public import Balaban.Fluctuation.H7Bridge
public import Balaban.Background.GenSetStabilityRestrict
public import Balaban.LargeField.Base.BaseBackgroundIdent

/-!
# The cube generating set inside the global one: geometry and closeness

For the generating set `G_q(□) = genCube □` (the preimage of the `2`-neighbourhood of the cube
`□ = y0` of side `P = L^q c M₁`), the set `Ω_q = cubePre (nbhd 2 {y0})`
(`genCube_Omega_top`). A site of the cube `y0` is at path distance at least `c M₁`
from the shadow of the complement of `Ω₁` (`genCube_far`): the shadow lies in the outer ring of
cubes at index distance `2` from `y0`, and the fine sup-distance between two sites whose cubes are
at index distance `2` is at least `P + 1`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.Fluctuation Balaban.Localization

variable {d M1 N₁ L q : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

/-- The top layer of the cube generating set is the preimage of the `2`-neighbourhood of the cube. -/
theorem genCube_Omega_top {c n : ℕ} [NeZero n] (hm : N₁ * L ^ (q - q) = c * n) (a : Torus d n) :
    (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n a).Ω q =
      cubePre M1 N₁ L q (L ^ q * (c * M1)) n (nbhd 2 {a}) := by
  rw [genCube_Ω, minLayer_self,
    (isCubeUnion_cubePre (M1 := M1) (N₁ := N₁) (L := L) (q := q) (le_refl q) hm
      (nbhd 2 {a})).cubeInterior_eq]

variable {c n : ℕ} [NeZero n]

/-- **A site of the cube is far from the shadow of the complement of `Ω₁`** (`q = 1`): for `x` in
the cube `y0` and `w` in the shadow of the set `W` of sites outside `Ω₁(G_1(□))`, the path
distance is at least `c M₁`. -/
theorem genCube_far (hm : N₁ * L ^ (1 - 1) = c * n) (y0 : Torus d n)
    {x w : Torus d (M1 * N₁ * L ^ 1)} (hx : blockMap (L ^ 1 * (c * M1)) n x = y0)
    {W : Finset (Torus d (M1 * N₁ * L ^ 1))}
    (hW : ∀ z, z ∈ W ↔ z ∉ (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := 1) c n y0).Ω 1)
    (hw : w ∈ shadowN (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := 1) c n y0) W) :
    ENNReal.ofReal ((c * M1 : ℕ) : ℝ) ≤
      (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := 1) c n y0).pathDist x w := by
  set G0 := genCube (M1 := M1) (N₁ := N₁) (L := L) (q := 1) c n y0 with hG0
  have hΩ : G0.Ω 1 = cubePre M1 N₁ L 1 (L ^ 1 * (c * M1)) n (nbhd 2 {y0}) :=
    genCube_Omega_top hm y0
  have hn : M1 * N₁ * L ^ 1 = (L ^ 1 * (c * M1)) * n := cube_fine_eq hm
  have hPpos : 0 < L ^ 1 * (c * M1) := by
    rcases Nat.eq_zero_or_pos (L ^ 1 * (c * M1)) with h0 | h0
    · exfalso
      have : 0 < M1 * N₁ * L ^ 1 := Nat.pos_of_ne_zero (by
        have := NeZero.ne L; have := NeZero.ne M1; have := NeZero.ne N₁; positivity)
      rw [hn, h0] at this; simp at this
    · exact h0
  simp only [shadowN, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  obtain ⟨hwΩ, hcase⟩ := hw
  have hwc : blockMap (L ^ 1 * (c * M1)) n w ∈ nbhd 2 {y0} := by
    have := hwΩ; rw [hΩ, mem_cubePre] at this; exact this
  obtain ⟨y', hy'W, hadj⟩ : ∃ y', y' ∉ G0.Ω 1 ∧ Adj w y' := by
    rcases hcase with h | ⟨y', hy', hadj⟩
    · exact absurd hwΩ ((hW w).1 h)
    · exact ⟨y', (hW y').1 hy', hadj⟩
  have hy'c : blockMap (L ^ 1 * (c * M1)) n y' ∉ nbhd 2 {y0} := by
    intro h; apply hy'W; rw [hΩ, mem_cubePre]; exact h
  have hd1 : supDist w y' ≤ 1 := Balaban.LargeField.Adj.supDist_le_one hadj
  have hd2 : supDist (blockMap (L ^ 1 * (c * M1)) n w) (blockMap (L ^ 1 * (c * M1)) n y') ≤ 1 :=
    supDist_blockMap_le_one (M1 := M1) (N₁ := N₁) (L := L) (q := 1) hn (D := 1)
      hPpos w y' hd1
  have hfar : 2 ≤ supDist (blockMap (L ^ 1 * (c * M1)) n w) y0 := by
    by_contra hlt
    push Not at hlt
    apply hy'c
    rw [mem_nbhd]
    refine ⟨y0, Set.mem_singleton _, ?_⟩
    have t := supDist_triangle (blockMap (L ^ 1 * (c * M1)) n y')
      (blockMap (L ^ 1 * (c * M1)) n w) y0
    have hd3 := (supDist_comm (blockMap (L ^ 1 * (c * M1)) n w)
      (blockMap (L ^ 1 * (c * M1)) n y')).symm ▸ hd2
    omega
  have hfine : L ^ 1 * (c * M1) + 1 ≤ supDist x w := by
    by_contra hlt
    push Not at hlt
    have h1 := supDist_blockMap_le_one (M1 := M1) (N₁ := N₁) (L := L) (q := 1) hn
      (D := L ^ 1 * (c * M1)) le_rfl x w (by omega)
    rw [hx] at h1
    rw [supDist_comm] at hfar
    omega
  have ht : ((L ^ 1 * (c * M1) + 1 : ℕ) : ℝ) ≤ Green.torusDist d (M1 * N₁ * L ^ 1) x w :=
    ((Nat.cast_le.2 hfine).trans (supDist_le_torusDist x w))
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (Balaban.Background.pathDist_ge_torusDist G0 x w)
  have hL0 : (0 : ℝ) < (L : ℝ) ^ 1 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rw [le_div_iff₀ hL0]
  push_cast at ht ⊢
  nlinarith

section Reg

variable {N : ℕ} (a : ℕ → ℝ) (μ δ : ℝ) (h : Fin N → ℝ)

/-- At level one every site of `Ω₁(G)` is in the layer `1` and has spacing `L`. -/
theorem layerIndex_one {ϱ : ℝ} {N₀ : ℕ} [NeZero N₀] (G : GeneratingSet d L N₀ 1 ϱ)
    {x : Torus d (N₀ * L ^ 1)} (hx : x ∈ G.Ω 1) : G.layerIndex x = 1 := by
  have := G.layerIndex_spec hx
  omega

theorem spacing_one {ϱ : ℝ} {N₀ : ℕ} [NeZero N₀] (G : GeneratingSet d L N₀ 1 ϱ)
    {x : Torus d (N₀ * L ^ 1)} (hx : x ∈ G.Ω 1) : G.spacing x = (L : ℝ) := by
  unfold GeneratingSet.spacing
  rw [layerIndex_one G hx, pow_one]

/-- The unpacked regularity predicate of the cube (`q = 1`): the domain, the block deviations on
the sites of `□^{∼1}` and the gradients at the sites of `Ω₁ ∩ □^{∼1}` of the local background. -/
theorem reg_gradClose {c n : ℕ} [NeZero n] (y0 : Torus d n)
    (ψ : BlockCfg d (M1 * N₁) L 1 1 N) (hχ : ChiKProp a μ δ h c n y0 ψ)
    (x : (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := 1) c n y0).Ω 1)
    (hxS : (x : Torus d (M1 * N₁ * L ^ 1)) ∈ cubeNbhd M1 N₁ L 1 c n 1 y0) (ν : Fin d) :
    (L : ℝ) ^ 1 * vn (barVec (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := 1) c n y0)
        (cubeData h c n y0 ψ)
        (bgFieldC (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := 1) c n y0) a μ (bgC0 d L N)
          (cubeData h c n y0 ψ))
        ((x : Torus d (M1 * N₁ * L ^ 1)) + Pi.single ν 1) -
      barVec (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := 1) c n y0) (cubeData h c n y0 ψ)
        (bgFieldC (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := 1) c n y0) a μ (bgC0 d L N)
          (cubeData h c n y0 ψ)) x) < δ :=
  (hχ.2.2.1 x hxS).1 ν |>.1

/-- At level one the block average of the restriction of a field is the block average of the
field. -/
theorem blockAvg_restrict {N₀ : ℕ} [NeZero N₀] {ϱ0 ϱ1 : ℝ} {G0 : GeneratingSet d L N₀ 1 ϱ0}
    {G1 : GeneratingSet d L N₀ 1 ϱ1} (hprec : Precedes G0 G1) (gl : G1.Ω 1 × Fin N → ℂ)
    {x : Torus d (N₀ * L ^ 1)} (hx : x ∈ G0.Ω 1) (i : Fin N) :
    blockAvg G0 (hprec.restrictφ gl) x i = blockAvg G1 gl x i := by
  have hx1 : x ∈ G1.Ω 1 := hprec.mem_Ω1 hx
  have l0 := layerIndex_one G0 hx
  have l1 := layerIndex_one G1 hx1
  unfold blockAvg
  rw [l0, l1]
  congr 1
  refine Finset.sum_congr rfl fun y hy => ?_
  have hyΩ : y ∈ G0.Ω 1 := by
    have h1 := G0.layerIndex_spec hx
    rw [l0] at h1
    exact blk_subset_Ω G0 h1.1 h1.2.1 (by simpa [l0] using h1.2.2)
      (by rw [blk_eq_fibre G0 1 x]; rwa [blk_eq_fibre G1 1 x] at hy)
  rw [svec_of_mem G0 _ ⟨y, hyΩ⟩, svec_of_mem G1 _ ⟨y, hprec.mem_Ω1 hyΩ⟩]
  rfl

end Reg

section Margins

open Classical in
/-- **Bond margins of the global background from the cube test `χ₁(□) = 1`** (first step, `q = 1`).
`G₁` is the global generating set `single` on the torus of side `M₁ N₁`, `D' = lift ψ` its datum,
`gl` its background; `ψ` passes the test `ChiKProp` at tolerance `δ₁` for the cube `y0`. Then for
every bond `(x, x + e_μ)` with `x` in the cube `y0`:
`L |∂_μ gl(x)| < δ₁ + √N ε`, `ε = K_w c_F (2d+2) K₁ δ' e^{-γ_w c M₁}`. -/
theorem cube_margins {N : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {M1 N₁ m₁ c n : ℕ} [NeZero M1] [NeZero N₁] [NeZero n] (_hM1 : M1 = L ^ m₁)
        (_hm : N₁ * L ^ (1 - 1) = c * n) {ϱ1 a₁ ν δ' ε' δ₁ : ℝ} (h : Fin N → ℝ),
        0 < a₁ →
        BgHyp d L 1 (minSep L M1) (compWeight L a₁) ν → BgHyp d L 1 ϱ1 (compWeight L a₁) ν →
        0 ≤ ν → ν * ((L : ℝ) ^ 1) ^ 2 ≤ 1 →
        2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1) →
        bgK1 d L N * bgC1 d L N ≤ min (deltaStar d L N) δw →
        0 < δ' → δ' ≤ ε' → ε' ≤ bgC0 d L N → δ' ≤ thm73C1 d L N →
        ν * ((L : ℝ) ^ 1) ^ 2 * ε' ^ 2 ≤ δ' ^ 2 →
        (2 * d + 2) * (bgK1 d L N * δ') ≤ deltaStar d L N →
        (2 * d + 2) * (bgK1 d L N * δ') ≤ δw →
        ∀ (ψ : BlockCfg d (M1 * N₁) L 1 1 N) (y0 : Torus d n),
        InDomainC (GeneratingSet.single (d := d) (L := L) (N₀ := M1 * N₁) (k := 1) ϱ1) ν δ' ε'
          (liftSingle (GeneratingSet.single (d := d) (L := L) (N₀ := M1 * N₁) (k := 1) ϱ1)
            ψ.toC (fun i => (h i : ℂ))) →
        ChiKProp (compWeight L a₁) ν δ₁ h c n y0 ψ →
        (∀ (x y : Torus d (M1 * N₁ * L ^ 1)) (μ : Fin d),
        blockMap (L ^ 1 * (c * M1)) n x = y0 → y = x + Pi.single μ 1 →
        ∀ (hx : x ∈ (GeneratingSet.single (d := d) (L := L) (N₀ := M1 * N₁) (k := 1) ϱ1).Ω 1)
          (hy : y ∈ (GeneratingSet.single (d := d) (L := L) (N₀ := M1 * N₁) (k := 1) ϱ1).Ω 1),
        (L : ℝ) * vn (fun i =>
          bgFieldC (GeneratingSet.single (d := d) (L := L) (N₀ := M1 * N₁) (k := 1) ϱ1)
            (compWeight L a₁) ν (bgC0 d L N)
            (liftSingle (GeneratingSet.single (d := d) (L := L) (N₀ := M1 * N₁) (k := 1) ϱ1)
              ψ.toC (fun i => (h i : ℂ))) (⟨y, hy⟩, i) -
          bgFieldC (GeneratingSet.single (d := d) (L := L) (N₀ := M1 * N₁) (k := 1) ϱ1)
            (compWeight L a₁) ν (bgC0 d L N)
            (liftSingle (GeneratingSet.single (d := d) (L := L) (N₀ := M1 * N₁) (k := 1) ϱ1)
              ψ.toC (fun i => (h i : ℂ))) (⟨x, hx⟩, i)) <
          δ₁ + Real.sqrt N * (Kw * (cF d L * ((2 * d + 2) * (bgK1 d L N * δ'))) *
            Real.exp (-(gammaW d * ((c * M1 : ℕ) : ℝ))))) ∧
        (∀ (x : Torus d (M1 * N₁ * L ^ 1)),
        blockMap (L ^ 1 * (c * M1)) n x = y0 →
        ∀ (_hx : x ∈ (GeneratingSet.single (d := d) (L := L) (N₀ := M1 * N₁) (k := 1) ϱ1).Ω 1),
        vn (fun i => (ψ (jBlock d L (M1 * N₁) 1 1 x) i : ℂ) -
          blockAvg (GeneratingSet.single (d := d) (L := L) (N₀ := M1 * N₁) (k := 1) ϱ1)
            (bgFieldC (GeneratingSet.single (d := d) (L := L) (N₀ := M1 * N₁) (k := 1) ϱ1)
              (compWeight L a₁) ν (bgC0 d L N)
              (liftSingle (GeneratingSet.single (d := d) (L := L) (N₀ := M1 * N₁) (k := 1) ϱ1)
                ψ.toC (fun i => (h i : ℂ)))) x i) <
          δ₁ + Real.sqrt N * (Kw * (cF d L * ((2 * d + 2) * (bgK1 d L N * δ'))) *
            Real.exp (-(gammaW d * ((c * M1 : ℕ) : ℝ))))) := by
  obtain ⟨Kw, δw, hK, hδw, hmar⟩ := bgField_nested_margins (N := N) hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro M1 N₁ m₁ c n _ _ _ hM1 hm ϱ1 a₁ ν δ' ε' δ₁ h ha₁ H0 H1 hν0 hνle hsep hKs hδ0' hδε' hε' hδc
    hνε' hK1' hKw' ψ y0 hD' hχ
  set G0 := genCube (M1 := M1) (N₁ := N₁) (L := L) (q := 1) c n y0 with hG0
  set G1 := GeneratingSet.single (d := d) (L := L) (N₀ := M1 * N₁) (k := 1) ϱ1 with hG1
  set D' := liftSingle G1 ψ.toC (fun i => (h i : ℂ)) with hD'def
  set D := cubeData h c n y0 ψ with hDdef
  have hN : M1 * N₁ = N₁ * L ^ m₁ := by rw [hM1, mul_comm]
  have hΩ1 : G1.Ω 1 = Finset.univ := single_Ω_one le_rfl
  have hprec : Precedes G0 G1 := fun i hi1 hik z _ => by
    have : i = 1 := by omega
    subst this
    rw [hΩ1]; exact Finset.mem_univ _
  have hdsG1 : ∀ z, z ∈ dataSites G1 := fun z =>
    (mem_dataSites G1).2 (Or.inl (by rw [hΩ1]; exact Finset.mem_univ z))
  have hΨ : ∀ z ∈ dataSites G0, D.Ψ z = D'.Ψ z := fun z hz => by
    rw [hDdef, cubeData, liftSingle_Ψ _ _ _ hz, hD'def, liftSingle_Ψ _ _ _ (hdsG1 z)]
  have hh : ∀ z ∈ G0.Ω 1, D.h z = D'.h z := fun z hz => by
    rw [hDdef, cubeData, liftSingle_h _ _ _ hz, hD'def,
      liftSingle_h _ _ _ (by rw [hΩ1]; exact Finset.mem_univ z)]
  have hd0 : 0 < d := by omega
  obtain ⟨δR, hδR0, hδR1, hDR⟩ := hχ.1
  have hDC : InDomainC G0 ν δR δR D := inDomainC_of_inDomainR hδR0 hDR
  have hεR : δR ≤ bgC0 d L N := hδR1.trans (bgC1_le_bgC0 d L N hd0)
  have hνεR : ν * ((L : ℝ) ^ (0 + 1)) ^ 2 * δR ^ 2 ≤ δR ^ 2 := by
    have : ν * ((L : ℝ) ^ (0 + 1)) ^ 2 ≤ 1 := by simpa using hνle
    nlinarith [sq_nonneg δR]
  have hK1R : bgK1 d L N * δR ≤ min (deltaStar d L N) δw :=
    (mul_le_mul_of_nonneg_left hδR1 (bgK1_pos d L N).le).trans hKs
  have hE : ∀ z ∈ ((G0.Ω 1 : Finset _) : Set (Torus d (M1 * N₁ * L ^ 1))), ∀ m, 1 ≤ m → m ≤ 0 + 1 →
      (z ∈ G0.Ω m ↔ z ∈ G1.Ω m) := by
    intro z hz m hm1 hm2
    have : m = 1 := by omega
    subst this
    exact ⟨fun _ => by rw [hΩ1]; exact Finset.mem_univ z, fun _ => hz⟩
  obtain ⟨hbond, hblock⟩ := hmar (N₁ := N₁) (m₁ := m₁) hN (G0 := G0) (G1 := G1) ha₁ H0 H1 hν0
    (by simpa using hνle) hsep hprec hδ0' hδε' hε' hδc (by simpa using hνε') hD' hΨ hh hδR0 le_rfl
    hεR hδR1 hνεR hDC (hK1R.trans (min_le_left _ _)) (hK1R.trans (min_le_right _ _)) hK1' hKw' hE
    (Dist := ((c * M1 : ℕ) : ℝ))
  have hPpos : 0 < L ^ 1 * (c * M1) := by
    rcases Nat.eq_zero_or_pos (L ^ 1 * (c * M1)) with h0 | h0
    · exfalso
      have hn : M1 * N₁ * L ^ 1 = (L ^ 1 * (c * M1)) * n := cube_fine_eq hm
      have : 0 < M1 * N₁ * L ^ 1 := Nat.pos_of_ne_zero (by
        have := NeZero.ne L; have := NeZero.ne M1; have := NeZero.ne N₁; positivity)
      rw [hn, h0] at this; simp at this
    · exact h0
  have hn : M1 * N₁ * L ^ 1 = (L ^ 1 * (c * M1)) * n := cube_fine_eq hm
  have hΩtop : G0.Ω 1 = cubePre M1 N₁ L 1 (L ^ 1 * (c * M1)) n (nbhd 2 {y0}) :=
    genCube_Omega_top hm y0
  refine ⟨fun x y μ hx0 hy hx hy' => ?_, fun x hx0 hx => ?_⟩
  ·   have hxΩ : x ∈ G0.Ω 1 := by
        rw [hΩtop, mem_cubePre, hx0, mem_nbhd]; exact ⟨y0, Set.mem_singleton _, by simp [supDist_self]⟩
      have hyΩ : y ∈ G0.Ω 1 := by
        rw [hΩtop, mem_cubePre, mem_nbhd]
        refine ⟨y0, Set.mem_singleton _, ?_⟩
        have h1 : supDist x y ≤ 1 := by
          rw [hy, supDist_comm]
          exact Balaban.LargeField.Adj.supDist_le_one ⟨μ, Or.inr rfl⟩
        have h2 := supDist_blockMap_le_one (M1 := M1) (N₁ := N₁) (L := L) (q := 1) hn (D := 1) hPpos
          x y h1
        rw [hx0] at h2
        have h3 := supDist_triangle (blockMap (L ^ 1 * (c * M1)) n y) y0 y0
        rw [supDist_comm] at h2
        simp [supDist_self] at h3
        omega
      have key := hbond ⟨x, hxΩ⟩ ⟨y, hyΩ⟩ μ hy
        (fun w hw => by
          refine genCube_far (d := d) (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) hm y0
            (x := x) (w := w) hx0 ?_ hw
          intro z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe]
          exact Iff.rfl)
      have hreg := reg_gradClose (compWeight L a₁) ν δ₁ h y0 ψ hχ ⟨x, hxΩ⟩
        (by unfold cubeNbhd; rw [mem_cubePre, hx0, mem_nbhd]; exact ⟨y0, Set.mem_singleton _, by simp [supDist_self]⟩) μ
      have hsp : G0.spacing x = (L : ℝ) := spacing_one G0 hxΩ
      have hbar : (barVec G0 D (bgFieldC G0 (compWeight L a₁) ν (bgC0 d L N) D)
            ((x : Torus d (M1 * N₁ * L ^ 1)) + Pi.single μ 1) -
          barVec G0 D (bgFieldC G0 (compWeight L a₁) ν (bgC0 d L N) D) x) =
          fun i => bgFieldC G0 (compWeight L a₁) ν (bgC0 d L N) D (⟨y, hyΩ⟩, i) -
            bgFieldC G0 (compWeight L a₁) ν (bgC0 d L N) D (⟨x, hxΩ⟩, i) := by
        funext i
        simp only [Pi.sub_apply, barVec, barField, ← hy, hxΩ, hyΩ, dite_true]
      rw [hbar, pow_one] at hreg
      rw [hsp] at key
      calc (L : ℝ) * _ ≤ _ := key
        _ < _ := by linarith
  · have hxΩ : x ∈ G0.Ω 1 := by
      rw [hΩtop, mem_cubePre, hx0, mem_nbhd]; exact ⟨y0, Set.mem_singleton _, by simp [supDist_self]⟩
    have hcube : ∀ z ∈ G0.blk (G0.layerIndex x) x, blockMap (L ^ 1 * (c * M1)) n z = y0 := by
      intro z hz
      rw [layerIndex_one G0 hxΩ, blk_eq_fibre, mem_blockFibre] at hz
      have hℓ : M1 * N₁ * L ^ 1 = L ^ 1 * (M1 * N₁ * L ^ (1 - 1)) := by simp [pow_one]; ring
      have hm' : M1 * N₁ * L ^ (1 - 1) = (c * M1) * n := by
        have : N₁ = c * n := by simpa using hm
        rw [this]; simp; ring
      have e1 := blockMap_comp (d := d) (ℓ := M1 * N₁ * L ^ 1) (N := L ^ 1)
        (m₁ := M1 * N₁ * L ^ (1 - 1)) (m₂ := n) (M := c * M1) hℓ hm' z
      have e2 := blockMap_comp (d := d) (ℓ := M1 * N₁ * L ^ 1) (N := L ^ 1)
        (m₁ := M1 * N₁ * L ^ (1 - 1)) (m₂ := n) (M := c * M1) hℓ hm' x
      have hx0' := hx0
      rw [← e2] at hx0'
      rw [← e1, ← hx0']
      exact congrArg _ hz
    have key := (hblock x hxΩ (fun y hy hyΩ w hw => by
      refine genCube_far (d := d) (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) hm y0
        (x := y) (w := w) (hcube y hy) ?_ hw
      intro z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe]
      exact Iff.rfl))
    have hreg := hχ.2.1 x (by unfold cubeNbhd; rw [mem_cubePre, hx0, mem_nbhd]; exact ⟨y0, Set.mem_singleton _, by simp [supDist_self]⟩)
    have hΨx : D.Ψ x = fun i => (ψ (jBlock d L (M1 * N₁) 1 1 x) i : ℂ) := by
      funext i
      rw [hDdef, cubeData, liftSingle_Ψ _ _ _ ((mem_dataSites G0).2 (Or.inl hxΩ))]
      rfl
    have hrestr : ∀ i, blockAvg G0 (hprec.restrictφ
        (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D')) x i =
        blockAvg G1 (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') x i :=
      fun i => blockAvg_restrict hprec _ hxΩ i
    simp only [hrestr] at key
    have hΨi : ∀ i, D.Ψ x i = (ψ (jBlock d L (M1 * N₁) 1 1 x) i : ℂ) := fun i => by rw [hΨx]
    simp only [hΨi] at key
    have hreg' : vn (fun i => (ψ (jBlock d L (M1 * N₁) 1 1 x) i : ℂ) -
        blockAvg G0 (bgFieldC G0 (compWeight L a₁) ν (bgC0 d L N) D) x i) < δ₁ := by
      have := hreg
      unfold blockDev at this
      have hΨi' : ∀ i, (cubeData h c n y0 ψ).Ψ x i = (ψ (jBlock d L (M1 * N₁) 1 1 x) i : ℂ) := hΨi
      simpa only [hΨi'] using this
    exact lt_of_le_of_lt key (by linarith)

end Margins



end Balaban.LargeField.Base
