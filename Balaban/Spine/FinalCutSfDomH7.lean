/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalCutSfDomNum
public import Balaban.Spine.FinalBoxLocChi
public import Balaban.LargeField.Characteristic.Analytic
public import Balaban.LargeField.Characteristic.Stencil
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The top-level cube domains of the H7 domain on the region tested by `χ_k(Y)`

A6-4 (`LFH7SupportInput`, the top-level part). The H7 domain of a boundary domain `X`
(Definition II.3.5 (d), `H7Domain`) asks at the level `k`, for the cubes `□ ⊂ X` away from
`(Ω^c_k)^{∼3}`, that the level-`k` field lie in the cube domain `Δ^c_k(□; 1, ε_k)` (`DeltaC`, (1.36)
of the first kind). At a late scale the characteristic function `χ_k(Y)` tests the datum against
`h` on `□₀^{∼ρ}` for every `□₀ ∈ Y` (the direction stencil, `ρ = 2 ⌊R_{k-1}⌋ + 3`). Hence every cube
`□` within `2 ⌊R_{k-1}⌋` of `Y` has all the data sites of `G_k(□) = 𝔹_k(□^{∼2})` within
`δ_k / √ν` of `h`, and `Δ^c_k(□; 1, ε)` holds once `(3 K₁ + 1) δ_k / √ν < ε`:

* `liftData_mem_deltaC_of_chiY`: for `χ_k(Y)(ψ_k) ≠ 0` and every cube `□ ∈ nbhd (2 ⌊R_{k-1}⌋) Y`, the
  level-`k` field `lift ψ_k` lies in `Δ^c_k(□; 1, ε)` at the weights and the cube mass of `χ_k`
  (the real domain of `G_k(□)` from `inPsiTilde_of_near`, the regularity from
  `reg_of_inDomainR_near`, the complex domain `Ψ̃^c(G_k(□); ε, ε)` of ruling R14 from the real one
  with zero perturbations, `DataWit.ofReal`);
* `liftData_mem_deltaC_of_numerics`: the same from the smallness `cutGamma δ_k / √ν ≤ min (c, ε)`.

The cubes of `X` farther inside the large-field region, the levels `j < k`, the step pairs of
(1.36) of the second kind and the fluctuation fields of (1.37) are not tested by `χ_k(Y)`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField
  Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Localization

namespace Balaban.RootFSpine

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N (j + 1) m₁ ϱ)
  (hv : EuclideanSpace ℝ (Fin N)) (Y : Set (Torus S.d (n (j + 1))))
  (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))

/-- **The top-level cube domain on the tested region** ((1.36) of the first kind at the level `k`):
if `χ_k(Y)(ψ_k) ≠ 0` at a cube mass `ν L^{-2k}`, `ν > 0`, then for every cube `□` within
`2 ⌊R_{k-1}⌋` of `Y` the level-`k` field `lift ψ_k` lies in `Δ^c_k(□; 1, ε)` at the weights and the
mass of `χ_k`, for `3 δ_k / √ν ≤ c₁`, `δ_k / √ν ≤ 1` and `K₁ · 3 δ_k / √ν + δ_k / √ν < ε`. -/
theorem liftData_mem_deltaC_of_chiY (hL : 2 ≤ S.L)
    (H : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.mu (j + 1)))
    {ν : ℝ} (hν : 0 < ν) (hunit : ‖hv‖ = 1) (hδ : 0 < C.cs.delta (j + 1))
    (hμ : C.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (he1 : C.cs.delta (j + 1) / Real.sqrt ν ≤ 1)
    (hη : 3 * (C.cs.delta (j + 1) / Real.sqrt ν) ≤ bgC1 S.d S.L N) {ε : ℝ}
    (hε : bgK1 S.d S.L N * (3 * (C.cs.delta (j + 1) / Real.sqrt ν)) +
      C.cs.delta (j + 1) / Real.sqrt ν < ε)
    (hχ : C.chiY Y ψk hv ≠ 0) {y0 : Torus S.d (n (j + 1))} (hy0 : y0 ∈ nbhd (2 * ⌊R j⌋₊) Y) :
    C.liftData ψk ∈ DeltaC (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L)
      (q := j + 1) C.weights (C.cs.mu (j + 1)) ε (hC hv) C.geo.c (n (j + 1)) y0 := by
  classical
  set e : ℝ := C.cs.delta (j + 1) / Real.sqrt ν with he
  have he0 : 0 < e := div_pos hδ (Real.sqrt_pos.2 hν)
  have hsum : ∑ i, hv i ^ 2 = 1 := by rw [parent_sum_sq_eq_norm_sq, hunit]; norm_num
  have hmL : C.cs.mu (j + 1) * ((S.L : ℝ) ^ (j + 1)) ^ 2 = ν := by
    rw [hμ]; exact physMass_mul_sq _ _
  set G := genCube (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
    C.geo.c (n (j + 1)) y0 with hG
  set cfg := blockCfgOf C.geo C.hnn le_rfl C.hkK ψk with hcfg
  -- the direction test of a cube of `Y` within `2 ⌊R_{k-1}⌋` of `□`
  obtain ⟨y₁, hy₁, hd⟩ := mem_nbhd.1 hy0
  have hy₁' : y₁ ∈ cubeFin Y := by simp [cubeFin, hy₁]
  have hD := dataDirClose_of_chiY_ne_zero C Y ψk hv hχ hy₁'
  rw [hmL] at hD
  -- every data site of `G_k(□)` is within `δ_k / √ν` of `h`
  have hnear : ∀ s ∈ dataSites G, rn (fun i => blockLift (j + 1) cfg s i - hv i) < e := by
    intro s hs
    have hc : 12 * C.geo.M1 ≤ C.geo.c * C.geo.M1 :=
      Nat.mul_le_mul_right _ (by have := C.geo.hc; omega)
    have hP : C.geo.M1 * (C.geo.c * n (j + 1)) * S.L ^ (j + 1) =
        (S.L ^ (j + 1) * (C.geo.c * C.geo.M1)) * n (j + 1) := by ring
    obtain ⟨y, hy, hdy⟩ := dataSites_cube_near (j := j + 1) (q := j + 1) hL (le_refl _)
      (cubePre C.geo.M1 (C.geo.c * n (j + 1)) S.L (j + 1)
        (S.L ^ (j + 1) * (C.geo.c * C.geo.M1)) (n (j + 1)) (nbhd 2 {y0}))
      (G' := G) (fun z hz => hz) (M := C.geo.c * C.geo.M1) hc hP hs
    obtain ⟨y0', hy0', hd2⟩ := mem_nbhd.1 (mem_cubePre.1 hy)
    rw [Set.mem_singleton_iff] at hy0'
    subst hy0'
    have hsx : s ∈ cubeNbhd C.geo.M1 (C.geo.c * n (j + 1)) S.L (j + 1) C.geo.c (n (j + 1))
        (dirRadius R (j + 1)) y₁ := by
      refine mem_cubePre.2 (mem_nbhd.2 ⟨y₁, rfl, ?_⟩)
      have t1 := supDist_triangle
        (blockMap (S.L ^ (j + 1) * (C.geo.c * C.geo.M1)) (n (j + 1)) s)
        (blockMap (S.L ^ (j + 1) * (C.geo.c * C.geo.M1)) (n (j + 1)) y) y₁
      have t2 := supDist_triangle
        (blockMap (S.L ^ (j + 1) * (C.geo.c * C.geo.M1)) (n (j + 1)) y) y0' y₁
      unfold dirRadius
      simp only [Nat.add_sub_cancel]
      omega
    have key := (hD hν).1 s hsx
    have e1 : (fun i => ((cfg (jBlock S.d S.L (C.geo.M1 * (C.geo.c * n (j + 1))) (j + 1) (j + 1)
        s) i : ℝ) : ℂ) - ((hv i : ℝ) : ℂ)) =
        fun i => (((blockLift (j + 1) cfg s i - hv i : ℝ)) : ℂ) := by
      funext i; push_cast; rfl
    rw [e1, vn_ofReal] at key
    exact key
  -- the datum of `G_k(□)` in the real domain
  have hP : InPsiTilde G (C.cs.mu (j + 1)) (3 * e) (blockLift (j + 1) cfg) (fun i => hv i) :=
    inPsiTilde_of_near hsum (liftSingle_layerConst G cfg) H.mass H.massLe he0 he1 hnear
  have hDR : InDomainR G (C.cs.mu (j + 1)) (3 * e) (liftSingle G (C.liftData ψk) (hC hv)) :=
    ⟨blockLift (j + 1) cfg, fun i => hv i, hP,
      fun x hx i => by
        simp [liftSingle_Ψ G _ _ hx, blockLift, SFCtx.liftData, BlockCfg.toC, hcfg],
      fun x hx i => by simp [liftSingle_h G _ _ hx, hC]⟩
  have hS := cubeNbhd_one_subset (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L)
    (q := j + 1) (c := C.geo.c) (n := n (j + 1)) (by simp) y0
  have hdata : ∀ x ∈ cubeNbhd C.geo.M1 (C.geo.c * n (j + 1)) S.L (j + 1) C.geo.c (n (j + 1)) 1 y0,
      vn (fun i => (liftSingle G (C.liftData ψk) (hC hv)).Ψ x i -
        (liftSingle G (C.liftData ψk) (hC hv)).h x i) ≤ e := by
    intro x hx
    have hxΩ : x ∈ G.Ω 1 := G.Ω_antitone le_rfl (by omega) (by omega) (hS x hx)
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hxΩ)
    have e1 : (fun i => (liftSingle G (C.liftData ψk) (hC hv)).Ψ x i -
        (liftSingle G (C.liftData ψk) (hC hv)).h x i) =
        fun i => (((blockLift (j + 1) cfg x i - hv i : ℝ)) : ℂ) := by
      funext i
      rw [liftSingle_Ψ G _ _ hxd, liftSingle_h G _ _ hxΩ]
      simp [blockLift, SFCtx.liftData, BlockCfg.toC, hcfg, hC]
    rw [e1, vn_ofReal]
    exact (hnear x hxd).le
  have hunit' : ∀ x ∈ cubeNbhd C.geo.M1 (C.geo.c * n (j + 1)) S.L (j + 1) C.geo.c (n (j + 1)) 1 y0,
      ∑ i, (liftSingle G (C.liftData ψk) (hC hv)).h x i *
        (liftSingle G (C.liftData ψk) (hC hv)).h x i = 1 := by
    intro x hx
    have hxΩ : x ∈ G.Ω 1 := G.Ω_antitone le_rfl (by omega) (by omega) (hS x hx)
    rw [liftSingle_h G _ _ hxΩ]
    have : ∑ i, hv i * hv i = 1 := by simpa [sq] using hsum
    simp only [hC]
    exact_mod_cast this
  have hReg := reg_of_inDomainR_near H (by omega) (by positivity) hη he0.le hε hDR _ hS hdata
    hunit'
  have h3e : 3 * e ≤ ε := by
    have hK1 := bgK1_ge_one S.d S.L N
    nlinarith [mul_nonneg (sub_nonneg.2 hK1) he0.le]
  obtain ⟨Ψ, h₀, hP', hΨ, hh⟩ := hDR
  have hε0 : 0 < ε := by linarith
  have W := DataWit.ofReal hε0 hε0 (hP'.mono (by positivity) h3e)
    (liftSingle G (C.liftData ψk) (hC hv)) hΨ hh
  exact ⟨⟨W.Ψ, W.h₀, W.Ψ', W.h', W.P, W.hΨ, W.hh⟩, hReg.2⟩

/-- **The top-level cube domain on the tested region, from the smallness of the tolerance**: as
`liftData_mem_deltaC_of_chiY`, for `cutGamma δ_k / √ν ≤ min (deltaCap, ε)`. -/
theorem liftData_mem_deltaC_of_numerics (hL : 2 ≤ S.L)
    (H : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.mu (j + 1)))
    {ν : ℝ} (hν : 0 < ν) (hunit : ‖hv‖ = 1) (hδ : 0 < C.cs.delta (j + 1))
    (hμ : C.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν) {ε : ℝ}
    (hnum : cutGamma S.d S.L N * (C.cs.delta (j + 1) / Real.sqrt ν) ≤ deltaCap S.d S.L N)
    (hnumε : cutGamma S.d S.L N * (C.cs.delta (j + 1) / Real.sqrt ν) ≤ ε)
    (hχ : C.chiY Y ψk hv ≠ 0) {y0 : Torus S.d (n (j + 1))} (hy0 : y0 ∈ nbhd (2 * ⌊R j⌋₊) Y) :
    C.liftData ψk ∈ DeltaC (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L)
      (q := j + 1) C.weights (C.cs.mu (j + 1)) ε (hC hv) C.geo.c (n (j + 1)) y0 := by
  set e : ℝ := C.cs.delta (j + 1) / Real.sqrt ν with he
  have he0 : 0 < e := div_pos hδ (Real.sqrt_pos.2 hν)
  have hK1 := bgK1_ge_one S.d S.L N
  have hd0 : 0 < S.d := by have := H.hd; omega
  have hcg : 32 * ((3 * bgK1 S.d S.L N + 1) * e) ≤ cutGamma S.d S.L N * e := by
    have h1 : 32 * (3 * bgK1 S.d S.L N + 1) ≤ cutGamma S.d S.L N := by unfold cutGamma; nlinarith
    have := mul_le_mul_of_nonneg_right h1 he0.le
    linarith
  have hcap1 : cutGamma S.d S.L N * e ≤ 1 :=
    hnum.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hcapT : cutGamma S.d S.L N * e ≤ thm73C1 S.d S.L N :=
    hnum.trans ((min_le_left _ _).trans (min_le_right _ _))
  have he1 : e ≤ 1 := by nlinarith
  have h3eT : 3 * e ≤ thm73C1 S.d S.L N := by nlinarith
  have h3e1 : 3 * e ≤ bgC1 S.d S.L N :=
    (thm73_small (L := S.L) (N := N) hd0 (by positivity) h3eT).1
  refine liftData_mem_deltaC_of_chiY C hv Y ψk hL H hν hunit hδ hμ he1 h3e1 ?_ hχ hy0
  nlinarith

end Ctx

end Balaban.RootFSpine
