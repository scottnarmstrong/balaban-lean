/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BPrimeCubeLoc
public import Balaban.LargeField.R.RegionalBoundArith
public import Balaban.Multiscale.ConstraintLocality

/-!
# The cube roots of the residual of `R`: the bound

The root of a cube is bounded in terms of a bound `B` of the fields it reads: `|φ̄| ≤ B`, the data on
the blocks of the cube `≤ B`, and the composed fields `|ψ^{(j)}| ≤ B` with `|ψ^{(j)}·ψ^{(j)} - 1| ≤ 1/2`
at the sites of the cube in `Y^≈` (so that `|(ψ^{(j)})₀| ≤ 10 B / 7`).  The bound is local: it counts
the sites and blocks of the cube.

* `vn_bavgL_le`: the block average of bounded fields is bounded;
* `norm_actionGWithCube_le`, `norm_starBondEWithCube_le`: the action of a class of a partition;
* `SFCtx.norm_cubeRoot_le`, `SFCtx.norm_cubePair_le`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.GsSpec

section Vn

variable {N : ℕ}

theorem norm_dot_self_le (v : Fin N → ℂ) : ‖SmallField.dot v v‖ ≤ vn v ^ 2 := by
  have := norm_dot_le v v
  unfold SmallField.dot
  nlinarith [vn_nonneg v]

theorem norm_dot_le_vn (v w : Fin N → ℂ) : ‖SmallField.dot v w‖ ≤ vn v * vn w :=
  norm_dot_le v w

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L]

/-- **The block average of fields bounded by `B` is bounded by `B`.** -/
theorem vn_bavgL_le {φ : Site d L N₀ q → Fin N → ℂ} {B : ℝ} (hφ : ∀ x, vn (φ x) ≤ B) {m : ℕ}
    (hm : m ≤ q) (y : Blk d L N₀ q m) : vn (bavgL d L N₀ q m φ y) ≤ B := by
  unfold bavgL bavg
  have hLm : (0 : ℝ) < ((L ^ m : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((L ^ m : ℕ) : ℝ) := by exact_mod_cast pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
    positivity
  have hside : N₀ * L ^ q = L ^ m * (N₀ * L ^ (q - m)) := by
    have e : L ^ q = L ^ m * L ^ (q - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
    rw [e]
    ring
  have hcard := card_blockFibre (d := d) hside y
  have hsm : (((((L ^ m : ℕ) : ℝ)) ^ d)⁻¹ • ∑ x ∈ blockFibre (L ^ m) (N₀ * L ^ (q - m)) y, φ x :
      Fin N → ℂ) = fun i => ((((((L ^ m : ℕ) : ℝ)) ^ d)⁻¹ : ℝ) : ℂ) *
        (∑ x ∈ blockFibre (L ^ m) (N₀ * L ^ (q - m)) y, φ x) i := by
    funext i
    simp [Complex.real_smul]
  rw [hsm, Background.vn_smul_real]
  have hs : vn (∑ x ∈ (blockFibre (L ^ m) (N₀ * L ^ (q - m)) y : Finset (Site d L N₀ q)), φ x) ≤
      ∑ x ∈ (blockFibre (L ^ m) (N₀ * L ^ (q - m)) y : Finset (Site d L N₀ q)), vn (φ x) := by
    have := Background.vn_sum_le
      (blockFibre (L ^ m) (N₀ * L ^ (q - m)) y : Finset (Site d L N₀ q)) φ
    have e : (∑ x ∈ (blockFibre (L ^ m) (N₀ * L ^ (q - m)) y : Finset (Site d L N₀ q)), φ x) =
        fun i => ∑ x ∈ (blockFibre (L ^ m) (N₀ * L ^ (q - m)) y : Finset (Site d L N₀ q)), φ x i := by
      funext i; simp [Finset.sum_apply]
    rw [e]; exact this
  have hs2 : ∑ x ∈ (blockFibre (L ^ m) (N₀ * L ^ (q - m)) y : Finset (Site d L N₀ q)), vn (φ x) ≤
      ((L ^ m : ℕ) : ℝ) ^ d * B := by
    calc _ ≤ ∑ _x ∈ (blockFibre (L ^ m) (N₀ * L ^ (q - m)) y : Finset (Site d L N₀ q)), B :=
          Finset.sum_le_sum fun x _ => hφ x
      _ = _ := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring
  rw [abs_of_pos (inv_pos.2 (by exact_mod_cast hLm))]
  calc ((((L ^ m : ℕ) : ℝ)) ^ d)⁻¹ * vn (∑ x ∈ blockFibre (L ^ m) (N₀ * L ^ (q - m)) y, φ x)
      ≤ ((((L ^ m : ℕ) : ℝ)) ^ d)⁻¹ * (((L ^ m : ℕ) : ℝ) ^ d * B) :=
        mul_le_mul_of_nonneg_left (hs.trans hs2) (inv_pos.2 hLm).le
    _ = B := by field_simp

end Vn

section Action

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {β : Type*} [DecidableEq β]
  (cs : Site d L N₀ q → β) (cb : ∀ m, Blk d L N₀ q m → β)

/-- **The bound of the action of a class of a partition**: the block terms of the blocks of the class,
the bonds of its sites and the mass terms of its sites, for fields bounded by `B`. -/
theorem norm_actionGWithCube_le (G : GeneratingSet d L N₀ q ϱ) (a : ℕ → ℝ) (μ : ℝ)
    (h : Fin N → ℂ) (X : Finset (Site d L N₀ q)) (c : β)
    (ψ : (m : ℕ) → Blk d L N₀ q m → Fin N → ℂ) (φ : Site d L N₀ q → Fin N → ℂ) {B : ℝ}
    (hψ : ∀ m ∈ Finset.Icc 1 q, ∀ y ∈ tBlocks d L N₀ q m (lam G m ∩ X), vn (ψ m y) ≤ B)
    (hφ : ∀ x, vn (φ x) ≤ B) :
    ‖actionGWithCube cs cb (fun v => SmallField.dot v v) G a μ h X ψ φ c‖ ≤
      1 / 2 * ∑ m ∈ Finset.Icc 1 q, ∑ _y ∈ (tBlocks d L N₀ q m (lam G m ∩ X)).filter
          (fun y => cb m y = c), |a m * (L : ℝ) ^ (m * (d - 2))| * (2 * B) ^ 2 +
        1 / 2 * ∑ _ν : Fin d, ∑ _x ∈ (Finset.univ : Finset (Site d L N₀ q)).filter
          (fun x => cs x = c), (2 * B) ^ 2 +
        |μ| / 2 * ∑ _x ∈ X.filter (fun x => cs x = c), (B + vn h) ^ 2 := by
  classical
  have hB : 0 ≤ B := (vn_nonneg _).trans (hφ (0 : Site d L N₀ q))
  have hsq : ∀ v : Fin N → ℂ, ∀ b : ℝ, vn v ≤ b → ‖SmallField.dot v v‖ ≤ b ^ 2 := fun v b hv =>
    (norm_dot_self_le v).trans (pow_le_pow_left₀ (vn_nonneg v) hv 2)
  have hbond : ∀ (ν : Fin d) (x : Site d L N₀ q),
      ‖bondTermWith (fun v => SmallField.dot v v) φ ν x‖ ≤ (2 * B) ^ 2 := fun ν x =>
    hsq _ _ ((Multiscale.vn_sub_le _ _).trans (by linarith [hφ (x + Pi.single ν 1), hφ x]))
  unfold actionGWithCube
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [norm_mul, show ‖(algebraMap ℝ ℂ (1 / 2))‖ = 1 / 2 by simp]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun y hy => ?_))) (by norm_num)
    rw [norm_mul, show ‖(algebraMap ℝ ℂ (a m * (L : ℝ) ^ (m * (d - 2))))‖ =
      |a m * (L : ℝ) ^ (m * (d - 2))| by simp]
    refine mul_le_mul_of_nonneg_left (hsq _ _ ((Multiscale.vn_sub_le _ _).trans ?_)) (abs_nonneg _)
    have h1 := hψ m hm y (Finset.mem_filter.1 hy).1
    have h2 := vn_bavgL_le hφ (Finset.mem_Icc.1 hm).2 y
    linarith
  · rw [norm_mul, show ‖(algebraMap ℝ ℂ (1 / 2))‖ = 1 / 2 by simp]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_))) (by norm_num)
    split_ifs
    · exact hbond ν x
    · simp only [norm_zero]; positivity
  · rw [norm_mul, show ‖(algebraMap ℝ ℂ (μ / 2))‖ = |μ| / 2 by simp]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ =>
      hsq _ _ ((Multiscale.vn_sub_le _ _).trans (by linarith [hφ x])))) (by positivity)

/-- **The bound of the star bonds of a class.** -/
theorem norm_starBondEWithCube_le (X : Finset (Site d L N₀ q)) (c : β)
    (φ : Site d L N₀ q → Fin N → ℂ) {B : ℝ} (hφ : ∀ x, vn (φ x) ≤ B) :
    ‖starBondEWithCube cs (fun v => SmallField.dot v v) X φ c‖ ≤
      ∑ _ν : Fin d, ∑ _x ∈ (Finset.univ : Finset (Site d L N₀ q)).filter (fun x => cs x = c),
        (2 * B) ^ 2 := by
  classical
  unfold starBondEWithCube
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_))
  split_ifs
  · exact (norm_dot_self_le _).trans (pow_le_pow_left₀ (vn_nonneg _)
      ((Multiscale.vn_sub_le _ _).trans (by linarith [hφ (x + Pi.single ν 1), hφ x])) 2)
  · simp only [norm_zero]; positivity

end Action

namespace Def7.SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (Y : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N))

/-- The coefficient of the `ψ·ψ` part of the corrections of level `j` at the site `s`. -/
noncomputable def coefE (vc : Def7v2.CorrCoef S.d) (j : ℕ)
    (s : Localization.CTorus S.d S.L C.N₁ m₁ k) : ℂ :=
  corrCoefSite (fun y x => vc.v1 j (Def6.unlift j (x - y))) (C.alignedIn j Y)
    (C.alignedIn j (thickY R Y)) s

/-- The coefficient of the `h·ψ₀` part of the corrections of level `j` at the site `s`. -/
noncomputable def coefM (vc : Def7v2.CorrCoef S.d) (j : ℕ)
    (s : Localization.CTorus S.d S.L C.N₁ m₁ k) : ℂ :=
  corrCoefSite (fun y x => vc.v2 j (Def6.unlift j (x - y))) (C.alignedIn j Y)
    (C.alignedIn j (thickY R Y)) s

/-- The unit direction of a vector near the unit sphere is bounded by `10/7` of the vector. -/
theorem vn_unitDirC_le {v : Fin N → ℂ} (hv1 : ‖SmallField.dot v v - 1‖ ≤ 1 / 2) :
    vn (Def7v2.unitDirC v) ≤ 10 / 7 * vn v := by
  unfold Def7v2.unitDirC vn
  rw [WithLp.toLp_smul, norm_smul, norm_inv]
  have h := RegionalArith.sqrtC_norm_ge hv1
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact inv_le_of_inv_le₀ (by norm_num) (by linarith)

open Classical in
/-- **The bound of the root of a cube** for fields bounded by `B`: the action of the cube, its
corrections and its source term, with the sites and blocks of the cube counted. -/
noncomputable def cubeBound (vc : Def7v2.CorrCoef S.d) (g : GIdx S n M K N → ℂ)
    (c : Torus S.d (n k)) (B : ℝ) : ℝ :=
  |(betaCanon S.d S.L (C.sf.β k) k 0 : ℝ)| *
    (1 / 2 * ∑ m ∈ Finset.Icc 1 k, ∑ _y ∈ (tBlocks S.d S.L (C.geo.M1 * (C.geo.c * n k)) k m
        (lam (levelGen (ϱ := (1 : ℝ)) k) m ∩ C.bgSet Y)).filter (fun y => C.tCubeOfBlk m y = c),
        |C.weights m * (S.L : ℝ) ^ (m * (S.d - 2))| * (2 * B) ^ 2 +
      1 / 2 * ∑ _ν : Fin S.d, ∑ _x ∈ (Finset.univ : Finset (BgT C.geo k)).filter
        (fun x => C.tCubeOfBg x = c), (2 * B) ^ 2 +
      |Def7v2.sfActMass2 C.cs k| / 2 * ∑ _x ∈ (C.bgSet Y).filter (fun x => C.tCubeOfBg x = c),
        (B + vn (hC hv)) ^ 2 +
      1 / 4 * ∑ _ν : Fin S.d, ∑ _x ∈ (Finset.univ : Finset (BgT C.geo k)).filter
        (fun x => C.tCubeOfBg x = c), (2 * B) ^ 2) +
    ∑ j ∈ Finset.Icc 1 k, ∑ s ∈ (Finset.univ : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)).filter
      (fun s => C.tCubeOfC s = c),
      (1 / 2 * ‖C.coefE Y vc j s‖ * B ^ 2 +
        ‖C.coefM Y vc j s‖ * (|Def6.nuIdeal S.L k (C.sf.ν k) j| * (vn (hC hv) * (10 / 7 * B)))) +
    ∑ x ∈ (C.bgSet Y).filter (fun x => C.tCubeOfBg x = c), ∑ i : Fin N,
      ‖g (bgToFine C.geo C.hnn C.hkK x, i)‖ * B

/-- **The bound of the root of a cube** at a point where `φ̄`, the data on the blocks of `Y` and the
composed fields at the sites of the cube in `Y^≈` are bounded by `B`, and the composed fields there
satisfy `|ψ·ψ - 1| ≤ 1/2`. -/
theorem norm_cubeRoot_le (vc : Def7v2.CorrCoef S.d) (g : GIdx S n M K N → ℂ)
    (c : Torus S.d (n k)) {u : BlockAt S n M K k → Fin N → ℂ} {φ : (C.genW Y).Ω 1 × Fin N → ℂ}
    {B : ℝ} (hφ : ∀ z, vn (C.phiBarAt Y u hv φ z) ≤ B)
    (hψb : ∀ m ∈ Finset.Icc 1 k, ∀ y ∈ tBlocks S.d S.L (C.geo.M1 * (C.geo.c * n k)) k m
      (lam (levelGen (ϱ := (1 : ℝ)) k) m ∩ C.bgSet Y), vn (C.psiLevelKOf u m y) ≤ B)
    (hψ : ∀ j ∈ Finset.Icc 1 k, ∀ s, C.tCubeOfC s = c → s ∈ C.sset (thickY R Y) →
      vn (C.psiJAt Y u hv φ j s) ≤ B ∧
        ‖SmallField.dot (C.psiJAt Y u hv φ j s) (C.psiJAt Y u hv φ j s) - 1‖ ≤ 1 / 2) :
    ‖Def7v2.cubeRoot C vc Y u hv g φ c‖ ≤ C.cubeBound Y hv vc g c B := by
  classical
  have hB : 0 ≤ B := (vn_nonneg _).trans (hφ 0)
  -- the action
  have hact : ‖C.actCube Y u hv (Def7v2.sfActMass2 C.cs k) φ c‖ ≤
      1 / 2 * ∑ m ∈ Finset.Icc 1 k, ∑ _y ∈ (tBlocks S.d S.L (C.geo.M1 * (C.geo.c * n k)) k m
        (lam (levelGen (ϱ := (1 : ℝ)) k) m ∩ C.bgSet Y)).filter (fun y => C.tCubeOfBlk m y = c),
        |C.weights m * (S.L : ℝ) ^ (m * (S.d - 2))| * (2 * B) ^ 2 +
      1 / 2 * ∑ _ν : Fin S.d, ∑ _x ∈ (Finset.univ : Finset (BgT C.geo k)).filter
        (fun x => C.tCubeOfBg x = c), (2 * B) ^ 2 +
      |Def7v2.sfActMass2 C.cs k| / 2 * ∑ _x ∈ (C.bgSet Y).filter (fun x => C.tCubeOfBg x = c),
        (B + vn (hC hv)) ^ 2 +
      1 / 4 * ∑ _ν : Fin S.d, ∑ _x ∈ (Finset.univ : Finset (BgT C.geo k)).filter
        (fun x => C.tCubeOfBg x = c), (2 * B) ^ 2 := by
    unfold actCube
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact norm_actionGWithCube_le C.tCubeOfBg C.tCubeOfBlk _ _ _ _ _ c _ _ hψb hφ
    · rw [norm_mul, show ‖(1 / 4 : ℂ)‖ = 1 / 4 by norm_num]
      exact mul_le_mul_of_nonneg_left
        (norm_starBondEWithCube_le C.tCubeOfBg _ c _ hφ) (by norm_num)
  -- the corrections
  have hcorr : ∀ j ∈ Finset.Icc 1 k, ‖Def7v2.corrCube C vc Y u hv φ j c‖ ≤
      ∑ s ∈ (Finset.univ : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)).filter
        (fun s => C.tCubeOfC s = c),
        (1 / 2 * ‖C.coefE Y vc j s‖ * B ^ 2 +
          ‖C.coefM Y vc j s‖ * (|Def6.nuIdeal S.L k (C.sf.ν k) j| *
            (vn (hC hv) * (10 / 7 * B)))) := by
    intro j hj
    unfold Def7v2.corrCube
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
    have hsc : C.tCubeOfC s = c := (Finset.mem_filter.1 hs).2
    have hnn : 0 ≤ 1 / 2 * ‖C.coefE Y vc j s‖ * B ^ 2 +
        ‖C.coefM Y vc j s‖ * (|Def6.nuIdeal S.L k (C.sf.ν k) j| *
          (vn (hC hv) * (10 / 7 * B))) :=
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (sq_nonneg B))
        (mul_nonneg (norm_nonneg _) (mul_nonneg (abs_nonneg _)
          (mul_nonneg (vn_nonneg _) (by linarith))))
    by_cases hsT : s ∈ C.sset (thickY R Y)
    · obtain ⟨hψB, hψ1⟩ := hψ j hj s hsc hsT
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
        exact mul_le_mul_of_nonneg_left
          ((norm_dot_self_le _).trans (pow_le_pow_left₀ (vn_nonneg _) hψB 2)) (by positivity)
      · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
          (norm_nonneg _)
        refine (norm_dot_le_vn _ _).trans (mul_le_mul_of_nonneg_left ?_ (vn_nonneg _))
        exact (vn_unitDirC_le hψ1).trans (by linarith)
    · have hB' : s ∉ C.alignedIn j (thickY R Y) := fun h => hsT (Finset.mem_filter.1 h).2.2
      have hA : s ∉ C.alignedIn j Y := fun h =>
        hsT (subset_nbhd _ Y (Finset.mem_filter.1 h).2.2)
      have h0 : ∀ v : Localization.CTorus S.d S.L C.N₁ m₁ k →
          Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ,
          corrCoefSite v (C.alignedIn j Y) (C.alignedIn j (thickY R Y)) s = 0 := by
        intro v
        simp [corrCoefSite, hA, hB']
      simp only [h0, mul_zero, zero_mul, add_zero, norm_zero]
      exact hnn
  -- the source term
  have hg : ‖Def7v2.gCube C Y u hv g φ c‖ ≤ ∑ x ∈ (C.bgSet Y).filter
      (fun x => C.tCubeOfBg x = c), ∑ i : Fin N, ‖g (bgToFine C.geo C.hnn C.hkK x, i)‖ * B := by
    unfold Def7v2.gCube
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((norm_le_vn _ i).trans (hφ x)) (norm_nonneg _)
  unfold Def7v2.cubeRoot cubeBound
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) hg)
  · rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hact (abs_nonneg _)
  · exact (norm_sum_le _ _).trans (Finset.sum_le_sum hcorr)

end Def7.SFCtx

end Balaban.LargeField
