module

public import Balaban.LargeField.R.ZeroDomain
public import Balaban.LargeField.R.ChainSetting
public import Balaban.LargeField.Operators.QuietIndep
public import Balaban.LargeField.Operators.AncVars
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The margin of `Z''₀` (Part III, Lemma III.5.0 (b))

For a component `Z` of `Z^pre_k` of a region history `H` with the operative radii `R_j = R_base λ̂_j²`
(version 1.2, D-IV.2):

* `RegionStep.nbhd_six_Omega_compl_subset_Z0`: `(Ω^c)^{∼6} ⊆ Z^{(0)}` for one step;
* `coarse_mem_of_margin`: a fine site within `D` cubes (at scale `k`) of a site whose `π_j`-cube
  lies in `Z_j`, with `(D+1) L^{k-j} ≤ L([R_j]+4)+2`, has its `π_{j+1}`-cube in `Z_{j+1} ∖ Ω_{j+1}`
  and its `π_k`-cube in `Z`  (the margin of Lemma III.1.2 (f));
* `nbhd_ZzeroDD_subset`: **Lemma III.5.0 (b)**, `(Z''₀)^{∼3} ⊆ Ω^c_{k₃+1} ⊆ Z`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionStep

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rprev Rk : ℝ}
  (st : RegionStep d L n0 n1 Rprev Rk)

/-- `(Ωᶜ)^{∼6} ⊆ Z^{(0)}`: `Ωᶜ ⊆ Ω''ᶜ`, `(Ω''ᶜ)^{∼4} ⊆ F^Z` and `(F^Z)^{∼(⌊2R⌋+2)} ⊆ Z^{(0)}`. -/
theorem nbhd_six_Omega_compl_subset_Z0 : nbhd 6 st.Omegaᶜ ⊆ st.Z0 := by
  intro x hx
  have h1 : x ∈ nbhd 2 (nbhd 4 st.OmegaDDᶜ) := by
    rw [nbhd_nbhd]
    exact nbhd_mono (by norm_num) st.Omega_compl_subset_OmegaDD_compl hx
  have h2 : x ∈ nbhd (⌊2 * Rk⌋₊ + 2) st.FZ :=
    nbhd_mono (by omega) (show nbhd 4 st.OmegaDDᶜ ⊆ st.FZ from Set.subset_union_left) h1
  exact Region.nbhd_subset_Z0 L _ _ h2

end RegionStep

theorem blockMap_torusCast {d ℓ ℓ' : ℕ} (h : ℓ = ℓ') (A m : ℕ) (x : Torus d ℓ) :
    blockMap A m (torusCast h x) = blockMap A m x := by
  funext i
  unfold blockMap blockCoord
  rw [torusCast_val]

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M]

theorem fineSide_eq_mul (k : ℕ) : fineSide S n k = S.M * n k * S.L ^ k := by
  unfold fineSide; ring

theorem cubeMap_torusCast_fineSide (k j : ℕ) (s : Torus S.d (fineSide S n k)) :
    cubeMap n S.L S.M k j (torusCast (fineSide_eq_mul (S := S) (n := n) k) s) = cubeOf S n k j s := by
  unfold cubeMap cubeOf
  rw [blockMap_torusCast, mul_comm]

/-- **The margin of Lemma III.1.2 (f)**, in `π_j`-cube units: if the `π_j`-cube of `s` lies in
`Z_j = Lin_j(Z)` (`j < k`), and the `π_j`-cubes of `x` and `s` are at index distance `≤ E` with
`E < L([R_j] + 4) + 2`, then the `π_{j+1}`-cube of `x` lies in `Z_{j+1} ∖ Ω_{j+1}` (of the
localization of `Z`), and its `π_k`-cube lies in `Z`. -/
theorem mem_of_cube_dist {k : ℕ} (hkK : k ≤ K) (Z : H.Comp k) {j : ℕ} (hjk : j < k)
    {x s : Torus S.d (S.M * n k * S.L ^ k)}
    (hs : cubeMap n S.L S.M k j s ∈ ((H.lin j k Z : Finset (Torus S.d (n j))) : Set _)) {E : ℕ}
    (hE : supDist (cubeMap n S.L S.M k j x) (cubeMap n S.L S.M k j s) ≤ E)
    (hm : E < S.L * (⌊R j⌋₊ + 4) + 2) :
    cubeMap n S.L S.M k (j + 1) x ∉ ((H.locRH k Z).step j).Omega ∧
    cubeMap n S.L S.M k (j + 1) x ∈ ((H.locRH k Z).step (j + 1)).Z ∧
    cubeMap n S.L S.M k k x ∈ Z.1 := by
  have hnn := hnn_k H hkK
  have hz : cubeMap n S.L S.M k j s ∈ ((H.locRH k Z).step j).Z := by
    rw [locRH_Z Z hjk.le (hjk.le.trans hkK)]; exact hs
  have hOm : cubeMap n S.L S.M k (j + 1) x ∉ ((H.locRH k Z).step j).Omega := by
    intro hy
    have hyc : blockMap S.L (n (j + 1)) (cubeMap n S.L S.M k j x) ∈ ((H.locRH k Z).step j).Omega := by
      rw [cubeMap_succ hnn (by omega) x]; exact hy
    have hfar := ((H.locRH k Z).step j).fine_far
      (Nat.pos_of_ne_zero (NeZero.ne S.L)) (hnn j hjk) hyc hz
    omega
  have hZ1 : cubeMap n S.L S.M k (j + 1) x ∈ ((H.locRH k Z).step (j + 1)).Z :=
    ((H.locRH k Z).toSeq hkK (fun _ => rfl)).OmegaAt_compl_subset_Z j hOm
  refine ⟨hOm, hZ1, ?_⟩
  rw [locRH_Z Z (by omega) (by omega)] at hZ1
  obtain ⟨Y, hd, hxY⟩ := mem_lin.mp (Finset.mem_coe.mp hZ1)
  exact cubeMap_mem_of_desc' (M := S.M) hnn le_rfl hd hxY

/-- **The margin of Lemma III.1.2 (f), coarsened**: let `x, s` be sites of the fine torus of scale `k`,
the `π_j`-cube of `s` lying in `Z_j = Lin_j(Z)`, `j < k`, and the `π_k`-cubes of `x` and `s` at index
distance `≤ D`, with `(D + 1) L^{k-j} ≤ L([R_j] + 4) + 2`.  Then the `π_{j+1}`-cube of `x` lies in
`Z_{j+1} ∖ Ω_{j+1}` (of the localization of `Z`) and its `π_k`-cube lies in `Z`. -/
theorem coarse_mem_of_margin {k : ℕ} (hkK : k ≤ K) (Z : H.Comp k) {j : ℕ} (hjk : j < k)
    {x s : Torus S.d (S.M * n k * S.L ^ k)}
    (hs : cubeMap n S.L S.M k j s ∈ ((H.lin j k Z : Finset (Torus S.d (n j))) : Set _)) {D : ℕ}
    (hD : supDist (cubeMap n S.L S.M k k x) (cubeMap n S.L S.M k k s) ≤ D)
    (hm : (D + 1) * S.L ^ (k - j) ≤ S.L * (⌊R j⌋₊ + 4) + 2) :
    cubeMap n S.L S.M k (j + 1) x ∉ ((H.locRH k Z).step j).Omega ∧
    cubeMap n S.L S.M k (j + 1) x ∈ ((H.locRH k Z).step (j + 1)).Z ∧
    cubeMap n S.L S.M k k x ∈ Z.1 := by
  have hnn := hnn_k H hkK
  have hpow : n j = S.L ^ (k - j) * n k := H.F.n_eq_pow hjk.le hkK
  have hcomp : ∀ y : Torus S.d (S.M * n k * S.L ^ k),
      blockMap (S.L ^ (k - j)) (n k) (cubeMap n S.L S.M k j y) = cubeMap n S.L S.M k k y := by
    intro y
    unfold cubeMap
    rw [blockMap_comp (fine_eq hnn hjk.le) hpow]
    have : S.L ^ j * S.M * S.L ^ (k - j) = S.L ^ k * S.M := by
      rw [mul_right_comm, ← pow_add, show j + (k - j) = k by omega]
    rw [this]
  have hle := supDist_le_blockMap (d := S.d) (L := S.L ^ (k - j)) (m := n k) hpow
    (cubeMap n S.L S.M k j x) (cubeMap n S.L S.M k j s)
  rw [hcomp, hcomp] at hle
  have hP : 1 ≤ S.L ^ (k - j) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne S.L))
  have h1 : S.L ^ (k - j) * supDist (cubeMap n S.L S.M k k x) (cubeMap n S.L S.M k k s) ≤
      S.L ^ (k - j) * D := Nat.mul_le_mul_left _ hD
  have h2 : (D + 1) * S.L ^ (k - j) = S.L ^ (k - j) * D + S.L ^ (k - j) := by ring
  exact H.mem_of_cube_dist hkK Z hjk hs (E := S.L ^ (k - j) * D + (S.L ^ (k - j) - 1)) (by omega)
    (by omega)

include H

/-- The a priori radii are at least `R_base ≥ 4L + 20 ≥ 8` (so `8 ≤ [R̂_j]`). -/
theorem eight_le_lateR (j : ℕ) : 8 ≤ S.lateR j := by
  have RH := H.F.RH
  have hL := H.F.ok.two_le_L
  unfold Setting.lateR
  apply Nat.le_floor
  have h1 : (4 * S.L + 20 : ℝ) ≤ S.Rb := RH.base
  have h2 := RH.one_le j
  have hL' : (2 : ℝ) ≤ S.L := by exact_mod_cast hL
  push_cast
  nlinarith

theorem eight_le_L_mul_lateR (k : ℕ) : 8 ≤ S.L * S.lateR k := by
  have := H.eight_le_lateR k
  have hL := H.F.ok.two_le_L
  nlinarith

/-- `k₃ < k` for `k ≥ 1`. -/
theorem kThree_lt {k : ℕ} (hk : 1 ≤ k) : S.kThree k < k := by
  have hS := H.F.ok
  have h3 := H.eight_le_L_mul_lateR k
  have : S.kThree k ≤ k - 1 := by
    rw [hS.kThree_le_iff h3 (by omega), show k - (k - 1) = 1 by omega, pow_one]
    have := H.eight_le_lateR (k - 1)
    nlinarith
  omega

/-- **Lemma III.5.0 (b)**: `(Z''₀)^{∼3} ⊆ Ω^c_{k₃+1} ⊆ Z`.  A fine site whose `π_k`-cube lies in
`(Z''₀)^{∼3}` has its `π_{k₃+1}`-cube in `Z_{k₃+1} ∖ Ω_{k₃+1}` (of the localization of `Z`), and its
`π_k`-cube in `Z`.  Hypothesis: the operative radii `R_j = R_base λ̂_j²` (version 1.2, D-IV.2). -/
theorem ZzeroDD_nbhd_margin (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) {k : ℕ} (hkK : k ≤ K) (hk : 1 ≤ k)
    (Z : H.Comp k) {x : Torus S.d (S.M * n k * S.L ^ k)}
    (hx : cubeMap n S.L S.M k k x ∈ nbhd 3 (H.ZzeroDD k Z)) :
    cubeMap n S.L S.M k (S.kThree k + 1) x ∉ ((H.locRH k Z).step (S.kThree k)).Omega ∧
    cubeMap n S.L S.M k (S.kThree k + 1) x ∈ ((H.locRH k Z).step (S.kThree k + 1)).Z ∧
    cubeMap n S.L S.M k k x ∈ Z.1 := by
  have hS := H.F.ok
  have h3 := H.eight_le_L_mul_lateR k
  unfold ZzeroDD at hx
  rw [nbhd_nbhd] at hx
  obtain ⟨c', ⟨s, hsc, hs3⟩, hd⟩ := mem_nbhd.mp hx
  have hs3' : cubeMap n S.L S.M k (S.kThree k) (torusCast (fineSide_eq_mul (S := S) (n := n) k) s) ∈
      ((H.lin (S.kThree k) k Z : Finset (Torus S.d (n (S.kThree k)))) : Set _) := by
    rw [cubeMap_torusCast_fineSide]; exact hs3
  have hD : supDist (cubeMap n S.L S.M k k x)
      (cubeMap n S.L S.M k k (torusCast (fineSide_eq_mul (S := S) (n := n) k) s)) ≤ 3 + 3 := by
    rw [cubeMap_torusCast_fineSide]
    unfold cubeOf at hsc ⊢
    rw [hsc]; exact hd
  have hm : (3 + 3 + 1) * S.L ^ (k - S.kThree k) ≤ S.L * (⌊R (S.kThree k)⌋₊ + 4) + 2 := by
    have h8 := (hS.kThree_mem h3).2
    have hl : S.lateR (S.kThree k) = ⌊R (S.kThree k)⌋₊ := by
      unfold Setting.lateR; rw [hR]
    rw [hl] at h8
    have : S.L * ⌊R (S.kThree k)⌋₊ ≤ S.L * (⌊R (S.kThree k)⌋₊ + 4) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  exact H.coarse_mem_of_margin hkK Z (H.kThree_lt hk) hs3' hD hm

/-- **The margin of `Ω^c_k`**: a cube of `𝕋_k` within index distance `6` of a cube outside `Ω_k`
(of the localization of `Z`) lies in `Z`: `(Ω^c_k)^{∼6} ⊆ Z`. -/
theorem nbhd_six_Omega_compl_subset {k' : ℕ} (hkK : k' + 1 ≤ K) (Z : H.Comp (k' + 1))
    {x y : Torus S.d (n (k' + 1))} (hy : y ∉ ((H.locRH (k' + 1) Z).step k').Omega)
    (hxy : supDist x y ≤ 6) : x ∈ Z.1 := by
  have hx : x ∈ ((H.locRH (k' + 1) Z).step k').Z0 :=
    ((H.locRH (k' + 1) Z).step k').nbhd_six_Omega_compl_subset_Z0 (mem_nbhd.mpr ⟨y, hy, hxy⟩)
  have h1 := ((H.locRH (k' + 1) Z).step k').Z0_subset_Zpre (S.omega (k' + 1)) (critOpt S k0 (k' + 1)) hx
  have h2 : x ∈ (H.locRH (k' + 1) Z).F.Zpre (k' + 1) := h1
  rw [locRH_Zpre Z le_rfl hkK, lin_self] at h2
  simpa using h2

end RegionHistory

end Balaban.LargeField
