module

public import Balaban.LargeField.R.ZeroDomainC
public import Balaban.LargeField.Operators.HistGen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The region `Z₀` and the large-field domains (Part III, Lemma III.3.2 (d))

* `RegionStep.nbhd_Omega_compl_subset_Z0`: `(Ωᶜ)^{∼(⌊2R⌋+6)} ⊆ Z^{(0)}` for one step, hence
  `dist(Z^c_0, Ω^c_{k₂}) ≥ ([2R_{k₂-1}] + 6)` cubes (`nbhd_Omega_compl_subset_lin`);
* `Zzero_margin`: `Z_{k₂} ⊆ Z₀ ⊆ Ω^c_{k₂+1} ⊆ Ω^c_k` (`Zzero_subset_Omega_compl_succ`,
  `Zzero_not_mem_Omega_top`);
* `far_Zzero_Omega_succ`: `dist(Z₀, Ω_{k₂+1}) ≥ 4L + [R_{k₂-1}] + 2` in `π_{k₂}`-cube units;
* `far_Zzero_Omega_top`: `dist(Z₀, Ω_k)` is at least `L([R_{k-1}] + 3) + [R_{k-2}] + 2` in
  `π_{k-1}`-cube units.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionStep

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rprev Rk : ℝ}
  (st : RegionStep d L n0 n1 Rprev Rk)

/-- `(Ωᶜ)^{∼(⌊2R⌋+6)} ⊆ Z^{(0)}`. -/
theorem nbhd_Omega_compl_subset_Z0 : nbhd (⌊2 * Rk⌋₊ + 6) st.Omegaᶜ ⊆ st.Z0 := by
  intro x hx
  have h1 : x ∈ nbhd (⌊2 * Rk⌋₊ + 2) (nbhd 4 st.OmegaDDᶜ) := by
    rw [nbhd_nbhd]
    refine nbhd_mono (by omega) st.Omega_compl_subset_OmegaDD_compl hx
  exact Region.nbhd_subset_Z0 L _ _
    (nbhd_mono le_rfl (show nbhd 4 st.OmegaDDᶜ ⊆ st.FZ from Set.subset_union_left) h1)

end RegionStep

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M]

/-- `(Ω^c_{j+1})^{∼(⌊2R_j⌋+6)} ⊆ Z_{j+1}` for the localization of `Z` (`j + 1 ≤ k`). -/
theorem nbhd_Omega_compl_subset_lin {k : ℕ} (hkK : k ≤ K) (Z : H.Comp k) {j : ℕ} (hjk : j + 1 ≤ k)
    {c y : Torus S.d (n (j + 1))} (hy : y ∉ ((H.locRH k Z).step j).Omega)
    (hcy : supDist c y ≤ ⌊2 * R j⌋₊ + 6) :
    c ∈ ((H.lin (j + 1) k Z : Finset (Torus S.d (n (j + 1)))) : Set _) := by
  have hx : c ∈ ((H.locRH k Z).step j).Z0 :=
    ((H.locRH k Z).step j).nbhd_Omega_compl_subset_Z0 (mem_nbhd.mpr ⟨y, hy, hcy⟩)
  have h1 := ((H.locRH k Z).step j).Z0_subset_Zpre (S.omega (j + 1)) (critOpt S k0 (j + 1)) hx
  have h2 : c ∈ (H.locRH k Z).F.Zpre (j + 1) := h1
  rwa [locRH_Zpre Z hjk (hjk.trans hkK)] at h2

/-- **Lemma I.3.5 (f)** from a nearby site of `Z_j`: if `s` has its `π_j`-cube in `Z_j`, `x` is within
fine distance `F` of `s` and the `π_{j+1}`-cube of `y` lies in `Ω_{j+1}`, then
`L([R_j]+4) + [R_{j-1}] + 2 ≤ dist(c_j(y), c_j(x)) + ⌈F / (L^j M)⌉'` where `⌈F/A⌉' = (F + A - 1)/A`. -/
theorem far_of_near {k : ℕ} (hkK : k ≤ K) (Z : H.Comp k) {j : ℕ} (hjk : j < k)
    {x s y : Torus S.d (S.M * n k * S.L ^ k)}
    (hs : cubeMap n S.L S.M k j s ∈ ((H.lin j k Z : Finset (Torus S.d (n j))) : Set _)) {F : ℕ}
    (hF : supDist x s ≤ F)
    (hy : cubeMap n S.L S.M k (j + 1) y ∈ ((H.locRH k Z).step j).Omega) :
    S.L * (⌊R j⌋₊ + 4) + ⌊R (j - 1)⌋₊ + 2 ≤
      supDist (cubeMap n S.L S.M k j y) (cubeMap n S.L S.M k j x) +
        (F + S.L ^ j * S.M - 1) / (S.L ^ j * S.M) := by
  have hnn := hnn_k H hkK
  have hz : cubeMap n S.L S.M k j s ∈ ((H.locRH k Z).step j).Z := by
    rw [locRH_Z Z hjk.le (hjk.le.trans hkK)]; exact hs
  have hyc : blockMap S.L (n (j + 1)) (cubeMap n S.L S.M k j y) ∈ ((H.locRH k Z).step j).Omega := by
    rw [cubeMap_succ hnn (by omega) y]; exact hy
  have hfar := ((H.locRH k Z).step j).fine_far
    (Nat.pos_of_ne_zero (NeZero.ne S.L)) (hnn j hjk) hyc hz
  have h1 := supDist_triangle (cubeMap n S.L S.M k j y) (cubeMap n S.L S.M k j x)
    (cubeMap n S.L S.M k j s)
  have h2 : supDist (cubeMap n S.L S.M k j x) (cubeMap n S.L S.M k j s) ≤
      (F + S.L ^ j * S.M - 1) / (S.L ^ j * S.M) := by
    have := supDist_blockMap_le (d := S.d) (L := S.L ^ j * S.M) (m := n j)
      (fine_eq hnn hjk.le) x s
    exact this.trans (Nat.div_le_div_right (by omega))
  omega

/-- A site of `Z₀` has a witness `s` in the same `k`-block whose `π_{k₂}`-cube lies in `Z_{k₂}`. -/
theorem Zzero_witness {k : ℕ} (Z : H.Comp k) {x : Torus S.d (S.M * n k * S.L ^ k)}
    (hx : blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z) :
    ∃ s : Torus S.d (S.M * n k * S.L ^ k), blockMap (S.L ^ k) (S.M * n k) s =
        blockMap (S.L ^ k) (S.M * n k) x ∧
      cubeMap n S.L S.M k (S.kTwo k) s ∈
        ((H.lin (S.kTwo k) k Z : Finset (Torus S.d (n (S.kTwo k)))) : Set _) := by
  obtain ⟨s0, hs0, hl⟩ := hx
  refine ⟨torusCast (fineSide_eq_mul (S := S) (n := n) k) s0, ?_, ?_⟩
  · rw [blockMap_torusCast]; exact hs0
  · rw [cubeMap_torusCast_fineSide]; exact hl

include H in
/-- Two sites of the same `k`-block have `π_j`-cubes at distance `≤ (L^k + A - 2)/A`, `A = L^j M`. -/
theorem cube_dist_of_block {k : ℕ} (hkK : k ≤ K) {j : ℕ} (hjk : j ≤ k)
    {x s : Torus S.d (S.M * n k * S.L ^ k)}
    (h : blockMap (S.L ^ k) (S.M * n k) x = blockMap (S.L ^ k) (S.M * n k) s) :
    supDist (cubeMap n S.L S.M k j x) (cubeMap n S.L S.M k j s) ≤
      (S.L ^ k - 1 + S.L ^ j * S.M - 1) / (S.L ^ j * S.M) := by
  have hnn := hnn_k H hkK
  have hd : supDist x s ≤ S.L ^ k - 1 :=
    supDist_le_of_blockMap_eq (L := S.L ^ k) (m := S.M * n k) (by ring) h
  have := supDist_blockMap_le (d := S.d) (L := S.L ^ j * S.M) (m := n j) (fine_eq hnn hjk) x s
  exact this.trans (Nat.div_le_div_right (by omega))

include H in
theorem kTwo_lt {k : ℕ} (hk : 1 ≤ k) : S.kTwo k < k :=
  lt_of_le_of_lt (H.F.ok.kTwo_le_kThree (H.eight_le_L_mul_lateR k)) (H.kThree_lt hk)

include H in
/-- The definition of `k₂` (`L^{n₂} ≤ L M [R_{k₂}]`) in the form used for the cube distances. -/
theorem div_k2_le (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) {k : ℕ} (hk : 1 ≤ k) :
    (S.L ^ k - 1 + S.L ^ S.kTwo k * S.M - 1) / (S.L ^ S.kTwo k * S.M) ≤
      S.L * ⌊R (S.kTwo k)⌋₊ := by
  have hS := H.F.ok
  have hk2 := H.kTwo_lt hk
  have hl : S.lateR (S.kTwo k) = ⌊R (S.kTwo k)⌋₊ := by unfold Setting.lateR; rw [hR]
  have hspec := hS.kTwo_spec k
  rw [hl] at hspec
  have hA : 0 < S.L ^ S.kTwo k * S.M :=
    Nat.mul_pos (pow_pos (NeZero.pos S.L) _) (NeZero.pos S.M)
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hA]
  have hk' : S.L ^ k = S.L ^ S.kTwo k * S.L ^ (k - S.kTwo k) := by
    rw [← pow_add]; congr 1; omega
  have h1 : S.L ^ k ≤ (S.L ^ S.kTwo k * S.M) * (S.L * ⌊R (S.kTwo k)⌋₊) := by
    rw [hk']
    calc S.L ^ S.kTwo k * S.L ^ (k - S.kTwo k)
        ≤ S.L ^ S.kTwo k * (S.L * S.M * ⌊R (S.kTwo k)⌋₊) := Nat.mul_le_mul_left _ hspec
      _ = _ := by ring
  have e : (S.L * ⌊R (S.kTwo k)⌋₊).succ * (S.L ^ S.kTwo k * S.M) =
      (S.L ^ S.kTwo k * S.M) * (S.L * ⌊R (S.kTwo k)⌋₊) + S.L ^ S.kTwo k * S.M := by
    rw [Nat.succ_eq_add_one]; ring
  rw [e]
  omega

include H in
/-- Two sites of the same `k`-block have `π_{k₂}`-cubes at distance `≤ L [R_{k₂}]`. -/
theorem cube_dist_k2_le (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) {k : ℕ} (hkK : k ≤ K) (hk : 1 ≤ k)
    {x s : Torus S.d (S.M * n k * S.L ^ k)}
    (h : blockMap (S.L ^ k) (S.M * n k) x = blockMap (S.L ^ k) (S.M * n k) s) :
    supDist (cubeMap n S.L S.M k (S.kTwo k) x) (cubeMap n S.L S.M k (S.kTwo k) s) ≤
      S.L * ⌊R (S.kTwo k)⌋₊ :=
  (H.cube_dist_of_block hkK (H.kTwo_lt hk).le h).trans (H.div_k2_le hR hk)

/-- The division bound for the `π_{k-1}`-cubes of two sites of one `k`-block. -/
theorem div_pred_le (k' : ℕ) :
    (S.L ^ (k' + 1) - 1 + S.L ^ k' * S.M - 1) / (S.L ^ k' * S.M) ≤ S.L := by
  have hA : 0 < S.L ^ k' * S.M := Nat.mul_pos (pow_pos (NeZero.pos S.L) _) (NeZero.pos S.M)
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hA]
  have h1 : S.L ^ (k' + 1) ≤ (S.L ^ k' * S.M) * S.L := by
    have := NeZero.pos S.M
    calc S.L ^ (k' + 1) = S.L ^ k' * 1 * S.L := by ring
      _ ≤ (S.L ^ k' * S.M) * S.L := by gcongr; omega
  have e : S.L.succ * (S.L ^ k' * S.M) = (S.L ^ k' * S.M) * S.L + S.L ^ k' * S.M := by
    rw [Nat.succ_eq_add_one]; ring
  rw [e]
  omega

include H in
/-- **Lemma III.3.2 (d)**: `Z₀ ⊆ Ω^c_{k₂+1}` (and `⊆ Z`): a fine site in a `k`-block of `Z₀` has its
`π_{k₂+1}`-cube in `Z_{k₂+1} ∖ Ω_{k₂+1}` and its `π_k`-cube in `Z`. -/
theorem Zzero_margin (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) {k : ℕ} (hkK : k ≤ K) (hk : 1 ≤ k)
    (Z : H.Comp k) {x : Torus S.d (S.M * n k * S.L ^ k)}
    (hx : blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z) :
    cubeMap n S.L S.M k (S.kTwo k + 1) x ∉ ((H.locRH k Z).step (S.kTwo k)).Omega ∧
    cubeMap n S.L S.M k (S.kTwo k + 1) x ∈ ((H.locRH k Z).step (S.kTwo k + 1)).Z ∧
    cubeMap n S.L S.M k k x ∈ Z.1 := by
  obtain ⟨s, hbs, hsl⟩ := H.Zzero_witness Z hx
  have hE := H.cube_dist_k2_le hR hkK hk hbs.symm
  have e : S.L * (⌊R (S.kTwo k)⌋₊ + 4) = S.L * ⌊R (S.kTwo k)⌋₊ + S.L * 4 := by ring
  have hL := H.F.ok.two_le_L
  exact H.mem_of_cube_dist hkK Z (H.kTwo_lt hk) hsl hE (by omega)

include H in
/-- **Lemma III.3.2 (d)**: `dist(Z₀, Ω_{k₂+1}) ≥ 4L + [R_{k₂-1}] + 2` in `π_{k₂}`-cube units. -/
theorem far_Zzero_Omega_succ (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) {k : ℕ} (hkK : k ≤ K)
    (hk : 1 ≤ k) (Z : H.Comp k) {x y : Torus S.d (S.M * n k * S.L ^ k)}
    (hx : blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z)
    (hy : cubeMap n S.L S.M k (S.kTwo k + 1) y ∈ ((H.locRH k Z).step (S.kTwo k)).Omega) :
    4 * S.L + ⌊R (S.kTwo k - 1)⌋₊ + 2 ≤
      supDist (cubeMap n S.L S.M k (S.kTwo k) y) (cubeMap n S.L S.M k (S.kTwo k) x) := by
  obtain ⟨s, hbs, hsl⟩ := H.Zzero_witness Z hx
  have hF : supDist x s ≤ S.L ^ k - 1 :=
    supDist_le_of_blockMap_eq (L := S.L ^ k) (m := S.M * n k) (by ring) hbs.symm
  have h1 := H.far_of_near hkK Z (H.kTwo_lt hk) hsl hF hy
  have h3 := H.div_k2_le hR hk
  have e : S.L * (⌊R (S.kTwo k)⌋₊ + 4) = S.L * ⌊R (S.kTwo k)⌋₊ + S.L * 4 := by ring
  omega

include H in
/-- **Lemma III.3.2 (d)**: `Z_{k₂} ⊆ Z₀`. -/
theorem Zzero_of_lin {k : ℕ} (Z : H.Comp k) {x : Torus S.d (S.M * n k * S.L ^ k)}
    (hx : cubeMap n S.L S.M k (S.kTwo k) x ∈
      ((H.lin (S.kTwo k) k Z : Finset (Torus S.d (n (S.kTwo k)))) : Set _)) :
    blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z := by
  refine ⟨torusCast (fineSide_eq_mul (S := S) (n := n) k).symm x, ?_, ?_⟩
  · unfold zeroBlockOf; rw [blockMap_torusCast]
  · unfold cubeOf
    rw [blockMap_torusCast, mul_comm S.M (S.L ^ S.kTwo k)]
    exact hx

include H in
/-- **Lemma III.3.2 (d)**: `Z₀ ⊆ Ω^c_k`. -/
theorem Zzero_not_mem_Omega_top (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) {k' : ℕ} (hkK : k' + 1 ≤ K)
    (Z : H.Comp (k' + 1)) {x : Torus S.d (S.M * n (k' + 1) * S.L ^ (k' + 1))}
    (hx : blockMap (S.L ^ (k' + 1)) (S.M * n (k' + 1)) x ∈ H.Zzero (k' + 1) Z) :
    cubeMap n S.L S.M (k' + 1) (k' + 1) x ∉ ((H.locRH (k' + 1) Z).step k').Omega := by
  intro h
  have hL := H.F.ok.two_le_L
  have hRb : ∀ j, 1 ≤ j → j < k' + 1 → S.Rb ≤ R j := by
    intro j _ _
    rw [hR]
    have h1 := H.F.RH.one_le j
    have h2 := H.F.RH.base
    have hL' : (2 : ℝ) ≤ S.L := by exact_mod_cast hL
    have h3 : (1 : ℝ) ≤ S.lam j ^ 2 := one_le_pow₀ h1
    have h4 : (0 : ℝ) ≤ S.Rb := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h3 h4]
  have hk2 := H.kTwo_lt (by omega : 1 ≤ k' + 1)
  have h1 : x ∈ (H.locGen Z S.M hkK hL hRb).Ω (k' + 1) :=
    (mem_locGen_succ (hL := hL) (hR := hRb) (Nat.lt_succ_self k')).mpr h
  have h2 : x ∈ (H.locGen Z S.M hkK hL hRb).Ω (S.kTwo (k' + 1) + 1) :=
    (H.locGen Z S.M hkK hL hRb).Ω_antitone (by omega) (by omega) (by omega) h1
  have h3 := (mem_locGen_succ (hL := hL) (hR := hRb) hk2).mp h2
  exact (H.Zzero_margin hR hkK (by omega) Z hx).1 h3

include H in
/-- **Lemma III.3.2 (d)**: `dist(Z₀, Ω_k)`: for a fine site `x` in a `k`-block of `Z₀` and `y` with
`π_k`-cube in `Ω_k`, the `π_{k-1}`-cubes are at index distance `≥ L([R_{k-1}] + 3) + [R_{k-2}] + 2`. -/
theorem far_Zzero_Omega_top {k' : ℕ} (hkK : k' + 1 ≤ K)
    (Z : H.Comp (k' + 1)) {x y : Torus S.d (S.M * n (k' + 1) * S.L ^ (k' + 1))}
    (hx : blockMap (S.L ^ (k' + 1)) (S.M * n (k' + 1)) x ∈ H.Zzero (k' + 1) Z)
    (hy : cubeMap n S.L S.M (k' + 1) (k' + 1) y ∈ ((H.locRH (k' + 1) Z).step k').Omega) :
    S.L * (⌊R k'⌋₊ + 3) + ⌊R (k' - 1)⌋₊ + 2 ≤
      supDist (cubeMap n S.L S.M (k' + 1) k' y) (cubeMap n S.L S.M (k' + 1) k' x) := by
  obtain ⟨s, hbs, hsl⟩ := H.Zzero_witness Z hx
  have hk2 := H.kTwo_lt (by omega : 1 ≤ k' + 1)
  have hsl' : cubeMap n S.L S.M (k' + 1) k' s ∈
      ((H.lin k' (k' + 1) Z : Finset (Torus S.d (n k'))) : Set _) := by
    have h1 : s ∈ H.locFine Z S.M (S.kTwo (k' + 1)) :=
      (mem_locFine_iff_lin hkK hk2.le).mpr hsl
    have h2 := locFine_mono hkK (by omega : S.kTwo (k' + 1) ≤ k') (Nat.le_succ k') h1
    exact (mem_locFine_iff_lin hkK (Nat.le_succ k')).mp h2
  have hF : supDist x s ≤ S.L ^ (k' + 1) - 1 :=
    supDist_le_of_blockMap_eq (L := S.L ^ (k' + 1)) (m := S.M * n (k' + 1)) (by ring) hbs.symm
  have h1 := H.far_of_near hkK Z (Nat.lt_succ_self k') hsl' hF hy
  have h3 := div_pred_le (S := S) k'
  have e : S.L * (⌊R k'⌋₊ + 4) = S.L * (⌊R k'⌋₊ + 3) + S.L := by ring
  omega

end RegionHistory

end Balaban.LargeField
