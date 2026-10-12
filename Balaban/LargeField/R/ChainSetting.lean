module

public import Balaban.LargeField.R.ChainGraph
public import Balaban.LargeField.Operators.HistGen
public import Balaban.LargeField.Operators.DomainIdentity
public import Balaban.LargeField.History.RipeWindow
public import Balaban.LargeField.Region.Inclusions

/-!
# The generating set of a localized history and the fine sets `Z_j` (Part III, §III.4)

For a component `Z` of `Z^pre_k` of a region history `H`, the localization `locRH H k Z` is a region
history without removals; its generating set (`locGen`, Lemma I.3.10) lives on the fine torus
`Torus d (M n_k L^k)` with layers `Λ_i = Ω_i ∖ Ω_{i+1}`.  `locFine j` is the fine set of the region
`Z_j = Lin_j(Z)` of the localization.

* `compl_Omega_subset`: `Ω_iᶜ ⊆ Z_i`;
* `locFine_mono`: `Z_j ⊆ Z_{j'}` for `j ≤ j' ≤ k` (regions grow);
* `locFine_not_mem_Omega`: `Z_j ∩ Ω_{j+1} = ∅`;
* `locFine_far`: `Z_j` is at `ℓ¹`-distance `> ϱ L^j` from `Ω_{j+1}`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Multiscale

namespace RegionHistory

section DescLemma

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {M : ℕ} [NeZero M]

/-- `cubeMap_mem_of_desc` for the fine torus of an arbitrary scale `K'` (not only the horizon). -/
theorem cubeMap_mem_of_desc' [NeZero S.L] {K' : ℕ} (hnn : ∀ i, i < K' → n i = S.L * n (i + 1))
    {a b : ℕ} (hbK : b ≤ K') {Y : H.Comp a} {Z : H.Comp b} (h : H.Desc a b Y Z)
    {x : Torus S.d (M * n K' * S.L ^ K')} (hx : cubeMap n S.L M K' a x ∈ Y.1) :
    cubeMap n S.L M K' b x ∈ Z.1 := by
  induction h with
  | refl => exact hx
  | step b' W' Y' Y'' hd hrem hs ih =>
    have h1 := ih (by omega) hx
    have h2 : blockMap S.L (n (b' + 1)) (cubeMap n S.L M K' b' x) ∈ Y''.1 := hs ⟨_, h1, rfl⟩
    rwa [cubeMap_succ hnn (by omega) x] at h2

end DescLemma

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) {k : ℕ} (Z : H.Comp k) (M : ℕ) [NeZero M]

/-- The fine set of the region `Z_j = Lin_j(Z)` of the localization of `Z` (the fine torus is the
one of the horizon `k`). -/
def locFine (j : ℕ) : Set (Torus S.d (M * n k * S.L ^ k)) :=
  fineSet (S := S) (n := n) M k j ((H.locRH k Z).step j).Z

theorem mem_locFine {j : ℕ} {x : Torus S.d (M * n k * S.L ^ k)} :
    x ∈ H.locFine Z M j ↔ cubeMap n S.L M k j x ∈ ((H.locRH k Z).step j).Z := Iff.rfl

variable {H Z M}

theorem hnn_k (H : RegionHistory S n R k0 K) (hkK : k ≤ K) : ∀ i, i < k → n i = S.L * n (i + 1) :=
  fun i hi => H.F.hnn i (lt_of_lt_of_le hi hkK)

theorem mem_locFine_iff_lin (hkK : k ≤ K) {j : ℕ} (hj : j ≤ k) {x : Torus S.d (M * n k * S.L ^ k)} :
    x ∈ H.locFine Z M j ↔ cubeMap n S.L M k j x ∈ ((H.lin j k Z : Finset (Torus S.d (n j))) : Set _) := by
  rw [mem_locFine, locRH_Z Z hj (hj.trans hkK)]

theorem mem_locFine_k (hkK : k ≤ K) {x : Torus S.d (M * n k * S.L ^ k)} :
    x ∈ H.locFine Z M k ↔ cubeMap n S.L M k k x ∈ Z.1 := by
  rw [mem_locFine_iff_lin hkK le_rfl, lin_self]
  simp

theorem locFine_mono (hkK : k ≤ K) {j j' : ℕ} (hjj : j ≤ j') (hj' : j' ≤ k) :
    H.locFine Z M j ⊆ H.locFine Z M j' := by
  have := H.neZero_L
  intro x hx
  rw [mem_locFine_iff_lin hkK (hjj.trans hj')] at hx
  rw [mem_locFine_iff_lin hkK hj']
  -- the cubes of the lineage coarsen into the lineage
  obtain ⟨Y, hd, hxY⟩ := mem_lin.mp (Finset.mem_coe.mp hx)
  obtain ⟨W, h1, h2⟩ := Desc.split hjj hj' hd
  exact Finset.mem_coe.mpr (mem_lin.mpr ⟨W, h2, cubeMap_mem_of_desc' (hnn_k H hkK) hj' h1 hxY⟩)

variable (H Z M) [NeZero S.L]

/-- The generating set of the localization of `Z` (Lemma I.3.10), up to the scale `k`. -/
noncomputable def locGen (hkK : k ≤ K) (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j) :
    GeneratingSet S.d S.L (M * n k) k ((S.L : ℝ) * M * S.Rb) :=
  (H.locRH k Z).histGen (M := M) hkK (fun _ => rfl) hL hR

variable {H Z M}

theorem mem_locGen {hkK : k ≤ K} {hL : 2 ≤ S.L} {hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j} {j : ℕ}
    {x : Torus S.d (M * n k * S.L ^ k)} :
    x ∈ (H.locGen Z M hkK hL hR).Ω j ↔
      j ≤ k ∧ cubeMap n S.L M k j x ∈ ((H.locRH k Z).toSeq hkK (fun _ => rfl)).OmegaAt j :=
  (H.locRH k Z).mem_histGen (M := M) hkK (fun _ => rfl) hL hR j x

theorem mem_locGen_succ {hkK : k ≤ K} {hL : 2 ≤ S.L} {hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j}
    {i : ℕ} (hi : i < k) {x : Torus S.d (M * n k * S.L ^ k)} :
    x ∈ (H.locGen Z M hkK hL hR).Ω (i + 1) ↔
      cubeMap n S.L M k (i + 1) x ∈ ((H.locRH k Z).step i).Omega := by
  rw [mem_locGen]
  exact ⟨fun h => h.2, fun h => ⟨hi, h⟩⟩

/-- `Ω_iᶜ ⊆ Z_i` for `1 ≤ i ≤ k`. -/
theorem compl_Omega_subset {hkK : k ≤ K} {hL : 2 ≤ S.L} {hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j}
    {i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) {x : Torus S.d (M * n k * S.L ^ k)}
    (hx : x ∉ (H.locGen Z M hkK hL hR).Ω i) : x ∈ H.locFine Z M i := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hx' : cubeMap n S.L M k (i' + 1) x ∉ ((H.locRH k Z).step i').Omega := fun h =>
    hx ((mem_locGen_succ (by omega)).mpr h)
  exact ((H.locRH k Z).toSeq hkK (fun _ => rfl)).OmegaAt_compl_subset_Z i' hx'

/-- `Z_j ∩ Ω_{j+1} = ∅` for `j < k`. -/
theorem locFine_not_mem_Omega {hkK : k ≤ K} {hL : 2 ≤ S.L}
    {hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j} {j : ℕ} (hjk : j < k)
    {x : Torus S.d (M * n k * S.L ^ k)} (hx : x ∈ H.locFine Z M j) :
    x ∉ (H.locGen Z M hkK hL hR).Ω (j + 1) := by
  intro h
  have h1 := (mem_locGen_succ (hL := hL) (hR := hR) hjk).mp h
  rw [← cubeMap_succ (hnn_k H hkK) (by omega) x] at h1
  exact ((H.locRH k Z).step j).not_mem_Z_of_mem_Omega (by omega) (hnn_k H hkK j hjk) h1 hx

/-- `Z_j` is at `ℓ¹`-distance `> 2dL^{j+1}` from `Ω_{j+1}` (`1 ≤ j < k`), given `2dL ≤ ϱ = LMR_base`
and `R_base ≤ R_j` (Lemma III.1.2 (f) for the core). -/
theorem locFine_far {hkK : k ≤ K} {hL : 2 ≤ S.L} {hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j}
    (hϱ : (2 * S.d * S.L : ℝ) ≤ (S.L : ℝ) * M * S.Rb) {j : ℕ} (hj : 1 ≤ j) (hjk : j < k)
    {z y : Torus S.d (M * n k * S.L ^ k)} (hz : z ∈ H.locFine Z M j)
    (hy : y ∈ (H.locGen Z M hkK hL hR).Ω (j + 1)) :
    (2 * S.d * (S.L : ℝ) ^ (j + 1) : ℝ) < Green.torusDist S.d (M * n k * S.L ^ k) z y := by
  have hyc := (mem_locGen_succ (hL := hL) (hR := hR) hjk).mp hy
  rw [← cubeMap_succ (hnn_k H hkK) (by omega) y] at hyc
  have hfar := ((H.locRH k Z).step j).fine_far (by omega) (hnn_k H hkK j hjk) hyc hz
  have hdist := torusDist_lower (d := S.d) (N := S.L ^ j * M) (m := n j)
    (ℓ := M * n k * S.L ^ k) (fine_eq (hnn_k H hkK) hjk.le)
    (Nat.pos_of_ne_zero (by have := NeZero.ne M; have := NeZero.ne S.L; positivity)) z y
  have hfar' : S.L * (⌊R j⌋₊ + 4) + 2 ≤
      supDist (blockMap (S.L ^ j * M) (n j) z) (blockMap (S.L ^ j * M) (n j) y) := by
    have h := hfar
    unfold cubeMap at h
    rw [supDist_comm] at h
    omega
  have hfarR : (S.L : ℝ) * ((⌊R j⌋₊ : ℝ) + 4) + 2 ≤
      (supDist (blockMap (S.L ^ j * M) (n j) z) (blockMap (S.L ^ j * M) (n j) y) : ℝ) := by
    exact_mod_cast hfar'
  have hρ := Nat.lt_floor_add_one (R j)
  have hRj := hR j hj hjk
  have hLpos : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hNpos : (0 : ℝ) < (S.L : ℝ) ^ j * M := by positivity
  have hN : (((S.L ^ j * M : ℕ)) : ℝ) = (S.L : ℝ) ^ j * M := by push_cast; ring
  rw [hN] at hdist
  have h1 := mul_le_mul_of_nonneg_left hfarR hNpos.le
  have h2 : S.Rb ≤ (⌊R j⌋₊ : ℝ) + 4 := by linarith
  have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hLpos.le) hNpos.le
  have h4 : (2 * S.d * (S.L : ℝ) ^ (j + 1) : ℝ) ≤ ((S.L : ℝ) ^ j * M) * (S.L * S.Rb) := by
    have : (2 * S.d * (S.L : ℝ) ^ (j + 1) : ℝ) = (2 * S.d * S.L) * (S.L : ℝ) ^ j := by ring
    rw [this]
    have hpow : (0 : ℝ) < (S.L : ℝ) ^ j := pow_pos hLpos j
    calc (2 * S.d * S.L) * (S.L : ℝ) ^ j ≤ ((S.L : ℝ) * M * S.Rb) * (S.L : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hϱ hpow.le
      _ = ((S.L : ℝ) ^ j * M) * (S.L * S.Rb) := by ring
  nlinarith

end RegionHistory

end Balaban.LargeField
