module

public import Balaban.LargeField.Region.Locality
public import Balaban.Multiscale.GeneratingSet
public import Balaban.Green.BlockDistance
import Mathlib.Tactic.Linarith

/-!
# The region sequence and its generating set (Part I, Lemma I.3.10)

`RegionSeq` is the sequence of steps `𝕋_i → 𝕋_{i+1}` of Definition I.3.1 with
`Z_{i+1} = Z^pre_{i+1}` (no removals; removals are Lemma I.3.12, see `Overwrite`). The domains
`Ω_j = (step (j-1)).Omega ⊆ 𝕋_j` give a `Balaban.Multiscale.GeneratingSet`
(`flowGeneratingSet`), as fine sets: the cube `x ∈ 𝕋_j` is the fibre of `x` under
`blockMap (L^j * M) (nn j)` (`cubeMap`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

/-! ### Distances: cyclic norm versus the `ℓ¹` torus distance -/

section Dist

variable {d : ℕ}

theorem cycNorm_le_natAbs_cycRep {m : ℕ} [NeZero m] (a : ZMod m) :
    cycNorm m a ≤ (Green.cycRep a).natAbs := by
  rw [cycNorm_le_iff]
  refine ⟨Green.cycRep a, ?_, Green.cast_cycRep a⟩
  rw [Int.abs_eq_natAbs]

theorem supDist_le_torusDist {m : ℕ} [NeZero m] (x y : Torus d m) :
    (supDist x y : ℝ) ≤ Green.torusDist d m x y := by
  have : supDist x y ≤ ∑ i, (Green.cycRep (x i - y i)).natAbs := by
    refine supDist_le_iff.mpr fun i => ?_
    exact (cycNorm_le_natAbs_cycRep _).trans
      (Finset.single_le_sum (f := fun i => (Green.cycRep (x i - y i)).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  unfold Green.torusDist
  exact_mod_cast this

/-- Fine versus coarse distance: `N D + 1 ≤ torusDist + N` where `D` is the coarse index
distance of the blocks. -/
theorem torusDist_lower {N m ℓ : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N)
    (x y : Torus d ℓ) :
    (N : ℝ) * supDist (blockMap N m x) (blockMap N m y) + 1 ≤ Green.torusDist d ℓ x y + N := by
  have h1 := supDist_blockMap_le (L := N) (m := m) (n := ℓ) hℓ x y
  have h2 : supDist (blockMap N m x) (blockMap N m y) * N ≤ supDist x y + N - 1 :=
    (Nat.le_div_iff_mul_le hN).mp h1
  have h3 : N * supDist (blockMap N m x) (blockMap N m y) + 1 ≤ supDist x y + N := by
    rw [mul_comm]; omega
  have h4 : ((N * supDist (blockMap N m x) (blockMap N m y) + 1 : ℕ) : ℝ) ≤
      (supDist x y : ℝ) + N := by exact_mod_cast h3
  push_cast at h4
  linarith [supDist_le_torusDist x y]

end Dist

/-! ### The region sequence -/

/-- The steps `i → i+1` for all `i`, with `Z_{i+1} = Z^pre_{i+1}` (the widths are
`ω_{i+1} = omegaW (i+1)`; `crit i` is `none` once `i > k₀`, otherwise the critical side).
`nn i` is the cube-torus side `n_i`, `nn i = L * nn (i+1)` for the scales `i < K` below the
horizon `K` (the flow runs from scale `0` to the top scale `K`; a relation `nn i = L * nn (i+1)` for
all `i` would be contradictory). -/
structure RegionSeq (d L : ℕ) (nn : ℕ → ℕ) [∀ i, NeZero (nn i)] (Rbase : ℝ) (lam R : ℕ → ℝ)
    (crit : ℕ → Option ℕ) (K : ℕ) where
  hnn : ∀ i, i < K → nn i = L * nn (i + 1)
  step : ∀ i, RegionStep d L (nn i) (nn (i + 1)) (R (i - 1)) (R i)
  Z_zero : (step 0).Z = ∅
  Z_succ : ∀ i, (step (i + 1)).Z = (step i).Zpre (omegaW L Rbase lam (i + 1)) (crit (i + 1))

namespace RegionSeq

variable {d L : ℕ} {nn : ℕ → ℕ} [∀ i, NeZero (nn i)] {Rbase : ℝ} {lam R : ℕ → ℝ}
  {crit : ℕ → Option ℕ} {K : ℕ} (S : RegionSeq d L nn Rbase lam R crit K)

/-- The domain `Ω_j ⊆ 𝕋_j` (`Ω_0 = ∅`, `Ω_{i+1}` is the output of the step `i`). -/
def OmegaAt : ∀ j, Set (Torus d (nn j))
  | 0 => ∅
  | i + 1 => (S.step i).Omega

@[simp] theorem OmegaAt_succ (i : ℕ) : S.OmegaAt (i + 1) = (S.step i).Omega := rfl

/-- `Ω_{i+1}ᶜ ⊆ Z^pre_{i+1}`. -/
theorem Omega_compl_subset_Zpre (i : ℕ) (ω : ℕ) (c : Option ℕ) :
    ((S.step i).Omega)ᶜ ⊆ (S.step i).Zpre ω c := by
  intro x hx
  by_contra hxn
  exact hx ((S.step i).OmegaDD_subset_Omega ((S.step i).Zpre_compl_subset_OmegaDD ω c hxn))

/-- `Ω_{j}ᶜ ⊆ Z_j` for `j ≥ 1`. -/
theorem OmegaAt_compl_subset_Z (i : ℕ) : (S.OmegaAt (i + 1))ᶜ ⊆ (S.step (i + 1)).Z := by
  rw [S.Z_succ i]
  exact S.Omega_compl_subset_Zpre i _ _

end RegionSeq

theorem nn_eq_pow {L : ℕ} {nn : ℕ → ℕ} {K : ℕ} (hnn : ∀ i, i < K → nn i = L * nn (i + 1))
    (j t : ℕ) (hjt : j + t ≤ K) : nn j = nn (j + t) * L ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [ih (by omega), hnn (j + t) (by omega), pow_succ, ← add_assoc]
    ring

theorem nn_eq_pow' {L : ℕ} {nn : ℕ → ℕ} {K : ℕ} (hnn : ∀ i, i < K → nn i = L * nn (i + 1))
    {j : ℕ} (h : j ≤ K) : nn j = nn K * L ^ (K - j) := by
  have := nn_eq_pow hnn j (K - j) (by omega)
  rwa [show j + (K - j) = K by omega] at this

/-! ### Fine sets and the generating set -/

section Flow

variable {d L M : ℕ} [NeZero L] {nn : ℕ → ℕ} [∀ i, NeZero (nn i)] {Rbase : ℝ} {lam R : ℕ → ℝ}
  {crit : ℕ → Option ℕ}

/-- The cube of `𝕋_j` containing a fine site: the fibre of `blockMap (L^j * M) (nn j)`. The fine
torus is `Torus d (M * nn K * L ^ K)`. -/
def cubeMap (nn : ℕ → ℕ) (L M K j : ℕ) (x : Torus d (M * nn K * L ^ K)) : Torus d (nn j) :=
  blockMap (L ^ j * M) (nn j) x

variable [NeZero M]

theorem fine_eq {K : ℕ} (hnn : ∀ i, i < K → nn i = L * nn (i + 1)) {j : ℕ} (hjK : j ≤ K) :
    M * nn K * L ^ K = L ^ j * M * nn j := by
  rw [nn_eq_pow' hnn hjK]
  have : L ^ K = L ^ j * L ^ (K - j) := by rw [← pow_add]; congr 1; omega
  rw [this]; ring

theorem cubeMap_eq_comp {K : ℕ} (hnn : ∀ i, i < K → nn i = L * nn (i + 1)) {j : ℕ} (hjK : j ≤ K)
    (x : Torus d (M * nn K * L ^ K)) :
    blockMap M (nn j) (Multiscale.jBlock d L (M * nn K) K j x) = cubeMap nn L M K j x := by
  unfold Multiscale.jBlock cubeMap
  rw [blockMap_comp (Multiscale.side_eq hjK)]
  rw [nn_eq_pow' hnn hjK]; ring

theorem cubeMap_succ {K : ℕ} (hnn : ∀ i, i < K → nn i = L * nn (i + 1)) {j : ℕ} (hjK : j + 1 ≤ K)
    (x : Torus d (M * nn K * L ^ K)) :
    blockMap L (nn (j + 1)) (cubeMap nn L M K j x) = cubeMap nn L M K (j + 1) x := by
  unfold cubeMap
  have h := blockMap_comp (d := d) (ℓ := M * nn K * L ^ K) (N := L ^ j * M) (m₁ := nn j)
    (m₂ := nn (j + 1)) (M := L) (fine_eq hnn (by omega)) (hnn j (by omega)) x
  rw [h, show L ^ j * M * L = L ^ (j + 1) * M by ring]

variable (M)

open Classical in
/-- The fine domain `Ω_j` (`1 ≤ j ≤ K`; empty for `j > K`): the sites whose `𝕋_j`-cube lies in
`Ω_j`. -/
noncomputable def flowOmega {K₀ : ℕ} (S : RegionSeq d L nn Rbase lam R crit K₀) (K j : ℕ) :
    Finset (Torus d (M * nn K * L ^ K)) :=
  if j ≤ K then Finset.univ.filter fun x => cubeMap nn L M K j x ∈ S.OmegaAt j else ∅

theorem mem_flowOmega {K₀ : ℕ} (S : RegionSeq d L nn Rbase lam R crit K₀) {K j : ℕ}
    {x : Torus d (M * nn K * L ^ K)} :
    x ∈ flowOmega M S K j ↔ j ≤ K ∧ cubeMap nn L M K j x ∈ S.OmegaAt j := by
  classical
  unfold flowOmega
  split_ifs with h
  · simp [h]
  · simp [h]

variable {K : ℕ} (S : RegionSeq d L nn Rbase lam R crit K)

/-- **Lemma I.3.10 (a)**, nesting: a cube of `𝕋_{i+1}` over a cube of `Ω_{i+2}` lies in
`Ω''_{i+1}` (so `Ω_{j+1} ⊆ Z_jᶜ ⊆ Ω''_j ⊆ Ω_j`). -/
theorem RegionSeq.nesting (hL : 0 < L) (i : ℕ) (hi : i + 1 < K) {y : Torus d (nn (i + 1))}
    (hy : blockMap L (nn (i + 1 + 1)) y ∈ (S.step (i + 1)).Omega) : y ∈ (S.step i).OmegaDD := by
  have h1 := (S.step (i + 1)).not_mem_Z_of_mem_Omega hL (S.hnn (i + 1) hi) hy
  rw [S.Z_succ i] at h1
  by_contra h2
  exact h1 ((S.step i).OmegaDD_compl_subset_Z0 h2 |> (S.step i).Z0_subset_Zpre _ _)

/-- **Lemma I.3.10**: the domains of the region sequence form a `GeneratingSet` with
`ϱ = L M R_base` (fields: `top` is the terminal `Ω_{K+1} = ∅`; `subset`, `blockUnion`, `separation`
by (a), (b), (c); `separation` needs `R_j ≥ R_base`, audit P1-04). -/
noncomputable def flowGeneratingSet (hL : 2 ≤ L)
    (hR : ∀ j, 1 ≤ j → j < K → Rbase ≤ R j) :
    Multiscale.GeneratingSet d L (M * nn K) K ((L : ℝ) * M * Rbase) where
  Ω := flowOmega M S K
  top := by
    ext x
    simp [flowOmega]
  subset := by
    intro j hj hjK x hx
    rw [mem_flowOmega] at hx ⊢
    obtain ⟨hj1, hx⟩ := hx
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    refine ⟨hjK, ?_⟩
    have hy : blockMap L (nn (i + 1 + 1)) (cubeMap nn L M K (i + 1) x) ∈ (S.step (i + 1)).Omega := by
      rw [cubeMap_succ S.hnn (by omega)]; exact hx
    exact (S.step i).OmegaDD_subset_Omega (S.nesting (by omega) i (by omega) hy)
  blockUnion := by
    intro j hj hjK x x' hxx'
    rw [mem_flowOmega, mem_flowOmega]
    have h1 := cubeMap_eq_comp S.hnn hjK x
    have h2 := cubeMap_eq_comp S.hnn hjK x'
    have : cubeMap nn L M K j x = cubeMap nn L M K j x' := by
      rw [← h1, ← h2]; exact congrArg _ hxx'
    rw [this]
  separation := by
    intro j hj hjK x hx y hy
    rw [mem_flowOmega] at hx hy
    obtain ⟨-, hy⟩ := hy
    have hx' : cubeMap nn L M K j x ∉ S.OmegaAt j := fun h => hx ⟨by omega, h⟩
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hz : cubeMap nn L M K (i + 1) x ∈ (S.step (i + 1)).Z := S.OmegaAt_compl_subset_Z i hx'
    have hyc : blockMap L (nn (i + 1 + 1)) (cubeMap nn L M K (i + 1) y) ∈
        (S.step (i + 1)).Omega := by
      rw [cubeMap_succ S.hnn (by omega)]; exact hy
    have hfar := (S.step (i + 1)).fine_far (by omega) (S.hnn (i + 1) (by omega)) hyc hz
    have hdist := torusDist_lower (d := d) (N := L ^ (i + 1) * M) (m := nn (i + 1))
      (ℓ := M * nn K * L ^ K) (fine_eq S.hnn (by omega))
      (Nat.pos_of_ne_zero (by have := NeZero.ne M; have := NeZero.ne L; positivity)) x y
    have hfar' : L * (⌊R (i + 1)⌋₊ + 4) + 2 ≤
        supDist (blockMap (L ^ (i + 1) * M) (nn (i + 1)) x)
          (blockMap (L ^ (i + 1) * M) (nn (i + 1)) y) := by
      have h := hfar
      unfold cubeMap at h
      rw [supDist_comm] at h
      omega
    have hfarR : (L : ℝ) * ((⌊R (i + 1)⌋₊ : ℝ) + 4) + 2 ≤
        (supDist (blockMap (L ^ (i + 1) * M) (nn (i + 1)) x)
          (blockMap (L ^ (i + 1) * M) (nn (i + 1)) y) : ℝ) := by
      exact_mod_cast hfar'
    have hρ := Nat.lt_floor_add_one (R (i + 1))
    have hRj := hR (i + 1) (by omega) (by omega)
    have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
    have hNpos : (0 : ℝ) < (L : ℝ) ^ (i + 1) * M := by positivity
    have hN : (((L ^ (i + 1) * M : ℕ)) : ℝ) = (L : ℝ) ^ (i + 1) * M := by push_cast; ring
    rw [hN] at hdist
    have h1 := mul_le_mul_of_nonneg_left hfarR hNpos.le
    have h2 : Rbase ≤ (⌊R (i + 1)⌋₊ : ℝ) + 4 := by linarith
    have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hLpos.le) hNpos.le
    have e : (L : ℝ) * M * Rbase * (L : ℝ) ^ (i + 1) =
        ((L : ℝ) ^ (i + 1) * M) * ((L : ℝ) * Rbase) := by ring
    rw [e]
    nlinarith

end Flow

end Balaban.LargeField
