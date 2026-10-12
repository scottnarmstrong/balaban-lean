module

public import Balaban.LargeField.Region.Generating
import Mathlib.Tactic.Linarith

/-!
# The removal overwrite (Part I, Definition I.3.11, Lemma I.3.12)

If `R^{(k)}` removes a component `Zr` of `Z^pre_k` then, as fine sets, for `1 ≤ j ≤ k`
`Ω_j ↦ Ω_j ∪ Zr` (and likewise `Ω'_j`, `Ω''_j`), and `Z_j`, `P_j, …, S_j` lose `Zr`.

* `removeOverwrite`, `removeOverwriteDel`: the two operations on a family of fine sets;
* `overwriteGeneratingSet`: the abstract preservation of the generating-set conditions
  (Lemma I.3.12 (a)-(c)) from two hypotheses: `Zr` is a union of `k`-blocks, and `Zr` is far from the
  rest of the complements `Ω_jᶜ`, `j < k`;
* `flowOverwrite`: both hypotheses hold when `Zr` is (the fine set of) a component of `Z^pre_k` of
  the region sequence.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section Abstract

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L]

open Classical in
/-- Definition I.3.11 for the domains: `Ω_j ↦ Ω_j ∪ Zr` for `1 ≤ j ≤ k`. -/
def removeOverwrite (Ω : ℕ → Finset (Torus d (N₀ * L ^ K))) (k : ℕ)
    (Zr : Finset (Torus d (N₀ * L ^ K))) : ℕ → Finset (Torus d (N₀ * L ^ K)) :=
  fun j => if 1 ≤ j ∧ j ≤ k then Ω j ∪ Zr else Ω j

open Classical in
/-- Definition I.3.11 for the regions and the new cubes: `A_j ↦ A_j ∖ Zr` for `1 ≤ j ≤ k`. -/
def removeOverwriteDel (A : ℕ → Finset (Torus d (N₀ * L ^ K))) (k : ℕ)
    (Zr : Finset (Torus d (N₀ * L ^ K))) : ℕ → Finset (Torus d (N₀ * L ^ K)) :=
  fun j => if 1 ≤ j ∧ j ≤ k then A j \ Zr else A j

theorem isBlockUnion_of_le {j k : ℕ} (hjk : j ≤ k) (hkK : k ≤ K)
    {S : Finset (Torus d (N₀ * L ^ K))} (h : Multiscale.IsBlockUnion L N₀ K k S) :
    Multiscale.IsBlockUnion L N₀ K j S := by
  intro x x' hxx'
  apply h
  unfold Multiscale.jBlock at hxx' ⊢
  rw [blockMap_eq_iff_val (Multiscale.side_eq (le_trans hjk hkK))] at hxx'
  rw [blockMap_eq_iff_val (Multiscale.side_eq hkK)]
  intro i
  have h1 := hxx' i
  have e : L ^ k = L ^ j * L ^ (k - j) := by rw [← pow_add]; congr 1; omega
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h1]

theorem removeOverwrite_of {Ω : ℕ → Finset (Torus d (N₀ * L ^ K))} {k j : ℕ}
    {Zr : Finset (Torus d (N₀ * L ^ K))} (h : 1 ≤ j ∧ j ≤ k) :
    removeOverwrite Ω k Zr j = Ω j ∪ Zr := by
  simp [removeOverwrite, h]

theorem removeOverwrite_of_not {Ω : ℕ → Finset (Torus d (N₀ * L ^ K))} {k j : ℕ}
    {Zr : Finset (Torus d (N₀ * L ^ K))} (h : ¬ (1 ≤ j ∧ j ≤ k)) :
    removeOverwrite Ω k Zr j = Ω j := by
  simp [removeOverwrite, h]

/-- **Lemma I.3.12** (abstract form). Let `G` be a generating set, `1 ≤ k ≤ K`, `Zr` a union of
`k`-blocks that is far (`> ϱ L^j`) from `Ω_jᶜ ∖ Zr` for `1 ≤ j < k`. Then the overwritten family
`Ω_j ∪ Zr` (`j ≤ k`) is a generating set: nesting (a), block unions (b), separation (c). -/
def overwriteGeneratingSet {ϱ : ℝ} (G : Multiscale.GeneratingSet d L N₀ K ϱ) {k : ℕ} (hkK : k ≤ K)
    (Zr : Finset (Torus d (N₀ * L ^ K))) (hZ : Multiscale.IsBlockUnion L N₀ K k Zr)
    (hsep : ∀ j, 1 ≤ j → j < k → ∀ x, x ∉ G.Ω j → x ∉ Zr → ∀ y ∈ Zr,
      ϱ * (L : ℝ) ^ j < Green.torusDist d (N₀ * L ^ K) x y) :
    Multiscale.GeneratingSet d L N₀ K ϱ where
  Ω := removeOverwrite G.Ω k Zr
  top := by
    rw [removeOverwrite_of_not (by omega)]
    exact G.top
  subset := by
    intro j hj hjK x hx
    by_cases h1 : 1 ≤ j + 1 ∧ j + 1 ≤ k
    · rw [removeOverwrite_of h1] at hx
      rw [removeOverwrite_of ⟨hj, by omega⟩]
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ (G.subset j hj hjK hx)
      · exact Finset.mem_union_right _ hx
    · rw [removeOverwrite_of_not h1] at hx
      by_cases h2 : 1 ≤ j ∧ j ≤ k
      · rw [removeOverwrite_of h2]; exact Finset.mem_union_left _ (G.subset j hj hjK hx)
      · rw [removeOverwrite_of_not h2]; exact G.subset j hj hjK hx
  blockUnion := by
    intro j hj hjK x x' hxx'
    by_cases h : 1 ≤ j ∧ j ≤ k
    · rw [removeOverwrite_of h]
      have h1 := G.blockUnion j hj hjK x x' hxx'
      have h2 := isBlockUnion_of_le h.2 hkK hZ x x' hxx'
      simp only [Finset.mem_union, h1, h2]
    · rw [removeOverwrite_of_not h]
      exact G.blockUnion j hj hjK x x' hxx'
  separation := by
    intro j hj hjK x hx y hy
    by_cases h1 : 1 ≤ j + 1 ∧ j + 1 ≤ k
    · rw [removeOverwrite_of h1] at hy
      rw [removeOverwrite_of ⟨hj, by omega⟩] at hx
      have hxG : x ∉ G.Ω j := fun h => hx (Finset.mem_union_left _ h)
      have hxZ : x ∉ Zr := fun h => hx (Finset.mem_union_right _ h)
      rcases Finset.mem_union.mp hy with hy | hy
      · exact G.separation j hj hjK x hxG y hy
      · exact hsep j hj (by omega) x hxG hxZ y hy
    · rw [removeOverwrite_of_not h1] at hy
      by_cases h2 : 1 ≤ j ∧ j ≤ k
      · rw [removeOverwrite_of h2] at hx
        exact G.separation j hj hjK x (fun h => hx (Finset.mem_union_left _ h)) y hy
      · rw [removeOverwrite_of_not h2] at hx
        exact G.separation j hj hjK x hx y hy

end Abstract

/-! ### The overwrite for the region sequence -/

section Flow

variable {d L M : ℕ} [NeZero L] [NeZero M] {nn : ℕ → ℕ} [∀ i, NeZero (nn i)] {Rbase : ℝ}
  {lam R : ℕ → ℝ} {crit : ℕ → Option ℕ} (S : RegionSeq d L nn Rbase lam R crit)

variable (M) in
open Classical in
/-- The fine set of a set `Y` of cubes of `𝕋_k`. -/
noncomputable def fineCubes (K k : ℕ) (Y : Finset (Torus d (nn k))) :
    Finset (Torus d (M * nn K * L ^ K)) :=
  Finset.univ.filter fun x => cubeMap nn L M K k x ∈ Y

theorem mem_fineCubes {K k : ℕ} {Y : Finset (Torus d (nn k))} {x : Torus d (M * nn K * L ^ K)} :
    x ∈ fineCubes (nn := nn) (L := L) M K k Y ↔ cubeMap nn L M K k x ∈ Y := by
  classical
  simp [fineCubes]

theorem fineCubes_isBlockUnion (hnn : ∀ i, nn i = L * nn (i + 1)) {K k : ℕ} (hkK : k ≤ K)
    (Y : Finset (Torus d (nn k))) :
    Multiscale.IsBlockUnion L (M * nn K) K k (fineCubes (nn := nn) (L := L) M K k Y) := by
  intro x x' hxx'
  rw [mem_fineCubes, mem_fineCubes, ← cubeMap_eq_comp hnn hkK, ← cubeMap_eq_comp hnn hkK x',
    hxx']

/-- Regions grow (Lemma I.4.3 for the no-removal sequence): a cube of `Z_{i+1}` has its ancestor
cubes in `Z_{i+1+t}`. -/
theorem RegionSeq.Z_grow {K : ℕ} (i : ℕ) (x : Torus d (M * nn K * L ^ K))
    (hx : cubeMap nn L M K (i + 1) x ∈ (S.step (i + 1)).Z) :
    ∀ t, i + 1 + t ≤ K → cubeMap nn L M K (i + 1 + t) x ∈ (S.step (i + 1 + t)).Z := by
  intro t
  induction t with
  | zero => intro _; exact hx
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    have h2 : blockMap L (nn (i + 1 + t + 1)) (cubeMap nn L M K (i + 1 + t) x) ∈
        (S.step (i + 1 + t)).Uprime := (S.step (i + 1 + t)).blockMap_Z_subset_Uprime h1
    rw [cubeMap_succ S.hnn (by omega)] at h2
    have h3 := (S.step (i + 1 + t)).Z0_subset_Zpre (omegaW L Rbase lam (i + 1 + t + 1)) (crit (i + 1 + t + 1))
      ((S.step (i + 1 + t)).Uprime_subset_Z0 h2)
    rw [← S.Z_succ (i + 1 + t)] at h3
    rw [show i + 1 + (t + 1) = i + 1 + t + 1 by ring]
    exact h3

/-- **Lemma I.3.12 (c)**, geometric input: the fine set of a component `Y` of `Z_k` is at fine
distance `> ϱ L^j` (`ϱ = L M R_base`, `j < k`) from every fine site outside `Y` whose `𝕋_j`-cube
lies in `Z_j`. Needs `R_base ≥ 0`, `λ ≥ 1`. -/
theorem flow_overwrite_sep (hRH : RadiusHyp L Rbase lam R) (hL : 2 ≤ L) {K k : ℕ}
    (hk1 : 1 ≤ k) (hkK : k ≤ K) {Y : Finset (Torus d (nn k))}
    (hY : Y ∈ comps (omegaW L Rbase lam k) (finOf (S.step k).Z))
    {j : ℕ} (hj : 1 ≤ j) (hjk : j < k) {x : Torus d (M * nn K * L ^ K)}
    (hxj : cubeMap nn L M K j x ∈ (S.step j).Z)
    (hxY : x ∉ fineCubes (nn := nn) (L := L) M K k Y) {y : Torus d (M * nn K * L ^ K)}
    (hy : y ∈ fineCubes (nn := nn) (L := L) M K k Y) :
    ((L : ℝ) * M * Rbase) * (L : ℝ) ^ j < Green.torusDist d (M * nn K * L ^ K) x y := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hgrow := S.Z_grow i x hxj (k - (i + 1)) (by omega)
  rw [show i + 1 + (k - (i + 1)) = k by omega] at hgrow
  have hxk : cubeMap nn L M K k x ∈ (S.step k).Z := hgrow
  obtain ⟨Y2, hY2, hxY2⟩ := mem_comp_self (ω := omegaW L Rbase lam k)
    (mem_finOf.mpr hxk : cubeMap nn L M K k x ∈ finOf (S.step k).Z)
  have hne : Y2 ≠ Y := by
    rintro rfl
    exact hxY (mem_fineCubes.mpr hxY2)
  have hsep := comps_sep hY2 hY hne hxY2 (mem_fineCubes.mp hy)
  have hdist := torusDist_lower (d := d) (N := L ^ k * M) (m := nn k)
    (ℓ := M * nn K * L ^ K) (fine_eq S.hnn hkK)
    (Nat.pos_of_ne_zero (by have := NeZero.ne M; have := NeZero.ne L; positivity)) x y
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hNpos : (0 : ℝ) < (L : ℝ) ^ k * M := by positivity
  have hN : (((L ^ k * M : ℕ)) : ℝ) = (L : ℝ) ^ k * M := by push_cast; ring
  rw [hN] at hdist
  -- the width
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hRb : 0 ≤ Rbase := by linarith [hRH.base, (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hlam2 : 1 ≤ lam k' ^ 2 := one_le_pow₀ (hRH.one_le k')
  have hfl : ⌊Rbase⌋₊ ≤ ⌊Rbase * lam k' ^ 2⌋₊ :=
    Nat.floor_le_floor (le_mul_of_one_le_right hRb hlam2)
  have hflt := Nat.lt_floor_add_one Rbase
  have hω : (Rbase + 1 : ℝ) ≤ (omegaW L Rbase lam (k' + 1) : ℝ) := by
    have h1 : (⌊Rbase⌋₊ : ℝ) ≤ ⌊Rbase * lam k' ^ 2⌋₊ := by exact_mod_cast hfl
    simp only [omegaW]
    push_cast
    linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hD : (omegaW L Rbase lam (k' + 1) : ℝ) ≤
      (supDist (blockMap (L ^ (k' + 1) * M) (nn (k' + 1)) x)
        (blockMap (L ^ (k' + 1) * M) (nn (k' + 1)) y) : ℝ) := by
    exact_mod_cast hsep
  have h1 := mul_le_mul_of_nonneg_left hD hNpos.le
  -- `L^(i+1) ≤ L^k'`
  have hpow : (L : ℝ) ^ (i + 1) ≤ (L : ℝ) ^ k' :=
    pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ L)) (by omega)
  have hϱ : (0 : ℝ) ≤ (L : ℝ) * M * Rbase := by positivity
  have e : (L : ℝ) * M * Rbase * (L : ℝ) ^ k' = ((L : ℝ) ^ (k' + 1) * M) * Rbase := by ring
  have h2 := mul_le_mul_of_nonneg_left hpow hϱ
  nlinarith

/-- **Lemma I.3.12** for the region sequence: removing a component `Y` of `Z^pre_k` keeps the
domains a generating set. -/
noncomputable def flowOverwrite (hRH : RadiusHyp L Rbase lam R) (hL : 2 ≤ L) (K : ℕ)
    (hR : ∀ j, 1 ≤ j → j < K → Rbase ≤ R j) {k : ℕ} (hk1 : 1 ≤ k) (hkK : k ≤ K)
    (Y : Finset (Torus d (nn k))) (hY : Y ∈ comps (omegaW L Rbase lam k) (finOf (S.step k).Z)) :
    Multiscale.GeneratingSet d L (M * nn K) K ((L : ℝ) * M * Rbase) :=
  overwriteGeneratingSet (flowGeneratingSet M S hL K hR) hkK
    (fineCubes (nn := nn) (L := L) M K k Y) (fineCubes_isBlockUnion S.hnn hkK Y)
    (by
      intro j hj hjk x hx hxY y hy
      have hx' : x ∉ flowOmega M S K j := hx
      rw [mem_flowOmega] at hx'
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hxj : cubeMap nn L M K (i + 1) x ∉ S.OmegaAt (i + 1) := fun h => hx' ⟨by omega, h⟩
      exact flow_overwrite_sep S hRH hL hk1 hkK hY hj hjk (S.OmegaAt_compl_subset_Z i hxj) hxY hy)

end Flow

end Balaban.LargeField
