/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldHS2
public import Balaban.Spine.LFOldH7Refute
public import Balaban.Spine.LFOldD7Reads

/-!
# The H7 domain of scale `k + 1` leaves `ψ_k` free next to `Ω_{k+1}` (finding of W1154c)

The H7 domain of scale `k + 1` (Definition II.3.5 (c), (d)) reads the component `ψ_k` of the multiscale
field through three kinds of cube tests: `Δ^c_k(□)` at the cubes `□` of `𝕋_k` with no cube of `𝕋_{k+1}`
in `Ω^{∼3}_{k+1}`, `Δ'^c_{k+1}(□')` at the cubes of `𝕋_{k+1}` in `Ω^{∼3}_{k+1} ∩ (Ω^c_{k+1})^{∼3}`, and
`Δ'^c_k(□)` at the cubes of `𝕋_k` in `Ω^{∼3}_k ∩ (Ω^c_k)^{∼3}`, where `Ω^c_j = Z_j ∖ Ω_j` (`omegaCNb`).
Each test reads the blocks of the cubes within `3` cubes of its own (`deltaC_stencil`,
`deltaPrimeC_stencil`).  So on a `k`-block whose cube of `𝕋_{k+1}` lies within `2` cubes of `Ω_{k+1}`
(and `L ≥ 3`), farther than `3` cubes from `(Ω^c_{k+1})^{∼3}` and whose cube of `𝕋_k` lies farther than
`3` cubes from `(Ω^c_k)^{∼3}`, no test reads `ψ_k`.

The datum of the local pair of reading HS-2 (`holeStepLoc2`) reads `ψ_k` at its data sites off `Ω_{k+1}`,
and the local sets `V₂(X, J)` reach one cube of `𝕋_{k+1}` beyond `Ω_{k+1}` (`r′ ≥ L^{k+1+m₁}`).  At such a
site in the unread band the named input `H7MixedDatumLoc2` fails.

* `h7Domain_succ_congr_k`: two multiscale fields differing only in the component `k`, on blocks of the
  unread band, lie in the H7 domain of scale `k + 1` together; `notMem_nbhd_omegaCNb_of_far` (a cube at
  distance `≥ 7` from `Z_{i+1} ∖ Ω_{i+1}` is not within `3` cubes of `(Ω^c_{i+1})^{∼3}`);
* `mem_stepG'_top_iff`, `holeStepLoc2_D'_Ψ_of_notMem`: the datum of the local pair at a data site off
  `Ω_{k+1}` is `ψ_k` at its block;
* `exists_h7Domain_not_inDomainC_of_site`, `not_h7MixedDatumLoc2_of_site`: **the failure**: a data site
  of `G′_V` off `Ω_{k+1}` in the unread band gives a field of the H7 domain of scale `k + 1` whose datum is
  outside `Ψ̃^c(G′_V; δ_b, δ_b)` (the existence of the site is a hypothesis);
* `mem_omegaCNb_of_notMem_omega`, `rem_ne_empty_of_far`: **the band is unread only at a removal**: when
  `R^{(k+1)}` removes no component, every cube off `Ω_{k+1}` lies in `Z_{k+1} ∖ Ω_{k+1}` (Lemma I.3.5 (e)), so the
  holes of the H7 domain are the printed `(𝕋_{k+1} ∖ Ω_{k+1})^{∼3}` and the hypotheses of the failure lemma force
  `Rem_{k+1} ≠ ∅`: the unread band lies around the holes of `Ω_{k+1}` in the components removed by `R^{(k+1)}`
  (`Z_{k+1} = Z^pre_{k+1} ∖ ⋃ Rem_{k+1}`).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background

namespace Balaban.RootFSpine

section Free

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}

/-- The cubes of `(Ω^c_{i+1})^{∼r}` of the H7 domain of a global history are within `r` of a cube of
`Z_{i+1} ∖ Ω_{i+1}`. -/
theorem exists_near_of_mem_omegaCNb (hnn : ∀ i, i < K → n i = S.L * n (i + 1))
    (H : RegionHistory S n R k0 K) {i r : ℕ} (hi : i + 1 ≤ K) {y : Torus S.d (n (i + 1))}
    (hy : y ∈ omegaCNb (globalLH H M) r (i + 1)) :
    ∃ v ∈ (H.step (i + 1)).Z \ (H.step i).Omega, LargeField.supDist y v ≤ r := by
  obtain ⟨v, hv, hd⟩ := mem_nbhd.1 hy
  obtain ⟨x, hx⟩ := cubeMap_surjective (S := S) (M := M) hnn hi v
  have h1 := hv x hx
  simp only [globalLH, Nat.add_sub_cancel, fineSet, Set.mem_sdiff, Set.mem_ofPred_eq, hx] at h1
  exact ⟨v, h1, hd⟩

omit [NeZero M] [NeZero S.L] in
/-- The cubes of `Ω_{k+1}` are cubes of the fine set `Ω_{k+1}` of the global history. -/
theorem cubeSub_omega_of_mem (H : RegionHistory S n R k0 K) {k : ℕ} {y : Torus S.d (n (k + 1))}
    (hy : y ∈ (H.step k).Omega) :
    CubeSub (S := S) (n := n) M K (k + 1) y ((globalLH H M).Omega k) := fun x hx => by
  show LargeField.cubeMap n S.L M K (k + 1) x ∈ (H.step k).Omega
  rw [hx]; exact hy

omit [NeZero M] [NeZero S.L] in
/-- **Without a removal at scale `i + 1` the holes of `Ω_{i+1}` are holes of the H7 domain**: if `R^{(i+1)}`
removes no component (`Rem_{i+1} = ∅`, in particular for `i + 1 > k₀`), every cube of `𝕋_{i+1}` outside
`Ω_{i+1}` lies in `Z_{i+1} ∖ Ω_{i+1}` (`Ω^c_{i+1} ⊆ Z^{(0)}_{i+1} ⊆ Z^pre_{i+1}`, Lemma I.3.5 (e)), hence in
`(Ω^c_{i+1})^{∼r}` (`omegaCNb`): on such histories `Z_{i+1} ∖ Ω_{i+1}` is the complement of `Ω_{i+1}`. -/
theorem mem_omegaCNb_of_notMem_omega (H : RegionHistory S n R k0 K) {i r : ℕ}
    (hrem : H.rem (i + 1) = ∅) {u : Torus S.d (n (i + 1))} (hu : u ∉ (H.step i).Omega) :
    u ∈ omegaCNb (globalLH H M) r (i + 1) := by
  refine mem_nbhd.2 ⟨u, fun x hx => ?_, by rw [LargeField.supDist_self]; exact Nat.zero_le _⟩
  simp only [globalLH, Nat.add_sub_cancel, fineSet, Set.mem_sdiff, Set.mem_ofPred_eq, hx]
  refine ⟨?_, hu⟩
  show u ∈ (H.F.step (i + 1)).Z
  rw [H.Z_eq (i + 1), hrem]
  simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.sdiff_empty]
  exact (H.step i).Z0_subset_Zpre _ _ ((H.step i).Omega_compl_subset_Z0 hu)

omit [NeZero M] [NeZero S.L] in
/-- **The unread band exists only at a removal** (correction of the W1154c finding): a cube of `𝕋_{k+1}`
outside `Ω_{k+1}` and farther than `3` cubes from `(Ω^c_{k+1})^{∼3}` (the hypotheses `hxΩ`, `hB` of
`exists_h7Domain_not_inDomainC_of_site`) forces `Rem_{k+1} ≠ ∅` (so `1 ≤ k + 1 ≤ k₀`). -/
theorem rem_ne_empty_of_far (H : RegionHistory S n R k0 K) {k : ℕ} {u : Torus S.d (n (k + 1))}
    (hu : u ∉ (H.step k).Omega) (hB : u ∉ nbhd 3 (omegaCNb (globalLH H M) 3 (k + 1))) :
    H.rem (k + 1) ≠ ∅ := fun hrem =>
  hB (subset_nbhd 3 _ (mem_omegaCNb_of_notMem_omega H hrem hu))

variable (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1))

/-- **The H7 domain of scale `k + 1` does not read `ψ_k` near `Ω_{k+1}`, away from the holes**: one
direction of `h7Domain_succ_congr_k`. -/
theorem h7Domain_succ_of_congr_k (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hL : 3 ≤ S.L) {Yf : Set (Torus S.d (M * n K * S.L ^ K))} {aw μs ε ε1 νs : ℕ → ℝ}
    {h : Fin N → ℂ} {ψ ψ₂ ψ' : MultiFieldC S n M K N}
    {gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ}
    (hj : ∀ j, j ≠ k → ψ₂ j = ψ j)
    (hfree : ∀ x : Torus S.d (M * n K * S.L ^ K),
      ψ₂ k (jBlock S.d S.L (M * n K) K k x) ≠ ψ k (jBlock S.d S.L (M * n K) K k x) →
      LargeField.cubeMap n S.L M K (k + 1) x ∈ nbhd 2 (H.step k).Omega ∧
      LargeField.cubeMap n S.L M K (k + 1) x ∉ nbhd 3 (omegaCNb (globalLH H M) 3 (k + 1)) ∧
      LargeField.cubeMap n S.L M K k x ∉ nbhd 3 (omegaCNb (globalLH H M) 3 k))
    (hdom : H7Domain g.M1 g.c g.hM hnn (globalLH H M) (k + 1) hk Yf aw μs ε ε1 νs h ψ ψ' gf) :
    H7Domain g.M1 g.c g.hM hnn (globalLH H M) (k + 1) hk Yf aw μs ε ε1 νs h ψ₂ ψ' gf := by
  have hc := g.hc
  have hkK : k ≤ K := Nat.le_of_succ_le hk
  obtain ⟨h1, h2, h3, h4⟩ := hdom
  refine ⟨?_, ?_, h3, h4⟩
  · intro j hjk y hyX hfar hyC
    by_cases hjk' : j = k
    · subst hjk'
      have ht := h1 j hjk y hyX hfar hyC
      refine (deltaC_stencil aw (μs j) (ε j) h (by omega) (by omega) (by simp) y
        fun x hx => ?_).1 ht
      by_contra hne
      set x'' := LargeField.torusCast (histScale_top g.hM hnn hkK) x with hx''
      have e := jBlock_torusCast_top g.hM hnn le_rfl hkK x
      have hne' : ψ₂ j (jBlock S.d S.L (M * n K) K j x'') ≠ ψ j (jBlock S.d S.L (M * n K) K j x'') := by
        rw [e]; exact fun h' => hne h'.symm
      obtain ⟨hA, -, -⟩ := hfree x'' hne'
      have hu : LargeField.cubeMap n S.L M K j x'' ∈ nbhd 3 ({y} : Set (Torus S.d (n j))) := by
        rw [hx'', cubeMap_torusCast_top g.hM hnn hkK]; exact hx
      obtain ⟨x₀, hx₀⟩ := cubeMap_surjective (S := S) (M := M) hnn hkK y
      refine hfar x₀ hx₀ ?_
      unfold omegaNb
      simp only [show j + 1 ≠ j + 1 + 1 by omega, ↓reduceIte]
      obtain ⟨ω, hω, hdω⟩ := mem_nbhd.1 hA
      refine mem_nbhd.2 ⟨ω, cubeSub_omega_of_mem H hω, ?_⟩
      obtain ⟨z, hz, hdz⟩ := mem_nbhd.1 hu
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have hb : LargeField.supDist (LargeField.cubeMap n S.L M K (j + 1) x₀)
          (LargeField.cubeMap n S.L M K (j + 1) x'') ≤ 1 := by
        rw [← cubeMap_succ hnn hk x₀, ← cubeMap_succ hnn hk x'', hx₀]
        refine (supDist_blockMap_le (hnn j (by omega)) _ _).trans ?_
        rw [LargeField.supDist_comm] at hdz
        have : (LargeField.supDist (LargeField.cubeMap n S.L M K j x₀)
            (LargeField.cubeMap n S.L M K j x'') + S.L - 1) < 2 * S.L := by
          rw [hx₀]; omega
        exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 (by omega))
      have := LargeField.supDist_triangle (LargeField.cubeMap n S.L M K (j + 1) x₀)
        (LargeField.cubeMap n S.L M K (j + 1) x'') ω
      omega
    · rw [hj j hjk']
      exact h1 j hjk y hyX hfar hyC
  · intro i hik y hyX hyΩ hyC
    rcases Nat.lt_or_ge (i + 1) k with hi | hi
    · rw [hj i (by omega), hj (i + 1) (by omega)]
      exact h2 i hik y hyX hyΩ hyC
    rcases Nat.lt_or_ge i k with hi' | hi'
    · -- the pair `(ψ_{k-1}, ψ_k)` at the cubes of `𝕋_k` near the holes of `Ω_k`
      obtain rfl : k = i + 1 := by omega
      rw [hj i (by omega)]
      have ht := h2 i hik y hyX hyΩ hyC
      refine (deltaPrimeC_stencil aw (μs (i + 1)) (ε i) (νs i) h (by omega) (by omega) (by simp) y _ _
        ?_ ?_).1 ht
      · intro x _; rfl
      intro x hx
      by_contra hne
      set x'' := LargeField.torusCast (histScale_top g.hM hnn hkK) x with hx''
      have e := jBlock_torusCast_top g.hM hnn le_rfl hkK x
      have hne' : ψ₂ (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) x'') ≠
          ψ (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) x'') := by
        rw [e]; exact fun h' => hne h'.symm
      obtain ⟨-, -, hC⟩ := hfree x'' hne'
      have hu : LargeField.cubeMap n S.L M K (i + 1) x'' ∈ nbhd 3 ({y} : Set (Torus S.d (n (i + 1)))) := by
        rw [hx'', cubeMap_torusCast_top g.hM hnn hkK]; exact hx
      obtain ⟨z, hz, hdz⟩ := mem_nbhd.1 hu
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hC (mem_nbhd.2 ⟨z, hyC, hdz⟩)
    · -- the pair `(ψ_k, ψ_{k+1})` at the cubes of `𝕋_{k+1}` near `Ω_{k+1}` and its holes
      obtain rfl : i = k := by omega
      rw [hj (i + 1) (by omega)]
      have ht := h2 i hik y hyX hyΩ hyC
      refine (deltaPrimeC_stencil aw (μs (i + 1)) (ε i) (νs i) h (by omega) (by omega) (by simp) y _ _
        ?_ ?_).1 ht
      rotate_left
      · intro x _; rfl
      intro x hx
      by_contra hne
      set x'' := LargeField.torusCast (histScale_top g.hM hnn hk) x with hx''
      have e := jBlock_torusCast_top g.hM hnn (Nat.le_succ i) hk x
      have hne' : ψ₂ i (jBlock S.d S.L (M * n K) K i x'') ≠ ψ i (jBlock S.d S.L (M * n K) K i x'') := by
        rw [e]; exact fun h' => hne h'.symm
      obtain ⟨-, hB, -⟩ := hfree x'' hne'
      have hu : LargeField.cubeMap n S.L M K (i + 1) x'' ∈ nbhd 3 ({y} : Set (Torus S.d (n (i + 1)))) := by
        rw [hx'', cubeMap_torusCast_top g.hM hnn hk]; exact hx
      obtain ⟨z, hz, hdz⟩ := mem_nbhd.1 hu
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hB (mem_nbhd.2 ⟨z, hyC, hdz⟩)

/-- **The H7 domain of scale `k + 1` does not read `ψ_k` on the blocks near `Ω_{k+1}` away from the
holes** (Definition II.3.5 (c) with `Ω^c_j = Z_j ∖ Ω_j`, `omegaCNb`): two multiscale fields that differ
only in the component `k`, and there only on `k`-blocks whose cube of `𝕋_{k+1}` lies within `2` cubes of
`Ω_{k+1}` and farther than `3` cubes from `(Ω^c_{k+1})^{∼3}`, and whose cube of `𝕋_k` lies farther than
`3` cubes from `(Ω^c_k)^{∼3}`, lie in the H7 domain of scale `k + 1` together.  The tests reading `ψ_k` are
`Δ^c_k(□)` at the cubes `□` of `𝕋_k` with no cube of `𝕋_{k+1}` in `Ω^{∼3}_{k+1}`, `Δ'^c_{k+1}(□')` at the
cubes of `𝕋_{k+1}` in `(Ω^c_{k+1})^{∼3}` and `Δ'^c_k(□)` at the cubes of `𝕋_k` in `(Ω^c_k)^{∼3}`; each
reads the blocks of the cubes within `3` cubes of its own (`deltaC_stencil`, `deltaPrimeC_stencil`),
and none of them reaches such a block (`L ≥ 3`). -/
theorem h7Domain_succ_congr_k (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hL : 3 ≤ S.L) {Yf : Set (Torus S.d (M * n K * S.L ^ K))} {aw μs ε ε1 νs : ℕ → ℝ}
    {h : Fin N → ℂ} {ψ ψ₂ ψ' : MultiFieldC S n M K N}
    {gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ}
    (hj : ∀ j, j ≠ k → ψ₂ j = ψ j)
    (hfree : ∀ x : Torus S.d (M * n K * S.L ^ K),
      ψ₂ k (jBlock S.d S.L (M * n K) K k x) ≠ ψ k (jBlock S.d S.L (M * n K) K k x) →
      LargeField.cubeMap n S.L M K (k + 1) x ∈ nbhd 2 (H.step k).Omega ∧
      LargeField.cubeMap n S.L M K (k + 1) x ∉ nbhd 3 (omegaCNb (globalLH H M) 3 (k + 1)) ∧
      LargeField.cubeMap n S.L M K k x ∉ nbhd 3 (omegaCNb (globalLH H M) 3 k)) :
    H7Domain g.M1 g.c g.hM hnn (globalLH H M) (k + 1) hk Yf aw μs ε ε1 νs h ψ ψ' gf ↔
      H7Domain g.M1 g.c g.hM hnn (globalLH H M) (k + 1) hk Yf aw μs ε ε1 νs h ψ₂ ψ' gf :=
  ⟨h7Domain_succ_of_congr_k g hnn H hk hL hj hfree,
    h7Domain_succ_of_congr_k g hnn H hk hL (fun j hj' => (hj j hj').symm)
      fun x hx => hfree x (Ne.symm hx)⟩

include hnn in
/-- **A sufficient condition for the hole conditions of `h7Domain_succ_congr_k`**: a cube of `𝕋_{i+1}` at
distance `≥ 7` from `Z_{i+1} ∖ Ω_{i+1}` is not within `3` cubes of `(Ω^c_{i+1})^{∼3}`. -/
theorem notMem_nbhd_omegaCNb_of_far (H : RegionHistory S n R k0 K) {i : ℕ} (hi : i + 1 ≤ K)
    {u : Torus S.d (n (i + 1))} (hu : u ∉ nbhd 6 ((H.step (i + 1)).Z \ (H.step i).Omega)) :
    u ∉ nbhd 3 (omegaCNb (globalLH H M) 3 (i + 1)) := fun h => by
  obtain ⟨y, hy, hd⟩ := mem_nbhd.1 h
  obtain ⟨v, hv, hdv⟩ := exists_near_of_mem_omegaCNb (M := M) hnn H hi hy
  refine hu (mem_nbhd.2 ⟨v, hv, ?_⟩)
  have := LargeField.supDist_triangle u y v
  omega

variable (hM1 : g.M1 = S.L ^ m₁)

omit [NeZero M] in
/-- A site of the cover torus lies in the global top layer `Ω_{k+1}` of the step iff its cube of `𝕋_{k+1}`
lies in `Ω_{k+1}`. -/
theorem mem_stepG'_top_iff (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    x ∈ (stepG' g hnn hM1 H hk hρ).Ω (k + 1) ↔
      cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ (H.step k).Omega := by
  have hc := g.hc
  change x ∈ (p6TopC (k := k) (H.step k) hM1 (hnn k (by omega)) hρ (by omega)).Ω (k + 1) ↔ _
  rw [p6TopC, mem_castN_Ω, p6Top_Ω_top, mem_fineK1]
  rfl

/-- **The datum of `holeStepLoc2` at a data site off `Ω_{k+1}`** is `ψ_k` at the `k`-block of the site. -/
theorem holeStepLoc2_D'_Ψ_of_notMem (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (hx : x ∈ dataSites (locG' g hnn hM1 H hk hρ V))
    (hxΩ : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∉ (H.step k).Omega) :
    (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D'.Ψ x =
      ψ k (jBlock S.d S.L (M * n K) K k (fineOfC g hnn hM1 hk x)) := by
  rw [holeStepLoc2_D'_Ψ g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V hx,
    jBlock_fineOfC g hnn hM1 hk k (Nat.le_succ k) x]
  have h1 : x ∉ (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.Ω (k + 1) :=
    fun h => hxΩ ((mem_stepG'_top_iff g hnn hM1 H hk hρ x).1 h)
  unfold mixedLift blockLift
  simp only [h1, ↓reduceIte]
  rfl

/-- **Changing `ψ_k` at the block of a data site off `Ω_{k+1}` in the unread band**: if a data site `x`
of `G′_V` has its cube of `𝕋_{k+1}` outside `Ω_{k+1}` but within `2` cubes of it, at distance `> 3` from
`(Ω^c_{k+1})^{∼3}`, and its cube of `𝕋_k` at distance `> 3` from `(Ω^c_k)^{∼3}`, then for every field
`ψ` of the H7 domain of scale `k + 1` the field `ψ₂` equal to `ψ` except at the `k`-block of `x`, where it
is `i (2|δ_b| + 1) (1, …, 1)`, lies in the same H7 domain (`h7Domain_succ_congr_k`), while the datum of the
local pair of reading HS-2 at `ψ₂` is outside `Ψ̃^c(G′_V; δ_b, δ_b)` (its value at `x` has imaginary
part `2|δ_b| + 1`, `not_inDomainC_of_im`). -/
theorem exists_h7Domain_not_inDomainC_of_site (H : RegionHistory S n R k0 K) {k : ℕ}
    (hk : k + 1 ≤ K) (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (hL : 3 ≤ S.L) (hN : 0 < N)
    (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) {aw μs ε ε1 νs : ℕ → ℝ} {h : Fin N → ℂ}
    (νb δb : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {Yf : Set (Torus S.d (M * n K * S.L ^ K))} {ψ ψ' : MultiFieldC S n M K N}
    {gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ}
    (hdom : H7Domain g.M1 g.c g.hM hnn (globalLH H M) (k + 1) hk Yf aw μs ε ε1 νs h ψ ψ' gf)
    {x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (hx : x ∈ dataSites (locG' g hnn hM1 H hk hρ V))
    (hxΩ : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∉ (H.step k).Omega)
    (hA : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ nbhd 2 (H.step k).Omega)
    (hB : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∉ nbhd 3 (omegaCNb (globalLH H M) 3 (k + 1)))
    (hC : cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x ∉
      nbhd 3 (omegaCNb (globalLH H M) 3 k)) :
    ∃ ψ₂ : MultiFieldC S n M K N, (∀ j, j ≠ k → ψ₂ j = ψ j) ∧
      H7Domain g.M1 g.c g.hM hnn (globalLH H M) (k + 1) hk Yf aw μs ε ε1 νs h ψ₂ ψ' gf ∧
      ¬ InDomainC (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ₂ z h₀ a₁ ν β p₁ δ V).G' νb δb δb
        (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ₂ z h₀ a₁ ν β p₁ δ V).D' := by
  classical
  set b := jBlock S.d S.L (M * n K) K k (fineOfC g hnn hM1 hk x) with hb
  set w : Fin N → ℂ := fun _ => ((2 * |δb| + 1 : ℝ) : ℂ) * Complex.I with hw
  set ψ₂ : MultiFieldC S n M K N := Function.update ψ k (Function.update (ψ k) b w) with hψ₂
  have hψ₂k : ψ₂ k = Function.update (ψ k) b w := by rw [hψ₂, Function.update_self]
  have hψ₂j : ∀ j, j ≠ k → ψ₂ j = ψ j := fun j hj => by rw [hψ₂, Function.update_of_ne hj]
  refine ⟨ψ₂, hψ₂j, ?_, ?_⟩
  · refine h7Domain_succ_of_congr_k g hnn H hk hL hψ₂j (fun x' hx' => ?_) hdom
    have hbx : jBlock S.d S.L (M * n K) K k x' = b := by
      by_contra hne
      rw [hψ₂k, Function.update_of_ne hne] at hx'
      exact hx' rfl
    have hk' : LargeField.cubeMap n S.L M K k x' = cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x := by
      rw [← cubeMap_fineOfC_k g hnn hM1 hk x]
      exact cubeMap_eq_of_jBlock_eq le_rfl (Nat.le_of_succ_le hk) hnn hbx
    have hk1' : LargeField.cubeMap n S.L M K (k + 1) x' = cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x := by
      rw [← cubeMap_fineOfC_succ g hnn hM1 hk x]
      exact cubeMap_eq_of_jBlock_eq (Nat.le_succ k) hk hnn hbx
    rw [hk', hk1']
    exact ⟨hA, hB, hC⟩
  · refine not_inDomainC_of_im (i := ⟨0, hN⟩) (show x ∈ dataSites (locG' g hnn hM1 H hk hρ V) from hx) ?_
    rw [holeStepLoc2_D'_Ψ_of_notMem g hnn hM1 H hk hk1 hρ ψ₂ z h₀ a₁ ν β p₁ δ V hx hxΩ, ← hb, hψ₂k,
      Function.update_self, hw]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re,
      mul_zero, add_zero, mul_one]
    rw [abs_of_pos (by positivity)]
    linarith [le_abs_self δb]

/-- **`H7MixedDatumLoc2` fails when a set `V` has a data site off `Ω_{k+1}` in the unread band** (the
existence of such a site, of a field of the H7 domain of scale `k + 1` at a set `Y_f`, and the condition
`CubesOfIn` are the hypotheses): `exists_h7Domain_not_inDomainC_of_site`. -/
theorem not_h7MixedDatumLoc2_of_site (H : RegionHistory S n R k0 K) {k : ℕ}
    (hk : k + 1 ≤ K) (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (hL : 3 ≤ S.L) (hN : 0 < N)
    (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (aw μs ε ε1 νs : ℕ → ℝ) (h : Fin N → ℂ)
    (νb δb : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {Yf : Set (Torus S.d (M * n K * S.L ^ K))} {ψ ψ' : MultiFieldC S n M K N}
    {gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ}
    (hdom : H7Domain g.M1 g.c g.hM hnn (globalLH H M) (k + 1) hk Yf aw μs ε ε1 νs h ψ ψ' gf)
    (hY : CubesOfIn (S := S) (n := n) (M := M) (K := K) (k + 1) Yf
      (fineOfC g hnn hM1 hk '' (dataSites (locG' g hnn hM1 H hk hρ V) :
        Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))))
    {x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (hx : x ∈ dataSites (locG' g hnn hM1 H hk hρ V))
    (hxΩ : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∉ (H.step k).Omega)
    (hA : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ nbhd 2 (H.step k).Omega)
    (hB : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∉ nbhd 3 (omegaCNb (globalLH H M) 3 (k + 1)))
    (hC : cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x ∉
      nbhd 3 (omegaCNb (globalLH H M) 3 k)) :
    ¬ H7MixedDatumLoc2 g hnn hM1 H hk hk1 hρ z h₀ a₁ ν β p₁ δ aw μs ε ε1 νs h νb δb := by
  intro hD
  obtain ⟨ψ₂, -, hdom₂, hnot⟩ := exists_h7Domain_not_inDomainC_of_site g hnn hM1 H hk hk1 hρ hL hN
    z h₀ a₁ ν β p₁ δ νb δb V hdom hx hxΩ hA hB hC
  exact hnot (hD V Yf ψ₂ ψ' gf hdom₂ hY)

end Free

end Balaban.RootFSpine
