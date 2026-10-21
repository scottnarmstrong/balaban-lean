/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.OmegaPost
public import Balaban.LargeField.Characteristic.Analytic
public import Balaban.LargeField.Budget.Fine

/-!
# The holes of the H7 domain of a global history (ruling request R17)

The cube tests of the H7 domain (Definition II.3.5 (c); P5 (1.36)) are placed by the holes
`Ω^c_j`: `Δ^c_j(□)` away from `(Ω^c_j)^{∼3}`, `Δ'^c_j(□)` on `Ω^{∼3}_j ∩ (Ω^c_j)^{∼3}`.  The landed
`omegaCNb a r j` is the `r`-neighbourhood of the cubes of `Z_j ∖ Ω_j`.

* `omegaCNb_globalLH_succ`: for the global history, `Z_j ∖ Ω_j` is the complement of the post-`R`
  domain `Ω_j^post = Ω_j ∪ ⋃ Rem_j` (Definition I.3.11): the post-`R` records read the printed holes
  of the post-`R` domain;
* `omegaCNb_globalLHPre_top`: with the pre-`R` region at the top scale (`globalLHPre`, ruling request
  R17), the holes are the complement of the raw `Ω_k`, the printed `Ω^c_k` of the pre-`R` record;
* `omegaCNb_globalLHPre_of_ne`: below the top scale the two histories have the same holes;
* `globalLHPre_congr`; `h7Domain_withZ_iff` (the H7 domain reads the regions only through its holes);
* `h7Domain_globalLHPre_iff_of_far`: at a label `Y` whose `3`-neighbourhood misses the components
  removed by `R^{(k)}`, the pre-`R` and the post-`R` H7 domains agree (the transport across `R`).
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban Balaban.LargeField RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L]

omit [NeZero S.L] in
/-- The cube of `𝕋_{i+1}` of a cube off `Ω_{i+1}` lies in the pre-`R` region (Lemma I.3.5 (e)). -/
theorem mem_Zpre_of_notMem_omega (H : RegionHistory S n R k0 K) {i : ℕ} {y : Torus S.d (n (i + 1))}
    (hy : y ∉ (H.step i).Omega) : y ∈ H.F.Zpre (i + 1) :=
  (H.step i).Z0_subset_Zpre _ _ ((H.step i).Omega_compl_subset_Z0 hy)

/-- **The holes of the H7 domain of the global history are the complement of the post-`R` domain**:
`Z_{i+1} ∖ Ω_{i+1} = (Ω_{i+1}^post)^c`, `Ω^post = Ω ∪ ⋃ Rem` (Definition I.3.11). -/
theorem omegaCNb_globalLH_succ (hnn : ∀ i, i < K → n i = S.L * n (i + 1))
    (H : RegionHistory S n R k0 K) {i : ℕ} (hi : i + 1 ≤ K) (r : ℕ) :
    omegaCNb (globalLH H M) r (i + 1) = nbhd r (H.omegaPost (i + 1))ᶜ := by
  unfold omegaCNb
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, omegaPost, OmegaCube, Set.mem_union, not_or]
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := cubeMap_surjective (S := S) (M := M) hnn hi y
    have h1 := hy x hx
    simp only [globalLH, Nat.add_sub_cancel, fineSet, Set.mem_sdiff, Set.mem_ofPred_eq, hx] at h1
    obtain ⟨hZ, hΩ⟩ := h1
    have hZ' : y ∈ (H.F.step (i + 1)).Z := hZ
    rw [H.Z_eq] at hZ'
    refine ⟨hΩ, fun hrem => hZ'.2 ?_⟩
    obtain ⟨c, hc, hyc⟩ := H.mem_removedSet_iff.1 hrem
    exact Set.mem_biUnion hc hyc
  · rintro ⟨hΩ, hrem⟩ x hx
    simp only [globalLH, Nat.add_sub_cancel, fineSet, Set.mem_sdiff, Set.mem_ofPred_eq, hx]
    refine ⟨?_, hΩ⟩
    show y ∈ (H.F.step (i + 1)).Z
    rw [H.Z_eq]
    refine ⟨mem_Zpre_of_notMem_omega H hΩ, fun hU => hrem ?_⟩
    obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.1 hU
    exact H.mem_removedSet_iff.2 ⟨c, hc, hyc⟩

/-- **The holes of the H7 domain of the pre-`R` records at the top scale** (ruling request R17): with
the pre-`R` region `Z^pre_{i+1}`, `Z^pre_{i+1} ∖ Ω_{i+1}` is the complement of the raw `Ω_{i+1}`, the
printed `Ω^c_{i+1}` of P5 (1.36). -/
theorem omegaCNb_globalLHPre_top (hnn : ∀ i, i < K → n i = S.L * n (i + 1))
    (H : RegionHistory S n R k0 K) {i : ℕ} (hi : i + 1 ≤ K) (r : ℕ) :
    omegaCNb (globalLHPre H M (i + 1)) r (i + 1) = nbhd r ((H.step i).Omega)ᶜ := by
  unfold omegaCNb
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := cubeMap_surjective (S := S) (M := M) hnn hi y
    have h1 := hy x hx
    simp only [globalLHPre, globalLH, Nat.add_sub_cancel, fineSet, Set.mem_sdiff, Set.mem_ofPred_eq,
      hx] at h1
    exact h1.2
  · intro hΩ x hx
    simp only [globalLHPre, globalLH, Nat.add_sub_cancel, fineSet, Set.mem_sdiff, Set.mem_ofPred_eq,
      hx, ↓reduceIte]
    exact ⟨mem_Zpre_of_notMem_omega H hΩ, hΩ⟩

omit [NeZero M] [NeZero S.L] in
/-- Below (and above) the top scale the pre-`R` records have the holes of the global records. -/
theorem omegaCNb_globalLHPre_of_ne (H : RegionHistory S n R k0 K) {k j : ℕ} (hj : j ≠ k) (r : ℕ) :
    omegaCNb (globalLHPre H M k) r j = omegaCNb (globalLH H M) r j := by
  unfold omegaCNb
  simp only [globalLHPre, globalLH, hj, ↓reduceIte]

omit [NeZero M] [NeZero S.L] in
/-- Two histories with the same global records and the same pre-`R` region at scale `k` have the same
pre-`R` records. -/
theorem globalLHPre_congr {H H' : RegionHistory S n R k0 K} {k : ℕ}
    (hG : globalLH H' M = globalLH H M) (hZ : H'.F.Zpre k = H.F.Zpre k) :
    globalLHPre H' M k = globalLHPre H M k := by
  have hZj : ∀ j, fineSet (S := S) (n := n) M K j (H'.step j).Z =
      fineSet (S := S) (n := n) M K j (H.step j).Z := fun j =>
    congrFun (congrArg LocalHistory.Z hG) j
  have hZf : (fun j => fineSet (S := S) (n := n) M K j
      (if j = k then H'.F.Zpre j else (H'.step j).Z)) =
      fun j => fineSet (S := S) (n := n) M K j (if j = k then H.F.Zpre j else (H.step j).Z) := by
    funext j
    split_ifs with hj
    · subst hj; rw [hZ]
    · exact hZj j
  unfold globalLHPre
  rw [hZf, hG]

section Domain

variable {N : ℕ} (M1 c : ℕ) [NeZero M1] [NeZero c] (hM : M = c * M1)
  (hnn : ∀ i, i < K → n i = S.L * n (i + 1))

/-- **The H7 domain depends on the regions `Z_j` only through its holes**: changing the regions of a
history leaves the H7 domain at `X` unchanged when the holes `(Z_j ∖ Ω_j)^{∼3}` agree at the cubes of
`X` of the scales `j ≤ k`. -/
theorem h7Domain_withZ_iff (a : LocalHistory S n M K) (Z' : ℕ → Set (Torus S.d (M * n K * S.L ^ K)))
    (k : ℕ) (hkK : k ≤ K) (Xf : Set (Torus S.d (M * n K * S.L ^ K))) (aw μs ε ε1 νs : ℕ → ℝ)
    (h : Fin N → ℂ) (ψ ψ' : MultiFieldC S n M K N) (g : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ)
    (hC : ∀ j, j ≤ k → ∀ y : Torus S.d (n j), CubeSub (S := S) (n := n) M K j y Xf →
      (y ∈ omegaCNb a 3 j ↔ y ∈ omegaCNb { a with Z := Z' } 3 j)) :
    H7Domain M1 c hM hnn a k hkK Xf aw μs ε ε1 νs h ψ ψ' g ↔
      H7Domain M1 c hM hnn { a with Z := Z' } k hkK Xf aw μs ε ε1 νs h ψ ψ' g := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun j hjk y hyX hfar hyC => h1 j hjk y hyX hfar fun hy => hyC ((hC j hjk y hyX).1 hy),
      fun i hik y hyX hyΩ hyC => h2 i hik y hyX hyΩ ((hC (i + 1) hik y hyX).2 hyC), h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun j hjk y hyX hfar hyC => h1 j hjk y hyX hfar fun hy => hyC ((hC j hjk y hyX).2 hy),
      fun i hik y hyX hyΩ hyC => h2 i hik y hyX hyΩ ((hC (i + 1) hik y hyX).1 hyC), h3, h4⟩

/-- **Away from the removed set the pre-`R` and the post-`R` H7 domains agree** (ruling request R17): at
a label `Y` of scale `k` whose `3`-neighbourhood misses the components removed by `R^{(k)}`, the holes
of the two records at the cubes of `Y` are the same (`Ω^pre_k ⊆ Ω^post_k`, and a hole of `Ω^pre_k` within
`3` cubes of `Y` is not removed). -/
theorem h7Domain_globalLHPre_iff_of_far (H : RegionHistory S n R k0 K) {k : ℕ} (hkK : k ≤ K)
    {Y : Finset (Torus S.d (n k))}
    (hY : Disjoint (nbhd 3 (Y : Set (Torus S.d (n k)))) (H.removedSet k)) (aw μs ε ε1 νs : ℕ → ℝ)
    (h : Fin N → ℂ) (ψ ψ' : MultiFieldC S n M K N) (g : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ) :
    H7Domain M1 c hM hnn (globalLH H M) k hkK (fineSet (S := S) (n := n) M K k (Y : Set _)) aw μs ε
        ε1 νs h ψ ψ' g ↔
      H7Domain M1 c hM hnn (globalLHPre H M k) k hkK (fineSet (S := S) (n := n) M K k (Y : Set _))
        aw μs ε ε1 νs h ψ ψ' g := by
  refine h7Domain_withZ_iff M1 c hM hnn (globalLH H M) _ k hkK _ aw μs ε ε1 νs h ψ ψ' g
    fun j hj y hyX => ?_
  show y ∈ omegaCNb (globalLH H M) 3 j ↔ y ∈ omegaCNb (globalLHPre H M k) 3 j
  rcases Nat.lt_or_ge j k with hjk | hjk
  · rw [omegaCNb_globalLHPre_of_ne H (by omega) 3]
  obtain rfl : j = k := le_antisymm hj hjk
  cases j with
  | zero => rw [globalLHPre_eq_of_rem_empty H (H.rem_empty 0 (Or.inl rfl))]
  | succ i =>
    rw [omegaCNb_globalLH_succ hnn H hkK, omegaCNb_globalLHPre_top hnn H hkK]
    obtain ⟨x, hx⟩ := cubeMap_surjective (S := S) (M := M) hnn hkK y
    have hyY : y ∈ (Y : Set (Torus S.d (n (i + 1)))) := by
      have := hyX x hx
      simp only [fineSet, Set.mem_ofPred_eq, hx] at this
      exact this
    constructor
    · intro hy
      obtain ⟨v, hv, hd⟩ := mem_nbhd.1 hy
      exact mem_nbhd.2 ⟨v, fun hvΩ => hv (H.OmegaCube_subset_omegaPost (i + 1) hvΩ), hd⟩
    · intro hy
      obtain ⟨v, hv, hd⟩ := mem_nbhd.1 hy
      refine mem_nbhd.2 ⟨v, fun hvP => ?_, hd⟩
      rcases hvP with hvΩ | hvR
      · exact hv hvΩ
      · refine Set.disjoint_left.1 hY (mem_nbhd.2 ⟨y, hyY, ?_⟩) hvR
        rw [LargeField.supDist_comm]
        exact hd

end Domain

end Balaban.LargeField.Def7
