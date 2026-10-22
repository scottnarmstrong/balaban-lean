/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldRead

/-!
# The source H7 domain of the composed multiscale field (OPEN-H7-MIXED, the transfer)

An old boundary term `ℬ^{(k)}(X, 𝔸)` of a history is re-expanded at the multiscale field
`composedMulti` of the step on a region: the composed field on the unit points of `Ω_{k+1}`, the
record's fields elsewhere.  Its analyticity and bound ((D7) `analytic`, `bound`) hold on the H7
domain of scale `k` at `X` (Definition II.3.5 (d)), while the new term is to be analytic on the H7
domain of scale `k + 1` at the output label `Y ⊇ X`.  This file proves the part of the image lemma
that is a transfer of conditions: every condition of the source domain at `X` that does not read
the composed field near `Ω_{k+1}` follows from the target domain at `Y`.

* `deltaC_stencil`, `deltaPrimeC_stencil`: `Δ^c_q(□; 1, ε)` and `Δ'^c_{k+1}(□'; (¾, 5/4), ε)` read the
  fields only on the blocks of the cubes of `□^{∼3}` (the complex forms of `chiK_stencil`,
  `chiPrimeNew_stencil`);
* `histScale_top`, `cubeMap_torusCast_top`, `jBlock_torusCast_top`: the level-`q` torus of a cube
  test is the fine torus of the history;
* `omegaNb_eq_succ`: `Ω^{∼r}_j` is the same at the scales `k` and `k + 1` for `j ≤ k`;
* `composedMulti_eq_of_notMem`: off `Ω_{k+1}` the composed multiscale field is the record's field;
* `cubeMap_succ_notMem_Omega_of_far`, `cubeMap_succ_notMem_Omega_of_nearZ`: the sites read by a cube
  test away from `Ω^{∼3}_{k+1}`, or near the large-field region `Ω^c_k`, have their cube of
  `𝕋_{k+1}` outside `Ω_{k+1}` (P5 (2.3), `blockMap_notMem_Omega_of_near`);
* `h7Domain_composedMulti_of_inner`: **the transfer**: if `(ψ, ψ', g)` lies in the H7 domain of
  scale `k + 1` at `Y ⊇ X`, then `(composedMulti ψ comp, ψ', g)` lies in the H7 domain of scale `k`
  at `X`, given the remaining condition `hin`: at the cubes `□ ⊂ X` of `𝕋_k` with a cube of
  `𝕋_{k+1}` in `Ω^{∼3}_{k+1}` (and outside `(Ω^c_k)^{∼3}`), the composed field lies in
  `Δ^c_k(□; 1, ε_k)`.  The statement is general in the composed field `comp`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background

namespace Balaban.LargeField

section Stencils

variable {d M1 N₁ L N : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] {c n : ℕ} [NeZero n]

/-- **`Δ^c_q(□; 1, ε)` reads the field only on the blocks of the cubes of `□^{∼3}`** (the complex form
of `chiK_stencil`, Lemma II.3.3). -/
theorem deltaC_stencil {q : ℕ} (a : ℕ → ℝ) (μ ε : ℝ) (h : Fin N → ℂ) (hL : 2 ≤ L) (hc : 12 ≤ c)
    (hm : N₁ * L ^ (q - q) = c * n) (y0 : Torus d n)
    {ψ ψ' : Torus d (M1 * N₁ * L ^ (q - q)) → Fin N → ℂ}
    (hψ : ∀ x : Torus d (M1 * N₁ * L ^ q), blockMap (L ^ q * (c * M1)) n x ∈ nbhd 3 {y0} →
      ψ (jBlock d L (M1 * N₁) q q x) = ψ' (jBlock d L (M1 * N₁) q q x)) :
    ψ ∈ DeltaC (M1 := M1) (N₁ := N₁) (L := L) (q := q) a μ ε h c n y0 ↔
      ψ' ∈ DeltaC (M1 := M1) (N₁ := N₁) (L := L) (q := q) a μ ε h c n y0 := by
  have hD : liftSingle (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) ψ h =
      liftSingle (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) ψ' h :=
    liftSingle_congr _ fun x hx => hψ x (dataSites_genCube_near hL hc hm y0 hx)
  unfold DeltaC
  simp only [Set.mem_ofPred_eq, hD]

/-- **`Δ'^c_{k+1}(□'; (¾, 5/4), ε)` reads the pair only on the blocks of the cubes of `□'^{∼3}`** (the
complex form of `chiPrimeNew_stencil`). -/
theorem deltaPrimeC_stencil {k : ℕ} (a : ℕ → ℝ) (μ ε νk : ℝ) (h : Fin N → ℂ) (hL : 2 ≤ L)
    (hc : 12 ≤ c) (hm : N₁ * L ^ (k + 1 - (k + 1)) = c * n) (y0 : Torus d n)
    (Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1))))
    (hOm : IsBlockUnion L (M1 * N₁) (k + 1) (k + 1) Om)
    {p p' : (Torus d (M1 * N₁ * L ^ (k + 1 - k)) → Fin N → ℂ) ×
      (Torus d (M1 * N₁ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ)}
    (hψ : ∀ x : Torus d (M1 * N₁ * L ^ (k + 1)),
      blockMap (L ^ (k + 1) * (c * M1)) n x ∈ nbhd 3 {y0} →
      p.1 (jBlock d L (M1 * N₁) (k + 1) k x) = p'.1 (jBlock d L (M1 * N₁) (k + 1) k x))
    (hθ : ∀ x : Torus d (M1 * N₁ * L ^ (k + 1)),
      blockMap (L ^ (k + 1) * (c * M1)) n x ∈ nbhd 3 {y0} →
      p.2 (jBlock d L (M1 * N₁) (k + 1) (k + 1) x) =
        p'.2 (jBlock d L (M1 * N₁) (k + 1) (k + 1) x)) :
    p ∈ DeltaPrimeC (M1 := M1) (N₁ := N₁) (L := L) (k := k) a μ ε νk h hm y0 Om hOm ↔
      p' ∈ DeltaPrimeC (M1 := M1) (N₁ := N₁) (L := L) (k := k) a μ ε νk h hm y0 Om hOm := by
  have hD : mixedDataC h hm y0 Om hOm p.1 p.2 = mixedDataC h hm y0 Om hOm p'.1 p'.2 :=
    liftMixed_congr _ _ _ (fun x hx => hψ x (dataSites_genCubeMixed_near hL hc hm y0 Om hOm hx))
      (fun x hx => hθ x (dataSites_genCubeMixed_near hL hc hm y0 Om hOm hx))
  unfold DeltaPrimeC
  simp only [Set.mem_ofPred_eq, hD]

end Stencils

end Balaban.LargeField

namespace Balaban.RootFSpine

section Bridge

variable {S : Setting} {n : ℕ → ℕ} {K M M1 c : ℕ}
  (hM : M = c * M1) (hnn : ∀ i, i < K → n i = S.L * n (i + 1))

include hM hnn in
/-- The level-`q` torus of a cube test is the fine torus of the history. -/
theorem histScale_top {q : ℕ} (hqK : q ≤ K) : M1 * (c * n q) * S.L ^ q = M * n K * S.L ^ K := by
  simpa using histScale_eq hM hnn (Nat.zero_le q) hqK

/-- The cube of `𝕋_q` of a site of the level-`q` torus, read in the fine torus of the history. -/
theorem cubeMap_torusCast_top {q : ℕ} (hqK : q ≤ K) (x : Torus S.d (M1 * (c * n q) * S.L ^ q)) :
    LargeField.cubeMap n S.L M K q (LargeField.torusCast (histScale_top hM hnn hqK) x) =
      blockMap (S.L ^ q * (c * M1)) (n q) x := by
  unfold LargeField.cubeMap
  rw [blockMap_torusCast]
  subst hM
  rfl

/-- The `j`-block of a site of the level-`q` torus, read in the fine torus of the history. -/
theorem jBlock_torusCast_top {j q : ℕ} (hjq : j ≤ q) (hqK : q ≤ K)
    (x : Torus S.d (M1 * (c * n q) * S.L ^ q)) :
    jBlock S.d S.L (M * n K) K j (LargeField.torusCast (histScale_top hM hnn hqK) x) =
      LargeField.torusCast (histScale_eq hM hnn hjq hqK) (jBlock S.d S.L (M1 * (c * n q)) q j x) := by
  unfold jBlock
  rw [blockMap_torusCast, torusCast_blockMap_right]

end Bridge

section Omega

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- `Ω^{∼r}_j` is the same at the scales `k` and `k + 1` away from the top indices. -/
theorem omegaNb_eq_succ (a : LocalHistory S n M K) {k r j : ℕ} (hj : j ≠ k + 1) (hj' : j ≠ k + 2) :
    omegaNb a k r j = omegaNb a (k + 1) r j := by
  unfold omegaNb
  simp only [hj, hj', ↓reduceIte]

end Omega

section History

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **Off `Ω_{k+1}` the composed multiscale field is the record's field**: for a set `G′` whose unit
points have their cubes of `𝕋_{k+1}` in `Ω_{k+1}` (`hG'`), if a site of a `k`-block has its cube of
`𝕋_{k+1}` outside `Ω_{k+1}`, the unit block of the block is not a unit point of `G′`. -/
theorem composedMulti_eq_of_notMem (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    {ϱ' : ℝ} {G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ'}
    (hG' : ∀ b : unitPts G', cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 (unitRep b) ∈ (H.step k).Omega)
    (ψc : MultiFieldC S n M K N) (comp : unitPts G' → Fin N → ℂ)
    {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : LargeField.cubeMap n S.L M K (k + 1) x ∉ (H.step k).Omega) :
    composedMulti g hnn hM1 hk G' ψc comp k (jBlock S.d S.L (M * n K) K k x) =
      ψc k (jBlock S.d S.L (M * n K) K k x) := by
  refine composedMulti_out hk _ ψc comp _ fun hu => hx ?_
  obtain ⟨xh, hxh, -, hxh1⟩ := exists_fine_of_unitOfBlock g hnn hM1 hk ⟨_, hu⟩ rfl
  have hmem := hG' ⟨_, hu⟩
  rw [← hxh1, cubeMap_eq_of_jBlock_eq (Nat.le_succ k) hk hnn hxh] at hmem
  exact hmem

include hnn in
/-- **The sites read by a cube test away from `Ω^{∼3}_{k+1}` lie off `Ω_{k+1}`**: if no site of the
cube `□` of `𝕋_k` has its cube of `𝕋_{k+1}` in `Ω^{∼3}_{k+1}`, then every site whose cube of `𝕋_k`
lies in `□^{∼3}` has its cube of `𝕋_{k+1}` outside `Ω_{k+1}`. -/
theorem cubeMap_succ_notMem_Omega_of_far (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    {y : Torus S.d (n k)}
    (hfar : ∀ x, LargeField.cubeMap n S.L M K k x = y →
      LargeField.cubeMap n S.L M K (k + 1) x ∉ omegaNb (globalLH H M) (k + 1) 3 (k + 1))
    {x' : Torus S.d (M * n K * S.L ^ K)}
    (hx' : LargeField.cubeMap n S.L M K k x' ∈ nbhd 3 ({y} : Set (Torus S.d (n k)))) :
    LargeField.cubeMap n S.L M K (k + 1) x' ∉ (H.step k).Omega := by
  intro hΩ
  have hL0 : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨x₀, hx₀⟩ := cubeMap_surjective (S := S) (M := M) hnn (Nat.le_of_succ_le hk) y
  refine hfar x₀ hx₀ ?_
  unfold omegaNb
  simp only [show k + 1 ≠ k + 1 + 1 by omega, ↓reduceIte]
  refine mem_nbhd.2 ⟨LargeField.cubeMap n S.L M K (k + 1) x', fun x hx => ?_, ?_⟩
  · simp only [globalLH, Nat.add_sub_cancel, fineSet, Set.mem_ofPred_eq]
    rw [hx]
    exact hΩ
  · obtain ⟨z, hz, hd⟩ := mem_nbhd.1 hx'
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [← cubeMap_succ hnn hk x₀, ← cubeMap_succ hnn hk x', hx₀]
    refine (supDist_blockMap_le (hnn k (by omega)) _ _).trans (Nat.div_le_of_le_mul ?_)
    rw [supDist_comm] at hd
    omega

include hnn in
/-- **The sites read by a cube test near the large-field region lie off `Ω_{k+1}`** (P5 (2.3)): if
`□ ∈ (Ω^c_k)^{∼3}` and `5 ≤ ⌊R_{k-1}⌋`, every site whose cube of `𝕋_k` lies in `□^{∼3}` has its
cube of `𝕋_{k+1}` outside `Ω_{k+1}` (it is within `6 ≤ ⌊R_{k-1}⌋ + 1` of `Z_k`). -/
theorem cubeMap_succ_notMem_Omega_of_nearZ (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hR : 5 ≤ ⌊R (k - 1)⌋₊) {y : Torus S.d (n k)} (hy : y ∈ omegaCNb (globalLH H M) 3 k)
    {x' : Torus S.d (M * n K * S.L ^ K)}
    (hx' : LargeField.cubeMap n S.L M K k x' ∈ nbhd 3 ({y} : Set (Torus S.d (n k)))) :
    LargeField.cubeMap n S.L M K (k + 1) x' ∉ (H.step k).Omega := by
  obtain ⟨y', hy', hd⟩ := mem_nbhd.1 hy
  obtain ⟨x₁, hx₁⟩ := cubeMap_surjective (S := S) (M := M) hnn (Nat.le_of_succ_le hk) y'
  have hZ : y' ∈ (H.step k).Z := by
    have h1 := (hy' x₁ hx₁).1
    simp only [globalLH, fineSet, Set.mem_ofPred_eq, hx₁] at h1
    exact h1
  obtain ⟨z, hz, hdz⟩ := mem_nbhd.1 hx'
  rw [Set.mem_singleton_iff] at hz
  subst hz
  rw [← cubeMap_succ hnn hk x']
  refine (H.step k).blockMap_notMem_Omega_of_near (mem_nbhd.2 ⟨y', hZ, ?_⟩)
  have := supDist_triangle (LargeField.cubeMap n S.L M K k x') z y'
  omega

/-- **The transfer of the H7 domain to the composed multiscale field, for a target record with the
regions `Z'`** (the core of `h7Domain_composedMulti_of_inner`): the target H7 domain of scale `k + 1` is
taken at the global records with the regions `Z'` (ruling R17: the pre-`R` records `globalLHPre`, whose
regions differ from those of `globalLH` at the top scale only), whose holes agree with those of the global
records at the scales `j ≤ k` (`hZ'`); the source domain of scale `k` is that of the global records.  If `(ψ, ψ', g)` lies in the H7 domain of scale
`k + 1` at `Y ⊇ X`, then `(composedMulti ψ comp, ψ', g)` lies in the H7 domain of scale `k` at `X`,
given `hin`: at the cubes `□ ⊂ X` of `𝕋_k` outside `(Ω^c_k)^{∼3}` with a cube of `𝕋_{k+1}` in
`Ω^{∼3}_{k+1}`, the composed field lies in `Δ^c_k(□; 1, ε_k)`.  The other conditions are those of
the target: below the scale `k` the fields are the record's, at the scale `k` away from `Ω^{∼3}_{k+1}`
and on the pairs at `(Ω^c_k)^{∼3}` the cube tests read only blocks off `Ω_{k+1}`
(`cubeMap_succ_notMem_Omega_of_far`, `cubeMap_succ_notMem_Omega_of_nearZ`), and the fluctuation field
and `g` are unchanged. -/
theorem h7Domain_composedMulti_of_inner_withZ (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 5 ≤ ⌊R (k - 1)⌋₊) (hL : 2 ≤ S.L) (Z' : ℕ → Set (Torus S.d (M * n K * S.L ^ K)))
    (hZ' : ∀ j, j ≤ k → omegaCNb { globalLH H M with Z := Z' } 3 j = omegaCNb (globalLH H M) 3 j)
    {ϱ' : ℝ}
    {G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ'}
    (hG' : ∀ b : unitPts G', cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 (unitRep b) ∈ (H.step k).Omega)
    (ψ : MultiFieldC S n M K N) (comp : unitPts G' → Fin N → ℂ)
    {Xf Yf : Set (Torus S.d (M * n K * S.L ^ K))} (hXY : Xf ⊆ Yf) (aw μs ε ε1 νs : ℕ → ℝ)
    (h : Fin N → ℂ) (ψ' : MultiFieldC S n M K N) (gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ)
    (htgt : H7Domain g.M1 g.c g.hM hnn { globalLH H M with Z := Z' } (k + 1) hk Yf aw μs ε ε1 νs h ψ
      ψ' gf)
    (hin : ∀ y : Torus S.d (n k), CubeSub (S := S) (n := n) M K k y Xf →
      y ∉ omegaCNb (globalLH H M) 3 k →
      (¬ ∀ x, LargeField.cubeMap n S.L M K k x = y →
        LargeField.cubeMap n S.L M K (k + 1) x ∉ omegaNb (globalLH H M) (k + 1) 3 (k + 1)) →
      (fun z => composedMulti g hnn hM1 hk G' ψ comp k
          (LargeField.torusCast (histScale_eq g.hM hnn le_rfl (Nat.le_of_succ_le hk)) z)) ∈
        DeltaC (M1 := g.M1) (N₁ := g.c * n k) (L := S.L) (q := k) aw (μs k) (ε k) h g.c (n k) y) :
    H7Domain g.M1 g.c g.hM hnn (globalLH H M) k (Nat.le_of_succ_le hk) Xf aw μs ε ε1 νs h
      (composedMulti g hnn hM1 hk G' ψ comp) ψ' gf := by
  have hc := g.hc
  have eNb : ∀ k' r j', omegaNb { globalLH H M with Z := Z' } k' r j' = omegaNb (globalLH H M) k' r j' :=
    fun _ _ _ => rfl
  obtain ⟨h1, h2, h3, h4⟩ := htgt
  refine ⟨?_, ?_, ?_, h4⟩
  · intro j hjk y hyX hfar hyC
    rcases Nat.lt_or_ge j k with hj | hj
    · simp only [composedMulti_of_lt hk _ ψ comp hj]
      refine h1 j (by omega) y (fun x hx => hXY (hyX x hx)) (fun x hx => ?_)
        (by rw [hZ' j hjk]; exact hyC)
      rw [eNb, ← omegaNb_eq_succ (globalLH H M) (k := k) (r := 3) (j := j + 1) (by omega) (by omega)]
      exact hfar x hx
    · have hjk' : j = k := le_antisymm hjk hj
      subst hjk'
      by_cases hnear : ∀ x, LargeField.cubeMap n S.L M K j x = y →
          LargeField.cubeMap n S.L M K (j + 1) x ∉ omegaNb (globalLH H M) (j + 1) 3 (j + 1)
      · have ht := h1 j (Nat.le_succ j) y (fun x hx => hXY (hyX x hx)) hnear
          (by rw [hZ' j le_rfl]; exact hyC)
        refine (deltaC_stencil aw (μs j) (ε j) h hL (by omega) (by simp) y fun x hx => ?_).2 ht
        show composedMulti g hnn hM1 hk G' ψ comp j (LargeField.torusCast _ _) =
          ψ j (LargeField.torusCast _ _)
        rw [← jBlock_torusCast_top g.hM hnn le_rfl (Nat.le_of_succ_le hk) x]
        refine composedMulti_eq_of_notMem g hnn hM1 H hk hG' ψ comp ?_
        refine cubeMap_succ_notMem_Omega_of_far hnn H hk hnear ?_
        rw [cubeMap_torusCast_top g.hM hnn (Nat.le_of_succ_le hk)]
        exact hx
      · exact hin y hyX hyC hnear
  · intro i hik y hyX hyΩ hyC
    rcases Nat.lt_or_ge (i + 1) k with hi | hi
    · simp only [composedMulti_of_lt hk _ ψ comp hi, composedMulti_of_lt hk _ ψ comp (by omega : i < k)]
      refine h2 i (by omega) y (fun x hx => hXY (hyX x hx)) ?_ (by rw [hZ' (i + 1) hik]; exact hyC)
      rw [eNb, ← omegaNb_eq_succ (globalLH H M) (k := k) (r := 3) (j := i + 1) (by omega) (by omega)]
      exact hyΩ
    · obtain rfl : i + 1 = k := le_antisymm hik hi
      have ht := h2 i (by omega) y (fun x hx => hXY (hyX x hx))
        (by
          rw [eNb, ← omegaNb_eq_succ (globalLH H M) (k := i + 1) (r := 3) (j := i + 1) (by omega)
            (by omega)]
          exact hyΩ) (by rw [hZ' (i + 1) hik]; exact hyC)
      refine (deltaPrimeC_stencil aw (μs (i + 1)) (ε i) (νs i) h hL (by omega) (by simp) y _ _
        (fun x _ => ?_) (fun x hx => ?_)).2 ht
      · show composedMulti g hnn hM1 hk G' ψ comp i (LargeField.torusCast _ _) =
          ψ i (LargeField.torusCast _ _)
        exact composedMulti_of_lt hk _ ψ comp (by omega) _
      · show composedMulti g hnn hM1 hk G' ψ comp (i + 1) (LargeField.torusCast _ _) =
          ψ (i + 1) (LargeField.torusCast _ _)
        rw [← jBlock_torusCast_top g.hM hnn le_rfl (Nat.le_of_succ_le hk) x]
        refine composedMulti_eq_of_notMem g hnn hM1 H hk hG' ψ comp ?_
        refine cubeMap_succ_notMem_Omega_of_nearZ hnn H hk hρ hyC ?_
        rw [cubeMap_torusCast_top g.hM hnn (Nat.le_of_succ_le hk)]
        exact hx
  · intro j hj y hy
    exact h3 j (by omega) y fun x hx => ⟨hXY (hy x hx).1, (hy x hx).2⟩

/-- **The transfer of the H7 domain to the composed multiscale field** (OPEN-H7-MIXED, all but the
cubes near `Ω_{k+1}`; Definition II.3.5 (c), (d)): if `(ψ, ψ', g)` lies in the H7 domain of scale
`k + 1` at `Y ⊇ X`, then `(composedMulti ψ comp, ψ', g)` lies in the H7 domain of scale `k` at `X`,
given `hin`: at the cubes `□ ⊂ X` of `𝕋_k` outside `(Ω^c_k)^{∼3}` with a cube of `𝕋_{k+1}` in
`Ω^{∼3}_{k+1}`, the composed field lies in `Δ^c_k(□; 1, ε_k)`.  The other conditions are those of
the target: below the scale `k` the fields are the record's, at the scale `k` away from `Ω^{∼3}_{k+1}`
and on the pairs at `(Ω^c_k)^{∼3}` the cube tests read only blocks off `Ω_{k+1}`
(`cubeMap_succ_notMem_Omega_of_far`, `cubeMap_succ_notMem_Omega_of_nearZ`), and the fluctuation field
and `g` are unchanged. -/
theorem h7Domain_composedMulti_of_inner (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 5 ≤ ⌊R (k - 1)⌋₊) (hL : 2 ≤ S.L) {ϱ' : ℝ}
    {G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ'}
    (hG' : ∀ b : unitPts G', cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 (unitRep b) ∈ (H.step k).Omega)
    (ψ : MultiFieldC S n M K N) (comp : unitPts G' → Fin N → ℂ)
    {Xf Yf : Set (Torus S.d (M * n K * S.L ^ K))} (hXY : Xf ⊆ Yf) (aw μs ε ε1 νs : ℕ → ℝ)
    (h : Fin N → ℂ) (ψ' : MultiFieldC S n M K N) (gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ)
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLH H M) (k + 1) hk Yf aw μs ε ε1 νs h ψ ψ' gf)
    (hin : ∀ y : Torus S.d (n k), CubeSub (S := S) (n := n) M K k y Xf →
      y ∉ omegaCNb (globalLH H M) 3 k →
      (¬ ∀ x, LargeField.cubeMap n S.L M K k x = y →
        LargeField.cubeMap n S.L M K (k + 1) x ∉ omegaNb (globalLH H M) (k + 1) 3 (k + 1)) →
      (fun z => composedMulti g hnn hM1 hk G' ψ comp k
          (LargeField.torusCast (histScale_eq g.hM hnn le_rfl (Nat.le_of_succ_le hk)) z)) ∈
        DeltaC (M1 := g.M1) (N₁ := g.c * n k) (L := S.L) (q := k) aw (μs k) (ε k) h g.c (n k) y) :
    H7Domain g.M1 g.c g.hM hnn (globalLH H M) k (Nat.le_of_succ_le hk) Xf aw μs ε ε1 νs h
      (composedMulti g hnn hM1 hk G' ψ comp) ψ' gf :=
  h7Domain_composedMulti_of_inner_withZ g hnn hM1 H hk hρ hL (globalLH H M).Z (fun _ _ => rfl) hG'
    ψ comp hXY aw μs ε ε1 νs h ψ' gf htgt hin

end History

end Balaban.RootFSpine
