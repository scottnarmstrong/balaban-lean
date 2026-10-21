/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldDatum

/-!
# `H7MixedDatumLoc2` at the local sets of its use, for the pre-`R` records (target (3b) of W1154e)

The named input `H7MixedDatumLoc2` asks the datum of the local pair `G′_V` in `Ψ̃^c(δ_b, δ_b)` for every
set `V` and the post-`R` records `globalLH` of scale `k + 1`.  As stated it is false: for `V` reaching the
holes of `Ω_k`, or a removed component at scale `k + 1`, the datum `ψ_k` is read by no cube test
(`not_h7MixedDatumLoc2_of_site`); and without the premises on `z`, on the external field and on the
mass the cube tests do not control the datum.  Its only use is at the local sets `V₂(X, J)` of the
families `J ∈ allJ ρ`, and the step's boundary terms are pre-`R` records of scale `k + 1` (ruling R17).

* `cubeOfC_supDist_le_two`: sites within two cube sides lie over cubes of `𝕋_{k+1}` within two cubes;
* `near_omega_of_mem_dataSites_locSetXJ2`: **the data sites of `G′_{V₂(X,J)}` lie over cubes within
  `ρ + 3` cubes of `Ω_{k+1}`** (`J ∈ allJ ρ`, room `r + r′ ≤ c M₁ L^{k+1}`): the local set lies within
  `r + r′` of `Ω_{k+1} ∩ X^{∼3}` or of the localization range, its data sites within
  `11 L^{m₁} L^{k+1} + 1` of it (`localB_dataSites_range`);
* `le_supDist_Z_of_near_omega`: a cube of `𝕋_k` under a cube of `𝕋_{k+1}` within `⌊R_k⌋ + 3` cubes of
  `Ω_{k+1}` is at distance `≥ 4` from `Z_k` (P5 (2.3), `RegionStep.fine_far`);
* `cubeKOfC_notMem_omegaCNb_of_near`, `cubeSub_holes_globalLHPre`: the premises `hfar` and `hholes` of
  `inDomainC_holeStepLoc2_of_h7` for the pre-`R` records;
* `H7MixedDatumLoc2Pre`: **the named input restated** at `V₂(X, J)`, `J ∈ allJ ρ`, the target domain at
  `globalLHPre H M (k + 1)` and the external field `h₀` (ruling R16: `h₀ = Re h = hv`, the physical field);
* `h7MixedDatumLoc2Pre_holds`: **it holds** for `ρ ≤ ⌊R_k⌋`, `r + r′ ≤ c M₁ L^{k+1}`, `|z - 1| ≤ η`,
  condition (R4), the mass condition in either regime and `3 δ₁ + 2 ε_k ≤ δ_b`; `h7MixedDatumLoc2Pre_of_sfz`:
  the same with `η = c₁₀ ε_{k+1}` (`SFZInput`, P4 (4.1), (5.2)); `h7MixedDatumLoc2Pre_zero`: an admissible
  instance (rule 10);
* `massRegime_of_bgMass`: the mass condition from the cutoff masses `μ_j = bgMass(k₀, j)`
  (`FieldClauses.mu_eq`): the small-mass form for `k ≤ k₀`, the large-mass form for `k > k₀`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background

namespace Balaban.RootFSpine

set_option linter.unusedSectionVars false

section Pre

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-! ### Geometry of the data sites of `G′_{V₂(X,J)}` -/

/-- **Two sites within two cube sides lie over cubes of `𝕋_{k+1}` within two cubes.** -/
theorem cubeOfC_supDist_le_two {k : ℕ} {x y : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (h : LargeField.supDist x y ≤ 2 * (g.c * g.M1 * S.L ^ (k + 1))) :
    LargeField.supDist (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x)
      (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 y) ≤ 2 := by
  set P := S.L ^ (k + 1) * (g.c * g.M1) with hP
  have hP0 : 0 < P := Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _)
    (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne g.c)) (Nat.pos_of_ne_zero (NeZero.ne g.M1)))
  have hn : g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1) = P * n (k + 1) := by rw [hP]; ring
  rw [cubeOfC_eq_toCube, cubeOfC_eq_toCube]
  refine (supDist_blockMap_le hn _ _).trans ?_
  have e : LargeField.supDist (toCube g hM1 x) (toCube g hM1 y) = LargeField.supDist x y := by
    unfold toCube; exact LargeField.supDist_torusCast_eq _ x y
  rw [e]
  have h2 : 2 * (g.c * g.M1 * S.L ^ (k + 1)) = 2 * P := by rw [hP]; ring
  rw [h2] at h
  refine Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hP0).2 ?_)
  omega

/-- **The data sites of the local pair of `V₂(X, J)` lie over cubes within `ρ + 3` cubes of `Ω_{k+1}`**
for a family `J` of cover cubes in the localization range (`J ∈ allJ ρ`) and `r + r′ ≤ c M₁ L^{k+1}`:
the local set lies within `r + r′` of a site of `Ω_{k+1} ∩ X^{∼3}` or within `r′` of a site of the
localization range (cubes within `ρ + 1` of `Ω_{k+1}`), and the data sites of `𝔹_{k+1}(V)` lie within
`11 L^{m₁} L^{k+1} + 1 ≤ c M₁ L^{k+1}` of `V`. -/
theorem near_omega_of_mem_dataSites_locSetXJ2 (H : RegionHistory S n R k0 K) {k : ℕ}
    (hk : k + 1 ≤ K) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) {ρ r r' : ℕ} (hL : 2 ≤ S.L)
    (hroom : r + r' ≤ g.c * g.M1 * S.L ^ (k + 1)) (X : Finset (Torus S.d (n k)))
    {J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (hJ : J ∈ allJ g hnn hM1 H hk hρ ρ) {x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (hx : x ∈ dataSites (locG' g hnn hM1 H hk hρ (locSetXJ2 g hM1 H r r' X J))) :
    ∃ Y ∈ (H.step k).Omega,
      LargeField.supDist (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x) Y ≤ ρ + 3 := by
  classical
  have hc := g.hc
  have hx' := dataSites_inter_subset _ _ hx
  obtain ⟨v, hv, hxv⟩ := SmallField.GsSpec.localB_dataSites_range hL hx'
  obtain ⟨y, hy, hvy⟩ := hv
  -- the reach of the data sites
  have hs : 11 * S.L ^ m₁ * S.L ^ (k + 1) + 1 ≤ g.c * g.M1 * S.L ^ (k + 1) := by
    rw [hM1]
    have h1 : 1 ≤ S.L ^ m₁ * S.L ^ (k + 1) :=
      Nat.one_le_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (NeZero.ne _)) (pow_ne_zero _ (NeZero.ne _)))
    have h2 : g.c * S.L ^ m₁ * S.L ^ (k + 1) = g.c * (S.L ^ m₁ * S.L ^ (k + 1)) := by ring
    have h3 : 11 * S.L ^ m₁ * S.L ^ (k + 1) = 11 * (S.L ^ m₁ * S.L ^ (k + 1)) := by ring
    rw [h2, h3]
    nlinarith
  rcases hy with hcol | ⟨P, hPJ, hyP⟩
  · obtain ⟨y', hy', hyy'⟩ := (mem_collarCoreC _).1 hcol
    refine ⟨_, ((mem_activeCoreC _).1 hy').2, ?_⟩
    have hd : LargeField.supDist x y' ≤ 2 * (g.c * g.M1 * S.L ^ (k + 1)) := by
      have t1 := LargeField.supDist_triangle x v y
      have t2 := LargeField.supDist_triangle x y y'
      omega
    have := cubeOfC_supDist_le_two g hM1 hd
    omega
  · have hP := Finset.mem_filter.1 (Finset.mem_powerset.1 hJ hPJ)
    obtain ⟨x₀, hx₀Ω, hy₀⟩ := hP.2.2 (Finset.mem_coe.2 hyP)
    have hyx₀ := mem_nbhd.1 (mem_locDomC.1 hy₀)
    obtain ⟨w, hw, hyw⟩ := hyx₀
    rw [Set.mem_singleton_iff] at hw
    subst hw
    refine ⟨_, hx₀Ω, ?_⟩
    have hd : LargeField.supDist x y ≤ 2 * (g.c * g.M1 * S.L ^ (k + 1)) := by
      have t1 := LargeField.supDist_triangle x v y
      omega
    have h1 := cubeOfC_supDist_le_two g hM1 hd
    have t := LargeField.supDist_triangle (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x)
      (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 y) (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x₀)
    omega

include hnn in
/-- **A cube of `𝕋_k` under a cube of `𝕋_{k+1}` near `Ω_{k+1}` is far from `Z_k`** (P5 (2.3)): if the
coarse cube of `u` lies within `ρ + 3` cubes of `Ω_{k+1}`, `ρ ≤ ⌊R_k⌋`, then `u` is at distance
`≥ ⌊R_{k-1}⌋ + 3` from every cube of `Z_k` (`RegionStep.fine_far`: a cube under `Ω_{k+1}` is at
distance `≥ L(⌊R_k⌋ + 4) + ⌊R_{k-1}⌋ + 2` from `Z_k`). -/
theorem le_supDist_Z_of_near_omega (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) {ρ : ℕ}
    (hρk : ρ ≤ ⌊R k⌋₊) {u : Torus S.d (n k)} {Y : Torus S.d (n (k + 1))} (hY : Y ∈ (H.step k).Omega)
    (hu : LargeField.supDist (blockMap S.L (n (k + 1)) u) Y ≤ ρ + 3) {z : Torus S.d (n k)}
    (hz : z ∈ (H.step k).Z) : ⌊R (k - 1)⌋₊ + 3 ≤ LargeField.supDist u z := by
  have hL0 : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne S.L)
  have hn : n k = S.L * n (k + 1) := hnn k (by omega)
  obtain ⟨x₀, hx₀⟩ := cubeMap_surjective (S := S) (M := 1) hnn hk Y
  set u₀ := LargeField.cubeMap n S.L 1 K k x₀ with hu₀
  have hb : blockMap S.L (n (k + 1)) u₀ = Y := by rw [hu₀, cubeMap_succ hnn hk x₀, hx₀]
  have hff := (H.step k).fine_far hL0 hn (hb ▸ hY) hz
  have hle := supDist_le_blockMap hn u u₀
  rw [hb] at hle
  have t := LargeField.supDist_triangle u₀ u z
  rw [LargeField.supDist_comm u₀ u] at t
  have h1 : S.L * LargeField.supDist (blockMap S.L (n (k + 1)) u) Y ≤ S.L * (ρ + 3) :=
    Nat.mul_le_mul_left _ hu
  have h2 : S.L * (ρ + 4) ≤ S.L * (⌊R k⌋₊ + 4) := Nat.mul_le_mul_left _ (by omega)
  have h3 : S.L * (ρ + 4) = S.L * (ρ + 3) + S.L := by ring
  omega

include hnn in
/-- **The premise `hfar` for the pre-`R` records**: a cube of `𝕋_k` whose coarse cube lies within
`ρ + 3` cubes of `Ω_{k+1}` (`ρ ≤ ⌊R_k⌋`) is not within `3` cubes of a hole of scale `k` of
`globalLHPre H M (k + 1)` (the holes of scale `k` lie in `Z_k`). -/
theorem notMem_omegaCNb_globalLHPre_of_near (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) {ρ : ℕ} (hρk : ρ ≤ ⌊R k⌋₊) {u : Torus S.d (n k)}
    {Y : Torus S.d (n (k + 1))} (hY : Y ∈ (H.step k).Omega)
    (hu : LargeField.supDist (blockMap S.L (n (k + 1)) u) Y ≤ ρ + 3) :
    u ∉ omegaCNb (globalLHPre H M (k + 1)) 3 k := by
  rw [omegaCNb_globalLHPre_of_ne H (by omega : k ≠ k + 1)]
  intro hmem
  obtain ⟨y', hy', hd⟩ := mem_nbhd.1 hmem
  obtain ⟨x₁, hx₁⟩ := cubeMap_surjective (S := S) (M := M) hnn (Nat.le_of_succ_le hk) y'
  have hZ : y' ∈ (H.step k).Z := by
    have h1 := (hy' x₁ hx₁).1
    simp only [globalLH, fineSet, Set.mem_ofPred_eq, hx₁] at h1
    exact h1
  have := le_supDist_Z_of_near_omega hnn H hk hρk hY hu hZ
  have hL1 : 1 ≤ S.L := Nat.one_le_iff_ne_zero.2 (NeZero.ne S.L)
  omega

omit [NeZero M] [NeZero S.L] in
/-- **The premise `hholes` for the pre-`R` records** (ruling R17): every cube of `𝕋_{k+1}` off
`Ω_{k+1}` is a hole of scale `k + 1` of `globalLHPre H M (k + 1)` (`Ω^c_{k+1} ⊆ Z^pre_{k+1}`, Lemma
I.3.5 (e)). -/
theorem cubeSub_holes_globalLHPre (H : RegionHistory S n R k0 K) {k : ℕ} {Y : Torus S.d (n (k + 1))}
    (hY : Y ∉ (H.step k).Omega) :
    CubeSub (S := S) (n := n) M K (k + 1) Y
      ((globalLHPre H M (k + 1)).Z (k + 1) \ (globalLHPre H M (k + 1)).Omega k) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · show LargeField.cubeMap n S.L M K (k + 1) x ∈ (if k + 1 = k + 1 then H.F.Zpre (k + 1) else _)
    simp only [↓reduceIte]
    rw [hx]
    exact mem_Zpre_of_notMem_omega H hY
  · show ¬ LargeField.cubeMap n S.L M K (k + 1) x ∈ (H.step k).Omega
    rw [hx]
    exact hY

/-! ### The named input, restated, and its proof -/

/-- **OPEN-H7-MIXED, the background part, at the local sets of its use, for the pre-`R` records**
(restatement of `H7MixedDatumLoc2`, ruling R17): for every old label `X`, every family `J` of cover cubes
in the localization range (`J ∈ allJ ρ`), and every field of the H7 domain of scale `k + 1` of the
pre-`R` records `globalLHPre H M (k + 1)` with the external field `h₀` (ruling R16: the boundary terms
are asked at the physical field, `h₀ = Re h = hv`) at a set `Y_f` containing the cubes of `𝕋_{k+1}` of
the data sites of `G′_V`, `V = V₂(X, J)`, the restricted global datum of the local pair lies in
`Ψ̃^c(G′_V; δ_b, δ_b)`.  Proved by `h7MixedDatumLoc2Pre_holds`. -/
def H7MixedDatumLoc2Pre (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (ρ r r' : ℕ)
    (aw μs ε ε1 νs : ℕ → ℝ) (νb δb : ℝ) : Prop :=
  ∀ (X : Finset (Torus S.d (n k))) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))),
    J ∈ allJ g hnn hM1 H hk hρ ρ →
    ∀ (Yf : Set (Torus S.d (M * n K * S.L ^ K))) (ψ ψ' : MultiFieldC S n M K N)
      (gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ),
    H7Domain g.M1 g.c g.hM hnn (globalLHPre H M (k + 1)) (k + 1) hk Yf aw μs ε ε1 νs
      (fun i => (h₀ i : ℂ)) ψ ψ' gf →
    CubesOfIn (S := S) (n := n) (M := M) (K := K) (k + 1) Yf
      (fineOfC g hnn hM1 hk '' (dataSites (locG' g hnn hM1 H hk hρ (locSetXJ2 g hM1 H r r' X J)) :
        Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))) →
    InDomainC (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ2 g hM1 H r r' X J)).G'
      νb δb δb (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ2 g hM1 H r r' X J)).D'

/-- **`H7MixedDatumLoc2Pre` holds** (the case analysis `inDomainC_holeStepLoc2_of_h7` at the pre-`R`
records): for `L ≥ 2`, `ρ ≤ ⌊R_k⌋`, the room `r + r′ ≤ c M₁ L^{k+1}` (then every data site of
`G′_{V₂(X,J)}` lies over a cube within `ρ + 3` cubes of `Ω_{k+1}`, and its cube of `𝕋_k` is away from the
holes of scale `k`), `|z - 1| ≤ η`, `0 < ε_{k+1} ≤ ε_k`, condition (R4) for `h₀`, the mass condition in
either regime and `3 δ₁ + 2 ε_k ≤ δ_b`, `δ₁ = scaledTol ε_k ε_k η`, the datum lies in
`Ψ̃^c(δ_b, δ_b)` at the step's mass `ν`. -/
theorem h7MixedDatumLoc2Pre_holds (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ)
    {ρ r r' : ℕ} (aw μs ε ε1 νs : ℕ → ℝ) {η δb : ℝ} (hL : 2 ≤ S.L) (hρk : ρ ≤ ⌊R k⌋₊)
    (hroom : r + r' ≤ g.c * g.M1 * S.L ^ (k + 1))
    (hη : 0 ≤ η) (hz : |z - 1| ≤ η) (hε0 : 0 < ε (k + 1)) (hεk : ε (k + 1) ≤ ε k)
    (hR4 : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < scaledTol (ε k) (ε k) η ^ 2)
    (hmass : (0 ≤ ν ∧ ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * (1 + rn h₀) < scaledTol (ε k) (ε k) η ^ 2) ∨
      (∃ τ : ℝ, 0 < τ ∧ 0 ≤ ν ∧ ν ≤ τ * μs (k + 1) ∧ ν ≤ τ * μs k ∧
        2 * τ * ε k ^ 2 ≤ scaledTol (ε k) (ε k) η ^ 2))
    (hδb : 3 * scaledTol (ε k) (ε k) η + 2 * ε k ≤ δb) :
    H7MixedDatumLoc2Pre g hnn hM1 H hk hk1 hρ z h₀ a₁ ν β p₁ δ ρ r r' aw μs ε ε1 νs ν δb := by
  intro X J hJ Yf ψ ψ' gf htgt hY
  refine (inDomainC_holeStepLoc2_of_h7 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
    (locSetXJ2 g hM1 H r r' X J) (globalLHPre H M (k + 1)) rfl
    (fun Y hY => cubeSub_holes_globalLHPre H hY) htgt hY (fun x hx _ => ?_) hη hz hε0 hεk hR4
    hmass).mono_diag hδb
  obtain ⟨Y, hYΩ, hYd⟩ := near_omega_of_mem_dataSites_locSetXJ2 g hnn hM1 H hk hρ hL hroom X hJ hx
  exact notMem_omegaCNb_globalLHPre_of_near hnn H hk hρ hρk hYΩ
    (by rw [blockMap_cubeKOfC g hnn hM1 hk x]; exact hYd)

/-- **`H7MixedDatumLoc2Pre` with the field renormalization of `SFZInput`** (P4 (4.1), (5.2)): with
`|z_{k+1} - 1| ≤ c₁₀ ε_{k+1}` the premise on `z` holds at `η = c₁₀ ε_{k+1}`. -/
theorem h7MixedDatumLoc2Pre_of_sfz (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ)
    {ρ r r' : ℕ} (aw μs ε ε1 νs : ℕ → ℝ) {c₁₀ δb : ℝ} (hL : 2 ≤ S.L) (hρk : ρ ≤ ⌊R k⌋₊)
    (hroom : r + r' ≤ g.c * g.M1 * S.L ^ (k + 1)) (hc₁₀ : 0 ≤ c₁₀)
    (hz : |z - 1| ≤ c₁₀ * ε (k + 1)) (hε0 : 0 < ε (k + 1)) (hεk : ε (k + 1) ≤ ε k)
    (hR4 : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * |∑ i, h₀ i ^ 2 - 1| <
      scaledTol (ε k) (ε k) (c₁₀ * ε (k + 1)) ^ 2)
    (hmass : (0 ≤ ν ∧ ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * (1 + rn h₀) <
        scaledTol (ε k) (ε k) (c₁₀ * ε (k + 1)) ^ 2) ∨
      (∃ τ : ℝ, 0 < τ ∧ 0 ≤ ν ∧ ν ≤ τ * μs (k + 1) ∧ ν ≤ τ * μs k ∧
        2 * τ * ε k ^ 2 ≤ scaledTol (ε k) (ε k) (c₁₀ * ε (k + 1)) ^ 2))
    (hδb : 3 * scaledTol (ε k) (ε k) (c₁₀ * ε (k + 1)) + 2 * ε k ≤ δb) :
    H7MixedDatumLoc2Pre g hnn hM1 H hk hk1 hρ z h₀ a₁ ν β p₁ δ ρ r r' aw μs ε ε1 νs ν δb :=
  h7MixedDatumLoc2Pre_holds g hnn hM1 H hk hk1 hρ z h₀ a₁ ν β p₁ δ aw μs ε ε1 νs hL hρk hroom
    (mul_nonneg hc₁₀ hε0.le) hz hε0 hεk hR4 hmass hδb

/-- **An admissible instance of `H7MixedDatumLoc2Pre`** (rule 10): at `z = 1`, zero mass, `ρ = r = r' = 0`
and `δ_b = 5 ε_k`, for `L ≥ 2` and `0 < ε_{k+1} ≤ ε_k`. -/
theorem h7MixedDatumLoc2Pre_zero (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (h₀ : Fin N → ℝ) (a₁ β p₁ δ : ℝ)
    (aw μs ε ε1 νs : ℕ → ℝ) (hL : 2 ≤ S.L) (hε0 : 0 < ε (k + 1)) (hεk : ε (k + 1) ≤ ε k) :
    H7MixedDatumLoc2Pre g hnn hM1 H hk hk1 hρ 1 h₀ a₁ 0 β p₁ δ 0 0 0 aw μs ε ε1 νs 0 (5 * ε k) := by
  have hεk0 : 0 < ε k := hε0.trans_le hεk
  have hδ : scaledTol (ε k) (ε k) 0 = ε k := by unfold scaledTol; ring
  refine h7MixedDatumLoc2Pre_holds g hnn hM1 H hk hk1 hρ 1 h₀ a₁ 0 β p₁ δ aw μs ε ε1 νs hL
    (Nat.zero_le _) (Nat.zero_le _) le_rfl (by simp) hε0 hεk ?_ (Or.inl ⟨le_rfl, ?_⟩) ?_
  · rw [hδ]; simp only [zero_mul]; positivity
  · rw [hδ]; simp only [zero_mul]; positivity
  · rw [hδ]; linarith

/-! ### The mass condition from the cutoff masses -/

/-- **The mass condition of `h7MixedDatumLoc2Pre_holds` from the cutoff masses** `μ_j = bgMass(k₀, j)`
(`FieldClauses.mu_eq`, P5 (1.18)–(1.19): zero for `j ≤ k₀`, `ν_j L^{-2j}` above): for `k ≤ k₀` the
small-mass form, `ν L^{2(k+1)} (1 + |h₀|) < δ₁²`; for `k > k₀` the large-mass form with the factor
`τ`, `ν ≤ τ ν_{k+1} L^{-2(k+1)}`, `ν ≤ τ ν_k L^{-2k}` (the step's mass against the cutoff masses of the
two scales) and `2 τ ε_k² ≤ δ₁²`. -/
theorem massRegime_of_bgMass {L k k₀ : ℕ} {ν δ₁ εk : ℝ} {νq μs : ℕ → ℝ} (h₀ : Fin N → ℝ)
    (hμ1 : μs (k + 1) = LargeField.bgMass k₀ L νq (k + 1)) (hμ0 : μs k = LargeField.bgMass k₀ L νq k)
    (hν : 0 ≤ ν)
    (hsmall : k ≤ k₀ → ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (1 + rn h₀) < δ₁ ^ 2)
    (hlarge : k₀ < k → ∃ τ : ℝ, 0 < τ ∧ ν ≤ τ * (νq (k + 1) / (L : ℝ) ^ (2 * (k + 1))) ∧
      ν ≤ τ * (νq k / (L : ℝ) ^ (2 * k)) ∧ 2 * τ * εk ^ 2 ≤ δ₁ ^ 2) :
    (0 ≤ ν ∧ ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (1 + rn h₀) < δ₁ ^ 2) ∨
      (∃ τ : ℝ, 0 < τ ∧ 0 ≤ ν ∧ ν ≤ τ * μs (k + 1) ∧ ν ≤ τ * μs k ∧ 2 * τ * εk ^ 2 ≤ δ₁ ^ 2) := by
  rcases Nat.lt_or_ge k₀ k with hk | hk
  · obtain ⟨τ, hτ, h1, h2, h3⟩ := hlarge hk
    refine Or.inr ⟨τ, hτ, hν, ?_, ?_, h3⟩
    · have hn : ¬ k + 1 ≤ k₀ := by omega
      rw [hμ1, LargeField.bgMass]; simp only [hn, ↓reduceIte]; exact h1
    · have hn : ¬ k ≤ k₀ := by omega
      rw [hμ0, LargeField.bgMass]; simp only [hn, ↓reduceIte]; exact h2
  · exact Or.inl ⟨hν, hsmall hk⟩

end Pre

end Balaban.RootFSpine
