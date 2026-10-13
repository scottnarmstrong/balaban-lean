/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkFibreSitesOf
public import Balaban.Inhabited.Thm31aFromTower
public import Balaban.Inhabited.Thm31bKernelSupport

/-!
# Theorem 3.1 (a) and (b): coefficients indexed by the paper's domains

The landed coefficient theorems of Theorem 3.1 index the terms by finite sets `T` of level-one
cubes, with decay `exp(-κ dExt T)`.  The map `T ↦ sitesOf T` is injective, and on the sets with
`sitesOf T` a polymer it takes values in the domains `IsDj 1 (k+1)` with `sizeJ 1 (k+1) (sitesOf T)
= dExt T` (`markFibre_sitesOf`).  Hence the same expansions are indexed by the site sets
`Y = sitesOf T`, with decay in `sizeJ 1 (k+1) Y`, and every non-zero term has a root block
contained in `Y`.

* `sitesOf_regroup`: the generic re-indexing.
* `thm31a_zeroClass_sites_fromTower`: Theorem 3.1 (a), energy.
* `thm31b_zeroClass_sites_fromTower`: Theorem 3.1 (b), coefficient part only.
* `sitesOf_regroup_analytic`, `sitesOf_regroup_eq`: parameter dependence of the re-indexing.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Set Metric

section Generic

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

open Classical in
/-- **Re-indexing a cube-set expansion by site sets.**  Let `e` be supported on the cube sets `T`
with `sitesOf T` a polymer, bounded by `B exp(-lam dExt T)` there, and non-zero only if the cube
`bx` lies in `T`.  Then the sum over site sets `X` of the filtered sums
`eY X = ∑_{sitesOf T = X} e T` equals `∑ e`; `eY (sitesOf T) = e T`; `eY X ≠ 0` implies that `X` is
`IsDj` and contains the box of `bx`; and `‖eY X‖ ≤ B exp(-lam sizeJ X)`. -/
theorem sitesOf_regroup (hN : L ^ m₀ ∣ N₁)
    (e : Finset 𝔅 → ℂ)
    (B lam : ℝ) (hB : 0 ≤ B)
    (bx : 𝔅)
    (hbd : ∀ T, IsPolyDom m₀ K (sitesOf T) → ‖e T‖ ≤ B * Real.exp (-lam * dExt T))
    (hsupp : ∀ T, e T ≠ 0 → IsPolyDom m₀ K (sitesOf T) ∧ bx ∈ T) :
    ∃ eY : Set (CTorus d L N₁ m₁ K) → ℂ,
      (∀ X, eY X = ∑ T ∈ Finset.univ.filter (fun T' : Finset 𝔅 => sitesOf T' = X), e T) ∧
      (∀ T : Finset 𝔅, eY (sitesOf T) = e T) ∧
      ∑ T, e T = ∑ X ∈ Finset.univ.image (fun T : Finset 𝔅 => sitesOf T), eY X ∧
      (∀ X, eY X ≠ 0 → IsDj m₀ K X ∧
        box bx.1 (cellSide L m₀ m₁ K) ⊆ X) ∧
      (∀ X, ‖eY X‖ ≤ B * Real.exp (-lam * sizeJ m₀ K X)) := by
  obtain ⟨-, -, -, hfib⟩ := markFibre_sitesOf.{0} (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
    (m₀ := m₀) hN
  obtain ⟨hF, hbound, hsum⟩ := hfib e B lam hB hbd (fun T hT => by
    by_contra h
    exact hT (hsupp T h).1)
  refine ⟨fun X => ∑ T ∈ Finset.univ.filter (fun T' : Finset 𝔅 => sitesOf T' = X), e T, fun X => rfl,
    fun T => ?_, hsum, fun X hX => ?_, hbound⟩
  · simp only [hF (sitesOf T) T rfl, Finset.sum_singleton]
  · obtain ⟨T, hT, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hX
    have hTX : sitesOf T = X := (Finset.mem_filter.1 hT).2
    obtain ⟨hpoly, hbx⟩ := hsupp T hne
    subst hTX
    refine ⟨(markFibre_sitesOf.{0} (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) hN).1 T
      hpoly |>.1, fun z hz => ?_⟩
    exact mem_sitesOf.2 ⟨bx, hbx, hz⟩

open Classical in
/-- Analyticity in a parameter passes to the re-indexed coefficients: if `θ ↦ e θ T` is analytic
on `V` for every `T`, then so is `θ ↦ ∑_{sitesOf T = X} e θ T` for every `X`. -/
theorem sitesOf_regroup_analytic {α : Type*} [NormedAddCommGroup α] [NormedSpace ℂ α]
    (e : α → Finset 𝔅 → ℂ) (V : Set α)
    (he : ∀ T, AnalyticOnNhd ℂ (fun θ => e θ T) V) (X : Set (CTorus d L N₁ m₁ K)) :
    AnalyticOnNhd ℂ
      (fun θ => ∑ T ∈ Finset.univ.filter (fun T' : Finset 𝔅 => sitesOf T' = X), e θ T) V :=
  fun θ hθ => Finset.analyticAt_fun_sum _ (fun T _ => he T θ hθ)

open Classical in
/-- Locality passes to the re-indexed coefficients: if `e θ T = e θ' T` for every `T` with
`sitesOf T = X`, then the regrouped coefficients at `X` agree at `θ` and `θ'`. -/
theorem sitesOf_regroup_eq {α : Type*} (e : α → Finset 𝔅 → ℂ) (θ θ' : α)
    (X : Set (CTorus d L N₁ m₁ K)) (h : ∀ T : Finset 𝔅, sitesOf T = X → e θ T = e θ' T) :
    ∑ T ∈ Finset.univ.filter (fun T' : Finset 𝔅 => sitesOf T' = X), e θ T =
      ∑ T ∈ Finset.univ.filter (fun T' : Finset 𝔅 => sitesOf T' = X), e θ' T :=
  Finset.sum_congr rfl fun T hT => h T (Finset.mem_filter.1 hT).2

end Generic

open Classical in
/-- **Theorem 3.1 (a), energy term, on the paper's domains.**  As
`thm31a_zeroClass_supp_fromTower`, with the coefficients re-indexed by the site sets
`Y = sitesOf T'`: `E0locC` is the sum over the domains `Y` in the image of `sitesOf` of
`eY Y = ∑_{sitesOf T' = Y} e T'`; each non-zero `eY Y` has `Y` in `𝒟_{k+1}` (`IsDj 1 (k+1) Y`) and
contains the box of the root cube of `z`; `‖eY Y‖ ≤ (2·27·BL + 1) K0 exp(-κ' · sizeJ 1 (k+1) Y)`;
and `eY (sitesOf T') = e T'`. -/
theorem thm31a_zeroClass_sites_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ _ : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      StepScaleData T k hk N₁ ν β p₁ →
      ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
        ∃ (e : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ)
          (eY : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ℂ),
          (T.step k hk N₁ ν β p₁).E0locC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z =
            ∑ T', e T' ∧
          (T.step k hk N₁ ν β p₁).E0locC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z =
            ∑ Y ∈ Finset.univ.image (fun T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁)
              (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) => sitesOf T'), eY Y ∧
          (∀ Y, eY Y = ∑ T' ∈ Finset.univ.filter (fun T'' : Finset (CubeB (d := 3) (L := 3)
              (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) => sitesOf T'' = Y),
              e T') ∧
          (∀ T', eY (sitesOf T') = e T') ∧
          (∀ Y, eY Y ≠ 0 → IsDj 1 (k + 1) Y ∧
            box (rootCube (m₀ := 1) (K := k + 1) z).1 (cellSide 3 1 T.m₁ (k + 1)) ⊆ Y) ∧
          ∀ Y, ‖eY Y‖ ≤ (2 * (3 : ℝ) ^ 3 * (covBLogMax 3 3 T.κ /
              (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) + 1) *
            K0 3 3 T.κ0 * Real.exp (-T.κ' * sizeJ 1 (k + 1) Y) := by
  obtain ⟨β₀, h3, h⟩ := thm31a_zeroClass_supp_fromTower T hHull hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D z => ?_⟩
  obtain ⟨e, hsum, hbd, hsupp⟩ := h k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D z
  have hB : 0 ≤ (2 * (3 : ℝ) ^ 3 * (covBLogMax 3 3 T.κ /
              (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) + 1) *
            K0 3 3 T.κ0 := by
    have h0 := (norm_nonneg (e ∅)).trans (hbd ∅)
    exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 h0
  obtain ⟨eY, h1, h2, h3', h4, h5⟩ := sitesOf_regroup (L := 3) (N₁ := N₁) (m₁ := T.m₁)
    (K := k + 1) (m₀ := 1) (by simpa using h3N) e _ T.κ' hB (rootCube z)
    (fun T' _ => hbd T') (fun T' hne => ⟨(hsupp T' hne).2, (hsupp T' hne).1⟩)
  exact ⟨e, eY, hsum, hsum.trans h3', h1, h2, h4, h5⟩

open Classical in
/-- **`thm31b_zeroClass_sites_fromTower_rho` for the general tower.**  From
`thm31b_onCommonWitness_fromTowerG_supp_rho`: the constant `Cthm` does not depend on `ρ`; for each
`ρ > 0` the threshold `β₀` satisfies `3 ≤ β₀` and `ρ ≤ β₀`, and the sources `g` range over the `ℓ¹`
ball of radius `ρ`.  The coefficients are indexed by the site sets `Y = sitesOf T'`, with decay in
`sizeJ T.m₀ (k+1) Y`.  The step `S` is over `ϱ = rhoSepG d L T.m₁` and is `T.step …` up to `HEq`,
`b = β L^{k(d-2)}`.  The fixed `thm31b_zeroClass_sites_fromTower_rho` is its corollary. -/
theorem thm31b_zeroClass_sites_fromTowerG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (C : StepOutputConsts d L)
    (hKc : C.Kc = 2 * (K0 d L T.κ0 + 1))
    (hKall : C.Kall = max (2 * K0 d L T.κ0) (rootUnionK d L T.m₀ T.m₁ T.κ0))
    (hH : C.kH = 2 * T.κdec - 1) (h0 : C.k0 = T.κ0) (h' : C.k' = T.κ') {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ Cthm : ℝ, 0 ≤ Cthm ∧
  ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ρ ≤ β₀ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_hLN : L ^ T.m₀ ∣ N₁), 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (b : ℝ), b = β * (L : ℝ) ^ (k * (d - 2)) → ∀ (p₁ : ℝ) (_hp0 : 0 < p₁),
  p₁ ≤ pLog A₁ p b → StepScaleDataG T k hk N₁ ν β p₁ →
  ∀ (ϱ : ℝ), ϱ = rhoSepG d L T.m₁ →
  ∀ (S : StepSetting d L N₁ T.m₁ k N ϱ), HEq S (T.step k hk N₁ ν β p₁) →
  ∀ (_hp : 0 < S.p₁),
    ∀ g : Fld d L N₁ T.m₁ (k + 1) N, g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N ρ →
    ∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N),
    ∃ (E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
        Set.univ) → ℂ)
      (eY : Set (CTorus d L N₁ T.m₁ (k + 1)) → ℂ),
      S.M0C (zeroClass d L N₁ T.m₁ k N ϱ) g y i =
        ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', E T' ∧
      S.M0C (zeroClass d L N₁ T.m₁ k N ϱ) g y i =
        ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ Y ∈ Finset.univ.image
          (fun T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀
            (k + 1) Set.univ) => sitesOf T'), eY Y ∧
      (∀ Y, eY Y = ∑ T' ∈ Finset.univ.filter (fun T'' : Finset (CubeB (d := d) (L := L)
          (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1) Set.univ) => sitesOf T'' = Y),
          E T') ∧
      (∀ T', eY (sitesOf T') = E T') ∧
      (∀ Y, eY Y ≠ 0 → IsDj T.m₀ (k + 1) Y ∧
        box (rootCube (m₀ := T.m₀) (K := k + 1) (blockIndex y)).1
          (cellSide L T.m₀ T.m₁ (k + 1)) ⊆ Y) ∧
      ∀ Y, ‖eY Y‖ ≤ Cthm * obsPrefactor p s b *
        Real.exp (-(3 / 2 * T.κdec) * sizeJ T.m₀ (k + 1) Y) := by
  classical
  obtain ⟨CE, CF, Cthm, -, -, hC, h⟩ :=
    thm31b_onCommonWitness_fromTowerG_supp_rho T C hKc hKall hH h0 h' hA p hCR hs0 hs
  refine ⟨Cthm, hC, fun ρ hρ => ?_⟩
  obtain ⟨β₀, h3, hρβ, h⟩ := h ρ hρ
  refine ⟨β₀, h3, hρβ, fun k hk N₁ _ hLN h5 ν hν hνk β hβ b hb p₁ hp0 hp₁ hsc ϱ hϱ S hS hp g hg y i => ?_⟩
  obtain ⟨-, -, -, -, -, -, hlast⟩ := h k hk N₁ hLN h5 ν hν hνk β hβ b hb p₁ hp0 hp₁ hsc ϱ hϱ S hS hp
  obtain ⟨E, hsum, hroot, hbd, hsupp⟩ := hlast g hg y i
  have hB : 0 ≤ Cthm * obsPrefactor p s b := by
    have h0 := (norm_nonneg (E ∅)).trans (hbd ∅)
    exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 h0
  obtain ⟨eY, h1, h2, h3', h4, h5'⟩ := sitesOf_regroup (L := L) (N₁ := N₁) (m₁ := T.m₁)
    (K := k + 1) (m₀ := T.m₀) hLN E _ (3 / 2 * T.κdec) hB
    (rootCube (blockIndex y))
    (fun T' _ => hbd T')
    (fun T' hne => ⟨hsupp T' hne, by
      by_contra hn; exact hne (hroot T' hn)⟩)
  exact ⟨E, eY, hsum, by rw [hsum, h3'], h1, h2, h4, h5'⟩


open Classical in
/-- **`thm31b_zeroClass_sites_fromTower` at source radius `ρ`.**  From
`thm31b_onCommonWitness_fromTower_supp_rho`: the constant `C` does not depend on `ρ`; for each
`ρ > 0` the threshold `β₀` satisfies `3 ≤ β₀` and `ρ ≤ β₀`, and the sources `g` range over the `ℓ¹`
ball of radius `ρ`.  The coefficients are indexed by the site sets `Y = sitesOf T'` as in
`thm31b_zeroClass_sites_fromTower`. -/
theorem thm31b_zeroClass_sites_fromTower_rho {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧
  ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ρ ≤ β₀ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : 3 ∣ N₁), 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (_hp0 : 0 < p₁),
  p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
  ∀ (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)), S = T.step k hk N₁ ν β p₁ →
  ∀ (_hp : 0 < S.p₁),
    ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 ρ →
    ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    ∃ (E : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ)
      (eY : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ℂ),
      S.M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
        ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', E T' ∧
      S.M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
        ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ Y ∈ Finset.univ.image
          (fun T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
            (k + 1) Set.univ) => sitesOf T'), eY Y ∧
      (∀ Y, eY Y = ∑ T' ∈ Finset.univ.filter (fun T'' : Finset (CubeB (d := 3) (L := 3)
          (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) => sitesOf T'' = Y),
          E T') ∧
      (∀ T', eY (sitesOf T') = E T') ∧
      (∀ Y, eY Y ≠ 0 → IsDj 1 (k + 1) Y ∧
        box (rootCube (m₀ := 1) (K := k + 1) (blockIndex y)).1 (cellSide 3 1 T.m₁ (k + 1)) ⊆ Y) ∧
      ∀ Y, ‖eY Y‖ ≤ C * obsPrefactor p s (β * 3 ^ k) *
        Real.exp (-(3 / 2 * T.κdec) * sizeJ 1 (k + 1) Y) := by
  classical
  obtain ⟨Cthm, hC, H⟩ :=
    thm31b_zeroClass_sites_fromTowerG_rho T.toG (stepOutputPhysical T hHull) rfl rfl rfl rfl rfl
      hA p hCR hs0 hs
  refine ⟨Cthm, hC, fun ρ hρ => ?_⟩
  obtain ⟨β₀, h3, hρβ, H1⟩ := H ρ hρ
  refine ⟨β₀, h3, hρβ, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D S hS hp
  exact H1 k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ (β * 3 ^ k)
    (by norm_num) p₁ hp0 hp₁ (StepTower.scaleDataG_of_fixed T D) _ (rhoSepG_three _).symm S
    (by rw [hS]; exact (StepTower.toG_step_heq T k hk N₁ ν β p₁).symm) hp


open Classical in
/-- **Theorem 3.1 (b), observable term, on the paper's domains (coefficient part only).**  From
`thm31b_onCommonWitness_fromTower_supp`: the witness clauses (`val`, `𝒴`, `Tt`, the label
activities) are not restated; only the coefficient clause is, for the base datum, with the
coefficients indexed by the site sets `Y = sitesOf T'`.  For each `g` in the `ℓ¹` ball and each
`y, i`, `M0C` is `betaU^{1/2}` times the sum over the image of `sitesOf` of `eY Y`; non-zero `eY Y`
has `IsDj 1 (k+1) Y` and contains the box of the root cube of the block of `y`;
`‖eY Y‖ ≤ C · obsPrefactor · exp(-(3/2 κ_dec) sizeJ 1 (k+1) Y)`. -/
theorem thm31b_zeroClass_sites_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ β₀ C : ℝ, 3 ≤ β₀ ∧ 0 ≤ C ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : 3 ∣ N₁), 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (_hp0 : 0 < p₁),
  p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
  ∀ (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)), S = T.step k hk N₁ ν β p₁ →
  ∀ (_hp : 0 < S.p₁),
    ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
    ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    ∃ (E : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ)
      (eY : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ℂ),
      S.M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
        ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', E T' ∧
      S.M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
        ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ Y ∈ Finset.univ.image
          (fun T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
            (k + 1) Set.univ) => sitesOf T'), eY Y ∧
      (∀ Y, eY Y = ∑ T' ∈ Finset.univ.filter (fun T'' : Finset (CubeB (d := 3) (L := 3)
          (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) => sitesOf T'' = Y),
          E T') ∧
      (∀ T', eY (sitesOf T') = E T') ∧
      (∀ Y, eY Y ≠ 0 → IsDj 1 (k + 1) Y ∧
        box (rootCube (m₀ := 1) (K := k + 1) (blockIndex y)).1 (cellSide 3 1 T.m₁ (k + 1)) ⊆ Y) ∧
      ∀ Y, ‖eY Y‖ ≤ C * obsPrefactor p s (β * 3 ^ k) *
        Real.exp (-(3 / 2 * T.κdec) * sizeJ 1 (k + 1) Y) := by
  obtain ⟨C, hC, H⟩ := thm31b_zeroClass_sites_fromTower_rho T hHull hA p hCR hs0 hs
  obtain ⟨β₀, h3, -, H1⟩ := H 1 one_pos
  exact ⟨β₀, C, h3, hC, H1⟩


end Balaban.Inhabited
