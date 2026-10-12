/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.H7Bridge
public import Balaban.Fluctuation.CubeActionRealBound
public import Balaban.LargeField.Background.StepGenSetsFlow
import Balaban.Localization.DecoupledFieldX0
import Balaban.LargeField.Region.Generating

/-!
# The distance premise of Step 3 and the star Step 3 on any torus (FLUCTUATION §4.2)

* `pathDist_shadow_ge`: if the sites of `R` are at torus distance `≥ T` from the support `W` of the
  data change, the path distance from `R ∩ Ω₁` to the `Ω₁`-shadow of `W` is at least
  `min((T - 1)/L^{m+1}, ϱ - 1)` (`m` bounds the layer indices on `R`; `pathDist_ge_torusDist`);
* `torusDist_ge_of_not_nbhd`: the cube distance `D_k` (LFR Lemma II.2.5 (c)): a site at distance
  `≤ 1` from `Z'`-fine sites is at torus distance `≥ L^{k+1} c M₁ ρ` from every site whose
  `π_{k+1}`-cube is outside `Z'^{∼ρ}`;
* `step_dist_premise`: the two combined, for the data change vanishing on `E = fine(Z'^{∼ρ})`;
* `cubeDiffStar_step3_quadratic_gen`: `cubeDiffStar_step3_quadratic` on a torus of any size
  `N₀ * L ^ K`, with the distance premise in the form `pathDist y w` for `w` in `shadowN`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField

section Dist

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The distance premise of Step 3 from the physical distance** (FLUCTUATION §4.2 Step 2): if the
sites of `R` with layer index at most `m` are at torus distance at least `T` from every site of
`W` (the support of the data change), then the path distance from such a site to the `Ω₁`-shadow
of `W` is at least `min((T - 1)/L^{m+1}, ϱ - 1)`. -/
theorem pathDist_shadow_ge (G : GeneratingSet d L N₀ k ϱ) (hϱ : 1 ≤ ϱ) {m : ℕ}
    (R : Finset (Torus d (N₀ * L ^ k))) (hRm : ∀ y ∈ R, y ∈ G.Ω 1 → G.layerIndex y ≤ m)
    (W : Finset (Torus d (N₀ * L ^ k))) {T : ℝ}
    (hfar : ∀ y ∈ R, ∀ w ∈ W, T ≤ Green.torusDist d (N₀ * L ^ k) y w) :
    ∀ y ∈ R, y ∈ G.Ω 1 → ∀ w ∈ shadowN G W,
      ENNReal.ofReal (min ((T - 1) / (L : ℝ) ^ (m + 1)) (ϱ - 1)) ≤ G.pathDist y w := by
  intro y hyR hyΩ w hw
  obtain ⟨hn1, hnk, hyl⟩ := G.layerIndex_spec hyΩ
  set n := G.layerIndex y with hn
  have hnm := hRm y hyR hyΩ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hdist : T - 1 ≤ Green.torusDist d (N₀ * L ^ k) y w := by
    classical
    obtain ⟨-, hw1⟩ := Finset.mem_filter.1 hw
    rcases hw1.2 with hwW | ⟨w', hw'W, hadj⟩
    · have := hfar y hyR w hwW; linarith
    · have h1 := hfar y hyR w' hw'W
      have h2 := Green.torusDist_triangle_gen (d := d) (m := N₀ * L ^ k) y w w'
      have h3 : Green.torusDist d (N₀ * L ^ k) w w' ≤ 1 := hadj.torusDist_le
      linarith
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (pathDist_ge_torusDist G hϱ hn1 hyl w)
  set c : ℝ := (L : ℝ) ^ (n + 1) with hc
  set cm : ℝ := (L : ℝ) ^ (m + 1) with hcm
  have hc1 : 1 ≤ c := one_le_pow₀ hL1
  have hcc : c ≤ cm := pow_le_pow_right₀ hL1 (by omega)
  have hc0 : 0 < c := by linarith
  have hcm0 : 0 < cm := by linarith
  rw [← min_div_div_right hc0.le]
  refine le_min ((min_le_left _ _).trans ?_) ((min_le_right _ _).trans ?_)
  · by_cases hT : T - 1 ≤ 0
    · have h1 : (T - 1) / cm ≤ 0 := div_nonpos_of_nonpos_of_nonneg hT hcm0.le
      have h2 : 0 ≤ Green.torusDist d (N₀ * L ^ k) y w / c := by
        have := Green.torusDist_nonneg_gen (d := d) (m := N₀ * L ^ k) y w
        positivity
      linarith
    · push Not at hT
      calc (T - 1) / cm ≤ (T - 1) / c := div_le_div_of_nonneg_left hT.le hc0 hcc
        _ ≤ _ := div_le_div_of_nonneg_right hdist hc0.le
  · have e : (ϱ * c - 1) / c = ϱ - 1 / c := by field_simp
    have : 1 / c ≤ 1 := by rw [div_le_one hc0]; exact hc1
    rw [e]; linarith

end Dist

section Real

variable {d M1 c n1 L : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n1]

/-- **The cube distance `D_k`** (FLUCTUATION §4.2 Step 2; LFR Lemma II.2.5 (c)): a site at torus
distance at most `1` from a site whose `π_{k+1}`-cube lies in `Z'` is at torus distance at least
`L^{k+1} c M₁ ρ` from every site whose cube is not in the `ρ`-neighbourhood of `Z'`. -/
theorem torusDist_ge_of_not_nbhd (k : ℕ) (Z' : Set (Torus d n1)) (ρ : ℕ)
    {x y e : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (hx : blockMap (L ^ (k + 1) * (c * M1)) n1 x ∈ Z')
    (hxy : Green.torusDist d (M1 * (c * n1) * L ^ (k + 1)) y x ≤ 1)
    (he : blockMap (L ^ (k + 1) * (c * M1)) n1 e ∉ nbhd ρ Z') :
    ((L ^ (k + 1) * (c * M1) : ℕ) : ℝ) * ρ ≤ Green.torusDist d (M1 * (c * n1) * L ^ (k + 1)) y e := by
  have hℓ : M1 * (c * n1) * L ^ (k + 1) = (L ^ (k + 1) * (c * M1)) * n1 := by ring
  have hPpos : 0 < L ^ (k + 1) * (c * M1) := Nat.pos_of_ne_zero (by
    have := NeZero.ne L; have := NeZero.ne M1; have := NeZero.ne c; positivity)
  have h1 := torusDist_lower (d := d) hℓ hPpos x e
  have hsup : ρ + 1 ≤ supDist (blockMap (L ^ (k + 1) * (c * M1)) n1 x)
      (blockMap (L ^ (k + 1) * (c * M1)) n1 e) := by
    by_contra hlt
    push Not at hlt
    apply he
    rw [mem_nbhd]
    refine ⟨_, hx, ?_⟩
    rw [supDist_comm]
    omega
  have h2 : ((L ^ (k + 1) * (c * M1) : ℕ) : ℝ) * ((ρ : ℝ) + 1) ≤
      ((L ^ (k + 1) * (c * M1) : ℕ) : ℝ) *
        (supDist (blockMap (L ^ (k + 1) * (c * M1)) n1 x)
          (blockMap (L ^ (k + 1) * (c * M1)) n1 e) : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hsup) (Nat.cast_nonneg _)
  have h3 := Green.torusDist_triangle_gen (d := d) (m := M1 * (c * n1) * L ^ (k + 1)) x y e
  have h4 : Green.torusDist d (M1 * (c * n1) * L ^ (k + 1)) x y =
      Green.torusDist d (M1 * (c * n1) * L ^ (k + 1)) y x := Green.torusDist_comm_gen _ _
  nlinarith

end Real

section Step

variable {d M1 c n1 L : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n1] {ϱ : ℝ}

open Classical in
/-- The sites of the level-`(k+1)` torus whose `π_{k+1}`-cube lies outside `Z'^{∼ρ}`: the
complement of `E = Z'^{∼ρ}` (the support of the data change `δΨ`, which vanishes on `E`). -/
noncomputable def stepFarSites (k : ℕ) (Z' : Set (Torus d n1)) (ρ : ℕ) :
    Finset (Torus d (M1 * (c * n1) * L ^ (k + 1))) :=
  Finset.univ.filter fun e => blockMap (L ^ (k + 1) * (c * M1)) n1 e ∉ nbhd ρ Z'

open Classical in
/-- The sites at torus distance `≤ 1` from a site whose `π_{k+1}`-cube lies in `Z'`: the
neighbourhood `X_{Z'}^{+1}` on which the regularity inequalities are used. -/
noncomputable def stepNearSites (k : ℕ) (Z' : Set (Torus d n1)) :
    Finset (Torus d (M1 * (c * n1) * L ^ (k + 1))) :=
  Finset.univ.filter fun y => ∃ x, blockMap (L ^ (k + 1) * (c * M1)) n1 x ∈ Z' ∧
    Green.torusDist d (M1 * (c * n1) * L ^ (k + 1)) y x ≤ 1

/-- The scaled distance `min((L^{k+1} c M₁ ρ - 1)/L^{k+2}, ϱ - 1)` of Step 3 for a data change
vanishing on `Z'^{∼ρ}` (`step_dist_premise`). -/
noncomputable def stepDist (L M1 c k ρ : ℕ) (ϱ : ℝ) : ℝ :=
  min ((((L ^ (k + 1) * (c * M1) : ℕ) : ℝ) * ρ - 1) / (L : ℝ) ^ (k + 1 + 1)) (ϱ - 1)

theorem mem_stepFarSites {k : ℕ} {Z' : Set (Torus d n1)} {ρ : ℕ}
    {e : Torus d (M1 * (c * n1) * L ^ (k + 1))} :
    e ∈ stepFarSites (M1 := M1) (c := c) (L := L) k Z' ρ ↔
      blockMap (L ^ (k + 1) * (c * M1)) n1 e ∉ nbhd ρ Z' := by
  classical
  simp only [stepFarSites, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_stepNearSites {k : ℕ} {Z' : Set (Torus d n1)}
    {y : Torus d (M1 * (c * n1) * L ^ (k + 1))} :
    y ∈ stepNearSites (M1 := M1) (c := c) (L := L) k Z' ↔
      ∃ x, blockMap (L ^ (k + 1) * (c * M1)) n1 x ∈ Z' ∧
        Green.torusDist d (M1 * (c * n1) * L ^ (k + 1)) y x ≤ 1 := by
  classical
  simp only [stepNearSites, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The distance premise of Step 3 for the real step**: for a data change vanishing on
`E = Z'^{∼ρ}` (so supported in `stepFarSites`), the path distance from `X_{Z'}^{+1} ∩ Ω₁` to the
shadow of its support is at least `min((L^{k+1} c M₁ ρ - 1)/L^{k+2}, ϱ - 1)`. -/
theorem step_dist_premise (k : ℕ) (G : GeneratingSet d L (M1 * (c * n1)) (k + 1) ϱ) (hϱ : 1 ≤ ϱ)
    (Z' : Set (Torus d n1)) (ρ : ℕ) :
    ∀ y ∈ stepNearSites (M1 := M1) (c := c) k Z', y ∈ G.Ω 1 →
      ∀ w ∈ shadowN G (stepFarSites (M1 := M1) (c := c) k Z' ρ),
      ENNReal.ofReal (stepDist L M1 c k ρ ϱ) ≤ G.pathDist y w := by
  classical
  refine pathDist_shadow_ge G hϱ _ (fun y _ hyΩ => (G.layerIndex_spec hyΩ).2.1) _ ?_
  intro y hy w hw
  obtain ⟨x, hx, hxy⟩ := mem_stepNearSites.1 hy
  exact torusDist_ge_of_not_nbhd k Z' ρ hx hxy (mem_stepFarSites.1 hw)

end Step

section StarGen

variable {d L : ℕ} [NeZero L]

/-- **`cubeDiffStar_step3_quadratic` on a torus of arbitrary size** `N₀ * L ^ K` (star convention);
the distance premise is stated with `pathDist` to the sites of `shadowN G W`. -/
theorem cubeDiffStar_step3_quadratic_gen (hd : 3 ≤ d) (hL : 3 ≤ L) {N : ℕ} {Cδ : ℝ} (hCδ : 0 ≤ Cδ) :
    ∃ CF δw : ℝ, 0 < CF ∧ 0 < δw ∧
      ∀ {N₀ K N₁ m₁ : ℕ} [NeZero N₀] (_hN : N₀ = N₁ * L ^ m₁) {ϱ : ℝ}
        {G : GeneratingSet d L N₀ K ϱ}
        {a : ℕ → ℝ} {ν : ℝ}, BgHyp d L K ϱ a ν → 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1) →
        ∀ {D Du : BgData G N} {δ ε δ' ε' : ℝ},
        0 < δ → δ ≤ ε → ε ≤ bgC0 d L N → δ ≤ bgC1 d L N →
        ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2 → InDomainC G ν δ ε D →
        0 < δ' → δ' ≤ ε' → ε' ≤ bgC0 d L N → δ' ≤ bgC1 d L N →
        ν * ((L : ℝ) ^ K) ^ 2 * ε' ^ 2 ≤ δ' ^ 2 → InDomainC G ν δ' ε' Du →
        bgK1 d L N * δ ≤ deltaStar d L N → bgK1 d L N * δ ≤ δw →
        ∀ {δΨ : Torus d (N₀ * L ^ K) → Fin N → ℂ} (W : Finset (Torus d (N₀ * L ^ K))),
        (∀ y ∉ W, δΨ y = 0) →
        (∀ x i, Du.Ψ x i = D.Ψ x i + δΨ x i) → (∀ x i, Du.h x i = D.h x i) →
        ∀ {δ₁ : ℝ}, 0 ≤ δ₁ → δ₁ ≤ deltaStar d L N → δ₁ ≤ δw →
        (∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₁) →
        ∀ (Q R : Finset (Torus d (N₀ * L ^ K))) {r Dist : ℝ}, 0 ≤ r → 0 ≤ Dist → δ₁ ≤ Cδ * r →
        Q ⊆ R → (∀ x ∈ Q, ∀ μ : Fin d, x + Pi.single μ 1 ∈ R) →
        (∀ x : Torus d (N₀ * L ^ K), ∀ μ : Fin d, x + Pi.single μ 1 ∈ Q → x ∈ R) →
        (∀ x ∈ Q, x ∈ G.Ω 1 → ∀ y ∈ G.blk (G.layerIndex x) x, y ∈ R) →
        RegIneq G a ν D r R R →
        (∀ y ∈ R, y ∈ G.Ω 1 → ∀ w ∈ shadowN G W, ENNReal.ofReal Dist ≤ G.pathDist y w) →
        ∀ β : ℝ, 0 ≤ β →
        ‖(β : ℂ) * (cubeActionStar G a ν Q D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) Du) -
            cubeActionStar G a ν Q D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) D))‖ ≤
          CF * β * Q.card * r ^ 2 * Real.exp (-(gammaW d * Dist)) := by
  obtain ⟨CF, δw, hCF, hδw, hstep⟩ := cubeDiffStar_step3_quadratic (N := N) hd hL hCδ
  refine ⟨CF, δw, hCF, hδw, ?_⟩
  intro N₀ K N₁ m₁ _ hN ϱ G a ν H hsep D Du δ ε δ' ε' hδ0 hδε hε hδ1 hνε hD hδ0' hδε' hε' hδ1' hνε'
    hDu hK1 hKw δΨ W hsupp hΨ hh δ₁ hδ₁0 hδ₁s hδ₁w hdΨ Q R r Dist hr hDist hδr hQR hQR1 hQR2 hQblk
    hreg hdist β hβ
  subst hN
  have : NeZero N₁ := ⟨by rintro rfl; exact absurd (by simp) (NeZero.ne (0 * L ^ m₁))⟩
  have hOp : Dec2.OpSetting G a ν :=
    ⟨H.hd, H.hL, H.mass, H.massLe, H.weights, hsep⟩
  refine hstep H hOp hδ0 hδε hε hδ1 hνε hD hδ0' hδε' hε' hδ1' hνε' hDu hK1 hKw W hsupp hΨ hh
    hδ₁0 hδ₁s hδ₁w hdΨ Q R hr hDist hδr hQR hQR1 hQR2 hQblk hreg ?_ β hβ
  intro y hy hyΩ
  refine le_iInf₂ fun w hw => hdist y hy hyΩ w ?_
  exact hw

end StarGen

end Balaban.Fluctuation
