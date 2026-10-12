/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroInput
public import Balaban.LargeField.R.PsiZeroConvex
public import Balaban.LargeField.R.ChainCount
public import Balaban.Localization.DecoupledBackground

/-!
# Lemma III.3.3: existence and uniqueness of the solution of (2.34), from the cited expansion estimate

`PsiZeroSol` says that `ψ` is a solution of the variational problem (2.34) in the tube `Ψ̃(X; κ)`: it lies in the tube,
equals `ψ_k` off the box `Z₀`, and minimizes the effective action among all such fields.
`psiZero_exists_unique_of_input` proves, from `PsiZeroInput`, that for `δ ≤ c₁₁` there is exactly one solution in
`Ψ̃(X; K₆ δ)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Metric

section Exists

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)

/-- **A solution of (2.34) in `Ψ̃(X; κ)`**: `ψ ∈ Ψ̃(X; κ)`, `ψ = ψ_k` off the box `Z₀`, and `ψ` minimizes
`A_k(𝔹_k(U_k); ψ̃, φ_k(𝔹_k(U_k); ψ̃))` among all such fields. -/
def PsiZeroSol (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ) (X : Set (Torus d (N₀ * L ^ (k - k)))) (κ : ℝ)
    (ψk ψ : BlockField d L N₀ k N) : Prop :=
  TubeOn G X κ ψ ∧ (∀ z, z ∉ box b0 w → ψ z = ψk z) ∧
    ∀ ψ' : BlockField d L N₀ k N, TubeOn G X κ ψ' → (∀ z, z ∉ box b0 w → ψ' z = ψk z) →
      effAction G a ψ ≤ effAction G a ψ'

theorem tubeOn_mono_set {X Y : Set (Torus d (N₀ * L ^ (k - k)))} (h : X ⊆ Y) {δ : ℝ}
    {ψ : BlockField d L N₀ k N} (ht : TubeOn G Y δ ψ) : TubeOn G X δ ψ :=
  ⟨fun x x' hp hx hx' => ht.1 x x' hp (h hx) (h hx'), fun x hx hX => ht.2 x hx (h hX)⟩

theorem tubeOn_mono {X : Set (Torus d (N₀ * L ^ (k - k)))} {δ δ' : ℝ} (h : δ ≤ δ')
    {ψ : BlockField d L N₀ k N} (ht : TubeOn G X δ ψ) : TubeOn G X δ' ψ :=
  ⟨fun x x' hp hx hx' => lt_of_lt_of_le (ht.1 x x' hp hx hx') h,
    fun x hx hX => lt_of_lt_of_le (ht.2 x hx hX) h⟩

theorem card_boxFinset_le {D : ℕ} (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ) (hwD : ∀ i, w i ≤ D) :
    ((boxFinset (L := L) (N₀ := N₀) (k := k) b0 w).card : ℝ) ≤ (D : ℝ) ^ d := by
  have h1 : (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w).card = (box b0 w).ncard := by
    rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]; rfl
  have h2 : (box b0 w).ncard ≤ D ^ d := by
    refine (ncard_box_le b0 w).trans ?_
    calc ∏ i, w i ≤ D ^ (Finset.univ : Finset (Fin d)).card :=
          Finset.prod_le_pow_card _ _ _ fun i _ => hwD i
      _ = D ^ d := by simp
  rw [h1]; exact_mod_cast h2

variable [NeZero N]

/-- The tube radius produced by `tube_of_close` from a closeness radius `ν`. -/
def tubeRad (d D : ℕ) (δ ν : ℝ) : ℝ := ν * (2 + ν) + 2 * ν + (12 * d * (D + 2) + 3) * δ + δ

theorem tubeRad_le (d D : ℕ) {δ ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν ≤ 1) :
    tubeRad d D δ ν ≤ 5 * ν + (12 * d * (D + 2) + 3 + 1) * δ := by
  unfold tubeRad; nlinarith

theorem tubeRad_mono (d D : ℕ) {δ ν ν' : ℝ} (h0 : 0 ≤ ν) (h : ν ≤ ν') :
    tubeRad d D δ ν ≤ tubeRad d D δ ν' := by
  unfold tubeRad; nlinarith

/-- The reference vector `ψ₀` of `ψ_k` on the box. -/
noncomputable def refPt (ψk : BlockField d L N₀ k N) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ) :
    EuclideanSpace ℝ (Fin N) := refVec (fun z => eu (ψk z)) (box b0 w)

/-- The centre `ψ_{k,0}↾Z₀ = ψ₀` of the ball on which the variational function is analysed. -/
noncomputable def centrePt (ψk : BlockField d L N₀ k N) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ) :
    SuppSpace (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) N :=
  constSupp (boxFinset b0 w) (refPt ψk b0 w)

theorem tube_merge {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
    (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
    {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
    (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
    (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) {δ : ℝ} (hδ : 0 < δ)
    {ψk : BlockField d L N₀ k N} (hψk : TubeOn G (X \ box b0 w) δ ψk)
    (u : SuppSpace (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) N) {ν : ℝ} (hν : 0 ≤ ν)
    (hu : ‖u - centrePt ψk b0 w‖ ≤ ν) :
    TubeOn G Set.univ (tubeRad d D δ ν) (mergeField (boxFinset b0 w) ψk u) := by
  refine tube_of_close hd hk b0 w hw1 hwD hm hXreg hΩ hdata hδ hν hψk
    (fun z hz => mergeField_of_not_mem (fun h => hz (mem_boxFinset.1 h))) ?_
  intro z hz
  exact (norm_merge_sub_le ψk u (refPt ψk b0 w) (mem_boxFinset.2 hz)).trans hu

/-- Smoothness and the Hessian bound on a ball about `ψ_{k,0}`. -/
theorem local_analysis {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k)))
    (w : Fin d → ℕ) (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
    {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
    (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
    (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)
    (inp : PsiZeroInput (N := N) G a b0 w X) {δ r τ : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hτ : 0 < τ)
    (hτη : τ ≤ inp.η₀) (hτ0 : τ ≤ bgC0 d L N) (hτ1 : τ ≤ bgC1 d L N)
    (hrad : tubeRad d D δ (2 * r) ≤ τ) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) :
    (∀ u ∈ closedBall (centrePt ψk b0 w) r, ContDiffAt ℝ 2 (effOn G a (boxFinset b0 w) ψk) u) ∧
    ∀ u ∈ closedBall (centrePt ψk b0 w) r, ∀ v : SuppSpace (boxFinset b0 w) N,
      inp.c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (effOn G a (boxFinset b0 w) ψk)) u v v := by
  have hsm : ContDiffOn ℝ 2 (effOn G a (boxFinset b0 w) ψk) (ball (centrePt ψk b0 w) (2 * r)) := by
    have h1 := contDiffOn_effAction (n := 2) (a := a) G H hτ hτ0 hτ1
      (U := {ψ | TubeOn G Set.univ τ ψ}) (fun ψ hψ => hψ)
    refine h1.comp (contDiff_mergeField (n := 2) ψk).contDiffOn fun u hu => ?_
    have hu' : ‖u - centrePt ψk b0 w‖ ≤ 2 * r := by
      rw [← dist_eq_norm]; exact (mem_ball.1 hu).le
    exact tubeOn_mono G hrad (tube_merge G hd hk b0 w hw1 hwD hm hXreg hΩ hdata hδ hψk u (by positivity) hu')
  refine ⟨fun u hu => hsm.contDiffAt (isOpen_ball.mem_nhds (by
      rw [mem_ball]; have := mem_closedBall.1 hu; linarith)), fun u hu v => ?_⟩
  have hu' : ‖u - centrePt ψk b0 w‖ ≤ r := by rw [← dist_eq_norm]; exact mem_closedBall.1 hu
  have ht := tubeOn_mono G ((tubeRad_mono d D hr.le (by linarith)).trans hrad)
    (tube_merge G hd hk b0 w hw1 hwD hm hXreg hΩ hdata hδ hψk u hr.le hu')
  have h := inp.hess (mergeField (boxFinset b0 w) ψk u) τ hτ hτη ht v
  rw [effOn_merge, restrict_mergeField] at h
  exact h

/-- The convexity argument: from smoothness, the Hessian bound, and the gradient bound, (2.34) has exactly one
solution in the tube. -/
theorem solve_core {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k)))
    (w : Fin d → ℕ) (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
    {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
    (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w))) {δ r c ε K M : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    (hc : 0 < c) (hε0 : 0 ≤ ε) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk)
    (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X)
    (hF : ∀ u ∈ closedBall (centrePt ψk b0 w) r, ContDiffAt ℝ 2 (effOn G a (boxFinset b0 w) ψk) u)
    (hlow : ∀ u ∈ closedBall (centrePt ψk b0 w) r, ∀ v : SuppSpace (boxFinset b0 w) N,
      c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (effOn G a (boxFinset b0 w) ψk)) u v v)
    (hres : ‖fderiv ℝ (effOn G a (boxFinset b0 w) ψk) (centrePt ψk b0 w)‖ ≤ ε) (hεr : ε ≤ c * r / 2)
    (hK : tubeRad d D δ (ε / c) ≤ K * δ) (hK0 : 0 ≤ K)
    (hsqrt : Real.sqrt ((boxFinset (L := L) (N₀ := N₀) (k := k) b0 w).card) ≤ M)
    (hMr : M * (D * (K * δ) + (12 * d * (D + 2) + 3) * δ) ≤ r) :
    ∃! ψ, PsiZeroSol G a b0 w X (K * δ) ψk ψ := by
  have hZfmem : ∀ z, z ∈ boxFinset (L := L) (N₀ := N₀) (k := k) b0 w ↔ z ∈ box b0 w := fun z => mem_boxFinset
  obtain ⟨x, hxB, hxcrit, hxuniq, hxdist, hxmin⟩ :=
    exists_unique_critical_ball hF hc hr.le hlow hres hεr
  have hag : ∀ z, z ∉ box b0 w → mergeField (boxFinset b0 w) ψk x z = ψk z := fun z hz =>
    mergeField_of_not_mem ((hZfmem z).not.2 hz)
  have hν0 : 0 ≤ ε / c := by positivity
  have hxtube : TubeOn G X (K * δ) (mergeField (boxFinset b0 w) ψk x) :=
    tubeOn_mono_set G (Set.subset_univ _) (tubeOn_mono G hK
      (tube_merge G hd hk b0 w hw1 hwD hm hXreg hΩ hdata hδ hψk x hν0 hxdist))
  have hclose : ∀ y : BlockField d L N₀ k N, TubeOn G X (K * δ) y →
      (∀ z, z ∉ box b0 w → y z = ψk z) → ‖restrictSupp (boxFinset b0 w) y - centrePt ψk b0 w‖ ≤ r := by
    intro y hy hyag
    have h := close_of_tube (D := D) hd hk b0 w hw1 hwD hm hXreg hΩ (by positivity : 0 ≤ K * δ) hψk hy hyag
    have h2 := norm_restrict_sub_le (Zf := boxFinset b0 w) y (refPt ψk b0 w)
      (by positivity : 0 ≤ D * (K * δ) + (12 * d * (D + 2) + 3) * δ)
      (fun z hz => h z ((hZfmem z).1 hz))
    refine h2.trans (le_trans ?_ hMr)
    exact mul_le_mul_of_nonneg_right hsqrt (by positivity)
  have hmerge : ∀ y : BlockField d L N₀ k N, (∀ z, z ∉ box b0 w → y z = ψk z) →
      mergeField (boxFinset b0 w) ψk (restrictSupp (boxFinset b0 w) y) = y := fun y hy =>
    mergeField_restrict fun z hz => hy z ((hZfmem z).not.1 hz)
  have e : ∀ y : BlockField d L N₀ k N, (∀ z, z ∉ box b0 w → y z = ψk z) →
      effAction G a y = effOn G a (boxFinset b0 w) ψk (restrictSupp (boxFinset b0 w) y) := by
    intro y hy; simp only [effOn]; rw [hmerge y hy]
  have hsol : PsiZeroSol G a b0 w X (K * δ) ψk (mergeField (boxFinset b0 w) ψk x) := by
    refine ⟨hxtube, hag, fun y hy hyag => ?_⟩
    have hyB' : restrictSupp (boxFinset b0 w) y ∈ closedBall (centrePt ψk b0 w) r := by
      rw [mem_closedBall, dist_eq_norm]; exact hclose y hy hyag
    by_cases he : restrictSupp (boxFinset b0 w) y = x
    · rw [← hmerge y hyag, he]
    · rw [e y hyag]; exact (hxmin _ hyB' he).le
  refine ⟨_, hsol, fun y hy => ?_⟩
  obtain ⟨hyt, hyag, hymin⟩ := hy
  have hyB' : restrictSupp (boxFinset b0 w) y ∈ closedBall (centrePt ψk b0 w) r := by
    rw [mem_closedBall, dist_eq_norm]; exact hclose y hyt hyag
  by_contra hne
  have hne' : restrictSupp (boxFinset b0 w) y ≠ x := fun h => hne (by rw [← hmerge y hyag, h])
  have hlt := hxmin _ hyB' hne'
  have hle := hymin _ hxtube hag
  rw [e y hyag] at hle
  have e2 : effAction G a (mergeField (boxFinset b0 w) ψk x) = effOn G a (boxFinset b0 w) ψk x := rfl
  rw [e2] at hle
  linarith

/-- The numerical constants of Lemma III.3.3: `K₆ = 5 Gr / c + C₂.₂₀ + 1`. -/
theorem psiZero_constants (d D : ℕ) (hd0 : 0 < d) (hD1 : 1 ≤ D) {c Gr η₀ b0c b1c : ℝ} (hc : 0 < c)
    (hGr : 0 ≤ Gr) (hη : 0 < η₀) (h0 : 0 < b0c) (h1 : 0 < b1c) :
    ∃ K c11 : ℝ, 0 < K ∧ 0 < c11 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ c11 →
      ∃ r τ : ℝ, 0 < r ∧ 0 < τ ∧ τ ≤ η₀ ∧ τ ≤ b0c ∧ τ ≤ b1c ∧
        tubeRad d D δ (2 * r) ≤ τ ∧ δ ≤ τ ∧ Gr * δ ≤ c * r / 2 ∧ Gr * δ / c ≤ 1 ∧
        tubeRad d D δ (Gr * δ / c) ≤ K * δ ∧
        (D : ℝ) ^ d * (D * (K * δ) + (12 * d * (D + 2) + 3) * δ) ≤ r := by
  have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hC0 : (0 : ℝ) ≤ 12 * d * (D + 2) + 3 := by positivity
  have hM1 : (1 : ℝ) ≤ (D : ℝ) ^ d := one_le_pow₀ hD1'
  have hG0 : 0 ≤ 5 * Gr / c := by positivity
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 5 * Gr / c + (12 * d * (D + 2) + 3) + 1 := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = (D : ℝ) ^ d * (D * K + (12 * d * (D + 2) + 3)) := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 10 * P + (12 * d * (D + 2) + 3) + 1 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by linarith
  have hPK : K ≤ P := by
    have h1 : K ≤ D * K := by nlinarith
    rw [hPdef]; nlinarith
  have hP0 : 0 < P := by linarith
  have hA1 : 1 ≤ A := by linarith
  refine ⟨K, min (min (1 / (2 * P)) (c / (Gr + 1))) (min η₀ (min b0c b1c) / A), by linarith,
    lt_min (lt_min (by positivity) (by positivity)) (div_pos (lt_min hη (lt_min h0 h1)) (by linarith)),
    fun δ hδ hδc => ?_⟩
  have hδ1 : δ ≤ 1 / (2 * P) := hδc.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ2 : δ ≤ c / (Gr + 1) := hδc.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ3 : δ ≤ min η₀ (min b0c b1c) / A := hδc.trans (min_le_right _ _)
  have hAδ : A * δ ≤ min η₀ (min b0c b1c) := by
    rw [le_div_iff₀ (by linarith)] at hδ3; linarith
  have hPδ : 2 * (P * δ) ≤ 1 := by
    rw [le_div_iff₀ (by linarith)] at hδ1; linarith
  have hGrδ : Gr * δ ≤ c := by
    rw [le_div_iff₀ (by linarith)] at hδ2; nlinarith
  have hAδ' : δ ≤ A * δ := by nlinarith
  have hPr : (D : ℝ) ^ d * (D * (K * δ) + (12 * d * (D + 2) + 3) * δ) = P * δ := by
    rw [hPdef]; ring
  have hν : Gr * δ / c ≤ 1 := by rw [div_le_one hc]; exact hGrδ
  have hν0 : 0 ≤ Gr * δ / c := by positivity
  refine ⟨P * δ, A * δ, by positivity, by positivity, hAδ.trans (min_le_left _ _),
    hAδ.trans ((min_le_right _ _).trans (min_le_left _ _)),
    hAδ.trans ((min_le_right _ _).trans (min_le_right _ _)), ?_, hAδ', ?_, hν, ?_, hPr.le⟩
  · refine (tubeRad_le d D (by positivity) (by linarith)).trans ?_
    rw [hAdef]; nlinarith
  · have h5 : 5 * Gr ≤ c * K := by
      have h := mul_le_mul_of_nonneg_left (show 5 * Gr / c ≤ K by linarith) hc.le
      rw [mul_div_cancel₀ _ hc.ne'] at h; exact h
    have : K * δ ≤ P * δ := mul_le_mul_of_nonneg_right hPK hδ.le
    nlinarith [mul_nonneg hGr hδ.le]
  · refine (tubeRad_le d D hν0 hν).trans ?_
    have e : 5 * (Gr * δ / c) = 5 * Gr / c * δ := by ring
    rw [e, hKdef]; nlinarith

/-- **Lemma III.3.3, existence and uniqueness (from the cited expansion estimate `PsiZeroInput`)**: there are
`K₆, c₁₁ > 0` such that for `0 < δ ≤ c₁₁` and `ψ_k ∈ Ψ̃(X ∖ Z₀; δ)` the variational problem (2.34) has exactly one
solution in `Ψ̃(X; K₆ δ)`. -/
theorem psiZero_exists_unique_of_input {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k)))
    (w : Fin d → ℕ) (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
    {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
    (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
    (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)
    (inp : PsiZeroInput (N := N) G a b0 w X) :
    ∃ K c11 : ℝ, 0 < K ∧ 0 < c11 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ c11 → ∀ ψk : BlockField d L N₀ k N,
      TubeOn G (X \ box b0 w) δ ψk → ∃! ψ, PsiZeroSol G a b0 w X (K * δ) ψk ψ := by
  have hd0 : 0 < d := by omega
  have hD1 : 1 ≤ D := (hw1 ⟨0, hd0⟩).trans (hwD _)
  obtain ⟨K, c11, hK, hc11, hmain⟩ := psiZero_constants d D hd0 hD1 inp.c_pos inp.Gr_nonneg inp.η₀_pos
    (bgC0_pos d L N hd0) (Balaban.Localization.bgC1_pos' (d := d) (L := L) (N := N) hd0)
  refine ⟨K, c11, hK, hc11, fun δ hδ hδc ψk hψk => ?_⟩
  obtain ⟨r, τ, hr, hτ, hτη, hτ0, hτ1, hrad, hδτ, hε, -, hKr, hMr⟩ := hmain δ hδ hδc
  obtain ⟨hF, hlow⟩ := local_analysis G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H inp hδ hr hτ hτη hτ0 hτ1
    hrad hψk
  have hsqrt : Real.sqrt ((boxFinset (L := L) (N₀ := N₀) (k := k) b0 w).card) ≤ (D : ℝ) ^ d := by
    have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
    have hM1 : (1 : ℝ) ≤ (D : ℝ) ^ d := one_le_pow₀ hD1'
    have hcard := card_boxFinset_le (L := L) (N₀ := N₀) (k := k) b0 w hwD
    have hn := Nat.cast_nonneg (α := ℝ) (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w).card
    exact Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  exact solve_core G a hd hk b0 w hw1 hwD hm hXreg hΩ hδ hr inp.c_pos (mul_nonneg inp.Gr_nonneg hδ.le)
    hψk hdata hF hlow (inp.grad ψk δ hδ (hδτ.trans hτη) hψk) hε hKr hK.le hsqrt hMr

end Exists

end Balaban.LargeField
