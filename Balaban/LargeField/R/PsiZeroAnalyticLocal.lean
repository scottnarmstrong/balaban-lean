/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroExists
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The local structure of the solution of (2.34) (data for its analytic continuation)

* `eventually_tubeOn`: the tube `Ψ̃(X; κ)` is open in the block field (finitely many strict inequalities);
* `solve_core_crit`: the proof of `solve_core` (`PsiZeroExists`) with its intermediate data kept: the solution is the
  merge of the unique critical point `x` of the variational function in the ball, and every block field of
  `Ψ̃(X; K₆ δ)` agreeing with `ψ_k` off `Z₀` has its restriction in the ball;
* `psiZero_local_of_input`: the same for the constants of `psiZero_exists_unique_of_input`: radii `r, τ`
  (`τ ≤ min (c₀, c₁)`), the tube `Ψ̃(𝔹; τ)` on the ball, smoothness and the Hessian bound on the ball.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Filter Topology Metric

set_option linter.unusedSectionVars false

section Open

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)

theorem eventually_tubeOn {X : Set (Torus d (N₀ * L ^ (k - k)))} {κ : ℝ} {ψ : BlockField d L N₀ k N}
    (h : TubeOn G X κ ψ) : ∀ᶠ ψ' in 𝓝 ψ, TubeOn G X κ ψ' := by
  classical
  refine Filter.Eventually.and ?_ ?_
  · refine Filter.eventually_all.2 fun x => Filter.eventually_all.2 fun x' => ?_
    by_cases hc : IsInterfacePair G x x' ∧ jBlock d L N₀ k k x ∈ X ∧ jBlock d L N₀ k k x' ∈ X
    · have hlt := h.1 x x' hc.1 hc.2.1 hc.2.2
      have hcont : Continuous (fun ψ' : BlockField d L N₀ k N =>
          rn (fun i => liftR ψ' x i - liftR ψ' x' i)) := by
        unfold rn liftR
        fun_prop
      filter_upwards [hcont.continuousAt.eventually_lt continuousAt_const hlt] with ψ' hψ' _ _ _ using hψ'
    · exact Filter.Eventually.of_forall fun ψ' hp hx hx' => absurd ⟨hp, hx, hx'⟩ hc
  · refine Filter.eventually_all.2 fun x => ?_
    by_cases hc : x ∈ dataSites G ∧ jBlock d L N₀ k k x ∈ X
    · have hlt := h.2 x hc.1 hc.2
      have hcont : Continuous (fun ψ' : BlockField d L N₀ k N =>
          |∑ i, ψ' (jBlock d L N₀ k k x) i ^ 2 - 1|) := by fun_prop
      filter_upwards [hcont.continuousAt.eventually_lt continuousAt_const hlt] with ψ' hψ' _ _ using hψ'
    · exact Filter.Eventually.of_forall fun ψ' hx hX => absurd ⟨hx, hX⟩ hc

end Open

section Crit

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)
  [NeZero N]

open Metric in
theorem solve_core_crit {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k)))
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
    ∃ x ∈ closedBall (centrePt ψk b0 w) r,
      fderiv ℝ (effOn G a (boxFinset b0 w) ψk) x = 0 ∧
      PsiZeroSol G a b0 w X (K * δ) ψk (mergeField (boxFinset b0 w) ψk x) ∧
      (∀ y : BlockField d L N₀ k N, TubeOn G X (K * δ) y → (∀ z, z ∉ box b0 w → y z = ψk z) →
        restrictSupp (boxFinset b0 w) y ∈ closedBall (centrePt ψk b0 w) r) ∧
      (∀ y ∈ closedBall (centrePt ψk b0 w) r, fderiv ℝ (effOn G a (boxFinset b0 w) ψk) y = 0 → y = x) ∧
      (∀ ψ : BlockField d L N₀ k N, PsiZeroSol G a b0 w X (K * δ) ψk ψ →
        ψ = mergeField (boxFinset b0 w) ψk x) := by
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
  refine ⟨x, hxB, hxcrit, hsol, ?_, hxuniq, ?_⟩
  · intro y hy hyag
    rw [mem_closedBall, dist_eq_norm]; exact hclose y hy hyag
  · intro y hy
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

end Crit

section Local

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)
  [NeZero N]

open Metric in
/-- **The local structure of the solution of (2.34)**: besides the existence and uniqueness of the solution, the
data used to continue it analytically: the radii `r, τ`, the tube `Ψ̃(𝔹; τ)` on the ball of radius `r`, smoothness and
the Hessian bound on that ball, and the critical point `x` (whose merge is the solution). -/
theorem psiZero_local_of_input {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k)))
    (w : Fin d → ℕ) (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
    {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
    (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
    (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)
    (inp : PsiZeroInput (N := N) G a b0 w X) :
    ∃ K c11 : ℝ, 0 < K ∧ 0 < c11 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ c11 → ∀ ψk : BlockField d L N₀ k N,
      TubeOn G (X \ box b0 w) δ ψk →
      ∃ r τ : ℝ, 0 < r ∧ 0 < τ ∧ τ ≤ bgC0 d L N ∧ τ ≤ bgC1 d L N ∧
        (∀ u ∈ closedBall (centrePt ψk b0 w) r,
          TubeOn G Set.univ τ (mergeField (boxFinset b0 w) ψk u)) ∧
        (∀ u ∈ closedBall (centrePt ψk b0 w) r, ContDiffAt ℝ 2 (effOn G a (boxFinset b0 w) ψk) u) ∧
        (∀ u ∈ closedBall (centrePt ψk b0 w) r, ∀ v : SuppSpace (boxFinset b0 w) N,
          inp.c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (effOn G a (boxFinset b0 w) ψk)) u v v) ∧
        ∃ x ∈ closedBall (centrePt ψk b0 w) r,
          fderiv ℝ (effOn G a (boxFinset b0 w) ψk) x = 0 ∧
          PsiZeroSol G a b0 w X (K * δ) ψk (mergeField (boxFinset b0 w) ψk x) ∧
          (∀ y : BlockField d L N₀ k N, TubeOn G X (K * δ) y → (∀ z, z ∉ box b0 w → y z = ψk z) →
            restrictSupp (boxFinset b0 w) y ∈ closedBall (centrePt ψk b0 w) r) ∧
          (∀ y ∈ closedBall (centrePt ψk b0 w) r,
            fderiv ℝ (effOn G a (boxFinset b0 w) ψk) y = 0 → y = x) ∧
          (∀ ψ : BlockField d L N₀ k N, PsiZeroSol G a b0 w X (K * δ) ψk ψ →
            ψ = mergeField (boxFinset b0 w) ψk x) := by
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
  refine ⟨r, τ, hr, hτ, hτ0, hτ1, ?_, hF, hlow, ?_⟩
  · intro u hu
    have hu' : ‖u - centrePt ψk b0 w‖ ≤ 2 * r := by
      rw [← dist_eq_norm]; have := mem_closedBall.1 hu; linarith
    exact tubeOn_mono G hrad (tube_merge G hd hk b0 w hw1 hwD hm hXreg hΩ hdata hδ hψk u (by positivity) hu')
  · exact solve_core_crit G a hd hk b0 w hw1 hwD hm hXreg hΩ hδ hr inp.c_pos
      (mul_nonneg inp.Gr_nonneg hδ.le) hψk hdata hF hlow
      (inp.grad ψk δ hδ (hδτ.trans hτη) hψk) hε hKr hK.le hsqrt hMr

end Local

end Balaban.LargeField
