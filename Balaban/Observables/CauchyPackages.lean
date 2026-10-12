/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.Cauchy
public import Balaban.SmallField.Def6Terms

/-!
# `g`-derivatives of inherited packages (OBSERVABLES.md §3.2, Lemma 3.2)

A *package* `a(Y; g)` is an analytic function of the complex source `g : T → ℂ^N` on the open
`ℓ¹` unit ball `{‖g‖₁ < 1}` (`‖g‖₁ = ∑_x |g(x)|`, the `l1` of `Def6`), bounded there by `B_Y`, that
depends on `g` only through `g|_Y` (locality in `g`).

* `l1Seminorm`: the `ℓ¹` norm as a seminorm; `l1Seminorm_apply` identifies it with `Def6.l1`;
* `fderiv_srcDelta_eq_zero`, `D2_srcDelta_eq_zero_left/right`: `∂_{g_i(x)} a(Y; 0) = 0` unless
  `x ∈ Y` and the second derivatives vanish unless `x, y ∈ Y`;
* `norm_fderiv_srcDelta_le`, `norm_D2_srcDelta_le`: `|∂_{g_i(x)} a(Y; 0)| ≤ B_Y` (hence `≤ 2 B_Y`)
  and `|∂_{g_i(x)} ∂_{g_k(y)} a(Y; 0)| ≤ 4 B_Y` (hence `≤ 32 B_Y`): the Lemma 3.2;
* `fderiv_sum_srcDelta`, `D2_sum_srcDelta`: for a finite sum `A = ∑_Y a(Y; ·)` of packages the
  derivative at a site `x` only picks the packages with `x ∈ Y` (resp. `x, y ∈ Y`), and
  `norm_fderiv_sum_srcDelta_le`, `norm_D2_sum_srcDelta_le` bound it by `∑_{Y ∋ x} B_Y`
  (resp. `4 ∑_{Y ∋ x, y} B_Y`);
* `norm_fderiv_pkg_le`, `norm_D2_pkg_le`: the bounds `|M_R| ≤ 2 β_k^{-2} e^{-κ d}` and
  `β_k |∂²a| ≤ 32 β_k^{-1} e^{-κ d}` for `B_Y = β_k^{-n-1} e^{-κ d}`, `n ≥ 1`, `β_k ≥ 1`.
-/

@[expose] public section

open Metric Set Filter Topology Finset

namespace Balaban.Observables

open Balaban.SmallField Balaban.Multiscale

variable {T : Type*} [Fintype T] {N : ℕ}

/-- The `ℓ¹` norm `‖g‖₁ = ∑_x |g(x)|` of a source `g : T → ℂ^N` as a seminorm. -/
noncomputable def l1Seminorm : Seminorm ℂ (T → Fin N → ℂ) where
  toFun g := ∑ x : T, vn (g x)
  map_zero' := by simp [vn]
  add_le' g g' := by
    calc ∑ x : T, vn ((g + g') x) ≤ ∑ x : T, (vn (g x) + vn (g' x)) :=
          Finset.sum_le_sum fun x _ => vn_add (g x) (g' x)
      _ = _ := Finset.sum_add_distrib
  neg' g := by simp [vn]
  smul' c g := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    show ‖(WithLp.toLp 2 (c • g x) : EuclideanSpace ℂ (Fin N))‖ = ‖c‖ * vn (g x)
    rw [show (WithLp.toLp 2 (c • g x) : EuclideanSpace ℂ (Fin N)) =
      c • (WithLp.toLp 2 (g x) : EuclideanSpace ℂ (Fin N)) from rfl, norm_smul]
    rfl

theorem l1Seminorm_apply (g : T → Fin N → ℂ) : l1Seminorm g = ∑ x : T, vn (g x) := rfl

theorem continuous_l1Seminorm : Continuous (l1Seminorm : Seminorm ℂ (T → Fin N → ℂ)) := by
  show Continuous fun g : T → Fin N → ℂ => ∑ x : T, vn (g x)
  refine continuous_finsetSum _ fun x _ => ?_
  unfold vn
  fun_prop

variable [DecidableEq T]

/-- The unit source `δ_{x,i}`: `1` in the component `i` at the site `x`. -/
noncomputable def srcDelta (x : T) (i : Fin N) : T → Fin N → ℂ := Pi.single x (Pi.single i 1)

theorem l1Seminorm_srcDelta (x : T) (i : Fin N) : l1Seminorm (srcDelta x i) = 1 := by
  rw [l1Seminorm_apply, Finset.sum_eq_single x]
  · simp [srcDelta, vn]
  · intro y _ hy; simp [srcDelta, Pi.single_eq_of_ne hy, vn]
  · simp

omit [Fintype T] in
theorem srcDelta_apply_of_ne {x y : T} (i : Fin N) (h : y ≠ x) : srcDelta x i y = 0 := by
  simp [srcDelta, Pi.single_eq_of_ne h]

/-- The ball `{‖g‖₁ < 1}` on which the packages are analytic. -/
abbrev srcBall : Set (T → Fin N → ℂ) := seminormBall l1Seminorm

/-- A package `a(Y; ·)` depends on `g` only through `g|_Y`. -/
def LocalIn (Y : Set T) (a : (T → Fin N → ℂ) → ℂ) : Prop :=
  ∀ g g' : T → Fin N → ℂ, (∀ x ∈ Y, g x = g' x) → a g = a g'

section Locality

variable {Y : Set T} {a : (T → Fin N → ℂ) → ℂ}

theorem fderiv_srcDelta_eq_zero (hloc : LocalIn Y a) {g : T → Fin N → ℂ}
    (hg : DifferentiableAt ℂ a g) {x : T} (hx : x ∉ Y) (i : Fin N) :
    fderiv ℂ a g (srcDelta x i) = 0 := by
  have h1 := hasDerivAt_line (f := a) (c := g) (z := srcDelta x i) (τ := 0) (by simpa using hg)
  have hconst : (fun t : ℂ => a (g + t • srcDelta x i)) = fun _ => a g := by
    funext t
    refine hloc _ _ fun y hy => ?_
    have hyx : y ≠ x := fun h => hx (h ▸ hy)
    simp [srcDelta_apply_of_ne i hyx]
  rw [hconst] at h1
  simpa using h1.unique (hasDerivAt_const (0 : ℂ) (a g))

theorem D2_srcDelta_eq_zero_right (hloc : LocalIn Y a) (hp : AnalyticOnNhd ℂ a srcBall)
    (v : T → Fin N → ℂ) {x : T} (hx : x ∉ Y) (i : Fin N) :
    D2 a 0 v (srcDelta x i) = 0 := by
  have hopen := isOpen_seminormBall (continuous_l1Seminorm (T := T) (N := N))
  have h0 : (0 : T → Fin N → ℂ) ∈ srcBall (T := T) (N := N) := zero_mem_seminormBall _
  have hev : (fun g => fderiv ℂ a g (srcDelta x i)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    filter_upwards [hopen.mem_nhds h0] with g hg
    exact fderiv_srcDelta_eq_zero hloc (hp g hg).differentiableAt hx i
  have hfd : DifferentiableAt ℂ (fderiv ℂ a) 0 :=
    ((hp.fderiv_of_isOpen hopen) 0 h0).differentiableAt
  have h2 : HasFDerivAt (fun g => fderiv ℂ a g (srcDelta x i))
      ((ContinuousLinearMap.apply ℂ ℂ (srcDelta x i)).comp (fderiv ℂ (fderiv ℂ a) 0)) 0 :=
    (ContinuousLinearMap.apply ℂ ℂ (srcDelta x i)).hasFDerivAt.comp 0 hfd.hasFDerivAt
  have h3 : HasFDerivAt (fun g => fderiv ℂ a g (srcDelta x i)) (0 : (T → Fin N → ℂ) →L[ℂ] ℂ) 0 :=
    (hasFDerivAt_const (0 : ℂ) (0 : T → Fin N → ℂ)).congr_of_eventuallyEq hev
  have := congrArg (fun A => A v) (h2.unique h3)
  simpa [D2] using this

theorem D2_srcDelta_eq_zero_left (hloc : LocalIn Y a) (hp : AnalyticOnNhd ℂ a srcBall)
    (v : T → Fin N → ℂ) {x : T} (hx : x ∉ Y) (i : Fin N) :
    D2 a 0 (srcDelta x i) v = 0 := by
  rw [D2_symm (hp 0 (zero_mem_seminormBall _))]
  exact D2_srcDelta_eq_zero_right hloc hp v hx i

end Locality

section Bounds

variable {a : (T → Fin N → ℂ) → ℂ} {B : ℝ}

/-- **Lemma 3.2, first derivative**: `|∂_{g_i(x)} a(Y; 0)| ≤ B_Y`. -/
theorem norm_fderiv_srcDelta_le (hp : AnalyticOnNhd ℂ a srcBall)
    (hB : ∀ g ∈ srcBall (T := T) (N := N), ‖a g‖ ≤ B) (x : T) (i : Fin N) :
    ‖fderiv ℂ a 0 (srcDelta x i)‖ ≤ B :=
  norm_fderiv_zero_le continuous_l1Seminorm hp.differentiableOn hB
    (le_of_eq (l1Seminorm_srcDelta x i))

/-- **Lemma 3.2, first derivative, the document's constant**: `≤ 2 B_Y`. -/
theorem norm_fderiv_srcDelta_le_two (hp : AnalyticOnNhd ℂ a srcBall)
    (hB : ∀ g ∈ srcBall (T := T) (N := N), ‖a g‖ ≤ B) (x : T) (i : Fin N) :
    ‖fderiv ℂ a 0 (srcDelta x i)‖ ≤ 2 * B :=
  norm_fderiv_zero_le_two continuous_l1Seminorm hp.differentiableOn hB
    (le_of_eq (l1Seminorm_srcDelta x i))

/-- **Lemma 3.2, second derivative**: `|∂_{g_i(x)} ∂_{g_k(y)} a(Y; 0)| ≤ 4 B_Y` (all `x, y`,
including `x = y`; polarization). -/
theorem norm_D2_srcDelta_le (hp : AnalyticOnNhd ℂ a srcBall)
    (hB : ∀ g ∈ srcBall (T := T) (N := N), ‖a g‖ ≤ B) (x y : T) (i k : Fin N) :
    ‖D2 a 0 (srcDelta x i) (srcDelta y k)‖ ≤ 4 * B :=
  norm_D2_zero_le continuous_l1Seminorm hp hB (le_of_eq (l1Seminorm_srcDelta x i))
    (le_of_eq (l1Seminorm_srcDelta y k))

/-- **Lemma 3.2, second derivative, the document's constant**: `≤ 32 B_Y`. -/
theorem norm_D2_srcDelta_le_doc (hp : AnalyticOnNhd ℂ a srcBall)
    (hB : ∀ g ∈ srcBall (T := T) (N := N), ‖a g‖ ≤ B) (x y : T) (i k : Fin N) :
    ‖D2 a 0 (srcDelta x i) (srcDelta y k)‖ ≤ 32 * B :=
  norm_D2_zero_le_doc continuous_l1Seminorm hp hB (le_of_eq (l1Seminorm_srcDelta x i))
    (le_of_eq (l1Seminorm_srcDelta y k))

end Bounds

section Sums

variable {ι : Type*} (S : Finset ι) (Y : ι → Set T) (a : ι → (T → Fin N → ℂ) → ℂ)

open scoped Classical in
/-- The first `g`-derivative at `0` of a finite sum of packages picks the packages with `x ∈ Y`. -/
theorem fderiv_sum_srcDelta (hloc : ∀ s ∈ S, LocalIn (Y s) (a s))
    (hp : ∀ s ∈ S, AnalyticOnNhd ℂ (a s) srcBall) (x : T) (i : Fin N) :
    fderiv ℂ (fun g => ∑ s ∈ S, a s g) 0 (srcDelta x i) =
      ∑ s ∈ S with x ∈ Y s, fderiv ℂ (a s) 0 (srcDelta x i) := by
  have h0 : (0 : T → Fin N → ℂ) ∈ srcBall (T := T) (N := N) := zero_mem_seminormBall _
  have hd : ∀ s ∈ S, DifferentiableAt ℂ (a s) 0 := fun s hs =>
    (hp s hs 0 h0).differentiableAt
  rw [fderiv_fun_sum hd, _root_.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s hs => ?_
  split_ifs with hx
  · rfl
  · exact fderiv_srcDelta_eq_zero (hloc s hs) (hd s hs) hx i

open scoped Classical in
/-- The second `g`-derivative at `0` of a finite sum of packages picks the packages with
`x, y ∈ Y`. -/
theorem D2_sum_srcDelta (hloc : ∀ s ∈ S, LocalIn (Y s) (a s))
    (hp : ∀ s ∈ S, AnalyticOnNhd ℂ (a s) srcBall) (x y : T) (i k : Fin N) :
    D2 (fun g => ∑ s ∈ S, a s g) 0 (srcDelta x i) (srcDelta y k) =
      ∑ s ∈ S with x ∈ Y s ∧ y ∈ Y s, D2 (a s) 0 (srcDelta x i) (srcDelta y k) := by
  have hopen := isOpen_seminormBall (continuous_l1Seminorm (T := T) (N := N))
  have h0 : (0 : T → Fin N → ℂ) ∈ srcBall (T := T) (N := N) := zero_mem_seminormBall _
  have hev : (fun g => fderiv ℂ (fun g => ∑ s ∈ S, a s g) g) =ᶠ[𝓝 0]
      fun g => ∑ s ∈ S, fderiv ℂ (a s) g := by
    filter_upwards [hopen.mem_nhds h0] with g hg
    exact fderiv_fun_sum fun s hs => (hp s hs g hg).differentiableAt
  have hdd : ∀ s ∈ S, DifferentiableAt ℂ (fderiv ℂ (a s)) 0 := fun s hs =>
    ((hp s hs).fderiv_of_isOpen hopen 0 h0).differentiableAt
  unfold D2
  rw [(Filter.EventuallyEq.fderiv_eq hev), fderiv_fun_sum hdd, _root_.sum_apply, _root_.sum_apply,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun s hs => ?_
  split_ifs with hxy
  · rfl
  · by_cases hx : x ∈ Y s
    · have hy : y ∉ Y s := fun hy => hxy ⟨hx, hy⟩
      exact D2_srcDelta_eq_zero_right (hloc s hs) (hp s hs) _ hy k
    · exact D2_srcDelta_eq_zero_left (hloc s hs) (hp s hs) _ hx i

open scoped Classical in
/-- Bound of the first derivative of a sum of packages: `∑_{Y ∋ x} B_Y`. -/
theorem norm_fderiv_sum_srcDelta_le (B : ι → ℝ) (hloc : ∀ s ∈ S, LocalIn (Y s) (a s))
    (hp : ∀ s ∈ S, AnalyticOnNhd ℂ (a s) srcBall)
    (hB : ∀ s ∈ S, ∀ g ∈ srcBall (T := T) (N := N), ‖a s g‖ ≤ B s) (x : T) (i : Fin N) :
    ‖fderiv ℂ (fun g => ∑ s ∈ S, a s g) 0 (srcDelta x i)‖ ≤ ∑ s ∈ S with x ∈ Y s, B s := by
  rw [fderiv_sum_srcDelta S Y a hloc hp]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
  exact norm_fderiv_srcDelta_le (hp s (Finset.mem_filter.1 hs).1) (hB s (Finset.mem_filter.1 hs).1) x i

open scoped Classical in
/-- Bound of the second derivative of a sum of packages: `4 ∑_{Y ∋ x, y} B_Y`. -/
theorem norm_D2_sum_srcDelta_le (B : ι → ℝ) (hloc : ∀ s ∈ S, LocalIn (Y s) (a s))
    (hp : ∀ s ∈ S, AnalyticOnNhd ℂ (a s) srcBall)
    (hB : ∀ s ∈ S, ∀ g ∈ srcBall (T := T) (N := N), ‖a s g‖ ≤ B s) (x y : T) (i k : Fin N) :
    ‖D2 (fun g => ∑ s ∈ S, a s g) 0 (srcDelta x i) (srcDelta y k)‖ ≤
      4 * ∑ s ∈ S with x ∈ Y s ∧ y ∈ Y s, B s := by
  rw [D2_sum_srcDelta S Y a hloc hp, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
  exact norm_D2_srcDelta_le (hp s (Finset.mem_filter.1 hs).1) (hB s (Finset.mem_filter.1 hs).1)
    x y i k

end Sums

section Packages

variable {a : (T → Fin N → ℂ) → ℂ}

/-- The bounds on the `g`-derivatives of the packages `ℛ''^{(k)}_n(X; ·)` with
`|ℛ| ≤ β_k^{-n-1} e^{-κ d}`, `n ≥ 1`, `β_k ≥ 1` (OBSERVABLES §3.2, after Lemma 3.2):
`|M_ℛ(x, Y)| = |∂_g a| ≤ 2 β_k^{-2} e^{-κ d}`. -/
theorem norm_fderiv_pkg_le {β e : ℝ} (hβ : 1 ≤ β) (he : 0 ≤ e) {n : ℕ} (hn : 1 ≤ n)
    (hp : AnalyticOnNhd ℂ a srcBall)
    (hB : ∀ g ∈ srcBall (T := T) (N := N), ‖a g‖ ≤ (β ^ (n + 1))⁻¹ * e) (x : T) (i : Fin N) :
    ‖fderiv ℂ a 0 (srcDelta x i)‖ ≤ 2 * ((β ^ 2)⁻¹ * e) := by
  have h1 := norm_fderiv_srcDelta_le_two hp hB x i
  have h2 : (β ^ (n + 1))⁻¹ ≤ (β ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hβ (by omega))
  nlinarith [mul_le_mul_of_nonneg_right h2 he]

/-- `β_k |R_ℛ| = β_k |∂_g² a| ≤ 32 β_k^{-1} e^{-κ d}`. -/
theorem norm_D2_pkg_le {β e : ℝ} (hβ : 1 ≤ β) (he : 0 ≤ e) {n : ℕ} (hn : 1 ≤ n)
    (hp : AnalyticOnNhd ℂ a srcBall)
    (hB : ∀ g ∈ srcBall (T := T) (N := N), ‖a g‖ ≤ (β ^ (n + 1))⁻¹ * e) (x y : T)
    (i k : Fin N) :
    β * ‖D2 a 0 (srcDelta x i) (srcDelta y k)‖ ≤ 32 * (β⁻¹ * e) := by
  have h1 := norm_D2_srcDelta_le_doc hp hB x y i k
  have hβ0 : 0 < β := by linarith
  have h2 : (β ^ (n + 1))⁻¹ ≤ (β ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hβ (by omega))
  have h3 : β * (β ^ 2)⁻¹ = β⁻¹ := by field_simp
  calc β * ‖D2 a 0 (srcDelta x i) (srcDelta y k)‖ ≤ β * (32 * ((β ^ (n + 1))⁻¹ * e)) :=
        mul_le_mul_of_nonneg_left h1 hβ0.le
    _ ≤ β * (32 * ((β ^ 2)⁻¹ * e)) := by
        gcongr
    _ = 32 * (β⁻¹ * e) := by rw [← h3]; ring

end Packages

end Balaban.Observables
