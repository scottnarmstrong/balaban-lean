/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6Terms
public import Balaban.Localization.P6PairCover
public import Balaban.Localization.P6ActiveHalo
public import Balaban.Localization.MooreDegree
public import Balaban.Localization.LedgerPacking

/-!
# The full-torus top-only auxiliary cover `F^top` (VMOD-31 §1-§2, packages (i) and (iii))

On the cover torus with top scale `K`, let `F^top` be the generating set whose domains are the
whole torus `Ω_j = 𝕋` for `j ≤ K` and empty above.  This is the landed `levelGS K le_rfl` (the
whole-lattice generating set of level `K`); no parallel object is defined, `topGS` below is only
the reducible abbreviation `levelGS K le_rfl`.

Proved here, for the cover geometry only:

* `topGS_cubeAligned`, `topGS_supSep`: `F^top` is cube aligned and sup-separated (the separation
  clause quantifies over sites outside `Ω_j` with `1 ≤ j < K`, and there are none);
* `layer_eq_top_of_mem_cubeIdx`: every index of `cubeIdx F^top` has layer `K`, so every patch has
  side `M₁ L^K`;
* `topGS_precedes`: `Background.Precedes H F^top` for every generating set `H` on the same torus;
* `not_supSep_of_proper`: the refuted alternative.  A domain `T` that is a nonempty proper subset
  of the torus, used as `Ω_j` for all `1 ≤ j ≤ K` with `K ≥ 2`, is not sup-separated: the
  separation at `j = K - 1` asks for sup-distance `> 4 L^(K+m₁)` between a site outside `T` and a
  site of `T`, while an adjacent such pair has sup-distance `1`;
* `topGS_root_patch_count`: for EVERY top cell `U` (active or not), at most `3^d (L^m₀)^d` indices
  of `cubeIdx F^top` have a patch Moore-touching `U`; `topGS_degree_le`: the Moore graph of the
  patches has degree at most `3 (L+4)^d` when `d ≤ ϱ L²` (the separation parameter of `levelGS` is
  free).

**Not proved here.**  That the actual P6 interpolation coefficients vanish when a connected
component of the patch set misses the active cells and the source cover (`P6_COEF_ROOTED_XB` of
`notes/phase1/VMOD-31.md`); the H7 mixed transfer; the source-size bridge.  Using `F^top` in place
of the multiscale cover `F♯` is a choice of auxiliary cover, and its agreement with P6
(4.32)-(4.34) is being checked separately.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.LargeField Balaban.Multiscale Balaban.Multiscale.GeneratingSet
  Balaban.SmallField.Def6

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- `F^top`: the whole-torus generating set of level `K` on the cover torus (this is `levelGS`). -/
noncomputable abbrev topGS (d L N₁ m₁ K : ℕ) [NeZero L] [NeZero N₁] (ϱ : ℝ) :
    GeneratingSet d L (N₁ * L ^ m₁) K ϱ :=
  levelGS K le_rfl

theorem mem_topGS_Ω {j : ℕ} (hj : j ≤ K) (x : CTorus d L N₁ m₁ K) :
    x ∈ (topGS d L N₁ m₁ K ϱ).Ω j := by
  simp [topGS, levelGS, hj]

theorem not_mem_topGS_Ω {j : ℕ} (hj : K < j) (x : CTorus d L N₁ m₁ K) :
    x ∉ (topGS d L N₁ m₁ K ϱ).Ω j := by
  simp [topGS, levelGS, show ¬ j ≤ K by omega]

/-- **T1.** `F^top` is cube aligned (`2 ≤ m₁`). -/
theorem topGS_cubeAligned (hm : 2 ≤ m₁) : CubeAligned (topGS d L N₁ m₁ K ϱ) m₁ where
  two_le := hm
  dvd := dvd_mul_left _ _
  union j _ hj x x' _ := by
    simp only [mem_topGS_Ω hj x, mem_topGS_Ω hj x']

/-- **T1.** `F^top` is sup-separated: no site lies outside `Ω_j` for `1 ≤ j < K`. -/
theorem topGS_supSep : SupSep (topGS d L N₁ m₁ K ϱ) m₁ := by
  intro j _ hjK x hx
  exact absurd (mem_topGS_Ω hjK.le x) hx

/-- **T1.** Every index of `cubeIdx F^top` has layer `K`: all patches have side `M₁ L^K`. -/
theorem layer_eq_top_of_mem_cubeIdx {P : ℕ × CTorus d L N₁ m₁ K}
    (hP : P ∈ cubeIdx (topGS d L N₁ m₁ K ϱ)) : P.1 = K := by
  obtain ⟨⟨_, hK⟩, hl, -⟩ := (mem_cubeIdx _).1 hP
  by_contra h
  exact ((topGS d L N₁ m₁ K ϱ).mem_layer.1 hl).2 (mem_topGS_Ω (by omega) _)

/-- **T2.** Every generating set `H` on the same torus precedes `F^top` (inclusion in the whole
torus). -/
theorem topGS_precedes {ϱ' : ℝ} (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ') :
    Background.Precedes H (topGS d L N₁ m₁ K ϱ) :=
  fun _ _ hi _ _ => mem_topGS_Ω hi _

/-! ### T3: why the whole torus -/

/-- **T3 (the refuted alternative).**  Let `F` have `Ω_j = T` for all `1 ≤ j ≤ K`, with `K ≥ 2` and
`T` a nonempty proper subset of the torus.  Then `F` is not sup-separated: the torus is connected,
so some site `x ∉ T` is at sup-distance `1` from a site `y ∈ T`, whereas the separation at
`j = K - 1` demands sup-distance `> 4 L^(K+m₁)` between them. -/
theorem not_supSep_of_proper (F : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (T : Finset (CTorus d L N₁ m₁ K)) (hK : 2 ≤ K) (hF : ∀ j, 1 ≤ j → j ≤ K → F.Ω j = T)
    (hne : T.Nonempty) (hpr : T ≠ Finset.univ) : ¬ SupSep F m₁ := by
  intro hSS
  have hsep : ∀ x, x ∉ T → ∀ y ∈ T, 1 < supDist x y := by
    intro x hx y hy
    have h := hSS (K - 1) (by omega) (by omega) x (by rw [hF _ (by omega) (by omega)]; exact hx) y
      (by rw [show K - 1 + 1 = K by omega, hF K (by omega) le_rfl]; exact hy)
    have h1 : (1 : ℝ) ≤ 4 * (L : ℝ) ^ (K - 1 + 1 + m₁) := by
      have : (1 : ℝ) ≤ (L : ℝ) ^ (K - 1 + 1 + m₁) :=
        one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
      linarith
    exact_mod_cast lt_of_le_of_lt h1 h
  obtain ⟨y0, hy0⟩ := hne
  have hstep : ∀ z ∈ T, ∀ μ : Fin d, z + Pi.single μ 1 ∈ T := by
    intro z hz μ
    by_contra hn
    have := hsep _ hn z hz
    have h2 := supDist_sub_single_le (z + Pi.single μ 1) μ
    simp only [add_sub_cancel_right] at h2
    omega
  have hnat : ∀ μ : Fin d, ∀ n : ℕ, ∀ v ∈ T, v + Pi.single μ (n : ZMod _) ∈ T := by
    intro μ n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      have := hstep _ (ih v hv) μ
      convert this using 1
      rw [add_assoc, ← Pi.single_add]
      push_cast; rfl
  have hall : ∀ s : Finset (Fin d), ∀ w : CTorus d L N₁ m₁ K, (∀ μ, μ ∉ s → w μ = y0 μ) → w ∈ T := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro w hw; convert hy0 using 1; funext μ; exact hw μ (by simp)
    | insert a s ha ih =>
      intro w hw
      have hw' : Function.update w a (y0 a) ∈ T := by
        refine ih _ fun μ hμ => ?_
        by_cases h : μ = a
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hw μ (by simp [h, hμ])
      have := hnat a (w a - y0 a).val _ hw'
      convert this using 1
      funext μ
      by_cases h : μ = a
      · subst h; simp
      · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
  exact hpr (Finset.eq_univ_iff_forall.2 fun w => hall Finset.univ w fun μ hμ => absurd (Finset.mem_univ μ) hμ)

/-! ### T5: incidence counts for every top cell -/

open Classical in
/-- **T5.** For EVERY top cell `U` (no hypothesis that it is active or near an old region), at most
`3^d (L^m₀)^d` indices of `cubeIdx F^top` have a patch Moore-touching `U` (`L^m₀ ∣ N₁`). -/
theorem topGS_root_patch_count {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (u : CTorus d L N₁ m₁ K) :
    ((cubeIdx (topGS d L N₁ m₁ K ϱ)).filter
        fun P => MooreTouch (topCell m₀ (K, u)) (Pset m₁ P)).card ≤ 3 ^ d * (L ^ m₀) ^ d :=
  root_patch_count _ hN u fun _ _ _ _ => mem_topGS_Ω le_rfl _

open Classical in
/-- **T5.** Degree of the Moore graph of the patches of `F^top`, `≤ 3 (L+4)^d` whenever
`d ≤ ϱ L²`. -/
theorem topGS_degree_le (hm : 2 ≤ m₁) (hϱ : (d : ℝ) ≤ ϱ * (L : ℝ) ^ 2)
    (P : {P // P ∈ cubeIdx (topGS d L N₁ m₁ K ϱ)}) :
    (mooreGraph (topGS d L N₁ m₁ K ϱ)).degree P ≤ 3 * (L + 4) ^ d :=
  mooreGraph_degree_le (topGS_cubeAligned hm) hϱ P

end Balaban.Localization
