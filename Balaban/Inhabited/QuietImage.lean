/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.QuietLocalIso
public import Balaban.LargeField.Operators.QuietLocalInput
public import Balaban.LargeField.Region.SymmLoc
public import Balaban.LargeField.History.ImageHistBook


/-!
# Quiet realizability is closed under lattice symmetries

For a lattice symmetry `σ : LatTorusSym` and an admissible region history `H` on tori that are
points above the horizon (`n j = 1` for `j ≥ K`), with `k₀ ≤ K`, the image history `imgHist σ H`
(`History/ImageHist.lean`; admissible by `admissible_imgHist_iff`, `History/ImageHistBook.lean`)
realizes the `σ`-image of every quiet realizable localized history.  Consequently the quiet
realizable localized histories are closed under `HistImage` (`quietRealized_iff_of_histImage`):
this is the field `real_euclid` of `QuietStepInput'`, for every `k₀ ≤ K`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban RegionHistory

section Hist

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] (σ : LatTorusSym S n M K) (H : RegionHistory S n R k0 K)
  (hsub : ∀ j, K ≤ j → n j = 1)


local notation "Hi" => imgHist σ H hsub
local notation "ci" => imgComp σ H hsub

theorem isQuiet_img {k : ℕ} (hk : k + 1 ≤ K) (Z : H.Comp (k + 1))
    (hq : IsQuiet (H.locRH (k + 1) Z) k Z.1) :
    IsQuiet ((Hi).locRH (k + 1) (ci Z)) k (ci Z).1 := by
  have hiso : RegionIso σ (H.locRH (k + 1) Z) ((Hi).locRH (k + 1) (ci Z)) :=
    ⟨fun j _ => (locStep_corr σ H hsub Z j).1,
      fun j _ => (locStep_corr σ H hsub Z j).2.1,
      fun j _ => (locStep_corr σ H hsub Z j).2.2.1,
      fun j _ => (locStep_corr σ H hsub Z j).2.2.2.1,
      fun j _ => (locStep_corr σ H hsub Z j).2.2.2.2⟩
  exact isQuiet_of_regionIso σ hiso hk (imgComp_coe σ H hsub Z) hq

end Hist

section Realized

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] (σ : LatTorusSym S n M K) (hsub : ∀ j, K ≤ j → n j = 1) (hk0 : k0 ≤ K)

include hsub hk0 in
/-- Quiet realizability is stable under lattice symmetries (for `k₀ ≤ K` and tori that are points
above the horizon). -/
theorem QuietRealized.image {k : ℕ} {a : LocalHistory S n M K} (h : QuietRealized R k0 k a) :
    ∃ a', QuietRealized R k0 k a' ∧ HistImage σ.toTorusSym a a' := by
  obtain ⟨H, hadm, Z', hk1, hkK, hq, rfl⟩ := h
  exact ⟨_, ⟨imgHist σ H hsub, (admissible_imgHist_iff σ H hsub hk0).mpr hadm, imgComp σ H hsub Z',
    hk1, hkK, isQuiet_img σ H hsub hkK Z' hq, rfl⟩, histImage_loc σ H hsub Z'⟩


/-- `b` is the image of the localized history `a` under the permutation `g` of the fine torus. -/
def LocalHistory.ImgBy (g : Equiv.Perm (Torus S.d (M * n K * S.L ^ K)))
    (a b : LocalHistory S n M K) : Prop :=
  (∀ j, b.Z j = g '' a.Z j) ∧ (∀ j, b.P j = g '' a.P j) ∧ (∀ j, b.Q j = g '' a.Q j) ∧
  (∀ j, b.R j = g '' a.R j) ∧ (∀ j, b.Sset j = g '' a.Sset j) ∧
  (∀ j, b.OmegaPrime j = g '' a.OmegaPrime j) ∧ (∀ j, b.Omega j = g '' a.Omega j) ∧
  (∀ j, b.OmegaDD j = g '' a.OmegaDD j)

variable {σ} {a b c : LocalHistory S n M K}

theorem LocalHistory.ImgBy.of_histImage (h : HistImage σ.toTorusSym a b) :
    LocalHistory.ImgBy σ.ef a b :=
  ⟨h.Z, h.P, h.Q, h.R, h.Sset, h.OmegaPrime, h.Omega, h.OmegaDD⟩

theorem LocalHistory.ImgBy.toHistImage (h : LocalHistory.ImgBy σ.ef a b) :
    HistImage σ.toTorusSym a b :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem LocalHistory.ImgBy.comp {g g' : Equiv.Perm (Torus S.d (M * n K * S.L ^ K))}
    (h : LocalHistory.ImgBy g a b) (h' : LocalHistory.ImgBy g' b c) :
    LocalHistory.ImgBy (g' * g) a c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := h'
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_,
    fun j => ?_, fun j => ?_⟩
  · rw [k1, h1, Set.image_image]; rfl
  · rw [k2, h2, Set.image_image]; rfl
  · rw [k3, h3, Set.image_image]; rfl
  · rw [k4, h4, Set.image_image]; rfl
  · rw [k5, h5, Set.image_image]; rfl
  · rw [k6, h6, Set.image_image]; rfl
  · rw [k7, h7, Set.image_image]; rfl
  · rw [k8, h8, Set.image_image]; rfl

theorem LocalHistory.ext' {b c : LocalHistory S n M K} (h1 : b.Z = c.Z) (h2 : b.P = c.P)
    (h3 : b.Q = c.Q) (h4 : b.R = c.R) (h5 : b.Sset = c.Sset) (h6 : b.OmegaPrime = c.OmegaPrime)
    (h7 : b.Omega = c.Omega) (h8 : b.OmegaDD = c.OmegaDD) : b = c := by
  cases b; cases c
  simp only [LocalHistory.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem LocalHistory.ImgBy.unique {g : Equiv.Perm (Torus S.d (M * n K * S.L ^ K))}
    (h : LocalHistory.ImgBy g a b) (h' : LocalHistory.ImgBy g a c) : b = c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := h'
  exact LocalHistory.ext' (funext fun j => by rw [h1 j, k1 j]) (funext fun j => by rw [h2 j, k2 j])
    (funext fun j => by rw [h3 j, k3 j]) (funext fun j => by rw [h4 j, k4 j])
    (funext fun j => by rw [h5 j, k5 j]) (funext fun j => by rw [h6 j, k6 j])
    (funext fun j => by rw [h7 j, k7 j]) (funext fun j => by rw [h8 j, k8 j])

theorem LocalHistory.ImgBy.one (h : LocalHistory.ImgBy (1 : Equiv.Perm (Torus S.d (M * n K * S.L ^ K))) a b) : b = a := by
  have h' : LocalHistory.ImgBy (1 : Equiv.Perm (Torus S.d (M * n K * S.L ^ K))) a a := by
    refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_,
      fun j => ?_, fun j => ?_⟩ <;> simp
  exact h.unique h'

include hsub hk0 in
/-- **Closure of quiet realizability under lattice symmetries** (`real_euclid`). -/
theorem quietRealized_iff_of_histImage {k : ℕ} (hI : HistImage σ.toTorusSym a b) :
    QuietRealized R k0 k a ↔ QuietRealized R k0 k b := by
  constructor
  · intro h
    obtain ⟨a'', hr, hI''⟩ := QuietRealized.image σ hsub hk0 h
    rwa [(LocalHistory.ImgBy.of_histImage hI).unique (LocalHistory.ImgBy.of_histImage hI'')]
  · intro h
    have hfin : Finite (Torus S.d (M * n K * S.L ^ K)) := inferInstance
    obtain ⟨m, hm, hfm⟩ := (isOfFinOrder_of_finite σ.ef).exists_pow_eq_one
    have key : ∀ i : ℕ, ∃ b', QuietRealized R k0 k b' ∧ LocalHistory.ImgBy (σ.ef ^ i) b b' := by
      intro i
      induction i with
      | zero =>
        refine ⟨b, h, ?_⟩
        refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_,
          fun j => ?_, fun j => ?_⟩ <;> simp
      | succ i ih =>
        obtain ⟨b', hr, hb'⟩ := ih
        obtain ⟨b'', hr'', hI''⟩ := QuietRealized.image σ hsub hk0 hr
        refine ⟨b'', hr'', ?_⟩
        rw [pow_succ']
        exact hb'.comp (LocalHistory.ImgBy.of_histImage hI'')
    obtain ⟨b', hr, hb'⟩ := key (m - 1)
    have hcomp := (LocalHistory.ImgBy.of_histImage hI).comp hb'
    rw [← pow_succ, Nat.sub_add_cancel hm, hfm] at hcomp
    rwa [← LocalHistory.ImgBy.one (S := S) (n := n) (M := M) (K := K) hcomp]

end Realized

end Balaban.LargeField
