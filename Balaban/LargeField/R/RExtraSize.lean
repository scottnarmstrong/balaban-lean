/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoarseFineComponents
public import Balaban.LargeField.R.RRawHoleComponent
public import Balaban.LargeField.R.RRipeCard
public import Balaban.LargeField.R.SizeModExtendPull
public import Balaban.LargeField.Def7FineSize
public import Balaban.LargeField.Def7Hist
import Mathlib.Tactic.Linarith

/-!
# The size of a boundary domain grows by a bounded amount per removed cube (VMOD-38, package 4)

The large-field renormalization `R^{(k)}` removes the ripe components `H.rem k` of the scale-`k`
large-field region.  For a finite label `X` of cubes of `𝕋_k`, `d7SizePre F A k X` measures the
fine chosen-cover size of `X` against the raw region `Ω_k^pre` and `d7Size F A k X` against the
post region `Ω_k^post = Ω_k^pre ∪ ⋃ Rem_k`.  With `d = S.d`, `L = S.L` and `A_X = X ∩ (⋃ Rem_k ∖
Ω_k^pre)` the cubes of `X` that become active (`RegionHistory.newlyActive`):

* `hsplit_omegaPost`: every cell-component of the fine lift of `X ∩ (Ω_k^pre)ᶜ` lies in the fine
  lift of `Ω_k^post` or misses it (coarse components of the raw hole meeting a removed component lie
  inside it, `rawHole_nnConnected_subset_comp`; `cellComps_d7Pull` converts fine cell-components to
  coarse nearest-neighbour components);
* `d7Size_le_d7SizePre_add` (**★**): `d7Size ≤ d7SizePre + (d L + d + 3) · |A_X|`, for `1 ≤ k ≤ K`
  and a label whose fine lift is a connected union of `π'_k`-cubes (`IsDj`; this holds for every
  `FineValid` label, `d7Size_le_d7SizePre_add_of_fineValid`);
* `d7Size_eq_d7SizePre_of_no_removal`: for `k = 0` or `k₀ < k` the two sizes coincide, and
  `d7SizePre_le_d7Size_le` is the two-sided statement;
* `newlyActive_card_le`, `d7Size_le_d7SizePre_add_removed` (**★★**): under admissibility, `Good`
  and the thickness condition, `|A_X| ≤ (number of removed components meeting X) · (2ρ_k + 10)^d`,
  so `d7Size ≤ d7SizePre + (d L + d + 3) · N · (2ρ_k + 10)^d`, `N = |remMeeting H X|`.

**How the inequality is to be used (`notes/phase1/VMOD-40.md` §1-§2).**  It is *not* a per-term
multiplier for old boundary coefficients (that use is refuted there); it is an input to the reserve
ledger of the removed-component gas, where the increment `(d L + d + 3) |c|` per used removed
component `c` is paid by the reserve of `c`.

**NOT proved here.**  The analytic charge for `R` (the gas estimate, the reserve ledger,
`OPEN-R-D7-CHARGE`) and the post-`R` boundary record are not proved here; this file is finite
geometry on the cover size only.  The constant `d L + d + 3` is the landed statement of
`Fluctuation.dcovMod_le_add_of_region_grow`, whose proof gives `d L + 1`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Localization Def7

section Split

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M m₀ m₁ : ℕ}
  [NeZero S.L] (H : RegionHistory S n R k0 K) (F : FineSizeFrame S n M K m₀ m₁)

omit [NeZero S.L] in
/-- The tower condition `n_i = L n_{i+1}` of a region history. -/
theorem RegionHistory.tower (H : RegionHistory S n R k0 K) :
    ∀ i, i < K → n i = S.L * n (i + 1) := fun _ hi => (H.stepGeom hi).hn

/-- **The component hypothesis for `R`.**  For `1 ≤ k ≤ K` and a finite label `X`, every
cell-component of the fine lift of `X ∩ (Ω_k^pre)ᶜ` lies in the fine lift of `Ω_k^post` or is
disjoint from it. -/
theorem hsplit_omegaPost {k : ℕ} (hk : 1 ≤ k) (hkK : k ≤ K) (X : Finset (Torus S.d (n k))) :
    ∀ Q ∈ Fluctuation.cellComps m₀ k
        (d7Pull F k (X : Set (Torus S.d (n k))) ∩ (d7Pull F k (OmegaCube H k))ᶜ),
      Q ⊆ d7Pull F k (H.omegaPost k) ∨ Disjoint Q (d7Pull F k (H.omegaPost k)) := by
  intro Q hQ
  rw [← d7Pull_compl, ← d7Pull_inter] at hQ
  obtain ⟨Q₀, hQ₀, hconn, rfl⟩ :=
    cellComps_d7Pull F (RegionHistory.tower H) hkK _ hQ
  by_cases hmeet : ∃ c ∈ H.rem k, (Q₀ ∩ (c : Set (Torus S.d (n k)))).Nonempty
  · obtain ⟨c, hc, hne⟩ := hmeet
    refine Or.inl (d7Pull_mono F k fun y hy => ?_)
    exact H.removedSet_subset_omegaPost k
      (H.mem_removedSet_iff.2 ⟨c, hc, H.rawHole_nnConnected_subset_comp hk X hc hQ₀ hconn hne hy⟩)
  · refine Or.inr (Set.disjoint_left.2 fun x hx hx' => ?_)
    rw [d7Pull_iff] at hx hx'
    rcases hx' with hO | hR
    · exact (hQ₀ hx).2 hO
    · obtain ⟨c, hc, hxc⟩ := H.mem_removedSet_iff.1 hR
      exact hmeet ⟨c, hc, _, hx, hxc⟩

end Split

section Size

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M m₀ m₁ : ℕ}
  [NeZero S.L] (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K)

/-- **Cover-size increment at the level of `dcovMod`** (★ for the region history). -/
theorem dcovMod_omegaPost_le {k : ℕ} (hk : 1 ≤ k) (hkK : k ≤ K) (X : Finset (Torus S.d (n k)))
    (hX : Fluctuation.IsDj m₀ k (d7Pull F k (X : Set (Torus S.d (n k))))) :
    Fluctuation.dcovMod m₀ k (d7Pull F k (A.H.omegaPost k)) (d7Pull F k (X : Set (Torus S.d (n k)))) ≤
      Fluctuation.dcovMod m₀ k (d7Pull F k (OmegaCube A.H k))
          (d7Pull F k (X : Set (Torus S.d (n k)))) +
        ((S.d : ℝ) * S.L + S.d + 3) * ((A.H.newlyActive X).card : ℝ) := by
  have h := dcovMod_d7Pull_le_add F (RegionHistory.tower A.H) hkK hX (hsplit_omegaPost A.H F hk hkK X)
  have hset : d7Pull F k (X : Set (Torus S.d (n k))) ∩
      (d7Pull F k (A.H.omegaPost k) \ d7Pull F k (OmegaCube A.H k)) =
      d7Pull F k ((A.H.newlyActive X : Finset (Torus S.d (n k))) : Set (Torus S.d (n k))) := by
    rw [A.H.coe_newlyActive_eq]; rfl
  rw [hset, card_cellsIn_d7Pull F (RegionHistory.tower A.H) hkK] at h
  exact h

/-- **(★) The size after `R` exceeds the size before `R` by at most `(d L + d + 3)` per newly
active cube.**  For `1 ≤ k ≤ K` and a label `X` whose fine lift is in `𝒟_k` (a nonempty connected
union of `π'_k`-cubes),
`d7Size F A k X ≤ d7SizePre F A k X + (d L + d + 3) · |X ∩ (⋃ Rem_k ∖ Ω_k^pre)|`. -/
theorem d7Size_le_d7SizePre_add {k : ℕ} (hk : 1 ≤ k) (hkK : k ≤ K)
    {X : Finset (Torus S.d (n k))}
    (hX : Fluctuation.IsDj m₀ k (d7Pull F k (X : Set (Torus S.d (n k))))) :
    d7Size F A k X ≤ d7SizePre F A k X +
      ((S.d : ℝ) * S.L + S.d + 3) * ((A.H.newlyActive X).card : ℝ) :=
  dcovMod_omegaPost_le F A hk hkK X hX

/-- (★) for every `FineValid` label. -/
theorem d7Size_le_d7SizePre_add_of_fineValid {k : ℕ} (hk : 1 ≤ k) (hkK : k ≤ K)
    {X : Finset (Torus S.d (n k))} (hv : FineValid F A k X) :
    d7Size F A k X ≤ d7SizePre F A k X +
      ((S.d : ℝ) * S.L + S.d + 3) * ((A.H.newlyActive X).card : ℝ) :=
  d7Size_le_d7SizePre_add F A hk hkK hv.1.1

omit [NeZero S.L] in
/-- For `k = 0` or `k₀ < k` nothing is removed and the two sizes coincide. -/
theorem d7Size_eq_d7SizePre_of_no_removal {k : ℕ} (hk : k = 0 ∨ k0 < k)
    (X : Finset (Torus S.d (n k))) : d7Size F A k X = d7SizePre F A k X :=
  d7Size_eq_d7SizePre_of_rem_empty F X (A.H.rem_empty k hk)

/-- **The two-sided statement**: for a label of finite size after `R` (e.g. a `FineValid` label)
with `1 ≤ k ≤ K` and `IsDj` fine lift, `d7SizePre ≤ d7Size ≤ d7SizePre + (d L + d + 3) |A_X|`. -/
theorem d7SizePre_le_d7Size_le {k : ℕ} (hk : 1 ≤ k) (hkK : k ≤ K) {X : Finset (Torus S.d (n k))}
    (hfin : d7SizeE F A k X ≠ ⊤)
    (hX : Fluctuation.IsDj m₀ k (d7Pull F k (X : Set (Torus S.d (n k))))) :
    d7SizePre F A k X ≤ d7Size F A k X ∧
      d7Size F A k X ≤ d7SizePre F A k X +
        ((S.d : ℝ) * S.L + S.d + 3) * ((A.H.newlyActive X).card : ℝ) :=
  ⟨d7SizePre_le_d7Size hfin, d7Size_le_d7SizePre_add F A hk hkK hX⟩

end Size

section Removed

open Classical in
/-- The removed components of scale `k` that meet the label `X`. -/
noncomputable def RegionHistory.remMeeting {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    {R : ℕ → ℝ} {k0 K : ℕ} (H : RegionHistory S n R k0 K) {k : ℕ}
    (X : Finset (Torus S.d (n k))) : Finset (Finset (Torus S.d (n k))) :=
  (H.rem k).filter fun c => ∃ x ∈ c, x ∈ X

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M m₀ m₁ : ℕ}
  [NeZero S.L] (H : RegionHistory S n R k0 K)

omit [NeZero S.L] in
theorem RegionHistory.mem_remMeeting {k : ℕ} {X : Finset (Torus S.d (n k))}
    {c : Finset (Torus S.d (n k))} :
    c ∈ H.remMeeting X ↔ c ∈ H.rem k ∧ ∃ x ∈ c, x ∈ X := by
  classical
  simp [RegionHistory.remMeeting]

omit [NeZero S.L] in
/-- **The newly active cubes are covered by the removed components meeting `X`**:
`|A_X| ≤ Σ_{c ∈ Rem_k, c ∩ X ≠ ∅} |c|`, and each removed component has at most `(2ρ_k + 10)^d`
cubes. -/
theorem newlyActive_card_le (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hadm : H.Admissible) {k : ℕ}
    (hkK : k ≤ K) (X : Finset (Torus S.d (n k))) :
    (H.newlyActive X).card ≤ ∑ c ∈ H.remMeeting X, c.card ∧
      (H.newlyActive X).card ≤ (H.remMeeting X).card * (2 * S.rho k + 10) ^ S.d := by
  classical
  have h1 : (H.newlyActive X).card ≤ ∑ c ∈ H.remMeeting X, c.card := by
    refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
    intro x hx
    obtain ⟨hxX, hxR, -⟩ := H.mem_newlyActive.1 hx
    obtain ⟨c, hc, hxc⟩ := H.mem_removedSet_iff.1 hxR
    exact Finset.mem_biUnion.2 ⟨c, H.mem_remMeeting.2 ⟨hc, x, hxc, hxX⟩, hxc⟩
  refine ⟨h1, h1.trans ?_⟩
  calc ∑ c ∈ H.remMeeting X, c.card ≤ ∑ _c ∈ H.remMeeting X, (2 * S.rho k + 10) ^ S.d := by
        refine Finset.sum_le_sum fun c hc => ?_
        have hcr := (H.mem_remMeeting.1 hc).1
        exact RegionHistory.removed_card_le G hT hadm hkK (c := ⟨c, H.rem_sub k hcr⟩) hcr
    _ = (H.remMeeting X).card * (2 * S.rho k + 10) ^ S.d := by simp

end Removed

section Final

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M m₀ m₁ : ℕ}
  [NeZero S.L] (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K)

/-- **(★★) The increment in terms of removed components.**  Under `Good` and the thickness
condition, for `1 ≤ k ≤ K` and an `IsDj` label `X`,
`d7Size ≤ d7SizePre + (d L + d + 3) · N · (2ρ_k + 10)^d`, `N` the number of removed components
that meet `X`. -/
theorem d7Size_le_d7SizePre_add_removed (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) {k : ℕ} (hk : 1 ≤ k) (hkK : k ≤ K)
    {X : Finset (Torus S.d (n k))}
    (hX : Fluctuation.IsDj m₀ k (d7Pull F k (X : Set (Torus S.d (n k))))) :
    d7Size F A k X ≤ d7SizePre F A k X +
      ((S.d : ℝ) * S.L + S.d + 3) *
        (((A.H.remMeeting X).card : ℝ) * ((2 * S.rho k + 10 : ℕ) ^ S.d : ℕ)) := by
  have h1 := d7Size_le_d7SizePre_add F A hk hkK hX
  have h2 := (newlyActive_card_le A.H G hT A.adm hkK X).2
  have h3 : ((A.H.newlyActive X).card : ℝ) ≤
      ((A.H.remMeeting X).card : ℝ) * (((2 * S.rho k + 10 : ℕ) ^ S.d : ℕ) : ℝ) := by
    exact_mod_cast h2
  have hc : (0 : ℝ) ≤ (S.d : ℝ) * S.L + S.d + 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 hc]

end Final

end Balaban.LargeField
