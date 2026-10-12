module

public import Balaban.LargeField.History.Floor

/-!
# Lemma I.4.13 (b): the covers of the lineage of an `Active` or `Pending` component

For `Z` of scale `k ≤ k₀`, `Active` or `Pending` with core `q`, and `q ≤ j ≤ k`, the lineage
`Lin_j(Z)` (`lin j k Z`) is covered by `ν(Z)` boxes of side `≤ crit_j`; more precisely
`ν(Z) = ∑_{Y ∈ Anc_j(Z)} ν(Y)` for the post-`R` ancestors at `j < k` (`nu_sum`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

theorem CoveredBy.biUnion {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {k : ℕ} {ι : Type*}
    (I : Finset ι) (c : ι → Finset (Torus S.d (n k))) (N : ι → ℕ)
    (h : ∀ i ∈ I, CoveredBy S n k (c i) (N i)) :
    CoveredBy S n k (I.biUnion c) (∑ i ∈ I, N i) := by
  classical
  choose! B hB1 hB2 hB3 using h
  refine ⟨I.biUnion B, ?_, ?_, ?_⟩
  · exact (Finset.card_biUnion_le).trans (Finset.sum_le_sum hB1)
  · intro b hb
    obtain ⟨i, hi, hbi⟩ := Finset.mem_biUnion.mp hb
    exact hB2 i hi b hbi
  · intro y hy
    obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hy)
    have := hB3 i hi (Finset.mem_coe.mpr hyi)
    obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.mp this
    exact Set.mem_iUnion₂.mpr ⟨b, Finset.mem_biUnion.mpr ⟨i, hi, hb⟩, hyb⟩

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K}

section Cover

variable (G : S.Good)

include G

/-- The number of pieces adds up over the ancestors at scale `j` of a component whose steps in
`(j, s]` are live and whose ancestors in `(j, s]` are not ripe. -/
theorem nu_sum {j : ℕ} {s : ℕ} (hjs : j < s) (hs : s ≤ k0) (hsK : s ≤ K)
    (W : H.Comp s)
    (hLive : ∀ s' (Y' : H.Comp s'), j < s' → s' ≤ s → H.Desc s' s Y' W → LiveAt s' Y')
    (hNR : ∀ s' (Y' : H.Comp s'), j < s' → s' < s → H.Desc s' s Y' W → ¬ S.Ripe s' (H.bk s' Y')) :
    (H.bk s W).nu = ∑ Y ∈ H.ancFin j s W, (H.pb j Y).nu := by
  classical
  induction s, hjs using Nat.le_induction with
  | base =>
    have hL : H.Live j W := hLive (j + 1) W (by omega) le_rfl (Desc.refl W)
    rw [Live.nu_eq G hs hsK hL, ancFin_succ le_rfl, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [ancFin_self, Finset.sum_singleton]
    · intro c _ c' _ hne
      exact ancFin_disjoint hne
  | succ s hjs ih =>
    have hL : H.Live s W := hLive (s + 1) W (by omega) le_rfl (Desc.refl W)
    rw [Live.nu_eq G hs hsK hL, ancFin_succ (by omega), Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun c hc => ?_
      have hcd : H.Desc s (s + 1) c W := by
        obtain ⟨hrem, hsu⟩ := (H.mem_parts s c W).mp hc
        exact Desc.single hrem hsu
      have hnr : ¬ S.Ripe s (H.bk s c) := hNR s c (by omega) (by omega) hcd
      have e1 : (H.pb s c).nu = (H.bk s c).nu := by
        show (S.postBook k0 s (H.bk s c)).nu = _
        rw [S.postBook_of_not_ripe hnr]
      rw [e1]
      refine ih (by omega) (by omega) c ?_ ?_
      · intro s' Y' h1 h2 hd
        exact hLive s' Y' h1 (by omega) (hd.trans hcd)
      · intro s' Y' h1 h2 hd
        exact hNR s' Y' h1 (by omega) (hd.trans hcd)
    · intro c _ c' _ hne
      exact ancFin_disjoint hne

variable {k : ℕ} {Z : H.Comp k}

/-- **Lemma I.4.13 (b)**: for `q ≤ j < k`, the lineage `Lin_j(Z)` is covered by `ν(Z)` boxes of
side `≤ crit_j`, and `ν(Z) = ∑_{Y ∈ Anc_j(Z)} ν(Y)`. -/
theorem nu_sum_window (hk0 : k ≤ k0) (hkK : k ≤ K) (hZ : (H.bk k Z).IsActive ∨ (H.bk k Z).IsPending) {j : ℕ}
    (hqj : (H.bk k Z).q ≤ j) (hjk : j < k) :
    (H.bk k Z).nu = ∑ Y ∈ H.ancFin j k Z, (H.pb j Y).nu := by
  refine nu_sum G hjk hk0 hkK Z ?_ ?_
  · intro s' Y' h1 h2 hd
    exact live_of_desc G hk0 hkK hZ hd (by omega)
  · intro s' Y' h1 h2 hd
    exact not_ripe_of_desc G hk0 hkK hZ hd (by omega) h2

/-- **Lemma I.4.13 (b)**, the cover: `Lin_j(Z)` is covered by `ν(Z)` boxes of side `≤ crit_j`
for `q ≤ j ≤ k`. -/
theorem cover_window (hT : ∀ k, 1 ≤ k → k ≤ k0 → 4 * S.rho k + 21 ≤ n k) (hk0 : k ≤ k0)
    (hkK : k ≤ K) (hZ : (H.bk k Z).IsActive ∨ (H.bk k Z).IsPending) {j : ℕ} (hqj : (H.bk k Z).q ≤ j)
    (hjk : j ≤ k) : CoveredBy S n j (H.lin j k Z) (H.bk k Z).nu := by
  have hk1 : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    subst this
    exact (H.F.isEmpty_comp_zero.false Z).elim
  rcases Nat.eq_or_lt_of_le hjk with heq | hlt
  · subst heq
    have hl : H.lin j j Z = Z.1 := by
      unfold lin; rw [ancFin_self, Finset.singleton_biUnion]
    rw [hl]
    exact H.cover_inv G hT j hk1 hk0 hkK Z hZ
  · rw [H.nu_sum_window G hk0 hkK hZ hqj hlt]
    unfold lin
    refine CoveredBy.biUnion _ _ _ fun Y hY => ?_
    have hd : H.Desc j k Y Z := mem_ancFin.mp hY
    have hj1 : 1 ≤ j := by
      by_contra h
      have : j = 0 := by omega
      subst this
      exact (H.F.isEmpty_comp_zero.false Y).elim
    have hap := nonpre_of_desc G hk0 hkK hZ hd hqj
    refine H.cover_post G hT hj1 (by omega) (by omega) Y ?_
    by_cases hr : S.Ripe j (H.bk j Y)
    · rw [S.postBook_of_ripe hj1 (by omega) hr]
      exact Or.inl ⟨j, 1, ∅, rfl⟩
    · rw [S.postBook_of_not_ripe hr]; exact hap

end Cover

end RegionHistory

end Balaban.LargeField
