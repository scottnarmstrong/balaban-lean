module

public import Balaban.LargeField.History.GainClock
public import Balaban.LargeField.Geometry.LocalGlobal

/-!
# What Part III's Lemma III.1.2 needs: the geometry of a ripe component

`RipeWindow H k Z` collects the statements of Lemma III.1.2 (RQ1)–(RQ5) that are about the region
history (Part I, Lemma I.4.13 (a), (b), (e4), (f4), (g) and Lemma I.4.10 (a)); `ripe_window` proves
them for a ripe component `Z` of `Z^pre_k`, `1 ≤ k ≤ k₀`, with `q = k₁(k)` the core and `ν` the number
of pieces.  The analytic parts of Lemma III.1.2 ((III.1.1), `λ_j ≥ λ̂_k/(4 c_*)`, the counts of
blocks, (f)) are not about the history.

* `core_k1`: `q = k₁(k)`;
* `active`, `live`, `no_new`, `not_ripe`, `gain_le` (RQ1, Lemma I.4.13 (a));
* `cover`, `nu_le` (RQ2, Lemma I.4.13 (b));
* `point`, `unique_box` (RQ3, Lemma I.4.13 (g));
* `core_box`, `core_sep`, `core_thick` (RQ5, Lemma I.4.13 (e4) and Lemma I.2.13).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0)

/-- The geometric content of Lemma III.1.2 for a ripe component `Z` of scale `k`; `q` is the core
and `ν` the number of pieces of `Z`. -/
structure RipeWindow (k : ℕ) (Z : H.Comp k) : Prop where
  /-- (a): the core is `k₁(k)`. -/
  core_k1 : S.k1 k = (H.bk k Z).q
  /-- `q + n_q(q) ≤ k < (q + 1) + n_q(q + 1)`. -/
  core_window : (H.bk k Z).q + S.nq (H.bk k Z).q ≤ k ∧
    k < ((H.bk k Z).q + 1) + S.nq ((H.bk k Z).q + 1)
  /-- (RQ1): the ancestors at scales `j ≥ q` are `Active` or `Pending`. -/
  active : ∀ j (Y : H.Comp j), H.Desc j k Y Z → (H.bk k Z).q ≤ j →
    (H.bk j Y).IsActive ∨ (H.bk j Y).IsPending
  /-- (RQ1): the steps into the ancestors at scales `j ∈ (q, k]` are live: no new cube, only (T1)
  and (T4). -/
  live : ∀ j (Y : H.Comp j), H.Desc j k Y Z → (H.bk k Z).q < j → LiveAt j Y
  /-- (RQ1): no new cube in the lineage at scales `j ∈ (q, k]`. -/
  no_new : ∀ j, (H.bk k Z).q < j → j ≤ k → H.lin j k Z ∩ H.newCubes j = ∅
  /-- (RQ1): no ancestor at a scale in `(q, k)` is ripe (so none is removed or kept). -/
  not_ripe : ∀ j (Y : H.Comp j), H.Desc j k Y Z → (H.bk k Z).q < j → j < k →
    ¬ S.Ripe j (H.bk j Y)
  /-- the gain clock `b(Z) ≤ q`. -/
  gain_le : H.gain k Z ≤ (H.bk k Z).q
  /-- (RQ2): `Lin_j(Z)` is covered by `ν` boxes of side `≤ crit_j`, `q ≤ j ≤ k`. -/
  cover : ∀ j, (H.bk k Z).q ≤ j → j ≤ k → CoveredBy S n j (H.lin j k Z) (H.bk k Z).nu
  /-- `ν ≤ ν_max(k)`. -/
  nu_le : (H.bk k Z).nu ≤ S.numax k
  /-- (RQ3): the spine of `Z` is a point and `s + n_2(s) ≤ k`, `s < k`. -/
  point : (H.bk k Z).len = 0 ∧ (H.bk k Z).s + S.n2 (H.bk k Z).s ≤ k ∧ (H.bk k Z).s < k
  /-- (RQ3): for `s ≤ j ≤ k` the ancestor of `Z` at scale `j` is unique, a point, one box. -/
  unique_box : ∀ j (Y : H.Comp j), (H.bk k Z).s ≤ j → H.Desc j k Y Z →
    (H.bk j Y).len = 0 ∧ CoveredBy S n j Y.1 1 ∧ ∀ Y' : H.Comp j, H.Desc j k Y' Z → Y' = Y
  /-- (RQ5): the ancestors at scale `q` are boxes of side `≤ crit_q`. -/
  core_box : ∀ Y : H.Comp (H.bk k Z).q, H.Desc (H.bk k Z).q k Y Z → CoveredBy S n _ Y.1 1
  /-- (RQ5): distinct ancestors at scale `q` are at distance `≥ ω_q`. -/
  core_sep : ∀ Y Y' : H.Comp (H.bk k Z).q, Y ≠ Y' → ∀ x ∈ Y.1, ∀ y ∈ Y'.1,
    S.omega (H.bk k Z).q ≤ supDist x y

variable {H}

/-- Lemma I.2.13 (flow form) for the ancestors at scale `q ≥ 1`: for `m ≤ (L + 8)/2` the sets
`(C^≈)^{∼m}` of distinct components are disjoint. -/
theorem core_thick (RH : RadiusHyp S.L S.Rb S.lam R) {q : ℕ} (hq : 1 ≤ q) {Y Y' : H.Comp q}
    (hne : Y ≠ Y') (m : ℕ) :
    ∀ u ∈ nbhd m (thick ⌊R (q - 1)⌋₊ (Y.1 : Set (Torus S.d (n q)))),
      ∀ u' ∈ nbhd m (thick ⌊R (q - 1)⌋₊ (Y'.1 : Set (Torus S.d (n q)))),
        S.L + 9 ≤ supDist u u' + 2 * m := by
  refine nbhd_thick_disjoint Y.2 Y'.2 (fun h => hne (Subtype.ext h)) (L := S.L)
    (rhat := ⌊S.Rb * S.lam (q - 1) ^ 2⌋₊) ?_ ?_ m
  · exact Nat.floor_le_floor (RH.le (q - 1))
  · obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
    simp [Setting.omega]

theorem core_thick_disjoint (RH : RadiusHyp S.L S.Rb S.lam R) {q : ℕ} (hq : 1 ≤ q)
    {Y Y' : H.Comp q} (hne : Y ≠ Y') {m : ℕ} (hm : 2 * m ≤ S.L + 8) :
    Disjoint (nbhd m (thick ⌊R (q - 1)⌋₊ (Y.1 : Set (Torus S.d (n q)))))
      (nbhd m (thick ⌊R (q - 1)⌋₊ (Y'.1 : Set (Torus S.d (n q))))) := by
  rw [Set.disjoint_left]
  intro u hu hu'
  have := core_thick RH hq hne m u hu u hu'
  rw [supDist_self] at this
  omega

variable (G : S.Good)

include G

/-- **Lemma III.1.2 (RQ1)–(RQ5), the part about the region history**: a ripe component `Z` of
`Z^pre_k`, `1 ≤ k ≤ k₀` (assuming `n_j ≥ 4ρ_j + 21` for `1 ≤ j ≤ k₀`). -/
theorem ripe_window (hT : ∀ k, 1 ≤ k → k ≤ k0 → 4 * S.rho k + 21 ≤ n k) {k : ℕ} {Z : H.Comp k}
    (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z)) : H.RipeWindow k Z := by
  have hZ : (H.bk k Z).IsActive ∨ (H.bk k Z).IsPending := Or.inl hrip.1
  have hk1 : 1 ≤ k := not_isEmpty_comp Z hk0
  have hinv := (H.window_inv' G k hk1 hk0 Z).1
  have htS : S.tStar (H.bk k Z) = k := hrip.2
  have hlo : (H.bk k Z).q + S.nq (H.bk k Z).q ≤ k := by
    have := S.tStar_ge_left (H.bk k Z); omega
  have hhi : k < ((H.bk k Z).q + 1) + S.nq ((H.bk k Z).q + 1) := by
    have := hinv.f4 hZ; rwa [htS] at this
  obtain ⟨hpt, hlen0, hsn⟩ := S.ripe_facts hinv hrip
  have hn2 := G.ok.one_le_n2 (H.bk k Z).s
  have hs_lt : (H.bk k Z).s < k := by omega
  refine ⟨?_, ⟨hlo, hhi⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨hlen0, hsn, hs_lt⟩, ?_, ?_, ?_⟩
  · have := (G.ok.k1_eq_iff (S := S) (t := k) (c := (H.bk k Z).q)
      (by have := G.ok.nq_mono (Nat.zero_le (H.bk k Z).q); omega)).mpr ⟨hlo, hhi⟩
    exact this
  · intro j Y hd hq; exact nonpre_of_desc G hk0 hZ hd hq
  · intro j Y hd hq; exact live_of_desc G hk0 hZ hd hq
  · intro j hq hjk
    ext x
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
    rintro ⟨hx, hxn⟩
    obtain ⟨Y, hd, hxY⟩ := mem_lin.mp hx
    have hL := live_of_desc G hk0 hZ hd hq
    obtain ⟨κ, rfl⟩ : ∃ κ, j = κ + 1 := ⟨j - 1, by omega⟩
    have hr : (Y.1 ∩ H.newCubes (κ + 1)).card = 0 := hL.1
    rw [Finset.card_eq_zero] at hr
    have : x ∈ Y.1 ∩ H.newCubes (κ + 1) := Finset.mem_inter.mpr ⟨hxY, hxn⟩
    rw [hr] at this
    simp at this
  · intro j Y hd hq hjk; exact not_ripe_of_desc G hk0 hZ hd hq hjk
  · exact gain_le_core G hk0 hZ
  · intro j hq hjk; exact cover_window G hT hk0 hZ hq hjk
  · have := hinv.adm
    obtain ⟨q, ν, M, hst⟩ := hrip.1
    rw [S.adm_active hst] at this
    rw [Book.nu_active hst]
    exact this.2.2.1
  · intro j Y hsj hd
    have hjk := hd.le
    obtain ⟨h1, -, h3⟩ := pt_desc G k Z hk0 hpt (s := (H.bk k Z).s) rfl (by omega) j Y hsj hd
    have hj1 : 1 ≤ j := not_isEmpty_comp Y (by omega)
    have hinvY := (H.window_inv' G j hj1 (by omega) Y).1
    have hl := hinvY.pt_len h1
    exact ⟨hl, cover_of_len hT hj1 (by omega) Y hl, h3⟩
  · intro Y hd; exact core_box G hT hk0 hZ rfl hd
  · intro Y Y' hne x hx y hy; exact core_sep hne hx hy

end RegionHistory

end Balaban.LargeField
