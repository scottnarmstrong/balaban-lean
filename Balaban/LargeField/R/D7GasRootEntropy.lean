/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModHoleRoot
public import Balaban.LargeField.R.CoarseFineComponents
public import Balaban.LargeField.R.RExtraSize

/-!
# Rooted entropy and touched components at a removed component (VMOD-41, packages 1 and 3)

Counting lemmas on the landed fine cover size `d7SizePre` (the size of the pre-`R` boundary labels
against the raw region `Ω₋ = Ω_k^pre`).  A removed component `c` lies in `Z^pre_k ⊇ (Ω₋)ᶜ`, so
`G2_X` (rooted at a cell of `Ω₋`) does not apply to a root in `c`; but a pre-valid label that meets
`c` and `Ω₋` has an active cube of `Ω₋` in `c` or next to `c`.  With `K₀ = K0 d L κ₀`:

* `sum_exp_le_of_coarse_roots`: the `G2_X` sum over pre-valid coarse labels that contain one of
  finitely many root cubes of `Ω₋` is at most `#roots · K₀`;
* `sum_exp_le_rawHole`: labels containing a nearest-neighbour closed piece `Q ≠ ∅` of the raw hole
  `(Ω₋)ᶜ` and meeting `Ω₋`: at most `2 d |Q| K₀` (for `Q ⊆ c` a removed component, at most
  `2 d (2ρ_k + 10)^d K₀`);
* `sum_exp_le_removed`: labels meeting a removed component `c` (also when its raw hole is empty)
  and `Ω₋`: at most `(2d + 1) |c| K₀ ≤ (2d + 1)(2ρ_k + 10)^d K₀`;
* `remMeeting_card_le`: the number of removed components meeting a pre-valid label `X` that meets
  `Ω₋` is at most `(2d + 1) c₁(d, L) (1 + d7SizePre X)`.

These are counting lemmas.  The gas estimate itself, the retained-hole bridge and everything
analytic about the renormalization operation `R` are NOT proved here.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Localization Def7

section Exit

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K m₀ m₁ : ℕ} [NeZero S.L]
  (F : FineSizeFrame S n M K m₀ m₁) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ}
  (hkK : k ≤ K)
include hnn hkK

/-- A nearest-neighbour step of fine sites stays in a scale-`k` cube or moves to a
nearest-neighbour cube. -/
theorem cubeIdx_nbr {y z : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K} (h : Nbr y z) :
    cubeIdx F k z = cubeIdx F k y ∨ NNAdj (cubeIdx F k y) (cubeIdx F k z) := by
  have ha0 := cellSide_pos (L := S.L) m₀ m₁ k
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) (m₀ := m₀) F.divN₁ hkK
  rcases Fluctuation.cbase_nbr hdvd ha0 h with e | e
  · left
    rw [← cubeIdx_cbase F hnn hkK z, e, cubeIdx_cbase F hnn hkK y]
  · right
    have := (cAdj_iff_nnAdj F hnn hkK (aligned_cbase y) (aligned_cbase z)).1 e
    rwa [cubeIdx_cbase F hnn hkK, cubeIdx_cbase F hnn hkK] at this

/-- **The exit root.**  A pre-valid label `X` (a label whose fine lift is in `𝒟_k(mod (Ω_f)ᶜ)`)
that contains a cube `x ∉ Ω` and meets `Ω` contains a cube `q ∈ Ω` that is a nearest neighbour of
a cube `q'` joined to `x` by a nearest-neighbour path in `Ωᶜ`. -/
theorem exists_exit_root {Om : Set (Torus S.d (n k))} {X : Finset (Torus S.d (n k))}
    (hX : Fluctuation.DjMod m₀ k (d7Pull F k Om) (d7Pull F k (X : Set (Torus S.d (n k)))))
    {x : Torus S.d (n k)} (hxX : x ∈ X) (hxO : x ∉ Om) (hXO : ∃ q ∈ X, q ∈ Om) :
    ∃ q ∈ X, q ∈ Om ∧ ∃ q', Relation.ReflTransGen
      (fun u v => u ∉ Om ∧ v ∉ Om ∧ NNAdj u v) x q' ∧ NNAdj q' q := by
  have ha0 := cellSide_pos (L := S.L) m₀ m₁ k
  set Xf := d7Pull F k (X : Set (Torus S.d (n k))) with hXf
  set Of := d7Pull F k Om with hOf
  set y := cubeBase F k x with hy
  have hyc : cubeIdx F k y = x := cubeIdx_cubeBase F hnn hkK x
  have hyX : y ∈ Xf := by rw [hXf, d7Pull_iff, hyc]; exact hxX
  have hyO : y ∉ Of := by rw [hOf, d7Pull_iff, hyc]; exact hxO
  set Hc := Fluctuation.OmegaComp Of y with hHc
  have hHsub : Hc ⊆ Xf := by
    rcases hX.2 y hyO with h | h
    · exact h
    · exact absurd hyX (Set.disjoint_left.1 h (show y ∈ Fluctuation.OmegaComp Of y from
        ⟨hyO, Relation.ReflTransGen.refl⟩))
  have hyH : y ∈ Hc := ⟨hyO, Relation.ReflTransGen.refl⟩
  obtain ⟨q0, hq0X, hq0O⟩ := hXO
  have hXOf : (Xf ∩ Of).Nonempty :=
    ⟨cubeBase F k q0, by rw [hXf, d7Pull_iff, cubeIdx_cubeBase F hnn hkK]; exact hq0X,
      by rw [hOf, d7Pull_iff, cubeIdx_cubeBase F hnn hkK]; exact hq0O⟩
  obtain ⟨u, hu, t, hta, htb, hadj⟩ := Fluctuation.exists_active_adj_hole (H := Hc) F.divN₁ hkK
    (d7Pull_isPiUnion F hnn hkK Om) hX (fun z hz => hz.1)
    (fun y' hy' z hz hn => ⟨hz, hy'.2.tail ⟨hy'.1, hz, hn⟩⟩) hHsub ⟨y, hyH⟩ hXOf
  have htmem : t ∈ Xf ∩ Of := htb (mem_box_self t (cellSide_pos m₀ m₁ k))
  refine ⟨cubeIdx F k t, htmem.1, htmem.2, cubeIdx F k u, ?_, ?_⟩
  · -- the path from `y` to `u` projects to a path in the raw hole
    have key : ∀ b, Relation.ReflTransGen
        (fun u v => u ∈ Ofᶜ ∧ v ∈ Ofᶜ ∧ Nbr u v) y b →
        Relation.ReflTransGen (fun u v => u ∉ Om ∧ v ∉ Om ∧ NNAdj u v) x (cubeIdx F k b) := by
      intro b hb
      induction hb with
      | refl => rw [hyc]
      | @tail b' c' _ hbc ih =>
        rcases cubeIdx_nbr F hnn hkK hbc.2.2 with h | h
        · rw [h]; exact ih
        · exact ih.tail ⟨hbc.1, hbc.2.1, h⟩
    exact key u hu.2
  · have := (cAdj_iff_nnAdj F hnn hkK (aligned_cbase u) hta).1 hadj
    rwa [cubeIdx_cbase F hnn hkK] at this

/-- The fine lift of finite sets of cubes is injective. -/
theorem d7Pull_coe_injective :
    Function.Injective (fun X : Finset (Torus S.d (n k)) => d7Pull F k (X : Set (Torus S.d (n k)))) := by
  intro X X' h
  ext q
  have := congrArg (fun Y => cubeBase F k q ∈ Y) h
  simpa only [d7Pull_iff, cubeIdx_cubeBase F hnn hkK, Finset.mem_coe, eq_iff_iff] using this

open Classical in
/-- **The `G2_X` sum over valid coarse labels containing a root cube.**  If every label of a
family (valid at the region `Om`) contains one of the cubes of `Rt ⊆ Om`, then
`∑ e^{-κ₀ d} ≤ |Rt| · K₀`. -/
theorem sum_exp_le_of_coarse_roots (Om : Set (Torus S.d (n k))) (Rt : Finset (Torus S.d (n k)))
    (hRt : ∀ q ∈ Rt, q ∈ Om) {κ₀ : ℝ} (hκ : Fluctuation.aEnt S.d S.L + 1 ≤ κ₀)
    (P : Finset (Torus S.d (n k)) → Prop)
    (hP : ∀ X, FineValidAt F k Om X → P X → ∃ q ∈ Rt, q ∈ X) :
    ∑ X ∈ Finset.univ.filter (fun X : Finset (Torus S.d (n k)) => FineValidAt F k Om X ∧ P X),
        Real.exp (-κ₀ * d7SizeAt F k Om X) ≤ Rt.card * Fluctuation.K0 S.d S.L κ₀ := by
  have hinj : Function.Injective (fun X : Finset (Torus S.d (n k)) => d7Pull F k (X : Set (Torus S.d (n k)))) :=
    d7Pull_coe_injective F hnn hkK
  have h1 : ∑ X ∈ Finset.univ.filter (fun X : Finset (Torus S.d (n k)) => FineValidAt F k Om X ∧ P X),
        Real.exp (-κ₀ * d7SizeAt F k Om X) =
      ∑ Y ∈ (Finset.univ.filter (fun X : Finset (Torus S.d (n k)) => FineValidAt F k Om X ∧ P X)).image
          (fun X : Finset (Torus S.d (n k)) => d7Pull F k (X : Set (Torus S.d (n k)))),
        Real.exp (-κ₀ * Fluctuation.dcovMod m₀ k (d7Pull F k Om) Y) := by
    rw [Finset.sum_image (fun X _ X' _ h => hinj h)]
    exact Finset.sum_congr rfl fun X _ => by simp only [d7SizeAt, d7SizeAtE, Fluctuation.dcovMod]
  have hcell : ∀ (Y : Set (Torus S.d (n k))) (q : Torus S.d (n k)), q ∈ Y →
      Aligned (cellSide S.L m₀ m₁ k) (cubeBase F k q) ∧
        Localization.box (cubeBase F k q) (cellSide S.L m₀ m₁ k) ⊆ d7Pull F k Y := by
    intro Y q hq
    have := Fluctuation.mem_cellsIn.1
      ((cellsIn_d7Pull_mem F hnn hkK Y (cubeBase F k q)).2
        ⟨aligned_cubeBase F hnn hkK q, by rw [cubeIdx_cubeBase F hnn hkK]; exact hq⟩)
    exact this
  obtain ⟨Pf, hPf⟩ : ∃ Pf : Set (Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K) → Prop,
      ∀ Y, Pf Y ↔ ∃ X : Finset (Torus S.d (n k)), FineValidAt F k Om X ∧ P X ∧
        d7Pull F k (X : Set (Torus S.d (n k))) = Y := ⟨_, fun _ => Iff.rfl⟩
  have h2 := Fluctuation.sum_exp_le_of_roots (m₀ := m₀) (j := k) F.divN₁ hkK
    (d7Pull_isPiUnion F hnn hkK Om) (Rt.image (cubeBase F k))
    (fun r hr => by
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hr
      exact hcell Om q (hRt q hq)) hκ
    Pf (by
      rintro Y - hY
      obtain ⟨X, hv, hp, rfl⟩ := (hPf Y).1 hY
      obtain ⟨q, hq, hqX⟩ := hP X hv hp
      exact ⟨cubeBase F k q, Finset.mem_image.2 ⟨q, hq, rfl⟩, (hcell _ q hqX).2⟩)
  have hK : 0 ≤ Fluctuation.K0 S.d S.L κ₀ := by
    have h1 : 0 < 1 - Real.exp (-1) := by
      have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
      rw [Real.exp_zero] at this; linarith
    exact div_nonneg (Real.exp_pos _).le h1.le
  rw [h1]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
    (fun _ _ _ => (Real.exp_pos _).le)) (le_trans h2 ?_)
  · intro Y hY
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 hY
    obtain ⟨-, hv, hp⟩ := Finset.mem_filter.1 hX
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hv.1, (hPf _).2 ⟨X, hv, hp, rfl⟩⟩
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_image_le) hK

end Exit

section Cubes

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {k : ℕ}

/-- The at most `2 d` nearest neighbours of a cube (a literal helper set). -/
def nbrCubes (q : Torus S.d (n k)) : Finset (Torus S.d (n k)) :=
  (Finset.univ : Finset (Fin S.d × Bool)).image fun p =>
    if p.2 then q + Pi.single p.1 1 else q - Pi.single p.1 1

omit [∀ k, NeZero (n k)] in
theorem card_nbrCubes_le (q : Torus S.d (n k)) : (nbrCubes q).card ≤ 2 * S.d := by
  refine Finset.card_image_le.trans ?_
  simp [mul_comm]

omit [∀ k, NeZero (n k)] in
theorem nnAdj_symm_d7gas {q q' : Torus S.d (n k)} (h : NNAdj q q') : NNAdj q' q := by
  obtain ⟨μ, h⟩ := h
  exact ⟨μ, h.symm⟩

omit [∀ k, NeZero (n k)] in
theorem mem_nbrCubes_of_nnAdj {q q' : Torus S.d (n k)} (h : NNAdj q q') : q' ∈ nbrCubes q := by
  obtain ⟨μ, h | h⟩ := h
  · exact Finset.mem_image.2 ⟨(μ, true), Finset.mem_univ _, by simp [h]⟩
  · exact Finset.mem_image.2 ⟨(μ, false), Finset.mem_univ _, by simp [h]⟩

end Cubes

section Sums

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M m₀ m₁ : ℕ} [NeZero S.L]
  (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) {k : ℕ} (hkK : k ≤ K)
include hkK

/-- A removed component `c` meeting a pre-valid label `X` that meets `Ω₋` has a cube of
`X ∩ Ω₋` in `c` or next to a cube of `c`. -/
theorem exists_root_of_removed (hk : 1 ≤ k) {c : Finset (Torus S.d (n k))} (hc : c ∈ A.H.rem k)
    {X : Finset (Torus S.d (n k))} (hX : FineValidPre F A k X)
    (hXO : ∃ q ∈ X, q ∈ OmegaCube A.H k) {x : Torus S.d (n k)} (hxc : x ∈ c) (hxX : x ∈ X) :
    ∃ q ∈ X, q ∈ OmegaCube A.H k ∧ (q ∈ c ∨ ∃ q' ∈ c, NNAdj q' q) := by
  by_cases hxO : x ∈ OmegaCube A.H k
  · exact ⟨x, hxX, hxO, Or.inl hxc⟩
  · obtain ⟨q, hqX, hqO, q', hchain, hadj⟩ :=
      exists_exit_root F (RegionHistory.tower A.H) hkK hX.1 hxX hxO hXO
    exact ⟨q, hqX, hqO, Or.inr ⟨q', A.H.mem_of_nnPath_rawHole hk hc
      (T := (OmegaCube A.H k)ᶜ) subset_rfl hxc hchain, hadj⟩⟩

open Classical in
/-- **Rooted entropy at a raw-hole component (T4, hole form).**  Let `Q ≠ ∅` be a set of cubes of
the raw hole `(Ω₋)ᶜ` (`Ω₋ = Ω_k^pre`), closed under nearest-neighbour steps into the hole (for
instance a nearest-neighbour component of the hole), and `κ₀ ≥ a_ent + 1`.  Then
`∑_{X pre-valid, Q ⊆ X, X ∩ Ω₋ ≠ ∅} e^{-κ₀ d7SizePre(X)} ≤ 2 d |Q| K₀`. -/
theorem sum_exp_le_rawHole (Q : Finset (Torus S.d (n k))) (hQne : Q.Nonempty)
    (hQhole : ∀ q ∈ Q, q ∉ OmegaCube A.H k)
    (hQcl : ∀ y ∈ Q, ∀ z, z ∉ OmegaCube A.H k → NNAdj y z → z ∈ Q)
    {κ₀ : ℝ} (hκ : Fluctuation.aEnt S.d S.L + 1 ≤ κ₀) :
    ∑ X ∈ Finset.univ.filter (fun X : Finset (Torus S.d (n k)) =>
        FineValidPre F A k X ∧ Q ⊆ X ∧ ∃ q ∈ X, q ∈ OmegaCube A.H k),
      Real.exp (-κ₀ * d7SizePre F A k X) ≤ 2 * S.d * Q.card * Fluctuation.K0 S.d S.L κ₀ := by
  have hnn := RegionHistory.tower A.H
  set Rt : Finset (Torus S.d (n k)) := Finset.univ.filter fun q =>
    q ∈ OmegaCube A.H k ∧ ∃ q' ∈ Q, NNAdj q' q with hRt
  have hcard : Rt.card ≤ Q.card * (2 * S.d) := by
    refine le_trans (Finset.card_le_card (t := Q.biUnion nbrCubes) ?_)
      (Finset.card_biUnion_le.trans ?_)
    · intro q hq
      obtain ⟨-, -, q', hq', h⟩ := Finset.mem_filter.1 hq
      exact Finset.mem_biUnion.2 ⟨q', hq', mem_nbrCubes_of_nnAdj h⟩
    · calc ∑ s ∈ Q, (nbrCubes s).card ≤ ∑ _s ∈ Q, 2 * S.d :=
            Finset.sum_le_sum fun s _ => card_nbrCubes_le s
        _ = _ := by simp
  have key := sum_exp_le_of_coarse_roots F hnn hkK (OmegaCube A.H k) Rt
    (fun q hq => (Finset.mem_filter.1 hq).2.1) hκ
    (fun X => Q ⊆ X ∧ ∃ q ∈ X, q ∈ OmegaCube A.H k) (by
      rintro X hX ⟨hQX, hXO⟩
      obtain ⟨x, hx⟩ := hQne
      obtain ⟨q, hqX, hqO, q', hchain, hadj⟩ :=
        exists_exit_root F hnn hkK hX.1 (hQX hx) (hQhole x hx) hXO
      have hq' : q' ∈ Q := by
        have key : ∀ b, Relation.ReflTransGen
            (fun u v => u ∉ OmegaCube A.H k ∧ v ∉ OmegaCube A.H k ∧ NNAdj u v) x b → b ∈ Q := by
          intro b hb
          induction hb with
          | refl => exact hx
          | tail _ hbc ih => exact hQcl _ ih _ hbc.2.1 hbc.2.2
        exact key q' hchain
      exact ⟨q, Finset.mem_filter.2 ⟨Finset.mem_univ _, hqO, q', hq', hadj⟩, hqX⟩)
  have hK : 0 ≤ Fluctuation.K0 S.d S.L κ₀ := by
    have h1 : 0 < 1 - Real.exp (-1) := by
      have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
      rw [Real.exp_zero] at this; linarith
    exact div_nonneg (Real.exp_pos _).le h1.le
  unfold FineValidPre d7SizePre
  refine le_trans (le_of_eq (Finset.sum_congr (by ext; simp) (fun _ _ => rfl))) (key.trans ?_)
  have : (Rt.card : ℝ) ≤ 2 * S.d * Q.card := by
    have := (Nat.cast_le (α := ℝ)).2 hcard
    push_cast at this; linarith
  nlinarith

/-- Cubes of `Ω₋` in a removed component `c` or next to it (a literal helper set). -/
noncomputable def removedRoots (c : Finset (Torus S.d (n k))) : Finset (Torus S.d (n k)) :=
  open Classical in
  Finset.univ.filter fun q => q ∈ OmegaCube A.H k ∧ (q ∈ c ∨ ∃ q' ∈ c, NNAdj q' q)

omit [NeZero S.L] hkK in
theorem mem_removedRoots {c : Finset (Torus S.d (n k))} {q : Torus S.d (n k)} :
    q ∈ removedRoots A c ↔ q ∈ OmegaCube A.H k ∧ (q ∈ c ∨ ∃ q' ∈ c, NNAdj q' q) := by
  classical
  simp [removedRoots]

omit [NeZero S.L] hkK in
theorem card_removedRoots_le (c : Finset (Torus S.d (n k))) :
    (removedRoots A c).card ≤ (2 * S.d + 1) * c.card := by
  classical
  refine le_trans (Finset.card_le_card (t := c ∪ c.biUnion nbrCubes) ?_)
    ((Finset.card_union_le _ _).trans ?_)
  · intro q hq
    obtain ⟨-, h | ⟨q', hq', h⟩⟩ := (mem_removedRoots A).1 hq
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨q', hq', mem_nbrCubes_of_nnAdj h⟩)
  · have : (c.biUnion nbrCubes).card ≤ c.card * (2 * S.d) :=
      Finset.card_biUnion_le.trans (by
        calc ∑ s ∈ c, (nbrCubes s).card ≤ ∑ _s ∈ c, 2 * S.d :=
              Finset.sum_le_sum fun s _ => card_nbrCubes_le s
          _ = _ := by simp)
    nlinarith

open Classical in
/-- **Rooted entropy at a removed component (T4, both cases).**  For a removed component `c` of
scale `k` (`1 ≤ k ≤ K`) and `κ₀ ≥ a_ent + 1`:
`∑_{X pre-valid, X ∩ c ≠ ∅, X ∩ Ω₋ ≠ ∅} e^{-κ₀ d7SizePre(X)} ≤ (2d + 1) |c| K₀`.
(The roots are the cubes of `Ω₋` in `c`, if `c` has any, and those adjacent to `c`.) -/
theorem sum_exp_le_removed (hk : 1 ≤ k) {c : Finset (Torus S.d (n k))} (hc : c ∈ A.H.rem k)
    {κ₀ : ℝ} (hκ : Fluctuation.aEnt S.d S.L + 1 ≤ κ₀) :
    ∑ X ∈ Finset.univ.filter (fun X : Finset (Torus S.d (n k)) =>
        FineValidPre F A k X ∧ (∃ x ∈ X, x ∈ c) ∧ ∃ q ∈ X, q ∈ OmegaCube A.H k),
      Real.exp (-κ₀ * d7SizePre F A k X) ≤ (2 * S.d + 1) * c.card * Fluctuation.K0 S.d S.L κ₀ := by
  have hnn := RegionHistory.tower A.H
  have key := sum_exp_le_of_coarse_roots F hnn hkK (OmegaCube A.H k) (removedRoots A c)
    (fun q hq => ((mem_removedRoots A).1 hq).1) hκ
    (fun X => (∃ x ∈ X, x ∈ c) ∧ ∃ q ∈ X, q ∈ OmegaCube A.H k) (by
      rintro X hX ⟨⟨x, hxX, hxc⟩, hXO⟩
      obtain ⟨q, hqX, hqO, hq⟩ := exists_root_of_removed F A hkK hk hc hX hXO hxc hxX
      exact ⟨q, (mem_removedRoots A).2 ⟨hqO, hq⟩, hqX⟩)
  have hK : 0 ≤ Fluctuation.K0 S.d S.L κ₀ := by
    have h1 : 0 < 1 - Real.exp (-1) := by
      have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
      rw [Real.exp_zero] at this; linarith
    exact div_nonneg (Real.exp_pos _).le h1.le
  unfold FineValidPre d7SizePre
  refine le_trans (le_of_eq (Finset.sum_congr (by ext; simp) (fun _ _ => rfl))) (key.trans ?_)
  have : ((removedRoots A c).card : ℝ) ≤ (2 * S.d + 1) * c.card := by
    have := (Nat.cast_le (α := ℝ)).2 (card_removedRoots_le A c)
    push_cast at this; linarith
  nlinarith

open Classical in
/-- **The removed-component bound with explicit size** (`2ρ_k + 10` per side). -/
theorem sum_exp_le_removed_explicit (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hk : 1 ≤ k)
    {c : Finset (Torus S.d (n k))} (hc : c ∈ A.H.rem k)
    {κ₀ : ℝ} (hκ : Fluctuation.aEnt S.d S.L + 1 ≤ κ₀) :
    ∑ X ∈ Finset.univ.filter (fun X : Finset (Torus S.d (n k)) =>
        FineValidPre F A k X ∧ (∃ x ∈ X, x ∈ c) ∧ ∃ q ∈ X, q ∈ OmegaCube A.H k),
      Real.exp (-κ₀ * d7SizePre F A k X) ≤
        (2 * S.d + 1) * (((2 * S.rho k + 10) ^ S.d : ℕ) : ℝ) * Fluctuation.K0 S.d S.L κ₀ := by
  refine (sum_exp_le_removed F A hkK hk hc hκ).trans ?_
  have hK : 0 ≤ Fluctuation.K0 S.d S.L κ₀ := by
    have h1 : 0 < 1 - Real.exp (-1) := by
      have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
      rw [Real.exp_zero] at this; linarith
    exact div_nonneg (Real.exp_pos _).le h1.le
  have hcard : (c.card : ℝ) ≤ (((2 * S.rho k + 10) ^ S.d : ℕ) : ℝ) := by
    exact_mod_cast RegionHistory.removed_card_le G hT A.adm hkK (c := ⟨c, A.H.rem_sub k hc⟩) hc
  have h0 : (0 : ℝ) ≤ 2 * S.d + 1 := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard h0) hK

/-- **Touched components per label (T5).**  For a pre-valid label `X` that meets `Ω₋`, the number of
removed components meeting `X` is at most `(2d + 1) c₁(d, L) (1 + d7SizePre(X))`. -/
theorem remMeeting_card_le (hk : 1 ≤ k) {X : Finset (Torus S.d (n k))}
    (hX : FineValidPre F A k X) (hXO : ∃ q ∈ X, q ∈ OmegaCube A.H k) :
    ((A.H.remMeeting X).card : ℝ) ≤
      (2 * S.d + 1) * Fluctuation.c1 S.d S.L * (1 + d7SizePre F A k X) := by
  classical
  have hnn := RegionHistory.tower A.H
  set Ract : Finset (Torus S.d (n k)) := X.filter (fun q => q ∈ OmegaCube A.H k) with hRact
  set Cq : Torus S.d (n k) → Finset (Finset (Torus S.d (n k))) := fun q =>
    (A.H.rem k).filter (fun c => q ∈ c ∨ ∃ q' ∈ c, NNAdj q' q) with hCq
  have hCcard : ∀ q, (Cq q).card ≤ 2 * S.d + 1 := by
    intro q
    set N := insert q (nbrCubes q) with hN
    have hNcard : N.card ≤ 2 * S.d + 1 :=
      (Finset.card_insert_le _ _).trans (by have := card_nbrCubes_le (S := S) (n := n) q; omega)
    have hex : ∀ c ∈ Cq q, ∃ p, p ∈ c ∧ p ∈ N := by
      intro c hc
      obtain ⟨-, h | ⟨q', hq', h⟩⟩ := Finset.mem_filter.1 hc
      · exact ⟨q, h, Finset.mem_insert_self _ _⟩
      · exact ⟨q', hq', Finset.mem_insert_of_mem (mem_nbrCubes_of_nnAdj (nnAdj_symm_d7gas h))⟩
    refine le_trans (Finset.card_le_card_of_injOn
      (fun c => Classical.epsilon (fun p => p ∈ c ∧ p ∈ N)) (t := N) ?_ ?_) hNcard
    · intro c hc
      exact (Classical.epsilon_spec (hex c hc)).2
    · intro c hc c' hc' h
      have h1 := (Classical.epsilon_spec (hex c hc)).1
      have h2 := (Classical.epsilon_spec (hex c' hc')).1
      by_contra hne
      have hrc := (Finset.mem_filter.1 hc).1
      have hrc' := (Finset.mem_filter.1 hc').1
      have hd := RegionHistory.comp_disjoint (H := A.H)
        (c := ⟨c, A.H.rem_sub k hrc⟩) (c' := ⟨c', A.H.rem_sub k hrc'⟩)
        (fun e => hne (congrArg Subtype.val e))
      refine Finset.disjoint_left.1 hd h1 ?_
      simpa only [h] using h2
  have hsub : A.H.remMeeting X ⊆ Ract.biUnion Cq := by
    intro c hc
    obtain ⟨hcr, x, hxc, hxX⟩ := A.H.mem_remMeeting.1 hc
    obtain ⟨q, hqX, hqO, hq⟩ := exists_root_of_removed F A hkK hk hcr hX hXO hxc hxX
    exact Finset.mem_biUnion.2 ⟨q, Finset.mem_filter.2 ⟨hqX, hqO⟩, Finset.mem_filter.2 ⟨hcr, hq⟩⟩
  have hcount : (A.H.remMeeting X).card ≤ Ract.card * (2 * S.d + 1) :=
    (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (by
      calc ∑ q ∈ Ract, (Cq q).card ≤ ∑ _q ∈ Ract, (2 * S.d + 1) :=
            Finset.sum_le_sum fun q _ => hCcard q
        _ = _ := by simp))
  have hG1 := Fluctuation.G1_cellCount (m₀ := m₀) (j := k) F.divN₁ hkK
    (Ω := d7Pull F k (OmegaCube A.H k)) (X := d7Pull F k (X : Set (Torus S.d (n k)))) hX.1
  have hset : d7Pull F k (X : Set (Torus S.d (n k))) ∩ d7Pull F k (OmegaCube A.H k) =
      d7Pull F k (Ract : Set (Torus S.d (n k))) := by
    ext x
    simp [hRact, d7Pull_iff]
  have hcc : cellCount (cellSide S.L m₀ m₁ k) (d7Pull F k (Ract : Set (Torus S.d (n k)))) =
      Ract.card := by
    rw [← card_cellsIn_d7Pull F hnn hkK Ract]; rfl
  rw [hset, hcc] at hG1
  have hc1 : 0 ≤ Fluctuation.c1 S.d S.L := by unfold Fluctuation.c1; positivity
  have hD : d7SizePre F A k X = Fluctuation.dcovMod m₀ k (d7Pull F k (OmegaCube A.H k))
      (d7Pull F k (X : Set (Torus S.d (n k)))) := rfl
  rw [hD]
  have h1 : ((A.H.remMeeting X).card : ℝ) ≤ (Ract.card : ℝ) * (2 * S.d + 1) := by
    exact_mod_cast hcount
  have h2 : (0 : ℝ) ≤ 2 * S.d + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hG1 h2]

end Sums

end Balaban.LargeField
