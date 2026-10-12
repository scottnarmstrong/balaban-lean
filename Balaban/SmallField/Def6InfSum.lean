/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6BridgeGeom
public import Balaban.SmallField.Def6InfBasic

/-!
# Def-6: summability of the infinite-volume family `T∞` (CLASS-RULINGS Q-C)

* `exp_sum_le_at`: counting of the lifts of non-winding shapes containing a centre `y`, from (G2);
* `InfDom`: the data `(ψ, h)` lie in the class analytic domain of the polymers of `T∞` containing `y`;
* `Einf_norm_le`: the class bound `E₀ e^{-κ d_j}` transported to `Einf` by `Einf_eq_torus`;
* `ElocInf_summable_norm_le`, `ElocInf_summable`, `norm_ElocInf_le`: for a member of the class
  and `κ ≥ a_ent + 1` the family `X' ↦ ℰ_∞(y, X')` over the polymers of `T∞` containing `y` is
  absolutely summable, with sum of norms at most `E₀ K0`.  The `tsum` of `ElocInf` is a genuine
  sum, so the conditions (H.5) of `RenormCond` are not vacuous.
-/


@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation Balaban.SmallField Metric Set

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- The cell of the origin-block of a point lies in a polymer containing it. -/
theorem cell_subset_of_mem {m₀ j : ℕ} (hjk : j ≤ k) (hN : L ^ m₀ ∣ N₁)
    {Y : Set (CTorus d L N₁ m₁ k)} (hY : IsDj m₀ j Y) {z : CTorus d L N₁ m₁ k} (hz : z ∈ Y) :
    box (cbase (cellSide L m₀ m₁ j) z) (cellSide L m₀ m₁ j) ⊆ Y := by
  obtain ⟨b, hb, hzb, hsub⟩ := hY.2.1 z hz
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hdvd := cellSide_dvd (K := k) (m₁ := m₁) hN hjk
  exact (cell_subset_cube hdvd ha0 hb hzb).trans hsub

/-- A shape that does not wind is determined by its torus polymer. -/
theorem ypoly_injOn_nonWind {j : ℕ} (hjk : j ≤ k) {A B : Finset (Site d)}
    (hA : NonWind L N₁ m₁ k j A) (hB : NonWind L N₁ m₁ k j B)
    (h : Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j A =
      Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j B) : A = B := by
  have key : ∀ {A B : Finset (Site d)}, NonWind L N₁ m₁ k j A →
      Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j A ⊆
        Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j B → A ⊆ B := by
    intro A B hA hAB z hz
    have hmem : ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z ∈ Ypoly j A := by
      show unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (ibase j z) ∈ A
      rw [unlift_ibase hjk (hA z hz)]; exact hz
    have := hAB hmem
    change unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (ibase j z) ∈ B at this
    rwa [unlift_ibase hjk (hA z hz)] at this
  exact Finset.Subset.antisymm (key hA h.le) (key hB h.ge)

open Classical in
/-- **Counting around a centre `y`** (from (G2)): the polymers of `𝒟_j` that are lifts of
non-winding shapes containing `y` satisfy `∑ e^{-κ₀ d_j} ≤ K₀` (for `κ₀ ≥ a_ent + 1`). -/
theorem exp_sum_le_at {m₀ j : ℕ} (hjk : j ≤ k) (hN : L ^ m₀ ∣ N₁) {κ₀ : ℝ}
    (hκ : aEnt d L + 1 ≤ κ₀) (y : Site d) (S : Finset (Finset (Site d)))
    (hS : ∀ X' ∈ S, y ∈ X' ∧ NonWind L N₁ m₁ k j X' ∧
      IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) :
    ∑ X' ∈ S, Real.exp (-κ₀ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) ≤ K0 d L κ₀ := by
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hΩ : IsPiUnion (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k) m₀ j Set.univ :=
    fun z _ => ⟨cbase (cellSide L m₀ m₁ j) z, aligned_cbase z, mem_box_cbase ha0 z,
      Set.subset_univ _⟩
  set t : CTorus d L N₁ m₁ k := cbase (cellSide L m₀ m₁ j) (ibase j y) with ht
  have hG2 := G2_X (m₀ := m₀) (j := j) hN hjk hΩ (t0 := t) (aligned_cbase _) (Set.subset_univ _) hκ
  have hinj : Set.InjOn (fun X' : Finset (Site d) =>
      Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') (S : Set (Finset (Site d))) :=
    fun A hA B hB h => ypoly_injOn_nonWind hjk (hS A hA).2.1 (hS B hB).2.1 h
  rw [← Finset.sum_image (f := fun Y : Set (CTorus d L N₁ m₁ k) =>
    Real.exp (-κ₀ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j Y)) hinj]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.univ.filter
    (fun X : Set (CTorus d L N₁ m₁ k) => DjMod m₀ j Set.univ X ∧
      box t (cellSide L m₀ m₁ j) ⊆ X)) ?_ (fun _ _ _ => (Real.exp_pos _).le)) ?_
  · intro Y hY
    obtain ⟨X', hX', rfl⟩ := Finset.mem_image.1 hY
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨hy, hnw, hX⟩ := hS X' hX'
    have hDj := isDj_of_isPolyDom hX
    have hmem : ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y ∈ Ypoly j X' := by
      show unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (ibase j y) ∈ X'
      rw [unlift_ibase hjk (hnw y hy)]; exact hy
    exact ⟨⟨hDj, fun z hz => absurd (Set.mem_univ z) hz⟩, cell_subset_of_mem hjk hN hDj hmem⟩
  · refine le_trans (le_of_eq (Finset.sum_congr rfl fun Y hY => ?_)) hG2
    rw [dcovMod_of_subset (Set.subset_univ Y)]
    rfl


section Summable

open Filter

variable {N : ℕ} {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}

/-- The class analytic domain of the polymers of `T∞` containing `y`: the pulled-back data lie in
`Ξ^c_j(𝔹_j(Y); 1, ε_j)` of the lift `Y` of the polymer, on all tori of the sequence from some
torus on. -/
def InfDom (P : Consts) (β ν a : ℕ → ℝ) (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
    (j : ℕ) (y : Fin d → ℤ) (ψ h : InfFld d N) : Prop :=
  ∀ X' : Finset (Fin d → ℤ), InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' → y ∈ X' →
    ∀ᶠ n in atTop, haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
      XiDom ((Tm (torusSeq L P.m₀ n)).gs j (Ypoly j X')) (aIdeal L k (a k))
        (bgMass L k (β k) (ν k)) j (P.eps d L j) (pullFld j ψ) (pullFld j h)

open Classical in
/-- The summand of `ElocInf` at the centre `y`. -/
noncomputable def ElocInfTerm (P : Consts) (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
    (j : ℕ) (y : Fin d → ℤ) (ψ h : InfFld d N) (X' : Finset (Fin d → ℤ)) : ℂ :=
  if InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' ∧ y ∈ X' then Einf P.m₀ Tm j y X' ψ h else 0

/-- **The bound of the terms of `T∞`**: for a polymer of `T∞` containing `y` and data in the class
analytic domain, the term is bounded by the class bound `E₀ e^{-κ d_j}` of any torus on which the
polymer does not wind. -/
theorem Einf_norm_le (hF : IsSFFamily P β ν a Tm ρd Ek) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : Fin d → ℤ} {X' : Finset (Fin d → ℤ)} (hy : y ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') (ψ h : InfFld d N)
    (N₁ : ℕ) [NeZero N₁] (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (hxi : XiDom ((Tm N₁).gs j (Ypoly j X')) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j
      (P.eps d L j) (pullFld j ψ) (pullFld j h)) :
    ‖Einf P.m₀ Tm j y X' ψ h‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) P.m₀ j (Ypoly j X')) := by
  rw [Einf_eq_torus hF.torusIndep hj1 hjk hy hX ψ h N₁ hnw hpd]
  have hmem : (blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y) ∈ Ypoly j X' := by
    have : blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y = ibase j y := by
      funext μ; simp only [blockPt, ibase]; congr 1; ring
    rw [this]
    show unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (ibase j y) ∈ X'
    rw [unlift_ibase hjk (hnw y hy)]; exact hy
  exact (hF.torus N₁).boundE j hj1 hjk _ _ hpd hmem _ _ hxi

/-- **Item 1: `ElocInf` is a genuine sum.**  For a member of the class, data `(ψ, h)` in the class
analytic domain of the polymers of `T∞` containing `y`, and `κ ≥ a_ent + 1`, the family
`X' ↦ ℰ_∞(y, X'; ψ, h)` over the polymers of `T∞` containing `y` is absolutely summable, with
`∑ |ℰ_∞(y, X')| ≤ E₀ K₀`, `K₀ = K0 d L κ` (the entropy constant of (G2), independent of the scale
and of the torus). -/
theorem ElocInf_summable_norm_le (hF : IsSFFamily P β ν a Tm ρd Ek) (hE0 : 0 ≤ P.E₀)
    (hκ : aEnt d L + 1 ≤ P.κ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (y : Fin d → ℤ)
    (ψ h : InfFld d N) (hdom : InfDom P β ν a Tm j y ψ h) :
    Summable (fun X' => ‖ElocInfTerm P Tm j y ψ h X'‖) ∧
      ∑' X', ‖ElocInfTerm P Tm j y ψ h X'‖ ≤ P.E₀ * K0 d L P.κ := by
  classical
  have key : ∀ u : Finset (Finset (Fin d → ℤ)),
      ∑ X' ∈ u, ‖ElocInfTerm P Tm j y ψ h X'‖ ≤ P.E₀ * K0 d L P.κ := by
    intro u
    set u' := u.filter (fun X' => InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' ∧ y ∈ X') with hu'
    have h1 : ∑ X' ∈ u, ‖ElocInfTerm P Tm j y ψ h X'‖ = ∑ X' ∈ u', ‖Einf P.m₀ Tm j y X' ψ h‖ := by
      rw [hu', Finset.sum_filter]
      refine Finset.sum_congr rfl fun X' _ => ?_
      unfold ElocInfTerm
      split_ifs <;> simp
    have hev : ∀ᶠ n in atTop, ∀ X' ∈ u',
        haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
        NonWind L (torusSeq L P.m₀ n) m₁ k j X' ∧
          IsPolyDom (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) P.m₀ j
            (Ypoly (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j X') ∧
          XiDom ((Tm (torusSeq L P.m₀ n)).gs j (Ypoly j X')) (aIdeal L k (a k))
            (bgMass L k (β k) (ν k)) j (P.eps d L j) (pullFld j ψ) (pullFld j h) := by
      rw [Filter.eventually_all_finset]
      intro X' hX'
      have hX'' := (Finset.mem_filter.1 hX').2
      filter_upwards [hX''.1, hdom X' hX''.1 hX''.2] with n h1 h2 using ⟨h1.1, h1.2, h2⟩
    obtain ⟨n, hn⟩ := hev.exists
    have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
    rw [h1]
    calc ∑ X' ∈ u', ‖Einf P.m₀ Tm j y X' ψ h‖
        ≤ ∑ X' ∈ u', P.E₀ * Real.exp (-P.κ * sizeJ (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁)
            (k := k) P.m₀ j (Ypoly j X')) :=
          Finset.sum_le_sum fun X' hX' =>
            Einf_norm_le hF hj1 hjk (Finset.mem_filter.1 hX').2.2 (Finset.mem_filter.1 hX').2.1
              ψ h _ (hn X' hX').1 (hn X' hX').2.1 (hn X' hX').2.2
      _ = P.E₀ * ∑ X' ∈ u', Real.exp (-P.κ * sizeJ (L := L) (N₁ := torusSeq L P.m₀ n)
            (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X')) := by rw [Finset.mul_sum]
      _ ≤ P.E₀ * K0 d L P.κ := by
          refine mul_le_mul_of_nonneg_left ?_ hE0
          exact exp_sum_le_at hjk (torusSeq_dvd P.m₀ n) hκ y u' fun X' hX' =>
            ⟨(Finset.mem_filter.1 hX').2.2, (hn X' hX').1, (hn X' hX').2.1⟩
  have hs : Summable (fun X' => ‖ElocInfTerm P Tm j y ψ h X'‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) key
  exact ⟨hs, hs.tsum_le_of_sum_le key⟩


/-- **`ElocInf_summable`**: the family of terms of `T∞` at the centre `y` is summable. -/
theorem ElocInf_summable (hF : IsSFFamily P β ν a Tm ρd Ek) (hE0 : 0 ≤ P.E₀)
    (hκ : aEnt d L + 1 ≤ P.κ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (y : Fin d → ℤ)
    (ψ h : InfFld d N) (hdom : InfDom P β ν a Tm j y ψ h) :
    Summable (ElocInfTerm P Tm j y ψ h) :=
  (ElocInf_summable_norm_le hF hE0 hκ hj1 hjk y ψ h hdom).1.of_norm

/-- `ElocInf` is the sum of `ElocInfTerm`. -/
theorem ElocInf_eq_tsum (j : ℕ) (y : Fin d → ℤ) (ψ h : InfFld d N) :
    ElocInf P.m₀ Tm j y ψ h = ∑' X', ElocInfTerm P Tm j y ψ h X' := rfl

/-- **The bound of `ElocInf`**: `|ℰ_∞^{(j)}(y; ψ, h)| ≤ E₀ K₀`. -/
theorem norm_ElocInf_le (hF : IsSFFamily P β ν a Tm ρd Ek) (hE0 : 0 ≤ P.E₀)
    (hκ : aEnt d L + 1 ≤ P.κ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (y : Fin d → ℤ)
    (ψ h : InfFld d N) (hdom : InfDom P β ν a Tm j y ψ h) :
    ‖ElocInf P.m₀ Tm j y ψ h‖ ≤ P.E₀ * K0 d L P.κ := by
  obtain ⟨hs, hle⟩ := ElocInf_summable_norm_le hF hE0 hκ hj1 hjk y ψ h hdom
  exact (norm_tsum_le_tsum_norm hs).trans hle

end Summable

end Balaban.SmallField.Def6
