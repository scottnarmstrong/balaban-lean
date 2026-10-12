module

public import Balaban.LargeField.History.RipeWindow
public import Balaban.LargeField.Region.Hull
public import Balaban.LargeField.History.FlowCover

/-!
# `Z_j` is one box (Lemma III.1.2 (d), RQ3)

`RipeWindow.unique_box` gives, for the ancestor `Y` of a ripe `Z` at scale `j ∈ [s, k]`, a *cover* of
`Y` by one box of side `≤ crit_j`.  The source says that `Z_j` *is* one box.  The two agree because the
components of `Z^pre_j = Hull_{crit_j}(Z^{(0)}_j)` (`j ≤ k₀`) that are small of side `≤ crit_j` are
boxes (Lemma I.3.4 (b), `hullClosure_box`):

* `comp_eq_box_of_covered`: a component of `Z^pre_j`, `1 ≤ j ≤ k₀`, covered by one box of side
  `≤ crit_j` (with `n_j ≥ 4 ρ_j + 21`) is a box of sides in `[1, crit_j]`;
* `RipeWindow.lin_eq_box`: `Z_j = Lin_j(Z)` is one box of sides in `[1, crit_j]` for `s ≤ j ≤ k`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K}

/-- A component of `Z^pre_j` covered by one box of side `≤ crit_j` is a box of sides in
`[1, crit_j]` (Lemma I.3.4 (b)). -/
theorem comp_eq_box_of_covered {j : ℕ} (hj1 : 1 ≤ j) (hjk0 : j ≤ k0) (hT : 4 * S.rho j + 21 ≤ n j)
    (Y : H.Comp j) (hY : CoveredBy S n j Y.1 1) :
    ∃ (a : Torus S.d (n j)) (sd : Fin S.d → ℕ), (Y.1 : Set (Torus S.d (n j))) = box a sd ∧
      ∀ i, 1 ≤ sd i ∧ sd i ≤ S.crit j := by
  obtain ⟨B, hBc, hBs, hsub⟩ := hY
  obtain ⟨y0, hy0⟩ := comp_nonempty Y.2
  have hy0' : y0 ∈ (Y.1 : Set (Torus S.d (n j))) := hy0
  have hne : (Y.1 : Set (Torus S.d (n j))).Nonempty := ⟨y0, hy0⟩
  have hBne : B.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := hsub hy0'
    simp [h] at this
  obtain ⟨b, hb⟩ := hBne
  have hB1 := Finset.card_le_one.mp hBc
  have hcov : ∀ x ∈ (Y.1 : Set (Torus S.d (n j))), ∀ i, x i ∈ cycInt (b.1 i) (b.2 i) := by
    intro x hx i
    have := hsub hx
    simp only [Set.mem_iUnion] at this
    obtain ⟨b', hb', hxb'⟩ := this
    have := hB1 b' hb' b hb
    rw [this] at hxb'
    exact hxb' i
  have hs := hBs b hb
  have hcrit : S.crit j = 2 * S.rho j + 10 := rfl
  have hsmall : IsSmall (Y.1 : Set (Torus S.d (n j))) := fun i =>
    ⟨b.1 i, b.2 i, by have := hs i; omega, fun x hx => hcov x hx i⟩
  have hside : side (Y.1 : Set (Torus S.d (n j))) ≤ S.crit j :=
    Finset.sup_le fun i _ => (ncard_hullCoord_le (by have := hs i; omega) (fun x hx => hcov x hx i)).trans
      (hs i)
  have hω : 2 ≤ S.omega j := by
    unfold Setting.omega
    have : j ≠ 0 := by omega
    simp only [this, ↓reduceIte]; omega
  have hjcrit : critOpt S k0 j = some (S.crit j) := by simp [critOpt, hjk0]
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hC : Y.1 ∈ comps (S.omega (j' + 1))
      (finOf (hullClosure (S.omega (j' + 1)) (S.crit (j' + 1)) (H.F.step j').Z0)) := by
    have h : Y.1 ∈ comps (S.omega (j' + 1)) (finOf (H.F.Zpre (j' + 1))) := Y.2
    have e : H.F.Zpre (j' + 1) =
        hullClosure (S.omega (j' + 1)) (S.crit (j' + 1)) (H.F.step j').Z0 := by
      show (H.F.step j').Zpre (S.omega (j' + 1)) (critOpt S k0 (j' + 1)) = _
      rw [hjcrit]; rfl
    rwa [e] at h
  have hbox := hullClosure_box hω _ hC hsmall hside
  obtain ⟨a', s', hh, hs', hsd⟩ := hull_eq_box hne hsmall
  refine ⟨a', s', hbox.trans hh, fun i => ⟨(hs' i).1, ?_⟩⟩
  have : s' i ≤ Finset.univ.sup s' := Finset.le_sup (f := s') (Finset.mem_univ i)
  omega

/-- **Lemma III.1.2 (d), RQ3**: for a ripe window and `s ≤ j ≤ k`, `Z_j = Lin_j(Z)` *is* one box, of
sides in `[1, crit_j]` (not only covered by one box).  The hypothesis is (H-T): `n_j ≥ 4ρ_j + 21`. -/
theorem RipeWindow.lin_eq_box {k : ℕ} {Z : H.Comp k} (W : H.RipeWindow k Z) (hk0 : k ≤ k0)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) {j : ℕ} (hsj : (H.bk k Z).s ≤ j)
    {Y : H.Comp j} (hd : H.Desc j k Y Z) :
    ∃ (a : Torus S.d (n j)) (sd : Fin S.d → ℕ), (H.lin j k Z : Set (Torus S.d (n j))) = box a sd ∧
      ∀ i, 1 ≤ sd i ∧ sd i ≤ S.crit j := by
  have hj1 : 1 ≤ j := not_isEmpty_comp Y (hd.le.trans hk0)
  obtain ⟨-, hcov, huniq⟩ := W.unique_box j Y hsj hd
  obtain ⟨a, sd, hbox, hsd⟩ := comp_eq_box_of_covered hj1 (hd.le.trans hk0) (hT j hj1 (hd.le.trans hk0)) Y hcov
  refine ⟨a, sd, ?_, hsd⟩
  rw [← hbox]
  ext x
  constructor
  · intro hx
    obtain ⟨Y', hY', hxY'⟩ := mem_lin.mp hx
    rw [huniq Y' hY'] at hxY'
    exact hxY'
  · intro hx
    exact Finset.mem_coe.mpr (mem_lin.mpr ⟨Y, hd, hx⟩)

end RegionHistory

end Balaban.LargeField
