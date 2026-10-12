module

public import Balaban.LargeField.History.FlowCover
public import Balaban.LargeField.History.Step
public import Balaban.LargeField.History.RStep

/-!
# The cover invariant along a region history (Lemma I.4.10 (a), cover)

Assume `S.Good` and (H-T) in the form `n_k ≥ 4ρ_k + 21` for `1 ≤ k ≤ k₀`.  For `1 ≤ k ≤ k₀`:

* `window_inv'`: every component of `Z^pre_k` satisfies `BookInv k`, and after `R^{(k)}` also
  (the numerical invariant, as for `CounterHist.window_inv`);
* `cover_inv`: an `Active` or `Pending` component `Z` of `Z^pre_k` is covered by at most `ν(Z)` boxes
  of side `≤ crit_k`; the same after `R^{(k)}` (`cover_post`).

The restart outputs are point-spine components, hence boxes (`cover_of_pt`, Lemma I.4.8); the kept
ripe components have point spines (`Setting.ripe_facts`); (T1) and (T4) are `cover_step`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0)

/-- A small component of `Z^pre_k` (`k ≤ k₀`) of side `≤ crit_k` is one box of side `≤ crit_k`. -/
theorem box_of_small {k : ℕ} (hk1 : 1 ≤ k) (hk0 : k ≤ k0) (Z : H.Comp k)
    (hsm : IsSmall (Z.1 : Set (Torus S.d (n k))))
    (hsd : side (Z.1 : Set (Torus S.d (n k))) ≤ S.crit k) : CoveredBy S n k Z.1 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hg := H.stepGeom j
  have hc : critOpt S k0 (j + 1) = some (S.crit (j + 1)) := by simp [critOpt, hk0]
  have hZ' : Z.1 ∈ comps (S.omega (j + 1))
      (finOf ((H.step j).Zpre (S.omega (j + 1)) (critOpt S k0 (j + 1)))) := Z.2
  rw [hc] at hZ'
  have hZb : Z.1 ∈ comps (S.omega (j + 1)) (finOf (hullClosure (S.omega (j + 1)) (S.crit (j + 1))
      (H.step j).Z0)) := hZ'
  have hEq := hullClosure_box hg.hω2 (H.step j).Z0 hZb hsm hsd
  obtain ⟨a, s, hhull, -, hside⟩ := hull_eq_box (Finset.coe_nonempty.mpr (comp_nonempty Z.2)) hsm
  have hsi : ∀ i, s i ≤ S.crit (j + 1) := fun i =>
    le_trans (hside ▸ Finset.le_sup (f := s) (Finset.mem_univ i)) hsd
  refine ⟨{(a, s)}, by simp, by simpa using hsi, ?_⟩
  intro y hy
  refine Set.mem_iUnion₂.mpr ⟨(a, s), Finset.mem_singleton_self _, ?_⟩
  rw [← hhull, ← hEq]
  exact hy

/-- A component of `Z^pre_k` with a point spine is one box (Lemma I.4.8). -/
theorem cover_of_pt {k : ℕ} (hk1 : 1 ≤ k) (hk0 : k ≤ k0) (hT : 4 * S.rho k + 21 ≤ n k)
    (Z : H.Comp k) (h : (H.spine k Z).length = 0) : CoveredBy S n k Z.1 1 := by
  obtain ⟨hsm, hsd⟩ := (H.spine_point_iff hk1 hk0 hT Z).mp h
  exact H.box_of_small hk1 hk0 Z hsm hsd

variable (G : S.Good)

include G

theorem window_inv' : ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : H.Comp k,
    BookInv S k (H.bk k c) ∧ BookInv S k (S.postBook k0 k (H.bk k c)) ∧
      k < S.tStar (S.postBook k0 k (H.bk k c)) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro hk0 c
    have hinv : BookInv S 1 (H.bk 1 c) :=
      (G.step_classify (k := 0) (parts := H.parts 0 c)
        (f := fun c' => S.postBook k0 0 (H.bk 0 c'))
        (fun i _ => (H.F.isEmpty_comp_zero.false i).elim)
        (fun i _ => (H.F.isEmpty_comp_zero.false i).elim) (H.seed_pos 0 c)
        (Setting.BookRule.toTrue S (H.book_rule 0 c) hk0)).1
    have hr := G.rstep_inv (k0 := k0) (le_refl 1) hk0 hinv
    exact ⟨hinv, hr.1, hr.2.1⟩
  | succ k hk ih =>
    intro hk0 c
    have hinv : BookInv S (k + 1) (H.bk (k + 1) c) :=
      (G.step_classify (k := k) (parts := H.parts k c)
        (f := fun c' => S.postBook k0 k (H.bk k c'))
        (fun i _ => (ih (by omega) i).2.1) (fun i _ => (ih (by omega) i).2.2)
        (H.seed_pos k c) (Setting.BookRule.toTrue S (H.book_rule k c) hk0)).1
    have hr := G.rstep_inv (k0 := k0) (by omega) hk0 hinv
    exact ⟨hinv, hr.1, hr.2.1⟩

/-- The cover of the post-`R` books, given the cover of the pre-`R` books at the same scale. -/
theorem cover_post_of {k : ℕ} (hk1 : 1 ≤ k) (hk0 : k ≤ k0) (hT : 4 * S.rho k + 21 ≤ n k)
    (hcov : ∀ Z : H.Comp k, ((H.bk k Z).IsActive ∨ (H.bk k Z).IsPending) →
      CoveredBy S n k Z.1 (H.bk k Z).nu) (Z : H.Comp k)
    (h : (S.postBook k0 k (H.bk k Z)).IsActive ∨ (S.postBook k0 k (H.bk k Z)).IsPending) :
    CoveredBy S n k Z.1 (S.postBook k0 k (H.bk k Z)).nu := by
  by_cases hr : S.Ripe k (H.bk k Z)
  · rw [S.postBook_of_ripe hk1 hk0 hr]
    have hnu : ((H.bk k Z).kept k).nu = 1 := Book.nu_active rfl
    rw [hnu]
    have hinv := (H.window_inv' G k hk1 hk0 Z).1
    obtain ⟨hpt, -, -⟩ := S.ripe_facts hinv hr
    rw [H.bk_pt] at hpt
    exact H.cover_of_pt hk1 hk0 hT Z hpt
  · rw [S.postBook_of_not_ripe hr] at h ⊢
    exact hcov Z h

omit G in
theorem one_le_nu_of {k : ℕ} {b : Book} (hinv : BookInv S k b) (h : b.IsActive ∨ b.IsPending) :
    1 ≤ b.nu := by
  rcases h with ⟨q, ν, M, h⟩ | ⟨q, ν, h⟩
  · have := hinv.adm; rw [S.adm_active h] at this; rw [Book.nu_active h]; exact this.2.1
  · have := hinv.adm; rw [S.adm_pending h] at this; rw [Book.nu_pending h]; exact this.2.2.1

/-- One step of the cover invariant. -/
theorem cover_step_inv {k : ℕ} (hk0 : k + 1 ≤ k0) (hT : 4 * S.rho (k + 1) + 21 ≤ n (k + 1))
    (Z' : H.Comp (k + 1))
    (hinv : ∀ c ∈ H.parts k Z', BookInv S k (S.postBook k0 k (H.bk k c)) ∧
      k < S.tStar (S.postBook k0 k (H.bk k c)))
    (hpost : ∀ c ∈ H.parts k Z', ((S.postBook k0 k (H.bk k c)).IsActive ∨
      (S.postBook k0 k (H.bk k c)).IsPending) →
        CoveredBy S n k c.1 (S.postBook k0 k (H.bk k c)).nu)
    (hZ' : (H.bk (k + 1) Z').IsActive ∨ (H.bk (k + 1) Z').IsPending) :
    CoveredBy S n (k + 1) Z'.1 (H.bk (k + 1) Z').nu := by
  classical
  have hrule := H.book_rule k Z'
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := hrule.state hk0
  obtain ⟨-, hcase⟩ := G.step_classify (k := k) (parts := H.parts k Z')
    (f := fun c' => S.postBook k0 k (H.bk k c')) (fun i hi => (hinv i hi).1)
    (fun i hi => (hinv i hi).2) (H.seed_pos k Z') (Setting.BookRule.toTrue S hrule hk0)
  -- restart outputs
  have hrestart : (H.bk (k + 1) Z').st = WState.restart (k + 1) (H.bk (k + 1) Z').pt →
      (H.bk (k + 1) Z').nu = 1 → CoveredBy S n (k + 1) Z'.1 (H.bk (k + 1) Z').nu := by
    intro hst hnu
    have hp : (H.bk (k + 1) Z').pt := by
      by_contra hnp
      rw [WState.restart_npt hnp] at hst
      rcases hZ' with ⟨q, ν, M, h⟩ | ⟨q, ν, h⟩ <;> rw [hst] at h <;> cases h
    rw [hnu]
    refine H.cover_of_pt (by omega) hk0 hT Z' ?_
    rw [H.bk_pt] at hp
    exact hp
  -- sums of covers
  have hsum : (Z'.1 ∩ H.newCubes (k + 1)).card = 0 →
      (∀ c ∈ H.parts k Z', (S.postBook k0 k (H.bk k c)).IsActive ∨
        (S.postBook k0 k (H.bk k c)).IsPending) →
      CoveredBy S n (k + 1) Z'.1 (∑ c ∈ H.parts k Z', (S.postBook k0 k (H.bk k c)).nu) := by
    intro hr hact
    refine H.cover_step k Z' (Finset.card_eq_zero.mp hr) (fun c => (S.postBook k0 k (H.bk k c)).nu)
      (fun c hc => one_le_nu_of (hinv c hc).1 (hact c hc)) (fun c hc => hpost c hc (hact c hc))
  cases hcase with
  | shadow i hparts hr hle hge hnu hbank =>
    have hi : i ∈ H.parts k Z' := by rw [hparts]; exact Finset.mem_singleton_self i
    by_cases hact : (S.postBook k0 k (H.bk k i)).IsActive ∨ (S.postBook k0 k (H.bk k i)).IsPending
    · have := hsum hr (fun c hc => by rw [hparts, Finset.mem_singleton] at hc; subst hc; exact hact)
      rw [hparts, Finset.sum_singleton] at this
      rw [hnu]
      exact this
    · -- the part is `Pre`
      have hpre : (S.postBook k0 k (H.bk k i)).st = .pre := by
        rcases Book.cases_st (S.postBook k0 k (H.bk k i)) with h | h | h
        · exact h
        · exact absurd (Or.inr h) hact
        · exact absurd (Or.inl h) hact
      have hshadow := hs2 hr i hparts
      have hp : (H.bk (k + 1) Z').pt := by
        by_contra hnp
        simp only [WState.shadow, hpre, hnp, ↓reduceIte] at hshadow
        rcases hZ' with ⟨q, ν, M, h⟩ | ⟨q, ν, h⟩ <;> rw [hshadow] at h <;> cases h
      have hn1 : (H.bk (k + 1) Z').nu = 1 := by rw [hnu]; exact Book.nu_pre hpre
      rw [hn1]
      refine H.cover_of_pt (by omega) hk0 hT Z' ?_
      rw [H.bk_pt] at hp
      exact hp
  | new hr hf => exact hrestart (hs1 hr) hf.2.2.2.1
  | mergePre hr hcard hpre hf => exact hrestart (hs3 hr hcard hpre) hf.2.2.2.1
  | overflow hr hcard hnpre hcap hf => exact hrestart (hs5 hr hcard hnpre hcap) hf.2.2.2.1
  | mergeCap hr hcard hnpre hcap hf =>
    have hact : ∀ c ∈ H.parts k Z', (S.postBook k0 k (H.bk k c)).IsActive ∨
        (S.postBook k0 k (H.bk k c)).IsPending := by
      intro c hc
      rcases Book.cases_st (S.postBook k0 k (H.bk k c)) with h | h | h
      · exact absurd h (hnpre c hc)
      · exact Or.inr h
      · exact Or.inl h
    have := hsum hr hact
    rw [hf.nu_eq]
    exact this

/-- **Lemma I.4.10 (a), cover**: for `1 ≤ k ≤ k₀`, an `Active` or `Pending` component of `Z^pre_k`
is covered by at most `ν(Z)` boxes of side `≤ crit_k`. -/
theorem cover_inv (hT : ∀ k, 1 ≤ k → k ≤ k0 → 4 * S.rho k + 21 ≤ n k) :
    ∀ k, 1 ≤ k → k ≤ k0 → ∀ Z : H.Comp k, ((H.bk k Z).IsActive ∨ (H.bk k Z).IsPending) →
      CoveredBy S n k Z.1 (H.bk k Z).nu := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro hk0 Z hZ
    exact H.cover_step_inv G (k := 0) hk0 (hT 1 le_rfl hk0) Z
      (fun c _ => (H.F.isEmpty_comp_zero.false c).elim)
      (fun c _ => (H.F.isEmpty_comp_zero.false c).elim) hZ
  | succ k hk ih =>
    intro hk0 Z hZ
    refine H.cover_step_inv G (k := k) hk0 (hT (k + 1) (by omega) hk0) Z
      (fun c _ => ⟨(H.window_inv' G k hk (by omega) c).2.1, (H.window_inv' G k hk (by omega) c).2.2⟩)
      (fun c _ => H.cover_post_of G hk (by omega) (hT k hk (by omega)) (ih (by omega)) c) hZ

/-- The cover after `R^{(k)}`. -/
theorem cover_post (hT : ∀ k, 1 ≤ k → k ≤ k0 → 4 * S.rho k + 21 ≤ n k) {k : ℕ} (hk1 : 1 ≤ k)
    (hk0 : k ≤ k0) (Z : H.Comp k)
    (h : (S.postBook k0 k (H.bk k Z)).IsActive ∨ (S.postBook k0 k (H.bk k Z)).IsPending) :
    CoveredBy S n k Z.1 (S.postBook k0 k (H.bk k Z)).nu :=
  H.cover_post_of G hk1 hk0 (hT k hk1 hk0) (H.cover_inv G hT k hk1 hk0) Z h

end RegionHistory

end Balaban.LargeField
