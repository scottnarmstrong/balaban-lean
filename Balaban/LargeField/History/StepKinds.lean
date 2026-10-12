module

public import Balaban.LargeField.History.FlowInv
public import Balaban.LargeField.History.Descent
import Mathlib.Tactic.Linarith

/-!
# The kinds of steps along a region history (Lemmas I.4.10, I.4.12)

For `k + 1 ≤ k₀` every component of `Z^pre_{k+1}` falls under one of the cases (T1)–(T5)
(`step_facts`).  A step is *live* when no restart occurs (no new cube, no `Pre` part, no overflow):
it is then a pure shadow of an `Active` or `Pending` part, or a merge within the cap (T4).

* `floor_step`, `floor_post`: the floor invariant of Lemma I.4.12 for one step and for `R^{(k)}`:
  if one part is `Pre` or has core `≥ m`, then the component is `Pre` or has core `≥ m`
  (for `m ≤ k + 1`);
* `live_or_floor`: a step is live, or its output is `Pre` or has core `k + 1`;
* `Live.nu_eq`: the number of pieces adds up over a live step;
* `recInv_step`, `recInv_base`: the merge record `ξ` is kept, or released with core `> ξ + h_ξ`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

/-- The floor predicate: `Pre`, or `Active`/`Pending` with core `≥ m`. -/
def Book.Fl (m : ℕ) (b : Book) : Prop := b.st = .pre ∨ ((b.IsActive ∨ b.IsPending) ∧ m ≤ b.q)

/-- The merge record `ξ` is still recorded in `𝓜`, or has been released with core `> ξ + h_ξ`. -/
def Setting.RecInv (S : Setting) (ξ : ℕ) (b : Book) : Prop := ξ ∈ b.M ∨ ξ + S.h ξ < b.q

namespace Book

variable {b : Book} {m q ν : ℕ} {M : Finset ℕ}

theorem Fl.mono {m' : ℕ} (h : b.Fl m) (hm : m' ≤ m) : b.Fl m' := by
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, hm.trans h'⟩

theorem fl_of_nonpre (h : b.IsActive ∨ b.IsPending) : b.Fl b.q := Or.inr ⟨h, le_rfl⟩

theorem fl_pre (h : b.st = .pre) : b.Fl m := Or.inl h

theorem fl_active (h : b.st = .active q ν M) (hm : m ≤ q) : b.Fl m :=
  Or.inr ⟨Or.inl (Book.isActive_of h), by rw [Book.q_active h]; exact hm⟩

theorem fl_pending (h : b.st = .pending q ν) (hm : m ≤ q) : b.Fl m :=
  Or.inr ⟨Or.inr (Book.isPending_of h), by rw [Book.q_pending h]; exact hm⟩

theorem fl_restart {μ : ℕ} (hm : m ≤ μ) {pt : Prop} (h : b.st = WState.restart μ pt) : b.Fl m := by
  by_cases hp : pt
  · rw [WState.restart_pt hp] at h; exact fl_active h hm
  · rw [WState.restart_npt hp] at h; exact fl_pre h

theorem fl_shadow {μ : ℕ} (hm : m ≤ μ) {pt : Prop} {b0 b : Book}
    (h : b.st = WState.shadow μ pt b0) (hF : b0.Fl m) : b.Fl m := by
  rcases hF with hpre | ⟨hact, hq⟩
  · by_cases hp : pt
    · rw [WState.shadow_pre_pt hpre hp] at h; exact fl_active h hm
    · rw [WState.shadow_pre_npt hpre hp] at h; exact fl_pre h
  · rcases hact with ⟨q0, ν0, M0, h0⟩ | ⟨q0, ν0, h0⟩
    · rw [Book.q_active h0] at hq
      rw [WState.shadow_active h0] at h; exact fl_active h hq
    · rw [Book.q_pending h0] at hq
      by_cases hlt : μ < q0
      · rw [WState.shadow_pending_lt h0 hlt] at h; exact fl_pending h hq
      · rw [WState.shadow_pending_ge h0 hlt] at h; exact fl_active h hq

/-- A pure shadow of an `Active` or `Pending` book keeps the merge record and the core. -/
theorem shadow_M_q {μ : ℕ} {pt : Prop} {b0 b : Book} (h : b.st = WState.shadow μ pt b0)
    (hb : b0.IsActive ∨ b0.IsPending) : b.M = b0.M ∧ b.q = b0.q := by
  rcases hb with ⟨q0, ν0, M0, h0⟩ | ⟨q0, ν0, h0⟩
  · rw [WState.shadow_active h0] at h
    rw [Book.M_active h, Book.M_active h0, Book.q_active h, Book.q_active h0]
    exact ⟨rfl, rfl⟩
  · by_cases hlt : μ < q0
    · rw [WState.shadow_pending_lt h0 hlt] at h
      rw [Book.M_pending h, Book.M_pending h0, Book.q_pending h, Book.q_pending h0]
      exact ⟨rfl, rfl⟩
    · rw [WState.shadow_pending_ge h0 hlt] at h
      rw [Book.M_active h, Book.M_pending h0, Book.q_active h, Book.q_pending h0]
      exact ⟨rfl, rfl⟩

end Book

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K)

/-- The post-`R` book of a component of `Z^pre_k`. -/
noncomputable abbrev pb (k : ℕ) (c : H.Comp k) : Book := S.postBook k0 k (H.bk k c)

/-- The number of new cubes of a component of `Z^pre_{k+1}`. -/
noncomputable abbrev nr (k : ℕ) (Z' : H.Comp (k + 1)) : ℕ := (Z'.1 ∩ H.newCubes (k + 1)).card

/-- A live step: no new cube, all parts `Active` or `Pending`, one part or a merge within the cap. -/
def Live (k : ℕ) (Z' : H.Comp (k + 1)) : Prop :=
  H.nr k Z' = 0 ∧ (∀ c ∈ H.parts k Z', (H.pb k c).IsActive ∨ (H.pb k c).IsPending) ∧
    ((H.parts k Z').card = 1 ∨ ∑ c ∈ H.parts k Z', (H.pb k c).nu ≤ S.numax (k + 1))

variable {H}

section Facts

variable (G : S.Good)

include G

/-- The invariant, the case of the step, and the state rules, for `k + 1 ≤ k₀`. -/
theorem step_facts {k : ℕ} (hk0 : k + 1 ≤ k0) (hkK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) :
    BookInv S (k + 1) (H.bk (k + 1) Z') ∧
      StepCase S k (H.parts k Z') (fun c => H.pb k c) (H.nr k Z') (H.bk (k + 1) Z') ∧
      S.StateRule (k + 1) (H.parts k Z') (fun c => H.pb k c) (H.nr k Z')
        (H.bk (k + 1) Z').pt (H.bk (k + 1) Z').s (H.bk (k + 1) Z').st := by
  have hrule := H.book_rule (k := k) (by omega) Z'
  have hinvp : ∀ c ∈ H.parts k Z', BookInv S k (H.pb k c) ∧ k < S.tStar (H.pb k c) := by
    intro c _
    cases k with
    | zero => exact (H.F.isEmpty_comp_zero.false c).elim
    | succ k =>
      exact ⟨(H.window_inv' G (k + 1) (by omega) (by omega) (by omega) c).2.1,
        (H.window_inv' G (k + 1) (by omega) (by omega) (by omega) c).2.2⟩
  obtain ⟨hinv, hcase⟩ := G.step_classify (k := k) (parts := H.parts k Z')
    (f := fun c => H.pb k c) (fun i hi => (hinvp i hi).1) (fun i hi => (hinvp i hi).2)
    (H.seed_pos (k := k) (by omega) Z') (Setting.BookRule.toTrue S hrule hk0)
  exact ⟨hinv, hcase, hrule.state hk0⟩

/-- The floor invariant of Lemma I.4.12 for one step. -/
theorem floor_step {k : ℕ} (hk0 : k + 1 ≤ k0) (hkK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) {m : ℕ} (hm : m ≤ k + 1)
    {c : H.Comp k} (hc : c ∈ H.parts k Z') (hF : (H.pb k c).Fl m) : (H.bk (k + 1) Z').Fl m := by
  obtain ⟨-, hcase, hs1, hs2, hs3, hs4, hs5⟩ := H.step_facts G hk0 hkK Z'
  cases hcase with
  | shadow i hparts hr hle hge hnu hbank =>
    have hci : c = i := by rw [hparts] at hc; simpa using hc
    subst hci
    exact Book.fl_shadow hm (hs2 hr c hparts) hF
  | new hr hf => exact Book.fl_restart hm (hs1 hr)
  | mergePre hr hcard hpre hf => exact Book.fl_restart hm (hs3 hr hcard hpre)
  | overflow hr hcard hnpre hcap hf => exact Book.fl_restart hm (hs5 hr hcard hnpre hcap)
  | mergeCap hr hcard hnpre hcap hf =>
    have hst := hs4 hr hcard hnpre hcap
    have hcn : (H.pb k c).st ≠ .pre := hnpre c hc
    have hq : m ≤ (H.pb k c).q := by
      rcases hF with h | ⟨-, h⟩
      · exact absurd h hcn
      · exact h
    have hqq : (H.pb k c).q ≤ S.t4q (k + 1) (H.parts k Z') (fun c => H.pb k c)
        (H.bk (k + 1) Z').s :=
      (Finset.le_sup (f := fun c => (H.pb k c).q) hc).trans hf.Q_le_q
    unfold Setting.t4State at hst
    split_ifs at hst with hcond
    · exact Book.fl_active hst (hq.trans hqq)
    · exact Book.fl_pending hst (hq.trans hqq)

/-- The floor invariant for `R^{(k)}`. -/
theorem floor_post {k : ℕ} (hk1 : 1 ≤ k) (hk0 : k ≤ k0) {m : ℕ} (hm : m ≤ k) (c : H.Comp k)
    (hF : (H.bk k c).Fl m) : (H.pb k c).Fl m := by
  by_cases hr : S.Ripe k (H.bk k c)
  · have : H.pb k c = (H.bk k c).kept k := S.postBook_of_ripe hk1 hk0 hr
    rw [this]
    exact Book.fl_active (b := (H.bk k c).kept k) (q := k) (ν := 1) (M := ∅) rfl hm
  · rw [show H.pb k c = H.bk k c from S.postBook_of_not_ripe hr]
    exact hF

/-- A step is live, or its output is `Pre` or has core `k + 1`. -/
theorem live_or_floor {k : ℕ} (hk0 : k + 1 ≤ k0) (hkK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) :
    H.Live k Z' ∨ (H.bk (k + 1) Z').Fl (k + 1) := by
  obtain ⟨-, hcase, hs1, hs2, hs3, hs4, hs5⟩ := H.step_facts G hk0 hkK Z'
  cases hcase with
  | shadow i hparts hr hle hge hnu hbank =>
    have hmem : i ∈ H.parts k Z' := by rw [hparts]; exact Finset.mem_singleton_self i
    by_cases hact : (H.pb k i).IsActive ∨ (H.pb k i).IsPending
    · left
      refine ⟨hr, fun c hc => ?_, Or.inl (by rw [hparts]; simp)⟩
      have : c = i := by rw [hparts] at hc; simpa using hc
      subst this; exact hact
    · right
      have hpre : (H.pb k i).st = .pre := by
        rcases Book.cases_st (H.pb k i) with h | h | h
        · exact h
        · exact absurd (Or.inr h) hact
        · exact absurd (Or.inl h) hact
      exact Book.fl_shadow le_rfl (hs2 hr i hparts) (Book.fl_pre hpre)
  | new hr hf => exact Or.inr (Book.fl_restart le_rfl (hs1 hr))
  | mergePre hr hcard hpre hf => exact Or.inr (Book.fl_restart le_rfl (hs3 hr hcard hpre))
  | overflow hr hcard hnpre hcap hf => exact Or.inr (Book.fl_restart le_rfl (hs5 hr hcard hnpre hcap))
  | mergeCap hr hcard hnpre hcap hf =>
    left
    refine ⟨hr, fun c hc => ?_, Or.inr hcap⟩
    rcases Book.cases_st (H.pb k c) with h | h | h
    · exact absurd h (hnpre c hc)
    · exact Or.inr h
    · exact Or.inl h

/-- The number of pieces adds up over a live step. -/
theorem Live.nu_eq {k : ℕ} (hk0 : k + 1 ≤ k0) (hkK : k + 1 ≤ K) {Z' : H.Comp (k + 1)} (hL : H.Live k Z') :
    (H.bk (k + 1) Z').nu = ∑ c ∈ H.parts k Z', (H.pb k c).nu := by
  obtain ⟨hr, hact, hcap⟩ := hL
  obtain ⟨-, hcase, -⟩ := H.step_facts G hk0 hkK Z'
  cases hcase with
  | shadow i hparts hr' hle hge hnu hbank => rw [hnu, hparts, Finset.sum_singleton]
  | new hr' hf => omega
  | mergePre hr' hcard hpre hf =>
    obtain ⟨i, hi, hpre⟩ := hpre
    rcases hact i hi with h | h
    · exact absurd hpre (Book.not_pre_of_active h)
    · exact absurd hpre (Book.not_pre_of_pending h)
  | overflow hr' hcard hnpre hcap' hf =>
    rcases hcap with h | h
    · omega
    · omega
  | mergeCap hr' hcard hnpre hcap' hf => exact hf.nu_eq

/-- At a merge, the record `μ` is kept or released with core `> μ + h_μ`. -/
theorem t4_recInv {ι : Type*} {k : ℕ} {parts : Finset ι} {f : ι → Book} {b' : Book}
    (hf : T4Facts S k parts f b') : S.RecInv (k + 1) b' := by
  have hnb := G.ok.q'_not_blocked (Setting.t4E (k + 1) parts f)
    (S.t4t0 parts f b'.s)
  have hq : b'.q = S.k1 (S.Tmin (Setting.t4E (k + 1) parts f) (S.t4t0 parts f b'.s)) := hf.q_eq
  have hmem : (k + 1) ∈ Setting.t4E (k + 1) parts f := by
    simp [Setting.t4E]
  have : ¬ ((k + 1) ≤ b'.q ∧ b'.q ≤ (k + 1) + S.h (k + 1)) := by
    rintro ⟨h1, h2⟩
    rw [hq] at h1 h2
    exact hnb ⟨k + 1, hmem, h1, h2⟩
  by_cases hlt : b'.q < k + 1
  · left
    rw [hf.M_eq]
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    rw [← hf.q_eq]; exact hlt
  · right
    push Not at hlt
    by_contra hcon
    exact this ⟨hlt, not_lt.mp hcon⟩

/-- The merge record `ξ` is kept or released with core `> ξ + h_ξ`, over a live step. -/
theorem recInv_step {k : ℕ} (hk0 : k + 1 ≤ k0) (hkK : k + 1 ≤ K) {Z' : H.Comp (k + 1)} (hL : H.Live k Z') {ξ : ℕ}
    {c : H.Comp k} (hc : c ∈ H.parts k Z') (hR : S.RecInv ξ (H.pb k c)) :
    S.RecInv ξ (H.bk (k + 1) Z') := by
  obtain ⟨hr, hact, hcap⟩ := hL
  obtain ⟨-, hcase, hs1, hs2, hs3, hs4, hs5⟩ := H.step_facts G hk0 hkK Z'
  cases hcase with
  | shadow i hparts hr' hle hge hnu hbank =>
    have hci : c = i := by rw [hparts] at hc; simpa using hc
    subst hci
    obtain ⟨hM, hq⟩ := Book.shadow_M_q (hs2 hr' c hparts) (hact c hc)
    unfold Setting.RecInv at hR ⊢
    rw [hM, hq]; exact hR
  | new hr' hf => omega
  | mergePre hr' hcard hpre hf =>
    obtain ⟨i, hi, hpre⟩ := hpre
    rcases hact i hi with h | h
    · exact absurd hpre (Book.not_pre_of_active h)
    · exact absurd hpre (Book.not_pre_of_pending h)
  | overflow hr' hcard hnpre hcap' hf => rcases hcap with h | h <;> omega
  | mergeCap hr' hcard hnpre hcap' hf =>
    have hnb := G.ok.q'_not_blocked (Setting.t4E (k + 1) (H.parts k Z') (fun c => H.pb k c))
      (S.t4t0 (H.parts k Z') (fun c => H.pb k c) (H.bk (k + 1) Z').s)
    have hq : (H.bk (k + 1) Z').q = S.k1 (S.Tmin (Setting.t4E (k + 1) (H.parts k Z')
        (fun c => H.pb k c)) (S.t4t0 (H.parts k Z') (fun c => H.pb k c)
          (H.bk (k + 1) Z').s)) := hf.q_eq
    have hqq : (H.pb k c).q ≤ (H.bk (k + 1) Z').q :=
      ((Finset.le_sup (f := fun c => (H.pb k c).q) hc).trans hf.Q_le_q).trans hf.q_eq.symm.le
    rcases hR with hR | hR
    · have hξE : ξ ∈ Setting.t4E (k + 1) (H.parts k Z') (fun c => H.pb k c) := by
        unfold Setting.t4E
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨c, hc, hR⟩))
      by_cases hlt : (H.bk (k + 1) Z').q < ξ
      · left
        rw [hf.M_eq]
        refine Finset.mem_filter.mpr ⟨hξE, ?_⟩
        rw [← hf.q_eq]; exact hlt
      · right
        push Not at hlt
        by_contra hcon
        rw [hq] at hlt
        exact hnb ⟨ξ, hξE, hlt, by rw [← hq]; exact not_lt.mp hcon⟩
    · right; omega

end Facts

end RegionHistory

end Balaban.LargeField
