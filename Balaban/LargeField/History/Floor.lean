module

public import Balaban.LargeField.History.StepKinds

/-!
# The floor invariant along descent and Lemma I.4.13 (a)

* `floor_desc_post`, `floor_desc_pre` (Lemma I.4.12): if the component `Y` of scale `a` is `Pre` or
  has core `≥ m` (`m ≤ a + 1`), so is every descendant on the path to `Z` (before and after `R`).
* For `Z` of scale `k ≤ k₀` that is `Active` or `Pending` with core `q`, and an ancestor `Y` of `Z`
  at scale `s` (Lemma I.4.13 (a)):
  `nonpre_of_desc` (`q ≤ s ≤ k`: `Y` is `Active` or `Pending`),
  `live_of_desc` (`q < s ≤ k`: the step into `Y` is live, so (T1) or (T4)),
  `not_ripe_of_desc` (`q < s < k`: `Y` is not ripe, so neither removed nor kept).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  {H : RegionHistory S n R k0}

/-- The step into a component of `Z^pre_s` is live (`False` for `s = 0`). -/
def LiveAt : ∀ s : ℕ, H.Comp s → Prop
  | 0, _ => False
  | k + 1, Y => H.Live k Y

section Floor

variable (G : S.Good)

include G

/-- Lemma I.4.12 along a path, after `R`. -/
theorem floor_desc_post {a b : ℕ} {Y : H.Comp a} {Z : H.Comp b} (h : H.Desc a b Y Z)
    (hb : b ≤ k0) {m : ℕ} (hm : m ≤ a + 1) (hF : (H.pb a Y).Fl m) : (H.pb b Z).Fl m := by
  induction h with
  | refl => exact hF
  | step b' _ Y' Y'' hd hrem hs ih =>
    have hle := hd.le
    have ih' := ih (by omega) hF
    have hmem : Y' ∈ H.parts b' Y'' := (H.mem_parts b' Y' Y'').mpr ⟨hrem, hs⟩
    have h1 := floor_step G hb Y'' (by omega) hmem ih'
    exact floor_post G (by omega) hb (by omega) Y'' h1

/-- Lemma I.4.12 along a path, before `R` at the final scale (`a < b`). -/
theorem floor_desc_pre {a b : ℕ} {Y : H.Comp a} {Z : H.Comp b} (h : H.Desc a b Y Z)
    (hab : a < b) (hb : b ≤ k0) {m : ℕ} (hm : m ≤ a + 1) (hF : (H.pb a Y).Fl m) :
    (H.bk b Z).Fl m := by
  cases h with
  | refl => omega
  | step b' _ Y' Z' hd hrem hs =>
    have hle := hd.le
    have ih' := floor_desc_post G hd (by omega) hm hF
    have hmem : Y' ∈ H.parts b' Z' := (H.mem_parts b' Y' Z').mpr ⟨hrem, hs⟩
    exact floor_step G hb Z' (by omega) hmem ih'

variable {k : ℕ} {Z : H.Comp k}

omit G in
theorem not_pre_of_ap {s : ℕ} {Y : H.Comp s} (hZ : (H.bk s Y).IsActive ∨ (H.bk s Y).IsPending)
    (hpre : (H.bk s Y).st = .pre) : False := by
  rcases hZ with h' | h'
  · exact Book.not_pre_of_active h' hpre
  · exact Book.not_pre_of_pending h' hpre

omit G in
theorem not_fl_of_ap {s : ℕ} {Y : H.Comp s} (hZ : (H.bk s Y).IsActive ∨ (H.bk s Y).IsPending)
    {m : ℕ} (hF : (H.bk s Y).Fl m) : m ≤ (H.bk s Y).q := by
  rcases hF with h | ⟨-, h⟩
  · exact (not_pre_of_ap hZ h).elim
  · exact h

/-- A `Pre` component is not changed by `R`. -/
theorem pb_of_pre {s : ℕ} {Y : H.Comp s} (h : (H.bk s Y).st = .pre) : H.pb s Y = H.bk s Y :=
  S.postBook_of_not_ripe fun hr => Book.not_active_of_pre h hr.1

/-- Lemma I.4.13 (a): the ancestors at scales `s ≥ q` of an `Active` or `Pending` component are
`Active` or `Pending`. -/
theorem nonpre_of_desc (hk0 : k ≤ k0) (hZ : (H.bk k Z).IsActive ∨ (H.bk k Z).IsPending)
    {s : ℕ} {Y : H.Comp s} (hd : H.Desc s k Y Z) (hq : (H.bk k Z).q ≤ s) :
    (H.bk s Y).IsActive ∨ (H.bk s Y).IsPending := by
  have hle := hd.le
  rcases Book.cases_st (H.bk s Y) with hpre | hpend | hact
  · exfalso
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · subst heq
      have : Z = Y := hd.unique (Desc.refl Y)
      subst this
      exact not_pre_of_ap hZ hpre
    · have hF : (H.pb s Y).Fl (s + 1) := Book.fl_pre (by rw [pb_of_pre G hpre]; exact hpre)
      have := not_fl_of_ap hZ (floor_desc_pre G hd hlt hk0 le_rfl hF)
      omega
  · exact Or.inr hpend
  · exact Or.inl hact

/-- Lemma I.4.13 (a): the steps into the ancestors at scales `s ∈ (q, k]` are live, so (T1) or
(T4). -/
theorem live_of_desc (hk0 : k ≤ k0) (hZ : (H.bk k Z).IsActive ∨ (H.bk k Z).IsPending)
    {s : ℕ} {Y : H.Comp s} (hd : H.Desc s k Y Z) (hq : (H.bk k Z).q < s) : LiveAt s Y := by
  have hle := hd.le
  obtain ⟨κ, rfl⟩ : ∃ κ, s = κ + 1 := ⟨s - 1, by omega⟩
  rcases live_or_floor G (show κ + 1 ≤ k0 by omega) Y with hL | hF
  · exact hL
  · exfalso
    have hq' : (H.bk k Z).q < κ + 1 := hq
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · subst heq
      have : Z = Y := hd.unique (Desc.refl Y)
      subst this
      have := not_fl_of_ap hZ hF
      omega
    · have hF' := floor_post G (by omega) (by omega) le_rfl Y hF
      have := not_fl_of_ap hZ (floor_desc_pre G hd hlt hk0 (by omega) hF')
      omega

/-- Lemma I.4.13 (a): no ancestor at a scale in `(q, k)` is ripe (so none is removed or kept). -/
theorem not_ripe_of_desc (hk0 : k ≤ k0) (hZ : (H.bk k Z).IsActive ∨ (H.bk k Z).IsPending)
    {s : ℕ} {Y : H.Comp s} (hd : H.Desc s k Y Z) (hq : (H.bk k Z).q < s) (hsk : s < k) :
    ¬ S.Ripe s (H.bk s Y) := by
  intro hr
  have hpb : H.pb s Y = (H.bk s Y).kept s := S.postBook_of_ripe (by omega) (by omega) hr
  have hF : (H.pb s Y).Fl s := by
    rw [hpb]
    exact Book.fl_active (b := (H.bk s Y).kept s) (q := s) (ν := 1) (M := ∅) rfl le_rfl
  have := not_fl_of_ap hZ (floor_desc_pre G hd hsk hk0 (by omega) hF)
  omega

end Floor

end RegionHistory

end Balaban.LargeField
