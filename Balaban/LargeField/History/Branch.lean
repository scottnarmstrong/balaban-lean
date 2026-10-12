module

public import Balaban.LargeField.History.WindowCover

/-!
# Branches of the lineage: entries, shadow chains (Lemma I.4.13 (d), (e4))

* `ShDesc a b W Y`: a chain of pure shadows from `W` (scale `a`) to `Y` (scale `b`), through
  `Active`/`Pending`, non-ripe components with no new cube;
* `ShDesc.len_le`, `ShDesc.len_zero`: the spine length is divided by `L` at each pure shadow, and
  a spine of length `≤ L` becomes a point at the next pure shadow;
* `back`: every `Active` or `Pending` component of scale `κ ≤ k₀` is the pure-shadow descendant of
  a component `W` that is a point (length `0`) or a merge (T4) with its record bookkeeping;
* `exists_entry` (Lemma I.4.13 (d)): every `Active` or `Pending` component has an ancestor that is
  a certified entry: a point spine, post-`R` state `Active(e, 1, ∅)`, one box of side `≤ crit_e`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  {H : RegionHistory S n R k0}

variable (H) in
/-- A chain of pure shadows. -/
inductive ShDesc (a : ℕ) : (b : ℕ) → H.Comp a → H.Comp b → Prop
  | refl (Y : H.Comp a) : ShDesc a a Y Y
  | step (b : ℕ) (Y : H.Comp a) (Y' : H.Comp b) (Y'' : H.Comp (b + 1)) :
      ShDesc a b Y Y' → (h : Y'.1 ∉ H.rem b) → H.succ b Y' h = Y'' →
        H.parts b Y'' = {Y'} → H.nr b Y'' = 0 →
        ((H.pb b Y').IsActive ∨ (H.pb b Y').IsPending) → ¬ S.Ripe b (H.bk b Y') →
        ShDesc a (b + 1) Y Y''

theorem ShDesc.toDesc {a b : ℕ} {W : H.Comp a} {Y : H.Comp b} (h : H.ShDesc a b W Y) :
    H.Desc a b W Y := by
  induction h with
  | refl => exact Desc.refl _
  | step b _ Y' Y'' _ hrem hs _ _ _ _ ih => exact Desc.step b _ Y' Y'' ih hrem hs

theorem ShDesc.le {a b : ℕ} {W : H.Comp a} {Y : H.Comp b} (h : H.ShDesc a b W Y) : a ≤ b :=
  h.toDesc.le

/-- One pure shadow: the length is divided by `L`, and a short spine becomes a point. -/
theorem shadow_len {k : ℕ} {Y'' : H.Comp (k + 1)} {c : H.Comp k} (hparts : H.parts k Y'' = {c})
    (hr : H.nr k Y'' = 0) :
    (H.bk (k + 1) Y'').len ≤ (H.bk k c).len / S.L ∧
      ((H.bk k c).len ≤ S.L → (H.bk (k + 1) Y'').len = 0) := by
  have hrule := H.book_rule k Y''
  have hlen := hrule.len_gen
  have hr' : (Y''.1 ∩ H.newCubes (k + 1)).card = 0 := hr
  rw [hparts, hr'] at hlen
  simp only [Finset.sum_singleton, Finset.card_singleton, add_zero, Nat.cast_one, sub_self,
    zero_mul, add_zero] at hlen
  have hl : (S.postBook k0 k (H.bk k c)).len = (H.bk k c).len := by
    unfold Setting.postBook; split_ifs <;> rfl
  rw [hl] at hlen
  refine ⟨hlen, fun hc => ?_⟩
  obtain ⟨h1, -⟩ := hrule.shadow hr c hparts
  have hpt : (H.bk (k + 1) Y'').pt := by
    by_contra hnp
    have := h1 hnp
    rw [hl] at this
    exact absurd hc (not_le.mpr (by exact_mod_cast this))
  exact hrule.pt_len hpt

variable (G : S.Good)

include G

/-- The length along a chain of pure shadows. -/
theorem ShDesc.len_le {a b : ℕ} {W : H.Comp a} {Y : H.Comp b} (h : H.ShDesc a b W Y) :
    (H.bk b Y).len ≤ (H.bk a W).len / (S.L : ℝ) ^ (b - a) := by
  have hL : (1 : ℝ) < S.L := by linarith [G.ok.cast_L_ge]
  induction h with
  | refl => simp
  | step b' W' Y' Y'' hd hrem hs hparts hr _ _ ih =>
    have hle := hd.le
    obtain ⟨h1, -⟩ := shadow_len hparts hr
    have e : b' + 1 - a = (b' - a) + 1 := by omega
    rw [e, pow_succ]
    calc (H.bk (b' + 1) Y'').len ≤ (H.bk b' Y').len / S.L := h1
      _ ≤ ((H.bk a W').len / (S.L : ℝ) ^ (b' - a)) / S.L := by gcongr
      _ = _ := by rw [div_div]

/-- A spine of length `≤ L^t` becomes a point after `t ≥ 1` pure shadows. -/
theorem ShDesc.len_zero {a b : ℕ} {W : H.Comp a} {Y : H.Comp b} (h : H.ShDesc a b W Y)
    (hab : a < b) (hW : (H.bk a W).len ≤ (S.L : ℝ) ^ (b - a)) : (H.bk b Y).len = 0 := by
  have hL : (1 : ℝ) < S.L := by linarith [G.ok.cast_L_ge]
  cases h with
  | refl => omega
  | step b' _ Y' _ hd hrem hs hparts hr _ _ =>
    obtain ⟨-, h2⟩ := shadow_len hparts hr
    refine h2 ?_
    have h3 := ShDesc.len_le G hd
    have hpos : (0 : ℝ) < (S.L : ℝ) ^ (b' - a) := by positivity
    have e : b' + 1 - a = (b' - a) + 1 := by have := hd.le; omega
    rw [e, pow_succ] at hW
    refine h3.trans ?_
    rw [div_le_iff₀ hpos]
    linarith

/-- What the last event of a branch looks like: a point, or a merge within the cap with its record
bookkeeping and its length bound. -/
def BackKind (ξ : ℕ) (W : H.Comp ξ) : Prop :=
  (H.bk ξ W).len = 0 ∨
    (S.RecInv ξ (H.bk ξ W) ∧ (H.bk ξ W).len ≤ S.numax ξ * S.D ξ ∧ ¬ S.Ripe ξ (H.bk ξ W))

omit G in
theorem len_zero_of_ripe {k : ℕ} {b : Book} (hb : BookInv S k b) (hr : S.Ripe k b) : b.len = 0 :=
  (S.ripe_facts hb hr).2.1

omit G in
theorem not_isEmpty_comp {k : ℕ} (Y : H.Comp k) (hk : k ≤ k0) : 1 ≤ k := by
  by_contra h
  have : k = 0 := by omega
  subst this
  exact (H.F.isEmpty_comp_zero.false Y).elim

/-- **Branches of the lineage**: every `Active` or `Pending` component of scale `κ ≤ k₀` is the
pure-shadow descendant of a component `W` that is a point or a merge within the cap. -/
theorem back : ∀ κ (Y : H.Comp κ), κ ≤ k0 → ((H.bk κ Y).IsActive ∨ (H.bk κ Y).IsPending) →
    ∃ ξ, ∃ W : H.Comp ξ, H.ShDesc ξ κ W Y ∧ BackKind ξ W := by
  intro κ
  induction κ with
  | zero => intro Y; exact (H.F.isEmpty_comp_zero.false Y).elim
  | succ k ih =>
    intro Y hk0 hact
    obtain ⟨hinv, hcase, hs1, hs2, hs3, hs4, hs5⟩ := H.step_facts G hk0 Y
    have hrestart : (H.bk (k + 1) Y).st = WState.restart (k + 1) (H.bk (k + 1) Y).pt →
        (H.bk (k + 1) Y).len = 0 := by
      intro hst
      have hp : (H.bk (k + 1) Y).pt := by
        by_contra hnp
        rw [WState.restart_npt hnp] at hst
        rcases hact with h | h
        · exact Book.not_pre_of_active h hst
        · exact Book.not_pre_of_pending h hst
      exact hinv.pt_len hp
    cases hcase with
    | new hr hf => exact ⟨k + 1, Y, ShDesc.refl Y, Or.inl (hrestart (hs1 hr))⟩
    | mergePre hr hcard hpre hf =>
      exact ⟨k + 1, Y, ShDesc.refl Y, Or.inl (hrestart (hs3 hr hcard hpre))⟩
    | overflow hr hcard hnpre hcap hf =>
      exact ⟨k + 1, Y, ShDesc.refl Y, Or.inl (hrestart (hs5 hr hcard hnpre hcap))⟩
    | mergeCap hr hcard hnpre hcap hf =>
      by_cases hrip : S.Ripe (k + 1) (H.bk (k + 1) Y)
      · exact ⟨k + 1, Y, ShDesc.refl Y, Or.inl (len_zero_of_ripe hinv hrip)⟩
      · refine ⟨k + 1, Y, ShDesc.refl Y, Or.inr ⟨t4_recInv G hf, ?_, hrip⟩⟩
        refine hf.len_le.trans ?_
        have h1 : ((∑ i ∈ H.parts k Y, (H.pb k i).nu : ℕ) : ℝ) - 1 ≤ S.numax (k + 1) := by
          have : ((∑ i ∈ H.parts k Y, (H.pb k i).nu : ℕ) : ℝ) ≤ S.numax (k + 1) := by
            exact_mod_cast hcap
          linarith
        exact mul_le_mul_of_nonneg_right h1 (S.D_nonneg _)
    | shadow i hparts hr hle hge hnu hbank =>
      have hmem : i ∈ H.parts k Y := by rw [hparts]; exact Finset.mem_singleton_self i
      obtain ⟨hrem, hsu⟩ := (H.mem_parts k i Y).mp hmem
      by_cases hact' : (H.pb k i).IsActive ∨ (H.pb k i).IsPending
      · by_cases hrip : S.Ripe k (H.bk k i)
        · have hk1 := not_isEmpty_comp i (by omega)
          have h0 := len_zero_of_ripe (H.window_inv' G k hk1 (by omega) i).1 hrip
          obtain ⟨hl1, -⟩ := shadow_len hparts hr
          have : (H.bk (k + 1) Y).len = 0 := by
            have h2 := hinv.len_nonneg
            rw [h0, zero_div] at hl1
            exact le_antisymm hl1 h2
          exact ⟨k + 1, Y, ShDesc.refl Y, Or.inl this⟩
        · have hbk : H.pb k i = H.bk k i := S.postBook_of_not_ripe hrip
          obtain ⟨ξ, W, hsh, hkind⟩ := ih i (by omega) (by rw [← hbk]; exact hact')
          exact ⟨ξ, W, ShDesc.step k W i Y hsh hrem hsu hparts hr hact' hrip, hkind⟩
      · have hpre : (H.pb k i).st = .pre := by
          rcases Book.cases_st (H.pb k i) with h | h | h
          · exact h
          · exact absurd (Or.inr h) hact'
          · exact absurd (Or.inl h) hact'
        have hst := hs2 hr i hparts
        have hp : (H.bk (k + 1) Y).pt := by
          by_contra hnp
          rw [WState.shadow_pre_npt hpre hnp] at hst
          rcases hact with h | h
          · exact Book.not_pre_of_active h hst
          · exact Book.not_pre_of_pending h hst
        exact ⟨k + 1, Y, ShDesc.refl Y, Or.inl (hinv.pt_len hp)⟩

end RegionHistory

end Balaban.LargeField
