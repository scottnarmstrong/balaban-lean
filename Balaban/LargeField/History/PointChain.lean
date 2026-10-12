module

public import Balaban.LargeField.History.Entry

/-!
# Lemma I.4.13 (g): the lineage of a point spine

A component with a point spine and smallness clock `s < k` is a pure shadow of a point component
with the same clock (the clock of a point spine is the scale of the last event, Definition I.4.7
item 5).  Hence its lineage at every scale `j ∈ [s, k]` is a single component, with a point spine
and clock `s`, hence one box of side `≤ crit_j` (`pt_desc`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

theorem Setting.postBook_s (S : Setting) (k0 k : ℕ) (b : Book) : (S.postBook k0 k b).s = b.s := by
  unfold Setting.postBook; split_ifs <;> rfl

theorem Setting.Ok.one_le_n2 {S : Setting} (ok : S.Ok) (j : ℕ) : 1 ≤ S.n2 j := by
  by_contra h
  have h0 : S.n2 j = 0 := by omega
  have := ok.lt_pow_n2 j
  rw [h0, pow_zero] at this
  have hL := ok.two_le_L
  have hM := ok.one_le_M
  have hc : 10 ≤ S.crit j := by unfold Setting.crit; omega
  have : 0 < S.L * S.M * S.crit j := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  omega

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K}

/-- A point spine with clock `s < k + 1` is a pure shadow of a point with the same clock. -/
theorem pt_back {k : ℕ} (hk : k < K) (Z' : H.Comp (k + 1)) (hpt : (H.bk (k + 1) Z').pt)
    (hs : (H.bk (k + 1) Z').s < k + 1) :
    ∃ c, H.parts k Z' = {c} ∧ H.nr k Z' = 0 ∧ (H.bk k c).pt ∧
      (H.bk k c).s = (H.bk (k + 1) Z').s := by
  classical
  have hrule := H.book_rule hk Z'
  by_cases hcond : H.nr k Z' = 0 ∧ ∃ i, H.parts k Z' = {i} ∧ (S.postBook k0 k (H.bk k i)).pt
  · obtain ⟨hr, i, hi, hip⟩ := hcond
    refine ⟨i, hi, hr, by rwa [postBook_pt] at hip, ?_⟩
    have := hrule.clock_pt_shadow hpt hr i hi hip
    rw [this, S.postBook_s]
  · have := hrule.clock_pt_other hpt hcond
    omega

theorem desc_self_unique {b : ℕ} {Y Z : H.Comp b} (h : H.Desc b b Y Z) : Y = Z := by
  cases h with
  | refl => rfl
  | step b' _ _ _ hd _ _ => have := hd.le; omega

variable (G : S.Good)

include G

/-- **Lemma I.4.13 (g)**: for `Z` of scale `b ≤ k₀` with a point spine and clock `s ≤ b`, every
ancestor `Y` at a scale `j ∈ [s, b]` is the unique such ancestor, and has a point spine and clock
`s`. -/
theorem pt_desc : ∀ b (Z : H.Comp b), b ≤ k0 → b ≤ K → (H.bk b Z).pt → ∀ {s : ℕ}, (H.bk b Z).s = s →
    s ≤ b → ∀ j (Y : H.Comp j), s ≤ j → H.Desc j b Y Z →
      (H.bk j Y).pt ∧ (H.bk j Y).s = s ∧ ∀ Y' : H.Comp j, H.Desc j b Y' Z → Y' = Y := by
  intro b
  induction b with
  | zero => intro Z; exact (H.F.isEmpty_comp_zero.false Z).elim
  | succ b0 ih =>
    intro Z hk0 hkK hpt s hs hsb j Y hsj hd
    rcases Nat.eq_or_lt_of_le hd.le with heq | hlt
    · subst heq
      have : Y = Z := desc_self_unique hd
      subst this
      exact ⟨hpt, hs, fun Y' hY' => desc_self_unique hY'⟩
    · have hs' : (H.bk (b0 + 1) Z).s < b0 + 1 := by omega
      obtain ⟨c, hparts, hr, hcpt, hcs⟩ := pt_back (by omega) Z hpt hs'
      have hcb : ∀ Y' : H.Comp j, H.Desc j (b0 + 1) Y' Z → H.Desc j b0 Y' c := by
        intro Y' hY'
        obtain ⟨c', hc', hd'⟩ := (desc_succ_iff (by omega)).mp hY'
        have : c' = c := by rw [hparts] at hc'; simpa using hc'
        subst this; exact hd'
      have hY := hcb Y hd
      obtain ⟨h1, h2, h3⟩ := ih c (by omega) (by omega) hcpt (s := s) (by omega) (by omega) j Y hsj hY
      exact ⟨h1, h2, fun Y' hY' => h3 Y' (hcb Y' hY')⟩

/-- **Lemma I.4.13 (g)**, boxes: under the hypotheses of `pt_desc`, the ancestors at scales
`j ∈ [s, b]` are boxes of side `≤ crit_j`. -/
theorem pt_desc_box (hT : ∀ k, 1 ≤ k → k ≤ k0 → 4 * S.rho k + 21 ≤ n k) {b : ℕ} {Z : H.Comp b}
    (hb : b ≤ k0) (hbK : b ≤ K) (hpt : (H.bk b Z).pt) {s : ℕ} (hs : (H.bk b Z).s = s) (hsb : s ≤ b) {j : ℕ}
    {Y : H.Comp j} (hsj : s ≤ j) (hd : H.Desc j b Y Z) : CoveredBy S n j Y.1 1 := by
  obtain ⟨h1, -, -⟩ := pt_desc G b Z hb hbK hpt hs hsb j Y hsj hd
  have hj1 : 1 ≤ j := not_isEmpty_comp Y (by have := hd.le; omega)
  have hinv := (H.window_inv' G j hj1 (by have := hd.le; omega) (by have := hd.le; omega) Y).1
  exact cover_of_len hT hj1 (by have := hd.le; omega) (by have := hd.le; omega) Y (hinv.pt_len h1)

end RegionHistory

end Balaban.LargeField
