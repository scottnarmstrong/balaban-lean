module

public import Balaban.LargeField.History.PointChain

/-!
# The gain clock `b(Z)` (Definition I.4.6, I.4.7 item 5)

`gain k Z` is the scale of the last new cube or kept `R` event in the history of `Z`:

* `gain_succ_of_not_new`: the recursion `b' = max_i b(Z_i)`, with the value `k` for a kept ripe
  part, for a component without new cube;
* `gain_le_iff`: `b(Z) ≤ m` iff no ancestor of scale `j > m` contains a new cube and no ancestor of
  scale `j ∈ (m, k)` is ripe (kept);
* `gain_le_core` (Lemma I.4.13 (a)): `b(Z) ≤ q` for `Z` `Active` or `Pending` of scale `k ≤ k₀`
  with core `q`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K}

theorem gain_zero (Z : H.Comp 0) : H.gain 0 Z = 0 := by
  unfold gain; rfl

open Classical in
/-- The rule for a component without new cube: `b' = max_i b(Z_i)` over the old parts, where a
kept ripe part counts as `k`. -/
theorem gain_succ_of_not_new (k : ℕ) (Z' : H.Comp (k + 1))
    (h : ¬ (Z'.1 ∩ H.newCubes (k + 1)).Nonempty) :
    H.gain (k + 1) Z' = (H.parts k Z').sup fun c =>
      if 1 ≤ k ∧ k ≤ k0 ∧ S.Ripe k (H.bk k c) then k else H.gain k c := by
  have e : H.gain (k + 1) Z' = if (Z'.1 ∩ H.newCubes (k + 1)).Nonempty then k + 1 else
      (H.parts k Z').sup fun c => if 1 ≤ k ∧ k ≤ k0 ∧ S.Ripe k (H.bk k c) then k else H.gain k c :=
    rfl
  rw [e]
  simp only [h, ↓reduceIte]

/-- The events of the gain clock: new cubes at scales `> m`. -/
def GainNew (m k : ℕ) (Z : H.Comp k) : Prop :=
  ∀ j (Y : H.Comp j), H.Desc j k Y Z → m < j → ¬ (Y.1 ∩ H.newCubes j).Nonempty

/-- The events of the gain clock: kept ripe ancestors at scales in `(m, k)`. -/
def GainKept (m k : ℕ) (Z : H.Comp k) : Prop :=
  ∀ j (Y : H.Comp j), H.Desc j k Y Z → j < k → m < j →
    ¬ (1 ≤ j ∧ j ≤ k0 ∧ S.Ripe j (H.bk j Y))

/-- **The rules of the gain clock**: `b(Z) ≤ m` iff there is no event of scale `> m` in the history
of `Z`. -/
theorem gain_le_iff {m : ℕ} : ∀ k (Z : H.Comp k), H.gain k Z ≤ m ↔ GainNew m k Z ∧ GainKept m k Z := by
  classical
  intro k
  induction k with
  | zero =>
    intro Z
    exact (H.F.isEmpty_comp_zero.false Z).elim
  | succ k ih =>
    intro Z'
    by_cases hnew : (Z'.1 ∩ H.newCubes (k + 1)).Nonempty
    · rw [H.gain_of_new k Z' hnew]
      constructor
      · intro hle
        refine ⟨fun j Y hd hmj => ?_, fun j Y hd hjk hmj => ?_⟩
        · exfalso; have := hd.le; omega
        · exfalso; omega
      · rintro ⟨h1, -⟩
        by_contra hlt
        exact h1 (k + 1) Z' (Desc.refl Z') (by omega) hnew
    · rw [H.gain_succ_of_not_new k Z' hnew, Finset.sup_le_iff]
      have hdesc : ∀ {j : ℕ} {Y : H.Comp j}, j ≤ k → (H.Desc j (k + 1) Y Z' ↔
          ∃ c ∈ H.parts k Z', H.Desc j k Y c) := fun hj => desc_succ_iff hj
      constructor
      · intro hle
        have hP : ∀ c ∈ H.parts k Z', GainNew m k c ∧ GainKept m k c := by
          intro c hc
          have hc' := hle c hc
          by_cases hK : 1 ≤ k ∧ k ≤ k0 ∧ S.Ripe k (H.bk k c)
          · rw [ite_eq_left_of_eq_true _ _ (eq_true hK)] at hc'
            refine ⟨fun j Y hd hmj => ?_, fun j Y hd hjk hmj => ?_⟩
            · exfalso; have := hd.le; omega
            · exfalso; omega
          · rw [ite_eq_right_of_eq_false _ _ (eq_false hK)] at hc'
            exact (ih c).mp hc'
        refine ⟨fun j Y hd hmj => ?_, fun j Y hd hjk hmj => ?_⟩
        · rcases Nat.eq_or_lt_of_le hd.le with heq | hlt
          · subst heq
            have : Y = Z' := desc_self_unique hd
            subst this; exact hnew
          · obtain ⟨c, hc, hd'⟩ := (hdesc (by omega)).mp hd
            exact (hP c hc).1 j Y hd' hmj
        · rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hjk) with heq | hlt
          · subst heq
            obtain ⟨c, hc, hd'⟩ := (hdesc le_rfl).mp hd
            have : Y = c := desc_self_unique hd'
            subst this
            have hc' := hle Y hc
            intro hK
            rw [ite_eq_left_of_eq_true _ _ (eq_true hK)] at hc'
            omega
          · obtain ⟨c, hc, hd'⟩ := (hdesc (by omega)).mp hd
            exact (hP c hc).2 j Y hd' hlt hmj
      · rintro ⟨h1, h2⟩ c hc
        have hsingle : H.Desc k (k + 1) c Z' := by
          obtain ⟨hrem, hs⟩ := (H.mem_parts k c Z').mp hc
          exact Desc.single hrem hs
        split_ifs with hK
        · by_contra hlt
          exact h2 k c hsingle (Nat.lt_succ_self k) (by omega) hK
        · refine (ih c).mpr ⟨fun j Y hd hmj => h1 j Y (hd.trans hsingle) hmj,
            fun j Y hd hjk hmj => h2 j Y (hd.trans hsingle) (by omega) hmj⟩

variable (G : S.Good)

include G

/-- **Lemma I.4.13 (a)**: `b(Z) ≤ q` for `Z` `Active` or `Pending` of scale `k ≤ k₀` with core `q`. -/
theorem gain_le_core {k : ℕ} {Z : H.Comp k} (hk0 : k ≤ k0) (hkK : k ≤ K)
    (hZ : (H.bk k Z).IsActive ∨ (H.bk k Z).IsPending) : H.gain k Z ≤ (H.bk k Z).q := by
  refine (gain_le_iff k Z).mpr ⟨fun j Y hd hmj hne => ?_, fun j Y hd hjk hmj hK => ?_⟩
  · have hL := live_of_desc G hk0 hkK hZ hd hmj
    obtain ⟨κ, rfl⟩ : ∃ κ, j = κ + 1 := ⟨j - 1, by omega⟩
    have hr : (Y.1 ∩ H.newCubes (κ + 1)).card = 0 := hL.1
    rw [Finset.card_eq_zero] at hr
    rw [hr] at hne
    simp at hne
  · exact not_ripe_of_desc G hk0 hkK hZ hd hmj hjk hK.2.2

end RegionHistory

end Balaban.LargeField
