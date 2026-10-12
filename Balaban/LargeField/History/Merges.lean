module

public import Balaban.LargeField.History.RipeWindow

/-!
# Merges and floors in the language of Lemmas I.4.12 and I.4.13 (e4)

* `IsReset` (Definition I.4.11) and `floor_reset` (Lemma I.4.12): a component with a reset at scale
  `a` has descendants that are `Pre` or have core `≥ a` (`≥ a + 1` for a `Pre` reset);
* `IsMerge`: the component is the output of a merge within the cap (T4);
* `merge_in_record` (Lemma I.4.13 (e4)): a (T4) merge at a scale in `(q, k]` lies in `𝓜`;
* `merge_released`: a (T4) merge at a scale `ξ ≤ q` of a live non-ripe path to `Z` has
  `ξ + h_ξ < q`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K}

/-- The output of a restart (T2), (T3), (T5) at the step into scale `a`. -/
def IsRestart : ∀ a : ℕ, H.Comp a → Prop
  | 0, _ => False
  | k + 1, Y => 1 ≤ H.nr k Y ∨ (H.nr k Y = 0 ∧ 2 ≤ (H.parts k Y).card ∧
      ((∃ c ∈ H.parts k Y, (H.pb k c).st = .pre) ∨ S.numax (k + 1) < ∑ c ∈ H.parts k Y, (H.pb k c).nu))

/-- **Definition I.4.11**: `Y` has a reset at its own scale `a`: (i) it is `Pre`, (ii) it is the output
of a restart, (iii) it is kept by `R^{(a)}`. -/
def IsReset (a : ℕ) (Y : H.Comp a) : Prop :=
  (H.bk a Y).st = .pre ∨ H.IsRestart a Y ∨ (1 ≤ a ∧ a ≤ k0 ∧ S.Ripe a (H.bk a Y))

/-- The output of a merge within the cap (T4) at the step into scale `a`. -/
def IsMerge : ∀ a : ℕ, H.Comp a → Prop
  | 0, _ => False
  | k + 1, Y => H.nr k Y = 0 ∧ 2 ≤ (H.parts k Y).card ∧
      (∀ c ∈ H.parts k Y, (H.pb k c).IsActive ∨ (H.pb k c).IsPending) ∧
      ∑ c ∈ H.parts k Y, (H.pb k c).nu ≤ S.numax (k + 1)

variable (G : S.Good)

include G

/-- A restart is not a live step. -/
theorem not_live_of_restart {k : ℕ} {Y : H.Comp (k + 1)} (h : H.IsRestart (k + 1) Y) :
    ¬ H.Live k Y := by
  rintro ⟨hr, hact, hcap⟩
  rcases h with h | ⟨-, hcard, hpre | hover⟩
  · omega
  · obtain ⟨c, hc, hpre⟩ := hpre
    rcases hact c hc with h' | h'
    · exact Book.not_pre_of_active h' hpre
    · exact Book.not_pre_of_pending h' hpre
  · rcases hcap with h' | h' <;> omega

/-- **Lemma I.4.12 (floor)**: a component with a reset at scale `a` has, at every later scale
`b ≤ k₀` of its descendants, the form `Pre` or core `≥ a` (and `≥ a + 1` if the reset is (i)). -/
theorem floor_reset {a b : ℕ} {Y : H.Comp a} {Z : H.Comp b} (hd : H.Desc a b Y Z) (hb : b ≤ k0)
    (hbK : b ≤ K)
    (hR : H.IsReset a Y) :
    (H.pb b Z).Fl a ∧ (a < b → (H.bk b Z).Fl a) ∧
      ((H.bk a Y).st = .pre → (a < b → (H.bk b Z).Fl (a + 1))) := by
  have hle := hd.le
  have hpost : (H.pb a Y).Fl a := by
    rcases hR with hpre | hrs | ⟨h1, h2, hrip⟩
    · exact Book.fl_pre (by rw [pb_of_pre G hpre]; exact hpre)
    · cases a with
      | zero => exact hrs.elim
      | succ k =>
        have hF : (H.bk (k + 1) Y).Fl (k + 1) := by
          rcases live_or_floor G (show k + 1 ≤ k0 by omega) (show k + 1 ≤ K by omega) Y with hL | hF
          · exact (not_live_of_restart G hrs hL).elim
          · exact hF
        exact floor_post G (by omega) (by omega) le_rfl Y hF
    · rw [show H.pb a Y = (H.bk a Y).kept a from S.postBook_of_ripe h1 h2 hrip]
      exact Book.fl_active (b := (H.bk a Y).kept a) (q := a) (ν := 1) (M := ∅) rfl le_rfl
  refine ⟨floor_desc_post G hd hb hbK (by omega) hpost, fun hab =>
    floor_desc_pre G hd hab hb hbK (by omega) hpost, fun hpre hab => ?_⟩
  exact floor_desc_pre G hd hab hb hbK le_rfl (Book.fl_pre (by rw [pb_of_pre G hpre]; exact hpre))

/-- The output of a merge within the cap satisfies `RecInv` for its own scale. -/
theorem recInv_of_merge {k : ℕ} {Y : H.Comp (k + 1)} (hk0 : k + 1 ≤ k0) (hkK : k + 1 ≤ K) (hM : H.IsMerge (k + 1) Y) :
    S.RecInv (k + 1) (H.bk (k + 1) Y) := by
  obtain ⟨hr, hcard, hact, hcap⟩ := hM
  obtain ⟨-, hcase, -⟩ := H.step_facts G hk0 hkK Y
  cases hcase with
  | new hr' hf => omega
  | mergePre hr' hcard' hpre hf =>
    obtain ⟨i, hi, hpre⟩ := hpre
    rcases hact i hi with h | h
    · exact absurd hpre (Book.not_pre_of_active h)
    · exact absurd hpre (Book.not_pre_of_pending h)
  | overflow hr' hcard' hnpre hcap' hf => omega
  | mergeCap hr' hcard' hnpre hcap' hf => exact t4_recInv G hf
  | shadow i hparts hr' hle hge hnu hbank =>
    rw [hparts] at hcard; simp at hcard

variable {k : ℕ} {Z : H.Comp k}

/-- The records of an `Active` or `Pending` component are scales `> q`. -/
theorem core_lt_of_mem_M (hk0 : k ≤ k0) (hkK : k ≤ K) (hZ : (H.bk k Z).IsActive ∨ (H.bk k Z).IsPending)
    {ξ : ℕ} (hξ : ξ ∈ (H.bk k Z).M) : (H.bk k Z).q < ξ := by
  have hk1 : 1 ≤ k := not_isEmpty_comp Z hk0
  have hadm := (H.window_inv' G k hk1 hk0 hkK Z).1.adm
  rcases hZ with ⟨q', ν, M', hst⟩ | ⟨q', ν, hst⟩
  · rw [S.adm_active hst] at hadm
    rw [Book.M_active hst] at hξ
    rw [Book.q_active hst]
    exact (hadm.2.2.2 ξ hξ).1
  · rw [Book.M_pending hst] at hξ
    simp at hξ

/-- The record of a merge at the start of a live path to `Z` is kept or released with a large core. -/
theorem recInv_of_live_merge (hk0 : k ≤ k0) (hkK : k ≤ K) {ξ : ℕ} {W : H.Comp ξ} (hM : H.IsMerge ξ W)
    (hL : H.LiveDesc ξ k W Z) : S.RecInv ξ (H.bk k Z) := by
  have hξ := hL.toDesc.le
  obtain ⟨κ, rfl⟩ : ∃ κ, ξ = κ + 1 := ⟨ξ - 1, by
    cases ξ with
    | zero => exact (H.F.isEmpty_comp_zero.false W).elim
    | succ ξ => omega⟩
  have hrec := recInv_of_merge G (show κ + 1 ≤ k0 by omega) (show κ + 1 ≤ K by omega) hM
  rcases Nat.eq_or_lt_of_le hξ with heq | hlt
  · subst heq
    have : Z = W := hL.toDesc.unique (Desc.refl W)
    subst this; exact hrec
  · exact recInv_liveDesc G hL hlt hk0 hkK hrec

/-- **Lemma I.4.13 (e4)**: every (T4) merge of the lineage at a scale `ξ ∈ (q, k]` lies in `𝓜`. -/
theorem merge_in_record (hk0 : k ≤ k0) (hkK : k ≤ K) (hZ : (H.bk k Z).IsActive ∨ (H.bk k Z).IsPending)
    {ξ : ℕ} {Y : H.Comp ξ} (hd : H.Desc ξ k Y Z) (hq : (H.bk k Z).q < ξ)
    (hM : H.IsMerge ξ Y) : ξ ∈ (H.bk k Z).M := by
  have hξ := hd.le
  have hL : H.LiveDesc ξ k Y Z := by
    rcases Nat.eq_or_lt_of_le hξ with heq | hlt
    · subst heq
      have : Z = Y := hd.unique (Desc.refl Y)
      subst this; exact LiveDesc.refl _
    · exact liveDesc_of_desc G hk0 hkK hZ hd hq.le (not_ripe_of_desc G hk0 hkK hZ hd hq hlt)
  rcases recInv_of_live_merge G hk0 hkK hM hL with h | h
  · exact h
  · omega

/-- **Lemma I.4.13 (e4)**: a (T4) merge at a scale `ξ ≤ q` that lies on a live path (no certified
entry after it) to `Z` satisfies `ξ + h_ξ < q`. -/
theorem merge_released (hk0 : k ≤ k0) (hkK : k ≤ K) (hZ : (H.bk k Z).IsActive ∨ (H.bk k Z).IsPending)
    {ξ : ℕ} {W : H.Comp ξ} (hM : H.IsMerge ξ W) (hL : H.LiveDesc ξ k W Z)
    (hξq : ξ ≤ (H.bk k Z).q) : ξ + S.h ξ < (H.bk k Z).q := by
  rcases recInv_of_live_merge G hk0 hkK hM hL with h | h
  · have := core_lt_of_mem_M G hk0 hkK hZ h
    omega
  · exact h

end RegionHistory

end Balaban.LargeField
