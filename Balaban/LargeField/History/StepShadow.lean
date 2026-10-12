module

public import Balaban.LargeField.History.Scale
public import Balaban.LargeField.History.StepRestart
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Pure shadows: the invariant `BookInv` after (T1) and the monotonicity of `t^*`
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

/-- The clock of a pure shadow does not increase, and is either unchanged or at least `k + 1`. -/
theorem shadow_clock {k : ℕ} {b b' : Book} (hb : BookInv S k b)
    (hle : b'.len ≤ b.len / S.L)
    (hsh1 : ¬ b'.pt → (S.L : ℝ) < b.len) (hsh2 : b.pt → b'.pt)
    (hnp : ¬ b'.pt → b'.s = (k + 1) + max 1 ⌈Real.logb S.L (max b'.len 1)⌉₊)
    (hc1 : b'.pt → b.pt → b'.s = b.s) (hc2 : b'.pt → ¬ b.pt → b'.s = k + 1) :
    b'.s ≤ b.s ∧ (b'.s = b.s ∨ k + 1 ≤ b'.s) := by
  by_cases hbp : b.pt
  · have := hc1 (hsh2 hbp) hbp
    exact ⟨le_of_eq this, Or.inl this⟩
  · have hbs := hb.np_clock hbp
    have h1 : k + 1 ≤ b.s := by omega
    by_cases hp' : b'.pt
    · have := hc2 hp' hbp
      exact ⟨by omega, Or.inr (by omega)⟩
    · have h2 := clock_shadow_le (L := S.L) G.ok.cast_L_ge (k := k) hle (hsh1 hp')
      have h3 := hnp hp'
      rw [hbs]
      refine ⟨by omega, Or.inr (by omega)⟩

theorem tStar_le_of_shadow {b b' : Book} (hq : b'.q = b.q) (hs : b'.s ≤ b.s) :
    S.tStar b' ≤ S.tStar b := by
  unfold Setting.tStar
  rw [hq]
  exact max_le_max le_rfl (Nat.add_le_add hs (G.ok.n2_mono hs))

/-- Common tail for a pure shadow of an `Active` or `Pending` part: the core, the number of
pieces and the bank are unchanged. -/
theorem shadow_tail {k : ℕ} {b b' : Book} (hb : BookInv S k b) (hpost : k < S.tStar b)
    (hact : b.IsActive ∨ b.IsPending) (hq : b'.q = b.q) (hnu : b'.nu = b.nu)
    (hadm : S.Admissible (k + 1) b')
    (hlen : 0 ≤ b'.len) (hptl : b'.pt → b'.len = 0)
    (hle : b'.len ≤ b.len / S.L)
    (hsh1 : ¬ b'.pt → (S.L : ℝ) < b.len) (hsh2 : b.pt → b'.pt)
    (hnp : ¬ b'.pt → b'.s = (k + 1) + max 1 ⌈Real.logb S.L (max b'.len 1)⌉₊)
    (hc1 : b'.pt → b.pt → b'.s = b.s) (hc2 : b'.pt → ¬ b.pt → b'.s = k + 1) :
    BookInv S (k + 1) b' ∧ S.tStar b' ≤ S.tStar b ∧ k + 1 ≤ S.tStar b' := by
  obtain ⟨hsle, hscases⟩ := G.shadow_clock hb hle hsh1 hsh2 hnp hc1 hc2
  have hL1 : (1 : ℝ) ≤ S.L := by linarith [G.ok.cast_L_ge]
  have htle : S.tStar b' ≤ S.tStar b := G.tStar_le_of_shadow hq hsle
  have htge : k + 1 ≤ S.tStar b' := by
    rcases hscases with h | h
    · have : S.tStar b' = S.tStar b := by unfold Setting.tStar; rw [hq, h]
      omega
    · have := S.tStar_ge_right b'
      omega
  refine ⟨⟨hadm, hlen, hptl, ?_, hnp, ?_, ?_, htge⟩, htle, htge⟩
  · intro hp'
    by_cases hbp : b.pt
    · rw [hc1 hp' hbp]; exact le_trans (hb.pt_clock hbp) (Nat.le_succ k)
    · rw [hc2 hp' hbp]
  · intro _
    have h1 := hb.len_nu hact
    have hν : 1 ≤ b.nu := by
      rcases hact with ⟨q, ν, M, h⟩ | ⟨q, ν, h⟩
      · have := hb.adm; rw [S.adm_active h] at this; rw [Book.nu_active h]; exact this.2.1
      · have := hb.adm; rw [S.adm_pending h] at this; rw [Book.nu_pending h]; exact this.2.2.1
    have hD : S.D k ≤ S.D (k + 1) := G.ok.D_mono (Nat.le_succ k)
    have hD0 := S.D_nonneg k
    have hνr : (0 : ℝ) ≤ (b.nu : ℝ) - 1 := by
      have : (1 : ℝ) ≤ b.nu := by exact_mod_cast hν
      linarith
    rw [hnu]
    calc b'.len ≤ b.len / S.L := hle
      _ ≤ b.len := div_le_self hb.len_nonneg hL1
      _ ≤ ((b.nu : ℝ) - 1) * S.D k := h1
      _ ≤ ((b.nu : ℝ) - 1) * S.D (k + 1) := by gcongr
  · intro _
    have h1 := hb.f4 hact
    rw [hq]
    exact lt_of_le_of_lt htle h1

/-- The invariant of a pure shadow ((T1)). -/
theorem shadow_inv {k : ℕ} {b b' : Book} (hb : BookInv S k b) (hpost : k < S.tStar b)
    (hst : b'.st = WState.shadow (k + 1) b'.pt b)
    (hlen : 0 ≤ b'.len) (hptl : b'.pt → b'.len = 0)
    (hle : b'.len ≤ b.len / S.L)
    (hsh1 : ¬ b'.pt → (S.L : ℝ) < b.len) (hsh2 : b.pt → b'.pt)
    (hnp : ¬ b'.pt → b'.s = (k + 1) + max 1 ⌈Real.logb S.L (max b'.len 1)⌉₊)
    (hc1 : b'.pt → b.pt → b'.s = b.s) (hc2 : b'.pt → ¬ b.pt → b'.s = k + 1) :
    BookInv S (k + 1) b' ∧ S.tStar b' ≤ S.tStar b ∧ k + 1 ≤ S.tStar b' ∧
      b'.nu = b.nu ∧ S.bank b' = S.bank b := by
  rcases Book.cases_st b with hpre | ⟨q, ν, hpend⟩ | ⟨q, ν, M, hact⟩
  · -- `Pre`: the shadow state is the restart state
    have hbpt : ¬ b.pt := (S.adm_pre hpre).mp hb.adm
    have hbs := hb.np_clock hbpt
    have hst' : b'.st = WState.restart (k + 1) b'.pt := by
      by_cases hp' : b'.pt
      · rw [hst, WState.shadow_pre_pt hpre hp', WState.restart_pt hp']
      · rw [hst, WState.shadow_pre_npt hpre hp', WState.restart_npt hp']
    obtain ⟨hinv, htS, hμs, -, hnu, hbank⟩ := G.restart_inv hst' hlen hptl hnp
      (fun hp' => hc2 hp' hbpt)
    obtain ⟨hsle, -⟩ := G.shadow_clock hb hle hsh1 hsh2 hnp hc1 hc2
    refine ⟨hinv, ?_, by rw [htS]; omega, by rw [hnu, Book.nu_pre hpre], ?_⟩
    · rw [htS, G.tStar_pre hpre]
      exact Nat.add_le_add hsle (G.ok.nq_mono hsle)
    · rw [hbank, S.bank_of_not_active (Book.not_active_of_pre hpre)]
  · -- `Pending`
    have hadm := hb.adm
    rw [S.adm_pending hpend] at hadm
    obtain ⟨h1, h2, h3, h4⟩ := hadm
    by_cases hlt : k + 1 < q
    · have hst' : b'.st = .pending q ν := by rw [hst, WState.shadow_pending_lt hpend hlt]
      have hh : S.h k ≤ S.h (k + 1) := G.ok.h_mono (Nat.le_succ k)
      have hn : S.numax k ≤ S.numax (k + 1) := G.ok.numax_mono (Nat.le_succ k)
      have hadm' : S.Admissible (k + 1) b' := by
        rw [S.adm_pending hst']; refine ⟨hlt, by omega, h3, by omega⟩
      obtain ⟨hinv, hle1, hge1⟩ := G.shadow_tail hb hpost (Or.inr ⟨q, ν, hpend⟩)
        (by rw [Book.q_pending hst', Book.q_pending hpend])
        (by rw [Book.nu_pending hst', Book.nu_pending hpend])
        hadm' hlen hptl hle hsh1 hsh2 hnp hc1 hc2
      refine ⟨hinv, hle1, hge1, by rw [Book.nu_pending hst', Book.nu_pending hpend], ?_⟩
      rw [S.bank_of_not_active (Book.not_active_of_pending ⟨q, ν, hst'⟩),
        S.bank_of_not_active (Book.not_active_of_pending ⟨q, ν, hpend⟩)]
    · have hst' : b'.st = .active q ν ∅ := by rw [hst, WState.shadow_pending_ge hpend hlt]
      have hn : S.numax k ≤ S.numax (k + 1) := G.ok.numax_mono (Nat.le_succ k)
      have hadm' : S.Admissible (k + 1) b' := by
        rw [S.adm_active hst']; refine ⟨by omega, h3, by omega, by simp⟩
      obtain ⟨hinv, hle1, hge1⟩ := G.shadow_tail hb hpost (Or.inr ⟨q, ν, hpend⟩)
        (by rw [Book.q_active hst', Book.q_pending hpend])
        (by rw [Book.nu_active hst', Book.nu_pending hpend])
        hadm' hlen hptl hle hsh1 hsh2 hnp hc1 hc2
      refine ⟨hinv, hle1, hge1, by rw [Book.nu_active hst', Book.nu_pending hpend], ?_⟩
      rw [S.bank_active hst', S.bank_of_not_active (Book.not_active_of_pending ⟨q, ν, hpend⟩)]
      simp
  · -- `Active`
    have hadm := hb.adm
    rw [S.adm_active hact] at hadm
    obtain ⟨h1, h2, h3, h4⟩ := hadm
    have hst' : b'.st = .active q ν M := by rw [hst, WState.shadow_active hact]
    have hn : S.numax k ≤ S.numax (k + 1) := G.ok.numax_mono (Nat.le_succ k)
    have hadm' : S.Admissible (k + 1) b' := by
      rw [S.adm_active hst']
      refine ⟨by omega, h2, by omega, fun ξ hξ => ?_⟩
      have := h4 ξ hξ; exact ⟨this.1, by omega⟩
    obtain ⟨hinv, hle1, hge1⟩ := G.shadow_tail hb hpost (Or.inl ⟨q, ν, M, hact⟩)
      (by rw [Book.q_active hst', Book.q_active hact])
      (by rw [Book.nu_active hst', Book.nu_active hact])
      hadm' hlen hptl hle hsh1 hsh2 hnp hc1 hc2
    refine ⟨hinv, hle1, hge1, by rw [Book.nu_active hst', Book.nu_active hact], ?_⟩
    rw [S.bank_active hst', S.bank_active hact]

end Setting.Good

end Balaban.LargeField
