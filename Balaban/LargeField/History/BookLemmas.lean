module

public import Balaban.LargeField.History.WState
import Mathlib.Tactic.Linarith

/-!
# Elementary lemmas on books and window states
-/

@[expose] public section

namespace Balaban.LargeField

namespace WState

theorem restart_pt {μ : ℕ} {pt : Prop} (h : pt) : WState.restart μ pt = .active μ 1 ∅ := by
  simp [WState.restart, h]

theorem restart_npt {μ : ℕ} {pt : Prop} (h : ¬ pt) : WState.restart μ pt = .pre := by
  simp [WState.restart, h]

end WState

namespace Book

variable {b : Book}

theorem q_pre (h : b.st = .pre) : b.q = b.s := by simp [Book.q, h]
theorem q_pending {q ν : ℕ} (h : b.st = .pending q ν) : b.q = q := by simp [Book.q, h]
theorem q_active {q ν : ℕ} {M : Finset ℕ} (h : b.st = .active q ν M) : b.q = q := by
  simp [Book.q, h]

theorem nu_pre (h : b.st = .pre) : b.nu = 1 := by simp [Book.nu, h]
theorem nu_pending {q ν : ℕ} (h : b.st = .pending q ν) : b.nu = ν := by simp [Book.nu, h]
theorem nu_active {q ν : ℕ} {M : Finset ℕ} (h : b.st = .active q ν M) : b.nu = ν := by
  simp [Book.nu, h]

theorem M_pre (h : b.st = .pre) : b.M = ∅ := by simp [Book.M, h]
theorem M_pending {q ν : ℕ} (h : b.st = .pending q ν) : b.M = ∅ := by simp [Book.M, h]
theorem M_active {q ν : ℕ} {M : Finset ℕ} (h : b.st = .active q ν M) : b.M = M := by
  simp [Book.M, h]

theorem isActive_of {q ν : ℕ} {M : Finset ℕ} (h : b.st = .active q ν M) : b.IsActive :=
  ⟨q, ν, M, h⟩

theorem isPending_of {q ν : ℕ} (h : b.st = .pending q ν) : b.IsPending := ⟨q, ν, h⟩

/-- Every book is `Pre`, `Pending` or `Active`. -/
theorem cases_st (b : Book) :
    b.st = .pre ∨ b.IsPending ∨ b.IsActive := by
  cases h : b.st with
  | pre => exact Or.inl rfl
  | pending q ν => exact Or.inr (Or.inl ⟨q, ν, h⟩)
  | active q ν M => exact Or.inr (Or.inr ⟨q, ν, M, h⟩)

theorem not_pre_of_active (h : b.IsActive) : b.st ≠ .pre := by
  obtain ⟨q, ν, M, h⟩ := h; simp [h]

theorem not_pre_of_pending (h : b.IsPending) : b.st ≠ .pre := by
  obtain ⟨q, ν, h⟩ := h; simp [h]

theorem not_active_of_pre (h : b.st = .pre) : ¬ b.IsActive := by
  rintro ⟨q, ν, M, h'⟩; simp [h] at h'

theorem not_pending_of_pre (h : b.st = .pre) : ¬ b.IsPending := by
  rintro ⟨q, ν, h'⟩; simp [h] at h'

theorem not_active_of_pending (h : b.IsPending) : ¬ b.IsActive := by
  obtain ⟨q, ν, h⟩ := h
  rintro ⟨q', ν', M', h'⟩; simp [h] at h'

end Book

namespace WState

theorem shadow_pre_pt {μ : ℕ} {pt : Prop} {b : Book} (hb : b.st = .pre) (h : pt) :
    WState.shadow μ pt b = .active μ 1 ∅ := by
  simp [WState.shadow, hb, h]

theorem shadow_pre_npt {μ : ℕ} {pt : Prop} {b : Book} (hb : b.st = .pre) (h : ¬ pt) :
    WState.shadow μ pt b = .pre := by
  simp [WState.shadow, hb, h]

theorem shadow_pending_lt {μ q ν : ℕ} {pt : Prop} {b : Book} (hb : b.st = .pending q ν)
    (h : μ < q) : WState.shadow μ pt b = .pending q ν := by
  simp [WState.shadow, hb, h]

theorem shadow_pending_ge {μ q ν : ℕ} {pt : Prop} {b : Book} (hb : b.st = .pending q ν)
    (h : ¬ μ < q) : WState.shadow μ pt b = .active q ν ∅ := by
  simp [WState.shadow, hb, h]

theorem shadow_active {μ q ν : ℕ} {M : Finset ℕ} {pt : Prop} {b : Book}
    (hb : b.st = .active q ν M) : WState.shadow μ pt b = .active q ν M := by
  simp [WState.shadow, hb]

end WState

namespace Setting

variable (S : Setting) {b : Book}

theorem adm_pre {k : ℕ} (h : b.st = .pre) : S.Admissible k b ↔ ¬ b.pt := by
  unfold Setting.Admissible; rw [h]

theorem adm_pending {k q ν : ℕ} (h : b.st = .pending q ν) :
    S.Admissible k b ↔ k < q ∧ q ≤ k + S.h k + 1 ∧ 1 ≤ ν ∧ ν ≤ S.numax k := by
  unfold Setting.Admissible; rw [h]

theorem adm_active {k q ν : ℕ} {M : Finset ℕ} (h : b.st = .active q ν M) :
    S.Admissible k b ↔ q ≤ k ∧ 1 ≤ ν ∧ ν ≤ S.numax k ∧ ∀ ξ ∈ M, q < ξ ∧ ξ ≤ k := by
  unfold Setting.Admissible; rw [h]

theorem bank_of_not_active (h : ¬ b.IsActive) : S.bank b = 0 := by
  unfold Setting.bank
  have : b.M = ∅ := by
    rcases Book.cases_st b with h1 | h1 | h1
    · exact Book.M_pre h1
    · obtain ⟨q, ν, h2⟩ := h1; exact Book.M_pending h2
    · exact absurd h1 h
  simp [this]

theorem bank_active {q ν : ℕ} {M : Finset ℕ} (h : b.st = .active q ν M) :
    S.bank b = 1 / 2 * ∑ ξ ∈ M, S.tau ξ := by
  unfold Setting.bank; rw [Book.M_active h]

theorem tStar_ge_left (b : Book) : b.q + S.nq b.q ≤ S.tStar b := le_max_left _ _

theorem tStar_ge_right (b : Book) : b.s + S.n2 b.s ≤ S.tStar b := le_max_right _ _

theorem ripe_isActive {k : ℕ} (h : S.Ripe k b) : b.IsActive := h.1

theorem ripe_tStar {k : ℕ} (h : S.Ripe k b) : S.tStar b = k := h.2

theorem postBook_of_not_ripe {k0 k : ℕ} (h : ¬ S.Ripe k b) : S.postBook k0 k b = b := by
  unfold Setting.postBook
  simp [h]

theorem postBook_of_ripe {k0 k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ k0) (h : S.Ripe k b) :
    S.postBook k0 k b = b.kept k := by
  unfold Setting.postBook
  simp [h1, h2, h]

theorem postBook_of_out {k0 k : ℕ} (h : ¬ (1 ≤ k ∧ k ≤ k0)) : S.postBook k0 k b = b := by
  unfold Setting.postBook
  simp only [not_and_or] at h
  rcases h with h | h <;> simp [h]

end Setting

end Balaban.LargeField
