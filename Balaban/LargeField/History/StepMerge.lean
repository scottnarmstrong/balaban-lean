module

public import Balaban.LargeField.History.StepShadow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Merges within the cap: the invariant `BookInv` after (T4) and the facts (B.4)
-/

@[expose] public section

namespace Balaban.LargeField

/-- The facts (B.4) and the shape of a merge within the cap. -/
structure T4Facts {ι : Type*} (S : Setting) (k : ℕ) (parts : Finset ι) (f : ι → Book)
    (b' : Book) : Prop where
  inv : BookInv S (k + 1) b'
  E_le : ∀ ξ ∈ Setting.t4E (k + 1) parts f, ξ ≤ k + 1
  Q_le : Setting.t4Q parts f ≤ k + 1 + S.h (k + 1)
  k1_small : S.k1 (b'.s + S.n2 b'.s) ≤ k
  Q_le_q : Setting.t4Q parts f ≤ S.t4q (k + 1) parts f b'.s
  q_le : S.t4q (k + 1) parts f b'.s ≤ k + 1 + S.h (k + 1) + 1
  tStar_eq : S.tStar b' = S.t4T (k + 1) parts f b'.s
  len_le : b'.len ≤ (((∑ i ∈ parts, (f i).nu : ℕ) : ℝ) - 1) * S.D (k + 1)
  nu_eq : b'.nu = ∑ i ∈ parts, (f i).nu
  s_ge : k + 1 ≤ b'.s
  s_le : (b'.s : ℝ) ≤ (k + 1 : ℕ) + 1 + Real.logb S.L (max b'.len 1)
  q_eq : b'.q = S.t4q (k + 1) parts f b'.s

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

/-- The logarithm of the length of a spine bounded by `ν_max(μ) D_μ` is at most
`log_L (ν̄(λ_μ) D̄(λ_μ))`. -/
theorem logb_len_le {μ : ℕ} {len' : ℝ} (hlen : len' ≤ S.numax μ * S.D μ) :
    Real.logb S.L (max len' 1) ≤ Real.logb S.L (S.nuBar (S.lam μ) * S.Dbar (S.lam μ)) := by
  have hL := G.ok.cast_L_ge
  have hl := (G.ok.lam_pos μ).le
  have h1 := G.ok.numax_le_bar μ
  have h2 := G.ok.D_le_bar μ
  have h3 := G.ok.one_le_nuBar hl
  have h4 := G.ok.one_le_Dbar (S.lam μ)
  have h5 : (S.numax μ : ℝ) * S.D μ ≤ S.nuBar (S.lam μ) * S.Dbar (S.lam μ) := by
    have := S.D_nonneg μ
    have : (0 : ℝ) ≤ S.numax μ := Nat.cast_nonneg _
    gcongr
  apply Real.logb_le_logb_of_le (by linarith) (lt_of_lt_of_le one_pos (le_max_right _ _))
  refine max_le (hlen.trans h5) ?_
  nlinarith

/-- `s' + n_2(s') < μ + n_q(μ)` for the clock of a merge (Lemma I.4.10 (b), via (Λ1)). -/
theorem s_add_n2_lt {μ s' : ℕ} {len' : ℝ} (hlen : len' ≤ S.numax μ * S.D μ)
    (hs1 : μ ≤ s') (hs2 : (s' : ℝ) ≤ μ + 1 + Real.logb S.L (max len' 1)) :
    s' + S.n2 s' < μ + S.nq μ := by
  set Y := Real.logb S.L (S.nuBar (S.lam μ) * S.Dbar (S.lam μ)) with hY
  have hΛ := G.logb_len_le hlen
  have hx := G.lam_ge μ
  have hl := G.ok.lam_pos μ
  have hθ := G.ok.θp_pos
  have h1a := G.lc.l1_a (S.lam μ) hx
  have h1b := G.lc.l1_b (S.lam μ) hx
  have hY0 : 0 ≤ Y := by
    have := G.ok.one_le_nuBar hl.le
    have := G.ok.one_le_Dbar (S.lam μ)
    exact Real.logb_nonneg (by linarith [G.ok.cast_L_ge]) (by nlinarith)
  obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le hs1
  have hz : (z : ℝ) ≤ 1 + Y := by push_cast at hs2; linarith
  have hlam : S.lam (μ + z) ≤ 2 * S.lam μ := by
    have := G.ok.lam_add_le μ z
    have h2 : (z : ℝ) * S.θp ≤ (1 + Y) * S.θp := by gcongr
    nlinarith
  have hn2 : (S.n2 (μ + z) : ℝ) ≤ S.n2Bar (2 * S.lam μ) :=
    (G.ok.n2_le_bar (μ + z)).trans (G.ok.n2Bar_mono (G.ok.lam_pos _).le hlam)
  have hnq := S.lt_nq μ
  have : ((μ + z + S.n2 (μ + z) : ℕ) : ℝ) < ((μ + S.nq μ : ℕ) : ℝ) := by
    push_cast at hz ⊢
    linarith
  exact_mod_cast this

/-- Length of a merge: `ℓ' ≤ (ν' - 1) D_μ`, from (4.1) and the part bounds. -/
theorem merge_len_bound {ι : Type*} {k : ℕ} {parts : Finset ι} {f : ι → Book} {len' : ℝ}
    (hinv : ∀ i ∈ parts, BookInv S k (f i))
    (hact : ∀ i ∈ parts, (f i).IsActive ∨ (f i).IsPending)
    (hgen : len' ≤ ∑ i ∈ parts, (f i).len / S.L + (((parts.card + 0 : ℕ) : ℝ) - 1) * S.D (k + 1)) :
    len' ≤ (((∑ i ∈ parts, (f i).nu : ℕ) : ℝ) - 1) * S.D (k + 1) := by
  have hL1 : (1 : ℝ) ≤ S.L := by linarith [G.ok.cast_L_ge]
  have hD : S.D k ≤ S.D (k + 1) := G.ok.D_mono (Nat.le_succ k)
  have hD0 := S.D_nonneg k
  have hν : ∀ i ∈ parts, 1 ≤ (f i).nu := by
    intro i hi
    rcases hact i hi with ⟨q, ν, M, h⟩ | ⟨q, ν, h⟩
    · have := (hinv i hi).adm; rw [S.adm_active h] at this; rw [Book.nu_active h]; exact this.2.1
    · have := (hinv i hi).adm; rw [S.adm_pending h] at this; rw [Book.nu_pending h]; exact this.2.2.1
  have h1 : ∑ i ∈ parts, (f i).len / S.L ≤ ∑ i ∈ parts, (((f i).nu : ℝ) - 1) * S.D (k + 1) := by
    apply Finset.sum_le_sum
    intro i hi
    have h2 := (hinv i hi).len_nu (hact i hi)
    have h3 := (hinv i hi).len_nonneg
    have h4 : (1 : ℝ) ≤ (f i).nu := by exact_mod_cast hν i hi
    calc (f i).len / S.L ≤ (f i).len := div_le_self h3 hL1
      _ ≤ (((f i).nu : ℝ) - 1) * S.D k := h2
      _ ≤ (((f i).nu : ℝ) - 1) * S.D (k + 1) := by
        have : (0 : ℝ) ≤ ((f i).nu : ℝ) - 1 := by linarith
        gcongr
  have h2 : ∑ i ∈ parts, (((f i).nu : ℝ) - 1) * S.D (k + 1) =
      (((∑ i ∈ parts, (f i).nu : ℕ) : ℝ) - parts.card) * S.D (k + 1) := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib]
    simp
  have h3 : (((parts.card + 0 : ℕ) : ℝ) - 1) = (parts.card : ℝ) - 1 := by simp
  rw [h3] at hgen
  rw [h2] at h1
  nlinarith

/-- The invariant and the facts (B.4) for a merge within the cap ((T4)). -/
theorem t4_inv {ι : Type*} {k : ℕ} {parts : Finset ι} {f : ι → Book} {b' : Book}
    (hcard : 2 ≤ parts.card)
    (hinv : ∀ i ∈ parts, BookInv S k (f i)) 
    (hact : ∀ i ∈ parts, (f i).IsActive ∨ (f i).IsPending)
    (hcap : ∑ i ∈ parts, (f i).nu ≤ S.numax (k + 1))
    (hst : b'.st = S.t4State (k + 1) parts f b'.s)
    (hlen : 0 ≤ b'.len) (hptl : b'.pt → b'.len = 0)
    (hgen : b'.len ≤ ∑ i ∈ parts, (f i).len / S.L +
      (((parts.card + 0 : ℕ) : ℝ) - 1) * S.D (k + 1))
    (hnp : ¬ b'.pt → b'.s = (k + 1) + max 1 ⌈Real.logb S.L (max b'.len 1)⌉₊)
    (hpt : b'.pt → b'.s = k + 1) :
    T4Facts S k parts f b' := by
  have hL := G.ok.cast_L_ge
  have hne : parts.Nonempty := Finset.card_pos.mp (by omega)
  have hlenν := G.merge_len_bound hinv hact hgen
  -- the clock
  have hs_ge : k + 1 ≤ b'.s := by
    by_cases hp : b'.pt
    · rw [hpt hp]
    · rw [hnp hp]; omega
  have hs_le : (b'.s : ℝ) ≤ (k + 1 : ℕ) + 1 + Real.logb S.L (max b'.len 1) := by
    have hΛ : 0 ≤ Real.logb S.L (max b'.len 1) :=
      Real.logb_nonneg (by linarith) (le_max_right _ _)
    by_cases hp : b'.pt
    · rw [hpt hp]; push_cast; linarith
    · have h1 : (⌈Real.logb S.L (max b'.len 1)⌉₊ : ℝ) ≤ Real.logb S.L (max b'.len 1) + 1 :=
        (Nat.ceil_lt_add_one hΛ).le
      have hm : ((max 1 ⌈Real.logb S.L (max b'.len 1)⌉₊ : ℕ) : ℝ) ≤
          1 + Real.logb S.L (max b'.len 1) := by
        rcases le_total 1 ⌈Real.logb S.L (max b'.len 1)⌉₊ with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h]; push_cast; linarith
      rw [hnp hp, Nat.cast_add]
      push_cast at hm ⊢
      linarith
  -- bound on the length
  have hlen2 : b'.len ≤ S.numax (k + 1) * S.D (k + 1) := by
    refine hlenν.trans ?_
    have h1 : (((∑ i ∈ parts, (f i).nu : ℕ) : ℝ) - 1) ≤ S.numax (k + 1) := by
      have : ((∑ i ∈ parts, (f i).nu : ℕ) : ℝ) ≤ S.numax (k + 1) := by exact_mod_cast hcap
      linarith
    exact mul_le_mul_of_nonneg_right h1 (S.D_nonneg _)
  have hk1small : S.k1 (b'.s + S.n2 b'.s) ≤ k := by
    have h := G.s_add_n2_lt hlen2 hs_ge hs_le
    have := G.ok.k1_le_pred (S := S) (t := b'.s + S.n2 b'.s) (μ := k + 1) (by omega) h
    omega
  -- books of the parts
  have hq_le : ∀ i ∈ parts, (f i).q ≤ k + 1 + S.h (k + 1) := by
    intro i hi
    rcases hact i hi with ⟨q, ν, M, h⟩ | ⟨q, ν, h⟩
    · have := (hinv i hi).adm; rw [S.adm_active h] at this
      rw [Book.q_active h]; omega
    · have := (hinv i hi).adm; rw [S.adm_pending h] at this
      rw [Book.q_pending h]
      have := G.ok.h_mono (show k ≤ k + 1 by omega)
      omega
  have hQ : Setting.t4Q parts f ≤ k + 1 + S.h (k + 1) := by
    unfold Setting.t4Q
    exact Finset.sup_le hq_le
  have hE : ∀ ξ ∈ Setting.t4E (k + 1) parts f, ξ ≤ k + 1 := by
    intro ξ hξ
    unfold Setting.t4E at hξ
    rcases Finset.mem_union.mp hξ with h | h
    · obtain ⟨i, hi, hξi⟩ := Finset.mem_biUnion.mp h
      rcases hact i hi with ⟨q, ν, M, h'⟩ | ⟨q, ν, h'⟩
      · have := (hinv i hi).adm; rw [S.adm_active h'] at this
        rw [Book.M_active h'] at hξi
        have := this.2.2.2 ξ hξi; omega
      · rw [Book.M_pending h'] at hξi; simp at hξi
    · simp at h; omega
  -- the start time
  set Q := Setting.t4Q parts f with hQdef
  set t0 := S.t4t0 parts f b'.s with ht0def
  have ht0a : Q + S.nq Q ≤ t0 := le_max_left _ _
  have ht0b : b'.s + S.n2 b'.s ≤ t0 := le_max_right _ _
  have ht0nq : S.nq 0 ≤ t0 := by
    have := G.ok.nq_mono (Nat.zero_le Q)
    omega
  have hc : S.k1 t0 ≤ k + 1 + S.h (k + 1) := by
    have : S.k1 t0 = max (S.k1 (Q + S.nq Q)) (S.k1 (b'.s + S.n2 b'.s)) := by
      rw [ht0def]; unfold Setting.t4t0
      exact S.k1_mono.map_max
    rw [this, G.ok.k1_add_nq]
    exact max_le hQ (by omega)
  have hQc : Q ≤ S.k1 t0 := S.le_k1 ht0a
  -- the new core
  set E := Setting.t4E (k + 1) parts f with hEdef
  have hTdef : S.t4T (k + 1) parts f b'.s = S.Tmin E t0 := rfl
  have hqdef : S.t4q (k + 1) parts f b'.s = S.k1 (S.Tmin E t0) := rfl
  have hq1 : S.k1 t0 ≤ S.k1 (S.Tmin E t0) := G.ok.k1_le_q' E t0
  have hq2 : S.k1 (S.Tmin E t0) ≤ k + 1 + S.h (k + 1) + 1 :=
    G.ok.q'_le hE (by omega)
  -- the ripeness time
  have hT_spec := G.ok.Tmin_spec E t0
  have hT1 := G.ok.q'_add_nq_le (E := E) ht0nq
  have hT2 := G.ok.Tmin_le (E := E) (t0 := t0)
  -- the state
  have hnuν : 1 ≤ ∑ i ∈ parts, (f i).nu := by
    obtain ⟨i, hi⟩ := hne
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => (f i).nu) (fun _ _ => Nat.zero_le _) hi)
    rcases hact i hi with ⟨q, ν, M, h⟩ | ⟨q, ν, h⟩
    · have := (hinv i hi).adm; rw [S.adm_active h] at this; rw [Book.nu_active h]; exact this.2.1
    · have := (hinv i hi).adm; rw [S.adm_pending h] at this; rw [Book.nu_pending h]
      exact this.2.2.1
  set q' := S.k1 (S.Tmin E t0) with hq'
  have hcases : (q' ≤ k + 1 ∧ b'.st = .active q' (∑ i ∈ parts, (f i).nu)
        (E.filter (fun ξ => q' < ξ))) ∨
      (¬ q' ≤ k + 1 ∧ b'.st = .pending q' (∑ i ∈ parts, (f i).nu)) := by
    rw [hst]; unfold Setting.t4State
    by_cases h : S.t4q (k + 1) parts f b'.s ≤ k + 1
    · left
      have h' : q' ≤ k + 1 := h
      refine ⟨h', ?_⟩
      simp only [ite_true, h]; rfl
    · right
      have h' : ¬ q' ≤ k + 1 := h
      refine ⟨h', ?_⟩
      simp only [h, ite_false]; rfl
  have hqb : b'.q = q' := by
    rcases hcases with ⟨_, h⟩ | ⟨_, h⟩
    · exact Book.q_active h
    · exact Book.q_pending h
  have hnub : b'.nu = ∑ i ∈ parts, (f i).nu := by
    rcases hcases with ⟨_, h⟩ | ⟨_, h⟩
    · exact Book.nu_active h
    · exact Book.nu_pending h
  have htS : S.tStar b' = S.Tmin E t0 := by
    unfold Setting.tStar
    rw [hqb]
    apply le_antisymm
    · exact max_le hT1 (le_trans ht0b hT_spec.1)
    · refine hT2.trans (max_le (le_max_left _ _) ?_)
      refine max_le ?_ (le_max_right _ _)
      exact le_trans (Nat.add_le_add (hQc.trans hq1) (G.ok.nq_mono (hQc.trans hq1)))
        (le_max_left _ _)
  have hadm : S.Admissible (k + 1) b' := by
    rcases hcases with ⟨hq1', h⟩ | ⟨hq1', h⟩
    · rw [S.adm_active h]
      refine ⟨hq1', hnuν, hcap, fun ξ hξ => ?_⟩
      have := Finset.mem_filter.mp hξ
      exact ⟨this.2, hE ξ this.1⟩
    · rw [S.adm_pending h]
      exact ⟨by omega, by omega, hnuν, hcap⟩
  refine ⟨⟨hadm, hlen, hptl, fun h => by rw [hpt h], hnp, ?_, ?_, ?_⟩, hE, hQ, hk1small,
    hQc.trans hq1, hq2, htS, hlenν, hnub, hs_ge, hs_le, hqb⟩
  · intro _; rw [hnub]; exact hlenν
  · intro _
    rw [hqb, htS]
    exact S.lt_k1_succ _
  · rw [htS]
    have := hT_spec.1
    omega

end Setting.Good

end Balaban.LargeField
