module

public import Balaban.LargeField.Counter.CapDelta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Case 2a: merge within the cap ((T4), Part I §I.5.4)
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

/-- (B.7) for a merge within the cap. -/
theorem case_cap {k : ℕ} {ι : Type*} {P : Finset ι} {f : ι → Book} {b' : Book}
    (hinv : ∀ i ∈ P, BookInv S k (f i)) (hpost : ∀ i ∈ P, k < S.tStar (f i))
    (hact : ∀ i ∈ P, (f i).IsActive ∨ (f i).IsPending) (hcard : 2 ≤ P.card)
    (hcap : ∑ i ∈ P, (f i).nu ≤ S.numax (k + 1)) (hT : T4Facts S k P f b')
    (hlen : b'.len ≤ ∑ i ∈ P, (f i).len / S.L + (((P.card + 0 : ℕ) : ℝ) - 1) * S.D (k + 1)) :
    S.B7 k P f 0 b' := by
  classical
  have hne : P.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i0, hi0, hmax0⟩ := Finset.exists_max_image P (fun i => S.tStar (f i)) hne
  obtain ⟨i1, hi1, hmax1⟩ := Finset.exists_max_image P (fun i => (f i).len) hne
  have hm : (2 : ℝ) ≤ P.card := by exact_mod_cast hcard
  have hlenP : ∀ j ∈ P, 0 ≤ (f j).len := fun j hj => (hinv j hj).len_nonneg
  have hcs := G.ok.cStar_ge_one
  have hl := G.ok.lam_pos (k + 1)
  have hμt : ∀ i ∈ P, k + 1 ≤ S.tStar (f i) := fun i hi => hpost i hi
  -- the data of the merge
  set E := Setting.t4E (k + 1) P f with hEdef
  set t0 := S.t4t0 P f b'.s with ht0def
  set Q := Setting.t4Q P f with hQdef
  have hTdef : S.tStar b' = S.Tmin E t0 := hT.tStar_eq
  have ht0nq : S.nq 0 ≤ t0 := by
    have h1 : Q + S.nq Q ≤ t0 := le_max_left _ _
    have := G.ok.nq_mono (Nat.zero_le Q)
    omega
  have hQc : Q ≤ S.k1 t0 := S.le_k1 (le_max_left _ _)
  have hqdef : S.k1 (S.Tmin E t0) = S.t4q (k + 1) P f b'.s := rfl
  -- shifts
  have hD1 := G.delta1_bound hinv hpost hne hcap hmax0 hi1 hmax1 hlen hT
  have hD2 := G.delta2_bound (E := E) (t0 := t0) (μ := k + 1) ht0nq hT.E_le
  have hT0 : k + 1 ≤ S.tStar (f i0) := hμt i0 hi0
  have htel := G.telescope hT0 (S.tStar b')
  rw [hTdef] at htel
  have hAb0 : 0 ≤ S.Abar (S.lam (S.Tmin E t0)) := by
    have := G.ok.A2_pos; have := G.ok.θp_pos; have := G.ok.Cw_nonneg
    have := (G.ok.lam_pos (S.Tmin E t0)).le
    unfold Typing.Abar; positivity
  have hspec := G.ok.Tmin_spec E t0
  have hnatsub : S.Tmin E t0 - S.tStar (f i0) ≤ (t0 - S.tStar (f i0)) + (S.Tmin E t0 - t0) := by
    have := hspec.1
    omega
  have hnatR : ((S.Tmin E t0 - S.tStar (f i0) : ℕ) : ℝ) ≤
      ((t0 - S.tStar (f i0) : ℕ) : ℝ) + ((S.Tmin E t0 - t0 : ℕ) : ℝ) := by
    exact_mod_cast hnatsub
  -- scales
  obtain ⟨iQ, hiQ, hQeq⟩ := Finset.exists_mem_eq_sup P hne (fun i => (f i).q)
  have hQb : (f iQ).q = Q := hQeq.symm
  have hcore := G.lam_core_ge (hinv iQ hiQ) (hpost iQ hiQ) (hact iQ hiQ)
  rw [hQb] at hcore
  have hlamT : S.lam (S.Tmin E t0) ≤ 3 * S.cStar * S.lam (k + 1) :=
    G.lam_T_le (μ := k + 1) (T := S.Tmin E t0) (q' := S.t4q (k + 1) P f b'.s) hqdef hT.q_le
  -- payment of the strip
  have hpayξ : ∀ ξ ∈ S.stripSet E t0,
      (S.cStar * (S.h (k + 1) + 1) + 1) * S.Abar (S.lam (S.Tmin E t0)) ≤ 1 / 2 * S.tau ξ := by
    intro ξ hξ
    obtain ⟨hξE, -, hξc⟩ := S.mem_stripSet.mp hξ
    have hξμ := hT.E_le ξ hξE
    have hh := G.ok.h_mono hξμ
    have hQξ : Q ≤ ξ + S.h (k + 1) := by omega
    exact G.tau_pay (G.lam_strip_ge hcore hQξ) hlamT
  have hΔ2A : ((S.Tmin E t0 - t0 : ℕ) : ℝ) * S.Abar (S.lam (S.Tmin E t0)) ≤
      1 / 2 * ∑ ξ ∈ S.stripSet E t0, S.tau ξ := by
    have h1 : ((S.stripSet E t0).card : ℝ) *
        ((S.cStar * (S.h (k + 1) + 1) + 1) * S.Abar (S.lam (S.Tmin E t0))) ≤
        ∑ ξ ∈ S.stripSet E t0, (1 / 2 * S.tau ξ) := by
      have := Finset.card_nsmul_le_sum (S.stripSet E t0) (fun ξ => 1 / 2 * S.tau ξ)
        ((S.cStar * (S.h (k + 1) + 1) + 1) * S.Abar (S.lam (S.Tmin E t0))) hpayξ
      simpa using this
    rw [← Finset.mul_sum] at h1
    calc ((S.Tmin E t0 - t0 : ℕ) : ℝ) * S.Abar (S.lam (S.Tmin E t0))
        ≤ (((S.stripSet E t0).card : ℝ) * (S.cStar * (S.h (k + 1) + 1) + 1)) *
            S.Abar (S.lam (S.Tmin E t0)) := by gcongr
      _ = ((S.stripSet E t0).card : ℝ) *
          ((S.cStar * (S.h (k + 1) + 1) + 1) * S.Abar (S.lam (S.Tmin E t0))) := by ring
      _ ≤ _ := h1
  have hΔ1A : ((t0 - S.tStar (f i0) : ℕ) : ℝ) * S.Abar (S.lam (S.Tmin E t0)) ≤
      1 / 2 * S.A2 * S.lam (k + 1) ^ S.p2 := by
    have h5a := G.lc.l5_a (S.lam (k + 1)) (G.lam_ge _)
    have hAm : S.Abar (S.lam (S.Tmin E t0)) ≤ S.Abar (3 * S.cStar * S.lam (k + 1)) :=
      G.ok.Abar_mono (G.ok.lam_pos _).le hlamT
    calc ((t0 - S.tStar (f i0) : ℕ) : ℝ) * S.Abar (S.lam (S.Tmin E t0))
        ≤ S.DeltaBar (S.lam (k + 1)) * S.Abar (3 * S.cStar * S.lam (k + 1)) := by
          have hD0 : (0 : ℝ) ≤ ((t0 - S.tStar (f i0) : ℕ) : ℝ) := Nat.cast_nonneg _
          have hAm0 : 0 ≤ S.Abar (3 * S.cStar * S.lam (k + 1)) := hAb0.trans hAm
          have hΔ0 := G.DeltaBar_nonneg hl.le
          calc _ ≤ ((t0 - S.tStar (f i0) : ℕ) : ℝ) * S.Abar (3 * S.cStar * S.lam (k + 1)) := by
                gcongr
            _ ≤ _ := by gcongr
      _ ≤ _ := h5a
  -- the banks
  have hbank := G.bank_ineq hT
  -- the sum of the parts
  have hsplit := sum_split (P := P) (i0 := i0)
    (h := fun j => S.tau (S.tStar (f j)) + S.W (k + 1) (S.tStar (f j))) (c := S.tau (k + 1))
    hi0 (fun j hj => by
      have h1 := G.ok.tau_mono (hμt j hj)
      have h2 := G.ok.W_nonneg (k + 1) (S.tStar (f j))
      show S.tau (k + 1) ≤ _
      linarith)
  have hν : ∑ i ∈ P, ((f i).nu : ℝ) = (b'.nu : ℝ) := by
    rw [hT.nu_eq]; push_cast; rfl
  have hA : 0 ≤ S.v (k + 1) / S.L * ∑ i ∈ P, (f i).len := by
    have := G.ok.v_nonneg (k + 1)
    have : 0 ≤ ∑ i ∈ P, (f i).len := Finset.sum_nonneg hlenP
    have := G.ok.cast_L_ge
    positivity
  have hE5 := G.lc.l5_b (S.lam (k + 1)) (G.lam_ge _)
  have hEl := G.ok.E_le (k + 1)
  have hτdef : S.tau (k + 1) = 2 * (S.A2 * S.lam (k + 1) ^ S.p2) := by unfold Setting.tau; ring
  have ha2 : 0 ≤ S.A2 * S.lam (k + 1) ^ S.p2 := by
    have := G.ok.A2_pos; positivity
  have hEb : S.E (k + 1) ≤ 1 / 2 * S.A2 * S.lam (k + 1) ^ S.p2 := hEl.trans hE5
  have hm1 : (0 : ℝ) ≤ (P.card : ℝ) - 2 := by linarith
  have hsumsplit : ∑ i ∈ P, (S.tau (S.tStar (f i)) + S.W (k + 1) (S.tStar (f i)) + (f i).nu +
      S.bank (f i)) = ∑ i ∈ P, (S.tau (S.tStar (f i)) + S.W (k + 1) (S.tStar (f i))) +
      ∑ i ∈ P, ((f i).nu : ℝ) + ∑ i ∈ P, S.bank (f i) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hmulE : ((P.card : ℝ) - 1) * S.E (k + 1) ≤ ((P.card : ℝ) - 1) *
      (1 / 2 * S.A2 * S.lam (k + 1) ^ S.p2) := by
    apply mul_le_mul_of_nonneg_left hEb; linarith
  unfold Setting.B7
  rw [hTdef]
  push_cast
  simp only [add_zero, mul_zero] at *
  rw [hsumsplit]
  have hcast : ((S.Tmin E t0 - S.tStar (f i0) : ℕ) : ℝ) * S.Abar (S.lam (S.Tmin E t0)) ≤
      ((t0 - S.tStar (f i0) : ℕ) : ℝ) * S.Abar (S.lam (S.Tmin E t0)) +
      ((S.Tmin E t0 - t0 : ℕ) : ℝ) * S.Abar (S.lam (S.Tmin E t0)) := by
    rw [← add_mul]; exact mul_le_mul_of_nonneg_right hnatR hAb0
  nlinarith [mul_nonneg hm1 ha2, hbank, hsplit, htel, hcast, hΔ1A, hΔ2A, hmulE, hν, hA]

end Setting.Good

end Balaban.LargeField
