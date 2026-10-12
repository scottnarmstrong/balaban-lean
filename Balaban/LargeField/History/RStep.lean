module

public import Balaban.LargeField.History.Step
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The step `R^{(k)}` (T6): ripe components are removed or kept as `Active(k, 1, ∅)`
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting

variable {S : Setting}

/-- A ripe book has a point spine of length `0` and a clock `s ≤ k`
(Lemma I.4.13 (g), numerical part). -/
theorem ripe_facts {k : ℕ} {b : Book} (hb : BookInv S k b) (hr : S.Ripe k b) :
    b.pt ∧ b.len = 0 ∧ b.s + S.n2 b.s ≤ k := by
  have h1 := S.tStar_ge_right b
  have h2 := S.ripe_tStar hr
  have hpt : b.pt := by
    by_contra hp
    have := hb.np_clock hp
    omega
  exact ⟨hpt, hb.pt_len hpt, by omega⟩

end Setting

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

/-- The invariant after `R^{(k)}` ((T6)), `1 ≤ k ≤ k₀`. -/
theorem rstep_inv {k k0 : ℕ} (hk1 : 1 ≤ k) (hk0 : k ≤ k0) {b : Book} (hb : BookInv S k b) :
    BookInv S k (S.postBook k0 k b) ∧ k < S.tStar (S.postBook k0 k b) ∧
      (S.Ripe k b → (S.postBook k0 k b).len = 0 ∧ (S.postBook k0 k b).nu = 1 ∧
        S.bank (S.postBook k0 k b) = 0 ∧ S.tStar (S.postBook k0 k b) = k + S.nq k) := by
  by_cases hr : S.Ripe k b
  · obtain ⟨hpt, hlen0, hsn⟩ := S.ripe_facts hb hr
    have hkb : S.postBook k0 k b = b.kept k := S.postBook_of_ripe hk1 hk0 hr
    rw [hkb]
    have hst : (b.kept k).st = .active k 1 ∅ := rfl
    have htS : S.tStar (b.kept k) = k + S.nq k := by
      unfold Setting.tStar
      rw [Book.q_active hst]
      show max (k + S.nq k) (b.s + S.n2 b.s) = k + S.nq k
      have := S.one_le_nq k
      omega
    have hnu : (b.kept k).nu = 1 := Book.nu_active hst
    have hlen : (b.kept k).len = 0 := hlen0
    have hbank : S.bank (b.kept k) = 0 := by rw [S.bank_active hst]; simp
    have hadm : S.Admissible k (b.kept k) := by
      rw [S.adm_active hst]; exact ⟨le_rfl, le_rfl, G.ok.one_le_numax k, by simp⟩
    have hq : (b.kept k).q = k := Book.q_active hst
    refine ⟨⟨hadm, hb.len_nonneg, fun _ => hlen, fun _ => by
      show b.s ≤ k; have := hsn; omega, fun h => absurd hpt h, ?_, ?_, ?_⟩, ?_, fun _ => ⟨hlen, hnu, hbank, htS⟩⟩
    · intro _; rw [hlen, hnu]; simp
    · intro _
      rw [htS, hq]
      have := G.ok.nq_mono (show k ≤ k + 1 by omega)
      omega
    · rw [htS]; omega
    · rw [htS]; have := S.one_le_nq k; omega
  · rw [S.postBook_of_not_ripe hr]
    refine ⟨hb, ?_, fun h => absurd h hr⟩
    have hge := hb.tstar_ge
    rcases Book.cases_st b with hpre | ⟨q, ν, hpend⟩ | ⟨q, ν, M, hact⟩
    · have hnp : ¬ b.pt := (S.adm_pre hpre).mp hb.adm
      have := hb.np_clock hnp
      rw [G.tStar_pre hpre]
      have := S.one_le_nq b.s
      omega
    · have := hb.adm; rw [S.adm_pending hpend] at this
      have := S.tStar_ge_left b
      rw [Book.q_pending hpend] at this
      have := S.one_le_nq q
      omega
    · have hne : S.tStar b ≠ k := fun h => hr ⟨⟨q, ν, M, hact⟩, h⟩
      omega

end Setting.Good

end Balaban.LargeField
