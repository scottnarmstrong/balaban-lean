module

public import Balaban.LargeField.Counter.CapBank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Scales in a merge within the cap (Part I, (B.13), (B.14))
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

/-- `λ_μ ≤ 2 c_* λ_q` for the core `q` of an `Active` or `Pending` part. -/
theorem lam_core_ge {k : ℕ} {b : Book} (hb : BookInv S k b) (hpost : k < S.tStar b)
    (hact : b.IsActive ∨ b.IsPending) : S.lam (k + 1) ≤ 2 * S.cStar * S.lam b.q := by
  have hcs := G.ok.cStar_ge_one
  have hθ := G.ok.θp_pos
  have h0a := G.lc.l0_a (S.lam (k + 1)) (G.lam_ge _)
  have hq : S.lam (k + 1) ≤ S.cStar * (S.lam b.q + S.θp) := by
    rcases hact with ⟨q, ν, M, h⟩ | ⟨q, ν, h⟩
    · have hq := Book.q_active h
      have hf4 := hb.f4 (Or.inl ⟨q, ν, M, h⟩)
      rw [hq] at hf4 ⊢
      have h1 : k + 1 ≤ (q + 1) + (S.nq (q + 1) - 1) := by
        have := S.one_le_nq (q + 1); omega
      have h2 := G.ok.lam_mono h1
      have h3 := G.ok.lam_add_nq_sub_one (q + 1)
      have h4 := (G.ok.lam_step q).2
      have h5 : S.cStar * S.lam (q + 1) ≤ S.cStar * (S.lam q + S.θp) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
      linarith
    · have hq := Book.q_pending h
      have hadm := hb.adm
      rw [S.adm_pending h] at hadm
      rw [hq]
      have h1 : S.lam (k + 1) ≤ S.lam q := G.ok.lam_mono (by omega)
      have : S.lam q ≤ S.cStar * (S.lam q + S.θp) := by
        have := (G.ok.lam_pos q).le
        nlinarith
      linarith
  nlinarith [G.ok.lam_pos b.q, G.ok.lam_pos (k + 1)]

theorem lam_strip_ge {μ Q ξ : ℕ} (hQ : S.lam μ ≤ 2 * S.cStar * S.lam Q)
    (hξ : Q ≤ ξ + S.h μ) : S.lam μ / (4 * S.cStar) ≤ S.lam ξ := by
  have hcs := G.ok.cStar_ge_one
  have hθ := G.ok.θp_pos
  have hcpos : 0 < S.cStar := by linarith
  have h0b := G.lc.l0_b (S.lam μ) (G.lam_ge _)
  have hh := G.ok.h_le_bar μ
  have h1 : S.lam Q ≤ S.lam ξ + S.h μ * S.θp := by
    have := G.ok.lam_mono hξ
    have := G.ok.lam_add_le ξ (S.h μ)
    linarith
  have h2 : (S.h μ : ℝ) * S.θp ≤ S.hBar (S.lam μ) * S.θp := by gcongr
  have h3 : S.θp * (S.hBar (S.lam μ) + 2) ≤ S.lam μ / (4 * S.cStar) := h0b
  have h4 : S.lam μ / (2 * S.cStar) ≤ S.lam Q := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h5 : S.lam μ / (2 * S.cStar) = 2 * (S.lam μ / (4 * S.cStar)) := by
    field_simp; ring
  have : 0 ≤ S.θp := hθ.le
  nlinarith

theorem lam_T_le {μ T q' : ℕ} (hq1 : S.k1 T = q') (hq2 : q' ≤ μ + S.h μ + 1) :
    S.lam T ≤ 3 * S.cStar * S.lam μ := by
  have hcs := G.ok.cStar_ge_one
  have hθ := G.ok.θp_pos
  have hcpos : 0 < S.cStar := by linarith
  have h0b := G.lc.l0_b (S.lam μ) (G.lam_ge _)
  have hh := G.ok.h_le_bar μ
  have hT := S.lt_k1_succ T
  rw [hq1] at hT
  have h1 : T ≤ (q' + 1) + (S.nq (q' + 1) - 1) := by
    have := S.one_le_nq (q' + 1); omega
  have h2 := G.ok.lam_mono h1
  have h3 := G.ok.lam_add_nq_sub_one (q' + 1)
  have h4 : S.lam (q' + 1) ≤ S.lam (μ + (S.h μ + 2)) := G.ok.lam_mono (by omega)
  have h5 := G.ok.lam_add_le μ (S.h μ + 2)
  push_cast at h5
  have h6 : (S.h μ : ℝ) * S.θp ≤ S.hBar (S.lam μ) * S.θp := by gcongr
  have h7 : S.θp * (S.hBar (S.lam μ) + 2) ≤ S.lam μ / (4 * S.cStar) := h0b
  have h8 : S.lam μ / (4 * S.cStar) * S.cStar = S.lam μ / 4 := by field_simp
  have h9 : S.lam (q' + 1) ≤ S.lam μ + S.lam μ / (4 * S.cStar) := by nlinarith
  have h10 : S.cStar * S.lam (q' + 1) ≤ S.cStar * (S.lam μ + S.lam μ / (4 * S.cStar)) :=
    mul_le_mul_of_nonneg_left h9 hcpos.le
  have h11 : S.cStar * (S.lam μ + S.lam μ / (4 * S.cStar)) = S.cStar * S.lam μ + S.lam μ / 4 := by
    rw [mul_add, mul_comm S.cStar (S.lam μ / (4 * S.cStar)), h8]
  have hl := G.ok.lam_pos μ
  nlinarith

theorem tau_pay {μ ξ T : ℕ} (hξ : S.lam μ / (4 * S.cStar) ≤ S.lam ξ)
    (hT : S.lam T ≤ 3 * S.cStar * S.lam μ) :
    (S.cStar * (S.h μ + 1) + 1) * S.Abar (S.lam T) ≤ 1 / 2 * S.tau ξ := by
  have hcs := G.ok.cStar_ge_one
  have h6 := G.lc.l6 (S.lam μ) (G.lam_ge _)
  have hh := G.ok.h_le_bar μ
  have hAm : S.Abar (S.lam T) ≤ S.Abar (3 * S.cStar * S.lam μ) :=
    G.ok.Abar_mono (G.ok.lam_pos _).le hT
  have hA0 : 0 ≤ S.Abar (S.lam T) := by
    have := G.ok.A2_pos; have := G.ok.θp_pos; have := G.ok.Cw_nonneg
    have := (G.ok.lam_pos T).le
    unfold Typing.Abar; positivity
  have h1 : (S.cStar * (S.h μ + 1) + 1) ≤ (S.cStar * (S.hBar (S.lam μ) + 1) + 1) := by
    have : (0 : ℝ) ≤ S.cStar := by linarith
    nlinarith
  have h2 : (S.cStar * (S.h μ + 1) + 1) * S.Abar (S.lam T) ≤
      (S.cStar * (S.hBar (S.lam μ) + 1) + 1) * S.Abar (3 * S.cStar * S.lam μ) := by
    have : 0 ≤ S.cStar * (S.h μ + 1) + 1 := by positivity
    calc (S.cStar * (S.h μ + 1) + 1) * S.Abar (S.lam T)
        ≤ (S.cStar * (S.h μ + 1) + 1) * S.Abar (3 * S.cStar * S.lam μ) := by gcongr
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right h1
        exact hA0.trans hAm
  have hA2 := G.ok.A2_pos
  have h4 : S.A2 * (S.lam μ / (4 * S.cStar)) ^ S.p2 ≤ S.A2 * S.lam ξ ^ S.p2 := by
    have : 0 ≤ S.lam μ / (4 * S.cStar) := by
      have := G.ok.lam_pos μ; positivity
    gcongr
  unfold Setting.tau
  linarith

end Setting.Good

end Balaban.LargeField
