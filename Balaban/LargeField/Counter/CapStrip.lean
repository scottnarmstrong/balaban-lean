module

public import Balaban.LargeField.Counter.CaseMerge2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The strip shift of a merge within the cap (Part I, (B.9)–(B.12))

For a record set `E` and a start time `t₀`, let `T = Tmin E t₀`, `q' = k₁(T)`, `c = k₁(t₀)` and
`X = {ξ ∈ E : ξ < q', c ≤ ξ + h_ξ}`.  Then `q' - c ≤ ∑_{ξ ∈ X} (h_ξ + 1)`, and the shift
`T - t₀` is at most `|X| (c_*(h_μ + 1) + 1)`.
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting

variable (S : Setting)

/-- The set `X = {ξ ∈ E : ξ < q', c ≤ ξ + h_ξ}` of (B.9). -/
noncomputable def stripSet (E : Finset ℕ) (t0 : ℕ) : Finset ℕ :=
  E.filter (fun ξ => ξ < S.k1 (S.Tmin E t0) ∧ S.k1 t0 ≤ ξ + S.h ξ)


theorem mem_stripSet {E : Finset ℕ} {t0 ξ : ℕ} :
    ξ ∈ S.stripSet E t0 ↔
      ξ ∈ E ∧ ξ < S.k1 (S.Tmin E t0) ∧ S.k1 t0 ≤ ξ + S.h ξ := by
  unfold Setting.stripSet; simp [Finset.mem_filter]

end Setting

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

theorem strip_card (E : Finset ℕ) (t0 : ℕ) :
    S.k1 (S.Tmin E t0) - S.k1 t0 ≤ ∑ ξ ∈ S.stripSet E t0, (S.h ξ + 1) := by
  classical
  have hsub : Finset.Ico (S.k1 t0) (S.k1 (S.Tmin E t0)) ⊆
      (S.stripSet E t0).biUnion (fun ξ => Finset.Icc ξ (ξ + S.h ξ)) := by
    intro v hv
    rw [Finset.mem_Ico] at hv
    have hb := G.ok.q'_min (E := E) (t0 := t0) hv.1 hv.2
    obtain ⟨ξ, hξ, h1, h2⟩ := hb
    rw [Finset.mem_biUnion]
    refine ⟨ξ, S.mem_stripSet.mpr ⟨hξ, by omega, by omega⟩, Finset.mem_Icc.mpr ⟨h1, h2⟩⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := S.stripSet E t0) (t := fun ξ => Finset.Icc ξ (ξ + S.h ξ))
  simp only [Nat.card_Icc, Nat.card_Ico] at h1 h2
  have h3 : ∑ ξ ∈ S.stripSet E t0, (ξ + S.h ξ + 1 - ξ) = ∑ ξ ∈ S.stripSet E t0, (S.h ξ + 1) := by
    apply Finset.sum_congr rfl; intro ξ _; omega
  omega

/-- The shift `T - t₀` of a merge within the cap. -/
theorem delta2_bound {E : Finset ℕ} {t0 μ : ℕ} (ht0 : S.nq 0 ≤ t0) (hE : ∀ ξ ∈ E, ξ ≤ μ) :
    ((S.Tmin E t0 - t0 : ℕ) : ℝ) ≤
      ((S.stripSet E t0).card : ℝ) * (S.cStar * (S.h μ + 1) + 1) := by
  have hc0 : 0 ≤ S.cStar := by linarith [G.ok.cStar_ge_one]
  have hspec := G.ok.Tmin_spec E t0
  by_cases hc : S.k1 t0 ∈ S.blocked E
  · -- `T = q' + n_q(q')` and `t₀ ≥ c + n_q(c)`
    have hTgt : t0 < S.Tmin E t0 := by
      rcases Nat.eq_or_lt_of_le hspec.1 with h | h
      · exfalso; apply hspec.2; rw [← h]; exact hc
      · exact h
    have hTle := G.ok.Tmin_le (E := E) (t0 := t0)
    have hT1 := G.ok.q'_add_nq_le (E := E) ht0
    have hTeq : S.Tmin E t0 = S.k1 (S.Tmin E t0) + S.nq (S.k1 (S.Tmin E t0)) := by
      rcases le_max_iff.mp (show S.Tmin E t0 ≤ max _ t0 from hTle) with h | h
      · omega
      · omega
    have ht0c : S.k1 t0 + S.nq (S.k1 t0) ≤ t0 := S.k1_spec ht0
    have hcq : S.k1 t0 ≤ S.k1 (S.Tmin E t0) := G.ok.k1_le_q' E t0
    obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le hcq
    have hts := G.t_shift (S.k1 t0) x
    have hX : 1 ≤ (S.stripSet E t0).card := by
      apply Finset.card_pos.mpr
      have hlt : S.k1 t0 < S.k1 (S.Tmin E t0) := by
        rcases Nat.eq_or_lt_of_le hcq with h | h
        · exfalso; apply hspec.2; rw [← h]; exact hc
        · exact h
      obtain ⟨ξ, hξ, h1, h2⟩ := hc
      exact ⟨ξ, S.mem_stripSet.mpr ⟨hξ, by omega, by omega⟩⟩
    have hstrip := G.strip_card E t0
    have hsum : ∑ ξ ∈ S.stripSet E t0, (S.h ξ + 1) ≤ (S.stripSet E t0).card * (S.h μ + 1) := by
      have := Finset.sum_le_card_nsmul (S.stripSet E t0) (fun ξ => S.h ξ + 1) (S.h μ + 1)
        (fun ξ hξ => by
          have := (S.mem_stripSet.mp hξ).1
          have := G.ok.h_mono (hE ξ this)
          omega)
      simpa using this
    have hxle : (x : ℝ) ≤ ((S.stripSet E t0).card : ℝ) * (S.h μ + 1) := by
      have : x ≤ (S.stripSet E t0).card * (S.h μ + 1) := by omega
      exact_mod_cast this
    have hT' : ((S.Tmin E t0 : ℕ) : ℝ) ≤ (t0 : ℝ) + S.cStar * x + 1 := by
      have e : S.Tmin E t0 = S.k1 t0 + x + S.nq (S.k1 t0 + x) := by rw [← hx]; exact hTeq
      have h1 : ((S.k1 t0 + S.nq (S.k1 t0) : ℕ) : ℝ) ≤ t0 := by exact_mod_cast ht0c
      rw [e]; push_cast at hts h1 ⊢; linarith
    have hcard : (1 : ℝ) ≤ (S.stripSet E t0).card := by exact_mod_cast hX
    have h5 : S.cStar * (x : ℝ) ≤ S.cStar * (((S.stripSet E t0).card : ℝ) * (S.h μ + 1)) :=
      mul_le_mul_of_nonneg_left hxle hc0
    rcases le_total t0 (S.Tmin E t0) with h | h
    · rw [Nat.cast_sub h]
      nlinarith
    · omega
  · -- `T = t₀`
    have hTeq : S.Tmin E t0 = t0 := by
      apply le_antisymm
      · exact Nat.sInf_le ⟨le_rfl, hc⟩
      · exact hspec.1
    rw [hTeq]
    simp only [Nat.sub_self, Nat.cast_zero]
    have : 0 ≤ ((S.stripSet E t0).card : ℝ) * (S.cStar * (S.h μ + 1) + 1) := by positivity
    exact this

end Setting.Good

end Balaban.LargeField
