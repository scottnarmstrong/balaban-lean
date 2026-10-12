module

public import Balaban.LargeField.History.WState
import Mathlib.Tactic.Linarith

/-!
# The combinatorics of the merge (T4) (Part I, Lemma I.4.10 (b), (B.3)–(B.4))

For a finite set `E` of merge records and a start time `t₀`, `T = Tmin E t₀` is the first
`t ≥ t₀` whose core `k₁(t)` is not blocked by `E`; `q' = k₁(T)` is the least unblocked integer
`≥ k₁(t₀)`.
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting

variable {S : Setting}

theorem mem_blocked {E : Finset ℕ} {c : ℕ} :
    c ∈ S.blocked E ↔ ∃ ξ ∈ E, ξ ≤ c ∧ c ≤ ξ + S.h ξ := Iff.rfl

theorem Tmin_min {E : Finset ℕ} {t0 t : ℕ} (h0 : t0 ≤ t) (h : t < S.Tmin E t0) :
    S.k1 t ∈ S.blocked E := by
  by_contra hcon
  have : S.Tmin E t0 ≤ t := Nat.sInf_le ⟨h0, hcon⟩
  omega

end Setting

namespace Setting.Ok

variable {S : Setting} (ok : S.Ok)

include ok

theorem Tmin_nonempty (E : Finset ℕ) (t0 : ℕ) :
    {t : ℕ | t0 ≤ t ∧ S.k1 t ∉ S.blocked E}.Nonempty := by
  set v := E.sup (fun ξ => ξ + S.h ξ) + 1 + S.k1 t0 with hv
  obtain ⟨t, ht0, ht⟩ := ok.exists_k1_eq (t₀ := t0) (v := v) (by omega)
  refine ⟨t, ht0, ?_⟩
  rw [ht]
  rintro ⟨ξ, hξ, _, h2⟩
  have : ξ + S.h ξ ≤ E.sup (fun ξ => ξ + S.h ξ) := Finset.le_sup (f := fun ξ => ξ + S.h ξ) hξ
  omega

theorem Tmin_spec (E : Finset ℕ) (t0 : ℕ) :
    t0 ≤ S.Tmin E t0 ∧ S.k1 (S.Tmin E t0) ∉ S.blocked E :=
  Nat.sInf_mem (ok.Tmin_nonempty E t0)

theorem k1_le_q' (E : Finset ℕ) (t0 : ℕ) : S.k1 t0 ≤ S.k1 (S.Tmin E t0) :=
  S.k1_mono (ok.Tmin_spec E t0).1

theorem q'_min {E : Finset ℕ} {t0 v : ℕ} (hv0 : S.k1 t0 ≤ v) (hv : v < S.k1 (S.Tmin E t0)) :
    v ∈ S.blocked E := by
  obtain ⟨t, ht0, htv⟩ := ok.exists_k1_eq hv0
  have : t < S.Tmin E t0 := by
    by_contra hcon
    have := S.k1_mono (not_lt.mp hcon)
    omega
  rw [← htv]
  exact S.Tmin_min ht0 this

theorem q'_not_blocked (E : Finset ℕ) (t0 : ℕ) : S.k1 (S.Tmin E t0) ∉ S.blocked E :=
  (ok.Tmin_spec E t0).2

/-- `q' ≤ μ + h_μ + 1` when all records are `≤ μ` and `k₁(t₀) ≤ μ + h_μ + 1`. -/
theorem q'_le {E : Finset ℕ} {t0 μ : ℕ} (hE : ∀ ξ ∈ E, ξ ≤ μ) (hc : S.k1 t0 ≤ μ + S.h μ + 1) :
    S.k1 (S.Tmin E t0) ≤ μ + S.h μ + 1 := by
  by_contra hcon
  have hcon := not_le.mp hcon
  have hb := ok.q'_min (E := E) (t0 := t0) hc hcon
  obtain ⟨ξ, hξ, _, h2⟩ := hb
  have h3 := ok.h_mono (hE ξ hξ)
  have h4 := hE ξ hξ
  omega

theorem q'_add_nq_le {E : Finset ℕ} {t0 : ℕ} (ht0 : S.nq 0 ≤ t0) :
    S.k1 (S.Tmin E t0) + S.nq (S.k1 (S.Tmin E t0)) ≤ S.Tmin E t0 :=
  S.k1_spec (le_trans ht0 (ok.Tmin_spec E t0).1)

/-- `T = t₀` or `T ≤ q' + n_q(q')`. -/
theorem Tmin_le {E : Finset ℕ} {t0 : ℕ} :
    S.Tmin E t0 ≤ max (S.k1 (S.Tmin E t0) + S.nq (S.k1 (S.Tmin E t0))) t0 := by
  set T := S.Tmin E t0 with hT
  by_cases h : T = t0
  · omega
  · have hlt : t0 ≤ T - 1 := by have := (ok.Tmin_spec E t0).1; omega
    have hlt2 : T - 1 < T := by have := (ok.Tmin_spec E t0).1; omega
    have hb := S.Tmin_min hlt hlt2
    have hne : S.k1 (T - 1) ≠ S.k1 T := fun heq => ok.q'_not_blocked E t0 (heq ▸ hb)
    have hle : S.k1 (T - 1) ≤ S.k1 T := S.k1_mono (by omega)
    have hlt3 : S.k1 (T - 1) < S.k1 T := lt_of_le_of_ne hle hne
    have : T - 1 < S.k1 T + S.nq (S.k1 T) := by
      by_contra hcon
      have := S.le_k1 (not_lt.mp hcon)
      omega
    omega

end Setting.Ok

end Balaban.LargeField
