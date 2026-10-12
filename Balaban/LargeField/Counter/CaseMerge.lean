module

public import Balaban.LargeField.Counter.CaseShadow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Case 2b: merge with a `Pre` part ((T3), Part I §I.5.4)
-/

@[expose] public section

namespace Balaban.LargeField

theorem nat_sub_cast_le {a b : ℕ} {R : ℝ} (hR : 0 ≤ R) (h : (b : ℝ) ≤ a + R) :
    ((b - a : ℕ) : ℝ) ≤ R := by
  rcases le_total a b with hab | hab
  · rw [Nat.cast_sub hab]; linarith
  · have : b - a = 0 := by omega
    rw [this]; simpa using hR

theorem BookInv.one_le_nu {S : Setting} {k : ℕ} {b : Book} (hb : BookInv S k b) : 1 ≤ b.nu := by
  rcases Book.cases_st b with h | ⟨q, ν, h⟩ | ⟨q, ν, M, h⟩
  · rw [Book.nu_pre h]
  · have := hb.adm; rw [S.adm_pending h] at this; rw [Book.nu_pending h]; exact this.2.2.1
  · have := hb.adm; rw [S.adm_active h] at this; rw [Book.nu_active h]; exact this.2.1

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

theorem Gbar_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ S.Gbar x := by
  have hL := G.ok.cast_L_ge
  have h1 := G.ok.cStar_ge_one
  have h2 := G.ok.one_le_nuBar hx
  have h3 := G.ok.one_le_Dbar x
  have h4 : 0 ≤ Real.logb S.L (S.nuBar x * S.Dbar x) :=
    Real.logb_nonneg (by linarith) (by nlinarith)
  have h5 : 0 ≤ Real.logb S.L (1 + S.Dbar x) :=
    Real.logb_nonneg (by linarith) (by linarith)
  unfold Typing.Gbar
  positivity

theorem len_le_numax {k : ℕ} {b : Book} (hb : BookInv S k b) (h : b.IsActive ∨ b.IsPending) :
    b.len ≤ S.numax (k + 1) * S.D (k + 1) := by
  have h1 := hb.len_nu h
  have hν : b.nu ≤ S.numax k := by
    rcases h with ⟨q, ν, M, h⟩ | ⟨q, ν, h⟩
    · have := hb.adm; rw [S.adm_active h] at this; rw [Book.nu_active h]; exact this.2.2.1
    · have := hb.adm; rw [S.adm_pending h] at this; rw [Book.nu_pending h]; exact this.2.2.2
  have h2 : (b.nu : ℝ) ≤ S.numax (k + 1) :=
    by exact_mod_cast hν.trans (G.ok.numax_mono (Nat.le_succ k))
  have hD : S.D k ≤ S.D (k + 1) := G.ok.D_mono (Nat.le_succ k)
  have hD0 := S.D_nonneg k
  have hν1 : (1 : ℝ) ≤ b.nu := by exact_mod_cast hb.one_le_nu
  calc b.len ≤ ((b.nu : ℝ) - 1) * S.D k := h1
    _ ≤ (S.numax (k + 1) : ℝ) * S.D (k + 1) := by
      have : (0 : ℝ) ≤ (b.nu : ℝ) - 1 := by linarith
      have hD1 := S.D_nonneg (k + 1)
      calc ((b.nu : ℝ) - 1) * S.D k ≤ (b.nu : ℝ) * S.D (k + 1) := by
            have : ((b.nu : ℝ) - 1) ≤ b.nu := by linarith
            gcongr
        _ ≤ _ := by gcongr

theorem t_shift (a x : ℕ) :
    ((a + x + S.nq (a + x) : ℕ) : ℝ) ≤ a + S.nq a + S.cStar * x + 1 := by
  have h := G.ok.nq_add_le a x
  have hαL := G.ok.αlogL_pos
  have e : S.cStar * x = x + S.θp * x / (S.α * S.logL) := by
    unfold Typing.cStar; field_simp
  push_cast
  linarith

theorem shift_A {k s1 s' : ℕ} {Λ1 Λ' B : ℝ} (hΛ1 : (k : ℝ) + Λ1 ≤ s1)
    (hs2 : (s' : ℝ) ≤ k + 2 + Λ') (hΛ : Λ' ≤ Λ1 + B) (hB : 0 ≤ B) :
    ((s' + S.nq s' : ℕ) : ℝ) ≤ s1 + S.nq s1 + S.cStar * (2 + B) + 1 := by
  have hc0 : 0 ≤ S.cStar := by linarith [G.ok.cStar_ge_one]
  have hcB : 0 ≤ S.cStar * (2 + B) := mul_nonneg hc0 (by linarith)
  by_cases hcmp : s1 ≤ s'
  · obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le hcmp
    have hts := G.t_shift s1 x
    have hxR : (x : ℝ) ≤ 2 + B := by
      have : ((s' : ℕ) : ℝ) = s1 + x := by rw [hx]; push_cast; ring
      linarith
    have := mul_le_mul_of_nonneg_left hxR hc0
    rw [hx]
    linarith
  · have hlt := not_le.mp hcmp
    have h1 : S.nq s' ≤ S.nq s1 := G.ok.nq_mono hlt.le
    have : s' + S.nq s' ≤ s1 + S.nq s1 := by omega
    have h2 : ((s' + S.nq s' : ℕ) : ℝ) ≤ ((s1 + S.nq s1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h2 ⊢
    linarith

theorem shift_B {μ s' : ℕ} {Λ' B : ℝ} (hs1 : μ ≤ s') (hs2 : (s' : ℝ) ≤ μ + 1 + Λ')
    (hΛ : Λ' ≤ B) :
    ((s' + S.nq s' : ℕ) : ℝ) ≤ μ + S.nq μ + S.cStar * (1 + B) + 1 := by
  have hc0 : 0 ≤ S.cStar := by linarith [G.ok.cStar_ge_one]
  obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le hs1
  have hts := G.t_shift μ x
  have hxR : (x : ℝ) ≤ 1 + B := by
    have : ((s' : ℕ) : ℝ) = μ + x := by rw [hx]; push_cast; ring
    linarith
  have := mul_le_mul_of_nonneg_left hxR hc0
  rw [hx]
  linarith

/-- The bound `Δ ≤ (m - 1)(Ḡ(λ) + 2c_*)` on the shift of the ripeness time after a merge with a
`Pre` part (B.9)–(B.13), second half of Case 2b. -/
theorem delta_pre {k : ℕ} {ι : Type*} {P : Finset ι} {f : ι → Book} {b' : Book} {i0 i1 p : ι}
    (hinv : ∀ i ∈ P, BookInv S k (f i))
    (hcard : 2 ≤ P.card) (hp : p ∈ P) (hppre : (f p).st = .pre)
    (hmax0 : ∀ j ∈ P, S.tStar (f j) ≤ S.tStar (f i0))
    (hi1 : i1 ∈ P) (hmax1 : ∀ j ∈ P, (f j).len ≤ (f i1).len)
    (hf : RestartFacts S k b')
    (hlen : b'.len ≤ ∑ i ∈ P, (f i).len / S.L + (((P.card + 0 : ℕ) : ℝ) - 1) * S.D (k + 1)) :
    ((S.tStar b' - S.tStar (f i0) : ℕ) : ℝ) ≤
      ((P.card : ℝ) - 1) * (S.Gbar (S.lam (k + 1)) + 2 * S.cStar) := by
  have hL := G.ok.cast_L_ge
  have hcs := G.ok.cStar_ge_one
  have hm : (2 : ℝ) ≤ P.card := by exact_mod_cast hcard
  have hlenP : ∀ j ∈ P, 0 ≤ (f j).len := fun j hj => (hinv j hj).len_nonneg
  have hD0 : 0 ≤ S.D (k + 1) := S.D_nonneg _
  have hDl : S.D (k + 1) ≤ S.Dbar (S.lam (k + 1)) := G.ok.D_le_bar _
  obtain ⟨ht, hs1, hs2, -, -⟩ := hf
  have hlb := G.len_log_bound (P := P) (f := f) hi1 hmax1 hlenP hD0 (by simpa using hlen)
  have hY0 : 0 ≤ Real.logb S.L (S.nuBar (S.lam (k + 1)) * S.Dbar (S.lam (k + 1))) := by
    have := G.ok.one_le_nuBar (G.ok.lam_pos (k + 1)).le
    have := G.ok.one_le_Dbar (S.lam (k + 1))
    exact Real.logb_nonneg (by linarith) (by nlinarith)
  have hlm : Real.logb S.L (P.card : ℝ) ≤ (P.card : ℝ) - 1 :=
    logb_le_pred hL (m := P.card) (by omega)
  have hlm0 : 0 ≤ Real.logb S.L (P.card : ℝ) :=
    Real.logb_nonneg (by linarith) (by linarith)
  have hld0 : 0 ≤ Real.logb S.L (1 + S.D (k + 1)) :=
    Real.logb_nonneg (by linarith) (by linarith)
  have hld : Real.logb S.L (1 + S.D (k + 1)) ≤ Real.logb S.L (1 + S.Dbar (S.lam (k + 1))) :=
    Real.logb_le_logb_of_le (by linarith) (by linarith) (by linarith)
  have hGb : S.Gbar (S.lam (k + 1)) = S.cStar * (2 +
      Real.logb S.L (S.nuBar (S.lam (k + 1)) * S.Dbar (S.lam (k + 1))) +
      Real.logb S.L (1 + S.Dbar (S.lam (k + 1)))) + 1 := by
    unfold Typing.Gbar; ring
  have hGb0 := G.Gbar_nonneg (G.ok.lam_pos (k + 1)).le
  -- the shift: `t' ≤ t0 + R'`
  have hpnp : ¬ (f p).pt := (S.adm_pre hppre).mp (hinv p hp).adm
  have hsp : k + 1 ≤ (f p).s := by have := (hinv p hp).np_clock hpnp; omega
  have htp : S.tStar (f p) = (f p).s + S.nq (f p).s := G.tStar_pre hppre
  have ht0p : S.tStar (f p) ≤ S.tStar (f i0) := hmax0 p hp
  have hc0 : 0 ≤ S.cStar := by linarith
  have htR : (S.tStar b' : ℝ) = ((b'.s + S.nq b'.s : ℕ) : ℝ) := by rw [ht]
  have hs2' : (b'.s : ℝ) ≤ k + 2 + Real.logb S.L (max b'.len 1) := by
    push_cast at hs2; linarith
  have hshift : (S.tStar b' : ℝ) ≤ S.tStar (f i0) + (S.cStar * (2 +
      Real.logb S.L (S.nuBar (S.lam (k + 1)) * S.Dbar (S.lam (k + 1))) +
      Real.logb S.L (P.card : ℝ) + Real.logb S.L (1 + S.D (k + 1))) + 1) := by
    rw [htR]
    by_cases hpre1 : (f i1).st = .pre
    · have hnp1 : ¬ (f i1).pt := (S.adm_pre hpre1).mp (hinv i1 hi1).adm
      have hs1' := (hinv i1 hi1).np_clock hnp1
      have ht1 : S.tStar (f i1) = (f i1).s + S.nq (f i1).s := G.tStar_pre hpre1
      have ht0 : S.tStar (f i1) ≤ S.tStar (f i0) := hmax0 i1 hi1
      have hΛ1ge : (k : ℝ) + Real.logb S.L (max (f i1).len 1) ≤ (f i1).s := by
        have h1 := Nat.le_ceil (Real.logb S.L (max (f i1).len 1))
        have h2 : ((⌈Real.logb S.L (max (f i1).len 1)⌉₊ : ℕ) : ℝ) ≤
            ((max 1 ⌈Real.logb S.L (max (f i1).len 1)⌉₊ : ℕ) : ℝ) := by
          exact_mod_cast le_max_right _ _
        have h3 : ((f i1).s : ℝ) = k + ((max 1 ⌈Real.logb S.L (max (f i1).len 1)⌉₊ : ℕ) : ℝ) := by
          rw [hs1']; push_cast; ring
        linarith
      have := G.shift_A (k := k) (s1 := (f i1).s) (s' := b'.s) hΛ1ge hs2'
        (B := Real.logb S.L (P.card : ℝ) + Real.logb S.L (1 + S.D (k + 1))) (by linarith)
        (by linarith)
      have h1 : (S.tStar (f i1) : ℝ) ≤ S.tStar (f i0) := by exact_mod_cast ht0
      rw [ht1] at h1
      push_cast at h1
      have hcY : 0 ≤ S.cStar * Real.logb S.L (S.nuBar (S.lam (k + 1)) * S.Dbar (S.lam (k + 1))) :=
        mul_nonneg hc0 hY0
      nlinarith
    · have hact1 : (f i1).IsActive ∨ (f i1).IsPending := by
        rcases Book.cases_st (f i1) with h | h | h
        · exact absurd h hpre1
        · exact Or.inr h
        · exact Or.inl h
      have hΛ1Y := G.logb_len_le (G.len_le_numax (hinv i1 hi1) hact1)
      have := G.shift_B (μ := k + 1) (s' := b'.s) hs1 hs2
        (B := Real.logb S.L (S.nuBar (S.lam (k + 1)) * S.Dbar (S.lam (k + 1))) +
          Real.logb S.L (P.card : ℝ) + Real.logb S.L (1 + S.D (k + 1))) (by linarith)
      have hp1 : (k + 1) + S.nq (k + 1) ≤ S.tStar (f p) := by
        rw [htp]; exact Nat.add_le_add hsp (G.ok.nq_mono hsp)
      have hp2 : (((k + 1) + S.nq (k + 1) : ℕ) : ℝ) ≤ S.tStar (f i0) := by
        exact_mod_cast hp1.trans ht0p
      push_cast at hp2 this ⊢
      nlinarith
  have hR'0 : 0 ≤ S.cStar * (2 +
      Real.logb S.L (S.nuBar (S.lam (k + 1)) * S.Dbar (S.lam (k + 1))) +
      Real.logb S.L (P.card : ℝ) + Real.logb S.L (1 + S.D (k + 1))) + 1 := by
    have : 0 ≤ S.cStar * (2 +
      Real.logb S.L (S.nuBar (S.lam (k + 1)) * S.Dbar (S.lam (k + 1))) +
      Real.logb S.L (P.card : ℝ) + Real.logb S.L (1 + S.D (k + 1))) :=
      mul_nonneg hc0 (by linarith)
    linarith
  refine (nat_sub_cast_le hR'0 hshift).trans ?_
  have key : S.cStar * (2 + Real.logb S.L (S.nuBar (S.lam (k + 1)) * S.Dbar (S.lam (k + 1))) +
      Real.logb S.L (P.card : ℝ) + Real.logb S.L (1 + S.D (k + 1))) + 1 ≤
      S.Gbar (S.lam (k + 1)) + S.cStar * ((P.card : ℝ) - 1) := by
    rw [hGb]
    nlinarith [mul_le_mul_of_nonneg_left hlm hc0, mul_le_mul_of_nonneg_left hld hc0]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ (P.card : ℝ) - 2 by linarith) hGb0]

end Setting.Good

end Balaban.LargeField
