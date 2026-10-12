module

public import Balaban.LargeField.Counter.CapScale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The smallness shift of a merge within the cap (Part I, (B.11))
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

theorem DeltaBar_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ S.DeltaBar x := by
  have hL := G.ok.cast_L_ge
  have h1 := G.ok.one_le_nuBar hx
  have h2 := G.ok.one_le_Dbar x
  have h3 : 0 ≤ Real.logb S.L (S.nuBar x) := Real.logb_nonneg (by linarith) h1
  have h4 : 0 ≤ Real.logb S.L (1 + S.Dbar x) := Real.logb_nonneg (by linarith) (by linarith)
  have h5 : 0 ≤ S.n2Bar (2 * x) := by
    unfold Typing.n2Bar
    have hM : (1 : ℝ) ≤ S.M := by exact_mod_cast G.ok.one_le_M
    have hc := G.ok.critBar_ge (2 * x)
    have : 0 ≤ Real.logb S.L ((S.L : ℝ) * S.M * S.critBar (2 * x)) :=
      Real.logb_nonneg (by linarith)
        (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hM)
          (by linarith))
    linarith
  unfold Typing.DeltaBar
  linarith

/-- (B.11): the smallness shift `Δ₁ = (t₀ - t^*_{i₀})₊` is at most `Δ̄(λ_μ)`. -/
theorem delta1_bound {ι : Type*} {k : ℕ} {P : Finset ι} {f : ι → Book} {b' : Book} {i0 i1 : ι}
    (hinv : ∀ i ∈ P, BookInv S k (f i)) (hpost : ∀ i ∈ P, k < S.tStar (f i))
    (hact : ∀ i ∈ P, (f i).IsActive ∨ (f i).IsPending) (hne : P.Nonempty)
    (hcap : ∑ i ∈ P, (f i).nu ≤ S.numax (k + 1))
    (hmax0 : ∀ j ∈ P, S.tStar (f j) ≤ S.tStar (f i0))
    (hi1 : i1 ∈ P) (hmax1 : ∀ j ∈ P, (f j).len ≤ (f i1).len)
    (hlen : b'.len ≤ ∑ i ∈ P, (f i).len / S.L + (((P.card + 0 : ℕ) : ℝ) - 1) * S.D (k + 1))
    (hT : T4Facts S k P f b') :
    ((S.t4t0 P f b'.s - S.tStar (f i0) : ℕ) : ℝ) ≤ S.DeltaBar (S.lam (k + 1)) := by
  have hL := G.ok.cast_L_ge
  have hlenP : ∀ j ∈ P, 0 ≤ (f j).len := fun j hj => (hinv j hj).len_nonneg
  have hD0 : 0 ≤ S.D (k + 1) := S.D_nonneg _
  have hl := G.ok.lam_pos (k + 1)
  have hΔ0 := G.DeltaBar_nonneg hl.le
  have hθ := G.ok.θp_pos
  have hlb := G.len_log_bound (P := P) (f := f) hi1 hmax1 hlenP hD0 (by simpa using hlen)
  set Λ' := Real.logb S.L (max b'.len 1) with hΛ'
  set Λ1 := Real.logb S.L (max (f i1).len 1) with hΛ1
  have hs_ge := hT.s_ge
  have hs_le := hT.s_le
  -- `Λ' ≤ Y`
  have hlen2 : b'.len ≤ S.numax (k + 1) * S.D (k + 1) := by
    refine hT.len_le.trans ?_
    have h1 : (((∑ i ∈ P, (f i).nu : ℕ) : ℝ) - 1) ≤ S.numax (k + 1) := by
      have : ((∑ i ∈ P, (f i).nu : ℕ) : ℝ) ≤ S.numax (k + 1) := by exact_mod_cast hcap
      linarith
    exact mul_le_mul_of_nonneg_right h1 hD0
  have hΛY := G.logb_len_le hlen2
  set Y := Real.logb S.L (S.nuBar (S.lam (k + 1)) * S.Dbar (S.lam (k + 1))) with hY
  have h1a := G.lc.l1_a (S.lam (k + 1)) (G.lam_ge _)
  -- `λ_{s'} ≤ 2 λ_μ`
  have hΛ0 : 0 ≤ Λ' := Real.logb_nonneg (by linarith) (le_max_right _ _)
  obtain ⟨z, hz⟩ := Nat.exists_eq_add_of_le hs_ge
  have hzR : (z : ℝ) ≤ 1 + Y := by
    have : ((b'.s : ℕ) : ℝ) = (k + 1 : ℕ) + z := by rw [hz]; push_cast; ring
    push_cast at hs_le this
    linarith
  have hlam2 : S.lam b'.s ≤ 2 * S.lam (k + 1) := by
    have := G.ok.lam_add_le (k + 1) z
    rw [← hz] at this
    have h2 : (z : ℝ) * S.θp ≤ (1 + Y) * S.θp := by gcongr
    nlinarith
  have hn2 : (S.n2 b'.s : ℝ) ≤ S.n2Bar (2 * S.lam (k + 1)) :=
    (G.ok.n2_le_bar b'.s).trans (G.ok.n2Bar_mono (G.ok.lam_pos _).le hlam2)
  -- logs
  have hm_le : (P.card : ℝ) ≤ S.nuBar (S.lam (k + 1)) := by
    have h1 : P.card ≤ ∑ i ∈ P, (f i).nu := by
      calc P.card = ∑ i ∈ P, 1 := by simp
        _ ≤ ∑ i ∈ P, (f i).nu := Finset.sum_le_sum (fun i hi => (hinv i hi).one_le_nu)
    have h2 : (P.card : ℝ) ≤ S.numax (k + 1) := by exact_mod_cast h1.trans hcap
    exact h2.trans (G.ok.numax_le_bar _)
  have hcard1 : (1 : ℝ) ≤ P.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hlm : Real.logb S.L (P.card : ℝ) ≤ Real.logb S.L (S.nuBar (S.lam (k + 1))) :=
    Real.logb_le_logb_of_le (by linarith) (by linarith) hm_le
  have hld : Real.logb S.L (1 + S.D (k + 1)) ≤ Real.logb S.L (1 + S.Dbar (S.lam (k + 1))) :=
    Real.logb_le_logb_of_le (by linarith) (by linarith)
      (by linarith [G.ok.D_le_bar (k + 1)])
  -- the lengths of the parts
  have ht1 : (k : ℝ) + Λ1 ≤ S.tStar (f i1) := G.tStar_ge_len (hinv i1 hi1) (hpost i1 hi1)
  have ht0 : S.tStar (f i1) ≤ S.tStar (f i0) := hmax0 i1 hi1
  have ht0R : (S.tStar (f i1) : ℝ) ≤ S.tStar (f i0) := by exact_mod_cast ht0
  -- first term of `t₀`
  have hQ : Setting.t4Q P f + S.nq (Setting.t4Q P f) ≤ S.tStar (f i0) := by
    obtain ⟨i, hi, hiQ⟩ := Finset.exists_mem_eq_sup P hne (fun i => (f i).q)
    have : Setting.t4Q P f = (f i).q := hiQ
    rw [this]
    exact (S.tStar_ge_left (f i)).trans (hmax0 i hi)
  -- second term of `t₀`
  have hS : ((b'.s + S.n2 b'.s : ℕ) : ℝ) ≤ S.tStar (f i0) + S.DeltaBar (S.lam (k + 1)) := by
    unfold Typing.DeltaBar
    push_cast
    have : (b'.s : ℝ) ≤ (k + 1 : ℕ) + 1 + Λ' := hs_le
    push_cast at this
    linarith
  have hfinal : (S.t4t0 P f b'.s : ℝ) ≤ S.tStar (f i0) + S.DeltaBar (S.lam (k + 1)) := by
    unfold Setting.t4t0
    rw [Nat.cast_max]
    refine max_le ?_ hS
    have : ((Setting.t4Q P f + S.nq (Setting.t4Q P f) : ℕ) : ℝ) ≤ S.tStar (f i0) := by
      exact_mod_cast hQ
    linarith
  exact nat_sub_cast_le hΔ0 hfinal

end Setting.Good

end Balaban.LargeField
