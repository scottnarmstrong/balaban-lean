module

public import Balaban.Background.Def5Response
public import Balaban.Background.Theorem73
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Lemma 2.3: the smallness domain for the linear response

`thm73C2`: the smallness of the datum `(θ, h)` of level `n + 1` under which the composed datum
`ψ^{(k)}` (`composeData`) lies in `𝒟(𝔹_k)` with `δ ≤ bgC2`, the domain of the linear response
and of the constrained operator `Π` (`standing_bgFieldC`).  `theorem73_complex_small` is
`theorem73_complex` with this smaller constant (same proof).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

section Domain

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {a₁ ν : ℝ}

/-- The smallness of the datum `(θ, h)` under which the composed datum is in the domain of the
linear response (`bgC2`): `c₂ / (2 C₄ K₁)`. -/
noncomputable def thm73C2 (d L N : ℕ) [NeZero L] : ℝ :=
  bgC2 d L N / (2 * (compC4 d * bgK1 d L N))

theorem thm73C2_le_thm73C1 (d L N : ℕ) [NeZero L] : thm73C2 d L N ≤ thm73C1 d L N := by
  unfold thm73C2 thm73C1
  have hpos : 0 < 2 * (compC4 d * bgK1 d L N) := by
    have := compC4_ge d; have := bgK1_ge_one d L N; positivity
  exact div_le_div_of_nonneg_right (bgC2_le_bgC1 d L N) hpos.le

/-- **Theorem 7.3 (complex data) in the domain of the linear response**: for `D'` in `𝒟(𝔹'_k)`
with `δ ≤ thm73C2`, the composed datum lies in the domain `𝒟` with `δ_j = 2 C₄ K₁ δ ≤ c₂`
(the proof of `theorem73_complex`, with the smaller constant). -/
theorem theorem73_complex_small (ha₁ : 0 < a₁) (H : BgHyp d L k ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L k ϱ' (compWeight L a₁) ν) (h : Precedes G G') {D' : BgData G' N}
    (hD' : InUnionDomainC G' (bgC0 d L N) (thm73C2 d L N) ν D') :
    InUnionDomainC G (bgC0 d L N) (bgC2 d L N) ν
        (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D') := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hL2 : 2 ≤ L := by have := H.hL; omega
  have ha : ∀ j, 1 ≤ j → j ≤ k → compWeight L a₁ j ≠ 0 := fun j hj _ =>
    (compWeight_pos hL2 ha₁ hj).ne'
  obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hD'
  have hδc1 : δ ≤ thm73C1 d L N := hδc.trans (thm73C2_le_thm73C1 d L N)
  have h2s : 2 * (compC4 d * (bgK1 d L N * δ)) ≤ bgC2 d L N := by
    have hpos : 0 < 2 * (compC4 d * bgK1 d L N) := by
      have := compC4_ge d; have := bgK1_ge_one d L N; positivity
    have := (le_div_iff₀ hpos).1 hδc
    nlinarith
  obtain ⟨hδ1, h2, hx4, hKds, hsm⟩ := thm73_small (L := L) (N := N) hd0 hδ0 hδc1
  have hK1 := bgK1_ge_one d L N
  obtain ⟨W⟩ := DataWit.exists hDC
  -- the complex small solution and the real one
  obtain ⟨φc, αc, hsc, hbc, huc⟩ := theorem52_exists H' hδ0 hδε hε hδ1 hνε hDC
  obtain ⟨hfc, hmc⟩ := bgFieldC_eq hsc huc
  have hDr : InDomainR G' ν δ W.real :=
    ⟨W.Ψ, W.h₀, W.P.toInPsiTilde, fun x hx i => W.real_Ψ hx i, fun x hx i => W.real_h hx i⟩
  obtain ⟨φr, αr, hsr, hbr, hur, hunitr, -, -⟩ := bg_real H' hδ0 hδ1 hDr
  have hφr : ∀ z i, (φr (z, i)).im = 0 := fun z i => (hunitr z).1 i
  have hdiff : ∀ z : G'.Ω 1, vn (fun i => φc (z, i) - φr (z, i)) ≤ ε + bgK1 d L N * δ := fun z =>
    theorem52_compare H' hδ0 hδε hε hδ1 hνε W W.real (fun x hx i => W.real_Ψ hx i)
      (fun x hx i => W.real_h hx i) hsc hsr z
  have hmass : ∀ z : G'.Ω 1,
      Real.sqrt ν * G'.spacing z * vn (fun i => φr (z, i) - (W.h₀ i : ℂ)) ≤ bgK1 d L N * δ := by
    intro z
    have := mass_bound_spacing H' hδ0 hδ1 W.P.toInPsiTilde (fun x hx i => W.real_Ψ hx i)
      (fun x hx i => W.real_h hx i) hsr z
    have e : (fun i => φr (z, i) - W.real.h z i) = fun i => φr (z, i) - (W.h₀ i : ℂ) :=
      funext fun i => by rw [W.real_h z.2 i]
    rwa [e] at this
  have hcons : Hyp63 G G' a₁ ν δ ε (bgK1 d L N) (bgK1 d L N * δ) W.Ψ W.h₀ W.Ψ' W.h' φr φc :=
    { prec := h, hL := hL2, ha₁ := ha₁, hK₁ := hK1, hδ := hδ0, hδε := hδε
      hε1 := hε.trans (bgC0_le d L N |>.trans (by norm_num)), hη := rfl
      hsmall := hsm, hν := H'.mass, hνk := H'.massLe, hPC := W.P, hφr := hφr
      hbr := fieldBounds_of_bgBounds (fun x hx i => (W.real_Ψ hx i).symm) hbr hsr.1.2
      hmass := hmass
      hbc := fieldBounds_of_bgBounds (fun x hx i => by rw [W.hΨ x hx i]; rfl) hbc hsc.1.2
      hdiff := hdiff }
  have hdom := lemma63_inDomainC hcons D' (fun x hx i => by rw [W.hΨ x hx i]; rfl)
    (fun x hx i => W.hh x hx i)
  rw [hfc]
  have hδj0 : 0 < 2 * (compC4 d * (bgK1 d L N * δ)) := by
    have := compC4_ge d; positivity
  have hδjc0 : 2 * (compC4 d * (bgK1 d L N * δ)) ≤ bgC0 d L N :=
    h2.trans (bgC1_le_bgC0 d L N hd0)
  have hδδj : δ ≤ 2 * (compC4 d * (bgK1 d L N * δ)) := by
    have := compC4_ge d
    nlinarith [mul_pos hδ0 (by linarith : (0 : ℝ) < bgK1 d L N)]
  have hνj : ν * ((L : ℝ) ^ k) ^ 2 * (max ε (2 * (compC4 d * (bgK1 d L N * δ)))) ^ 2 ≤
      (2 * (compC4 d * (bgK1 d L N * δ))) ^ 2 := by
    rcases le_total ε (2 * (compC4 d * (bgK1 d L N * δ))) with he | he
    · rw [max_eq_right he]
      have := H.massLe
      nlinarith [sq_nonneg (2 * (compC4 d * (bgK1 d L N * δ)))]
    · rw [max_eq_left he]
      have : δ ^ 2 ≤ (2 * (compC4 d * (bgK1 d L N * δ))) ^ 2 :=
        pow_le_pow_left₀ hδ0.le hδδj 2
      linarith
  have hDj : InUnionDomainC G (bgC0 d L N) (bgC2 d L N) ν
      (composeData h (compWeight L a₁) φc D') :=
    ⟨_, _, hδj0, le_max_right _ _, max_le hε hδjc0, h2s, hνj, hdom⟩
  exact hDj

end Domain

end Balaban.Fluctuation
