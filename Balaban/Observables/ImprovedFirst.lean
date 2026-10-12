/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.ImprovedLemma
public import Balaban.SmallField.PsiGeomSlice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemma 3.4, first bound: the geometry of `Ψ^c_j(σ, ε)` discharged

OBSERVABLES.md §3.4, P9 pp. 498-501, P1 Lemma 3.6, (3.54)-(3.58).  `improved_first_of_const` is the
first bound (2.21) of P9 Lemma 2 (corrected subtrahend, see `ImprovedBound.lean`) for a datum
`(Ψ, h)` of the data domain `Ψ̃^c(𝔹_j(X); δ, ε)` (the landed `InPsiTildeC`, the space `Ψ̄^c_j(δ, ε)` of
P1 (3.19)), `δ = σ ε`.  Unlike `improved_first_of_slice`, the slice and the path geometry are *proved*:

* the path estimate (3.54) on the polymer `X` (`psi_path_bounds`);
* the truncated slice `t ↦ (c + t (Ψ - c) 1_X, h)` stays in `Ξ^c_j(𝔹_j(X); 1, ε_j)` for
  `|t| < r₀ = Rad / (c₁ (1 + d_j(X)/(2L)) δ)` when `d_j(X) ≤ c'/δ` (`xiDom_slice`);
* the constant configuration and the datum itself are in `Ξ^c_j` (`xiDom_const`, `xiDom_orig`).

The only remaining premise is `hconst`, the bound of the *constant part*
`M(c, h) - M(v, v)` (the `b`-form of OBSERVABLES §3.4, which rests on the `(u, v, w²)` expansion and
is not a geometric statement).  Hence the name `_of_const`: this is the first bound modulo the constant
part, as `improved_first_of_slice` is modulo the slice geometry.
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Metric Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem analyticAt_sliceField (X : Set (CTorus d L N₁ m₁ k)) (Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ)
    (Ψ'' : CTorus d L N₁ m₁ k → Fin N → ℂ) (y : CTorus d L N₁ m₁ k) (t : ℂ) :
    AnalyticAt ℂ (fun u : ℂ => (fun z i => (sliceBase X Ψ₀ y z i : ℂ) +
      slicePert X Ψ₀ Ψ'' y u z i : Fld d L N₁ m₁ k N)) t := by
  refine AnalyticAt.pi (fun z => ?_)
  refine AnalyticAt.pi (fun i => ?_)
  by_cases hz : z ∈ X
  · simp only [slicePert, hz, ↓reduceIte]
    fun_prop
  · simp only [slicePert, hz, ↓reduceIte]
    fun_prop


/-- The arithmetic of the slice radius: with `Q = δ (K₀ + E D)` and `|t| < r₀`
(`r₀ = (δ₀/128) / (c₁ (1 + D/(2L)) δ)`, `D ≤ δ₀/(128 E δ)`, `128 K₀ δ ≤ δ₀`, `K₀, 2 L E ≤ c₁`)
one has `(1 + 2|t|) Q ≤ δ₀/32` (P1 (3.57)). -/
theorem slice_arith {δ δ₀ K₀ E c₁ D T Lr : ℝ} (hδ : 0 < δ) (hE0 : 0 < E) (hK₀1 : 1 ≤ K₀)
    (hc₁ : K₀ ≤ c₁) (hc₂ : 2 * Lr * E ≤ c₁) (hL : 0 < Lr) (hD0 : 0 ≤ D)
    (hsmall : 128 * K₀ * δ ≤ δ₀) (hsm : D ≤ δ₀ / (128 * E) / δ) (hT0 : 0 ≤ T)
    (ht : T < δ₀ / 128 / (c₁ * (1 + D / (2 * Lr)) * δ)) :
    (1 + 2 * T) * (δ * (K₀ + E * D)) ≤ δ₀ / 32 ∧ δ ≤ δ * (K₀ + E * D) ∧ 4 * δ ≤ δ₀ := by
  have hc₁0 : 0 < c₁ := by linarith
  have h5 : 0 ≤ D / (2 * Lr) := by positivity
  have hr0 : 0 < c₁ * (1 + D / (2 * Lr)) * δ := by positivity
  have hKD : K₀ + E * D ≤ c₁ * (1 + D / (2 * Lr)) := by
    have h4 : E * D = 2 * Lr * E * (D / (2 * Lr)) := by field_simp
    rw [h4]
    nlinarith [mul_le_mul_of_nonneg_right hc₂ h5]
  have hKD0 : 0 ≤ K₀ + E * D := by positivity
  have hTQ : T * (δ * (K₀ + E * D)) ≤ δ₀ / 128 := by
    have h1 : T * (c₁ * (1 + D / (2 * Lr)) * δ) ≤ δ₀ / 128 := by
      have := mul_le_mul_of_nonneg_right ht.le hr0.le
      calc T * (c₁ * (1 + D / (2 * Lr)) * δ)
          ≤ δ₀ / 128 / (c₁ * (1 + D / (2 * Lr)) * δ) * (c₁ * (1 + D / (2 * Lr)) * δ) := this
        _ = δ₀ / 128 := by field_simp
    calc T * (δ * (K₀ + E * D)) ≤ T * (δ * (c₁ * (1 + D / (2 * Lr)))) := by gcongr
      _ = T * (c₁ * (1 + D / (2 * Lr)) * δ) := by ring
      _ ≤ δ₀ / 128 := h1
  have hDδ : δ * D ≤ δ₀ / (128 * E) := by
    have := (le_div_iff₀ hδ).1 hsm
    linarith [mul_comm δ D]
  have hQ1 : δ * (K₀ + E * D) ≤ δ₀ / 128 + δ₀ / 128 := by
    have e : δ * (K₀ + E * D) = δ * K₀ + E * (δ * D) := by ring
    rw [e]
    have h1 : δ * K₀ ≤ δ₀ / 128 := by nlinarith
    have h2 : E * (δ * D) ≤ δ₀ / 128 := by
      calc E * (δ * D) ≤ E * (δ₀ / (128 * E)) := mul_le_mul_of_nonneg_left hDδ hE0.le
        _ = δ₀ / 128 := by field_simp
    linarith
  refine ⟨by nlinarith, ?_, by nlinarith⟩
  nlinarith [mul_nonneg hδ.le (sub_nonneg.2 hK₀1), mul_nonneg hδ.le (mul_nonneg hE0.le hD0)]

section Lemma

variable {P : Consts} {Q : ObsConsts} {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ}

/-- **The first bound of Lemma 3.4 (2.21), corrected form, from the constant part.**

Let `X ∈ 𝒟_j` lie in the top layer `j` of `𝔹_j(X)`, `x, y ∈ X`, and let `(Ψ₀ + Ψ'', h₀ + h')` be a
datum of `Ψ̃^c(𝔹_j(X); δ, ε)` (`h'` constant, as in P1 (3.14)), `δ = σ ε`, so that
`Ψ = Ψ₀ + Ψ''` and `h = h₀ + h'` are the field and the constant field of the observable.  Let
`δ₀ ≥ ε` with `δ₀ ≤ min (c₀, c₁)` and `(2 K₁ + 2) δ₀ ≤ ε_j` (the chain (3.22): the target domain is
`Ψ̃^c(δ₀, δ₀)`, `Ξ^c_j(1, ε_j)` by (3.21)), and
`128 · 3^d (4 d L M + 1) · δ ≤ δ₀` (P1 (3.57), `M = L^{m₀+m₁}`).  If the constant part is bounded,
`|M(c, h) - M(v, v)| ≤ b_c` for `c = Ψ(y)` and a real unit vector `v`, then
`|M(x, X; Ψ, h) - M(x, X; v, v)| ≤ C β^{-1/2+ρ₁} L^{-jρ₀} δ e^{-(κ-1) d_j(X)} + b_c`
with `C = improvedConst c₁ (δ₀/128) (δ₀/(128 · 3^d M))`,
`c₁ = max (3^d (4 d L M + 1)) (2 L · 3^d M)`. -/
theorem improved_first_of_const (hO : IsObs P Q β ν a Tm Ot Gker) (hsf : IsSF P β ν a Tm ρd Ek)
    (hbg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    {y : CTorus d L N₁ m₁ k} (hy : y ∈ X)
    (hlayer : ∀ z ∈ X, (Tm.gs j X).layerIndex z = j)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' : CTorus d L N₁ m₁ k → Fin N → ℂ} {h' : Fin N → ℂ} {δ ε δ₀ : ℝ}
    (hP : InPsiTildeC (Tm.gs j X) (bgMass L k (β k) (ν k)) δ ε Ψ₀ h₀ Ψ'' (fun _ => h'))
    (hβ0 : 0 < β 0) (hδ : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ δ₀) (hc0 : δ₀ ≤ bgC0 d L N)
    (hc1 : δ₀ ≤ bgC1 d L N)
    (hεj : δ₀ + (2 * bgK1 d L N + 1) * δ₀ ≤ P.eps d L j)
    (hsmall : 128 * (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) * δ ≤ δ₀)
    {v : Fin N → ℝ} {bc : ℝ}
    (hconst : vn (Ot.M j x X (constFld (fun i => (Ψ₀ y i : ℂ) + Ψ'' y i))
        (constFld (fun i => (h₀ i : ℂ) + h' i)) -
      Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤ bc) :
    vn (Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) (constFld (fun i => (h₀ i : ℂ) + h' i)) -
        Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤
      improvedConst
          (max (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) (2 * L * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁))))
          (δ₀ / 128) (δ₀ / (128 * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁)))) *
        ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) * δ *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)) + bc := by
  classical
  obtain ⟨hXΩ, hΩ⟩ := hsf.gs_spec j hj1 hjk X hX
  have hLp : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  set M : ℝ := (L : ℝ) ^ (P.m₀ + m₁) with hM
  have hM1 : 1 ≤ M := one_le_pow₀ hL1
  have h3d : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  set K₀ : ℝ := 3 ^ d * (M * (4 * d * L) + 1) with hK₀
  have hK₀1 : 1 ≤ K₀ := by
    have : 0 ≤ M * (4 * d * L) := by positivity
    rw [hK₀]; nlinarith
  set E : ℝ := 3 ^ d * M with hE
  have hE0 : 0 < E := by positivity
  set c₁ : ℝ := max K₀ (2 * L * E) with hc₁
  have hc₁0 : 0 < c₁ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  set D : ℝ := sizeJ P.m₀ j X with hD
  have hD0 : 0 ≤ D := treeLenCovOne_nonneg _ _ _
  set A : ℝ := (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hδ₀ : 0 < δ₀ := by linarith
  have h4δ : 4 * δ ≤ δ₀ := by nlinarith
  have hblock : ∀ z z', jBlock d L (N₁ * L ^ m₁) k j z = jBlock d L (N₁ * L ^ m₁) k j z' →
      z ∈ X → z' ∈ X := fun z z' h hz => IsPolyDom.block_closed hjk hN hX hz h
  have hδ₀1 : δ₀ ≤ 1 / 16 := hc0.trans (bgC0_le d L N)
  set hfld : Fld d L N₁ m₁ k N := constFld (fun i => (h₀ i : ℂ) + h' i) with hhf
  set c : Fin N → ℂ := fun i => (Ψ₀ y i : ℂ) + Ψ'' y i with hc
  set Sf : ℂ → Fld d L N₁ m₁ k N := fun t z i =>
    (sliceBase X Ψ₀ y z i : ℂ) + slicePert X Ψ₀ Ψ'' y t z i with hSf
  -- the endpoints
  have e1 : ∀ z ∈ X, Sf 1 z = fun i => (Ψ₀ z i : ℂ) + Ψ'' z i := by
    intro z hz; funext i
    simp only [hSf, sliceBase, slicePert, hz, ↓reduceIte]; ring
  have e0 : Sf 0 = constFld c := by
    funext z i
    by_cases hz : z ∈ X
    · simp only [hSf, sliceBase, slicePert, hz, ↓reduceIte, constFld, hc]; push_cast; ring
    · simp only [hSf, sliceBase, slicePert, hz, ↓reduceIte, constFld, hc]
  set Gs : ℂ → Fin N → ℂ := fun t => Ot.M j x X (Sf t) hfld with hGs
  have hG1 : Gs 1 = Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) hfld :=
    hO.localM j x X (Sf 1) _ hfld hfld (fun z hz => ⟨e1 z hz, rfl⟩)
  have hG0 : Gs 0 = Ot.M j x X (constFld c) hfld := by simp only [hGs, e0]
  -- domain facts
  have hdomΨ := xiDom_orig (G := Tm.gs j X) (a := aIdeal L k (a k)) hbg hjk hP hδ hδε hε hc0 hc1 hεj
  have hdom0 := xiDom_const (G := Tm.gs j X) (a := aIdeal L k (a k)) hbg hjk hΩ hP (hXΩ hy)
    (hlayer y hy) hδ hδε hε hc0 hc1 hεj
  have hBΨ : vn (Gs 1) ≤ A * Real.exp (-P.κ * D) := by
    rw [hG1]; exact hO.boundM j hj1 hjk x X hX hx _ hfld hdomΨ
  have hB0 : vn (Gs 0) ≤ A * Real.exp (-P.κ * D) := by
    rw [hG0]; exact hO.boundM j hj1 hjk x X hX hx _ hfld hdom0
  set G' : ℂ → EuclideanSpace ℂ (Fin N) := fun t => WithLp.toLp 2 (Gs t) with hG'
  have hnorm : ∀ t, ‖G' t‖ = vn (Gs t) := fun t => rfl
  have hdelta := improved_delta_bound (G := G') (A := A) (κ := P.κ) (D := D) (s := δ)
    (L := (L : ℝ)) (c := c₁) (Rad := δ₀ / 128) (c' := δ₀ / (128 * E)) hA0 hD0 hδ (by linarith)
    hc₁0 (by positivity) (by positivity) (by rw [hnorm]; exact hBΨ) (by rw [hnorm]; exact hB0)
    (by
      intro hsm
      set r : ℝ := (δ₀ / 128) / (c₁ * (1 + D / (2 * (L : ℝ))) * δ) with hr
      have hmem : ∀ t : ℂ, ‖t‖ < r →
          XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
            (Sf t) hfld := by
        intro t ht
        -- the path bounds
        have hpb := fun z (hz : z ∈ X) =>
          psi_path_bounds (m₀ := P.m₀) hjk hN hP hX hXΩ hlayer hδ hy hz
        have hQeq : δ * (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L + sizeJ P.m₀ j X) + 1)) =
            δ * (K₀ + E * D) := by rw [hK₀, hE, hM, hD]; ring
        have hpb' : ∀ z ∈ X, rn (fun i => Ψ₀ z i - Ψ₀ y i) ≤ δ * (K₀ + E * D) ∧
            vn (fun i => Ψ'' z i - Ψ'' y i) ≤ δ * (K₀ + E * D) := fun z hz => by
          rw [← hQeq]; exact hpb z hz
        obtain ⟨hT, hδQ, -⟩ := slice_arith hδ hE0 hK₀1 (le_max_left _ _) (le_max_right _ _) hLp hD0
          hsmall hsm (norm_nonneg t) ht
        exact xiDom_slice (G := Tm.gs j X) (a := aIdeal L k (a k)) hbg hjk hΩ hP hXΩ hlayer hblock hy
          (fun z hz => (hpb' z hz).1) (fun z hz => (hpb' z hz).2) hδ hδε hε hδQ hδ₀1 h4δ hc0 hc1 hεj t hT
      have hd : DifferentiableOn ℂ Gs (ball 0 r) := by
        intro t ht
        have h1 := hO.analyticM j hj1 hjk x X hX hx (Sf t, hfld) (hmem t (mem_ball_zero_iff.1 ht))
        have h2 : AnalyticAt ℂ (fun u : ℂ => (Sf u, hfld)) t :=
          (analyticAt_sliceField X Ψ₀ Ψ'' y t).prod analyticAt_const
        exact (AnalyticAt.comp (g := fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
          Ot.M j x X p.1 p.2) (f := fun u : ℂ => (Sf u, hfld)) h1 h2).differentiableAt.differentiableWithinAt
      refine ⟨?_, ?_⟩
      · exact (EuclideanSpace.equiv (Fin N) ℂ).symm.differentiable.comp_differentiableOn hd
      · intro t ht
        rw [hnorm]
        exact hO.boundM j hj1 hjk x X hX hx _ hfld (hmem t ht))
  have hd2 : vn (Gs 1 - Gs 0) ≤ improvedConst c₁ (δ₀ / 128) (δ₀ / (128 * E)) *
      (A * δ * Real.exp (-(P.κ - 1) * D)) := by
    have e : G' 1 - G' 0 = WithLp.toLp 2 (Gs 1 - Gs 0) := rfl
    rw [e] at hdelta
    exact hdelta
  rw [hG1, hG0] at hd2
  have htri : vn (Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) hfld -
        Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤
      vn (Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) hfld - Ot.M j x X (constFld c) hfld) +
      vn (Ot.M j x X (constFld c) hfld - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) := by
    have e : Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) hfld -
        Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ))) =
        (Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) hfld - Ot.M j x X (constFld c) hfld) +
        (Ot.M j x X (constFld c) hfld - Ot.M j x X (constFld (fun i => (v i : ℂ)))
          (constFld (fun i => (v i : ℂ)))) := by abel
    rw [e]
    exact vn_add' _ _
  linarith

end Lemma

end Balaban.Observables
