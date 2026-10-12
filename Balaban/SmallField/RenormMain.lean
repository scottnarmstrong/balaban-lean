/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormNumeric

/-!
# Assembly: Theorem 2.1 (a) for the family of polymers containing the origin

`Dlt X` is `𝓔(0,X;ψ,b) - 𝓔(0,X;ψ(0),b) - A_X + L_X`.  We show `‖Dlt X‖ ≤ C E₀ wt(X) σ^{3-α₁} (ε/ρ)²`
(small polymers by `small_case`, large ones by `tail_case`), sum over `X`, and use the vanishing of
`Σ_X L_X` (second moment, isotropy).
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

/-- The per-polymer quantity `𝓔(0,X;ψ,b) - 𝓔(0,X;ψ(0),b) - A_X + L_X`. -/
noncomputable def Dlt (T : TermFamily d N) (i₀ i₁ : Fin N) (ν : ℝ) (R : Matrix (Fin N) (Fin N) ℂ)
    (ψ : Site d → Spin N) (b : Spin N) (X : Finset (Site d)) : ℂ :=
  T.term X (pack X ψ b) - T.term X (pack X (fun _ => ψ 0) b)
    - (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x * (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))
    + (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
        wquad (gradTensor i₀ R ψ) x.1 x'.1

/-- `A_X = ½ Σ_x a_X(x) (g(x) - g(0))`. -/
noncomputable def Ax (T : TermFamily d N) (i₀ : Fin N) (ν : ℝ) (ψ : Site d → Spin N)
    (X : Finset (Site d)) : ℂ :=
  (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x * (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))

/-- `L_X = ¼ Σ_{x,x'} B_X(x,x') wquad`. -/
noncomputable def Lx (T : TermFamily d N) (i₀ i₁ : Fin N) (ν : ℝ) (R : Matrix (Fin N) (Fin N) ℂ)
    (ψ : Site d → Spin N) (X : Finset (Site d)) : ℂ :=
  (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
    wquad (gradTensor i₀ R ψ) x.1 x'.1

theorem Dlt_eq (T : TermFamily d N) (i₀ i₁ : Fin N) (ν : ℝ) (R : Matrix (Fin N) (Fin N) ℂ)
    (ψ : Site d → Spin N) (b : Spin N) (X : Finset (Site d)) :
    Dlt T i₀ i₁ ν R ψ b X = T.term X (pack X ψ b) - T.term X (pack X (fun _ => ψ 0) b)
      - Ax T i₀ ν ψ X + Lx T i₀ i₁ ν R ψ X := rfl

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)} {ψ : Site d → Spin N} {b : Spin N}
  {σ ε K₂ : ℝ} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}

theorem Ctx.dlt_bound (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {Λ Kc α₁ Cs Ct : ℝ} (hCs0 : 0 ≤ Cs) (hCt0 : 0 ≤ Ct)
    (hα0 : 0 < α₁) (hα1 : α₁ < 1)
    (hCs : ∀ (M ρ ν σ r K₂ t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → ρ ≤ 1 → 0 < r →
      r ≤ Λ → 0 ≤ ν → ν ≤ σ ^ 2 → 1 ≤ t → 1 ≤ P → 0 ≤ K₂ → K₂ ≤ Kc * Sσ * (r * ρ) →
      SigPow σ α₁ Tσ Sσ →
      smallBnd N A M ρ ν σ (r * ρ) K₂ t P ≤ Cs * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hCt : ∀ (M ρ σ r t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → 0 < r → r ≤ Λ → 1 ≤ t →
      1 ≤ P → 1 < 2 * (cC1 N + cK1 N A) * t * σ * r → SigPow σ α₁ Tσ Sσ →
      tailBnd N A M ρ σ (r * ρ) t P ≤ Ct * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hεΛ : ε ≤ Λ * ρ) (hK : K₂ ≤ Kc * σ ^ (2 - α₁) * ε) {X : Finset (Site d)}
    (hX : X ∈ T.polys) :
    ‖Dlt T i₀ i₁ ν R ψ b X‖ ≤
      (Cs + Ct) * (E₀ * wt κ X (T.dist X)) * (σ ^ (3 - α₁) * (ε / ρ) ^ 2) := by
  have hρ := c.ρpos
  have hεpos := c.εpos
  have hd0 : 0 ≤ T.dist X := c.hyp.dist_nonneg X hX
  have hS := sigPow σ α₁ c.σpos c.σle hα0 hα1
  set r : ℝ := ε / ρ with hr
  have hr0 : 0 < r := by positivity
  have hrε : ε = r * ρ := by rw [hr]; field_simp
  have hrΛ : r ≤ Λ := by rw [hr, div_le_iff₀ hρ]; linarith
  set t : ℝ := 1 + T.dist X with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  have hP : (1 : ℝ) ≤ X.card := by exact_mod_cast c.card_pos hX
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by have := c.E0nn; positivity
  have hwt := wt_ge (κ := κ) X hd0 (c.card_pos hX) 2 6 le_rfl le_rfl
  have hMP : M * (X.card : ℝ) ^ 2 * t ^ 6 ≤ E₀ * wt κ X (T.dist X) := by
    calc M * (X.card : ℝ) ^ 2 * t ^ 6 = E₀ * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6 *
          Real.exp (-κ * T.dist X)) := by rw [hMdef, ht]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hwt c.E0nn
  have hT0 : 0 ≤ σ ^ (3 - α₁) := (Real.rpow_pos_of_pos c.σpos _).le
  have hfin : ∀ C : ℝ, 0 ≤ C → ‖Dlt T i₀ i₁ ν R ψ b X‖ ≤ C * (M * (X.card : ℝ) ^ 2 * t ^ 6 *
      σ ^ (3 - α₁) * r ^ 2) → ‖Dlt T i₀ i₁ ν R ψ b X‖ ≤ C * (E₀ * wt κ X (T.dist X)) *
      (σ ^ (3 - α₁) * r ^ 2) := by
    intro C hC h
    refine h.trans ?_
    calc C * (M * (X.card : ℝ) ^ 2 * t ^ 6 * σ ^ (3 - α₁) * r ^ 2)
        = C * ((M * (X.card : ℝ) ^ 2 * t ^ 6) * (σ ^ (3 - α₁) * r ^ 2)) := by ring
      _ ≤ C * ((E₀ * wt κ X (T.dist X)) * (σ ^ (3 - α₁) * r ^ 2)) := by
          gcongr
      _ = _ := by ring
  have hfin' : ∀ C : ℝ, 0 ≤ C → C ≤ Cs + Ct → C * (E₀ * wt κ X (T.dist X)) *
      (σ ^ (3 - α₁) * r ^ 2) ≤ (Cs + Ct) * (E₀ * wt κ X (T.dist X)) *
      (σ ^ (3 - α₁) * r ^ 2) := by
    intro C hC hle
    have hw : 0 ≤ E₀ * wt κ X (T.dist X) := by
      have := c.E0nn
      have : 0 ≤ wt κ X (T.dist X) := by
        unfold wt
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) 6))
          (Real.exp_pos _).le
      exact mul_nonneg c.E0nn this
    have : 0 ≤ σ ^ (3 - α₁) * r ^ 2 := mul_nonneg hT0 (sq_nonneg r)
    gcongr
  by_cases hsm : (cC1 N + cK1 N A) * t * σ * ε ≤ ρ / 2
  · have h1 := c.small_case hX hsm
    have h2 := hCs M ρ ν σ r K₂ t X.card (σ ^ (3 - α₁)) (σ ^ (2 - α₁)) α₁ hM0 hρ c.ρle hr0 hrΛ
      c.ν0 c.νσ ht1 hP c.dat.K2_nonneg (by rw [← hrε]; exact hK) hS
    rw [← hrε] at h2
    have := hfin (Cs) hCs0 (h1.trans h2)
    have h3 := hfin' Cs hCs0 (by linarith)
    exact this.trans h3
  · have h1 := c.tail_case hX
    have hlt : 1 < 2 * (cC1 N + cK1 N A) * t * σ * r := by
      by_contra hcon
      push Not at hcon
      have := mul_le_mul_of_nonneg_right hcon hρ.le
      rw [hrε] at hsm
      nlinarith
    have h2 := hCt M ρ σ r t X.card (σ ^ (3 - α₁)) (σ ^ (2 - α₁)) α₁ hM0 hρ hr0 hrΛ ht1 hP hlt hS
    rw [← hrε] at h2
    have := hfin Ct hCt0 (h1.trans h2)
    have h3 := hfin' Ct hCt0 (by linarith)
    exact this.trans h3

theorem Aterm_eq (T : TermFamily d N) (i₀ : Fin N) (ν : ℝ) (ψ : Site d → Spin N) :
    Aterm T i₀ ν ψ = ∑' X : T.polys, Ax T i₀ ν ψ X.1 := by
  unfold Aterm Ax
  rw [← tsum_mul_left]
  congr 1
  ext X
  congr 1
  have : ∑ x ∈ X.1, aCoefX T i₀ ν X.1 x * (dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)) =
      ∑ x : ↥X.1, tensA i₀ ν X.1 (T.term X.1) x *
        (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0)) := by
    rw [← Finset.sum_coe_sort X.1]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [aCoefX, x.2]
  exact this

theorem Ctx.interaction_bound (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R)
    {Λ Kc α₁ Cs Ct : ℝ} (hCs0 : 0 ≤ Cs) (hCt0 : 0 ≤ Ct) (hα0 : 0 < α₁) (hα1 : α₁ < 1)
    (hCs : ∀ (M ρ ν σ r K₂ t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → ρ ≤ 1 → 0 < r →
      r ≤ Λ → 0 ≤ ν → ν ≤ σ ^ 2 → 1 ≤ t → 1 ≤ P → 0 ≤ K₂ → K₂ ≤ Kc * Sσ * (r * ρ) →
      SigPow σ α₁ Tσ Sσ →
      smallBnd N A M ρ ν σ (r * ρ) K₂ t P ≤ Cs * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hCt : ∀ (M ρ σ r t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → 0 < r → r ≤ Λ → 1 ≤ t →
      1 ≤ P → 1 < 2 * (cC1 N + cK1 N A) * t * σ * r → SigPow σ α₁ Tσ Sσ →
      tailBnd N A M ρ σ (r * ρ) t P ≤ Ct * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hεΛ : ε ≤ Λ * ρ) (hK : K₂ ≤ Kc * σ ^ (2 - α₁) * ε)
    (hL : ∑' X : T.polys, Lx T i₀ i₁ ν R ψ X.1 = 0) :
    ‖energy T ψ b - potential T (ψ 0) b - Aterm T i₀ ν ψ‖ ≤
      (Cs + Ct) * E₀ * K₀ * (σ ^ (3 - α₁) * (ε / ρ) ^ 2) := by
  classical
  have hρ := c.ρpos
  have hE0 := c.E0nn
  have hwt : ∀ X : T.polys, 0 ≤ wt κ X.1 (T.dist X.1) := fun X => by
    have := c.hyp.dist_nonneg X.1 X.2
    unfold wt
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) 6)) (Real.exp_pos _).le
  have hsum : Summable fun X : T.polys => wt κ X.1 (T.dist X.1) := c.hyp.count_summable
  have hMle : ∀ (X : T.polys) (a k : ℕ), a ≤ 2 → k ≤ 6 →
      (X.1.card : ℝ) ^ a * (1 + T.dist X.1) ^ k * (E₀ * Real.exp (-κ * T.dist X.1)) ≤
        E₀ * wt κ X.1 (T.dist X.1) := by
    intro X a k ha hk
    have := wt_ge (κ := κ) X.1 (c.hyp.dist_nonneg X.1 X.2) (c.card_pos X.2) a k ha hk
    calc _ = E₀ * ((X.1.card : ℝ) ^ a * (1 + T.dist X.1) ^ k * Real.exp (-κ * T.dist X.1)) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hE0
  have hε := c.εpos
  have hMn : ∀ X : T.polys, 0 ≤ E₀ * Real.exp (-κ * T.dist X.1) := fun X => by positivity
  -- the families
  set e : T.polys → ℂ := fun X => T.term X.1 (pack X.1 ψ b) with he
  set v : T.polys → ℂ := fun X => T.term X.1 (pack X.1 (fun _ => ψ 0) b) with hv
  set a : T.polys → ℂ := fun X => Ax T i₀ ν ψ X.1 with ha
  set l : T.polys → ℂ := fun X => Lx T i₀ i₁ ν R ψ X.1 with hl
  set δ : T.polys → ℂ := fun X => Dlt T i₀ i₁ ν R ψ b X.1 with hδ
  have b_e : ∀ X : T.polys, ‖e X‖ ≤ E₀ * wt κ X.1 (T.dist X.1) := fun X => by
    have h1 := c.hyp.bdd_dom X.1 X.2 (ψ, b) c.dat.mem
    have := hMle X 0 0 (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul] at this
    exact h1.trans this
  have b_v : ∀ X : T.polys, ‖v X‖ ≤ E₀ * wt κ X.1 (T.dist X.1) := fun X => by
    have h1 := c.hyp.bdd_dom X.1 X.2 ((fun _ => ψ 0), b) c.dat.mem_const
    have := hMle X 0 0 (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul] at this
    exact h1.trans this
  have b_a : ∀ X : T.polys, ‖a X‖ ≤ E₀ / ρ * (σ ^ 2 * ε) * wt κ X.1 (T.dist X.1) := fun X => by
    have h1 := c.A_le X.2
    have := hMle X 1 0 (by norm_num) (by norm_num)
    simp only [pow_one, pow_zero, mul_one] at this
    refine h1.trans ?_
    calc (X.1.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X.1) / ρ * (σ ^ 2 * ε))
        = ((X.1.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X.1))) / ρ * (σ ^ 2 * ε) := by ring
      _ ≤ (E₀ * wt κ X.1 (T.dist X.1)) / ρ * (σ ^ 2 * ε) := by gcongr
      _ = _ := by ring
  set CL : ℝ := (2 * A) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2) / ρ ^ 2 with hCL
  have b_l : ∀ X : T.polys, ‖l X‖ ≤ E₀ * CL * wt κ X.1 (T.dist X.1) := fun X => by
    have h1 := c.Lq_le X.2
    have := hMle X 2 2 le_rfl (by norm_num)
    refine h1.trans ?_
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc (X.1.card : ℝ) ^ 2 * (E₀ * Real.exp (-κ * T.dist X.1) / ρ ^ 2) *
          ((2 * (A * (1 + T.dist X.1))) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2))
        = ((X.1.card : ℝ) ^ 2 * (1 + T.dist X.1) ^ 2 * (E₀ * Real.exp (-κ * T.dist X.1))) * CL := by
          rw [hCL]; field_simp
      _ ≤ (E₀ * wt κ X.1 (T.dist X.1)) * CL := by
          have : 0 ≤ CL := by rw [hCL]; have := c.Ann; positivity
          gcongr
      _ = _ := by ring
  set Cd : ℝ := (Cs + Ct) * E₀ * (σ ^ (3 - α₁) * (ε / ρ) ^ 2) with hCd
  have b_δ : ∀ X : T.polys, ‖δ X‖ ≤ Cd * wt κ X.1 (T.dist X.1) := fun X => by
    have := c.dlt_bound hCs0 hCt0 hα0 hα1 hCs hCt hεΛ hK X.2
    refine this.trans ?_
    rw [hCd]; ring_nf; exact le_rfl
  have S_e : Summable e := Summable.of_norm_bounded (hsum.mul_left E₀) b_e
  have S_v : Summable v := Summable.of_norm_bounded (hsum.mul_left E₀) b_v
  have S_a : Summable a := Summable.of_norm_bounded (hsum.mul_left (E₀ / ρ * (σ ^ 2 * ε))) b_a
  have S_l : Summable l := Summable.of_norm_bounded (hsum.mul_left (E₀ * CL)) b_l
  have S_δ : Summable δ := Summable.of_norm_bounded (hsum.mul_left Cd) b_δ
  have hδl : ∀ X, δ X = e X - v X - a X + l X := fun X => rfl
  have hmain : energy T ψ b - potential T (ψ 0) b - Aterm T i₀ ν ψ = ∑' X, δ X := by
    rw [Aterm_eq]
    unfold energy potential
    have hδ' : δ = fun X => (e X - v X - a X) + l X := by ext X; exact hδl X
    have hsub : ∑' X, (e X - v X - a X) = ∑' X, e X - ∑' X, v X - ∑' X, a X := by
      rw [Summable.tsum_sub (S_e.sub S_v) S_a, Summable.tsum_sub S_e S_v]
    have hl' : ∑' X, l X = 0 := hL
    have : ∑' X, δ X = ∑' X, (e X - v X - a X) + ∑' X, l X := by
      rw [hδ']; exact Summable.tsum_add ((S_e.sub S_v).sub S_a) S_l
    rw [this, hl', add_zero, hsub]
  rw [hmain]
  have hb := tsum_of_norm_bounded (hsum.mul_left Cd).hasSum b_δ
  refine hb.trans ?_
  rw [tsum_mul_left]
  have hCd0 : 0 ≤ Cd := by
    rw [hCd]
    exact mul_nonneg (mul_nonneg (add_nonneg hCs0 hCt0) c.E0nn)
      (mul_nonneg (Real.rpow_nonneg c.σpos.le _) (sq_nonneg _))
  calc Cd * ∑' X : T.polys, wt κ X.1 (T.dist X.1) ≤ Cd * K₀ :=
        mul_le_mul_of_nonneg_left c.hyp.count_le hCd0
    _ = _ := by rw [hCd]; ring

end Balaban.SmallField
