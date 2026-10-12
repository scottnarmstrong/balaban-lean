/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormTermwiseCrude

/-!
# Lemma 3.2 (iv): the subdomain form (3.2)

For a finite set `W ⊂ ℤ^d` (the neighbourhood `(Z^c_k)^≈`, in the centred form `y = 0`):

* `AW`: `A^W_y = ½ Σ_{x∈W} a^{(j)}(x - y)(ψ·ψ(x) - ψ·ψ(y))`; `AWx`: the term `A^W_{y,X}`;
* `IW`: `I^W(y,X) = I(y,X)` for `X ⊆ W` and `-T_X - Φ_{y,X} - A^W_{y,X}` otherwise;
* `energyW_sub_AW_eq_tsum_IW`: `Σ_{X∋y, X⊆W} 𝓔(y,X) - A^W_y = Σ_{X∋y} I^W(y,X)` (3.2);
* `IW_congr`: `I^W(y,X)` depends on `ψ` only on `(X ∩ W) ∪ star`;
* `IW_bound_outside`: for `X ⊄ W`, where `W` contains the `ℓ¹`-ball of radius `r`,
  `|I^W(y,X)| ≤ C E₀ e^{-(κ-1) d_j(X)} e^{-(r/A - 1)/2}`.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

open Classical in
/-- `A^W_{y,X} = ½ Σ_{x ∈ W} a_X(x)(ψ·ψ(x) - ψ·ψ(y))` (the sum of `A_{y,X}` over `x ∈ X ∩ W`). -/
noncomputable def AWx (T : TermFamily d N) (i₀ : Fin N) (ν : ℝ) (W : Finset (Site d))
    (ψ : Site d → Spin N) (X : Finset (Site d)) : ℂ :=
  (1 / 2 : ℂ) * ∑ x ∈ W, aCoefX T i₀ ν X x * (dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0))

/-- `A^W_y = ½ Σ_{x∈W} a^{(j)}(x)(ψ·ψ(x) - ψ·ψ(y))`. -/
noncomputable def AW (T : TermFamily d N) (i₀ : Fin N) (ν : ℝ) (W : Finset (Site d))
    (ψ : Site d → Spin N) : ℂ :=
  (1 / 2 : ℂ) * ∑ x ∈ W, aCoef T i₀ ν x * (dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0))

open Classical in
/-- `I^W(y,X)`: `I(y,X)` for `X ⊆ W`, `-T_X - Φ_{y,X} - A^W_{y,X}` for `X ⊄ W`. -/
noncomputable def IW (T : TermFamily d N) (i₀ i₁ : Fin N) (ν : ℝ) (W : Finset (Site d))
    (X : Finset (Site d)) (ψ : Site d → Spin N) (b : Spin N) : ℂ :=
  if X ⊆ W then Itw T i₀ i₁ ν X ψ b
  else -Ttw T i₀ ν X ψ b - Phitw T i₀ i₁ ν X ψ - AWx T i₀ ν W ψ X

open Classical in
/-- `Σ_{X∋y, X⊆W} 𝓔(y,X; ψ, b)`. -/
noncomputable def energyW (T : TermFamily d N) (W : Finset (Site d)) (ψ : Site d → Spin N)
    (b : Spin N) : ℂ :=
  ∑' X : T.polys, if X.1 ⊆ W then T.term X.1 (pack X.1 ψ b) else 0

section Sub

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)}

open Classical in
theorem AWx_eq_Ax {W X : Finset (Site d)} (hXW : X ⊆ W) (ψ : Site d → Spin N) :
    AWx T i₀ ν W ψ X = Ax T i₀ ν ψ X := by
  unfold AWx Ax
  congr 1
  rw [← Finset.sum_subset hXW (fun x _ hx => by rw [aCoefX_zero hx, zero_mul]),
    ← Finset.sum_coe_sort X]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [aCoefX, x.2]

open Classical in
theorem IW_eq (W X : Finset (Site d)) (ψ : Site d → Spin N) (b : Spin N) :
    IW T i₀ i₁ ν W X ψ b = (if X ⊆ W then T.term X (pack X ψ b) else 0) - Ttw T i₀ ν X ψ b
      - Phitw T i₀ i₁ ν X ψ - AWx T i₀ ν W ψ X := by
  unfold IW
  by_cases h : X ⊆ W
  · simp only [h, ite_true, AWx_eq_Ax h]; unfold Itw; ring
  · simp only [h, ite_false]; ring

theorem aCoefX_norm_le_tw (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ)
    (hE0 : 0 ≤ E₀) {X : Finset (Site d)} (hX : X ∈ T.polys) (x : Site d) :
    ‖aCoefX T i₀ ν X x‖ ≤ E₀ * Real.exp (-κ * T.dist X) / ρ := by
  by_cases hx : x ∈ X
  · have hok := hP.termOK hρ hX
    have hM : ∀ y ∈ ball (refPt i₀ ν X) ρ, ‖T.term X y‖ ≤ E₀ * Real.exp (-κ * T.dist X) :=
      fun y hy => hP.bdd_tube X hX y (ball_subset_tube i₀ ν ρ X hy)
    simpa [aCoefX, hx] using hok.norm_tensA_le hM ⟨x, hx⟩
  · rw [aCoefX_zero hx]; simp; positivity

/-- **Lemma 3.2 (iv), the identity (3.2)**:
`Σ_{X∋y, X⊆W} 𝓔(y,X) - A^W_y = Σ_{X∋y} I^W(y,X)`. -/
theorem energyW_sub_AW_eq_tsum_IW (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom)
    (hS : SumConds T i₀ i₁ ν) (hρ : 0 < ρ) (hE0 : 0 ≤ E₀) (hA : 0 ≤ A) (W : Finset (Site d))
    {ψ : Site d → Spin N} {b : Spin N} {σ ε K₂ : ℝ} (dat : DataHyp Dom ν σ ε K₂ ψ b) :
    energyW T W ψ b - AW T i₀ ν W ψ = ∑' X : T.polys, IW T i₀ i₁ ν W X.1 ψ b := by
  classical
  have hP' := hP.toPremises hS
  have hsum : Summable fun X : T.polys => wt κ X.1 (T.dist X.1) := hP.count_summable
  have hMle : ∀ X : T.polys, E₀ * Real.exp (-κ * T.dist X.1) ≤ E₀ * wt κ X.1 (T.dist X.1) := fun X => by
    have := wt_ge (κ := κ) X.1 (hP.dist_nonneg X.1 X.2)
      (Finset.card_pos.mpr ⟨0, hP.zero_mem X.1 X.2⟩) 0 0 (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul] at this
    exact mul_le_mul_of_nonneg_left this hE0
  have S_e : Summable fun X : T.polys =>
      (if X.1 ⊆ W then T.term X.1 (pack X.1 ψ b) else 0) := by
    refine Summable.of_norm_bounded (hsum.mul_left E₀) fun X => ?_
    by_cases h : X.1 ⊆ W
    · simp only [h, ite_true]
      exact (hP.bdd_dom X.1 X.2 (ψ, b) dat.mem).trans (hMle X)
    · simp only [h, ite_false, norm_zero]
      have := wt_ge (κ := κ) X.1 (hP.dist_nonneg X.1 X.2)
        (Finset.card_pos.mpr ⟨0, hP.zero_mem X.1 X.2⟩) 0 0 (by norm_num) (by norm_num)
      have h0 : 0 ≤ wt κ X.1 (T.dist X.1) := le_trans (by positivity) this
      positivity
  obtain ⟨S_v0, S_s, S_d⟩ := hP.summable_tensors hρ hE0
  have S_T : Summable fun X : T.polys => Ttw T i₀ ν X.1 ψ b :=
    (S_v0.add (S_s.mul_left (uInv ψ - 1))).add (S_d.mul_left (vInv ψ b - ν))
  have S_Φ : Summable fun X : T.polys => Phitw T i₀ i₁ ν X.1 ψ := by
    unfold Phitw
    exact (summable_sum fun μ _ => summable_sum fun μ' _ =>
      (Sx_summable hP' hρ hE0 hA μ μ').mul_left _).mul_left _
  -- the summable coefficient families
  set h : Site d → ℂ := fun x => dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0) with hh
  have S_a : ∀ x : Site d, Summable fun X : T.polys => aCoefX T i₀ ν X.1 x := fun x => by
    refine Summable.of_norm_bounded (hsum.mul_left (E₀ / ρ)) fun X => ?_
    refine (aCoefX_norm_le_tw hP hρ hE0 X.2 x).trans ?_
    calc E₀ * Real.exp (-κ * T.dist X.1) / ρ ≤ E₀ * wt κ X.1 (T.dist X.1) / ρ :=
          div_le_div_of_nonneg_right (hMle X) hρ.le
      _ = _ := by ring
  have S_AW : Summable fun X : T.polys => AWx T i₀ ν W ψ X.1 := by
    unfold AWx
    exact (summable_sum fun x _ => (S_a x).mul_right (h x)).mul_left _
  have h1 : ∑' X : T.polys, IW T i₀ i₁ ν W X.1 ψ b =
      energyW T W ψ b - ∑' X : T.polys, Ttw T i₀ ν X.1 ψ b -
        ∑' X : T.polys, Phitw T i₀ i₁ ν X.1 ψ - ∑' X : T.polys, AWx T i₀ ν W ψ X.1 := by
    simp only [IW_eq]
    unfold energyW
    rw [Summable.tsum_sub ((S_e.sub S_T).sub S_Φ) S_AW, Summable.tsum_sub (S_e.sub S_T) S_Φ,
      Summable.tsum_sub S_e S_T]
  have h2 : ∑' X : T.polys, AWx T i₀ ν W ψ X.1 = AW T i₀ ν W ψ := by
    unfold AWx AW
    rw [tsum_mul_left]
    congr 1
    rw [Summable.tsum_finsetSum (fun x _ => (S_a x).mul_right (h x))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [tsum_mul_right]
    rfl
  rw [h1, h2, Ttw_tsum_zero hP hS hρ hE0, Phitw_tsum_zero hP hS hρ hE0 hA]
  ring

open Classical in
/-- **Lemma 3.2 (iv), locality**: `I^W(y,X)` depends on `ψ` only on `(X ∩ W) ∪ star`. -/
theorem IW_congr {W X : Finset (Site d)} {ψ ψ' : Site d → Spin N} {b : Spin N}
    (h0 : (0 : Site d) ∈ X)
    (h : ∀ x ∈ (X ∩ W) ∪ starSet d, ψ x = ψ' x) :
    IW T i₀ i₁ ν W X ψ b = IW T i₀ i₁ ν W X ψ' b := by
  have hst : ∀ x ∈ starSet d, ψ x = ψ' x := fun x hx => h x (Finset.mem_union_right _ hx)
  by_cases hXW : X ⊆ W
  · unfold IW
    simp only [hXW, ite_true]
    refine Itw_congr h0 fun x hx => h x ?_
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hXW hx⟩)
    · exact Finset.mem_union_right _ hx
  · unfold IW
    simp only [hXW, ite_false]
    rw [Ttw_congr (hst 0 zero_mem_starSet), Phitw_congr hst]
    congr 1
    unfold AWx
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    by_cases hxX : x ∈ X
    · rw [h x (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxX, hx⟩)),
        hst 0 zero_mem_starSet]
    · rw [aCoefX_zero hxX, zero_mul, zero_mul]

theorem crude_AW (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ) (hE0 : 0 ≤ E₀)
    {X : Finset (Site d)} (hX : X ∈ T.polys) (W : Finset (Site d)) {ψ : Site d → Spin N}
    {b : Spin N} {σ ε K₂ : ℝ} (dat : DataHyp Dom ν σ ε K₂ ψ b) :
    ‖AWx T i₀ ν W ψ X‖ ≤ E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) * (σ ^ 2 * ε / ρ)) := by
  classical
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hτ0 : 0 ≤ σ ^ 2 * ε := le_trans (norm_nonneg _) (dat.sq 0)
  have hga : ∀ x, ‖dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)‖ ≤ 2 * (σ ^ 2 * ε) := by
    intro x
    have h1 := dat.sq x
    have h2 := dat.sq 0
    calc ‖dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)‖
        = ‖(dot (ψ x) (ψ x) - 1) - (dot (ψ 0) (ψ 0) - 1)‖ := by ring_nf
      _ ≤ ‖dot (ψ x) (ψ x) - 1‖ + ‖dot (ψ 0) (ψ 0) - 1‖ := norm_sub_le _ _
      _ ≤ 2 * (σ ^ 2 * ε) := by linarith
  unfold AWx
  rw [norm_mul]
  have hsub : ∑ x ∈ W, aCoefX T i₀ ν X x * (dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)) =
      ∑ x ∈ W ∩ X, aCoefX T i₀ ν X x * (dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)) := by
    symm
    refine Finset.sum_subset Finset.inter_subset_left fun x hxW hx => ?_
    have : x ∉ X := fun h => hx (Finset.mem_inter.mpr ⟨hxW, h⟩)
    rw [aCoefX_zero this, zero_mul]
  rw [hsub]
  have h1 : ‖∑ x ∈ W ∩ X, aCoefX T i₀ ν X x * (dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0))‖ ≤
      ((W ∩ X).card : ℝ) * (M / ρ * (2 * (σ ^ 2 * ε))) := by
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_card_nsmul (W ∩ X)
      (fun x => ‖aCoefX T i₀ ν X x * (dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0))‖)
      (M / ρ * (2 * (σ ^ 2 * ε))) fun x _ => by
        rw [norm_mul]
        exact mul_le_mul (aCoefX_norm_le_tw hP hρ hE0 hX x) (hga x) (norm_nonneg _)
          (by positivity)
    simpa [nsmul_eq_mul] using this
  have hcard : ((W ∩ X).card : ℝ) ≤ (X.card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h2]
  have e : M * ((X.card : ℝ) * (σ ^ 2 * ε / ρ)) =
      1 / 2 * ((X.card : ℝ) * (M / ρ * (2 * (σ ^ 2 * ε)))) := by field_simp
  rw [e]
  refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by norm_num)
  exact mul_le_mul_of_nonneg_right hcard (by positivity)
theorem outside_parts (d N : ℕ) (A Λ Sm : ℝ) (hA : 0 ≤ A) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν ρ E₀ κ K₀ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (ψ : Site d → Spin N) (b : Spin N)
      (σ ε K₂ : ℝ) (_ : DataHyp Dom ν σ ε K₂ ψ b) (W X : Finset (Site d)) (_ : X ∈ T.polys),
      0 < ρ → ρ ≤ 1 → 0 < ε → ε ≤ Λ * ρ → 0 < σ → σ ≤ Sm → σ ^ 2 * ε ≤ 1 / 4 → 0 ≤ ν →
      ν ≤ σ ^ 2 → 0 ≤ E₀ →
      ‖Ttw T i₀ ν X ψ b‖ + ‖Phitw T i₀ i₁ ν X ψ‖ + ‖AWx T i₀ ν W ψ X‖ ≤
        C * (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hΛ0 : 0 ≤ Λ := by linarith
  set Qm : ℝ := Sm ^ 2 * Λ with hQm
  set c₁ : ℝ := N + 8 * (N : ℝ) ^ 2 with hc₁
  have hQ0 : 0 ≤ Qm := by positivity
  have hc₁0 : 0 ≤ c₁ := by positivity
  set C0 : ℝ := 2 + 2 * Qm + (Sm ^ 2 + 3 * N) * Qm + 16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * Sm ^ 2 * Λ ^ 2
    with hC0
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨C0, hC00, ?_⟩
  intro T i₀ i₁ ν ρ E₀ κ K₀ Dom hP ψ b σ ε K₂ dat W X hX hρ hρ1 hε hεΛ hσ hσSm hτ hν hνσ hE0
  obtain ⟨u, huU, hus, hu1, hu34, hg⟩ := crude_frame i₀ dat hτ
  have hS2 : ν ≤ Sm ^ 2 := hνσ.trans (pow_le_pow_left₀ hσ.le hσSm 2)
  have hτ0 : 0 ≤ σ ^ 2 * ε := le_trans (norm_nonneg _) (dat.sq 0)
  have hq := crude_ratio hρ hε hεΛ hσ hσSm
  have hq0 : 0 ≤ σ ^ 2 * ε / ρ := by positivity
  have hβ := crude_beta dat huU hus hu1 hu34 hν hS2
  have hbT := crude_T hP hρ hE0 hX (ψ := ψ) (b := b) (τ := σ ^ 2 * ε)
    (B := (Sm ^ 2 + 3 * N) * (σ ^ 2 * ε)) (by rw [huU]; exact hu1) hβ hτ0
  have hbA := crude_AW hP hρ hE0 hX W dat
  have hbΦ := crude_Phi hP hρ hE0 hA hX dat hg
  have hd0 := hP.dist_nonneg X hX
  have hP1 : (1 : ℝ) ≤ X.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, hP.zero_mem X hX⟩
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X) := by positivity
  -- abbreviations
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  set P : ℝ := (X.card : ℝ) with hPdef
  set t : ℝ := 1 + T.dist X with htdef
  have ht1 : 1 ≤ t := by rw [htdef]; linarith
  have hP2 : 1 ≤ P ^ 2 := one_le_pow₀ hP1
  have ht6 : 1 ≤ t ^ 6 := one_le_pow₀ ht1
  have hW : 1 ≤ P ^ 2 * t ^ 6 := one_le_mul_of_one_le_of_one_le hP2 ht6
  have hMY : M ≤ M * (P ^ 2 * t ^ 6) := le_mul_of_one_le_right hM0 hW
  have hPMY : P * M ≤ M * (P ^ 2 * t ^ 6) := by
    have h1 : P ≤ P ^ 2 := le_self_pow₀ hP1 (by norm_num)
    have h2 : P ^ 2 ≤ P ^ 2 * t ^ 6 := le_mul_of_one_le_right (by positivity) ht6
    calc P * M = M * P := mul_comm _ _
      _ ≤ M * (P ^ 2 * t ^ 6) := mul_le_mul_of_nonneg_left (h1.trans h2) hM0
  have hP2tY : M * (P ^ 2 * t ^ 2) ≤ M * (P ^ 2 * t ^ 6) := by
    have : P ^ 2 * t ^ 2 ≤ P ^ 2 * t ^ 6 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by norm_num)) (by positivity)
    exact mul_le_mul_of_nonneg_left this hM0
  have hY0 : 0 ≤ M * (P ^ 2 * t ^ 6) := by positivity
  -- T
  have hT1 : ‖Ttw T i₀ ν X ψ b‖ ≤ M * (1 + P * Qm + (Sm ^ 2 + 3 * N) * Qm) := by
    refine hbT.trans ?_
    have e : (Sm ^ 2 + 3 * N) * (σ ^ 2 * ε) / ρ = (Sm ^ 2 + 3 * N) * (σ ^ 2 * ε / ρ) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hM0
    have : 0 ≤ Sm ^ 2 + 3 * (N : ℝ) := by positivity
    have h1 : P * (σ ^ 2 * ε / ρ) ≤ P * Qm := mul_le_mul_of_nonneg_left hq (by linarith)
    have h2 : (Sm ^ 2 + 3 * N) * (σ ^ 2 * ε / ρ) ≤ (Sm ^ 2 + 3 * N) * Qm :=
      mul_le_mul_of_nonneg_left hq this
    linarith
  have hA1 : ‖AWx T i₀ ν W ψ X‖ ≤ M * (P * Qm) := by
    refine hbA.trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (by linarith)) hM0
  have hΦ1 : ‖Phitw T i₀ i₁ ν X ψ‖ ≤ 16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * Sm ^ 2 * Λ ^ 2 *
      (M * (P ^ 2 * t ^ 2)) := by
    refine hbΦ.trans ?_
    have hr : (σ * ε) ^ 2 / ρ ^ 2 ≤ Sm ^ 2 * Λ ^ 2 := by
      have hε' : ε / ρ ≤ Λ := by rw [div_le_iff₀ hρ]; linarith
      have e : (σ * ε) ^ 2 / ρ ^ 2 = σ ^ 2 * (ε / ρ) ^ 2 := by field_simp
      rw [e]
      have h1 : σ ^ 2 ≤ Sm ^ 2 := pow_le_pow_left₀ hσ.le hσSm 2
      have h2 : (ε / ρ) ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (by positivity) hε' 2
      exact mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    have e : (d : ℝ) ^ 2 * c₁ * (σ * ε) ^ 2 *
        (P ^ 2 * (4 * M / ρ ^ 2) * (2 * (A * t)) ^ 2) =
        16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * (M * (P ^ 2 * t ^ 2)) * ((σ * ε) ^ 2 / ρ ^ 2) := by
      field_simp
      ring
    have e' : (1 + T.dist X) = t := rfl
    rw [e'] at *
    rw [e]
    have h16 : 0 ≤ 16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * (M * (P ^ 2 * t ^ 2)) := by positivity
    calc _ ≤ 16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * (M * (P ^ 2 * t ^ 2)) * (Sm ^ 2 * Λ ^ 2) :=
          mul_le_mul_of_nonneg_left hr h16
      _ = _ := by ring
  have hB0 : 0 ≤ Sm ^ 2 + 3 * (N : ℝ) := by positivity
  have x2 : P * M * Qm ≤ (M * (P ^ 2 * t ^ 6)) * Qm := mul_le_mul_of_nonneg_right hPMY hQ0
  have x3 : M * ((Sm ^ 2 + 3 * N) * Qm) ≤ (M * (P ^ 2 * t ^ 6)) * ((Sm ^ 2 + 3 * N) * Qm) :=
    mul_le_mul_of_nonneg_right hMY (by positivity)
  have x4 : 16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * Sm ^ 2 * Λ ^ 2 * (M * (P ^ 2 * t ^ 2)) ≤
      16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * Sm ^ 2 * Λ ^ 2 * (M * (P ^ 2 * t ^ 6)) :=
    mul_le_mul_of_nonneg_left hP2tY (by positivity)
  have e1 : M * (1 + P * Qm + (Sm ^ 2 + 3 * N) * Qm) =
      M + P * M * Qm + M * ((Sm ^ 2 + 3 * N) * Qm) := by ring
  have e2 : M * (P * Qm) = P * M * Qm := by ring
  have : C0 * (M * (P ^ 2 * t ^ 6)) =
      2 * (M * (P ^ 2 * t ^ 6)) + 2 * ((M * (P ^ 2 * t ^ 6)) * Qm) +
      (M * (P ^ 2 * t ^ 6)) * ((Sm ^ 2 + 3 * N) * Qm) +
      16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * Sm ^ 2 * Λ ^ 2 * (M * (P ^ 2 * t ^ 6)) := by
    rw [hC0]; ring
  rw [this]
  rw [e1] at hT1
  rw [e2] at hA1
  have : M * (P ^ 2 * t ^ 6) = E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6) := by
    rw [hMdef]
  linarith



/-- The polynomial weight is absorbed into `e^{-t/2}` (half a unit of `κ` is lost, not one). -/
theorem weight_absorb_half (A : ℝ) (hA : 0 ≤ A) (d : ℕ) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ (κ t P : ℝ), 0 ≤ t → 0 ≤ P → P ≤ (2 * (A * (1 + t)) + 1) ^ d →
      Real.exp (-κ * t) * (P ^ 2 * (1 + t) ^ 6) ≤ Cw * Real.exp (-(κ - 1 / 2) * t) := by
  refine ⟨(2 * A + 1) ^ (2 * d) * (2 ^ (2 * d + 6) * ((2 * d + 6).factorial : ℝ)) *
    Real.exp (1 / 2), by positivity, ?_⟩
  intro κ t P ht hP0 hP
  have ht1 : (1 : ℝ) ≤ 1 + t := by linarith
  have h1 : 2 * (A * (1 + t)) + 1 ≤ (2 * A + 1) * (1 + t) := by nlinarith
  have h2 : P ≤ ((2 * A + 1) * (1 + t)) ^ d :=
    hP.trans (pow_le_pow_left₀ (by positivity) h1 d)
  have h3 : P ^ 2 ≤ ((2 * A + 1) ^ (2 * d)) * (1 + t) ^ (2 * d) := by
    calc P ^ 2 ≤ (((2 * A + 1) * (1 + t)) ^ d) ^ 2 := pow_le_pow_left₀ hP0 h2 2
      _ = _ := by rw [← pow_mul, mul_pow, mul_comm d 2]
  have h4 : (1 + t) ^ (2 * d + 6) ≤
      2 ^ (2 * d + 6) * ((2 * d + 6).factorial : ℝ) * Real.exp ((1 + t) / 2) := by
    have := Real.pow_div_factorial_le_exp ((1 + t) / 2) (by linarith) (2 * d + 6)
    rw [div_le_iff₀ (by positivity), div_pow, div_le_iff₀ (by positivity)] at this
    calc (1 + t) ^ (2 * d + 6) ≤ Real.exp ((1 + t) / 2) * ((2 * d + 6).factorial : ℝ) *
          2 ^ (2 * d + 6) := this
      _ = _ := by ring
  have hexp : Real.exp (-κ * t) = Real.exp (-(κ - 1 / 2) * t) * Real.exp (-(t / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp (-κ * t) * (P ^ 2 * (1 + t) ^ 6)
      ≤ Real.exp (-κ * t) * (((2 * A + 1) ^ (2 * d)) * (1 + t) ^ (2 * d) * (1 + t) ^ 6) := by
        gcongr
    _ = Real.exp (-(κ - 1 / 2) * t) * ((2 * A + 1) ^ (2 * d)) *
          ((1 + t) ^ (2 * d + 6) * Real.exp (-(t / 2))) := by
        rw [hexp]; ring
    _ ≤ Real.exp (-(κ - 1 / 2) * t) * ((2 * A + 1) ^ (2 * d)) *
          (2 ^ (2 * d + 6) * ((2 * d + 6).factorial : ℝ) * Real.exp ((1 + t) / 2) *
            Real.exp (-(t / 2))) := by
        gcongr
    _ = _ := by
        have : Real.exp ((1 + t) / 2) * Real.exp (-(t / 2)) = Real.exp (1 / 2) := by
          rw [← Real.exp_add]; congr 1; ring
        calc _ = Real.exp (-(κ - 1 / 2) * t) * ((2 * A + 1) ^ (2 * d)) *
              (2 ^ (2 * d + 6) * ((2 * d + 6).factorial : ℝ)) *
              (Real.exp ((1 + t) / 2) * Real.exp (-(t / 2))) := by ring
          _ = _ := by rw [this]; ring

/-- **Lemma 3.2 (iv), the terms outside `W`**: if `W` contains the `ℓ¹`-ball of radius `r` and
`X ⊄ W`, then `d_j(X) ≥ r/A - 1` (the path bound `diam`) and
`|I^W(y,X)| ≤ C E₀ e^{-(κ-1) d_j(X)} e^{-(r/A - 1)/2}`, for the data (Σ1) with `σ ≤ Σ_m`,
`σ² ε ≤ 1/4`; no renormalization condition and no smallness of `σ` is used. -/
theorem IW_bound_outside (d N : ℕ) (A Λ Sm : ℝ) (hA : 0 < A) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν ρ E₀ κ K₀ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (ψ : Site d → Spin N) (b : Spin N)
      (σ ε K₂ : ℝ) (_ : DataHyp Dom ν σ ε K₂ ψ b) (W X : Finset (Site d)) (_ : X ∈ T.polys)
      (r : ℝ), (∀ x : Site d, ((∑ μ, |x μ| : ℤ) : ℝ) ≤ r → x ∈ W) → ¬ X ⊆ W →
      0 < ρ → ρ ≤ 1 → 0 < ε → ε ≤ Λ * ρ → 0 < σ → σ ≤ Sm → σ ^ 2 * ε ≤ 1 / 4 → 0 ≤ ν →
      ν ≤ σ ^ 2 → 0 ≤ E₀ →
      ‖IW T i₀ i₁ ν W X ψ b‖ ≤
        C * E₀ * Real.exp (-(κ - 1) * T.dist X) * Real.exp (-(r / A - 1) / 2) := by
  classical
  obtain ⟨C0, hC00, hC0⟩ := outside_parts d N A Λ Sm hA.le hΛ
  obtain ⟨Cw, hCw0, hCw⟩ := weight_absorb_half A hA.le d
  refine ⟨C0 * Cw, by positivity, ?_⟩
  intro T i₀ i₁ ν ρ E₀ κ K₀ Dom hP ψ b σ ε K₂ dat W X hX r hW hXW hρ hρ1 hε hεΛ hσ hσSm hτ hν hνσ hE0
  have hpar := hC0 T i₀ i₁ ν ρ E₀ κ K₀ Dom hP ψ b σ ε K₂ dat W X hX hρ hρ1 hε hεΛ hσ hσSm hτ hν hνσ hE0
  have hd0 := hP.dist_nonneg X hX
  -- the lower bound for the distance
  have hdist : r / A - 1 ≤ T.dist X := by
    obtain ⟨x, hxX, hxW⟩ := Finset.not_subset.mp hXW
    have h1 : r < ((∑ μ, |x μ| : ℤ) : ℝ) := by
      by_contra hcon
      exact hxW (hW x (not_lt.mp hcon))
    have h2 := hP.diam X hX x hxX
    have h3 : r < A * (1 + T.dist X) := h1.trans_le h2
    rw [div_sub_one hA.ne', div_le_iff₀ hA]
    nlinarith
  have hI : ‖IW T i₀ i₁ ν W X ψ b‖ ≤ ‖Ttw T i₀ ν X ψ b‖ + ‖Phitw T i₀ i₁ ν X ψ‖ +
      ‖AWx T i₀ ν W ψ X‖ := by
    unfold IW
    simp only [hXW, ite_false]
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans ?_) le_rfl
    rw [norm_neg]
  have hcard := card_le_of_diam hP hX
  have hab := hCw κ (T.dist X) (X.card : ℝ) hd0 (Nat.cast_nonneg _) hcard
  have hex : Real.exp (-(κ - 1 / 2) * T.dist X) ≤
      Real.exp (-(κ - 1) * T.dist X) * Real.exp (-(r / A - 1) / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  refine hI.trans (hpar.trans ?_)
  calc C0 * (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6))
      = C0 * E₀ * (Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) := by ring
    _ ≤ C0 * E₀ * (Cw * Real.exp (-(κ - 1 / 2) * T.dist X)) :=
        mul_le_mul_of_nonneg_left hab (mul_nonneg hC00 hE0)
    _ ≤ C0 * E₀ * (Cw * (Real.exp (-(κ - 1) * T.dist X) * Real.exp (-(r / A - 1) / 2))) := by
        have : 0 ≤ C0 * E₀ * Cw := by positivity
        calc _ = C0 * E₀ * Cw * Real.exp (-(κ - 1 / 2) * T.dist X) := by ring
          _ ≤ C0 * E₀ * Cw * (Real.exp (-(κ - 1) * T.dist X) * Real.exp (-(r / A - 1) / 2)) :=
              mul_le_mul_of_nonneg_left hex this
          _ = _ := by ring
    _ = _ := by ring

end Sub

end Balaban.SmallField
