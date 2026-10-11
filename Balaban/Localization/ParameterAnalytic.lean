/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.AbstractExpansion
public import Balaban.Localization.RiemannSum
public import Balaban.Analysis.AnalyticLimit

/-!
# Analytic dependence of the coefficients on parameters

If `F λ s` is jointly analytic in `(λ, s) ∈ S × {|s i| < R}` with `S` open and bounded by `B`,
then `λ ↦ coef (F λ) C` is analytic on `S` for every `C`
(`analyticOnNhd_coef`), with the bound of `abstract_expansion`.

The proof: an interval integral `x ↦ ∫_0^1 Q (x[j := t]) dt` of a function analytic and bounded on
a domain is analytic there (`analyticOnNhd_integral_step`): the left Riemann sums are analytic,
and converge uniformly because `t ↦ Q (x[j := t])` is Lipschitz on `[0,1]` (Cauchy estimate in
the `j`-th coordinate); then use `analyticOnNhd_of_tendstoUniformlyOn`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban.Analysis Filter Set

section Gen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The derivative of `f` in the direction `v`. -/
noncomputable def lineD (v : E) (f : E → ℂ) : E → ℂ :=
  fun x => deriv (fun t : ℂ => f (x + t • v)) 0

theorem lineD_eq_fderiv {f : E → ℂ} {x : E} (v : E) (hf : DifferentiableAt ℂ f x) :
    lineD v f x = fderiv ℂ f x v := by
  have h1 : HasDerivAt (fun t : ℂ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
  have h2 : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v) := by
    simpa using hf.hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv

theorem analyticOnNhd_lineD {U : Set E} (hU : IsOpen U) {f : E → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (v : E) : AnalyticOnNhd ℂ (lineD v f) U := by
  have ha : AnalyticOnNhd ℂ (fun s => fderiv ℂ f s v) U := fun w hw =>
    ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt (fderiv ℂ f w)).comp (hf.fderiv w hw)
  exact ha.congr hU fun w hw => (lineD_eq_fderiv v (hf w hw).differentiableAt).symm

theorem hasDerivAt_real_line {f : E → ℂ} {a v : E} {t : ℝ}
    (hf : DifferentiableAt ℂ f (a + (t : ℂ) • v)) :
    HasDerivAt (fun x : ℝ => f (a + (x : ℂ) • v)) (fderiv ℂ f (a + (t : ℂ) • v) v) t := by
  have h1 : HasDerivAt (fun τ : ℂ => a + τ • v) v (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).smul_const v).const_add a
  exact (hf.hasFDerivAt.comp_hasDerivAt (t : ℂ) h1).comp_ofReal

/-- Iterated directional derivatives along a list of directions. -/
noncomputable def lineDList : List E → (E → ℂ) → (E → ℂ)
  | [], f => f
  | v :: l, f => lineDList l (lineD v f)

theorem analyticOnNhd_lineDList {U : Set E} (hU : IsOpen U) :
    ∀ (l : List E) {f : E → ℂ}, AnalyticOnNhd ℂ f U → AnalyticOnNhd ℂ (lineDList l f) U := by
  intro l
  induction l with
  | nil => exact fun h => h
  | cons v l ih => exact fun h => ih (analyticOnNhd_lineD hU h v)

end Gen

section Param

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The parameter-and-variable domain: `λ ∈ S`, and `‖s i‖ < R` for `i ∉ l`. -/
def Dom (S : Set Λ) (R : ℝ) (l : List ι) : Set (Λ × (ι → ℂ)) :=
  {x | x.1 ∈ S ∧ ∀ i, i ∉ l → ‖x.2 i‖ < R}

omit [NormedSpace ℂ Λ] in
theorem isOpen_Dom {S : Set Λ} (hS : IsOpen S) (R : ℝ) (l : List ι) : IsOpen (Dom S R l) := by
  have : Dom S R l = (Prod.fst ⁻¹' S) ∩
      ⋂ i ∈ (Finset.univ.filter (· ∉ l)), {x : Λ × (ι → ℂ) | ‖x.2 i‖ < R} := by
    ext x; simp [Dom]
  rw [this]
  refine (hS.preimage continuous_fst).inter (isOpen_biInter_finset fun i _ => ?_)
  exact isOpen_lt (continuous_norm.comp ((continuous_apply i).comp continuous_snd)) continuous_const

omit [NormedAddCommGroup Λ] [NormedSpace ℂ Λ] [Fintype ι] in
theorem update_mem_Dom {S : Set Λ} {R : ℝ} {l : List ι} {j : ι} {x : Λ × (ι → ℂ)}
    (hx : x ∈ Dom S R (j :: l)) {c : ℂ} (hc : ‖c‖ < R) :
    (x.1, Function.update x.2 j c) ∈ Dom S R l := by
  refine ⟨hx.1, fun i hi => ?_⟩
  by_cases hij : i = j
  · subst hij; simpa using hc
  · show ‖Function.update x.2 j c i‖ < R
    rw [Function.update_of_ne hij]; exact hx.2 i (by simp [hij, hi])

omit [Fintype ι] in
theorem update_eq_add (x : ι → ℂ) (j : ι) (c : ℂ) :
    Function.update x j c = x + (c - x j) • (Pi.single j 1 : ι → ℂ) := by
  ext i
  by_cases hij : i = j
  · subst hij; simp
  · simp [Function.update_of_ne hij, Pi.single_eq_of_ne hij]

theorem analyticAt_updX (j : ι) (c : ℂ) (x : Λ × (ι → ℂ)) :
    AnalyticAt ℂ (fun y : Λ × (ι → ℂ) => (y.1, Function.update y.2 j c)) x := by
  have : (fun y : Λ × (ι → ℂ) => (y.1, Function.update y.2 j c)) =
      fun y => (y.1, y.2 + (c - y.2 j) • (Pi.single j 1 : ι → ℂ)) := by
    funext y; rw [update_eq_add]
  rw [this]
  have hj : AnalyticAt ℂ (fun y : Λ × (ι → ℂ) => y.2 j) x :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) j).analyticAt x.2).comp
      (analyticAt_snd (𝕜 := ℂ))
  exact AnalyticAt.prod (analyticAt_fst (𝕜 := ℂ))
    ((analyticAt_snd (𝕜 := ℂ)).add ((analyticAt_const.sub hj).smul analyticAt_const))

/-- The Lipschitz bound in the `j`-th coordinate, from the Cauchy estimate. -/
theorem lipschitz_update {S : Set Λ} {R B : ℝ} (hR : 1 < R) (l : List ι) (j : ι)
    {Q : Λ × (ι → ℂ) → ℂ} (hQ : AnalyticOnNhd ℂ Q (Dom S R l))
    (hB : ∀ x ∈ Dom S R l, ‖Q x‖ ≤ B) {x : Λ × (ι → ℂ)} (hx : x ∈ Dom S R (j :: l)) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1,
      ‖Q (x.1, Function.update x.2 j (t : ℂ)) - Q (x.1, Function.update x.2 j (t' : ℂ))‖
        ≤ B / (R - 1) * |t - t'| := by
  set v : Λ × (ι → ℂ) := (0, Pi.single j 1) with hv
  set a : Λ × (ι → ℂ) := (x.1, Function.update x.2 j 0) with ha
  have hpt : ∀ τ : ℂ, (x.1, Function.update x.2 j τ) = a + τ • v := by
    intro τ
    refine Prod.ext (by simp [ha, hv]) (funext fun i => ?_)
    by_cases hij : i = j
    · subst hij; simp [ha, hv]
    · simp [ha, hv, Function.update_of_ne hij, Pi.single_eq_of_ne hij]
  have hmem : ∀ τ : ℂ, ‖τ‖ < R → a + τ • v ∈ Dom S R l := fun τ hτ => by
    rw [← hpt]; exact update_mem_Dom hx hτ
  have hdiff : ∀ τ : ℂ, ‖τ‖ < R → DifferentiableAt ℂ Q (a + τ • v) := fun τ hτ =>
    (hQ _ (hmem τ hτ)).differentiableAt
  have hreal : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖(t : ℂ)‖ < R := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℂ Q (a + (t : ℂ) • v) v‖ ≤ B / (R - 1) := by
    intro t ht
    refine norm_fderiv_line_le (by linarith) (fun l' hl' => ?_) (fun l' hl' => ?_)
    · have : a + (t : ℂ) • v + l' • v = a + ((t : ℂ) + l') • v := by rw [add_smul]; abel
      rw [this]
      refine hdiff _ ?_
      calc ‖(t : ℂ) + l'‖ ≤ ‖(t : ℂ)‖ + ‖l'‖ := norm_add_le _ _
        _ < R := by
          have := hreal t ht
          have h1 : ‖(t : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; exact ht.2
          linarith
    · have : a + (t : ℂ) • v + l' • v = a + ((t : ℂ) + l') • v := by rw [add_smul]; abel
      rw [this]
      refine hB _ (hmem _ ?_)
      calc ‖(t : ℂ) + l'‖ ≤ ‖(t : ℂ)‖ + ‖l'‖ := norm_add_le _ _
        _ < R := by
          have h1 : ‖(t : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; exact ht.2
          linarith
  intro t ht t' ht'
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => Q (a + (y : ℂ) • v))
    (f' := fun y => fderiv ℂ Q (a + (y : ℂ) • v) v) (C := B / (R - 1))
    (fun y hy => (hasDerivAt_real_line (hdiff _ (hreal y hy))).hasDerivWithinAt) hbound ht' ht
  rw [hpt, hpt]
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

/-- An interval integral of a bounded analytic function is analytic. -/
theorem analyticOnNhd_integral_step {S : Set Λ} {R B : ℝ} (hR : 1 < R) (hS : IsOpen S)
    (l : List ι) (j : ι) {Q : Λ × (ι → ℂ) → ℂ} (hQ : AnalyticOnNhd ℂ Q (Dom S R l))
    (hB : ∀ x ∈ Dom S R l, ‖Q x‖ ≤ B) :
    AnalyticOnNhd ℂ (fun x : Λ × (ι → ℂ) => ∫ t in (0 : ℝ)..1, Q (x.1, Function.update x.2 j (t : ℂ)))
      (Dom S R (j :: l)) ∧
    ∀ x ∈ Dom S R (j :: l),
      ‖∫ t in (0 : ℝ)..1, Q (x.1, Function.update x.2 j (t : ℂ))‖ ≤ B := by
  have hU := isOpen_Dom hS R (j :: l)
  have hreal : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖(t : ℂ)‖ < R := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  have hk : ∀ n k : ℕ, k < n + 1 → ((k : ℝ) / ((n + 1 : ℕ) : ℝ)) ∈ Icc (0 : ℝ) 1 := by
    intro n k hk
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hpos]; exact_mod_cast hk.le
  have hB0 : ∀ x ∈ Dom S R (j :: l), 0 ≤ B := fun x hx =>
    le_trans (norm_nonneg _) (hB _ (update_mem_Dom hx (c := 0) (by simp; linarith)))
  set f : ℕ → Λ × (ι → ℂ) → ℂ := fun n x => ((1 / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
    ∑ k ∈ Finset.range (n + 1),
      Q (x.1, Function.update x.2 j (((k : ℝ) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ)) with hf
  have hfa : ∀ n, AnalyticOnNhd ℂ (f n) (Dom S R (j :: l)) := by
    intro n x hx
    refine AnalyticAt.mul (analyticAt_const (𝕜 := ℂ)) (Finset.analyticAt_fun_sum _ fun k hkk => ?_)
    have h1 := (hQ _ (update_mem_Dom hx (hreal _ (hk n k (Finset.mem_range.mp hkk))))).comp
      (f := fun y : Λ × (ι → ℂ) => (y.1, Function.update y.2 j
        (((k : ℝ) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ))) (analyticAt_updX j _ x)
    exact h1
  have hfb : ∀ n, ∀ x ∈ Dom S R (j :: l), ‖f n x‖ ≤ B := by
    intro n x hx
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    simp only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hpos)]
    calc 1 / ((n + 1 : ℕ) : ℝ) * ‖∑ k ∈ Finset.range (n + 1), Q (x.1, Function.update x.2 j
            (((k : ℝ) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ))‖
        ≤ 1 / ((n + 1 : ℕ) : ℝ) * ∑ k ∈ Finset.range (n + 1), B := by
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k hkk => ?_))
            (by positivity)
          exact hB _ (update_mem_Dom hx (hreal _ (hk n k (Finset.mem_range.mp hkk))))
      _ = B := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  have hu : TendstoUniformlyOn f
      (fun x : Λ × (ι → ℂ) => ∫ t in (0 : ℝ)..1, Q (x.1, Function.update x.2 j (t : ℂ)))
      atTop (Dom S R (j :: l)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set L := B / (R - 1) with hL
    obtain ⟨N, hN⟩ := exists_nat_gt (L / ε)
    filter_upwards [eventually_ge_atTop N] with n hn x hx
    have hB' := hB0 x hx
    have hL0 : 0 ≤ L := div_nonneg hB' (by linarith)
    have hr := norm_integral_sub_riemann_le (g := fun t : ℝ => Q (x.1, Function.update x.2 j (t : ℂ)))
      hL0 (lipschitz_update hR l j hQ hB hx) (n + 1) (by omega)
    rw [dist_eq_norm]
    have hfe : f n x = (1 / ((n + 1 : ℕ) : ℝ)) • ∑ k ∈ Finset.range (n + 1),
        Q (x.1, Function.update x.2 j (((k : ℝ) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ)) := by
      simp only [hf, Complex.real_smul]
    rw [hfe]
    refine lt_of_le_of_lt hr ?_
    rw [div_lt_iff₀ (by positivity)]
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have : L < ε * N := by
      have := (div_lt_iff₀ hε).mp hN
      linarith
    push_cast
    nlinarith
  refine ⟨analyticOnNhd_of_tendstoUniformlyOn hU hfa hfb hu, fun x hx => ?_⟩
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := B)
    (f := fun t : ℝ => Q (x.1, Function.update x.2 j (t : ℂ)))
    (fun t ht => hB _ (update_mem_Dom hx (hreal t (by
      rw [← uIcc_of_le zero_le_one]; exact Set.uIoc_subset_uIcc ht))))
  simpa using this

/-- Iterated integrals of a bounded analytic function are analytic. -/
theorem analyticOnNhd_iterInt {S : Set Λ} {R B : ℝ} (hR : 1 < R) (hS : IsOpen S)
    {H : Λ × (ι → ℂ) → ℂ} (hH : AnalyticOnNhd ℂ H (Dom S R []))
    (hB : ∀ x ∈ Dom S R [], ‖H x‖ ≤ B) :
    ∀ l : List ι,
      AnalyticOnNhd ℂ (fun x : Λ × (ι → ℂ) => iterInt l (fun s => H (x.1, s)) x.2) (Dom S R l) ∧
      ∀ x ∈ Dom S R l, ‖iterInt l (fun s => H (x.1, s)) x.2‖ ≤ B := by
  intro l
  induction l with
  | nil => exact ⟨hH, hB⟩
  | cons j l ih => exact analyticOnNhd_integral_step hR hS l j ih.1 ih.2

theorem lineDList_map_eq (l : List ι) :
    ∀ (Φ : Λ × (ι → ℂ) → ℂ) (a : Λ) (s : ι → ℂ),
      lineDList (l.map fun i => ((0 : Λ), (Pi.single i 1 : ι → ℂ))) Φ (a, s) =
        pderList l (fun s => Φ (a, s)) s := by
  induction l with
  | nil => intro Φ a s; rfl
  | cons i l ih =>
    intro Φ a s
    simp only [List.map_cons, lineDList, pderList]
    rw [ih]
    congr 2
    funext s'
    simp [lineD, pder]

/-- **Lemma AE, parameter dependence.**  If `Φ (λ, s)` is analytic on `S × {|s i| < R}` and
bounded there, then each coefficient `λ ↦ F_C(λ)` is analytic on `S`. -/
theorem analyticOnNhd_coef {S : Set Λ} {R B : ℝ} (hR : 1 < R) (hS : IsOpen S)
    {Φ : Λ × (ι → ℂ) → ℂ}
    (hΦ : AnalyticOnNhd ℂ Φ (S ×ˢ polydisc (0 : ι → ℂ) (fun _ => R)))
    (hB : ∀ x ∈ S ×ˢ polydisc (0 : ι → ℂ) (fun _ => R), ‖Φ x‖ ≤ B) (C : Finset ι) :
    AnalyticOnNhd ℂ (fun a : Λ => coef (fun s => Φ (a, s)) C) S := by
  set R' := (1 + R) / 2 with hR'
  have hR'1 : 1 < R' := by rw [hR']; linarith
  have hR'R : R' < R := by rw [hR']; linarith
  set lC := Finset.univ.toList.filter (· ∈ C) with hlC
  set vs : List (Λ × (ι → ℂ)) := lC.map fun i => ((0 : Λ), (Pi.single i 1 : ι → ℂ)) with hvs
  set H := lineDList vs Φ with hH
  have hopen : IsOpen (S ×ˢ polydisc (0 : ι → ℂ) (fun _ => R)) :=
    hS.prod (isOpen_polydisc _ _)
  have hHa : AnalyticOnNhd ℂ H (S ×ˢ polydisc (0 : ι → ℂ) (fun _ => R)) :=
    analyticOnNhd_lineDList hopen vs hΦ
  have hHe : ∀ a s, H (a, s) = pderList lC (fun s => Φ (a, s)) s :=
    fun a s => lineDList_map_eq lC Φ a s
  have hsub : Dom S R' ([] : List ι) ⊆ S ×ˢ polydisc (0 : ι → ℂ) (fun _ => R) := by
    intro x hx
    exact ⟨hx.1, fun i => by simpa using lt_trans (hx.2 i (by simp)) hR'R⟩
  -- bound for `H` on `Dom S R' []`
  set B' := B / (R - R') ^ C.card with hB'
  have hHb : ∀ x ∈ Dom S R' ([] : List ι), ‖H x‖ ≤ B' := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hfa : AnalyticOnNhd ℂ (fun s => Φ (x.1, s)) (polydisc (0 : ι → ℂ) (fun _ => R)) := by
      intro s hs
      exact (hΦ (x.1, s) ⟨hx1, hs⟩).comp (f := fun s' : ι → ℂ => (x.1, s'))
        ((analyticAt_const (𝕜 := ℂ)).prod (analyticAt_id (𝕜 := ℂ)))
    have hsP : x.2 ∈ polydisc (0 : ι → ℂ) (fun _ => R) := fun i => by
      simpa using lt_trans (hx2 i (by simp)) hR'R
    have h1 := norm_pderList_le (c := (0 : ι → ℂ)) (r := fun _ => R) hfa
      (fun s hs => hB (x.1, s) ⟨hx1, hs⟩) lC (nodup_filter_toList C) hsP
    rw [toFinset_filter_toList] at h1
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB (x.1, 0) ⟨hx1, fun i => by simp; linarith⟩)
    have hpos : 0 < (R - R') ^ C.card := pow_pos (by linarith) _
    have : x = (x.1, x.2) := rfl
    rw [show H x = H (x.1, x.2) from rfl, hHe]
    refine h1.trans (div_le_div_of_nonneg_left hB0 hpos ?_)
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => by linarith) (fun i _ => by
      have := hx2 i (by simp); simp only [Pi.zero_apply, sub_zero]; linarith)
  have hit := analyticOnNhd_iterInt hR'1 hS (hHa.mono hsub) hHb lC
  intro a ha
  have hmem : (a, (0 : ι → ℂ)) ∈ Dom S R' lC := ⟨ha, fun i _ => by simp; linarith⟩
  have h1 := (hit.1 _ hmem).comp (f := fun a' : Λ => (a', (0 : ι → ℂ)))
    ((analyticAt_id (𝕜 := ℂ)).prod (analyticAt_const (𝕜 := ℂ)))
  refine h1.congr ?_
  filter_upwards [hS.mem_nhds ha] with a' ha'
  simp only [Function.comp, coef, hHe]
  rfl

end Param

end Balaban.Localization
