module

public import Balaban.Polymer.Gas

/-!
# The activity bound in GAS

With `|β Y| ≤ B₀ e^{-κ'' d(Y)}`, `|τ Z| ≤ e^{-p - h |Z|}` and the entropy bounds, every polymer
`X` with `|X| ≤ c₁ (1 + d(X))` has `|K(X)| ≤ 3 c₁ e^{-p} e^{-(κ' - 2) d(X)}`
(`gas_activity_bound`; POLYMER.md §2.6, §3.9 with the corrected constants: the threshold for the
volume decay `h` is `C + κ'(c₂ + c) + c₁ + 3 + ln K₀''`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

section Entropy

variable {B Zt : Type*} [Fintype B] [Fintype Zt] {zs : Zt → Finset B}

/-- The entropy sum of the heavy objects through a block. -/
theorem heavy_entropy {K0 c1 lam : ℝ} (hc1 : 0 ≤ c1) (hK0 : 1 ≤ K0)
    (hz : ∀ z, (zs z).Nonempty)
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤ K0 ^ v)
    (hlam : c1 + 3 + Real.log K0 ≤ lam) (b : B) :
    ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z), Real.exp (-lam * (zs z).card) ≤
      Real.exp (-(c1 + 2)) := by
  set x : ℝ := K0 * Real.exp (-lam) with hx
  have hK0pos : 0 < K0 := by linarith
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ Real.exp (-(c1 + 3)) := by
    rw [hx]
    calc K0 * Real.exp (-lam) = Real.exp (Real.log K0) * Real.exp (-lam) := by
          rw [Real.exp_log hK0pos]
      _ = Real.exp (Real.log K0 - lam) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(c1 + 3)) := Real.exp_le_exp.mpr (by linarith)
  have he3 : Real.exp (-3) ≤ 1 / 2 := by
    have h3 : (2 : ℝ) ≤ Real.exp 3 := by
      have := Real.add_one_le_exp (3 : ℝ); linarith
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h3
  have hx12 : x ≤ 1 / 2 :=
    hx1.trans ((Real.exp_le_exp.mpr (by linarith : -(c1 + 3) ≤ -3)).trans he3)
  have hg : ∀ z ∈ Finset.univ.filter (fun z => b ∈ zs z),
      (zs z).card - 1 ∈ Finset.range (Fintype.card B) := by
    intro z hzF
    rw [Finset.mem_filter] at hzF
    rw [Finset.mem_range]
    have h1 := Finset.card_le_univ (zs z)
    have h2 : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨b⟩
    have h3 := (hz z).card_pos
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hg]
  have hinner : ∀ j ∈ Finset.range (Fintype.card B),
      ∑ z ∈ (Finset.univ.filter (fun z => b ∈ zs z)).filter (fun z => (zs z).card - 1 = j),
        Real.exp (-lam * (zs z).card) ≤ x ^ (j + 1) := by
    intro j _
    have hset : (Finset.univ.filter (fun z => b ∈ zs z)).filter (fun z => (zs z).card - 1 = j) =
        Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = j + 1) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := (hz z).card_pos
      constructor
      · rintro ⟨hb, hj⟩; exact ⟨hb, by omega⟩
      · rintro ⟨hb, hj⟩; exact ⟨hb, by omega⟩
    rw [hset]
    have : ∀ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = j + 1),
        Real.exp (-lam * (zs z).card) = Real.exp (-lam) ^ (j + 1) := by
      intro z hzz
      rw [Finset.mem_filter] at hzz
      rw [hzz.2.2, ← Real.exp_nat_mul]
      congr 1; push_cast; ring
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hx, mul_pow]
    exact mul_le_mul_of_nonneg_right (hcount b (j + 1)) (by positivity)
  refine (Finset.sum_le_sum hinner).trans ?_
  have hgeo : ∑ j ∈ Finset.range (Fintype.card B), x ^ j ≤ (1 - x)⁻¹ :=
    sum_le_hasSum _ (fun i _ => by positivity) (hasSum_geometric_of_lt_one hx0 (by linarith))
  calc ∑ j ∈ Finset.range (Fintype.card B), x ^ (j + 1)
      = x * ∑ j ∈ Finset.range (Fintype.card B), x ^ j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ x * (1 - x)⁻¹ := mul_le_mul_of_nonneg_left hgeo hx0
    _ ≤ x * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hx0
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
    _ ≤ 2 * Real.exp (-(c1 + 3)) := by linarith
    _ ≤ Real.exp (-(c1 + 2)) := by
        have h1 : Real.exp (-(c1 + 2)) = Real.exp 1 * Real.exp (-(c1 + 3)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [h1]
        have := Real.exp_one_gt_d9
        have hp := Real.exp_pos (-(c1 + 3))
        nlinarith

end Entropy

section RealBound

/-- The real-variable inequality closing the proof of GAS. -/
theorem gas_real_bound {p c1 D n : ℝ} (hp : 0 ≤ p) (hc1 : 0 ≤ c1) (hD : 0 ≤ D) (hn : 0 ≤ n)
    (hG1 : n ≤ c1 * (1 + D)) :
    Real.exp (n * (Real.exp (-p) * Real.exp (-(c1 + 2)))) - 1 ≤
      3 * c1 * Real.exp (-p) * Real.exp (2 * D) := by
  set η : ℝ := Real.exp (-p) * Real.exp (-(c1 + 2)) with hη
  have hη0 : 0 < η := by positivity
  have hηp : η ≤ Real.exp (-p) := by
    rw [hη]
    calc _ ≤ Real.exp (-p) * 1 := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by linarith)
      _ = _ := mul_one _
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have h1 := Real.exp_one_gt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith
  have hc1η : c1 * η ≤ 1 / 7 := by
    have h1 : c1 * Real.exp (-(c1 + 2)) ≤ 1 / 7 := by
      have hc : c1 * Real.exp (-c1) ≤ 1 := by
        have := Real.add_one_le_exp c1
        have h2 : Real.exp c1 * Real.exp (-c1) = 1 := by rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (-c1)]
      have e : Real.exp (-(c1 + 2)) = Real.exp (-c1) * Real.exp (-2) := by
        rw [← Real.exp_add]; congr 1; ring
      have h3 : Real.exp (-2) ≤ 1 / 7 := by
        rw [Real.exp_neg, ← one_div]
        exact one_div_le_one_div_of_le (by norm_num) he2
      rw [e, ← mul_assoc]
      calc c1 * Real.exp (-c1) * Real.exp (-2) ≤ 1 * Real.exp (-2) := by gcongr
        _ ≤ 1 / 7 := by linarith
    calc c1 * η = Real.exp (-p) * (c1 * Real.exp (-(c1 + 2))) := by rw [hη]; ring
      _ ≤ 1 * (1 / 7) := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by linarith)
      _ = 1 / 7 := one_mul _
  set y : ℝ := n * η with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ c1 * η * (1 + D) := by
    rw [hy]; calc n * η ≤ c1 * (1 + D) * η := by gcongr
      _ = _ := by ring
  have hy2 : y ≤ (1 + D) / 7 := hy1.trans (by nlinarith)
  have h1 : Real.exp y - 1 ≤ y * Real.exp y := by
    have := Real.add_one_le_exp (-y)
    have h2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos y]
  have h3 : y * Real.exp y ≤ c1 * η * (1 + D) * Real.exp ((1 + D) / 7) :=
    mul_le_mul hy1 (Real.exp_le_exp.mpr hy2) (Real.exp_pos _).le (by positivity)
  have h4 : 1 + D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have h5 : Real.exp (1 / 7) ≤ 3 := by
    have := Real.exp_one_lt_d9
    have h6 : Real.exp (1 / 7) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have e1 : Real.exp ((1 + D) / 7) = Real.exp (1 / 7) * Real.exp (D / 7) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (2 * D) = Real.exp D * Real.exp (D / 7) * Real.exp (6 * D / 7) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h7 : 1 ≤ Real.exp (6 * D / 7) := Real.one_le_exp (by positivity)
  have hc1η0 : 0 ≤ c1 * η := by positivity
  calc Real.exp y - 1 ≤ c1 * η * (1 + D) * Real.exp ((1 + D) / 7) := h1.trans h3
    _ ≤ c1 * Real.exp (-p) * Real.exp D * (3 * Real.exp (D / 7)) := by
        have hA : c1 * η * (1 + D) ≤ c1 * Real.exp (-p) * Real.exp D := by
          calc c1 * η * (1 + D) ≤ c1 * Real.exp (-p) * (1 + D) := by gcongr
            _ ≤ c1 * Real.exp (-p) * Real.exp D := by gcongr
        have hB : Real.exp ((1 + D) / 7) ≤ 3 * Real.exp (D / 7) := by
          rw [e1]; exact mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
        exact mul_le_mul hA hB (Real.exp_pos _).le (by positivity)
    _ = 3 * c1 * Real.exp (-p) * (Real.exp D * Real.exp (D / 7)) := by ring
    _ ≤ 3 * c1 * Real.exp (-p) * Real.exp (2 * D) := by
        rw [e2]
        have : 0 ≤ 3 * c1 * Real.exp (-p) := by positivity
        refine mul_le_mul_of_nonneg_left ?_ this
        have hh : 0 ≤ Real.exp D * Real.exp (D / 7) := by positivity
        nlinarith

end RealBound

section Family

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {cy : Yt → Finset B} {zs cr : Zt → Finset B} {β : Yt → ℂ} {τ : Zt → ℂ}
  {d : Finset B → ℝ} {B0 κ' κ'' c c2 p h : ℝ}

omit [Fintype B] [Fintype Yt] in
theorem norm_expm1_le (hB0 : 0 ≤ B0) (hκ'' : 0 ≤ κ'') (hd : ∀ Y, 0 ≤ d Y) (y : Yt)
    (hB : ‖β y‖ ≤ B0 * Real.exp (-κ'' * d (cy y))) :
    ‖Complex.exp (β y) - 1‖ ≤ B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y)) := by
  have hle : Real.exp (-κ'' * d (cy y)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [hd (cy y)])
  have hβ : ‖β y‖ ≤ B0 := hB.trans (by nlinarith [Real.exp_pos (-κ'' * d (cy y))])
  have h1 := Complex.norm_exp_sub_sum_le_norm_mul_exp (β y) 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, pow_one] at h1
  refine h1.trans ?_
  calc ‖β y‖ * Real.exp ‖β y‖ ≤ (B0 * Real.exp (-κ'' * d (cy y))) * Real.exp B0 := by
        gcongr
    _ = _ := by ring

variable (cy zs cr β τ d B0 κ' κ'' c c2 p h)

/-- The weight of a coupling after the factor `e^{κ' (d + c)}`. -/
def gasG (y : Yt) : ℝ :=
  B0 * Real.exp B0 * Real.exp (κ' * c) * Real.exp (-(κ'' - κ') * d (cy y))

/-- The weight of a heavy object after the factor `e^{κ' (c₂ + c) |Z|}`. -/
def gasAz (z : Zt) : ℝ := Real.exp (-p - (h - κ' * (c2 + c)) * (zs z).card)

variable {cy zs cr β τ d B0 κ' κ'' c c2 p h}

omit [Fintype B] [Fintype Yt] in
theorem gasG_nonneg (hB0 : 0 ≤ B0) (y : Yt) : 0 ≤ gasG cy d B0 κ' κ'' c y := by
  unfold gasG; positivity

omit [Fintype B] [Fintype Zt] in
theorem gasAz_nonneg (z : Zt) : 0 ≤ gasAz zs κ' c c2 p h z := (Real.exp_pos _).le

omit [Fintype Yt] [Fintype Zt] in
theorem sum_gasCs (C : Finset (Yt ⊕ Zt)) (F : Yt ⊕ Zt → ℝ) :
    ∑ t ∈ C, F t = ∑ y ∈ C.toLeft, F (Sum.inl y) + ∑ z ∈ C.toRight, F (Sum.inr z) := by
  conv_lhs => rw [← Finset.toLeft_disjSum_toRight (u := C)]
  rw [Finset.sum_disjSum]

omit [Fintype B] in
theorem gas_family_bound (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c)
    (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (zs z).Nonempty)
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hτ : ∀ z, ‖τ z‖ ≤ Real.exp (-p - h * (zs z).card))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → gasA cy zs cr C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    {X : Finset B} {C : Finset (Yt ⊕ Zt)}
    (hC : C ∈ Cfam (gasCs cy zs) (gasA cy zs cr) X) :
    Real.exp (κ' * d X) * ‖∏ t ∈ C, gasW β τ t‖ ≤
      (∏ y ∈ C.toLeft, gasG cy d B0 κ' κ'' c y) * ∏ z ∈ C.toRight, gasAz zs κ' c c2 p h z := by
  obtain ⟨hconn, hA, hU⟩ := mem_Cfam.mp hC
  have h3 := hG3 C hconn hA
  rw [hU, sum_gasCs] at h3
  have hcard : (C.card : ℝ) = C.toLeft.card + C.toRight.card := by
    rw [← Finset.card_toLeft_add_card_toRight (u := C)]; push_cast; ring
  rw [hcard] at h3
  have hc2 : ∀ z, d (zs z) + c ≤ (c2 + c) * (zs z).card := by
    intro z
    have h1 : (1 : ℝ) ≤ (zs z).card := by exact_mod_cast (hz z).card_pos
    have := hzd z
    nlinarith
  have hdX : d X ≤ ∑ y ∈ C.toLeft, (d (cy y) + c) +
      ∑ z ∈ C.toRight, (c2 + c) * (zs z).card := by
    have e1 : ∑ y ∈ C.toLeft, (d (cy y) + c) = ∑ y ∈ C.toLeft, d (cy y) + C.toLeft.card * c := by
      rw [Finset.sum_add_distrib]; simp
    have e2 : ∑ z ∈ C.toRight, d (zs z) ≤ ∑ z ∈ C.toRight, ((c2 + c) * (zs z).card - c) :=
      Finset.sum_le_sum (fun z _ => by linarith [hc2 z])
    have e3 : ∑ z ∈ C.toRight, ((c2 + c) * (zs z).card - c) =
        ∑ z ∈ C.toRight, (c2 + c) * (zs z).card - C.toRight.card * c := by
      rw [Finset.sum_sub_distrib]; simp
    simp only [gasCs_inl, gasCs_inr] at h3
    nlinarith
  have hexp : Real.exp (κ' * d X) ≤
      (∏ y ∈ C.toLeft, Real.exp (κ' * (d (cy y) + c))) *
        ∏ z ∈ C.toRight, Real.exp (κ' * ((c2 + c) * (zs z).card)) := by
    rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add, ← Finset.mul_sum, ← Finset.mul_sum,
      ← mul_add]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdX hκ')
  rw [prod_gasW, norm_mul, norm_prod, norm_prod]
  calc Real.exp (κ' * d X) * ((∏ y ∈ C.toLeft, ‖Complex.exp (β y) - 1‖) *
        ∏ z ∈ C.toRight, ‖τ z‖)
      ≤ ((∏ y ∈ C.toLeft, Real.exp (κ' * (d (cy y) + c))) *
        ∏ z ∈ C.toRight, Real.exp (κ' * ((c2 + c) * (zs z).card))) *
        ((∏ y ∈ C.toLeft, ‖Complex.exp (β y) - 1‖) * ∏ z ∈ C.toRight, ‖τ z‖) := by
        gcongr
    _ = (∏ y ∈ C.toLeft, (Real.exp (κ' * (d (cy y) + c)) * ‖Complex.exp (β y) - 1‖)) *
        ∏ z ∈ C.toRight, (Real.exp (κ' * ((c2 + c) * (zs z).card)) * ‖τ z‖) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]; ring
    _ ≤ _ := by
        refine mul_le_mul (Finset.prod_le_prod₀ (fun y _ => by positivity) (fun y _ => ?_))
          (Finset.prod_le_prod₀ (fun z _ => by positivity) (fun z _ => ?_))
          (Finset.prod_nonneg (fun z _ => by positivity))
          (Finset.prod_nonneg (fun y _ => gasG_nonneg hB0 y))
        · have := norm_expm1_le hB0 (hκ'.trans hκ'') hd y (hB y)
          unfold gasG
          calc Real.exp (κ' * (d (cy y) + c)) * ‖Complex.exp (β y) - 1‖
              ≤ Real.exp (κ' * (d (cy y) + c)) *
                (B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y))) := by gcongr
            _ = _ := by
              have : Real.exp (κ' * (d (cy y) + c)) * Real.exp (-κ'' * d (cy y)) =
                  Real.exp (κ' * c) * Real.exp (-(κ'' - κ') * d (cy y)) := by
                rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
              calc Real.exp (κ' * (d (cy y) + c)) * (B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y)))
                  = B0 * Real.exp B0 * (Real.exp (κ' * (d (cy y) + c)) *
                      Real.exp (-κ'' * d (cy y))) := by ring
                _ = _ := by rw [this]; ring
        · unfold gasAz
          calc Real.exp (κ' * ((c2 + c) * (zs z).card)) * ‖τ z‖
              ≤ Real.exp (κ' * ((c2 + c) * (zs z).card)) * Real.exp (-p - h * (zs z).card) := by
                gcongr; exact hτ z
            _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Family

section Cover

/-- A sum over a family of nonnegative terms is bounded by the sums over the members through each
block of a covering set of blocks. -/
theorem sum_le_sum_cover {ι B : Type*} [Fintype ι] (s : Finset ι) (cov : ι → Finset B)
    (W : Finset B) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (h : ∀ i ∈ s, ∃ b ∈ W, b ∈ cov i) :
    ∑ i ∈ s, f i ≤ ∑ b ∈ W, ∑ i ∈ Finset.univ.filter (fun i => b ∈ cov i), f i := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, ∑ b ∈ W, (if b ∈ cov i then f i else 0) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        obtain ⟨b, hbW, hb⟩ := h i hi
        calc f i = (if b ∈ cov i then f i else 0) := by
              rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
          _ ≤ _ := Finset.single_le_sum (f := fun b => (if b ∈ cov i then f i else 0))
            (fun _ _ => by split_ifs <;> simp [hf i]) hbW
    _ = ∑ b ∈ W, ∑ i ∈ s, (if b ∈ cov i then f i else 0) := Finset.sum_comm
    _ ≤ ∑ b ∈ W, ∑ i, (if b ∈ cov i then f i else 0) :=
        Finset.sum_le_sum (fun b _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => by split_ifs <;> simp [hf i]))
    _ = _ := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.sum_filter]

end Cover

section Sum

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {cy : Yt → Finset B} {zs cr : Zt → Finset B}

variable (cy cr) in
/-- The couplings meeting the core of the heavy objects `Γ`. -/
def gasYm (Γ : Finset Zt) : Finset Yt :=
  Finset.univ.filter (fun y => ¬ Disjoint (cy y) (Γ.biUnion cr))

variable (zs) in
/-- The heavy objects supported in `X`. -/
def gasZsub (X : Finset B) : Finset Zt := Finset.univ.filter (fun z => zs z ⊆ X)

omit [Fintype B] in
theorem sum_cfam_le (g : Yt → ℝ) (a : Zt → ℝ) (hg : ∀ y, 0 ≤ g y) (ha : ∀ z, 0 ≤ a z)
    (X : Finset B) :
    ∑ C ∈ Cfam (gasCs cy zs) (gasA cy zs cr) X, (∏ y ∈ C.toLeft, g y) * ∏ z ∈ C.toRight, a z ≤
      ∑ Γ ∈ ((gasZsub zs X).powerset).erase ∅,
        (∏ z ∈ Γ, a z) * ∏ y ∈ gasYm cy cr Γ, (1 + g y) := by
  set 𝒮 : Finset (Σ _ : Finset Zt, Finset Yt) :=
    (((gasZsub zs X).powerset).erase ∅).sigma (fun Γ => (gasYm cy cr Γ).powerset) with h𝒮
  set ψ : (Σ _ : Finset Zt, Finset Yt) → Finset (Yt ⊕ Zt) := fun x => x.2.disjSum x.1 with hψ
  have hsub : Cfam (gasCs cy zs) (gasA cy zs cr) X ⊆ 𝒮.image ψ := by
    intro C hC
    obtain ⟨hconn, hA, hU⟩ := mem_Cfam.mp hC
    rw [Finset.mem_image]
    refine ⟨⟨C.toRight, C.toLeft⟩, ?_, ?_⟩
    · rw [h𝒮, Finset.mem_sigma, Finset.mem_erase, Finset.mem_powerset, Finset.mem_powerset]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro hR0
        have hR : C.toRight = ∅ := hR0
        have hL : C.toLeft = ∅ := by
          refine Finset.eq_empty_of_forall_notMem (fun y hy => ?_)
          obtain ⟨z, hz, _⟩ := hA.2 y hy
          rw [hR] at hz; simp at hz
        have : C = ∅ := by
          rw [← Finset.toLeft_disjSum_toRight (u := C), hL, hR]; rfl
        exact Finset.not_nonempty_empty (this ▸ hconn.1)
      · intro z hz
        simp only [gasZsub, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hU]
        have := Finset.subset_biUnion_of_mem (gasCs cy zs) (Finset.mem_toRight.mp hz)
        simpa [unionCs] using this
      · intro y hy
        obtain ⟨z, hz, hnd⟩ := hA.2 y hy
        simp only [gasYm, Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun hd => hnd (Finset.disjoint_of_subset_right
          (Finset.subset_biUnion_of_mem cr hz) hd)
    · simp [hψ, Finset.toLeft_disjSum_toRight]
  have hinj : Set.InjOn ψ (𝒮 : Set _) := by
    rintro ⟨Γ, Dy⟩ _ ⟨Γ', Dy'⟩ _ hxy
    have h1 := congrArg Finset.toLeft hxy
    have h2 := congrArg Finset.toRight hxy
    simp only [hψ, Finset.toLeft_disjSum, Finset.toRight_disjSum] at h1 h2
    subst h1; subst h2; rfl
  calc ∑ C ∈ Cfam (gasCs cy zs) (gasA cy zs cr) X, (∏ y ∈ C.toLeft, g y) * ∏ z ∈ C.toRight, a z
      ≤ ∑ C ∈ 𝒮.image ψ, (∏ y ∈ C.toLeft, g y) * ∏ z ∈ C.toRight, a z :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun C _ _ =>
          mul_nonneg (Finset.prod_nonneg (fun y _ => hg y)) (Finset.prod_nonneg (fun z _ => ha z)))
    _ = ∑ x ∈ 𝒮, (∏ y ∈ x.2, g y) * ∏ z ∈ x.1, a z := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        simp [hψ]
    _ = ∑ Γ ∈ ((gasZsub zs X).powerset).erase ∅, ∑ Dy ∈ (gasYm cy cr Γ).powerset,
          (∏ y ∈ Dy, g y) * ∏ z ∈ Γ, a z := by
        rw [h𝒮, Finset.sum_sigma']
    _ = _ := by
        refine Finset.sum_congr rfl (fun Γ _ => ?_)
        rw [← Finset.sum_mul, ← Finset.prod_one_add, mul_comm]

end Sum

section Main

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {cy : Yt → Finset B} {zs cr : Zt → Finset B} {β : Yt → ℂ} {τ : Zt → ℂ}
  {d : Finset B → ℝ} {B0 κ' κ'' c c1 c2 p h : ℝ}

omit [Fintype B] [Fintype Zt] in
theorem gas_prod_le (hB0 : 0 ≤ B0) {K0' : ℝ} (hK0' : 0 ≤ K0') (hcr : ∀ z, cr z ⊆ zs z)
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y),
      Real.exp (-(κ'' - κ') * d (cy y)) ≤ K0') (Γ : Finset Zt) :
    ∏ y ∈ gasYm cy cr Γ, (1 + gasG cy d B0 κ' κ'' c y) ≤
      Real.exp (B0 * Real.exp B0 * Real.exp (κ' * c) * K0' * ∑ z ∈ Γ, ((zs z).card : ℝ)) := by
  refine (Real.prod_one_add_le_exp_sum _ (gasG_nonneg hB0)).trans (Real.exp_le_exp.mpr ?_)
  have hcov := sum_le_sum_cover (gasYm cy cr Γ) cy (Γ.biUnion cr) (gasG cy d B0 κ' κ'' c)
    (gasG_nonneg hB0) (fun y hy => by
      simp only [gasYm, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨b, hb1, hb2⟩ := Finset.not_disjoint_iff.mp hy
      exact ⟨b, hb2, hb1⟩)
  refine hcov.trans ?_
  have hCc : 0 ≤ B0 * Real.exp B0 * Real.exp (κ' * c) * K0' := by positivity
  have hin : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y), gasG cy d B0 κ' κ'' c y ≤
      B0 * Real.exp B0 * Real.exp (κ' * c) * K0' := by
    intro b
    unfold gasG
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hent b) (by positivity)
  calc ∑ b ∈ Γ.biUnion cr, ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y), gasG cy d B0 κ' κ'' c y
      ≤ ∑ b ∈ Γ.biUnion cr, B0 * Real.exp B0 * Real.exp (κ' * c) * K0' :=
        Finset.sum_le_sum (fun b _ => hin b)
    _ = ((Γ.biUnion cr).card : ℝ) * (B0 * Real.exp B0 * Real.exp (κ' * c) * K0') := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∑ z ∈ Γ, ((zs z).card : ℝ)) * (B0 * Real.exp B0 * Real.exp (κ' * c) * K0') := by
        refine mul_le_mul_of_nonneg_right ?_ hCc
        have h1 : (Γ.biUnion cr).card ≤ ∑ z ∈ Γ, (cr z).card := Finset.card_biUnion_le
        have h2 : ∑ z ∈ Γ, (cr z).card ≤ ∑ z ∈ Γ, (zs z).card :=
          Finset.sum_le_sum (fun z _ => Finset.card_le_card (hcr z))
        exact_mod_cast h1.trans h2
    _ = _ := by ring

/-- **GAS (activity bound)**.  The activities of the polymer gas of `gas_eq` satisfy
`|K(X)| ≤ 3 c₁ e^{-p} e^{-(κ' - 2) d(X)}` for the polymers with `|X| ≤ c₁ (1 + d(X))`, provided the
volume decay `h` of the heavy weights is at least
`C + κ'(c₂ + c) + c₁ + 3 + ln K₀''`, where `C = B₀ e^{B₀} e^{κ' c} K₀'`. -/
theorem gas_activity_bound (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c)
    (hc1 : 0 ≤ c1) (hp : 0 ≤ p) (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (zs z).Nonempty)
    (hcr : ∀ z, cr z ⊆ zs z)
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hτ : ∀ z, ‖τ z‖ ≤ Real.exp (-p - h * (zs z).card))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → gasA cy zs cr C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    {K0' K0'' : ℝ} (hK0' : 0 ≤ K0')
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y),
      Real.exp (-(κ'' - κ') * d (cy y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤ K0'' ^ v)
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' + κ' * (c2 + c) + c1 + 3 + Real.log K0'' ≤ h)
    (X : NePoly B) (hG1 : (X.1.card : ℝ) ≤ c1 * (1 + d X.1)) :
    ‖gasK cy zs cr β τ X‖ ≤ 3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X.1) := by
  set Cc : ℝ := B0 * Real.exp B0 * Real.exp (κ' * c) * K0' with hCc
  set lam : ℝ := h - κ' * (c2 + c) - Cc with hlam
  have hlam' : c1 + 3 + Real.log K0'' ≤ lam := by rw [hlam]; linarith
  have hCc0 : 0 ≤ Cc := by positivity
  set ζ : Zt → ℝ := fun z => Real.exp (-p) * Real.exp (-lam * (zs z).card) with hζ
  have hζ0 : ∀ z, 0 ≤ ζ z := fun z => by positivity
  -- the family bound
  have hfam : ∀ C ∈ Cfam (gasCs cy zs) (gasA cy zs cr) X.1,
      Real.exp (κ' * d X.1) * ‖∏ t ∈ C, gasW β τ t‖ ≤
        (∏ y ∈ C.toLeft, gasG cy d B0 κ' κ'' c y) * ∏ z ∈ C.toRight, gasAz zs κ' c c2 p h z :=
    fun C hC => gas_family_bound hB0 hκ' hκ'' hc hd hz hB hτ hzd hG3 hC
  have h1 : Real.exp (κ' * d X.1) * ‖gasK cy zs cr β τ X‖ ≤
      ∑ C ∈ Cfam (gasCs cy zs) (gasA cy zs cr) X.1,
        (∏ y ∈ C.toLeft, gasG cy d B0 κ' κ'' c y) * ∏ z ∈ C.toRight, gasAz zs κ' c c2 p h z := by
    unfold gasK polyAct
    calc Real.exp (κ' * d X.1) * ‖∑ C ∈ Cfam (gasCs cy zs) (gasA cy zs cr) X.1,
          ∏ t ∈ C, gasW β τ t‖
        ≤ Real.exp (κ' * d X.1) * ∑ C ∈ Cfam (gasCs cy zs) (gasA cy zs cr) X.1,
          ‖∏ t ∈ C, gasW β τ t‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.exp_pos _).le
      _ = ∑ C ∈ Cfam (gasCs cy zs) (gasA cy zs cr) X.1,
          Real.exp (κ' * d X.1) * ‖∏ t ∈ C, gasW β τ t‖ := by rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum hfam
  have h2 := sum_cfam_le (cy := cy) (zs := zs) (cr := cr) (gasG cy d B0 κ' κ'' c)
    (gasAz zs κ' c c2 p h) (gasG_nonneg hB0) gasAz_nonneg X.1
  have h3 : ∀ Γ ∈ ((gasZsub zs X.1).powerset).erase ∅,
      (∏ z ∈ Γ, gasAz zs κ' c c2 p h z) * ∏ y ∈ gasYm cy cr Γ, (1 + gasG cy d B0 κ' κ'' c y) ≤
        ∏ z ∈ Γ, ζ z := by
    intro Γ _
    calc _ ≤ (∏ z ∈ Γ, gasAz zs κ' c c2 p h z) * Real.exp (Cc * ∑ z ∈ Γ, ((zs z).card : ℝ)) :=
          mul_le_mul_of_nonneg_left (gas_prod_le hB0 hK0' hcr hent Γ)
            (Finset.prod_nonneg (fun z _ => gasAz_nonneg z))
      _ = ∏ z ∈ Γ, (gasAz zs κ' c c2 p h z * Real.exp (Cc * (zs z).card)) := by
          rw [Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]
      _ = ∏ z ∈ Γ, ζ z := by
          refine Finset.prod_congr rfl (fun z _ => ?_)
          simp only [gasAz, hζ, hlam]
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h4 := (Finset.sum_le_sum h3).trans (sum_powerset_erase_le ζ hζ0 (gasZsub zs X.1))
  have h5 : ∑ z ∈ gasZsub zs X.1, ζ z ≤ X.1.card * (Real.exp (-p) * Real.exp (-(c1 + 2))) := by
    refine (sum_le_sum_cover (gasZsub zs X.1) zs X.1 ζ hζ0 (fun z hz' => ?_)).trans ?_
    · obtain ⟨b, hb⟩ := hz z
      simp only [gasZsub, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
      exact ⟨b, hz' hb, hb⟩
    · calc ∑ b ∈ X.1, ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z), ζ z
          ≤ ∑ b ∈ X.1, Real.exp (-p) * Real.exp (-(c1 + 2)) := by
            refine Finset.sum_le_sum (fun b _ => ?_)
            rw [hζ, ← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left
              (heavy_entropy hc1 hK1 hz hcount hlam' b) (Real.exp_pos _).le
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have h6 := gas_real_bound (p := p) (c1 := c1) (D := d X.1) (n := (X.1.card : ℝ)) hp hc1 (hd _)
    (Nat.cast_nonneg _) hG1
  have h7 : Real.exp (κ' * d X.1) * ‖gasK cy zs cr β τ X‖ ≤
      3 * c1 * Real.exp (-p) * Real.exp (2 * d X.1) := by
    refine h1.trans (h2.trans (h4.trans ?_))
    have := Real.exp_le_exp.mpr h5
    linarith
  have h8 : ‖gasK cy zs cr β τ X‖ ≤
      Real.exp (-κ' * d X.1) * (3 * c1 * Real.exp (-p) * Real.exp (2 * d X.1)) := by
    have hpos : 0 < Real.exp (κ' * d X.1) := Real.exp_pos _
    have e : Real.exp (-κ' * d X.1) * Real.exp (κ' * d X.1) = 1 := by
      rw [← Real.exp_add]; simp
    calc ‖gasK cy zs cr β τ X‖ = Real.exp (-κ' * d X.1) *
          (Real.exp (κ' * d X.1) * ‖gasK cy zs cr β τ X‖) := by
          rw [← mul_assoc, e, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h7 (Real.exp_pos _).le
  refine h8.trans (le_of_eq ?_)
  have : Real.exp (-κ' * d X.1) * Real.exp (2 * d X.1) = Real.exp (-(κ' - 2) * d X.1) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← this]; ring

end Main

end Balaban.Polymer
