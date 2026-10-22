module

public import Balaban.Polymer.Gas

/-!
# The activity bound in GAS

With `|β Y| ≤ B₀ e^{-κ'' d(Y)}`, `|τ Z| ≤ e^{-p - h |Z|}` and the entropy bounds, every polymer
`X` with `|X| ≤ c₁ (1 + d(X))` has `|K(X)| ≤ 3 c₁ e^{-p} e^{-(κ' - 2) d(X)}`
(`gas_activity_bound`; POLYMER.md §2.6, §3.9 with the corrected constants: the threshold for the
volume decay `h` is `C + κ'(c₂ + c) + c₁ + 3 + ln K₀''`).

The statements are instances of the bound for the general activation rules of `Gas.lean`
(`actGasK_activity_bound`), with the summed counts `∑_{Z ∋ b, |Z| = v} a(Z) ≤ K₀''^v e^{-p - h v}`
of heavy majorants and the entropy of the couplings active for each compatible family:

* `heavy_entropy_weighted`: the heavy entropy from weighted counts (`heavy_entropy` for `ω = 1`);
* `exp_le_prod_of_mem_cfam`, `exp_mul_prod_le_of_mem_cfam`: the size of a connected admissible
  family distributed over its members (`gas_family_bound`);
* `sum_cfam_actGas_le`, `prod_actGas_le`, `cfam_actGas_majorant_le`: the combinatorial part
  (`sum_cfam_le`, `gas_prod_le`);
* `sum_cfam_actGas_le_of_counts`, `actGasK_activity_bound` (`gas_activity_bound`).

The cores measure the heavy objects by a size `σ Z ≥ 1` (for instance the number of cubes of a
record) instead of `|Z|`, and separate three sets of a heavy object: its dependence set `zs Z`
(compatibility), the set `att Z` the couplings it activates meet (`|att Z| ≤ σ Z`), and the
anchor set `anc Z ⊆ zs Z` of its counts `∑_{Z : b ∈ anc Z, σ Z = v} a(Z) ≤ M₀ K₀''^v e^{-p - h v}`;
the entropy margin `c'` of the rate `h` is independent of the ratio `c₁` of (G1), which enters only
through `c₁ M₀ e^{-p} e^{-(c' + 2)} ≤ 1/7`:

* `heavy_entropy_sized`, `exp_le_prod_of_mem_cfam_sized`, `exp_mul_prod_le_of_mem_cfam_sized`,
  `prod_actGas_le_att`, `cfam_actGas_majorant_le_gen`, `gas_real_bound_gen`,
  `sum_cfam_actGas_le_of_counts_sized`, `actGasK_activity_bound_sized`; the statements above are
  their instances `σ = |·|`, `att = anc = zs`, `M₀ = 1`, `c' = c₁`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

section Entropy

variable {B Zt : Type*} [Fintype B] [Fintype Zt] {zs : Zt → Finset B}

omit [Fintype B] in
/-- **Heavy entropy from weighted counts, for a general size and anchor** (the core).  Let every
heavy object have a size `σ Z ≥ 1` and an anchor set `anc Z` of blocks.  If the weights `ω Z` of the
heavy objects anchored at a block with size `v` sum to at most `M₀ K₀^v`, then
`∑_{Z : b ∈ anc Z} ω Z e^{-λ σ Z} ≤ M₀ e^{-(c₁+2)}` for `λ ≥ c₁ + 3 + ln K₀`. -/
theorem heavy_entropy_sized {K0 M0 c1 lam : ℝ} (hc1 : 0 ≤ c1) (hK0 : 1 ≤ K0) (hM0 : 0 ≤ M0)
    (σ : Zt → ℕ) (hσ : ∀ z, 1 ≤ σ z) (anc : Zt → Finset B) (ω : Zt → ℝ)
    (hcount : ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ anc z ∧ σ z = v), ω z ≤ M0 * K0 ^ v)
    (hlam : c1 + 3 + Real.log K0 ≤ lam) (b : B) :
    ∑ z ∈ Finset.univ.filter (fun z => b ∈ anc z), ω z * Real.exp (-lam * σ z) ≤
      M0 * Real.exp (-(c1 + 2)) := by
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
      have := Real.add_one_le_exp (3 : ℝ)
      linarith
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h3
  have hx12 : x ≤ 1 / 2 :=
    hx1.trans ((Real.exp_le_exp.mpr (by linarith : -(c1 + 3) ≤ -3)).trans he3)
  set Nσ : ℕ := Finset.univ.sup σ with hNσ
  have hg : ∀ z ∈ Finset.univ.filter (fun z => b ∈ anc z), σ z - 1 ∈ Finset.range Nσ := by
    intro z _
    rw [Finset.mem_range]
    have h1 : σ z ≤ Nσ := Finset.le_sup (f := σ) (Finset.mem_univ z)
    have h2 := hσ z
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hg]
  have hinner : ∀ j ∈ Finset.range Nσ,
      ∑ z ∈ (Finset.univ.filter (fun z => b ∈ anc z)).filter (fun z => σ z - 1 = j),
        ω z * Real.exp (-lam * σ z) ≤ M0 * x ^ (j + 1) := by
    intro j _
    have hset : (Finset.univ.filter (fun z => b ∈ anc z)).filter (fun z => σ z - 1 = j) =
        Finset.univ.filter (fun z => b ∈ anc z ∧ σ z = j + 1) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := hσ z
      constructor
      · rintro ⟨hb, hj⟩
        exact ⟨hb, by omega⟩
      · rintro ⟨hb, hj⟩
        exact ⟨hb, by omega⟩
    rw [hset]
    have : ∀ z ∈ Finset.univ.filter (fun z => b ∈ anc z ∧ σ z = j + 1),
        ω z * Real.exp (-lam * σ z) = ω z * Real.exp (-lam) ^ (j + 1) := by
      intro z hzz
      rw [Finset.mem_filter] at hzz
      rw [hzz.2.2, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, hx, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hcount b (j + 1)) (by positivity)
  refine (Finset.sum_le_sum hinner).trans ?_
  have hgeo : ∑ j ∈ Finset.range Nσ, x ^ j ≤ (1 - x)⁻¹ :=
    sum_le_hasSum _ (fun i _ => by positivity) (hasSum_geometric_of_lt_one hx0 (by linarith))
  have hsum : ∑ j ∈ Finset.range Nσ, x ^ (j + 1) ≤ Real.exp (-(c1 + 2)) := by
    calc ∑ j ∈ Finset.range Nσ, x ^ (j + 1)
        = x * ∑ j ∈ Finset.range Nσ, x ^ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ x * (1 - x)⁻¹ := mul_le_mul_of_nonneg_left hgeo hx0
      _ ≤ x * 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hx0
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
      _ ≤ 2 * Real.exp (-(c1 + 3)) := by linarith
      _ ≤ Real.exp (-(c1 + 2)) := by
          have h1 : Real.exp (-(c1 + 2)) = Real.exp 1 * Real.exp (-(c1 + 3)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [h1]
          have := Real.exp_one_gt_d9
          have hp := Real.exp_pos (-(c1 + 3))
          nlinarith
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hsum hM0

omit [Fintype B] in
/-- **Heavy entropy from weighted counts.**  If the weights `ω Z` of the heavy objects through
a block with `v` blocks sum to at most `K₀^v`, then `∑_{Z ∋ b} ω Z e^{-λ |Z|} ≤ e^{-(c₁+2)}` for
`λ ≥ c₁ + 3 + ln K₀` (`heavy_entropy` is the case `ω = 1`; the instance of `heavy_entropy_sized`
with the size `|Z|`, the anchor `Z` and `M₀ = 1`). -/
theorem heavy_entropy_weighted {K0 c1 lam : ℝ} (hc1 : 0 ≤ c1) (hK0 : 1 ≤ K0)
    (hz : ∀ z, (zs z).Nonempty) (ω : Zt → ℝ)
    (hcount : ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v), ω z ≤ K0 ^ v)
    (hlam : c1 + 3 + Real.log K0 ≤ lam) (b : B) :
    ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z), ω z * Real.exp (-lam * (zs z).card) ≤
      Real.exp (-(c1 + 2)) := by
  simpa using heavy_entropy_sized hc1 hK0 zero_le_one (fun z => (zs z).card)
    (fun z => (hz z).card_pos) zs ω (fun b v => by simpa using hcount b v) hlam b

omit [Fintype B] in
/-- The entropy sum of the heavy objects through a block. -/
theorem heavy_entropy {K0 c1 lam : ℝ} (hc1 : 0 ≤ c1) (hK0 : 1 ≤ K0)
    (hz : ∀ z, (zs z).Nonempty)
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤ K0 ^ v)
    (hlam : c1 + 3 + Real.log K0 ≤ lam) (b : B) :
    ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z), Real.exp (-lam * (zs z).card) ≤
      Real.exp (-(c1 + 2)) := by
  simpa using heavy_entropy_weighted hc1 hK0 hz (fun _ => (1 : ℝ))
    (fun b v => by simpa using hcount b v) hlam b

end Entropy

section RealBound

/-- **The real-variable inequality closing the proof of GAS, for a general entropy `η`** (the
core): for `n ≤ c₁ (1 + D)` and `c₁ η ≤ 1/7`, `e^{n η} - 1 ≤ 3 c₁ η e^{2D}`. -/
theorem gas_real_bound_gen {η c1 D n : ℝ} (hη0 : 0 ≤ η) (hc1η : c1 * η ≤ 1 / 7)
    (hc1 : 0 ≤ c1) (hD : 0 ≤ D) (hn : 0 ≤ n) (hG1 : n ≤ c1 * (1 + D)) :
    Real.exp (n * η) - 1 ≤ 3 * (c1 * η) * Real.exp (2 * D) := by
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
    _ ≤ c1 * η * Real.exp D * (3 * Real.exp (D / 7)) := by
        have hA : c1 * η * (1 + D) ≤ c1 * η * Real.exp D :=
          mul_le_mul_of_nonneg_left h4 hc1η0
        have hB : Real.exp ((1 + D) / 7) ≤ 3 * Real.exp (D / 7) := by
          rw [e1]; exact mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
        exact mul_le_mul hA hB (Real.exp_pos _).le (by positivity)
    _ = 3 * (c1 * η) * (Real.exp D * Real.exp (D / 7)) := by ring
    _ ≤ 3 * (c1 * η) * Real.exp (2 * D) := by
        rw [e2]
        have : 0 ≤ 3 * (c1 * η) := by positivity
        refine mul_le_mul_of_nonneg_left ?_ this
        have hh : 0 ≤ Real.exp D * Real.exp (D / 7) := by positivity
        nlinarith

/-- `c₁ e^{-p} e^{-(c₁+2)} ≤ 1/7` for `p, c₁ ≥ 0`. -/
theorem mul_exp_neg_le_seventh {p c1 : ℝ} (hp : 0 ≤ p) (hc1 : 0 ≤ c1) :
    c1 * (Real.exp (-p) * Real.exp (-(c1 + 2))) ≤ 1 / 7 := by
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have h1 := Real.exp_one_gt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith
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
  calc c1 * (Real.exp (-p) * Real.exp (-(c1 + 2))) =
        Real.exp (-p) * (c1 * Real.exp (-(c1 + 2))) := by ring
    _ ≤ 1 * (1 / 7) := by
        gcongr
        exact Real.exp_le_one_iff.mpr (by linarith)
    _ = 1 / 7 := one_mul _

/-- The real-variable inequality closing the proof of GAS (the instance of `gas_real_bound_gen`
with `η = e^{-p} e^{-(c₁+2)}`). -/
theorem gas_real_bound {p c1 D n : ℝ} (hp : 0 ≤ p) (hc1 : 0 ≤ c1) (hD : 0 ≤ D) (hn : 0 ≤ n)
    (hG1 : n ≤ c1 * (1 + D)) :
    Real.exp (n * (Real.exp (-p) * Real.exp (-(c1 + 2)))) - 1 ≤
      3 * c1 * Real.exp (-p) * Real.exp (2 * D) := by
  have h := gas_real_bound_gen (by positivity) (mul_exp_neg_le_seventh hp hc1) hc1 hD hn hG1
  refine h.trans ?_
  have hη : Real.exp (-p) * Real.exp (-(c1 + 2)) ≤ Real.exp (-p) := by
    calc _ ≤ Real.exp (-p) * 1 := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by linarith)
      _ = _ := mul_one _
  have h2 : 3 * (c1 * (Real.exp (-p) * Real.exp (-(c1 + 2)))) ≤ 3 * c1 * Real.exp (-p) := by
    nlinarith
  exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

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

end Family

section ActFamily

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {act : Yt → Finset Zt → Prop} {cy : Yt → Finset B} {zs : Zt → Finset B}

omit [Fintype B] in
/-- **The size of a connected admissible family distributed over its members, for a general size
of the heavy objects** (the core).  If the size `d` is subadditive over connected admissible
families up to `c` per member and `d(Z) ≤ c₂ σ Z` with `σ Z ≥ 1`, then
`e^{κ' d(X)} ≤ ∏_Y e^{κ' (d(Y) + c)} ∏_Z e^{κ' (c₂ + c) σ Z}` for a family with union `X`. -/
theorem exp_le_prod_of_mem_cfam_sized {A : Finset (Yt ⊕ Zt) → Prop} {d : Finset B → ℝ}
    {κ' c c2 : ℝ} (hκ' : 0 ≤ κ') (hc : 0 ≤ c) (σ : Zt → ℝ) (hσ : ∀ z, 1 ≤ σ z)
    (hzd : ∀ z, d (zs z) ≤ c2 * σ z)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → A C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    {X : Finset B} {C : Finset (Yt ⊕ Zt)} (hC : C ∈ Cfam (gasCs cy zs) A X) :
    Real.exp (κ' * d X) ≤
      (∏ y ∈ C.toLeft, Real.exp (κ' * (d (cy y) + c))) *
        ∏ z ∈ C.toRight, Real.exp (κ' * ((c2 + c) * σ z)) := by
  obtain ⟨hconn, hA, hU⟩ := mem_Cfam.mp hC
  have h3 := hG3 C hconn hA
  rw [hU, sum_gasCs] at h3
  have hcard : (C.card : ℝ) = C.toLeft.card + C.toRight.card := by
    rw [← Finset.card_toLeft_add_card_toRight (u := C)]
    push_cast
    ring
  rw [hcard] at h3
  have hc2 : ∀ z, d (zs z) + c ≤ (c2 + c) * σ z := by
    intro z
    have h1 := hσ z
    have := hzd z
    nlinarith
  have hdX : d X ≤ ∑ y ∈ C.toLeft, (d (cy y) + c) +
      ∑ z ∈ C.toRight, (c2 + c) * σ z := by
    have e1 : ∑ y ∈ C.toLeft, (d (cy y) + c) = ∑ y ∈ C.toLeft, d (cy y) + C.toLeft.card * c := by
      rw [Finset.sum_add_distrib]
      simp
    have e2 : ∑ z ∈ C.toRight, d (zs z) ≤ ∑ z ∈ C.toRight, ((c2 + c) * σ z - c) :=
      Finset.sum_le_sum (fun z _ => by linarith [hc2 z])
    have e3 : ∑ z ∈ C.toRight, ((c2 + c) * σ z - c) =
        ∑ z ∈ C.toRight, (c2 + c) * σ z - C.toRight.card * c := by
      rw [Finset.sum_sub_distrib]
      simp
    simp only [gasCs_inl, gasCs_inr] at h3
    nlinarith
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add, ← Finset.mul_sum, ← Finset.mul_sum,
    ← mul_add]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdX hκ')

omit [Fintype B] in
/-- **The size of a connected admissible family distributed over its members.**  If the size `d`
is subadditive over connected admissible families up to `c` per member and `d(Z) ≤ c₂ |Z|`, then
`e^{κ' d(X)} ≤ ∏_Y e^{κ' (d(Y) + c)} ∏_Z e^{κ' (c₂ + c) |Z|}` for a family with union `X`. -/
theorem exp_le_prod_of_mem_cfam {A : Finset (Yt ⊕ Zt) → Prop} {d : Finset B → ℝ}
    {κ' c c2 : ℝ} (hκ' : 0 ≤ κ') (hc : 0 ≤ c) (hz : ∀ z, (zs z).Nonempty)
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → A C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    {X : Finset B} {C : Finset (Yt ⊕ Zt)} (hC : C ∈ Cfam (gasCs cy zs) A X) :
    Real.exp (κ' * d X) ≤
      (∏ y ∈ C.toLeft, Real.exp (κ' * (d (cy y) + c))) *
        ∏ z ∈ C.toRight, Real.exp (κ' * ((c2 + c) * (zs z).card)) :=
  exp_le_prod_of_mem_cfam_sized hκ' hc (fun z => ((zs z).card : ℝ))
    (fun z => by exact_mod_cast (hz z).card_pos) hzd hG3 hC

omit [Fintype B] in
/-- **The size distributed over the members of a family, with the coupling majorants, for a
general size of the heavy objects** (the core):
`e^{κ' d(X)} ∏_Y B₀ e^{B₀} e^{-κ'' d(Y)} ∏_Z a(Z) ≤ ∏_Y gasG(Y) ∏_Z e^{κ' (c₂ + c) σ Z} a(Z)`. -/
theorem exp_mul_prod_le_of_mem_cfam_sized {A : Finset (Yt ⊕ Zt) → Prop} {d : Finset B → ℝ}
    {B0 κ' κ'' c c2 : ℝ} (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hc : 0 ≤ c) (σ : Zt → ℝ)
    (hσ : ∀ z, 1 ≤ σ z) (hzd : ∀ z, d (zs z) ≤ c2 * σ z)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → A C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    {a : Zt → ℝ} (ha : ∀ z, 0 ≤ a z) {X : Finset B} {C : Finset (Yt ⊕ Zt)}
    (hC : C ∈ Cfam (gasCs cy zs) A X) :
    Real.exp (κ' * d X) *
        ((∏ y ∈ C.toLeft, B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y))) *
          ∏ z ∈ C.toRight, a z) ≤
      (∏ y ∈ C.toLeft, gasG cy d B0 κ' κ'' c y) *
        ∏ z ∈ C.toRight, (Real.exp (κ' * ((c2 + c) * σ z)) * a z) := by
  have hgas : ∀ y, B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y)) *
      Real.exp (κ' * (d (cy y) + c)) = gasG cy d B0 κ' κ'' c y := by
    intro y
    simp only [gasG]
    have : Real.exp (-κ'' * d (cy y)) * Real.exp (κ' * (d (cy y) + c)) =
        Real.exp (κ' * c) * Real.exp (-(κ'' - κ') * d (cy y)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y)) * Real.exp (κ' * (d (cy y) + c))
        = B0 * Real.exp B0 * (Real.exp (-κ'' * d (cy y)) * Real.exp (κ' * (d (cy y) + c))) := by
          ring
      _ = _ := by rw [this]; ring
  have h1 := exp_le_prod_of_mem_cfam_sized hκ' hc σ hσ hzd hG3 hC
  calc Real.exp (κ' * d X) *
        ((∏ y ∈ C.toLeft, B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y))) *
          ∏ z ∈ C.toRight, a z)
      ≤ ((∏ y ∈ C.toLeft, Real.exp (κ' * (d (cy y) + c))) *
          ∏ z ∈ C.toRight, Real.exp (κ' * ((c2 + c) * σ z))) *
        ((∏ y ∈ C.toLeft, B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y))) *
          ∏ z ∈ C.toRight, a z) :=
        mul_le_mul_of_nonneg_right h1
          (mul_nonneg (Finset.prod_nonneg (fun y _ => by positivity))
            (Finset.prod_nonneg (fun z _ => ha z)))
    _ = (∏ y ∈ C.toLeft, (B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y)) *
          Real.exp (κ' * (d (cy y) + c)))) *
          ∏ z ∈ C.toRight, (Real.exp (κ' * ((c2 + c) * σ z)) * a z) := by
        simp only [Finset.prod_mul_distrib]
        ring
    _ = _ := by simp only [hgas]

omit [Fintype B] in
/-- **The size distributed over the members of a family, with the coupling majorants**:
`e^{κ' d(X)} ∏_Y B₀ e^{B₀} e^{-κ'' d(Y)} ∏_Z a(Z) ≤ ∏_Y gasG(Y) ∏_Z e^{κ' (c₂ + c) |Z|} a(Z)` for a
connected admissible family with union `X`. -/
theorem exp_mul_prod_le_of_mem_cfam {A : Finset (Yt ⊕ Zt) → Prop} {d : Finset B → ℝ}
    {B0 κ' κ'' c c2 : ℝ} (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hc : 0 ≤ c) (hz : ∀ z, (zs z).Nonempty)
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → A C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    {a : Zt → ℝ} (ha : ∀ z, 0 ≤ a z) {X : Finset B} {C : Finset (Yt ⊕ Zt)}
    (hC : C ∈ Cfam (gasCs cy zs) A X) :
    Real.exp (κ' * d X) *
        ((∏ y ∈ C.toLeft, B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y))) *
          ∏ z ∈ C.toRight, a z) ≤
      (∏ y ∈ C.toLeft, gasG cy d B0 κ' κ'' c y) *
        ∏ z ∈ C.toRight, (Real.exp (κ' * ((c2 + c) * (zs z).card)) * a z) :=
  exp_mul_prod_le_of_mem_cfam_sized hB0 hκ' hc (fun z => ((zs z).card : ℝ))
    (fun z => by exact_mod_cast (hz z).card_pos) hzd hG3 ha hC

end ActFamily

section FamilyBound

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {cy : Yt → Finset B} {zs cr : Zt → Finset B} {β : Yt → ℂ} {τ : Zt → ℂ}
  {d : Finset B → ℝ} {B0 κ' κ'' c c2 p h : ℝ}

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
  have h1 : ‖∏ t ∈ C, gasW β τ t‖ ≤
      (∏ y ∈ C.toLeft, B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y))) *
        ∏ z ∈ C.toRight, Real.exp (-p - h * (zs z).card) := by
    rw [prod_gasW, norm_mul, norm_prod, norm_prod]
    exact mul_le_mul (Finset.prod_le_prod₀ (fun y _ => norm_nonneg _)
        (fun y _ => norm_expm1_le hB0 (hκ'.trans hκ'') hd y (hB y)))
      (Finset.prod_le_prod₀ (fun z _ => norm_nonneg _) (fun z _ => hτ z))
      (Finset.prod_nonneg (fun z _ => norm_nonneg _))
      (Finset.prod_nonneg (fun y _ => by positivity))
  refine (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le).trans ?_
  refine (exp_mul_prod_le_of_mem_cfam hB0 hκ' hc hz hzd hG3 (fun _ => (Real.exp_pos _).le)
    hC).trans_eq ?_
  congr 1
  refine Finset.prod_congr rfl (fun z _ => ?_)
  unfold gasAz
  rw [← Real.exp_add]
  congr 1
  ring

end FamilyBound

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

end Sum

section ActSum

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {act : Yt → Finset Zt → Prop} {cy : Yt → Finset B} {zs : Zt → Finset B}

omit [Fintype B] in
/-- The sum over the connected admissible families with union `X` of products of nonnegative
majorants is at most the sum over the nonempty compatible families `Γ` of heavy objects inside `X`
of `∏_Γ a` times the product of `1 + g` over the couplings active for `Γ`. -/
theorem sum_cfam_actGas_le (hne : ∀ y Γ, act y Γ → Γ.Nonempty)
    (g : Yt → ℝ) (a : Zt → ℝ) (hg : ∀ y, 0 ≤ g y) (ha : ∀ z, 0 ≤ a z) (X : Finset B) :
    ∑ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X, (∏ y ∈ C.toLeft, g y) * ∏ z ∈ C.toRight, a z ≤
      ∑ Γ ∈ (((gasZsub zs X).powerset).erase ∅).filter
          (fun Γ => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')),
        (∏ z ∈ Γ, a z) * ∏ y ∈ Finset.univ.filter (fun y => act y Γ), (1 + g y) := by
  set 𝒮 : Finset (Σ _ : Finset Zt, Finset Yt) :=
    ((((gasZsub zs X).powerset).erase ∅).filter
      (fun Γ => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z'))).sigma
      (fun Γ => (Finset.univ.filter (fun y => act y Γ)).powerset) with h𝒮
  set ψ : (Σ _ : Finset Zt, Finset Yt) → Finset (Yt ⊕ Zt) := fun x => x.2.disjSum x.1 with hψ
  have hsub : Cfam (gasCs cy zs) (actGasA act zs) X ⊆ 𝒮.image ψ := by
    intro C hC
    obtain ⟨hconn, hA, hU⟩ := mem_Cfam.mp hC
    rw [Finset.mem_image]
    refine ⟨⟨C.toRight, C.toLeft⟩, ?_, ?_⟩
    · rw [h𝒮, Finset.mem_sigma, Finset.mem_filter, Finset.mem_erase, Finset.mem_powerset,
        Finset.mem_powerset]
      refine ⟨⟨⟨?_, ?_⟩, hA.1⟩, ?_⟩
      · intro hR0
        have hR : C.toRight = ∅ := hR0
        have hL : C.toLeft = ∅ := by
          refine Finset.eq_empty_of_forall_notMem (fun y hy => ?_)
          obtain ⟨z, hz⟩ := hne y _ (hA.2 y hy)
          rw [hR] at hz
          simp at hz
        have : C = ∅ := by
          rw [← Finset.toLeft_disjSum_toRight (u := C), hL, hR]
          rfl
        exact Finset.not_nonempty_empty (this ▸ hconn.1)
      · intro z hz
        simp only [gasZsub, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hU]
        have := Finset.subset_biUnion_of_mem (gasCs cy zs) (Finset.mem_toRight.mp hz)
        simpa [unionCs] using this
      · intro y hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA.2 y hy⟩
    · simp [hψ, Finset.toLeft_disjSum_toRight]
  have hinj : Set.InjOn ψ (𝒮 : Set _) := by
    rintro ⟨Γ, Dy⟩ _ ⟨Γ', Dy'⟩ _ hxy
    have h1 := congrArg Finset.toLeft hxy
    have h2 := congrArg Finset.toRight hxy
    simp only [hψ, Finset.toLeft_disjSum, Finset.toRight_disjSum] at h1 h2
    subst h1
    subst h2
    rfl
  calc ∑ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X, (∏ y ∈ C.toLeft, g y) * ∏ z ∈ C.toRight, a z
      ≤ ∑ C ∈ 𝒮.image ψ, (∏ y ∈ C.toLeft, g y) * ∏ z ∈ C.toRight, a z :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun C _ _ =>
          mul_nonneg (Finset.prod_nonneg (fun y _ => hg y)) (Finset.prod_nonneg (fun z _ => ha z)))
    _ = ∑ x ∈ 𝒮, (∏ y ∈ x.2, g y) * ∏ z ∈ x.1, a z := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        simp [hψ]
    _ = ∑ Γ ∈ (((gasZsub zs X).powerset).erase ∅).filter
          (fun Γ => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')),
          ∑ Dy ∈ (Finset.univ.filter (fun y => act y Γ)).powerset,
            (∏ y ∈ Dy, g y) * ∏ z ∈ Γ, a z := by
        rw [h𝒮, Finset.sum_sigma']
    _ = _ := by
        refine Finset.sum_congr rfl (fun Γ _ => ?_)
        rw [← Finset.sum_mul, ← Finset.prod_one_add, mul_comm]

omit [Fintype B] [Fintype Zt] in
/-- **The coupling entropy through the attachment sets** (the core): if every coupling active for
`Γ` meets the attachment set `att Z` of a member of `Γ` and the active couplings through every
block have entropy `Cc`, the product of `1 + g` over them is at most `e^{Cc ∑_Γ |att Z|}`. -/
theorem prod_actGas_le_att (att : Zt → Finset B)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (att z))
    (g : Yt → ℝ) (hg : ∀ y, 0 ≤ g y) {Cc : ℝ} (hCc : 0 ≤ Cc) (Γ : Finset Zt)
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y), g y ≤ Cc) :
    ∏ y ∈ Finset.univ.filter (fun y => act y Γ), (1 + g y) ≤
      Real.exp (Cc * ∑ z ∈ Γ, ((att z).card : ℝ)) := by
  refine (Real.prod_one_add_le_exp_sum _ hg).trans (Real.exp_le_exp.mpr ?_)
  set f : Yt → ℝ := fun y => if act y Γ then g y else 0 with hf
  have hf0 : ∀ y, 0 ≤ f y := fun y => by
    simp only [hf]
    split_ifs
    · exact hg y
    · exact le_rfl
  have hcov := sum_le_sum_cover (Finset.univ.filter (fun y => act y Γ)) cy (Γ.biUnion att) f hf0
    (fun y hy => by
      obtain ⟨z, hz, hnd⟩ := hmeet y Γ (Finset.mem_filter.mp hy).2
      obtain ⟨b, hb1, hb2⟩ := Finset.not_disjoint_iff.mp hnd
      exact ⟨b, Finset.mem_biUnion.mpr ⟨z, hz, hb2⟩, hb1⟩)
  have hfs : ∑ y ∈ Finset.univ.filter (fun y => act y Γ), g y =
      ∑ y ∈ Finset.univ.filter (fun y => act y Γ), f y :=
    Finset.sum_congr rfl (fun y hy => by
      simp [hf, (Finset.mem_filter.mp hy).2])
  have hin : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y), f y ≤ Cc := by
    intro b
    refine le_of_eq_of_le ?_ (hent b)
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h1 : act y Γ <;> by_cases h2 : b ∈ cy y <;> simp [hf, h1, h2]
  calc ∑ y ∈ Finset.univ.filter (fun y => act y Γ), g y
      ≤ ∑ b ∈ Γ.biUnion att, ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y), f y := hfs ▸ hcov
    _ ≤ ∑ _b ∈ Γ.biUnion att, Cc := Finset.sum_le_sum (fun b _ => hin b)
    _ = ((Γ.biUnion att).card : ℝ) * Cc := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∑ z ∈ Γ, ((att z).card : ℝ)) * Cc := by
        refine mul_le_mul_of_nonneg_right ?_ hCc
        exact_mod_cast Finset.card_biUnion_le
    _ = Cc * ∑ z ∈ Γ, ((att z).card : ℝ) := mul_comm _ _

omit [Fintype B] [Fintype Zt] in
/-- The product of `1 + g` over the couplings active for `Γ` is at most `e^{Cc ∑_Γ |Z|}` when the
active couplings through every block have entropy `Cc`. -/
theorem prod_actGas_le (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z))
    (g : Yt → ℝ) (hg : ∀ y, 0 ≤ g y) {Cc : ℝ} (hCc : 0 ≤ Cc) (Γ : Finset Zt)
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y), g y ≤ Cc) :
    ∏ y ∈ Finset.univ.filter (fun y => act y Γ), (1 + g y) ≤
      Real.exp (Cc * ∑ z ∈ Γ, ((zs z).card : ℝ)) :=
  prod_actGas_le_att zs hmeet g hg hCc Γ hent

omit [Fintype B] in
/-- **The combinatorial part of the activity bound, with attachment and anchor sets and a general
size** (the core).  Let every heavy object have an attachment set `att Z` met by the couplings it
activates, of at most `σ Z` blocks, and a nonempty anchor set `anc Z ⊆ Z`.  For nonnegative
majorants `g` of the couplings and `a` of the heavy objects, if the couplings active for every
compatible family have entropy `Cc` through every block and the heavy objects anchored at every
block satisfy `∑ a e^{Cc σ Z} ≤ η`, the sum over the connected admissible families with union `X` of
`∏ g ∏ a` is at most `exp(|X| η) - 1`. -/
theorem cfam_actGas_majorant_le_gen (att anc : Zt → Finset B) (σ : Zt → ℝ)
    (hanc : ∀ z, (anc z).Nonempty) (hancs : ∀ z, anc z ⊆ zs z)
    (hatt : ∀ z, ((att z).card : ℝ) ≤ σ z)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (att z))
    (g : Yt → ℝ) (a : Zt → ℝ) (hg : ∀ y, 0 ≤ g y) (ha : ∀ z, 0 ≤ a z) {Cc η : ℝ}
    (hCc : 0 ≤ Cc)
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y), g y ≤ Cc)
    (hheavy : ∀ b : B, ∑ z ∈ Finset.univ.filter (fun z => b ∈ anc z),
      a z * Real.exp (Cc * σ z) ≤ η)
    (X : Finset B) :
    ∑ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X, (∏ y ∈ C.toLeft, g y) * ∏ z ∈ C.toRight, a z ≤
      Real.exp (X.card * η) - 1 := by
  set ζ : Zt → ℝ := fun z => a z * Real.exp (Cc * σ z) with hζ
  have hζ0 : ∀ z, 0 ≤ ζ z := fun z => mul_nonneg (ha z) (Real.exp_pos _).le
  have h1 := sum_cfam_actGas_le (cy := cy) (zs := zs)
    (fun y Γ h => (hmeet y Γ h).elim fun z hz => ⟨z, hz.1⟩) g a hg ha X
  have h2 : ∀ Γ ∈ (((gasZsub zs X).powerset).erase ∅).filter
      (fun Γ => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')),
      (∏ z ∈ Γ, a z) * ∏ y ∈ Finset.univ.filter (fun y => act y Γ), (1 + g y) ≤
        ∏ z ∈ Γ, ζ z := by
    intro Γ hΓ
    calc (∏ z ∈ Γ, a z) * ∏ y ∈ Finset.univ.filter (fun y => act y Γ), (1 + g y)
        ≤ (∏ z ∈ Γ, a z) * Real.exp (Cc * ∑ z ∈ Γ, ((att z).card : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (prod_actGas_le_att att hmeet g hg hCc Γ (hent Γ (Finset.mem_filter.mp hΓ).2))
            (Finset.prod_nonneg (fun z _ => ha z))
      _ ≤ (∏ z ∈ Γ, a z) * Real.exp (Cc * ∑ z ∈ Γ, σ z) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
            (Finset.prod_nonneg (fun z _ => ha z))
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => hatt z) hCc
      _ = ∏ z ∈ Γ, ζ z := by
          rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  have h3 : ∑ Γ ∈ (((gasZsub zs X).powerset).erase ∅).filter
      (fun Γ => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')), ∏ z ∈ Γ, ζ z ≤
        ∑ Γ ∈ ((gasZsub zs X).powerset).erase ∅, ∏ z ∈ Γ, ζ z :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun Γ _ _ => Finset.prod_nonneg (fun z _ => hζ0 z))
  have h4 := sum_powerset_erase_le ζ hζ0 (gasZsub zs X)
  have h5 : ∑ z ∈ gasZsub zs X, ζ z ≤ X.card * η := by
    refine (sum_le_sum_cover (gasZsub zs X) anc X ζ hζ0 (fun z hz' => ?_)).trans ?_
    · obtain ⟨b, hb⟩ := hanc z
      simp only [gasZsub, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
      exact ⟨b, hz' (hancs z hb), hb⟩
    · calc ∑ b ∈ X, ∑ z ∈ Finset.univ.filter (fun z => b ∈ anc z), ζ z
          ≤ ∑ _b ∈ X, η := Finset.sum_le_sum (fun b _ => hheavy b)
        _ = X.card * η := by rw [Finset.sum_const, nsmul_eq_mul]
  have h6 := Real.exp_le_exp.mpr h5
  linarith [(Finset.sum_le_sum h2).trans h3]

omit [Fintype B] in
/-- **The combinatorial part of the activity bound.**  For nonnegative majorants `g` of the
couplings and `a` of the heavy objects, if the couplings active for every compatible family have
entropy `Cc` through every block and the heavy objects through every block satisfy
`∑ a e^{Cc |Z|} ≤ η`, the sum over the connected admissible families with union `X` of `∏ g ∏ a`
is at most `exp(|X| η) - 1`. -/
theorem cfam_actGas_majorant_le (hz : ∀ z, (zs z).Nonempty)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z))
    (g : Yt → ℝ) (a : Zt → ℝ) (hg : ∀ y, 0 ≤ g y) (ha : ∀ z, 0 ≤ a z) {Cc η : ℝ}
    (hCc : 0 ≤ Cc)
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y), g y ≤ Cc)
    (hheavy : ∀ b : B, ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z),
      a z * Real.exp (Cc * (zs z).card) ≤ η)
    (X : Finset B) :
    ∑ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X, (∏ y ∈ C.toLeft, g y) * ∏ z ∈ C.toRight, a z ≤
      Real.exp (X.card * η) - 1 :=
  cfam_actGas_majorant_le_gen zs zs (fun z => ((zs z).card : ℝ)) hz (fun _ => subset_rfl)
    (fun _ => le_rfl) hmeet g a hg ha hCc hent hheavy X

end ActSum

section SumLe

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {cy : Yt → Finset B} {zs cr : Zt → Finset B}

omit [Fintype B] in
theorem sum_cfam_le (g : Yt → ℝ) (a : Zt → ℝ) (hg : ∀ y, 0 ≤ g y) (ha : ∀ z, 0 ≤ a z)
    (X : Finset B) :
    ∑ C ∈ Cfam (gasCs cy zs) (gasA cy zs cr) X, (∏ y ∈ C.toLeft, g y) * ∏ z ∈ C.toRight, a z ≤
      ∑ Γ ∈ ((gasZsub zs X).powerset).erase ∅,
        (∏ z ∈ Γ, a z) * ∏ y ∈ gasYm cy cr Γ, (1 + g y) := by
  have hset : ∀ Γ : Finset Zt,
      Finset.univ.filter (fun y => coreAct cy cr y Γ) = gasYm cy cr Γ := by
    intro Γ
    ext y
    simp only [gasYm, Finset.mem_filter, Finset.mem_univ, true_and]
    simp [coreAct, Finset.disjoint_biUnion_right]
  refine (sum_cfam_actGas_le (act := coreAct cy cr) (fun y Γ h => ?_) g a hg ha X).trans ?_
  · obtain ⟨z, hz, _⟩ := h
    exact ⟨z, hz⟩
  · simp only [hset]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun Γ _ _ =>
      mul_nonneg (Finset.prod_nonneg (fun z _ => ha z))
        (Finset.prod_nonneg (fun y _ => by linarith [hg y])))

end SumLe

section ActMain

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {act : Yt → Finset Zt → Prop} {cy : Yt → Finset B} {zs : Zt → Finset B}

omit [Fintype B] [Fintype Zt] in
/-- The entropy of all the couplings through a block bounds that of the active ones. -/
theorem sum_filter_act_le {f : Yt → ℝ} {K : ℝ} (hf : ∀ y, 0 ≤ f y)
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y), f y ≤ K)
    (Γ : Finset Zt) (b : B) :
    ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y), f y ≤ K :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (fun _ hy => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2.2⟩)
    (fun y _ _ => hf y)) (hent b)

omit [Fintype B] [Fintype Yt] in
/-- Unweighted counts with a uniform bound give the summed counts. -/
theorem sum_filter_le_of_count {a : Zt → ℝ} {p h K0 : ℝ}
    (ha : ∀ z, a z ≤ Real.exp (-p - h * (zs z).card))
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤ K0 ^ v)
    (b : B) (v : ℕ) :
    ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v), a z ≤
      K0 ^ v * Real.exp (-p - h * v) := by
  calc ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v), a z
      ≤ ∑ _z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v),
          Real.exp (-p - h * v) := by
        refine Finset.sum_le_sum (fun z hz => ?_)
        have := (Finset.mem_filter.mp hz).2.2
        exact (ha z).trans_eq (by rw [this])
    _ = ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) *
          Real.exp (-p - h * v) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ K0 ^ v * Real.exp (-p - h * v) :=
        mul_le_mul_of_nonneg_right (hcount b v) (Real.exp_pos _).le

omit [Fintype B] in
/-- **The activity bound with weighted counts, for heavy objects with a size, an attachment set and
an anchor set** (the scalar core).  Let every heavy object `Z` have a size `σ Z ≥ 1`, an attachment
set `att Z` of at most `σ Z` blocks, met by every coupling it activates, and a nonempty anchor set
`anc Z ⊆ Z`; the size of the support is `d(Z) ≤ c₂ σ Z`.  For heavy majorants `a ≥ 0` whose sums
over the heavy objects anchored at a block with size `v` are at most `M₀ K₀''^v e^{-p - h v}`, if
the couplings active for every compatible family satisfy `∑_{Y ∋ b} e^{-(κ'' - κ') d(Y)} ≤ K₀'`,
then for `|X| ≤ c₁ (1 + d(X))`
`∑_{C ∈ Cfam X} ∏_Y B₀ e^{B₀} e^{-κ'' d(Y)} ∏_Z a(Z) ≤ 3 c₁ η e^{-(κ' - 2) d(X)}`,
`η = M₀ e^{-p} e^{-(c'+2)}`, provided `h ≥ B₀ e^{B₀} e^{κ' c} K₀' + κ' (c₂ + c) + c' + 3 + ln K₀''`
and `c₁ η ≤ 1/7`.  The ratio `c₁` of the polymers to their size and the entropy margin `c'` of the
heavy objects are independent; the prefactor `M₀` of the counts enters `η` only. -/
theorem sum_cfam_actGas_le_of_counts_sized {d : Finset B → ℝ}
    {B0 κ' κ'' c c1 c' c2 p h K0' K0'' M0 : ℝ}
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hc : 0 ≤ c) (hc1 : 0 ≤ c1) (hc' : 0 ≤ c') (hM0 : 0 ≤ M0)
    (hd : ∀ Y, 0 ≤ d Y)
    (σ : Zt → ℕ) (hσ : ∀ z, 1 ≤ σ z) (att anc : Zt → Finset B)
    (hanc : ∀ z, (anc z).Nonempty) (hancs : ∀ z, anc z ⊆ zs z)
    (hatt : ∀ z, (att z).card ≤ σ z)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (att z))
    (a : Zt → ℝ) (ha : ∀ z, 0 ≤ a z)
    (hzd : ∀ z, d (zs z) ≤ c2 * σ z)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → actGasA act zs C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    (hK0' : 0 ≤ K0')
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y),
        Real.exp (-(κ'' - κ') * d (cy y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ anc z ∧ σ z = v), a z ≤
        M0 * K0'' ^ v * Real.exp (-p - h * v))
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' + κ' * (c2 + c) + c' + 3 +
      Real.log K0'' ≤ h)
    (hη : c1 * (M0 * Real.exp (-p) * Real.exp (-(c' + 2))) ≤ 1 / 7)
    (X : Finset B) (hG1 : (X.card : ℝ) ≤ c1 * (1 + d X)) :
    ∑ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X,
        (∏ y ∈ C.toLeft, B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y))) * ∏ z ∈ C.toRight, a z ≤
      3 * (c1 * (M0 * Real.exp (-p) * Real.exp (-(c' + 2)))) * Real.exp (-(κ' - 2) * d X) := by
  set η : ℝ := M0 * Real.exp (-p) * Real.exp (-(c' + 2)) with hηdef
  set Cc : ℝ := B0 * Real.exp B0 * Real.exp (κ' * c) * K0' with hCc
  set lam : ℝ := h - κ' * (c2 + c) - Cc with hlam
  have hlam' : c' + 3 + Real.log K0'' ≤ lam := by
    rw [hlam]
    linarith
  have hCc0 : 0 ≤ Cc := by positivity
  have hσr : ∀ z, (1 : ℝ) ≤ (σ z : ℝ) := fun z => by exact_mod_cast hσ z
  set a' : Zt → ℝ := fun z => Real.exp (κ' * ((c2 + c) * (σ z : ℝ))) * a z with ha'
  -- the size distributed over the members of each family
  have hterm : ∀ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X,
      Real.exp (κ' * d X) *
          ((∏ y ∈ C.toLeft, B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y))) *
            ∏ z ∈ C.toRight, a z) ≤
        (∏ y ∈ C.toLeft, gasG cy d B0 κ' κ'' c y) * ∏ z ∈ C.toRight, a' z :=
    fun C hC => exp_mul_prod_le_of_mem_cfam_sized hB0 hκ' hc (fun z => (σ z : ℝ)) hσr hzd hG3
      ha hC
  -- the entropy of the couplings
  have hent' : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y),
        gasG cy d B0 κ' κ'' c y ≤ Cc := by
    intro Γ hΓ b
    simp only [gasG]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hent Γ hΓ b) (by positivity)
  -- the entropy of the heavy objects
  have hcountω : ∀ (b : B) (v : ℕ), ∑ z ∈ Finset.univ.filter
      (fun z => b ∈ anc z ∧ σ z = v), Real.exp (p + h * (σ z : ℝ)) * a z ≤ M0 * K0'' ^ v := by
    intro b v
    calc ∑ z ∈ Finset.univ.filter (fun z => b ∈ anc z ∧ σ z = v),
          Real.exp (p + h * (σ z : ℝ)) * a z
        = Real.exp (p + h * v) *
            ∑ z ∈ Finset.univ.filter (fun z => b ∈ anc z ∧ σ z = v), a z := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun z hz => ?_)
          rw [(Finset.mem_filter.mp hz).2.2]
      _ ≤ Real.exp (p + h * v) * (M0 * K0'' ^ v * Real.exp (-p - h * v)) :=
          mul_le_mul_of_nonneg_left (hcount b v) (Real.exp_pos _).le
      _ = M0 * K0'' ^ v := by
          have : Real.exp (p + h * v) * Real.exp (-p - h * v) = 1 := by
            rw [← Real.exp_add]; simp
          calc Real.exp (p + h * v) * (M0 * K0'' ^ v * Real.exp (-p - h * v))
              = M0 * K0'' ^ v * (Real.exp (p + h * v) * Real.exp (-p - h * v)) := by ring
            _ = _ := by rw [this, mul_one]
  have hheavy : ∀ b : B, ∑ z ∈ Finset.univ.filter (fun z => b ∈ anc z),
      a' z * Real.exp (Cc * (σ z : ℝ)) ≤ η := by
    intro b
    calc ∑ z ∈ Finset.univ.filter (fun z => b ∈ anc z), a' z * Real.exp (Cc * (σ z : ℝ))
        = Real.exp (-p) * ∑ z ∈ Finset.univ.filter (fun z => b ∈ anc z),
            Real.exp (p + h * (σ z : ℝ)) * a z * Real.exp (-lam * (σ z : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun z _ => ?_)
          simp only [ha']
          have : Real.exp (κ' * ((c2 + c) * (σ z : ℝ))) * Real.exp (Cc * (σ z : ℝ)) =
              Real.exp (-p) * Real.exp (p + h * (σ z : ℝ)) * Real.exp (-lam * (σ z : ℝ)) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            congr 1
            rw [hlam]
            ring
          calc Real.exp (κ' * ((c2 + c) * (σ z : ℝ))) * a z * Real.exp (Cc * (σ z : ℝ))
              = (Real.exp (κ' * ((c2 + c) * (σ z : ℝ))) * Real.exp (Cc * (σ z : ℝ))) * a z := by
                ring
            _ = _ := by rw [this]; ring
      _ ≤ Real.exp (-p) * (M0 * Real.exp (-(c' + 2))) :=
          mul_le_mul_of_nonneg_left (heavy_entropy_sized hc' hK1 hM0 σ hσ anc _ hcountω hlam' b)
            (Real.exp_pos _).le
      _ = η := by rw [hηdef]; ring
  have h2 := cfam_actGas_majorant_le_gen att anc (fun z => (σ z : ℝ)) hanc hancs
    (fun z => by exact_mod_cast hatt z) hmeet (gasG cy d B0 κ' κ'' c) a' (gasG_nonneg hB0)
    (fun z => mul_nonneg (Real.exp_pos _).le (ha z)) hCc0 hent' hheavy X
  have hη0 : 0 ≤ η := by rw [hηdef]; positivity
  have h3 := gas_real_bound_gen (D := d X) (n := (X.card : ℝ)) hη0 hη hc1 (hd _)
    (Nat.cast_nonneg _) hG1
  set S := ∑ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X,
    (∏ y ∈ C.toLeft, B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y))) * ∏ z ∈ C.toRight, a z
    with hS
  have h4 : Real.exp (κ' * d X) * S ≤ 3 * (c1 * η) * Real.exp (2 * d X) := by
    rw [hS, Finset.mul_sum]
    exact ((Finset.sum_le_sum hterm).trans h2).trans (by linarith)
  have e : Real.exp (-κ' * d X) * Real.exp (κ' * d X) = 1 := by
    rw [← Real.exp_add]
    simp
  calc S = Real.exp (-κ' * d X) * (Real.exp (κ' * d X) * S) := by rw [← mul_assoc, e, one_mul]
    _ ≤ Real.exp (-κ' * d X) * (3 * (c1 * η) * Real.exp (2 * d X)) :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    _ = 3 * (c1 * η) * Real.exp (-(κ' - 2) * d X) := by
        have : Real.exp (-κ' * d X) * Real.exp (2 * d X) = Real.exp (-(κ' - 2) * d X) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [← this]
        ring

omit [Fintype B] in
/-- **The activity bound with weighted counts (scalar core).**  For heavy majorants `a ≥ 0` whose
sums over the heavy objects through a block with `v` blocks are at most `K₀''^v e^{-p - h v}`, if
the couplings active for every compatible family satisfy `∑_{Y ∋ b} e^{-(κ'' - κ') d(Y)} ≤ K₀'`,
then `∑_{C ∈ Cfam X} ∏_Y B₀ e^{B₀} e^{-κ'' d(Y)} ∏_Z a(Z) ≤ 3 c₁ e^{-p} e^{-(κ' - 2) d(X)}` for
`|X| ≤ c₁ (1 + d(X))`, provided `h ≥ B₀ e^{B₀} e^{κ' c} K₀' + κ' (c₂ + c) + c₁ + 3 + ln K₀''` (the
instance of `sum_cfam_actGas_le_of_counts_sized` with the size `|Z|`, attachment and anchor `Z`,
`M₀ = 1`, `c' = c₁`). -/
theorem sum_cfam_actGas_le_of_counts {d : Finset B → ℝ} {B0 κ' κ'' c c1 c2 p h K0' K0'' : ℝ}
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hc : 0 ≤ c) (hc1 : 0 ≤ c1) (hp : 0 ≤ p)
    (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (zs z).Nonempty)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z))
    (a : Zt → ℝ) (ha : ∀ z, 0 ≤ a z)
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → actGasA act zs C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    (hK0' : 0 ≤ K0')
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y),
        Real.exp (-(κ'' - κ') * d (cy y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v), a z ≤
        K0'' ^ v * Real.exp (-p - h * v))
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' + κ' * (c2 + c) + c1 + 3 +
      Real.log K0'' ≤ h)
    (X : Finset B) (hG1 : (X.card : ℝ) ≤ c1 * (1 + d X)) :
    ∑ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X,
        (∏ y ∈ C.toLeft, B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y))) * ∏ z ∈ C.toRight, a z ≤
      3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X) := by
  have h := sum_cfam_actGas_le_of_counts_sized (M0 := 1) (c' := c1) hB0 hκ' hc hc1 hc1
    zero_le_one hd (fun z => (zs z).card) (fun z => (hz z).card_pos) zs zs hz
    (fun _ => subset_rfl) (fun _ => le_rfl) hmeet a ha hzd hG3 hK0' hent hK1
    (fun b v => by simpa using hcount b v) hh (by simpa using mul_exp_neg_le_seventh hp hc1) X hG1
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  have hle : Real.exp (-(c1 + 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h0 : 0 ≤ Real.exp (-p) := (Real.exp_pos _).le
  nlinarith [mul_le_mul_of_nonneg_left hle (mul_nonneg hc1 h0)]

omit [Fintype B] in
/-- **GAS with a general activation rule (activity bound), for heavy objects with a size, an
attachment set and an anchor set**: with couplings bounded by `B₀ e^{-κ'' d(Y)}` and heavy weights
with the counts `∑_{Z : b ∈ anc Z, σ Z = v} |τ Z| ≤ M₀ K₀''^v e^{-p - h v}`, the activities satisfy
`|K(X)| ≤ 3 c₁ η e^{-(κ' - 2) d(X)}`, `η = M₀ e^{-p} e^{-(c'+2)}`, for `|X| ≤ c₁ (1 + d(X))`
(`sum_cfam_actGas_le_of_counts_sized`). -/
theorem actGasK_activity_bound_sized {β : Yt → ℂ} {τ : Zt → ℂ} {d : Finset B → ℝ}
    {B0 κ' κ'' c c1 c' c2 p h K0' K0'' M0 : ℝ}
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c) (hc1 : 0 ≤ c1) (hc' : 0 ≤ c')
    (hM0 : 0 ≤ M0) (hd : ∀ Y, 0 ≤ d Y)
    (σ : Zt → ℕ) (hσ : ∀ z, 1 ≤ σ z) (att anc : Zt → Finset B)
    (hanc : ∀ z, (anc z).Nonempty) (hancs : ∀ z, anc z ⊆ zs z)
    (hatt : ∀ z, (att z).card ≤ σ z)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (att z))
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hzd : ∀ z, d (zs z) ≤ c2 * σ z)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → actGasA act zs C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    (hK0' : 0 ≤ K0')
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y),
        Real.exp (-(κ'' - κ') * d (cy y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ anc z ∧ σ z = v), ‖τ z‖ ≤
        M0 * K0'' ^ v * Real.exp (-p - h * v))
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' + κ' * (c2 + c) + c' + 3 +
      Real.log K0'' ≤ h)
    (hη : c1 * (M0 * Real.exp (-p) * Real.exp (-(c' + 2))) ≤ 1 / 7)
    (X : NePoly B) (hG1 : (X.1.card : ℝ) ≤ c1 * (1 + d X.1)) :
    ‖actGasK act cy zs β τ X‖ ≤
      3 * (c1 * (M0 * Real.exp (-p) * Real.exp (-(c' + 2)))) * Real.exp (-(κ' - 2) * d X.1) := by
  refine le_trans ?_ (sum_cfam_actGas_le_of_counts_sized hB0 hκ' hc hc1 hc' hM0 hd σ hσ att anc
    hanc hancs hatt hmeet (fun z => ‖τ z‖) (fun z => norm_nonneg _) hzd hG3 hK0' hent hK1
    hcount hh hη X.1 hG1)
  unfold actGasK polyAct
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C _ => ?_))
  rw [prod_gasW, norm_mul, norm_prod, norm_prod]
  exact mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀ (fun y _ => norm_nonneg _)
    (fun y _ => norm_expm1_le hB0 (hκ'.trans hκ'') hd y (hB y)))
    (Finset.prod_nonneg (fun z _ => norm_nonneg _))

omit [Fintype B] in
/-- **GAS with a general activation rule (activity bound)**: with couplings bounded by
`B₀ e^{-κ'' d(Y)}` and heavy weights with the summed counts
`∑_{Z ∋ b, |Z| = v} |τ Z| ≤ K₀''^v e^{-p - h v}`, the activities satisfy
`|K(X)| ≤ 3 c₁ e^{-p} e^{-(κ' - 2) d(X)}` for `|X| ≤ c₁ (1 + d(X))`. -/
theorem actGasK_activity_bound {β : Yt → ℂ} {τ : Zt → ℂ} {d : Finset B → ℝ}
    {B0 κ' κ'' c c1 c2 p h K0' K0'' : ℝ}
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c) (hc1 : 0 ≤ c1) (hp : 0 ≤ p)
    (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (zs z).Nonempty)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z))
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → actGasA act zs C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    (hK0' : 0 ≤ K0')
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y),
        Real.exp (-(κ'' - κ') * d (cy y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v), ‖τ z‖ ≤
        K0'' ^ v * Real.exp (-p - h * v))
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' + κ' * (c2 + c) + c1 + 3 +
      Real.log K0'' ≤ h)
    (X : NePoly B) (hG1 : (X.1.card : ℝ) ≤ c1 * (1 + d X.1)) :
    ‖actGasK act cy zs β τ X‖ ≤ 3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X.1) := by
  have h := actGasK_activity_bound_sized (M0 := 1) (c' := c1) hB0 hκ' hκ'' hc hc1 hc1 zero_le_one
    hd (fun z => (zs z).card) (fun z => (hz z).card_pos) zs zs hz (fun _ => subset_rfl)
    (fun _ => le_rfl) hmeet hB hzd hG3 hK0' hent hK1 (fun b v => by simpa using hcount b v) hh
    (by simpa using mul_exp_neg_le_seventh hp hc1) X hG1
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  have hle : Real.exp (-(c1 + 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h0 : 0 ≤ Real.exp (-p) := (Real.exp_pos _).le
  nlinarith [mul_le_mul_of_nonneg_left hle (mul_nonneg hc1 h0)]

end ActMain

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
  have hset : gasYm cy cr Γ = Finset.univ.filter (fun y => coreAct cy cr y Γ) := by
    ext y
    simp only [gasYm, Finset.mem_filter, Finset.mem_univ, true_and]
    simp [coreAct, Finset.disjoint_biUnion_right]
  rw [hset]
  refine prod_actGas_le (coreAct_meets (fun _ => Finset.Subset.rfl) hcr) _ (gasG_nonneg hB0)
    (by positivity) Γ (fun b => ?_)
  simp only [gasG]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_filter_act_le (fun _ => (Real.exp_pos _).le) hent Γ b)
    (by positivity)

omit [Fintype B] in
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
    ‖gasK cy zs cr β τ X‖ ≤ 3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X.1) :=
  actGasK_activity_bound (act := coreAct cy cr) hB0 hκ' hκ'' hc hc1 hp hd hz
    (coreAct_meets (fun _ => Finset.Subset.rfl) hcr) hB hzd hG3 hK0'
    (fun Γ _ b => sum_filter_act_le (fun _ => (Real.exp_pos _).le) hent Γ b) hK1
    (sum_filter_le_of_count hτ hcount) hh X hG1

end Main

end Balaban.Polymer
