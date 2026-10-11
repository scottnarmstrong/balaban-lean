/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.Locality
public import Balaban.Multiscale.Analyticity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The block-decay algebra (GREEN.md §4.6, "the kernel algebra")

For finite index types `ι` carrying a site map `s : ι → Ω₁` (scalar fields: `ι = Ω₁`; vector
fields: `ι = Ω₁ × Fin N`) the *block norm* `bn s j y f` is the `ℓ²` norm of `f` restricted to the
points `p` whose site lies in the `j`-block of `y`.  A matrix `T : Matrix ι₁ ι₂ ℂ` lies in the
class `Dec w γ τ C` if for all blocks `(j, y)`, `(j', y')`
`bn (T (χ_{y'} f)) ≤ C (ℓ_j ℓ_{j'})^w e^{-γ d(y,y')} τ(y,y') bn_{y'} f`.
With `τ = 1` this is the class `𝒜_γ(C)` of GREEN.md §4.6 for `w = 1` (up to the harmless change
`ℓ⁻¹ T ℓ⁻¹ ↔ T`); `w` records the dimension of the operator (`G` has `w = 1`, `K(φ₀) G` has
`w = 0`).  The composition lemma `Dec.comp` is the summation Lemma 4.4
(`sum_siteWeight_decay_le`) combined with the absorption of the scale mismatch
`ℓ_x / ℓ_y ≤ L e^{κ d(x,y)}`, `κ = log L / (ϱ - 1)` (`spacing_ratio_le`); it loses an arbitrarily
small amount of the rate (the parameter `θ`).
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-! ### Algebra of the decay factor -/

section DecayAlgebra

theorem decay_add_rate (c₁ c₂ : ℝ) (D : ENNReal) :
    decay (c₁ + c₂) D = decay c₁ D * decay c₂ D := by
  unfold decay
  split_ifs with h
  · simp
  · rw [← Real.exp_add]; congr 1; ring

theorem decay_add_dist (c : ℝ) (D₁ D₂ : ENNReal) :
    decay c (D₁ + D₂) = decay c D₁ * decay c D₂ := by
  unfold decay
  by_cases h1 : D₁ = ⊤
  · simp [h1]
  by_cases h2 : D₂ = ⊤
  · simp [h2]
  have h12 : D₁ + D₂ ≠ ⊤ := ENNReal.add_ne_top.2 ⟨h1, h2⟩
  simp only [h1, h2, h12, ↓reduceIte]
  rw [← Real.exp_add, ENNReal.toReal_add h1 h2]; congr 1; ring

theorem decay_anti_dist {c : ℝ} (hc : 0 ≤ c) {D₁ D₂ : ENNReal} (h : D₁ ≤ D₂) :
    decay c D₂ ≤ decay c D₁ := by
  unfold decay
  by_cases h2 : D₂ = ⊤
  · simp only [h2, ↓reduceIte]
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  · have h1 : D₁ ≠ ⊤ := ne_top_of_le_ne_top h2 h
    simp only [h1, h2, ↓reduceIte]
    exact Real.exp_le_exp.2 (by
      have := ENNReal.toReal_mono h2 h
      nlinarith)

theorem decay_anti_rate {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) (D : ENNReal) : decay c₂ D ≤ decay c₁ D := by
  unfold decay
  split_ifs
  · exact le_rfl
  · exact Real.exp_le_exp.2 (by nlinarith [ENNReal.toReal_nonneg (a := D)])

theorem decay_le_one {c : ℝ} (hc : 0 ≤ c) (D : ENNReal) : decay c D ≤ 1 := by
  unfold decay
  split_ifs
  · exact zero_le_one
  · rw [Real.exp_le_one_iff]; nlinarith [ENNReal.toReal_nonneg (a := D)]

theorem decay_of_ne_top {c : ℝ} {D : ENNReal} (h : D ≠ ⊤) :
    decay c D = Real.exp (-(c * D.toReal)) := by
  simp [decay, h]

theorem decay_top (c : ℝ) : decay c ⊤ = 0 := by simp [decay]

theorem decay_ofReal_ge {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s) {D : ENNReal}
    (h : D ≤ ENNReal.ofReal s) : Real.exp (-(c * s)) ≤ decay c D := by
  have := decay_anti_dist hc h
  rw [decay_of_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hs] at this
  exact this

end DecayAlgebra

/-! ### Scale ratios -/

section Ratio

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The scale mismatch: if `d(y, y') < ⊤` and `log L ≤ κ (ϱ - 1)` then `ℓ_{j'} ≤ L e^{κ d(y,y')} ℓ_j`. -/
theorem spacing_ratio_le (hϱ : 1 < ϱ) {κ : ℝ} (hκ : Real.log L ≤ κ * (ϱ - 1)) {j j' : ℕ}
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k) {y y' : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j') (hD : G.pathDist y y' ≠ ⊤) :
    (L : ℝ) ^ j' ≤ L * Real.exp (κ * (G.pathDist y y').toReal) * (L : ℝ) ^ j := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hr : 0 < ϱ - 1 := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hκ0 : 0 ≤ κ := by
    by_contra h
    push Not at h
    nlinarith
  have hsep := G.pathDist_separation hϱ.le hj1 hj'1 hjk hj'k hy hy'
  have hsep' : (ϱ - 1) * ((j - j' + (j' - j) - 1 : ℕ) : ℝ) ≤ (G.pathDist y y').toReal := by
    have := ENNReal.toReal_mono hD hsep
    rwa [ENNReal.toReal_ofReal (mul_nonneg hr.le (Nat.cast_nonneg _))] at this
  set m := j - j' + (j' - j) - 1 with hm
  have hjj : j' ≤ j + (m + 1) := by omega
  have h1 : (L : ℝ) ^ j' ≤ (L : ℝ) ^ j * (L : ℝ) ^ (m + 1) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hL hjj
  have h2 : (L : ℝ) ^ m ≤ Real.exp (κ * (G.pathDist y y').toReal) := by
    have e : (L : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log L) := by
      rw [Real.exp_nat_mul, Real.exp_log hL0]
    rw [e]
    apply Real.exp_le_exp.2
    have h3 : (m : ℝ) * Real.log L ≤ (m : ℝ) * (κ * (ϱ - 1)) :=
      mul_le_mul_of_nonneg_left hκ (Nat.cast_nonneg _)
    have h4 : κ * ((ϱ - 1) * (m : ℝ)) ≤ κ * (G.pathDist y y').toReal :=
      mul_le_mul_of_nonneg_left hsep' hκ0
    nlinarith
  calc (L : ℝ) ^ j' ≤ (L : ℝ) ^ j * (L : ℝ) ^ (m + 1) := h1
    _ = L * (L : ℝ) ^ m * (L : ℝ) ^ j := by ring
    _ ≤ L * Real.exp (κ * (G.pathDist y y').toReal) * (L : ℝ) ^ j := by gcongr

end Ratio

theorem zpow_div_le {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 1 ≤ r) (h1 : a ≤ r * b)
    (h2 : b ≤ r * a) (m : ℤ) : (a / b) ^ m ≤ r ^ m.natAbs := by
  have hr0 : 0 < r := by linarith
  rcases le_total 0 m with hm | hm
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    simp only [zpow_natCast, Int.natAbs_natCast]
    have : a / b ≤ r := by rw [div_le_iff₀ hb]; linarith
    exact pow_le_pow_left₀ (by positivity) this n
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, m = -(n : ℤ) := ⟨m.natAbs, by omega⟩
    rw [hn, _root_.zpow_neg, _root_.zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast]
    have : (a / b)⁻¹ ≤ r := by
      rw [inv_div, div_le_iff₀ ha]; linarith
    calc ((a / b) ^ n)⁻¹ = (a / b)⁻¹ ^ n := by rw [inv_pow]
      _ ≤ r ^ n := pow_le_pow_left₀ (by positivity) this n

/-- Product of three scales in the composition: `a^w b^{w+w'} c^{w'} ≤ r₁^{|w'|} r₂^{|w|} (a c)^{w+w'}`. -/
theorem scale_comp {a b c r₁ r₂ : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hr₁ : 1 ≤ r₁)
    (hr₂ : 1 ≤ r₂) (hab : b ≤ r₁ * a) (hba : a ≤ r₁ * b) (hbc : b ≤ r₂ * c) (hcb : c ≤ r₂ * b)
    (w w' : ℤ) :
    a ^ w * b ^ (w + w') * c ^ w' ≤ r₁ ^ w'.natAbs * r₂ ^ w.natAbs * (a * c) ^ (w + w') := by
  have e : a ^ w * b ^ (w + w') * c ^ w' =
      (a * c) ^ (w + w') * ((b / a) ^ w' * (b / c) ^ w) := by
    rw [mul_zpow, div_zpow, div_zpow, zpow_add₀ ha.ne', zpow_add₀ hc.ne', zpow_add₀ hb.ne']
    have := ha.ne'
    have := hc.ne'
    field_simp
  rw [e]
  have h1 := zpow_div_le hb ha hr₁ hab hba w'
  have h2 := zpow_div_le hb hc hr₂ hbc hcb w
  have hp : 0 < (a * c) ^ (w + w') := by positivity
  have h3 : (b / a) ^ w' * (b / c) ^ w ≤ r₁ ^ w'.natAbs * r₂ ^ w.natAbs :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  calc (a * c) ^ (w + w') * ((b / a) ^ w' * (b / c) ^ w)
      ≤ (a * c) ^ (w + w') * (r₁ ^ w'.natAbs * r₂ ^ w.natAbs) :=
        mul_le_mul_of_nonneg_left h3 hp.le
    _ = _ := by ring

/-! ### Block norms on general index types -/

section L2

variable {ι : Type*} [Fintype ι]

/-- The `ℓ²` norm of a field on a finite index type. -/
noncomputable def l2 (f : ι → ℂ) : ℝ := ‖(WithLp.toLp 2 f : EuclideanSpace ℂ ι)‖

theorem l2_eq (f : ι → ℂ) : l2 f = Real.sqrt (∑ p, ‖f p‖ ^ 2) := by
  rw [l2, EuclideanSpace.norm_eq]

theorem l2_nonneg (f : ι → ℂ) : 0 ≤ l2 f := norm_nonneg _

theorem l2_sq (f : ι → ℂ) : l2 f ^ 2 = ∑ p, ‖f p‖ ^ 2 := by
  rw [l2_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

theorem l2_add_le (f g : ι → ℂ) : l2 (f + g) ≤ l2 f + l2 g := by
  unfold l2
  exact norm_add_le (WithLp.toLp 2 f : EuclideanSpace ℂ ι) (WithLp.toLp 2 g)

theorem l2_smul (c : ℂ) (f : ι → ℂ) : l2 (c • f) = ‖c‖ * l2 f := by
  unfold l2
  exact norm_smul c (WithLp.toLp 2 f : EuclideanSpace ℂ ι)

theorem l2_sum_le {κ : Type*} (s : Finset κ) (f : κ → ι → ℂ) :
    l2 (∑ x ∈ s, f x) ≤ ∑ x ∈ s, l2 (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l2]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (l2_add_le _ _).trans (by linarith)

theorem l2_mono {f g : ι → ℂ} (h : ∀ p, ‖f p‖ ≤ ‖g p‖) : l2 f ≤ l2 g := by
  rw [l2_eq, l2_eq]
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun p _ => pow_le_pow_left₀ (norm_nonneg _) (h p) 2)

theorem l2_zero_of {f : ι → ℂ} (h : ∀ p, f p = 0) : l2 f = 0 := by
  rw [l2_eq]; simp [h]

theorem exists_ne_of_l2_ne {f : ι → ℂ} (h : l2 f ≠ 0) : ∃ p, f p ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (l2_zero_of hc)

end L2

section BlockNorm

variable {ι ι₁ ι₂ ι₃ : Type*} [Fintype ι] [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
variable (G : GeneratingSet d L N₀ k ϱ)

omit [Fintype ι] in
/-- The restriction of a field to the points whose site lies in the `j`-block of `y`. -/
noncomputable def bproj (s : ι → G.Ω 1) (j : ℕ) (y : Torus d (N₀ * L ^ k)) (f : ι → ℂ) : ι → ℂ :=
  fun p => if jBlock d L N₀ k j (s p : Torus d (N₀ * L ^ k)) = jBlock d L N₀ k j y then f p else 0

/-- The block norm: the `ℓ²` norm of `f` on the `j`-block of `y`. -/
noncomputable def bn (s : ι → G.Ω 1) (j : ℕ) (y : Torus d (N₀ * L ^ k)) (f : ι → ℂ) : ℝ :=
  l2 (bproj G s j y f)

variable {G}

theorem bn_nonneg (s : ι → G.Ω 1) (j : ℕ) (y : Torus d (N₀ * L ^ k)) (f : ι → ℂ) :
    0 ≤ bn G s j y f := l2_nonneg _

omit [Fintype ι] in
theorem bproj_add (s : ι → G.Ω 1) (j : ℕ) (y : Torus d (N₀ * L ^ k)) (f g : ι → ℂ) :
    bproj G s j y (f + g) = bproj G s j y f + bproj G s j y g := by
  funext p; simp only [bproj, Pi.add_apply]; split_ifs <;> simp

omit [Fintype ι] in
theorem bproj_smul (s : ι → G.Ω 1) (j : ℕ) (y : Torus d (N₀ * L ^ k)) (c : ℂ) (f : ι → ℂ) :
    bproj G s j y (c • f) = c • bproj G s j y f := by
  funext p; simp only [bproj, Pi.smul_apply]; split_ifs <;> simp

omit [Fintype ι] in
theorem bproj_sum {κ : Type*} (s : ι → G.Ω 1) (j : ℕ) (y : Torus d (N₀ * L ^ k)) (S : Finset κ)
    (f : κ → ι → ℂ) : bproj G s j y (∑ x ∈ S, f x) = ∑ x ∈ S, bproj G s j y (f x) := by
  funext p; simp only [bproj, Finset.sum_apply]; split_ifs <;> simp

theorem bn_sum_le {κ : Type*} (s : ι → G.Ω 1) (j : ℕ) (y : Torus d (N₀ * L ^ k)) (S : Finset κ)
    (c : κ → ℝ) (hc : ∀ x, 0 ≤ c x) (f : κ → ι → ℂ) :
    bn G s j y (∑ x ∈ S, ((c x : ℝ) : ℂ) • f x) ≤ ∑ x ∈ S, c x * bn G s j y (f x) := by
  unfold bn
  rw [bproj_sum]
  refine (l2_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
  rw [bproj_smul, l2_smul, Complex.norm_real, Real.norm_of_nonneg (hc x)]

theorem bn_le_of_norm_le (s : ι → G.Ω 1) (j : ℕ) (y : Torus d (N₀ * L ^ k)) {f g : ι → ℂ}
    (h : ∀ p, ‖f p‖ ≤ ‖g p‖) : bn G s j y f ≤ bn G s j y g := by
  refine l2_mono fun p => ?_
  simp only [bproj]
  split_ifs
  · exact h p
  · simp

/-- Restricting to a block does not increase the norm on another block. -/
theorem bn_bproj_le (s : ι → G.Ω 1) (j j' : ℕ) (y y' : Torus d (N₀ * L ^ k)) (f : ι → ℂ) :
    bn G s j y (bproj G s j' y' f) ≤ bn G s j' y' f := by
  unfold bn
  refine l2_mono fun p => ?_
  simp only [bproj]
  split_ifs <;> simp_all

omit [Fintype ι] in
theorem bproj_bproj_self (s : ι → G.Ω 1) (j : ℕ) (y : Torus d (N₀ * L ^ k)) (f : ι → ℂ) :
    bproj G s j y (bproj G s j y f) = bproj G s j y f := by
  funext p; simp only [bproj]; split_ifs <;> simp

theorem bn_bproj_self (s : ι → G.Ω 1) (j : ℕ) (y : Torus d (N₀ * L ^ k)) (f : ι → ℂ) :
    bn G s j y (bproj G s j y f) = bn G s j y f := by
  unfold bn; rw [bproj_bproj_self]

/-- The partition of unity over blocks: `∑ₓ ℓ(x)^{-d} 1[i ∈ Δ(x)] = 1`. -/
theorem sum_siteWeight_indicator (i : G.Ω 1) :
    ∑ x : G.Ω 1, (if jBlock d L N₀ k (G.layerIndex x) (i : Torus d (N₀ * L ^ k)) =
      jBlock d L N₀ k (G.layerIndex x) x then siteWeight G x else 0) = 1 := by
  classical
  have h := decomp_blocks G (Finset.univ : Finset (G.Ω 1)) (fun _ => 1)
    (fun _ h => absurd (Finset.mem_univ _) h)
  have h1 := congrFun h i
  have hZ : Zplus G (Finset.univ : Finset (G.Ω 1)) = Finset.univ := by
    ext x
    simp [Zplus]
  rw [hZ, Finset.sum_apply] at h1
  simp only [Pi.smul_apply, blockProj, smul_eq_mul] at h1
  have h2 : ((∑ x : G.Ω 1, (if jBlock d L N₀ k (G.layerIndex x) (i : Torus d (N₀ * L ^ k)) =
      jBlock d L N₀ k (G.layerIndex x) x then siteWeight G x else 0) : ℝ) : ℂ) = 1 := by
    rw [h1]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  exact_mod_cast h2

omit [Fintype ι] in
/-- Every field is the weighted sum of its restrictions to the blocks `Δ(x)`, `x ∈ Ω₁`. -/
theorem decomp_field (s : ι → G.Ω 1) (g : ι → ℂ) :
    g = ∑ x : G.Ω 1, ((siteWeight G x : ℝ) : ℂ) • bproj G s (G.layerIndex x) x g := by
  funext p
  rw [Finset.sum_apply]
  have h := sum_siteWeight_indicator (s p)
  have h2 : ∑ x : G.Ω 1, (((siteWeight G x : ℝ) : ℂ) • bproj G s (G.layerIndex x) x g) p =
      ((∑ x : G.Ω 1, (if jBlock d L N₀ k (G.layerIndex x) (s p : Torus d (N₀ * L ^ k)) =
      jBlock d L N₀ k (G.layerIndex x) x then siteWeight G x else 0) : ℝ) : ℂ) * g p := by
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.smul_apply, bproj, smul_eq_mul]
    split_ifs <;> simp
  rw [h2, h]; simp

end BlockNorm

/-! ### The class `Dec` -/

section Dec

variable {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
variable (G : GeneratingSet d L N₀ k ϱ)

/-- The trivial tail. -/
def noTail : Torus d (N₀ * L ^ k) → Torus d (N₀ * L ^ k) → ℝ := fun _ _ => 1

/-- **Block decay of an operator** (GREEN.md §4.6): for `f` supported in the block `Δ_{j'}(y')`,
`‖χ_{Δ_j(y)} T f‖ ≤ C (ℓ_j ℓ_{j'})^w e^{-γ d(y,y')} τ(y,y') ‖f‖`. -/
def Dec (s₁ : ι₁ → G.Ω 1) (s₂ : ι₂ → G.Ω 1) (T : Matrix ι₁ ι₂ ℂ) (w : ℤ) (γ : ℝ)
    (τ : Torus d (N₀ * L ^ k) → Torus d (N₀ * L ^ k) → ℝ) (C : ℝ) : Prop :=
  ∀ (j j' : ℕ) (y y' : Torus d (N₀ * L ^ k)), 1 ≤ j → j ≤ k → 1 ≤ j' → j' ≤ k →
    y ∈ G.layer j → y' ∈ G.layer j' → ∀ f : ι₂ → ℂ,
      bn G s₁ j y (T *ᵥ bproj G s₂ j' y' f) ≤
        C * (((L : ℝ) ^ j * (L : ℝ) ^ j') ^ w) * decay γ (G.pathDist y y') * τ y y' *
          bn G s₂ j' y' f

variable {G}

theorem Dec.mono_rate {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {T : Matrix ι₁ ι₂ ℂ} {w : ℤ}
    {γ γ' : ℝ} {τ : Torus d (N₀ * L ^ k) → Torus d (N₀ * L ^ k) → ℝ} {C : ℝ}
    (hτ : ∀ y y', 0 ≤ τ y y') (hC : 0 ≤ C) (h : Dec G s₁ s₂ T w γ τ C) (hγ : γ' ≤ γ) :
    Dec G s₁ s₂ T w γ' τ C := by
  intro j j' y y' hj1 hjk hj'1 hj'k hy hy' f
  refine (h j j' y y' hj1 hjk hj'1 hj'k hy hy' f).trans ?_
  have := decay_anti_rate hγ (G.pathDist y y')
  have h0 : 0 ≤ C * ((L : ℝ) ^ j * (L : ℝ) ^ j') ^ w := by positivity
  have h1 : 0 ≤ τ y y' * bn G s₂ j' y' f := mul_nonneg (hτ _ _) (bn_nonneg _ _ _ _)
  calc _ = (C * ((L : ℝ) ^ j * (L : ℝ) ^ j') ^ w) * decay γ (G.pathDist y y') *
        (τ y y' * bn G s₂ j' y' f) := by ring
    _ ≤ (C * ((L : ℝ) ^ j * (L : ℝ) ^ j') ^ w) * decay γ' (G.pathDist y y') *
        (τ y y' * bn G s₂ j' y' f) := by gcongr
    _ = _ := by ring

theorem Dec.mono_const {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {T : Matrix ι₁ ι₂ ℂ} {w : ℤ}
    {γ : ℝ} {τ : Torus d (N₀ * L ^ k) → Torus d (N₀ * L ^ k) → ℝ} {C C' : ℝ}
    (hτ : ∀ y y', 0 ≤ τ y y') (h : Dec G s₁ s₂ T w γ τ C) (hC : C ≤ C') :
    Dec G s₁ s₂ T w γ τ C' := by
  intro j j' y y' hj1 hjk hj'1 hj'k hy hy' f
  refine (h j j' y y' hj1 hjk hj'1 hj'k hy hy' f).trans ?_
  have h1 : 0 ≤ ((L : ℝ) ^ j * (L : ℝ) ^ j') ^ w * decay γ (G.pathDist y y') * τ y y' *
      bn G s₂ j' y' f := by
    have := decay_nonneg γ (G.pathDist y y')
    have := hτ y y'
    have := bn_nonneg s₂ j' y' f
    positivity
  nlinarith [mul_le_mul_of_nonneg_right hC h1]

theorem Dec.add {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {T S : Matrix ι₁ ι₂ ℂ} {w : ℤ}
    {γ : ℝ} {τ : Torus d (N₀ * L ^ k) → Torus d (N₀ * L ^ k) → ℝ} {C C' : ℝ}
    (hT : Dec G s₁ s₂ T w γ τ C) (hS : Dec G s₁ s₂ S w γ τ C') :
    Dec G s₁ s₂ (T + S) w γ τ (C + C') := by
  intro j j' y y' hj1 hjk hj'1 hj'k hy hy' f
  have h1 := hT j j' y y' hj1 hjk hj'1 hj'k hy hy' f
  have h2 := hS j j' y y' hj1 hjk hj'1 hj'k hy hy' f
  have : bn G s₁ j y ((T + S) *ᵥ bproj G s₂ j' y' f) ≤
      bn G s₁ j y (T *ᵥ bproj G s₂ j' y' f) + bn G s₁ j y (S *ᵥ bproj G s₂ j' y' f) := by
    unfold bn
    rw [Matrix.add_mulVec, bproj_add]
    exact l2_add_le _ _
  nlinarith

theorem Dec.neg {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {T : Matrix ι₁ ι₂ ℂ} {w : ℤ}
    {γ : ℝ} {τ : Torus d (N₀ * L ^ k) → Torus d (N₀ * L ^ k) → ℝ} {C : ℝ}
    (hT : Dec G s₁ s₂ T w γ τ C) : Dec G s₁ s₂ (-T) w γ τ C := by
  intro j j' y y' hj1 hjk hj'1 hj'k hy hy' f
  have := hT j j' y y' hj1 hjk hj'1 hj'k hy hy' f
  have e : bn G s₁ j y ((-T) *ᵥ bproj G s₂ j' y' f) = bn G s₁ j y (T *ᵥ bproj G s₂ j' y' f) := by
    unfold bn
    rw [Matrix.neg_mulVec]
    refine le_antisymm (l2_mono fun p => ?_) (l2_mono fun p => ?_) <;>
      (simp only [bproj]; split_ifs <;> simp)
  rwa [e]

theorem Dec.sub {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {T S : Matrix ι₁ ι₂ ℂ} {w : ℤ}
    {γ : ℝ} {τ : Torus d (N₀ * L ^ k) → Torus d (N₀ * L ^ k) → ℝ} {C C' : ℝ}
    (hT : Dec G s₁ s₂ T w γ τ C) (hS : Dec G s₁ s₂ S w γ τ C') :
    Dec G s₁ s₂ (T - S) w γ τ (C + C') := by
  rw [sub_eq_add_neg]; exact hT.add hS.neg
theorem exp_bound_aux {κ p q m M : ℝ} (hκ : 0 ≤ κ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hm : 0 ≤ m)
    (hmM : m ≤ M) : m * (κ * p) ≤ κ * M * (p + q) := by
  have hM : 0 ≤ M := hm.trans hmM
  calc m * (κ * p) ≤ M * (κ * p) := mul_le_mul_of_nonneg_right hmM (by positivity)
    _ ≤ M * (κ * (p + q)) := by gcongr; linarith
    _ = κ * M * (p + q) := by ring

/-- The pointwise (one intermediate block) estimate of the composition lemma. -/
theorem comp_pointwise (hϱ : 1 < ϱ) {κ : ℝ} (hκ : Real.log L ≤ κ * (ϱ - 1)) {w w' : ℤ}
    {γ γ'' θ ρ B C₁ C₂ : ℝ}
    (hrate : γ'' + θ + ρ + κ * ((w.natAbs : ℝ) + w'.natAbs) ≤ γ) (hγ'' : 0 ≤ γ'')
    (hθ : 0 ≤ θ) {j jx j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hjx1 : 1 ≤ jx) (hjxk : jx ≤ k)
    (hj'1 : 1 ≤ j') (hj'k : j' ≤ k) {y x y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j)
    (hx : x ∈ G.layer jx) (hy' : y' ∈ G.layer j') {t₁ t₂ τv : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (hτv : 0 ≤ τv)
    (hcompat : G.pathDist y x ≠ ⊤ → G.pathDist x y' ≠ ⊤ →
      t₁ * t₂ ≤ B * τv * Real.exp (ρ * ((G.pathDist y x).toReal + (G.pathDist x y').toReal)))
    {ωx : ℝ} (hω : 0 ≤ ωx) {b : ℝ} (hb : 0 ≤ b) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hB : 0 ≤ B) :
    ωx * (C₁ * ((((L : ℝ) ^ j) * ((L : ℝ) ^ jx)) ^ w) * decay γ (G.pathDist y x) * t₁) *
        (C₂ * ((((L : ℝ) ^ jx) * ((L : ℝ) ^ j')) ^ w') * decay γ (G.pathDist x y') * t₂ * b) ≤
      (C₁ * C₂ * B * (L : ℝ) ^ (w.natAbs + w'.natAbs)) * ((((L : ℝ) ^ j) * ((L : ℝ) ^ j')) ^ (w + w')) *
        decay γ'' (G.pathDist y y') * τv * b * (ωx * decay θ (G.pathDist y x)) := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have ha : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hbx : (0 : ℝ) < (L : ℝ) ^ jx := by positivity
  have hc : (0 : ℝ) < (L : ℝ) ^ j' := by positivity
  -- nonnegativity of the right side
  have hR0 : 0 ≤ (C₁ * C₂ * B * (L : ℝ) ^ (w.natAbs + w'.natAbs)) *
      ((((L : ℝ) ^ j) * ((L : ℝ) ^ j')) ^ (w + w')) * decay γ'' (G.pathDist y y') * τv * b *
        (ωx * decay θ (G.pathDist y x)) := by
    have := decay_nonneg γ'' (G.pathDist y y')
    have := decay_nonneg θ (G.pathDist y x)
    positivity
  by_cases hp : G.pathDist y x = ⊤
  · refine le_trans (le_of_eq ?_) hR0; rw [hp, decay_top]; ring
  by_cases hq : G.pathDist x y' = ⊤
  · refine le_trans (le_of_eq ?_) hR0; rw [hq, decay_top]; ring
  set p := (G.pathDist y x).toReal with hpdef
  set q := (G.pathDist x y').toReal with hqdef
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hsum : G.pathDist y y' ≤ G.pathDist y x + G.pathDist x y' := G.pathDist_triangle y x y'
  have hsumne : G.pathDist y x + G.pathDist x y' ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hp, hq⟩
  have hDne : G.pathDist y y' ≠ ⊤ := ne_top_of_le_ne_top hsumne hsum
  set D := (G.pathDist y y').toReal with hDdef
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  have hDle : D ≤ p + q := by
    have := ENNReal.toReal_mono hsumne hsum
    rwa [ENNReal.toReal_add hp hq] at this
  -- the scale mismatch
  have hr₁ := spacing_ratio_le G hϱ hκ hj1 hjk hjx1 hjxk hy hx hp
  have hr₁' := spacing_ratio_le G hϱ hκ hjx1 hjxk hj1 hjk hx hy (by
    rw [GeneratingSet.pathDist_comm]; exact hp)
  have hr₂ := spacing_ratio_le G hϱ hκ hjx1 hjxk hj'1 hj'k hx hy' hq
  have hr₂' := spacing_ratio_le G hϱ hκ hj'1 hj'k hjx1 hjxk hy' hx (by
    rw [GeneratingSet.pathDist_comm]; exact hq)
  rw [GeneratingSet.pathDist_comm x y] at hr₁'
  rw [GeneratingSet.pathDist_comm y' x] at hr₂'
  have hκ0 : 0 ≤ κ := by
    by_contra h
    push Not at h
    have := Real.log_nonneg hL
    nlinarith
  have hexp1 : (1 : ℝ) ≤ Real.exp (κ * p) := Real.one_le_exp (by positivity)
  have hexp2 : (1 : ℝ) ≤ Real.exp (κ * q) := Real.one_le_exp (by positivity)
  have hsc := scale_comp (a := (L : ℝ) ^ j) (b := (L : ℝ) ^ jx) (c := (L : ℝ) ^ j')
    (r₁ := L * Real.exp (κ * p)) (r₂ := L * Real.exp (κ * q)) ha hbx hc
    (by nlinarith) (by nlinarith) hr₁ hr₁' hr₂' hr₂ w w'
  -- rewrite the left side
  have hE : (((L : ℝ) ^ j * (L : ℝ) ^ jx) ^ w) * (((L : ℝ) ^ jx * (L : ℝ) ^ j') ^ w') =
      ((L : ℝ) ^ j) ^ w * ((L : ℝ) ^ jx) ^ (w + w') * ((L : ℝ) ^ j') ^ w' := by
    rw [mul_zpow, mul_zpow, zpow_add₀ hbx.ne']; ring
  -- the power of `L e^{κ p}`
  have hpow1 : (L * Real.exp (κ * p)) ^ w'.natAbs =
      (L : ℝ) ^ w'.natAbs * Real.exp ((w'.natAbs : ℝ) * (κ * p)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
  have hpow2 : (L * Real.exp (κ * q)) ^ w.natAbs =
      (L : ℝ) ^ w.natAbs * Real.exp ((w.natAbs : ℝ) * (κ * q)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
  set μ : ℝ := (w.natAbs : ℝ) + w'.natAbs with hμ
  have hμ1 : (w'.natAbs : ℝ) ≤ μ := by
    rw [hμ]; linarith [(Nat.cast_nonneg w.natAbs : (0 : ℝ) ≤ w.natAbs)]
  have hμ2 : (w.natAbs : ℝ) ≤ μ := by
    rw [hμ]; linarith [(Nat.cast_nonneg w'.natAbs : (0 : ℝ) ≤ w'.natAbs)]
  have hexp3 : Real.exp ((w'.natAbs : ℝ) * (κ * p)) * Real.exp ((w.natAbs : ℝ) * (κ * q)) ≤
      Real.exp (κ * μ * (p + q)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : (w'.natAbs : ℝ) * (κ * p) ≤ μ * (κ * p) :=
      mul_le_mul_of_nonneg_right hμ1 (by positivity)
    have h2 : (w.natAbs : ℝ) * (κ * q) ≤ μ * (κ * q) :=
      mul_le_mul_of_nonneg_right hμ2 (by positivity)
    linarith
  have hQ : 0 < (((L : ℝ) ^ j) * ((L : ℝ) ^ j')) ^ (w + w') := by positivity
  have hscale : (((L : ℝ) ^ j * (L : ℝ) ^ jx) ^ w) * (((L : ℝ) ^ jx * (L : ℝ) ^ j') ^ w') ≤
      (L : ℝ) ^ (w.natAbs + w'.natAbs) * Real.exp (κ * μ * (p + q)) *
        (((L : ℝ) ^ j) * ((L : ℝ) ^ j')) ^ (w + w') := by
    rw [hE]
    refine hsc.trans ?_
    rw [hpow1, hpow2]
    calc (L : ℝ) ^ w'.natAbs * Real.exp ((w'.natAbs : ℝ) * (κ * p)) *
          ((L : ℝ) ^ w.natAbs * Real.exp ((w.natAbs : ℝ) * (κ * q))) *
          (((L : ℝ) ^ j) * ((L : ℝ) ^ j')) ^ (w + w')
        = (L : ℝ) ^ (w.natAbs + w'.natAbs) *
          (Real.exp ((w'.natAbs : ℝ) * (κ * p)) * Real.exp ((w.natAbs : ℝ) * (κ * q))) *
          (((L : ℝ) ^ j) * ((L : ℝ) ^ j')) ^ (w + w') := by rw [pow_add]; ring
      _ ≤ _ := by gcongr
  have hdp : decay γ (G.pathDist y x) = Real.exp (-(γ * p)) := decay_of_ne_top hp
  have hdq : decay γ (G.pathDist x y') = Real.exp (-(γ * q)) := decay_of_ne_top hq
  have hdD : decay γ'' (G.pathDist y y') = Real.exp (-(γ'' * D)) := decay_of_ne_top hDne
  have hdθ : decay θ (G.pathDist y x) = Real.exp (-(θ * p)) := decay_of_ne_top hp
  rw [hdp, hdq, hdD, hdθ]
  have hcomp := hcompat hp hq
  have hexp : Real.exp (-(γ * p)) * Real.exp (-(γ * q)) * Real.exp (κ * μ * (p + q)) *
      Real.exp (ρ * (p + q)) ≤ Real.exp (-(γ'' * D)) * Real.exp (-(θ * p)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : (γ'' + θ + ρ + κ * μ) * (p + q) ≤ γ * (p + q) :=
      mul_le_mul_of_nonneg_right hrate (by positivity)
    have h2 : γ'' * D ≤ γ'' * (p + q) := mul_le_mul_of_nonneg_left hDle hγ''
    have h3 : θ * p ≤ θ * (p + q) := mul_le_mul_of_nonneg_left (by linarith) hθ
    linarith
  set Q := (((L : ℝ) ^ j) * ((L : ℝ) ^ j')) ^ (w + w') with hQdef
  set X := (((L : ℝ) ^ j * (L : ℝ) ^ jx) ^ w) * (((L : ℝ) ^ jx * (L : ℝ) ^ j') ^ w') with hX
  set e1 := Real.exp (-(γ * p))
  set e2 := Real.exp (-(γ * q))
  set Eκ := Real.exp (κ * μ * (p + q))
  set Eρ := Real.exp (ρ * (p + q))
  have he1 : 0 < e1 := Real.exp_pos _
  have he2 : 0 < e2 := Real.exp_pos _
  have hEκ : 0 < Eκ := Real.exp_pos _
  have hEρ : 0 < Eρ := Real.exp_pos _
  have hX0 : 0 ≤ X := by positivity
  have h1 : X * (t₁ * t₂) ≤ ((L : ℝ) ^ (w.natAbs + w'.natAbs) * Eκ * Q) * (B * τv * Eρ) :=
    mul_le_mul hscale hcomp (mul_nonneg ht₁ ht₂) (by positivity)
  have hLn : (0 : ℝ) < (L : ℝ) ^ (w.natAbs + w'.natAbs) := by positivity
  have hpre : 0 ≤ ωx * C₁ * C₂ * b := by positivity
  calc ωx * (C₁ * (((L : ℝ) ^ j * (L : ℝ) ^ jx) ^ w) * e1 * t₁) *
        (C₂ * (((L : ℝ) ^ jx * (L : ℝ) ^ j') ^ w') * e2 * t₂ * b)
      = (ωx * C₁ * C₂ * b) * ((X * (t₁ * t₂)) * (e1 * e2)) := by rw [hX]; ring
    _ ≤ (ωx * C₁ * C₂ * b) * (((L : ℝ) ^ (w.natAbs + w'.natAbs) * Eκ * Q) * (B * τv * Eρ) *
          (e1 * e2)) := by gcongr
    _ = (ωx * C₁ * C₂ * b) * ((L : ℝ) ^ (w.natAbs + w'.natAbs) * Q * B * τv) *
          (e1 * e2 * Eκ * Eρ) := by ring
    _ ≤ (ωx * C₁ * C₂ * b) * ((L : ℝ) ^ (w.natAbs + w'.natAbs) * Q * B * τv) *
          (Real.exp (-(γ'' * D)) * Real.exp (-(θ * p))) := by gcongr
    _ = _ := by ring


/-- **Composition** (the summation Lemma 4.4 with the scale mismatch absorbed).  If `T ∈ Dec w γ τ₁`
and `S ∈ Dec w' γ τ₂`, the tails are compatible (`τ₁(y,x) τ₂(x,y') ≤ B τ(y,y') e^{ρ(d(y,x)+d(x,y'))}`
for the intermediate sites `x` with `P x`), and the intermediate blocks with `¬ P x` do not
contribute, then `T S ∈ Dec (w + w') γ'' τ`, with `γ'' + θ + ρ + κ(|w| + |w'|) ≤ γ`, where
`log L ≤ κ (ϱ - 1)` and `2 d log L ≤ (θ/2)(ϱ - 1)` (so `ϱ` is large). -/
theorem Dec.comp {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {s₃ : ι₃ → G.Ω 1}
    {T : Matrix ι₁ ι₂ ℂ} {S : Matrix ι₂ ι₃ ℂ} {w w' : ℤ} {γ γ'' θ ρ κ B C₁ C₂ : ℝ}
    {τ₁ τ₂ τ : Torus d (N₀ * L ^ k) → Torus d (N₀ * L ^ k) → ℝ}
    (hϱ : 1 < ϱ) (hκ : Real.log L ≤ κ * (ϱ - 1)) (hθ : 0 < θ)
    (hcount : 2 * d * Real.log L ≤ θ / 2 * (ϱ - 1))
    (hrate : γ'' + θ + ρ + κ * ((w.natAbs : ℝ) + w'.natAbs) ≤ γ) (hγ'' : 0 ≤ γ'')
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hB : 0 ≤ B) (hτ₁ : ∀ y y', 0 ≤ τ₁ y y')
    (hτ₂ : ∀ y y', 0 ≤ τ₂ y y') (hτ : ∀ y y', 0 ≤ τ y y')
    (P : G.Ω 1 → Prop)
    (hP : ∀ (j' : ℕ) (y' : Torus d (N₀ * L ^ k)) (f : ι₃ → ℂ) (x : G.Ω 1), ¬ P x →
      bn G s₂ (G.layerIndex x) x (S *ᵥ bproj G s₃ j' y' f) = 0)
    (hcompat : ∀ (y y' : Torus d (N₀ * L ^ k)) (x : G.Ω 1), P x → G.pathDist y x ≠ ⊤ →
      G.pathDist x y' ≠ ⊤ → τ₁ y x * τ₂ x y' ≤
        B * τ y y' * Real.exp (ρ * ((G.pathDist y x).toReal + (G.pathDist x y').toReal)))
    (hT : Dec G s₁ s₂ T w γ τ₁ C₁) (hS : Dec G s₂ s₃ S w' γ τ₂ C₂) :
    Dec G s₁ s₃ (T * S) (w + w') γ'' τ
      (C₁ * C₂ * B * (L : ℝ) ^ (w.natAbs + w'.natAbs) * countConst d L θ) := by
  intro j j' y y' hj1 hjk hj'1 hj'k hy hy' f
  have hyΩ : y ∈ G.Ω 1 := G.layer_subset hj1 hjk hy
  set F := bproj G s₃ j' y' f with hF
  set u := S *ᵥ F with hu
  set b := bn G s₃ j' y' f with hb
  have hb0 : 0 ≤ b := bn_nonneg _ _ _ _
  rw [← Matrix.mulVec_mulVec]
  have hdec : T *ᵥ u = ∑ x : G.Ω 1, ((siteWeight G x : ℝ) : ℂ) •
      (T *ᵥ bproj G s₂ (G.layerIndex x) x u) := by
    conv_lhs => rw [decomp_field s₂ u]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.mulVec_smul]
  rw [hdec]
  have hsumle := bn_sum_le s₁ j y (Finset.univ : Finset (G.Ω 1))
    (fun x => siteWeight G (x : Torus d (N₀ * L ^ k))) (fun x => siteWeight_nonneg G _)
    (fun x => T *ᵥ bproj G s₂ (G.layerIndex x) x u)
  refine hsumle.trans ?_
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (C₁ * C₂ * B * (L : ℝ) ^ (w.natAbs + w'.natAbs)) *
    (((L : ℝ) ^ j * (L : ℝ) ^ j') ^ (w + w')) * decay γ'' (G.pathDist y y') * τ y y' * b :=
    ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 := decay_nonneg γ'' (G.pathDist y y')
    have h2 := hτ y y'
    have h3 : (0 : ℝ) < ((L : ℝ) ^ j * (L : ℝ) ^ j') ^ (w + w') := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    have h4 : 0 ≤ C₁ * C₂ * B * (L : ℝ) ^ (w.natAbs + w'.natAbs) := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h4 h3.le) h1) h2) hb0
  have hterm : ∀ x : G.Ω 1, siteWeight G (x : Torus d (N₀ * L ^ k)) *
      bn G s₁ j y (T *ᵥ bproj G s₂ (G.layerIndex x) x u) ≤
      K * (siteWeight G (x : Torus d (N₀ * L ^ k)) * decay θ (G.pathDist y x)) := by
    intro x
    obtain ⟨hjx1, hjxk, hxl⟩ := G.layerIndex_spec x.2
    have hω := siteWeight_nonneg G (x : Torus d (N₀ * L ^ k))
    by_cases hPx : P x
    · have h1 := hT j (G.layerIndex x) y x hj1 hjk hjx1 hjxk hy hxl (u)
      have h2 := hS (G.layerIndex x) j' x y' hjx1 hjxk hj'1 hj'k hxl hy' f
      rw [← hF, ← hu, ← hb] at h2
      have hd1 := decay_nonneg γ (G.pathDist y x)
      have hd2 := decay_nonneg γ (G.pathDist x y')
      have ht1 := hτ₁ y x
      have ht2 := hτ₂ x y'
      have hpre : 0 ≤ C₁ * (((L : ℝ) ^ j * (L : ℝ) ^ (G.layerIndex x)) ^ w) *
          decay γ (G.pathDist y x) * τ₁ y x := by
        have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
        positivity
      have h3 := mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hpre)) hω
      refine h3.trans ?_
      have := comp_pointwise hϱ hκ hrate hγ'' hθ.le hj1 hjk hjx1 hjxk hj'1 hj'k hy hxl hy'
        (hτ₁ y x) (hτ₂ x y') (hτ y y') (hcompat y y' x hPx) hω hb0 hC₁ hC₂ hB
      refine le_of_eq_of_le (by ring) (this.trans (le_of_eq ?_))
      rw [hK]
    · have h0 : bn G s₂ (G.layerIndex x) x u = 0 := hP j' y' f x hPx
      have h1 := hT j (G.layerIndex x) y x hj1 hjk hjx1 hjxk hy hxl u
      rw [h0, mul_zero] at h1
      have h2 : bn G s₁ j y (T *ᵥ bproj G s₂ (G.layerIndex x) x u) = 0 :=
        le_antisymm h1 (bn_nonneg _ _ _ _)
      rw [h2, mul_zero]
      have := decay_nonneg θ (G.pathDist y x)
      exact mul_nonneg hK0 (mul_nonneg hω this)
  refine (Finset.sum_le_sum fun x _ => hterm x).trans ?_
  rw [← Finset.mul_sum]
  have hsum := sum_siteWeight_decay_le G hϱ hθ hcount hyΩ
  calc K * ∑ x : G.Ω 1, siteWeight G (x : Torus d (N₀ * L ^ k)) * decay θ (G.pathDist y x)
      ≤ K * countConst d L θ := mul_le_mul_of_nonneg_left hsum hK0
    _ = _ := by rw [hK]; ring

/-- Two blocks that share a site of `Ω₁` lie in the same layer and at distance `≤ 4 d`. -/
theorem blocks_meet {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j') {z : G.Ω 1}
    (hz : jBlock d L N₀ k j (z : Torus d (N₀ * L ^ k)) = jBlock d L N₀ k j y)
    (hz' : jBlock d L N₀ k j' (z : Torus d (N₀ * L ^ k)) = jBlock d L N₀ k j' y') :
    j = j' ∧ G.pathDist y y' ≤ ENNReal.ofReal (4 * d) := by
  have hzl : (z : Torus d (N₀ * L ^ k)) ∈ G.layer j := (G.mem_layer_iff hj1 hjk hz).2 hy
  have hzl' : (z : Torus d (N₀ * L ^ k)) ∈ G.layer j' := (G.mem_layer_iff hj'1 hj'k hz').2 hy'
  have hjj : j = j' := by
    by_contra hne
    exact G.layer_disjoint hj1 hjk hj'1 hj'k hne hzl hzl'
  subst hjj
  refine ⟨rfl, ?_⟩
  have h1 := G.pathDist_block_le hj1 hjk hy hz
  have h2 := G.pathDist_block_le hj1 hjk hy' hz'
  rw [GeneratingSet.pathDist_comm] at h2
  refine (G.pathDist_triangle y z y').trans ?_
  calc G.pathDist y z + G.pathDist z y' ≤ ENNReal.ofReal (2 * d) + ENNReal.ofReal (2 * d) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (4 * d) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- An operator that does not increase block norms (blockwise, with the scale `(ℓ_j²)^w`) lies in
`Dec w γ 1` for every `γ ≥ 0`: blocks that do not meet are not seen, and blocks that meet are within
distance `4 d`. -/
theorem Dec.of_blockwise {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {T : Matrix ι₁ ι₂ ℂ} {w : ℤ}
    {c γ : ℝ} (hc : 0 ≤ c) (hγ : 0 ≤ γ)
    (hT : ∀ (j : ℕ) (y : Torus d (N₀ * L ^ k)), 1 ≤ j → j ≤ k → y ∈ G.layer j → ∀ f : ι₂ → ℂ,
      bn G s₁ j y (T *ᵥ f) ≤ c * (((L : ℝ) ^ j * (L : ℝ) ^ j) ^ w) * bn G s₂ j y f) :
    Dec G s₁ s₂ T w γ noTail (c * Real.exp (γ * (4 * d))) := by
  intro j j' y y' hj1 hjk hj'1 hj'k hy hy' f
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hR0 : 0 ≤ c * Real.exp (γ * (4 * d)) * (((L : ℝ) ^ j * (L : ℝ) ^ j') ^ w) *
      decay γ (G.pathDist y y') * noTail y y' * bn G s₂ j' y' f := by
    have := decay_nonneg γ (G.pathDist y y')
    have := bn_nonneg s₂ j' y' f
    unfold noTail
    positivity
  set F := bproj G s₂ j' y' f with hF
  by_cases h0 : bn G s₁ j y (T *ᵥ F) = 0
  · rw [h0]; exact hR0
  have h1 := hT j y hj1 hjk hy F
  have hne : bn G s₂ j y F ≠ 0 := by
    intro h
    rw [h, mul_zero] at h1
    exact h0 (le_antisymm h1 (bn_nonneg _ _ _ _))
  obtain ⟨p, hp⟩ := exists_ne_of_l2_ne hne
  have hpj : jBlock d L N₀ k j (s₂ p : Torus d (N₀ * L ^ k)) = jBlock d L N₀ k j y := by
    by_contra h; simp [bproj, h] at hp
  have hpF : F p ≠ 0 := by
    intro h; simp [bproj, h] at hp
  have hpj' : jBlock d L N₀ k j' (s₂ p : Torus d (N₀ * L ^ k)) = jBlock d L N₀ k j' y' := by
    by_contra h; simp [hF, bproj, h] at hpF
  obtain ⟨hjj, hdist⟩ := blocks_meet hj1 hjk hj'1 hj'k hy hy' hpj hpj'
  subst hjj
  have hdec := decay_ofReal_ge hγ (by positivity : (0 : ℝ) ≤ 4 * d) hdist
  have hexp : 1 ≤ Real.exp (γ * (4 * d)) * decay γ (G.pathDist y y') := by
    calc (1 : ℝ) = Real.exp (γ * (4 * d)) * Real.exp (-(γ * (4 * d))) := by
          rw [← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hdec (Real.exp_pos _).le
  have hb : bn G s₂ j y F ≤ bn G s₂ j y' f := bn_bproj_le s₂ j j y y' f
  have hsc : 0 ≤ c * (((L : ℝ) ^ j * (L : ℝ) ^ j) ^ w) := by positivity
  have hb0 := bn_nonneg s₂ j y' f
  calc bn G s₁ j y (T *ᵥ F) ≤ c * (((L : ℝ) ^ j * (L : ℝ) ^ j) ^ w) * bn G s₂ j y F := h1
    _ ≤ c * (((L : ℝ) ^ j * (L : ℝ) ^ j) ^ w) * bn G s₂ j y' f :=
        mul_le_mul_of_nonneg_left hb hsc
    _ ≤ c * (((L : ℝ) ^ j * (L : ℝ) ^ j) ^ w) * (Real.exp (γ * (4 * d)) *
          decay γ (G.pathDist y y')) * bn G s₂ j y' f := by
        have := mul_le_mul_of_nonneg_left hexp hsc
        nlinarith [mul_le_mul_of_nonneg_right this hb0]
    _ = _ := by unfold noTail; ring

/-- Conversion of the one-sided form `ℓ_j^{2w-b} ℓ_{j'}^b` (the form produced by the Agmon
estimates) to the symmetric form `(ℓ_j ℓ_{j'})^w` at the price of `κ |b - w|` in the rate. -/
theorem Dec.of_one_sided {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {T : Matrix ι₁ ι₂ ℂ} {w b : ℤ}
    {A γ₀ κ : ℝ} (hϱ : 1 < ϱ) (hκ : Real.log L ≤ κ * (ϱ - 1)) (hA : 0 ≤ A)
    (hT : ∀ (j j' : ℕ) (y y' : Torus d (N₀ * L ^ k)), 1 ≤ j → j ≤ k → 1 ≤ j' → j' ≤ k →
      y ∈ G.layer j → y' ∈ G.layer j' → ∀ f : ι₂ → ℂ,
        bn G s₁ j y (T *ᵥ bproj G s₂ j' y' f) ≤
          A * (((L : ℝ) ^ j) ^ (2 * w - b) * ((L : ℝ) ^ j') ^ b) * decay γ₀ (G.pathDist y y') *
            bn G s₂ j' y' f) :
    Dec G s₁ s₂ T w (γ₀ - κ * ((b - w).natAbs : ℝ)) noTail (A * (L : ℝ) ^ (b - w).natAbs) := by
  intro j j' y y' hj1 hjk hj'1 hj'k hy hy' f
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have ha : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hc : (0 : ℝ) < (L : ℝ) ^ j' := by positivity
  have hb0 := bn_nonneg s₂ j' y' f
  have h1 := hT j j' y y' hj1 hjk hj'1 hj'k hy hy' f
  have hR0 : 0 ≤ A * (L : ℝ) ^ (b - w).natAbs * (((L : ℝ) ^ j * (L : ℝ) ^ j') ^ w) *
      decay (γ₀ - κ * ((b - w).natAbs : ℝ)) (G.pathDist y y') * noTail y y' *
        bn G s₂ j' y' f := by
    have := decay_nonneg (γ₀ - κ * ((b - w).natAbs : ℝ)) (G.pathDist y y')
    unfold noTail
    positivity
  by_cases hD : G.pathDist y y' = ⊤
  · rw [hD, decay_top] at h1
    refine h1.trans ?_
    rw [hD, decay_top]
    simp
  have hκ0 : 0 ≤ κ := by
    by_contra h
    push Not at h
    have := Real.log_nonneg hL
    nlinarith
  set Dr := (G.pathDist y y').toReal with hDr
  have hr1 := spacing_ratio_le G hϱ hκ hj1 hjk hj'1 hj'k hy hy' hD
  have hr2 := spacing_ratio_le G hϱ hκ hj'1 hj'k hj1 hjk hy' hy (by
    rw [GeneratingSet.pathDist_comm]; exact hD)
  rw [GeneratingSet.pathDist_comm y' y] at hr2
  have hE1 : (1 : ℝ) ≤ Real.exp (κ * Dr) := Real.one_le_exp (by positivity)
  have hratio := zpow_div_le (a := (L : ℝ) ^ j') (b := (L : ℝ) ^ j) (r := L * Real.exp (κ * Dr))
    hc ha (by nlinarith) hr1 hr2 (b - w)
  have hid : ((L : ℝ) ^ j) ^ (2 * w - b) * ((L : ℝ) ^ j') ^ b =
      ((L : ℝ) ^ j * (L : ℝ) ^ j') ^ w * (((L : ℝ) ^ j') / ((L : ℝ) ^ j)) ^ (b - w) := by
    rw [mul_zpow, div_zpow]
    have e1 : ((L : ℝ) ^ j) ^ (2 * w - b) = ((L : ℝ) ^ j) ^ w * ((L : ℝ) ^ j) ^ (w - b) := by
      rw [← zpow_add₀ ha.ne']; congr 1; ring
    have e2 : ((L : ℝ) ^ j') ^ b = ((L : ℝ) ^ j') ^ w * ((L : ℝ) ^ j') ^ (b - w) := by
      rw [← zpow_add₀ hc.ne']; congr 1; ring
    have e3 : ((L : ℝ) ^ j) ^ (w - b) = (((L : ℝ) ^ j) ^ (b - w))⁻¹ := by
      rw [← _root_.zpow_neg]; congr 1; ring
    rw [e1, e2, e3]
    have : ((L : ℝ) ^ j) ^ (b - w) ≠ 0 := zpow_ne_zero _ ha.ne'
    field_simp
  rw [hid] at h1
  have hpow : (L * Real.exp (κ * Dr)) ^ (b - w).natAbs =
      (L : ℝ) ^ (b - w).natAbs * Real.exp (((b - w).natAbs : ℝ) * (κ * Dr)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
  have hdec : decay γ₀ (G.pathDist y y') * Real.exp (((b - w).natAbs : ℝ) * (κ * Dr)) =
      decay (γ₀ - κ * ((b - w).natAbs : ℝ)) (G.pathDist y y') := by
    rw [decay_of_ne_top hD, decay_of_ne_top hD, ← Real.exp_add]; congr 1; ring
  have hQ : 0 ≤ ((L : ℝ) ^ j * (L : ℝ) ^ j') ^ w := by positivity
  have hdn := decay_nonneg γ₀ (G.pathDist y y')
  calc _ ≤ A * (((L : ℝ) ^ j * (L : ℝ) ^ j') ^ w * (((L : ℝ) ^ j') / ((L : ℝ) ^ j)) ^ (b - w)) *
        decay γ₀ (G.pathDist y y') * bn G s₂ j' y' f := h1
    _ ≤ A * (((L : ℝ) ^ j * (L : ℝ) ^ j') ^ w * (L * Real.exp (κ * Dr)) ^ (b - w).natAbs) *
        decay γ₀ (G.pathDist y y') * bn G s₂ j' y' f := by gcongr
    _ = A * (L : ℝ) ^ (b - w).natAbs * (((L : ℝ) ^ j * (L : ℝ) ^ j') ^ w) *
        (decay γ₀ (G.pathDist y y') * Real.exp (((b - w).natAbs : ℝ) * (κ * Dr))) * noTail y y' *
          bn G s₂ j' y' f := by rw [hpow]; unfold noTail; ring
    _ = _ := by rw [hdec]

end Dec

end Balaban.Multiscale
