/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseSmallField

/-!
# The physical base carrier in product form (obligation D4)

LFR Definition II.7.6 and Lemma II.7.7, (II.7.4): the base kernel is
`K₀ = ∏ z₁^N t₀ · ∑_w F^w₀(u) K̃^w₀` with **one** boundary exponent `b₀(Z')` for all the Gaussian
witnesses `w`: the witness selects only source-free indicator factors (`F^w₀`, the `(1 - B_c)` of
the `bd` cubes), while the source and the small-field terms with domains in `Z'` sit in `b₀`. So
the physical carrier has the product form
`Kphys^w(g) = Kt^w · exp(b(g))`, with `Kt^w ≥ 0` source-free and `b` independent of `w`.

* `BaseProductData`: the properties of `Kt` and `b`; `baseProductData_nonempty`: the zero member
  (rule 10);
* `BaseProductData.toInput`: the carrier `BaseSmallFieldInput` with `Kphys := Kt · exp b`, every
  field proved from the properties;
* `Kphys_cross`: obligation D4, `Kphys^w(g) Kphys^{w'}(0) = Kphys^{w'}(g) Kphys^w(0)`;
* `baseKC_toInput`: `baseKC = baseK0 · exp(b(g) - b(0))` everywhere, so the scale-`0` kernel has the
  total analytic boundary factor `b(g) - b(0)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory ENNReal

section Sums

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- A factor independent of the witness comes out of the complex witness sum. -/
theorem baseSumC_mul_const (cs : OpConsts) (a : LocalHistory S n M K)
    (Kt : BaseW a 0 → OutT N R a (0 + 1) → NewCfg N a 0 → EuclideanSpace ℝ (Fin N) → ℝ)
    (c : OutT N R a (0 + 1) → NewCfg N a 0 → EuclideanSpace ℝ (Fin N) → ℂ)
    (o : OutT N R a (0 + 1)) (x : NewCfg N a 0) (hv : EuclideanSpace ℝ (Fin N)) :
    baseSumC cs a (fun w o x hv => (Kt w o x hv : ℂ) * c o x hv) o x hv =
      (baseSumOf cs a Kt o x hv : ℂ) * c o x hv := by
  classical
  unfold baseSumC baseSumOf
  push_cast
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun w _ => by ring

/-- A factor independent of the witness comes out of the real witness sum. -/
theorem baseSumOf_mul_const (cs : OpConsts) (a : LocalHistory S n M K)
    (Kt : BaseW a 0 → OutT N R a (0 + 1) → NewCfg N a 0 → EuclideanSpace ℝ (Fin N) → ℝ)
    (c : OutT N R a (0 + 1) → NewCfg N a 0 → EuclideanSpace ℝ (Fin N) → ℝ)
    (o : OutT N R a (0 + 1)) (x : NewCfg N a 0) (hv : EuclideanSpace ℝ (Fin N)) :
    baseSumOf cs a (fun w o x hv => Kt w o x hv * c o x hv) o x hv =
      baseSumOf cs a Kt o x hv * c o x hv := by
  classical
  unfold baseSumOf
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun w _ => by ring

end Sums

section Product

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} [NeZero S.L] {N : ℕ}
  {M K : ℕ} [NeZero M]

variable (M K) in
/-- **The product form of the physical base carrier** (LFR (II.7.4); BASECARRIER obligation D4):
the source-free real factors `Kt^w ≥ 0` and the one boundary exponent `b` of all the witnesses. -/
structure BaseProductData (k0 : ℕ) (geo : Geo S n R M) (cs : OpConsts) (N : ℕ) where
  /-- the source-free real factors `K̃^w_0` (before the exponent), indexed by the localized history
  (S4) -/
  Kt : ∀ (a : LocalHistory S n M K), BaseW a 0 → OutT N R a 1 → NewCfg N a 0 →
    EuclideanSpace ℝ (Fin N) → ℝ
  /-- the boundary exponent `b₀`, the same for all witnesses -/
  b : ∀ (a : LocalHistory S n M K), (GIdx S n M K N → ℂ) → OutT N R a 1 → NewCfg N a 0 →
    EuclideanSpace ℝ (Fin N) → ℂ
  Kt_nonneg : ∀ a w o x hv, 0 ≤ Kt a w o x hv
  Kt_meas : ∀ (a : LocalHistory S n M K) (w : BaseW a 0) (hv : EuclideanSpace ℝ (Fin N)),
    Measurable fun p : OutT N R a 1 × NewCfg N a 0 => Kt a w p.1 p.2 hv
  Kt_outside : ∀ (a : LocalHistory S n M K) (w : BaseW a 0) (o o' : OutT N R a 1)
    (x : NewCfg N a 0) (hv : EuclideanSpace ℝ (Fin N)),
    (∀ y : Vblk R a (0 + 1), y.1 ∉ gaussBlocks a 0 → o y = o' y) → Kt a w o x hv = Kt a w o' x hv
  /-- `K̃^w_0` vanishes off `χ^new_0` -/
  Kt_dom : ∀ (H : RegionHistory S n R k0 K) (_ : H.Admissible) (Z' : H.Comp 1)
    (w : BaseW (H.localHistory M K 1 Z') 0) (o : OutT N R (H.localHistory M K 1 Z') 1)
    (x : NewCfg N (H.localHistory M K 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N)),
    ¬ ChiNewAt geo cs H 0 Z' o x → Kt (H.localHistory M K 1 Z') w o x hv = 0
  Kt_rot : ∀ (a : LocalHistory S n M K) (w : BaseW a 0) (ρ : OrthN N) (o : OutT N R a 1)
    (x : NewCfg N a 0) (hv : EuclideanSpace ℝ (Fin N)),
    Kt a w (rotOut ρ o) (rotSub ρ x) (ρ hv) = Kt a w o x hv
  /-- Euclidean covariance of `∏ z₁^N t₀ · ∑_w F^w₀ K̃^w₀` (the witness sum) -/
  euclid_Kt : ∀ (σ : TorusSym S n M K) (a a' : LocalHistory S n M K) (hI : HistImage σ a a')
    (hk : 0 + 1 ≤ K) (o : OutT N R a 1) (o' : OutT N R a' 1) (x : NewCfg N a 0)
    (x' : NewCfg N a' 0) (hv : EuclideanSpace ℝ (Fin N)),
    RelOut σ o o' → RelSub hI hk x x' →
      gaussProd N a' 0 cs o' x' * baseSumOf cs a' (fun w => Kt a' w) o' x' hv =
        gaussProd N a 0 cs o x * baseSumOf cs a (fun w => Kt a w) o x hv
  b_meas : ∀ (a : LocalHistory S n M K) (g : GIdx S n M K N → ℂ) (hv : EuclideanSpace ℝ (Fin N)),
    Measurable fun p : OutT N R a 1 × NewCfg N a 0 => b a g p.1 p.2 hv
  b_outside : ∀ (a : LocalHistory S n M K) (g : GIdx S n M K N → ℂ) (o o' : OutT N R a 1)
    (x : NewCfg N a 0) (hv : EuclideanSpace ℝ (Fin N)),
    (∀ y : Vblk R a (0 + 1), y.1 ∉ gaussBlocks a 0 → o y = o' y) → b a g o x hv = b a g o' x hv
  b_analytic : ∀ (a : LocalHistory S n M K) (o : OutT N R a 1) (x : NewCfg N a 0)
    (hv : EuclideanSpace ℝ (Fin N)),
    AnalyticOnNhd ℂ (fun g => b a g o x hv) (l1Ball (GIdx S n M K N))
  b_zero_real : ∀ (a : LocalHistory S n M K) (o : OutT N R a 1) (x : NewCfg N a 0)
    (hv : EuclideanSpace ℝ (Fin N)), (b a 0 o x hv).im = 0
  b_real : ∀ (a : LocalHistory S n M K) (g : GIdx S n M K N → ℂ) (o : OutT N R a 1)
    (x : NewCfg N a 0) (hv : EuclideanSpace ℝ (Fin N)),
    g ∈ l1Ball (GIdx S n M K N) → (∀ i, (g i).im = 0) → (b a g o x hv).im = 0
  /-- `b` reads the source only on the sites of `Z'` -/
  b_supp : ∀ (H : RegionHistory S n R k0 K) (_ : H.Admissible) (Z' : H.Comp 1)
    (g g' : GIdx S n M K N → ℂ) (o : OutT N R (H.localHistory M K 1 Z') 1)
    (x : NewCfg N (H.localHistory M K 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N)),
    (∀ i : GIdx S n M K N, i.1 ∈ baseZsites M H Z' → g i = g' i) →
      b (H.localHistory M K 1 Z') g o x hv = b (H.localHistory M K 1 Z') g' o x hv
  /-- `b` reads the source only on the sites of `V` of the localized history (the form of (S0) for
  the step data; for the localized history of a component it follows from `b_supp`, since the
  sites of `Z'` are among those of `V`) -/
  b_suppV : ∀ (a : LocalHistory S n M K) (g g' : GIdx S n M K N → ℂ) (o : OutT N R a 1)
    (x : NewCfg N a 0) (hv : EuclideanSpace ℝ (Fin N)),
    (∀ i : GIdx S n M K N, i.1 ∈ Vsites R a (0 + 1) → g i = g' i) → b a g o x hv = b a g' o x hv
  b_rot : ∀ (a : LocalHistory S n M K) (g : GIdx S n M K N → ℂ) (ρ : OrthN N) (o : OutT N R a 1)
    (x : NewCfg N a 0) (hv : EuclideanSpace ℝ (Fin N)),
    b a (rotG ρ g) (rotOut ρ o) (rotSub ρ x) (ρ hv) = b a g o x hv
  b_euclid : ∀ (σ : TorusSym S n M K) (a a' : LocalHistory S n M K) (hI : HistImage σ a a')
    (hk : 0 + 1 ≤ K) (g g' : GIdx S n M K N → ℂ) (o : OutT N R a 1) (o' : OutT N R a' 1)
    (x : NewCfg N a 0) (x' : NewCfg N a' 0) (hv : EuclideanSpace ℝ (Fin N)),
    RelOut σ o o' → RelSub hI hk x x' → RelG σ g g' → b a' g' o' x' hv = b a g o x hv
  /-- the relative bound of the source part: `Re (b(g) - b(0)) ≤ ‖g|_{Z'}‖₁` on the `ℓ¹` ball and
  `χ^new_0` -/
  b_bound : ∀ (H : RegionHistory S n R k0 K) (_ : H.Admissible) (Z' : H.Comp 1)
    (g : GIdx S n M K N → ℂ) (o : OutT N R (H.localHistory M K 1 Z') 1)
    (x : NewCfg N (H.localHistory M K 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N)),
    g ∈ l1Ball (GIdx S n M K N) → ChiNewAt geo cs H 0 Z' o x →
    (b (H.localHistory M K 1 Z') g o x hv - b (H.localHistory M K 1 Z') 0 o x hv).re ≤
      baseSourceNorm M H Z' g

variable {k0 : ℕ} {geo : Geo S n R M} {cs : OpConsts}

/-- **The zero product data** (rule 10): `Kt = 0`, `b = 0`. -/
def zeroBaseProductData : BaseProductData M K k0 geo cs N where
  Kt := fun _ _ _ _ _ => 0
  b := fun _ _ _ _ _ => 0
  Kt_nonneg := fun _ _ _ _ _ => le_rfl
  Kt_meas := fun _ _ _ => measurable_const
  Kt_outside := fun _ _ _ _ _ _ _ => rfl
  Kt_dom := fun _ _ _ _ _ _ _ _ => rfl
  Kt_rot := fun _ _ _ _ _ _ => rfl
  euclid_Kt := by
    intro σ a a' hI hk o o' x x' hv ho hx
    classical
    simp [baseSumOf]
  b_meas := fun _ _ _ => measurable_const
  b_outside := fun _ _ _ _ _ _ _ => rfl
  b_analytic := fun _ _ _ _ => analyticOnNhd_const
  b_zero_real := fun _ _ _ _ => rfl
  b_real := fun _ _ _ _ _ _ _ => rfl
  b_supp := fun _ _ _ _ _ _ _ _ _ => rfl
  b_suppV := fun _ _ _ _ _ _ _ => rfl
  b_rot := fun _ _ _ _ _ _ => rfl
  b_euclid := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  b_bound := by
    intro H hH Z' g o x hv _ _
    simp only [sub_self, Complex.zero_re]
    unfold baseSourceNorm
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> positivity

/-- **`BaseProductData` is inhabited** (rule 10). -/
theorem baseProductData_nonempty (geo : Geo S n R M) (cs : OpConsts) (N k0 : ℕ) :
    Nonempty (BaseProductData M K k0 geo cs N) :=
  ⟨zeroBaseProductData⟩

end Product

section ToInput

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} [NeZero S.L] {N : ℕ}
  {M K : ℕ} [NeZero M] {k0 : ℕ} {geo : Geo S n R M} {cs : OpConsts}

/-- The exponential of a complex number with zero imaginary part is the real exponential. -/
theorem cexp_of_im_eq_zero {z : ℂ} (h : z.im = 0) :
    Complex.exp z = ((Real.exp z.re : ℝ) : ℂ) := by
  have : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h])
  rw [this, ← Complex.ofReal_exp]
  simp

/-- A real nonnegative factor times the exponential of a number with zero imaginary part is real. -/
theorem im_ofReal_mul_cexp {r : ℝ} {z : ℂ} (h : z.im = 0) :
    ((r : ℂ) * Complex.exp z).im = 0 := by
  rw [cexp_of_im_eq_zero h, ← Complex.ofReal_mul]
  exact Complex.ofReal_im _

/-- **The carrier of a product form**: `Kphys^w(g) := Kt^w · exp(b(g))`, every field proved from the
properties of `BaseProductData`. -/
noncomputable def BaseProductData.toInput (D : BaseProductData M K k0 geo cs N) :
    BaseSmallFieldInput M K k0 geo cs N where
  Kphys := fun H hH Z' g w o x hv =>
    (D.Kt (H.localHistory M K 1 Z') w o x hv : ℂ) *
      Complex.exp (D.b (H.localHistory M K 1 Z') g o x hv)
  Kphys_meas := fun H hH Z' g w hv =>
    (Complex.measurable_ofReal.comp (D.Kt_meas _ w hv)).mul
      (Complex.measurable_exp.comp (D.b_meas _ g hv))
  Kphys_outside := fun H hH Z' g w o o' x hv h => by
    rw [D.Kt_outside _ w o o' x hv h, D.b_outside _ g o o' x hv h]
  Kphys_dom := fun H hH Z' g w o x hv h => by
    rw [D.Kt_dom H hH Z' w o x hv h]; simp
  Kphys_zero_sector := fun H hH Z' w o x hv => by
    rw [cexp_of_im_eq_zero (D.b_zero_real _ o x hv), ← Complex.ofReal_mul]
    exact ⟨Complex.ofReal_im _, by
      rw [Complex.ofReal_re]; exact mul_nonneg (D.Kt_nonneg _ w o x hv) (Real.exp_pos _).le⟩
  Kphys_bound := fun H hH Z' g w o x hv hg hc => by
    rw [cexp_of_im_eq_zero (D.b_zero_real _ o x hv), ← Complex.ofReal_mul,
      Complex.ofReal_re, norm_mul, Complex.norm_real, Complex.norm_exp,
      Real.norm_of_nonneg (D.Kt_nonneg _ w o x hv), mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (D.Kt_nonneg _ w o x hv)
    have := D.b_bound H hH Z' g o x hv hg hc
    rw [Complex.sub_re] at this
    linarith
  Kphys_analytic := fun H hH Z' w o x hv =>
    fun g hg => analyticAt_const.fun_mul ((D.b_analytic _ o x hv g hg).cexp)
  Kphys_real := fun H hH Z' g w o x hv hg hr => by
    exact im_ofReal_mul_cexp (D.b_real _ g o x hv hg hr)
  Kphys_supp := fun H hH Z' g g' w o x hv h => by
    rw [D.b_supp H hH Z' g g' o x hv h]
  Kphys_rot := fun H hH Z' g w ρ o x hv => by
    rw [D.Kt_rot _ w ρ o x hv, D.b_rot _ g ρ o x hv]
  euclid_K := by
    intro σ H hH Z' H' hH' Z'' hI hk g g' o o' x x' hv ho hx hg
    have h1 := D.euclid_Kt σ _ _ hI hk o o' x x' hv ho hx
    have h2 := D.b_euclid σ _ _ hI hk g g' o o' x x' hv ho hx hg
    have e1 := baseSumC_mul_const cs (H'.localHistory M K 1 Z'')
      (fun w => D.Kt (H'.localHistory M K 1 Z'') w)
      (fun o x hv => Complex.exp (D.b (H'.localHistory M K 1 Z'') g' o x hv)) o' x' hv
    have e2 := baseSumC_mul_const cs (H.localHistory M K 1 Z')
      (fun w => D.Kt (H.localHistory M K 1 Z') w)
      (fun o x hv => Complex.exp (D.b (H.localHistory M K 1 Z') g o x hv)) o x hv
    show (gaussProd N (H'.localHistory M K 1 Z'') 0 cs o' x' : ℂ) *
        baseSumC cs (H'.localHistory M K 1 Z'')
          (fun w o x hv => (D.Kt (H'.localHistory M K 1 Z'') w o x hv : ℂ) *
            Complex.exp (D.b (H'.localHistory M K 1 Z'') g' o x hv)) o' x' hv =
      (gaussProd N (H.localHistory M K 1 Z') 0 cs o x : ℂ) *
        baseSumC cs (H.localHistory M K 1 Z')
          (fun w o x hv => (D.Kt (H.localHistory M K 1 Z') w o x hv : ℂ) *
            Complex.exp (D.b (H.localHistory M K 1 Z') g o x hv)) o x hv
    rw [e1, e2, h2]
    have h1c := congrArg (fun r : ℝ => (r : ℂ)) h1
    simp only [Complex.ofReal_mul] at h1c
    calc _ = ((gaussProd N (H'.localHistory M K 1 Z'') 0 cs o' x' : ℂ) *
          (baseSumOf cs (H'.localHistory M K 1 Z'') (fun w => D.Kt (H'.localHistory M K 1 Z'') w)
            o' x' hv : ℂ)) *
          Complex.exp (D.b (H.localHistory M K 1 Z') g o x hv) := by ring
      _ = _ := by rw [h1c]; ring

variable (D : BaseProductData M K k0 geo cs N)
  (H : RegionHistory S n R k0 K) (hH : H.Admissible) (Z' : H.Comp 1)

/-- **Obligation D4** for the product form: `Kphys^w(g) Kphys^{w'}(0) = Kphys^{w'}(g) Kphys^w(0)`
(both sides are `Kt^w Kt^{w'} e^{b(g) + b(0)}`). -/
theorem BaseProductData.Kphys_cross (g : GIdx S n M K N → ℂ)
    (w w' : BaseW (H.localHistory M K 1 Z') 0) (o : OutT N R (H.localHistory M K 1 Z') 1)
    (x : NewCfg N (H.localHistory M K 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N)) :
    D.toInput.Kphys H hH Z' g w o x hv * D.toInput.Kphys H hH Z' 0 w' o x hv =
      D.toInput.Kphys H hH Z' g w' o x hv * D.toInput.Kphys H hH Z' 0 w o x hv := by
  show (D.Kt (H.localHistory M K 1 Z') w o x hv : ℂ) * Complex.exp (D.b (H.localHistory M K 1 Z') g o x hv) *
      ((D.Kt (H.localHistory M K 1 Z') w' o x hv : ℂ) * Complex.exp (D.b (H.localHistory M K 1 Z') 0 o x hv)) =
    (D.Kt (H.localHistory M K 1 Z') w' o x hv : ℂ) * Complex.exp (D.b (H.localHistory M K 1 Z') g o x hv) *
      ((D.Kt (H.localHistory M K 1 Z') w o x hv : ℂ) * Complex.exp (D.b (H.localHistory M K 1 Z') 0 o x hv))
  ring

/-- The source-free factor of the product carrier is `Kt^w e^{Re b(0)}`. -/
theorem BaseProductData.baseKt0_toInput (w : BaseW (H.localHistory M K 1 Z') 0)
    (o : OutT N R (H.localHistory M K 1 Z') 1) (x : NewCfg N (H.localHistory M K 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) :
    baseKt0 D.toInput H hH Z' w o x hv =
      D.Kt (H.localHistory M K 1 Z') w o x hv * Real.exp (D.b (H.localHistory M K 1 Z') 0 o x hv).re := by
  unfold baseKt0
  show ((D.Kt (H.localHistory M K 1 Z') w o x hv : ℂ) * Complex.exp (D.b (H.localHistory M K 1 Z') 0 o x hv)).re = _
  rw [cexp_of_im_eq_zero (D.b_zero_real _ o x hv), ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- **The total exponent**: `baseKC = baseK0 · exp(b(g) - b(0))` everywhere (not only on the
nonvanishing domain), so the scale-`0` kernel is an `LFKernel` with the total analytic boundary
factor `b(g) - b(0)`. -/
theorem BaseProductData.baseKC_toInput (g : GIdx S n M K N → ℂ)
    (o : OutT N R (H.localHistory M K 1 Z') 1) (x : NewCfg N (H.localHistory M K 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) :
    baseKC D.toInput H hH Z' g o x hv =
      (baseK0 D.toInput H hH Z' o x hv : ℂ) *
        Complex.exp (D.b (H.localHistory M K 1 Z') g o x hv - D.b (H.localHistory M K 1 Z') 0 o x hv) := by
  have h0 := D.b_zero_real _ o x hv
  have hx : Complex.exp (D.b (H.localHistory M K 1 Z') g o x hv) =
      ((Real.exp (D.b (H.localHistory M K 1 Z') 0 o x hv).re : ℝ) : ℂ) *
        Complex.exp (D.b (H.localHistory M K 1 Z') g o x hv - D.b (H.localHistory M K 1 Z') 0 o x hv) := by
    rw [← cexp_of_im_eq_zero h0, ← Complex.exp_add]
    congr 1
    ring
  have e1 := baseSumC_mul_const cs (H.localHistory M K 1 Z') (fun w => D.Kt (H.localHistory M K 1 Z') w)
    (fun o x hv => Complex.exp (D.b (H.localHistory M K 1 Z') g o x hv)) o x hv
  have e2 := baseSumOf_mul_const cs (H.localHistory M K 1 Z') (fun w => D.Kt (H.localHistory M K 1 Z') w)
    (fun o x hv => Real.exp (D.b (H.localHistory M K 1 Z') 0 o x hv).re) o x hv
  have hfun : (fun w => baseKt0 D.toInput H hH Z' w) = fun w o x hv =>
      D.Kt (H.localHistory M K 1 Z') w o x hv * Real.exp (D.b (H.localHistory M K 1 Z') 0 o x hv).re := by
    funext w o x hv
    exact D.baseKt0_toInput H hH Z' w o x hv
  unfold baseKC baseK0
  rw [hfun]
  show (gaussProd N (H.localHistory M K 1 Z') 0 cs o x : ℂ) *
      baseSumC cs (H.localHistory M K 1 Z') (fun w o x hv => (D.Kt (H.localHistory M K 1 Z') w o x hv : ℂ) *
        Complex.exp (D.b (H.localHistory M K 1 Z') g o x hv)) o x hv = _
  rw [e1, e2, hx]
  push_cast
  ring

end ToInput

end Balaban.LargeField
