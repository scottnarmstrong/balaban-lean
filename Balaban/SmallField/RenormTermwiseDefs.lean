/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormTorus

/-!
# Lemma 3.2 (termwise irrelevance): premises and objects (FLUCTUATION.md §3.2)

The landed `Premises` of I-6 bundle (H.2)–(H.4) with the four renormalization conditions
(H.5)(1)–(4), which are conditions on the *sum* over the polymers `X ∋ y`.  Lemma 3.2 treats the
terms one by one, so the premises are split:

* `PremisesTerm`: (H.2)–(H.4) and the geometric facts, i.e. `Premises` without (H.5);
* `SumConds`: the renormalization conditions (H.5)(1)–(4) on the sum;
* `PremisesTerm.toPremises`, `Premises.toTerm`, `Premises.sumConds`: the two together are `Premises`.

The termwise objects of the centred form (`y = 0`, `X ∈ T.polys`; `ψ(y) = ψ 0`):

* `Ttw`: `T_X = f_X(P₀) + ∂_u f_X(P₀) (u - 1) + ∂_v f_X(P₀) (v - ν)` with the invariants
  `u = √(ψ(y)·ψ(y))` (principal root, `sqrtC`) and `v = (ψ(y)·b)/u`;
* `Ax`: `A_{y,X} = ½ Σ_x a_X(x) (ψ(x)·ψ(x) - ψ(y)·ψ(y))` (landed);
* `Phitw`: `Φ_{y,X} = -¼ Σ_{μν} S_X^{μν} [∂_μψ·∂_νψ - (ψ̂·∂_μψ)(ψ̂·∂_νψ)]`, `ψ̂·ψ̂ = 1`
  written without the root: `(ψ(y)·∂_μψ)(ψ(y)·∂_νψ)/(ψ(y)·ψ(y))`;
* `Itw`: `I(y,X) = 𝓔(y,X) - T_X - A_{y,X} - Φ_{y,X}`.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

/-- **Premises of Lemma 3.2** without the renormalization conditions: (H.2)–(H.4) with constants
`E₀, κ` and the cited geometric facts on the polymers; the same fields as `Premises` except
(H.5)(1)–(4), which are the separate hypotheses `SumConds`. -/
structure PremisesTerm (T : TermFamily d N) (i₀ i₁ : Fin N) (ν ρ E₀ κ A K₀ : ℝ)
    (Dom : Set ((Site d → Spin N) × Spin N)) : Prop where
  ne : i₀ ≠ i₁
  zero_mem : ∀ X ∈ T.polys, (0 : Site d) ∈ X
  dist_nonneg : ∀ X ∈ T.polys, 0 ≤ T.dist X
  diam : ∀ X ∈ T.polys, ∀ x ∈ X, ((∑ μ, |x μ| : ℤ) : ℝ) ≤ A * (1 + T.dist X)
  count_summable : Summable fun X : T.polys => wt κ X.1 (T.dist X.1)
  count_le : ∑' X : T.polys, wt κ X.1 (T.dist X.1) ≤ K₀
  /-- (H.2), (H.4): analyticity on the analyticity domain -/
  analytic : ∀ X ∈ T.polys, AnalyticOnNhd ℂ (T.term X) (Tube i₀ ν ρ X)
  /-- (H.4): the bound on the analyticity domain -/
  bdd_tube : ∀ X ∈ T.polys, ∀ c ∈ Tube i₀ ν ρ X, ‖T.term X c‖ ≤ E₀ * Real.exp (-κ * T.dist X)
  /-- (H.4): the same bound on the data domain `Dom` -/
  bdd_dom : ∀ X ∈ T.polys, ∀ p ∈ Dom,
    ‖T.term X (pack X p.1 p.2)‖ ≤ E₀ * Real.exp (-κ * T.dist X)
  /-- (H.3): rotation invariance -/
  rot_inv : ∀ X ∈ T.polys, ∀ c ∈ Tube i₀ ν ρ X, ∀ R : Matrix (Fin N) (Fin N) ℂ,
    IsOrth R → EntryBd N R → rotCfgL R X c ∈ Tube i₀ ν ρ X →
      T.term X (rotCfgL R X c) = T.term X c
  /-- (H.3): the polymer family is invariant under the generators of the point group -/
  sym_mem : ∀ r : Site d → Site d, IsLatGen r → ∀ X ∈ T.polys, X.image r ∈ T.polys
  /-- (H.3): Euclid invariance of the terms -/
  sym_inv : ∀ r : Site d → Site d, IsLatGen r → ∀ X ∈ T.polys, ∀ (ψ : Site d → Spin N) (b : Spin N),
    T.term (X.image r) (pack (X.image r) (fun x => ψ (r x)) b) = T.term X (pack X ψ b)

/-- **The renormalization conditions (H.5)(1)–(4)**, conditions on the sum over the polymers
`X ∋ y`: they are source premises of the class, not termwise facts. -/
structure SumConds (T : TermFamily d N) (i₀ i₁ : Fin N) (ν : ℝ) : Prop where
  /-- (H.5)(1): `𝓥(e₁, ν e₁) = 0` -/
  ren_val : ∑' X : T.polys, T.term X.1 (refPt i₀ ν X.1) = 0
  /-- (H.5)(2): `∂_b 𝓥(e₁, ν e₁) · e₁ = 0` -/
  ren_b : ∑' X : T.polys,
    fderiv ℂ (T.term X.1) (refPt i₀ ν X.1) (Pi.single (Sum.inr i₀) 1) = 0
  /-- (H.5)(3) -/
  ren_psi : ∑' X : T.polys, ∑ x : ↥X.1, tensA i₀ ν X.1 (T.term X.1) x = 0
  /-- (H.5)(4): the second moment -/
  moment : ∑' X : T.polys, ∑ x : ↥X.1, ∑ x' : ↥X.1,
    tensB i₀ i₁ ν X.1 (T.term X.1) x x' * (∑ μ, (((x.1 μ - x'.1 μ : ℤ) : ℂ)) ^ 2) = 0

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)}

theorem Premises.toTerm (h : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) :
    PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom :=
  ⟨h.ne, h.zero_mem, h.dist_nonneg, h.diam, h.count_summable, h.count_le, h.analytic, h.bdd_tube,
    h.bdd_dom, h.rot_inv, h.sym_mem, h.sym_inv⟩

theorem Premises.sumConds (h : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) : SumConds T i₀ i₁ ν :=
  ⟨h.ren_val, h.ren_b, h.ren_psi, h.moment⟩

theorem PremisesTerm.toPremises (h : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom)
    (s : SumConds T i₀ i₁ ν) : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom :=
  ⟨h.ne, h.zero_mem, h.dist_nonneg, h.diam, h.count_summable, h.count_le, h.analytic, h.bdd_tube,
    h.bdd_dom, h.rot_inv, h.sym_mem, h.sym_inv, s.ren_val, s.ren_b, s.ren_psi, s.moment⟩

/-- The premises with the analyticity domain of the class given as an arbitrary family of sets
`Ω X ⊇ Tube`: analyticity, the bound, and rotation invariance are required on `Ω` and restrict to
the `Tube`.  This isolates the domain: a later inclusion `Tube ⊆ XiDom` is all that is needed to
apply the termwise theorems to a family analytic on `XiDom`. -/
theorem PremisesTerm.ofDomain (Ω : (X : Finset (Site d)) → Set (Cfg d N X))
    (hΩ : ∀ X ∈ T.polys, Tube i₀ ν ρ X ⊆ Ω X)
    (ne : i₀ ≠ i₁) (zero_mem : ∀ X ∈ T.polys, (0 : Site d) ∈ X)
    (dist_nonneg : ∀ X ∈ T.polys, 0 ≤ T.dist X)
    (diam : ∀ X ∈ T.polys, ∀ x ∈ X, ((∑ μ, |x μ| : ℤ) : ℝ) ≤ A * (1 + T.dist X))
    (count_summable : Summable fun X : T.polys => wt κ X.1 (T.dist X.1))
    (count_le : ∑' X : T.polys, wt κ X.1 (T.dist X.1) ≤ K₀)
    (analytic : ∀ X ∈ T.polys, AnalyticOnNhd ℂ (T.term X) (Ω X))
    (bdd : ∀ X ∈ T.polys, ∀ c ∈ Ω X, ‖T.term X c‖ ≤ E₀ * Real.exp (-κ * T.dist X))
    (bdd_dom : ∀ X ∈ T.polys, ∀ p ∈ Dom,
      ‖T.term X (pack X p.1 p.2)‖ ≤ E₀ * Real.exp (-κ * T.dist X))
    (rot_inv : ∀ X ∈ T.polys, ∀ c ∈ Ω X, ∀ R : Matrix (Fin N) (Fin N) ℂ,
      IsOrth R → EntryBd N R → rotCfgL R X c ∈ Ω X → T.term X (rotCfgL R X c) = T.term X c)
    (sym_mem : ∀ r : Site d → Site d, IsLatGen r → ∀ X ∈ T.polys, X.image r ∈ T.polys)
    (sym_inv : ∀ r : Site d → Site d, IsLatGen r → ∀ X ∈ T.polys, ∀ (ψ : Site d → Spin N)
      (b : Spin N), T.term (X.image r) (pack (X.image r) (fun x => ψ (r x)) b) =
        T.term X (pack X ψ b)) :
    PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom :=
  ⟨ne, zero_mem, dist_nonneg, diam, count_summable, count_le,
    fun X hX => (analytic X hX).mono (hΩ X hX), fun X hX c hc => bdd X hX c (hΩ X hX hc),
    bdd_dom, fun X hX c hc R hR hb hm => rot_inv X hX c (hΩ X hX hc) R hR hb (hΩ X hX hm),
    sym_mem, sym_inv⟩

/-! ### The termwise objects -/

/-- The principal square root. -/
noncomputable def sqrtC (z : ℂ) : ℂ := z ^ (1 / 2 : ℂ)

theorem sqrtC_re_nonneg (z : ℂ) : 0 ≤ (sqrtC z).re := by
  unfold sqrtC
  by_cases hz : z = 0
  · subst hz; simp
  rw [Complex.cpow_def_of_ne_zero hz, Complex.exp_re]
  refine mul_nonneg (Real.exp_pos _).le ?_
  have h : (Complex.log z * (1 / 2 : ℂ)).im = Complex.arg z / 2 := by
    simp [Complex.log_im]; ring
  rw [h]
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · have := Complex.neg_pi_lt_arg z; linarith [Real.pi_pos]
  · have := Complex.arg_le_pi z; linarith [Real.pi_pos]

theorem sqrtC_mul_self (z : ℂ) : sqrtC z * sqrtC z = z := by
  unfold sqrtC
  by_cases hz : z = 0
  · subst hz; simp
  rw [← Complex.cpow_add _ _ hz]; norm_num

/-- The principal root is the root with positive real part. -/
theorem sqrtC_eq {z u : ℂ} (hu : u * u = z) (hre : 0 < u.re) : sqrtC z = u := by
  have hw := sqrtC_mul_self z
  have h0 := sqrtC_re_nonneg z
  have : (sqrtC z - u) * (sqrtC z + u) = 0 := by linear_combination hw - hu
  rcases mul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have := congrArg Complex.re h
    simp at this; linarith

/-- The invariant `u = √(ψ(y)·ψ(y))` of the data. -/
noncomputable def uInv (ψ : Site d → Spin N) : ℂ := sqrtC (dot (ψ 0) (ψ 0))

/-- The invariant `v = (ψ(y)·b)/u`. -/
noncomputable def vInv (ψ : Site d → Spin N) (b : Spin N) : ℂ := dot (ψ 0) b / uInv ψ

/-- `T_X = f_X(P₀) + ∂_u f_X(P₀) (u - 1) + ∂_v f_X(P₀) (v - ν)`, written with the tensors of the
single term at the reference point: `∂_u f_X(P₀) = Σ_x a_X(x)`, `∂_v f_X(P₀) = ∂_b 𝓔(y,X)·e₁`. -/
noncomputable def Ttw (T : TermFamily d N) (i₀ : Fin N) (ν : ℝ) (X : Finset (Site d))
    (ψ : Site d → Spin N) (b : Spin N) : ℂ :=
  T.term X (refPt i₀ ν X) + (uInv ψ - 1) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x
    + (vInv ψ b - ν) * fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1)

/-- The frozen gradient tensor in invariant form:
`∂_μψ·∂_νψ - (ψ(y)·∂_μψ)(ψ(y)·∂_νψ)/(ψ(y)·ψ(y))`, `∂_μψ = ψ(y + e_μ) - ψ(y)`. -/
noncomputable def gradInv (ψ : Site d → Spin N) (μ μ' : Fin d) : ℂ :=
  dot (ψ (eU μ) - ψ 0) (ψ (eU μ') - ψ 0) -
    dot (ψ 0) (ψ (eU μ) - ψ 0) * dot (ψ 0) (ψ (eU μ') - ψ 0) / dot (ψ 0) (ψ 0)

/-- `Φ_{y,X} = -¼ Σ_{μν} S_X^{μν} [∂_μψ·∂_νψ - (ψ̂·∂_μψ)(ψ̂·∂_νψ)]`. -/
noncomputable def Phitw (T : TermFamily d N) (i₀ i₁ : Fin N) (ν : ℝ) (X : Finset (Site d))
    (ψ : Site d → Spin N) : ℂ :=
  -(1 / 4 : ℂ) * ∑ μ, ∑ μ', gradInv ψ μ μ' * Sx T i₀ i₁ ν X μ μ'

/-- `I(y,X;ψ,b) = 𝓔(y,X;ψ,b) - T_X - A_{y,X} - Φ_{y,X}`. -/
noncomputable def Itw (T : TermFamily d N) (i₀ i₁ : Fin N) (ν : ℝ) (X : Finset (Site d))
    (ψ : Site d → Spin N) (b : Spin N) : ℂ :=
  T.term X (pack X ψ b) - Ttw T i₀ ν X ψ b - Ax T i₀ ν ψ X - Phitw T i₀ i₁ ν X ψ

/-! ### Identification with the rotated-frame expressions of the landed proof -/

theorem dot_eq_dotT_add (i₀ : Fin N) (v w : Spin N) : dot v w = dotT i₀ v w + v i₀ * w i₀ := by
  unfold dot dotT
  rw [add_comm]
  exact (Finset.add_sum_erase _ (fun i => v i * w i) (Finset.mem_univ i₀)).symm

theorem Frame.uInv_eq {σ ε : ℝ} {ψ : Site d → Spin N} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}
    (f : Frame i₀ σ ε ψ u R) (hτ : σ ^ 2 * ε ≤ 1 / 4) : uInv ψ = u := by
  unfold uInv
  refine sqrtC_eq f.u_sq ?_
  have h1 : ‖u - 1‖ ≤ 1 / 4 := f.u_close.trans hτ
  have h2 : |(u - 1).re| ≤ ‖u - 1‖ := Complex.abs_re_le_norm _
  have h3 : (u - 1).re = u.re - 1 := by simp
  rw [h3] at h2
  have := (abs_le.mp (h2.trans h1)).1
  linarith

theorem Frame.u_ne {σ ε : ℝ} {ψ : Site d → Spin N} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}
    (f : Frame i₀ σ ε ψ u R) (hτ : σ ^ 2 * ε ≤ 1 / 4) : u ≠ 0 := by
  intro h
  have := f.u_close
  rw [h] at this
  simp at this
  linarith

/-- In the frame, the rotated component along `e_{i₀}` is `(ψ(0)·w)/u`. -/
theorem Frame.mulVec_apply {σ ε : ℝ} {ψ : Site d → Spin N} {u : ℂ}
    {R : Matrix (Fin N) (Fin N) ℂ} (f : Frame i₀ σ ε ψ u R) (hu : u ≠ 0) (w : Spin N) :
    R.mulVec w i₀ = dot (ψ 0) w / u := by
  have h1 : dot (R.mulVec (ψ 0)) (R.mulVec w) = dot (ψ 0) w := dot_mulVec_rot f.orth _ _
  rw [f.rot0, dot_smul_left, dot_single_left, one_mul] at h1
  rw [← h1]; field_simp

theorem Frame.gradTensor_eq {σ ε : ℝ} {ψ : Site d → Spin N} {u : ℂ}
    {R : Matrix (Fin N) (Fin N) ℂ} (f : Frame i₀ σ ε ψ u R) (hτ : σ ^ 2 * ε ≤ 1 / 4) (μ μ' : Fin d) :
    gradTensor i₀ R ψ μ μ' = gradInv ψ μ μ' := by
  have hu := f.u_ne hτ
  have hg : dot (ψ 0) (ψ 0) = u * u := f.u_sq.symm
  unfold gradTensor gradInv rotDiff
  have h := dot_eq_dotT_add i₀ (R.mulVec (ψ (eU μ) - ψ 0)) (R.mulVec (ψ (eU μ') - ψ 0))
  rw [dot_mulVec_rot f.orth, f.mulVec_apply hu, f.mulVec_apply hu] at h
  rw [hg, h]
  field_simp
  ring

/-- The frozen-gradient term `Φ` is `-L` of the landed proof. -/
theorem Frame.phitw_eq {σ ε : ℝ} {ψ : Site d → Spin N} {u : ℂ}
    {R : Matrix (Fin N) (Fin N) ℂ} (f : Frame i₀ σ ε ψ u R) (hτ : σ ^ 2 * ε ≤ 1 / 4)
    (X : Finset (Site d)) : Phitw T i₀ i₁ ν X ψ = -Lx T i₀ i₁ ν R ψ X := by
  rw [Lx_eq]
  unfold Phitw
  simp only [← f.gradTensor_eq hτ]
  ring

end Balaban.SmallField
