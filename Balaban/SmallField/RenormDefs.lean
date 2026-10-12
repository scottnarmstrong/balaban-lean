/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.TaylorCauchy
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# I-6, the renormalization analysis: objects and premises (SMALLFIELD.md §2.2)

The localized terms `𝓔^{(j)}(y, X; ψ, b)` of (H.2)–(H.4) at one scale `j`, in units of that scale
(lattice `ℤ^d`, spacing `1`), in the *centred* form: `T.term X` is the term of a polymer `X ∋ 0`
centred at the origin, a function of the finitely many values `(ψ(x))_{x ∈ X}` and of `b = ν_j h`.
The term of a polymer `X' ∋ y` is `T.term (X' - y)` evaluated at the translated configuration
`ψ(· + y)`; this is the translation covariance of (H.3), built into the notation.

* `Balaban.SmallField.TermFamily`: the data `(𝒟, d_j, 𝓔)`;
* `Balaban.SmallField.Tube`: the analyticity domain used by the proof: configurations that a
  complex orthogonal matrix of bounded entries carries into the polydisc of radius `ρ` around the
  reference point `(e₀, ν e₀)`;
* `Balaban.SmallField.Premises`: (H.2)–(H.5) with constants `E₀, κ` (the genuine premises of the
  source lemma), together with the cited geometric facts about the polymer family;
* `Balaban.SmallField.DataHyp`: the properties (Σ1), (Σ2) of the configuration used by the proof;
* `Balaban.SmallField.energy`, `potential`, `Aterm`: the three terms of Theorem 2.1(a).
-/

@[expose] public section

open Metric Set

namespace Balaban.SmallField

/-- The values of the spin field: `ℂ^N` (complex analytic extension of `ℝ^N`). -/
abbrev Spin (N : ℕ) := Fin N → ℂ

/-- The sites of the lattice `ℤ^d` at the scale `j` (spacing `1`). -/
abbrev Site (d : ℕ) := Fin d → ℤ

/-- Coordinates of the finite-dimensional configuration space of a polymer `X`: the spins
`ψ(x)`, `x ∈ X`, and the field `b`. -/
abbrev Idx (d N : ℕ) (X : Finset (Site d)) := (↥X × Fin N) ⊕ Fin N

/-- The configuration space of a polymer `X`, with the sup norm. -/
abbrev Cfg (d N : ℕ) (X : Finset (Site d)) := Idx d N X → ℂ

variable {d N : ℕ}

/-- The bilinear (not Hermitian) scalar product on `ℂ^N`. -/
def dot (v w : Spin N) : ℂ := ∑ i, v i * w i

/-- The bilinear scalar product on the components transverse to `i₀`. -/
def dotT (i₀ : Fin N) (v w : Spin N) : ℂ := ∑ i ∈ Finset.univ.erase i₀, v i * w i

/-- The configuration of a polymer `X` determined by the spin field `ψ` and the field `b`. -/
def pack (X : Finset (Site d)) (ψ : Site d → Spin N) (b : Spin N) : Cfg d N X :=
  Sum.elim (fun p => ψ p.1.1 p.2) b

/-- The reference point `(e_{i₀}, ν e_{i₀})`, in the variables `(ψ, b)`, `b = ν h`. -/
def refPt (i₀ : Fin N) (ν : ℝ) (X : Finset (Site d)) : Cfg d N X :=
  pack X (fun _ => Pi.single i₀ 1) ((ν : ℂ) • Pi.single i₀ 1)

/-- The action of a matrix on a configuration: it acts on each `ψ(x)` and on `b`. -/
def rotCfgL (R : Matrix (Fin N) (Fin N) ℂ) (X : Finset (Site d)) :
    Cfg d N X →ₗ[ℂ] Cfg d N X where
  toFun c := Sum.elim (fun p => ∑ k, R p.2 k * c (Sum.inl (p.1, k)))
    (fun i => ∑ k, R i k * c (Sum.inr k))
  map_add' c c' := by
    ext (p | i) <;> simp [mul_add, Finset.sum_add_distrib]
  map_smul' t c := by
    ext (p | i) <;> simp [Finset.mul_sum, mul_left_comm]

/-- Complex orthogonality `Rᵀ R = 1`. -/
def IsOrth (R : Matrix (Fin N) (Fin N) ℂ) : Prop := R.transpose * R = 1

/-- The bound on the entries of the rotations admitted in the analyticity domain. -/
def rotBound (_N : ℕ) : ℝ := 40

/-- The entries of `R` are bounded by `rotBound N`. -/
def EntryBd (N : ℕ) (R : Matrix (Fin N) (Fin N) ℂ) : Prop := ∀ i k, ‖R i k‖ ≤ rotBound N

/-- **The analyticity domain used by the proof**: the configurations of `X` which a complex
orthogonal matrix with entries bounded by `rotBound N` carries into the polydisc of radius `ρ`
around the reference point. -/
def Tube (i₀ : Fin N) (ν ρ : ℝ) (X : Finset (Site d)) : Set (Cfg d N X) :=
  {c | ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
    rotCfgL R X c ∈ ball (refPt i₀ ν X) ρ}

/-- The localized terms at one scale: the polymers (containing the origin), their distance
`d_j`, and the terms `𝓔(y, X; ·)` in centred form. -/
structure TermFamily (d N : ℕ) where
  polys : Set (Finset (Site d))
  dist : Finset (Site d) → ℝ
  term : (X : Finset (Site d)) → Cfg d N X → ℂ

/-! ### The tensors at the reference point -/

/-- `a_X(x) = ∂𝓔(0, X)/∂ψ_{i₀}(x)` at the reference point. -/
noncomputable def tensA (i₀ : Fin N) (ν : ℝ) (X : Finset (Site d)) (f : Cfg d N X → ℂ)
    (x : ↥X) : ℂ :=
  fderiv ℂ f (refPt i₀ ν X) (Pi.single (Sum.inl (x, i₀)) 1)

/-- `B_X(x, x') = ∂²𝓔(0, X)/∂ψ_{i₁}(x)∂ψ_{i₁}(x')` at the reference point. -/
noncomputable def tensB (i₀ i₁ : Fin N) (ν : ℝ) (X : Finset (Site d)) (f : Cfg d N X → ℂ)
    (x x' : ↥X) : ℂ :=
  D2 f (refPt i₀ ν X) (Pi.single (Sum.inl (x, i₁)) 1) (Pi.single (Sum.inl (x', i₁)) 1)

/-- `m_X(x') = ∂²𝓔(0, X)/∂b_{i₁}∂ψ_{i₁}(x')` at the reference point. -/
noncomputable def tensM (i₀ i₁ : Fin N) (ν : ℝ) (X : Finset (Site d)) (f : Cfg d N X → ℂ)
    (x' : ↥X) : ℂ :=
  D2 f (refPt i₀ ν X) (Pi.single (Sum.inr i₁) 1) (Pi.single (Sum.inl (x', i₁)) 1)

/-- The weight of a polymer in the counting premise: `|X|² (1 + d_j(X))⁶ e^{-(κ-1) d_j(X)}`. -/
noncomputable def wt (κ : ℝ) (X : Finset (Site d)) (dj : ℝ) : ℝ :=
  (X.card : ℝ) ^ 2 * (1 + dj) ^ 6 * Real.exp (-(κ - 1) * dj)

/-- **Premises of the source lemma** (SMALLFIELD.md §2.2, P1 Prop 3.10): (H.2)–(H.4) and the
renormalization conditions (H.5) for the terms of one scale, with constants `E₀, κ`; the
analyticity radius is `ρ ≍ ε_j`; the family `Dom` is the abstract data domain `Ξ^c_j`.
The last four fields are the cited geometric facts on the polymers (Step 0 of §2.3).  -/
structure Premises (T : TermFamily d N) (i₀ i₁ : Fin N) (ν ρ E₀ κ A K₀ : ℝ)
    (Dom : Set ((Site d → Spin N) × Spin N)) : Prop where
  ne : i₀ ≠ i₁
  /-- geometry: polymers contain their centre, `d_j ≥ 0` -/
  zero_mem : ∀ X ∈ T.polys, (0 : Site d) ∈ X
  dist_nonneg : ∀ X ∈ T.polys, 0 ≤ T.dist X
  /-- geometry: path bound (P1 (3.54)): `|x|₁ ≤ A (1 + d_j(X))` for `x ∈ X` -/
  diam : ∀ X ∈ T.polys, ∀ x ∈ X, ((∑ μ, |x μ| : ℤ) : ℝ) ≤ A * (1 + T.dist X)
  /-- geometry: counting (P6 (4.11), PE-L (G2)) -/
  count_summable : Summable fun X : T.polys => wt κ X.1 (T.dist X.1)
  count_le : ∑' X : T.polys, wt κ X.1 (T.dist X.1) ≤ K₀
  /-- (H.2), (H.4): analyticity on the analyticity domain -/
  analytic : ∀ X ∈ T.polys, AnalyticOnNhd ℂ (T.term X) (Tube i₀ ν ρ X)
  /-- (H.4): the bound `E₀ e^{-κ d_j(X)}` on the analyticity domain -/
  bdd_tube : ∀ X ∈ T.polys, ∀ c ∈ Tube i₀ ν ρ X, ‖T.term X c‖ ≤ E₀ * Real.exp (-κ * T.dist X)
  /-- (H.4): the same bound on the data domain `Dom` (where `𝓔` is evaluated) -/
  bdd_dom : ∀ X ∈ T.polys, ∀ p ∈ Dom,
    ‖T.term X (pack X p.1 p.2)‖ ≤ E₀ * Real.exp (-κ * T.dist X)
  /-- (H.3): invariance under (complex) rotations, where defined -/
  rot_inv : ∀ X ∈ T.polys, ∀ c ∈ Tube i₀ ν ρ X, ∀ R : Matrix (Fin N) (Fin N) ℂ,
    IsOrth R → EntryBd N R → rotCfgL R X c ∈ Tube i₀ ν ρ X →
      T.term X (rotCfgL R X c) = T.term X c
  /-- (H.5)(1): `𝓥(e₁, ν e₁) = 0` -/
  ren_val : ∑' X : T.polys, T.term X.1 (refPt i₀ ν X.1) = 0
  /-- (H.5)(2): `∂_b 𝓥(e₁, ν e₁) · e₁ = 0` -/
  ren_b : ∑' X : T.polys,
    fderiv ℂ (T.term X.1) (refPt i₀ ν X.1) (Pi.single (Sum.inr i₀) 1) = 0
  /-- (H.5)(3): `Σ_{y'} ∂_{ψ(y')} 𝓔(y; e₁, ν e₁) · e₁ = 0` -/
  ren_psi : ∑' X : T.polys, ∑ x : ↥X.1, tensA i₀ ν X.1 (T.term X.1) x = 0
  /-- (H.5)(4): the second moment `Σ_x tr[∂²/∂ψ(x)∂ψ(0) 𝓔 (e₂⊗e₂)] |x|² = 0` -/
  moment : ∑' X : T.polys, ∑ x : ↥X.1, ∑ x' : ↥X.1,
    tensB i₀ i₁ ν X.1 (T.term X.1) x x' * (∑ μ, (((x.1 μ - x'.1 μ : ℤ) : ℂ)) ^ 2) = 0

/-- **The properties (Σ1), (Σ2) of the configuration `(ψ, b)`** used by the proof, at the scale
`σ` with field size `ε` (`σ = C₀ s`, `ε = ε_k`); `K₂` bounds the second differences.  The
configuration and its constant version lie in the domain `Dom`. -/
structure DataHyp (Dom : Set ((Site d → Spin N) × Spin N)) (ν σ ε K₂ : ℝ)
    (ψ : Site d → Spin N) (b : Spin N) : Prop where
  sq : ∀ x, ‖dot (ψ x) (ψ x) - 1‖ ≤ σ ^ 2 * ε
  bdd0 : ‖ψ 0‖ ≤ 2
  adj : ∀ x μ, ‖ψ (x + Pi.single μ 1) - ψ x‖ ≤ σ * ε
  b_close : ‖b - (ν : ℂ) • ψ 0‖ ≤ σ ^ 2 * ε
  sec : ∀ x μ μ', ‖ψ (x + Pi.single μ 1 + Pi.single μ' 1) - ψ (x + Pi.single μ 1)
    - ψ (x + Pi.single μ' 1) + ψ x‖ ≤ K₂
  mem : (ψ, b) ∈ Dom
  mem_const : ((fun _ => ψ 0), b) ∈ Dom

/-! ### The three terms of Theorem 2.1 (a) -/

/-- `𝓔^{(j)}(0; ψ, b)`: the sum of the terms of the polymers containing the origin. -/
noncomputable def energy (T : TermFamily d N) (ψ : Site d → Spin N) (b : Spin N) : ℂ :=
  ∑' X : T.polys, T.term X.1 (pack X.1 ψ b)

/-- `𝓥^{(j)}(p, b)`: the same for the constant configuration `p`. -/
noncomputable def potential (T : TermFamily d N) (p b : Spin N) : ℂ :=
  ∑' X : T.polys, T.term X.1 (pack X.1 (fun _ => p) b)

/-- `a_X(x) = ∂_{ψ(x)} 𝓔(0, X; e₁, ν e₁) · e₁`, extended by `0` outside `X`. -/
noncomputable def aCoefX (T : TermFamily d N) (i₀ : Fin N) (ν : ℝ) (X : Finset (Site d))
    (x : Site d) : ℂ :=
  if hx : x ∈ X then tensA i₀ ν X (T.term X) ⟨x, hx⟩ else 0

/-- `a^{(j)}(x) = Σ_{X ∋ 0, x} ∂_{ψ(x)} 𝓔(0, X; e₁, ν e₁) · e₁`. -/
noncomputable def aCoef (T : TermFamily d N) (i₀ : Fin N) (ν : ℝ) (x : Site d) : ℂ :=
  ∑' X : T.polys, aCoefX T i₀ ν X.1 x

/-- `A_0(ψ) = ½ Σ_x a^{(j)}(x) (ψ(x)·ψ(x) - ψ(0)·ψ(0))`, written as the sum over polymers. -/
noncomputable def Aterm (T : TermFamily d N) (i₀ : Fin N) (ν : ℝ) (ψ : Site d → Spin N) : ℂ :=
  (1 / 2 : ℂ) * ∑' X : T.polys, ∑ x ∈ X.1,
    aCoefX T i₀ ν X.1 x * (dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0))

/-! ### Basic lemmas -/

theorem rotCfgL_apply_inl (R : Matrix (Fin N) (Fin N) ℂ) (X : Finset (Site d)) (c : Cfg d N X)
    (p : ↥X × Fin N) :
    rotCfgL R X c (Sum.inl p) = ∑ k, R p.2 k * c (Sum.inl (p.1, k)) := rfl

theorem rotCfgL_apply_inr (R : Matrix (Fin N) (Fin N) ℂ) (X : Finset (Site d)) (c : Cfg d N X)
    (i : Fin N) : rotCfgL R X c (Sum.inr i) = ∑ k, R i k * c (Sum.inr k) := rfl

theorem rotCfgL_pack (R : Matrix (Fin N) (Fin N) ℂ) (X : Finset (Site d)) (ψ : Site d → Spin N)
    (b : Spin N) :
    rotCfgL R X (pack X ψ b) = pack X (fun x => R.mulVec (ψ x)) (R.mulVec b) := by
  ext (p | i) <;> simp [rotCfgL_apply_inl, rotCfgL_apply_inr, pack, Matrix.mulVec, dotProduct]

theorem rotCfgL_one (X : Finset (Site d)) (c : Cfg d N X) :
    rotCfgL (1 : Matrix (Fin N) (Fin N) ℂ) X c = c := by
  ext (p | i) <;> simp [rotCfgL_apply_inl, rotCfgL_apply_inr, Matrix.one_apply]

theorem rotCfgL_mul (R S : Matrix (Fin N) (Fin N) ℂ) (X : Finset (Site d)) (c : Cfg d N X) :
    rotCfgL (R * S) X c = rotCfgL R X (rotCfgL S X c) := by
  ext (p | i)
  · simp only [rotCfgL_apply_inl, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  · simp only [rotCfgL_apply_inr, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem isOrth_one : IsOrth (1 : Matrix (Fin N) (Fin N) ℂ) := by simp [IsOrth]

theorem entryBd_one : EntryBd N (1 : Matrix (Fin N) (Fin N) ℂ) := by
  intro i k
  by_cases h : i = k
  · subst h; simp [rotBound]
  · simp [h, rotBound]

theorem refPt_mem_ball (i₀ : Fin N) (ν ρ : ℝ) (hρ : 0 < ρ) (X : Finset (Site d)) :
    refPt i₀ ν X ∈ ball (refPt i₀ ν X) ρ := mem_ball_self hρ

theorem ball_subset_tube (i₀ : Fin N) (ν ρ : ℝ) (X : Finset (Site d)) :
    ball (refPt i₀ ν X) ρ ⊆ Tube i₀ ν ρ X := by
  intro c hc
  exact ⟨1, isOrth_one, entryBd_one, by rwa [rotCfgL_one]⟩

end Balaban.SmallField
