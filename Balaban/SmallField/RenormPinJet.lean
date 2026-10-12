/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormAnisoIrrel

/-!
# PIN-I6: the reference-jet certificate and the termwise irrelevance bound

`notes/phase1/PIN-I6.md` §3.  The landed anisotropic I-6 (`termwise_irrelevant_aniso`) consumes
analyticity and a bound of each old term on the whole polydisc `polyAniso i₀ ν r X`, in
particular in the transverse-`b` directions; on the pinned physical chart this is not available
(§2, `RenormPinCounter.lean`).  The corrected statement replaces exactly the wide-domain Cauchy
inputs (`CtxAniso.analytic_poly`, `CtxAniso.hM`, hence `aniso_taylor_diff` and the Hessian bounds
of `TermOK.local_bound_aniso`, and `CtxAniso.constant_potential_aniso`) by a **reference-jet
certificate** `PinJetTerm` (one term) / `PinJet` (a family) on the data:

* `germ`: the term is analytic near the reference point and invariant under rotations there
  (`TermOK` at some radius), which gives the shape lemmas and the Ward identity;
* the reference tensors `a_X`, `B_X`, `A_X`, `m_X` have the sizes the polydisc would give;
* `small`: for small polymers, the Taylor difference and the cross Hessian term on the actual
  (rotated) configurations are bounded as the polydisc Cauchy estimates would bound them;
* `potential`: the constant-potential remainder (3.1).

All the algebra (shape identities, Ward identity, tensor algebra, `smallBndA`/`tailBndA` bounds,
`weight_absorb`) is the landed one.

* `PremisesGeom`: the geometric/counting/bound fields of `PremisesTermAniso`, without the
  analyticity domain;
* `CtxPin`: `CtxAniso` with `PremisesGeom` in place of `PremisesTermAniso`;
* `TermOK.local_bound_pin`, `CtxPin.small_case`, `CtxPin.tail_case`, `CtxPin.dlt_bound_raw`,
  `CtxPin.itw_bound_raw`;
* `termwise_irrelevant_pin`, `termwise_irrelevant_pin_scaled`: the corrected theorem (3.2);
* `PinJet.of_ctxAniso`-type bridge theorems are in `RenormPinBridge.lean`.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

/-! ### Geometry and the data context without the analyticity domain -/

/-- **The geometric part of the premises**: the fields of `PremisesTermAniso` that do not involve
the analyticity domain (polymer geometry, counting, and the bound on the data domain). -/
structure PremisesGeom (T : TermFamily d N) (i₀ i₁ : Fin N) (E₀ κ A K₀ : ℝ)
    (Dom : Set ((Site d → Spin N) × Spin N)) : Prop where
  ne : i₀ ≠ i₁
  zero_mem : ∀ X ∈ T.polys, (0 : Site d) ∈ X
  dist_nonneg : ∀ X ∈ T.polys, 0 ≤ T.dist X
  diam : ∀ X ∈ T.polys, ∀ x ∈ X, ((∑ μ, |x μ| : ℤ) : ℝ) ≤ A * (1 + T.dist X)
  count_summable : Summable fun X : T.polys => wt κ X.1 (T.dist X.1)
  count_le : ∑' X : T.polys, wt κ X.1 (T.dist X.1) ≤ K₀
  bdd_dom : ∀ X ∈ T.polys, ∀ p ∈ Dom,
    ‖T.term X (pack X p.1 p.2)‖ ≤ E₀ * Real.exp (-κ * T.dist X)

theorem PremisesTermAniso.toGeom {T : TermFamily d N} {i₀ i₁ : Fin N} {ν r E₀ κ A K₀ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} (h : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom) :
    PremisesGeom T i₀ i₁ E₀ κ A K₀ Dom :=
  ⟨h.ne, h.zero_mem, h.dist_nonneg, h.diam, h.count_summable, h.count_le, h.bdd_dom⟩

theorem PremisesTerm.toGeom {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} (h : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) :
    PremisesGeom T i₀ i₁ E₀ κ A K₀ Dom :=
  ⟨h.ne, h.zero_mem, h.dist_nonneg, h.diam, h.count_summable, h.count_le, h.bdd_dom⟩

/-- The context of the local analysis on the pinned domain: `CtxAniso` with the geometric
premises in place of the premises on `TubeAniso`. -/
structure CtxPin (T : TermFamily d N) (i₀ i₁ : Fin N) (ν r E₀ κ A K₀ Λ : ℝ)
    (Dom : Set ((Site d → Spin N) × Spin N)) (ψ : Site d → Spin N) (b : Spin N)
    (σ ε K₂ : ℝ) (u : ℂ) (R : Matrix (Fin N) (Fin N) ℂ) : Prop where
  geom : PremisesGeom T i₀ i₁ E₀ κ A K₀ Dom
  dat : DataHypAniso Dom ν σ ε K₂ ψ b
  frame : Frame i₀ σ ε ψ u R
  σpos : 0 < σ
  σle : σ ≤ 1
  εpos : 0 < ε
  εle : ε ≤ Λ * r
  rpos : 0 < r
  rle : r ≤ 1
  ν0 : 0 ≤ ν
  νσ : ν ≤ σ ^ 2
  E0nn : 0 ≤ E₀
  Ann : 0 ≤ A
  τle : σ ^ 2 * ε ≤ 1 / 4

/-- The family with the same polymers and distances and all terms zero. -/
def zeroFam (T : TermFamily d N) : TermFamily d N where
  polys := T.polys
  dist := T.dist
  term := fun _ _ => 0

/-- The term-free part of the context: `CtxPin` gives `CtxAniso` for the zero family, whose
term-independent lemmas (`l1_le`, `rotDiff_le`, `zc_gauge_le`, ...) are used verbatim. -/
theorem CtxPin.zero {T : TermFamily d N} {i₀ i₁ : Fin N} {ν r E₀ κ A K₀ Λ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} {ψ : Site d → Spin N} {b : Spin N}
    {σ ε K₂ : ℝ} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}
    (c : CtxPin T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R) :
    CtxAniso (zeroFam T) i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R := by
  have hE := c.E0nn
  refine ⟨⟨c.geom.ne, c.geom.zero_mem, c.geom.dist_nonneg, c.geom.diam, c.geom.count_summable,
    c.geom.count_le, ?_, ?_, ?_, ?_⟩, c.dat, c.frame, c.σpos, c.σle, c.εpos, c.εle, c.rpos, c.rle,
    c.ν0, c.νσ, c.E0nn, c.Ann, c.τle⟩
  · intro X _; exact analyticOnNhd_const
  · intro X _ y _; simp only [zeroFam, norm_zero]; positivity
  · intro X _ p _; simp only [zeroFam, norm_zero]; positivity
  · intro X _ y _ R _ _ _; rfl

/-! ### The certificate -/

/-- **The reference-jet certificate of one term** (PIN-I6 §3, `PinJet` items 1, 2, 3; item 4,
the physical values, is `PremisesGeom.bdd_dom`).  With `M = E₀ e^{-κ d_j(X)}`, `P` the reference
point, `δ = (ψ̃ - ψ̃(0))` the rotated spin difference, `z_c` the rotated constant displacement:

* `germ`: `TermOK` at some radius (analyticity and rotation invariance near the reference point);
* tensor bounds `|a_X| ≤ M/r`, `|B_X|, |A_X|, |m_X| ≤ 4M/r²`;
* `small`: for small polymers, the values at the two actual configurations are the values at the
  rotated points, the second-order Taylor difference is at most `2M(Z³ + Z₀³)` and
  `|D²f(P)[z_c, δ]| ≤ 4 M Z₀ (D/r)`, with the quantities of `smallBndA`;
* `potential`: the constant-potential remainder (3.1). -/
structure PinJetTerm (T : TermFamily d N) (i₀ i₁ : Fin N) (ν r E₀ κ A Λ : ℝ)
    (ψ : Site d → Spin N) (b : Spin N) (σ ε : ℝ) (R : Matrix (Fin N) (Fin N) ℂ)
    (X : Finset (Site d)) : Prop where
  germ : ∃ ρ : ℝ, TermOK i₀ ν ρ X (T.term X)
  tensA_le : ∀ x : ↥X, ‖tensA i₀ ν X (T.term X) x‖ ≤ E₀ * Real.exp (-κ * T.dist X) / r
  tensB_le : ∀ x x' : ↥X,
    ‖tensB i₀ i₁ ν X (T.term X) x x'‖ ≤ 4 * (E₀ * Real.exp (-κ * T.dist X)) / r ^ 2
  tensAA_le : ∀ x x' : ↥X,
    ‖tensAA i₀ ν X (T.term X) x x'‖ ≤ 4 * (E₀ * Real.exp (-κ * T.dist X)) / r ^ 2
  tensM_le : ∀ x : ↥X,
    ‖tensM i₀ i₁ ν X (T.term X) x‖ ≤ 4 * (E₀ * Real.exp (-κ * T.dist X)) / r ^ 2
  small : (cZA N Λ + cK1 N A) * (1 + T.dist X) * σ * ε ≤ r / 2 →
    T.term X (pack X ψ b) =
        T.term X (refPt i₀ ν X + (zcfg X i₀ ν ψ b R + pack X (rotDiff R ψ) 0)) ∧
      T.term X (pack X (fun _ => ψ 0) b) = T.term X (refPt i₀ ν X + zcfg X i₀ ν ψ b R) ∧
      ‖T.term X (refPt i₀ ν X + (zcfg X i₀ ν ψ b R + pack X (rotDiff R ψ) 0))
          - T.term X (refPt i₀ ν X + zcfg X i₀ ν ψ b R)
          - fderiv ℂ (T.term X) (refPt i₀ ν X) (pack X (rotDiff R ψ) 0)
          - D2 (T.term X) (refPt i₀ ν X) (zcfg X i₀ ν ψ b R) (pack X (rotDiff R ψ) 0)
          - (1 / 2 : ℂ) * D2 (T.term X) (refPt i₀ ν X) (pack X (rotDiff R ψ) 0)
              (pack X (rotDiff R ψ) 0)‖ ≤
        2 * (E₀ * Real.exp (-κ * T.dist X)) *
            ((sZ0A N Λ σ ε + sD N A σ ε (1 + T.dist X)) / r) ^ 3 +
          2 * (E₀ * Real.exp (-κ * T.dist X)) * (sZ0A N Λ σ ε / r) ^ 3 ∧
      ‖D2 (T.term X) (refPt i₀ ν X) (zcfg X i₀ ν ψ b R) (pack X (rotDiff R ψ) 0)‖ ≤
        4 * (E₀ * Real.exp (-κ * T.dist X)) * (sZ0A N Λ σ ε / r) *
          (sD N A σ ε (1 + T.dist X) / r)
  potential : ‖T.term X (pack X (fun _ => ψ 0) b) - Ttw T i₀ ν X ψ b‖ ≤
    12 * (X.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X)) * cZA N Λ ^ 2 *
      (σ ^ 4 * (ε / r) ^ 2)

/-- **The reference-jet certificate of a term family** at the data `(ψ, b)` with the frame
rotation `R`: `PinJetTerm` for every polymer. -/
structure PinJet (T : TermFamily d N) (i₀ i₁ : Fin N) (ν r E₀ κ A Λ : ℝ)
    (ψ : Site d → Spin N) (b : Spin N) (σ ε : ℝ) (R : Matrix (Fin N) (Fin N) ℂ) : Prop where
  term : ∀ X ∈ T.polys, PinJetTerm T i₀ i₁ ν r E₀ κ A Λ ψ b σ ε R X

/-! ### The local estimate with the certificate -/

section Local

variable {i₀ i₁ : Fin N} {ν ρ r : ℝ} {X : Finset (Site d)} {f : Cfg d N X → ℂ}

/-- `TermOK.local_bound_aniso` with the polydisc inputs (`aniso_taylor_diff`, `aniso_norm_D2_le`,
the tensor Cauchy bounds) replaced by their certificate values. -/
theorem TermOK.local_bound_pin (hf : TermOK i₀ ν ρ X f) (hi : i₁ ≠ i₀) {M : ℝ} (hr : 0 < r)
    (hM0 : 0 ≤ M) (hν : 0 ≤ ν) (φ : Site d → Spin N) (ga : Site d → ℂ) (G : Fin d → Fin d → ℂ)
    (zc : Cfg d N X) {Z Z0 D F Ee Eb : ℝ} (hF0 : 0 ≤ F)
    (hD : ∀ x ∈ X, ‖φ x‖ ≤ D) (hF : ∀ x ∈ X, ‖φ x i₀‖ ≤ F)
    (hE : ∀ x ∈ X, ‖φ x i₀ - ga x / 2 + dotT i₀ (φ x) (φ x) / 2‖ ≤ Ee)
    (hEb : ∀ x ∈ X, ∀ x' ∈ X,
      ‖dotT i₀ (φ x - φ x') (φ x - φ x') - wquad G x x'‖ ≤ Eb)
    (hTb : ‖f (refPt i₀ ν X + (zc + pack X φ 0)) - f (refPt i₀ ν X + zc)
        - fderiv ℂ f (refPt i₀ ν X) (pack X φ 0) - D2 f (refPt i₀ ν X) zc (pack X φ 0)
        - (1 / 2 : ℂ) * D2 f (refPt i₀ ν X) (pack X φ 0) (pack X φ 0)‖ ≤
        2 * M * Z ^ 3 + 2 * M * Z0 ^ 3)
    (t2 : ‖D2 f (refPt i₀ ν X) zc (pack X φ 0)‖ ≤ 4 * M * Z0 * (D / r))
    (hbA : ∀ x : ↥X, ‖tensA i₀ ν X f x‖ ≤ M / r)
    (hbB : ∀ x x' : ↥X, ‖tensB i₀ i₁ ν X f x x'‖ ≤ 4 * M / r ^ 2)
    (hbAA : ∀ x x' : ↥X, ‖tensAA i₀ ν X f x x'‖ ≤ 4 * M / r ^ 2)
    (hbM : ∀ x : ↥X, ‖tensM i₀ i₁ ν X f x‖ ≤ 4 * M / r ^ 2) :
    ‖f (refPt i₀ ν X + (zc + pack X φ 0)) - f (refPt i₀ ν X + zc)
        - (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X f x * ga x.1
        + (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' * wquad G x.1 x'.1‖ ≤
      2 * M * Z ^ 3 + 2 * M * Z0 ^ 3 + 4 * M * Z0 * (D / r)
        + (X.card : ℝ) * (M / r) * Ee + 2 * (X.card : ℝ) ^ 2 * M * F ^ 2 / r ^ 2
        + ν / 2 * (X.card : ℝ) * (4 * M / r ^ 2) * (N * D ^ 2)
        + (X.card : ℝ) ^ 2 * (M / r ^ 2) * Eb := by
  classical
  set P := refPt i₀ ν X with hP
  set δ : Cfg d N X := pack X φ 0 with hδ
  have hcard : (Fintype.card ↥X : ℝ) = X.card := by simp
  -- shape
  have hlin := hf.lin_pack φ
  have hquad := hf.quad_pack hi φ φ
  have hward := ward_algebra i₀ (ν : ℂ) (fun x => tensA i₀ ν X f x) (fun x => tensM i₀ i₁ ν X f x)
    (fun x x' => tensB i₀ i₁ ν X f x x') (fun x x' => hf.tensB_symm x x')
    (fun x' => hf.ward hi x') (fun x : ↥X => φ x.1)
  -- exact identity
  have hs1 : ∑ x : ↥X, tensA i₀ ν X f x * (φ x.1 i₀ - ga x.1 / 2 + dotT i₀ (φ x.1) (φ x.1) / 2) =
      ∑ x : ↥X, tensA i₀ ν X f x * φ x.1 i₀ - (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X f x * ga x.1
        + (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X f x * dotT i₀ (φ x.1) (φ x.1) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hs2 : ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' *
        (dotT i₀ (φ x.1 - φ x'.1) (φ x.1 - φ x'.1) - wquad G x.1 x'.1) =
      ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' * dotT i₀ (φ x.1 - φ x'.1) (φ x.1 - φ x'.1)
        - ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' * wquad G x.1 x'.1 := by
    simp only [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => by ring
  have hs3 : ∑ x : ↥X, ∑ x' : ↥X, (tensAA i₀ ν X f x x' * (φ x.1 i₀ * φ x'.1 i₀) +
        tensB i₀ i₁ ν X f x x' * dotT i₀ (φ x.1) (φ x'.1)) =
      ∑ x : ↥X, ∑ x' : ↥X, tensAA i₀ ν X f x x' * (φ x.1 i₀ * φ x'.1 i₀) +
      ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' * dotT i₀ (φ x.1) (φ x'.1) := by
    simp only [Finset.sum_add_distrib]
  have hid : f (P + (zc + δ)) - f (P + zc) - (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X f x * ga x.1
        + (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' * wquad G x.1 x'.1 =
      (f (P + (zc + δ)) - f (P + zc) - fderiv ℂ f P δ - D2 f P zc δ
        - (1 / 2 : ℂ) * D2 f P δ δ) + D2 f P zc δ
      + ∑ x : ↥X, tensA i₀ ν X f x * (φ x.1 i₀ - ga x.1 / 2 + dotT i₀ (φ x.1) (φ x.1) / 2)
      + (1 / 2 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensAA i₀ ν X f x x' * (φ x.1 i₀ * φ x'.1 i₀)
      - ((ν : ℂ) / 2) * ∑ x : ↥X, tensM i₀ i₁ ν X f x * dotT i₀ (φ x.1) (φ x.1)
      - (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' *
          (dotT i₀ (φ x.1 - φ x'.1) (φ x.1 - φ x'.1) - wquad G x.1 x'.1) := by
    rw [hs1, hs2]
    rw [hs3] at hquad
    simp only [neg_mul] at hward
    linear_combination hlin * (1 : ℂ) + (1 / 2 : ℂ) * hquad + hward
  rw [hid]
  have hcr : 0 ≤ M / r := by positivity
  have hcr2 : 0 ≤ 4 * M / r ^ 2 := by positivity
  have hθ : ∀ x : ↥X, ‖dotT i₀ (φ x.1) (φ x.1)‖ ≤ N * D ^ 2 := fun x =>
    (norm_dotT_self_le i₀ _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hD x.1 x.2) 2) (by positivity))
  -- the six terms
  have t3 : ‖∑ x : ↥X, tensA i₀ ν X f x * (φ x.1 i₀ - ga x.1 / 2 + dotT i₀ (φ x.1) (φ x.1) / 2)‖
      ≤ (X.card : ℝ) * (M / r) * Ee := by
    refine (norm_sum_le_card _ (c := M / r * Ee) fun x => ?_).trans (by rw [hcard]; ring_nf; rfl)
    rw [norm_mul]
    exact mul_le_mul (hbA x) (hE x.1 x.2) (norm_nonneg _) hcr
  have t4 : ‖(1 / 2 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensAA i₀ ν X f x x' * (φ x.1 i₀ * φ x'.1 i₀)‖
      ≤ 2 * (X.card : ℝ) ^ 2 * M * F ^ 2 / r ^ 2 := by
    rw [norm_mul]
    have h1 : ‖∑ x : ↥X, ∑ x' : ↥X, tensAA i₀ ν X f x x' * (φ x.1 i₀ * φ x'.1 i₀)‖ ≤
        (Fintype.card ↥X : ℝ) * ((Fintype.card ↥X : ℝ) * (4 * M / r ^ 2 * F ^ 2)) := by
      refine norm_sum_le_card _ fun x => ?_
      refine norm_sum_le_card _ fun x' => ?_
      rw [norm_mul, norm_mul]
      have := mul_le_mul (hF x.1 x.2) (hF x'.1 x'.2) (norm_nonneg _) hF0
      calc ‖tensAA i₀ ν X f x x'‖ * (‖φ x.1 i₀‖ * ‖φ x'.1 i₀‖)
          ≤ 4 * M / r ^ 2 * (F * F) := mul_le_mul (hbAA x x') this (by positivity) hcr2
        _ = 4 * M / r ^ 2 * F ^ 2 := by ring
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h2, hcard] at *
    calc 1 / 2 * ‖∑ x : ↥X, ∑ x' : ↥X, tensAA i₀ ν X f x x' * (φ x.1 i₀ * φ x'.1 i₀)‖
        ≤ 1 / 2 * ((X.card : ℝ) * ((X.card : ℝ) * (4 * M / r ^ 2 * F ^ 2))) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 2 * (X.card : ℝ) ^ 2 * M * F ^ 2 / r ^ 2 := by ring
  have t5 : ‖((ν : ℂ) / 2) * ∑ x : ↥X, tensM i₀ i₁ ν X f x * dotT i₀ (φ x.1) (φ x.1)‖
      ≤ ν / 2 * (X.card : ℝ) * (4 * M / r ^ 2) * (N * D ^ 2) := by
    rw [norm_mul]
    have h1 : ‖∑ x : ↥X, tensM i₀ i₁ ν X f x * dotT i₀ (φ x.1) (φ x.1)‖ ≤
        (Fintype.card ↥X : ℝ) * (4 * M / r ^ 2 * (N * D ^ 2)) := by
      refine norm_sum_le_card _ fun x => ?_
      rw [norm_mul]
      exact mul_le_mul (hbM x) (hθ x) (norm_nonneg _) hcr2
    have h2 : ‖((ν : ℂ) / 2)‖ = ν / 2 := by
      rw [norm_div]; simp [abs_of_nonneg hν]
    rw [h2, hcard] at *
    calc ν / 2 * ‖∑ x : ↥X, tensM i₀ i₁ ν X f x * dotT i₀ (φ x.1) (φ x.1)‖
        ≤ ν / 2 * ((X.card : ℝ) * (4 * M / r ^ 2 * (N * D ^ 2))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have t6 : ‖(1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' *
        (dotT i₀ (φ x.1 - φ x'.1) (φ x.1 - φ x'.1) - wquad G x.1 x'.1)‖
      ≤ (X.card : ℝ) ^ 2 * (M / r ^ 2) * Eb := by
    rw [norm_mul]
    have h1 : ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' *
        (dotT i₀ (φ x.1 - φ x'.1) (φ x.1 - φ x'.1) - wquad G x.1 x'.1)‖ ≤
        (Fintype.card ↥X : ℝ) * ((Fintype.card ↥X : ℝ) * (4 * M / r ^ 2 * Eb)) := by
      refine norm_sum_le_card _ fun x => ?_
      refine norm_sum_le_card _ fun x' => ?_
      rw [norm_mul]
      exact mul_le_mul (hbB x x') (hEb x.1 x.2 x'.1 x'.2) (norm_nonneg _) hcr2
    have h2 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
    rw [h2, hcard] at *
    calc 1 / 4 * ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X f x x' *
          (dotT i₀ (φ x.1 - φ x'.1) (φ x.1 - φ x'.1) - wquad G x.1 x'.1)‖
        ≤ 1 / 4 * ((X.card : ℝ) * ((X.card : ℝ) * (4 * M / r ^ 2 * Eb))) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = _ := by ring
  have tri : ∀ a b c d e g : ℂ,
      ‖a + b + c + d - e - g‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖g‖ := by
    intro a b c d e g
    have h1 := norm_sub_le (a + b + c + d - e) g
    have h2 := norm_sub_le (a + b + c + d) e
    have h3 := norm_add_le (a + b + c) d
    have h4 := norm_add_le (a + b) c
    have h5 := norm_add_le a b
    linarith
  refine (tri _ _ _ _ _ _).trans ?_
  linarith [hTb, t2, t3, t4, t5, t6]

end Local

/-! ### The per-term estimates with the certificate -/

section CtxPin

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν r E₀ κ A K₀ Λ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)} {ψ : Site d → Spin N} {b : Spin N}
  {σ ε K₂ : ℝ} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}

theorem CtxPin.card_pos (c : CtxPin T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) : 1 ≤ X.card :=
  Finset.card_pos.mpr ⟨0, c.geom.zero_mem X hX⟩

theorem CtxPin.l1_le (c : CtxPin T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) {x : Site d} (hx : x ∈ X) :
    (l1 x : ℝ) ≤ A * (1 + T.dist X) := by
  rw [l1_cast]; exact c.geom.diam X hX x hx

theorem CtxPin.itw_eq (c : CtxPin T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    (X : Finset (Site d)) :
    Itw T i₀ i₁ ν X ψ b = Dlt T i₀ i₁ ν R ψ b X +
      (T.term X (pack X (fun _ => ψ 0) b) - Ttw T i₀ ν X ψ b) := by
  unfold Itw
  rw [c.frame.phitw_eq c.τle, Dlt_eq]
  ring

/-- **The local estimate** for a polymer with `(C₁ + Λ + κ₁)(1 + d_j(X)) σ ε ≤ r/2`, from the
certificate (replaces `CtxAniso.small_case`). -/
theorem CtxPin.small_case (c : CtxPin T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys)
    (jet : PinJetTerm T i₀ i₁ ν r E₀ κ A Λ ψ b σ ε R X)
    (hs : (cZA N Λ + cK1 N A) * (1 + T.dist X) * σ * ε ≤ r / 2) :
    ‖T.term X (pack X ψ b) - T.term X (pack X (fun _ => ψ 0) b)
        - (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x *
            (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))
        + (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
            wquad (gradTensor i₀ R ψ) x.1 x'.1‖ ≤
      smallBndA N A Λ (E₀ * Real.exp (-κ * T.dist X)) r ν σ ε K₂ (1 + T.dist X) X.card := by
  have c0 := c.zero
  obtain ⟨ρ', hok⟩ := jet.germ
  obtain ⟨e1, e2, hTb, t2⟩ := jet.small hs
  have hne : i₁ ≠ i₀ := c.geom.ne.symm
  have hd0 : 0 ≤ T.dist X := c.geom.dist_nonneg X hX
  set t : ℝ := 1 + T.dist X with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hσ := c.σpos
  have hε := c.εpos
  have hr := c.rpos
  have hΛ := c0.Λnn
  have hK1 : 0 ≤ cK1 N A := by unfold cK1; have := c.Ann; positivity
  have hCZ : 0 ≤ cZA N Λ := cZA_nonneg N hΛ
  have hτ0 : 0 ≤ σ ^ 2 * ε := by positivity
  have hD0 : 0 ≤ sD N A σ ε t := by unfold sD; positivity
  have hZ0n : 0 ≤ sZ0A N Λ σ ε := by unfold sZ0A; positivity
  have hDφ : ∀ x ∈ X, ‖rotDiff R ψ x‖ ≤ sD N A σ ε t := by
    intro x hx
    refine (c0.rotDiff_le x).trans ?_
    unfold sD cK1
    have := c.l1_le hX hx
    have h2 : 0 ≤ σ * ε := by positivity
    calc (N : ℝ) * 40 * ((l1 x : ℝ) * (σ * ε)) ≤ N * 40 * (A * t * (σ * ε)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ h2) (by positivity)
          simpa [ht] using this
      _ = _ := by ring
  have hpk : anisoGauge i₀ r X (pack X (rotDiff R ψ) 0) ≤ sD N A σ ε t / r :=
    anisoGauge_pack_zero_le hr _ hD0 hDφ
  have hzc : anisoGauge i₀ r X (zcfg X i₀ ν ψ b R) ≤ sZ0A N Λ σ ε / r := c0.zc_gauge_le X
  have hz : anisoGauge i₀ r X (zcfg X i₀ ν ψ b R + pack X (rotDiff R ψ) 0) ≤
      (sZ0A N Λ σ ε + sD N A σ ε t) / r := by
    rw [add_div]
    exact (anisoGauge_add_le _ _).trans (add_le_add hzc hpk)
  have hsum : sZ0A N Λ σ ε + sD N A σ ε t ≤ r / 2 := by
    refine le_trans ?_ hs
    unfold sZ0A sD
    have h1 : σ ^ 2 * ε ≤ t * σ * ε := by
      have : σ ≤ 1 := c.σle
      nlinarith [mul_pos hσ hε]
    nlinarith [mul_pos hσ hε, mul_nonneg hCZ (sub_nonneg.mpr h1)]
  have hZ0 : sZ0A N Λ σ ε / r ≤ 1 / 2 := by
    rw [div_le_iff₀ hr]; linarith
  rw [e1, e2]
  -- the longitudinal and transverse bounds
  have hlong : ∀ x ∈ X, ‖rotDiff R ψ x (i₀)‖ ≤ sF N A σ ε t ∧
      ‖rotDiff R ψ x i₀ - (dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)) / 2 +
        dotT i₀ (rotDiff R ψ x) (rotDiff R ψ x) / 2‖ ≤ sEe N A σ ε t := by
    intro x hx
    have hθ : ‖dotT i₀ (rotDiff R ψ x) (rotDiff R ψ x)‖ ≤ N * sD N A σ ε t ^ 2 :=
      (norm_dotT_self_le i₀ _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hDφ x hx) 2) hN)
    have hφ : ‖rotDiff R ψ x i₀‖ ≤ 1 / 2 := by
      refine (norm_le_pi_norm _ i₀).trans ((hDφ x hx).trans ?_)
      have := c.rle; linarith
    exact long_bounds (u := u) (φ0 := rotDiff R ψ x i₀)
      (θ := dotT i₀ (rotDiff R ψ x) (rotDiff R ψ x))
      (g := dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)) c.frame.u_close c.τle (c0.ga_le x) hθ hφ
      (c.frame.long_identity x)
  have hEb : ∀ x ∈ X, ∀ x' ∈ X, ‖dotT i₀ (rotDiff R ψ x - rotDiff R ψ x')
      (rotDiff R ψ x - rotDiff R ψ x') - wquad (gradTensor i₀ R ψ) x x'‖ ≤
      sEb N A σ ε K₂ t := by
    intro x hx x' hx'
    have hR : ∀ i k, ‖R i k‖ ≤ 40 := fun i k => by
      have := c.frame.bd i k; simpa [rotBound] using this
    exact dotT_diff_bound hR c.dat.adj c.dat.sec x x' (L := A * t)
      (by simpa [ht] using c.l1_le hX hx) (by simpa [ht] using c.l1_le hX hx')
      (by have := c.Ann; positivity) i₀ (by positivity) c.dat.K2_nonneg
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X) := by have := c.E0nn; positivity
  exact hok.local_bound_pin hne hr hM0 c.ν0 (rotDiff R ψ)
    (fun y => dot (ψ y) (ψ y) - dot (ψ 0) (ψ 0)) (gradTensor i₀ R ψ) (zcfg X i₀ ν ψ b R)
    (Z := (sZ0A N Λ σ ε + sD N A σ ε t) / r) (Z0 := sZ0A N Λ σ ε / r) (D := sD N A σ ε t)
    (F := sF N A σ ε t) (Ee := sEe N A σ ε t) (Eb := sEb N A σ ε K₂ t)
    (by unfold sF; positivity) hDφ (fun x hx => (hlong x hx).1)
    (fun x hx => (hlong x hx).2) hEb hTb t2 jet.tensA_le jet.tensB_le jet.tensAA_le jet.tensM_le

/-- Bound for the first-order term `A_X` from the certificate. -/
theorem CtxPin.A_le (c : CtxPin T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (jet : PinJetTerm T i₀ i₁ ν r E₀ κ A Λ ψ b σ ε R X) :
    ‖(1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x *
      (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))‖ ≤
      X.card * (E₀ * Real.exp (-κ * T.dist X) / r * (σ ^ 2 * ε)) := by
  have c0 := c.zero
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by have := c.E0nn; positivity
  have hr := c.rpos
  have hcard : (Fintype.card ↥X : ℝ) = X.card := by simp
  have hcr : 0 ≤ M / r := by positivity
  rw [norm_mul]
  have h1 : ‖∑ x : ↥X, tensA i₀ ν X (T.term X) x * (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))‖ ≤
      (Fintype.card ↥X : ℝ) * (M / r * (2 * (σ ^ 2 * ε))) := by
    refine norm_sum_le_card _ fun x => ?_
    rw [norm_mul]
    exact mul_le_mul (jet.tensA_le x) (c0.ga_le x.1) (norm_nonneg _) hcr
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h2, hcard] at *
  calc 1 / 2 * ‖∑ x : ↥X, tensA i₀ ν X (T.term X) x * (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))‖
      ≤ 1 / 2 * ((X.card : ℝ) * (M / r * (2 * (σ ^ 2 * ε)))) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = _ := by ring

/-- Bound for the quadratic term `L_X` from the certificate. -/
theorem CtxPin.Lq_le (c : CtxPin T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys)
    (jet : PinJetTerm T i₀ i₁ ν r E₀ κ A Λ ψ b σ ε R X) :
    ‖(1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
      wquad (gradTensor i₀ R ψ) x.1 x'.1‖ ≤
      (X.card : ℝ) ^ 2 * (E₀ * Real.exp (-κ * T.dist X) / r ^ 2) *
        ((2 * (A * (1 + T.dist X))) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2)) := by
  have c0 := c.zero
  have hd0 : 0 ≤ T.dist X := c.geom.dist_nonneg X hX
  set t : ℝ := 1 + T.dist X with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by have := c.E0nn; positivity
  have hr := c.rpos
  have hσ := c.σpos
  have hε := c.εpos
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hcard : (Fintype.card ↥X : ℝ) = X.card := by simp
  have hcr2 : 0 ≤ 4 * M / r ^ 2 := by positivity
  have hGm : ∀ μ μ', ‖gradTensor i₀ R ψ μ μ'‖ ≤ N * (N * 40 * (σ * ε)) ^ 2 := by
    intro μ μ'
    have hφ : ∀ ν', ‖rotDiff R ψ (eU ν')‖ ≤ N * 40 * (σ * ε) := fun ν' => by
      have := c0.rotDiff_le (eU ν')
      rwa [l1_eU, Nat.cast_one, one_mul] at this
    refine (norm_dotT_le i₀ _ _).trans ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hφ μ) (hφ μ') (norm_nonneg _) (by positivity)) hN
  rw [norm_mul]
  have h1 : ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
      wquad (gradTensor i₀ R ψ) x.1 x'.1‖ ≤ (Fintype.card ↥X : ℝ) * ((Fintype.card ↥X : ℝ) *
        (4 * M / r ^ 2 * ((2 * (A * t)) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2)))) := by
    refine norm_sum_le_card _ fun x => ?_
    refine norm_sum_le_card _ fun x' => ?_
    rw [norm_mul]
    refine mul_le_mul (jet.tensB_le x x') ?_ (norm_nonneg _) (by positivity)
    refine (norm_wquad_le _ hGm x.1 x'.1).trans ?_
    have hl : (l1 (x.1 - x'.1) : ℝ) ≤ 2 * (A * t) := by
      have := l1_sub_le x.1 x'.1
      have h3 : (l1 (x.1 - x'.1) : ℝ) ≤ l1 x.1 + l1 x'.1 := by exact_mod_cast this
      have h4 := c.l1_le hX x.2
      have h5 := c.l1_le hX x'.2
      simp only [ht] at *
      linarith
    have hl0 : (0 : ℝ) ≤ l1 (x.1 - x'.1) := Nat.cast_nonneg _
    have : 0 ≤ (N : ℝ) * (N * 40 * (σ * ε)) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hl0 hl 2) this
  have h2 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
  rw [h2, hcard] at *
  calc 1 / 4 * ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
        wquad (gradTensor i₀ R ψ) x.1 x'.1‖
      ≤ 1 / 4 * ((X.card : ℝ) * ((X.card : ℝ) *
        (4 * M / r ^ 2 * ((2 * (A * t)) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2))))) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = _ := by ring

/-- The crude bound for the polymers with large `d_j(X)` from the certificate (replaces
`CtxAniso.tail_case`): only the physical values and the reference tensors are used. -/
theorem CtxPin.tail_case (c : CtxPin T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys)
    (jet : PinJetTerm T i₀ i₁ ν r E₀ κ A Λ ψ b σ ε R X) :
    ‖T.term X (pack X ψ b) - T.term X (pack X (fun _ => ψ 0) b)
        - (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x *
            (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))
        + (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
            wquad (gradTensor i₀ R ψ) x.1 x'.1‖ ≤
      tailBnd N A (E₀ * Real.exp (-κ * T.dist X)) r σ ε (1 + T.dist X) X.card := by
  set t : ℝ := 1 + T.dist X with ht
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hr := c.rpos
  have a1 : ‖T.term X (pack X ψ b)‖ ≤ M := c.geom.bdd_dom X hX (ψ, b) c.dat.mem
  have a2 : ‖T.term X (pack X (fun _ => ψ 0) b)‖ ≤ M :=
    c.geom.bdd_dom X hX ((fun _ => ψ 0), b) c.dat.mem_const
  have a3 := c.A_le jet
  have a4 := c.Lq_le hX jet
  have tri : ∀ a b c e : ℂ, ‖a - b - c + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖e‖ := by
    intro a b c e
    have h1 := norm_add_le (a - b - c) e
    have h2 := norm_sub_le (a - b) c
    have h3 := norm_sub_le a b
    linarith
  refine (tri _ _ _ _).trans ?_
  unfold tailBnd
  have e : (X.card : ℝ) * (M / r * (σ ^ 2 * ε)) + (X.card : ℝ) ^ 2 * (M / r ^ 2) *
      ((2 * (A * t)) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2)) =
      M * ((X.card : ℝ) * (σ ^ 2 * ε / r) + 6400 * N ^ 3 * A ^ 2 * (X.card : ℝ) ^ 2 * t ^ 2 *
        (σ * ε / r) ^ 2) := by
    field_simp
    ring
  linarith [a1, a2, a3, a4, e]

/-- The per-term bound of the local part `Dlt X` before the weights are absorbed. -/
theorem CtxPin.dlt_bound_raw (c : CtxPin T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {Kc α₁ Cs Ct : ℝ} (hCs0 : 0 ≤ Cs) (hCt0 : 0 ≤ Ct)
    (hα0 : 0 < α₁) (hα1 : α₁ < 1)
    (hCs : ∀ (M ρ ν σ r K₂ t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → ρ ≤ 1 → 0 < r →
      r ≤ Λ → 0 ≤ ν → ν ≤ σ ^ 2 → 1 ≤ t → 1 ≤ P → 0 ≤ K₂ → K₂ ≤ Kc * Sσ * (r * ρ) →
      SigPow σ α₁ Tσ Sσ →
      smallBndA N A Λ M ρ ν σ (r * ρ) K₂ t P ≤ Cs * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hCt : ∀ (M ρ σ r t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → 0 < r → r ≤ Λ → 1 ≤ t →
      1 ≤ P → 1 < 2 * (cZA N Λ + cK1 N A) * t * σ * r → SigPow σ α₁ Tσ Sσ →
      tailBnd N A M ρ σ (r * ρ) t P ≤ Ct * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hK : K₂ ≤ Kc * σ ^ (2 - α₁) * ε) {X : Finset (Site d)} (hX : X ∈ T.polys)
    (jet : PinJetTerm T i₀ i₁ ν r E₀ κ A Λ ψ b σ ε R X) :
    ‖Dlt T i₀ i₁ ν R ψ b X‖ ≤
      (Cs + Ct) * (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / r) ^ 2) := by
  have c0 := c.zero
  have hr := c.rpos
  have hεpos := c.εpos
  have hd0 : 0 ≤ T.dist X := c.geom.dist_nonneg X hX
  have hS := sigPow σ α₁ c.σpos c.σle hα0 hα1
  set q : ℝ := ε / r with hq
  have hq0 : 0 < q := by positivity
  have hqε : ε = q * r := by rw [hq]; field_simp
  have hqΛ : q ≤ Λ := by rw [hq, div_le_iff₀ hr]; exact c.εle
  set t : ℝ := 1 + T.dist X with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  have hP : (1 : ℝ) ≤ X.card := by exact_mod_cast c.card_pos hX
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by have := c.E0nn; positivity
  have hT0 : 0 ≤ σ ^ (3 - α₁) := (Real.rpow_pos_of_pos c.σpos _).le
  have hfin : ∀ C : ℝ, 0 ≤ C → C ≤ Cs + Ct → ‖Dlt T i₀ i₁ ν R ψ b X‖ ≤
      C * (M * (X.card : ℝ) ^ 2 * t ^ 6 * σ ^ (3 - α₁) * q ^ 2) →
      ‖Dlt T i₀ i₁ ν R ψ b X‖ ≤ (Cs + Ct) * (M * ((X.card : ℝ) ^ 2 * t ^ 6)) *
        (σ ^ (3 - α₁) * q ^ 2) := by
    intro C hC hle h
    refine h.trans ?_
    have hw : 0 ≤ M * ((X.card : ℝ) ^ 2 * t ^ 6) :=
      mul_nonneg hM0 (mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) 6))
    have : 0 ≤ σ ^ (3 - α₁) * q ^ 2 := mul_nonneg hT0 (sq_nonneg q)
    calc C * (M * (X.card : ℝ) ^ 2 * t ^ 6 * σ ^ (3 - α₁) * q ^ 2)
        = C * (M * ((X.card : ℝ) ^ 2 * t ^ 6)) * (σ ^ (3 - α₁) * q ^ 2) := by ring
      _ ≤ (Cs + Ct) * (M * ((X.card : ℝ) ^ 2 * t ^ 6)) * (σ ^ (3 - α₁) * q ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hw) this
  rw [Dlt]
  by_cases hsm : (cZA N Λ + cK1 N A) * t * σ * ε ≤ r / 2
  · have h1 := c.small_case hX jet hsm
    have h2 := hCs M r ν σ q K₂ t X.card (σ ^ (3 - α₁)) (σ ^ (2 - α₁)) α₁ hM0 hr c.rle hq0 hqΛ
      c.ν0 c.νσ ht1 hP c.dat.K2_nonneg (by rw [← hqε]; exact hK) hS
    rw [← hqε] at h2
    exact hfin Cs hCs0 (by linarith) (h1.trans h2)
  · have h1 := c.tail_case hX jet
    have hlt : 1 < 2 * (cZA N Λ + cK1 N A) * t * σ * q := by
      by_contra hcon
      push Not at hcon
      have := mul_le_mul_of_nonneg_right hcon hr.le
      rw [hqε] at hsm
      nlinarith
    have h2 := hCt M r σ q t X.card (σ ^ (3 - α₁)) (σ ^ (2 - α₁)) α₁ hM0 hr hq0 hqΛ ht1 hP hlt hS
    rw [← hqε] at h2
    exact hfin Ct hCt0 (by linarith) (h1.trans h2)

/-- **The per-term bound of `I(y,X)`** before the polynomial weight is absorbed. -/
theorem CtxPin.itw_bound_raw (c : CtxPin T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {Kc α₁ Cs Ct : ℝ} (hCs0 : 0 ≤ Cs) (hCt0 : 0 ≤ Ct)
    (hα0 : 0 < α₁) (hα1 : α₁ < 1)
    (hCs : ∀ (M ρ ν σ r K₂ t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → ρ ≤ 1 → 0 < r →
      r ≤ Λ → 0 ≤ ν → ν ≤ σ ^ 2 → 1 ≤ t → 1 ≤ P → 0 ≤ K₂ → K₂ ≤ Kc * Sσ * (r * ρ) →
      SigPow σ α₁ Tσ Sσ →
      smallBndA N A Λ M ρ ν σ (r * ρ) K₂ t P ≤ Cs * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hCt : ∀ (M ρ σ r t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → 0 < r → r ≤ Λ → 1 ≤ t →
      1 ≤ P → 1 < 2 * (cZA N Λ + cK1 N A) * t * σ * r → SigPow σ α₁ Tσ Sσ →
      tailBnd N A M ρ σ (r * ρ) t P ≤ Ct * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hK : K₂ ≤ Kc * σ ^ (2 - α₁) * ε) {X : Finset (Site d)} (hX : X ∈ T.polys)
    (jet : PinJetTerm T i₀ i₁ ν r E₀ κ A Λ ψ b σ ε R X) :
    ‖Itw T i₀ i₁ ν X ψ b‖ ≤
      (Cs + Ct + 12 * cZA N Λ ^ 2) *
        (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / r) ^ 2) := by
  have c0 := c.zero
  have hd0 : 0 ≤ T.dist X := c.geom.dist_nonneg X hX
  have h1 := c.dlt_bound_raw hCs0 hCt0 hα0 hα1 hCs hCt hK hX jet
  have h2 := jet.potential
  have hP : (1 : ℝ) ≤ X.card := by exact_mod_cast c.card_pos hX
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X) := by have := c.E0nn; positivity
  have ht6 : (1 : ℝ) ≤ (1 + T.dist X) ^ 6 := one_le_pow₀ (by linarith)
  have hS := sigPow σ α₁ c.σpos c.σle hα0 hα1
  have hs4 : σ ^ 4 ≤ σ ^ (3 - α₁) := hS.quart
  have hCZ : 0 ≤ cZA N Λ := cZA_nonneg N c0.Λnn
  have hr2 : 12 * (X.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X)) * cZA N Λ ^ 2 *
        (σ ^ 4 * (ε / r) ^ 2) ≤
      12 * cZA N Λ ^ 2 * (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / r) ^ 2) := by
    have hq : 0 ≤ (ε / r) ^ 2 := sq_nonneg _
    have hPP : (X.card : ℝ) ≤ (X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6 := by nlinarith
    calc 12 * (X.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X)) * cZA N Λ ^ 2 *
          (σ ^ 4 * (ε / r) ^ 2)
        = 12 * cZA N Λ ^ 2 * (E₀ * Real.exp (-κ * T.dist X) * (X.card : ℝ)) *
            (σ ^ 4 * (ε / r) ^ 2) := by ring
      _ ≤ 12 * cZA N Λ ^ 2 *
          (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
          (σ ^ (3 - α₁) * (ε / r) ^ 2) := by
          have : 0 ≤ 12 * cZA N Λ ^ 2 := by positivity
          gcongr
  rw [c.itw_eq]
  refine (norm_add_le _ _).trans ?_
  have hcomb : (Cs + Ct) *
      (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
      (σ ^ (3 - α₁) * (ε / r) ^ 2) +
      12 * cZA N Λ ^ 2 *
        (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / r) ^ 2) =
      (Cs + Ct + 12 * cZA N Λ ^ 2) *
        (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / r) ^ 2) := by ring
  rw [← hcomb]
  exact add_le_add h1 (h2.trans hr2)

end CtxPin

/-! ### The corrected termwise irrelevance theorem -/

theorem card_le_of_diam_geom {T : TermFamily d N} {i₀ i₁ : Fin N} {E₀ κ A K₀ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} (hP : PremisesGeom T i₀ i₁ E₀ κ A K₀ Dom)
    {X : Finset (Site d)} (hX : X ∈ T.polys) :
    (X.card : ℝ) ≤ (2 * (A * (1 + T.dist X)) + 1) ^ d := by
  classical
  set Rr : ℝ := A * (1 + T.dist X) with hRr
  have hR0 : 0 ≤ Rr := by
    have h0 := hP.diam X hX 0 (hP.zero_mem X hX)
    refine le_trans ?_ h0
    simp
  set m : ℤ := ⌊Rr⌋ with hm
  have hm0 : 0 ≤ m := Int.floor_nonneg.mpr hR0
  have hsub : X ⊆ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-m) m) := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro μ
    have h1 := hP.diam X hX x hx
    have h2 : |x μ| ≤ ∑ ν, |x ν| := Finset.single_le_sum (f := fun ν => |x ν|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ μ)
    have h3 : ((|x μ| : ℤ) : ℝ) ≤ Rr := by
      refine le_trans ?_ h1
      exact_mod_cast h2
    have h4 : |x μ| ≤ m := Int.le_floor.mpr h3
    exact Finset.mem_Icc.mpr (abs_le.mp h4)
  have hc := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at hc
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hc
  have hc' : (X.card : ℝ) ≤ (((m + 1 - -m).toNat : ℕ) : ℝ) ^ d := by exact_mod_cast hc
  refine hc'.trans ?_
  have hm1 : (((m + 1 - -m).toNat : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by
    have : ((m + 1 - -m).toNat : ℤ) = m + 1 - -m := Int.toNat_of_nonneg (by omega)
    have h2 : (((m + 1 - -m).toNat : ℕ) : ℝ) = (((m + 1 - -m).toNat : ℤ) : ℝ) := by
      norm_cast
    rw [h2, this]; push_cast; ring
  rw [hm1]
  have hmR : (m : ℝ) ≤ Rr := Int.floor_le Rr
  have h5 : 2 * (m : ℝ) + 1 ≤ 2 * Rr + 1 := by linarith
  have h6 : 0 ≤ 2 * (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ m := by exact_mod_cast hm0
    linarith
  exact pow_le_pow_left₀ h6 h5 d

/-- **Corrected Lemma 3.2 (iii) on the pinned domain** (PIN-I6 §3, (3.2)): under the reference-jet
certificate `PinJetTerm` (for the normalizing rotation of the data), the geometric premises and the
numerical hypotheses of `termwise_irrelevant_aniso`,
`‖I(y,X)‖ ≤ C E₀ e^{-(κ-1) d_j(X)} σ^{3-α₁} (ε/r)²`.  No analyticity on `TubeAniso` is used. -/
theorem termwise_irrelevant_pin (d N : ℕ) (A Λ Ksig α₁ : ℝ) (hA : 0 ≤ A) (hΛ : 1 ≤ Λ)
    (hKsig : 0 ≤ Ksig) (hα0 : 0 < α₁) (hα1 : α₁ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν r E₀ κ K₀ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : PremisesGeom T i₀ i₁ E₀ κ A K₀ Dom) (ψ : Site d → Spin N) (b : Spin N)
      (σ ε K₂ : ℝ) (_ : DataHypAniso Dom ν σ ε K₂ ψ b) (X : Finset (Site d)) (_ : X ∈ T.polys),
      0 < r → r ≤ 1 → 0 < ε → ε ≤ Λ * r → 0 < σ → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 → 0 ≤ ν →
      ν ≤ σ ^ 2 → 0 ≤ E₀ → K₂ ≤ Ksig * σ ^ (2 - α₁) * ε →
      (∃ (u : ℂ) (R : Matrix (Fin N) (Fin N) ℂ), Frame i₀ σ ε ψ u R ∧
        PinJetTerm T i₀ i₁ ν r E₀ κ A Λ ψ b σ ε R X) →
      ‖Itw T i₀ i₁ ν X ψ b‖ ≤
        C * E₀ * Real.exp (-(κ - 1) * T.dist X) * (σ ^ (3 - α₁) * (ε / r) ^ 2) := by
  obtain ⟨Cs, hCs0, hCs⟩ := smallBndA_le N A Λ Ksig hA hΛ hKsig
  obtain ⟨Ct, hCt0, hCt⟩ := tailBndA_le N A Λ hA hΛ
  obtain ⟨Cw, hCw0, hCw⟩ := weight_absorb A hA d
  have hCZ : 0 ≤ cZA N Λ := cZA_nonneg N (by linarith)
  refine ⟨(Cs + Ct + 12 * cZA N Λ ^ 2) * Cw, by positivity, ?_⟩
  intro T i₀ i₁ ν r E₀ κ K₀ Dom hP ψ b σ ε K₂ dat X hX hr hr1 hε hεΛ hσ hσ1 hτ hν hνσ hE0 hK
    ⟨u, R, hF, jet⟩
  have c : CtxPin T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R :=
    ⟨hP, dat, hF, hσ, hσ1, hε, hεΛ, hr, hr1, hν, hνσ, hE0, hA, hτ⟩
  have h := c.itw_bound_raw hCs0 hCt0 hα0 hα1 hCs hCt hK hX jet
  refine h.trans ?_
  have hd0 := hP.dist_nonneg X hX
  have hcard := card_le_of_diam_geom hP hX
  have hab := hCw κ (T.dist X) (X.card : ℝ) hd0 (Nat.cast_nonneg _) hcard
  have hT0 : 0 ≤ σ ^ (3 - α₁) * (ε / r) ^ 2 :=
    mul_nonneg (Real.rpow_pos_of_pos hσ _).le (sq_nonneg _)
  have hCsum : 0 ≤ Cs + Ct + 12 * cZA N Λ ^ 2 := by positivity
  calc (Cs + Ct + 12 * cZA N Λ ^ 2) *
        (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / r) ^ 2)
      = (Cs + Ct + 12 * cZA N Λ ^ 2) * E₀ *
        (Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / r) ^ 2) := by ring
    _ ≤ (Cs + Ct + 12 * cZA N Λ ^ 2) * E₀ * (Cw * Real.exp (-(κ - 1) * T.dist X)) *
        (σ ^ (3 - α₁) * (ε / r) ^ 2) := by
        have : 0 ≤ (Cs + Ct + 12 * cZA N Λ ^ 2) * E₀ := mul_nonneg hCsum hE0
        gcongr
    _ = _ := by ring

/-- **The scaled form** of `termwise_irrelevant_pin`: with `σ = C₀ s` and
`ε/r ≤ K_R s^{(d-2)/2 - γ}`, `‖I(y,X)‖ ≤ C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)}`, `α₃ = 1 - 2γ - α₁`. -/
theorem termwise_irrelevant_pin_scaled (d N : ℕ) (A Λ Ksig α₁ γ C₀ KR : ℝ) (hA : 0 ≤ A)
    (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hα0 : 0 < α₁) (hα1 : α₁ < 1) (hC₀ : 0 < C₀) :
    ∃ CI : ℝ, 0 ≤ CI ∧ ∀ (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν r E₀ κ K₀ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : PremisesGeom T i₀ i₁ E₀ κ A K₀ Dom) (ψ : Site d → Spin N) (b : Spin N)
      (s σ ε K₂ : ℝ) (_ : DataHypAniso Dom ν σ ε K₂ ψ b) (X : Finset (Site d))
      (_ : X ∈ T.polys),
      0 < s → σ = C₀ * s → ε / r ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ) →
      0 < r → r ≤ 1 → 0 < ε → ε ≤ Λ * r → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 → 0 ≤ ν → ν ≤ σ ^ 2 →
      0 ≤ E₀ → K₂ ≤ Ksig * σ ^ (2 - α₁) * ε →
      (∃ (u : ℂ) (R : Matrix (Fin N) (Fin N) ℂ), Frame i₀ σ ε ψ u R ∧
        PinJetTerm T i₀ i₁ ν r E₀ κ A Λ ψ b σ ε R X) →
      ‖Itw T i₀ i₁ ν X ψ b‖ ≤
        CI * E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - α₁)) * Real.exp (-(κ - 1) * T.dist X) := by
  obtain ⟨C, hC0, hC⟩ := termwise_irrelevant_pin d N A Λ Ksig α₁ hA hΛ hKsig hα0 hα1
  refine ⟨C * (C₀ ^ (3 - α₁) * KR ^ 2), by positivity, ?_⟩
  intro T i₀ i₁ ν r E₀ κ K₀ Dom hP ψ b s σ ε K₂ dat X hX hs hσs hR hr hr1 hε hεΛ hσ1 hτ hν hνσ
    hE0 hK jet
  have hσ : 0 < σ := by rw [hσs]; positivity
  have h := hC T i₀ i₁ ν r E₀ κ K₀ Dom hP ψ b σ ε K₂ dat X hX hr hr1 hε hεΛ hσ hσ1 hτ hν hνσ
    hE0 hK jet
  refine h.trans ?_
  have hr0 : 0 ≤ ε / r := by positivity
  have h1 : (ε / r) ^ 2 ≤ KR ^ 2 * s ^ (2 * (((d : ℝ) - 2) / 2 - γ)) := by
    have := pow_le_pow_left₀ hr0 hR 2
    refine this.trans (le_of_eq ?_)
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num
    ring_nf
  have h2 : σ ^ (3 - α₁) = C₀ ^ (3 - α₁) * s ^ (3 - α₁) := by
    rw [hσs, Real.mul_rpow hC₀.le hs.le]
  have h3 : s ^ (3 - α₁) * s ^ (2 * (((d : ℝ) - 2) / 2 - γ)) =
      s ^ ((d : ℝ) + (1 - 2 * γ - α₁)) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  have hs0 : 0 ≤ s ^ (3 - α₁) := (Real.rpow_pos_of_pos hs _).le
  calc C * E₀ * Real.exp (-(κ - 1) * T.dist X) * (σ ^ (3 - α₁) * (ε / r) ^ 2)
      ≤ C * E₀ * Real.exp (-(κ - 1) * T.dist X) *
        (C₀ ^ (3 - α₁) * s ^ (3 - α₁) * (KR ^ 2 * s ^ (2 * (((d : ℝ) - 2) / 2 - γ)))) := by
        rw [h2]
        have : 0 ≤ C * E₀ * Real.exp (-(κ - 1) * T.dist X) := by positivity
        gcongr
    _ = C * (C₀ ^ (3 - α₁) * KR ^ 2) * E₀ *
        (s ^ (3 - α₁) * s ^ (2 * (((d : ℝ) - 2) / 2 - γ))) *
        Real.exp (-(κ - 1) * T.dist X) := by ring
    _ = _ := by rw [h3]

end Balaban.SmallField
