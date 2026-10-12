/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormAnisoLocal
public import Balaban.SmallField.RenormTermwiseBound

/-!
# Lemma 3.2 on the anisotropic domain: premises, data and the per-term estimates

* `PremisesTermAniso`: (H.2)–(H.4) and the geometric facts on the polymers, with the analyticity
  domain `TubeAniso i₀ ν r X` (spin radius `r`, longitudinal field radius `r²`, transverse field
  radius `r`) in place of the isotropic `Tube i₀ ν ρ X` of `PremisesTerm`.  The Euclid symmetry
  fields of `PremisesTerm` are not used by the termwise estimate and are not part of it; they
  enter only at the level of the sum over polymers.
* `DataHypAniso`: the properties (Σ1), (Σ2) of `DataHyp` together with the longitudinal bound of
  P1 (3.13)–(3.14), p. 123: `ν_j |1 - ψ̂·h| < σ² ε²`, in the variables `b = ν h`:
  `‖vInv ψ b - ν‖ ≤ σ² ε²`.
* `CtxAniso`: the context of the local analysis (premises, data, a frame, numerical conditions,
  and the scale comparison `ε ≤ Λ r`).

The per-term estimates of `CtxTw` are re-proved: the rotated constant displacement `zcfg` has
gauge `≤ (C₁ + Λ) σ² ε / r` (`CtxAniso.zc_gauge_le`; its longitudinal field component is
`vInv ψ b - ν`, of size `σ² ε²`, measured against `r²`), which gives

* `CtxAniso.small_case`: the local estimate for polymers with `(C₁ + Λ + κ₁)(1 + d_j(X)) σ ε ≤ r/2`;
* `CtxAniso.tail_case`: the crude bound for the other polymers;
* `CtxAniso.constant_potential_aniso`: `‖𝓔(y, X; ψ(y), b) - T_X‖ ≤ 12 |X| M (C₁ + Λ)² σ⁴ (ε/r)²`.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

/-- **Premises of Lemma 3.2 on the anisotropic domain**: (H.2)–(H.4) with constants `E₀, κ` and
the cited geometric facts on the polymers, the analyticity domain being `TubeAniso i₀ ν r X`.
These are the fields of `PremisesTerm` with `Tube i₀ ν ρ X` replaced by `TubeAniso i₀ ν r X`,
without the Euclid symmetry fields (which only the sum over polymers uses). -/
structure PremisesTermAniso (T : TermFamily d N) (i₀ i₁ : Fin N) (ν r E₀ κ A K₀ : ℝ)
    (Dom : Set ((Site d → Spin N) × Spin N)) : Prop where
  ne : i₀ ≠ i₁
  /-- geometry: polymers contain their centre, `d_j ≥ 0` -/
  zero_mem : ∀ X ∈ T.polys, (0 : Site d) ∈ X
  dist_nonneg : ∀ X ∈ T.polys, 0 ≤ T.dist X
  /-- geometry: path bound (P1 (3.54)) -/
  diam : ∀ X ∈ T.polys, ∀ x ∈ X, ((∑ μ, |x μ| : ℤ) : ℝ) ≤ A * (1 + T.dist X)
  /-- geometry: counting (P6 (4.11)) -/
  count_summable : Summable fun X : T.polys => wt κ X.1 (T.dist X.1)
  count_le : ∑' X : T.polys, wt κ X.1 (T.dist X.1) ≤ K₀
  /-- (H.2), (H.4): analyticity on the anisotropic analyticity domain -/
  analytic : ∀ X ∈ T.polys, AnalyticOnNhd ℂ (T.term X) (TubeAniso i₀ ν r X)
  /-- (H.4): the bound on the anisotropic analyticity domain -/
  bdd_tube : ∀ X ∈ T.polys, ∀ c ∈ TubeAniso i₀ ν r X,
    ‖T.term X c‖ ≤ E₀ * Real.exp (-κ * T.dist X)
  /-- (H.4): the same bound on the data domain `Dom` -/
  bdd_dom : ∀ X ∈ T.polys, ∀ p ∈ Dom,
    ‖T.term X (pack X p.1 p.2)‖ ≤ E₀ * Real.exp (-κ * T.dist X)
  /-- (H.3): rotation invariance -/
  rot_inv : ∀ X ∈ T.polys, ∀ c ∈ TubeAniso i₀ ν r X, ∀ R : Matrix (Fin N) (Fin N) ℂ,
    IsOrth R → EntryBd N R → rotCfgL R X c ∈ TubeAniso i₀ ν r X →
      T.term X (rotCfgL R X c) = T.term X c

/-- **The properties of the configuration on the anisotropic domain**: the properties (Σ1), (Σ2)
of `DataHyp`, and the longitudinal bound of P1 (3.13)–(3.14), p. 123:
`ν_j |1 - ψ̂(y)·h| < σ² ε²` with `ψ̂ = ψ(y)/√(ψ(y)·ψ(y))` and `h = b/ν`, i.e.
`‖(ψ(y)·b)/√(ψ(y)·ψ(y)) - ν‖ ≤ σ² ε²`.  (P1 states it for the real background in (3.13) and for
the complex perturbation `ν (ψ₀)₀·h'` in (3.14); as for the other fields of `DataHyp`, the
numerical constant of their combination is absorbed into `σ = C₀ s`.) -/
structure DataHypAniso (Dom : Set ((Site d → Spin N) × Spin N)) (ν σ ε K₂ : ℝ)
    (ψ : Site d → Spin N) (b : Spin N) : Prop extends DataHyp Dom ν σ ε K₂ ψ b where
  /-- P1 (3.13)–(3.14): the component of `b` along `ψ̂(y)` is `ν` up to `σ² ε²` -/
  b_long : ‖vInv ψ b - ν‖ ≤ σ ^ 2 * ε ^ 2

/-- The isotropic premises at radius `r ≤ 1` give the anisotropic ones at the same `r`. -/
theorem PremisesTerm.toAniso {T : TermFamily d N} {i₀ i₁ : Fin N} {ν r E₀ κ A K₀ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} (h : PremisesTerm T i₀ i₁ ν r E₀ κ A K₀ Dom)
    (hr : 0 < r) (hr1 : r ≤ 1) : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom := by
  have hsub : ∀ X : Finset (Site d), TubeAniso i₀ ν r X ⊆ Tube i₀ ν r X := by
    rintro X c ⟨R, hR, hb, hc⟩
    refine ⟨R, hR, hb, ?_⟩
    rw [mem_ball, dist_eq_norm]
    rw [(mem_polyAniso_iff hr _)] at hc
    have hg : ∀ p, ‖(rotCfgL R X c - refPt i₀ ν X) p‖ < r := by
      intro p
      have h1 := norm_apply_le_anisoWt_mul (i₀ := i₀) hr (rotCfgL R X c - refPt i₀ ν X) p
      have h2 : anisoWt i₀ r X p ≤ r := by
        rcases p with p | i
        · exact le_rfl
        · simp only [anisoWt, Sum.elim_inr]
          split_ifs
          · nlinarith
          · exact le_rfl
      have h3 := anisoWt_pos (i₀ := i₀) (X := X) hr p
      calc ‖(rotCfgL R X c - refPt i₀ ν X) p‖
          ≤ anisoWt i₀ r X p * anisoGauge i₀ r X (rotCfgL R X c - refPt i₀ ν X) := h1
        _ < anisoWt i₀ r X p * 1 := mul_lt_mul_of_pos_left hc h3
        _ ≤ r := by linarith
    exact (pi_norm_lt_iff hr).mpr hg
  exact ⟨h.ne, h.zero_mem, h.dist_nonneg, h.diam, h.count_summable, h.count_le,
    fun X hX => (h.analytic X hX).mono (hsub X), fun X hX c hc => h.bdd_tube X hX c (hsub X hc),
    h.bdd_dom, fun X hX c hc R hR hb hm => h.rot_inv X hX c (hsub X hc) R hR hb (hsub X hm)⟩

/-- The premises with the analyticity domain of the class given as an arbitrary family of sets
`Ω X ⊇ TubeAniso`: analyticity, the bound and rotation invariance on `Ω` restrict to
`TubeAniso` (the analogue of `PremisesTerm.ofDomain`). -/
theorem PremisesTermAniso.ofDomain {T : TermFamily d N} {i₀ i₁ : Fin N} {ν r E₀ κ A K₀ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} (Ω : (X : Finset (Site d)) → Set (Cfg d N X))
    (hΩ : ∀ X ∈ T.polys, TubeAniso i₀ ν r X ⊆ Ω X)
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
      IsOrth R → EntryBd N R → rotCfgL R X c ∈ Ω X → T.term X (rotCfgL R X c) = T.term X c) :
    PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom :=
  ⟨ne, zero_mem, dist_nonneg, diam, count_summable, count_le,
    fun X hX => (analytic X hX).mono (hΩ X hX), fun X hX c hc => bdd X hX c (hΩ X hX hc),
    bdd_dom, fun X hX c hc R hR hb hm => rot_inv X hX c (hΩ X hX hc) R hR hb (hΩ X hX hm)⟩

/-! ### Constants -/

/-- The constant `C₁ + Λ` bounding the gauge of the constant part of the displacement. -/
def cZA (N : ℕ) (Λ : ℝ) : ℝ := cC1 N + Λ

/-- The size `(C₁ + Λ) σ² ε` of the constant part, measured in the gauge times `r`. -/
def sZ0A (N : ℕ) (Λ σ ε : ℝ) : ℝ := cZA N Λ * (σ ^ 2 * ε)

/-- The explicit bound of the anisotropic local estimate (`smallBnd` with `C₁` replaced by
`C₁ + Λ` and `ρ` by `r`). -/
noncomputable def smallBndA (N : ℕ) (A Λ M r ν σ ε K₂ t P : ℝ) : ℝ :=
  2 * M * ((sZ0A N Λ σ ε + sD N A σ ε t) / r) ^ 3 + 2 * M * (sZ0A N Λ σ ε / r) ^ 3 +
    4 * M * (sZ0A N Λ σ ε / r) * (sD N A σ ε t / r) + P * (M / r) * sEe N A σ ε t +
    2 * P ^ 2 * M * sF N A σ ε t ^ 2 / r ^ 2 +
    ν / 2 * P * (4 * M / r ^ 2) * (N * sD N A σ ε t ^ 2) +
    P ^ 2 * (M / r ^ 2) * sEb N A σ ε K₂ t

theorem cZA_nonneg (N : ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ) : 0 ≤ cZA N Λ := by
  unfold cZA cC1; positivity

theorem one_le_cZA (N : ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ) : 1 ≤ cZA N Λ := by
  unfold cZA cC1
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

/-! ### The rotated field -/

section Frame

variable {i₀ : Fin N} {σ ε : ℝ} {ψ : Site d → Spin N} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}

theorem Frame.norm_u_ge (fr : Frame i₀ σ ε ψ u R) (hτ : σ ^ 2 * ε ≤ 1 / 4) : 3 / 4 ≤ ‖u‖ := by
  have h := fr.u_close
  have := norm_sub_norm_le (1 : ℂ) u
  rw [norm_sub_rev] at this
  simp at this
  linarith

/-- The rotated field differs from `ν e_{i₀}` by `O(σ² ε)` (the field part of `Ctx.zc_le`). -/
theorem Frame.norm_mulVec_b_sub_le (fr : Frame i₀ σ ε ψ u R)
    {Dom : Set ((Site d → Spin N) × Spin N)} {ν K₂ : ℝ} {b : Spin N}
    (dat : DataHyp Dom ν σ ε K₂ ψ b) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) (hν : 0 ≤ ν)
    (hνσ : ν ≤ σ ^ 2) (hτ : σ ^ 2 * ε ≤ 1 / 4) :
    ‖R.mulVec b - (ν : ℂ) • Pi.single i₀ 1‖ ≤ (160 * N + 1) * (σ ^ 2 * ε) := by
  have hτ0 : 0 ≤ σ ^ 2 * ε := by positivity
  have hu := fr.norm_u_ge hτ
  have hu0 : u ≠ 0 := by intro h; rw [h] at hu; simp at hu; linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hw : R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 =
      R.mulVec (b - ((ν : ℂ) / u) • ψ 0) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, fr.rot0, smul_smul]
    congr 1
    rw [div_mul_cancel₀ _ hu0]
  rw [hw]
  have hb := norm_mulVec_le (R := R) (B := 40) (by norm_num) (fun i k => by
    have := fr.bd i k; simpa [rotBound] using this) (b - ((ν : ℂ) / u) • ψ 0)
  have h1 : ‖b - ((ν : ℂ) / u) • ψ 0‖ ≤ 4 * (σ ^ 2 * ε) := by
    have e : b - ((ν : ℂ) / u) • ψ 0 =
        (b - (ν : ℂ) • ψ 0) + ((ν : ℂ) • ψ 0 - ((ν : ℂ) / u) • ψ 0) := by
      abel
    rw [e]
    have t1 := dat.b_close
    have t2 : ‖(ν : ℂ) • ψ 0 - ((ν : ℂ) / u) • ψ 0‖ ≤ 3 * (σ ^ 2 * ε) := by
      have : (ν : ℂ) • ψ 0 - ((ν : ℂ) / u) • ψ 0 = ((ν : ℂ) * (1 - 1 / u)) • ψ 0 := by
        rw [mul_sub, sub_smul, mul_one, mul_one_div]
      rw [this, norm_smul, norm_mul]
      have h3 : ‖(ν : ℂ)‖ = ν := by simp [abs_of_nonneg hν]
      have h4 : ‖(1 : ℂ) - 1 / u‖ ≤ 4 / 3 * (σ ^ 2 * ε) := by
        have : (1 : ℂ) - 1 / u = (u - 1) / u := by field_simp
        rw [this, norm_div, div_le_iff₀ (by linarith)]
        have := fr.u_close
        nlinarith [norm_nonneg (u - 1)]
      have h5 : ν ≤ 1 := hνσ.trans (by nlinarith)
      rw [h3]
      calc ν * ‖(1 : ℂ) - 1 / u‖ * ‖ψ 0‖ ≤ 1 * (4 / 3 * (σ ^ 2 * ε)) * 2 := by
            refine mul_le_mul (mul_le_mul h5 h4 (norm_nonneg _) zero_le_one) dat.bdd0
              (norm_nonneg _) (by positivity)
        _ ≤ 3 * (σ ^ 2 * ε) := by nlinarith
    linarith [(norm_add_le _ _).trans (add_le_add t1 t2)]
  calc ‖R.mulVec (b - ((ν : ℂ) / u) • ψ 0)‖ ≤ N * 40 * ‖b - ((ν : ℂ) / u) • ψ 0‖ := hb
    _ ≤ N * 40 * (4 * (σ ^ 2 * ε)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (160 * N + 1) * (σ ^ 2 * ε) := by nlinarith

end Frame

/-! ### The context -/

/-- The context of the anisotropic local analysis: the premises, the data, a frame, the numerical
conditions, and the comparison `ε ≤ Λ r` of the field size with the analyticity radius. -/
structure CtxAniso (T : TermFamily d N) (i₀ i₁ : Fin N) (ν r E₀ κ A K₀ Λ : ℝ)
    (Dom : Set ((Site d → Spin N) × Spin N)) (ψ : Site d → Spin N) (b : Spin N)
    (σ ε K₂ : ℝ) (u : ℂ) (R : Matrix (Fin N) (Fin N) ℂ) : Prop where
  hyp : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom
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

section CtxAniso

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν r E₀ κ A K₀ Λ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)} {ψ : Site d → Spin N} {b : Spin N}
  {σ ε K₂ : ℝ} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}

theorem CtxAniso.Λnn (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R) : 0 ≤ Λ := by
  have h1 := c.εle
  have h2 := c.εpos
  have h3 := c.rpos
  by_contra h
  push Not at h
  nlinarith

theorem CtxAniso.l1_le (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) {x : Site d} (hx : x ∈ X) :
    (l1 x : ℝ) ≤ A * (1 + T.dist X) := by
  rw [l1_cast]; exact c.hyp.diam X hX x hx

theorem CtxAniso.rotDiff_le (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    (x : Site d) : ‖rotDiff R ψ x‖ ≤ N * 40 * ((l1 x : ℝ) * (σ * ε)) := by
  have h := norm_mulVec_le (R := R) (B := 40) (by norm_num) (fun i k => by
    have := c.frame.bd i k; simpa [rotBound] using this) (ψ x - ψ 0)
  have h2 := norm_sub_le_l1 (ψ := ψ) (δ := σ * ε) c.dat.adj 0 x
  simp only [zero_add] at h2
  unfold rotDiff
  calc ‖R.mulVec (ψ x - ψ 0)‖ ≤ N * 40 * ‖ψ x - ψ 0‖ := h
    _ ≤ N * 40 * ((l1 x : ℝ) * (σ * ε)) := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem CtxAniso.ga_le (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R) (x : Site d) :
    ‖dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)‖ ≤ 2 * (σ ^ 2 * ε) := by
  have h1 := c.dat.sq x
  have h2 := c.dat.sq 0
  calc ‖dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)‖
      = ‖(dot (ψ x) (ψ x) - 1) - (dot (ψ 0) (ψ 0) - 1)‖ := by ring_nf
    _ ≤ ‖dot (ψ x) (ψ x) - 1‖ + ‖dot (ψ 0) (ψ 0) - 1‖ := norm_sub_le _ _
    _ ≤ 2 * (σ ^ 2 * ε) := by linarith

theorem CtxAniso.uInv_eq (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R) :
    uInv ψ = u :=
  c.frame.uInv_eq c.τle

theorem CtxAniso.alpha_eq (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R) :
    ((R.mulVec (ψ 0) - Pi.single i₀ 1 : Spin N) i₀) = uInv ψ - 1 := by
  rw [c.uInv_eq, c.frame.rot0]
  simp

/-- The longitudinal component of the rotated field is `vInv ψ b`. -/
theorem CtxAniso.beta_eq (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R) :
    ((R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) i₀) = vInv ψ b - ν := by
  have hu := c.frame.u_ne c.τle
  unfold vInv
  rw [c.uInv_eq, Pi.sub_apply, c.frame.mulVec_apply hu]
  simp

/-- **The gauge of the constant displacement**: `g(z_c) ≤ (C₁ + Λ) σ² ε / r`.  Its spin and
transverse field components are `O(σ² ε)` against the radius `r`; its longitudinal field
component `vInv ψ b - ν` is `O(σ² ε²)` against the radius `r²`. -/
theorem CtxAniso.zc_gauge_le (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    (X : Finset (Site d)) : anisoGauge i₀ r X (zcfg X i₀ ν ψ b R) ≤ sZ0A N Λ σ ε / r := by
  have hr := c.rpos
  have hσ := c.σpos
  have hε := c.εpos
  have hΛ := c.Λnn
  have hτ0 : 0 ≤ σ ^ 2 * ε := by positivity
  have hZ : 1 ≤ cZA N Λ := one_le_cZA N hΛ
  have hC1 : cC1 N ≤ cZA N Λ := by unfold cZA; linarith
  refine anisoGauge_le_of hr (by unfold sZ0A; have := cZA_nonneg N hΛ; positivity) fun p => ?_
  rcases p with ⟨x, j⟩ | j
  · -- the spin part: `(u - 1) e_{i₀}`
    have key : R.mulVec (ψ 0) - (Pi.single i₀ 1 : Spin N) =
        (u - 1) • (Pi.single i₀ 1 : Spin N) := by
      rw [c.frame.rot0, sub_smul, one_smul]
    simp only [zcfg, pack, Sum.elim_inl, key, Pi.smul_apply, smul_eq_mul]
    have h1 : ‖(u - 1) * (Pi.single i₀ 1 : Spin N) j‖ ≤ ‖u - 1‖ := by
      rw [norm_mul]
      have : ‖(Pi.single i₀ 1 : Spin N) j‖ ≤ 1 := by
        by_cases h : j = i₀ <;> simp [h]
      nlinarith [norm_nonneg (u - 1), norm_nonneg ((Pi.single i₀ 1 : Spin N) j)]
    rw [anisoWt_inl, mul_div_cancel₀ _ hr.ne']
    unfold sZ0A
    have := c.frame.u_close
    nlinarith
  · simp only [zcfg, pack, Sum.elim_inr]
    by_cases hj : j = i₀
    · -- the longitudinal field part: `vInv ψ b - ν`, against `r²`
      subst hj
      rw [c.beta_eq, anisoWt_inr_self]
      have h1 := c.dat.b_long
      have h2 : ε ≤ cZA N Λ * r := by
        have := c.εle
        have : Λ ≤ cZA N Λ := by unfold cZA cC1; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
        nlinarith
      have e : r ^ 2 * (sZ0A N Λ σ ε / r) = r * (cZA N Λ * (σ ^ 2 * ε)) := by
        unfold sZ0A; field_simp
      rw [e]
      calc ‖vInv ψ b - ν‖ ≤ σ ^ 2 * ε ^ 2 := h1
        _ = (σ ^ 2 * ε) * ε := by ring
        _ ≤ (σ ^ 2 * ε) * (cZA N Λ * r) := mul_le_mul_of_nonneg_left h2 hτ0
        _ = r * (cZA N Λ * (σ ^ 2 * ε)) := by ring
    · -- the transverse field part, against `r`
      rw [anisoWt_inr_ne hj, mul_div_cancel₀ _ hr.ne']
      have h1 := c.frame.norm_mulVec_b_sub_le c.dat.toDataHyp hσ c.σle hε c.ν0 c.νσ c.τle
      have h2 := norm_le_pi_norm (R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) j
      unfold sZ0A
      calc ‖(R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) j‖
          ≤ (160 * N + 1) * (σ ^ 2 * ε) := h2.trans h1
        _ = cC1 N * (σ ^ 2 * ε) := by unfold cC1; ring
        _ ≤ cZA N Λ * (σ ^ 2 * ε) := mul_le_mul_of_nonneg_right hC1 hτ0

theorem CtxAniso.termOK (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) : TermOK i₀ ν (r ^ 2) X (T.term X) :=
  termOK_of_tubeAniso c.rpos c.rle (c.hyp.analytic X hX) (c.hyp.rot_inv X hX)

theorem CtxAniso.analytic_poly (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) :
    AnalyticOnNhd ℂ (T.term X) (polyAniso i₀ ν r X) :=
  (c.hyp.analytic X hX).mono polyAniso_subset_tubeAniso

theorem CtxAniso.hM (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) :
    ∀ y ∈ polyAniso i₀ ν r X, ‖T.term X y‖ ≤ E₀ * Real.exp (-κ * T.dist X) :=
  fun y hy => c.hyp.bdd_tube X hX y (polyAniso_subset_tubeAniso hy)

/-- Rotation invariance for the configuration of a polymer. -/
theorem CtxAniso.term_rot (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) {ψ' : Site d → Spin N} {b' : Spin N}
    (hpoly : rotCfgL R X (pack X ψ' b') ∈ polyAniso i₀ ν r X) :
    T.term X (pack X ψ' b') = T.term X (rotCfgL R X (pack X ψ' b')) := by
  have hmem : pack X ψ' b' ∈ TubeAniso i₀ ν r X := ⟨R, c.frame.orth, c.frame.bd, hpoly⟩
  exact (c.hyp.rot_inv X hX _ hmem R c.frame.orth c.frame.bd
    (polyAniso_subset_tubeAniso hpoly)).symm

theorem CtxAniso.card_pos (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) : 1 ≤ X.card :=
  Finset.card_pos.mpr ⟨0, c.hyp.zero_mem X hX⟩

/-- **The local estimate** for a polymer with `(C₁ + Λ + κ₁)(1 + d_j(X)) σ ε ≤ r/2`. -/
theorem CtxAniso.small_case (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys)
    (hs : (cZA N Λ + cK1 N A) * (1 + T.dist X) * σ * ε ≤ r / 2) :
    ‖T.term X (pack X ψ b) - T.term X (pack X (fun _ => ψ 0) b)
        - (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x *
            (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))
        + (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
            wquad (gradTensor i₀ R ψ) x.1 x'.1‖ ≤
      smallBndA N A Λ (E₀ * Real.exp (-κ * T.dist X)) r ν σ ε K₂ (1 + T.dist X) X.card := by
  have hok := c.termOK hX
  have han := c.analytic_poly hX
  have hM := c.hM hX
  have hne : i₁ ≠ i₀ := c.hyp.ne.symm
  have hd0 : 0 ≤ T.dist X := c.hyp.dist_nonneg X hX
  set t : ℝ := 1 + T.dist X with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hσ := c.σpos
  have hε := c.εpos
  have hr := c.rpos
  have hΛ := c.Λnn
  have hK1 : 0 ≤ cK1 N A := by unfold cK1; have := c.Ann; positivity
  have hCZ : 0 ≤ cZA N Λ := cZA_nonneg N hΛ
  have hτ0 : 0 ≤ σ ^ 2 * ε := by positivity
  have hD0 : 0 ≤ sD N A σ ε t := by unfold sD; positivity
  have hZ0n : 0 ≤ sZ0A N Λ σ ε := by unfold sZ0A; positivity
  have hDφ : ∀ x ∈ X, ‖rotDiff R ψ x‖ ≤ sD N A σ ε t := by
    intro x hx
    refine (c.rotDiff_le x).trans ?_
    unfold sD cK1
    have := c.l1_le hX hx
    have h2 : 0 ≤ σ * ε := by positivity
    calc (N : ℝ) * 40 * ((l1 x : ℝ) * (σ * ε)) ≤ N * 40 * (A * t * (σ * ε)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ h2) (by positivity)
          simpa [ht] using this
      _ = _ := by ring
  have hpk : anisoGauge i₀ r X (pack X (rotDiff R ψ) 0) ≤ sD N A σ ε t / r :=
    anisoGauge_pack_zero_le hr _ hD0 hDφ
  have hzc : anisoGauge i₀ r X (zcfg X i₀ ν ψ b R) ≤ sZ0A N Λ σ ε / r := c.zc_gauge_le X
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
  have hZ : (sZ0A N Λ σ ε + sD N A σ ε t) / r ≤ 1 / 2 := by
    rw [div_le_iff₀ hr]; linarith
  have hZ0 : sZ0A N Λ σ ε / r ≤ 1 / 2 := by
    rw [div_le_iff₀ hr]; linarith
  -- the rotated configurations lie in the polydisc
  have hpoly1 : rotCfgL R X (pack X ψ b) ∈ polyAniso i₀ ν r X := by
    rw [rotCfgL_pack, pack_rot_eq, refPt_add_mem_polyAniso_iff hr]
    linarith
  have hpoly2 : rotCfgL R X (pack X (fun _ => ψ 0) b) ∈ polyAniso i₀ ν r X := by
    rw [rotCfgL_pack, pack_const_rot_eq, refPt_add_mem_polyAniso_iff hr]
    linarith
  rw [c.term_rot hX hpoly1, c.term_rot hX hpoly2, rotCfgL_pack, rotCfgL_pack, pack_rot_eq,
    pack_const_rot_eq]
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
      (g := dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)) c.frame.u_close c.τle (c.ga_le x) hθ hφ
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
  have key := hok.local_bound_aniso hne hr han hM c.ν0 (rotDiff R ψ)
    (fun y => dot (ψ y) (ψ y) - dot (ψ 0) (ψ 0)) (gradTensor i₀ R ψ) (zcfg X i₀ ν ψ b R)
    (Z := (sZ0A N Λ σ ε + sD N A σ ε t) / r) (Z0 := sZ0A N Λ σ ε / r) (D := sD N A σ ε t)
    (F := sF N A σ ε t) (Ee := sEe N A σ ε t) (Eb := sEb N A σ ε K₂ t) hD0
    (by unfold sF; positivity) hz hZ hzc hZ0 hDφ (fun x hx => (hlong x hx).1)
    (fun x hx => (hlong x hx).2) hEb
  exact key

/-- Bound for the first-order term `A_X`. -/
theorem CtxAniso.A_le (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) :
    ‖(1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x *
      (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))‖ ≤
      X.card * (E₀ * Real.exp (-κ * T.dist X) / r * (σ ^ 2 * ε)) := by
  have han := c.analytic_poly hX
  have hM := c.hM hX
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
    exact mul_le_mul (aniso_norm_tensA_le hr han hM x) (c.ga_le x.1) (norm_nonneg _) hcr
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h2, hcard] at *
  calc 1 / 2 * ‖∑ x : ↥X, tensA i₀ ν X (T.term X) x * (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))‖
      ≤ 1 / 2 * ((X.card : ℝ) * (M / r * (2 * (σ ^ 2 * ε)))) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = _ := by ring

/-- Bound for the quadratic term `L_X`. -/
theorem CtxAniso.Lq_le (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) :
    ‖(1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
      wquad (gradTensor i₀ R ψ) x.1 x'.1‖ ≤
      (X.card : ℝ) ^ 2 * (E₀ * Real.exp (-κ * T.dist X) / r ^ 2) *
        ((2 * (A * (1 + T.dist X))) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2)) := by
  have han := c.analytic_poly hX
  have hM := c.hM hX
  have hd0 : 0 ≤ T.dist X := c.hyp.dist_nonneg X hX
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
      have := c.rotDiff_le (eU ν')
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
    refine mul_le_mul (aniso_norm_D2_basis_le hr han hM (anisoWt_inl _) (anisoWt_inl _)) ?_
      (norm_nonneg _) (by positivity)
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

/-- The crude bound for the polymers with large `d_j(X)`. -/
theorem CtxAniso.tail_case (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) :
    ‖T.term X (pack X ψ b) - T.term X (pack X (fun _ => ψ 0) b)
        - (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x *
            (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))
        + (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
            wquad (gradTensor i₀ R ψ) x.1 x'.1‖ ≤
      tailBnd N A (E₀ * Real.exp (-κ * T.dist X)) r σ ε (1 + T.dist X) X.card := by
  set t : ℝ := 1 + T.dist X with ht
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hr := c.rpos
  have a1 : ‖T.term X (pack X ψ b)‖ ≤ M := c.hyp.bdd_dom X hX (ψ, b) c.dat.mem
  have a2 : ‖T.term X (pack X (fun _ => ψ 0) b)‖ ≤ M :=
    c.hyp.bdd_dom X hX ((fun _ => ψ 0), b) c.dat.mem_const
  have a3 := c.A_le hX
  have a4 := c.Lq_le hX
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

/-- The expansion of the term at the constant configuration around the reference point:
first-order Taylor in the gauge. -/
theorem CtxAniso.potential_term (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) (hZ0 : sZ0A N Λ σ ε / r ≤ 1 / 2) :
    ‖T.term X (pack X (fun _ => ψ 0) b) - T.term X (refPt i₀ ν X) -
        ((∑ x : ↥X, tensA i₀ ν X (T.term X) x) * ((R.mulVec (ψ 0) - Pi.single i₀ 1 : Spin N) i₀) +
          ((R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) i₀) *
            fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1))‖ ≤
      2 * (E₀ * Real.exp (-κ * T.dist X)) * (sZ0A N Λ σ ε / r) ^ 2 := by
  have hok := c.termOK hX
  have han := c.analytic_poly hX
  have hM := c.hM hX
  have hr := c.rpos
  have hzc := c.zc_gauge_le X
  have hpoly : rotCfgL R X (pack X (fun _ => ψ 0) b) ∈ polyAniso i₀ ν r X := by
    rw [rotCfgL_pack, pack_const_rot_eq, refPt_add_mem_polyAniso_iff hr]
    linarith
  rw [c.term_rot hX hpoly, rotCfgL_pack, pack_const_rot_eq]
  have h := aniso_taylor_first hr han hM (z := zcfg X i₀ ν ψ b R) (hzc.trans hZ0)
  have hlin : fderiv ℂ (T.term X) (refPt i₀ ν X) (zcfg X i₀ ν ψ b R) =
      (∑ x : ↥X, tensA i₀ ν X (T.term X) x) * ((R.mulVec (ψ 0) - Pi.single i₀ 1 : Spin N) i₀) +
        ((R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) i₀) *
          fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1) := by
    unfold zcfg
    rw [hok.lin_pack_b, Finset.sum_mul]
  rw [hlin] at h
  refine h.trans ?_
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X) := by have := c.E0nn; positivity
  have : anisoGauge i₀ r X (zcfg X i₀ ν ψ b R) ^ 2 ≤ (sZ0A N Λ σ ε / r) ^ 2 :=
    pow_le_pow_left₀ (anisoGauge_nonneg _) hzc 2
  nlinarith

theorem CtxAniso.ttw_eq (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    (X : Finset (Site d)) :
    Ttw T i₀ ν X ψ b = T.term X (refPt i₀ ν X) +
      ((∑ x : ↥X, tensA i₀ ν X (T.term X) x) * ((R.mulVec (ψ 0) - Pi.single i₀ 1 : Spin N) i₀) +
        ((R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) i₀) *
          fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1)) := by
  rw [c.alpha_eq, c.beta_eq]
  unfold Ttw
  ring

theorem CtxAniso.itw_eq (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    (X : Finset (Site d)) :
    Itw T i₀ i₁ ν X ψ b = Dlt T i₀ i₁ ν R ψ b X +
      (T.term X (pack X (fun _ => ψ 0) b) - Ttw T i₀ ν X ψ b) := by
  unfold Itw
  rw [c.frame.phitw_eq c.τle, Dlt_eq]
  ring

/-- **The constant-field potential of a single term**: the first-order invariant Taylor
polynomial `T_X` approximates `𝓔(y, X; ψ(y), b)` to `12 |X| M (C₁ + Λ)² σ⁴ (ε/r)²`. -/
theorem CtxAniso.constant_potential_aniso
    (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) :
    ‖T.term X (pack X (fun _ => ψ 0) b) - Ttw T i₀ ν X ψ b‖ ≤
      12 * (X.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X)) * cZA N Λ ^ 2 *
        (σ ^ 4 * (ε / r) ^ 2) := by
  have hr := c.rpos
  have han := c.analytic_poly hX
  have hM := c.hM hX
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by have := c.E0nn; positivity
  have hcard : (1 : ℝ) ≤ X.card := by exact_mod_cast c.card_pos hX
  have hΛ := c.Λnn
  have hsq : (sZ0A N Λ σ ε / r) ^ 2 = cZA N Λ ^ 2 * (σ ^ 4 * (ε / r) ^ 2) := by
    unfold sZ0A; field_simp
  suffices hq : ‖T.term X (pack X (fun _ => ψ 0) b) - Ttw T i₀ ν X ψ b‖ ≤
      12 * (X.card : ℝ) * M * (sZ0A N Λ σ ε / r) ^ 2 by
    rw [hsq] at hq; linarith
  have hz0 : 0 ≤ sZ0A N Λ σ ε := by
    have := c.εpos; have := c.σpos; have := cZA_nonneg N hΛ; unfold sZ0A; positivity
  by_cases hZ0 : sZ0A N Λ σ ε / r ≤ 1 / 2
  · have h := c.potential_term hX hZ0
    rw [c.ttw_eq]
    have e : T.term X (pack X (fun _ => ψ 0) b) - (T.term X (refPt i₀ ν X) +
        ((∑ x : ↥X, tensA i₀ ν X (T.term X) x) * ((R.mulVec (ψ 0) - Pi.single i₀ 1 : Spin N) i₀) +
          ((R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) i₀) *
            fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1))) =
        T.term X (pack X (fun _ => ψ 0) b) - T.term X (refPt i₀ ν X) -
        ((∑ x : ↥X, tensA i₀ ν X (T.term X) x) * ((R.mulVec (ψ 0) - Pi.single i₀ 1 : Spin N) i₀) +
          ((R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) i₀) *
            fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1)) := by ring
    rw [e]
    refine h.trans ?_
    have : 0 ≤ M * (sZ0A N Λ σ ε / r) ^ 2 := by positivity
    nlinarith
  · push Not at hZ0
    set q : ℝ := sZ0A N Λ σ ε / r with hqdef
    have hq0 : 0 ≤ q := by positivity
    -- the crude bound
    have hzc := c.zc_gauge_le X
    set α : ℂ := uInv ψ - 1 with hα
    set β : ℂ := vInv ψ b - ν with hβ
    have hαb : ‖α‖ ≤ r * q := by
      rw [hα, ← c.alpha_eq]
      have h2 : ‖((R.mulVec (ψ 0) - Pi.single i₀ 1 : Spin N) i₀)‖ ≤ σ ^ 2 * ε := by
        rw [c.frame.rot0]
        simpa using c.frame.u_close
      refine h2.trans ?_
      rw [hqdef, mul_div_cancel₀ _ hr.ne']
      unfold sZ0A
      have := one_le_cZA N hΛ
      have : 0 ≤ σ ^ 2 * ε := by have := c.εpos; positivity
      nlinarith
    have hβb : ‖β‖ ≤ r ^ 2 * q := by
      rw [hβ, ← c.beta_eq]
      have h1 := norm_apply_le_anisoWt_mul (i₀ := i₀) hr (zcfg X i₀ ν ψ b R) (Sum.inr i₀)
      rw [anisoWt_inr_self] at h1
      have h2 : zcfg X i₀ ν ψ b R (Sum.inr i₀) =
          ((R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) i₀) := by
        simp [zcfg, pack]
      rw [h2] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hzc (by positivity))
    have hg : ‖T.term X (pack X (fun _ => ψ 0) b)‖ ≤ M :=
      c.hyp.bdd_dom X hX ((fun _ => ψ 0), b) c.dat.mem_const
    have hv0 : ‖T.term X (refPt i₀ ν X)‖ ≤ M := hM _ (refPt_mem_polyAniso hr)
    have hs : ‖∑ x : ↥X, tensA i₀ ν X (T.term X) x‖ ≤ (X.card : ℝ) * (M / r) := by
      have := norm_sum_le_card _ fun x => aniso_norm_tensA_le hr han hM x
      rwa [Fintype.card_coe] at this
    have hd : ‖fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1)‖ ≤ M / r ^ 2 :=
      aniso_norm_fderiv_inr_self_le hr han hM
    have hT : ‖Ttw T i₀ ν X ψ b‖ ≤ M + (r * q) * ((X.card : ℝ) * (M / r)) +
        (r ^ 2 * q) * (M / r ^ 2) := by
      unfold Ttw
      calc _ ≤ ‖T.term X (refPt i₀ ν X)‖ + ‖α * ∑ x : ↥X, tensA i₀ ν X (T.term X) x‖ +
            ‖β * fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1)‖ :=
              (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ M + (r * q) * ((X.card : ℝ) * (M / r)) + (r ^ 2 * q) * (M / r ^ 2) := by
            rw [norm_mul, norm_mul]
            gcongr
    have hr' : ‖T.term X (pack X (fun _ => ψ 0) b) - Ttw T i₀ ν X ψ b‖ ≤
        M + (M + (r * q) * ((X.card : ℝ) * (M / r)) + (r ^ 2 * q) * (M / r ^ 2)) :=
      (norm_sub_le _ _).trans (add_le_add hg hT)
    refine hr'.trans ?_
    have e1 : (r * q) * ((X.card : ℝ) * (M / r)) = (X.card : ℝ) * M * q := by field_simp
    have e2 : (r ^ 2 * q) * (M / r ^ 2) = M * q := by field_simp
    rw [e1, e2]
    have hq1 : q ≤ 2 * q ^ 2 := by nlinarith
    have hq2 : 1 ≤ 4 * q ^ 2 := by nlinarith
    have hP0 : 0 ≤ (X.card : ℝ) := by linarith
    calc M + (M + (X.card : ℝ) * M * q + M * q)
        ≤ 4 * M * q ^ 2 + (4 * M * q ^ 2 + (X.card : ℝ) * M * (2 * q ^ 2) + M * (2 * q ^ 2)) := by
          gcongr <;> nlinarith [mul_nonneg hM0 hq0]
      _ ≤ 12 * (X.card : ℝ) * M * q ^ 2 := by nlinarith [mul_nonneg hM0 (sq_nonneg q)]

end CtxAniso

end Balaban.SmallField
