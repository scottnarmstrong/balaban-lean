/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.ImprovedBound
public import Balaban.SmallField.Def6BridgeLift
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemma 3.4: the layer at constant configurations, and the `b`-form at `λ = ∞`

OBSERVABLES.md §3.4 ("at `λ = ∞` the constant configuration `ψ_j(y)` lies on the sphere and the
dependence on `h` is through `b = ν_j h`") for the observable terms `M^{(j)}(x, X; ·)` of `IsObs`.

The constant configurations `(constFld v, constFld w)` with `v` within `ρ` of a coordinate vector
`e_{i₀}` and `w` constant lie in the analyticity domain `XiDom` of the class (landed
`xiDom_of_close`; radius `ρ ≍ ε_j²`, `LiftCtx`).  On them `M^{(j)}(x, X; ·)` is holomorphic and
bounded by `B = β^{-1/2+ρ₁} L^{-jρ₀} e^{-κ d_j(X)}`, so:

* `M_const_diff_le` (**Lipschitz bound in `(ψ, b)`**, the "Lipschitz bound in `b`" of §3.4): for two
  constant pairs `(v, w)`, `(v', w')` of the tube `|v - e| ≤ ρ/2`, `ν_bg L^{2j} |w - e| ≤ ρ/2`,
  `|M(v, w) - M(v', w')| ≤ 4B · max(|v - v'|, ν_bg L^{2j} |w - w'|) / ρ`, where `ν_bg = bgMass`
  (Cauchy estimate on the complex line through the two points).
* `M_const_indep_h_of_massFree` (**the `ν`-free regime, `β_k ν_k ≤ 1`**): the background mass is
  `0`, the domain places no condition on the constant field `h`, so `t ↦ M(v, w + t u)` is entire and
  bounded, hence constant (Liouville): **on constant configurations near `e_{i₀}` the term
  `M^{(j)}(x, X; ψ, h)` does not depend on `h`**.  This is the analogue for the layer of RGFREE-3
  Proposition 1 (for `ℰ`): the `b`-form at `λ = ∞` is trivial in the `ν`-free regime of the landed
  class, because of a degeneracy of the landed domain (no condition on `h` at zero background mass),
  and not because the physical `b`-dependence (of size `ν_j ≤ β_j^{-1}`) is absent.
* `Mobs_const_eq_zero_massFree`: for a unit vector `e_{i₀}` and every complex `w`,
  `M^{(j)}(x; e_{i₀}, w) = 0` (with the normalization (2.1)).

**Caveat on the radius.**  The radius of the constant tube is `ρ ≍ ε_j²` in the landed class (the
data domain `Ψ̃^c(δ, δ)` constrains `|Ψ · Ψ - 1| < δ²` quadratically), not `≍ ε_j` as in P9's
`Ψ^c_const(σ, ε)`, `δ₀ = σ₁ ε_{j+1}` (P1 Lemma 2.4); the gain obtained from `M_const_diff_le` for the
radial direction is therefore `σ² ε / ε_j²`, not the printed `σ² ε / ε_j`.
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Metric Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- `vn`-version of the Cauchy step on a slice (valued in `Fin N → ℂ`). -/
theorem slice_diff_le_inv_vn {G : ℂ → Fin N → ℂ} {r B : ℝ} (hr : 0 < r)
    (hG : DifferentiableOn ℂ G (ball 0 r)) (hB : ∀ t, ‖t‖ < r → vn (G t) ≤ B)
    (h1 : vn (G 1) ≤ B) : vn (G 1 - G 0) ≤ 2 * B / r := by
  set G' : ℂ → EuclideanSpace ℂ (Fin N) := fun t => WithLp.toLp 2 (G t) with hG'
  have hd : DifferentiableOn ℂ G' (ball 0 r) :=
    (EuclideanSpace.equiv (Fin N) ℂ).symm.differentiable.comp_differentiableOn hG
  have := slice_diff_le_inv_vec (G := G') hr hd (fun t ht => hB t ht) h1
  have e : G' 1 - G' 0 = WithLp.toLp 2 (G 1 - G 0) := rfl
  rw [e] at this
  exact this

section Const

variable {P : Consts} {Q : ObsConsts} {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ} {ρ : ℝ}

/-- **Constant pairs near `e_{i₀}` lie in `Ξ^c_j(𝔹_j(X); 1, ε_j)`** (for every polymer `X ∈ 𝒟_j`):
`|v - e_{i₀}| ≤ ρ` coordinatewise, and `ν_bg L^{2j} |w - e_{i₀}| ≤ ρ`. -/
theorem const_pair_mem_xiDom (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom P.m₀ j X) (i₀ : Fin N) (v w : Fin N → ℂ)
    (hv : ∀ i, ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ)
    (hw : ∀ i, bgMass L k (β k) (ν k) * ((L : ℝ) ^ j) ^ 2 *
      ‖w i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) :
    XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
      (constFld v) (constFld w) := by
  obtain ⟨δ, hδ0, hδ1, hδ2, hδ3, hδ4⟩ := ctx.radius
  have hN : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
  have hρ0 := ctx.rho_pos
  exact xiDom_of_close ctx.bg (ctx.sf.gs_spec j ctx.j1 ctx.jk X hX).2 ctx.jk i₀ hδ0 hδ1 hδ2 hρ0
    (by nlinarith) hδ3 (constFld v) w (fun _ i => hv i) (fun _ _ _ => rfl) hw

theorem analyticAt_constFld_line (v u : Fin N → ℂ) (t : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (constFld (v + s • u) : Fld d L N₁ m₁ k N)) t := by
  refine AnalyticAt.pi (fun z => ?_)
  refine AnalyticAt.pi (fun i => ?_)
  simp only [constFld, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

/-- The slice `t ↦ (constFld (v + t • u), constFld (w + t • u'))` of constant pairs is holomorphic
for the term `M^{(j)}(x, X; ·)` as long as it stays in the domain. -/
theorem M_slice_analyticAt (hO : IsObs P Q β ν a Tm Ot Gker) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    (v w u u' : Fin N → ℂ) (S : Set ℂ)
    (hS : ∀ t ∈ S, XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
      (constFld (v + t • u)) (constFld (w + t • u'))) :
    ∀ t ∈ S, AnalyticAt ℂ (fun s : ℂ =>
      Ot.M j x X (constFld (v + s • u)) (constFld (w + s • u'))) t := by
  intro t ht
  have h1 := hO.analyticM j hj1 hjk x X hX hx (constFld (v + t • u), constFld (w + t • u')) (hS t ht)
  have h2 : AnalyticAt ℂ (fun s : ℂ => ((constFld (v + s • u) : Fld d L N₁ m₁ k N),
      (constFld (w + s • u') : Fld d L N₁ m₁ k N))) t :=
    (analyticAt_constFld_line v u t).prod (analyticAt_constFld_line w u' t)
  exact AnalyticAt.comp (g := fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Ot.M j x X p.1 p.2)
    (f := fun s : ℂ => ((constFld (v + s • u) : Fld d L N₁ m₁ k N),
      (constFld (w + s • u') : Fld d L N₁ m₁ k N))) h1 h2

/-- The bound `B_X = β^{-1/2+ρ₁} L^{-jρ₀} e^{-κ d_j(X)}` of (2.1). -/
noncomputable def termBound (P : Consts) (Q : ObsConsts) (β : ℕ → ℝ) (L j : ℕ)
    (X : Set (CTorus d L N₁ m₁ k)) : ℝ :=
  (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) * Real.exp (-P.κ * sizeJ P.m₀ j X)

/-- **Lipschitz bound for `M^{(j)}` at constant pairs** (OBSERVABLES §3.4, "Lipschitz bound in
`b`"; the Cauchy estimate on the complex line through the two pairs).  Two constant pairs
`(v, w)`, `(v', w')` with `|v - e_{i₀}| ≤ ρ/2` and `m |w - e_{i₀}| ≤ ρ/2` coordinatewise,
`m = ν_bg L^{2j}`, at distance `|v - v'| ≤ Δ`, `m |w - w'| ≤ Δ` satisfy
`|M(v, w) - M(v', w')| ≤ 4 B_X Δ / ρ`. -/
theorem M_const_diff_le (hO : IsObs P Q β ν a Tm Ot Gker) (ctx : LiftCtx P β ν a Tm ρd Ek j ρ)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    (i₀ : Fin N) (v w v' w' : Fin N → ℂ) {Δ : ℝ} (hΔ : 0 < Δ)
    (hv : ∀ i, ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hv' : ∀ i, ‖v' i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hw : ∀ i, bgMass L k (β k) (ν k) * ((L : ℝ) ^ j) ^ 2 *
      ‖w i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hw' : ∀ i, bgMass L k (β k) (ν k) * ((L : ℝ) ^ j) ^ 2 *
      ‖w' i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hdv : ∀ i, ‖v' i - v i‖ ≤ Δ)
    (hdw : ∀ i, bgMass L k (β k) (ν k) * ((L : ℝ) ^ j) ^ 2 * ‖w' i - w i‖ ≤ Δ) :
    vn (Ot.M j x X (constFld v') (constFld w') - Ot.M j x X (constFld v) (constFld w)) ≤
      4 * termBound P Q β L j X * Δ / ρ := by
  have hρ := ctx.rho_pos
  have hj1 := ctx.j1
  have hjk := ctx.jk
  set m : ℝ := bgMass L k (β k) (ν k) * ((L : ℝ) ^ j) ^ 2 with hm
  set r : ℝ := ρ / (2 * Δ) with hr
  have hr0 : 0 < r := by positivity
  -- membership along the line
  have hmem : ∀ t : ℂ, ‖t‖ < r →
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        (constFld (v + t • (v' - v))) (constFld (w + t • (w' - w))) := by
    intro t ht
    have htΔ : ‖t‖ * Δ ≤ ρ / 2 := by
      have := mul_le_mul_of_nonneg_right ht.le hΔ.le
      calc ‖t‖ * Δ ≤ r * Δ := this
        _ = ρ / 2 := by rw [hr]; field_simp
    refine const_pair_mem_xiDom ctx hX i₀ _ _ (fun i => ?_) (fun i => ?_)
    · have e : (v + t • (v' - v)) i - (Pi.single i₀ 1 : Fin N → ℂ) i =
          (v i - (Pi.single i₀ 1 : Fin N → ℂ) i) + t * (v' i - v i) := by
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
      rw [e]
      calc ‖(v i - (Pi.single i₀ 1 : Fin N → ℂ) i) + t * (v' i - v i)‖
          ≤ ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ + ‖t‖ * ‖v' i - v i‖ := by
            refine (norm_add_le _ _).trans ?_; rw [norm_mul]
        _ ≤ ρ / 2 + ‖t‖ * Δ := add_le_add (hv i) (mul_le_mul_of_nonneg_left (hdv i) (norm_nonneg _))
        _ ≤ ρ := by linarith
    · have e : (w + t • (w' - w)) i - (Pi.single i₀ 1 : Fin N → ℂ) i =
          (w i - (Pi.single i₀ 1 : Fin N → ℂ) i) + t * (w' i - w i) := by
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
      rw [e]
      have hm0 : 0 ≤ m := by
        have := bgMass_nonneg ctx.nu_pos L k (βk := β k)
        rw [hm]; positivity
      calc m * ‖(w i - (Pi.single i₀ 1 : Fin N → ℂ) i) + t * (w' i - w i)‖
          ≤ m * (‖w i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ + ‖t‖ * ‖w' i - w i‖) := by
            refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) hm0
            rw [norm_mul]
        _ = m * ‖w i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ + ‖t‖ * (m * ‖w' i - w i‖) := by ring
        _ ≤ ρ / 2 + ‖t‖ * Δ := add_le_add (hw i) (mul_le_mul_of_nonneg_left (hdw i) (norm_nonneg _))
        _ ≤ ρ := by linarith
  have hB : ∀ t : ℂ, ‖t‖ < r →
      vn (Ot.M j x X (constFld (v + t • (v' - v))) (constFld (w + t • (w' - w)))) ≤
        termBound P Q β L j X := fun t ht =>
    hO.boundM j hj1 hjk x X hX hx _ _ (hmem t ht)
  have hdiff : DifferentiableOn ℂ (fun s : ℂ =>
      Ot.M j x X (constFld (v + s • (v' - v))) (constFld (w + s • (w' - w)))) (ball 0 r) := by
    intro t ht
    exact (M_slice_analyticAt hO hj1 hjk hX hx v w (v' - v) (w' - w) (ball 0 r)
      (fun s hs => hmem s (mem_ball_zero_iff.1 hs)) t ht).differentiableAt.differentiableWithinAt
  have hp' : XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
      (constFld v') (constFld w') :=
    const_pair_mem_xiDom ctx hX i₀ v' w' (fun i => (hv' i).trans (by linarith))
      (fun i => (hw' i).trans (by linarith))
  have h1 : vn (Ot.M j x X (constFld (v + (1 : ℂ) • (v' - v))) (constFld (w + (1 : ℂ) • (w' - w)))) ≤
      termBound P Q β L j X := by
    have e1 : v + (1 : ℂ) • (v' - v) = v' := by simp
    have e2 : w + (1 : ℂ) • (w' - w) = w' := by simp
    rw [e1, e2]
    exact hO.boundM j hj1 hjk x X hX hx _ _ hp'
  have key := slice_diff_le_inv_vn hr0 hdiff hB h1
  have e1 : v + (1 : ℂ) • (v' - v) = v' := by simp
  have e2 : w + (1 : ℂ) • (w' - w) = w' := by simp
  have e3 : v + (0 : ℂ) • (v' - v) = v := by simp
  have e4 : w + (0 : ℂ) • (w' - w) = w := by simp
  simp only [e1, e2, e3, e4] at key
  refine key.trans (le_of_eq ?_)
  rw [hr]; field_simp; ring

/-- At `β_k ν_k ≤ 1` the background mass is `0` (the `ν`-free regime of the class). -/
theorem bgMass_eq_zero_of_le (L k : ℕ) {βk νk : ℝ} (h : βk * νk ≤ 1) : bgMass L k βk νk = 0 := by
  simp [bgMass, h]

/-- **The `ν`-free regime (`β_k ν_k ≤ 1`): on constant configurations near `e_{i₀}`, `M^{(j)}(x, X;
ψ, h)` does not depend on the constant field `h`** (Liouville: the background mass is `0`, the domain
has no condition on `h`, so `t ↦ M(v, w + t (w' - w))` is entire and bounded by `B_X`).  This is the
`b`-form at `λ = ∞` in the `ν`-free regime of the landed class; compare RGFREE-3 Proposition 1 for
`ℰ`.  It says that the landed `IsObs` cannot carry the physical `b`-dependence (of size
`ν_j ≤ β_j^{-1}`) of `M^{(j)}` in this regime. -/
theorem M_const_indep_h_of_massFree (hO : IsObs P Q β ν a Tm Ot Gker)
    (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (hmf : β k * ν k ≤ 1)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    (i₀ : Fin N) (v : Fin N → ℂ) (hv : ∀ i, ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ)
    (w w' : Fin N → ℂ) :
    Ot.M j x X (constFld v) (constFld w) = Ot.M j x X (constFld v) (constFld w') := by
  have hρ := ctx.rho_pos
  have hj1 := ctx.j1
  have hjk := ctx.jk
  have hbm : bgMass L k (β k) (ν k) = 0 := bgMass_eq_zero_of_le L k hmf
  set G : ℂ → Fin N → ℂ := fun s => Ot.M j x X (constFld (v + s • (0 : Fin N → ℂ)))
    (constFld (w + s • (w' - w))) with hG
  have hmem : ∀ t : ℂ, XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j
      (P.eps d L j) (constFld (v + t • (0 : Fin N → ℂ))) (constFld (w + t • (w' - w))) := by
    intro t
    refine const_pair_mem_xiDom ctx hX i₀ _ _ (fun i => ?_) (fun i => ?_)
    · simpa using hv i
    · rw [hbm]; simpa using hρ.le
  have hdiff : Differentiable ℂ G := fun t =>
    (M_slice_analyticAt hO hj1 hjk hX hx v w 0 (w' - w) Set.univ (fun s _ => hmem s) t
      (Set.mem_univ t)).differentiableAt
  have hbd : Bornology.IsBounded (Set.range G) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨termBound P Q β L j X, ?_⟩
    rintro _ ⟨t, rfl⟩
    refine (pi_norm_le_iff_of_nonneg ?_).2 (fun i => ?_)
    · exact le_trans (vn_nonneg _) (hO.boundM j hj1 hjk x X hX hx _ _ (hmem 0))
    · exact (norm_le_vn _ i).trans (hO.boundM j hj1 hjk x X hX hx _ _ (hmem t))
  have h := hdiff.apply_eq_apply_of_bounded hbd 0 1
  simpa [hG] using h

/-- The sum over polymers: `M^{(j)}(x; v, w)` is independent of the constant `h` near `e_{i₀}`. -/
theorem Mobs_const_indep_h_of_massFree (hO : IsObs P Q β ν a Tm Ot Gker)
    (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (hmf : β k * ν k ≤ 1) {x : CTorus d L N₁ m₁ k}
    (i₀ : Fin N) (v : Fin N → ℂ) (hv : ∀ i, ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ)
    (w w' : Fin N → ℂ) :
    Mobs P.m₀ Ot j x (constFld v) (constFld w) = Mobs P.m₀ Ot j x (constFld v) (constFld w') := by
  unfold Mobs
  exact finsum_mem_congr rfl (fun X hX =>
    M_const_indep_h_of_massFree hO ctx hmf hX.1 hX.2 i₀ v hv w w')

/-- **The `b`-form in the `ν`-free regime**: `M^{(j)}(x; e_{i₀}, w) = 0` for every complex constant
`w` (normalization (2.1) at `(e_{i₀}, e_{i₀})`, then independence of `h`). -/
theorem Mobs_const_eq_zero_massFree (hO : IsObs P Q β ν a Tm Ot Gker)
    (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (hmf : β k * ν k ≤ 1) (x : CTorus d L N₁ m₁ k)
    (i₀ : Fin N) (w : Fin N → ℂ) :
    Mobs P.m₀ Ot j x (constFld (Pi.single i₀ 1 : Fin N → ℂ)) (constFld w) = 0 := by
  have hv : ∀ i, ‖(Pi.single i₀ 1 : Fin N → ℂ) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ := by
    intro i; simpa using ctx.rho_pos.le
  have h1 := Mobs_const_indep_h_of_massFree hO ctx hmf (x := x) i₀ _ hv w (Pi.single i₀ 1)
  have hvv : (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) ⬝ᵥ (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) = 1 := by
    simp [dotProduct, Pi.single_apply]
  have h0 := Mobs_const_zero hO ctx.j1 ctx.jk x hvv
  have e : (fun i => (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ)) =
      (Pi.single i₀ 1 : Fin N → ℂ) := by
    funext i; by_cases h : i = i₀ <;> simp [h]
  rw [e] at h0
  rw [h1]; exact h0

/-- **Lemma 3.4 at constant configurations, `ν`-free regime** (first bound): for `v, v'` within `ρ/2`
of `e_{i₀}` with `|v' - v| ≤ Δ` coordinatewise and arbitrary constant `h = w`, `h' = w'`,
`|M(x, X; v', w') - M(x, X; v, w)| ≤ 4 B_X Δ / ρ`. -/
theorem M_const_diff_le_massFree (hO : IsObs P Q β ν a Tm Ot Gker)
    (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (hmf : β k * ν k ≤ 1)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    (i₀ : Fin N) (v w v' w' : Fin N → ℂ) {Δ : ℝ} (hΔ : 0 < Δ)
    (hv : ∀ i, ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hv' : ∀ i, ‖v' i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hdv : ∀ i, ‖v' i - v i‖ ≤ Δ) :
    vn (Ot.M j x X (constFld v') (constFld w') - Ot.M j x X (constFld v) (constFld w)) ≤
      4 * termBound P Q β L j X * Δ / ρ := by
  have hρ := ctx.rho_pos
  have hbm : bgMass L k (β k) (ν k) = 0 := bgMass_eq_zero_of_le L k hmf
  have e : Ot.M j x X (constFld v') (constFld w') = Ot.M j x X (constFld v') (constFld w) :=
    M_const_indep_h_of_massFree hO ctx hmf hX hx i₀ v' (fun i => (hv' i).trans (by linarith)) w' w
  rw [e]
  refine M_const_diff_le hO ctx hX hx i₀ v w v' w hΔ hv hv' ?_ ?_ hdv ?_
  · intro i; rw [hbm]; simpa using (by linarith : (0 : ℝ) ≤ ρ / 2)
  · intro i; rw [hbm]; simpa using (by linarith : (0 : ℝ) ≤ ρ / 2)
  · intro i; rw [hbm]; simpa using hΔ.le

/-- **(2.22) at constant configurations, `ν`-free regime**: for `v` within `ρ/2` of `e_{i₀}`,
`|v_i - δ_{i i₀}| ≤ Δ`, and any constant `h = w`,
`|M^{(j)}(x; v, w)| ≤ (4 Δ / ρ) A K₀`, where `A = β^{-1/2+ρ₁} L^{-jρ₀}` and `K₀` bounds the polymer
sum `∑_{X ∋ x} e^{-κ d_j(X)}` (P5 (1.35)).  (The gain is `Δ/ρ` with `ρ ≍ ε_j²`, see the module
docstring.) -/
theorem Mobs_const_bound_massFree (hO : IsObs P Q β ν a Tm Ot Gker)
    (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (hmf : β k * ν k ≤ 1) (x : CTorus d L N₁ m₁ k)
    (i₀ : Fin N) (v w : Fin N → ℂ) {Δ K₀ : ℝ} (hΔ : 0 < Δ)
    (hv : ∀ i, ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hdv : ∀ i, ‖(Pi.single i₀ 1 : Fin N → ℂ) i - v i‖ ≤ Δ)
    (hK : ∑ᶠ X ∈ polysAt P.m₀ j x, Real.exp (-P.κ * sizeJ P.m₀ j X) ≤ K₀)
    (hA : 0 ≤ (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀))) :
    vn (Mobs P.m₀ Ot j x (constFld v) (constFld w)) ≤
      4 * Δ / ρ * ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) * K₀) := by
  have hρ := ctx.rho_pos
  set A : ℝ := (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) with hAdef
  have hS : (polysAt P.m₀ j x).Finite := Set.toFinite _
  have hv0 : ∀ i, ‖(Pi.single i₀ 1 : Fin N → ℂ) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2 := by
    intro i; simpa using (by linarith : (0 : ℝ) ≤ ρ / 2)
  have hvv : (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) ⬝ᵥ (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) = 1 := by
    simp [dotProduct, Pi.single_apply]
  have e : (fun i => (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ)) =
      (Pi.single i₀ 1 : Fin N → ℂ) := by
    funext i; by_cases h : i = i₀ <;> simp [h]
  have hfirst : ∀ X ∈ polysAt P.m₀ j x,
      vn (Ot.M j x X (constFld v) (constFld w) - Ot.M j x X
        (constFld (fun i => (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ)))
        (constFld (fun i => (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ)))) ≤
        4 * Δ / ρ * (A * Real.exp (-P.κ * sizeJ P.m₀ j X)) := by
    intro X hX
    rw [e]
    have h := M_const_diff_le_massFree hO ctx hmf hX.1 hX.2 i₀ (Pi.single i₀ 1) (Pi.single i₀ 1) v w
      hΔ hv0 hv (fun i => by simpa [norm_sub_rev] using hdv i)
    have h' : vn (Ot.M j x X (constFld v) (constFld w) - Ot.M j x X (constFld (Pi.single i₀ 1))
        (constFld (Pi.single i₀ 1))) ≤ 4 * termBound P Q β L j X * Δ / ρ := h
    refine h'.trans (le_of_eq ?_)
    unfold termBound; rw [← hAdef]; ring
  have h2 := improved_second_of_first hO ctx.j1 ctx.jk x (constFld v) (constFld w)
    (v := (Pi.single i₀ (1 : ℝ) : Fin N → ℝ)) hvv _ hfirst
  refine h2.trans ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ hS]
  rw [finsum_mem_eq_finite_toFinset_sum _ hS] at hK
  calc ∑ X ∈ hS.toFinset, 4 * Δ / ρ * (A * Real.exp (-P.κ * sizeJ P.m₀ j X))
      = 4 * Δ / ρ * A * ∑ X ∈ hS.toFinset, Real.exp (-P.κ * sizeJ P.m₀ j X) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun X _ => by ring
    _ ≤ 4 * Δ / ρ * A * K₀ := mul_le_mul_of_nonneg_left hK (by positivity)
    _ = _ := by ring

end Const

end Balaban.Observables
