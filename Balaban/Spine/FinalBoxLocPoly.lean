/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalBoxLocRGeom
public import Balaban.Green.FinalBoxLocParam
public import Balaban.Green.FinalBoxLocConsts
public import Balaban.Green.FinalBoxLocWhiten
public import Balaban.Fluctuation.DARateNumerics
public import Balaban.Polymer.GasBound

/-!
# The local form of a family of polymer terms of the block field on the box (A6-3, (L4), core)

The level-`k` terms of the class (`ℛ^{(k)}_n(X)`, and `ℰ^{(k)}(y, X)`, `ℳ^{(k)}(x, X)` at the top
level) are functions of the complex block field `ψ` on the box that read `ψ` on the blocks of a
polymer `X ∈ 𝒟_k` and are analytic and bounded by `amp · e^{-κ_R d_k(X)}` on the sup ball of
radius `r` around the constant configuration `h` (`PolyTerms`, a family indexed by a finite set of
labels; `PolyTerms.empty` inhabits it).  The cut family on the blocks is `T(s) = c · whitenCut(s)`
(`blockCut`), the cut family of the localized square root `L = whitenCut(1)` (Amendment B-1′,
localization radius `D`), with macro cells of side `M_c`; `polyLocal` collects the rooted
coefficients of the normalized terms `τ_a(ψ) - τ_a(h)`.  In the application `c = β_k^{-1/2}` and
`w = ψ̂` is the Gaussian variable of the box.  For complex `w` with `‖w‖_∞ ≤ ρ`,
`m = |c| B_box ρ < r`:

* `sum_polyLocal`: `∑_Y W_Y(w, g) = ∑_a (τ_a(h + c L w) - τ_a(h))`;
* `polyLocal_congr_w` (W1), `polyLocal_congr_g` (W2), `polyLocal_eq_zero_of_not_isAnimal` (W3),
  `analyticOnNhd_polyLocal` (joint analyticity in `(g, w)`), `polyLocal_zero_var` (`W_Y(0, g) = 0`);
* `polyLocal_bound` (W5, cell units, `M_c = L^{m₀+m₁}`): if at the source `g` the labels of every
  polymer `X` carry the amplitude `∑_{a ↦ X} amp(g)_a ≤ F e^{λ d_k(X)}`, then
  `∑_{Y ∋ x} ‖W_Y‖ e^{α #cells(Y)} ≤ polyBoundConst F m r κ_R λ κ α`, linear in `m` for `m ≤ r/2`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.LargeField Balaban.LargeField.Def7 Balaban.Localization
  Balaban.Green Balaban.SmallField Balaban.Analysis Finset

section Defs

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (hv : EuclideanSpace ℝ (Fin N))

/-- The constant configuration `h` as a block field. -/
def hvField : BlockAt S n M K k × Fin N → ℂ := fun p => ((hv p.2 : ℝ) : ℂ)

/-- The domain of the terms: sources of the unit `ℓ¹` ball and block fields within `r` of `h`. -/
def rDom (r : ℝ) : Set ((GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ)) :=
  {p | ∑ q, ‖p.1 q‖ < 1 ∧ p.2 ∈ Metric.ball (hvField (S := S) (n := n) (M := M) (K := K)
    (k := k) hv) r}

/-- **A family of polymer terms of the block field**, indexed by a finite set `A` of labels: the
polymer `X_a ∈ 𝒟_k`, the term `τ(g)_a(ψ)` reading `ψ` on the blocks of `X_a` and the source at the
fine sites of these blocks, analytic in `(g, ψ)` and bounded by `amp_a e^{-κ_R d_k(X_a)}` on the
domain `rDom hv r` (the amplitude `amp(g)_a` may depend on the source, e.g. `|g(x)|` for the
source terms). -/
structure PolyTerms (r κR : ℝ) (A : Type*) [Fintype A] where
  /-- the polymer of a label -/
  X : A → Set (Localization.CTorus S.d S.L C.N₁ m₁ k)
  /-- the polymers lie in `𝒟_k` -/
  isPoly : ∀ a, Def6.IsPolyDom C.m₀ k (X a)
  /-- the terms -/
  τ : (GIdx S n M K N → ℂ) → A → (BlockAt S n M K k × Fin N → ℂ) → ℂ
  /-- the amplitudes (they may depend on the source) -/
  amp : (GIdx S n M K N → ℂ) → A → ℝ
  amp_nonneg : ∀ g a, 0 ≤ amp g a
  /-- locality in the block field -/
  reads : ∀ g a, ReadsOn (blockSites N (blocksOf C (X a))) (τ g a)
  /-- locality in the source -/
  congr_g : ∀ a (g g' : GIdx S n M K N → ℂ),
    (∀ x, jBlock S.d S.L (M * n K) K k x ∈ blocksOf C (X a) → ∀ i, g (x, i) = g' (x, i)) →
      ∀ ψ, τ g a ψ = τ g' a ψ
  /-- analyticity on the domain -/
  analytic : ∀ a, AnalyticOnNhd ℂ
    (fun p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ) => τ p.1 a p.2) (rDom hv r)
  /-- the bound on the domain -/
  bound : ∀ a, ∀ p ∈ rDom hv r,
    ‖τ p.1 a p.2‖ ≤ amp p.1 a * Real.exp (-κR * Def6.sizeJ C.m₀ k (X a))

/-- **`PolyTerms` is inhabited** (rule 10): the empty family. -/
def PolyTerms.empty (r κR : ℝ) : PolyTerms C hv r κR Empty where
  X := fun a => a.elim
  isPoly := fun a => a.elim
  τ := fun _ a => a.elim
  amp := fun _ a => a.elim
  amp_nonneg := fun _ a => a.elim
  reads := fun _ a => a.elim
  congr_g := fun a => a.elim
  analytic := fun a => a.elim
  bound := fun a => a.elim

/-- **The cut family on the `k`-blocks**: `c · whitenCut(s)`, the cut family of the localized square
root `L = whitenCut(1)` of the final Hessian (mass `v`, weight `a`, macro side `M_c`, centre `h`,
localization radius `D`). -/
noncomputable def blockCut (c : ℂ) (Mc : ℕ) (v a : ℝ) (D : ℕ)
    (s : MacIdx S.d (M * n K * S.L ^ (K - k)) Mc → ℂ) (p q : BlockAt S n M K k × Fin N) : ℂ :=
  c * whitenCut S.d S.L (M * n K * S.L ^ (K - k)) k Mc v a (hC hv) D s p q

variable {C hv}

/-- **The union of two families of polymer terms** (labels `A₁ ⊕ A₂`). -/
def PolyTerms.sum {r κR : ℝ} {A₁ A₂ : Type*} [Fintype A₁] [Fintype A₂]
    (P₁ : PolyTerms C hv r κR A₁) (P₂ : PolyTerms C hv r κR A₂) :
    PolyTerms C hv r κR (A₁ ⊕ A₂) where
  X := Sum.elim P₁.X P₂.X
  isPoly := fun t => by cases t with | inl a => exact P₁.isPoly a | inr a => exact P₂.isPoly a
  τ := fun g => Sum.elim (P₁.τ g) (P₂.τ g)
  amp := fun g => Sum.elim (P₁.amp g) (P₂.amp g)
  amp_nonneg := fun g t => by
    cases t with | inl a => exact P₁.amp_nonneg g a | inr a => exact P₂.amp_nonneg g a
  reads := fun g t => by cases t with | inl a => exact P₁.reads g a | inr a => exact P₂.reads g a
  congr_g := fun t g g' h ψ => by
    cases t with
    | inl a => exact P₁.congr_g a g g' h ψ
    | inr a => exact P₂.congr_g a g g' h ψ
  analytic := fun t => by
    cases t with | inl a => exact P₁.analytic a | inr a => exact P₂.analytic a
  bound := fun t p hp => by
    cases t with | inl a => exact P₁.bound a p hp | inr a => exact P₂.bound a p hp

/-- **A family on a smaller ball** of the block fields. -/
def PolyTerms.mono {r r' κR : ℝ} {A : Type*} [Fintype A] (P : PolyTerms C hv r κR A)
    (hr : r' ≤ r) : PolyTerms C hv r' κR A where
  X := P.X
  isPoly := P.isPoly
  τ := P.τ
  amp := P.amp
  amp_nonneg := P.amp_nonneg
  reads := P.reads
  congr_g := P.congr_g
  analytic := fun t => (P.analytic t).mono fun _ hp =>
    ⟨hp.1, Metric.ball_subset_ball hr hp.2⟩
  bound := fun t p hp => P.bound t p ⟨hp.1, Metric.ball_subset_ball hr hp.2⟩

/-- **The local form of a family of polymer terms**: the rooted coefficients of the normalized
terms, collected by their regions. -/
noncomputable def polyLocal {r κR : ℝ} {A : Type*} [Fintype A] (P : PolyTerms C hv r κR A)
    (c : ℂ) (Mc : ℕ) (v a : ℝ) (D : ℕ) (g : GIdx S n M K N → ℂ) (Y : Finset (BlockAt S n M K k))
    (w : BlockAt S n M K k × Fin N → ℂ) : ℂ :=
  localFormOf (normAt (P.τ g) (hvField hv)) (fun t => blocksOf C (P.X t))
    (macBoxF S.d (M * n K * S.L ^ (K - k)) Mc) (hvField hv) (blockCut hv c Mc v a D) Y w

end Defs

section Cut

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k : ℕ} (hv : EuclideanSpace ℝ (Fin N))

/-- The bound of the spin projection at a unit vector. -/
theorem norm_spinProj_hC_le (hunit : ‖hv‖ = 1) (i j : Fin N) :
    ‖Green.spinProj (hC hv) i j‖ ≤ 1 :=
  norm_spinProj_ofReal_le_one (sum_sq_eq_one_of_norm_eq_one hv hunit) i j

variable {hv}

/-- The cut family on the blocks is decoupled with the block patches of the macro boxes. -/
theorem cutDecoupling_blockCut {Mc : ℕ} {v a κ α : ℝ} (hBC : BoxCutConsts S.d S.L k Mc v a κ α)
    (c : ℂ) (D : ℕ) :
    CutDecoupling (blockPatch N (macBoxF S.d (M * n K * S.L ^ (K - k)) Mc)) (Real.exp κ)
      (blockCut (S := S) (n := n) (M := M) (K := K) (k := k) hv c Mc v a D) := by
  rw [blockPatch_macBoxF]
  exact CutDecoupling.const_mul (cutDecoupling_whitenCut hBC.hd hBC.hk hBC.hv0 hBC.hv1 hBC.ha1
    hBC.ha2 hBC.hmass hBC.hM (by linarith [hBC.ties.1]) hBC.ties.2.1 hBC.ties.2.2.1 (hC hv) D) c

theorem analyticOnNhd_blockCut {Mc : ℕ} {v a κ α : ℝ} (hBC : BoxCutConsts S.d S.L k Mc v a κ α)
    (c : ℂ) (D : ℕ) (p q : BlockAt S n M K k × Fin N) :
    AnalyticOnNhd ℂ (fun s => blockCut hv c Mc v a D s p q)
      (polydisc (0 : MacIdx S.d (M * n K * S.L ^ (K - k)) Mc → ℂ) (fun _ => Real.exp κ)) :=
  fun s hs => analyticAt_const.mul (analyticOnNhd_whitenCut hBC.hd hBC.hk hBC.hv0 hBC.hv1
    hBC.ha1 hBC.ha2 hBC.hmass hBC.hM (by linarith [hBC.ties.1]) hBC.ties.2.1 hBC.ties.2.2.1
    (hC hv) D p q s hs)

theorem whitenCut_row_bound_hC {Mc : ℕ} {v a κ α : ℝ} (hBC : BoxCutConsts S.d S.L k Mc v a κ α)
    (hunit : ‖hv‖ = 1) (D : ℕ) :
    ∀ s ∈ polydisc (0 : MacIdx S.d (M * n K * S.L ^ (K - k)) Mc → ℂ) (fun _ => Real.exp κ),
      ∀ q : BlockAt S n M K k × Fin N,
        ∑ q', ‖whitenCut S.d S.L (M * n K * S.L ^ (K - k)) k Mc v a (hC hv) D s q q'‖ ≤
          boxCutConst S.d S.L N a κ 1 := fun s hs q =>
  whitenCut_row_bound hBC.hd hBC.hk hBC.hv0 hBC.hv1 hBC.ha1 hBC.ha2 hBC.hmass hBC.hM
    (by linarith [hBC.ties.1]) hBC.ties.2.1 hBC.ties.2.2.1 (norm_spinProj_hC_le hv hunit) D hs q

/-- The cut fields stay within `m` of `h`. -/
theorem linField_blockCut_mem_closedBall {Mc : ℕ} {v a κ α : ℝ}
    (hBC : BoxCutConsts S.d S.L k Mc v a κ α) (hunit : ‖hv‖ = 1) (c : ℂ) (D : ℕ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) {w : BlockAt S n M K k × Fin N → ℂ} (hw : ∀ q, ‖w q‖ ≤ ρ)
    {s : MacIdx S.d (M * n K * S.L ^ (K - k)) Mc → ℂ}
    (hs : s ∈ polydisc (0 : MacIdx S.d (M * n K * S.L ^ (K - k)) Mc → ℂ) (fun _ => Real.exp κ)) :
    linField (hvField hv) (blockCut hv c Mc v a D) s w ∈
      Metric.closedBall (hvField hv) (‖c‖ * boxCutConst S.d S.L N a κ 1 * ρ) :=
  linField_mem_closedBall_of_row_bound (boxCutConst_nonneg hBC.hd zero_le_one)
    (whitenCut_row_bound_hC hBC hunit D) c (hvField hv) hρ hw hs

end Cut

section Form

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} {C : SFCtx S n R M K N k m₁ ϱ}
  {hv : EuclideanSpace ℝ (Fin N)} {r κR : ℝ} {A : Type*} [Fintype A] {D : ℕ}
  (P : PolyTerms C hv r κR A)

/-- **(W1)**: `W_Y` reads `w` on `Y × Fin N` only. -/
theorem polyLocal_congr_w {Mc : ℕ} {v a κ α : ℝ} (hBC : BoxCutConsts S.d S.L k Mc v a κ α)
    (c : ℂ) (g : GIdx S n M K N → ℂ) (Y : Finset (BlockAt S n M K k))
    {w w' : BlockAt S n M K k × Fin N → ℂ}
    (hww : ∀ p : BlockAt S n M K k × Fin N, p.1 ∈ Y → w p = w' p) :
    polyLocal P c Mc v a D g Y w = polyLocal P c Mc v a D g Y w' :=
  localFormOf_congr (Real.one_lt_exp_iff.2 (by linarith [hBC.ties.1]))
    (cutDecoupling_blockCut hBC c D) Y hww

/-- **(W3)**: `W_Y = 0` unless `Y` is a nonempty connected set of blocks. -/
theorem polyLocal_eq_zero_of_not_isAnimal {Mc : ℕ} (hMc : 0 < Mc) (c : ℂ) (v a : ℝ)
    (g : GIdx S n M K N → ℂ) {Y : Finset (BlockAt S n M K k)}
    (hY : ¬ Polymer.IsAnimal (Polymer.blockGraph S.d (M * n K * S.L ^ (K - k))) Y)
    (w : BlockAt S n M K k × Fin N → ℂ) : polyLocal P c Mc v a D g Y w = 0 :=
  localFormOf_eq_zero_of_not_isAnimal _ (fun t => isAnimal_blocksOf C (P.isPoly t))
    (isAnimal_macBoxF hMc) hY w

/-- `W_Y(0, g) = 0`. -/
theorem polyLocal_zero_var (c : ℂ) (Mc : ℕ) (v a : ℝ) (g : GIdx S n M K N → ℂ)
    (Y : Finset (BlockAt S n M K k)) : polyLocal P c Mc v a D g Y 0 = 0 :=
  localFormOf_zero_var (normAt_self _ _) Y

/-- **(W2)**: `W_Y` reads the source at the fine sites of the blocks of `Y` only. -/
theorem polyLocal_congr_g (c : ℂ) (Mc : ℕ) (v a : ℝ) (Y : Finset (BlockAt S n M K k))
    {g g' : GIdx S n M K N → ℂ}
    (hgg : ∀ x, jBlock S.d S.L (M * n K) K k x ∈ Y → ∀ i, g (x, i) = g' (x, i))
    (w : BlockAt S n M K k × Fin N → ℂ) :
    polyLocal P c Mc v a D g Y w = polyLocal P c Mc v a D g' Y w := by
  unfold polyLocal
  refine localFormOf_congr_param (fun g => normAt (P.τ g) (hvField hv))
    (fun Y g g' => ∀ x, jBlock S.d S.L (M * n K) K k x ∈ Y → ∀ i, g (x, i) = g' (x, i))
    (fun hYY' h x hx i => h x (hYY' hx) i) (fun t g g' h => ?_) Y hgg w
  funext u
  simp only [normAt]
  rw [P.congr_g t g g' h u, P.congr_g t g g' h (hvField hv)]

open Classical in
/-- **The rooted expansion of a term** at the cut field of the blocks. -/
theorem poly_expansion (hunit : ‖hv‖ = 1) {Mc : ℕ} {v a κ α : ℝ}
    (hBC : BoxCutConsts S.d S.L k Mc v a κ α) {c : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hm : ‖c‖ * boxCutConst S.d S.L N a κ 1 * ρ < r) {g : GIdx S n M K N → ℂ}
    (hg : ∑ q, ‖g q‖ < 1) {w : BlockAt S n M K k × Fin N → ℂ} (hw : ∀ q, ‖w q‖ ≤ ρ) (t : A) :
    P.τ g t (linField (hvField hv) (blockCut hv c Mc v a D) (fun _ => 1) w) =
        P.τ g t (hvField hv) +
        ∑ C' ∈ Finset.univ.filter (fun C' : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc) =>
          C'.Nonempty ∧ IsRootedFamily (blockPatch N (macBoxF S.d (M * n K * S.L ^ (K - k)) Mc))
            (blockSites N (blocksOf C (P.X t))) C'),
          rootedCoef (P.τ g t) (hvField hv) (blockCut hv c Mc v a D) w C' ∧
      ∀ C', C'.Nonempty → ‖rootedCoef (P.τ g t) (hvField hv) (blockCut hv c Mc v a D) w C'‖ ≤
        P.amp g t * Real.exp (-κR * Def6.sizeJ C.m₀ k (P.X t)) *
          (‖c‖ * boxCutConst S.d S.L N a κ 1 * ρ) /
          (r - ‖c‖ * boxCutConst S.d S.L N a κ 1 * ρ) * Real.exp (-(κ - 1) * C'.card) := by
  have hτan : AnalyticOnNhd ℂ (P.τ g t) (Metric.ball (hvField hv) r) := fun u hu =>
    AnalyticAt.comp (g := fun p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ) =>
        P.τ p.1 t p.2) (f := fun u => (g, u))
      (P.analytic t (g, u) ⟨hg, hu⟩) (analyticAt_const.prod analyticAt_id)
  have hτb : ∀ u ∈ Metric.ball (hvField hv) r,
      ‖P.τ g t u‖ ≤ P.amp g t * Real.exp (-κR * Def6.sizeJ C.m₀ k (P.X t)) :=
    fun u hu => P.bound t (g, u) ⟨hg, hu⟩
  have hκ0 : 0 ≤ κ := by linarith [hBC.ties.1]
  have key := rootedExpansion_of_row_bound hBC.ties.1
    (cutDecoupling_whitenCut (N₀ := M * n K * S.L ^ (K - k)) (k := k) (M := Mc) (v := v)
      (a := a) hBC.hd hBC.hk hBC.hv0 hBC.hv1 hBC.ha1 hBC.ha2 hBC.hmass hBC.hM hκ0 hBC.ties.2.1
      hBC.ties.2.2.1 (hC hv) D)
    (analyticOnNhd_whitenCut hBC.hd hBC.hk hBC.hv0 hBC.hv1 hBC.ha1 hBC.ha2 hBC.hmass hBC.hM hκ0
      hBC.ties.2.1 hBC.ties.2.2.1 (hC hv) D)
    (boxCutConst_nonneg hBC.hd zero_le_one) (whitenCut_row_bound_hC hBC hunit D) c
    (hvField hv) (P.reads g t) hτan hτb hρ w hw hm
  dsimp only at key
  rw [← blockPatch_macBoxF] at key
  exact ⟨key.1, key.2.2.2⟩

/-- **The sum of the local form** is the sum of the changes of the terms:
`∑_Y W_Y(w, g) = ∑_a (τ_a(h + T(1) w) - τ_a(h))`. -/
theorem sum_polyLocal (hunit : ‖hv‖ = 1) {Mc : ℕ} {v a κ α : ℝ}
    (hBC : BoxCutConsts S.d S.L k Mc v a κ α) {c : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hm : ‖c‖ * boxCutConst S.d S.L N a κ 1 * ρ < r) {g : GIdx S n M K N → ℂ}
    (hg : ∑ q, ‖g q‖ < 1) {w : BlockAt S n M K k × Fin N → ℂ} (hw : ∀ q, ‖w q‖ ≤ ρ) :
    ∑ Y, polyLocal P c Mc v a D g Y w =
      ∑ t, (P.τ g t (linField (hvField hv) (blockCut hv c Mc v a D) (fun _ => 1) w) -
        P.τ g t (hvField hv)) := by
  unfold polyLocal
  exact sum_localFormOf_normAt fun t => (poly_expansion P hunit hBC hρ hm hg hw t).1

/-- **(W4) The local form is analytic in `(g, w)`** on the unit `ℓ¹` ball of sources and the
complex variables with `‖w‖_∞ ≤ ρ`, `m = |c| B_box ρ < r` (so along the dilations
`t ↦ W_Y(t w, g)`, `|t| ≤ R_t`, for `R_t p₁ ≤ ρ`, `analyticOnNhd_comp_dilation`, and continuously
for real `w`, `continuousOn_comp_ofReal`). -/
theorem analyticOnNhd_polyLocal (hunit : ‖hv‖ = 1) {Mc : ℕ} {v a κ α : ℝ}
    (hBC : BoxCutConsts S.d S.L k Mc v a κ α) (hr0 : 0 < r) {c : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hm : ‖c‖ * boxCutConst S.d S.L N a κ 1 * ρ < r) (Y : Finset (BlockAt S n M K k)) :
    AnalyticOnNhd ℂ (fun p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ) =>
      polyLocal P c Mc v a D p.1 Y p.2) {p | ∑ q, ‖p.1 q‖ < 1 ∧ ∀ q, ‖p.2 q‖ ≤ ρ} := by
  unfold polyLocal
  refine analyticOnNhd_localFormOf_param (Real.one_lt_exp_iff.2 (by linarith [hBC.ties.1]))
    (cutDecoupling_blockCut hBC c D) (analyticOnNhd_blockCut hBC c D)
    (τ := fun g => normAt (P.τ g) (hvField hv)) (V := rDom hv r)
    (D := {p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ) |
      ∑ q, ‖p.1 q‖ < 1 ∧ ∀ q, ‖p.2 q‖ ≤ ρ}) (fun t => ?_) (fun p hp s hs => ?_) Y
  · intro p hp
    have h1 := P.analytic t p hp
    have h2 : AnalyticAt ℂ (fun p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ) =>
        P.τ p.1 t (hvField hv)) p :=
      AnalyticAt.comp (g := fun p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ) =>
          P.τ p.1 t p.2)
        (f := fun p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ) => (p.1, hvField hv))
        (P.analytic t (p.1, hvField hv) ⟨hp.1, Metric.mem_ball_self hr0⟩)
        (analyticAt_fst.prod analyticAt_const)
    exact h1.sub h2
  · exact ⟨hp.1, Metric.closedBall_subset_ball hm
      (linField_blockCut_mem_closedBall hBC hunit c D hρ hp.2 hs)⟩

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem norm_dilation_le {t : ℂ} {Rt p1 : ℝ} (ht : ‖t‖ < Rt) {w : BlockAt S n M K k × Fin N → ℝ}
    (hw : ∀ p, |w p| ≤ p1) (p : BlockAt S n M K k × Fin N) : ‖t * (w p : ℂ)‖ ≤ Rt * p1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul ht.le (hw p) (abs_nonneg _) ((norm_nonneg t).trans ht.le)

/-- **(W4) at the dilations**: for a real `w` with `|w| ≤ p₁`, `(t, g) ↦ W_Y(t w, g)` is analytic on
`|t| < R_t`, `‖g‖₁ < 1`, when `m = |c| B_box R_t p₁ < r`. -/
theorem analyticOnNhd_polyLocal_dilation (hunit : ‖hv‖ = 1) {Mc : ℕ} {v a κ α : ℝ}
    (hBC : BoxCutConsts S.d S.L k Mc v a κ α) (hr0 : 0 < r) {c : ℂ} {Rt p1 : ℝ} (hp1 : 0 ≤ p1)
    (hRt : 0 ≤ Rt) (hm : ‖c‖ * boxCutConst S.d S.L N a κ 1 * (Rt * p1) < r)
    (Y : Finset (BlockAt S n M K k)) {w : BlockAt S n M K k × Fin N → ℝ} (hw : ∀ p, |w p| ≤ p1) :
    AnalyticOnNhd ℂ (fun q : ℂ × (GIdx S n M K N → ℂ) =>
        polyLocal P c Mc v a D q.2 Y (fun p => q.1 * (w p : ℂ)))
      (Metric.ball (0 : ℂ) Rt ×ˢ {g | ∑ i, ‖g i‖ < 1}) := by
  have hA := analyticOnNhd_polyLocal (D := D) P hunit hBC hr0 (ρ := Rt * p1) (mul_nonneg hRt hp1)
    hm Y
  intro q hq
  have ht : ‖q.1‖ < Rt := by simpa using hq.1
  refine AnalyticAt.comp (g := fun p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ) =>
      polyLocal P c Mc v a D p.1 Y p.2) (f := fun q : ℂ × (GIdx S n M K N → ℂ) =>
      (q.2, fun p => q.1 * (w p : ℂ))) (hA _ ⟨hq.2, fun p => norm_dilation_le ht hw p⟩) ?_
  refine AnalyticAt.prod analyticAt_snd (analyticAt_pi_iff.2 fun p => ?_)
  exact analyticAt_fst.mul analyticAt_const

/-- **(W4) continuity at the dilations**: `(t, g, w) ↦ W_Y(t w, g)` is continuous on
`(|t| < R_t) × (‖g‖₁ < 1) × (|w| ≤ p₁)`. -/
theorem continuousOn_polyLocal_dilation (hunit : ‖hv‖ = 1) {Mc : ℕ} {v a κ α : ℝ}
    (hBC : BoxCutConsts S.d S.L k Mc v a κ α) (hr0 : 0 < r) {c : ℂ} {Rt p1 : ℝ} (hp1 : 0 ≤ p1)
    (hRt : 0 ≤ Rt) (hm : ‖c‖ * boxCutConst S.d S.L N a κ 1 * (Rt * p1) < r)
    (Y : Finset (BlockAt S n M K k)) :
    ContinuousOn (fun q : (ℂ × (GIdx S n M K N → ℂ)) × (BlockAt S n M K k × Fin N → ℝ) =>
        polyLocal P c Mc v a D q.1.2 Y (fun p => q.1.1 * (q.2 p : ℂ)))
      ((Metric.ball (0 : ℂ) Rt ×ˢ {g | ∑ i, ‖g i‖ < 1}) ×ˢ {w | ∀ p, |w p| ≤ p1}) := by
  have hA := analyticOnNhd_polyLocal (D := D) P hunit hBC hr0 (ρ := Rt * p1) (mul_nonneg hRt hp1)
    hm Y
  intro q hq
  have ht : ‖q.1.1‖ < Rt := by simpa using hq.1.1
  refine ((hA (q.1.2, fun p => q.1.1 * (q.2 p : ℂ))
    ⟨hq.1.2, fun p => norm_dilation_le ht hq.2 p⟩).continuousAt.comp
    (f := fun q : (ℂ × (GIdx S n M K N → ℂ)) × (BlockAt S n M K k × Fin N → ℝ) =>
      (q.1.2, fun p => q.1.1 * (q.2 p : ℂ))) ?_).continuousWithinAt
  refine (continuous_snd.comp continuous_fst).prodMk ?_ |>.continuousAt
  exact continuous_pi fun p => (continuous_fst.comp continuous_fst).mul
    (Complex.continuous_ofReal.comp ((continuous_apply p).comp continuous_snd))

end Form

section Bound

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} {C : SFCtx S n R M K N k m₁ ϱ}
  {hv : EuclideanSpace ℝ (Fin N)} {r κR : ℝ} {A : Type*} [Fintype A] {D : ℕ}

/-- **The weight of a term with its root cells**: for the coefficient bound
`amp e^{-κ_R d_k(X)} μ`, the cell weight `e^{α #cells}` and the root-cell factor
`(1 + A)^{#root cells}`, the product is at most `amp μ e^{γ c₁} e^{-(κ_R - c₁ γ) d_k(X)}`. -/
theorem polyWeight_le (hN : S.L ^ C.m₀ ∣ C.N₁) {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    (hX : Def6.IsPolyDom C.m₀ k X) {amp κ α μ : ℝ} (hamp : 0 ≤ amp) (hα : 0 ≤ α) (hμ : 0 ≤ μ)
    (hq : ((16 ^ S.d : ℕ) : ℝ) ^ 2 * cutRatio S.d κ α < 1) :
    amp * Real.exp (-κR * Def6.sizeJ C.m₀ k X) * μ *
        Real.exp (α * (macCellCount S.d (M * n K * S.L ^ (K - k)) (S.L ^ (C.m₀ + m₁))
          (blocksOf C X) : ℝ)) *
        (1 + animalSumConst (16 ^ S.d) (cutRatio S.d κ α)) ^
          (rootCells (blockPatch N (macBoxF S.d (M * n K * S.L ^ (K - k)) (S.L ^ (C.m₀ + m₁))))
            (blockSites N (blocksOf C X))).card ≤
      amp * (μ * Real.exp (cellGamma S.d κ α * Fluctuation.c1 S.d S.L) *
        Real.exp (-(κR - Fluctuation.c1 S.d S.L * cellGamma S.d κ α) * Def6.sizeJ C.m₀ k X)) := by
  set cc := macCellCount S.d (M * n K * S.L ^ (K - k)) (S.L ^ (C.m₀ + m₁)) (blocksOf C X)
    with hcc
  set Ac := animalSumConst (16 ^ S.d) (cutRatio S.d κ α) with hAc
  set sz := Def6.sizeJ C.m₀ k X with hsz
  have hq0 := cutRatio_pos S.d κ α
  have hAc0 : 0 ≤ Ac := animalSumConst_nonneg hq0.le hq
  have h1A : 1 ≤ 1 + Ac := by linarith
  have hMc : 0 < S.L ^ (C.m₀ + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _
  have hrc := card_rootCells_le (N := N) hMc (blocksOf C X)
  have hpow : (1 + Ac) ^ (rootCells (blockPatch N (macBoxF S.d (M * n K * S.L ^ (K - k))
      (S.L ^ (C.m₀ + m₁)))) (blockSites N (blocksOf C X))).card ≤ (1 + Ac) ^ (16 ^ S.d * cc) :=
    pow_le_pow_right₀ h1A hrc
  have hexp : (1 + Ac) ^ (16 ^ S.d * cc) =
      Real.exp ((16 : ℝ) ^ S.d * cc * Real.log (1 + Ac)) := by
    calc (1 + Ac) ^ (16 ^ S.d * cc) = (Real.exp (Real.log (1 + Ac))) ^ (16 ^ S.d * cc) := by
          rw [Real.exp_log (by linarith)]
      _ = Real.exp (((16 ^ S.d * cc : ℕ) : ℝ) * Real.log (1 + Ac)) := (Real.exp_nat_mul _ _).symm
      _ = _ := by push_cast; ring_nf
  have hγ0 : 0 ≤ cellGamma S.d κ α :=
    add_nonneg hα (mul_nonneg (by positivity) (Real.log_nonneg h1A))
  have hccle : (cc : ℝ) ≤ Fluctuation.c1 S.d S.L * (1 + sz) :=
    macCellCount_blocksOf_le C hN hX
  have hγcc : cellGamma S.d κ α * cc = α * cc + (16 : ℝ) ^ S.d * cc * Real.log (1 + Ac) := by
    unfold cellGamma; rw [← hAc]; ring
  calc amp * Real.exp (-κR * sz) * μ * Real.exp (α * cc) *
        (1 + Ac) ^ (rootCells (blockPatch N (macBoxF S.d (M * n K * S.L ^ (K - k))
          (S.L ^ (C.m₀ + m₁)))) (blockSites N (blocksOf C X))).card
      ≤ amp * Real.exp (-κR * sz) * μ * Real.exp (α * cc) * (1 + Ac) ^ (16 ^ S.d * cc) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = amp * μ * (Real.exp (-κR * sz) * Real.exp (cellGamma S.d κ α * cc)) := by
        rw [hexp, hγcc, Real.exp_add]; ring
    _ ≤ amp * μ * (Real.exp (-κR * sz) *
          Real.exp (cellGamma S.d κ α * (Fluctuation.c1 S.d S.L * (1 + sz)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
          (mul_nonneg hamp hμ)
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hccle hγ0)
    _ = _ := by
        rw [← Real.exp_add, mul_assoc μ, ← Real.exp_add]
        ring_nf

/-- **The label count of a union of families**. -/
theorem PolyTerms.sum_count {A₁ A₂ : Type*} [Fintype A₁] [Fintype A₂]
    (P₁ : PolyTerms C hv r κR A₁) (P₂ : PolyTerms C hv r κR A₂) (g : GIdx S n M K N → ℂ)
    {F₁ F₂ l₁ l₂ lam : ℝ} (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂) (h₁ : l₁ ≤ lam) (h₂ : l₂ ≤ lam)
    (hc₁ : ∀ X, ∑ t ∈ Finset.univ.filter (fun t => P₁.X t = X), P₁.amp g t ≤
      F₁ * Real.exp (l₁ * Def6.sizeJ C.m₀ k X))
    (hc₂ : ∀ X, ∑ t ∈ Finset.univ.filter (fun t => P₂.X t = X), P₂.amp g t ≤
      F₂ * Real.exp (l₂ * Def6.sizeJ C.m₀ k X))
    (X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) :
    ∑ t ∈ Finset.univ.filter (fun t => (P₁.sum P₂).X t = X), (P₁.sum P₂).amp g t ≤
      (F₁ + F₂) * Real.exp (lam * Def6.sizeJ C.m₀ k X) := by
  classical
  have hs : 0 ≤ Def6.sizeJ C.m₀ k X := treeLenCovOne_nonneg _ _ _
  rw [Finset.sum_filter, Fintype.sum_sum_type, add_mul]
  have e₁ : ∑ a : A₁, (if (P₁.sum P₂).X (Sum.inl a) = X then (P₁.sum P₂).amp g (Sum.inl a)
      else 0) = ∑ t ∈ Finset.univ.filter (fun t => P₁.X t = X), P₁.amp g t := by
    rw [Finset.sum_filter]; rfl
  have e₂ : ∑ a : A₂, (if (P₁.sum P₂).X (Sum.inr a) = X then (P₁.sum P₂).amp g (Sum.inr a)
      else 0) = ∑ t ∈ Finset.univ.filter (fun t => P₂.X t = X), P₂.amp g t := by
    rw [Finset.sum_filter]; rfl
  rw [e₁, e₂]
  refine add_le_add ((hc₁ X).trans ?_) ((hc₂ X).trans ?_)
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h₁ hs)) hF₁
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h₂ hs)) hF₂

variable (P : PolyTerms C hv r κR A)

open Classical in
/-- **The polymer sum through a site**: if the labels of every polymer carry the amplitude
`∑_{a ↦ X} amp_a ≤ F e^{λ d_k(X)}`, then
`∑_{a : c ∈ X_a} amp_a μ e^{γ c₁} e^{-(κ_R - c₁ γ) d_k(X_a)} ≤ F μ e^{γ c₁} K₀`
(`sum_polyDom_through_le`). -/
theorem sum_polyWeight_through_le (hN : S.L ^ C.m₀ ∣ C.N₁) {lam κ α μ F : ℝ} (hμ : 0 ≤ μ)
    (hF : 0 ≤ F) (g : GIdx S n M K N → ℂ)
    (hcount : ∀ X, ∑ t ∈ Finset.univ.filter (fun t => P.X t = X), P.amp g t ≤
      F * Real.exp (lam * Def6.sizeJ C.m₀ k X))
    (hTies : PolyTies S.d S.L κR lam κ α) (c₀ : Localization.CTorus S.d S.L C.N₁ m₁ k) :
    ∑ t ∈ Finset.univ.filter (fun t => c₀ ∈ P.X t),
        P.amp g t * (μ * Real.exp (cellGamma S.d κ α * Fluctuation.c1 S.d S.L) *
          Real.exp (-(κR - Fluctuation.c1 S.d S.L * cellGamma S.d κ α) *
            Def6.sizeJ C.m₀ k (P.X t))) ≤
      F * (μ * Real.exp (cellGamma S.d κ α * Fluctuation.c1 S.d S.L) *
        Fluctuation.K0 S.d S.L (κR - Fluctuation.c1 S.d S.L * cellGamma S.d κ α - lam)) := by
  classical
  set γc := Fluctuation.c1 S.d S.L * cellGamma S.d κ α with hγc
  set E := μ * Real.exp (cellGamma S.d κ α * Fluctuation.c1 S.d S.L) with hE
  have hE0 : 0 ≤ E := mul_nonneg hμ (Real.exp_pos _).le
  have hmaps : ∀ t ∈ Finset.univ.filter (fun t => c₀ ∈ P.X t),
      P.X t ∈ Finset.univ.filter (fun X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) =>
        Def6.IsPolyDom C.m₀ k X ∧ c₀ ∈ X) := fun t ht =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, P.isPoly t, (Finset.mem_filter.1 ht).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ X ∈ Finset.univ.filter (fun X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) =>
      Def6.IsPolyDom C.m₀ k X ∧ c₀ ∈ X),
      ∑ t ∈ (Finset.univ.filter fun t => c₀ ∈ P.X t).filter (fun t => P.X t = X),
        P.amp g t * (E * Real.exp (-(κR - γc) * Def6.sizeJ C.m₀ k (P.X t))) ≤
      F * E * Real.exp (-(κR - γc - lam) * Def6.sizeJ C.m₀ k X) := by
    intro X _
    have h1 : ∀ t ∈ (Finset.univ.filter fun t => c₀ ∈ P.X t).filter (fun t => P.X t = X),
        P.amp g t * (E * Real.exp (-(κR - γc) * Def6.sizeJ C.m₀ k (P.X t))) =
          P.amp g t * (E * Real.exp (-(κR - γc) * Def6.sizeJ C.m₀ k X)) := by
      intro t ht
      rw [(Finset.mem_filter.1 ht).2]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
    have h2 : ∑ t ∈ (Finset.univ.filter fun t => c₀ ∈ P.X t).filter (fun t => P.X t = X),
        P.amp g t ≤ F * Real.exp (lam * Def6.sizeJ C.m₀ k X) :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset_filter _ (Finset.subset_univ _)) fun t _ _ => P.amp_nonneg g t)
        (hcount X)
    calc (∑ t ∈ (Finset.univ.filter fun t => c₀ ∈ P.X t).filter (fun t => P.X t = X), P.amp g t) *
          (E * Real.exp (-(κR - γc) * Def6.sizeJ C.m₀ k X))
        ≤ (F * Real.exp (lam * Def6.sizeJ C.m₀ k X)) *
          (E * Real.exp (-(κR - γc) * Def6.sizeJ C.m₀ k X)) :=
          mul_le_mul_of_nonneg_right h2 (mul_nonneg hE0 (Real.exp_pos _).le)
      _ = F * E * Real.exp (-(κR - γc - lam) * Def6.sizeJ C.m₀ k X) := by
          rw [show -(κR - γc - lam) * Def6.sizeJ C.m₀ k X =
            lam * Def6.sizeJ C.m₀ k X + -(κR - γc) * Def6.sizeJ C.m₀ k X by ring, Real.exp_add]
          ring
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [← Finset.mul_sum, mul_assoc F E]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hE0) hF
  have hκ : Fluctuation.aEnt S.d S.L + 1 ≤ κR - γc - lam := by
    unfold PolyTies at hTies; linarith
  exact Fluctuation.sum_polyDom_through_le (m₀ := C.m₀) (j := k) (le_refl k) hN hκ c₀

/-- **(W5) The summed bound of the local form, in cell units**: with macro cells of side
`M = L^{m₀+m₁}`, for sources of the unit ball and complex variables with `‖w‖_∞ ≤ ρ`,
`∑_{Y ∋ x} ‖W_Y‖ e^{α #cells(Y)} ≤ polyBoundConst F m r κ_R λ κ α`, `m = |c| B_box ρ`, when the
labels of every polymer carry the amplitude `∑_{a ↦ X} amp_a ≤ F e^{λ d_k(X)}`. -/
theorem polyLocal_bound (hunit : ‖hv‖ = 1) (hN : S.L ^ C.m₀ ∣ C.N₁) {v a κ α lam F : ℝ}
    (hBC : BoxCutConsts S.d S.L k (S.L ^ (C.m₀ + m₁)) v a κ α) (hF : 0 ≤ F)
    (hTies : PolyTies S.d S.L κR lam κ α)
    {c : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hm : ‖c‖ * boxCutConst S.d S.L N a κ 1 * ρ < r)
    {g : GIdx S n M K N → ℂ} (hg : ∑ q, ‖g q‖ < 1)
    (hcount : ∀ X, ∑ t ∈ Finset.univ.filter (fun t => P.X t = X), P.amp g t ≤
      F * Real.exp (lam * Def6.sizeJ C.m₀ k X)) {w : BlockAt S n M K k × Fin N → ℂ}
    (hw : ∀ q, ‖w q‖ ≤ ρ) (x : BlockAt S n M K k) :
    ∑ Y ∈ Finset.univ.filter (fun Y : Finset (BlockAt S n M K k) => x ∈ Y),
        ‖polyLocal P c (S.L ^ (C.m₀ + m₁)) v a D g Y w‖ *
          Real.exp (α * (macCellCount S.d (M * n K * S.L ^ (K - k)) (S.L ^ (C.m₀ + m₁)) Y : ℝ)) ≤
      polyBoundConst S.d S.L F (‖c‖ * boxCutConst S.d S.L N a κ 1 * ρ) r κR lam κ α := by
  classical
  set Mc := S.L ^ (C.m₀ + m₁) with hMcdef
  set N₀ := M * n K * S.L ^ (K - k) with hN₀
  set m := ‖c‖ * boxCutConst S.d S.L N a κ 1 * ρ with hmdef
  have hM : 0 < Mc := hBC.hM
  have hα : 0 ≤ α := hBC.ties.2.2.2.1
  have hq : ((16 ^ S.d : ℕ) : ℝ) ^ 2 * cutRatio S.d κ α < 1 := by
    have := hBC.ties.2.2.2.2
    unfold cutRatio; linarith
  have hm0 : 0 ≤ m := mul_nonneg (mul_nonneg (norm_nonneg _)
    (boxCutConst_nonneg hBC.hd zero_le_one)) hρ
  have hrm : 0 < r - m := by linarith
  set μ := m / (r - m) with hμdef
  have hμ : 0 ≤ μ := div_nonneg hm0 hrm.le
  set B₁ := F * (μ * Real.exp (cellGamma S.d κ α * Fluctuation.c1 S.d S.L) *
    Fluctuation.K0 S.d S.L (κR - Fluctuation.c1 S.d S.L * cellGamma S.d κ α - lam)) with hB₁
  have hB₁0 : 0 ≤ B₁ := mul_nonneg hF (mul_nonneg (mul_nonneg hμ (Real.exp_pos _).le)
    (Fluctuation.K0_pos _ _ _).le)
  set b : A → ℝ := fun t => P.amp g t * Real.exp (-κR * Def6.sizeJ C.m₀ k (P.X t)) * μ with hbdef
  have hb : ∀ t, 0 ≤ b t := fun t =>
    mul_nonneg (mul_nonneg (P.amp_nonneg g t) (Real.exp_pos _).le) hμ
  have hcoef : ∀ t (C' : Finset (MacIdx S.d N₀ Mc)), C'.Nonempty →
      IsRootedFamily (blockPatch N (macBoxF S.d N₀ Mc)) (blockSites N (blocksOf C (P.X t))) C' →
      ‖rootedCoef (normAt (P.τ g) (hvField hv) t) (hvField hv) (blockCut hv c Mc v a D) w C'‖ ≤
        b t * Real.exp (-(κ - 1) * C'.card) := by
    intro t C' hne _
    rw [rootedCoef_normAt _ _ _ _ hne]
    refine ((poly_expansion P hunit hBC hρ hm hg hw t).2 C' hne).trans (le_of_eq ?_)
    rw [hbdef, hμdef]
    ring
  have hW : ∀ t, b t * Real.exp (α * (macCellCount S.d N₀ Mc (blocksOf C (P.X t)) : ℝ)) *
      (1 + animalSumConst (16 ^ S.d) (Real.exp (α * 16 ^ S.d) * Real.exp (-(κ - 1)))) ^
        (rootCells (blockPatch N (macBoxF S.d N₀ Mc)) (blockSites N (blocksOf C (P.X t)))).card ≤
      P.amp g t * (μ * Real.exp (cellGamma S.d κ α * Fluctuation.c1 S.d S.L) *
        Real.exp (-(κR - Fluctuation.c1 S.d S.L * cellGamma S.d κ α) *
          Def6.sizeJ C.m₀ k (P.X t))) := fun t =>
    polyWeight_le hN (P.isPoly t) (P.amp_nonneg g t) hα hμ hq
  have hthrough : ∀ c₀ : Localization.CTorus S.d S.L C.N₁ m₁ k,
      ∑ t ∈ Finset.univ.filter (fun t => c₀ ∈ P.X t),
        P.amp g t * (μ * Real.exp (cellGamma S.d κ α * Fluctuation.c1 S.d S.L) *
          Real.exp (-(κR - Fluctuation.c1 S.d S.L * cellGamma S.d κ α) *
            Def6.sizeJ C.m₀ k (P.X t))) ≤ B₁ :=
    fun c₀ => sum_polyWeight_through_le P hN hμ hF g hcount hTies c₀
  have hW0 : ∀ t, 0 ≤ P.amp g t * (μ * Real.exp (cellGamma S.d κ α * Fluctuation.c1 S.d S.L) *
      Real.exp (-(κR - Fluctuation.c1 S.d S.L * cellGamma S.d κ α) *
        Def6.sizeJ C.m₀ k (P.X t))) := fun t =>
    mul_nonneg (P.amp_nonneg g t) (mul_nonneg (mul_nonneg hμ (Real.exp_pos _).le)
      (Real.exp_pos _).le)
  -- the root sums
  have h1 : ∑ t ∈ Finset.univ.filter (fun t => x ∈ blocksOf C (P.X t)),
      b t * Real.exp (α * (macCellCount S.d N₀ Mc (blocksOf C (P.X t)) : ℝ)) *
        (1 + animalSumConst (16 ^ S.d) (Real.exp (α * 16 ^ S.d) * Real.exp (-(κ - 1)))) ^
          (rootCells (blockPatch N (macBoxF S.d N₀ Mc))
            (blockSites N (blocksOf C (P.X t)))).card ≤ B₁ := by
    refine (Finset.sum_le_sum fun t _ => hW t).trans ?_
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) fun t _ _ => hW0 t)
      (hthrough (cbase (cellSide S.L C.m₀ m₁ k) (boxLocBlockSite C x)))
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      cellBase_mem_of_mem_blocksOf C hN (P.isPoly t) (Finset.mem_filter.1 ht).2⟩
  have hdvd : S.L ^ (C.m₀ + m₁) ∣ M * n K * S.L ^ (K - k) := by
    rw [blockSide_eq C, pow_add]
    exact mul_dvd_mul_right hN _
  have h2 : ∀ l, ∑ t ∈ Finset.univ.filter (fun t =>
      l ∈ rootCells (blockPatch N (macBoxF S.d N₀ Mc)) (blockSites N (blocksOf C (P.X t)))),
      b t * Real.exp (α * (macCellCount S.d N₀ Mc (blocksOf C (P.X t)) : ℝ)) *
        (1 + animalSumConst (16 ^ S.d) (Real.exp (α * 16 ^ S.d) * Real.exp (-(κ - 1)))) ^
          (rootCells (blockPatch N (macBoxF S.d N₀ Mc))
            (blockSites N (blocksOf C (P.X t)))).card ≤ 16 ^ S.d * B₁ := by
    intro l
    refine (Finset.sum_le_sum fun t _ => hW t).trans ?_
    set Cl := (macBoxF S.d N₀ Mc l).image
      (fun b => cbase (cellSide S.L C.m₀ m₁ k) (boxLocBlockSite C b))
    refine (Polymer.sum_le_sum_cover _ (fun t => Finset.univ.filter fun c₀ => c₀ ∈ P.X t) Cl _ hW0
      fun t ht => ?_).trans ?_
    · obtain ⟨p, hpP, hpS⟩ := mem_rootCells.1 (Finset.mem_filter.1 ht).2
      exact ⟨cbase (cellSide S.L C.m₀ m₁ k) (boxLocBlockSite C p.1),
        Finset.mem_image_of_mem _ hpP, Finset.mem_filter.2 ⟨Finset.mem_univ _,
          cellBase_mem_of_mem_blocksOf C hN (P.isPoly t) hpS⟩⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      calc ∑ c₀ ∈ Cl, ∑ t ∈ Finset.univ.filter (fun t => c₀ ∈ P.X t),
            P.amp g t * (μ * Real.exp (cellGamma S.d κ α * Fluctuation.c1 S.d S.L) *
              Real.exp (-(κR - Fluctuation.c1 S.d S.L * cellGamma S.d κ α) *
                Def6.sizeJ C.m₀ k (P.X t)))
          ≤ ∑ _c₀ ∈ Cl, B₁ := Finset.sum_le_sum fun c₀ _ => hthrough c₀
        _ = Cl.card * B₁ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 16 ^ S.d * B₁ := by
            refine mul_le_mul_of_nonneg_right ?_ hB₁0
            exact_mod_cast card_cellBases_macBoxF_le C (m₀ := C.m₀) hdvd l
  have hfinal := sum_norm_localFormOf_le_of_rootSums (τ := normAt (P.τ g) (hvField hv))
    (RA := fun t => blocksOf C (P.X t)) (PB := macBoxF S.d N₀ Mc) (φ₀ := hvField hv)
    (T := blockCut hv c Mc v a D) w x (κ := κ) (θ := Real.exp (α * 16 ^ S.d)) (Real.exp_pos _) hb
    hcoef (normAt_self _ _)
    (fun Y => Real.exp (α * (macCellCount S.d N₀ Mc Y : ℝ))) (fun _ => (Real.exp_pos _).le)
    (fun t C' => exp_macCellCount_rootRegion_le hM hα _ _) (Δ := 16 ^ S.d)
    (cellGraph_degree_le hM) hq h1 h2 (mul_nonneg (by positivity) hB₁0) (nb := 7 ^ S.d)
    (card_boxes_mem_le hM x)
  refine hfinal.trans (le_of_eq ?_)
  unfold polyBoundConst
  rw [hB₁, hμdef]
  push_cast
  unfold cutRatio
  ring

/-- **(W5) at the dilations**: for a real `w` with `|w| ≤ p₁`, `|t| < R_t` and `‖g‖₁ < 1`, the summed
bound of `W_Y(t w, g)` at the radius `ρ = R_t p₁`. -/
theorem polyLocal_bound_dilation (hunit : ‖hv‖ = 1) (hN : S.L ^ C.m₀ ∣ C.N₁) {v a κ α lam F : ℝ}
    (hBC : BoxCutConsts S.d S.L k (S.L ^ (C.m₀ + m₁)) v a κ α) (hF : 0 ≤ F)
    (hTies : PolyTies S.d S.L κR lam κ α) {c : ℂ} {Rt p1 : ℝ} (hp1 : 0 ≤ p1) (hRt : 0 ≤ Rt)
    (hm : ‖c‖ * boxCutConst S.d S.L N a κ 1 * (Rt * p1) < r)
    {g : GIdx S n M K N → ℂ} (hg : ∑ q, ‖g q‖ < 1)
    (hcount : ∀ X, ∑ t ∈ Finset.univ.filter (fun t => P.X t = X), P.amp g t ≤
      F * Real.exp (lam * Def6.sizeJ C.m₀ k X))
    {w : BlockAt S n M K k × Fin N → ℝ} (hw : ∀ p, |w p| ≤ p1) {t : ℂ} (ht : ‖t‖ < Rt)
    (x : BlockAt S n M K k) :
    ∑ Y ∈ Finset.univ.filter (fun Y : Finset (BlockAt S n M K k) => x ∈ Y),
        ‖polyLocal P c (S.L ^ (C.m₀ + m₁)) v a D g Y (fun p => t * (w p : ℂ))‖ *
          Real.exp (α * (macCellCount S.d (M * n K * S.L ^ (K - k)) (S.L ^ (C.m₀ + m₁)) Y : ℝ)) ≤
      polyBoundConst S.d S.L F (‖c‖ * boxCutConst S.d S.L N a κ 1 * (Rt * p1)) r κR lam κ α :=
  polyLocal_bound P hunit hN hBC hF hTies (mul_nonneg hRt hp1) hm hg hcount
    (fun p => norm_dilation_le ht hw p) x

end Bound

end Balaban.RootFSpine
