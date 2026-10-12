/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2Corr
public import Balaban.LargeField.Def7Inhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-7 v2, part 2: the clause (D1-corr) and the regime of Def-7 -- DRAFT

**Draft, pending Roland's answer to Q13.**  CLASS-RULINGS-2 items 2, 6 for the landed draft
`Def7.IsRep` (unchanged).

* `CorrCoef`, `D1Corr`: **the Def-7 v2 clause for P5 (1.8)** (item 6: "the corresponding Def-7
  representation should add this definition, its branch condition, and the `v₁, v₂` coefficient
  data").  The landed `SFData.corr` is an unconstrained datum; `D1Corr` pins it:
  - `src_pos`: the source data `St` are the source form of the terms `ℰ^{(j)}` of `𝔰` (for
    `ν_j > 0`, on constant sources);
  - `v1_lim`, `v2_lim`: the coefficient data `v^{(j)}_{1,2}` are the thermodynamic limits (P1
    p. 147 (3.110), along the tori `L^{m₀}(n+1)`) of the whole-torus sums `v1T`, `v2T` of the local
    coefficients of P1 (3.106), at the reference `(h, ν_j h)` of the physical field `h` and, for
    `v₂`, every real unit `e₂ ⟂ h`; they are functions of the block displacement;
  - `corr_eq`: on the branch domain (`ψ(x)·ψ(x)`, `ψ(y)·ψ(y)` in the slit plane),
    `corr(y, x; ψ, h) = ½ v₁(x - y)[ψ²(x) - ψ²(y)] + v₂(x - y) ν_j h·[(ψ)₀(x) - (ψ)₀(y)]`
    (`corrPair`).
  `corr_sum_eq_p5`: under `D1Corr` the sum subtracted in the landed `SFCtx.EresJ` is the restricted
  antisymmetric sum `corrSum` of P5 (1.8).
* `IsRepCorr`: `Def7.IsRep` together with `D1Corr`; `wIsRepCorr`: it is inhabited (the landed
  witness: the terms `ℰ` vanish, so `v₁ = v₂ = 0` and `corr = 0`).
* `FieldClauses.regime`: the masses of the landed Def-7 are those of the regime record
  `(k₀, ν)` of `Def6v2` (`cs.mu k = bgMassAt(k₀, k, ν_k)`, `cs.muAct k = ν_k L^{-2k}`), with the a
  priori `k₀` of D-IV.11 (`Coh.k0_eq`); `sfActMass2`, `hDomR2`, `hSetB2`: the mass of the
  small-field action and the pinned field ball that a full second version of (D1), (D2), (D7)
  would use (items 1, 4).

**Not done** (recorded for the handoff): the full second version of `IsRep` — (D1) with the
physical mass `sfActMass2` in `A*_k` and the P5 (1.8) sum in place of `corr`, (D2) with
`Def6v2.IsSFFamily2` on the pinned domain, (D7) with `hSetB2` — requires new versions of
`SFCtx.actStar … D1Form` and of the witnesses of `Def7Inhabited`.

**Reading recorded.**  P5 (1.8) does not say how the infinite-volume coefficient `v^{(j)}(y, x)`
is read at a pair of sites of a finite torus; here it is evaluated at the centred block
displacement `unlift j (x - y)` (the nearest image).
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.LargeField.Def7 Filter Topology

/-! ### The clause (D1-corr) -/

/-- **The coefficient data of P5 (1.8)** (CLASS-RULINGS-2 item 6): `v^{(j)}_1`, `v^{(j)}_2` as
functions of the scale `j` and of the block displacement in `ℤ^d` (they are translation invariant
in the thermodynamic limit). -/
structure CorrCoef (d : ℕ) where
  /-- `v^{(j)}_1` -/
  v1 : ℕ → (Fin d → ℤ) → ℂ
  /-- `v^{(j)}_2` -/
  v2 : ℕ → (Fin d → ℤ) → ℂ

section Clause

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **(D1-corr): the Def-7 v2 clause for the boundary correction of P5 (1.8)** (CLASS-RULINGS-2
item 6), for the polymer exponent `m₀`, the small-field data `𝔰`, the source data `St` of its
terms, the physical field `h` and the coefficient data `vc`.  See the module docstring.  Draft
pending Roland's answer to Q13. -/
structure D1Corr (m₀ : ℕ) (sf : SFData d L m₁ k N ϱ)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N) (hv : EuclideanSpace ℝ (Fin N))
    (vc : CorrCoef d) : Prop where
  /-- `St` is the source form of the terms `ℰ^{(j)}` of `𝔰` (positive mass, constant sources) -/
  src_pos : ∀ (N₁ : ℕ) [NeZero N₁], ∀ j, 1 ≤ j → j ≤ k → 0 < nuIdeal L k (sf.ν k) j →
    ∀ (y : Localization.CTorus d L N₁ m₁ k) (X : Set (Localization.CTorus d L N₁ m₁ k))
      (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y X Ψ (constFld b) =
        (sf.Tm N₁).E j y X Ψ (constFld ((nuIdeal L k (sf.ν k) j : ℂ)⁻¹ • b))
  /-- `v^{(j)}_1` is the thermodynamic limit of the whole-torus coefficient (P1 (3.106), (3.110)) -/
  v1_lim : ∀ j, 1 ≤ j → j ≤ k → ∀ z : Fin d → ℤ,
    Tendsto (fun n : ℕ => haveI : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
      v1T m₀ (St (torusSeq L m₀ n)) j (nuIdeal L k (sf.ν k) j) (hC hv) 0 (blockPt j z))
      atTop (𝓝 (vc.v1 j z))
  /-- `v^{(j)}_2` is the thermodynamic limit of the whole-torus coefficient, for every real unit
  `e₂ ⟂ h` -/
  v2_lim : ∀ j, 1 ≤ j → j ≤ k → ∀ e₂ : Fin N → ℝ, ∑ i, e₂ i ^ 2 = 1 → ∑ i, hv i * e₂ i = 0 →
    ∀ z : Fin d → ℤ,
    Tendsto (fun n : ℕ => haveI : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
      v2T m₀ (St (torusSeq L m₀ n)) j (nuIdeal L k (sf.ν k) j) (hC hv) (fun i => (e₂ i : ℂ)) 0
        (blockPt j z))
      atTop (𝓝 (vc.v2 j z))
  /-- the datum `corr` of `𝔰` is the pair term of P5 (1.8), on the branch domain of `(ψ)₀` -/
  corr_eq : ∀ (N₁ : ℕ) [NeZero N₁], ∀ j, 1 ≤ j → j ≤ k →
    ∀ (y x : Localization.CTorus d L N₁ m₁ k) (ψ : Fld d L N₁ m₁ k N),
      dot (ψ x) (ψ x) ∈ Complex.slitPlane → dot (ψ y) (ψ y) ∈ Complex.slitPlane →
      sf.corr N₁ j y x ψ (constFld (hC hv)) =
        corrPair (vc.v1 j (unlift j (x - y))) (vc.v2 j (unlift j (x - y)))
          (nuIdeal L k (sf.ν k) j) ψ (hC hv) y x

end Clause

section Restricted

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

/-- **Under (D1-corr) the sum subtracted in `ℰ^{(j)}(Y; ψ_j, h)` is P5 (1.8)'s restricted
antisymmetric sum**: the second sum of the landed `SFCtx.EresJ` (over `y ∈ Y ∩ T^{(j)}`,
`x ∈ Y^≈ ∩ T^{(j)}`, of the datum `corr`) is `corrSum` with the coefficients `v^{(j)}_{1,2}`, the
sitewise unit direction and the physical source `ν_j h`, when `ψ^{(j)}_k` is in the branch domain. -/
theorem corr_sum_eq_p5 (C : SFCtx S n R M K N k m₁ ϱ)
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ m₁ k N}
    {hv : EuclideanSpace ℝ (Fin N)} {vc : CorrCoef S.d} (h : D1Corr C.m₀ C.sf St hv vc)
    (Y : Set (Torus S.d (n k))) (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) {j : ℕ}
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hbr : ∀ x, dot (C.psiJ Y ψk hv j x) (C.psiJ Y ψk hv j x) ∈ Complex.slitPlane) :
    ∑ y ∈ C.alignedIn j Y, ∑ x ∈ C.alignedIn j (thickY R Y),
        C.sf.corr C.N₁ j y x (C.psiJ Y ψk hv j) (Def6.constFld (hC hv)) =
      corrSum (fun y x => vc.v1 j (unlift j (x - y))) (fun y x => vc.v2 j (unlift j (x - y)))
        (nuIdeal S.L k (C.sf.ν k) j) (C.alignedIn j Y) (C.alignedIn j (thickY R Y))
        (C.psiJ Y ψk hv j) (hC hv) :=
  Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ =>
    h.corr_eq C.N₁ j hj1 hjk y x _ (hbr x) (hbr y)

end Restricted

/-! ### The regime and the field clauses of Def-7 -/

section Field

variable {S : Setting} [NeZero S.L] {k0 k : ℕ} {cs : OpConsts} {m₁ N : ℕ} {ϱ : ℝ}
  {sf : SFData S.d S.L m₁ k N ϱ} {hv : EuclideanSpace ℝ (Fin N)}

/-- **The masses of the landed Def-7 are those of the regime record** (CLASS-RULINGS-2 item 2:
"pass the same `k₀` to Def-6, IsObs, Def-7"): the solver mass is `bgMassAt(k₀, k, ν_k)` and the
mass of the main action of the large-field operators is the physical mass `ν_k L^{-2k}`. -/
theorem _root_.Balaban.LargeField.Def7.FieldClauses.regime (h : FieldClauses S k0 k cs sf hv) :
    cs.mu k = (⟨k0, sf.ν⟩ : Regime S.L).bgMass k ∧
      cs.muAct k = (⟨k0, sf.ν⟩ : Regime S.L).physMass k := by
  refine ⟨?_, ?_⟩
  · rw [h.mu_eq k le_rfl]; exact (bgMassAt_eq_lfBgMass S.L k0 sf.ν k).symm
  · rw [h.muAct_eq k le_rfl]
    show _ = sf.ν k * ((S.L : ℝ) ^ k)⁻¹ ^ 2
    rw [pow_mul, div_eq_mul_inv, inv_pow, ← pow_mul, ← pow_mul, mul_comm k 2]

/-- **The mass of the small-field action `A*_k` in the second version** (CLASS-RULINGS-2 item 1;
the docstring of `Def7.sfActMass`): the physical mass `cs.muAct k = ν_k L^{-2k}`, not the solver
mass. -/
def sfActMass2 (cs : OpConsts) (k : ℕ) : ℝ := cs.muAct k

theorem sfActMass2_eq (h : FieldClauses S k0 k cs sf hv) :
    sfActMass2 cs k = (⟨k0, sf.ν⟩ : Regime S.L).physMass k := h.regime.2

/-- The landed small-field action mass is the background mass of the regime. -/
theorem sfActMass_eq (h : FieldClauses S k0 k cs sf hv) :
    sfActMass cs k = (⟨k0, sf.ν⟩ : Regime S.L).bgMass k := h.regime.1

/-- **The pinned field ball** `‖h - h_*‖ < r_h` around the physical field (CLASS-RULINGS-2
item 4): the complex `h`-domain of the terms `ℛ^{(k)}_n` (D2) and of the boundary terms (D7) in the
second version, replacing `Def7.hDomR` (`Set.univ`) and `Def7.hSetB` (`{h}`). -/
def hDomR2 (hv : EuclideanSpace ℝ (Fin N)) (rH : ℝ) : Set (Fin N → ℂ) :=
  {h | vn (fun i => h i - hC hv i) < rH}

/-- The external fields of the boundary terms in the second version: the pinned ball. -/
def hSetB2 (hv : EuclideanSpace ℝ (Fin N)) (rH : ℝ) : Set (Fin N → ℂ) := hDomR2 hv rH

omit [NeZero S.L] in
/-- The physical field lies in the pinned ball, which lies in the landed (unrestricted) domain. -/
theorem hSetB_subset_hSetB2 {rH : ℝ} (hr : 0 < rH) :
    hSetB hv ⊆ hSetB2 hv rH ∧ hDomR2 hv rH ⊆ hDomR N := by
  refine ⟨?_, fun _ _ => Set.mem_univ _⟩
  rintro h rfl
  show vn (fun i => hC hv i - hC hv i) < rH
  have : (fun i => hC hv i - hC hv i) = 0 := by funext i; simp
  rw [this, vn_zero]; exact hr

end Field

/-! ### `IsRep` with (D1-corr), and its witness -/

section Rep

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {P6 : Def6.Consts} {C7 : Consts7} {k : ℕ} {ϱ : ℝ}

/-- **`IsRep_k` with the clause (D1-corr)** (Def-7 with CLASS-RULINGS-2 item 6): the landed draft
predicate `Def7.IsRep` for the family `F` and the density `ρ`, and the clause `D1Corr` for the
small-field data of `F`, the source data `St` and the coefficient data `vc`.  Draft pending Roland's
answer to Q13; the full second version of (D1), (D2), (D7) is not included (module docstring). -/
structure IsRepCorr (S : Setting) (R : ℕ → ℝ) (k0 K M : ℕ) [NeZero M] [NeZero S.L] (N : ℕ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M) (cs : OpConsts)
    (P : BudgetConsts) (P6 : Def6.Consts) (C7 : Consts7) (β ν : ℝ)
    (hv : EuclideanSpace ℝ (Fin N)) (k : ℕ) {ϱ : ℝ} (hM6 : M = S.L ^ (P6.m₀ + C7.m₁))
    (hkK : k ≤ K) (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ)
    (ρ : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) →
      (GIdx S (sides S.L K nK) M K N → ℂ) → ℂ)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ C7.m₁ k N) (vc : CorrCoef S.d) :
    Prop where
  rep : IsRep S R k0 K M N geo cs P P6 C7 β ν hv k hM6 hkK F ρ
  corr : D1Corr P6.m₀ F.sf St hv vc

end Rep

section Witness

open Balaban.LargeField.Def7.Wit

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

omit [NeZero L] [NeZero N₁] in
theorem v1Loc_zero (j : ℕ) (νj : ℝ) (e₁ : Fin N → ℂ) (x : Localization.CTorus d L N₁ m₁ k) :
    v1Loc (fun _ _ : Fld d L N₁ m₁ k N => (0 : ℂ)) j νj e₁ x = 0 := by
  simp [v1Loc]

omit [NeZero L] [NeZero N₁] in
theorem v2Loc_zero (j : ℕ) (νj : ℝ) (e₁ e₂ : Fin N → ℂ) (x : Localization.CTorus d L N₁ m₁ k) :
    v2Loc (fun _ _ : Fld d L N₁ m₁ k N => (0 : ℂ)) j νj e₁ e₂ x = 0 := by
  simp [v2Loc]

/-- **(D1-corr) is inhabited**: for the small-field data of the landed witness of Def-7 (zero
terms, `corr = 0`), with the reparametrized source data and the coefficients `v₁ = v₂ = 0`. -/
theorem wD1Corr (ν : ℝ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin 2)) :
    D1Corr m₀ (wSF ν 3) (fun N₁ _ => sourceOf (wSF ν 3).ν ((wSF ν 3).Tm N₁)) hv
      ⟨fun _ _ => 0, fun _ _ => 0⟩ where
  src_pos := fun _ _ _ _ _ _ _ _ _ _ => rfl
  v1_lim := by
    intro j _ _ z
    have h : ∀ n : ℕ, (haveI : NeZero (torusSeq 3 m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
        v1T m₀ (sourceOf (wSF ν 3).ν ((wSF ν 3).Tm (torusSeq 3 m₀ n))) j
          (nuIdeal 3 1 ((wSF ν 3).ν 1) j) (hC hv) 0 (blockPt j z)) = 0 := by
      intro n
      have : NeZero (torusSeq 3 m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
      unfold v1T
      refine finsum_mem_eq_zero_of_forall_eq_zero fun X _ => ?_
      exact v1Loc_zero _ _ _ _
    simp only [h]
    exact tendsto_const_nhds
  v2_lim := by
    intro j _ _ e₂ _ _ z
    have h : ∀ n : ℕ, (haveI : NeZero (torusSeq 3 m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
        v2T m₀ (sourceOf (wSF ν 3).ν ((wSF ν 3).Tm (torusSeq 3 m₀ n))) j
          (nuIdeal 3 1 ((wSF ν 3).ν 1) j) (hC hv) (fun i => (e₂ i : ℂ)) 0 (blockPt j z)) = 0 := by
      intro n
      have : NeZero (torusSeq 3 m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
      unfold v2T
      refine finsum_mem_eq_zero_of_forall_eq_zero fun X _ => ?_
      exact v2Loc_zero _ _ _ _ _
    simp only [h]
    exact tendsto_const_nhds
  corr_eq := by
    intro N₁ _ j _ _ y x ψ _ _
    show (0 : ℂ) = _
    simp [corrPair]

/-- **`IsRepCorr` is inhabited** (the landed witness of `IsRep_1`, `d = L = 3`, `N = 2`,
`0 < ν`, `β ν L^d ≤ 1`, with zero coefficients). -/
theorem wIsRepCorr (ν : ℝ) (hν0 : 0 < ν) (hν : wβ * ν * 27 ≤ 1) :
    IsRepCorr wS wR (kZero wS.d wS.L wβ ν) 1 27 2 wGeoF (wCs ν (kZero wS.d wS.L wβ ν))
      (budgetConsts wβ) wP6 wC7 wβ ν whv 1 wM6 le_rfl (wFam ν (kZero wS.d wS.L wβ ν) (1 + 1))
      (wRho ν (kZero wS.d wS.L wβ ν) (1 + 1))
      (fun N₁ _ => sourceOf (wSF ν 3).ν ((wSF ν 3).Tm N₁)) ⟨fun _ _ => 0, fun _ _ => 0⟩ where
  rep := wIsRep ν hν0 hν
  corr := wD1Corr ν _ whv

end Witness

end Balaban.LargeField.Def7v2
