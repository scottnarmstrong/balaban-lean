/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2
public import Balaban.LargeField.Def7Variants

/-!
# Def-7 v2, part 4: the form clause (D1) of the second version -- DRAFT

**Draft, pending Roland's answer to Q13.**  Decision in force (`orchestration/LEDGER.md`,
"DECISION: scheme A"; `notes/phase1/W2-RESOLVE.md` §4, CLASS-RULINGS-2 items 1, 6): the large-field
solver and the characteristic functions of Def-7 use `cs.mu` (zero for `k ≤ k₀`), the physical
action mass is `cs.muAct`, and the small-field action `A*_k` of the form clause carries the
physical mass `sfActMass2 = cs.muAct` (not the solver mass); the boundary correction of P5 (1.8) is
the restricted antisymmetric sum `corrSum` with the coefficients `v^{(j)}_{1,2}`, not the
unconstrained datum `SFData.corr`.

The new versions of the landed objects (the landed ones are untouched):
* `actStar2` (for `SFCtx.actStar`): mass `sfActMass2 cs k = cs.muAct k`;
* `EresJ2`, `EresK2`, `Ares2` (for `EresJ`, `EresK`, `Ares`): the second sum of `EresJ` is
  `corrSum` of the coefficient data `vc : CorrCoef`;
* `sfFactor2` (for `sfFactor`): `χ_k(Y) exp(𝒜₂ + ℱ + ℛ)(Y)`, with the landed `chiY` (mass `cs.mu`),
  `Fres` (the backgrounds are the LF backgrounds of mass `cs.mu`: the exact difference to the
  complete backgrounds of the small-field class is the interface term of W2-RESOLVE (3.1), outside
  this clause) and `Rres`;
* `integrand2`, `postTerm2`, `PostConv2`, `D1Form2` (for `integrand`, `postTerm`, `PostConv`,
  `D1Form`), and `preTerm2`, `PreConv2`, `D1PreForm2` (for `IsRep^pre`);
* `D1CorrLim`: the clauses of `D1Corr` that define the coefficient data `v^{(j)}_{1,2}` (source
  form of the terms and the two thermodynamic limits), without `corr_eq`: in the second version the
  correction is `corrSum` itself, so `SFData.corr` is not read at all (`D1Corr.toLim`);
* comparison theorems `actStar2_eq`, `EresJ2_eq`, `sfFactor2_eq`: with equal masses and under
  `D1Corr` the second version is the landed one.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Def7v2

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.LargeField.Def7
  RegionHistory Filter Topology

/-! ### The coefficient data -/

section Coef

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The clauses defining the coefficient data of P5 (1.8)** (CLASS-RULINGS-2 item 6): the clauses
`src_pos`, `v1_lim`, `v2_lim` of `D1Corr`.  `src_pos`: the source data `St` are the source form of
the terms `ℰ^{(j)}` of `𝔰`; `v1_lim`, `v2_lim`: `v^{(j)}_{1,2}` are the thermodynamic limits (P1
p. 147 (3.110), along the tori `L^{m₀}(n+1)`) of the whole-torus sums of the local coefficients of
P1 (3.106).  Unlike `D1Corr`, no clause ties the datum `SFData.corr` to them: in the second
version of the form clause the correction is `corrSum` of these coefficients. -/
structure D1CorrLim (m₀ : ℕ) (sf : SFData d L m₁ k N ϱ)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N) (hv : EuclideanSpace ℝ (Fin N))
    (vc : CorrCoef d) : Prop where
  src_pos : ∀ (N₁ : ℕ) [NeZero N₁], ∀ j, 1 ≤ j → j ≤ k → 0 < nuIdeal L k (sf.ν k) j →
    ∀ (y : Localization.CTorus d L N₁ m₁ k) (X : Set (Localization.CTorus d L N₁ m₁ k))
      (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y X Ψ (constFld b) =
        (sf.Tm N₁).E j y X Ψ (constFld ((nuIdeal L k (sf.ν k) j : ℂ)⁻¹ • b))
  v1_lim : ∀ j, 1 ≤ j → j ≤ k → ∀ z : Fin d → ℤ,
    Tendsto (fun n : ℕ => haveI : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
      v1T m₀ (St (torusSeq L m₀ n)) j (nuIdeal L k (sf.ν k) j) (hC hv) 0 (blockPt j z))
      atTop (𝓝 (vc.v1 j z))
  v2_lim : ∀ j, 1 ≤ j → j ≤ k → ∀ e₂ : Fin N → ℝ, ∑ i, e₂ i ^ 2 = 1 → ∑ i, hv i * e₂ i = 0 →
    ∀ z : Fin d → ℤ,
    Tendsto (fun n : ℕ => haveI : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
      v2T m₀ (St (torusSeq L m₀ n)) j (nuIdeal L k (sf.ν k) j) (hC hv) (fun i => (e₂ i : ℂ)) 0
        (blockPt j z))
      atTop (𝓝 (vc.v2 j z))

/-- `D1Corr` gives the defining clauses of the coefficient data. -/
theorem D1Corr.toLim {m₀ : ℕ} {sf : SFData d L m₁ k N ϱ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N} {hv : EuclideanSpace ℝ (Fin N)}
    {vc : CorrCoef d} (h : D1Corr m₀ sf St hv vc) : D1CorrLim m₀ sf St hv vc :=
  ⟨h.src_pos, h.v1_lim, h.v2_lim⟩

end Coef

/-! ### The restricted small-field functions, second version -/

section Restricted

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (vc : CorrCoef S.d) (Y : Set (Torus S.d (n k)))
  (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
  (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)

/-- **The single-scale action with half star bonds, second version** (P5 (1.5); CLASS-RULINGS-2
item 1; W2-RESOLVE §4): `A*_k(Y; ψ_k, φ_k)` with the physical mass `sfActMass2 = cs.muAct k` in
the action; the background `φ̄_k` is still the one of the solver mass `cs.mu k`. -/
noncomputable def actStar2 : ℝ :=
  actionG (levelGen (ϱ := (1 : ℝ)) k) C.weights (sfActMass2 C.cs k) hv (C.bgSet Y)
      (C.psiLevelK ψk) (C.phiBar Y ψk hv) +
    1 / 4 * starBondE (C.bgSet Y) (C.phiBar Y ψk hv)

open Classical in
/-- **`ℰ^{(j)}(Y; ψ_j, h)`, second version** (P5 (1.8)): the localized terms with `y ∈ Y`,
`X ⊂ Y^≈`, minus the restricted antisymmetric sum `corrSum` of the coefficient data `v^{(j)}_{1,2}`
of `vc` (CLASS-RULINGS-2 item 6), at the physical source `ν_j h`, in place of the datum `corr`. -/
noncomputable def EresJ2 (j : ℕ) : ℂ :=
  (∑ y ∈ C.alignedIn j Y,
      ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) | Def6.IsPolyDom C.m₀ j X ∧
          y ∈ X ∧ X ⊆ C.sset (thickY R Y)},
        (C.sf.Tm C.N₁).E j y X (C.psiJ Y ψk hv j) (Def6.constFld (hC hv))) -
    corrSum (fun y x => vc.v1 j (unlift j (x - y))) (fun y x => vc.v2 j (unlift j (x - y)))
      (nuIdeal S.L k (C.sf.ν k) j) (C.alignedIn j Y) (C.alignedIn j (thickY R Y))
      (C.psiJ Y ψk hv j) (hC hv)

/-- `ℰ_k = ∑_{j=1}^k ℰ^{(j)}`, second version (P5 (1.7)). -/
noncomputable def EresK2 : ℂ := ∑ j ∈ Finset.Icc 1 k, EresJ2 C vc Y ψk hv j

/-- **`𝒜_k = -β_k A*_k + ℰ_k - E_k |Y|_k`, second version** (P5 (1.6)): the fine-unit
coefficient `β_k L^{-k(d-2)}`, `actStar2`, `EresK2`. -/
noncomputable def Ares2 : ℂ :=
  -((betaCanon S.d S.L (C.sf.β k) k 0 : ℝ) : ℂ) * ((actStar2 C Y ψk hv : ℝ) : ℂ) +
    EresK2 C vc Y ψk hv - ((C.sf.E C.N₁ * volK M Y : ℝ) : ℂ)

/-- **The small-field factor of (D1), second version**: `χ_k(Y) exp(𝒜₂ + ℱ_k + ℛ^{(k)})(Y)`. -/
noncomputable def sfFactor2 : ℂ :=
  ((C.chiY Y ψk hv : ℝ) : ℂ) *
    Complex.exp (Ares2 C vc Y ψk hv + C.Fres Y ψk hv g + C.Rres Y ψk hv g)

/-! #### Comparison with the landed objects -/

/-- With equal masses the actions agree. -/
theorem actStar2_eq (h : C.cs.muAct k = C.cs.mu k) : actStar2 C Y ψk hv = C.actStar Y ψk hv := by
  unfold actStar2 SFCtx.actStar sfActMass2 sfActMass
  rw [h]

/-- Under `D1Corr`, on the branch domain, the second-version `ℰ^{(j)}` is the landed one. -/
theorem EresJ2_eq {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ m₁ k N}
    (h : D1Corr C.m₀ C.sf St hv vc) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hbr : ∀ x, dot (C.psiJ Y ψk hv j x) (C.psiJ Y ψk hv j x) ∈ Complex.slitPlane) :
    EresJ2 C vc Y ψk hv j = C.EresJ Y ψk hv j := by
  unfold EresJ2 SFCtx.EresJ
  congr 1
  exact (corr_sum_eq_p5 C h Y ψk hj1 hjk hbr).symm

/-- **The second-version small-field factor is the landed one when the masses agree and the
correction is P5 (1.8)'s** (the comparison theorem). -/
theorem sfFactor2_eq {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ m₁ k N}
    (h : D1Corr C.m₀ C.sf St hv vc) (hm : C.cs.muAct k = C.cs.mu k)
    (hbr : ∀ j, 1 ≤ j → j ≤ k → ∀ x,
      dot (C.psiJ Y ψk hv j x) (C.psiJ Y ψk hv j x) ∈ Complex.slitPlane) :
    sfFactor2 C vc Y ψk hv g = C.sfFactor Y ψk hv g := by
  have hE : EresK2 C vc Y ψk hv = C.EresK Y ψk hv := by
    unfold EresK2 SFCtx.EresK
    exact Finset.sum_congr rfl fun j hj =>
      EresJ2_eq C vc Y ψk hv h (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2
        (hbr j (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2)
  have hA : Ares2 C vc Y ψk hv = C.Ares Y ψk hv := by
    unfold Ares2 SFCtx.Ares
    rw [actStar2_eq C Y ψk hv hm, hE]
  unfold sfFactor2 SFCtx.sfFactor
  rw [hA]

end Restricted

/-! ### The form clause (D1) of the second version -/

section Form

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

/-- The integrand of (D1) for one history, second version: as `Def7.integrand` with `sfFactor2`. -/
noncomputable def integrand2 {ι : Type} [Fintype ι] (a : ι → LocalHistory S n M K)
    (Pk : ∀ i, OpPkg N R (a i) k) (car : ι → Set (Torus S.d (M * n K * S.L ^ K)))
    {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (rep : Rep S n R k0 K M N geo cs P k)
    (A : LabHist S n R k0 K) (Z : Set (Torus S.d (n k)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (x : GCfg a k Pk) : ℂ :=
  Complex.exp (rep.bdrySum A Z
      (MultiField.toC (gMulti a k Pk car (fineSet (S := S) (n := n) M K k (OmegaCube A.H k)) ψk x))
      (MultiField.toC (gFluct a k Pk car x)) (hC hv) g) *
    sfFactor2 C vc Zᶜ ψk hv g

/-- The term `𝕋_k(Z_k(𝔸), 𝔸)[e^{ℬ^{(k)}(𝔸)} χ_k(Z^c_k) exp(𝒜₂ + ℱ_k + ℛ^{(k)})(Z^c_k)]` of (D1),
second version, for the post-`R` class. -/
noncomputable def postTerm2 {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) : ℂ :=
  gOp (fun c : PostComp A k => A.H.localHistory M K k c.1) k
    (postOp geo cs rep.SD rep.KD A C.hkK) ψk hv g
    (integrand2 (fun c : PostComp A k => A.H.localHistory M K k c.1)
      (postOp geo cs rep.SD rep.KD A C.hkK)
      (fun c => fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k)))) C vc rep A
      (A.H.step k).Z ψk hv g)

/-- The integral of the post-`R` term converges absolutely, second version. -/
def PostConv2 {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) : Prop :=
  GConv (fun c : PostComp A k => A.H.localHistory M K k c.1) k
    (postOp geo cs rep.SD rep.KD A C.hkK) ψk hv g
    (integrand2 (fun c : PostComp A k => A.H.localHistory M K k c.1)
      (postOp geo cs rep.SD rep.KD A C.hkK)
      (fun c => fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k)))) C vc rep A
      (A.H.step k).Z ψk hv g)

/-- **(D1) Form, second version** (P5 H1, (1.1), (1.21); CLASS-RULINGS-2 items 1, 6; decision
"scheme A"): as `Def7.D1Form` with the small-field action of mass `sfActMass2 = cs.muAct` and the
P5 (1.8) correction `corrSum` of the coefficient data `vc`. -/
def D1Form2 {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (rep : Rep S n R k0 K M N geo cs P k) (hv : EuclideanSpace ℝ (Fin N))
    (ρ : (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) → (GIdx S n M K N → ℂ) → ℂ) : Prop :=
  ∀ (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ),
    g ∈ l1Ball (GIdx S n M K N) →
      (∀ A ∈ rep.hist, PostConv2 C vc rep A ψk hv g) ∧
        ρ ψk g = ∑ A ∈ rep.hist, postTerm2 C vc rep A ψk hv g

/-- The term of the pre-`R` form, second version. -/
noncomputable def preTerm2 {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) : ℂ :=
  gOp (fun c : A.H.Comp k => A.H.localHistory M K k c) k
    (preOpTop geo cs rep.SD rep.KD A k C.hkK) ψk hv g
    (integrand2 (fun c : A.H.Comp k => A.H.localHistory M K k c)
      (preOpTop geo cs rep.SD rep.KD A k C.hkK)
      (fun c => fineSet (S := S) (n := n) M K k (c.1 : Set (Torus S.d (n k)))) C vc rep A
      (A.H.F.Zpre k) ψk hv g)

/-- The integral of the pre-`R` term converges absolutely, second version. -/
def PreConv2 {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) : Prop :=
  GConv (fun c : A.H.Comp k => A.H.localHistory M K k c) k
    (preOpTop geo cs rep.SD rep.KD A k C.hkK) ψk hv g
    (integrand2 (fun c : A.H.Comp k => A.H.localHistory M K k c)
      (preOpTop geo cs rep.SD rep.KD A k C.hkK)
      (fun c => fineSet (S := S) (n := n) M K k (c.1 : Set (Torus S.d (n k)))) C vc rep A
      (A.H.F.Zpre k) ψk hv g)

/-- **(D1) for `IsRep^pre_k`, second version.** -/
def D1PreForm2 {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (rep : Rep S n R k0 K M N geo cs P k) (hv : EuclideanSpace ℝ (Fin N))
    (ρ : (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) → (GIdx S n M K N → ℂ) → ℂ) : Prop :=
  ∀ (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ),
    g ∈ l1Ball (GIdx S n M K N) →
      (∀ A ∈ rep.hist, PreConv2 C vc rep A ψk hv g) ∧
        ρ ψk g = ∑ A ∈ rep.hist, preTerm2 C vc rep A ψk hv g

end Form

end Balaban.LargeField.Def7v2
