/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldHS2Pre
public import Balaban.Spine.LFOldBD7
public import Balaban.Spine.LFBdryClauses

/-!
# The (D7) clauses of the old part in the form of the step (blocker 3, closing ladder target (0))

The old part of the step's boundary terms is the re-expanded old part of reading HS-2 (`oldBOfAt` at
`glob = true`, `σ = stencilX`) in the form the step uses (`oldStepB`): the unit points `inner 𝔸`, the cube
assignment `cb 𝔸` and the interaction family `IF 𝔸` do not depend on the fields (finding (iii) of
`notes/phase1/PLAN-B.md`, W1154c), the interaction is the member `IF 𝔸 at (ψ, ψ', h, g)` of the family,
and the external field of the datum and the physical field of the record's terms are the real part of
the argument `h` (`reExt`, `reExtE`; finding (i): at `h ∈ hSetB hv` they are `hv`, ruling R16).  The record
`rep` is the record whose terms are re-expanded; at the step it is the record of scale `k` re-indexed by
the histories of the successor (ladder item 6).

This file proves, for a record of scale `k + 1` whose boundary terms are `oldStepB …`, the clauses of
(D7) (`D7Clause.Holds`) that follow from the landed results on `oldBAtAt` (`Spine/LFOldBD7.lean`):

* `oldStepB_support` (clause `support`): unconditional;
* `oldStepB_locField` (clause `loc_field`): from the record's `loc_field`, the locality of the
  interaction family and of the fixed values.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background
  Balaban.Polymer

namespace Balaban.RootFSpine

/-- The real part of a complex external field. -/
def reExt {N : ℕ} (h : Fin N → ℂ) : Fin N → ℝ := fun i => (h i).re

/-- The real part of a complex external field, as a vector of `ℝ^N`. -/
noncomputable def reExtE {N : ℕ} (h : Fin N → ℂ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (reExt h)

theorem reExt_hC {N : ℕ} (hv : EuclideanSpace ℝ (Fin N)) (i : Fin N) : reExt (hC hv) i = hv i := by
  simp [reExt, hC]

theorem reExtE_hC {N : ℕ} (hv : EuclideanSpace ℝ (Fin N)) : reExtE (hC hv) = hv := by
  ext i
  simp [reExtE, reExt, hC]

/-- The arguments `(ψ, ψ', h, g)` of a boundary term: the parameter of the interaction family of the
old part. -/
abbrev OldPrm (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (M K N : ℕ) [NeZero M] [NeZero S.L] :
    Type :=
  MultiFieldC S n M K N × MultiFieldC S n M K N × (Fin N → ℂ) × (GIdx S n M K N → ℂ)

section Step

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **The re-expanded old boundary terms in the form of the step** (P5 (2.48), (3.2); P6 (4.32)–(4.34);
reading HS-2): `oldBOfAt` at the restricted global datum (`glob = true`) and the local sets `V₂(X, J)`
(`σ = stencilX`), with field-independent unit points `inner 𝔸 ⊆ unitPts G'`, cube assignment `cb 𝔸`
and interaction family `IF 𝔸` (the interaction at the arguments `(ψ, ψ', h, g)` is `IF 𝔸 at (ψ, ψ', h, g)`),
the fixed values `ψout 𝔸 ψ h`, and the external fields `Re h`. -/
noncomputable def oldStepB {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z a₁ ν β p₁ δ : ℝ)
    (inner : ∀ A : LabHist S n R k0 K, Finset (unitPts (stepG' g hnn hM1 A.H hk hρ)))
    (cb : ∀ A : LabHist S n R k0 K, inner A →
      CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
        (d7Pull F (k + 1) (OmegaCube A.H (k + 1))))
    (hp : 0 < p₁)
    (IF : ∀ A : LabHist S n R k0 K,
      LocIntFam (fun b => {u : inner A // cb A u = b} → Rn N) (OldPrm S n M K N))
    (ψout : ∀ A : LabHist S n R k0 K, MultiFieldC S n M K N → (Fin N → ℂ) →
      unitPts (stepG' g hnn hM1 A.H hk hρ) → Fin N → ℂ)
    (rψ ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) : BTerms S n R k0 K M N (k + 1) :=
  oldBOfAt g hnn hM1 true F stencilX hk hk1 hρ z reExt a₁ ν β p₁ δ (fun A _ _ => inner A)
    (fun A _ _ => cb A) hp (fun A ψ ψ' h gx => (IF A).at (ψ, ψ', h, gx)) (fun A ψ h => ψout A ψ h) rψ
    ρc ρ r r' rep reExtE

/-- **The clause `support` of (D7) for the old part in the form of the core `oldBOfAt`**: a record of
scale `k + 1` whose boundary terms are `oldBOfAt …` (any readings and parameters) vanishes at the labels
that are not valid (`oldBAtAt_eq_zero_of_not_valid`). -/
theorem oldBOfAt_support (glob : Bool) {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ}
    (σ : Finset (Torus S.d (n k)) → Finset (Torus S.d (n k))) (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : (Fin N → ℂ) → Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ)
    (inner : ∀ (A : LabHist S n R k0 K) (ψ : MultiFieldC S n M K N) (h : Fin N → ℂ),
      Finset (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z (h₀ h) a₁ ν β p₁ δ).U)
    (cb : ∀ (A : LabHist S n R k0 K) (ψ : MultiFieldC S n M K N) (h : Fin N → ℂ), inner A ψ h →
      CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
        (d7Pull F (k + 1) (OmegaCube A.H (k + 1))))
    (hp : 0 < p₁)
    (I : ∀ (A : LabHist S n R k0 K) (ψ _ : MultiFieldC S n M K N) (h : Fin N → ℂ)
      (_ : GIdx S n M K N → ℂ), LocInteraction (fun b => {u : inner A ψ h // cb A ψ h u = b} → Rn N))
    (ψout : ∀ (A : LabHist S n R k0 K) (ψ : MultiFieldC S n M K N) (h : Fin N → ℂ),
      (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z (h₀ h) a₁ ν β p₁ δ).U → Fin N → ℂ) (rψ : ℝ)
    (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (hv : (Fin N → ℂ) → EuclideanSpace ℝ (Fin N))
    {cs' : OpConsts} {P' : BudgetConsts} (rep' : Rep S n R k0 K M N g cs' P' (k + 1))
    (hB : rep'.B = oldBOfAt g hnn hM1 glob F σ hk hk1 hρ z h₀ a₁ ν β p₁ δ inner cb hp I ψout rψ ρc ρ
      r r' rep hv)
    (Zof : LabHist S n R k0 K → Set (Torus S.d (n (k + 1)))) (aw μs ε ε1 νs : ℕ → ℝ) (fac rate : ℝ)
    (hv' : EuclideanSpace ℝ (Fin N)) :
    D7Clause.support.Holds F hnn hk rep' Zof aw μs ε ε1 νs fac rate hv' := by
  intro A _ X _ hX ψ ψ' h gx
  rw [hB]
  exact oldBAtAt_eq_zero_of_not_valid g hnn hM1 glob F A.H σ hk hk1 hρ ψ z (h₀ h) a₁ ν β p₁ δ
    (inner A ψ h) (cb A ψ h) hp (I A ψ ψ' h gx) (ψout A ψ h) rψ ρc ρ r r' rep A (oldDoms F A.H k) ψ'
    (hv h) gx X hX

/-- **The clause `support` of (D7) for the old part in the form of the step.** -/
theorem oldStepB_support {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z a₁ ν β p₁ δ : ℝ)
    (inner : ∀ A : LabHist S n R k0 K, Finset (unitPts (stepG' g hnn hM1 A.H hk hρ)))
    (cb : ∀ A : LabHist S n R k0 K, inner A →
      CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
        (d7Pull F (k + 1) (OmegaCube A.H (k + 1))))
    (hp : 0 < p₁)
    (IF : ∀ A : LabHist S n R k0 K,
      LocIntFam (fun b => {u : inner A // cb A u = b} → Rn N) (OldPrm S n M K N))
    (ψout : ∀ A : LabHist S n R k0 K, MultiFieldC S n M K N → (Fin N → ℂ) →
      unitPts (stepG' g hnn hM1 A.H hk hρ) → Fin N → ℂ)
    (rψ ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k)
    {cs' : OpConsts} {P' : BudgetConsts} (rep' : Rep S n R k0 K M N g cs' P' (k + 1))
    (hB : rep'.B = oldStepB g hnn hM1 F hk hk1 hρ z a₁ ν β p₁ δ inner cb hp IF ψout rψ ρc ρ r r' rep)
    (Zof : LabHist S n R k0 K → Set (Torus S.d (n (k + 1)))) (aw μs ε ε1 νs : ℕ → ℝ) (fac rate : ℝ)
    (hv' : EuclideanSpace ℝ (Fin N)) :
    D7Clause.support.Holds F hnn hk rep' Zof aw μs ε ε1 νs fac rate hv' :=
  oldBOfAt_support g hnn hM1 true F stencilX hk hk1 hρ z reExt a₁ ν β p₁ δ _ _ hp _ _ rψ ρc ρ r r' rep
    reExtE rep' hB Zof aw μs ε ε1 νs fac rate hv'

omit [NeZero M] [NeZero S.L] in
/-- The old labels of a region history are boundary domains of the post-`R` class at the regions
`Z_k` of the step (`oldDoms` is a filter of `bdryDomsAt` at `Ω_k^post`, `Z_k`). -/
theorem mem_bdryDomsPost_of_mem_oldDoms {m₀ : ℕ} {F : FineSizeFrame S n M K m₀ m₁}
    {A : LabHist S n R k0 K} {k : ℕ} {X : Finset (Torus S.d (n k))} (hX : X ∈ oldDoms F A.H k) :
    X ∈ bdryDomsPost F A k (A.H.step k).Z := by
  classical
  unfold oldDoms at hX
  unfold bdryDomsPost
  exact (Finset.mem_filter.1 hX).1

/-- **The clause `loc_field` of (D7) for the old part in the form of the step** (`oldBAtAt_congr_fields`):
for a record of scale `k + 1` whose boundary terms are `oldStepB …` re-expanding the terms of `rep`, whose
histories are histories of `rep` (`hhist`), if the record `rep` satisfies (D7) of the post-`R` class at
the regions `Z_k` of the step, the activities of the interaction family at two arguments agreeing on the
fine set of `Y` agree on the labels inside `Y` (`hIF`), and the fixed values at two fields agreeing on
the fine set of `Y` agree at the unit points inside `Y` (`hout`), then the old part depends only on the
arguments on the fine set of `Y`.  The cube assignment puts every unit point in the box of its cube
(`hcb`). -/
theorem oldStepB_locField {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z a₁ ν β p₁ δ : ℝ)
    (inner : ∀ A : LabHist S n R k0 K, Finset (unitPts (stepG' g hnn hM1 A.H hk hρ)))
    (cb : ∀ A : LabHist S n R k0 K, inner A →
      CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
        (d7Pull F (k + 1) (OmegaCube A.H (k + 1))))
    (hcb : ∀ (A : LabHist S n R k0 K) (u : inner A), toFrame g hnn hM1 F hk (unitRep
      (u : unitPts (stepG' g hnn hM1 A.H hk hρ))) ∈
        Localization.box (cb A u).1 (cellSide S.L m₀ m₁ (k + 1)))
    (hp : 0 < p₁)
    (IF : ∀ A : LabHist S n R k0 K,
      LocIntFam (fun b => {u : inner A // cb A u = b} → Rn N) (OldPrm S n M K N))
    (ψout : ∀ A : LabHist S n R k0 K, MultiFieldC S n M K N → (Fin N → ℂ) →
      unitPts (stepG' g hnn hM1 A.H hk hρ) → Fin N → ℂ)
    (rψ ρc : ℝ) (ρ r r' : ℕ) {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N g cs P k) {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ}
    {hv : EuclideanSpace ℝ (Fin N)}
    (hrec : D7BdryPost F hnn (Nat.le_of_succ_le hk) rep (fun A => (A.H.step k).Z) aw μs ε ε1 νs fac
      rate hv)
    {cs' : OpConsts} {P' : BudgetConsts} (rep' : Rep S n R k0 K M N g cs' P' (k + 1))
    (hhist : ∀ A ∈ rep'.hist, A ∈ rep.hist)
    (hB : rep'.B = oldStepB g hnn hM1 F hk hk1 hρ z a₁ ν β p₁ δ inner cb hp IF ψout rψ ρc ρ r r' rep)
    (hIF : ∀ (A : LabHist S n R k0 K) (Y : Finset (Torus S.d (n (k + 1)))) (q₁ q₂ : OldPrm S n M K N),
      (∀ j, j ≤ K → ∀ y : BlockAt S n M K j, BlockSub (S := S) (n := n) (M := M) (K := K) j y
        (fineSet (S := S) (n := n) M K (k + 1) (Y : Set (Torus S.d (n (k + 1))))) →
        q₁.1 j y = q₂.1 j y ∧ q₁.2.1 j y = q₂.2.1 j y) →
      q₁.2.2.1 = q₂.2.2.1 →
      (∀ x i, x ∈ fineSet (S := S) (n := n) M K (k + 1) (Y : Set (Torus S.d (n (k + 1)))) →
        q₁.2.2.2 (x, i) = q₂.2.2.2 (x, i)) →
      ∀ (u : ℂ) (y : (IF A).Lb),
        (IF A).Lab.ysite y ⊆ d7Pull F (k + 1) (Y : Set (Torus S.d (n (k + 1)))) →
        ((IF A).A q₁ u).H y = ((IF A).A q₂ u).H y)
    (hout : ∀ (A : LabHist S n R k0 K) (Y : Finset (Torus S.d (n (k + 1))))
      (ψ₁ ψ₂ : MultiFieldC S n M K N) (h : Fin N → ℂ),
      (∀ j, j ≤ K → ∀ y : BlockAt S n M K j, BlockSub (S := S) (n := n) (M := M) (K := K) j y
        (fineSet (S := S) (n := n) M K (k + 1) (Y : Set (Torus S.d (n (k + 1))))) →
        ψ₁ j y = ψ₂ j y) →
      ∀ b, toFrame g hnn hM1 F hk (unitRep b) ∈ d7Pull F (k + 1) (Y : Set (Torus S.d (n (k + 1)))) →
        ψout A ψ₁ h b = ψout A ψ₂ h b)
    (Zof : LabHist S n R k0 K → Set (Torus S.d (n (k + 1)))) (aw' μs' ε' ε1' νs' : ℕ → ℝ)
    (fac' rate' : ℝ) (hv' : EuclideanSpace ℝ (Fin N)) :
    D7Clause.locField.Holds F hnn hk rep' Zof aw' μs' ε' ε1' νs' fac' rate' hv' := by
  intro A hA Y _ ψ₁ ψ₂ ψ'₁ ψ'₂ h g₁ g₂ hψ hg
  rw [hB]
  exact oldBAtAt_congr_fields_core g hnn hM1 true stencilX hk hrec (hhist A hA) hk1 hρ z (reExt h) a₁ ν
    β p₁ δ (fun X hX => ⟨mem_bdryDomsPost_of_mem_oldDoms hX, hX⟩) (hv := reExtE h) (ψ₁ := ψ₁) (inner A)
    (cb A) (hcb A) hp (IF A) (ψ₁, ψ'₁, h, g₁) (ψ₂, ψ'₂, h, g₂) Y
    (hIF A Y _ _ (fun j hj y hy => hψ j hj y hy) rfl hg)
    (ψout A ψ₁ h) (ψout A ψ₂ h) (hout A Y ψ₁ ψ₂ h fun j hj y hy => (hψ j hj y hy).1) rψ ρc ρ r r' ψ₂
    ψ'₁ ψ'₂ g₁ g₂ (fun j hj y hy => (hψ j hj y hy).1) (fun j hj y hy => (hψ j hj y hy).2) hg

end Step

end Balaban.RootFSpine
