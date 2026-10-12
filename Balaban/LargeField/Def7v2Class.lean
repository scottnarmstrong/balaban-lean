/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2Form
public import Balaban.LargeField.Def7v2Interface

/-!
# Def-7 v2, part 5: the class `IsRep2` -- DRAFT

**Draft, pending Roland's answer to Q13.**  The second version of Definition II.6.2 under the
decision "scheme A" (`orchestration/LEDGER.md`; W2-RESOLVE §4; CLASS-RULINGS-2 items 1, 2, 4, 6):

* (D1) `D1Form2` (`Def7v2Form`): small-field action of physical mass `sfActMass2 = cs.muAct`,
  correction `corrSum` of P5 (1.8) with the coefficient data `vc` (`corr : D1CorrLim`);
* (D2) `D2SF2`: the small-field data `𝔰` is a member of Def-6 v2 (`IsSFFamily2`) on the wide
  P1/P4 domain `xiFieldDom` (the `Regime` `(k₀, ν)` of the representation: complete small-field
  backgrounds, physical mass `ν_k L^{-2k}`), and the terms `ℛ^{(k)}_n` satisfy P5 H4 (`RTermsH4`,
  unchanged);
* (D7) `D7Bdry2`: the boundary terms are analytic and bounded at the external fields `hSetB2`
  (the pinned ball of radius `rH` around the physical field);
* (D9): `D9Coeff` is unchanged: the coefficient clauses of `IsSFFamily2` (`CoeffBounds` for the
  regime's `ν`) are those of Def-6, so (D9) (`β_k > B L^{k(d-2)}`, `0 < ν_k ≤ ν̄`, `k ≤ k₀`) is
  stated with the same `D9Coeff`;
* the clauses (D4)-(D6), (D8) and the field clauses (`cs.mu` the large-field solver mass, `0` for
  `k ≤ k₀`; `cs.muAct` the physical mass) are the landed ones.

`SFData.corr` is not read by any clause of the second version (the correction is `corrSum`); it is
an unused component of the landed structure.  **The SF-to-LF interface is not a field of
`IsRep2`** (its statement is being revised: `notes/phase1/INTERFACE-A.md`, `WALL-COLLAR.md`): it is
the separate predicate `IsRep2WithInterface`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Def7v2

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.LargeField.Def7
  RegionHistory Filter Topology

/-! ### (D2) of the second version -/

section SF

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The wide small-field field domain of a representation** (CLASS-RULINGS-2 item 4; W2-RESOLVE
§4): `Ξ^c_j(𝔹; 1, ε_j)` with the kernel sequence `a_k` and the complete small-field background
mass `sfBgMass` of the regime `(k₀, ν)`. -/
noncomputable def sfDom (P6 : Def6.Consts) (k0 : ℕ) (sf : SFData d L m₁ k N ϱ) :
    ∀ (N₁ : ℕ) [NeZero N₁], FieldDom d L N₁ m₁ k N ϱ :=
  fun _ _ => xiFieldDom (aIdeal L k (sf.a k)) ((⟨k0, sf.ν⟩ : Regime L).sfBgMass k) (P6.eps d L)

/-- **(D2) Small-field data, second version** (LFR (D2) [F-1]; CLASS-RULINGS-2 items 1, 2, 4):
`𝔰` is a member of Def-6 v2 (`IsSFFamily2`) for the regime `(k₀, ν)` on the wide domain
`sfDom`, and the `ℛ^{(k)}_n` satisfy P5 H4 on every Def-6 torus (`RTermsH4`, unchanged). -/
structure D2SF2 (P6 : Def6.Consts) (k0 : ℕ) (sf : SFData d L m₁ k N ϱ) (fac : ℕ → ℝ) : Prop where
  sfClass : ∃ ρsf : ∀ (N₁ : ℕ) [NeZero N₁], (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) →
      (Fin N → ℝ) → (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ,
    IsSFFamily2 P6 (⟨k0, sf.ν⟩ : Regime L) sf.β sf.a (sfDom P6 k0 sf) sf.Tm ρsf sf.E
  rTerms : ∀ (N₁ : ℕ) [NeZero N₁], RTermsH4 (ϱ := ϱ) P6 sf.β sf.ν sf.a N₁ (sf.Rt N₁) fac

/-- **(D2♭), second version** (§II.6.3 (iii)): as `D2SF2` with the mass range `0 < ν_k ≤ 1`
(`SFFlat` with `IsSF2` on the wide domain). -/
structure SFFlat2 (P6 : Def6.Consts) (k0 : ℕ) (sf : SFData d L m₁ k N ϱ) : Prop where
  admissible : P6.Admissible d L
  coeff : Def6.CoeffBounds d L k (massOne P6) sf.β sf.ν sf.a
  torus : ∃ ρsf : ∀ (N₁ : ℕ) [NeZero N₁], (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) →
      (Fin N → ℝ) → (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ,
    ∀ (N₁ : ℕ) [NeZero N₁], IsSF2 P6 (⟨k0, sf.ν⟩ : Regime L) sf.β sf.a (sfDom P6 k0 sf N₁)
      (sf.Tm N₁) (ρsf N₁) (sf.E N₁)
  torusIndep : Def6.TorusIndep P6.m₀ sf.Tm
  renorm : ∀ j, 1 ≤ j → j ≤ k → Def6.RenormCond (d := d) (L := L) (m₁ := m₁) (N := N)
    (ϱ := ϱ) P6.m₀ k (sf.ν k) sf.Tm j
  rTerms : ∀ (N₁ : ℕ) [NeZero N₁], RTermsH4 (ϱ := ϱ) P6 sf.β sf.ν sf.a N₁ (sf.Rt N₁) (fun _ => 1)

end SF

/-! ### (D7) of the second version -/

section Bdry

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

/-- **(D7) Boundary terms, second version** (P5 H7, (1.38)-(1.39); CLASS-RULINGS-2 item 4): as
`Def7.D7Bdry`, with the external fields of the analyticity and bound clauses the pinned ball
`hSetB2 hv rH` around the physical field instead of the point `hSetB hv`. -/
structure D7Bdry2 (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hkK : k ≤ K)
    (rep : Rep S n R k0 K M N geo cs P k) (Zof : LabHist S n R k0 K → Set (Torus S.d (n k)))
    (aw μs ε ε1 νs : ℕ → ℝ) (fac rate : ℝ) (hv : EuclideanSpace ℝ (Fin N)) (rH : ℝ) : Prop where
  loc_field : ∀ A ∈ rep.hist, ∀ X ∈ bdryDoms (OmegaCube A.H k) (Zof A),
    ∀ (ψ₁ ψ₂ ψ'₁ ψ'₂ : MultiFieldC S n M K N) (h : Fin N → ℂ) (g₁ g₂ : GIdx S n M K N → ℂ),
      (∀ j, j ≤ K → ∀ y : BlockAt S n M K j,
        BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) →
          ψ₁ j y = ψ₂ j y ∧ ψ'₁ j y = ψ'₂ j y) →
      (∀ x i, x ∈ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) →
        g₁ (x, i) = g₂ (x, i)) →
      rep.B A X ψ₁ ψ'₁ h g₁ = rep.B A X ψ₂ ψ'₂ h g₂
  loc_hist : ∀ A ∈ rep.hist, ∀ A' ∈ rep.hist, ∀ X : Finset (Torus S.d (n k)),
    X ∈ bdryDoms (OmegaCube A.H k) (Zof A) → X ∈ bdryDoms (OmegaCube A'.H k) (Zof A') →
    (∀ j, j ≤ k →
      fineSet (S := S) (n := n) M K j (OmegaCube A.H j) ∩
          fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) =
        fineSet (S := S) (n := n) M K j (OmegaCube A'.H j) ∩
          fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ∧
      (globalLH A.H M).OmegaDD j ∩ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) =
        (globalLH A'.H M).OmegaDD j ∩
          fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ∧
      (globalLH A.H M).Z j ∩ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) =
        (globalLH A'.H M).Z j ∩ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) →
    (∀ c : PostComp A k, (c.1.1 ∩ X).Nonempty → ∃ c' : PostComp A' k, c'.1.1 = c.1.1 ∧
      A'.H.localHistory M K k c'.1 = A.H.localHistory M K k c.1) →
    (∀ c' : PostComp A' k, (c'.1.1 ∩ X).Nonempty → ∃ c : PostComp A k, c.1.1 = c'.1.1) →
    ∀ ψ ψ' h g, rep.B A X ψ ψ' h g = rep.B A' X ψ ψ' h g
  real : ∀ A ∈ rep.hist, ∀ X ∈ bdryDoms (OmegaCube A.H k) (Zof A),
    ∀ (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      (∀ j y i, (ψ j y i).im = 0 ∧ (ψ' j y i).im = 0) → (∀ i, (h i).im = 0) →
      (∀ p, (g p).im = 0) → (rep.B A X ψ ψ' h g).im = 0
  analytic : ∀ A ∈ rep.hist, ∀ X ∈ bdryDoms (OmegaCube A.H k) (Zof A), ∀ h ∈ hSetB2 hv rH,
    AnalyticOnNhd ℂ
      (fun p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ) =>
        rep.B A X (extK p.1) (extK p.2.1) h p.2.2)
      {p | H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) k hkK
        (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i))}
  bound : ∀ A ∈ rep.hist, ∀ X ∈ bdryDoms (OmegaCube A.H k) (Zof A), ∀ h ∈ hSetB2 hv rH,
    ∀ p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ),
      H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) k hkK
        (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i)) →
      ‖rep.B A X (extK p.1) (extK p.2.1) h p.2.2‖ <
        fac * Real.exp (-rate * (dCovMod S.L (OmegaCube A.H k) X).toReal)
  rot : ∀ A ∈ rep.hist, ∀ X ∈ bdryDoms (OmegaCube A.H k) (Zof A), ∀ (ρ : OrthN N)
    (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      rep.B A X (rotM ρ ψ) (rotM ρ ψ') (rotC ρ h) (rotG ρ g) = rep.B A X ψ ψ' h g
  euclid : ∀ A ∈ rep.hist, ∀ A' ∈ rep.hist, ∀ σ : LatTorusSym S n M K, RegionIso σ A.H A'.H →
    (∀ j (c : Finset (Torus S.d (n j))), A'.keptLab j (c.map (σ.ec j).toEmbedding) =
      A.keptLab j c) →
    ∀ X ∈ bdryDoms (OmegaCube A.H k) (Zof A), ∀ (ψ ψ' : MultiFieldC S n M K N)
      (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      rep.B A' (X.map (σ.ec k).toEmbedding) (symM σ ψ) (symM σ ψ') h (symG σ g) =
        rep.B A X ψ ψ' h g


/-- The second version of (D7) contains the landed one, for a positive radius (the physical field
lies in the ball). -/
theorem D7Bdry2.toD7Bdry {hnn : ∀ i, i < K → n i = S.L * n (i + 1)} {hkK : k ≤ K}
    {rep : Rep S n R k0 K M N geo cs P k} {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))}
    {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ} {hv : EuclideanSpace ℝ (Fin N)} {rH : ℝ}
    (h : D7Bdry2 hnn hkK rep Zof aw μs ε ε1 νs fac rate hv rH) (hr : 0 < rH) :
    D7Bdry hnn hkK rep Zof aw μs ε ε1 νs fac rate hv where
  loc_field := h.loc_field
  loc_hist := h.loc_hist
  real := h.real
  analytic := fun A hA X hX h' hh => h.analytic A hA X hX h' ((hSetB_subset_hSetB2 hr).1 hh)
  bound := fun A hA X hX h' hh => h.bound A hA X hX h' ((hSetB_subset_hSetB2 hr).1 hh)
  rot := h.rot
  euclid := h.euclid

/-- **(D7) Boundary terms of the post-`R` class, second version** (P5 H7, (1.38)-(1.39);
CLASS-RULINGS-2 item 4): as `Def7.D7BdryPost` (the boundary domains `bdryDomsPost`, the fine
chosen-cover modular size `d7Size` at the post-`R` region, and the vanishing `support` off the
valid labels), with the external fields of the analyticity and bound clauses the pinned ball
`hSetB2 hv rH` around the physical field instead of the point `hSetB hv`. -/
structure D7Bdry2Post {m₀ m₁ : ℕ} (Fr : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hkK : k ≤ K)
    (rep : Rep S n R k0 K M N geo cs P k) (Zof : LabHist S n R k0 K → Set (Torus S.d (n k)))
    (aw μs ε ε1 νs : ℕ → ℝ) (fac rate : ℝ) (hv : EuclideanSpace ℝ (Fin N)) (rH : ℝ) : Prop where
  loc_field : ∀ A ∈ rep.hist, ∀ X ∈ bdryDomsPost Fr A k (Zof A),
    ∀ (ψ₁ ψ₂ ψ'₁ ψ'₂ : MultiFieldC S n M K N) (h : Fin N → ℂ) (g₁ g₂ : GIdx S n M K N → ℂ),
      (∀ j, j ≤ K → ∀ y : BlockAt S n M K j,
        BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) →
          ψ₁ j y = ψ₂ j y ∧ ψ'₁ j y = ψ'₂ j y) →
      (∀ x i, x ∈ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) →
        g₁ (x, i) = g₂ (x, i)) →
      rep.B A X ψ₁ ψ'₁ h g₁ = rep.B A X ψ₂ ψ'₂ h g₂
  loc_hist : ∀ A ∈ rep.hist, ∀ A' ∈ rep.hist, ∀ X : Finset (Torus S.d (n k)),
    X ∈ bdryDomsPost Fr A k (Zof A) → X ∈ bdryDomsPost Fr A' k (Zof A') →
    (∀ j, j ≤ k →
      fineSet (S := S) (n := n) M K j (OmegaCube A.H j) ∩
          fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) =
        fineSet (S := S) (n := n) M K j (OmegaCube A'.H j) ∩
          fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ∧
      (globalLH A.H M).OmegaDD j ∩ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) =
        (globalLH A'.H M).OmegaDD j ∩
          fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ∧
      (globalLH A.H M).Z j ∩ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) =
        (globalLH A'.H M).Z j ∩ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) →
    (∀ c : PostComp A k, (c.1.1 ∩ X).Nonempty → ∃ c' : PostComp A' k, c'.1.1 = c.1.1 ∧
      A'.H.localHistory M K k c'.1 = A.H.localHistory M K k c.1) →
    (∀ c' : PostComp A' k, (c'.1.1 ∩ X).Nonempty → ∃ c : PostComp A k, c.1.1 = c'.1.1) →
    ∀ ψ ψ' h g, rep.B A X ψ ψ' h g = rep.B A' X ψ ψ' h g
  real : ∀ A ∈ rep.hist, ∀ X ∈ bdryDomsPost Fr A k (Zof A),
    ∀ (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      (∀ j y i, (ψ j y i).im = 0 ∧ (ψ' j y i).im = 0) → (∀ i, (h i).im = 0) →
      (∀ p, (g p).im = 0) → (rep.B A X ψ ψ' h g).im = 0
  analytic : ∀ A ∈ rep.hist, ∀ X ∈ bdryDomsPost Fr A k (Zof A), ∀ h ∈ hSetB2 hv rH,
    AnalyticOnNhd ℂ
      (fun p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ) =>
        rep.B A X (extK p.1) (extK p.2.1) h p.2.2)
      {p | H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) k hkK
        (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i))}
  bound : ∀ A ∈ rep.hist, ∀ X ∈ bdryDomsPost Fr A k (Zof A), ∀ h ∈ hSetB2 hv rH,
    ∀ p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ),
      H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) k hkK
        (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i)) →
      ‖rep.B A X (extK p.1) (extK p.2.1) h p.2.2‖ <
        fac * Real.exp (-rate * d7Size Fr A k X)
  rot : ∀ A ∈ rep.hist, ∀ X ∈ bdryDomsPost Fr A k (Zof A), ∀ (ρ : OrthN N)
    (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      rep.B A X (rotM ρ ψ) (rotM ρ ψ') (rotC ρ h) (rotG ρ g) = rep.B A X ψ ψ' h g
  euclid : ∀ A ∈ rep.hist, ∀ A' ∈ rep.hist, ∀ σ : LatTorusSym S n M K, RegionIso σ A.H A'.H →
    (∀ j (c : Finset (Torus S.d (n j))), A'.keptLab j (c.map (σ.ec j).toEmbedding) =
      A.keptLab j c) →
    ∀ X ∈ bdryDomsPost Fr A k (Zof A), ∀ (ψ ψ' : MultiFieldC S n M K N)
      (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      rep.B A' (X.map (σ.ec k).toEmbedding) (symM σ ψ) (symM σ ψ') h (symG σ g) =
        rep.B A X ψ ψ' h g
  support : ∀ A ∈ rep.hist, ∀ X ∈ bdryDoms (A.H.omegaPost k) (Zof A), ¬ FineValid Fr A k X →
    ∀ (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      rep.B A X ψ ψ' h g = 0

/-- The second version of (D7) of the post-`R` class contains `Def7.D7BdryPost`, for a positive
radius (the physical field lies in the ball). -/
theorem D7Bdry2Post.toD7BdryPost {m₀ m₁ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁}
    {hnn : ∀ i, i < K → n i = S.L * n (i + 1)} {hkK : k ≤ K}
    {rep : Rep S n R k0 K M N geo cs P k} {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))}
    {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ} {hv : EuclideanSpace ℝ (Fin N)} {rH : ℝ}
    (h : D7Bdry2Post Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv rH) (hr : 0 < rH) :
    D7BdryPost Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv where
  loc_field := h.loc_field
  loc_hist := h.loc_hist
  real := h.real
  analytic := fun A hA X hX h' hh => h.analytic A hA X hX h' ((hSetB_subset_hSetB2 hr).1 hh)
  bound := fun A hA X hX h' hh => h.bound A hA X hX h' ((hSetB_subset_hSetB2 hr).1 hh)
  rot := h.rot
  euclid := h.euclid
  support := h.support

end Bdry

/-! ### The class -/

section Rep

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {P6 : Def6.Consts} {C7 : Consts7} {k : ℕ} {ϱ : ℝ}

/-- **Definition II.6.2 (Def-7), second version: `IsRep2_k(𝖼, rep, ρ)`** (decision "scheme A").
As `Def7.IsRep` (whose parameters it has, with the radius `rH` of the pinned field ball and the
coefficient data `St`, `vc` of P5 (1.8) added) except: `form` is `D1Form2`, `sfData` is `D2SF2`
(`IsSFFamily2` on the wide domain), `bdry` is `D7Bdry2` (external fields `hSetB2`), and `corr`
(`D1CorrLim`) defines the coefficient data.  `coeff` is `D9Coeff`: the coefficient clauses of
`IsSFFamily2` are those of Def-6.  The SF-to-LF interface is *not* a field
(`IsRep2WithInterface`). -/
structure IsRep2 (S : Setting) (R : ℕ → ℝ) (k0 K M : ℕ) [NeZero M] [NeZero S.L] (N : ℕ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M) (cs : OpConsts)
    (P : BudgetConsts) (P6 : Def6.Consts) (C7 : Consts7) (β ν : ℝ)
    (hv : EuclideanSpace ℝ (Fin N)) (rH : ℝ) (k : ℕ) {ϱ : ℝ}
    (hM6 : M = S.L ^ (P6.m₀ + C7.m₁)) (hkK : k ≤ K)
    (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ)
    (ρ : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) →
      (GIdx S (sides S.L K nK) M K N → ℂ) → ℂ)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ C7.m₁ k N) (vc : CorrCoef S.d) :
    Prop where
  coh : Coh S R k0 M cs P P6 C7 β ν k F.sf
  field : FieldClauses S k0 k cs F.sf hv
  complete : ∀ (nK : ℕ) [NeZero nK], IsComplete k (k + 1) (F.lf nK).hist
  form : ∀ (nK : ℕ) [NeZero nK], D1Form2 (F.ctx hM6 hkK nK) vc (F.lf nK) hv (ρ nK)
  corr : D1CorrLim P6.m₀ F.sf St hv vc
  sfData : D2SF2 P6 k0 F.sf (fun _ => 1)
  pin : ∀ (nK : ℕ) [NeZero nK], D4Pin (k + 1) (F.lf nK)
  opBound : ∀ (nK : ℕ) [NeZero nK], D5Bound (k + 1) hkK (F.lf nK)
  budget : ∀ (nK : ℕ) [NeZero nK], D6Budget (F.lf nK)
  bdry : ∀ (nK : ℕ) [NeZero nK], D7Bdry2 (sides_hnn S.L K nK) hkK (F.lf nK)
    (fun A => (A.H.step k).Z) F.weights cs.mu (P6.eps S.d S.L) (epsOne S P6 C7) cs.nu C7.B0 P6.κ
    hv rH
  coherent : D8SF P6.m₀ F.sf
  coeff : D9Coeff P6 k0 F.sf

/-- **The class `𝓡2_k(𝖼)`**: the density families that have a second-version representation
(for some coefficient data). -/
def RepClass2 (S : Setting) (R : ℕ → ℝ) (k0 K M : ℕ) [NeZero M] [NeZero S.L] (N : ℕ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M) (cs : OpConsts)
    (P : BudgetConsts) (P6 : Def6.Consts) (C7 : Consts7) (β ν : ℝ)
    (hv : EuclideanSpace ℝ (Fin N)) (rH : ℝ) (k : ℕ) (ϱ : ℝ)
    (hM6 : M = S.L ^ (P6.m₀ + C7.m₁)) (hkK : k ≤ K) :
    Set (∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) →
      (GIdx S (sides S.L K nK) M K N → ℂ) → ℂ) :=
  {ρ | ∃ (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ)
      (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ C7.m₁ k N) (vc : CorrCoef S.d),
    IsRep2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc}

/-- **`IsRep2` together with the SF-to-LF interface** (W2-RESOLVE §3; kept separate while the
interface statement is revised, `notes/phase1/INTERFACE-A.md`, `WALL-COLLAR.md`): `IsRep2` and,
on every Def-6 torus, kernel data `SFtoLFData` satisfying `SFtoLFInterface` for the regime
`(k₀, ν)` of the representation. -/
structure IsRep2WithInterface (S : Setting) (R : ℕ → ℝ) (k0 K M : ℕ) [NeZero M] [NeZero S.L]
    (N : ℕ) (geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M) (cs : OpConsts)
    (P : BudgetConsts) (P6 : Def6.Consts) (C7 : Consts7) (β ν : ℝ)
    (hv : EuclideanSpace ℝ (Fin N)) (rH : ℝ) (k : ℕ) {ϱ : ℝ}
    (hM6 : M = S.L ^ (P6.m₀ + C7.m₁)) (hkK : k ≤ K)
    (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ)
    (ρ : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) →
      (GIdx S (sides S.L K nK) M K N → ℂ) → ℂ)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ C7.m₁ k N) (vc : CorrCoef S.d)
    (c : IfConsts) : Prop where
  rep : IsRep2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc
  iface : ∀ (N₁ : ℕ) [NeZero N₁], ∃ X : SFtoLFData S.d S.L N₁ C7.m₁ k N ϱ,
    SFtoLFInterface P6 (⟨k0, F.sf.ν⟩ : Regime S.L) F.sf.β F.sf.a (F.sf.Tm N₁) X c

end Rep

end Balaban.LargeField.Def7v2
