/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFBdryOldAssembly

/-!
# The clauses of (D7) one by one, and the old part of the step's boundary terms clause by clause

`LFBdryPart … Φ Λ B' fac` asks (D7) of the pre-`R` class of scale `k + 1` (`Def7.D7Bdry`) for a family
`B'` of boundary terms of the step.  For the closing ladder of blocker 3 the eight clauses of (D7) have
different sources (`notes/phase1/PLAN-B.md`, "Blocker 3, closing ladder"), so they are named here one by
one.

* `D7Clause`: the eight clauses of (D7) (`locField`, `locHist`, `real`, `analytic`, `bound`, `rot`,
  `euclid`, `support`), and `D7Clause.Holds`: the statement of a clause for a record, each the
  statement of the field of `Def7.D7Bdry` of the same name;
* `d7Bdry_of_clauses`, `D7Bdry.clause`: (D7) is the conjunction of its clauses;
* `LFBdryClause … Λ B' fac c`: the clause `c` of (D7) for the family `B'` at the step (the form of
  `LFBdryPart`, one clause); `lfBdryPart_of_clauses`: `LFBdryPart` from its eight clauses;
* `lfBdryOldInput_of_clauses`: **`LFBdryOldInput Λ Sb Bo` from the identity `OldPartEq Λ Sb O` and the
  eight clauses of (D7) for `O`** (the assembly `lfBdryOldInput_of_old_eq` with its gap
  `LFBdryPart … O Bo` split into the clauses).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.Multiscale RegionHistory

namespace Balaban.RootFSpine

/-- **The clauses of (D7)** (P5 H7, (1.38)–(1.39); P5 H5; the fields of `Def7.D7Bdry`). -/
inductive D7Clause where
  /-- locality in the fields -/
  | locField
  /-- locality in the history -/
  | locHist
  /-- reality -/
  | real
  /-- analyticity on the H7 domain -/
  | analytic
  /-- the bound on the H7 domain -/
  | bound
  /-- `O(N)`-covariance -/
  | rot
  /-- invariance under the lattice symmetries -/
  | euclid
  /-- vanishing off the valid labels -/
  | support

/-- The largest of eight reals indexed by the clauses of (D7). -/
noncomputable def D7Clause.maxOf (b : D7Clause → ℝ) : ℝ :=
  max (max (max (b .locField) (b .locHist)) (max (b .real) (b .analytic)))
    (max (max (b .bound) (b .rot)) (max (b .euclid) (b .support)))

theorem D7Clause.le_maxOf (b : D7Clause → ℝ) (cl : D7Clause) : b cl ≤ D7Clause.maxOf b := by
  unfold D7Clause.maxOf
  cases cl <;> simp

section Clauses

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

/-- **The statement of one clause of (D7) of the pre-`R` class** for the record `rep`: the field of
`Def7.D7Bdry` of the same name (`d7Bdry_of_clauses`, `D7Bdry.clause`). -/
def D7Clause.Holds {m₀ m₁ : ℕ} (Fr : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hkK : k ≤ K)
    (rep : Rep S n R k0 K M N geo cs P k) (Zof : LabHist S n R k0 K → Set (Torus S.d (n k)))
    (aw μs ε ε1 νs : ℕ → ℝ) (fac rate : ℝ) (hv : EuclideanSpace ℝ (Fin N)) : D7Clause → Prop
  | .locField => ∀ A ∈ rep.hist, ∀ X ∈ bdryDomsPre Fr A k (Zof A),
    ∀ (ψ₁ ψ₂ ψ'₁ ψ'₂ : MultiFieldC S n M K N) (h : Fin N → ℂ) (g₁ g₂ : GIdx S n M K N → ℂ),
      (∀ j, j ≤ K → ∀ y : BlockAt S n M K j,
        BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) →
          ψ₁ j y = ψ₂ j y ∧ ψ'₁ j y = ψ'₂ j y) →
      (∀ x i, x ∈ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) →
        g₁ (x, i) = g₂ (x, i)) →
      rep.B A X ψ₁ ψ'₁ h g₁ = rep.B A X ψ₂ ψ'₂ h g₂
  | .locHist => ∀ A ∈ rep.hist, ∀ A' ∈ rep.hist, ∀ X : Finset (Torus S.d (n k)),
    X ∈ bdryDomsPre Fr A k (Zof A) → X ∈ bdryDomsPre Fr A' k (Zof A') →
    (∀ j, j ≤ k →
      fineSet (S := S) (n := n) M K j (OmegaCube A.H j) ∩
          fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) =
        fineSet (S := S) (n := n) M K j (OmegaCube A'.H j) ∩
          fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ∧
      (j < k → (globalLH A.H M).OmegaDD j ∩ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) =
        (globalLH A'.H M).OmegaDD j ∩
          fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) ∧
      (globalLHPre A.H M k).Z j ∩ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) =
        (globalLHPre A'.H M k).Z j ∩ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) →
    (∀ c : A.H.Comp k, (c.1 ∩ X).Nonempty → ∃ c' : A'.H.Comp k, c'.1 = c.1 ∧
      A'.H.localHistory M K k c' = A.H.localHistory M K k c) →
    (∀ c' : A'.H.Comp k, (c'.1 ∩ X).Nonempty → ∃ c : A.H.Comp k, c.1 = c'.1) →
    ∀ ψ ψ' h g, rep.B A X ψ ψ' h g = rep.B A' X ψ ψ' h g
  | .real => ∀ A ∈ rep.hist, ∀ X ∈ bdryDomsPre Fr A k (Zof A),
    ∀ (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      (∀ j y i, (ψ j y i).im = 0 ∧ (ψ' j y i).im = 0) → (∀ i, (h i).im = 0) →
      (∀ p, (g p).im = 0) → (rep.B A X ψ ψ' h g).im = 0
  | .analytic => ∀ A ∈ rep.hist, ∀ X ∈ bdryDomsPre Fr A k (Zof A), ∀ h ∈ hSetB hv,
    AnalyticOnNhd ℂ
      (fun p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ) =>
        rep.B A X (extK p.1) (extK p.2.1) h p.2.2)
      {p | H7Domain geo.M1 geo.c geo.hM hnn (globalLHPre A.H M k) k hkK
        (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i))}
  | .bound => ∀ A ∈ rep.hist, ∀ X ∈ bdryDomsPre Fr A k (Zof A), ∀ h ∈ hSetB hv,
    ∀ p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ),
      H7Domain geo.M1 geo.c geo.hM hnn (globalLHPre A.H M k) k hkK
        (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i)) →
      ‖rep.B A X (extK p.1) (extK p.2.1) h p.2.2‖ <
        fac * Real.exp (-rate * d7SizePre Fr A k X)
  | .rot => ∀ A ∈ rep.hist, ∀ X ∈ bdryDomsPre Fr A k (Zof A), ∀ (ρ : OrthN N)
    (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      rep.B A X (rotM ρ ψ) (rotM ρ ψ') (rotC ρ h) (rotG ρ g) = rep.B A X ψ ψ' h g
  | .euclid => ∀ A ∈ rep.hist, ∀ A' ∈ rep.hist, ∀ σ : LatTorusSym S n M K, RegionIso σ A.H A'.H →
    (∀ j (c : Finset (Torus S.d (n j))), A'.keptLab j (c.map (σ.ec j).toEmbedding) =
      A.keptLab j c) →
    ∀ X ∈ bdryDomsPre Fr A k (Zof A), ∀ (ψ ψ' : MultiFieldC S n M K N)
      (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      rep.B A' (X.map (σ.ec k).toEmbedding) (symM σ ψ) (symM σ ψ') h (symG σ g) =
        rep.B A X ψ ψ' h g
  | .support => ∀ A ∈ rep.hist, ∀ X ∈ bdryDoms (OmegaCube A.H k) (Zof A), ¬ FineValidPre Fr A k X →
    ∀ (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      rep.B A X ψ ψ' h g = 0

variable {m₀ m₁ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {hnn : ∀ i, i < K → n i = S.L * n (i + 1)}
  {hkK : k ≤ K} {rep : Rep S n R k0 K M N geo cs P k}
  {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))} {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ}
  {hv : EuclideanSpace ℝ (Fin N)}

/-- **(D7) of the pre-`R` class from its eight clauses.** -/
theorem d7Bdry_of_clauses
    (h : ∀ c : D7Clause, c.Holds Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv) :
    D7Bdry Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv :=
  ⟨h .locField, h .locHist, h .real, h .analytic, h .bound, h .rot, h .euclid, h .support⟩

/-- **Each clause of (D7) of the pre-`R` class holds.** -/
theorem _root_.Balaban.LargeField.Def7.D7Bdry.clause
    (h : D7Bdry Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv) :
    ∀ c : D7Clause, c.Holds Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv
  | .locField => h.loc_field
  | .locHist => h.loc_hist
  | .real => h.real
  | .analytic => h.analytic
  | .bound => h.bound
  | .rot => h.rot
  | .euclid => h.euclid
  | .support => h.support

/-- (D7) of the pre-`R` class is the conjunction of its eight clauses. -/
theorem d7Bdry_iff_clauses :
    D7Bdry Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv ↔
      ∀ c : D7Clause, c.Holds Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv :=
  ⟨D7Bdry.clause, d7Bdry_of_clauses⟩

end Clauses

section Inputs

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)
  (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉))

/-- **One clause of (D7) for a family of boundary terms of the step** (the form of `LFBdryPart`, the
clause `cl` only): at the physical field, with the constant `fac κ c₉` and the rate `3κ/2` of the
pre-`R` class, for the family whose boundary terms are those of `B'` (the other data of the successor
unchanged). -/
def LFBdryClause (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (B' : ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
      [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
      (rec : RepRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk) (nK : ℕ) [NeZero nK],
      BTerms 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) rec.R
        (kZero d (T κ c₉).L β ν) (kf + 1) (T κ c₉).M N (k + 1))
    (fac : ℝ → ℝ → ℝ) (cl : D7Clause) : Prop :=
  LFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ fun κ c₉ β ν h kf _ _ k ρ νk rec hkK' =>
    rec.SuccFams (Φ κ c₉ β ν k rec.F.sf) (Λ κ c₉ β ν h kf k ρ νk rec) fun F' =>
      ∀ (nK : ℕ) [NeZero nK], cl.Holds (fineFrame 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
          (sides (T κ c₉).L (kf + 1) nK) (kf + 1) rec.hM6) (sides_hnn (T κ c₉).L (kf + 1) nK)
        hkK' { F'.lf nK with B := B' κ c₉ β ν h kf k ρ νk rec nK } (fun A => A.H.F.Zpre (k + 1))
        F'.weights (rec.succCs (Φ κ c₉ β ν k rec.F.sf)).mu ((P6 κ c₉).eps d (T κ c₉).L)
        (epsOne 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (P6 κ c₉) (C7 κ c₉))
        (rec.succCs (Φ κ c₉ β ν k rec.F.sf)).nu (fac κ c₉) (3 / 2 * (P6 κ c₉).κ) h

/-- **(D7) of a family of boundary terms of the step from its eight clauses** (`LFBdryPart`). -/
theorem lfBdryPart_of_clauses (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (B' : ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
      [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
      (rec : RepRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk) (nK : ℕ) [NeZero nK],
      BTerms 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) rec.R
        (kZero d (T κ c₉).L β ν) (kf + 1) (T κ c₉).M N (k + 1))
    (fac : ℝ → ℝ → ℝ)
    (hcl : ∀ cl : D7Clause, LFBdryClause d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ B' fac cl) :
    LFBdryPart d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ B' fac := by
  intro κ hκ c₉ hc₉
  choose b hb using fun cl : D7Clause => hcl cl κ hκ c₉ hc₉
  refine ⟨D7Clause.maxOf b, ?_⟩
  intro β hβ ν hν hνL h hh kf hkf _ _ k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK' SD hM nK _
  refine d7Bdry_of_clauses fun cl => ?_
  exact hb cl β ((D7Clause.le_maxOf b cl).trans hβ) ν hν hνL h hh kf hkf k hk1 hk
    ρ νk rec hD2 hD8 hD9 hafree hcst hkK' SD hM nK

/-- **The old part of the step's boundary terms satisfies (D7), clause by clause** (blocker 3,
`LFBdryOldInput`): from the identity `OldPartEq Λ Sb O` (ladder item 6) and the eight clauses of (D7)
for the family `O` with the constant `Bo` (`LFBdryClause … O Bo cl`; the clauses `locHist` and
`euclid` are W1164's, the others ladder items 1–5). -/
theorem lfBdryOldInput_of_clauses (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (Sb : LFBdrySplit d N T P6 C7 PB cs₀ M1 c rH ϱ Λ) (Bo : ℝ → ℝ → ℝ)
    (O : ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
      [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
      (rec : RepRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk) (nK : ℕ) [NeZero nK],
      BTerms 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) rec.R
        (kZero d (T κ c₉).L β ν) (kf + 1) (T κ c₉).M N (k + 1))
    (hEq : OldPartEq d N T P6 C7 PB cs₀ M1 c rH ϱ Λ Sb O)
    (hLocField : LFBdryClause d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ O Bo .locField)
    (hLocHist : LFBdryClause d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ O Bo .locHist)
    (hReal : LFBdryClause d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ O Bo .real)
    (hAnalytic : LFBdryClause d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ O Bo .analytic)
    (hBound : LFBdryClause d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ O Bo .bound)
    (hRot : LFBdryClause d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ O Bo .rot)
    (hEuclid : LFBdryClause d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ O Bo .euclid)
    (hSupport : LFBdryClause d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ O Bo .support) :
    LFBdryOldInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ Sb Bo :=
  lfBdryOldInput_of_old_eq d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ Sb Bo O hEq
    (lfBdryPart_of_clauses d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ O Bo fun
      | .locField => hLocField
      | .locHist => hLocHist
      | .real => hReal
      | .analytic => hAnalytic
      | .bound => hBound
      | .rot => hRot
      | .euclid => hEuclid
      | .support => hSupport)

end Inputs

end Balaban.RootFSpine
