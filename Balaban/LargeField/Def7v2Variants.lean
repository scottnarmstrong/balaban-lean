/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2Class

/-!
# Def-7 v2, part 6: the variants `IsRepPre2`, `IsRepFlat2`, `IsRepFam2`, `IsRepFamPre2` -- DRAFT

**Draft, pending Roland's answer to Q13.**  The second versions of the variant classes of §II.6.3
and Definition IV.3.1 (`Def7Variants`), assembled from `D1PreForm2`/`D1Form2` (physical action mass
and the P5 (1.8) correction), `D2SF2`/`SFFlat2` (`IsSFFamily2` on the wide domain), (D7) on the
pinned ball `hSetB2` (the pre-`R` record `D7Bdry2` for `IsRepPre2`, the post-`R` record
`D7Bdry2Post` with the fine size `d7Size` for `IsRepFlat2`) and the unchanged clauses (D4)-(D6),
(H6♭), (D8), (D9), (D9♭).  As for
`IsRep2`, the SF-to-LF interface is not a field.  The continuity clauses `FamCont` of the family
classes are the landed ones (they are statements about the data `𝔰(ν)`; the domain on which the
limits are taken is the wide `Ξ^c_j` of Def-6).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Def7v2

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.LargeField.Def7
  RegionHistory Filter Topology

section Variants

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}

/-- **`IsRep^pre_k`, second version** (§II.6.3, first item): as `IsRep2` with `Z^pre_k` in place of
`Z_k` (no `R`-record at scale `k`, the operators `𝕋^pre_k`, `D1PreForm2`), (H6′)^pre in place of
(D6), (D7) with `κ_+ = 3κ/2` and `B_st` (on the pinned ball; the pre-`R` record `D7Bdry2`: raw
region `OmegaCube`, cube-level size `dCovMod`), and (D2) with `½ β_k^{-m-1}` for `ℛ^{(k)}_m`. -/
structure IsRepPre2 (S : Setting) (R : ℕ → ℝ) (k0 K M : ℕ) [NeZero M] [NeZero S.L] (N : ℕ)
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
  complete : ∀ (nK : ℕ) [NeZero nK], IsComplete k k (F.lf nK).hist
  form : ∀ (nK : ℕ) [NeZero nK], D1PreForm2 (F.ctx hM6 hkK nK) vc (F.lf nK) hv (ρ nK)
  corr : D1CorrLim P6.m₀ F.sf St hv vc
  sfData : D2SF2 P6 k0 F.sf (preFac (P6.m₀ + C7.m₁))
  pin : ∀ (nK : ℕ) [NeZero nK], D4Pin k (F.lf nK)
  opBound : ∀ (nK : ℕ) [NeZero nK], D5Bound k hkK (F.lf nK)
  budget : ∀ (nK : ℕ) [NeZero nK], D6Pre (F.lf nK)
  bdry : ∀ (nK : ℕ) [NeZero nK], D7Bdry2 (sides_hnn S.L K nK) hkK (F.lf nK)
    (fun A => A.H.F.Zpre k) F.weights cs.mu (P6.eps S.d S.L) (epsOne S P6 C7) cs.nu C7.Bst
    (3 / 2 * P6.κ) hv rH
  coherent : D8SF P6.m₀ F.sf
  coeff : D9Coeff P6 k0 F.sf

/-- **`IsRep^♭_k`, second version** (§II.6.3, second item; `k₀ ≤ k ≤ k_f`): as `IsRep2` except no
`R`-records beyond `k₀` (built into the histories), (D2♭) `SFFlat2`, (D9♭) `D9Flat`, (H6♭)
`D6Flat` with the a priori horizon `khat = k̂_f`.  (D7) is the post-`R` record `D7Bdry2Post`, as
in `IsRep2`. -/
structure IsRepFlat2 (S : Setting) (R : ℕ → ℝ) (k0 K M : ℕ) [NeZero M] [NeZero S.L] (N : ℕ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M) (cs : OpConsts)
    (P : BudgetConsts) (P6 : Def6.Consts) (C7 : Consts7) (β ν : ℝ)
    (hv : EuclideanSpace ℝ (Fin N)) (rH : ℝ) (k khat : ℕ) {ϱ : ℝ}
    (hM6 : M = S.L ^ (P6.m₀ + C7.m₁)) (hkK : k ≤ K)
    (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ)
    (ρ : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) →
      (GIdx S (sides S.L K nK) M K N → ℂ) → ℂ)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ C7.m₁ k N) (vc : CorrCoef S.d) :
    Prop where
  range : k0 ≤ k
  coh : Coh S R k0 M cs P P6 C7 β ν k F.sf
  field : FieldClauses S k0 k cs F.sf hv
  complete : ∀ (nK : ℕ) [NeZero nK], IsComplete k (k + 1) (F.lf nK).hist
  form : ∀ (nK : ℕ) [NeZero nK], D1Form2 (F.ctx hM6 hkK nK) vc (F.lf nK) hv (ρ nK)
  corr : D1CorrLim P6.m₀ F.sf St hv vc
  sfData : SFFlat2 P6 k0 F.sf
  pin : ∀ (nK : ℕ) [NeZero nK], D4Pin (k + 1) (F.lf nK)
  opBound : ∀ (nK : ℕ) [NeZero nK], D5Bound (k + 1) hkK (F.lf nK)
  budget : ∀ (nK : ℕ) [NeZero nK], D6Flat khat (F.lf nK)
  bdry : ∀ (nK : ℕ) [NeZero nK], D7Bdry2Post (fineFrame S (sides S.L K nK) K hM6)
    (sides_hnn S.L K nK) hkK (F.lf nK)
    (fun A => (A.H.step k).Z) F.weights cs.mu (P6.eps S.d S.L) (epsOne S P6 C7) cs.nu C7.B0 P6.κ
    hv rH
  coherent : D8SF P6.m₀ F.sf
  coeff : D9Flat P6 F.sf

/-- **`IsRepFam2_k`** (Definition IV.3.1, version 1.2, second version): for fixed `β, h`,
constants and `k ≥ 1`, a family `ν ↦ (F(ν), ρ(ν))` for `0 < ν ≤ ν_*(k)`, each member with the
regime index `k₀(ν) = kZero(β, ν)` and on the tori of its horizon `K(ν) ≥ k`: `member` (F-i)
`IsRep2_k` for every `ν` (with coefficient data `St ν`, `vc ν`), and the continuity clauses
`FamCont`.  (F-ii) and the large-field part of (F-iii) are not formalized (as in `IsRepFam`). -/
structure IsRepFam2 (S : Setting) (R : ℕ → ℝ) (M : ℕ) [NeZero M] [NeZero S.L] (N : ℕ)
    (Kν : ℝ → ℕ) (geo : ∀ (ν : ℝ) (nK : ℕ) [NeZero nK], Geo S (sides S.L (Kν ν) nK) R M)
    (cs : ℝ → OpConsts) (P : ℝ → BudgetConsts) (P6 : Def6.Consts) (C7 : Consts7) (β : ℝ)
    (hv : EuclideanSpace ℝ (Fin N)) (rH : ℝ) (k : ℕ) {ϱ : ℝ}
    (hM6 : M = S.L ^ (P6.m₀ + C7.m₁)) (hkK : ∀ ν, k ≤ Kν ν)
    (F : ∀ ν : ℝ, RepFam S R (kZero S.d S.L β ν) (Kν ν) M N (geo ν) (cs ν) (P ν) k C7.m₁ ϱ)
    (ρ : ∀ (ν : ℝ) (nK : ℕ) [NeZero nK],
      (BlockAt S (sides S.L (Kν ν) nK) M (Kν ν) k → EuclideanSpace ℝ (Fin N)) →
        (GIdx S (sides S.L (Kν ν) nK) M (Kν ν) N → ℂ) → ℂ)
    (St : ∀ (_ν : ℝ) (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ C7.m₁ k N)
    (vc : ℝ → CorrCoef S.d) : Prop where
  member : ∀ ν, 0 < ν → ν ≤ nuStar S.d S.L β k →
    IsRep2 S R (kZero S.d S.L β ν) (Kν ν) M N (geo ν) (cs ν) (P ν) P6 C7 β ν hv rH k hM6 (hkK ν)
      (F ν) (ρ ν) (St ν) (vc ν)
  cont : FamCont P6 (fun ν => (F ν).sf)

/-- **`IsRepFam2^pre_k`** (Definition IV.3.1 for the pre-`R` class, second version). -/
structure IsRepFamPre2 (S : Setting) (R : ℕ → ℝ) (M : ℕ) [NeZero M] [NeZero S.L] (N : ℕ)
    (Kν : ℝ → ℕ) (geo : ∀ (ν : ℝ) (nK : ℕ) [NeZero nK], Geo S (sides S.L (Kν ν) nK) R M)
    (cs : ℝ → OpConsts) (P : ℝ → BudgetConsts) (P6 : Def6.Consts) (C7 : Consts7) (β : ℝ)
    (hv : EuclideanSpace ℝ (Fin N)) (rH : ℝ) (k : ℕ) {ϱ : ℝ}
    (hM6 : M = S.L ^ (P6.m₀ + C7.m₁)) (hkK : ∀ ν, k ≤ Kν ν)
    (F : ∀ ν : ℝ, RepFam S R (kZero S.d S.L β ν) (Kν ν) M N (geo ν) (cs ν) (P ν) k C7.m₁ ϱ)
    (ρ : ∀ (ν : ℝ) (nK : ℕ) [NeZero nK],
      (BlockAt S (sides S.L (Kν ν) nK) M (Kν ν) k → EuclideanSpace ℝ (Fin N)) →
        (GIdx S (sides S.L (Kν ν) nK) M (Kν ν) N → ℂ) → ℂ)
    (St : ∀ (_ν : ℝ) (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ C7.m₁ k N)
    (vc : ℝ → CorrCoef S.d) : Prop where
  member : ∀ ν, 0 < ν → ν ≤ nuStar S.d S.L β k →
    IsRepPre2 S R (kZero S.d S.L β ν) (Kν ν) M N (geo ν) (cs ν) (P ν) P6 C7 β ν hv rH k hM6
      (hkK ν) (F ν) (ρ ν) (St ν) (vc ν)
  cont : FamCont P6 (fun ν => (F ν).sf)

end Variants

end Balaban.LargeField.Def7v2
