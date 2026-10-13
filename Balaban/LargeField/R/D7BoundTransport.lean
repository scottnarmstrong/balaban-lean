/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2Class
public import Balaban.LargeField.R.D7AvoidGeometry

/-!
# Transport of the bound field of the boundary terms across `R`, on labels avoiding removal

Package (3) of `notes/phase1/VMOD-40.md` §3.  The pre-`R` record `D7Bdry2` (labels `bdryDomsPre`,
size `d7SizePre`, constant `B_st`, rate `3κ/2`) and the post-`R` record `D7Bdry2Post` (labels
`bdryDomsPost`, size `d7Size`, constant `B₀`, rate `κ`) are related, for the labels that avoid the
components removed by `R`, by the geometry of `R/D7AvoidGeometry`.

**What is proved.**  `d7Post_bound_of_avoid_of_gas`: the `bound` field of `D7Bdry2Post`, for all
labels of `bdryDomsPost`, from the `bound` and `support` fields of the pre-`R` record `D7Bdry2`
together with two hypotheses on the output record (below).  The per-label field lemmas
`real_of_avoid`, `analytic_of_avoid`, `loc_field_of_avoid`, `rot_of_avoid`
(and `*_of_zero` for a label whose coefficient vanishes) and `post_support_of_avoid` transfer the
corresponding fields of the pre record to a label with the same coefficient.

**What is NOT proved.**  The coefficient identity on labels avoiding the removed set
(`rout.B A Y = rin.B (π A) Y`) and the gas bound on the others
(`‖rout.B A Y ...‖ < B₀ e^{-κ d7Size}`) are NOT proved; they are the outputs of the operation
`R` (P7 (3.26)-(3.28)), which is not constructed in this repository yet.  They are hypotheses of
the theorem, named `hyp_avoid`, `hyp_gas`, `hyp_split`.  The per-term charge of an earlier note
(VMOD-37 inequality (3), a multiplier for every old term meeting a removed component) is not the
mechanism (VMOD-40 §1): a coefficient whose label meets a removed component is consumed by the
gas of removed components, and the estimate needed concerns the sum of all gas clusters assigned
to each new boundary label.

**The three cases of a post label `Y`.**  (i) `Y` meets the removed set: `hyp_gas`.  (ii) `Y`
avoids the removed set and is a pre label at cube level (`Y ∈ bdryDoms Ω^pre Z^pre`): the output
coefficient is the input one (`hyp_avoid`); then if `Y` is `FineValidPre` the pre bound with rate
`3κ/2` and the equal sizes give the post bound, and otherwise the input coefficient vanishes by
the pre `support`.  (iii) `Y` avoids the removed set but is not a pre label at cube level (the
nearest-neighbour components of the cube-level complement of `Ω^pre` are joined through removed
cells, so the cube-level domain condition `DmodOmega` fails before `R`): the pre record says
nothing; `hyp_split` supplies the bound.  This case is the cube-level form of the failure of the
converse of `fineValid_of_fineValidPre` (`exists_split_comp_of_fineValid_not_pre`).

**Fields not transferred.**  `loc_hist` and `euclid` quantify over pairs of histories (and
lattice symmetries); they transfer only if the coefficient identity is coherent across the
histories `A, A'` and the symmetries (the map `π` commuting with the localized histories of the
components meeting `Y`, and with `RegionIso`); pointwise equality for one history does not give
them.  `support` for the post record needs the output to vanish on the post labels that are not
`FineValid`: for labels avoiding removal that are pre labels at cube level this follows
(`post_support_of_avoid`); the others are produced by `R`.  New coefficients (those of labels
meeting the removed set) need all seven fields afresh.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Def7v2

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.LargeField.Def7
  RegionHistory Filter Topology

section Transport

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {m₀ m₁ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁}
  {hnn : ∀ i, i < K → n i = S.L * n (i + 1)} {hkK : k ≤ K}
  {aw μs ε ε1 νs : ℕ → ℝ} {hv : EuclideanSpace ℝ (Fin N)} {rH : ℝ}
  {rin rout : Rep S n R k0 K M N geo cs P k}

/-- **T4: the two-case bound theorem** (VMOD-40 "Proposed bound theorem").

Data: the pre record `rin` with `hin : D7Bdry2 … (fun A => A.H.F.Zpre k) … Bst ((3/2) κ) …`;
`0 ≤ κ`, `0 ≤ Bst ≤ B0`, `0 < B0`; a map `π` from the histories of `rout` to histories of `rin`
with the same raw region `Ω_k^pre`, the same `Z^pre_k` and the same global localized history
(`hπ`; `Agree k k` gives the second, `zpre_eq_of_agree`).

Hypotheses on the output record (outputs of the operation `R`, NOT proved here):
`hyp_avoid`, the coefficient of a post label avoiding the removed set that is a pre label at cube
level is the input coefficient; `hyp_gas`, the post bound for labels meeting the removed set;
`hyp_split`, the post bound for labels avoiding the removed set that are not pre labels at cube
level (case (iii) of the module doc).

Conclusion: the `bound` field of `D7Bdry2Post` (constant `B0`, rate `κ`, size `d7Size`) for all
labels of `bdryDomsPost Fr A k (A.H.step k).Z`. -/
theorem d7Post_bound_of_avoid_of_gas {κ Bst B0 : ℝ}
    (hin : D7Bdry2 Fr hnn hkK rin (fun A => A.H.F.Zpre k) aw μs ε ε1 νs Bst ((3 / 2) * κ) hv rH)
    (hκ : 0 ≤ κ) (hBB : Bst ≤ B0) (hB0 : 0 < B0)
    (π : LabHist S n R k0 K → LabHist S n R k0 K)
    (hπ : ∀ A ∈ rout.hist, π A ∈ rin.hist ∧ OmegaCube (π A).H k = OmegaCube A.H k ∧
      (π A).H.F.Zpre k = A.H.F.Zpre k ∧ globalLH (π A).H M = globalLH A.H M)
    (hyp_avoid : ∀ A ∈ rout.hist, ∀ Y ∈ bdryDomsPost Fr A k (A.H.step k).Z,
      Disjoint (Y : Set (Torus S.d (n k))) (A.H.removedSet k) →
      Y ∈ bdryDoms (OmegaCube A.H k) (A.H.F.Zpre k) → rout.B A Y = rin.B (π A) Y)
    (hyp_gas : ∀ A ∈ rout.hist, ∀ Y ∈ bdryDomsPost Fr A k (A.H.step k).Z,
      ¬ Disjoint (Y : Set (Torus S.d (n k))) (A.H.removedSet k) →
      ∀ h ∈ hSetB2 hv rH, ∀ p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ),
      H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) k hkK
        (fineSet (S := S) (n := n) M K k (Y : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i)) →
      ‖rout.B A Y (extK p.1) (extK p.2.1) h p.2.2‖ < B0 * Real.exp (-κ * d7Size Fr A k Y))
    (hyp_split : ∀ A ∈ rout.hist, ∀ Y ∈ bdryDomsPost Fr A k (A.H.step k).Z,
      Disjoint (Y : Set (Torus S.d (n k))) (A.H.removedSet k) →
      Y ∉ bdryDoms (OmegaCube A.H k) (A.H.F.Zpre k) →
      ∀ h ∈ hSetB2 hv rH, ∀ p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ),
      H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) k hkK
        (fineSet (S := S) (n := n) M K k (Y : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i)) →
      ‖rout.B A Y (extK p.1) (extK p.2.1) h p.2.2‖ < B0 * Real.exp (-κ * d7Size Fr A k Y)) :
    ∀ A ∈ rout.hist, ∀ Y ∈ bdryDomsPost Fr A k (A.H.step k).Z, ∀ h ∈ hSetB2 hv rH,
    ∀ p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ),
      H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) k hkK
        (fineSet (S := S) (n := n) M K k (Y : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i)) →
      ‖rout.B A Y (extK p.1) (extK p.2.1) h p.2.2‖ < B0 * Real.exp (-κ * d7Size Fr A k Y) := by
  intro A hA Y hY h hh p hp
  by_cases hd : Disjoint (Y : Set (Torus S.d (n k))) (A.H.removedSet k)
  swap
  · exact hyp_gas A hA Y hY hd h hh p hp
  by_cases hcube : Y ∈ bdryDoms (OmegaCube A.H k) (A.H.F.Zpre k)
  swap
  · exact hyp_split A hA Y hY hd hcube h hh p hp
  obtain ⟨hπin, hΩ, hZ, hG⟩ := hπ A hA
  have hid := hyp_avoid A hA Y hY hd hcube
  have hcube' : Y ∈ bdryDoms (OmegaCube (π A).H k) ((π A).H.F.Zpre k) := by
    rw [hΩ, hZ]; exact hcube
  by_cases hvp : FineValidPre Fr (π A) k Y
  · have hYpre : Y ∈ bdryDomsPre Fr (π A) k ((π A).H.F.Zpre k) := mem_bdryDomsPre.2 ⟨hcube', hvp⟩
    have hb := hin.bound (π A) hπin Y hYpre h hh p (by rw [hG]; exact hp)
    rw [hid]
    have hsz : d7SizePre Fr (π A) k Y = d7Size Fr A k Y := by
      have : d7SizePre Fr (π A) k Y = d7SizePre Fr A k Y := by
        unfold d7SizePre d7SizeAt d7SizeAtE; rw [hΩ]
      rw [this, d7Size_eq_d7SizePre_of_disjoint Fr A Y hd]
    rw [hsz] at hb
    have hD := d7Size_nonneg Fr A k Y
    refine hb.trans_le ?_
    calc Bst * Real.exp (-(3 / 2 * κ) * d7Size Fr A k Y)
        ≤ B0 * Real.exp (-(3 / 2 * κ) * d7Size Fr A k Y) :=
          mul_le_mul_of_nonneg_right hBB (Real.exp_nonneg _)
      _ ≤ B0 * Real.exp (-κ * d7Size Fr A k Y) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hB0.le
          nlinarith [mul_nonneg hκ hD]
  · have hz := hin.support (π A) hπin Y hcube' hvp (extK p.1) (extK p.2.1) h p.2.2
    rw [hid, hz, norm_zero]
    exact mul_pos hB0 (Real.exp_pos _)

/-! ### T5: the other fields, label by label -/

variable {A Apre : LabHist S n R k0 K} {Y : Finset (Torus S.d (n k))}

/-- **`real`** at a label with the input coefficient. -/
theorem real_of_avoid {fac rate : ℝ}
    (hin : D7Bdry2 Fr hnn hkK rin (fun A => A.H.F.Zpre k) aw μs ε ε1 νs fac rate hv rH)
    (hA' : Apre ∈ rin.hist) (hY : Y ∈ bdryDomsPre Fr Apre k (Apre.H.F.Zpre k))
    (hid : rout.B A Y = rin.B Apre Y) :
    ∀ (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      (∀ j y i, (ψ j y i).im = 0 ∧ (ψ' j y i).im = 0) → (∀ i, (h i).im = 0) →
      (∀ p, (g p).im = 0) → (rout.B A Y ψ ψ' h g).im = 0 := by
  intro ψ ψ' h g h1 h2 h3
  rw [hid]; exact hin.real Apre hA' Y hY ψ ψ' h g h1 h2 h3

/-- **`rot`** at a label with the input coefficient. -/
theorem rot_of_avoid {fac rate : ℝ}
    (hin : D7Bdry2 Fr hnn hkK rin (fun A => A.H.F.Zpre k) aw μs ε ε1 νs fac rate hv rH)
    (hA' : Apre ∈ rin.hist) (hY : Y ∈ bdryDomsPre Fr Apre k (Apre.H.F.Zpre k))
    (hid : rout.B A Y = rin.B Apre Y) :
    ∀ (ρ : OrthN N) (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      rout.B A Y (rotM ρ ψ) (rotM ρ ψ') (rotC ρ h) (rotG ρ g) = rout.B A Y ψ ψ' h g := by
  intro ρ ψ ψ' h g
  rw [hid]; exact hin.rot Apre hA' Y hY ρ ψ ψ' h g

/-- **`loc_field`** at a label with the input coefficient. -/
theorem loc_field_of_avoid {fac rate : ℝ}
    (hin : D7Bdry2 Fr hnn hkK rin (fun A => A.H.F.Zpre k) aw μs ε ε1 νs fac rate hv rH)
    (hA' : Apre ∈ rin.hist) (hY : Y ∈ bdryDomsPre Fr Apre k (Apre.H.F.Zpre k))
    (hid : rout.B A Y = rin.B Apre Y) :
    ∀ (ψ₁ ψ₂ ψ'₁ ψ'₂ : MultiFieldC S n M K N) (h : Fin N → ℂ) (g₁ g₂ : GIdx S n M K N → ℂ),
      (∀ j, j ≤ K → ∀ y : BlockAt S n M K j,
        BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (fineSet (S := S) (n := n) M K k (Y : Set (Torus S.d (n k)))) →
          ψ₁ j y = ψ₂ j y ∧ ψ'₁ j y = ψ'₂ j y) →
      (∀ x i, x ∈ fineSet (S := S) (n := n) M K k (Y : Set (Torus S.d (n k))) →
        g₁ (x, i) = g₂ (x, i)) →
      rout.B A Y ψ₁ ψ'₁ h g₁ = rout.B A Y ψ₂ ψ'₂ h g₂ := by
  intro ψ₁ ψ₂ ψ'₁ ψ'₂ h g₁ g₂ h1 h2
  rw [hid]; exact hin.loc_field Apre hA' Y hY ψ₁ ψ₂ ψ'₁ ψ'₂ h g₁ g₂ h1 h2

/-- **`analytic`** at a label with the input coefficient, when the two histories have the same
global localized history. -/
theorem analytic_of_avoid {fac rate : ℝ}
    (hin : D7Bdry2 Fr hnn hkK rin (fun A => A.H.F.Zpre k) aw μs ε ε1 νs fac rate hv rH)
    (hA' : Apre ∈ rin.hist) (hY : Y ∈ bdryDomsPre Fr Apre k (Apre.H.F.Zpre k))
    (hid : rout.B A Y = rin.B Apre Y) (hG : globalLH Apre.H M = globalLH A.H M) :
    ∀ h ∈ hSetB2 hv rH, AnalyticOnNhd ℂ
      (fun p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ) =>
        rout.B A Y (extK p.1) (extK p.2.1) h p.2.2)
      {p | H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) k hkK
        (fineSet (S := S) (n := n) M K k (Y : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i))} := by
  intro h hh
  rw [hid, ← hG]
  exact hin.analytic Apre hA' Y hY h hh

/-- A label with vanishing output coefficient satisfies the fields `real`, `rot`, `loc_field`
and `analytic` trivially (here `real` and `analytic`). -/
theorem real_of_zero (hz : rout.B A Y = 0) :
    ∀ (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      (rout.B A Y ψ ψ' h g).im = 0 := by
  intro ψ ψ' h g; rw [hz]; rfl

/-- `analytic` for a label with vanishing output coefficient. -/
theorem analytic_of_zero (hz : rout.B A Y = 0) (s : Set (FinFieldC S n M K N × FinFieldC S n M K N
      × (GIdx S n M K N → ℂ))) (h : Fin N → ℂ) :
    AnalyticOnNhd ℂ
      (fun p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ) =>
        rout.B A Y (extK p.1) (extK p.2.1) h p.2.2) s := by
  have : (fun p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ) =>
      rout.B A Y (extK p.1) (extK p.2.1) h p.2.2) = fun _ => 0 := by
    funext p; rw [hz]; rfl
  rw [this]; exact fun _ _ => analyticAt_const

/-- **`support` of the post record at a label avoiding removal.**  If `Y ∈ bdryDoms Ω^pre Z^pre`
avoids the removed set, is not `FineValid` after `R`, and the output coefficient is the input
one, then the coefficient is zero: `Y` is not `FineValidPre` either
(`fineValid_of_fineValidPre`), so the pre `support` applies. -/
theorem post_support_of_avoid {fac rate : ℝ}
    (hin : D7Bdry2 Fr hnn hkK rin (fun A => A.H.F.Zpre k) aw μs ε ε1 νs fac rate hv rH)
    (hA' : Apre ∈ rin.hist) (hΩ : OmegaCube Apre.H k = OmegaCube A.H k)
    (hZ : Apre.H.F.Zpre k = A.H.F.Zpre k)
    (hcube : Y ∈ bdryDoms (OmegaCube A.H k) (A.H.F.Zpre k))
    (hid : rout.B A Y = rin.B Apre Y) (hnv : ¬ FineValid Fr A k Y) :
    ∀ (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ) (g : GIdx S n M K N → ℂ),
      rout.B A Y ψ ψ' h g = 0 := by
  intro ψ ψ' h g
  have hnp : ¬ FineValidPre Fr Apre k Y := fun hv' => hnv (by
    have : FineValidPre Fr A k Y := by
      unfold FineValidPre FineValidAt d7SizeAtE at hv' ⊢; rw [hΩ] at hv'; exact hv'
    exact fineValid_of_fineValidPre this)
  rw [hid]
  exact hin.support Apre hA' Y (by rw [hΩ, hZ]; exact hcube) hnp ψ ψ' h g

end Transport

end Balaban.LargeField.Def7v2
