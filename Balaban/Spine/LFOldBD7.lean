/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldHS2D7
public import Balaban.Fluctuation.MarkClusterFam
public import Balaban.Fluctuation.MarkClusterReal
public import Balaban.Fluctuation.MarkClusterEquiv

/-!
# The (D7) clauses of the re-expanded old boundary terms at an output label

The old part `oldBAtAt` of the boundary terms at an output label `Y` (any readings of the local pair:
the datum `glob` and the label map `σ` of the local sets) is a sum, over the sets `T` of cubes of
`Ω_{k+1}` with output label `Y`, of the cluster terms of the marks of the old labels.  This file
proves the clauses of (D7) that hold for every interaction family with the corresponding properties:

* `HoleStep.markOf_congr`: the mark of a coefficient depends only on the coefficient and on the fixed
  values at the unit points it reads;
* `oldBAtAt_eq_zero_of_not_valid` (clause `support`): the old part vanishes at a label that is not
  valid at `Ω_{k+1}`;
* `oldBAtAt_congr_fields` (clause `loc_field`): the old part at `Y` depends only on the fields on the
  blocks inside the fine set of `Y`, when the activities of the labels inside `Y` and the fixed values
  at the unit points inside `Y` depend only on them;
* `oldBAtAt_im` (clause `real`): the old part is real when the activities at real parameters, the
  fixed values and the coefficients at real fluctuation fields are real;
* `oldBAtAt_rot` (clause `rot`): the old part is `O(N)`-invariant when the interaction family and the
  coefficients are covariant.
-/

@[expose] public section

open MeasureTheory ComplexConjugate Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background
  Balaban.Polymer Balaban.Localization.DecEquiv Matrix


namespace Balaban.Fluctuation.HoleStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  (S : HoleStep d L N₁ m₁ k N ϱ ϱ')

/-- **Congruence of a mark**: the marks of two functions `T₁`, `T₂` that agree, the first reading the
field only at the unit points `U₀`, with fixed values agreeing on `U₀`, are equal. -/
theorem markOf_congr (inner : Finset S.U) {Cb : Type*} (cb : inner → Cb)
    {ψout₁ ψout₂ : S.U → Fin N → ℂ} (U₀ : Finset S.U) (r : ℝ) {T₁ T₂ : (S.U → Fin N → ℂ) → ℂ}
    (hT₁ : ∀ ψ ψ' : S.U → Fin N → ℂ, (∀ b ∈ U₀, ψ b = ψ' b) → T₁ ψ = T₁ ψ')
    (hT : ∀ ψ, T₁ ψ = T₂ ψ) (hout : ∀ b ∈ U₀, ψout₁ b = ψout₂ b) :
    S.markOf inner cb ψout₁ U₀ r T₁ = S.markOf inner cb ψout₂ U₀ r T₂ := by
  classical
  funext Φ
  have hfill : ∀ b ∈ U₀, S.fill inner (ungroup cb Φ) ψout₁ b = S.fill inner (ungroup cb Φ) ψout₂ b := by
    intro b hb
    funext i
    unfold fill
    by_cases hbi : b ∈ inner
    · simp only [hbi, ↓reduceDIte]
    · simp only [hbi, ↓reduceDIte, hout b hb]
  unfold markOf
  have hcond : (∀ b ∈ U₀, vn (S.fill inner (ungroup cb Φ) ψout₁ b) < r) ↔
      (∀ b ∈ U₀, vn (S.fill inner (ungroup cb Φ) ψout₂ b) < r) :=
    ⟨fun h b hb => hfill b hb ▸ h b hb, fun h b hb => (hfill b hb).symm ▸ h b hb⟩
  split_ifs with h1 h2 h2
  · rw [hT₁ _ _ hfill, hT]
  · exact absurd (hcond.1 h1) h2
  · exact absurd (hcond.2 h2) h1
  · rfl

end Balaban.Fluctuation.HoleStep

namespace Balaban.RootFSpine

section D7Old

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

open Classical in
/-- **The clause `support` of (D7) for the old part** (any readings of the local pair): the old part
at a label `Y` that is not valid at `Ω_{k+1}` vanishes (the terms of a set `T` of cubes with output
label `Y` vanish unless `T ≠ ∅` and `d_Ω(T) < ∞`, and then `Y` is valid, `outLabel_spec`). -/
theorem oldBAtAt_eq_zero_of_not_valid (glob : Bool) {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (σ : Finset (Torus S.d (n k)) → Finset (Torus S.d (n k)))
    (hk : k + 1 ≤ K) (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N)
    (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ)
    (inner : Finset (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull F (k + 1) (OmegaCube H (k + 1))))
    (hp : 0 < p₁) (I : LocInteraction (fun b => {u : inner // cb u = b} → Rn N))
    (ψout : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) (rψ : ℝ)
    (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (Xs : Finset (Finset (Torus S.d (n k)))) (ψ' : MultiFieldC S n M K N)
    (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ) (Y : Finset (Torus S.d (n (k + 1))))
    (hY : ¬ FineValidAt F (k + 1) (OmegaCube H (k + 1)) Y) :
    oldBAtAt (glob := glob) (σ := σ) g hnn hM1 F H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb hp I ψout
      rψ ρc ρ r r' rep A Xs ψ' hv gx Y = 0 := by
  have hΩ' := d7Pull_isPiUnion F hnn hk (OmegaCube H (k + 1))
  have := (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).isProbabilityMeasure_cubeMeasure
    inner cb hp
  unfold oldBAtAt
  refine Finset.sum_eq_zero fun T hT => Finset.sum_eq_zero fun X _ => Finset.sum_eq_zero fun V hV => ?_
  have hTY := (Finset.mem_filter.1 hT).2
  obtain ⟨hVs, hVT⟩ := Finset.mem_filter.1 hV
  obtain ⟨-, -, hVd, hm⟩ := exists_of_mem_sitesXAt (σ := σ) g hnn hM1 hVs
  obtain ⟨b, hb⟩ := blocksOf_nonempty_of_isDj F.divN₁ hk hΩ' hVd hm
  have hTne : T.Nonempty := ⟨b, hVT hb⟩
  by_cases hfin : dOmega m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1))) (sitesOf T) = ⊤
  · exact markTerm_eq_zero_of_dOmega_top _ F.divN₁ hk hΩ' I.A V hVd hm _ hfin
  · exact absurd (hTY ▸ (outLabel_spec F hnn hk (OmegaCube H (k + 1)) T hTne hfin).2.1) hY


open Classical in
/-- **The clause `loc_field` of (D7) for the old part at an output label** (any readings of the local
pair): for two values of the fields agreeing on the blocks inside the fine set of `Y`, an interaction
family whose activities agree on the labels inside `Y` (`hact`) and fixed values agreeing at the unit
points inside `Y` (`hout`), the old parts at `Y` agree.  The cluster terms read the activities of the
labels inside `Ŷ(T) = Y` (`Gst_congr`, `ysite_subset_Yhat`); the marks read the coefficients, which read
the fields inside `Y` (`oldCoefLocAt_congr_fields`, `stepReadsIn_outLabelAt`, `fineSet_subset_outLabelAt`,
the record's `loc_field`), and the fixed values at the unit points of the local pairs, inside the mark
sites (`markSiteAt_subset_outLabel`). -/
theorem oldBAtAt_congr_fields (glob : Bool) {m₀ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {k : ℕ}
    (σ : Finset (Torus S.d (n k)) → Finset (Torus S.d (n k))) (hk : k + 1 ≤ K)
    {cs : OpConsts} {P : BudgetConsts} {rep : Rep S n R k0 K M N g cs P k}
    {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))} {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ}
    {hv : EuclideanSpace ℝ (Fin N)}
    (hrec : D7BdryPost Fr hnn (Nat.le_of_succ_le hk) rep Zof aw μs ε ε1 νs fac rate hv)
    {A : LabHist S n R k0 K} (hA : A ∈ rep.hist) (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊)
    (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) {Xs : Finset (Finset (Torus S.d (n k)))}
    (hXs : ∀ X ∈ Xs, X ∈ bdryDomsPost Fr A k (Zof A) ∧ X ∈ oldDoms Fr A.H k)
    {ψ₁ : MultiFieldC S n M K N}
    (inner : Finset (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))))
    (hcb : ∀ u : inner, toFrame g hnn hM1 Fr hk
      (unitRep (u : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ).U)) ∈
        Localization.box (cb u).1 (cellSide S.L m₀ m₁ (k + 1)))
    (hp : 0 < p₁) {Prm : Type*} (IF : LocIntFam (fun b => {u : inner // cb u = b} → Rn N) Prm)
    (p₁' p₂' : Prm) (Y : Finset (Torus S.d (n (k + 1))))
    (hact : ∀ (u : ℂ) (y : IF.Lb), IF.Lab.ysite y ⊆ d7Pull Fr (k + 1) (Y : Set (Torus S.d (n (k + 1)))) →
      (IF.A p₁' u).H y = (IF.A p₂' u).H y)
    (ψout₁ ψout₂ : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ)
    (hout : ∀ b, toFrame g hnn hM1 Fr hk (unitRep b) ∈ d7Pull Fr (k + 1) (Y : Set (Torus S.d (n (k + 1)))) →
      ψout₁ b = ψout₂ b)
    (rψ ρc : ℝ) (ρ r r' : ℕ) (ψ₂ ψ'₁ ψ'₂ : MultiFieldC S n M K N) (gx₁ gx₂ : GIdx S n M K N → ℂ)
    (hψ : ∀ j, j ≤ K → ∀ y : BlockAt S n M K j, BlockSub (S := S) (n := n) (M := M) (K := K) j y
      (fineSet (S := S) (n := n) M K (k + 1) (Y : Set (Torus S.d (n (k + 1))))) → ψ₁ j y = ψ₂ j y)
    (hψ' : ∀ j, j ≤ K → ∀ y : BlockAt S n M K j, BlockSub (S := S) (n := n) (M := M) (K := K) j y
      (fineSet (S := S) (n := n) M K (k + 1) (Y : Set (Torus S.d (n (k + 1))))) → ψ'₁ j y = ψ'₂ j y)
    (hgx : ∀ x i, x ∈ fineSet (S := S) (n := n) M K (k + 1) (Y : Set (Torus S.d (n (k + 1)))) →
      gx₁ (x, i) = gx₂ (x, i)) :
    oldBAtAt (glob := glob) (σ := σ) g hnn hM1 Fr A.H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ inner cb hp
        (IF.at p₁') ψout₁ rψ ρc ρ r r' rep A Xs ψ'₁ hv gx₁ Y =
      oldBAtAt (glob := glob) (σ := σ) g hnn hM1 Fr A.H hk hk1 hρ ψ₂ z h₀ a₁ ν β p₁ δ inner cb hp
        (IF.at p₂') ψout₂ rψ ρc ρ r r' rep A Xs ψ'₂ hv gx₂ Y := by
  have hΩ' := d7Pull_isPiUnion Fr hnn hk (OmegaCube A.H (k + 1))
  have hp1 := (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ).isProbabilityMeasure_cubeMeasure
    inner cb hp
  have hp2 := (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ₂ z h₀ a₁ ν β p₁ δ).isProbabilityMeasure_cubeMeasure
    inner cb hp
  unfold oldBAtAt
  refine Finset.sum_congr rfl fun T hT => Finset.sum_congr rfl fun X hX =>
    Finset.sum_congr rfl fun V hV => ?_
  have hTY := (Finset.mem_filter.1 hT).2
  obtain ⟨hVs, hVT⟩ := Finset.mem_filter.1 hV
  obtain ⟨-, -, hVd, hm⟩ := exists_of_mem_sitesXAt (σ := σ) g hnn hM1 hVs
  by_cases hfin : dOmega m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (sitesOf T) = ⊤
  · rw [show oldClusterSiteAt (glob := glob) (σ := σ) g hnn hM1 Fr A.H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ
        inner cb hp (IF.at p₁') ψout₁ rψ ρc ρ r r' rep A X ψ'₁ hv gx₁ V T = 0 from
      markTerm_eq_zero_of_dOmega_top _ Fr.divN₁ hk hΩ' (IF.at p₁').A V hVd hm _ hfin]
    unfold oldClusterSiteAt
    exact (markTerm_eq_zero_of_dOmega_top
      ((holeStepLF g hnn hM1 A.H hk hk1 hρ ψ₂ z h₀ a₁ ν β p₁ δ).cubeMeasure inner cb) Fr.divN₁ hk hΩ'
      (IF.at p₂').A V hVd hm _ hfin).symm
  obtain ⟨b, hb⟩ := blocksOf_nonempty_of_isDj Fr.divN₁ hk hΩ' hVd hm
  have hTne : T.Nonempty := ⟨b, hVT hb⟩
  have hYhat : d7Pull Fr (k + 1) (Y : Set (Torus S.d (n (k + 1)))) =
      Yhat (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (sitesOf T) := by
    rw [← hTY]; exact (outLabel_spec Fr hnn hk (OmegaCube A.H (k + 1)) T hTne hfin).1
  -- the marks agree
  have hmark : oldMarkSiteAt (glob := glob) (σ := σ) g hnn hM1 Fr A.H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ
      inner cb ψout₁ rψ ρc ρ r r' rep A X ψ'₁ hv gx₁ V =
      oldMarkSiteAt (glob := glob) (σ := σ) g hnn hM1 Fr A.H hk hk1 hρ ψ₂ z h₀ a₁ ν β p₁ δ
      inner cb ψout₂ rψ ρc ρ r r' rep A X ψ'₂ hv gx₂ V := by
    funext Φ
    unfold oldMarkSiteAt
    refine Finset.sum_congr rfl fun J hJ => ?_
    obtain ⟨-, hJg, hJV⟩ := (mem_famAtAt g hnn hM1).1 hJ
    have hJT : blocksOf m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))
        (markSiteAt g hnn hM1 Fr A.H hk hρ r r' (σ X) X J) ⊆ T := hJV ▸ hVT
    obtain ⟨hb', hm'⟩ := Finset.mem_filter.1 (hXs X hX).2
    have hXY := fineSet_subset_outLabelAt g hnn hM1 Fr A.H σ hk hρ (mem_bdryDomsAt.1 hb').2 hm' r r'
      J T hJT hfin
    have hread := stepReadsIn_outLabelAt g hnn hM1 Fr A.H σ hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ r r' X J
      hJg T hJT hfin
    rw [hTY] at hXY hread
    have hsite := markSiteAt_subset_outLabel (σ := σ) Fr hnn hM1 A.H hk hρ r r' X J hJg T hJT hfin
    rw [hTY] at hsite
    have hout' : ∀ u ∈ locUnits g hnn hM1 A.H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ
        (locSetXJ g hM1 A.H r r' (σ X) J), ψout₁ u = ψout₂ u := by
      intro u hu
      refine hout u (hsite ?_)
      refine markBaseAt_subset_markSiteAt g hnn hM1 Fr A.H hk hρ r r' (σ X) X J ?_
      exact Or.inl (Or.inr ⟨_, unitRep_mem_of_mem_locUnits g hnn hM1 A.H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ
        _ hu, rfl⟩)
    have hmo := HoleStep.markOf_congr (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ) inner cb
      (ψout₁ := ψout₁) (ψout₂ := ψout₂) _ rψ
      (oldCoefLocAt_congr (glob := glob) (σ := σ) g hnn hM1 A.H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ ρc ρ r
        r' rep A X ψ'₁ hv gx₁ J)
      (oldCoefLocAt_congr_fields g hnn hM1 glob σ A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X hv
        J (hrec.loc_field A hA X (hXs X hX).1) _ hXY ψ₁ ψ₂ ψ'₁ ψ'₂ gx₁ gx₂ hread hψ hψ' hgx) hout'
    exact congrFun hmo Φ
  unfold oldClusterSiteAt markTerm
  refine intervalIntegral.integral_congr fun u _ => ?_
  have key := Gst_congr ((holeStepLF g hnn hM1 A.H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ).cubeMeasure inner cb)
    ((holeStepLF g hnn hM1 A.H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ).cubeMeasure inner cb)
    ((IF.at p₁').A (u : ℂ)) ((IF.at p₂').A (u : ℂ)).H _ T
    (oldMarkSiteAt_dep (glob := glob) (σ := σ) g hnn hM1 Fr A.H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ inner cb
      hcb ψout₁ rψ ρc ρ r r' rep A X ψ'₁ hv gx₁ V) (fun _ _ => rfl) (fun y hy => ?_) (fun _ => hmark)
  · exact key
  refine hact u y ?_
  rw [hYhat]
  exact ysite_subset_Yhat Fr.divN₁ hk hΩ' IF.Lab y hy


open Classical in
/-- **The clause `real` of (D7) for the old part at an output label** (any readings of the local
pair): the old part is real when the activities of the interaction at real parameters are real, the
fixed values are real and the coefficients of the marks are real at real fluctuation fields in the
ball of the mark (`oldCoefLocAt_im`).  The cluster terms are then real (`markTerm_conj`). -/
theorem oldBAtAt_im (glob : Bool) {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (σ : Finset (Torus S.d (n k)) → Finset (Torus S.d (n k)))
    (hk : k + 1 ≤ K) (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N)
    (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ)
    (inner : Finset (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull F (k + 1) (OmegaCube H (k + 1))))
    (hp : 0 < p₁) (I : LocInteraction (fun b => {u : inner // cb u = b} → Rn N))
    (ψout : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) (rψ : ℝ)
    (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (Xs : Finset (Finset (Torus S.d (n k)))) (ψ' : MultiFieldC S n M K N)
    (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ) (Y : Finset (Torus S.d (n (k + 1))))
    (hI : ∀ (u : ℝ) y Φ, ((I.A (u : ℂ)).H y Φ).im = 0) (hout : ∀ b i, (ψout b i).im = 0)
    (hcoef : ∀ X ∈ Xs, ∀ J, GoodJAt g hnn hM1 F H hk hρ r r' (d7Pull F (k + 1) (OmegaCube H (k + 1)))
      (σ X) X J → ∀ ψhat : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ,
      (∀ b i, (ψhat b i).im = 0) →
      (∀ b ∈ locUnits g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' (σ X) J),
        vn (ψhat b) < rψ) →
      (oldCoefLocAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A
        X ψ' hv gx J ψhat).im = 0) :
    (oldBAtAt (glob := glob) (σ := σ) g hnn hM1 F H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb hp I ψout
      rψ ρc ρ r r' rep A Xs ψ' hv gx Y).im = 0 := by
  have := (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).isProbabilityMeasure_cubeMeasure
    inner cb hp
  rw [← Complex.conj_eq_iff_im]
  unfold oldBAtAt
  simp only [map_sum]
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun X hX =>
    Finset.sum_congr rfl fun V _ => ?_
  unfold oldClusterSiteAt
  refine markTerm_conj _ _ _ _ _ (fun u y Φ => Complex.conj_eq_iff_im.2 (hI u y Φ)) fun Φ => ?_
  unfold oldMarkSiteAt
  simp only [map_sum]
  refine Finset.sum_congr rfl fun J hJ => ?_
  obtain ⟨-, hJg, -⟩ := (mem_famAtAt g hnn hM1).1 hJ
  unfold oldMarkLFAt
  exact HoleStep.markOf_conj _ inner cb _ rψ (fun b i => Complex.conj_eq_iff_im.2 (hout b i))
    (fun ψhat hre hball => Complex.conj_eq_iff_im.2 (hcoef X hX J hJg ψhat
      (fun b i => Complex.conj_eq_iff_im.1 (hre b i)) hball)) Φ

/-- The complex matrix of a rotation acts on real vectors as the rotation. -/
theorem rotCMat_mulVec_ofReal (ρo : OrthN N) (v : Rn N) :
    rotCMat ρo *ᵥ (fun i => ((v i : ℝ) : ℂ)) = fun i => ((ρo v i : ℝ) : ℂ) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rotCMat_apply, rot_apply_coord]
  push_cast
  rfl

open Classical in
/-- **The clause `rot` of (D7) for the old part at an output label** (any readings of the local
pair): rotating the fields `ψ`, `h₀`, `ψ'`, the physical field, the source and the fixed values by
`ρ ∈ O(N)`, with an interaction family covariant under the rotation of the cube variables (`hI`) and
coefficients covariant on the balls of the marks (`hcoef`, `oldCoefLocAt_rot`), leaves the old part
unchanged.  The cube measure is invariant under the rotation (`map_fluctMeasure1_isometry`). -/
theorem oldBAtAt_rot (glob : Bool) {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (σ : Finset (Torus S.d (n k)) → Finset (Torus S.d (n k)))
    (hk : k + 1 ≤ K) (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N)
    (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (ρo : OrthN N)
    (inner : Finset (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull F (k + 1) (OmegaCube H (k + 1))))
    (hp : 0 < p₁) {Prm : Type*} (IF : LocIntFam (fun b => {u : inner // cb u = b} → Rn N) Prm)
    (p₁' p₂' : Prm)
    (ψout : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) (rψ : ℝ)
    (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (Xs : Finset (Finset (Torus S.d (n k)))) (ψ' : MultiFieldC S n M K N)
    (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ) (Y : Finset (Torus S.d (n (k + 1))))
    (hI : ∀ (u : ℝ) y Φ, (IF.A p₂' (u : ℂ)).H y (fun b v => ρo (Φ b v)) = (IF.A p₁' (u : ℂ)).H y Φ)
    (hcoef : ∀ X ∈ Xs, ∀ J, GoodJAt g hnn hM1 F H hk hρ r r' (d7Pull F (k + 1) (OmegaCube H (k + 1)))
      (σ X) X J → ∀ ψhat : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ,
      (∀ b ∈ locUnits g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' (σ X) J),
        vn (ψhat b) < rψ) →
      oldCoefLocAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ (rotM ρo ψ) z (rotH0 ρo h₀) a₁ ν β
          p₁ δ ρc ρ r r' rep A X (rotM ρo ψ') (ρo hv) (rotG ρo gx) J (rotSite (rotCMat ρo) ψhat) =
        oldCoefLocAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A
          X ψ' hv gx J ψhat) :
    oldBAtAt (glob := glob) (σ := σ) g hnn hM1 F H hk hk1 hρ (rotM ρo ψ) z (rotH0 ρo h₀) a₁ ν β p₁ δ
        inner cb hp (IF.at p₂') (rotSite (rotCMat ρo) ψout) rψ ρc ρ r r' rep A Xs (rotM ρo ψ')
        (ρo hv) (rotG ρo gx) Y =
      oldBAtAt (glob := glob) (σ := σ) g hnn hM1 F H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb hp
        (IF.at p₁') ψout rψ ρc ρ r r' rep A Xs ψ' hv gx Y := by
  have := (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).isProbabilityMeasure_cubeMeasure
    inner cb hp
  have hf1 := isProbabilityMeasure_fluctMeasure1 N hp
  let ee : Rn N ≃ᵐ Rn N := ρo.toHomeomorph.toMeasurableEquiv
  have hee : MeasurePreserving ee (fluctMeasure1 N p₁) (fluctMeasure1 N p₁) :=
    ⟨ee.measurable, map_fluctMeasure1_isometry N p₁ ρo⟩
  let E : ∀ b, ({u : inner // cb u = b} → Rn N) ≃ᵐ ({u : inner // cb u = b} → Rn N) := fun b =>
    MeasurableEquiv.piCongrRight (fun _ : {u : inner // cb u = b} => ee)
  have hE : ∀ b, MeasurePreserving (E b)
      ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).cubeMeasure inner cb b)
      ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).cubeMeasure inner cb b) := fun b =>
    measurePreserving_pi (fun _ : {u : inner // cb u = b} => fluctMeasure1 N p₁)
      (fun _ => fluctMeasure1 N p₁) (fun _ => hee)
  have hRv : ∀ v, vn (rotCMat ρo *ᵥ v) = vn v :=
    vn_rot (isRealOrth_ofReal (rotMat_transpose_mul ρo))
  unfold oldBAtAt
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun X hX =>
    Finset.sum_congr rfl fun V _ => ?_
  unfold oldClusterSiteAt
  refine markTerm_equiv _ E hE (Q := Set.univ) (ae_of_all _ fun _ => Set.mem_univ _)
    (IF.at p₁').A (IF.at p₂').A V _ _ T (fun u y Φ _ => hI u y Φ) fun Φ _ => ?_
  unfold oldMarkSiteAt
  refine Finset.sum_congr rfl fun J hJ => ?_
  obtain ⟨-, hJg, -⟩ := (mem_famAtAt g hnn hM1).1 hJ
  unfold oldMarkLFAt
  exact HoleStep.markOf_rot (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ) inner cb _ rψ ρo
    (rotCMat ρo) (rotCMat_mulVec_ofReal ρo) hRv rfl (hcoef X hX J hJg) Φ

end D7Old

end Balaban.RootFSpine
