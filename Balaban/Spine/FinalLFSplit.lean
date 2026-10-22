/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalRepOne
import Mathlib.Tactic.Ring

/-!
# The large-field last integral: the histories and the regional integral (A6-4, piece (i))

The first piece of the large-field half of the last integral (`notes/phase1/A64-DESIGN.md` §1.1–1.2;
P7 (4.1)–(4.2)).

* `lfHist`: the histories of the large-field half, those of the representation with a nonempty
  region `Z_k(𝔸)` and no removal record.
* `integral_eq_sum_lfHist` (P7 (4.1), ruling R12, `n₀ = 1`): for a density with the form (D1) and a
  complete set of histories, `∫ ρ = ∫ sfFactor2(univ) + Σ_{𝔸 ∈ lfHist} lastHistInt 𝔸`; the
  histories with a removal record carry the zero term, and exactly one removal-free history has an
  empty region (`card_remFree_empty_eq_one`).
* `lfGlue Ω ψo ψi`: the field of the `k`-blocks equal to `ψi` on the blocks of a set `Ω` and to `ψo`
  off it.
* `gWeight_congr`: the kernels of the components read `ψ_k` only on the blocks of `V = (Z^≈)^∼`
  (`Vblk`; by type: the output variables are `OutT = OutConfig N (Vblk R a k)`).
* `integral_gOp_eq_split`: for a set `Ω` of `k`-blocks that no kernel reads,
  `∫ dψ 𝕋[F(ψ)](ψ) = ∫ dψ_out ∫ dμ(x) w(ψ_out, x) ∫ dψ_in F(ψ_out ⊔ ψ_in)(x)` (Fubini), under the
  integrability of the weighted integrand on the product of `ψ` and the internal variables.
* `lfRegInt`: the regional integral `I_𝔸(ψ_out, x) = ∫ dψ_in e^{ℬ^{(k)}(𝔸)} sfFactor2(Z^c_k)` of a
  history over the fields of the blocks of `Ω` (P7 (4.2): the boundary terms of the history read the
  field on their whole domain, which may reach any block of `Z^c_k`, so they stay in the integrand);
  `lastHistInt_eq_regional_of_integrable`: the last integral of a removal-free history is
  `∫ dψ_out ∫ dμ(x) w(ψ_out, x) I_𝔸(ψ_out, x)`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  RegionHistory

namespace Balaban.RootFSpine

section Hist

open Classical

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

/-- **The histories of the large-field half**: the histories of a set with a nonempty region
`Z_k(𝔸)` and no removal record `Rem_j`, `j ≤ k` (ruling R12). -/
noncomputable def lfHist (hist : Finset (LabHist S n R k0 K)) (k : ℕ) :
    Finset (LabHist S n R k0 K) :=
  hist.filter fun A => ¬ lastRegion A k = ∅ ∧ ∀ j, j ≤ k → A.H.rem j = ∅

omit [NeZero S.L] in
theorem mem_lfHist {hist : Finset (LabHist S n R k0 K)} {A : LabHist S n R k0 K} :
    A ∈ lfHist hist k ↔ A ∈ hist ∧ ¬ lastRegion A k = ∅ ∧ ∀ j, j ≤ k → A.H.rem j = ∅ := by
  unfold lfHist
  rw [Finset.mem_filter]

variable {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
  (rep : Rep S n R k0 K M N geo cs P k) (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)

/-- **The last integral by histories** (P7 (4.1); ruling R12, `n₀ = 1`): for a density with the
form (D1) of the second version and a complete set of histories, if the terms of the histories are
integrable in `ψ_k`, then `∫ ρ dψ_k` is the integral of the small-field factor on the whole torus
plus the last integrals of the histories of the large-field half (`lfHist`). -/
theorem integral_eq_sum_lfHist
    {ρ : (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) → (GIdx S n M K N → ℂ) → ℂ}
    (hD : D1Form2 C vc rep hv ρ) (hg : g ∈ l1Ball (GIdx S n M K N))
    (hint : ∀ A ∈ rep.hist, Integrable (fun ψk => postTerm2 C vc rep A ψk hv g))
    (hc : IsComplete k (k + 1) rep.hist) (A0 : LabHist S n R k0 K) :
    ∫ ψk, ρ ψk g = (∫ ψk, sfFactor2 C vc Set.univ ψk hv g) +
      ∑ A ∈ lfHist rep.hist k, lastHistInt C vc rep hv g A := by
  have h1 : ∀ ψk, ρ ψk g = ∑ A ∈ rep.hist, postTerm2 C vc rep A ψk hv g :=
    fun ψk => (hD ψk g hg).2
  simp_rw [h1]
  rw [integral_finsetSum _ hint]
  change ∑ A ∈ rep.hist, lastHistInt C vc rep hv g A = _
  rw [← Finset.sum_filter_add_sum_filter_not rep.hist (fun A => lastRegion A k = ∅)]
  have h0 : ∑ A ∈ rep.hist.filter (fun A => lastRegion A k = ∅), lastHistInt C vc rep hv g A =
      ∫ ψk, sfFactor2 C vc Set.univ ψk hv g :=
    lastRegionWeight_empty_of_card_eq_one C vc rep hv g (card_remFree_empty_eq_one C.hkK hc A0)
  rw [h0]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (rep.hist.filter (fun A => ¬ lastRegion A k = ∅))
    (fun A => ∀ j, j ≤ k → A.H.rem j = ∅)]
  rw [Finset.sum_eq_zero (s := (rep.hist.filter (fun A => ¬ lastRegion A k = ∅)).filter
    (fun A => ¬ ∀ j, j ≤ k → A.H.rem j = ∅)) (fun A hA =>
      lastHistInt_of_rem C vc rep hv g A (Finset.mem_filter.1 hA).2), add_zero,
    Finset.filter_filter]
  rfl

end Hist

section Split

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {k : ℕ}

/-- **The field glued from the fields on a set of blocks and off it**: `ψi` on the blocks of `Ω`,
`ψo` off `Ω`. -/
def lfGlue (Ω : Set (BlockAt S n M K k)) [DecidablePred (· ∈ Ω)]
    (ψo : {y : BlockAt S n M K k // y ∉ Ω} → EuclideanSpace ℝ (Fin N))
    (ψi : {y : BlockAt S n M K k // y ∈ Ω} → EuclideanSpace ℝ (Fin N)) :
    BlockAt S n M K k → EuclideanSpace ℝ (Fin N) :=
  fun y => if h : y ∈ Ω then ψi ⟨y, h⟩ else ψo ⟨y, h⟩

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem lfGlue_of_not_mem {Ω : Set (BlockAt S n M K k)} [DecidablePred (· ∈ Ω)]
    (ψo : {y : BlockAt S n M K k // y ∉ Ω} → EuclideanSpace ℝ (Fin N))
    (ψi : {y : BlockAt S n M K k // y ∈ Ω} → EuclideanSpace ℝ (Fin N)) {y : BlockAt S n M K k}
    (hy : y ∉ Ω) : lfGlue Ω ψo ψi y = ψo ⟨y, hy⟩ := by
  simp [lfGlue, hy]

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- The glued field is the inverse of the splitting of a field by `Ω`
(`MeasurableEquiv.piEquivPiSubtypeProd`). -/
theorem lfGlue_eq_symm (Ω : Set (BlockAt S n M K k)) [DecidablePred (· ∈ Ω)]
    (ψo : {y : BlockAt S n M K k // y ∉ Ω} → EuclideanSpace ℝ (Fin N))
    (ψi : {y : BlockAt S n M K k // y ∈ Ω} → EuclideanSpace ℝ (Fin N)) :
    lfGlue Ω ψo ψi = (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : BlockAt S n M K k =>
      EuclideanSpace ℝ (Fin N)) (· ∈ Ω)).symm (ψi, ψo) := by
  funext y
  by_cases hy : y ∈ Ω <;> simp [lfGlue, hy, MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd]

variable {ι : Type} [Fintype ι] (a : ι → LocalHistory S n M K) (P : ∀ i, OpPkg N R (a i) k)

/-- **The kernels read the field only on the blocks of `V`**: two fields that agree on the blocks
`Vblk` of every component give the same product kernel. -/
theorem gWeight_congr {ψ ψ' : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)}
    (h : ∀ i, ∀ y ∈ Vblk R (a i) k, ψ y = ψ' y) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (x : GCfg a k P) :
    gWeight a k P ψ hv g x = gWeight a k P ψ' hv g x := by
  unfold gWeight
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : outOf R (a i) k ψ = outOf R (a i) k ψ' := funext fun y => h i y.1 y.2
  rw [e]

/-- **Fubini for the global operator at a set of blocks that no kernel reads**: for a set `Ω` of
`k`-blocks disjoint from the blocks `V` of the components,
`∫ dψ 𝕋[F(ψ)](ψ) = ∫ dψ_out ∫ dμ(x) w(ψ_out, x) ∫ dψ_in F(ψ_out ⊔ ψ_in)(x)`, under the integrability
of `(ψ, x) ↦ w(ψ, x) F(ψ)(x)` on the product of the fields of the `k`-blocks and the internal
variables. -/
theorem integral_gOp_eq_split (Ω : Set (BlockAt S n M K k)) [DecidablePred (· ∈ Ω)]
    (hΩ : ∀ i, ∀ y ∈ Ω, y ∉ Vblk R (a i) k) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ)
    (F : (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) → GCfg a k P → ℂ)
    (hint : Integrable (fun q : (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) × GCfg a k P =>
      gWeight a k P q.1 hv g q.2 * F q.1 q.2) (volume.prod (gMeasure a k P))) :
    ∫ ψ, gOp a k P ψ hv g (F ψ) =
      ∫ ψo : {y : BlockAt S n M K k // y ∉ Ω} → EuclideanSpace ℝ (Fin N),
        ∫ x, gWeight a k P (lfGlue Ω ψo 0) hv g x *
          (∫ ψi : {y : BlockAt S n M K k // y ∈ Ω} → EuclideanSpace ℝ (Fin N),
            F (lfGlue Ω ψo ψi) x) ∂gMeasure a k P := by
  have : SigmaFinite (gMeasure a k P) := by unfold gMeasure; infer_instance
  have he : MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : BlockAt S n M K k => EuclideanSpace ℝ (Fin N)) (· ∈ Ω)) :=
    volume_preserving_piEquivPiSubtypeProd _ _
  -- the rearrangement `(ψo, (x, ψi)) ↦ (ψo ⊔ ψi, x)`
  let Φ : ({y : BlockAt S n M K k // y ∉ Ω} → EuclideanSpace ℝ (Fin N)) ×
      (GCfg a k P × ({y : BlockAt S n M K k // y ∈ Ω} → EuclideanSpace ℝ (Fin N)))
      ≃ᵐ (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) × GCfg a k P :=
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) MeasurableEquiv.prodComm).trans
      MeasurableEquiv.prodAssoc.symm).trans
      ((MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl _)).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.piEquivPiSubtypeProd
          (fun _ : BlockAt S n M K k => EuclideanSpace ℝ (Fin N)) (· ∈ Ω)).symm
          (MeasurableEquiv.refl _)))
  have hΦmp : MeasurePreserving Φ (volume.prod ((gMeasure a k P).prod volume))
      (volume.prod (gMeasure a k P)) := by
    have h1 := (MeasurePreserving.id (volume : Measure
        ({y : BlockAt S n M K k // y ∉ Ω} → EuclideanSpace ℝ (Fin N)))).prod
      (Measure.measurePreserving_swap (μ := gMeasure a k P)
        (ν := (volume : Measure ({y : BlockAt S n M K k // y ∈ Ω} → EuclideanSpace ℝ (Fin N)))))
    have h2 := (measurePreserving_prodAssoc
      (volume : Measure ({y : BlockAt S n M K k // y ∉ Ω} → EuclideanSpace ℝ (Fin N)))
      (volume : Measure ({y : BlockAt S n M K k // y ∈ Ω} → EuclideanSpace ℝ (Fin N)))
      (gMeasure a k P)).symm MeasurableEquiv.prodAssoc
    have h3 := (Measure.measurePreserving_swap
      (μ := (volume : Measure ({y : BlockAt S n M K k // y ∉ Ω} → EuclideanSpace ℝ (Fin N))))
      (ν := (volume : Measure ({y : BlockAt S n M K k // y ∈ Ω} → EuclideanSpace ℝ (Fin N))))).prod
      (MeasurePreserving.id (gMeasure a k P))
    have h4 := (he.symm _).prod (MeasurePreserving.id (gMeasure a k P))
    exact (h1.trans h2).trans (h3.trans h4)
  have hΦapp : ∀ ψo x ψi, Φ (ψo, (x, ψi)) = (lfGlue Ω ψo ψi, x) := by
    intro ψo x ψi
    rw [lfGlue_eq_symm]
    rfl
  have hintΦ : Integrable (fun p => gWeight a k P (Φ p).1 hv g (Φ p).2 * F (Φ p).1 (Φ p).2)
      (volume.prod ((gMeasure a k P).prod volume)) :=
    (hΦmp.integrable_comp_emb Φ.measurableEmbedding).2 hint
  calc ∫ ψ, gOp a k P ψ hv g (F ψ)
      = ∫ q, gWeight a k P q.1 hv g q.2 * F q.1 q.2 ∂(volume.prod (gMeasure a k P)) :=
        (integral_prod _ hint).symm
    _ = ∫ p, gWeight a k P (Φ p).1 hv g (Φ p).2 * F (Φ p).1 (Φ p).2
          ∂(volume.prod ((gMeasure a k P).prod volume)) :=
        (hΦmp.integral_comp' (fun q => gWeight a k P q.1 hv g q.2 * F q.1 q.2)).symm
    _ = ∫ ψo, ∫ q, gWeight a k P (Φ (ψo, q)).1 hv g (Φ (ψo, q)).2 * F (Φ (ψo, q)).1 (Φ (ψo, q)).2
          ∂((gMeasure a k P).prod volume) := integral_prod _ hintΦ
    _ = ∫ ψo, ∫ x, ∫ ψi, gWeight a k P (Φ (ψo, (x, ψi))).1 hv g (Φ (ψo, (x, ψi))).2 *
          F (Φ (ψo, (x, ψi))).1 (Φ (ψo, (x, ψi))).2 ∂volume ∂gMeasure a k P := by
        refine integral_congr_ae (hintΦ.prod_right_ae.mono fun ψo hψo => ?_)
        exact integral_prod _ hψo
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ψo => ?_)
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hΦapp]
        have hw : ∀ ψi, gWeight a k P (lfGlue Ω ψo ψi) hv g x =
            gWeight a k P (lfGlue Ω ψo 0) hv g x := fun ψi =>
          gWeight_congr a P (fun i y hy => by
            have hyΩ : y ∉ Ω := fun h => hΩ i y h hy
            rw [lfGlue_of_not_mem _ _ hyΩ, lfGlue_of_not_mem _ _ hyΩ]) hv g x
        simp_rw [hw]
        exact integral_const_mul _ _

end Split

section Regional

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
  (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)

/-- **The regional integral of a history** (P7 (4.2)): for a set `Ω` of `k`-blocks, the outer field
`ψ_out` off `Ω` and the internal variables `x` of the components,
`I_𝔸(ψ_out, x) = ∫ dψ_in e^{ℬ^{(k)}(𝔸)} sfFactor2(Z^c_k)` at the glued field `ψ_out ⊔ ψ_in`
(the integrand `integrand2` of (D1)). -/
noncomputable def lfRegInt (Ω : Set (BlockAt S n M K k)) [DecidablePred (· ∈ Ω)]
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (ψo : {y : BlockAt S n M K k // y ∉ Ω} → EuclideanSpace ℝ (Fin N))
    (x : GCfg (fun c : PostComp A k => A.H.localHistory M K k c.1) k
      (postOp geo cs rep.SD rep.KD A C.hkK)) : ℂ :=
  ∫ ψi : {y : BlockAt S n M K k // y ∈ Ω} → EuclideanSpace ℝ (Fin N),
    integrand2 (fun c : PostComp A k => A.H.localHistory M K k c.1)
      (postOp geo cs rep.SD rep.KD A C.hkK)
      (fun c => fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k)))) C vc rep A
      (A.H.step k).Z (lfGlue Ω ψo ψi) hv g x

/-- **The last integral of a removal-free history through the regional integral** (P7 (4.2)):
for a set `Ω` of `k`-blocks that no kernel of the history reads,
`lastHistInt 𝔸 = ∫ dψ_out ∫ dμ(x) w(ψ_out, x) I_𝔸(ψ_out, x)`, under the integrability of the
weighted integrand (`postWeighted2`) on the product of `ψ_k` and the internal variables. -/
theorem lastHistInt_eq_regional_of_integrable (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (hrem : ∀ j, j ≤ k → A.H.rem j = ∅)
    (Ω : Set (BlockAt S n M K k)) [DecidablePred (· ∈ Ω)]
    (hΩ : ∀ c : PostComp A k, ∀ y ∈ Ω, y ∉ Vblk R (A.H.localHistory M K k c.1) k)
    (hint : Integrable (fun q : (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) ×
        GCfg (fun c : PostComp A k => A.H.localHistory M K k c.1) k
          (postOp geo cs rep.SD rep.KD A C.hkK) =>
      gWeight (fun c : PostComp A k => A.H.localHistory M K k c.1) k
          (postOp geo cs rep.SD rep.KD A C.hkK) q.1 hv g q.2 *
        integrand2 (fun c : PostComp A k => A.H.localHistory M K k c.1)
          (postOp geo cs rep.SD rep.KD A C.hkK)
          (fun c => fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k)))) C vc rep A
          (A.H.step k).Z q.1 hv g q.2)
      (volume.prod (gMeasure (fun c : PostComp A k => A.H.localHistory M K k c.1) k
        (postOp geo cs rep.SD rep.KD A C.hkK)))) :
    lastHistInt C vc rep hv g A =
      ∫ ψo : {y : BlockAt S n M K k // y ∉ Ω} → EuclideanSpace ℝ (Fin N),
        ∫ x, gWeight (fun c : PostComp A k => A.H.localHistory M K k c.1) k
            (postOp geo cs rep.SD rep.KD A C.hkK) (lfGlue Ω ψo 0) hv g x *
          lfRegInt C vc rep A Ω hv g ψo x
          ∂gMeasure (fun c : PostComp A k => A.H.localHistory M K k c.1) k
            (postOp geo cs rep.SD rep.KD A C.hkK) := by
  unfold lastHistInt
  simp_rw [postTerm2_of_remFree C vc rep A _ hv g hrem]
  unfold postTerm2Raw
  exact integral_gOp_eq_split (fun c : PostComp A k => A.H.localHistory M K k c.1)
    (postOp geo cs rep.SD rep.KD A C.hkK) Ω hΩ hv g
    (fun ψ x => integrand2 (fun c : PostComp A k => A.H.localHistory M K k c.1)
      (postOp geo cs rep.SD rep.KD A C.hkK)
      (fun c => fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k)))) C vc rep A
      (A.H.step k).Z ψ hv g x) hint

end Regional

end Balaban.RootFSpine
