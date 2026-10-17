/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidNode
public import Balaban.LargeField.R.RRemovedChainRegroupOut

/-!
# The free nodes of the Gaussian forest as coordinates of the window integral (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, obstruction (2).  `exists_free_equiv`: the free nodes of the
Gaussian forest (the nodes other than the top ones in the tree group, which are fixed roots) are identified
with the coordinates of the regrouping `exists_regroup_shell`: the nodes of scale `≤ m'` with the variables
`x↾Nd`, the top nodes outside `Z₀` and the tree group with the outputs at the blocks of `G₃`, the top nodes
in `Z₀` with the inner outputs `ψ'_m↾Z₀`.  The reindexing is a measure preserving equivalence onto the
product space of the free node values.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section Free

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **The free nodes as coordinates.**  Let `nd` be the set of nodes of the Gaussian forest of a quiet
window (`hnd`), `Fx` the fixed roots (the top nodes in the tree group), `Nd` the set of the variables of `Z`
that are nodes (`hNd`).  The values of the free nodes are in measure preserving bijection with the product
of the outputs at the blocks of `G₃`, the variables `x↾Nd` and the inner outputs at the blocks of `Z₀`;
the bijection reads the value of a node from the corresponding coordinate. -/
theorem exists_free_equiv {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
    {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    (hnd0 : ∀ y : BlockAt S n M K 0, ¬ nd ⟨0, y⟩)
    [Fintype {b : Σ s, BlockAt S n M K s // nd b}]
    (Z0 V2 G3 : Set (BlockAt S n M K (m' + 1))) (P2 : BlockAt S n M K (m' + 1) → Prop)
    (hV2 : ∀ y, y ∈ V2 → P2 y → y ∉ Z0)
    (hZ0g : Z0 ⊆ gaussBlocks (H.localHistory M K (m' + 1) Z) m')
    (hG3 : ∀ y, y ∈ G3 ↔ y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧ y ∉ Z0 ∧
      ¬ (y ∈ V2 ∧ P2 y))
    (Nd : Set ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A) [Fintype ↑Nd]
    (hNd : ∀ p, p ∈ Nd ↔ p.1.1.2.1 = VarKind.large ∧ nd ⟨(p.1.1.1 : ℕ), p.1.1.2.2⟩)
    (Fx : {b : Σ s, BlockAt S n M K s // nd b} → Prop) [DecidablePred Fx]
    (hFx : ∀ i, Fx i ↔ ∃ y : BlockAt S n M K (m' + 1), i.1 = ⟨m' + 1, y⟩ ∧ y ∈ V2 ∧ P2 y) :
    ∃ Eq : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) ×
        ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) ×
          OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) ≃ᵐ
        ({i : {b : Σ s, BlockAt S n M K s // nd b} // ¬ Fx i} → EuclideanSpace ℝ (Fin N)),
      MeasurePreserving Eq
        ((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)).prod
          ((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod
            (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))))
        (Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) ∧
      (∀ v (y : {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ G3})
        (i : {i : {b : Σ s, BlockAt S n M K s // nd b} // ¬ Fx i}),
        i.1.1 = ⟨m' + 1, y.1⟩ → Eq v i = v.1 y) ∧
      (∀ v (y : {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0})
        (i : {i : {b : Σ s, BlockAt S n M K s // nd b} // ¬ Fx i}),
        i.1.1 = ⟨m' + 1, y.1⟩ → Eq v i = v.2.2 y) ∧
      (∀ v (p : ↥Nd) (i : {i : {b : Σ s, BlockAt S n M K s // nd b} // ¬ Fx i}),
        i.1.1 = ⟨(p.1.1.1.1 : ℕ), p.1.1.1.2.2⟩ → Eq v i = VarVal.toEuc (v.2.1 p)) := by
  -- the index set of the coordinates and its bijection with the free nodes
  have hZV : ∀ y, y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' →
      y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) := fun y hy =>
    ZBlk_mem_Vblk hm Z y (gaussBlocks_zblk hm Z hy)
  have hndtop : ∀ y, y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' → nd ⟨m' + 1, y⟩ := by
    intro y hy
    exact (hnd m' y).mpr ⟨hk1, le_rfl, Z, by rw [ancFin_self]; exact Finset.mem_singleton_self _, hy⟩
  have hnFx : ∀ (b : {b : Σ s, BlockAt S n M K s // nd b}) (s : ℕ) (y : BlockAt S n M K s),
      b.1 = ⟨s, y⟩ → s ≠ m' + 1 → ¬ Fx b := by
    intro b s y hb hs hF
    obtain ⟨y', hy', -⟩ := (hFx b).mp hF
    rw [hb] at hy'
    exact hs (Sigma.mk.inj_iff.mp hy').1
  have key : ∃ G : (↥Nd ⊕ ({y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ G3} ⊕
      {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0})) ≃
      {i : {b : Σ s, BlockAt S n M K s // nd b} // ¬ Fx i},
      (∀ p : ↥Nd, (G (Sum.inl p)).1.1 = ⟨(p.1.1.1.1 : ℕ), p.1.1.1.2.2⟩) ∧
      (∀ y : {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ G3},
        (G (Sum.inr (Sum.inl y))).1.1 = ⟨m' + 1, y.1⟩) ∧
      (∀ y : {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0},
        (G (Sum.inr (Sum.inr y))).1.1 = ⟨m' + 1, y.1⟩) := by
    let f : (↥Nd ⊕ ({y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ G3} ⊕
        {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0})) →
        {i : {b : Σ s, BlockAt S n M K s // nd b} // ¬ Fx i} := fun j =>
      match j with
      | Sum.inl p => ⟨⟨⟨(p.1.1.1.1 : ℕ), p.1.1.1.2.2⟩, ((hNd p.1).mp p.2).2⟩,
          hnFx _ _ _ rfl (by have := p.1.1.1.1.2; omega)⟩
      | Sum.inr (Sum.inl y) => ⟨⟨⟨m' + 1, y.1⟩, hndtop y.1 ((hG3 y.1).mp y.2.2).1⟩,
          fun hF => by
            obtain ⟨y', hy', hy2⟩ := (hFx _).mp hF
            have := (Sigma.mk.inj_iff.mp hy').2
            have h3 : y' = y.1 := eq_of_heq this.symm
            subst h3
            exact ((hG3 y.1).mp y.2.2).2.2 hy2⟩
      | Sum.inr (Sum.inr y) => ⟨⟨⟨m' + 1, y.1⟩, hndtop y.1 (hZ0g y.2.2)⟩,
          fun hF => by
            obtain ⟨y', hy', hy2⟩ := (hFx _).mp hF
            have := (Sigma.mk.inj_iff.mp hy').2
            have h3 : y' = y.1 := eq_of_heq this.symm
            subst h3
            exact hV2 y.1 hy2.1 hy2.2 y.2.2⟩
    have hNdinj : ∀ p q : ↥Nd, (⟨(p.1.1.1.1 : ℕ), p.1.1.1.2.2⟩ : Σ s, BlockAt S n M K s) =
        ⟨(q.1.1.1.1 : ℕ), q.1.1.1.2.2⟩ → p = q := by
      rintro ⟨⟨⟨⟨⟨j, hj⟩, κ, y⟩, hmem⟩, hA⟩, hp⟩ ⟨⟨⟨⟨⟨j', hj'⟩, κ', y'⟩, hmem'⟩, hA'⟩, hq'⟩ h
      have h1 := ((hNd _).mp hp).1
      have h2 := ((hNd _).mp hq').1
      simp only at h1 h2 h
      obtain ⟨rfl, hy⟩ := Sigma.mk.inj_iff.mp h
      obtain rfl := eq_of_heq hy
      subst h1
      subst h2
      rfl
    refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · intro a b hab
      have h0 : (f a).1.1 = (f b).1.1 := congrArg (fun i => i.1.1) hab
      rcases a with p | y | y <;> rcases b with q | y' | y'
      · exact congrArg Sum.inl (hNdinj p q h0)
      · exfalso
        have := (Sigma.mk.inj_iff.mp h0).1
        have h5 := p.1.1.1.1.2
        omega
      · exfalso
        have := (Sigma.mk.inj_iff.mp h0).1
        have h5 := p.1.1.1.1.2
        omega
      · exfalso
        have := (Sigma.mk.inj_iff.mp h0).1
        have h5 := q.1.1.1.1.2
        omega
      · have : y.1 = y'.1 := eq_of_heq (Sigma.mk.inj_iff.mp h0).2
        exact congrArg (fun z => Sum.inr (Sum.inl z)) (Subtype.ext this)
      · exfalso
        have : y.1 = y'.1 := eq_of_heq (Sigma.mk.inj_iff.mp h0).2
        exact ((hG3 y.1).mp y.2.2).2.1 (this ▸ y'.2.2)
      · exfalso
        have := (Sigma.mk.inj_iff.mp h0).1
        have h5 := q.1.1.1.1.2
        omega
      · exfalso
        have : y.1 = y'.1 := eq_of_heq (Sigma.mk.inj_iff.mp h0).2
        exact ((hG3 y'.1).mp y'.2.2).2.1 (this ▸ y.2.2)
      · have : y.1 = y'.1 := eq_of_heq (Sigma.mk.inj_iff.mp h0).2
        exact congrArg (fun z => Sum.inr (Sum.inr z)) (Subtype.ext this)
    · rintro ⟨⟨⟨s, y⟩, hn⟩, hF⟩
      rcases s with _ | j
      · exact absurd hn (hnd0 y)
      · obtain ⟨hkj, hjm, c, hc, hy⟩ := (hnd j y).mp hn
        by_cases hj : j = m'
        · subst hj
          rw [ancFin_self] at hc
          have hcZ : c = Z := Finset.mem_singleton.mp hc
          subst hcZ
          by_cases h0 : y ∈ Z0
          · exact ⟨Sum.inr (Sum.inr ⟨y, hZV y hy, h0⟩), rfl⟩
          · by_cases ht : y ∈ V2 ∧ P2 y
            · exact absurd ((hFx _).mpr ⟨y, rfl, ht⟩) hF
            · exact ⟨Sum.inr (Sum.inl ⟨y, hZV y hy, (hG3 y).mpr ⟨hy, h0, ht⟩⟩), rfl⟩
        · have hj' : j + 1 ≤ m' := by omega
          obtain ⟨hb, hA⟩ := node_var geo cs SD KD hkj hj' hm hq hc
            (gaussBlocks_zblk (by omega : j + 1 ≤ K) c hy)
          have hp : (⟨mkVar (H.localHistory M K (m' + 1) Z) (m' + 1) (j + 1) .large y (by omega) hb, hA⟩ :
              ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A) ∈ Nd :=
            (hNd _).mpr ⟨rfl, hn⟩
          exact ⟨Sum.inl ⟨_, hp⟩, rfl⟩
    · intro p; rfl
    · intro y; rfl
    · intro y; rfl
  obtain ⟨G, hGp, hGt, hGz⟩ := key
  -- the free nodes at scales `≥ 1`: the variables of `Nd` are not spins
  have hscale : ∀ (s : ℕ) (y : BlockAt S n M K s), nd ⟨s, y⟩ → s ≠ 0 := by
    intro s y h hs
    subst hs
    exact hnd0 y h
  have hspin : ∀ t : ↥Nd, t.1.1.isSpin = false := by
    intro t
    have h1 := hscale _ _ ((hNd t.1).mp t.2).2
    unfold InternalVars.isSpin
    simp [h1]
  choose eN heN hevN using fun t : ↥Nd => exists_varVal_equiv_euc (N := N) t.1.1.isSpin (hspin t)
  obtain ⟨Ψ1, h1, c1⟩ := exists_reindex_equiv G (β := fun _ => EuclideanSpace ℝ (Fin N))
    (γ := fun _ => EuclideanSpace ℝ (Fin N)) (fun _ => volume) (fun _ => volume)
    (fun _ => MeasurableEquiv.refl _) (fun _ => MeasurePreserving.id _)
  let U : (∀ t : ↥Nd, VarVal N t.1.1.isSpin) ≃ᵐ (↥Nd → EuclideanSpace ℝ (Fin N)) :=
    MeasurableEquiv.piCongrRight fun t => eN t
  have hU : MeasurePreserving U (Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin)
      (Measure.pi fun _ : ↥Nd => (volume : Measure (EuclideanSpace ℝ (Fin N)))) :=
    measurePreserving_pi _ _ (f := fun t => eN t) (fun t => heN t)
  let S1 := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : (↥Nd ⊕ ({y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ G3} ⊕
      {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0})) =>
        EuclideanSpace ℝ (Fin N))
  let S2 := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : ({y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ G3} ⊕
      {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0}) =>
        EuclideanSpace ℝ (Fin N))
  have hS1 := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : (↥Nd ⊕
    ({y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ G3} ⊕
      {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0})) =>
        EuclideanSpace ℝ (Fin N)) (fun _ => volume)
  have hS2 := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : ({y // y ∈
    Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ G3} ⊕
      {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0}) =>
        EuclideanSpace ℝ (Fin N)) (fun _ => volume)
  let sh : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) ×
      ((↥Nd → EuclideanSpace ℝ (Fin N)) ×
        OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) ≃ᵐ
      ((↥Nd → EuclideanSpace ℝ (Fin N)) ×
        (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) ×
          OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) :=
    { toFun := fun p => (p.2.1, (p.1, p.2.2))
      invFun := fun q => (q.2.1, (q.1, q.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      measurable_toFun := (measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
      measurable_invFun := (measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) }
  have hsh := measurePreserving_swap12
    (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3))
    (Measure.pi fun _ : ↥Nd => (volume : Measure (EuclideanSpace ℝ (Fin N))))
    (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))
  let Eq := ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
    (MeasurableEquiv.prodCongr U (MeasurableEquiv.refl _))).trans sh).trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) S2.symm).trans (S1.symm.trans Ψ1.symm))
  have hcoord : ∀ v j, Eq v (G j) = (S1.symm (U v.2.1, S2.symm (v.1, v.2.2))) j := by
    intro v j
    have := c1 (Ψ1.symm (S1.symm (U v.2.1, S2.symm (v.1, v.2.2)))) j
    show Ψ1.symm (S1.symm (U v.2.1, S2.symm (v.1, v.2.2))) (G j) = _
    simpa using this.symm
  refine ⟨Eq, ?_, ?_, ?_, ?_⟩
  · have hA := (MeasurePreserving.id
      (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3))).prod
      (hU.prod (MeasurePreserving.id
        (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))))
    have hB := (MeasurePreserving.id (Measure.pi fun _ : ↥Nd =>
      (volume : Measure (EuclideanSpace ℝ (Fin N))))).prod hS2
    exact (h1.symm Ψ1).comp (hS1.comp (hB.comp (hsh.comp hA)))
  · intro v y i hi
    have hiG : i = G (Sum.inr (Sum.inl y)) := Subtype.ext (Subtype.ext (hi.trans (hGt y).symm))
    rw [hiG, hcoord]
    rfl
  · intro v y i hi
    have hiG : i = G (Sum.inr (Sum.inr y)) := Subtype.ext (Subtype.ext (hi.trans (hGz y).symm))
    rw [hiG, hcoord]
    rfl
  · intro v p i hi
    have hiG : i = G (Sum.inl p) := Subtype.ext (Subtype.ext (hi.trans (hGp p).symm))
    rw [hiG, hcoord]
    exact hevN p _

end Free

end Balaban.LargeField
