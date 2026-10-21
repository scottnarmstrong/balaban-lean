/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldMarks
public import Balaban.Fluctuation.MarkCluster
public import Balaban.Fluctuation.HoleStepPointLocal

/-!
# The cluster terms of the re-expanded old boundary terms (P6 (4.32)–(4.34))

The old part of the boundary terms of the step on a region is the marked cluster expansion of the
measure of the step (FLUCTUATION Theorem 3.4 on the cubes of a region `Ω`, `markTerm`) with the marks
of the old terms (`oldMarkLF`).  The interaction of the measure is a package `I : LocInteraction` on
the block structure `HoleStep.prodSplit` of the measure (the data of Proposition 3.3 on a region:
labels, activities `A(u)`, the constants of Theorem 3.4); that it localizes the exponent of the
measure, and the properties of its activities in the fields, are the named input Proposition 3.3 on a
region (`notes/phase1/SPINE.md`).  The bound and the support of the cluster terms use only the
package.

* `HoleStep.Prop33On`: **Proposition 3.3 on a region at one field** (the core of the named input):
  the interaction localizes the exponent of the measure, holomorphically in the parameter;
* `Xcov`: the sites of the cover torus over an old label `X`;
* `markSite`: **the site of the mark of `(X, J)`**: the `π'_{k+1}`-cubes based at the cells of the
  sites over `X` and of the local set `V(X, J)`; `isPiPrimeUnion_markSite`,
  `locSetXJ_subset_markSite`;
* `GoodJ`: the families `J` whose site is a set of `𝒟_{k+1}` meeting `Ω`;
* `unitRep_mem_of_mem_locUnits`: the unit points of the local pair lie in the local set;
* `oldMarkLF_depOn_markSite`: the mark depends only on the cubes inside its site;
* `oldClusterLF`: **the cluster term `∫₀¹ G*_{X,J}(S) du` of the mark of `(X, J)`** at the set `S`
  of cubes;
* `oldClusterLF_spec`: **its bound** `C_PE fac e^{-rate d^cov(X)} e^{-(κ₁-1)|J_V|}
  e^{(κ_H-κ₀) 𝗱(V)} e^{-κ' d_Ω(S)}` (`V` the site of the mark) and **its support** (it vanishes
  unless the cubes of the site lie in `S`); conditional on the named inputs `H7MixedInnerLoc`,
  `H7MixedDatumLoc` of the local pair.
-/

@[expose] public section

namespace Balaban.Fluctuation.HoleStep

open MeasureTheory Balaban.Localization Balaban.Polymer

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}

/-- **Proposition 3.3 on a region at one field** (FLUCTUATION Proposition 3.3; P5 (3.2), P6 (4.32);
the core of the named input Proposition 3.3 on a region): the interaction `I` on the block structure
`prodSplit` of the measure of the step on the cubes of `Ω` localizes the exponent `W`: its activities
are holomorphic in `u` on an open `𝒰 ⊃ [0, 1]`, and for `s ∈ [0, 1]`, `ν`-a.e.,
`W(s) = ∑_y H_y(s)` at the variables of the cubes. -/
def Prop33On (S : HoleStep d L N₁ m₁ k N ϱ ϱ') (inner : Finset S.U) {m₀ : ℕ}
    {Ω : Set (CTorus d L N₁ m₁ (k + 1))}
    (cb : inner → CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Ω)
    (hp : 0 < S.p₁) (I : LocInteraction (S.prodSplit inner Ω cb hp).Ωb)
    (W : ℝ → (inner → Rn N) → ℂ) : Prop :=
  ∃ 𝒰 : Set ℂ, IsOpen 𝒰 ∧ (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰) ∧
    (∀ y Φ, DifferentiableOn ℂ (fun u => (I.A u).H y Φ) 𝒰) ∧
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂(S.nuIn inner),
      W s x = ∑ y, (I.A (s : ℂ)).H y ((S.prodSplit inner Ω cb hp).restr x)

end Balaban.Fluctuation.HoleStep

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background
  Balaban.Polymer

namespace Balaban.RootFSpine

section Cluster

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **The sites of the cover torus over an old label `X`**: those whose cube of `𝕋_k` lies in `X`. -/
def Xcov {k : ℕ} (X : Finset (Torus S.d (n k))) : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :=
  {x | cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x ∈ X}

/-- **The site of the mark of `(X, J)`**: the `π'_{k+1}`-cubes (side `L · cellSide`) based at the
cells of the sites over `X` and of the local set `V(X, J)` of the coefficient. -/
def markSite (m₀ : ℕ) (H : RegionHistory S n R k0 K) {k : ℕ} (r r' : ℕ)
    (X : Finset (Torus S.d (n k))) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :=
  {x | ∃ y, (y ∈ Xcov g hM1 X ∨ y ∈ locSetXJ g hM1 H r r' X J) ∧
    x ∈ Localization.box (cbase (cellSide S.L m₀ m₁ (k + 1)) y) (S.L * cellSide S.L m₀ m₁ (k + 1))}

omit [NeZero M] in
/-- A site lies in the `π'_{k+1}`-cube based at its cell. -/
theorem mem_box_cbase_cellSide (m₀ : ℕ) {k : ℕ} (y : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    y ∈ Localization.box (cbase (cellSide S.L m₀ m₁ (k + 1)) y) (S.L * cellSide S.L m₀ m₁ (k + 1)) :=
  Localization.box_mono _ (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne S.L)))
    (mem_box_cbase (cellSide_pos m₀ m₁ (k + 1)) y)

omit [NeZero M] in
/-- The local set lies in the site of the mark. -/
theorem locSetXJ_subset_markSite (m₀ : ℕ) (H : RegionHistory S n R k0 K) {k : ℕ} (r r' : ℕ)
    (X : Finset (Torus S.d (n k))) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    locSetXJ g hM1 H r r' X J ⊆ markSite g hM1 m₀ H r r' X J := fun y hy =>
  ⟨y, Or.inr hy, mem_box_cbase_cellSide g m₀ y⟩

omit [NeZero M] in
/-- The sites over `X` lie in the site of the mark. -/
theorem Xcov_subset_markSite (m₀ : ℕ) (H : RegionHistory S n R k0 K) {k : ℕ} (r r' : ℕ)
    (X : Finset (Torus S.d (n k))) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    Xcov g hM1 X ⊆ markSite g hM1 m₀ H r r' X J := fun y hy =>
  ⟨y, Or.inl hy, mem_box_cbase_cellSide g m₀ y⟩

omit [NeZero M] in
/-- **The site of a mark is a union of `π'_{k+1}`-cubes.** -/
theorem isPiPrimeUnion_markSite (m₀ : ℕ) (H : RegionHistory S n R k0 K) {k : ℕ} (r r' : ℕ)
    (X : Finset (Torus S.d (n k))) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    IsPiPrimeUnion m₀ (k + 1) (markSite g hM1 m₀ H r r' X J) := by
  rintro z ⟨y, hy, hz⟩
  exact ⟨cbase (cellSide S.L m₀ m₁ (k + 1)) y, aligned_cbase y, hz, fun z' hz' => ⟨y, hy, hz'⟩⟩

/-- **A family `J` with a good site**: the site of the mark of `(X, J)` is a set of `𝒟_{k+1}`
(nonempty, a union of `π'_{k+1}`-cubes, connected) meeting the region `Ω` of the cubes of the measure. -/
def GoodJ (m₀ : ℕ) (H : RegionHistory S n R k0 K) {k : ℕ} (r r' : ℕ)
    (Ω : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) (X : Finset (Torus S.d (n k)))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) : Prop :=
  IsDj m₀ (k + 1) (markSite g hM1 m₀ H r r' X J) ∧ (markSite g hM1 m₀ H r r' X J ∩ Ω).Nonempty

omit [NeZero M] in
/-- **The unit points of the local pair lie in the local set**: the representative of a unit point
of `G′ ∩ 𝔹_{k+1}(V)` is a site of the top layer of `𝔹_{k+1}(V)`, which lies in `V`. -/
theorem unitRep_mem_of_mem_locUnits (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {u : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U}
    (hu : u ∈ locUnits g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V) : unitRep u ∈ V := by
  classical
  simp only [locUnits, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  have h := (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).unitRep_mem_top ⟨u.1, hu⟩
  have hlay : (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G'.layer (k + 1) =
      (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G'.Ω (k + 1) := by
    unfold GeneratingSet.layer
    rw [(holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G'.top, Finset.sdiff_empty]
  rw [hlay] at h
  have h' : unitRep u ∈ (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.Ω (k + 1) ∩
      (locB g hM1 V).Ω (k + 1) := h
  exact (SmallField.GsSpec.mem_localB_Ω_top _).1 (Finset.mem_inter.1 h').2 _ rfl

omit [NeZero M] in
open Classical in
/-- **The cubes of the unit points of the local pair lie in the site of the mark**, for an assignment
`cb` of cells to the unit points (`unitRep u ∈ cb u`). -/
theorem image_cb_subset_blocksOf_markSite (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) {m₀ : ℕ} (hN : S.L ^ m₀ ∣ g.c * n (k + 1))
    {Ω : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (inner : Finset (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := g.c * n (k + 1)) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Ω)
    (hcb : ∀ u : inner, unitRep (u : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U) ∈
      Localization.box (cb u).1 (cellSide S.L m₀ m₁ (k + 1)))
    (r r' : ℕ) (X : Finset (Torus S.d (n k)))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    (inner.attach.filter fun u : inner => (u : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁
        δ).U) ∈ locUnits g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' X J)).image cb ⊆
      blocksOf m₀ (k + 1) Ω (markSite g hM1 m₀ H r r' X J) := by
  intro b hb
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hb
  have hV := unitRep_mem_of_mem_locUnits g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ _
    (Finset.mem_filter.1 hu).2
  refine mem_blocksOf.2 fun x hx => ⟨_, Or.inr hV, ?_⟩
  rw [cbase_eq_of_mem_box (cellSide_dvd hN le_rfl) (cb u).2.1 (hcb u)]
  exact Localization.box_mono _ (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne S.L))) hx

/-- **The mark of `(X, J)` depends only on the cubes inside its site.** -/
theorem oldMarkLF_depOn_markSite (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) {m₀ : ℕ} (hN : S.L ^ m₀ ∣ g.c * n (k + 1))
    {Ω : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (inner : Finset (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := g.c * n (k + 1)) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Ω)
    (hcb : ∀ u : inner, unitRep (u : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U) ∈
      Localization.box (cb u).1 (cellSide S.L m₀ m₁ (k + 1)))
    (ψout : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) (rψ : ℝ)
    (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    DepOn (blocksOf m₀ (k + 1) Ω (markSite g hM1 m₀ H r r' X J))
      (oldMarkLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb ψout rψ ρc ρ r r' rep A X ψ' hv
        gx J) :=
  (oldMarkLF_dep g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb ψout rψ ρc ρ r r' rep A X ψ' hv
    gx J).mono (image_cb_subset_blocksOf_markSite g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ hN inner
      cb hcb r r' X J)

/-- **The cluster term of the mark of `(X, J)`** at the set `T` of cubes of `Ω` (Theorem 3.4,
`markTerm`): the measure of the cubes of the block structure `HoleStep.prodSplit` of the step, the
interaction `I`, the mark `oldMarkLF` with site `markSite`. -/
noncomputable def oldClusterLF (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) {m₀ : ℕ}
    {Ω : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (inner : Finset (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := g.c * n (k + 1)) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Ω) (hp : 0 < p₁)
    (I : LocInteraction ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).prodSplit inner Ω cb
      hp).Ωb)
    (ψout : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) (rψ : ℝ)
    (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := g.c * n (k + 1)) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Ω)) : ℂ :=
  markTerm ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).prodSplit inner Ω cb hp).μ I.A
    (markSite g hM1 m₀ H r r' X J)
    (oldMarkLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb ψout rψ ρc ρ r r' rep A X ψ' hv gx
      J) T

/-- **The bound and the support of the cluster term of the mark of `(X, J)`** (P6 (4.34); Theorem
3.4 with the mark's site added to the labels): under the hypotheses of `norm_oldMarkLF_le`, for a
family `J` with a good site `V = markSite(X, J)` and a region `Ω` of cubes with an assignment `cb`
of the cells of the unit points,
`|∫₀¹ G*_{X,J}(T) du| ≤ C_PE fac e^{-rate d^cov(X)} e^{-(κ₁-1)|J_V|} e^{(κ_H-κ₀) 𝗱(V)} e^{-κ' d_Ω(T)}`
(`C_PE` with the entropy constant `K_c + 1`), and the term vanishes unless the cubes of `V` lie in
`T`; conditional on the named inputs `H7MixedInnerLoc`, `H7MixedDatumLoc`. -/
theorem oldClusterLF_spec {m₀' : ℕ} {Fr : FineSizeFrame S n M K m₀' m₁} {k : ℕ}
    (hk : k + 1 ≤ K) {cs : OpConsts} {P : BudgetConsts} {rep : Rep S n R k0 K M N g cs P k}
    {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))} {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ}
    {hv : EuclideanSpace ℝ (Fin N)}
    (hrec : D7BdryPost Fr hnn (Nat.le_of_succ_le hk) rep Zof aw μs ε ε1 νs fac rate hv)
    {A : LabHist S n R k0 K} (hA : A ∈ rep.hist) {X : Finset (Torus S.d (n k))}
    (hX : X ∈ bdryDomsPost Fr A k (Zof A)) (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) {c BG δb δc κ κ₁ rψ : ℝ}
    (hS : Dec2.DecSpecs S.d S.L (Dec2.mixedKc S.d S.L) (Cchi S.d S.L) c BG)
    (HB : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν)
    (hm₁ : 2 ≤ m₁) (hN : 5 < g.c * n (k + 1)) (hM : 4 * S.L ^ 2 ≤ S.L ^ m₁)
    (hag : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1))
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2) (hκ : 0 < κ)
    (hMc : c * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX S.d S.L (Cchi S.d S.L) * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hδ0 : 0 < δb) (hε : δb ≤ bgC0 S.d S.L N) (hδ : δb ≤ c7 S.d S.L N BG κ)
    (hphi : 3 * δb + K4 S.d S.L N BG κ * δb < 1 / 2)
    (hmarD : K4 S.d S.L N BG κ * δb + 2 * δb +
      K4 S.d S.L N BG κ * δb * (K4 S.d S.L N BG κ * δb + 2 * (1 + 3 * δb)) < δc)
    (hαD : K4 S.d S.L N BG κ * δb < coerciveConst S.d / 2)
    (hsm : δc ^ 2 * smallConstX S.d S.L κ ≤ 1 / 4) (hκ₁ : 1 ≤ κ₁) (hκ₁κ : κ₁ ≤ κ) (ρ r r' : ℕ)
    (hIn : H7MixedInnerLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r aw μs
      ε ε1 νs (hC hv) (Real.exp κ₁) rψ)
    (hDat : H7MixedDatumLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ aw μs ε ε1 νs (hC hv) ν δb)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {Yf : Set (Torus S.d (M * n K * S.L ^ K))} {ψ : MultiFieldC S n M K N}
    {q' : FinFieldC S n M K N} {gx : GIdx S n M K N → ℂ}
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLH A.H M) (k + 1) hk Yf aw μs ε ε1 νs (hC hv) ψ
      (extK q') (fun x i => gx (x, i)))
    (hXY : fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ⊆ Yf)
    (hV : ∀ x ∈ dataSites (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ g hM1 A.H r r' X J)).G', fineOfC g hnn hM1 hk x ∈ Yf)
    {m₀ : ℕ} (hNm : S.L ^ m₀ ∣ g.c * n (k + 1)) {Ω : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (hΩ : IsPiUnion m₀ (k + 1) Ω)
    (inner : Finset (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := g.c * n (k + 1)) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Ω)
    (hcb : ∀ u : inner, unitRep (u : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U) ∈
      Localization.box (cb u).1 (cellSide S.L m₀ m₁ (k + 1)))
    (hp : 0 < p₁)
    (I : LocInteraction ((holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).prodSplit inner Ω
      cb hp).Ωb)
    (ψout : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ)
    (hrψ : 0 < rψ) (hfac : 0 < fac) (hJ : GoodJ g hM1 m₀ A.H r r' Ω X J)
    (T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := g.c * n (k + 1)) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Ω)) :
    ‖oldClusterLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb hp I ψout rψ
        (rho4 S.d S.L N BG κ) ρ r r' rep A X (extK q') hv gx J T‖ ≤
      CPE S.d S.L (I.Kc + 1) I.κH I.κ0 I.κ' *
        (fac * Real.exp (-rate * d7Size Fr A k X) *
          Real.exp (-(κ₁ - 1) * (locCubes g (coverOf (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁
            ν β p₁ δ (locSetXJ g hM1 A.H r r' X J)).G') J).card)) *
        Real.exp ((I.κH - I.κ0) * treeLenCovOne (d := S.d) (L := S.L) (N₁ := g.c * n (k + 1))
          (m₁ := m₁) (K := k + 1) m₀ (k + 1) (markSite g hM1 m₀ A.H r r' X J)) *
        Real.exp (-I.κ' * dExt T) ∧
      (¬ blocksOf m₀ (k + 1) Ω (markSite g hM1 m₀ A.H r r' X J) ⊆ T →
        oldClusterLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb hp I ψout rψ
          (rho4 S.d S.L N BG κ) ρ r r' rep A X (extK q') hv gx J T = 0) := by
  obtain ⟨hVd, hm⟩ := hJ
  exact markTerm_spec_of_norm_le I _ hNm le_rfl hΩ _ hVd hm _
    (measurable_oldMarkLF g hnn hM1 hk hrec hA hX hk1 hρ z h₀ a₁ ν β p₁ δ hS HB hm₁ hN hM hag ha₁ ha₂ hκ
      hMc hMX hδ0 hε hδ hphi hmarD hαD hsm hκ₁ hκ₁κ ρ r r' hIn hDat J htgt hXY hV inner cb ψout)
    (oldMarkLF_depOn_markSite g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ hNm inner cb hcb ψout rψ
      (rho4 S.d S.L N BG κ) ρ r r' rep A X (extK q') hv gx J)
    (by positivity)
    (norm_oldMarkLF_le g hnn hM1 hk hrec hA hX hk1 hρ z h₀ a₁ ν β p₁ δ hS HB hm₁ hN hM hag ha₁ ha₂ hκ hMc
      hMX hδ0 hε hδ hphi hmarD hαD hsm hκ₁ hκ₁κ ρ r r' hIn hDat J htgt hXY hV inner cb ψout hrψ) T

end Cluster

end Balaban.RootFSpine
