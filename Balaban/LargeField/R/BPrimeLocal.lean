/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BPrimePair
public import Balaban.Localization.Decoupled2BackgroundLocal
public import Balaban.Localization.I5Local
public import Balaban.Localization.I5Glue
public import Balaban.Localization.SupportMargin

/-!
# Locality (AE2) of the decoupled background field at labelled cut parameters

For a pair `(C, H)` with `Dec2.CoverLocal` and the labelled parameters `labParams C π lab s`
(`BPrimePair.lean`), the decoupled background field on the root region `X₁` depends only on the
parameters of the cubes of the component `Y(𝒞) = compY lab X₁ 𝒞` and on the data on the
`resDep`-thickening of `Y(𝒞)` (P3 §4, (AE2); Theorem I-4b (iv), `Dec2.i4b_local`).

The label map `π` sends each cube `P` of the cover to the label of a cube containing it
(`hπsub`); every cube of the cover not contained in `X₁` has a label (`hπpar`), and the labels are
off `X₁` (`hoff`).  For the cover of the generating set of the labels `π` is the identity; for a
generating set whose cubes refine those of the labels (the old background of P7 (3.22)) it is the
cube of the label set above.

* `Pset_subset_compY_of_mem`: a cell of the family meeting `Y(𝒞)` lies in `Y(𝒞)`;
* `decBgField_lab_local`: the comparison form of the locality.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis Finset

section Geometry

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ι : Type*}

/-- **A cell of the family meeting the component lies in the component**: if `i ∈ 𝒞` and a point
of `P_i = Pset (lab i)` lies in `Y(𝒞)`, then `P_i ⊆ Y(𝒞)` (a cell is connected). -/
theorem Pset_subset_compY_of_mem (lab : ι → ℕ × CTorus d L N₁ m₁ K)
    {X₁ : Set (CTorus d L N₁ m₁ K)} {Cf : Finset ι} {i : ι} (hi : i ∈ Cf) (hK : (lab i).1 ≤ K)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ Pset m₁ (lab i)) (hxY : x ∈ compY lab X₁ Cf) :
    Pset m₁ (lab i) ⊆ compY lab X₁ Cf := by
  set a : ℕ := L ^ ((lab i).1 + m₁) with ha
  have ha0 : 0 < a := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hdvd : a ∣ (N₁ * L ^ m₁) * L ^ K := by
    have h1 : L ^ ((lab i).1 + m₁) ∣ L ^ (K + m₁) := pow_dvd_pow L (by omega)
    have h2 : (N₁ * L ^ m₁) * L ^ K = N₁ * L ^ (K + m₁) := by rw [pow_add]; ring
    rw [h2]
    exact Dvd.dvd.mul_left h1 N₁
  set b : CTorus d L N₁ m₁ K := cbase a (lab i).2 with hb
  have hboxP : box b a ⊆ Pset m₁ (lab i) := by
    intro z hz
    have hcz : cbase a z = b := cbase_eq_of_mem_box hdvd (aligned_cbase _) hz
    show SameCell (L ^ ((lab i).1 + m₁)) z (lab i).2
    exact (sameCell_iff_cbase_eq ha0).2 (hcz.trans hb)
  have hmem : ∀ z ∈ Pset m₁ (lab i), z ∈ box b a := fun z hz =>
    mem_box_cbase_of_sameCell ha0 fun μ => hz μ
  have hPV : Pset m₁ (lab i) ⊆ patchUnion X₁ (fun j => Pset m₁ (lab j)) Cf := fun z hz =>
    Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, hz⟩)
  intro z hz
  obtain ⟨x0, hx0, hpath⟩ := hxY
  exact ⟨x0, hx0, hpath.trans (chain_in_box b a _ (hboxP.trans hPV) (hmem x hx) (hmem z hz))⟩

end Geometry

section Local

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ}

/-- **(AE2) for the decoupled background field at labelled cut parameters, comparison form.**
Let `𝒞` be a family of labels, `s, s'` supported on `𝒞` with `|s_i|, |s'_i| ≤ e^κ`, agreeing on the
labels whose cell lies in `Y(𝒞) = compY lab X₁ 𝒞`, and `D, D'` two data of `Ψ̃^c(δ, ε)` agreeing on
the dependency sets `resDep` of the sites of `Y(𝒞) ∩ Ω₁`.  Then the decoupled background fields of
`(C, H)` at `labParams C π lab s` (datum `D`) and at `labParams C π lab s'` (datum `D'`) agree on
the root region `X₁`. -/
theorem decBgField_lab_local {c₀ BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c₀ BG)
    (S : Dec2.CoverLocal C H a ν Kc Cx) (hconn : Dec2.HatConn C H) (HB : BgHyp d L K ϱ a ν)
    {κ : ℝ} (hκ : 0 ≤ κ) (hM : c₀ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {ι : Type*} {lab : ι → ℕ × CTorus d L N₁ m₁ K} (hinj : Function.Injective lab)
    (hlabK : ∀ i, (lab i).1 ≤ K) {X₁ : Finset (CTorus d L N₁ m₁ K)}
    (hoff : ∀ i, Disjoint (Pset m₁ (lab i)) (↑X₁ : Set (CTorus d L N₁ m₁ K)))
    {π : ℕ × CTorus d L N₁ m₁ K → ℕ × CTorus d L N₁ m₁ K}
    (hπsub : ∀ P ∈ C.cubeIdx, ∀ x ∈ cubeP P, x ∈ Pset m₁ (π P))
    (hπpar : ∀ P ∈ C.cubeIdx, ¬ cubeP P ⊆ X₁ → ∃ i, lab i = π P)
    {Cf : Finset ι} {s s' : ι → ℂ} (hs0 : ∀ i, i ∉ Cf → s i = 0) (hs0' : ∀ i, i ∉ Cf → s' i = 0)
    (hsb : ∀ i, ‖s i‖ ≤ Real.exp κ) (hsb' : ∀ i, ‖s' i‖ ≤ Real.exp κ)
    (hag : ∀ i ∈ Cf, Pset m₁ (lab i) ⊆ compY lab ↑X₁ Cf → s i = s' i)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D D' : BgData H N}
    (hD : InDomainC H ν δ ε D) (hD' : InDomainC H ν δ ε D')
    (hdata : ∀ x ∈ compY lab ↑X₁ Cf, x ∈ H.Ω 1 → ∀ y ∈ resDep H x,
      D.Ψ y = D'.Ψ y ∧ D.h y = D'.h y) :
    ∀ (y : H.Ω 1), (y : CTorus d L N₁ m₁ K) ∈ X₁ → ∀ i : Fin N,
      Dec2.decBgField C H a ν (rho4 d L N BG κ) (labParams C π lab s) D (y, i) =
        Dec2.decBgField C H a ν (rho4 d L N BG κ) (labParams C π lab s') D' (y, i) := by
  classical
  have hE1 : (1 : ℝ) ≤ Real.exp κ := Real.one_le_exp hκ
  set p := labParams C π lab s with hp
  set p' := labParams C π lab s' with hp'
  have hpb : ∀ P, ‖p P‖ ≤ Real.exp κ := fun P => norm_labS_le lab hE1 hsb _
  have hpb' : ∀ P, ‖p' P‖ ≤ Real.exp κ := fun P => norm_labS_le lab hE1 hsb' _
  -- the decoupled fields
  obtain ⟨φ, α, hI, hu, -⟩ := Dec2.i4b_exists_unique hS S.toCoverBase HB hκ hM hpb hδ0 hδε hε hδ
    hνε hD
  obtain ⟨φ', α', hI', hu', -⟩ := Dec2.i4b_exists_unique hS S.toCoverBase HB hκ hM hpb' hδ0 hδε hε
    hδ hνε hD'
  rw [(Dec2.decBg_eq hI hu).1, (Dec2.decBg_eq hI' hu').1]
  -- notation
  set Yc : Set (CTorus d L N₁ m₁ K) := compY lab ↑X₁ Cf with hYc
  set 𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K) :=
    C.cubeIdx.filter fun P => ∃ i ∈ Cf, lab i = π P with h𝒞
  set Y : Finset (CTorus d L N₁ m₁ K) :=
    ((Vset X₁ 𝒞).filter fun x => x ∈ H.Ω 1).filter (· ∈ Yc) with hY
  have hVsub : ∀ x ∈ Vset X₁ 𝒞, x ∈ patchUnion (↑X₁ : Set (CTorus d L N₁ m₁ K))
      (fun j => Pset m₁ (lab j)) Cf := by
    intro x hx
    unfold Vset at hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 hx
      obtain ⟨hPC, i, hi, hiP⟩ := Finset.mem_filter.1 hP
      refine Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, ?_⟩)
      show x ∈ Pset m₁ (lab i)
      rw [hiP]
      exact hπsub P hPC x hxP
  have hYnn : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ H.Ω 1) Y := by
    refine ⟨Finset.filter_subset _ _, fun x hx y hy hadj => ?_⟩
    rw [hY, Finset.mem_filter] at hx
    rw [hY, Finset.mem_filter]
    refine ⟨hy, compY_closed (c := lab) hx.2 (hVsub y (Finset.mem_filter.1 hy).1) hadj⟩
  have hYsub : ∀ x ∈ Y, x ∈ Yc := fun x hx => (Finset.mem_filter.1 hx).2
  -- the parameters
  have hnotlab : ∀ P ∈ C.cubeIdx, cubeP P ⊆ X₁ → ∀ i, lab i ≠ π P := by
    intro P hPC hsub i hi
    have h2 : P.2 ∈ cubeP P := mem_cubeP.2 (SameCell.refl _ _)
    have hX : P.2 ∈ (↑X₁ : Set (CTorus d L N₁ m₁ K)) := Finset.mem_coe.2 (hsub h2)
    have hPs : P.2 ∈ Pset m₁ (lab i) := by rw [hi]; exact hπsub P hPC _ h2
    exact Set.disjoint_left.1 (hoff i) hPs hX
  have hs1E : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ →
      Dec2.extS C p P = 1 ∧ Dec2.extS C p' P = 1 := by
    intro P hPC hPn
    have hsub : cubeP P ⊆ X₁ := by
      by_contra h
      exact hPn (Finset.mem_filter.2 ⟨hPC, h⟩)
    unfold Dec2.extS
    simp only [hPC, ↓reduceDIte]
    exact ⟨labS_of_not_mem s (hnotlab P hPC hsub), labS_of_not_mem s' (hnotlab P hPC hsub)⟩
  have hs0E : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → Dec2.extS C p P = 0 ∧ Dec2.extS C p' P = 0 := by
    intro P hP hP𝒞
    obtain ⟨hPC, hPn⟩ := Finset.mem_filter.1 hP
    obtain ⟨i, hi⟩ := hπpar P hPC hPn
    have hiC : i ∉ Cf := fun hiC => hP𝒞 (Finset.mem_filter.2 ⟨hPC, i, hiC, hi⟩)
    unfold Dec2.extS
    simp only [hPC, ↓reduceDIte]
    show labS lab s (π P) = 0 ∧ labS lab s' (π P) = 0
    rw [← hi, labS_of_eq hinj, labS_of_eq hinj]
    exact ⟨hs0 i hiC, hs0' i hiC⟩
  have hagE : ∀ P ∈ 𝒞, SubI H (cubeP P) Y → Dec2.extS C p P = Dec2.extS C p' P := by
    intro P hP𝒞 hSub
    obtain ⟨hPC, i, hiC, hi⟩ := Finset.mem_filter.1 hP𝒞
    have h2 : P.2 ∈ cubeP P := mem_cubeP.2 (SameCell.refl _ _)
    have h2Ω : P.2 ∈ H.Ω 1 := S.cubeP_sub P hPC P.2 h2
    have h2Y : P.2 ∈ Yc := hYsub _ (hSub ⟨P.2, h2Ω⟩ h2)
    have h2P : P.2 ∈ Pset m₁ (lab i) := by rw [hi]; exact hπsub P hPC _ h2
    have hsub := Pset_subset_compY_of_mem lab hiC (hlabK i) h2P h2Y
    have hsi := hag i hiC hsub
    unfold Dec2.extS
    simp only [hPC, ↓reduceDIte]
    show labS lab s (π P) = labS lab s' (π P)
    rw [← hi, labS_of_eq hinj, labS_of_eq hinj, hsi]
  have hdata' : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → ∀ y ∈ resDep H (x : CTorus d L N₁ m₁ K),
      D.Ψ y = D'.Ψ y ∧ (y ∈ H.Ω 1 → D.h y = D'.h y) := by
    intro x hx y hy
    have := hdata x (hYsub _ hx) x.2 y hy
    exact ⟨this.1, fun _ => this.2⟩
  obtain ⟨-, key⟩ := Dec2.i4b_local hS S hconn HB hκ hM hpb hpb' hδ0 hδε hε hδ hνε hD hD' hYnn hs1E
    hs0E hagE hdata' hI hI'
  intro y hy i
  refine key y ?_ i
  rw [hY, Finset.mem_filter, Finset.mem_filter]
  refine ⟨⟨Finset.mem_union_left _ hy, y.2⟩, subset_compY _ _ (Finset.mem_coe.2 hy)⟩

end Local

end Balaban.LargeField
