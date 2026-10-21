/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStepPointLocal

/-!
# The decoupled background at two parameter vectors agrees on the hull of a seed

`Fluctuation.HoleStep.decBg_agree_of_hull` compares the decoupled objects of the pair `(coverOf G′, G′)`
at two vectors on the hull `actHull` of the active closure of a seed; the hull is empty if no centre
near the seed is active, so the seed itself must be covered by active boxes.  Here the hull is
replaced by `T = actHull ∪ nbhdSup (L^{k+1}) seed`, which always contains the seed, and the statement is
for an arbitrary generating set, weights and datum (no `HoleStep`).  The dichotomy, row, inner-centre
and residue hypotheses of `Dec2.decBg_component_cross` hold for `T`: an active centre whose box comes
within `D` of the seed is in the closure, hence its box is in the hull; one that does not, misses the
neighbourhood of the seed.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField

section Seed

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- The hull of a seed: the hull of the active closure together with the `L^{k+1}`-neighbourhood
of the seed. -/
noncomputable def seedHull (C : DecCover d L N₁ m₁ (k + 1)) (D : ℕ)
    (s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ)
    (seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))) :
    Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) :=
  actHull C D s seed ∪ nbhdSup (L ^ (k + 1)) seed

theorem seed_subset_seedHull (C : DecCover d L N₁ m₁ (k + 1)) (D : ℕ)
    (s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ)
    (seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))) :
    seed ⊆ seedHull C D s seed := fun _ hy =>
  Finset.mem_union_right _ (subset_nbhdSup _ _ hy)

variable {C : DecCover d L N₁ m₁ (k + 1)}

/-- An active centre whose box comes within `D` of the seed belongs to the closure. -/
theorem mem_actComp_of_near_seed {D : ℕ} {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    {seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hq : ActC C s q)
    {x z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ intBox q) (hz : z ∈ seed)
    (hxz : supDist x z ≤ D) : q ∈ actComp C D s seed :=
  mem_actComp.2 ⟨hq.1, q, hq, ⟨x, hx, z, hz, hxz⟩, Relation.ReflTransGen.refl⟩

variable {ϱ' : ℝ} {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}

/-- **The dichotomy for the seed hull.** -/
theorem subI_or_disjI_seedHull {D : ℕ} (hD : 2 * L ^ (k + 1) ≤ D)
    {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    {seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hq : ActC C s q) :
    SubI H (intBox q) (seedHull C D s seed) ∨ DisjI H (intBox q) (seedHull C D s seed) := by
  classical
  by_cases hnear : ∃ x ∈ intBox q, ∃ z ∈ seed, supDist x z ≤ D
  · obtain ⟨x, hx, z, hz, hxz⟩ := hnear
    refine Or.inl fun y hy => Finset.mem_union_left _ ?_
    exact intBox_subset_actHull (mem_actComp_of_near_seed hq hx hz hxz) hy
  · have hD0 : 0 + 2 * L ^ (k + 1) ≤ D := by omega
    rcases actC_dich hD0 (seed := seed) hq with h | h
    · exact Or.inl fun y hy => Finset.mem_union_left _ (h y hy)
    · refine Or.inr fun y hy hyT => ?_
      rcases Finset.mem_union.1 hyT with hyT | hyT
      · have := h y hy y hyT
        rw [supDist_self] at this
        exact lt_irrefl 0 this
      · obtain ⟨z, hz, hzy⟩ := mem_nbhdSup.1 hyT
        refine hnear ⟨y, hy, z, hz, ?_⟩
        rw [supDist_comm]
        have : L ^ (k + 1) ≤ D := by omega
        omega

/-- **The row hypothesis for the seed hull.** -/
theorem mem_seedHull_of_nbhd {D : ℕ} (hD : L ^ (k + 1) + 2 * L ^ (k + 1) ≤ D)
    {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    {seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hq : ActC C s q)
    {x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ intBox q)
    (hxY : x ∈ nbhdSup (L ^ (k + 1)) (seedHull C D s seed)) : x ∈ seedHull C D s seed := by
  classical
  obtain ⟨y, hyT, hyx⟩ := mem_nbhdSup.1 hxY
  rcases Finset.mem_union.1 hyT with hyT | hyT
  · exact Finset.mem_union_left _ (mem_actHull_of_nbhd hD hq hx hyT hyx)
  · obtain ⟨z, hz, hzy⟩ := mem_nbhdSup.1 hyT
    refine Finset.mem_union_left _ (intBox_subset_actHull
      (mem_actComp_of_near_seed hq hx hz ?_) hx)
    have h1 := supDist_triangle z y x
    rw [supDist_comm x z]
    omega

/-- **An inner active centre of the seed hull lies in the closure of a larger vector.** -/
theorem mem_actComp_of_inner_seed {D : ℕ} (hD : 2 * L ^ (k + 1) ≤ D)
    {t smax : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    {seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    (ht : ∀ q, ActC C t q → ActC C smax q) {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hqinn : q ∈ C.cubeIdx) (hsub : SubI H (intBox q) (seedHull C D t seed))
    (hbase : q.2 ∈ H.Ω 1) (hne : C.sProd t q ≠ 0) : q ∈ actComp C D smax seed := by
  classical
  have hq2T := hsub ⟨q.2, hbase⟩ (Localization.base_mem_intBox q)
  rcases Finset.mem_union.1 hq2T with h | h
  · have hD0 : 0 + 2 * L ^ (k + 1) ≤ D := by omega
    exact actComp_mono ht seed (mem_actComp_of_near hD0 ⟨hqinn, hne⟩
      (Localization.base_mem_intBox q) h (by rw [supDist_self]))
  · have h' : q.2 ∈ nbhdSup (L ^ (k + 1)) seed := h
    obtain ⟨z, hz, hzy⟩ := mem_nbhdSup.1 h'
    refine mem_actComp_of_near_seed (ht q ⟨hqinn, hne⟩) (Localization.base_mem_intBox q) hz ?_
    rw [supDist_comm]
    have : L ^ (k + 1) ≤ D := by omega
    omega

end Seed

section Agree

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ) (ν : ℝ) (D' : BgData G N)

/-- **Core: the decoupled backgrounds and multipliers of one pair at two vectors agree on `T`/`Y`.**
For an arbitrary set `T ⊆ Y` satisfying the dichotomy, row, inner-centre and residue hypotheses of
`Dec2.decBg_component_cross` for the pair compared with itself, the multipliers at `v` and `v'`
agree on `T` and the fields on `Y`.  `decBg_agree_of_seedHull` is the instance `T = seedHull`. -/
theorem decBg_agree_core {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf G) G a ν Kc Cx)
    (HB : BgHyp d L (k + 1) ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {v v' : Dec2.DecParams (coverOf G)}
    (hv : ∀ P, ‖v P‖ ≤ Real.exp κ) (hv' : ∀ P, ‖v' P‖ ≤ Real.exp κ)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hD' : InDomainC G ν δ ε D')
    {T Y : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} (hTY : T ⊆ Y)
    (hdich : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd (Dec2.extS _ v) q ≠ 0 →
      SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    (hdich' : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd (Dec2.extS _ v') q ≠ 0 →
      SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    (hrow : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd (Dec2.extS _ v) q ≠ 0 →
      ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hrow' : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd (Dec2.extS _ v') q ≠ 0 →
      ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hin : ∀ q ∈ Dec2.innerCentres (coverOf G) G T, (coverOf G).sProd (Dec2.extS _ v) q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf G) G T ∧
        (coverOf G).sProd (Dec2.extS _ v') q = (coverOf G).sProd (Dec2.extS _ v) q ∧
        (∀ x ∈ intBox q, ∀ y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
            ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ G.layer n ↔ y ∈ G.layer n)) ∧
        (∀ x ∈ intBox q, (coverOf G).chi q x = (coverOf G).chi q x))
    (hin' : ∀ q ∈ Dec2.innerCentres (coverOf G) G T, (coverOf G).sProd (Dec2.extS _ v') q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf G) G T ∧ (coverOf G).sProd (Dec2.extS _ v) q ≠ 0)
    (hres : ∀ x ∈ T, x ∈ G.Ω 1 → ∀ y ∈ resSites G x, y ∈ G.Ω 1 ∧ y ∈ Y) :
    (∀ (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) (hx : x ∈ G.Ω 1), x ∈ T →
        Dec2.decBgMult (coverOf G) G a ν (rho4 d L N BG κ) v' D' ⟨x, hx⟩ =
          Dec2.decBgMult (coverOf G) G a ν (rho4 d L N BG κ) v D' ⟨x, hx⟩) ∧
      ∀ (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ G.Ω 1), y ∈ Y → ∀ i : Fin N,
        Dec2.decBgField (coverOf G) G a ν (rho4 d L N BG κ) v' D' (⟨y, hy⟩, i) =
          Dec2.decBgField (coverOf G) G a ν (rho4 d L N BG κ) v D' (⟨y, hy⟩, i) := by
  classical
  obtain ⟨φ, α, hsol, huniq, -⟩ := Dec2.i4b_exists_unique hS Sb HB hκ hM hv hδ0 hδε hε hδ hνε hD'
  obtain ⟨φ', α', hsol', huniq', -⟩ :=
    Dec2.i4b_exists_unique hS Sb HB hκ hM hv' hδ0 hδε hε hδ hνε hD'
  obtain ⟨hφ, hα⟩ := Dec2.decBg_eq hsol huniq
  obtain ⟨hφ', hα'⟩ := Dec2.decBg_eq hsol' huniq'
  rw [hφ, hα, hφ', hα']
  have h := Dec2.decBg_component_cross (C := coverOf G) (C' := coverOf G) (H := G)
    (H' := G) (s := v) (s' := v') (D := D') (D' := D') (T := T) (Y := Y)
    hS Sb Sb HB HB hκ hM hv hv' hδ0 hδε hε hδ hνε hδ0 hδε hε hδ hνε hD' hD' hTY
    (fun _ _ _ _ _ => Iff.rfl) hdich hdich' hrow hrow' hin hin' hres
    (fun _ _ _ _ _ _ _ _ _ _ => Iff.rfl) (fun _ _ _ _ _ => ⟨rfl, rfl⟩) hsol hsol'
  exact ⟨fun x hx hxT => h.1 x hx hx hxT, fun y hy hyY i => h.2 y hy hy hyY i⟩

/-- **The decoupled backgrounds and multipliers of the pair `(coverOf G, G)` at two vectors agree
on the hull of a seed**, which contains the seed (P3 (4.47), Theorem I-4b (iv), compared with
itself).  Let `v`, `v'` be vectors with `|v_P|, |v'_P| ≤ e^κ`, whose active centres are active for
`smax`, with the same factors on the active closure of `smax` from the seed.  For a datum of
Theorem I-4b whose seed hull has depth `2 L^{k+1}` inside `Ω₁`, the multipliers agree on the seed
hull and the fields on its `L^{k+1}`-neighbourhood. -/
theorem decBg_agree_of_seedHull {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf G) G a ν Kc Cx)
    (HB : BgHyp d L (k + 1) ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {v v' smax : Dec2.DecParams (coverOf G)}
    (hv : ∀ P, ‖v P‖ ≤ Real.exp κ) (hv' : ∀ P, ‖v' P‖ ≤ Real.exp κ)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hD' : InDomainC G ν δ ε D')
    {D : ℕ} (hDD : L ^ (k + 1) + 2 * L ^ (k + 1) ≤ D)
    (seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
    (hsup : ∀ q, ActC (coverOf G) (Dec2.extS _ v) q → ActC (coverOf G) (Dec2.extS _ smax) q)
    (hsup' : ∀ q, ActC (coverOf G) (Dec2.extS _ v') q → ActC (coverOf G) (Dec2.extS _ smax) q)
    (hcomp : ∀ q ∈ actComp (coverOf G) D (Dec2.extS _ smax) seed,
      (coverOf G).sProd (Dec2.extS _ v) q = (coverOf G).sProd (Dec2.extS _ v') q)
    (hdeep : ∀ y ∈ seedHull (coverOf G) D (Dec2.extS _ v) seed,
      ∀ z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1),
        supDist y z ≤ 2 * L ^ (k + 1) → z ∈ G.Ω 1) :
    (∀ (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) (hx : x ∈ G.Ω 1),
        x ∈ seedHull (coverOf G) D (Dec2.extS _ v) seed →
        Dec2.decBgMult (coverOf G) G a ν (rho4 d L N BG κ) v' D' ⟨x, hx⟩ =
          Dec2.decBgMult (coverOf G) G a ν (rho4 d L N BG κ) v D' ⟨x, hx⟩) ∧
      ∀ (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ G.Ω 1),
        y ∈ nbhdSup (L ^ (k + 1)) (seedHull (coverOf G) D (Dec2.extS _ v) seed) →
        ∀ i : Fin N,
        Dec2.decBgField (coverOf G) G a ν (rho4 d L N BG κ) v' D' (⟨y, hy⟩, i) =
          Dec2.decBgField (coverOf G) G a ν (rho4 d L N BG κ) v D' (⟨y, hy⟩, i) := by
  classical
  set Th := seedHull (coverOf G) D (Dec2.extS _ v) seed with hTh
  have hTT' : seedHull (coverOf G) D (Dec2.extS _ v') seed = Th := by
    have := actHull_eq_of_sProd_eq hsup hsup' hcomp (D := D) (seed := seed)
    simp only [seedHull, hTh, this]
  have hD2 : 2 * L ^ (k + 1) ≤ D := by omega
  have hres : ∀ x ∈ Th, x ∈ G.Ω 1 → ∀ y ∈ resSites G x, y ∈ G.Ω 1 ∧
      y ∈ nbhdSup (L ^ (k + 1)) Th := by
    intro x hx _ y hy
    have hd := supDist_le_of_mem_resSites hy
    exact ⟨hdeep x hx y (by omega), mem_nbhdSup.2 ⟨x, hx, hd⟩⟩
  have hdich : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd (Dec2.extS _ v) q ≠ 0 →
      SubI G (intBox q) Th ∨ DisjI G (intBox q) Th :=
    fun q hq hne => subI_or_disjI_seedHull hD2 ⟨hq, hne⟩
  have hdich' : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd (Dec2.extS _ v') q ≠ 0 →
      SubI G (intBox q) Th ∨ DisjI G (intBox q) Th := by
    intro q hq hne
    rw [← hTT']
    exact subI_or_disjI_seedHull hD2 ⟨hq, hne⟩
  have hrow : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd (Dec2.extS _ v) q ≠ 0 →
      ∀ x ∈ nbhdSup (L ^ (k + 1)) Th, x ∈ intBox q → x ∈ Th := by
    intro q hq hne x hxY hxq
    exact mem_seedHull_of_nbhd hDD ⟨hq, hne⟩ hxq hxY
  have hrow' : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd (Dec2.extS _ v') q ≠ 0 →
      ∀ x ∈ nbhdSup (L ^ (k + 1)) Th, x ∈ intBox q → x ∈ Th := by
    intro q hq hne x hxY hxq
    rw [← hTT'] at hxY ⊢
    exact mem_seedHull_of_nbhd hDD ⟨hq, hne⟩ hxq hxY
  have hin : ∀ q ∈ Dec2.innerCentres (coverOf G) G Th,
      (coverOf G).sProd (Dec2.extS _ v) q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf G) G Th ∧
        (coverOf G).sProd (Dec2.extS _ v') q = (coverOf G).sProd (Dec2.extS _ v) q ∧
        (∀ x ∈ intBox q, ∀ y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
            ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ G.layer n ↔ y ∈ G.layer n)) ∧
        (∀ x ∈ intBox q, (coverOf G).chi q x = (coverOf G).chi q x) := by
    intro q hq hne
    have hqC : q ∈ (coverOf G).cubeIdx := (Finset.mem_filter.1 hq).1
    have hsub : SubI G (intBox q) Th := (Finset.mem_filter.1 hq).2
    have hmem := (mem_cubeIdx G).1 (show q ∈ cubeIdx G from hqC)
    have hbase : q.2 ∈ G.Ω 1 := G.layer_subset hmem.1.1 hmem.1.2 hmem.2.1
    exact ⟨hq, (hcomp q (mem_actComp_of_inner_seed hD2 hsup hqC hsub hbase hne)).symm,
      fun _ _ _ _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩
  have hin' : ∀ q ∈ Dec2.innerCentres (coverOf G) G Th,
      (coverOf G).sProd (Dec2.extS _ v') q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf G) G Th ∧ (coverOf G).sProd (Dec2.extS _ v) q ≠ 0 := by
    intro q hq hne
    have hqC : q ∈ (coverOf G).cubeIdx := (Finset.mem_filter.1 hq).1
    have hsub : SubI G (intBox q) Th := (Finset.mem_filter.1 hq).2
    have hmem := (mem_cubeIdx G).1 (show q ∈ cubeIdx G from hqC)
    have hbase : q.2 ∈ G.Ω 1 := G.layer_subset hmem.1.1 hmem.1.2 hmem.2.1
    have hsub' : SubI G (intBox q) (seedHull (coverOf G) D (Dec2.extS _ v') seed) := by
      rw [hTT']; exact hsub
    exact ⟨hq, by rw [hcomp q (mem_actComp_of_inner_seed hD2 hsup' hqC hsub' hbase hne)]; exact hne⟩
  exact decBg_agree_core G a ν D' hS Sb HB hκ hM hv hv' hδ0 hδε hε hδ hνε hD'
    (subset_nbhdSup _ _) hdich hdich' hrow hrow' hin hin' hres

end Agree

end Balaban.LargeField.Base
