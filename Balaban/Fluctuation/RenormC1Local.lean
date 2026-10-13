/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormBgClassDec
public import Balaban.Fluctuation.RenormDomainParams
public import Balaban.Localization.FootprintFl
public import Balaban.Localization.I5Local
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Locality of the cut functional of `C₁`: read sites and the agreement bridge

Toward the first localization principle `locC1` of `RenormExpInput`.  **`locC1` itself is NOT
proved here**; this file proves the locality inputs only.  It uses no zero class and is independent
of the choice of the generating set beyond the hypotheses stated.

**The read set (`renC1Reads`).**  For a finite set `B` of sites, the density `renC1Site` at `x ∈ B`
reads `Ψ` and `h` at `x`, the field `φ` on the block of `x` (through the block average) and at `x`
and `x + e_μ` (through the bond terms).  `renC1Reads G B` is the union of `B`, the right neighbours
of `B`, and the blocks `G.blk (layerIndex x) x`, `x ∈ B`.  `renC1On_congr` : two triples agreeing
on this set give the same value.  `renC1_root_reads` : for the block of a root `z` it lies in the
root neighbourhood `X₁ = nbhdF` of `levelLocalCover` (the landed block and read-site statements).

**The locality law of the cut functional.**  For the decoupled background `decBgField` at the cut
parameters `extParams (s ∘ renLabelEquiv.symm)`, the functional
`F ((D, ξ), s) = renC1On (blk z) D.Ψ D.h (decBgField …) ξ` satisfies `LocalityAEOn`
(`renC1_local_cut_of`, `renC1_local_cut`) for the agreement relation `RenC1Ag`: equal `ξ` and equal
`(Ψ, h)` on the component `compY C`.

**The bridge (`renC1Ag_of_rawAgree`).**  `RawAgree (finOf (Ysites C))` and equal `ξ` imply `RenC1Ag`,
because `compY C ⊆ Ysites C` (`compY_subset_Ysites`).  No hypothesis on the dependency sets is
needed: the residual footprint `resDep` of the block sites lies in `X₁` (the block margin), and the
row-local form of the locality of the decoupled background (`i4b_local_of_agree_on_component`)
needs the raw data on the component only.  The right neighbours read by the bond terms are handled
by the same theorem: `approxDep` of a site of `resSites x` lies in `resDep x`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Analysis LocalCover Finset Matrix

section Reads

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L N₀ K ϱ)

open Classical in
/-- **The sites read by `renC1On G a ν εζ B`**: the sites of `B`, their right neighbours
`x + e_μ`, and the blocks `G.blk (layerIndex x) x` of the sites of `B`. -/
noncomputable def renC1Reads (B : Finset (Torus d (N₀ * L ^ K))) : Finset (Torus d (N₀ * L ^ K)) :=
  B ∪ B.biUnion (fun x => Finset.univ.image fun μ : Fin d => x + Pi.single μ 1) ∪
    B.biUnion (fun x => G.blk (G.layerIndex x) x)

variable {G}

theorem mem_renC1Reads {B : Finset (Torus d (N₀ * L ^ K))} {y : Torus d (N₀ * L ^ K)} :
    y ∈ renC1Reads G B ↔ y ∈ B ∨ (∃ x ∈ B, ∃ μ : Fin d, y = x + Pi.single μ 1) ∨
      ∃ x ∈ B, y ∈ G.blk (G.layerIndex x) x := by
  classical
  simp only [renC1Reads, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ((h | ⟨x, hx, μ, rfl⟩) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨x, hx, μ, rfl⟩)
    · exact Or.inr (Or.inr h)
  · rintro (h | ⟨x, hx, μ, rfl⟩ | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨x, hx, μ, rfl⟩)
    · exact Or.inr h

theorem subset_renC1Reads (B : Finset (Torus d (N₀ * L ^ K))) : B ⊆ renC1Reads G B :=
  fun _ hx => mem_renC1Reads.2 (Or.inl hx)

/-- Every site read lies in `resSites x` for a site `x` of `B`. -/
theorem exists_mem_resSites_of_mem_renC1Reads {B : Finset (Torus d (N₀ * L ^ K))}
    {y : Torus d (N₀ * L ^ K)} (hy : y ∈ renC1Reads G B) : ∃ x ∈ B, y ∈ resSites G x := by
  classical
  rcases mem_renC1Reads.1 hy with h | ⟨x, hx, μ, rfl⟩ | ⟨x, hx, h⟩
  · exact ⟨y, h, mem_resSites_self y⟩
  · refine ⟨x, hx, ?_⟩
    unfold resSites
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inl (Or.inr ⟨μ, rfl⟩))
  · refine ⟨x, hx, ?_⟩
    unfold resSites
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inl (Or.inl h))

/-- **Congruence of `renC1On`.**  Two triples `(Ψ, h, φ)`, `(Ψ', h', φ')` that agree on the read set
`renC1Reads G B` (for `φ`: at the sites of `Ω₁` of the read set) give the same value. -/
theorem renC1On_congr {a : ℕ → ℝ} {ν εζ : ℝ} {ξ : Fin 3 → ℂ} {B : Finset (Torus d (N₀ * L ^ K))}
    {Ψ Ψ' h h' : Torus d (N₀ * L ^ K) → Fin N → ℂ} {φ φ' : G.Ω 1 × Fin N → ℂ}
    (hΨ : ∀ x ∈ renC1Reads G B, Ψ x = Ψ' x) (hh : ∀ x ∈ renC1Reads G B, h x = h' x)
    (hφ : ∀ y : G.Ω 1, (y : Torus d (N₀ * L ^ K)) ∈ renC1Reads G B → ∀ i, φ (y, i) = φ' (y, i)) :
    renC1On G a ν εζ B Ψ h φ ξ = renC1On G a ν εζ B Ψ' h' φ' ξ := by
  classical
  have hsv : ∀ y ∈ renC1Reads G B, ∀ i, svec G φ y i = svec G φ' y i := by
    intro y hy i
    by_cases hΩ : y ∈ G.Ω 1
    · rw [svec_of_mem G φ ⟨y, hΩ⟩ i, svec_of_mem G φ' ⟨y, hΩ⟩ i]
      exact hφ ⟨y, hΩ⟩ hy i
    · rw [svec_of_not_mem G φ hΩ i, svec_of_not_mem G φ' hΩ i]
  have hbf : ∀ y ∈ renC1Reads G B, ∀ i, barField G Ψ φ y i = barField G Ψ' φ' y i := by
    intro y hy i
    unfold barField
    by_cases hΩ : y ∈ G.Ω 1
    · simp only [hΩ, ↓reduceDIte]
      exact hφ ⟨y, hΩ⟩ hy i
    · simp only [hΩ, ↓reduceDIte]
      exact congrFun (hΨ y hy) i
  unfold renC1On
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxR : x ∈ renC1Reads G B := subset_renC1Reads B hx
  have hnR : ∀ μ : Fin d, x + Pi.single μ 1 ∈ renC1Reads G B := fun μ =>
    mem_renC1Reads.2 (Or.inr (Or.inl ⟨x, hx, μ, rfl⟩))
  have hQ : ∀ i, blockAvg G φ x i = blockAvg G φ' x i := by
    intro i
    unfold blockAvg
    congr 1
    refine Finset.sum_congr rfl fun y hy => hsv y ?_ i
    exact mem_renC1Reads.2 (Or.inr (Or.inr ⟨x, hx, hy⟩))
  have hS : ∀ i, svec G φ x i = svec G φ' x i := hsv x hxR
  have hΨx : ∀ i, Ψ x i = Ψ' x i := fun i => congrFun (hΨ x hxR) i
  have hhx : ∀ i, h x i = h' x i := fun i => congrFun (hh x hxR) i
  have hbx : ∀ i, barField G Ψ φ x i = barField G Ψ' φ' x i := hbf x hxR
  have hbn : ∀ (μ : Fin d) i, barField G Ψ φ (x + Pi.single μ 1) i =
      barField G Ψ' φ' (x + Pi.single μ 1) i := fun μ i => hbf _ (hnR μ) i
  unfold renC1Site bondSite
  simp only [hQ, hS, hΨx, hhx, hbx, hbn]

end Reads

section Root

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a : ℕ → ℝ} {ν : ℝ}

/-- At full level the block of a site of the block `B_{k+1}(z)` is the block itself. -/
theorem blk_subset_blockSites (hG : IsLevel Gp (k + 1))
    {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ blockSites d L N₁ m₁ (k + 1) k z) :
    Gp.blk (Gp.layerIndex x) x ⊆ blockSites d L N₁ m₁ (k + 1) k z := by
  intro y hy
  rw [(hG x).2] at hy
  have h1 : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y =
      jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x := GeneratingSet.mem_blk.1 hy
  have h2 : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x = z := by
    simpa [blockSites] using hx
  simp only [blockSites, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h1.trans h2

/-- **`renC1_root_reads`** (T1).  The read set of `renC1On (blockSites k z)` lies in the root
neighbourhood `X₁ = nbhdF (blockSite k z)` of `levelLocalCover`: the block and its blocks (the block
itself, at full level) by `blockSites ⊆ nbhdF`, and the right neighbours by
`readSites Hm k z ⊆ nbhdF`. -/
theorem renC1_root_reads (S : DGSetting Gp a ν) (hG' : IsLevel Gp (k + 1)) {m₀ : ℕ}
    (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁) (Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    (↑(renC1Reads Gp (blockSites d L N₁ m₁ (k + 1) k z)) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
      ↑(nbhdF m₀ (blockSite k z)) := by
  obtain ⟨hV, -⟩ := levelLocalCover (N := 0) (a := a) Hm S hG' hm₀ hN
  obtain ⟨-, -, -, -, hR, -, hB⟩ := hV z
  intro y hy
  rcases mem_renC1Reads.1 (Finset.mem_coe.1 hy) with h | ⟨x, hx, μ, rfl⟩ | ⟨x, hx, h⟩
  · exact hB (Finset.mem_coe.2 h)
  · exact hR ⟨x, hx, Or.inr (Or.inl ⟨μ, rfl⟩)⟩
  · exact hB (Finset.mem_coe.2 (blk_subset_blockSites hG' hx h))

/-- **Congruence at the root**: data agreeing on `X₁ = nbhdF (blockSite k z)` give the same
`C₁(B_{k+1}(z))`. -/
theorem renC1On_root_congr (S : DGSetting Gp a ν) (hG' : IsLevel Gp (k + 1)) {m₀ : ℕ}
    (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁) (Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {a' : ℕ → ℝ} {ν' εζ : ℝ}
    {ξ : Fin 3 → ℂ} {Ψ Ψ' h h' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    {φ φ' : Gp.Ω 1 × Fin N → ℂ}
    (hΨ : ∀ x ∈ nbhdF m₀ (blockSite k z), Ψ x = Ψ' x)
    (hh : ∀ x ∈ nbhdF m₀ (blockSite k z), h x = h' x)
    (hφ : ∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ nbhdF m₀ (blockSite k z) →
      ∀ i, φ (y, i) = φ' (y, i)) :
    renC1On Gp a' ν' εζ (blockSites d L N₁ m₁ (k + 1) k z) Ψ h φ ξ =
      renC1On Gp a' ν' εζ (blockSites d L N₁ m₁ (k + 1) k z) Ψ' h' φ' ξ := by
  have hsub := renC1_root_reads S hG' hm₀ hN Hm z
  have hmem : ∀ y ∈ renC1Reads Gp (blockSites d L N₁ m₁ (k + 1) k z),
      y ∈ nbhdF m₀ (blockSite k z) := fun y hy => Finset.mem_coe.1 (hsub (Finset.mem_coe.2 hy))
  exact renC1On_congr (fun x hx => hΨ x (hmem x hx)) (fun x hx => hh x (hmem x hx))
    (fun y hy => hφ y (hmem y hy))

end Root

section Local

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
variable {ι : Type*}

/-- **The agreement relation of the component** `Y = compY C`: two data `(D, ξ)`, `(D', ξ')` have
the same `ξ`, and the same `(Ψ, h)` at every site of the component `compY c X₁ C`. -/
def RenC1Ag (c : ι → ℕ × CTorus d L N₁ m₁ K) (X₁ : Set (CTorus d L N₁ m₁ K)) (C : Finset ι)
    (u u' : BgData Gp N × (Fin 3 → ℂ)) : Prop :=
  u.2 = u'.2 ∧ ∀ y ∈ compY c X₁ C, u.1.Ψ y = u'.1.Ψ y ∧ u.1.h y = u'.1.h y

theorem mem_finOf_set {Y : Set (CTorus d L N₁ m₁ K)} {x : CTorus d L N₁ m₁ K} :
    x ∈ finOf Y ↔ x ∈ Y := by
  rw [← Finset.mem_coe, coe_finOf]

/-- **The bridge** (T3).  Agreement of the raw data `(Ψ, h)` on the output set
`Ysites C = X₁ ∪ ⋃ Dsites` and equality of `ξ` give the agreement `RenC1Ag` on the component,
because `compY C ⊆ Ysites C` (`compY_subset_Ysites`). -/
theorem renC1Ag_of_rawAgree [DecidableEq ι] {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}
    (hcov : CovSetup Gp m₀ j X 𝒦X) {c : ι → ℕ × CTorus d L N₁ m₁ K}
    (hc : ∀ i, c i ∈ cubeIdx Gp) (C : Finset ι) {u u' : BgData Gp N × (Fin 3 → ℂ)}
    (h : RawAgree (finOf (Ysites Gp m₀ c (X1 Gp m₀ j 𝒦X) C)) (rawOf u.1) (rawOf u'.1))
    (hξ : u.2 = u'.2) : RenC1Ag c (X1 Gp m₀ j 𝒦X) C u u' :=
  ⟨hξ, fun y hy => h y (mem_finOf_set.2 (compY_subset_Ysites hcov.hU hcov.hN hc _ C hy))⟩

theorem renC1Ag_refl (c : ι → ℕ × CTorus d L N₁ m₁ K) (X₁ : Set (CTorus d L N₁ m₁ K))
    (C : Finset ι) (u : BgData Gp N × (Fin 3 → ℂ)) : RenC1Ag c X₁ C u u :=
  ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩

/-- **`renC1_local_cut_of`** (T2, with the root facts as hypotheses).  Let `B` be a set of sites
whose read set lies in `X₁` and whose sites carry the block margin against `X₁`, at a whole-lattice
generating set `Gp`.  The cut functional
`F ((D, ξ), s) = renC1On B D.Ψ D.h (decBgField (extParams (s ∘ renLabelEquiv.symm)) D) ξ`
satisfies `LocalityAEOn (e^κ)` for the patches `Pset (renCube i)`, the component `compY` and the
agreement `RenC1Ag`, on any set `S` of data of the fixed-`h` class domain. -/
theorem renC1_local_cut_of {n : ℕ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hconn : HatConn Gp)
    (hG : IsLevel Gp n) {m₀ : ℕ} {X₁ : Set (CTorus d L N₁ m₁ K)}
    {X₁f : Finset (CTorus d L N₁ m₁ K)} (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X₁)
    (hPS : PolySetup Gp m₀ X₁) (B : Finset (CTorus d L N₁ m₁ K))
    (hmar : BlockMargin Gp X₁f (↑B : Set (CTorus d L N₁ m₁ K)))
    (hreads : (↑(renC1Reads Gp B) : Set (CTorus d L N₁ m₁ K)) ⊆ ↑X₁f) (εζ : ℝ)
    {S : Set (BgData Gp N × (Fin 3 → ℂ))}
    (hS : ∀ u ∈ S, XiCOneReal Gp (compWeight L a₁) ν eps u.1) :
    LocalityAEOn (Real.exp κ) S (fun i : RenLabel Gp X₁ => Pset m₁ (renCube Gp X₁ i))
      (compY (renCube Gp X₁) X₁) (RenC1Ag (renCube Gp X₁) X₁)
      (fun u s => renC1On Gp (compWeight L a₁) ν εζ B u.1.Ψ u.1.h
        (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ)
          (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm)) u.1) u.2) := by
  classical
  subst hX₁
  intro C u u' hu hu' s s' hs hs' hag hAg
  obtain ⟨hξ, hdat⟩ := hAg
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hΩ : ∀ x : CTorus d L N₁ m₁ K, x ∈ Gp.Ω 1 := fun x => by
    rw [hG.Ω_one]; exact Finset.mem_univ x
  set cc := renCube Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) with hcc
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm) P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs.2 ((renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm i))
  have hsx' : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s' ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm) P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs'.2 ((renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm i))
  -- the data domain
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 (hS u hu).xiCOne
  have hDom' := xiCData_inDomainC hC.HBp hC.small1 (hS u' hu').xiCOne
  obtain ⟨φ, α, hI, huniq, -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    (fun P => (hsx P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom
  obtain ⟨φ', α', hI', huniq', -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    (fun P => (hsx' P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom'
  show renC1On Gp (compWeight L a₁) ν εζ B u.1.Ψ u.1.h
      (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ)
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) u.1) u.2 =
    renC1On Gp (compWeight L a₁) ν εζ B u'.1.Ψ u'.1.h
      (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ)
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s' ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) u'.1) u'.2
  rw [(decBg_eq hI huniq).1, (decBg_eq hI' huniq').1, hξ]
  -- notation for the component
  set Yc : Set (CTorus d L N₁ m₁ K) := compY cc (↑X₁f : Set (CTorus d L N₁ m₁ K)) C with hYc
  set Y : Finset (CTorus d L N₁ m₁ K) := finOf Yc with hY
  set 𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K) := C.image cc with h𝒞
  have hmemY : ∀ x, x ∈ Y ↔ x ∈ Yc := fun x => mem_finOf_set
  have hXY : ∀ y ∈ X₁f, y ∈ Yc := fun y hy =>
    subset_compY (c := cc) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C (Finset.mem_coe.2 hy)
  have hYsub : Yc ⊆ patchUnion (↑X₁f : Set (CTorus d L N₁ m₁ K)) (fun i => Pset m₁ (cc i)) C :=
    componentOf_subset _ (fun _ h => Or.inl h)
  -- the component property
  have hYnn : IsNnComp ((Vset X₁f 𝒞).filter fun x => x ∈ Gp.Ω 1) Y := by
    refine ⟨fun x hx => ?_, fun x hx y hy hadj => ?_⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter]
      exact ⟨(mem_Vset_iff cc C).2 (hYsub hxY), hΩ x⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter] at hy
      exact (hmemY y).2 (compY_closed hxY ((mem_Vset_iff cc C).1 hy.1) hadj)
  -- the cut parameters
  have hs1E : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁f →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P = 1 ∧
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s' ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P = 1 := fun P hP hPn =>
    ⟨renExt_one_of_not_mem_parCubes _ hP hPn, renExt_one_of_not_mem_parCubes _ hP hPn⟩
  have hs0E : ∀ P ∈ parCubes Gp X₁f, P ∉ 𝒞 →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P = 0 ∧
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s' ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P = 0 := fun P hP hP𝒞 =>
    ⟨renExt_extS_zero hPS s C (fun i hi => hs.1 i hi) hP hP𝒞,
      renExt_extS_zero hPS s' C (fun i hi => hs'.1 i hi) hP hP𝒞⟩
  have hagE : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P =
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s' ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P := by
    intro P hP𝒞 hSub
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP𝒞
    have hsub : Pset m₁ (cc i) ⊆ Yc := fun x hx =>
      (hmemY x).1 (hSub ⟨x, hΩ x⟩ (mem_cubeP.2 hx))
    rw [hcc, renExt_extS_label (↑X₁f : Set (CTorus d L N₁ m₁ K)) s i, renExt_extS_label (↑X₁f : Set (CTorus d L N₁ m₁ K)) s' i]
    exact hag i hi hsub
  have hdata : ∀ z ∈ Y, u.1.Ψ z = u'.1.Ψ z ∧ (z ∈ Gp.Ω 1 → u.1.h z = u'.1.h z) :=
    fun z hz => ⟨(hdat z ((hmemY z).1 hz)).1, fun _ => (hdat z ((hmemY z).1 hz)).2⟩
  obtain ⟨-, -, hrows, -⟩ := i4b_local_of_agree_on_component hC.hS hC.Sp hconn hC.HBp hC.hκ.le
    hC.hM (fun P => (hsx P).le) (fun P => (hsx' P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom hDom' hG
    hYnn hs1E hs0E hagE hdata hI hI'
  -- the sites of `B` lie in `S_Y`
  have hBSY : ∀ x ∈ B, x ∈ SY Gp X₁f 𝒞 Y := by
    intro x hx
    obtain ⟨q, hq, hxq, hQ, hsub⟩ := hmar x (Finset.mem_coe.2 hx) (hΩ x)
    refine Finset.mem_biUnion.2 ⟨q, ?_, hxq⟩
    refine Finset.mem_filter.2 ⟨hq, fun P hP hPpar => absurd hPpar (hQ P hP), ?_⟩
    exact fun x' hx' => (hmemY x').2 (hXY x' (hsub x' hx'))
  -- the field agrees on the read set
  refine renC1On_congr (fun x hx => ?_) (fun x hx => ?_) (fun y hy i => ?_)
  · exact (hdat x (hXY x (Finset.mem_coe.1 (hreads (Finset.mem_coe.2 hx))))).1
  · exact (hdat x (hXY x (Finset.mem_coe.1 (hreads (Finset.mem_coe.2 hx))))).2
  · obtain ⟨x, hxB, hyres⟩ := exists_mem_resSites_of_mem_renC1Reads hy
    have hyX : (y : CTorus d L N₁ m₁ K) ∈ X₁f := hreads (Finset.mem_coe.2 hy)
    exact hrows y ((hmemY _).2 (hXY _ hyX))
      (fun w hw => Or.inl ⟨⟨x, hΩ x⟩, hBSY x hxB, approxDep_subset_resDep hyres hw⟩) i

end Local

section RootLocal

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **`renC1_local_cut`** (T2).  At a block root `z` of the full level `k + 1`, with the root
neighbourhood `X₁ = X1 Gp m₀ k (fam m₀ (blockSite k z))` of `levelLocalCover` and the cover
`renCube` by the cubes whose patch misses `X₁`: the cut functional of `C₁(B_{k+1}(z))`,
`F ((D, ξ), s) = renC1On (blockSites k z) D.Ψ D.h (decBgField (extParams (s ∘ renLabelEquiv.symm)) D) ξ`,
satisfies `LocalityAEOn (e^κ)` with the agreement `RenC1Ag` on the component `compY`.  Together with
`renC1Ag_of_rawAgree` this is the locality hypothesis and the bridge `hlink` of
`renLoc_localization_expansion_fin`.  The only hypotheses are those of `levelLocalCover`
(`FlCore`, `HatConn`, `IsLevel`, `1 ≤ m₀`, `L ^ m₀ ∣ N₁`) and the typing of the data. -/
theorem renC1_local_cut (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn Gp) (hG' : IsLevel Gp (k + 1)) {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (εζ : ℝ)
    {S : Set (BgData Gp N × (Fin 3 → ℂ))}
    (hS : ∀ u ∈ S, XiCOneReal Gp (compWeight L a₁) ν eps u.1) :
    LocalityAEOn (Real.exp κ) S
      (fun i : RenLabel Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))) =>
        Pset m₁ (renCube Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))) i))
      (compY (renCube Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))))
        (X1 Gp m₀ k (fam m₀ (blockSite k z))))
      (RenC1Ag (renCube Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))))
        (X1 Gp m₀ k (fam m₀ (blockSite k z))))
      (fun u s => renC1On Gp (compWeight L a₁) ν εζ (blockSites d L N₁ m₁ (k + 1) k z)
        u.1.Ψ u.1.h
        (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ)
          (extParams Gp (X1 Gp m₀ k (fam m₀ (blockSite k z)))
            (s ∘ (renLabelEquiv Gp (X1 Gp m₀ k (fam m₀ (blockSite k z)))).symm)) u.1) u.2) := by
  obtain ⟨hV, -⟩ := renLoc_fin_domains (N := N) Hm hC.Sp hG' hm₀ hN
  obtain ⟨hcov, hX₁, -, -, -, hmar, -⟩ := hV z
  exact renC1_local_cut_of hC hconn hG' hX₁ hcov.polySetup _ hmar
    (renC1_root_reads hC.Sp hG' hm₀ hN Hm z) εζ hS

end RootLocal

section Instance

/-- **Non-vacuity at the landed pair of levels** (`d = L = 3`, `N₁ = 9`, `K = 2`).  The hypotheses
of `renC1_local_cut_of` hold jointly (`FlCore`, `HatConn`, `IsLevel`, `PolySetup`, the block margin
of every block `B_2(z)` against `X₁ = 𝕋`, the containment of the read set), the set of data of
`XiCOneReal` is nonempty, and the locality law holds.  There `X₁` is the whole torus, so the
label type is empty and the only cut family is `C = ∅`; the statement is the instance of the
labelled case at its degenerate end, not a case with a nonempty set of labels. -/
theorem renC1_local_cut_levelPair (N : ℕ) (hN : 0 < N) :
    ∃ (m₁ : ℕ) (ϱ BG κ eps : ℝ),
      (∃ D : BgData (LevelPair.Gp m₁ ϱ) N,
        XiCOneReal (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 eps D) ∧
      IsEmpty (RenLabel (LevelPair.Gp m₁ ϱ)
        (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2))) ∧
      ∀ (z : Torus 3 (9 * 3 ^ m₁ * 3 ^ (2 - (1 + 1)))) (εζ : ℝ),
        LocalityAEOn (Real.exp κ)
          {u : BgData (LevelPair.Gp m₁ ϱ) N × (Fin 3 → ℂ) |
            XiCOneReal (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 eps u.1}
          (fun i : RenLabel (LevelPair.Gp m₁ ϱ)
              (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) =>
            Pset m₁ (renCube (LevelPair.Gp m₁ ϱ)
              (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) i))
          (compY (renCube (LevelPair.Gp m₁ ϱ)
              (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)))
            (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)))
          (RenC1Ag (renCube (LevelPair.Gp m₁ ϱ)
              (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)))
            (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)))
          (fun u s => renC1On (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 εζ
            (blockSites 3 3 9 m₁ 2 1 z) u.1.Ψ u.1.h
            (decBgField (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 (rho4 3 3 N BG κ)
              (extParams (LevelPair.Gp m₁ ϱ)
                (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2))
                (s ∘ (renLabelEquiv (LevelPair.Gp m₁ ϱ)
                  (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) :
                    Set (CTorus 3 3 9 m₁ 2))).symm)) u.1) u.2) := by
  obtain ⟨m₁, ϱ, c, BG, κ, eps, c₂, BG₂, δ₁, κdec, κ₀, hC, -, hGp, hH, hconn, -, hcov, hX1, -, -,
    -, -, -, -, -, -, hmar, -⟩ := LevelPair.interaction_levelPair_witness N
  have hPS : PolySetup (LevelPair.Gp m₁ ϱ) 1
      (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) := by
    rw [hX1]; exact hcov.polySetup
  have hε : 0 < eps := hC.eps_pos
  obtain ⟨D, hD⟩ := Balaban.Inhabited.exists_xiCOneReal hH (LevelPair.Gp m₁ ϱ) hN
    (by simp) hε
  have hemp : IsEmpty (RenLabel (LevelPair.Gp m₁ ϱ)
      (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2))) := by
    refine ⟨fun q => ?_⟩
    exact Set.disjoint_left.1 q.2.2 (self_mem_Pset q.1) (Finset.mem_coe.2 (Finset.mem_univ _))
  refine ⟨m₁, ϱ, BG, κ, eps, ⟨D, hD⟩, hemp, fun z εζ => ?_⟩
  exact renC1_local_cut_of hC hconn hGp rfl hPS (blockSites 3 3 9 m₁ 2 1 z) (hmar z)
    (fun y _ => Finset.mem_coe.2 (Finset.mem_univ y)) εζ (fun u hu => hu)

end Instance

end Balaban.Localization
