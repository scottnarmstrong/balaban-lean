/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.StepBackgrounds
public import Balaban.Background.Composition
public import Balaban.Fluctuation.Theorem42RealStep1


/-!
# Theorem 4.2, Step 1 for the real step: the step generating sets (LFR Lemma II.2.3 (b), II.2.5)

* `genBoundaryLocal_precedes`, `genBoundaryUnion_precedes`: `𝔹^loc ≺ 𝔹^∂`, layer by layer
  (`Ω_n(G^{Z'}) ⊆ Ω_n(G^∂)`; Lemma II.2.3 (b));
* `genBoundaryUnion_agree`: Lemma II.2.5 (c) for the union `𝔹^loc`: the layers of `𝔹^loc` and
  `𝔹^∂` coincide on `E_{Z'} = Z'^{∼⌊R_k⌋}` (the other pieces lie in the disjoint `V_{Z''}`);
* `real_step1_flow`: `real_step1` for the step sets: the data change `δΨ = ψ(𝔹^loc, 𝔹^∂; ψ̃) - ψ̃`
  vanishes on `E = ⋃ E_{Z'}` and `φ^∂ - φ^loc = φ(𝔹^loc; ψ̃ + δΨ) - φ(𝔹^loc; ψ̃)`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale

set_option linter.unusedSectionVars false

section Precedes

variable {d M1 c n1 L k n0 : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} {ω : ℕ} {Zp : Set (Torus d n1)} {Z' : Finset (Torus d n1)}
  (st : RegionStep d L n0 n1 Rprev Rk)
  (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L) (hρ : 3 * L ≤ ⌊Rprev⌋₊)
  (hω : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω) (hZ : st.Omegaᶜ ⊆ Zp) (hZ' : Z' ∈ comps ω (finOf Zp))

include hc hL in
/-- **Lemma II.2.3 (b)**, layer by layer: the local family `G^{Z'}_{k+1}` precedes the global
boundary family `G^∂_{k+1}`: `Ω_n(G^{Z'}) ⊆ Ω_n(G^∂)`. -/
theorem genBoundaryLocal_precedes :
    Background.Precedes (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ')
      (genBoundary M1 c n1 L k st hc hn hL hρ (Zp := Zp) hZ) := by
  intro i hi1 hik x hx
  unfold genBoundaryLocal at hx
  unfold genBoundary
  rw [boundaryGenSet_Ω] at hx ⊢
  unfold boundaryLayer at hx ⊢
  have hW : stepWLoc M1 c n1 L k ⌊Rprev⌋₊ ⌊Rk⌋₊ st.Z (Z' : Set (Torus d n1)) ⊆
      stepW M1 c n1 L k ⌊Rprev⌋₊ st.Z := Finset.inter_subset_left
  have hU : stepU M1 c n1 L k ⌊Rk⌋₊ (Z' : Set (Torus d n1)) ⊆
      stepU M1 c n1 L k ⌊Rk⌋₊ Zp := by
    intro y hy
    unfold stepU at hy ⊢
    rw [mem_fineK1] at hy ⊢
    exact nbhd_mono le_rfl
      (fun z hz => mem_finOf.1 (comp_subset hZ' (Finset.mem_coe.1 hz))) hy
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at hx ⊢
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨minLayer_mono hW i h1, h2⟩
  · exact Or.inr ⟨minLayer_mono hU i h1, h2⟩

include hc hL in
/-- The union `𝔹^loc_{k+1}(∂Ω_{k+1})` of the local families precedes `𝔹^∂_{k+1}`. -/
theorem genBoundaryUnion_precedes :
    Background.Precedes (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ)
      (genBoundary M1 c n1 L k st hc hn hL hρ (Zp := Zp) hZ) := by
  intro i hi1 hik x hx
  unfold genBoundaryUnion at hx
  rw [unionGenSet_Ω] at hx
  obtain ⟨Z, -, hxZ⟩ := Finset.mem_biUnion.1 hx
  exact genBoundaryLocal_precedes st hc hn hL hρ hω hZ Z.2 i hi1 hik hxZ

include hc hL hZ' in
/-- **Lemma II.2.5 (c) for the union** `𝔹^loc`: on the fine set of `E_{Z'} = Z'^{∼⌊R_k⌋}` the
layers of `𝔹^loc = ⋃ G^{Z''}` and of `𝔹^∂` coincide (the other pieces lie in the disjoint
`V_{Z''}`, Lemma II.2.5 (b)). -/
theorem genBoundaryUnion_agree {x : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (hx : blockMap (L ^ (k + 1) * (c * M1)) n1 x ∈ nbhd ⌊Rk⌋₊ (Z' : Set (Torus d n1)))
    {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k + 1) :
    x ∈ (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ).Ω n ↔
      x ∈ (genBoundary M1 c n1 L k st hc hn hL hρ (Zp := Zp) hZ).Ω n := by
  constructor
  · intro hxU
    unfold genBoundaryUnion at hxU
    rw [unionGenSet_Ω] at hxU
    obtain ⟨⟨Zv, hZv⟩, -, hxZ⟩ := Finset.mem_biUnion.1 hxU
    by_cases hZZ : Zv = Z'
    · subst hZZ
      exact (genBoundaryLocal_agree st hc hn hL hρ hω hZ hZv hx n).1 hxZ
    · exfalso
      have hxΩ : x ∈ (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZv).Ω 1 :=
        (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZv).Ω_antitone le_rfl hn1 (by omega) hxZ
      have hV := genBoundaryLocal_subset_V st hc hn hL hρ hω hZ hZv
        ((Background.mem_dataSites _).2 (Or.inl hxΩ))
      obtain ⟨y', hy', hd'⟩ := mem_nbhd.1 hV
      obtain ⟨y'', hy'', hd''⟩ := mem_nbhd.1 hy'
      obtain ⟨y, hy, hd⟩ := mem_nbhd.1 hx
      have hsep := nbhd_disjoint_of_comps hZ' hZv (Ne.symm hZZ) (⌊Rk⌋₊ + 2)
        (blockMap (L ^ (k + 1) * (c * M1)) n1 x)
        (mem_nbhd.2 ⟨y, hy, by omega⟩)
        (blockMap (L ^ (k + 1) * (c * M1)) n1 x)
        (mem_nbhd.2 ⟨y'', hy'', by
          have := supDist_triangle (blockMap (L ^ (k + 1) * (c * M1)) n1 x) y' y''
          unfold thick at *
          omega⟩)
      rw [supDist_self] at hsep
      omega
  · intro hxD
    have h1 := (genBoundaryLocal_agree st hc hn hL hρ hω hZ hZ' hx n).2 hxD
    unfold genBoundaryUnion
    rw [unionGenSet_Ω]
    exact Finset.mem_biUnion.2 ⟨⟨Z', hZ'⟩, Finset.mem_univ _, h1⟩

end Precedes

end Balaban.LargeField


namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField

section Flow

variable {d M1 c n1 L k n0 N : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} {ω : ℕ} {Zp : Set (Torus d n1)}
  (st : RegionStep d L n0 n1 Rprev Rk)
  (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L) (hρ : 3 * L ≤ ⌊Rprev⌋₊)
  (hω : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω) (hZ : st.Omegaᶜ ⊆ Zp)

/-- The fine set of `E = ⋃_{Z'} Z'^{∼⌊R_k⌋}` (LFR Lemma II.2.5 (c)). -/
def stepE (Rk : ℝ) (ω : ℕ) (Zp : Set (Torus d n1)) :
    Set (Torus d (M1 * (c * n1) * L ^ (k + 1))) :=
  {x | ∃ Z' : Finset (Torus d n1), Z' ∈ comps ω (finOf Zp) ∧
    blockMap (L ^ (k + 1) * (c * M1)) n1 x ∈ nbhd ⌊Rk⌋₊ (Z' : Set (Torus d n1))}

variable (ψ : Torus d (M1 * (c * n1) * L ^ (k + 1 - k)) → Fin N → ℂ)
  (ϑ : Torus d (M1 * (c * n1) * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ)

/-- The lifted datum `ψ̃` of the global boundary family `𝔹^∂` (Definition II.2.7). -/
noncomputable abbrev stepDataBd : BgData (genBoundary M1 c n1 L k st hc hn hL hρ (Zp := Zp) hZ) N :=
  liftMixed (genBoundary M1 c n1 L k st hc hn hL hρ (Zp := Zp) hZ)
    ((isCubeUnion_fineK1 st.Omega).isBlockUnion (le_refl _))
    (boundaryGenSet_top_subset _ _ _ _) ψ ϑ h

/-- The lifted datum `ψ̃` of the local family `𝔹^loc = ⋃ G^{Z'}` (Definition II.2.7 (iv)). -/
noncomputable abbrev stepDataLoc :
    BgData (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ) N :=
  liftMixed (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ)
    ((isCubeUnion_fineK1 st.Omega).isBlockUnion (le_refl _))
    (genBoundaryUnion_top_subset st hc hn hL hρ hω hZ) ψ ϑ h

/-- **Theorem 4.2, Step 1 for the real step** (FLUCTUATION §4.2; LFR Lemma II.2.5 (c)).
`𝔹^loc = ⋃ G^{Z'}` and `𝔹^∂` are the step generating sets (Definition II.2.4 (iv), (v)), `ψ̃` the
mixed lift of `(ψ_k, ϑ, h)` on both.  If the data are in the domain `𝒟` of Theorem 5.2 (for the
composed datum this is the H7 bound `|δΨ| ≤ C r_H` of Step 1), then there is a data change `δΨ`,
vanishing on `E = ⋃ E_{Z'}`, with `ψ(𝔹^loc, 𝔹^∂; ψ̃) = ψ̃ + δΨ` (the same `h`) and
`φ^∂ - φ^loc = φ(𝔹^loc; ψ̃ + δΨ) - φ(𝔹^loc; ψ̃)` on `Ω₁(𝔹^loc)`. -/
theorem real_step1_flow {a : ℕ → ℝ} {ν : ℝ}
    (H : BgHyp d L (k + 1) (minSep L M1) a ν)
    (hD' : InUnionDomainC (genBoundary M1 c n1 L k st hc hn hL hρ (Zp := Zp) hZ)
      (bgC0 d L N) (bgC1 d L N) ν (stepDataBd st hc hn hL hρ hZ ψ ϑ h))
    (hDu : InUnionDomainC (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ)
      (bgC0 d L N) (bgC1 d L N) ν
      (stepComposed (genBoundaryUnion_precedes st hc hn hL hρ hω hZ) a ν
        (stepDataBd st hc hn hL hρ hZ ψ ϑ h))) :
    ∃ δΨ : Torus d (M1 * (c * n1) * L ^ (k + 1)) → Fin N → ℂ,
      (∀ x ∈ stepE (M1 := M1) (c := c) (k := k) Rk ω Zp, ∀ i, δΨ x i = 0) ∧
      (∀ x i, (stepComposed (genBoundaryUnion_precedes st hc hn hL hρ hω hZ) a ν
        (stepDataBd st hc hn hL hρ hZ ψ ϑ h)).Ψ x i =
        (stepDataLoc st hc hn hL hρ hω hZ ψ ϑ h).Ψ x i + δΨ x i) ∧
      (∀ x i, (stepComposed (genBoundaryUnion_precedes st hc hn hL hρ hω hZ) a ν
        (stepDataBd st hc hn hL hρ hZ ψ ϑ h)).h x i =
        (stepDataLoc st hc hn hL hρ hω hZ ψ ϑ h).h x i) ∧
      (∀ z : (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ).Ω 1, ∀ i,
        bgFieldC (genBoundary M1 c n1 L k st hc hn hL hρ (Zp := Zp) hZ) a ν (bgC0 d L N)
          (stepDataBd st hc hn hL hρ hZ ψ ϑ h)
          ((genBoundaryUnion_precedes st hc hn hL hρ hω hZ).incl z, i) -
          bgFieldC (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ) a ν (bgC0 d L N)
            (stepDataLoc st hc hn hL hρ hω hZ ψ ϑ h) (z, i) =
        bgFieldC (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ) a ν (bgC0 d L N)
          (stepComposed (genBoundaryUnion_precedes st hc hn hL hρ hω hZ) a ν
            (stepDataBd st hc hn hL hρ hZ ψ ϑ h)) (z, i) -
          bgFieldC (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ) a ν (bgC0 d L N)
            (stepDataLoc st hc hn hL hρ hω hZ ψ ϑ h) (z, i)) := by
  have hE : ∀ x ∈ stepE (M1 := M1) (c := c) (k := k) Rk ω Zp, ∀ n, 1 ≤ n → n ≤ k + 1 →
      (x ∈ (genBoundaryUnion M1 c n1 L k st hc hn hL hρ hω hZ).Ω n ↔
        x ∈ (genBoundary M1 c n1 L k st hc hn hL hρ (Zp := Zp) hZ).Ω n) := by
    rintro x ⟨Z', hZ', hx⟩ n hn1 hnk
    exact genBoundaryUnion_agree st hc hn hL hρ hω hZ hZ' hx hn1 hnk
  obtain ⟨δΨ, h1, h2, h3, h4⟩ := real_step1
    ((isCubeUnion_fineK1 st.Omega).isBlockUnion (le_refl _))
    (genBoundaryUnion_top_subset st hc hn hL hρ hω hZ) (boundaryGenSet_top_subset _ _ _ _)
    ψ ϑ h (genBoundaryUnion_precedes st hc hn hL hρ hω hZ) H
    (G' := genBoundary M1 c n1 L k st hc hn hL hρ (Zp := Zp) hZ)
    H hE hD' hDu
  exact ⟨δΨ, h1, h2, h3, h4⟩

end Flow

end Balaban.Fluctuation
