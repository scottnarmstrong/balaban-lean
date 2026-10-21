/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldD7Loc

/-!
# The local pair reads the history only through `W_k` and `Ω_{k+1}` near `V` (clause `loc_hist`)

For two histories `H`, `H'` whose region steps at scale `k` have the same `W_k = (Z_k^c)^{≈2}`
(`stepW`) within `12 M₁ L^k` of the sites of the layers of `𝔹_{k+1}(V)` and the same `Ω_{k+1}`
on the cubes of those sites, the local steps `holeStepLoc` agree (`holeStepLoc_congr_hist`): the
layers of `p6Hold` are `minLayer`s of `W_k`, which are local (`minLayer_local`).  With the equality of
the collar cores (`collarCoreC_congr`, from the agreement of `Ω_{k+1}` on the cubes of `X`) the
coefficient of the old term is the same (`oldCoefLF_congr_hist`).
-/

@[expose] public section

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Balaban.LargeField Balaban.Fluctuation

namespace Balaban.RootFSpine

set_option linter.unusedSectionVars false

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

theorem HoleStep.ext_of {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
    {S₁ S₂ : HoleStep d L N₁ m₁ k N ϱ ϱ'} (hG : S₁.G = S₂.G) (hG' : S₁.G' = S₂.G')
    (hD : HEq S₁.D' S₂.D') (h₀ : S₁.h₀ = S₂.h₀) (a₁ : S₁.a₁ = S₂.a₁) (ν : S₁.ν = S₂.ν)
    (β : S₁.β = S₂.β) (p₁ : S₁.p₁ = S₂.p₁) (δ : S₁.δ = S₂.δ) : S₁ = S₂ := by
  cases S₁; cases S₂
  simp only at hG hG' hD h₀ a₁ ν β p₁ δ
  subst hG hG' h₀ a₁ ν β p₁ δ
  cases hD
  rfl

theorem liftMixed_heq {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    {G₁ G₂ : GeneratingSet d L N₀ (k + 1) ϱ} (e : G₁ = G₂)
    (ψ : Torus d (N₀ * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ) (h1 : 1 ≤ k + 1) :
    HEq (liftMixed G₁ (G₁.blockUnion (k + 1) h1 le_rfl) subset_rfl ψ ϑ h)
      (liftMixed G₂ (G₂.blockUnion (k + 1) h1 le_rfl) subset_rfl ψ ϑ h) := by
  subst e; rfl

/-- Any datum `glob`. -/
theorem holeStepLocAt_G (glob : Bool) (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G =
      (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G.inter (locB g hM1 V) := rfl

theorem holeStepLoc_G (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G =
      (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G.inter (locB g hM1 V) :=
  holeStepLocAt_G (glob := false) g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V

/-- Any datum `glob`. -/
theorem holeStepLocAt_consts (glob : Bool) (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).h₀ = h₀ ∧
    (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).a₁ = a₁ ∧
    (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).ν = ν ∧
    (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).β = β ∧
    (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).p₁ = p₁ ∧
    (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).δ = δ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem holeStepLoc_consts (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).h₀ = h₀ ∧
    (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).a₁ = a₁ ∧
    (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).ν = ν ∧
    (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).β = β ∧
    (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).p₁ = p₁ ∧
    (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).δ = δ :=
  holeStepLocAt_consts (glob := false) g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V

/-- **Two mixed lifts on equal sets whose top sets agree at the data sites are equal** (the datum is
clipped to the data sites). -/
theorem liftMixed_heq_of_agree {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    {G₁ G₂ : GeneratingSet d L N₀ (k + 1) ϱ} (e : G₁ = G₂)
    {Ω₁ Ω₂ : Finset (Torus d (N₀ * L ^ (k + 1)))} (hΩ₁ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω₁)
    (hG₁ : G₁.Ω (k + 1) ⊆ Ω₁) (hΩ₂ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω₂)
    (hG₂ : G₂.Ω (k + 1) ⊆ Ω₂) (hag : ∀ x ∈ dataSites G₁, (x ∈ Ω₁ ↔ x ∈ Ω₂))
    (ψ : Torus d (N₀ * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ) :
    HEq (liftMixed G₁ hΩ₁ hG₁ ψ ϑ h) (liftMixed G₂ hΩ₂ hG₂ ψ ϑ h) := by
  classical
  subst e
  refine heq_of_eq (Background.BgData.ext' ?_ rfl)
  funext x
  simp only [liftMixed, BgData.clip]
  by_cases hx : x ∈ dataSites G₁
  · simp only [hx, ↓reduceIte]
    unfold mixedLift
    by_cases h1 : x ∈ Ω₁
    · simp [h1, (hag x hx).1 h1]
    · simp [h1, show x ∉ Ω₂ from fun h2 => h1 ((hag x hx).2 h2)]
  · simp [hx]

theorem holeStepLocAt_D'_eq (glob : Bool) (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D' =
      liftMixed ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter (locB g hM1 V))
      (locTop_blockUnion g hM1 glob (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G' V)
      (inter_top_subset_locTop g hM1 glob (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G' V)
      (coverField g hnn hM1 hk ψ k (Nat.le_succ k))
      (coverField g hnn hM1 hk (scaleMulti z ψ) (k + 1) le_rfl) (fun i => (h₀ i : ℂ)) := rfl

/-- **The local steps of two histories with the same sets agree** (the core of
`holeStepLoc_congr_sets` for the readings `glob` of the datum): equal restricted sets and top sets of
the mixed lift that agree at the data sites. -/
theorem holeStepLocAt_congr_sets (glob : Bool) (H H' : RegionHistory S n R k0 K) {k : ℕ}
    (hk : k + 1 ≤ K) (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N)
    (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ)
    (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hG : ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G.inter (locB g hM1 V)) =
      ((holeStepLF g hnn hM1 H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G.inter (locB g hM1 V)))
    (hG' : ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter (locB g hM1 V)) =
      ((holeStepLF g hnn hM1 H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter (locB g hM1 V)))
    (hTop : ∀ x ∈ dataSites ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter
        (locB g hM1 V)),
      (x ∈ locTop g hM1 glob (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G' V ↔
        x ∈ locTop g hM1 glob (holeStepLF g hnn hM1 H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G' V)) :
    holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V =
      holeStepLocAt g hnn hM1 glob H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := holeStepLocAt_consts g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := holeStepLocAt_consts g hnn hM1 glob H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
    V
  refine HoleStep.ext_of (by rw [holeStepLocAt_G, holeStepLocAt_G]; exact hG) hG' ?_
    (c1.trans d1.symm) (c2.trans d2.symm) (c3.trans d3.symm) (c4.trans d4.symm) (c5.trans d5.symm)
    (c6.trans d6.symm)
  rw [holeStepLocAt_D'_eq, holeStepLocAt_D'_eq]
  exact liftMixed_heq_of_agree hG' _ _ _ _ hTop _ _ _

theorem holeStepLoc_D'_eq (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D' =
      liftMixed ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter (locB g hM1 V))
      (((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter (locB g hM1 V)).blockUnion
        (k + 1) (by omega) le_rfl) subset_rfl
      (coverField g hnn hM1 hk ψ k (Nat.le_succ k))
      (coverField g hnn hM1 hk (scaleMulti z ψ) (k + 1) le_rfl) (fun i => (h₀ i : ℂ)) := rfl

theorem holeStepLoc_congr_sets (H H' : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hG : ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G.inter (locB g hM1 V)) =
      ((holeStepLF g hnn hM1 H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G.inter (locB g hM1 V)))
    (hG' : ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter (locB g hM1 V)) =
      ((holeStepLF g hnn hM1 H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter (locB g hM1 V))) :
    holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V =
      holeStepLoc g hnn hM1 H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V :=
  holeStepLocAt_congr_sets g hnn hM1 false H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V hG hG'
    (fun x _ => by
      change x ∈ (_ : GeneratingSet _ _ _ _ _).Ω (k + 1) ↔ x ∈ (_ : GeneratingSet _ _ _ _ _).Ω (k + 1)
      rw [hG'])

theorem holeStepLF_G_Ω (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (j : ℕ) (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    x ∈ (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G.Ω j ↔
      ((congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm ▸ x :
        Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))) ∈
        minLayer g.M1 (g.c * n (k + 1)) S.L (k + 1) k
          (stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H.step k).Z) j := by
  unfold holeStepLF holeStepOf p6OldC
  dsimp only
  rw [mem_castN_Ω, p6Hold_Ω]
theorem holeStepLF_G'_Ω_top (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    x ∈ (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.Ω (k + 1) ↔
      cubeOfC hM1 x ∈ (H.step k).Omega := by
  unfold holeStepLF holeStepOf
  dsimp only
  rw [p6TopC, mem_castN_Ω, p6Top_Ω_top, mem_fineK1]
  rfl

theorem holeStepLF_G'_Ω_of_ne (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) {j : ℕ} (hj : j ≠ k + 1)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    x ∈ (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.Ω j ↔
      ((congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm ▸ x :
        Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))) ∈
        minLayer g.M1 (g.c * n (k + 1)) S.L (k + 1) k
          (stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H.step k).Z) j := by
  unfold holeStepLF holeStepOf
  dsimp only
  rw [p6TopC, mem_castN_Ω]
  unfold p6Top
  rw [GeneratingSet.addTop_Ω]
  simp only [hj, ↓reduceIte]
  rw [p6Hold_Ω]
theorem GeneratingSet.ext_Ω' {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    {G₁ G₂ : GeneratingSet d L N₀ k ϱ} (h : G₁.Ω = G₂.Ω) : G₁ = G₂ := by
  cases G₁; cases G₂; simp only at h; subst h; rfl

theorem holeStepLF_inter_congr (H H' : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hL : 2 ≤ S.L)
    (hWag : ∀ j, j ≤ k → ∀ x ∈ (locB g hM1 V).Ω j, ∀ y : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)),
      supDist ((congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm ▸ x :
        Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))) y ≤ 12 * g.M1 * S.L ^ k →
        (y ∈ stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H.step k).Z ↔
          y ∈ stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H'.step k).Z))
    (hOm : ∀ x ∈ (locB g hM1 V).Ω (k + 1),
      (cubeOfC hM1 x ∈ (H.step k).Omega ↔ cubeOfC hM1 x ∈ (H'.step k).Omega)) :
    ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G.inter (locB g hM1 V)) =
      ((holeStepLF g hnn hM1 H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G.inter (locB g hM1 V)) ∧
    ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter (locB g hM1 V)) =
      ((holeStepLF g hnn hM1 H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter (locB g hM1 V)) := by
  have hmin : ∀ j, j ≤ k → ∀ x ∈ (locB g hM1 V).Ω j,
      (((congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm ▸ x :
        Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))) ∈
        minLayer g.M1 (g.c * n (k + 1)) S.L (k + 1) k
          (stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H.step k).Z) j ↔
      ((congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm ▸ x :
        Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))) ∈
        minLayer g.M1 (g.c * n (k + 1)) S.L (k + 1) k
          (stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H'.step k).Z) j) := fun j hj x hx =>
    minLayer_local _ hL (Nat.le_succ k) hj (hWag j hj x hx)
  have hgt : ∀ j, k < j → ∀ x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1),
      ((congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm ▸ x :
        Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))) ∉
        minLayer g.M1 (g.c * n (k + 1)) S.L (k + 1) k
          (stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H.step k).Z) j := fun j hj x => by
    rw [minLayer_of_gt _ hj]; exact Finset.notMem_empty _
  have hgt' : ∀ j, k < j → ∀ x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1),
      ((congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm ▸ x :
        Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))) ∉
        minLayer g.M1 (g.c * n (k + 1)) S.L (k + 1) k
          (stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H'.step k).Z) j := fun j hj x => by
    rw [minLayer_of_gt _ hj]; exact Finset.notMem_empty _
  constructor
  · refine GeneratingSet.ext_Ω' (funext fun j => ?_)
    ext x
    simp only [GeneratingSet.inter_Ω, Finset.mem_inter, holeStepLF_G_Ω]
    by_cases hj : j ≤ k
    · constructor
      · rintro ⟨h1, h2⟩; exact ⟨(hmin j hj x h2).1 h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨(hmin j hj x h2).2 h1, h2⟩
    · have hj' : k < j := by omega
      exact ⟨fun h => absurd h.1 (hgt j hj' x), fun h => absurd h.1 (hgt' j hj' x)⟩
  · refine GeneratingSet.ext_Ω' (funext fun j => ?_)
    ext x
    simp only [GeneratingSet.inter_Ω, Finset.mem_inter]
    by_cases hj : j = k + 1
    · subst hj
      simp only [holeStepLF_G'_Ω_top]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨(hOm x h2).1 h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨(hOm x h2).2 h1, h2⟩
    · simp only [holeStepLF_G'_Ω_of_ne g hnn hM1 _ hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ hj]
      by_cases hjk : j ≤ k
      · constructor
        · rintro ⟨h1, h2⟩; exact ⟨(hmin j hjk x h2).1 h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨(hmin j hjk x h2).2 h1, h2⟩
      · have hj' : k < j := by omega
        exact ⟨fun h => absurd h.1 (hgt j hj' x), fun h => absurd h.1 (hgt' j hj' x)⟩

theorem collarCoreC_congr (H H' : RegionHistory S n R k0 K) {k : ℕ} (r : ℕ)
    (X : Finset (Torus S.d (n k)))
    (hOm : ∀ x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1),
      cubeKOfC (n0 := n k) hM1 x ∈ X →
        (cubeOfC hM1 x ∈ (H.step k).Omega ↔ cubeOfC hM1 x ∈ (H'.step k).Omega)) :
    (collarCoreC (c := g.c) (k := k) (H.step k) hM1 r X :
        Finset (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) =
      collarCoreC (c := g.c) (k := k) (H'.step k) hM1 r X := by
  have hact : (activeCoreC (c := g.c) (k := k) (H.step k) hM1 X :
      Finset (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) =
      activeCoreC (c := g.c) (k := k) (H'.step k) hM1 X := by
    ext x
    rw [mem_activeCoreC, mem_activeCoreC]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hOm x h1).1 h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hOm x h1).2 h2⟩
  ext x
  rw [mem_collarCoreC, mem_collarCoreC, hact]

theorem locSetXJ_congr (H H' : RegionHistory S n R k0 K) {k : ℕ} (r r' : ℕ)
    (X : Finset (Torus S.d (n k)))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hc : (collarCoreC (c := g.c) (k := k) (H.step k) hM1 r X :
        Finset (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) =
      collarCoreC (c := g.c) (k := k) (H'.step k) hM1 r X) :
    locSetXJ g hM1 H r r' X J = locSetXJ g hM1 H' r r' X J := by
  unfold locSetXJ
  rw [hc]

/-- **The local steps of two histories agree** (the core of `holeStepLoc_congr_hist` for the readings
`glob` of the datum; for `glob = true`, reading HS-2, `Ω_{k+1}` also agrees on the cubes of the data
sites of the local pair, `hOmD`). -/
theorem holeStepLocAt_congr_hist (glob : Bool) (H H' : RegionHistory S n R k0 K) {k : ℕ}
    (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hL : 2 ≤ S.L)
    (hWag : ∀ j, j ≤ k → ∀ x ∈ (locB g hM1 V).Ω j, ∀ y : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)),
      supDist ((congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm ▸ x :
        Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))) y ≤ 12 * g.M1 * S.L ^ k →
        (y ∈ stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H.step k).Z ↔
          y ∈ stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H'.step k).Z))
    (hOm : ∀ x ∈ (locB g hM1 V).Ω (k + 1),
      (cubeOfC hM1 x ∈ (H.step k).Omega ↔ cubeOfC hM1 x ∈ (H'.step k).Omega))
    (hOmD : glob = true → ∀ x ∈ dataSites
        ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter (locB g hM1 V)),
      (cubeOfC hM1 x ∈ (H.step k).Omega ↔ cubeOfC hM1 x ∈ (H'.step k).Omega)) :
    holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V =
      holeStepLocAt g hnn hM1 glob H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V := by
  obtain ⟨hG, hG'⟩ := holeStepLF_inter_congr g hnn hM1 H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V hL hWag hOm
  refine holeStepLocAt_congr_sets g hnn hM1 glob H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V hG hG'
    (fun x hx => ?_)
  cases glob
  · change x ∈ (_ : GeneratingSet _ _ _ _ _).Ω (k + 1) ↔ x ∈ (_ : GeneratingSet _ _ _ _ _).Ω (k + 1)
    rw [hG']
  · change x ∈ (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.Ω (k + 1) ↔
      x ∈ (holeStepLF g hnn hM1 H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.Ω (k + 1)
    rw [holeStepLF_G'_Ω_top, holeStepLF_G'_Ω_top]
    exact hOmD rfl x hx

/-- **The local steps of two histories agree** when `W_k` agrees within `12 M₁ L^k` of the sites of
the layers of `𝔹_{k+1}(V)` and `Ω_{k+1}` agrees on the cubes of those sites. -/
theorem holeStepLoc_congr_hist (H H' : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hL : 2 ≤ S.L)
    (hWag : ∀ j, j ≤ k → ∀ x ∈ (locB g hM1 V).Ω j, ∀ y : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)),
      supDist ((congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm ▸ x :
        Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))) y ≤ 12 * g.M1 * S.L ^ k →
        (y ∈ stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H.step k).Z ↔
          y ∈ stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H'.step k).Z))
    (hOm : ∀ x ∈ (locB g hM1 V).Ω (k + 1),
      (cubeOfC hM1 x ∈ (H.step k).Omega ↔ cubeOfC hM1 x ∈ (H'.step k).Omega)) :
    holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V =
      holeStepLoc g hnn hM1 H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V :=
  holeStepLocAt_congr_hist g hnn hM1 false H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V hL hWag hOm
    (fun h => absurd h Bool.false_ne_true)

/-- **Locality of `W_k = (Z_k^c)^{≈2}`**: a site `y` is in `stepW Z` iff in `stepW Z'` when `Z`, `Z'`
agree on the cubes within `2 (ρ' + 1)` of the cube of `y`. -/
theorem mem_stepW_congr {d M1 c n1 L k n0 : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n1] [NeZero n0]
    {ρ' : ℕ} {Z Z' : Set (Torus d n0)}
    (y : Torus d (M1 * (c * n1) * L ^ (k + 1)))
    (h : ∀ w : Torus d n0, supDist (blockMap (L ^ k * (c * M1)) n0 y) w ≤ 2 * (ρ' + 1) →
      (w ∈ Z ↔ w ∈ Z')) :
    y ∈ stepW M1 c n1 L k ρ' Z ↔ y ∈ stepW M1 c n1 L k ρ' Z' := by
  have key : ∀ {Z Z' : Set (Torus d n0)}, (∀ w : Torus d n0,
      supDist (blockMap (L ^ k * (c * M1)) n0 y) w ≤ 2 * (ρ' + 1) → (w ∈ Z ↔ w ∈ Z')) →
      y ∈ stepW M1 c n1 L k ρ' Z → y ∈ stepW M1 c n1 L k ρ' Z' := by
    intro Z Z' h hy
    unfold stepW fineK at hy ⊢
    rw [mem_cubePre] at hy ⊢
    unfold thick2 thick at hy ⊢
    obtain ⟨v, hv, huv⟩ := mem_nbhd.1 hy
    obtain ⟨w, hw, hvw⟩ := mem_nbhd.1 hv
    refine mem_nbhd.2 ⟨v, mem_nbhd.2 ⟨w, ?_, hvw⟩, huv⟩
    have hd : supDist (blockMap (L ^ k * (c * M1)) n0 y) w ≤ 2 * (ρ' + 1) := by
      have := supDist_triangle (blockMap (L ^ k * (c * M1)) n0 y) v w
      omega
    intro hwZ'
    exact hw ((h w hd).2 hwZ')
  exact ⟨key h, key (fun w hw => (h w hw).symm)⟩

/-- **The local steps of two histories agree when `Z_k` agrees near `V`** (the core of
`holeStepLoc_congr_hist_Z` for the readings `glob` of the datum). -/
theorem holeStepLocAt_congr_hist_Z (glob : Bool) (H H' : RegionHistory S n R k0 K) {k : ℕ}
    (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hL : 2 ≤ S.L)
    (hZag : ∀ j, j ≤ k → ∀ x ∈ (locB g hM1 V).Ω j,
      ∀ y : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)),
      supDist ((congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm ▸ x :
        Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))) y ≤ 12 * g.M1 * S.L ^ k →
      ∀ w : Torus S.d (n k), supDist (blockMap (S.L ^ k * (g.c * g.M1)) (n k) y) w ≤
        2 * (⌊R (k - 1)⌋₊ + 1) → (w ∈ (H.step k).Z ↔ w ∈ (H'.step k).Z))
    (hOm : ∀ x ∈ (locB g hM1 V).Ω (k + 1),
      (cubeOfC hM1 x ∈ (H.step k).Omega ↔ cubeOfC hM1 x ∈ (H'.step k).Omega))
    (hOmD : glob = true → ∀ x ∈ dataSites
        ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter (locB g hM1 V)),
      (cubeOfC hM1 x ∈ (H.step k).Omega ↔ cubeOfC hM1 x ∈ (H'.step k).Omega)) :
    holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V =
      holeStepLocAt g hnn hM1 glob H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V :=
  holeStepLocAt_congr_hist g hnn hM1 glob H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V hL
    (fun j hj x hx y hxy => mem_stepW_congr y (hZag j hj x hx y hxy)) hOm hOmD

/-- **The local steps of two histories agree when `Z_k` agrees near `V`** (from
`holeStepLoc_congr_hist` and the locality of `W_k`, `mem_stepW_congr`): `Z_k`, `Z'_k` agree on the
cubes within `2 (⌊R_{k-1}⌋ + 1)` of the cube of every site within `12 M₁ L^k` of a site of a layer
of `𝔹_{k+1}(V)`, and `Ω_{k+1}` agrees on the cubes of those sites. -/
theorem holeStepLoc_congr_hist_Z (H H' : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hL : 2 ≤ S.L)
    (hZag : ∀ j, j ≤ k → ∀ x ∈ (locB g hM1 V).Ω j,
      ∀ y : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)),
      supDist ((congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm ▸ x :
        Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))) y ≤ 12 * g.M1 * S.L ^ k →
      ∀ w : Torus S.d (n k), supDist (blockMap (S.L ^ k * (g.c * g.M1)) (n k) y) w ≤
        2 * (⌊R (k - 1)⌋₊ + 1) → (w ∈ (H.step k).Z ↔ w ∈ (H'.step k).Z))
    (hOm : ∀ x ∈ (locB g hM1 V).Ω (k + 1),
      (cubeOfC hM1 x ∈ (H.step k).Omega ↔ cubeOfC hM1 x ∈ (H'.step k).Omega)) :
    holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V =
      holeStepLoc g hnn hM1 H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V :=
  holeStepLocAt_congr_hist_Z g hnn hM1 false H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V hL hZag hOm
    (fun h => absurd h Bool.false_ne_true)

end Balaban.RootFSpine
