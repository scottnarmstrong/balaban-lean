/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.GeneratingSet
public import Balaban.Background.Composition
public import Balaban.Fluctuation.CriticalPoint
public import Balaban.SmallField.GsSpecPoly
public import Balaban.SmallField.GsSpecStrong
public import Balaban.LargeField.Background.LocalGenNeg
public import Balaban.Background.ExistenceSetup
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Lowering the separation index of a generating set

This is a generic utility.  It makes no choice about which generating sets the terms of the
small-field class carry.

A generating set of separation `ϱ'` is a fortiori a generating set of every smaller separation
`ϱ ≤ ϱ'`: the condition `ϱ L^j < dist x y` follows from `ϱ' L^j < dist x y`.  The separation
constant is part of the type `GeneratingSet d L N₀ k ϱ`, so this needs an explicit map.

* `GeneratingSet.weakenSep`: the map; it copies `Ω`, `top`, `subset`, `blockUnion`.
* Everything defined from `Ω` alone (`layer`, `layerIndex`, `spacing`, `blk`, `collar`,
  `dataSites`, `IsLevel`, `IsLayerConstant`, `InPsiTilde`, ..., `Precedes`, `castG`) is unchanged
  (proved by `Iff.rfl` / `rfl`).  The types `BgData (G.weakenSep h) N` and `BgData G N` are
  *not* definitionally equal (their parameters have different types), so the canonical
  equivalence `BgData.weakenEquiv` is given.
* Corollaries for the minimal generating set of a polymer: layers and data sites are unchanged,
  and for `bgR0 d L ≤ minSep L M1` the minimal set is usable at separation `bgR0 d L`.

## Which hypotheses are monotone in the separation

Weakening lowers `ϱ`.  Preserved: any hypothesis that is an upper bound on `ϱ`, and the
`separation` field itself at the lower index.  Not preserved (can only be lost): hypotheses
requiring a lower bound on the separation of the set concerned, namely `BgHyp.hϱ : bgR0 d L ≤ ϱ`
(`Background/ExistenceSetup.lean`) and the `BgSetting` requirements `r₀ ≥ 4 d L^3`,
`r₀ M₁ ≤ ϱ - 1` of `Localization/I5Fan.lean`.  Consequently weakening is for passing from a set
of large separation to a consumer that needs a smaller one, never for establishing `BgHyp`.
-/

@[expose] public section

namespace Balaban.Multiscale

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

namespace GeneratingSet

/-- The generating set `G` of separation `ϱ'` viewed as one of separation `ϱ ≤ ϱ'`
(same domains). -/
def weakenSep (G : GeneratingSet d L N₀ k ϱ') (h : ϱ ≤ ϱ') : GeneratingSet d L N₀ k ϱ where
  Ω := G.Ω
  top := G.top
  subset := G.subset
  blockUnion := G.blockUnion
  separation := fun j hj1 hjk x hx y hy =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right h (by positivity)) (G.separation j hj1 hjk x hx y hy)

variable (G : GeneratingSet d L N₀ k ϱ') (h : ϱ ≤ ϱ')

@[simp] theorem weakenSep_Ω : (G.weakenSep h).Ω = G.Ω := rfl

@[simp] theorem weakenSep_refl (G : GeneratingSet d L N₀ k ϱ) :
    G.weakenSep (le_refl ϱ) = G := rfl

theorem weakenSep_trans {ϱ'' : ℝ} (h' : ϱ'' ≤ ϱ) :
    (G.weakenSep h).weakenSep h' = G.weakenSep (h'.trans h) := rfl

@[simp] theorem weakenSep_layer (j : ℕ) : (G.weakenSep h).layer j = G.layer j := rfl

@[simp] theorem weakenSep_layerIndex :
    (G.weakenSep h).layerIndex (d := d) (L := L) (N₀ := N₀) (k := k) = G.layerIndex := rfl

@[simp] theorem weakenSep_spacing :
    (G.weakenSep h).spacing (d := d) (L := L) (N₀ := N₀) (k := k) = G.spacing := rfl

@[simp] theorem weakenSep_blk (j : ℕ) :
    (G.weakenSep h).blk (d := d) (L := L) (N₀ := N₀) (k := k) j = G.blk j := rfl

@[simp] theorem weakenSep_isLevel (n : ℕ) :
    Fluctuation.IsLevel (G.weakenSep h) n ↔ Fluctuation.IsLevel G n := Iff.rfl

end GeneratingSet

open Background

section Background

variable (G : GeneratingSet d L N₀ k ϱ') (h : ϱ ≤ ϱ') {N : ℕ}

@[simp] theorem collar_weakenSep : collar (G.weakenSep h) = collar G := rfl

@[simp] theorem dataSites_weakenSep : dataSites (G.weakenSep h) = dataSites G := rfl

@[simp] theorem isLayerConstant_weakenSep {β : Type*} (Ψ : Torus d (N₀ * L ^ k) → β) :
    IsLayerConstant (G.weakenSep h) Ψ ↔ IsLayerConstant G Ψ := Iff.rfl

/-- The data of `G` as data of the weakened set (same fields). -/
def _root_.Balaban.Background.BgData.weaken (D : BgData G N) : BgData (G.weakenSep h) N where
  Ψ := D.Ψ
  h := D.h
  Ψ_layerConst := D.Ψ_layerConst
  h_layerConst := D.h_layerConst
  Ψ_zero := D.Ψ_zero
  h_zero := D.h_zero

/-- The data of the weakened set as data of `G` (same fields). -/
def _root_.Balaban.Background.BgData.unweaken (D : BgData (G.weakenSep h) N) : BgData G N where
  Ψ := D.Ψ
  h := D.h
  Ψ_layerConst := D.Ψ_layerConst
  h_layerConst := D.h_layerConst
  Ψ_zero := D.Ψ_zero
  h_zero := D.h_zero

/-- `BgData (G.weakenSep h) N ≃ BgData G N`: identity on the fields. -/
def _root_.Balaban.Background.BgData.weakenEquiv : BgData G N ≃ BgData (G.weakenSep h) N where
  toFun := BgData.weaken G h
  invFun := BgData.unweaken G h
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem _root_.Balaban.Background.BgData.weaken_Ψ (D : BgData G N) : (D.weaken G h).Ψ = D.Ψ := rfl
@[simp] theorem _root_.Balaban.Background.BgData.weaken_h (D : BgData G N) : (D.weaken G h).h = D.h := rfl

theorem _root_.Balaban.Background.BgData.isReal_weaken (D : BgData G N) : (D.weaken G h).IsReal ↔ D.IsReal := Iff.rfl

theorem inPsiTilde_weakenSep (ν δ : ℝ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (c : Fin N → ℝ) :
    InPsiTilde (G.weakenSep h) ν δ Ψ c ↔ InPsiTilde G ν δ Ψ c :=
  ⟨fun H => ⟨H.layerConst, H.r1, H.r2, H.r3, H.r4⟩, fun H => ⟨H.layerConst, H.r1, H.r2, H.r3, H.r4⟩⟩

theorem inDomainR_weaken (ν δ : ℝ) (D : BgData G N) :
    InDomainR (G.weakenSep h) ν δ (D.weaken G h) ↔ InDomainR G ν δ D := by
  unfold InDomainR
  simp only [inPsiTilde_weakenSep]
  exact Iff.rfl

theorem inDomainR_weakenSep (ν δ : ℝ) (D : BgData (G.weakenSep h) N) :
    InDomainR (G.weakenSep h) ν δ D ↔ InDomainR G ν δ (D.unweaken G h) := by
  exact inDomainR_weaken G h ν δ (D.unweaken G h)

theorem inPsiTildeC_weakenSep (ν δ ε : ℝ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ)
    (c : Fin N → ℝ) (Ψ' h' : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    InPsiTildeC (G.weakenSep h) ν δ ε Ψ c Ψ' h' ↔ InPsiTildeC G ν δ ε Ψ c Ψ' h' :=
  ⟨fun H => ⟨(inPsiTilde_weakenSep G h ν δ Ψ c).1 H.toInPsiTilde, H.eps_pos, H.layerConst',
      H.hLayerConst', H.c1, H.c2a, H.c2b, H.c3a, H.c3b⟩,
   fun H => ⟨(inPsiTilde_weakenSep G h ν δ Ψ c).2 H.toInPsiTilde, H.eps_pos, H.layerConst',
      H.hLayerConst', H.c1, H.c2a, H.c2b, H.c3a, H.c3b⟩⟩

theorem inDomainC_weaken (ν δ ε : ℝ) (D : BgData G N) :
    InDomainC (G.weakenSep h) ν δ ε (D.weaken G h) ↔ InDomainC G ν δ ε D := by
  unfold InDomainC
  simp only [inPsiTildeC_weakenSep]
  exact Iff.rfl

theorem inDomainC_weakenSep (ν δ ε : ℝ) (D : BgData (G.weakenSep h) N) :
    InDomainC (G.weakenSep h) ν δ ε D ↔ InDomainC G ν δ ε (D.unweaken G h) :=
  inDomainC_weaken G h ν δ ε (D.unweaken G h)

theorem inUnionDomainC_weaken (c₀ c₁ ν : ℝ) (D : BgData G N) :
    InUnionDomainC (G.weakenSep h) c₀ c₁ ν (D.weaken G h) ↔ InUnionDomainC G c₀ c₁ ν D := by
  unfold InUnionDomainC
  simp only [inDomainC_weaken]

theorem inUnionDomainC_weakenSep (c₀ c₁ ν : ℝ) (D : BgData (G.weakenSep h) N) :
    InUnionDomainC (G.weakenSep h) c₀ c₁ ν D ↔ InUnionDomainC G c₀ c₁ ν (D.unweaken G h) :=
  inUnionDomainC_weaken G h c₀ c₁ ν (D.unweaken G h)

/-! ### Comparison with other sets -/

variable {ϱ₂ : ℝ} (G' : GeneratingSet d L N₀ k ϱ₂)

theorem precedes_weakenSep_left : Precedes (G.weakenSep h) G' ↔ Precedes G G' := Iff.rfl

theorem precedes_weakenSep_right : Precedes G' (G.weakenSep h) ↔ Precedes G' G := Iff.rfl

end Background

section Cast

variable {N₀' : ℕ} [NeZero N₀'] (e : N₀' = N₀) (G : GeneratingSet d L N₀' k ϱ') (h : ϱ ≤ ϱ')

theorem castG_weakenSep :
    SmallField.GsSpec.castG e (G.weakenSep h) = (SmallField.GsSpec.castG e G).weakenSep h := by
  subst e
  rfl

end Cast

section Spec

open SmallField.GsSpec

theorem gsSpecCore_weakenSep {j : ℕ} {X : Set (Torus d (N₀ * L ^ k))}
    (G : GeneratingSet d L N₀ k ϱ') (h : ϱ ≤ ϱ') :
    GsSpecCore j X (G.weakenSep h) ↔ GsSpecCore j X G :=
  ⟨fun H => ⟨H.subset, H.noAbove, H.topLayer⟩, fun H => ⟨H.subset, H.noAbove, H.topLayer⟩⟩

/-- `GsSpecStrong` is independent of the separation index (it is stated through the layers, and the
whole-level set `levelGS` has the same layers at every index). -/
theorem gsSpecStrong_weakenSep {N₁ m₁ : ℕ} [NeZero N₁] {j : ℕ} (hjk : j ≤ k)
    {X : Set (Localization.CTorus d L N₁ m₁ k)} (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ') (h : ϱ ≤ ϱ') :
    GsSpecStrong j hjk X (G.weakenSep h) ↔ GsSpecStrong j hjk X G := by
  constructor
  · intro H
    exact ⟨(gsSpecCore_weakenSep G h).1 H.toGsSpecCore, fun z hz => H.layerEq z hz,
      fun z hz => H.blkEq z hz⟩
  · intro H
    exact ⟨(gsSpecCore_weakenSep G h).2 H.toGsSpecCore, fun z hz => H.layerEq z hz,
      fun z hz => H.blkEq z hz⟩

end Spec

section Minimal

open Balaban.LargeField

variable {M1 N₁ q : ℕ} [NeZero M1] [NeZero N₁] {j : ℕ}

/-- The minimal set of a polymer, viewed at any separation `ϱ ≤ minSep L M1`. -/
noncomputable def minimalGenSetAt (hj : j ≤ q) (X : Finset (Torus d (M1 * N₁ * L ^ q)))
    {ϱ : ℝ} (h : ϱ ≤ minSep L M1) : GeneratingSet d L (M1 * N₁) q ϱ :=
  (minimalGenSet hj X).weakenSep h

theorem minimalGenSetAt_Ω (hj : j ≤ q) (X : Finset (Torus d (M1 * N₁ * L ^ q)))
    {ϱ : ℝ} (h : ϱ ≤ minSep L M1) (n : ℕ) :
    (minimalGenSetAt hj X h).Ω n = minLayer M1 N₁ L q j X n := rfl

/-- The data sites of the minimal set are unchanged by lowering the separation, so the landed
range bound transfers verbatim. -/
theorem localGen_dataSites_range_weakenSep (hL : 2 ≤ L) (hj : j ≤ q)
    (X : Finset (Torus d (M1 * N₁ * L ^ q))) {ϱ : ℝ} (h : ϱ ≤ minSep L M1)
    {x : Torus d (M1 * N₁ * L ^ q)} (hx : x ∈ Background.dataSites (minimalGenSetAt hj X h)) :
    ∃ y ∈ X, supDist x y ≤ 11 * M1 * L ^ j + 1 :=
  localGen_dataSites_range X hL hj hx

/-- If `bgR0 d L ≤ 5 L M1` the minimal set is a generating set of separation `bgR0 d L`
(with the same layers and data sites). -/
noncomputable def minimalGenSetAtR0 (hj : j ≤ q) (X : Finset (Torus d (M1 * N₁ * L ^ q)))
    (hR : Background.bgR0 d L ≤ minSep L M1) : GeneratingSet d L (M1 * N₁) q (Background.bgR0 d L) :=
  minimalGenSetAt hj X hR

omit [NeZero L] [NeZero M1] in
/-- The criterion for `hR`: `bgR0 d L / (5 L) ≤ M1`. -/
theorem bgR0_le_minSep_of_div (hL : 0 < L) (hM : Background.bgR0 d L / (5 * L) ≤ M1) :
    Background.bgR0 d L ≤ minSep L M1 := (bgR0_le_minSep_iff hL).2 hM

/-- Monotonicity in the polymer survives weakening. -/
theorem minimalGenSetAt_precedes (hj : j ≤ q) {X X' : Finset (Torus d (M1 * N₁ * L ^ q))}
    {ϱ ϱ₂ : ℝ} (h : ϱ ≤ minSep L M1) (h₂ : ϱ₂ ≤ minSep L M1) (hX : X ⊆ X') :
    Background.Precedes (minimalGenSetAt hj X h) (minimalGenSetAt hj X' h₂) :=
  minimalGenSet_mono hj hX

end Minimal

section Instance

open Balaban.LargeField

/-- Non-vacuity: for `d = L = 3` and `M1 = 3 ^ m` with `bgR0 3 3 ≤ 15 · 3 ^ m` (such `m` exist),
the minimal set of the empty polymer weakened to `bgR0 3 3`. -/
theorem exists_minimalGenSet_bgR0 :
    ∃ m : ℕ, Background.bgR0 3 3 ≤ minSep 3 (3 ^ m) := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (Background.bgR0 3 3 / 15) (by norm_num : (1 : ℝ) < 3)
  refine ⟨m, ?_⟩
  unfold minSep
  push_cast
  rw [div_lt_iff₀ (by norm_num)] at hm
  linarith

/-- The weakened minimal set has the layers of the original. -/
theorem minimalGenSetAtR0_layer (m n : ℕ) (hR : Background.bgR0 3 3 ≤ minSep 3 (3 ^ m))
    (X : Finset (Torus 3 (3 ^ m * 1 * 3 ^ 2))) :
    (minimalGenSetAtR0 (L := 3) (N₁ := 1) (q := 2) (j := 2) le_rfl X hR).layer n =
      (minimalGenSet (L := 3) (N₁ := 1) (q := 2) (j := 2) le_rfl X).layer n := rfl

end Instance

end Balaban.Multiscale
