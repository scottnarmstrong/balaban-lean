/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusXGreen
public import Balaban.Localization.Decoupled2XLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The x-variant decoupled Green operator on two tori, for a cover without the mass bound

The comparisons `cubeGx_boxMap`, `Gstarx_block`, ..., `xGreen_rows_transport` of
`Balaban.Polymer.TwoTorusXGreen` assume `XSetting`, whose `DGSetting` contains the mass bound
`ν L^(2 K) ≤ 1`.  The first fluctuation integral of the first step uses the operator at the mass
`ν + x`, `x ≥ 0` unbounded (the Stieltjes integral of `BaseXSqrt`), where no mass bound holds; the
x-variant chain of `Dec2.XCover` never uses one.  This file proves the same statements for
`Dec2.XCover (coverOf G) G a aT ν Cx` on the top-level generating sets `levelGS (k + 1)` of two
tori (the cube resolvent, the block identities of `G*_{x,s}` and `𝒦_{x,s}`, and the rows of
`G_{k,x,s}(A) f` on a set `T` and on a component `Y ⊇ T`).  The statements of `TwoTorusXGreen` are
the instances `Dec2.xCover_self` of these.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.LargeField.Base.XC

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background Matrix Balaban.Polymer.TwoTorusStep

section XLevel

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {Cx : ℝ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
local notation "ιb" x:max => Subtype.mk (bm (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) (ϱ := ϱ)
    (Nat.le_add_left 1 k) le_rfl _)

/-- **The x-variant cube resolvent** `G^{(z)}_x(A) c_z` of the centre `(k+1, y0)`: its entries at
two sites of the box of radius `R = ρ₀ + 3 L^(k+1+m₁)` correspond, for potentials corresponding on
that box.  Margins: `2 R + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` and `2 (R + 2 + R) + 1 < N₁ L^m₁ L^(k+1)`
(and for `N₁'`). -/
theorem cubeGx_boxMap {ρ₀ : ℕ} {a : ℕ → ℝ} {aT x₀ ν : ℝ} (SA : Dec2.XCover (coverOf (GA)) (GA) a aT ν Cx)
    (SB : Dec2.XCover (coverOf (GB)) (GB) a aT ν Cx) (hx₀ : 0 ≤ x₀) {y0 : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ (k + 1)) y0)
    (hq : ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ cubeIdx (GA))
    (hn : 2 * (ρ₀ + 3 * L ^ (k + 1 + m₁)) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * (ρ₀ + 3 * L ^ (k + 1 + m₁)) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hm : 2 * ((ρ₀ + 3 * L ^ (k + 1 + m₁)) + 2 + (ρ₀ + 3 * L ^ (k + 1 + m₁))) + 1 <
      (N₁ * L ^ m₁) * L ^ (k + 1))
    (hm' : 2 * ((ρ₀ + 3 * L ^ (k + 1 + m₁)) + 2 + (ρ₀ + 3 * L ^ (k + 1 + m₁))) + 1 <
      (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot _ α) (hαB : AdmPot _ α')
    (hα : ∀ x : (GA).Ω 1, InBox d (ρ₀ + 3 * L ^ (k + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ (k + 1))
      (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) → α' (ιb x) = α x)
    (x y : (GA).Ω 1)
    (hx : InBox d (ρ₀ + 3 * L ^ (k + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ (k + 1))
      (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
    (hy : InBox d (ρ₀ + 3 * L ^ (k + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ (k + 1))
      (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1))) :
    cubeGx (GB) a aT x₀ ν α' (Prod.map id bm ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
        (ιb x) (ιb y) =
      cubeGx (GA) a aT x₀ ν α (k + 1, y0) x y := by
  classical
  rw [show Prod.map id bm ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) = (k + 1, bm y0) from rfl]
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  set R : ℕ := ρ₀ + 3 * L ^ (k + 1 + m₁) with hR
  have hn1 : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := lt_of_le_of_lt (by omega) hn
  have hn2 : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := lt_of_le_of_lt (by omega) hn'
  have hy0' : InBox d ρ₀ ((N₁' * L ^ m₁) * L ^ (k + 1)) (bm y0) := inBox_boxMap (by omega) hy0
  have hq' : ((k + 1, bm y0) : ℕ × Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈ cubeIdx (GB) := by
    obtain ⟨y1, he, hb⟩ := exists_of_mem_cubeIdx le_rfl hq
    have : y0 = y1 := (Prod.mk.inj he).2
    subst this
    exact (mem_cubeIdx_levelGS le_rfl _).2 ⟨rfl, Nat.le_add_left 1 k, cubeBase_boxMap le_rfl hb⟩
  obtain ⟨ι, hι⟩ : ∃ ι : (GA).Ω 1 → (GB).Ω 1, ∀ z, ι z = ιb z := ⟨_, fun _ => rfl⟩
  rw [← hι, ← hι]
  have hcubeA : ∀ z : (GA).Ω 1, (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈
      intBox ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) →
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) :=
    fun z h => inBox_of_mem_intBox hy0 hn1 h
  have hcubeB : ∀ z : (GB).Ω 1, (z : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈
      intBox ((k + 1, bm y0) : ℕ × Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) →
      InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) (z : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) :=
    fun z h => inBox_of_mem_intBox hy0' hn2 h
  have hiff : ∀ z : (GA).Ω 1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) →
      ((z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ intBox ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ↔
        ((ι z : _) : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈
          intBox ((k + 1, bm y0) : ℕ × Balaban.Localization.CTorus d L N₁' m₁ (k + 1))) := by
    intro z hz
    rw [hι]
    exact mem_intBox_boxMap_iff_of_le (N₁' := N₁') hy0 le_rfl hn1 hn2 hz
  have hinj : ∀ a b : (GA).Ω 1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (a : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) →
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (b : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) → ι a = ι b → a = b := by
    intro a b ha hb h
    rw [hι, hι] at h
    exact Subtype.ext (boxMap_inj (hm' := hn2) ha hb (congrArg Subtype.val h))
  have hsurj : ∀ z' : (GB).Ω 1, (z' : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈
      intBox ((k + 1, bm y0) : ℕ × Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) →
      ∃ z : (GA).Ω 1, (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈
        intBox ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∧ ι z = z' := by
    intro z' h
    have hb' := hcubeB z' h
    have hback : bm (bm' (z' : Balaban.Localization.CTorus d L N₁' m₁ (k + 1))) = z' := boxMap_boxMap hn1 hb'
    obtain ⟨zz, hzz⟩ : ∃ zz : (GA).Ω 1,
        (zz : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) = bm' (z' : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) :=
      ⟨⟨_, levelGS_mem_Ω_one (Nat.le_add_left 1 k) le_rfl _⟩, rfl⟩
    have hz1 : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (zz : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) := by
      rw [hzz]; exact inBox_boxMap hn1 hb'
    have hιz : ι zz = z' := by
      rw [hι]
      refine Subtype.ext ?_
      show bm (zz : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) = _
      rw [hzz]; exact hback
    refine ⟨zz, (hiff zz hz1).2 (by rw [hιz]; exact h), hιz⟩
  have hcore : ∀ x y : (GA).Ω 1,
      (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ intBox ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) →
      (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ intBox ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) →
      cubeGx (GB) a aT x₀ ν α' (k + 1, bm y0) (ι x) (ι y) =
        cubeGx (GA) a aT x₀ ν α (k + 1, y0) x y := by
    intro x y hxc hyc
    unfold cubeGx
    refine inv_block_transport (fun z : (GA).Ω 1 => (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈
        intBox ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
      (fun z : (GB).Ω 1 => (z : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈
        intBox ((k + 1, bm y0) : ℕ × Balaban.Localization.CTorus d L N₁' m₁ (k + 1))) ι
      (fun a b ha hb h => hinj a b (hcubeA a ha) (hcubeA b hb) h)
      (fun z hz => (hiff z (hcubeA z hz)).1 hz) hsurj _ _ _ _
      (fun f z => cD_mulVec _ f z) (fun f z => cD_mulVec _ f z) ?_ ?_
      (Dec2.cubeHx_isUnit SA hαA hx₀ hq) (Dec2.cubeHx_isUnit SB hαB hx₀ hq') ?_ hxc hyc
    · intro x z hx hz
      rw [hι, hι]
      exact cubeHx_boxMap (ρ := R) (ρ₀ := ρ₀) a aT x₀ ν hy0 hn hn' hm hm' hα x z
        (hcubeA x hx) (hcubeA z hz)
    · intro u hu x hx
      exact cutXOperator_mulVec_apply_of_not_mem (SA.blockAligned _ hq) hu x hx
    · intro f z hz
      exact Dec2.cubeGx_supp SB hαB hx₀ hq' f z hz
  by_cases hyc : (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ intBox ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1))
  · by_cases hxc : (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈
        intBox ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1))
    · exact hcore x y hxc hyc
    · have hxc' : ¬ ((ι x : _) : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈
          intBox ((k + 1, bm y0) : ℕ × Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) := fun h => hxc ((hiff x hx).2 h)
      have e1 := Dec2.cubeGx_supp SA hαA hx₀ hq (Pi.single y 1) x hxc
      have e2 := Dec2.cubeGx_supp SB hαB hx₀ hq' (Pi.single (ι y) 1) (ι x) hxc'
      rw [cubeGx_mulVec_single] at e1 e2
      rw [e1]; exact e2
  · have hyc' : ¬ ((ι y : _) : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈
        intBox ((k + 1, bm y0) : ℕ × Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) := fun h => hyc ((hiff y hy).2 h)
    rw [cubeGx_apply_of_not_mem _ _ _ hyc, cubeGx_apply_of_not_mem _ _ _ hyc']

end XLevel

/-! ### The block identities of the x-variant on one torus -/

section XBlock

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {Cx : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x₀ ν : ℝ}
  {α : G.Ω 1 → ℂ}

/-- **The block identity for `G*_{x,s}`.**  If every interaction cube with a non-zero factor lies
inside `T` or avoids it, then `P G*_{x,s} = G*_{x,s} P = ∑_{z inner} s_z χ_z G^{(z)}_x c_z`, `P` the
indicator of `T`. -/
theorem Gstarx_block (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hx : 0 ≤ x₀) (hα : AdmPot G α)
    {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T) :
    indY G T * Gstarx G a aT x₀ ν α s =
        ∑ q ∈ innerCentres G T, sProd G s q • (chiD G q * cubeGx G a aT x₀ ν α q) ∧
      Gstarx G a aT x₀ ν α s * indY G T =
        ∑ q ∈ innerCentres G T, sProd G s q • (chiD G q * cubeGx G a aT x₀ ν α q) := by
  have hM : ∀ q ∈ cubeIdx G, RowSupp (chiD G q * cubeGx G a aT x₀ ν α q) (intBox q) ∧
      chiD G q * cubeGx G a aT x₀ ν α q * cD G q = chiD G q * cubeGx G a aT x₀ ν α q :=
    fun q hq => ⟨Dec2.rowSupp_chi_cubeGx S hx hα hq, by rw [Matrix.mul_assoc, cubeGx_mul_cD]⟩
  obtain ⟨hin, hout⟩ := blk_conditions (s := s) _ hM hdich
  exact sum_block_facts _ hin hout

/-- **The block identity for `𝒦_{x,s}`**: `P 𝒦_{x,s} = 𝒦_{x,s} P = ∑_{z inner} s_z K^x_z G^{(z)}_x c_z`. -/
theorem Kcalx_block (S : Dec2.XCover (coverOf G) G a aT ν Cx) {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T) :
    indY G T * Kcalx G a aT x₀ ν α s =
        ∑ q ∈ innerCentres G T, sProd G s q • (Kzx G a aT x₀ ν q * cubeGx G a aT x₀ ν α q) ∧
      Kcalx G a aT x₀ ν α s * indY G T =
        ∑ q ∈ innerCentres G T, sProd G s q • (Kzx G a aT x₀ ν q * cubeGx G a aT x₀ ν α q) := by
  have hM : ∀ q ∈ cubeIdx G, RowSupp (Kzx G a aT x₀ ν q * cubeGx G a aT x₀ ν α q) (intBox q) ∧
      Kzx G a aT x₀ ν q * cubeGx G a aT x₀ ν α q * cD G q =
        Kzx G a aT x₀ ν q * cubeGx G a aT x₀ ν α q :=
    fun q hq => ⟨Dec2.rowSupp_Kzx_cubeGx S hq, by rw [Matrix.mul_assoc, cubeGx_mul_cD]⟩
  obtain ⟨hin, hout⟩ := blk_conditions (s := s) _ hM hdich
  exact sum_block_facts _ hin hout

theorem indY_mul_Kcalx_comm (S : Dec2.XCover (coverOf G) G a aT ν Cx) {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T) :
    indY G T * Kcalx G a aT x₀ ν α s = Kcalx G a aT x₀ ν α s * indY G T := by
  obtain ⟨h1, h2⟩ := Kcalx_block (x₀ := x₀) (α := α) S hdich
  rw [h1, h2]

theorem indY_mul_Gstarx_comm (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hx : 0 ≤ x₀) (hα : AdmPot G α)
    {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T) :
    indY G T * Gstarx G a aT x₀ ν α s = Gstarx G a aT x₀ ν α s * indY G T := by
  obtain ⟨h1, h2⟩ := Gstarx_block S hx hα hdich
  rw [h1, h2]

theorem Kcalx_apply_eq_zero_of_mem (S : Dec2.XCover (coverOf G) G a aT ν Cx) {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x z : G.Ω 1} (hx : (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T)
    (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∉ T) : Kcalx G a aT x₀ ν α s x z = 0 := by
  have h := congrFun (congrFun (indY_mul_Kcalx_comm (x₀ := x₀) (α := α) S hdich) x) z
  rw [indY_mul_apply, mul_indY_apply, ite_eq_left hx, ite_eq_right hz] at h
  exact h

theorem Kcalx_apply_eq_zero_of_not_mem (S : Dec2.XCover (coverOf G) G a aT ν Cx)
    {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x z : G.Ω 1} (hx : (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∉ T)
    (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T) : Kcalx G a aT x₀ ν α s x z = 0 := by
  have h := congrFun (congrFun (indY_mul_Kcalx_comm (x₀ := x₀) (α := α) S hdich) x) z
  rw [indY_mul_apply, mul_indY_apply, ite_eq_right hx, ite_eq_left hz] at h
  exact h.symm

theorem Gstarx_apply_eq_zero_of_mem (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hx₀ : 0 ≤ x₀) (hα : AdmPot G α)
    {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x z : G.Ω 1} (hx : (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T)
    (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∉ T) : Gstarx G a aT x₀ ν α s x z = 0 := by
  have h := congrFun (congrFun (indY_mul_Gstarx_comm S hx₀ hα hdich) x) z
  rw [indY_mul_apply, mul_indY_apply, ite_eq_left hx, ite_eq_right hz] at h
  exact h

/-- The row at a site of `T` of `G*_{x,s}` is the sum over the cubes inside `T`. -/
theorem Gstarx_apply_of_mem (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hx₀ : 0 ≤ x₀) (hα : AdmPot G α)
    {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x : G.Ω 1} (hx : (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T) (z : G.Ω 1) :
    Gstarx G a aT x₀ ν α s x z =
      ∑ q ∈ innerCentres G T, sProd G s q * (chiD G q * cubeGx G a aT x₀ ν α q) x z := by
  have h := congrFun (congrFun (Gstarx_block S hx₀ hα hdich).1 x) z
  rw [indY_mul_apply, ite_eq_left hx, Matrix.sum_apply] at h
  rw [h]
  simp only [Matrix.smul_apply, smul_eq_mul]

/-- The row at a site of `T` of `𝒦_{x,s}` is the sum over the cubes inside `T`. -/
theorem Kcalx_apply_of_mem (S : Dec2.XCover (coverOf G) G a aT ν Cx) {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x : G.Ω 1} (hx : (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T) (z : G.Ω 1) :
    Kcalx G a aT x₀ ν α s x z =
      ∑ q ∈ innerCentres G T, sProd G s q * (Kzx G a aT x₀ ν q * cubeGx G a aT x₀ ν α q) x z := by
  have h := congrFun (congrFun (Kcalx_block (x₀ := x₀) (α := α) S hdich).1 x) z
  rw [indY_mul_apply, ite_eq_left hx, Matrix.sum_apply] at h
  rw [h]
  simp only [Matrix.smul_apply, smul_eq_mul]

/-- **Rows of `G_{k,x,s}(A) f` outside `T`.**  If every active interaction cube meets `Y` only
inside `T`, the rows of `G_{k,x,s}(A) f` on `Y \ T` vanish. -/
theorem Gsx_apply_eq_zero_of_not_mem (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hx₀ : 0 ≤ x₀) (hα : AdmPot G α)
    {Y T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hrow : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (f : G.Ω 1 → ℂ) {y : G.Ω 1} (hyY : (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Y)
    (hyT : (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∉ T) : (Gsx G a aT x₀ ν α s *ᵥ f) y = 0 := by
  unfold Gsx Gstarx
  rw [← Matrix.mulVec_mulVec, Matrix.sum_mulVec, Finset.sum_apply]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  by_cases hs : sProd G s q = 0
  · rw [hs, zero_mul]
  · have hyq : (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∉ intBox q := fun h => hyT (hrow q hq hs _ hyY h)
    have h0 : ((chiD G q * cubeGx G a aT x₀ ν α q) *ᵥ ((1 - Kcalx G a aT x₀ ν α s)⁻¹ *ᵥ f)) y = 0 :=
      Dec2.rowSupp_chi_cubeGx S hx₀ hα hq _ y hyq
    rw [h0, mul_zero]

/-- **Rows of `G_{k,x,s}(A)` on `T` read only `T`.**  Under the dichotomy, the entries of
`G_{k,x,s}(A)` from a row in `T` to a column outside `T` vanish. -/
theorem Gsx_apply_eq_zero_of_mem (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hx₀ : 0 ≤ x₀) (hα : AdmPot G α)
    {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hU : IsUnit (1 - Kcalx G a aT x₀ ν α s))
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x z : G.Ω 1} (hx : (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T)
    (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∉ T) : Gsx G a aT x₀ ν α s x z = 0 := by
  have hK := indY_mul_Kcalx_comm (x₀ := x₀) (α := α) S hdich
  have hX := indY_mul_Gstarx_comm S hx₀ hα hdich
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have h1 : indY G T * (1 - Kcalx G a aT x₀ ν α s) = (1 - Kcalx G a aT x₀ ν α s) * indY G T := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hK]
  have h2 : indY G T * (1 - Kcalx G a aT x₀ ν α s)⁻¹ =
      (1 - Kcalx G a aT x₀ ν α s)⁻¹ * indY G T := by
    set Kc := 1 - Kcalx G a aT x₀ ν α s with hKc
    calc indY G T * Kc⁻¹ = (Kc⁻¹ * Kc) * indY G T * Kc⁻¹ := by
          rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
      _ = Kc⁻¹ * (Kc * indY G T) * Kc⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Kc⁻¹ * (indY G T * Kc) * Kc⁻¹ := by rw [h1]
      _ = Kc⁻¹ * indY G T * (Kc * Kc⁻¹) := by simp only [Matrix.mul_assoc]
      _ = Kc⁻¹ * indY G T := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  have h3 : indY G T * Gsx G a aT x₀ ν α s = Gsx G a aT x₀ ν α s * indY G T := by
    unfold Gsx
    rw [← Matrix.mul_assoc, hX, Matrix.mul_assoc, h2, Matrix.mul_assoc]
  have h := congrFun (congrFun h3 x) z
  rw [indY_mul_apply, mul_indY_apply, ite_eq_left hx, ite_eq_right hz] at h
  exact h

end XBlock

/-! ### The rows of the x-variant decoupled Green operator on two tori -/

section XRows

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {Cx : ℝ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
local notation "ιb" x:max => Subtype.mk (bm (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) (ϱ := ϱ)
    (Nat.le_add_left 1 k) le_rfl _)

/-- **The x-variant cube resolvent of a cube inside `T`**, with potentials corresponding on `T`
only.  Margin: `4 R + 12 L^(k+1+m₁) + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem cubeGx_boxMap_inner {a : ℕ → ℝ} {aT x₀ ν : ℝ} (SA : Dec2.XCover (coverOf (GA)) (GA) a aT ν Cx)
    (SB : Dec2.XCover (coverOf (GB)) (GB) a aT ν Cx) (hx₀ : 0 ≤ x₀) {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {T' : Finset (Balaban.Localization.CTorus d L N₁' m₁ (k + 1))} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
    (hα : ∀ x : (GA).Ω 1, (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T → α' (ιb x) = α x)
    {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ innerCentres (GA) T) (x z : (GA).Ω 1)
    (hx : InBox d (R + 3 * L ^ (k + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ (k + 1))
      (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
    (hz : InBox d (R + 3 * L ^ (k + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ (k + 1))
      (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1))) :
    cubeGx (GB) a aT x₀ ν α' (Prod.map id bm q) (ιb x) (ιb z) = cubeGx (GA) a aT x₀ ν α q x z := by
  have hj1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hq' := innerCentres_mapsTo hj1 le_rfl hT' hTR (by omega) (by omega) hq
  obtain ⟨y0, rfl, -, hy0T, -⟩ := inner_base_mem hj1 le_rfl hq
  have hy0 := hTR y0 hy0T
  have hqc : ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ cubeIdx (GA) :=
    (Finset.mem_filter.1 hq).1
  have hspA : ∀ w : Balaban.Localization.CTorus d L N₁ m₁ (k + 1), (GA).spacing w = (L : ℝ) ^ (k + 1) := fun w => by
    unfold GeneratingSet.spacing; rw [layerIndex_levelGS hj1 le_rfl]
  have hspB : ∀ w : Balaban.Localization.CTorus d L N₁' m₁ (k + 1), (GB).spacing w = (L : ℝ) ^ (k + 1) := fun w => by
    unfold GeneratingSet.spacing; rw [layerIndex_levelGS hj1 le_rfl]
  obtain ⟨α'', hα''⟩ : ∃ α'' : (GB).Ω 1 → ℂ, α'' = fun w : (GB).Ω 1 =>
      if InBox d (R + 3 * L ^ (k + 1 + m₁)) ((N₁' * L ^ m₁) * L ^ (k + 1))
          (w : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) then
        α ⟨bm' (w : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)), levelGS_mem_Ω_one hj1 le_rfl _⟩ else α' w :=
    ⟨_, rfl⟩
  have hα''B : AdmPot (GB) α'' := by
    intro w
    rw [hα'']
    dsimp only
    split_ifs with hw
    · have h1 := hαA ⟨bm' (w : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)), levelGS_mem_Ω_one hj1 le_rfl _⟩
      rw [hspA] at h1
      rw [hspB]
      exact h1
    · exact hαB w
  have hα''x : ∀ x : (GA).Ω 1, InBox d (R + 3 * L ^ (k + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ (k + 1))
      (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) → α'' (ιb x) = α x := by
    intro x hx
    have h1 : InBox d (R + 3 * L ^ (k + 1 + m₁)) ((N₁' * L ^ m₁) * L ^ (k + 1))
        (bm (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1))) := inBox_boxMap (by omega) hx
    rw [hα'']
    dsimp only
    split_ifs
    congr 1
    exact Subtype.ext (boxMap_boxMap (by omega) hx)
  have hagree'' : ∀ w : (GB).Ω 1, (w : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈
      intBox (Prod.map id bm ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1))) → α' w = α'' w := by
    intro w hw
    have hwT : (w : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈ T' := (Finset.mem_filter.1 hq').2 w hw
    rw [← hT', Finset.mem_image] at hwT
    obtain ⟨x, hxT, hxw⟩ := hwT
    have hw' : w = ιb (⟨x, levelGS_mem_Ω_one hj1 le_rfl x⟩ : (GA).Ω 1) := Subtype.ext hxw.symm
    rw [hw', hα ⟨x, levelGS_mem_Ω_one hj1 le_rfl x⟩ hxT,
      hα''x ⟨x, levelGS_mem_Ω_one hj1 le_rfl x⟩ (inBox_mono (by omega) (hTR x hxT))]
  rw [Dec2.cubeGx_congr SB hx₀ hαB hα''B (Finset.mem_filter.1 hq').1 hagree'']
  exact cubeGx_boxMap (ρ₀ := R) SA SB hx₀ hy0 hqc (by omega) (by omega) (by omega) (by omega)
    hαA hα''B hα''x x z hx hz

/-- The entries of `χ_z G^{(z)}_x c_z` of a cube inside `T` at two sites of `T` correspond. -/
theorem chiD_cubeGx_boxMap_inner {a : ℕ → ℝ} {aT x₀ ν : ℝ} (SA : Dec2.XCover (coverOf (GA)) (GA) a aT ν Cx)
    (SB : Dec2.XCover (coverOf (GB)) (GB) a aT ν Cx) (hx₀ : 0 ≤ x₀) {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {T' : Finset (Balaban.Localization.CTorus d L N₁' m₁ (k + 1))} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
    (hα : ∀ x : (GA).Ω 1, (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T → α' (ιb x) = α x)
    {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ innerCentres (GA) T) (x z : (GA).Ω 1)
    (hx : (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T) (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T) :
    (chiD (GB) (Prod.map id bm q) * cubeGx (GB) a aT x₀ ν α' (Prod.map id bm q)) (ιb x) (ιb z) =
      (chiD (GA) q * cubeGx (GA) a aT x₀ ν α q) x z := by
  have hj1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hxR := hTR _ hx
  have hzR := hTR _ hz
  unfold chiD
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul, cubeGx_boxMap_inner SA SB hx₀ hT' hTR hn hn'
    hαA hαB hα hq x z (inBox_mono (by omega) hxR) (inBox_mono (by omega) hzR)]
  obtain ⟨y0, rfl, -, hy0T, -⟩ := inner_base_mem hj1 le_rfl hq
  have hy0 := hTR y0 hy0T
  have hc := chi_boxMap (ϱ := ϱ) (N₁' := N₁') (ρ := R) hj1 le_rfl (by omega) (by omega) hxR
    (inBox_mono (by omega) hy0)
  simp only [hc]

/-- The entries of `K^x_z G^{(z)}_x c_z` of a cube inside `T` at two sites of `T` correspond. -/
theorem Kzx_cubeGx_boxMap_inner {a : ℕ → ℝ} {aT x₀ ν : ℝ} (SA : Dec2.XCover (coverOf (GA)) (GA) a aT ν Cx)
    (SB : Dec2.XCover (coverOf (GB)) (GB) a aT ν Cx) (hx₀ : 0 ≤ x₀) {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {T' : Finset (Balaban.Localization.CTorus d L N₁' m₁ (k + 1))} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
    (hα : ∀ x : (GA).Ω 1, (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T → α' (ιb x) = α x)
    {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ innerCentres (GA) T) (x z : (GA).Ω 1)
    (hx : (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T) (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T) :
    (Kzx (GB) a aT x₀ ν (Prod.map id bm q) * cubeGx (GB) a aT x₀ ν α' (Prod.map id bm q))
        (ιb x) (ιb z) =
      (Kzx (GA) a aT x₀ ν q * cubeGx (GA) a aT x₀ ν α q) x z := by
  have hj1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hq' := innerCentres_mapsTo hj1 le_rfl hT' hTR (by omega) (by omega) hq
  have hqc' := (Finset.mem_filter.1 hq').1
  have hqc := (Finset.mem_filter.1 hq).1
  have hxR := hTR _ hx
  have hzR := hTR _ hz
  have hn1 : 2 * (R + 3 * L ^ (k + 1 + m₁)) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hn2 : 2 * (R + 3 * L ^ (k + 1 + m₁)) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  obtain ⟨y0, rfl, -, hy0T, -⟩ := inner_base_mem hj1 le_rfl hq
  have hy0 := hTR y0 hy0T
  refine mul_apply_transport
    (fun w : (GA).Ω 1 => (w : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈
      intBox ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
    (fun w : (GB).Ω 1 => (w : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈
      intBox (Prod.map id bm ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1))))
    (fun w => ιb w) (fun w1 w2 h1 h2 h => ?_) (fun w hw => ?_) (fun w' hw' => ?_) _ _ _ _
    (fun w hw => ?_) (fun w' hw' => ?_) (fun w hw => ?_)
  · exact Subtype.ext (boxMap_inj (hm' := hn2) (inBox_of_mem_intBox hy0 hn1 h1)
      (inBox_of_mem_intBox hy0 hn1 h2) (congrArg Subtype.val h))
  · exact (mem_intBox_boxMap_iff hy0 hn1 hn2 (inBox_of_mem_intBox hy0 hn1 hw)).1 hw
  · have hw'' : (w' : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈
        intBox (Prod.map id bm ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1))) := hw'
    have hwT : (w' : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈ T' := (Finset.mem_filter.1 hq').2 w' hw''
    rw [← hT', Finset.mem_image] at hwT
    obtain ⟨x2, hx2T, hx2⟩ := hwT
    refine ⟨⟨x2, levelGS_mem_Ω_one hj1 le_rfl x2⟩, ?_, Subtype.ext hx2⟩
    show x2 ∈ intBox ((k + 1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1))
    rw [mem_intBox_boxMap_iff hy0 hn1 hn2 (inBox_mono (by omega) (hTR x2 hx2T)), hx2]
    exact hw''
  · have h1 := Dec2.cubeGx_supp SA hαA hx₀ hqc (Pi.single z 1) w hw
    rw [cubeGx_mulVec_single] at h1
    rw [h1, mul_zero]
  · have h1 := Dec2.cubeGx_supp SB hαB hx₀ hqc' (Pi.single (ιb z) 1) w' hw'
    rw [cubeGx_mulVec_single] at h1
    rw [h1, mul_zero]
  · have hwR := inBox_of_mem_intBox hy0 hn1 hw
    rw [Kzx_boxMap (ρ := R + 3 * L ^ (k + 1 + m₁)) a aT x₀ ν (inBox_mono (by omega) hy0)
      (by omega) (by omega) (by omega) (by omega) x w (inBox_mono (by omega) hxR) hwR,
      cubeGx_boxMap_inner SA SB hx₀ hT' hTR hn hn' hαA hαB hα hq w z hwR
        (inBox_mono (by omega) hzR)]

/-- **`G*_{x,s}` on two tori.**  If every active interaction cube lies inside `T` or avoids it, on
both tori (`T` in the box of radius `R`, `T' = bm '' T`), the factors agree on the cubes inside `T`
and the potentials on `T`, the entries of `G*_{x,s}` at two sites of `T` correspond. -/
theorem Gstarx_boxMap_apply {a : ℕ → ℝ} {aT x₀ ν : ℝ} (SA : Dec2.XCover (coverOf (GA)) (GA) a aT ν Cx)
    (SB : Dec2.XCover (coverOf (GB)) (GB) a aT ν Cx) (hx₀ : 0 ≤ x₀) {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {T' : Finset (Balaban.Localization.CTorus d L N₁' m₁ (k + 1))} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
    (hα : ∀ x : (GA).Ω 1, (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T → α' (ιb x) = α x)
    {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × Balaban.Localization.CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx (GA), sProd (GA) s q ≠ 0 →
      SubI (GA) (intBox q) T ∨ DisjI (GA) (intBox q) T)
    (hdich' : ∀ q ∈ cubeIdx (GB), sProd (GB) s' q ≠ 0 →
      SubI (GB) (intBox q) T' ∨ DisjI (GB) (intBox q) T')
    (hagree : ∀ q ∈ innerCentres (GA) T, sProd (GB) s' (Prod.map id bm q) = sProd (GA) s q)
    (x z : (GA).Ω 1) (hx : (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T)
    (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T) :
    Gstarx (GB) a aT x₀ ν α' s' (ιb x) (ιb z) = Gstarx (GA) a aT x₀ ν α s x z := by
  have hx' : ((ιb x : (GB).Ω 1) : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈ T' := by
    rw [← hT']; exact Finset.mem_image_of_mem _ hx
  rw [Gstarx_apply_of_mem SA hx₀ hαA hdich hx, Gstarx_apply_of_mem SB hx₀ hαB hdich' hx']
  refine sum_innerCentres_boxMap (Nat.le_add_left 1 k) le_rfl hT' hTR (by omega) (by omega) _ _
    fun q hq => ?_
  rw [hagree q hq, chiD_cubeGx_boxMap_inner SA SB hx₀ hT' hTR hn hn' hαA hαB hα hq x z hx hz]

/-- **`𝒦_{x,s}` on two tori.**  Under the hypotheses of `Gstarx_boxMap_apply`, the entries of
`𝒦_{x,s}` at two sites of `T` correspond. -/
theorem Kcalx_boxMap_apply {a : ℕ → ℝ} {aT x₀ ν : ℝ} (SA : Dec2.XCover (coverOf (GA)) (GA) a aT ν Cx)
    (SB : Dec2.XCover (coverOf (GB)) (GB) a aT ν Cx) (hx₀ : 0 ≤ x₀) {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {T' : Finset (Balaban.Localization.CTorus d L N₁' m₁ (k + 1))} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
    (hα : ∀ x : (GA).Ω 1, (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T → α' (ιb x) = α x)
    {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × Balaban.Localization.CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx (GA), sProd (GA) s q ≠ 0 →
      SubI (GA) (intBox q) T ∨ DisjI (GA) (intBox q) T)
    (hdich' : ∀ q ∈ cubeIdx (GB), sProd (GB) s' q ≠ 0 →
      SubI (GB) (intBox q) T' ∨ DisjI (GB) (intBox q) T')
    (hagree : ∀ q ∈ innerCentres (GA) T, sProd (GB) s' (Prod.map id bm q) = sProd (GA) s q)
    (x z : (GA).Ω 1) (hx : (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T)
    (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T) :
    Kcalx (GB) a aT x₀ ν α' s' (ιb x) (ιb z) = Kcalx (GA) a aT x₀ ν α s x z := by
  have hx' : ((ιb x : (GB).Ω 1) : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈ T' := by
    rw [← hT']; exact Finset.mem_image_of_mem _ hx
  rw [Kcalx_apply_of_mem SA hdich hx, Kcalx_apply_of_mem SB hdich' hx']
  refine sum_innerCentres_boxMap (Nat.le_add_left 1 k) le_rfl hT' hTR (by omega) (by omega) _ _
    fun q hq => ?_
  rw [hagree q hq, Kzx_cubeGx_boxMap_inner SA SB hx₀ hT' hTR hn hn' hαA hαB hα hq x z hx hz]

/-- **The rows of `G_{k,x,s}(A) f` on `T`.**  Let `T` be a set of sites of the box of radius `R`
such that every interaction cube with a non-zero factor lies inside `T` or avoids it, on both tori
(`T' = bm '' T`), the factors agree on the cubes inside `T`, `1 - 𝒦_{x,s}` is invertible on each
torus, and the potentials and the sources agree on `T`.  Then `G_{k,x,s}(A) f` and
`G_{k,x,s'}(A') f'` agree on `T` (after `bm`).  Margin:
`4 R + 12 L^(k+1+m₁) + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem Gsx_boxMap_rows {a : ℕ → ℝ} {aT x₀ ν : ℝ} (SA : Dec2.XCover (coverOf (GA)) (GA) a aT ν Cx)
    (SB : Dec2.XCover (coverOf (GB)) (GB) a aT ν Cx) (hx₀ : 0 ≤ x₀) {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {T' : Finset (Balaban.Localization.CTorus d L N₁' m₁ (k + 1))} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
    (hα : ∀ x : (GA).Ω 1, (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T → α' (ιb x) = α x)
    {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × Balaban.Localization.CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hU : IsUnit (1 - Kcalx (GA) a aT x₀ ν α s)) (hU' : IsUnit (1 - Kcalx (GB) a aT x₀ ν α' s'))
    (hdich : ∀ q ∈ cubeIdx (GA), sProd (GA) s q ≠ 0 →
      SubI (GA) (intBox q) T ∨ DisjI (GA) (intBox q) T)
    (hdich' : ∀ q ∈ cubeIdx (GB), sProd (GB) s' q ≠ 0 →
      SubI (GB) (intBox q) T' ∨ DisjI (GB) (intBox q) T')
    (hagree : ∀ q ∈ innerCentres (GA) T, sProd (GB) s' (Prod.map id bm q) = sProd (GA) s q)
    {f : (GA).Ω 1 → ℂ} {f' : (GB).Ω 1 → ℂ}
    (hf : ∀ x : (GA).Ω 1, (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T → f' (ιb x) = f x)
    (y : (GA).Ω 1) (hy : (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T) :
    (Gsx (GB) a aT x₀ ν α' s' *ᵥ f') (ιb y) = (Gsx (GA) a aT x₀ ν α s *ᵥ f) y := by
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  unfold Gsx
  refine resolvent_rows_transport (fun w : (GA).Ω 1 => (w : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T)
    (fun w : (GB).Ω 1 => (w : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈ T') (fun w => ιb w)
    (fun w1 w2 h1 h2 h => ?_) (fun w hw => ?_) (fun w' hw' => ?_) _ _ _ _
    (fun x z hx hz => Gstarx_apply_eq_zero_of_mem SA hx₀ hαA hdich hx hz)
    (fun x z hx hz => Kcalx_apply_eq_zero_of_mem SA hdich hx hz)
    (fun x z hx hz => Gstarx_apply_eq_zero_of_mem SB hx₀ hαB hdich' hx hz)
    (fun x z hx hz => Kcalx_apply_eq_zero_of_mem SB hdich' hx hz)
    (fun x z hx hz => Kcalx_apply_eq_zero_of_not_mem SB hdich' hx hz)
    (fun x z hx hz => Gstarx_boxMap_apply SA SB hx₀ hT' hTR hn hn' hαA hαB hα hdich hdich'
      hagree x z hx hz)
    (fun x z hx hz => Kcalx_boxMap_apply SA SB hx₀ hT' hTR hn hn' hαA hαB hα hdich hdich'
      hagree x z hx hz) hU hU' (fun z hz => hf z hz) hy
  · exact Subtype.ext (boxMap_inj (hm' := (by omega : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1)))
      (hTR _ h1) (hTR _ h2) (congrArg Subtype.val h))
  · show bm (w : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T'
    rw [← hT']; exact Finset.mem_image_of_mem _ hw
  · have hw'' : (w' : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈ T' := hw'
    rw [← hT', Finset.mem_image] at hw''
    obtain ⟨x2, hx2T, hx2⟩ := hw''
    exact ⟨⟨x2, levelGS_mem_Ω_one (Nat.le_add_left 1 k) le_rfl x2⟩, hx2T, Subtype.ext hx2⟩

/-- **The rows of the x-variant decoupled Green operator on a component, on two tori.**  Let
`Y ⊇ T` be sets of sites of the box of radius `R` (`Y' = bm '' Y`, `T' = bm '' T`; in the
application `Y` is a component of the cut and `T = S_Y`).  Suppose, on each torus, every interaction
cube with a non-zero factor lies inside `T` or avoids it, and meets `Y` only inside `T`; the factors
agree on the cubes inside `T`; `1 - 𝒦_{x,s}` is invertible on each torus; the admissible potentials
and the sources agree on `T`.  Then for `y ∈ Y`,
`(G_{k,x,s}(A) f)(y) = (G_{k,x,s'}(A') f')(bm y)`.  On `Y \ T` both sides vanish. -/
theorem xGreen_rows_transport {a : ℕ → ℝ} {aT x₀ ν : ℝ} (SA : Dec2.XCover (coverOf (GA)) (GA) a aT ν Cx)
    (SB : Dec2.XCover (coverOf (GB)) (GB) a aT ν Cx) (hx₀ : 0 ≤ x₀) {Y T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {Y' T' : Finset (Balaban.Localization.CTorus d L N₁' m₁ (k + 1))} (hY' : Y.image bm = Y') (hT' : T.image bm = T')
    (hTY : T ⊆ Y) {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
    (hα : ∀ x : (GA).Ω 1, (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T → α' (ιb x) = α x)
    {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × Balaban.Localization.CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hU : IsUnit (1 - Kcalx (GA) a aT x₀ ν α s)) (hU' : IsUnit (1 - Kcalx (GB) a aT x₀ ν α' s'))
    (hdich : ∀ q ∈ cubeIdx (GA), sProd (GA) s q ≠ 0 →
      SubI (GA) (intBox q) T ∨ DisjI (GA) (intBox q) T)
    (hdich' : ∀ q ∈ cubeIdx (GB), sProd (GB) s' q ≠ 0 →
      SubI (GB) (intBox q) T' ∨ DisjI (GB) (intBox q) T')
    (hrow : ∀ q ∈ cubeIdx (GA), sProd (GA) s q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hrow' : ∀ q ∈ cubeIdx (GB), sProd (GB) s' q ≠ 0 → ∀ x ∈ Y', x ∈ intBox q → x ∈ T')
    (hagree : ∀ q ∈ innerCentres (GA) T, sProd (GB) s' (Prod.map id bm q) = sProd (GA) s q)
    {f : (GA).Ω 1 → ℂ} {f' : (GB).Ω 1 → ℂ}
    (hf : ∀ x : (GA).Ω 1, (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T → f' (ιb x) = f x)
    (y : (GA).Ω 1) (hy : (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Y) :
    (Gsx (GB) a aT x₀ ν α' s' *ᵥ f') (ιb y) = (Gsx (GA) a aT x₀ ν α s *ᵥ f) y := by
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := fun x hx => hYR x (hTY hx)
  by_cases hyT : (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ T
  · exact Gsx_boxMap_rows SA SB hx₀ hT' hTR hn hn' hαA hαB hα hU hU' hdich hdich' hagree hf y hyT
  · have hy' : ((ιb y) : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∈ Y' := by
      rw [← hY']; exact Finset.mem_image_of_mem _ hy
    have hyT' : ((ιb y) : Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) ∉ T' := by
      intro h
      rw [← hT', Finset.mem_image] at h
      obtain ⟨x2, hx2T, hx2⟩ := h
      apply hyT
      rw [← boxMap_inj (hm' := (by omega : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1)))
        (hTR x2 hx2T) (hYR _ hy) hx2]
      exact hx2T
    rw [Gsx_apply_eq_zero_of_not_mem SA hx₀ hαA hrow f hy hyT,
      Gsx_apply_eq_zero_of_not_mem SB hx₀ hαB hrow' f' hy' hyT']

end XRows

end Balaban.LargeField.Base.XC
