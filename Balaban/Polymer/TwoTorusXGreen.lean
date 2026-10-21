/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusXOps
public import Balaban.LargeField.Base.BaseTwoTorusGreen
public import Balaban.Localization.DecoupledXLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The x-variant decoupled Green operator on two tori

The covariance of the step at scale `k` is built from the x-variant decoupled Green operator
`G_{k,x,s}(A) = G*_{x,s}(A) (1 - 𝒦_{x,s}(A))⁻¹` (`Gsx`) of the generating set `levelGS (k + 1)` of
the fine torus `CTorus d L N₁ m₁ (k + 1)` (the top level: every site lies in the layer `k + 1`).
For two such tori, identified on a centred box by `boxMap`, this file proves the x-variant forms of
the landed comparisons of `TwoTorusCubeOps` and `TwoTorusGreenRows` (W616):

* `xAvgMatrix_levelTop_apply`, `xAvgMatrix_boxMap`: the x-variant averaging form of the top level
  reads the blocks of side `L^k` and `L^(k+1)` only, and its entries correspond on the box;
* `cutXFullMatrix_boxMap`, `cutXOperator_boxMap`, `xDirichletOperator_boxMap`, `cubeHx_boxMap`,
  `Kzx_boxMap`, `cubeGx_boxMap`: the entries of the cut x-variant operator, of the cube operator
  `H_{k,x,z}(A)`, of the commutator `K^x_z` and of the cube resolvent `G^{(z)}_x(A) c_z`;
* `Gstarx_block`, `Kcalx_block` and their corollaries (one torus): the block identities
  `P G*_{x,s} = G*_{x,s} P`, `P 𝒦_{x,s} = 𝒦_{x,s} P` for the indicator `P` of a set `T` such that
  every active interaction cube lies inside `T` or avoids it;
* `Gstarx_boxMap_apply`, `Kcalx_boxMap_apply`, `Gsx_boxMap_rows`, `xGreen_rows_transport`: the
  rows of `G_{k,x,s}(A) f` on a component correspond (block-diagonal resolvent argument,
  `resolvent_rows_transport`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background Matrix

/-! ### The cube operators of the x-variant at the top level -/

section XLevel

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
local notation "ιb" x:max => Subtype.mk (bm (x : CTorus d L N₁ m₁ (k + 1)))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) (ϱ := ϱ)
    (Nat.le_add_left 1 k) le_rfl _)



/-- **The x-variant cube resolvent** `G^{(z)}_x(A) c_z` of the centre `(k+1, y0)`: its entries at
two sites of the box of radius `R = ρ₀ + 3 L^(k+1+m₁)` correspond, for potentials corresponding on
that box.  Margins: `2 R + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` and `2 (R + 2 + R) + 1 < N₁ L^m₁ L^(k+1)`
(and for `N₁'`). -/
theorem cubeGx_boxMap {ρ₀ : ℕ} {a : ℕ → ℝ} {aT x₀ ν : ℝ} (SA : XSetting (GA) a aT ν)
    (SB : XSetting (GB) a aT ν) (hx₀ : 0 ≤ x₀) {y0 : CTorus d L N₁ m₁ (k + 1)}
    (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ (k + 1)) y0)
    (hq : ((k + 1, y0) : ℕ × CTorus d L N₁ m₁ (k + 1)) ∈ cubeIdx (GA))
    (hn : 2 * (ρ₀ + 3 * L ^ (k + 1 + m₁)) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * (ρ₀ + 3 * L ^ (k + 1 + m₁)) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hm : 2 * ((ρ₀ + 3 * L ^ (k + 1 + m₁)) + 2 + (ρ₀ + 3 * L ^ (k + 1 + m₁))) + 1 <
      (N₁ * L ^ m₁) * L ^ (k + 1))
    (hm' : 2 * ((ρ₀ + 3 * L ^ (k + 1 + m₁)) + 2 + (ρ₀ + 3 * L ^ (k + 1 + m₁))) + 1 <
      (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot _ α) (hαB : AdmPot _ α')
    (hα : ∀ x : (GA).Ω 1, InBox d (ρ₀ + 3 * L ^ (k + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ (k + 1))
      (x : CTorus d L N₁ m₁ (k + 1)) → α' (ιb x) = α x)
    (x y : (GA).Ω 1)
    (hx : InBox d (ρ₀ + 3 * L ^ (k + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ (k + 1))
      (x : CTorus d L N₁ m₁ (k + 1)))
    (hy : InBox d (ρ₀ + 3 * L ^ (k + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ (k + 1))
      (y : CTorus d L N₁ m₁ (k + 1))) :
    cubeGx (GB) a aT x₀ ν α' (Prod.map id bm ((k + 1, y0) : ℕ × CTorus d L N₁ m₁ (k + 1)))
        (ιb x) (ιb y) =
      cubeGx (GA) a aT x₀ ν α (k + 1, y0) x y :=
  Balaban.LargeField.Base.XC.cubeGx_boxMap (Dec2.xCover_self SA) (Dec2.xCover_self SB) hx₀ hy0 hq hn hn' hm hm' hαA hαB hα x y hx hy

end XLevel

/-! ### The block identities of the x-variant on one torus -/

section XBlock

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x₀ ν : ℝ}
  {α : G.Ω 1 → ℂ}

/-- **The block identity for `G*_{x,s}`.**  If every interaction cube with a non-zero factor lies
inside `T` or avoids it, then `P G*_{x,s} = G*_{x,s} P = ∑_{z inner} s_z χ_z G^{(z)}_x c_z`, `P` the
indicator of `T`. -/
theorem Gstarx_block (S : XSetting G a aT ν) (hx : 0 ≤ x₀) (hα : AdmPot G α)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T) :
    indY G T * Gstarx G a aT x₀ ν α s =
        ∑ q ∈ innerCentres G T, sProd G s q • (chiD G q * cubeGx G a aT x₀ ν α q) ∧
      Gstarx G a aT x₀ ν α s * indY G T =
        ∑ q ∈ innerCentres G T, sProd G s q • (chiD G q * cubeGx G a aT x₀ ν α q) :=
  Balaban.LargeField.Base.XC.Gstarx_block (Dec2.xCover_self S) hx hα hdich
/-- **The block identity for `𝒦_{x,s}`**: `P 𝒦_{x,s} = 𝒦_{x,s} P = ∑_{z inner} s_z K^x_z G^{(z)}_x c_z`. -/
theorem Kcalx_block (S : XSetting G a aT ν) {T : Finset (CTorus d L N₁ m₁ (k + 1))}
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T) :
    indY G T * Kcalx G a aT x₀ ν α s =
        ∑ q ∈ innerCentres G T, sProd G s q • (Kzx G a aT x₀ ν q * cubeGx G a aT x₀ ν α q) ∧
      Kcalx G a aT x₀ ν α s * indY G T =
        ∑ q ∈ innerCentres G T, sProd G s q • (Kzx G a aT x₀ ν q * cubeGx G a aT x₀ ν α q) :=
  Balaban.LargeField.Base.XC.Kcalx_block (Dec2.xCover_self S) hdich
theorem indY_mul_Kcalx_comm (S : XSetting G a aT ν) {T : Finset (CTorus d L N₁ m₁ (k + 1))}
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T) :
    indY G T * Kcalx G a aT x₀ ν α s = Kcalx G a aT x₀ ν α s * indY G T :=
  Balaban.LargeField.Base.XC.indY_mul_Kcalx_comm (Dec2.xCover_self S) hdich
theorem indY_mul_Gstarx_comm (S : XSetting G a aT ν) (hx : 0 ≤ x₀) (hα : AdmPot G α)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T) :
    indY G T * Gstarx G a aT x₀ ν α s = Gstarx G a aT x₀ ν α s * indY G T :=
  Balaban.LargeField.Base.XC.indY_mul_Gstarx_comm (Dec2.xCover_self S) hx hα hdich
theorem Kcalx_apply_eq_zero_of_mem (S : XSetting G a aT ν) {T : Finset (CTorus d L N₁ m₁ (k + 1))}
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x z : G.Ω 1} (hx : (x : CTorus d L N₁ m₁ (k + 1)) ∈ T)
    (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∉ T) : Kcalx G a aT x₀ ν α s x z = 0 :=
  Balaban.LargeField.Base.XC.Kcalx_apply_eq_zero_of_mem (Dec2.xCover_self S) hdich hx hz
theorem Kcalx_apply_eq_zero_of_not_mem (S : XSetting G a aT ν)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x z : G.Ω 1} (hx : (x : CTorus d L N₁ m₁ (k + 1)) ∉ T)
    (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ T) : Kcalx G a aT x₀ ν α s x z = 0 :=
  Balaban.LargeField.Base.XC.Kcalx_apply_eq_zero_of_not_mem (Dec2.xCover_self S) hdich hx hz
theorem Gstarx_apply_eq_zero_of_mem (S : XSetting G a aT ν) (hx₀ : 0 ≤ x₀) (hα : AdmPot G α)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x z : G.Ω 1} (hx : (x : CTorus d L N₁ m₁ (k + 1)) ∈ T)
    (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∉ T) : Gstarx G a aT x₀ ν α s x z = 0 :=
  Balaban.LargeField.Base.XC.Gstarx_apply_eq_zero_of_mem (Dec2.xCover_self S) hx₀ hα hdich hx hz
/-- The row at a site of `T` of `G*_{x,s}` is the sum over the cubes inside `T`. -/
theorem Gstarx_apply_of_mem (S : XSetting G a aT ν) (hx₀ : 0 ≤ x₀) (hα : AdmPot G α)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x : G.Ω 1} (hx : (x : CTorus d L N₁ m₁ (k + 1)) ∈ T) (z : G.Ω 1) :
    Gstarx G a aT x₀ ν α s x z =
      ∑ q ∈ innerCentres G T, sProd G s q * (chiD G q * cubeGx G a aT x₀ ν α q) x z :=
  Balaban.LargeField.Base.XC.Gstarx_apply_of_mem (Dec2.xCover_self S) hx₀ hα hdich hx z
/-- The row at a site of `T` of `𝒦_{x,s}` is the sum over the cubes inside `T`. -/
theorem Kcalx_apply_of_mem (S : XSetting G a aT ν) {T : Finset (CTorus d L N₁ m₁ (k + 1))}
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x : G.Ω 1} (hx : (x : CTorus d L N₁ m₁ (k + 1)) ∈ T) (z : G.Ω 1) :
    Kcalx G a aT x₀ ν α s x z =
      ∑ q ∈ innerCentres G T, sProd G s q * (Kzx G a aT x₀ ν q * cubeGx G a aT x₀ ν α q) x z :=
  Balaban.LargeField.Base.XC.Kcalx_apply_of_mem (Dec2.xCover_self S) hdich hx z
/-- **Rows of `G_{k,x,s}(A) f` outside `T`.**  If every active interaction cube meets `Y` only
inside `T`, the rows of `G_{k,x,s}(A) f` on `Y \ T` vanish. -/
theorem Gsx_apply_eq_zero_of_not_mem (S : XSetting G a aT ν) (hx₀ : 0 ≤ x₀) (hα : AdmPot G α)
    {Y T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hrow : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (f : G.Ω 1 → ℂ) {y : G.Ω 1} (hyY : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y)
    (hyT : (y : CTorus d L N₁ m₁ (k + 1)) ∉ T) : (Gsx G a aT x₀ ν α s *ᵥ f) y = 0 :=
  Balaban.LargeField.Base.XC.Gsx_apply_eq_zero_of_not_mem (Dec2.xCover_self S) hx₀ hα hrow f hyY hyT
/-- **Rows of `G_{k,x,s}(A)` on `T` read only `T`.**  Under the dichotomy, the entries of
`G_{k,x,s}(A)` from a row in `T` to a column outside `T` vanish. -/
theorem Gsx_apply_eq_zero_of_mem (S : XSetting G a aT ν) (hx₀ : 0 ≤ x₀) (hα : AdmPot G α)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hU : IsUnit (1 - Kcalx G a aT x₀ ν α s))
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → SubI G (intBox q) T ∨ DisjI G (intBox q) T)
    {x z : G.Ω 1} (hx : (x : CTorus d L N₁ m₁ (k + 1)) ∈ T)
    (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∉ T) : Gsx G a aT x₀ ν α s x z = 0 :=
  Balaban.LargeField.Base.XC.Gsx_apply_eq_zero_of_mem (Dec2.xCover_self S) hx₀ hα hU hdich hx hz

end XBlock

/-! ### The rows of the x-variant decoupled Green operator on two tori -/

section XRows

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
local notation "ιb" x:max => Subtype.mk (bm (x : CTorus d L N₁ m₁ (k + 1)))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) (ϱ := ϱ)
    (Nat.le_add_left 1 k) le_rfl _)

/-- **The x-variant cube resolvent of a cube inside `T`**, with potentials corresponding on `T`
only.  Margin: `4 R + 12 L^(k+1+m₁) + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem cubeGx_boxMap_inner {a : ℕ → ℝ} {aT x₀ ν : ℝ} (SA : XSetting (GA) a aT ν)
    (SB : XSetting (GB) a aT ν) (hx₀ : 0 ≤ x₀) {T : Finset (CTorus d L N₁ m₁ (k + 1))}
    {T' : Finset (CTorus d L N₁' m₁ (k + 1))} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ T → α' (ιb x) = α x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ innerCentres (GA) T) (x z : (GA).Ω 1)
    (hx : InBox d (R + 3 * L ^ (k + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ (k + 1))
      (x : CTorus d L N₁ m₁ (k + 1)))
    (hz : InBox d (R + 3 * L ^ (k + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ (k + 1))
      (z : CTorus d L N₁ m₁ (k + 1))) :
    cubeGx (GB) a aT x₀ ν α' (Prod.map id bm q) (ιb x) (ιb z) = cubeGx (GA) a aT x₀ ν α q x z :=
  Balaban.LargeField.Base.XC.cubeGx_boxMap_inner (Dec2.xCover_self SA) (Dec2.xCover_self SB) hx₀ hT' hTR hn hn' hαA hαB hα hq x z hx hz
/-- The entries of `χ_z G^{(z)}_x c_z` of a cube inside `T` at two sites of `T` correspond. -/
theorem chiD_cubeGx_boxMap_inner {a : ℕ → ℝ} {aT x₀ ν : ℝ} (SA : XSetting (GA) a aT ν)
    (SB : XSetting (GB) a aT ν) (hx₀ : 0 ≤ x₀) {T : Finset (CTorus d L N₁ m₁ (k + 1))}
    {T' : Finset (CTorus d L N₁' m₁ (k + 1))} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ T → α' (ιb x) = α x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ innerCentres (GA) T) (x z : (GA).Ω 1)
    (hx : (x : CTorus d L N₁ m₁ (k + 1)) ∈ T) (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ T) :
    (chiD (GB) (Prod.map id bm q) * cubeGx (GB) a aT x₀ ν α' (Prod.map id bm q)) (ιb x) (ιb z) =
      (chiD (GA) q * cubeGx (GA) a aT x₀ ν α q) x z :=
  Balaban.LargeField.Base.XC.chiD_cubeGx_boxMap_inner (Dec2.xCover_self SA) (Dec2.xCover_self SB) hx₀ hT' hTR hn hn' hαA hαB hα hq x z hx hz
/-- The entries of `K^x_z G^{(z)}_x c_z` of a cube inside `T` at two sites of `T` correspond. -/
theorem Kzx_cubeGx_boxMap_inner {a : ℕ → ℝ} {aT x₀ ν : ℝ} (SA : XSetting (GA) a aT ν)
    (SB : XSetting (GB) a aT ν) (hx₀ : 0 ≤ x₀) {T : Finset (CTorus d L N₁ m₁ (k + 1))}
    {T' : Finset (CTorus d L N₁' m₁ (k + 1))} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ T → α' (ιb x) = α x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ innerCentres (GA) T) (x z : (GA).Ω 1)
    (hx : (x : CTorus d L N₁ m₁ (k + 1)) ∈ T) (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ T) :
    (Kzx (GB) a aT x₀ ν (Prod.map id bm q) * cubeGx (GB) a aT x₀ ν α' (Prod.map id bm q))
        (ιb x) (ιb z) =
      (Kzx (GA) a aT x₀ ν q * cubeGx (GA) a aT x₀ ν α q) x z :=
  Balaban.LargeField.Base.XC.Kzx_cubeGx_boxMap_inner (Dec2.xCover_self SA) (Dec2.xCover_self SB) hx₀ hT' hTR hn hn' hαA hαB hα hq x z hx hz
/-- **`G*_{x,s}` on two tori.**  If every active interaction cube lies inside `T` or avoids it, on
both tori (`T` in the box of radius `R`, `T' = bm '' T`), the factors agree on the cubes inside `T`
and the potentials on `T`, the entries of `G*_{x,s}` at two sites of `T` correspond. -/
theorem Gstarx_boxMap_apply {a : ℕ → ℝ} {aT x₀ ν : ℝ} (SA : XSetting (GA) a aT ν)
    (SB : XSetting (GB) a aT ν) (hx₀ : 0 ≤ x₀) {T : Finset (CTorus d L N₁ m₁ (k + 1))}
    {T' : Finset (CTorus d L N₁' m₁ (k + 1))} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ T → α' (ιb x) = α x)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx (GA), sProd (GA) s q ≠ 0 →
      SubI (GA) (intBox q) T ∨ DisjI (GA) (intBox q) T)
    (hdich' : ∀ q ∈ cubeIdx (GB), sProd (GB) s' q ≠ 0 →
      SubI (GB) (intBox q) T' ∨ DisjI (GB) (intBox q) T')
    (hagree : ∀ q ∈ innerCentres (GA) T, sProd (GB) s' (Prod.map id bm q) = sProd (GA) s q)
    (x z : (GA).Ω 1) (hx : (x : CTorus d L N₁ m₁ (k + 1)) ∈ T)
    (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ T) :
    Gstarx (GB) a aT x₀ ν α' s' (ιb x) (ιb z) = Gstarx (GA) a aT x₀ ν α s x z :=
  Balaban.LargeField.Base.XC.Gstarx_boxMap_apply (Dec2.xCover_self SA) (Dec2.xCover_self SB) hx₀ hT' hTR hn hn' hαA hαB hα hdich hdich' hagree x z hx hz
/-- **`𝒦_{x,s}` on two tori.**  Under the hypotheses of `Gstarx_boxMap_apply`, the entries of
`𝒦_{x,s}` at two sites of `T` correspond. -/
theorem Kcalx_boxMap_apply {a : ℕ → ℝ} {aT x₀ ν : ℝ} (SA : XSetting (GA) a aT ν)
    (SB : XSetting (GB) a aT ν) (hx₀ : 0 ≤ x₀) {T : Finset (CTorus d L N₁ m₁ (k + 1))}
    {T' : Finset (CTorus d L N₁' m₁ (k + 1))} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ T → α' (ιb x) = α x)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ cubeIdx (GA), sProd (GA) s q ≠ 0 →
      SubI (GA) (intBox q) T ∨ DisjI (GA) (intBox q) T)
    (hdich' : ∀ q ∈ cubeIdx (GB), sProd (GB) s' q ≠ 0 →
      SubI (GB) (intBox q) T' ∨ DisjI (GB) (intBox q) T')
    (hagree : ∀ q ∈ innerCentres (GA) T, sProd (GB) s' (Prod.map id bm q) = sProd (GA) s q)
    (x z : (GA).Ω 1) (hx : (x : CTorus d L N₁ m₁ (k + 1)) ∈ T)
    (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ T) :
    Kcalx (GB) a aT x₀ ν α' s' (ιb x) (ιb z) = Kcalx (GA) a aT x₀ ν α s x z :=
  Balaban.LargeField.Base.XC.Kcalx_boxMap_apply (Dec2.xCover_self SA) (Dec2.xCover_self SB) hx₀ hT' hTR hn hn' hαA hαB hα hdich hdich' hagree x z hx hz
/-- **The rows of `G_{k,x,s}(A) f` on `T`.**  Let `T` be a set of sites of the box of radius `R`
such that every interaction cube with a non-zero factor lies inside `T` or avoids it, on both tori
(`T' = bm '' T`), the factors agree on the cubes inside `T`, `1 - 𝒦_{x,s}` is invertible on each
torus, and the potentials and the sources agree on `T`.  Then `G_{k,x,s}(A) f` and
`G_{k,x,s'}(A') f'` agree on `T` (after `bm`).  Margin:
`4 R + 12 L^(k+1+m₁) + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem Gsx_boxMap_rows {a : ℕ → ℝ} {aT x₀ ν : ℝ} (SA : XSetting (GA) a aT ν)
    (SB : XSetting (GB) a aT ν) (hx₀ : 0 ≤ x₀) {T : Finset (CTorus d L N₁ m₁ (k + 1))}
    {T' : Finset (CTorus d L N₁' m₁ (k + 1))} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ T → α' (ιb x) = α x)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hU : IsUnit (1 - Kcalx (GA) a aT x₀ ν α s)) (hU' : IsUnit (1 - Kcalx (GB) a aT x₀ ν α' s'))
    (hdich : ∀ q ∈ cubeIdx (GA), sProd (GA) s q ≠ 0 →
      SubI (GA) (intBox q) T ∨ DisjI (GA) (intBox q) T)
    (hdich' : ∀ q ∈ cubeIdx (GB), sProd (GB) s' q ≠ 0 →
      SubI (GB) (intBox q) T' ∨ DisjI (GB) (intBox q) T')
    (hagree : ∀ q ∈ innerCentres (GA) T, sProd (GB) s' (Prod.map id bm q) = sProd (GA) s q)
    {f : (GA).Ω 1 → ℂ} {f' : (GB).Ω 1 → ℂ}
    (hf : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ T → f' (ιb x) = f x)
    (y : (GA).Ω 1) (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ T) :
    (Gsx (GB) a aT x₀ ν α' s' *ᵥ f') (ιb y) = (Gsx (GA) a aT x₀ ν α s *ᵥ f) y :=
  Balaban.LargeField.Base.XC.Gsx_boxMap_rows (Dec2.xCover_self SA) (Dec2.xCover_self SB) hx₀ hT' hTR hn hn' hαA hαB hα hU hU' hdich hdich' hagree hf y hy
/-- **The rows of the x-variant decoupled Green operator on a component, on two tori.**  Let
`Y ⊇ T` be sets of sites of the box of radius `R` (`Y' = bm '' Y`, `T' = bm '' T`; in the
application `Y` is a component of the cut and `T = S_Y`).  Suppose, on each torus, every interaction
cube with a non-zero factor lies inside `T` or avoids it, and meets `Y` only inside `T`; the factors
agree on the cubes inside `T`; `1 - 𝒦_{x,s}` is invertible on each torus; the admissible potentials
and the sources agree on `T`.  Then for `y ∈ Y`,
`(G_{k,x,s}(A) f)(y) = (G_{k,x,s'}(A') f')(bm y)`.  On `Y \ T` both sides vanish. -/
theorem xGreen_rows_transport {a : ℕ → ℝ} {aT x₀ ν : ℝ} (SA : XSetting (GA) a aT ν)
    (SB : XSetting (GB) a aT ν) (hx₀ : 0 ≤ x₀) {Y T : Finset (CTorus d L N₁ m₁ (k + 1))}
    {Y' T' : Finset (CTorus d L N₁' m₁ (k + 1))} (hY' : Y.image bm = Y') (hT' : T.image bm = T')
    (hTY : T ⊆ Y) {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ T → α' (ιb x) = α x)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hU : IsUnit (1 - Kcalx (GA) a aT x₀ ν α s)) (hU' : IsUnit (1 - Kcalx (GB) a aT x₀ ν α' s'))
    (hdich : ∀ q ∈ cubeIdx (GA), sProd (GA) s q ≠ 0 →
      SubI (GA) (intBox q) T ∨ DisjI (GA) (intBox q) T)
    (hdich' : ∀ q ∈ cubeIdx (GB), sProd (GB) s' q ≠ 0 →
      SubI (GB) (intBox q) T' ∨ DisjI (GB) (intBox q) T')
    (hrow : ∀ q ∈ cubeIdx (GA), sProd (GA) s q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hrow' : ∀ q ∈ cubeIdx (GB), sProd (GB) s' q ≠ 0 → ∀ x ∈ Y', x ∈ intBox q → x ∈ T')
    (hagree : ∀ q ∈ innerCentres (GA) T, sProd (GB) s' (Prod.map id bm q) = sProd (GA) s q)
    {f : (GA).Ω 1 → ℂ} {f' : (GB).Ω 1 → ℂ}
    (hf : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ T → f' (ιb x) = f x)
    (y : (GA).Ω 1) (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y) :
    (Gsx (GB) a aT x₀ ν α' s' *ᵥ f') (ιb y) = (Gsx (GA) a aT x₀ ν α s *ᵥ f) y :=
  Balaban.LargeField.Base.XC.xGreen_rows_transport (Dec2.xCover_self SA) (Dec2.xCover_self SB) hx₀ hY' hT' hTY hYR hn hn' hαA hαB hα hU hU' hdich hdich' hrow hrow' hagree hf y hy

end XRows