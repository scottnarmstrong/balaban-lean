module

public import Balaban.LargeField.Background.LocalGenNeg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# A concrete instance of P3's local generating set `B_j(X)` (non-vacuity)

`L = 3`, `M₁ = 9 = 3 ^ 2` (so `m₁ = 2`), `q = j = 2`, `N₁ = 25`, any dimension `d ≥ 1` (`d = 3`
is the case of interest): the torus has side `9 · 25 · 3 ^ 2 = 2025`.  The parameters are kept as
variables with the numerical hypotheses `M1 = 9`, `N₁ = 25`, `L = 3`, `q = 2` (so that no numeral
appears in a type; they are satisfied by the numerals).  `X = exX` is one `C_2`-cube, `{x | ∀ μ, (x μ).val < 81}` (side
`L ^ 2 M₁ = 81`).  The generating set `minimalGenSet` of `X` is:

* `Ω_2 = X` (`exX_top`), a union of `C_2`-cubes (`exX_isCellUnion`), with no layer above;
* `Ω_1 = {x | ∀ μ, (x μ).val < 486 ∨ 1620 ≤ (x μ).val}` (`exX_Ω_one`): the `C_1`-cubes (side 27,
  75 per direction) at cube-index distance `≤ 15 = 5 L` from the cubes of `X`, i.e. the cube of
  side `81 + 2 · 405 = 891` about `X`;
* the layers: layer `2` is `X`, layer `1` is `Ω_1 \\ X` (nonempty, `exX_lower`).

The landed theorems of `LocalGen`/`LocalGenNeg` apply with all their hypotheses satisfied:
alignment (`exX_cubeAligned`), range (`exX_dataSites_range`) and the failure of `IsLevel`
(`exX_not_isLevel`).  The torus is large enough: `2 (80 + 11 · 9 · 3 ^ 2 + 1) = 1944 ≤ 2025`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Finset

set_option linter.unusedSectionVars false

variable {d M1 N₁ L q : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

variable (d M1 N₁ L q) in
/-- One `C_2`-cube of the torus: the sites with all coordinates in `[0, 81)`. -/
noncomputable def exX : Finset (Torus d (M1 * N₁ * L ^ q)) := by
  classical
  exact Finset.univ.filter fun x => ∀ μ, (x μ).val < L ^ 2 * M1

theorem mem_exX {x : Torus d (M1 * N₁ * L ^ q)} :
    x ∈ exX d M1 N₁ L q ↔ ∀ μ, (x μ).val < L ^ 2 * M1 := by
  classical
  simp [exX]

variable (hM : M1 = 9) (hN : N₁ = 25) (hL : L = 3) (hq : q = 2)

include hM hL in
theorem exX_isCellUnion :
    IsCellUnion (L ^ 2 * M1) (exX d M1 N₁ L q : Set (Torus d (M1 * N₁ * L ^ q))) := by
  intro x hx y hy
  rw [Finset.mem_coe, mem_exX] at hx ⊢
  intro μ
  have h1 := hy μ
  have h2 := hx μ
  have e : L ^ 2 * M1 = 81 := by rw [hL, hM]; norm_num
  rw [e] at h1 h2 ⊢
  omega

include hM hN hL hq in
theorem exX_top :
    (minimalGenSet (d := d) (M1 := M1) (N₁ := N₁) (L := L) (q := q) (j := 2)
      (by omega) (exX d M1 N₁ L q)).Ω 2 = exX d M1 N₁ L q :=
  localGen_top_Ω _ _ (exX_isCellUnion hM hL)

include hM hN hL hq in
theorem exX_cubeAligned :
    CubeAligned (minimalGenSet (d := d) (M1 := M1) (N₁ := N₁) (L := L) (q := q) (j := 2)
      (by omega) (exX d M1 N₁ L q)) 2 :=
  localGen_cubeAligned _ _ (by rw [hM, hL]; norm_num) le_rfl

include hM hN hL hq in
/-- The range estimate (3.2) on the instance (`r_j = 11 · 9 · 3 ^ 2 + 1 = 892`). -/
theorem exX_dataSites_range {x : Torus d (M1 * N₁ * L ^ q)}
    (hx : x ∈ dataSites (minimalGenSet (d := d) (M1 := M1) (N₁ := N₁) (L := L) (q := q)
      (j := 2) (by omega) (exX d M1 N₁ L q))) :
    ∃ y ∈ exX d M1 N₁ L q, supDist x y ≤ 892 := by
  obtain ⟨y, hy, h⟩ := localGen_dataSites_range (exX d M1 N₁ L q) (by omega) (by omega) hx
  refine ⟨y, hy, h.trans ?_⟩
  rw [hM, hL]; norm_num

include hM hN hL hq in
theorem exX_sup (y : Torus d (M1 * N₁ * L ^ q)) (hy : y ∈ exX d M1 N₁ L q) :
    supDist 0 y ≤ 80 := by
  rw [supDist_le_iff]
  intro μ
  have h := (mem_exX.1 hy) μ
  have e : L ^ 2 * M1 = 81 := by rw [hL, hM]; norm_num
  have : cycNorm (M1 * N₁ * L ^ q) (0 - y μ) = cycNorm (M1 * N₁ * L ^ q) (y μ) := by
    rw [zero_sub, cycNorm_neg]
  rw [show (0 : Torus d (M1 * N₁ * L ^ q)) μ = 0 from rfl, this]
  exact (min_le_left _ _).trans (by omega)

include hM hN hL hq in
/-- On the instance, `B_2(X)` is not full level. -/
theorem exX_not_isLevel (hd : 0 < d) (n : ℕ) : ¬ Fluctuation.IsLevel
    (minimalGenSet (d := d) (M1 := M1) (N₁ := N₁) (L := L) (q := q) (j := 2) (by omega)
      (exX d M1 N₁ L q)) n := by
  refine localGen_not_isLevel_of_ball _ (by omega) _ hd (x₀ := 0) (R := 80)
    (exX_sup hM hN hL hq) ?_ n
  have h : M1 * N₁ * L ^ q = 2025 := by rw [hM, hN, hL, hq]; norm_num
  have h2 : 11 * M1 * L ^ 2 = 891 := by rw [hM, hL]; norm_num
  omega

end Balaban.LargeField
