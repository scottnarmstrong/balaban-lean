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

/-! ### The description of `Ω_1` -/

section Coord

omit [NeZero L] [NeZero M1] [NeZero N₁] in
private theorem nat_nec {m P A B W U V : ℕ} (hm : m = 75) (hP : P = 27) (hA : A = U / P)
    (hB : B = V / P) (hV : V < 81) (hAm : A < m) (hW : W < m) (h1 : A = (B + W) % m)
    (h : min W (m - W) ≤ 15) : U < 486 ∨ 1620 ≤ U := by
  subst hm hP; omega

omit [NeZero L] [NeZero M1] [NeZero N₁] in
private theorem nat_suff1 {m P A B U V : ℕ} (hm : m = 75) (hP : P = 27) (hA : A = U / P)
    (hB : B = V / P) (hV : V = min U 80) (hU : U < 486) :
    B ≤ A ∧ min (A - B) (m - (A - B)) ≤ 15 := by
  subst hm hP; omega

omit [NeZero L] [NeZero M1] [NeZero N₁] in
private theorem nat_suff2 {m P A U : ℕ} (hm : m = 75) (hP : P = 27) (hA : A = U / P)
    (hU : 1620 ≤ U) (hUl : U < 2025) : min A (m - A) ≤ 15 := by
  subst hm hP; omega

/-- One coordinate, necessity: a coordinate at cube distance `≤ 15` (in `C_1`-cubes of side 27,
75 per direction) from a coordinate in `[0, 81)` lies in `[0, 486) ∪ [1620, 2025)`. -/
theorem coord_necessary {ℓ P m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = P * m) (hm : m = 75)
    (hP : P = 27) (u v : ZMod ℓ) (hv : v.val < 81)
    (h : cycNorm m (blockCoord P m u - blockCoord P m v) ≤ 15) : u.val < 486 ∨ 1620 ≤ u.val := by
  have ha := blockCoord_val hℓ u
  have hb := blockCoord_val hℓ v
  have e : blockCoord P m u = blockCoord P m v + (blockCoord P m u - blockCoord P m v) := by
    ring
  have h1 := congrArg ZMod.val e
  rw [ZMod.val_add] at h1
  exact nat_nec hm hP ha hb hv (ZMod.val_lt _) (ZMod.val_lt _) h1 h

/-- One coordinate, sufficiency. -/
theorem coord_sufficient {ℓ P m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = P * m) (hm : m = 75)
    (hP : P = 27) (u : ZMod ℓ) (hu : u.val < 486 ∨ 1620 ≤ u.val) :
    ∃ v : ZMod ℓ, v.val < 81 ∧
      cycNorm m (blockCoord P m u - blockCoord P m v) ≤ 15 := by
  have hℓ' : ℓ = 2025 := by rw [hℓ, hm, hP]
  have hul : u.val < 2025 := hℓ' ▸ ZMod.val_lt u
  have ha := blockCoord_val hℓ u
  by_cases h : u.val < 486
  · refine ⟨((min u.val 80 : ℕ) : ZMod ℓ), ?_, ?_⟩
    · rw [ZMod.val_natCast_of_lt (by omega)]; omega
    · have hv : ((min u.val 80 : ℕ) : ZMod ℓ).val = min u.val 80 :=
        ZMod.val_natCast_of_lt (by omega)
      have hb := blockCoord_val hℓ ((min u.val 80 : ℕ) : ZMod ℓ)
      obtain ⟨hle, hc⟩ := nat_suff1 hm hP ha hb hv h
      unfold cycNorm
      rw [ZMod.val_sub hle]
      exact hc
  · have hu2 : 1620 ≤ u.val := hu.resolve_left h
    refine ⟨0, by simp, ?_⟩
    have hb : blockCoord P m (0 : ZMod ℓ) = 0 := by
      unfold blockCoord; simp
    rw [hb, sub_zero]
    unfold cycNorm
    have := nat_suff2 (m := m) (P := P) (A := (blockCoord P m u).val) (U := u.val) hm hP ha hu2 hul
    exact this

end Coord

include hM hN hL hq in
/-- **`Ω_1` on the instance**: the sites all of whose coordinates lie in `[0, 486)` or
`[1620, 2025)`: the cube of side `891` about `X` (`81 + 2 · 405`). -/
theorem exX_Ω_one {x : Torus d (M1 * N₁ * L ^ q)} :
    x ∈ (minimalGenSet (d := d) (M1 := M1) (N₁ := N₁) (L := L) (q := q) (j := 2)
      (by omega) (exX d M1 N₁ L q)).Ω 1 ↔ ∀ μ, (x μ).val < 486 ∨ 1620 ≤ (x μ).val := by
  have hq1 : 1 ≤ q := by omega
  have hℓ := fine_eq_cube (M1 := M1) (N₁ := N₁) (L := L) hq1
  have hm : N₁ * L ^ (q - 1) = 75 := by rw [hN, hL, hq]; norm_num
  have hP : L ^ 1 * M1 = 27 := by rw [hL, hM]; norm_num
  have e : L ^ 2 * M1 = 81 := by rw [hL, hM]; norm_num
  have e5 : 5 * L = 15 := by rw [hL]
  rw [minimalGenSet_Ω, minLayer_of_lt _ (by omega : 1 < 2), mem_nearStep]
  have htop : minLayer M1 N₁ L q 2 (exX d M1 N₁ L q) (1 + 1) = exX d M1 N₁ L q := by
    rw [show 1 + 1 = 2 from rfl, minLayer_self, localGen_cubeInterior_eq _ (by omega)
      (exX_isCellUnion hM hL)]
  rw [htop]
  constructor
  · rintro ⟨y, hy, hd⟩ μ
    rw [e5, supDist_le_iff] at hd
    have := hd μ
    unfold fineCubeIdx at this
    simp only [blockMap_apply] at this
    have hv := (mem_exX.1 hy) μ
    rw [e] at hv
    exact coord_necessary hℓ hm hP (x μ) (y μ) hv this
  · intro h
    choose v hv hd using fun μ => coord_sufficient hℓ hm hP (x μ) (h μ)
    refine ⟨v, ?_, ?_⟩
    · rw [mem_exX, e]; exact hv
    · rw [e5, supDist_le_iff]
      intro μ
      unfold fineCubeIdx
      simp only [blockMap_apply]
      exact hd μ

include hM hN hL hq in
/-- On the instance, `B_2(X)` has a site of layer `1`, below the top layer `2` (`d ≥ 1`). -/
theorem exX_lower (hd : 0 < d) : ∃ y, y ∈ (minimalGenSet (d := d) (M1 := M1) (N₁ := N₁)
    (L := L) (q := q) (j := 2) (by omega) (exX d M1 N₁ L q)).layer 1 ∧
    (minimalGenSet (d := d) (M1 := M1) (N₁ := N₁) (L := L) (q := q) (j := 2) (by omega)
      (exX d M1 N₁ L q)).layerIndex y = 1 := by
  have e : L ^ 2 * M1 = 81 := by rw [hL, hM]; norm_num
  have hℓ : M1 * N₁ * L ^ q = 2025 := by rw [hM, hN, hL, hq]; norm_num
  refine localGen_exists_lower _ (by omega) le_rfl (exX_isCellUnion hM hL) ⟨0, ?_⟩ ?_
  · rw [mem_exX, e]; intro μ; simp
  · intro h
    have : (fun _ => ((81 : ℕ) : ZMod (M1 * N₁ * L ^ q))) ∈ exX d M1 N₁ L q := by
      rw [h]; exact Finset.mem_univ _
    have h2 := (mem_exX.1 this) ⟨0, hd⟩
    rw [e, ZMod.val_natCast, hℓ] at h2
    norm_num at h2

end Balaban.LargeField
