module

public import Balaban.LargeField.Background.LocalGen
public import Balaban.Fluctuation.CriticalPoint
public import Balaban.Localization.I5Fan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# What P3's local generating set `B_j(X)` is not (`LOCALGEN.md` §2, §4)

The object is the landed `minimalGenSet hj X` (see `LocalGen`); this file records, in Lean, why the
landed full-level fluctuation engine does not apply to it as a parent.  It is the full-level form
of P3 (4.4)-(4.6); no class definition is changed and no claim is made about which generator the
class terms use.

* `localGen_not_isLevel`: if some site is farther than `11 M₁ L ^ j` from `X`, then `B_j(X)` is not
  `IsLevel _ n` for any `n` (its `Ω₁` is not the whole torus); `localGen_not_isLevel_of_ball`
  gives the size hypothesis for `X` inside a ball.
* `localGen_exists_lower`: for a nonempty proper cell union `X` and `2 ≤ j`, there is a site of
  `Ω_{j-1} \\ Ω_j`, i.e. of layer `j - 1`; the generating set has a nonempty layer below the top.
* `not_bgSetting_radius`, `not_bgSetting_minSep`: the separation `5 L M₁` is incompatible with the
  two radius fields `hr`, `hr₀` of `BgSetting`.
* `bgR0_le_minSep_iff`: when the separation does satisfy the `BgHyp` requirement `bgR0 d L ≤ ϱ`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Finset

set_option linter.unusedSectionVars false

variable {d M1 N₁ L q : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

/-! ### Not full level -/

section NotLevel

variable {j : ℕ} (X : Finset (Torus d (M1 * N₁ * L ^ q)))

/-- A site farther than `11 M₁ L ^ j` from `X` is not in `Ω₁(B_j(X))`. -/
theorem localGen_not_mem_Ω_one (hL : 2 ≤ L) (hj : j ≤ q) {z : Torus d (M1 * N₁ * L ^ q)}
    (hz : ∀ y ∈ X, 11 * M1 * L ^ j < supDist z y) : z ∉ (minimalGenSet hj X).Ω 1 := by
  intro h
  rw [minimalGenSet_Ω] at h
  by_cases h1 : 1 ≤ j
  · obtain ⟨y, hy, hd⟩ := exists_near_of_mem_minLayer' X hL hj h1 h
    exact absurd (hz y hy) (not_lt.2 hd)
  · rw [minLayer_of_gt X (by omega)] at h
    exact absurd h (Finset.notMem_empty _)

/-- **T4 (not full level).**  If some site of the torus is farther than `11 M₁ L ^ j` from `X`,
then `B_j(X)` is not `IsLevel _ n` for any `n`: its `Ω₁` is not the whole torus. -/
theorem localGen_not_isLevel (hL : 2 ≤ L) (hj : j ≤ q) {z : Torus d (M1 * N₁ * L ^ q)}
    (hz : ∀ y ∈ X, 11 * M1 * L ^ j < supDist z y) (n : ℕ) :
    ¬ Fluctuation.IsLevel (minimalGenSet hj X) n :=
  fun h => localGen_not_mem_Ω_one X hL hj hz (h z).1

/-- **T4, size hypothesis.**  If `X` lies in the sup-ball of radius `R` about `x₀` and the torus
side satisfies `2 (R + 11 M₁ L ^ j + 1) ≤ M₁ N₁ L ^ q`, then some site is farther than
`11 M₁ L ^ j` from `X`, hence `B_j(X)` is not `IsLevel _ n`. -/
theorem localGen_not_isLevel_of_ball (hL : 2 ≤ L) (hj : j ≤ q) (hd : 0 < d)
    {x₀ : Torus d (M1 * N₁ * L ^ q)} {R : ℕ} (hX : ∀ y ∈ X, supDist x₀ y ≤ R)
    (hsize : 2 * (R + 11 * M1 * L ^ j + 1) ≤ M1 * N₁ * L ^ q) (n : ℕ) :
    ¬ Fluctuation.IsLevel (minimalGenSet hj X) n := by
  set r := 11 * M1 * L ^ j with hr
  let i0 : Fin d := ⟨0, hd⟩
  let z : Torus d (M1 * N₁ * L ^ q) := x₀ + Pi.single i0 ((R + r + 1 : ℕ) : ZMod _)
  have h1 : R + r + 1 ≤ supDist x₀ z := by
    have h2 := cycNorm_le_supDist x₀ z i0
    have h3 : (x₀ i0 - z i0) = -(((R + r + 1 : ℕ) : ℤ) : ZMod (M1 * N₁ * L ^ q)) := by
      simp [z]
    have hu : 2 * |((R + r + 1 : ℕ) : ℤ)| ≤ ((M1 * N₁ * L ^ q : ℕ) : ℤ) := by
      rw [abs_of_nonneg (Int.natCast_nonneg _)]
      exact_mod_cast hsize
    rw [h3, cycNorm_neg, cycNorm_intCast_of_le hu, Int.natAbs_natCast] at h2
    exact h2
  refine localGen_not_isLevel X hL hj (z := z) (fun y hy => ?_) n
  have h4 := supDist_triangle x₀ y z
  have h5 := hX y hy
  have h6 := supDist_comm z y
  omega

/-- The first step out of a nonempty proper subset of the torus. -/
theorem exists_step_out (hne : X.Nonempty) (hproper : X ≠ Finset.univ) :
    ∃ x ∈ X, ∃ μ : Fin d, x + Pi.single μ 1 ∉ X := by
  by_contra hcon
  push Not at hcon
  apply hproper
  refine Finset.eq_univ_of_forall fun z => ?_
  obtain ⟨x0, hx0⟩ := hne
  let P : Torus d (M1 * N₁ * L ^ q) → Prop := fun w => ∀ x ∈ X, x + w ∈ X
  have hP0 : P 0 := fun x hx => by simpa using hx
  have hPadd : ∀ a b, P a → P b → P (a + b) := fun a b ha hb x hx => by
    rw [← add_assoc]; exact hb _ (ha x hx)
  have hPe : ∀ μ : Fin d, P (Pi.single μ 1) := fun μ x hx => hcon x hx μ
  have hPn : ∀ (μ : Fin d) (n : ℕ), P (n • Pi.single μ 1) := by
    intro μ n
    induction n with
    | zero => simpa using hP0
    | succ n ih => rw [succ_nsmul]; exact hPadd _ _ ih (hPe μ)
  have hsum : P (∑ μ, ((z - x0) μ).val • (Pi.single μ 1 : Torus d (M1 * N₁ * L ^ q))) :=
    Finset.sum_induction _ P hPadd hP0 fun μ _ => hPn μ _
  have e : z = x0 + ∑ μ, ((z - x0) μ).val • (Pi.single μ 1 : Torus d (M1 * N₁ * L ^ q)) := by
    funext ν
    rw [Pi.add_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, nsmul_eq_mul, mul_one, Pi.sub_apply,
      ZMod.natCast_zmod_val]
    ring
  rw [e]
  exact hsum x0 hx0

/-- **T4 (a nonempty layer below the top).**  For a nonempty proper union `X` of `C_j`-cubes,
`2 ≤ j`, `Ω_{j-1}(B_j(X)) \\ Ω_j(B_j(X))` contains a site; no size hypothesis is needed.  So the
generating set has a nonempty layer `j - 1` below its top layer `j`. -/
theorem localGen_exists_lower (hj : j ≤ q) (hj2 : 2 ≤ j)
    (hX : IsCellUnion (L ^ j * M1) (X : Set (Torus d (M1 * N₁ * L ^ q))))
    (hne : X.Nonempty) (hproper : X ≠ Finset.univ) :
    ∃ y, y ∈ (minimalGenSet hj X).layer (j - 1) ∧ (minimalGenSet hj X).layerIndex y = j - 1 := by
  obtain ⟨x, hx, μ, hxμ⟩ := exists_step_out X hne hproper
  set y : Torus d (M1 * N₁ * L ^ q) := x + Pi.single μ 1 with hy
  have hn : j - 1 ≤ q := by omega
  have e : minLayer M1 N₁ L q j X (j - 1 + 1) = X := by
    rw [show j - 1 + 1 = j by omega, minLayer_self, localGen_cubeInterior_eq X hj hX]
  have h1 : supDist y x ≤ 1 := by
    have h2 := supDist_le_torusDist y x
    have h3 := Multiscale.Adj.torusDist_le (d := d) (N₀ := M1 * N₁) (L := L) (k := q)
      (x := y) (y := x) ⟨μ, Or.inr rfl⟩
    have : (supDist y x : ℝ) ≤ 1 := h2.trans h3
    exact_mod_cast this
  have hLpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hMpos : 0 < M1 := Nat.pos_of_ne_zero (NeZero.ne M1)
  have hmem : y ∈ (minimalGenSet hj X).Ω (j - 1) := by
    rw [minimalGenSet_Ω, minLayer_of_lt X (by omega : j - 1 < j), mem_nearStep]
    refine ⟨x, by rw [e]; exact hx, ?_⟩
    unfold fineCubeIdx
    refine (supDist_blockMap_le_one (fine_eq_cube hn) (D := 1) ?_ y x h1).trans (by omega)
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hlay : y ∈ (minimalGenSet hj X).layer (j - 1) := by
    rw [GeneratingSet.mem_layer, show j - 1 + 1 = j by omega, localGen_top_Ω X hj hX]
    exact ⟨hmem, hxμ⟩
  exact ⟨y, hlay, GeneratingSet.layerIndex_eq _ (by omega) (by omega) hlay⟩

end NotLevel

/-! ### T7: the separation `5 L M₁` against the radius fields of `BgSetting` -/

section Radius

/-- **T7(a).**  The two radius fields of `BgSetting`, `hr₀ : 4 d L ^ 3 ≤ r₀` and
`hr : r₀ L ^ m₁ ≤ ϱ - 1`, with `M₁ = L ^ m₁` and `ϱ = 5 L M₁` the separation of `B_j(X)`, are
contradictory for `d, L ≥ 3`, `M₁ ≥ 1`: `r₀ M₁ ≥ 4 d L ^ 3 M₁ > 5 L M₁`. -/
theorem not_bgSetting_radius {d L M1 : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hM : 1 ≤ M1) (r₀ : ℝ) :
    ¬ (4 * (d : ℝ) * (L : ℝ) ^ 3 ≤ r₀ ∧ r₀ * (M1 : ℝ) ≤ minSep L M1 - 1) := by
  rintro ⟨h0, h1⟩
  unfold minSep at h1
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hL' : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hM' : (1 : ℝ) ≤ M1 := by exact_mod_cast hM
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hL2 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hL3 : 9 * (L : ℝ) ≤ (L : ℝ) ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hL2 hL0]
  have h2 : 5 * (L : ℝ) ≤ 4 * (d : ℝ) * (L : ℝ) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hd' (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 3)]
  have h3 : 4 * (d : ℝ) * (L : ℝ) ^ 3 * M1 ≤ r₀ * M1 := mul_le_mul_of_nonneg_right h0 (by linarith)
  nlinarith

/-- **T7(a), in the fields of `BgSetting`.**  A generating set whose separation is
`minSep L (L ^ m₁) = 5 L M₁` never satisfies `BgSetting` as the parent `Gp`. -/
theorem not_bgSetting_minSep {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L]
    {ϱ₁ ϱ₂ : ℝ} {Gp : GeneratingSet d L (N₁ * L ^ m₁) K (minSep L (L ^ m₁))}
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁} {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂}
    {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (Balaban.Localization.CTorus d L N₁ m₁ K)} {j : ℕ} :
    ¬ BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j := by
  intro h
  refine not_bgSetting_radius (d := d) (L := L) (M1 := L ^ m₁) h.HBp.hd h.HBp.hL
    (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (NeZero.ne L))) r₀ ⟨h.hr₀, ?_⟩
  have := h.hr
  push_cast
  linarith

/-- **T7(b).**  The `BgHyp` requirement `bgR0 d L ≤ ϱ` for the separation `ϱ = 5 L M₁` holds
exactly when `M₁ ≥ bgR0 d L / (5 L)`; in particular it needs `5 M₁ ≥ 4 d`
(`le_of_bgR0_le_minSep`), and it holds for `M₁ ≥ ⌈bgR0 d L / (5 L)⌉`. -/
theorem bgR0_le_minSep_iff {d L M1 : ℕ} (hL : 0 < L) :
    bgR0 d L ≤ minSep L M1 ↔ bgR0 d L / (5 * L) ≤ M1 := by
  unfold minSep
  have : (0 : ℝ) < 5 * L := by positivity
  rw [div_le_iff₀ this]
  constructor <;> intro h <;> linarith

theorem bgR0_le_minSep_of_ceil {d L M1 : ℕ} (hL : 0 < L)
    (h : ⌈bgR0 d L / (5 * L)⌉₊ ≤ M1) : bgR0 d L ≤ minSep L M1 :=
  (bgR0_le_minSep_iff hL).2 ((Nat.le_ceil _).trans (by exact_mod_cast h))

theorem le_of_bgR0_le_minSep {d L M1 : ℕ} (h : bgR0 d L ≤ minSep L M1) :
    4 * (d : ℝ) * L ≤ 5 * L * M1 :=
  (le_max_left _ _).trans h

end Radius

end Balaban.LargeField
