/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LevelLocalCover
public import Balaban.Localization.I5Expansion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cover, the size function and the fibre inequality of the renormalization localization

This file is geometry and counting only.  None of the three localization principles of the
record `RenormExpInput` (`locC1`, `locC2`, `locDφ`) is proved here, and nothing here depends on the
chart question (the domain `XiCOneReal`) or on the choice of generators.

**The torus.**  `RenormExpInput` indexes its covers by `Finset (Torus d (N₀ * L ^ k))` with
`G : GeneratingSet d L N₀ k ϱ`.  The localization files use `CTorus d L N₁ m₁ K`, an abbreviation
of `Torus d ((N₁ * L ^ m₁) * L ^ K)`, with `G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ`.  Putting
`N₀ = N₁ * L ^ m₁` and `k = K` the two tori are the same type, definitionally; no equivalence is
needed.

**Contents.**
* The finite label type `RenLabel G X₁` of the cubes of the cover whose patch misses `X₁`, the
  inclusion `renCube`, the cover `renYs` by finsets of sites (the image of the landed
  `polymerDomains` under `Set → Finset`), and the single size function `renDY = treeLenCov`
  (`renDY_nonneg`).
* `renLoc_fin_domains`: these data, with the root facts of `levelLocalCover` for a block root and
  a site root.
* `renLoc_fibre_two`, `renLoc_fibre`: the fibre inequality
  `e^{κ_out dY(Y)} ∑_{C connected, Y(C) = Y} e^{-(κ₁-1)|C|} ≤ 1` for `κ_out ≤ 2κ`, from the
  landed `gm4` and `gm3_fam` under the rate hypotheses of `localization_expansion`.
* `renAgg_sum`, `renAgg_norm_le`: the aggregation of coefficients with constant `K_loc = 1`.
* `renLoc_localization_expansion_fin`: the landed `localization_expansion` in the finset-indexed
  form.
* `renLoc_fibre_levelPair`: an instance at the landed pair of levels.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Analysis Finset

section Labels

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (X₁ : Set (CTorus d L N₁ m₁ K))

/-- **The labels**: the cubes of the cover whose patch misses `X₁`. -/
def RenLabel : Type :=
  {q : ℕ × CTorus d L N₁ m₁ K // q ∈ cubeIdx G ∧ Disjoint (Pset m₁ q) X₁}

/-- The inclusion of the labels into the cubes. -/
def renCube : RenLabel G X₁ → ℕ × CTorus d L N₁ m₁ K := Subtype.val

theorem renCube_injective : Function.Injective (renCube G X₁) := Subtype.val_injective

theorem renCube_mem (i : RenLabel G X₁) : renCube G X₁ i ∈ cubeIdx G := i.2.1

theorem renCube_disjoint (i : RenLabel G X₁) : Disjoint (Pset m₁ (renCube G X₁ i)) X₁ := i.2.2

noncomputable instance : Fintype (RenLabel G X₁) :=
  Fintype.ofInjective (fun q : RenLabel G X₁ => (⟨q.1, q.2.1⟩ : ↥(cubeIdx G)))
    (fun a b h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext h')

noncomputable instance : DecidableEq (RenLabel G X₁) := Classical.decEq _

end Labels

section Cover

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- A set of sites as a finset of sites. -/
noncomputable def finOf {d n : ℕ} [NeZero n] (Y : Set (Torus d n)) : Finset (Torus d n) :=
  open Classical in Finset.univ.filter (· ∈ Y)

theorem coe_finOf {d n : ℕ} [NeZero n] (Y : Set (Torus d n)) : (↑(finOf Y) : Set (Torus d n)) = Y := by
  ext y; simp [finOf]

theorem finOf_coe {d n : ℕ} [NeZero n] (Y : Finset (Torus d n)) : finOf (↑Y : Set (Torus d n)) = Y :=
  Finset.coe_injective (coe_finOf _)

theorem finOf_injective {d n : ℕ} [NeZero n] :
    Function.Injective (finOf : Set (Torus d n) → Finset (Torus d n)) := fun Y Y' h => by
  rw [← coe_finOf Y, ← coe_finOf Y', h]

variable (c : ι → ℕ × CTorus d L N₁ m₁ K) (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)
  (X₁ : Set (CTorus d L N₁ m₁ K))

/-- **The cover** (`Ys` of `RenormExpInput`): the domains `Y[𝒞]` of the connected families, as
finsets of sites. -/
noncomputable def renYs : Finset (Finset (CTorus d L N₁ m₁ K)) :=
  (polymerDomains c G m₀ X₁).image finOf

/-- **The size**: the covering functional `d̃^cov` of the finset, one function for all roots. -/
noncomputable def renDY (Y : Finset (CTorus d L N₁ m₁ K)) : ℝ :=
  treeLenCov G m₀ (↑Y : Set (CTorus d L N₁ m₁ K))

variable {c G m₀ X₁}

omit [DecidableEq ι] in
theorem mem_renYs {Y : Finset (CTorus d L N₁ m₁ K)} :
    Y ∈ renYs c G m₀ X₁ ↔ (↑Y : Set (CTorus d L N₁ m₁ K)) ∈ polymerDomains c G m₀ X₁ := by
  unfold renYs
  constructor
  · intro h
    obtain ⟨Y0, hY0, rfl⟩ := Finset.mem_image.1 h
    rwa [coe_finOf]
  · intro h
    exact Finset.mem_image.2 ⟨_, h, finOf_coe Y⟩

omit [DecidableEq ι] in
theorem finOf_mem_renYs {Y : Set (CTorus d L N₁ m₁ K)} (h : Y ∈ polymerDomains c G m₀ X₁) :
    finOf Y ∈ renYs c G m₀ X₁ := Finset.mem_image_of_mem _ h

/-- The size is nonnegative on every finset. -/
theorem renDY_nonneg (Y : Finset (CTorus d L N₁ m₁ K)) : 0 ≤ renDY G m₀ Y :=
  treeLenCov_nonneg G m₀ _

omit [DecidableEq ι] in
/-- Sums over the finset cover are sums over the domains. -/
theorem sum_renYs {E : Type*} [AddCommMonoid E] (g : Set (CTorus d L N₁ m₁ K) → E) :
    ∑ Y ∈ renYs c G m₀ X₁, g ↑Y = ∑ Y ∈ polymerDomains c G m₀ X₁, g Y := by
  unfold renYs
  rw [Finset.sum_image (fun Y _ Y' _ h => finOf_injective h)]
  exact Finset.sum_congr rfl fun Y _ => by rw [coe_finOf]

end Cover

section RootFacts

variable {d L N₁ m₁ : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}

open LocalCover in
/-- **Leaf 10a.1.**  In the setting of `levelLocalCover`, for a block root `z` and for a site root
`s`, with `X₁ = X1 Gp m₀ k 𝒦_X` (equal to `nbhdF`): the labels `RenLabel Gp X₁` form a finite type
whose inclusion is injective, legal, with patches missing `X₁`; the finset cover `renYs` consists of
the finsets whose coercions are the polymer domains; the size `renDY` is nonnegative; and the root
facts of `levelLocalCover` hold (`CovSetup`, attained tree, `Δ = 0`). -/
theorem renLoc_fin_domains {k N : ℕ} {a : ℕ → ℝ} {ν : ℝ}
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm) (S : DGSetting Gp a ν)
    (hG' : IsLevel Gp (k + 1)) {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁) :
    (∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      CovSetup Gp m₀ k (cube m₀ k (blockSite k z)) (fam m₀ (blockSite k z)) ∧
      (↑(nbhdF m₀ (blockSite k z)) : Set (CTorus d L N₁ m₁ (k + 1))) =
        X1 Gp m₀ k (fam m₀ (blockSite k z)) ∧
      (∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
        (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ cube m₀ k (blockSite k z)) ∧
          MeetsOne m₀ k (fam m₀ (blockSite k z)) W₀ ∧
          bondCost (scaleW L m₀ m₁ k) E₀ = treeLenCovOne m₀ k (cube m₀ k (blockSite k z))) ∧
      treeLenCovOne m₀ k (cube m₀ k (blockSite k z)) = 0 ∧
      readSites Hm k z ⊆ ↑(nbhdF m₀ (blockSite k z)) ∧
      BlockMargin Gp (nbhdF m₀ (blockSite k z))
        (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ∧
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
        ↑(nbhdF m₀ (blockSite k z)) ∧
      Function.Injective (renCube Gp (X1 Gp m₀ k (fam m₀ (blockSite k z)))) ∧
      (∀ i, renCube Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))) i ∈ cubeIdx Gp) ∧
      (∀ i, Disjoint (Pset m₁ (renCube Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))) i))
        (X1 Gp m₀ k (fam m₀ (blockSite k z)))) ∧
      (∀ Y ∈ renYs (renCube Gp (X1 Gp m₀ k (fam m₀ (blockSite k z)))) Gp m₀
          (X1 Gp m₀ k (fam m₀ (blockSite k z))),
        (↑Y : Set (CTorus d L N₁ m₁ (k + 1))) ∈
          polymerDomains (renCube Gp (X1 Gp m₀ k (fam m₀ (blockSite k z)))) Gp m₀
            (X1 Gp m₀ k (fam m₀ (blockSite k z)))) ∧
      (∀ Y : Finset (CTorus d L N₁ m₁ (k + 1)), 0 ≤ renDY Gp m₀ Y)) ∧
    (∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N,
      CovSetup Gp m₀ k (cube m₀ k s.1) (fam m₀ s.1) ∧
      (↑(nbhdF m₀ s.1) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ k (fam m₀ s.1) ∧
      (∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
        (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ cube m₀ k s.1) ∧ MeetsOne m₀ k (fam m₀ s.1) W₀ ∧
          bondCost (scaleW L m₀ m₁ k) E₀ = treeLenCovOne m₀ k (cube m₀ k s.1)) ∧
      treeLenCovOne m₀ k (cube m₀ k s.1) = 0 ∧ s.1 ∈ nbhdF m₀ s.1 ∧
      Function.Injective (renCube Gp (X1 Gp m₀ k (fam m₀ s.1))) ∧
      (∀ i, renCube Gp (X1 Gp m₀ k (fam m₀ s.1)) i ∈ cubeIdx Gp) ∧
      (∀ i, Disjoint (Pset m₁ (renCube Gp (X1 Gp m₀ k (fam m₀ s.1)) i))
        (X1 Gp m₀ k (fam m₀ s.1))) ∧
      (∀ Y ∈ renYs (renCube Gp (X1 Gp m₀ k (fam m₀ s.1))) Gp m₀ (X1 Gp m₀ k (fam m₀ s.1)),
        (↑Y : Set (CTorus d L N₁ m₁ (k + 1))) ∈
          polymerDomains (renCube Gp (X1 Gp m₀ k (fam m₀ s.1))) Gp m₀ (X1 Gp m₀ k (fam m₀ s.1))) ∧
      (∀ Y : Finset (CTorus d L N₁ m₁ (k + 1)), 0 ≤ renDY Gp m₀ Y)) := by
  obtain ⟨hV, hF⟩ := levelLocalCover (N := N) (a := a) Hm S hG' hm₀ hN
  refine ⟨fun z => ?_, fun s => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hV z
    exact ⟨h1, h2, h3, h4, h5, h6, h7, renCube_injective _ _, renCube_mem _ _,
      renCube_disjoint _ _, fun Y hY => mem_renYs.1 hY, renDY_nonneg⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hF s
    exact ⟨h1, h2, h3, h4, h5, renCube_injective _ _, renCube_mem _ _,
      renCube_disjoint _ _, fun Y hY => mem_renYs.1 hY, renDY_nonneg⟩

end RootFacts

section Fibre

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ j : ℕ}
variable {X 𝒦X : Set (CTorus d L N₁ m₁ K)}
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {c : ι → ℕ × CTorus d L N₁ m₁ K}

omit [Fintype ι] in
/-- **(2.1)**: for a connected family `C` with `Δ = 0`,
`(κ₁ - 1)|C| ≥ (κ₁/2 - 1)|C| + 2κ dY(Y(C))`. -/
theorem renLoc_exponent (hS : CovSetup G m₀ j X 𝒦X) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hc : ∀ i, c i ∈ cubeIdx G)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κ κ₀ κ₁ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκ : 3 * κ₀ + 3 ≤ κ)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁) (C : Finset ι)
    (hconn : IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c (X1 G m₀ j 𝒦X)) C) :
    (κ₁ / 2 - 1) * C.card + 2 * κ * treeLenCov G m₀ (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) ≤
      (κ₁ - 1) * C.card := by
  have h4 := gm4 hS hd hL hc C hconn hopt κ κ₀ κ₁ hκ₀ hκ hκ₁
  rw [hΔ] at h4
  linarith

/-- **(2.2)**: for every domain `Y`,
`e^{2κ d̃(Y)} ∑_{C connected, Y(C) = Y} e^{-(κ₁-1)|C|} ≤ 1`. -/
theorem renLoc_fibre_two (hS : CovSetup G m₀ j X 𝒦X) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hc : ∀ i, c i ∈ cubeIdx G) (hcinj : Function.Injective c)
    (hdisj : ∀ i, Disjoint (Pset m₁ (c i)) (X1 G m₀ j 𝒦X))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κ κ₀ κ₁ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκ : 3 * κ₀ + 3 ≤ κ)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁)
    (h1 : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2)
    (Y : Set (CTorus d L N₁ m₁ K)) :
    Real.exp (2 * κ * treeLenCov G m₀ Y) *
      ∑ C ∈ connFams c G m₀ (X1 G m₀ j 𝒦X) Y, Real.exp (-(κ₁ - 1) * C.card) ≤ 1 := by
  have hg := gm3_fam c hS hc hcinj hdisj Y (κ₁ / 2 - 1) h1 hlog
  rw [Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum fun C hC => ?_) hg
  obtain ⟨hconn, hY⟩ := (mem_connFams c).1 hC
  have h2 := renLoc_exponent hS hd hL hc hopt hΔ hκ₀ hκ hκ₁ C hconn
  rw [hY] at h2
  rw [← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

/-- **Leaf 10a.2, the fibre inequality with `K_loc = 1`**: for every output rate `κ_out ≤ 2κ` and
every finset `Y` of sites,
`e^{κ_out dY(Y)} ∑_{C connected, Y(C) = Y} e^{-(κ₁-1)|C|} ≤ 1`, with `dY = renDY`. -/
theorem renLoc_fibre (hS : CovSetup G m₀ j X 𝒦X) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hc : ∀ i, c i ∈ cubeIdx G) (hcinj : Function.Injective c)
    (hdisj : ∀ i, Disjoint (Pset m₁ (c i)) (X1 G m₀ j 𝒦X))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κ κ₀ κ₁ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκ : 3 * κ₀ + 3 ≤ κ)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁)
    (h1 : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2)
    {κout : ℝ} (hout : κout ≤ 2 * κ) (Y : Finset (CTorus d L N₁ m₁ K)) :
    Real.exp (κout * renDY G m₀ Y) *
      ∑ C ∈ connFams c G m₀ (X1 G m₀ j 𝒦X) (↑Y : Set (CTorus d L N₁ m₁ K)),
        Real.exp (-(κ₁ - 1) * C.card) ≤ 1 := by
  have h2 := renLoc_fibre_two hS hd hL hc hcinj hdisj hopt hΔ hκ₀ hκ hκ₁ h1 hlog
    (↑Y : Set (CTorus d L N₁ m₁ K))
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ =>
    (Real.exp_pos _).le)) h2
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hout (renDY_nonneg Y))

end Fibre

section Aggregate

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ j : ℕ}
variable {X 𝒦X : Set (CTorus d L N₁ m₁ K)}
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (c : ι → ℕ × CTorus d L N₁ m₁ K)

/-- The aggregate `t_Y = ∑_{C : Y(C) = Y} coef(C)` over the connected families. -/
noncomputable def renAgg {E : Type*} [AddCommMonoid E] (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (m₀ : ℕ) (X₁ : Set (CTorus d L N₁ m₁ K)) (coef : Finset ι → E)
    (Y : Finset (CTorus d L N₁ m₁ K)) : E :=
  ∑ C ∈ connFams c G m₀ X₁ (↑Y : Set (CTorus d L N₁ m₁ K)), coef C

variable {c}

omit [DecidableEq ι] in
/-- **The sum of the aggregates is the sum of the coefficients** (coefficients vanish off the
connected families). -/
theorem renAgg_sum {E : Type*} [AddCommMonoid E] (X₁ : Set (CTorus d L N₁ m₁ K))
    (coef : Finset ι → E)
    (hvan : ∀ C, ¬ IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c X₁) C → coef C = 0) :
    ∑ Y ∈ renYs c G m₀ X₁, renAgg c G m₀ X₁ coef Y = ∑ C, coef C := by
  classical
  have h1 : ∑ Y ∈ renYs c G m₀ X₁, renAgg c G m₀ X₁ coef Y =
      ∑ Y ∈ polymerDomains c G m₀ X₁, ∑ C ∈ connFams c G m₀ X₁ Y, coef C :=
    sum_renYs (c := c) (G := G) (m₀ := m₀) (X₁ := X₁)
      (fun Y => ∑ C ∈ connFams c G m₀ X₁ Y, coef C)
  have h2 : ∑ C, coef C = ∑ C ∈ Finset.univ.filter (fun C : Finset ι =>
      IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c X₁) C), coef C :=
    (Finset.sum_filter_of_ne (fun C _ hC => by_contra fun h => hC (hvan C h))).symm
  rw [h1, h2]
  unfold polymerDomains
  exact Finset.sum_fiberwise_of_maps_to (g := Ysites G m₀ c X₁)
    (s := Finset.univ.filter fun C : Finset ι =>
      IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c X₁) C) (f := coef)
    (fun C hC => Finset.mem_image_of_mem _ hC)

/-- **Aggregation with `K_loc = 1`.**  If the coefficients of the connected families satisfy
`‖coef C‖ ≤ M e^{-(κ₁-1)|C|}`, then the aggregates satisfy `‖t_Y‖ ≤ M e^{-κ_out dY(Y)}` for every
`κ_out ≤ 2κ`.  The constant `M ≥ 0` is arbitrary, so the transfer clause of `HasLocPrinciple`
(which quantifies over every `M`) follows from this statement. -/
theorem renAgg_norm_le {E : Type*} [NormedAddCommGroup E]
    (hS : CovSetup G m₀ j X 𝒦X) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hc : ∀ i, c i ∈ cubeIdx G) (hcinj : Function.Injective c)
    (hdisj : ∀ i, Disjoint (Pset m₁ (c i)) (X1 G m₀ j 𝒦X))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κ κ₀ κ₁ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκ : 3 * κ₀ + 3 ≤ κ)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁)
    (h1 : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2)
    (coef : Finset ι → E) {M : ℝ} (hM : 0 ≤ M)
    (hcoef : ∀ C, IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c (X1 G m₀ j 𝒦X)) C →
      ‖coef C‖ ≤ M * Real.exp (-(κ₁ - 1) * C.card))
    {κout : ℝ} (hout : κout ≤ 2 * κ) (Y : Finset (CTorus d L N₁ m₁ K)) :
    ‖renAgg c G m₀ (X1 G m₀ j 𝒦X) coef Y‖ ≤ M * Real.exp (-κout * renDY G m₀ Y) := by
  have hf := renLoc_fibre hS hd hL hc hcinj hdisj hopt hΔ hκ₀ hκ hκ₁ h1 hlog hout Y
  have hS' : ∑ C ∈ connFams c G m₀ (X1 G m₀ j 𝒦X) (↑Y : Set (CTorus d L N₁ m₁ K)),
      Real.exp (-(κ₁ - 1) * C.card) ≤ Real.exp (-κout * renDY G m₀ Y) := by
    set x := κout * renDY G m₀ Y with hx
    set S := ∑ C ∈ connFams c G m₀ (X1 G m₀ j 𝒦X) (↑Y : Set (CTorus d L N₁ m₁ K)),
      Real.exp (-(κ₁ - 1) * C.card) with hSdef
    have e : S = Real.exp (-x) * (Real.exp x * S) := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [show -κout * renDY G m₀ Y = -x by rw [hx]; ring, e]
    calc Real.exp (-x) * (Real.exp x * S) ≤ Real.exp (-x) * 1 :=
          mul_le_mul_of_nonneg_left hf (Real.exp_pos _).le
      _ = Real.exp (-x) := mul_one _
  unfold renAgg
  calc _ ≤ ∑ C ∈ connFams c G m₀ (X1 G m₀ j 𝒦X) (↑Y : Set (CTorus d L N₁ m₁ K)), ‖coef C‖ :=
        norm_sum_le _ _
    _ ≤ ∑ C ∈ connFams c G m₀ (X1 G m₀ j 𝒦X) (↑Y : Set (CTorus d L N₁ m₁ K)),
          M * Real.exp (-(κ₁ - 1) * C.card) :=
        Finset.sum_le_sum fun C hC => hcoef C ((mem_connFams c).1 hC).1
    _ = M * ∑ C ∈ connFams c G m₀ (X1 G m₀ j 𝒦X) (↑Y : Set (CTorus d L N₁ m₁ K)),
          Real.exp (-(κ₁ - 1) * C.card) := (Finset.mul_sum _ _ _).symm
    _ ≤ M * Real.exp (-κout * renDY G m₀ Y) := mul_le_mul_of_nonneg_left hS' hM

/-- **The landed `localization_expansion` in the finset-indexed form** (the corollary that makes
the aggregation lemma superfluous for the expansion itself).  With `Δ = 0` and the cover `renYs`,
the terms `t_Y = evTerm ↑Y` satisfy `F u 1 = ∑_{Y ∈ renYs} t_Y`, depend on `u` through `AgY ↑Y`
only, are analytic on `S`, and obey `‖t_Y u‖ ≤ Eb e^{-κ_out dY(Y)}` for every `κ_out ≤ 2κ`
(`K_loc = 1`). -/
theorem renLoc_localization_expansion_fin {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
    (hS : CovSetup G m₀ j X 𝒦X) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hc : ∀ i, c i ∈ cubeIdx G) (hcinj : Function.Injective c)
    (hdisj : ∀ i, Disjoint (Pset m₁ (c i)) (X1 G m₀ j 𝒦X))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κ κ₀ κ₁ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκ : 3 * κ₀ + 3 ≤ κ)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁)
    (h1 : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {S : Set U} {F : U → (ι → ℂ) → ℂ}
    {Ag : Finset ι → U → U → Prop} {AgY : Set (CTorus d L N₁ m₁ K) → U → U → Prop}
    (hrefl : ∀ C u, u ∈ S → Ag C u u)
    (hlink : ∀ C u u', AgY (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) u u' → Ag C u u')
    (hana : AnalyticOnNhd ℂ (fun p : U × (ι → ℂ) => F p.1 p.2)
      (S ×ˢ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁)))
    (hbd : ∀ u ∈ S, ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁),
      ‖F u s‖ ≤ Eb * Real.exp (-(κ - 1) * treeLenCovOne m₀ j X))
    (hloc : LocalityAEOn (Real.exp κ₁) S (fun i => Pset m₁ (c i)) (compY c (X1 G m₀ j 𝒦X)) Ag F)
    {κout : ℝ} (hout : κout ≤ 2 * κ) :
    (∀ u ∈ S, F u 1 = ∑ Y ∈ renYs c G m₀ (X1 G m₀ j 𝒦X),
      evTerm c G m₀ (X1 G m₀ j 𝒦X) F (↑Y : Set (CTorus d L N₁ m₁ K)) u) ∧
    (∀ Y : Finset (CTorus d L N₁ m₁ K), ∀ u ∈ S, ∀ u' ∈ S, AgY ↑Y u u' →
      evTerm c G m₀ (X1 G m₀ j 𝒦X) F (↑Y : Set (CTorus d L N₁ m₁ K)) u =
        evTerm c G m₀ (X1 G m₀ j 𝒦X) F (↑Y : Set (CTorus d L N₁ m₁ K)) u') ∧
    (∀ Y : Finset (CTorus d L N₁ m₁ K), ∀ u ∈ S,
      ‖evTerm c G m₀ (X1 G m₀ j 𝒦X) F (↑Y : Set (CTorus d L N₁ m₁ K)) u‖ ≤
        Eb * Real.exp (-κout * renDY G m₀ Y)) ∧
    (∀ Y : Finset (CTorus d L N₁ m₁ K),
      AnalyticOnNhd ℂ (evTerm c G m₀ (X1 G m₀ j 𝒦X) F (↑Y : Set (CTorus d L N₁ m₁ K))) S) := by
  obtain ⟨e1, e2, e3, e4⟩ := localization_expansion c hS hd hL hc hcinj hdisj hopt hκ₀ hκ hκ₁ h1
    hlog hEb hrefl hlink hana hbd hloc
  refine ⟨fun u hu => ?_, fun Y u hu u' hu' h => e2 _ u hu u' hu' h, fun Y u hu => ?_,
    fun Y => e4 _⟩
  · rw [e1 u hu]
    exact (sum_renYs (c := c) (G := G) (m₀ := m₀) (X₁ := X1 G m₀ j 𝒦X)
      (fun Y => evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u)).symm
  · refine (e3 _ u hu).trans ?_
    rw [hΔ]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hEb
    have := mul_le_mul_of_nonneg_right hout (renDY_nonneg (G := G) (m₀ := m₀) Y)
    unfold renDY at this ⊢
    linarith

end Aggregate

section Instance

/-- **Non-vacuity of the hypotheses of `renLoc_fibre`** at the landed pair of levels
(`d = L = 3`, `N₁ = 9`, `K = 2`, cover scale `m₀ = 1`; the rate hypotheses of
`interaction_levelPair_witness` with `κ₀ = 0`, `κ = κdec`, `κ₁ = κ`): the cover and rate hypotheses
hold jointly, and the fibre inequality holds at every finset `Y`.  There `X₁` is the whole torus,
so the label type is empty (the single cover cube of the landed witness fills the torus); a
setting with nonempty labels needs the proper neighbourhood of `levelLocalCover` on a larger
torus, which is not landed. -/
theorem renLoc_fibre_levelPair (N : ℕ) :
    ∃ (m₁ : ℕ) (ϱ κdec κ₀ κ₁ : ℝ),
      CovSetup (LevelPair.Gp m₁ ϱ) 1 1 LevelPair.Xr ({0} : Set (CTorus 3 3 9 m₁ 2)) ∧
      treeLenCovOne 1 1 (LevelPair.Xr (m₁ := m₁)) = 0 ∧
      0 ≤ κ₀ ∧ 3 * κ₀ + 3 ≤ κdec ∧ 4 * 3 * ((((2 * 3 + 1) ^ 3 : ℕ)) : ℝ) * κdec ≤ κ₁ ∧
      1 ≤ (κ₁ / 2 - 1) / 2 ∧
      Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ 1) ^ 3 : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2 ∧
      IsEmpty (RenLabel (LevelPair.Gp m₁ ϱ)
        (X1 (LevelPair.Gp m₁ ϱ) 1 1 ({0} : Set (CTorus 3 3 9 m₁ 2)))) ∧
      ∀ Y : Finset (CTorus 3 3 9 m₁ 2),
        Real.exp (2 * κdec * renDY (LevelPair.Gp m₁ ϱ) 1 Y) *
          ∑ C ∈ connFams (renCube (LevelPair.Gp m₁ ϱ)
              (X1 (LevelPair.Gp m₁ ϱ) 1 1 ({0} : Set (CTorus 3 3 9 m₁ 2))))
            (LevelPair.Gp m₁ ϱ) 1 (X1 (LevelPair.Gp m₁ ϱ) 1 1 ({0} : Set (CTorus 3 3 9 m₁ 2)))
            (↑Y : Set (CTorus 3 3 9 m₁ 2)), Real.exp (-(κ₁ - 1) * C.card) ≤ 1 := by
  obtain ⟨m₁, ϱ, c, BG, κ, eps, c₂, BG₂, δ₁, κdec, κ₀, -, -, -, -, -, -, hS, -, hopt, hΔ,
    hκ₀, hκ, hκ₁, h1, hlog, -⟩ := LevelPair.interaction_levelPair_witness N
  refine ⟨m₁, ϱ, κdec, κ₀, κ, hS, hΔ, hκ₀, hκ, hκ₁, h1, hlog, ?_, fun Y => ?_⟩
  · refine ⟨fun q => ?_⟩
    have h : Disjoint (Pset m₁ q.1) (X1 (LevelPair.Gp m₁ ϱ) 1 1 ({0} : Set (CTorus 3 3 9 m₁ 2))) :=
      q.2.2
    have key : ∀ y : CTorus 3 3 9 m₁ 2,
        y ∈ X1 (LevelPair.Gp m₁ ϱ) 1 1 ({0} : Set (CTorus 3 3 9 m₁ 2)) := fun y => by
      rw [LevelPair.X1_eq_univ]; exact Set.mem_univ y
    exact Set.disjoint_left.1 h (self_mem_Pset q.1) (key _)
  · have hκ₁' : 4 * ((3 : ℕ) : ℝ) * ((((2 * 3 + 1) ^ 3 : ℕ)) : ℝ) * κdec ≤ κ := by
      simpa using hκ₁
    exact renLoc_fibre hS (le_refl 3) (le_refl 3) (renCube_mem _ _) (renCube_injective _ _)
      (renCube_disjoint _ _) hopt hΔ hκ₀ hκ hκ₁' h1 hlog (le_refl _) Y

end Instance

end Balaban.Localization
