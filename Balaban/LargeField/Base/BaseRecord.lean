module

public import Balaban.LargeField.Region.Inclusions
public import Balaban.LargeField.Region.Generating
public import Balaban.LargeField.Characteristic.Functions
public import Balaban.Background.Data
public import Balaban.LargeField.Geometry.Coarsen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The scale-`0` small-field function and the base record (LF-RECONSTRUCTION Definition II.7.1)

* `chiPrimeZero`: `χ'^{(0)}(□') = A(□') · B(□')` for a cube `□'` of `𝕋_1`, with the block factor
  `A(□') = ∏_{y ∈ T_1(□')} 1[|θ(y) - (Qφ)(y)| < 2δ₀]` and the bond/site factor
  `B(□') = ∏_{b ∩ □' ≠ ∅} 1[|∂φ(b)| < δ₀] · (∏_{x ∈ □'} 1[|φ_x - h| < δ₀ ν^{-1/2}])^{[regime (B)]}`;
* `chiPrimeZero_decomposition`: the base decomposition
  `1 = ∏_{□'} [χ'^{(0)}(□') + χ'^{(0)c}(□')] = ∑_{P ⊆ 𝕋_1} χ'^{(0)c}(P) χ'^{(0)}(P^c)`;
* `BaseRecord`: a quadruple `(P₁, Q₁, R₁, S₁)` satisfying the constraints of Definition I.3.1 at
  `k = 0` (`Z₀ = ∅`, hence `U₀ = U'₀ = ∅` and `Ω'₁ = 𝕋₁`), `BaseRecord.toStep`: it is a
  `RegionStep` with `Z = ∅` (`baseRecord_isStep`).

The fields live on the fine torus `Torus d (M * nn K * L ^ K)` and on the `1`-blocks
`Torus d (M * nn K * L ^ (K - 1))`, as in the localized operators (block convention of
`Operators/Variables.lean`); the cube of a fine site is `cubeMap nn L M K 1` and the cube of a
`1`-block is `blockMap M (nn 1)`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background

section Chi

variable {d N : ℕ} (nn : ℕ → ℕ) (L M K : ℕ)

open Classical in
/-- The block average `(Qφ)(y) = L^{-d} ∑_{x ∈ B_1(y)} φ_x` of a spin field on the fine torus,
at a `1`-block `y`. -/
noncomputable def spinAverage [∀ k, NeZero (nn k)] [NeZero M] [NeZero L]
    (φ : Torus d (M * nn K * L ^ K) → Fin N → ℝ) (y : Torus d (M * nn K * L ^ (K - 1)))
    (i : Fin N) : ℝ :=
  ((L : ℝ) ^ d)⁻¹ *
    ∑ x ∈ Finset.univ.filter (fun x : Torus d (M * nn K * L ^ K) =>
      blockMap L (M * nn K * L ^ (K - 1)) x = y), φ x i

/-- The block condition of `A(□')`: `|θ(y) - (Qφ)(y)| < 2 δ₀` for every `1`-block `y ∈ T_1(□')`. -/
def ChiBlockProp [∀ k, NeZero (nn k)] [NeZero M] [NeZero L] (δ₀ : ℝ)
    (φ : Torus d (M * nn K * L ^ K) → Fin N → ℝ)
    (θ : Torus d (M * nn K * L ^ (K - 1)) → Fin N → ℝ) (c : Torus d (nn 1)) : Prop :=
  ∀ y : Torus d (M * nn K * L ^ (K - 1)), blockMap M (nn 1) y = c →
    rn (fun i => θ y i - spinAverage nn L M K φ y i) < 2 * δ₀

/-- The bond condition of `B(□')`: `|∂φ(b)| < δ₀` for every nearest-neighbour bond `b = (x, x + e_μ)`
with at least one end point in `□'`. -/
def ChiBondProp (δ₀ : ℝ) (φ : Torus d (M * nn K * L ^ K) → Fin N → ℝ) (c : Torus d (nn 1)) :
    Prop :=
  ∀ (x : Torus d (M * nn K * L ^ K)) (μ : Fin d),
    (cubeMap nn L M K 1 x = c ∨ cubeMap nn L M K 1 (x + Pi.single μ 1) = c) →
      rn (fun i => φ (x + Pi.single μ 1) i - φ x i) < δ₀

/-- The site condition of `B(□')` (regime (B)): `|φ_x - h| < δ₀ ν^{-1/2}` for every `x ∈ □'`,
written `ν |φ_x - h|² < δ₀²` (equivalent for `ν > 0`, `chiSiteProp_iff`). -/
def ChiSiteProp (ν δ₀ : ℝ) (φ : Torus d (M * nn K * L ^ K) → Fin N → ℝ) (h : Fin N → ℝ)
    (c : Torus d (nn 1)) : Prop :=
  ∀ x : Torus d (M * nn K * L ^ K), cubeMap nn L M K 1 x = c →
    ν * ∑ i, (φ x i - h i) ^ 2 < δ₀ ^ 2

/-- For `ν > 0` the site condition is `|φ_x - h| < δ₀ ν^{-1/2}`. -/
theorem chiSiteProp_iff {ν δ₀ : ℝ} (hν : 0 < ν) (hδ : 0 < δ₀) (v : Fin N → ℝ) :
    ν * ∑ i, v i ^ 2 < δ₀ ^ 2 ↔ rn v < δ₀ * ν ^ (-(1 / 2 : ℝ)) := by
  have hs : ν ^ (-(1 / 2 : ℝ)) = (Real.sqrt ν)⁻¹ := by
    rw [Real.rpow_neg hν.le, ← Real.sqrt_eq_rpow]
  have hsp : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  rw [hs, ← div_eq_mul_inv, lt_div_iff₀ hsp]
  unfold rn
  have hsq : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [← Real.sqrt_mul hsq, Real.sqrt_lt' hδ, mul_comm]


/-- The configurations on which the scale-`0` small-field function is evaluated: the spin field `φ`
on the fine torus and the block field `θ` on the `1`-blocks. -/
abbrev BaseCfg (d N : ℕ) (nn : ℕ → ℕ) (L M K : ℕ) : Type :=
  (Torus d (M * nn K * L ^ K) → Fin N → ℝ) × (Torus d (M * nn K * L ^ (K - 1)) → Fin N → ℝ)

/-- `A(□') = ∏_{y ∈ T_1(□')} 1[|θ(y) - (Qφ)(y)| < 2δ₀]`. -/
noncomputable def chiBlockA [∀ k, NeZero (nn k)] [NeZero M] [NeZero L] (δ₀ : ℝ)
    (c : Torus d (nn 1)) : BaseCfg d N nn L M K → ℝ :=
  charFn fun p => ChiBlockProp nn L M K δ₀ p.1 p.2 c

/-- `B(□') = ∏_{b ∩ □' ≠ ∅} 1[|∂φ(b)| < δ₀] · (∏_{x ∈ □'} 1[|φ_x - h| < δ₀ ν^{-1/2}])^{[regimeB]}`;
`regimeB` says that the step is in regime (B) (`k₀ = 0`), where the site condition is present. -/
noncomputable def chiBondB (regimeB : Prop) (ν δ₀ : ℝ) (h : Fin N → ℝ) (c : Torus d (nn 1)) :
    BaseCfg d N nn L M K → ℝ :=
  charFn fun p => ChiBondProp nn L M K δ₀ p.1 c ∧ (regimeB → ChiSiteProp nn L M K ν δ₀ p.1 h c)

/-- **Definition II.7.1**: the scale-`0` small-field function `χ'^{(0)}(□') = A(□') · B(□')` of a
cube `□'` of `𝕋_1`, at the spins `φ` and the block field `θ`; `regimeB` says that the site
condition `|φ_x - h| < δ₀ ν^{-1/2}` is imposed (regime (B)). -/
noncomputable def chiPrimeZero [∀ k, NeZero (nn k)] [NeZero M] [NeZero L] (regimeB : Prop)
    (ν δ₀ : ℝ) (h : Fin N → ℝ) (c : Torus d (nn 1)) (p : BaseCfg d N nn L M K) : ℝ :=
  chiBlockA nn L M K δ₀ c p * chiBondB nn L M K regimeB ν δ₀ h c p

theorem chiPrimeZero_eq_one_iff [∀ k, NeZero (nn k)] [NeZero M] [NeZero L] (regimeB : Prop)
    (ν δ₀ : ℝ) (h : Fin N → ℝ) (c : Torus d (nn 1)) (p : BaseCfg d N nn L M K) :
    chiPrimeZero nn L M K regimeB ν δ₀ h c p = 1 ↔
      ChiBlockProp nn L M K δ₀ p.1 p.2 c ∧ ChiBondProp nn L M K δ₀ p.1 c ∧
        (regimeB → ChiSiteProp nn L M K ν δ₀ p.1 h c) := by
  classical
  unfold chiPrimeZero chiBlockA chiBondB
  simp only [charFn_apply]
  by_cases h1 : ChiBlockProp nn L M K δ₀ p.1 p.2 c <;>
    by_cases h2 : ChiBondProp nn L M K δ₀ p.1 c ∧ (regimeB → ChiSiteProp nn L M K ν δ₀ p.1 h c) <;>
    simp [h1, h2]

theorem chiPrimeZero_eq_zero_or_one [∀ k, NeZero (nn k)] [NeZero M] [NeZero L] (regimeB : Prop)
    (ν δ₀ : ℝ) (h : Fin N → ℝ) (c : Torus d (nn 1)) (p : BaseCfg d N nn L M K) :
    chiPrimeZero nn L M K regimeB ν δ₀ h c p = 0 ∨ chiPrimeZero nn L M K regimeB ν δ₀ h c p = 1 := by
  classical
  unfold chiPrimeZero chiBlockA chiBondB
  simp only [charFn_apply]
  split_ifs <;> simp

/-- **The base decomposition** (P5 (2.6) at `k = 0`, `Ω'_1 = 𝕋_1`):
`1 = ∏_{□'} [χ'^{(0)}(□') + χ'^{(0)c}(□')] = ∑_{P ⊆ 𝕋_1} χ'^{(0)c}(P) χ'^{(0)}(P^c)`, where
`χ'^{(0)c}(□') = 1 - χ'^{(0)}(□')` and the products are over cubes. -/
theorem chiPrimeZero_decomposition [∀ k, NeZero (nn k)] [NeZero M] [NeZero L] (regimeB : Prop)
    (ν δ₀ : ℝ) (h : Fin N → ℝ) (p : BaseCfg d N nn L M K) :
    ∑ P ∈ (Finset.univ : Finset (Torus d (nn 1))).powerset,
        (∏ c ∈ P, (1 - chiPrimeZero nn L M K regimeB ν δ₀ h c p)) *
          ∏ c ∈ (Finset.univ : Finset (Torus d (nn 1))) \ P,
            chiPrimeZero nn L M K regimeB ν δ₀ h c p = 1 := by
  rw [← Finset.prod_add]
  exact Finset.prod_eq_one fun c _ => by ring

end Chi


/-! ### Adjacent sites lie in cubes at distance at most one -/

theorem supDist_add_single_le {d m : ℕ} [NeZero m] (x : Torus d m) (μ : Fin d) :
    supDist x (x + Pi.single μ 1) ≤ 1 := by
  refine supDist_le_iff.mpr fun i => ?_
  rw [Pi.add_apply, sub_add_cancel_left, cycNorm_neg]
  by_cases hi : i = μ
  · subst hi
    simp only [Pi.single_eq_same]
    exact (cycNorm_le_iff _ _).mpr ⟨1, by simp, by simp⟩
  · rw [Pi.single_eq_of_ne hi]
    exact (cycNorm_le_iff _ _).mpr ⟨0, by simp, by simp⟩

/-- The cubes of `𝕋_1` of two nearest-neighbour fine sites are within distance `1`. -/
theorem supDist_cubeMap_add_single_le {d : ℕ} {nn : ℕ → ℕ} [∀ k, NeZero (nn k)] {L M K : ℕ}
    [NeZero M] [NeZero L] (hnn : ∀ i, i < K → nn i = L * nn (i + 1)) (hK : 1 ≤ K)
    (x : Torus d (M * nn K * L ^ K)) (μ : Fin d) :
    supDist (cubeMap nn L M K 1 x) (cubeMap nn L M K 1 (x + Pi.single μ 1)) ≤ 1 := by
  have hn : M * nn K * L ^ K = (L ^ 1 * M) * nn 1 := fine_eq hnn hK
  have hN : 1 ≤ L ^ 1 * M := Nat.one_le_iff_ne_zero.mpr (by
    have := NeZero.ne L; have := NeZero.ne M; positivity)
  unfold cubeMap
  refine (supDist_blockMap_le hn x (x + Pi.single μ 1)).trans ?_
  have h1 := supDist_add_single_le x μ
  calc (supDist x (x + Pi.single μ 1) + L ^ 1 * M - 1) / (L ^ 1 * M)
      ≤ (1 + L ^ 1 * M - 1) / (L ^ 1 * M) := Nat.div_le_div_right (by omega)
    _ = 1 := by
      rw [show 1 + L ^ 1 * M - 1 = L ^ 1 * M by omega]
      exact Nat.div_self (by omega)

/-! ### The base record -/

section Record

variable {d L n1 : ℕ}

theorem opening_empty [NeZero L] (m : ℕ) : opening L m (∅ : Set (Torus d n1)) = Set.univ := by
  ext y
  simp only [Set.mem_univ, iff_true]
  exact ⟨y, mem_lblock_self (Nat.pos_of_ne_zero (NeZero.ne L)) y, by
    rw [setDist_eq_top_iff.mpr (Or.inr rfl)]; exact le_top⟩

/-- `Ω'_1 = Op_{[R̂_0]+2}(∅) = 𝕋_1` when `Z_0 = ∅` (`U_0 = U'_0 = ∅`). -/
theorem omegaPrime_of_empty [NeZero L] (ρ r : ℕ) {n0 : ℕ} :
    Region.OmegaPrime L ρ (Region.Uprime L n1 r (∅ : Set (Torus d n0))) = Set.univ := by
  have h1 : Region.Uprime L n1 r (∅ : Set (Torus d n0)) = ∅ := by
    unfold Region.Uprime Region.U thick
    rw [nbhd_empty, Set.image_empty]
  unfold Region.OmegaPrime
  rw [h1, nbhd_empty, opening_empty]

/-- A *base record* (Definition II.7.1): the quadruple `(P₁, Q₁, R₁, S₁)` of cubes of `𝕋_1`
satisfying the constraints (R4)-(R6) of Definition I.3.1 at `k = 0`, where `Z₀ = ∅` and hence
`Ω'_1 = 𝕋_1`: `Ω₁ = Op_1(P₁^{∼3}; 𝕋_1)`, `Q₁ ⊆ Ω₁^{∼3}`, `R₁ ⊆ Ω₁`, `S₁ ⊆ Ω''_1^{∼-3}` with
`Ω''_1 = Op_1(F''_1; Ω₁)`, `F''_1 = Q₁^{∼(ρ+2)} ∪ R₁^{∼(2ρ+4)}`, `ρ = ⌊R̂_0⌋`. `P₁ ⊆ Ω'_1 = 𝕋_1` is
vacuous. -/
structure BaseRecord (d L n1 : ℕ) (Rk : ℝ) where
  /-- the cubes `P₁` -/
  P : Set (Torus d n1)
  /-- the cubes `Q₁` -/
  Q : Set (Torus d n1)
  /-- the cubes `R₁` -/
  R : Set (Torus d n1)
  /-- the cubes `S₁` -/
  S : Set (Torus d n1)
  Q_sub : Q ⊆ nbhd 3 (Region.Omega L P Set.univ)
  R_sub : R ⊆ Region.Omega L P Set.univ
  S_sub : S ⊆ nbhdNeg 3 (Region.OmegaDD L (Region.FDD ⌊Rk⌋₊ Q R) (Region.Omega L P Set.univ))

namespace BaseRecord

variable {Rk : ℝ} (br : BaseRecord d L n1 Rk)

/-- `Ω_1 = Op_1(P₁^{∼3}; 𝕋_1)`. -/
abbrev Omega : Set (Torus d n1) := Region.Omega L br.P Set.univ

/-- `F''_1 = Q₁^{∼(ρ+2)} ∪ R₁^{∼(2ρ+4)}`. -/
abbrev FDD : Set (Torus d n1) := Region.FDD ⌊Rk⌋₊ br.Q br.R

/-- `Ω''_1 = Op_1(F''_1; Ω₁)`. -/
abbrev OmegaDD : Set (Torus d n1) := Region.OmegaDD L br.FDD br.Omega

/-- The base record as a step `0 → 1` of the region calculus, with `Z₀ = ∅`. -/
def toStep [NeZero L] (n0 : ℕ) (Rprev : ℝ) : RegionStep d L n0 n1 Rprev Rk where
  Z := ∅
  P := br.P
  Q := br.Q
  R := br.R
  S := br.S
  P_sub := by rw [omegaPrime_of_empty]; exact Set.subset_univ _
  Q_sub := by rw [omegaPrime_of_empty]; exact br.Q_sub
  R_sub := by rw [omegaPrime_of_empty]; exact br.R_sub
  S_sub := by rw [omegaPrime_of_empty]; exact br.S_sub

/-- The base record of a step with `Z = ∅`. -/
def ofStep {n0 : ℕ} {Rprev : ℝ} [NeZero L] (st : RegionStep d L n0 n1 Rprev Rk)
    (hZ : st.Z = ∅) : BaseRecord d L n1 Rk where
  P := st.P
  Q := st.Q
  R := st.R
  S := st.S
  Q_sub := by
    have := st.Q_sub
    rwa [hZ, omegaPrime_of_empty] at this
  R_sub := by
    have := st.R_sub
    rwa [hZ, omegaPrime_of_empty] at this
  S_sub := by
    have := st.S_sub
    rwa [hZ, omegaPrime_of_empty] at this

end BaseRecord

/-- **Lemma II.7.2 (a)** (the geometry). A base record is a step of the region calculus
(Definition I.3.1) with `Z_0 = ∅`: `U_0 = U'_0 = ∅`, `Ω'_1 = 𝕋_1`, the sets `Ω_1, Ω''_1, ...`
of the step are the ones of the record, and the record is recovered from the step. -/
theorem baseRecord_isStep [NeZero L] {Rk : ℝ} (br : BaseRecord d L n1 Rk) (n0 : ℕ) (Rprev : ℝ) :
    (br.toStep n0 Rprev).Z = ∅ ∧ (br.toStep n0 Rprev).U = ∅ ∧
      (br.toStep n0 Rprev).Uprime = ∅ ∧ (br.toStep n0 Rprev).OmegaPrime = Set.univ ∧
      (br.toStep n0 Rprev).P = br.P ∧ (br.toStep n0 Rprev).Q = br.Q ∧
      (br.toStep n0 Rprev).R = br.R ∧ (br.toStep n0 Rprev).S = br.S ∧
      (br.toStep n0 Rprev).Omega = br.Omega ∧ (br.toStep n0 Rprev).FDD = br.FDD ∧
      (br.toStep n0 Rprev).OmegaDD = br.OmegaDD := by
  have hU : (br.toStep n0 Rprev).U = ∅ := by
    show Region.U ⌊Rprev⌋₊ (∅ : Set (Torus d n0)) = ∅
    unfold Region.U thick; rw [nbhd_empty]
  have hU' : (br.toStep n0 Rprev).Uprime = ∅ := by
    show Region.Uprime L n1 ⌊Rprev⌋₊ (∅ : Set (Torus d n0)) = ∅
    unfold Region.Uprime Region.U thick; rw [nbhd_empty, Set.image_empty]
  have hΩ' : (br.toStep n0 Rprev).OmegaPrime = Set.univ := omegaPrime_of_empty _ _
  refine ⟨rfl, hU, hU', hΩ', rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · show Region.Omega L br.P (br.toStep n0 Rprev).OmegaPrime = _
    rw [hΩ']
  · rfl
  · show Region.OmegaDD L _ (Region.Omega L br.P (br.toStep n0 Rprev).OmegaPrime) = _
    rw [hΩ']
    rfl

/-- The record of a step with `Z = ∅` determines the step. -/
theorem baseRecord_ofStep_toStep [NeZero L] {Rk Rprev : ℝ} {n0 : ℕ}
    (st : RegionStep d L n0 n1 Rprev Rk) (hZ : st.Z = ∅) :
    (BaseRecord.ofStep st hZ).toStep n0 Rprev = st := by
  cases st
  simp only [BaseRecord.toStep, BaseRecord.ofStep] at hZ ⊢
  subst hZ
  rfl

namespace BaseRecord

variable {Rk : ℝ} (br : BaseRecord d L n1 Rk)

/-- **Lemma II.7.2 (d)**, first part: `P₁^{∼3} ⊆ Ω₁^c` (as `Ω'_1 = 𝕋_1`). -/
theorem nbhd_P_subset_compl_Omega [NeZero n1] : nbhd 3 br.P ⊆ br.Omegaᶜ := fun _ hc ho =>
  Set.disjoint_left.mp (Region.Omega_disjoint L br.P Set.univ) ho hc

/-- **Lemma II.7.2 (d)**, last part: no cube at index distance `≤ 3` from `Ω₁` lies in `P₁`. -/
theorem disjoint_nbhd_Omega_P [NeZero n1] : Disjoint (nbhd 3 br.Omega) br.P := by
  rw [Set.disjoint_left]
  intro c hc hcP
  obtain ⟨o, ho, hd⟩ := mem_nbhd.mp hc
  refine Set.disjoint_left.mp (Region.Omega_disjoint L br.P Set.univ) ho (mem_nbhd.mpr ⟨c, hcP, ?_⟩)
  rw [supDist_comm]; exact hd

theorem not_mem_P_of_near_Omega [NeZero n1] {c : Torus d n1}
    (h : ∃ o ∈ br.Omega, supDist c o ≤ 3) : c ∉ br.P := fun hc =>
  Set.disjoint_left.mp br.disjoint_nbhd_Omega_P (mem_nbhd.mpr h) hc

end BaseRecord

end Record

end Balaban.LargeField
