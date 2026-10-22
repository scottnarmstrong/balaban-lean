/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2SmallFieldC
public import Balaban.LargeField.Def7v2Corr

/-!
# The small-field exponent of `R` as a sum over cubes

The residual of `R` (P7 (3.22)–(3.25)) is localized into roots (P3 §4).  The site and bond
summands of the exponent `𝒜₂ + ℱ + ℛ` of (D1) — the single-scale action with half star bonds, the
mass and block terms, `⟨χ_Y g, φ̄⟩` — are local in the background field; they are grouped by the cube
of `𝕋_k` of their anchor site.

* `actionGWithCube`, `actionGWith_eq_sum_cube`; `starBondEWithCube`, `starBondEWith_eq_sum_cube`:
  the multiscale action and the star bond energy, for any partition of the sites and the blocks;
* `SFCtx.tCubeOfBg`, `SFCtx.blkBase`, `SFCtx.tCubeOfBlk`: the cube of a site and of a block of the
  level-`k` torus;
* `SFCtx.actCube`, `SFCtx.actStarAt_eq_sum_actCube`: `A*_k(Y; ψ_k, φ)` is the sum over the cubes
  of `𝕋_k` of the action of the cube;
* `corrCoefSite`, `corrSum_eq_site`: the restricted antisymmetric correction of P5 (1.8) is a sum over
  sites, with site coefficients `∑_{y ∈ A} v(y, s) - ∑_{x ∈ B} v(s, x)`;
* `finsum_poly_eq`, `Def7v2.polyIdx`, `EresMainAt_eq_poly`, `Mpart_eq_poly`: the terms `ℰ^{(j)}`,
  `ℳ^{(j)}` as sums over the polymers;
* `Def7v2.cubeRoot`, `Def7v2.polyRoot`, `sfExp2At_eq_roots`, `sfExp2At_sub_eq_roots`: the exponent
  `𝒜₂ + ℱ + ℛ` of (D1) at a background field is the sum of the roots of the cubes of `𝕋_k` and of the
  polymers of `𝒟_j`, the vacuum term and `ℛ^{(k)}`; the residual of two regions is the sum of the
  root differences.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Finset

section CubeSplit

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {β : Type*} [Fintype β] [DecidableEq β]
  (cs : Site d L N₀ q → β) (cb : ∀ m, Blk d L N₀ q m → β)

/-- **The multiscale action of the sites and blocks anchored in the class `c`** of a partition
(`cs` on the sites, `cb` on the blocks): the block terms of the blocks `y` with `cb y = c`, the
bonds with base site in `c` and the mass terms of the sites in `c`. -/
noncomputable def actionGWithCube (sq : (Fin N → ℂ) → ℂ) (G : GeneratingSet d L N₀ q ϱ)
    (a : ℕ → ℝ) (μ : ℝ) (h : Fin N → ℂ) (X : Finset (Site d L N₀ q))
    (ψ : (m : ℕ) → Blk d L N₀ q m → Fin N → ℂ) (φ : Site d L N₀ q → Fin N → ℂ) (c : β) : ℂ :=
  algebraMap ℝ ℂ (1 / 2) * ∑ m ∈ Icc 1 q, ∑ y ∈ (tBlocks d L N₀ q m (lam G m ∩ X)).filter
      (fun y => cb m y = c),
      algebraMap ℝ ℂ (a m * (L : ℝ) ^ (m * (d - 2))) * sq (ψ m y - bavgL d L N₀ q m φ y) +
    algebraMap ℝ ℂ (1 / 2) * ∑ ν : Fin d, ∑ x ∈ (univ : Finset (Site d L N₀ q)).filter
      (fun x => cs x = c), (if x ∈ X ∧ x + Pi.single ν 1 ∈ X then bondTermWith sq φ ν x else 0) +
    algebraMap ℝ ℂ (μ / 2) * ∑ x ∈ X.filter (fun x => cs x = c), sq (φ x - h)

/-- **The multiscale action is the sum of the actions of the classes of a partition.** -/
theorem actionGWith_eq_sum_cube (sq : (Fin N → ℂ) → ℂ) (G : GeneratingSet d L N₀ q ϱ)
    (a : ℕ → ℝ) (μ : ℝ) (h : Fin N → ℂ) (X : Finset (Site d L N₀ q))
    (ψ : (m : ℕ) → Blk d L N₀ q m → Fin N → ℂ) (φ : Site d L N₀ q → Fin N → ℂ) :
    actionGWith sq G a μ h X ψ φ = ∑ c, actionGWithCube cs cb sq G a μ h X ψ φ c := by
  have e1 : ∑ c, ∑ m ∈ Icc 1 q, algebraMap ℝ ℂ (a m * (L : ℝ) ^ (m * (d - 2))) *
      ∑ y ∈ (tBlocks d L N₀ q m (lam G m ∩ X)).filter (fun y => cb m y = c),
        sq (ψ m y - bavgL d L N₀ q m φ y) =
      ∑ m ∈ Icc 1 q, algebraMap ℝ ℂ (a m * (L : ℝ) ^ (m * (d - 2))) *
        ∑ y ∈ tBlocks d L N₀ q m (lam G m ∩ X), sq (ψ m y - bavgL d L N₀ q m φ y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.mul_sum, Finset.sum_fiberwise _ (cb m)
      (fun y => sq (ψ m y - bavgL d L N₀ q m φ y))]
  have e2 : ∑ c, ∑ ν : Fin d, ∑ x ∈ (univ : Finset (Site d L N₀ q)).filter (fun x => cs x = c),
      (if x ∈ X ∧ x + Pi.single ν 1 ∈ X then bondTermWith sq φ ν x else 0) =
      ∑ ν : Fin d, ∑ x : Site d L N₀ q,
        (if x ∈ X ∧ x + Pi.single ν 1 ∈ X then bondTermWith sq φ ν x else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun ν _ => Finset.sum_fiberwise _ cs
      (fun x => if x ∈ X ∧ x + Pi.single ν 1 ∈ X then bondTermWith sq φ ν x else 0)
  have e3 : ∑ c, ∑ x ∈ X.filter (fun x => cs x = c), sq (φ x - h) = ∑ x ∈ X, sq (φ x - h) :=
    Finset.sum_fiberwise _ cs (fun x => sq (φ x - h))
  unfold actionGWithCube actionGWith bondEWith bondEdirWith
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, e1, e2, e3]

/-- **The star bonds with base site in the class `c`.** -/
noncomputable def starBondEWithCube (sq : (Fin N → ℂ) → ℂ) (X : Finset (Site d L N₀ q))
    (φ : Site d L N₀ q → Fin N → ℂ) (c : β) : ℂ := by
  classical
  exact ∑ ν : Fin d, ∑ x ∈ (univ : Finset (Site d L N₀ q)).filter (fun x => cs x = c),
    if (x ∈ X) ≠ (x + Pi.single ν 1 ∈ X) then bondTermWith sq φ ν x else 0

/-- **The star bond energy is the sum over the classes of a partition.** -/
theorem starBondEWith_eq_sum_cube (sq : (Fin N → ℂ) → ℂ) (X : Finset (Site d L N₀ q))
    (φ : Site d L N₀ q → Fin N → ℂ) :
    starBondEWith sq X φ = ∑ c, starBondEWithCube cs sq X φ c := by
  classical
  unfold starBondEWithCube starBondEWith
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ν _ => Finset.sum_fiberwise _ cs
    (fun x => if (x ∈ X) ≠ (x + Pi.single ν 1 ∈ X) then bondTermWith sq φ ν x else 0)

end CubeSplit

namespace Def7.SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

/-- The cube of `𝕋_k` of a site of the level-`k` torus (that of `bgSet`). -/
def tCubeOfBg (x : BgT C.geo k) : Torus S.d (n k) :=
  cubeMap n S.L M K k (bgToFine C.geo C.hnn C.hkK x)

/-- The base site of an `m`-block of the level-`k` torus. -/
def blkBase (m : ℕ) (y : Blk S.d S.L (C.geo.M1 * (C.geo.c * n k)) k m) : BgT C.geo k :=
  fun ν => (((y ν).val * S.L ^ m : ℕ) : ZMod _)

/-- The cube of `𝕋_k` of an `m`-block (that of its base site). -/
def tCubeOfBlk (m : ℕ) (y : Blk S.d S.L (C.geo.M1 * (C.geo.c * n k)) k m) : Torus S.d (n k) :=
  C.tCubeOfBg (C.blkBase m y)

variable (Y : Set (Torus S.d (n k))) (ψC : BlockAt S n M K k → Fin N → ℂ)
  (hv : EuclideanSpace ℝ (Fin N))

/-- **The action of the cube `c` of `𝕋_k`**: the block, bond, mass and star bond terms of
`A*_k(Y; ψ_k, φ)` anchored in `c`, at a background field `φ` and an action mass `μ`. -/
noncomputable def actCube (μ : ℝ) (φ : (C.genW Y).Ω 1 × Fin N → ℂ) (c : Torus S.d (n k)) : ℂ :=
  actionGWithCube C.tCubeOfBg C.tCubeOfBlk (fun v => SmallField.dot v v)
      (levelGen (ϱ := (1 : ℝ)) k) C.weights μ (hC hv) (C.bgSet Y) (C.psiLevelKOf ψC)
      (C.phiBarAt Y ψC hv φ) c +
    1 / 4 * starBondEWithCube C.tCubeOfBg (fun v => SmallField.dot v v) (C.bgSet Y)
      (C.phiBarAt Y ψC hv φ) c

/-- **`A*_k(Y; ψ_k, φ)` is the sum over the cubes of `𝕋_k` of the actions of the cubes.** -/
theorem actStarAt_eq_sum_actCube (μ : ℝ) (φ : (C.genW Y).Ω 1 × Fin N → ℂ) :
    C.actStarAt Y ψC hv μ φ = ∑ c, C.actCube Y ψC hv μ φ c := by
  unfold actStarAt actCube actionGC starBondEC
  rw [actionGWith_eq_sum_cube C.tCubeOfBg C.tCubeOfBlk, starBondEWith_eq_sum_cube C.tCubeOfBg,
    Finset.mul_sum, ← Finset.sum_add_distrib]

/-- The cube of `𝕋_k` of a site of the Def-6 torus (that of `sset`). -/
def tCubeOfC (x : Localization.CTorus S.d S.L C.N₁ m₁ k) : Torus S.d (n k) :=
  C.tCubeOfBg (sfToBg C.geo C.hT x)

theorem mem_sset_iff_cube (A : Set (Torus S.d (n k))) (x : Localization.CTorus S.d S.L C.N₁ m₁ k) :
    x ∈ C.sset A ↔ C.tCubeOfC x ∈ A := Iff.rfl

end Def7.SFCtx

/-! ### The correction as a sum over sites -/

section CorrSite

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

open Classical in
/-- **The coefficient of a site in the restricted antisymmetric sum**: `∑_{y ∈ A} v(y, s)` if
`s ∈ B`, minus `∑_{x ∈ B} v(s, x)` if `s ∈ A`. -/
noncomputable def corrCoefSite (v : Localization.CTorus d L N₁ m₁ k →
    Localization.CTorus d L N₁ m₁ k → ℂ)
    (A B : Finset (Localization.CTorus d L N₁ m₁ k)) (s : Localization.CTorus d L N₁ m₁ k) : ℂ :=
  (if s ∈ B then ∑ y ∈ A, v y s else 0) - (if s ∈ A then ∑ x ∈ B, v s x else 0)

open Classical in
/-- A double sum of differences `F x - F y` is a sum over the sites. -/
theorem sum_sum_mul_sub_eq_site (v : Localization.CTorus d L N₁ m₁ k →
    Localization.CTorus d L N₁ m₁ k → ℂ)
    (A B : Finset (Localization.CTorus d L N₁ m₁ k)) (F : Localization.CTorus d L N₁ m₁ k → ℂ) :
    ∑ y ∈ A, ∑ x ∈ B, v y x * (F x - F y) = ∑ s, corrCoefSite v A B s * F s := by
  have h1 : ∑ y ∈ A, ∑ x ∈ B, v y x * F x = ∑ s, (if s ∈ B then ∑ y ∈ A, v y s else 0) * F s := by
    rw [Finset.sum_comm]
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_mul]
  have h2 : ∑ y ∈ A, ∑ x ∈ B, v y x * F y = ∑ s, (if s ∈ A then ∑ x ∈ B, v s x else 0) * F s := by
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact Finset.sum_congr rfl fun y _ => by rw [Finset.sum_mul]
  simp only [mul_sub, Finset.sum_sub_distrib, h1, h2, corrCoefSite, sub_mul]

/-- **The restricted antisymmetric sum of P5 (1.8) is a sum over the sites**:
`∑_s (½ c₁(s) ψ(s)·ψ(s) + c₂(s) ν_j h·(ψ)₀(s))` with the site coefficients `corrCoefSite`. -/
theorem corrSum_eq_site (v₁ v₂ : Localization.CTorus d L N₁ m₁ k →
    Localization.CTorus d L N₁ m₁ k → ℂ) (νj : ℝ)
    (A B : Finset (Localization.CTorus d L N₁ m₁ k)) (ψ : SmallField.Def6.Fld d L N₁ m₁ k N)
    (h : Fin N → ℂ) :
    Def7v2.corrSum v₁ v₂ νj A B ψ h = ∑ s, (1 / 2 * corrCoefSite v₁ A B s *
      SmallField.dot (ψ s) (ψ s) +
      corrCoefSite v₂ A B s * ((νj : ℂ) * SmallField.dot h (Def7v2.unitDirC (ψ s)))) := by
  have e : ∀ y x, Def7v2.corrPair (v₁ y x) (v₂ y x) νj ψ h y x =
      1 / 2 * (v₁ y x * (SmallField.dot (ψ x) (ψ x) - SmallField.dot (ψ y) (ψ y))) +
        v₂ y x * ((νj : ℂ) * SmallField.dot h (Def7v2.unitDirC (ψ x)) -
          (νj : ℂ) * SmallField.dot h (Def7v2.unitDirC (ψ y))) := by
    intro y x; unfold Def7v2.corrPair; ring
  unfold Def7v2.corrSum
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_sum_mul_sub_eq_site v₁ A B (fun s => SmallField.dot (ψ s) (ψ s)),
    sum_sum_mul_sub_eq_site v₂ A B (fun s => (νj : ℂ) * SmallField.dot h (Def7v2.unitDirC (ψ s))),
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by ring

end CorrSite

/-! ### Sums over the polymers -/

section Poly

variable {α : Type*} [Finite α] {β : Type*} [AddCommMonoid β]

open Classical in
/-- A finite sum over the polymers through a point inside a region is a sum over all polymers with
an indicator. -/
theorem finsum_poly_eq (P : Set α → Prop) (y : α) (T : Set α) (f : Set α → β) :
    ∑ᶠ X ∈ {X : Set α | P X ∧ y ∈ X ∧ X ⊆ T}, f X =
      ∑ X ∈ (Set.toFinite {X : Set α | P X}).toFinset, if y ∈ X ∧ X ⊆ T then f X else 0 := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext X
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_filter]

end Poly

/-! ### The exponent of the second version of (D1) as a sum over roots -/

namespace Def7v2

open SmallField SmallField.Def6 SmallField.Def6v2 Def7 Def7.SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (vc : CorrCoef S.d) (Y : Set (Torus S.d (n k))) (ψC : BlockAt S n M K k → Fin N → ℂ)
  (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)

/-- The polymers of `𝒟_j` on the Def-6 torus, as a finite set. -/
noncomputable def polyIdx (j : ℕ) : Finset (Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) :=
  (Set.toFinite {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) | Def6.IsPolyDom C.m₀ j X}).toFinset

/-- **The correction of the level `j` anchored in the cube `c`**: the site form of `corrSum` at the
composed field of `φ`, over the sites of `c`. -/
noncomputable def corrCube (φ : (C.genW Y).Ω 1 × Fin N → ℂ) (j : ℕ) (c : Torus S.d (n k)) : ℂ :=
  ∑ s ∈ (Finset.univ : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)).filter
      (fun s => C.tCubeOfC s = c),
    (1 / 2 * corrCoefSite (fun y x => vc.v1 j (unlift j (x - y))) (C.alignedIn j Y)
        (C.alignedIn j (thickY R Y)) s *
        dot (C.psiJAt Y ψC hv φ j s) (C.psiJAt Y ψC hv φ j s) +
      corrCoefSite (fun y x => vc.v2 j (unlift j (x - y))) (C.alignedIn j Y)
        (C.alignedIn j (thickY R Y)) s *
        (((nuIdeal S.L k (C.sf.ν k) j : ℝ) : ℂ) * dot (hC hv) (unitDirC (C.psiJAt Y ψC hv φ j s))))

/-- **The source term `⟨χ_Y g, φ̄⟩` anchored in the cube `c`.** -/
noncomputable def gCube (φ : (C.genW Y).Ω 1 × Fin N → ℂ) (c : Torus S.d (n k)) : ℂ :=
  ∑ x ∈ (C.bgSet Y).filter (fun x => C.tCubeOfBg x = c), ∑ i : Fin N,
    g (bgToFine C.geo C.hnn C.hkK x, i) * C.phiBarAt Y ψC hv φ x i

/-- **The root of the cube `c`**: `-β A*` of the cube, the corrections of all levels at its sites and
the source term at its sites. -/
noncomputable def cubeRoot (φ : (C.genW Y).Ω 1 × Fin N → ℂ) (c : Torus S.d (n k)) : ℂ :=
  -((betaCanon S.d S.L (C.sf.β k) k 0 : ℝ) : ℂ) * C.actCube Y ψC hv (sfActMass2 C.cs k) φ c -
    ∑ j ∈ Finset.Icc 1 k, corrCube C vc Y ψC hv φ j c + gCube C Y ψC hv g φ c

open Classical in
/-- **The root of the polymer `X` of `𝒟_j`**: the terms `ℰ^{(j)}(y, X)`, `y ∈ X` aligned in `Y`, and
`⟨g, ℳ^{(j)}(x, X)⟩`, `x ∈ X ∩ Y`, at the composed field of `φ`, when `X ⊂ Y^≈`. -/
noncomputable def polyRoot (φ : (C.genW Y).Ω 1 × Fin N → ℂ) (j : ℕ)
    (X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) : ℂ :=
  if X ⊆ C.sset (thickY R Y) then
    (∑ y ∈ (C.alignedIn j Y).filter (fun y => y ∈ X),
        (C.sf.Tm C.N₁).E j y X (C.psiJAt Y ψC hv φ j) (Def6.constFld (hC hv))) +
      ∑ x ∈ (Finset.univ : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)).filter
          (fun x => x ∈ X ∧ x ∈ C.sset Y), ∑ i : Fin N,
        sfG C.geo C.hnn C.hkK C.hT g x i * (C.sf.Tm C.N₁).M j x X (C.psiJAt Y ψC hv φ j)
          (Def6.constFld (hC hv)) (sfG C.geo C.hnn C.hkK C.hT g) i
  else 0

open Classical in
/-- `ℰ^{(j)}` without the correction, as a sum over the polymers. -/
theorem EresMainAt_eq_poly (φ : (C.genW Y).Ω 1 × Fin N → ℂ) (j : ℕ) :
    C.EresMainAt Y ψC hv φ j = ∑ X ∈ polyIdx C j, if X ⊆ C.sset (thickY R Y) then
      ∑ y ∈ (C.alignedIn j Y).filter (fun y => y ∈ X),
        (C.sf.Tm C.N₁).E j y X (C.psiJAt Y ψC hv φ j) (Def6.constFld (hC hv)) else 0 := by
  unfold EresMainAt
  simp only [finsum_poly_eq (fun X => Def6.IsPolyDom C.m₀ j X)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun X _ => ?_
  split_ifs with hX
  · rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun y _ => by simp [hX]
  · exact Finset.sum_eq_zero fun y _ => by simp [hX]

open Classical in
/-- The source part `∑_x ⟨g(x), ℳ^{(j)}(x, Y)⟩` of `ℱ`, as a sum over the polymers. -/
theorem Mpart_eq_poly (φ : (C.genW Y).Ω 1 × Fin N → ℂ) (j : ℕ) :
    (∑ x : Localization.CTorus S.d S.L C.N₁ m₁ k,
      if x ∈ C.sset Y then
        ∑ i : Fin N, sfG C.geo C.hnn C.hkK C.hT g x i * C.MresJAt Y ψC hv g φ j x i
      else 0) =
      ∑ X ∈ polyIdx C j, if X ⊆ C.sset (thickY R Y) then
        ∑ x ∈ (Finset.univ : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)).filter
            (fun x => x ∈ X ∧ x ∈ C.sset Y), ∑ i : Fin N,
          sfG C.geo C.hnn C.hkK C.hT g x i * (C.sf.Tm C.N₁).M j x X (C.psiJAt Y ψC hv φ j)
            (Def6.constFld (hC hv)) (sfG C.geo C.hnn C.hkK C.hT g) i else 0 := by
  have hM : ∀ x i, C.MresJAt Y ψC hv g φ j x i = ∑ X ∈ polyIdx C j,
      if x ∈ X ∧ X ⊆ C.sset (thickY R Y) then (C.sf.Tm C.N₁).M j x X (C.psiJAt Y ψC hv φ j)
        (Def6.constFld (hC hv)) (sfG C.geo C.hnn C.hkK C.hT g) i else 0 := by
    intro x i
    unfold MresJAt
    rw [finsum_poly_eq (fun X => Def6.IsPolyDom C.m₀ j X), Finset.sum_apply]
    exact Finset.sum_congr rfl fun X _ => by split_ifs <;> rfl
  simp only [hM, Finset.mul_sum]
  have e : ∀ x : Localization.CTorus S.d S.L C.N₁ m₁ k,
      (if x ∈ C.sset Y then ∑ i : Fin N, ∑ X ∈ polyIdx C j,
        sfG C.geo C.hnn C.hkK C.hT g x i *
          (if x ∈ X ∧ X ⊆ C.sset (thickY R Y) then (C.sf.Tm C.N₁).M j x X (C.psiJAt Y ψC hv φ j)
            (Def6.constFld (hC hv)) (sfG C.geo C.hnn C.hkK C.hT g) i else 0) else 0) =
      ∑ X ∈ polyIdx C j, if x ∈ X ∧ x ∈ C.sset Y ∧ X ⊆ C.sset (thickY R Y) then
        ∑ i : Fin N, sfG C.geo C.hnn C.hkK C.hT g x i * (C.sf.Tm C.N₁).M j x X
          (C.psiJAt Y ψC hv φ j) (Def6.constFld (hC hv)) (sfG C.geo C.hnn C.hkK C.hT g) i
      else 0 := by
    intro x
    rw [Finset.sum_comm]
    split_ifs with hx
    · refine Finset.sum_congr rfl fun X _ => ?_
      by_cases h : x ∈ X ∧ X ⊆ C.sset (thickY R Y)
      · simp [h, hx]
      · have : ¬ (x ∈ X ∧ x ∈ C.sset Y ∧ X ⊆ C.sset (thickY R Y)) := by tauto
        simp [h, this]
    · symm
      exact Finset.sum_eq_zero fun X _ => by simp [hx]
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun X _ => ?_
  split_ifs with hX
  · rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun x _ => by
      by_cases h : x ∈ X ∧ x ∈ C.sset Y <;> simp [h, hX]
  · exact Finset.sum_eq_zero fun x _ => by simp [hX]

/-- **The exponent of the second version of (D1) at a background field `φ` is a sum over roots**:
the cubes `c` of `𝕋_k` (the action, the corrections and the source term at their sites), the
polymers `X ∈ 𝒟_j`, `1 ≤ j ≤ k` (the terms `ℰ^{(j)}`, `⟨g, ℳ^{(j)}⟩`), the vacuum term and `ℛ^{(k)}`. -/
theorem sfExp2At_eq_roots (φ : (C.genW Y).Ω 1 × Fin N → ℂ) :
    sfExp2At C vc Y ψC hv g φ =
      ∑ c, cubeRoot C vc Y ψC hv g φ c +
        ∑ j ∈ Finset.Icc 1 k, ∑ X ∈ polyIdx C j, polyRoot C Y ψC hv g φ j X -
        ((C.sf.E C.N₁ * volK M Y : ℝ) : ℂ) + C.RresC Y ψC hv g := by
  classical
  unfold sfExp2At Ares2At EresK2At EresJ2At actStar2At FresAt
  rw [C.actStarAt_eq_sum_actCube]
  simp only [EresMainAt_eq_poly, Mpart_eq_poly, corrSum_eq_site]
  have hcorr : ∀ j, (∑ s : Localization.CTorus S.d S.L C.N₁ m₁ k,
      (1 / 2 * corrCoefSite (fun y x => vc.v1 j (unlift j (x - y))) (C.alignedIn j Y)
        (C.alignedIn j (thickY R Y)) s *
        dot (C.psiJAt Y ψC hv φ j s) (C.psiJAt Y ψC hv φ j s) +
      corrCoefSite (fun y x => vc.v2 j (unlift j (x - y))) (C.alignedIn j Y)
        (C.alignedIn j (thickY R Y)) s *
        (((nuIdeal S.L k (C.sf.ν k) j : ℝ) : ℂ) * dot (hC hv) (unitDirC (C.psiJAt Y ψC hv φ j s))))) =
      ∑ c, corrCube C vc Y ψC hv φ j c := fun j =>
    (Finset.sum_fiberwise _ C.tCubeOfC _).symm
  have hg : (∑ x ∈ C.bgSet Y, ∑ i : Fin N,
      g (bgToFine C.geo C.hnn C.hkK x, i) * C.phiBarAt Y ψC hv φ x i) =
      ∑ c, gCube C Y ψC hv g φ c := (Finset.sum_fiberwise _ C.tCubeOfBg _).symm
  simp only [hcorr, hg]
  unfold cubeRoot polyRoot
  simp only [ite_add_zero]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.Icc 1 k) (t := Finset.univ)]
  ring

/-- **The difference of the exponents of two small-field regions is a sum over roots** (the residual
of P7 (3.22)–(3.25) without the reference action of the removed components): old minus new root of
every cube and of every polymer, the difference of the vacuum terms and of `ℛ^{(k)}`. -/
theorem sfExp2At_sub_eq_roots (Y₁ Y₂ : Set (Torus S.d (n k)))
    (φ₁ : (C.genW Y₁).Ω 1 × Fin N → ℂ) (φ₂ : (C.genW Y₂).Ω 1 × Fin N → ℂ) :
    sfExp2At C vc Y₁ ψC hv g φ₁ - sfExp2At C vc Y₂ ψC hv g φ₂ =
      ∑ c, (cubeRoot C vc Y₁ ψC hv g φ₁ c - cubeRoot C vc Y₂ ψC hv g φ₂ c) +
        ∑ j ∈ Finset.Icc 1 k, ∑ X ∈ polyIdx C j,
          (polyRoot C Y₁ ψC hv g φ₁ j X - polyRoot C Y₂ ψC hv g φ₂ j X) -
        (((C.sf.E C.N₁ * volK M Y₁ : ℝ) : ℂ) - ((C.sf.E C.N₁ * volK M Y₂ : ℝ) : ℂ)) +
        (C.RresC Y₁ ψC hv g - C.RresC Y₂ ψC hv g) := by
  rw [sfExp2At_eq_roots, sfExp2At_eq_roots]
  simp only [Finset.sum_sub_distrib]
  ring

end Def7v2

end Balaban.LargeField
