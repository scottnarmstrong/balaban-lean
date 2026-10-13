/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.OmegaPost
public import Balaban.Fluctuation.SizeModCore
public import Balaban.Localization.CubeAligned

/-!
# The size of the boundary terms of Def-7 after `R`: the fine chosen-cover modular size

## The papers' definition

* P1 (2.26)–(2.27), p. 117.  `𝒟_j` is the set of connected unions of *open* cubes of the cover
  `π'_j` (cubes of side `L M ℓ_j` with bases on the lattice of spacing `M ℓ_j`, so neighbouring
  cover cubes overlap in their interiors), and `d_j(X) = inf M⁻¹ |Γ|`, the infimum over the
  continuous tree graphs `Γ` contained in `X` that intersect every cube of `π'_j` contained in `X`.
* P5 (1.33)–(1.35), p. 496.  `X ∈ 𝒟_k(mod Ω^c)` if every connected component of `Ω^c` is contained
  in `X` or disjoint from it; `d_k(X mod Ω^c)` is the infimum of `M⁻¹ |Γ|_η` over the connected
  tree graphs in the continuous space, contained in `X`, that intersect every cube of `π'_k`
  which intersects `X ∩ Ω`.  No subfamily of the cover is chosen.  (1.35) is the sum over the
  `X ∋ □`, `□ ⊂ Ω`, of `e^{-d_k(X mod Ω^c)}`.
* P5 (1.38)–(1.39), p. 497 (H7): `|ℬ^{(k)}(X, 𝔸_k)| < B₀ e^{-κ d_k(X mod Ω^c_k)}`; P6
  (4.32)–(4.34), p. 34, uses this size for the old boundary terms and asserts decay of the new ones
  in `d_{k+1}(Y mod Ω^c_{k+1})`.

## The landed size

The size in the bound of the post-`R` records `D7BdryPost`, `D7Bdry2Post` is **not** the papers'
functional.  It is the fine chosen-cover modular size `Fluctuation.dcovModE` of the fluctuation
step (FLUCTUATION Definition 1.1), the size for which the entropy bound `Fluctuation.G2_X` and the
cell count `Fluctuation.cellCount_le_of_admissible` are proved:

* the carrier is the set of sites of the fine torus `CTorus d L N₁ m₁ K`, identified with the fine
  torus `𝕋_{M n_K L^K}` of the history by the side equality of a `FineSizeFrame` (`castT`);
* the `π_k`-cubes are the aligned cells of `L^{k + m₀ + m₁} = M L^k` sites per side (the fine sets
  of the cubes of `𝕋_k`, by `FineSizeFrame.hM`), the `π'_k`-cubes the aligned boxes of `L` cells
  per side;
* `d7SizeE F 𝔸 k X = Fluctuation.dcovModE m₀ k Ω_f X_f` is the infimum of `|E| / (M L^k)` over the
  sets `𝒦` of `π'_k`-cubes contained in `X_f` whose union contains `X_f ∩ Ω_f` (a *chosen* cover)
  and the nearest-neighbour connected structures `(W, E)` of sites of `X_f` meeting every cube of
  `𝒦`; its value is `⊤` when there is no such pair;
* `Ω_f`, `X_f` are the fine sets (`d7Pull`) of the post-`R` region `Ω_k^post(𝔸)`
  (`RegionHistory.omegaPost`, Definition I.3.11) and of the set `X` of cubes of `𝕋_k`.

`d7Size` is the real value; `(⊤ : ENNReal).toReal = 0`, so a bound stated with `d7Size` is only
meaningful where `d7SizeE ≠ ⊤`.  `FineValid` is the condition under which the bound of (D7) is
stated: `X_f ∈ 𝒟_k(mod Ω_f^c)` in the sense of the fluctuation step (`Fluctuation.DjMod`: a
nonempty nearest-neighbour connected union of `π'_k`-cubes containing or missing every
nearest-neighbour component of `Ω_f^c`) and `d7SizeE ≠ ⊤`.  `bdryDomsPost` is the set of the
boundary domains of the post-`R` class: the domains `X ∈ 𝒟_k(mod (Ω_k^post)^c)` at cube level
(`bdryDoms`) meeting `Z` and its complement that are `FineValid`.

The pre-`R` records `D7Bdry`, `D7Bdry2` are unchanged: their domains are `bdryDoms` at the raw
region `OmegaCube` and their bound uses the cube-level size `dCovMod` (`Def7Hist`).

## Differences from the papers, and what is not proved

The landed size differs from P5 (1.34) in three ways: a nearest-neighbour structure of sites
replaces a continuous tree; a chosen subfamily of cover cubes replaces all cover cubes meeting
`X ∩ Ω`; half-open cells replace open cubes, and the components of `Ω^c` are nearest-neighbour
components of sites.  **None of the following is proved in this development.**

* **Comparison with the papers' size** (`OPEN-PAPER-FINE-REALIZATION`,
  `notes/phase1/VMOD-27.md` §3).  For every admissible post-`R` history `𝔸`, scale `k` and
  boundary domain `X ∈ 𝒟_k(mod (Ω_k^post)^c)`, with `Ω_f`, `X_f` as above and
  `d7SizeE F 𝔸 k X ≠ ⊤`: `X_f ∈ Fluctuation.DjMod m₀ k Ω_f`, and there are constants `a > 0`,
  `b ≥ 0` depending only on `d`, `L` such that
  `d_k^{P5}(X mod (Ω_k^post)^c) ≥ a · d7Size F 𝔸 k X - b`, where `d_k^{P5}` is the functional of
  P5 (1.34) on the open domain.  A sufficient statement: every continuous tree in the open domain
  meeting every eligible open cover cube gives a nearest-neighbour tree of sites in `X_f` meeting
  every corresponding box, of length at most `A |Γ| / M + B` (`notes/phase1/VMOD-27.md` §3).
* **Identification of the two notions of component** of `Ω^c` (continuum components of the closed
  complement in the papers, nearest-neighbour components of cubes in `DmodOmega`, of sites in
  `Fluctuation.DjMod`).
* **Support of the boundary terms on the valid labels** for the representation produced by the
  renormalization step: the field `support` of `D7BdryPost` requires `ℬ^{(k)}(X, 𝔸) = 0` at the
  cube-level boundary domains that are not `FineValid`; no producer of this clause is landed.
* **Reindexing of (D1).**  The form clause (D1) (`Rep.bdrySum`) still sums over the boundary
  domains `bdryDoms` at the raw region `OmegaCube`.  Every such domain is a boundary domain at
  `Ω_k^post` (`bdryDoms_OmegaCube_subset_omegaPost`), and under `support` the terms that are not
  `FineValid` vanish (`D7BdryPost.mem_or_eq_zero`, `D7BdryPost.bdrySum_eq` in `Def7`), so every
  term of (D1) is either zero or bounded with the fine size; the sum over all of `bdryDomsPost`
  (which may contain domains that are not boundary domains at the raw region) is not what (D1)
  states.
* **The pre-`R` class.**  `IsRepPre`, `IsRepPre2` keep the records `D7Bdry`, `D7Bdry2` with the
  cube-level size `dCovMod` at the raw region.  A fine size at the raw region for these classes,
  and the passage from the pre-`R` bound to the post-`R` bound through `R`, are not formalized.
* **The H7 domain.**  The analyticity domain of the boundary terms (`H7Domain` at `globalLH`) and
  the regions inside `loc_hist` are those of the pre-`R` record (raw regions `OmegaCube`); their
  form after `R` has not been examined.

For two blocks of cubes meeting at a corner the cube-level size `dCovMod` is `0` and the fine
size is `⊤` (`corner_dCovMod_zero_fine_top` in `Inhabited/D7FineSizeWitness`;
`notes/phase1/VMOD-25.md` §2), so the fine size is not bounded by an affine function of the
cube-level size; this is the reason for the change.  A boundary domain with finite fine size at a
history with a large-field region, and an inhabitant of `D7BdryPost` with a nonzero boundary
term, are in the same file (`d7SizeE_ne_top_at_boundary_domain`, `exists_d7BdryPost_nonzero`).

## Contents

* `FineSizeFrame`, `fineFrame`: the typing data identifying the two fine tori, and the frame
  `N₁ = L^{m₀} n_K` of a torus with `M = L^{m₀ + m₁}`.
* `d7Pull`: the fine set, on `CTorus d L N₁ m₁ K`, of a set of cubes of `𝕋_j`.
* `d7SizeE`, `d7Size`: the size; `FineValid`, `bdryDomsPost`: the valid labels.
* `bdryDoms_mono`, `bdryDoms_OmegaCube_subset_omegaPost`: a boundary domain at the raw region is a
  boundary domain at the post-`R` region.
* `d7SizeE_ne_top_of_isDj`, `fineValid_of_djMod`: finiteness on `𝒟_k`.
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban Balaban.Localization RegionHistory

/-! ### The frame -/

/-- **The typing data of the fine size**: the fine torus `CTorus d L N₁ m₁ K` of the fluctuation
step (side `N₁ L^{m₁} L^K`) is the fine torus `𝕋_{M n_K L^K}` of the history (`side`), the cells
of side `L^{k + m₀ + m₁}` are the fine sets of the cubes of `𝕋_k` (`hM : M = L^{m₀ + m₁}`), and
`L^{m₀} ∣ N₁` (the hypothesis of the cell-partition lemmas of the fluctuation step).  Given `hM`
and `side`, `N₁ = L^{m₀} n_K` (`FineSizeFrame.N₁_eq`). -/
structure FineSizeFrame (S : Setting) (n : ℕ → ℕ) (M K m₀ m₁ : ℕ) where
  /-- the number `N₁` of the fine torus `CTorus d L N₁ m₁ K` -/
  N₁ : ℕ
  /-- `N₁ ≥ 1` -/
  posN₁ : 0 < N₁
  /-- the cube side is `M = L^{m₀ + m₁}` -/
  hM : M = S.L ^ (m₀ + m₁)
  /-- the two fine tori have the same side -/
  side : (N₁ * S.L ^ m₁) * S.L ^ K = M * n K * S.L ^ K
  /-- `L^{m₀} ∣ N₁` -/
  divN₁ : S.L ^ m₀ ∣ N₁

section Frame

variable {S : Setting} {n : ℕ → ℕ} {M K m₀ m₁ : ℕ}

instance FineSizeFrame.neZero (F : FineSizeFrame S n M K m₀ m₁) : NeZero F.N₁ :=
  ⟨F.posN₁.ne'⟩

/-- In a frame, `N₁ = L^{m₀} n_K`. -/
theorem FineSizeFrame.N₁_eq [NeZero S.L] (F : FineSizeFrame S n M K m₀ m₁) :
    F.N₁ = S.L ^ m₀ * n K := by
  have hL : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne S.L)
  have hM : M = S.L ^ m₀ * S.L ^ m₁ := by rw [← pow_add]; exact F.hM
  have h : F.N₁ * S.L ^ m₁ * S.L ^ K = S.L ^ m₀ * S.L ^ m₁ * n K * S.L ^ K :=
    F.side.trans (by rw [hM])
  have h1 : F.N₁ * S.L ^ m₁ = S.L ^ m₀ * S.L ^ m₁ * n K :=
    Nat.eq_of_mul_eq_mul_right (pow_pos hL K) h
  have h2 : F.N₁ * S.L ^ m₁ = S.L ^ m₀ * n K * S.L ^ m₁ := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hL m₁) h2

/-- **The frame of a torus with `M = L^{m₀ + m₁}`**: `N₁ = L^{m₀} n_K`. -/
def fineFrame (S : Setting) (n : ℕ → ℕ) {M : ℕ} (K : ℕ) {m₀ m₁ : ℕ} [NeZero S.L] [NeZero (n K)]
    (hM : M = S.L ^ (m₀ + m₁)) : FineSizeFrame S n M K m₀ m₁ where
  N₁ := S.L ^ m₀ * n K
  posN₁ := Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _)
    (Nat.pos_of_ne_zero (NeZero.ne (n K)))
  hM := hM
  side := by rw [hM, pow_add]; ring
  divN₁ := Dvd.intro _ rfl

/-- `FineSizeFrame` is inhabited whenever `M = L^{m₀ + m₁}` (hard rule 10). -/
theorem FineSizeFrame.nonempty [NeZero S.L] [NeZero (n K)] (hM : M = S.L ^ (m₀ + m₁)) :
    Nonempty (FineSizeFrame S n M K m₀ m₁) :=
  ⟨fineFrame S n K hM⟩

/-- **The fine set, on the torus `CTorus d L N₁ m₁ K` of the frame, of a set `Y` of cubes of
`𝕋_j`**: the sites whose image in the fine torus of the history lies in a cube of `Y`. -/
def d7Pull (F : FineSizeFrame S n M K m₀ m₁) (j : ℕ) (Y : Set (Torus S.d (n j))) :
    Set (Localization.CTorus S.d S.L F.N₁ m₁ K) :=
  {x | castT F.side x ∈ fineSet (S := S) (n := n) M K j Y}

theorem mem_d7Pull {F : FineSizeFrame S n M K m₀ m₁} {j : ℕ} {Y : Set (Torus S.d (n j))}
    {x : Localization.CTorus S.d S.L F.N₁ m₁ K} :
    x ∈ d7Pull F j Y ↔ cubeMap n S.L M K j (castT F.side x) ∈ Y := Iff.rfl

@[simp] theorem d7Pull_univ (F : FineSizeFrame S n M K m₀ m₁) (j : ℕ) :
    d7Pull F j (Set.univ : Set (Torus S.d (n j))) = Set.univ :=
  Set.eq_univ_of_forall fun _ => Set.mem_univ _

@[simp] theorem d7Pull_empty (F : FineSizeFrame S n M K m₀ m₁) (j : ℕ) :
    d7Pull F j (∅ : Set (Torus S.d (n j))) = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h => h

theorem d7Pull_mono (F : FineSizeFrame S n M K m₀ m₁) (j : ℕ) {Y Y' : Set (Torus S.d (n j))}
    (h : Y ⊆ Y') : d7Pull F j Y ⊆ d7Pull F j Y' := fun _ hx => h hx

theorem d7Pull_inter (F : FineSizeFrame S n M K m₀ m₁) (j : ℕ) (Y Y' : Set (Torus S.d (n j))) :
    d7Pull F j (Y ∩ Y') = d7Pull F j Y ∩ d7Pull F j Y' := rfl

theorem d7Pull_compl (F : FineSizeFrame S n M K m₀ m₁) (j : ℕ) (Y : Set (Torus S.d (n j))) :
    d7Pull F j Yᶜ = (d7Pull F j Y)ᶜ := rfl

end Frame

/-! ### The size and the valid labels -/

section Size

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M m₀ m₁ : ℕ}

/-- **The size of a boundary domain after `R`, in `[0, ∞]`**: the fine chosen-cover modular size
`d^cov_k(X_f mod Ω_f^c)` (`Fluctuation.dcovModE`, FLUCTUATION Definition 1.1) of the fine set `X_f`
of `X` modulo the complement of the fine set `Ω_f` of the post-`R` region `Ω_k^post(𝔸)`
(`RegionHistory.omegaPost`).  `⊤` when `X_f` has no admissible cover and structure.  This is not
the functional of P5 (1.34); see the module docstring. -/
noncomputable def d7SizeE (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (X : Finset (Torus S.d (n k))) : ENNReal :=
  Fluctuation.dcovModE m₀ k (d7Pull F k (A.H.omegaPost k))
    (d7Pull F k (X : Set (Torus S.d (n k))))

/-- **The size of a boundary domain after `R`**: the real value of `d7SizeE` (`0` when
`d7SizeE = ⊤`; the bound of (D7) is stated only for `FineValid` domains). -/
noncomputable def d7Size (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (X : Finset (Torus S.d (n k))) : ℝ :=
  (d7SizeE F A k X).toReal

/-- **The valid labels of the boundary terms after `R`**: the fine set of `X` belongs to
`𝒟_k(mod Ω_f^c)` in the sense of the fluctuation step (`Fluctuation.DjMod`) and its size is
finite. -/
def FineValid (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (X : Finset (Torus S.d (n k))) : Prop :=
  Fluctuation.DjMod m₀ k (d7Pull F k (A.H.omegaPost k)) (d7Pull F k (X : Set (Torus S.d (n k)))) ∧
    d7SizeE F A k X ≠ ⊤

open Classical in
/-- **The boundary domains of the post-`R` class**: the domains `X ∈ 𝒟_k(mod (Ω_k^post)^c)`
meeting `Z` and its complement (`bdryDoms` at the post-`R` region) that are `FineValid`. -/
noncomputable def bdryDomsPost (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (Z : Set (Torus S.d (n k))) : Finset (Finset (Torus S.d (n k))) :=
  (bdryDoms (A.H.omegaPost k) Z).filter (FineValid F A k)

theorem mem_bdryDomsPost {F : FineSizeFrame S n M K m₀ m₁} {A : LabHist S n R k0 K} {k : ℕ}
    {Z : Set (Torus S.d (n k))} {X : Finset (Torus S.d (n k))} :
    X ∈ bdryDomsPost F A k Z ↔ X ∈ bdryDoms (A.H.omegaPost k) Z ∧ FineValid F A k X := by
  classical
  simp [bdryDomsPost]

theorem d7Size_nonneg (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (X : Finset (Torus S.d (n k))) : 0 ≤ d7Size F A k X :=
  ENNReal.toReal_nonneg

theorem d7SizeE_ne_top_of_mem {F : FineSizeFrame S n M K m₀ m₁} {A : LabHist S n R k0 K} {k : ℕ}
    {Z : Set (Torus S.d (n k))} {X : Finset (Torus S.d (n k))} (h : X ∈ bdryDomsPost F A k Z) :
    d7SizeE F A k X ≠ ⊤ :=
  (mem_bdryDomsPost.1 h).2.2

/-- The size is finite when the fine set of `X` belongs to `𝒟_k` (a nonempty nearest-neighbour
connected union of `π'_k`-cubes). -/
theorem d7SizeE_ne_top_of_isDj [NeZero S.L] (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) {k : ℕ} {X : Finset (Torus S.d (n k))}
    (h : Fluctuation.IsDj m₀ k (d7Pull F k (X : Set (Torus S.d (n k))))) :
    d7SizeE F A k X ≠ ⊤ :=
  Fluctuation.dcovModE_ne_top_of_IsDj h

/-- A domain whose fine set belongs to `𝒟_k(mod Ω_f^c)` is a valid label: the finiteness of the
size follows. -/
theorem fineValid_of_djMod [NeZero S.L] (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) {k : ℕ} {X : Finset (Torus S.d (n k))}
    (h : Fluctuation.DjMod m₀ k (d7Pull F k (A.H.omegaPost k))
      (d7Pull F k (X : Set (Torus S.d (n k))))) : FineValid F A k X :=
  ⟨h, d7SizeE_ne_top_of_isDj F A h.1⟩

end Size

/-! ### Boundary domains at the raw and at the post-`R` region -/

section Labels

variable {d n : ℕ}

/-- `𝒟_k(mod Ω^c)` is monotone in `Ω`: a component of the smaller complement lies in a component
of the larger one. -/
theorem dmodOmega_mono {Om Om' : Set (Torus d n)} (h : Om ⊆ Om') {X : Finset (Torus d n)}
    (hX : DmodOmega Om X) : DmodOmega Om' X := by
  refine ⟨hX.1, fun a ha => ?_⟩
  have ha' : a ∈ Omᶜ := fun h' => ha (h h')
  have hsub : nnComp Om'ᶜ a ⊆ nnComp Omᶜ a := nnComp_mono (Set.compl_subset_compl.2 h) a
  rcases hX.2 a ha' with h1 | h1
  · exact Or.inl (hsub.trans h1)
  · exact Or.inr (Set.disjoint_of_subset_left hsub h1)

/-- The boundary domains are monotone in the region `Ω`. -/
theorem bdryDoms_mono [NeZero n] {Om Om' : Set (Torus d n)} (h : Om ⊆ Om') (Z : Set (Torus d n)) :
    bdryDoms Om Z ⊆ bdryDoms Om' Z := by
  intro X hX
  rw [mem_bdryDoms] at hX ⊢
  exact ⟨dmodOmega_mono h hX.1, hX.2⟩

end Labels

/-- **A boundary domain at the raw region `Ω_k^pre` is a boundary domain at the post-`R` region
`Ω_k^post ⊇ Ω_k^pre`.**  (The converse fails when a removed component is cut by `X`.) -/
theorem bdryDoms_OmegaCube_subset_omegaPost {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    {R : ℕ → ℝ} {k0 K : ℕ} (H : RegionHistory S n R k0 K) (k : ℕ) (Z : Set (Torus S.d (n k))) :
    bdryDoms (OmegaCube H k) Z ⊆ bdryDoms (H.omegaPost k) Z :=
  bdryDoms_mono (H.OmegaCube_subset_omegaPost k) Z

end Balaban.LargeField.Def7
