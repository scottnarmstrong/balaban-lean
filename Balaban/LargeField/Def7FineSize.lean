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
# The size of the boundary terms of Def-7: the fine chosen-cover modular size

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

The size in the bounds of (D7) — of the pre-`R` records `D7Bdry`, `D7Bdry2` and of the post-`R`
records `D7BdryPost`, `D7Bdry2Post` — is **not** the papers' functional.  It is the fine
chosen-cover modular size `Fluctuation.dcovModE` of the fluctuation step (FLUCTUATION
Definition 1.1), the size in which the fluctuation step bounds its output and for which the
entropy bound `Fluctuation.G2_X` and the cell count `Fluctuation.cellCount_le_of_admissible` are
proved:

* the carrier is the set of sites of the fine torus `CTorus d L N₁ m₁ K`, identified with the fine
  torus `𝕋_{M n_K L^K}` of the history by the side equality of a `FineSizeFrame` (`castT`);
* the `π_k`-cubes are the aligned cells of `L^{k + m₀ + m₁} = M L^k` sites per side (the fine sets
  of the cubes of `𝕋_k`, by `FineSizeFrame.hM`), the `π'_k`-cubes the aligned boxes of `L` cells
  per side;
* `d7SizeAtE F k Ω X = Fluctuation.dcovModE m₀ k Ω_f X_f`, for a region `Ω ⊆ 𝕋_k` and a set `X` of
  cubes of `𝕋_k` with fine sets `Ω_f`, `X_f` (`d7Pull`), is the infimum of `|E| / (M L^k)` over the
  sets `𝒦` of `π'_k`-cubes contained in `X_f` whose union contains `X_f ∩ Ω_f` (a *chosen* cover)
  and the nearest-neighbour connected structures `(W, E)` of sites of `X_f` meeting every cube of
  `𝒦`; its value is `⊤` when there is no such pair;
* the post-`R` records use the post-`R` region `Ω_k^post(𝔸)` (`RegionHistory.omegaPost`,
  Definition I.3.11): `d7SizeE`, `d7Size`, `FineValid`, `bdryDomsPost`; the pre-`R` records use
  the raw region `Ω_k^pre(𝔸)` (`OmegaCube`; the pre-`R` class has no `R`-record at scale `k`):
  `d7SizePreE`, `d7SizePre`, `FineValidPre`, `bdryDomsPre`.  Both are instances of the definitions
  at a region `d7SizeAtE`, `d7SizeAt`, `FineValidAt`, `bdryDomsAt`.

`d7SizeAt` is the real value; `(⊤ : ENNReal).toReal = 0`, so a bound stated with it is only
meaningful where `d7SizeAtE ≠ ⊤`.  `FineValidAt` is the condition under which the bounds of (D7)
are stated: `X_f ∈ 𝒟_k(mod Ω_f^c)` in the sense of the fluctuation step (`Fluctuation.DjMod`: a
nonempty nearest-neighbour connected union of `π'_k`-cubes containing or missing every
nearest-neighbour component of `Ω_f^c`) and `d7SizeAtE ≠ ⊤` (the second follows from the first,
`fineValidAt_iff`).  `bdryDomsAt F k Ω Z` is the set of the boundary domains of a record: the
domains `X ∈ 𝒟_k(mod Ω^c)` at cube level (`bdryDoms`) meeting `Z` and its complement that are
valid.  Each record has a clause `support`: the boundary terms vanish at the cube-level boundary
domains that are not valid (the papers index the boundary terms by `𝒟_k(mod Ω^c_k)`; the
cube-level `bdryDoms` contains sets that are not unions of `π'_k`-cubes).

The cube-level size `dCovMod` of `Def7Hist` (continuous segments through closed cubes) is no
longer used by any class clause.  For two blocks of cubes meeting at a corner it is `0` while the
fine size is `⊤` (`corner_dCovMod_zero_fine_top` in `Inhabited/D7FineSizeWitness`;
`notes/phase1/VMOD-25.md` §2): the bound in the fine size given by the fluctuation step cannot be
recovered from a bound in `dCovMod`.

## The relation between the pre-`R` and the post-`R` record

`Ω_k^pre ⊆ Ω_k^post` (`RegionHistory.OmegaCube_subset_omegaPost`) and `Z_k ⊆ Z^pre_k`
(`RegionHistory.Z_subset_Zpre`).  The following are proved here.

* *Labels.*  `𝒟_k(mod Ω^c)` is nondecreasing in `Ω`, at cube level (`dmodOmega_mono`) and for the
  fine sets (`djMod_mono_region`).  Hence a valid label before `R` is a valid label after `R`
  (`fineValid_of_fineValidPre`), `bdryDomsPre F 𝔸 k Z ⊆ bdryDomsPost F 𝔸 k Z` for the same `Z`
  (`bdryDomsPre_subset_bdryDomsPost`), and a boundary domain of `IsRep^pre_k` (region `Z^pre_k`)
  that meets `Z_k` is a boundary domain of `IsRep_k` (`mem_bdryDomsPost_of_mem_bdryDomsPre`).  The
  converse inclusions do not follow from the definitions: a domain of `𝒟_k(mod (Ω_k^post)^c)` may
  contain a part of a removed component and miss the rest, and a boundary domain before `R` that
  meets only removed components is not one after `R`.
* *Sizes.*  The fine size is nondecreasing in `Ω` (`dcovModE_mono_region`: a cover of `X ∩ Ω'`
  covers `X ∩ Ω` for `Ω ⊆ Ω'`; no such lemma was landed in `Fluctuation/SizeMod*`).  Hence
  `d7SizePreE ≤ d7SizeE` (`d7SizePreE_le_d7SizeE`), `d7SizePre ≤ d7Size` where the latter is
  finite (`d7SizePre_le_d7Size`), and `fac · e^{-rate · d7Size} ≤ fac · e^{-rate · d7SizePre}`
  for `fac, rate ≥ 0` (`exp_d7Size_le_exp_d7SizePre`).
* *Consequence.*  The post-`R` bound is the stronger one: a bound in the post-`R` size implies
  the bound in the pre-`R` size with the same constants, and not conversely.  The pre-`R` bound
  does **not** give the post-`R` bound by a comparison of sizes; the decay in the additional
  length (the cover of the part of `X` over the removed components, which belong to `Ω_k^post`
  and not to `Ω_k^pre`) is an obligation of the operation `R`, as are the vanishing `support`
  after `R` and the terms at the new labels.  Nothing about `R` is proved here.
* *No removal.*  When `Rem_k = ∅` the regions, sizes, valid labels and boundary domains coincide
  (`d7SizeE_eq_d7SizePreE_of_rem_empty`, `fineValid_iff_fineValidPre_of_rem_empty`,
  `bdryDomsPost_eq_bdryDomsPre_of_rem_empty`), and the two records are equivalent
  (`d7Bdry_iff_d7BdryPost_of_rem_empty` in `Def7`).

## Differences from the papers, and what is not proved

The landed size differs from P5 (1.34) in three ways: a nearest-neighbour structure of sites
replaces a continuous tree; a chosen subfamily of cover cubes replaces all cover cubes meeting
`X ∩ Ω`; half-open cells replace open cubes, and the components of `Ω^c` are nearest-neighbour
components of sites.  **The following items are open: none of them is proved in this
development** (the labels are those of `notes/phase1/VMOD-27.md` §3 and `VMOD-28.md` §3; facts
that are proved are cited by their declaration names).

* **Comparison with the papers' size** (`OPEN-PAPER-FINE-REALIZATION`,
  `notes/phase1/VMOD-27.md` §3).  For every admissible post-`R` history `𝔸`, scale `k` and
  boundary domain `X ∈ 𝒟_k(mod (Ω_k^post)^c)`, with `Ω_f`, `X_f` as above and
  `d7SizeE F 𝔸 k X ≠ ⊤`: `X_f ∈ Fluctuation.DjMod m₀ k Ω_f`, and there are constants `a > 0`,
  `b ≥ 0` depending only on `d`, `L` such that
  `d_k^{P5}(X mod (Ω_k^post)^c) ≥ a · d7Size F 𝔸 k X - b`, where `d_k^{P5}` is the functional of
  P5 (1.34) on the open domain.  A sufficient statement: every continuous tree in the open domain
  meeting every eligible open cover cube gives a nearest-neighbour tree of sites in `X_f` meeting
  every corresponding box, of length at most `A |Γ| / M + B` (`notes/phase1/VMOD-27.md` §3).  The
  same for the pre-`R` size at the raw region.
* **Constants** (`OPEN-D7-CONSTANT-REBASE`).  Such a comparison turns the papers' bound
  `B₀ e^{-κ d_k}` into `B₀ e^{κ b} e^{-κ a · d7Size}`, not into a bound with the same `B₀`, `κ`;
  the clauses `bound` are stated with the constants `fac`, `rate` of the class.
* **Identification of the two notions of component** of `Ω^c` (`OPEN-MOD-COMPONENT-COMPAT`:
  continuum components of the closed complement in the papers, nearest-neighbour components of
  cubes in `DmodOmega`, of sites in `Fluctuation.DjMod`), and of the open domains of the papers
  with the fine sets (`OPEN-ALIGNED-LIFT-IDENTIFICATION`).
* **Support of the boundary terms on the valid labels** (`OPEN-D7-BOUNDARY-LABEL-SUPPORT`).  The
  fields `support` of the four records require `ℬ^{(k)}(X, 𝔸) = 0` at the cube-level boundary
  domains that are not valid.  **No producer of this clause is landed.**  On the fluctuation side
  it should come from the landed vanishing of the marked activities at cube sets of infinite
  modular cost, `Fluctuation.Gst_eq_zero_of_dOmega_top` (`Polymer/MarkedCubesVanish.lean`:
  `G^*(Y₀, S) = 0` when `d_Ω(S) = +∞`; `notes/phase1/ROOT.md` §2): the active marked cube sets
  have finite modular cost.  The deduction of `support` for the boundary terms of the pre-`R`
  class from it is not formalized, nor is its preservation by `R`.
* **Reindexing of (D1)** (`OPEN-D7-POST-REINDEX`).  The form clauses (D1) (`Rep.bdrySum`) sum over
  the boundary domains `bdryDoms` at the raw region `OmegaCube`, for the pre-`R` and for the
  post-`R` class.  For the pre-`R` class this sum is the sum over `bdryDomsPre`
  (`D7Bdry.bdrySum_eq`).  For the post-`R` class every such domain is a boundary domain at
  `Ω_k^post` (`bdryDoms_OmegaCube_subset_omegaPost`), and under `support` the terms that are not
  `FineValid` vanish (`D7BdryPost.mem_or_eq_zero`, `D7BdryPost.bdrySum_eq` in `Def7`), so every
  term of (D1) is either zero or bounded with the fine size; the sum over all of `bdryDomsPost`
  (which may contain domains that are not boundary domains at the raw region) is not what (D1)
  states.
* **The H7 domain** (`OPEN-D7-H7-POST-TRANSPORT`).  The analyticity domain of the boundary terms
  (`H7Domain` at `globalLH`) and the regions inside `loc_hist` are the raw regions `OmegaCube` in
  all four records; their form after `R` has not been examined.

A boundary domain with finite fine size at a history with a large-field region, and inhabitants
of `D7Bdry` and `D7BdryPost` with a nonzero boundary term, are in `Inhabited/D7FineSizeWitness`
(`d7SizeE_ne_top_at_boundary_domain`, `d7SizePreE_ne_top_at_boundary_domain`,
`exists_d7BdryPost_nonzero`, `exists_d7Bdry_nonzero`).

## Contents

* `FineSizeFrame`, `fineFrame`: the typing data identifying the two fine tori, and the frame
  `N₁ = L^{m₀} n_K` of a torus with `M = L^{m₀ + m₁}`.
* `d7Pull`: the fine set, on `CTorus d L N₁ m₁ K`, of a set of cubes of `𝕋_j`.
* `dcovModE_mono_region`, `djMod_mono_region`: monotonicity in the region.
* `d7SizeAtE`, `d7SizeAt`, `FineValidAt`, `bdryDomsAt`: the size and the valid labels at a region;
  `d7SizeE`, `d7Size`, `FineValid`, `bdryDomsPost` (post-`R` region) and `d7SizePreE`, `d7SizePre`,
  `FineValidPre`, `bdryDomsPre` (raw region).
* `bdryDoms_mono`, `bdryDoms_OmegaCube_subset_omegaPost`, `bdryDomsAt_mono`: boundary domains and
  the region.
* The relation between the two records: see above.
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

/-! ### Monotonicity of the fine modular size and of `𝒟_j(mod Ω^c)` in the region -/

section Mono

variable {d L N₁ m₁ K m₀ j : ℕ}

/-- **The fine modular size is nondecreasing in `Ω`**: for `Ω ⊆ Ω'` a cover of `X ∩ Ω'` covers
`X ∩ Ω`, so the infimum defining `d^cov_j(X mod Ω^c)` is over a larger set of pairs. -/
theorem dcovModE_mono_region {Ω Ω' X : Set (Localization.CTorus d L N₁ m₁ K)} (h : Ω ⊆ Ω') :
    Fluctuation.dcovModE m₀ j Ω X ≤ Fluctuation.dcovModE m₀ j Ω' X := by
  refine le_iInf fun 𝒦 => le_iInf fun W => le_iInf fun E => le_iInf fun hE => ?_
  exact Fluctuation.dcovModE_le_of_admissible
    ⟨hE.1, (Set.inter_subset_inter_right X h).trans hE.2.1, hE.2.2⟩

/-- For `Ω ⊆ Ω'` the component of a site in `Ω'^c` is contained in its component in `Ω^c`. -/
theorem omegaComp_anti_region {Ω Ω' : Set (Localization.CTorus d L N₁ m₁ K)} (h : Ω ⊆ Ω')
    (z : Localization.CTorus d L N₁ m₁ K) :
    Fluctuation.OmegaComp Ω' z ⊆ Fluctuation.OmegaComp Ω z := by
  rintro y ⟨hy, hzy⟩
  exact ⟨fun hy' => hy (h hy'), Relation.ReflTransGen.mono
    (fun _ _ huv => ⟨fun hu => huv.1 (h hu), fun hv => huv.2.1 (h hv), huv.2.2⟩) z y hzy⟩

/-- **`𝒟_j(mod Ω^c)` is nondecreasing in `Ω`**: a polymer containing or missing every component
of `Ω^c` contains or misses every component of the smaller set `Ω'^c`. -/
theorem djMod_mono_region {Ω Ω' X : Set (Localization.CTorus d L N₁ m₁ K)} (h : Ω ⊆ Ω')
    (hX : Fluctuation.DjMod m₀ j Ω X) : Fluctuation.DjMod m₀ j Ω' X := by
  refine ⟨hX.1, fun z hz => ?_⟩
  have hz' : z ∈ Ωᶜ := fun h' => hz (h h')
  rcases hX.2 z hz' with h1 | h1
  · exact Or.inl ((omegaComp_anti_region h z).trans h1)
  · exact Or.inr (Set.disjoint_of_subset_left (omegaComp_anti_region h z) h1)

end Mono

/-! ### The size and the valid labels at a region -/

section Region

variable {S : Setting} {n : ℕ → ℕ} {M K m₀ m₁ : ℕ}

/-- **The fine size of a set `X` of cubes of `𝕋_k` modulo the complement of a region `Ω ⊆ 𝕋_k`,
in `[0, ∞]`**: the fine chosen-cover modular size `d^cov_k(X_f mod Ω_f^c)`
(`Fluctuation.dcovModE`, FLUCTUATION Definition 1.1) of the fine sets `X_f`, `Ω_f` (`d7Pull`) of
`X` and `Ω`.  `⊤` when `X_f` has no admissible cover and structure.  This is not the functional of
P5 (1.34); see the module docstring.  The sizes of the two records of (D7) are its values at the
post-`R` region (`d7SizeE`) and at the raw region (`d7SizePreE`). -/
noncomputable def d7SizeAtE (F : FineSizeFrame S n M K m₀ m₁) (k : ℕ) (Om : Set (Torus S.d (n k)))
    (X : Finset (Torus S.d (n k))) : ENNReal :=
  Fluctuation.dcovModE m₀ k (d7Pull F k Om) (d7Pull F k (X : Set (Torus S.d (n k))))

/-- The real value of `d7SizeAtE` (`0` when `d7SizeAtE = ⊤`; the bounds of (D7) are stated only
for the domains with `FineValidAt`). -/
noncomputable def d7SizeAt (F : FineSizeFrame S n M K m₀ m₁) (k : ℕ) (Om : Set (Torus S.d (n k)))
    (X : Finset (Torus S.d (n k))) : ℝ :=
  (d7SizeAtE F k Om X).toReal

/-- **The valid labels at a region `Ω`**: the fine set of `X` belongs to `𝒟_k(mod Ω_f^c)` in the
sense of the fluctuation step (`Fluctuation.DjMod`) and its size is finite.  (The second clause
follows from the first, `fineValidAt_iff`.) -/
def FineValidAt (F : FineSizeFrame S n M K m₀ m₁) (k : ℕ) (Om : Set (Torus S.d (n k)))
    (X : Finset (Torus S.d (n k))) : Prop :=
  Fluctuation.DjMod m₀ k (d7Pull F k Om) (d7Pull F k (X : Set (Torus S.d (n k)))) ∧
    d7SizeAtE F k Om X ≠ ⊤

open Classical in
/-- **The boundary domains at a region `Ω` with valid fine set**: the domains
`X ∈ 𝒟_k(mod Ω^c)` at cube level meeting `Z` and its complement (`bdryDoms`) that satisfy
`FineValidAt`. -/
noncomputable def bdryDomsAt [∀ k, NeZero (n k)] (F : FineSizeFrame S n M K m₀ m₁) (k : ℕ)
    (Om Z : Set (Torus S.d (n k))) : Finset (Finset (Torus S.d (n k))) :=
  (bdryDoms Om Z).filter (FineValidAt F k Om)

variable {F : FineSizeFrame S n M K m₀ m₁} {k : ℕ} {Om Om' Z : Set (Torus S.d (n k))}
  {X : Finset (Torus S.d (n k))}

theorem mem_bdryDomsAt [∀ k, NeZero (n k)] :
    X ∈ bdryDomsAt F k Om Z ↔ X ∈ bdryDoms Om Z ∧ FineValidAt F k Om X := by
  classical
  simp [bdryDomsAt]

theorem d7SizeAt_nonneg (F : FineSizeFrame S n M K m₀ m₁) (k : ℕ) (Om : Set (Torus S.d (n k)))
    (X : Finset (Torus S.d (n k))) : 0 ≤ d7SizeAt F k Om X :=
  ENNReal.toReal_nonneg

/-- The size is finite when the fine set of `X` belongs to `𝒟_k` (a nonempty nearest-neighbour
connected union of `π'_k`-cubes), for every region. -/
theorem d7SizeAtE_ne_top_of_isDj [NeZero S.L]
    (h : Fluctuation.IsDj m₀ k (d7Pull F k (X : Set (Torus S.d (n k))))) :
    d7SizeAtE F k Om X ≠ ⊤ :=
  Fluctuation.dcovModE_ne_top_of_IsDj h

/-- A domain whose fine set belongs to `𝒟_k(mod Ω_f^c)` is a valid label: the finiteness of the
size follows. -/
theorem fineValidAt_of_djMod [NeZero S.L]
    (h : Fluctuation.DjMod m₀ k (d7Pull F k Om) (d7Pull F k (X : Set (Torus S.d (n k))))) :
    FineValidAt F k Om X :=
  ⟨h, d7SizeAtE_ne_top_of_isDj h.1⟩

theorem fineValidAt_iff [NeZero S.L] :
    FineValidAt F k Om X ↔
      Fluctuation.DjMod m₀ k (d7Pull F k Om) (d7Pull F k (X : Set (Torus S.d (n k)))) :=
  ⟨fun h => h.1, fineValidAt_of_djMod⟩

/-- **The fine size is nondecreasing in the region.** -/
theorem d7SizeAtE_mono (h : Om ⊆ Om') (X : Finset (Torus S.d (n k))) :
    d7SizeAtE F k Om X ≤ d7SizeAtE F k Om' X :=
  dcovModE_mono_region (d7Pull_mono F k h)

theorem d7SizeAt_mono (h : Om ⊆ Om') (hfin : d7SizeAtE F k Om' X ≠ ⊤) :
    d7SizeAt F k Om X ≤ d7SizeAt F k Om' X :=
  ENNReal.toReal_mono hfin (d7SizeAtE_mono h X)

/-- **The valid labels are nondecreasing in the region.** -/
theorem fineValidAt_mono [NeZero S.L] (h : Om ⊆ Om') (hX : FineValidAt F k Om X) :
    FineValidAt F k Om' X :=
  fineValidAt_of_djMod (djMod_mono_region (d7Pull_mono F k h) hX.1)

end Region

/-! ### Boundary domains at cube level: monotonicity in the region -/

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
`Ω_k^post ⊇ Ω_k^pre`.**  (The converse does not follow: a domain may contain a part of a removed
component and miss the rest.) -/
theorem bdryDoms_OmegaCube_subset_omegaPost {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    {R : ℕ → ℝ} {k0 K : ℕ} (H : RegionHistory S n R k0 K) (k : ℕ) (Z : Set (Torus S.d (n k))) :
    bdryDoms (OmegaCube H k) Z ⊆ bdryDoms (H.omegaPost k) Z :=
  bdryDoms_mono (H.OmegaCube_subset_omegaPost k) Z

/-- The valid boundary domains are nondecreasing in the region. -/
theorem bdryDomsAt_mono {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K m₀ m₁ : ℕ}
    [NeZero S.L] (F : FineSizeFrame S n M K m₀ m₁) (k : ℕ) {Om Om' : Set (Torus S.d (n k))}
    (h : Om ⊆ Om') (Z : Set (Torus S.d (n k))) : bdryDomsAt F k Om Z ⊆ bdryDomsAt F k Om' Z := by
  intro X hX
  rw [mem_bdryDomsAt] at hX ⊢
  exact ⟨bdryDoms_mono h Z hX.1, fineValidAt_mono h hX.2⟩

/-! ### The two instances: the post-`R` region and the raw region -/

section PrePost

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M m₀ m₁ : ℕ}

/-- **The size of a boundary domain after `R`, in `[0, ∞]`**: the fine chosen-cover modular size
`d^cov_k(X_f mod Ω_f^c)` of the fine set `X_f` of `X` modulo the complement of the fine set `Ω_f`
of the post-`R` region `Ω_k^post(𝔸)` (`RegionHistory.omegaPost`); `d7SizeAtE` at that region.
This is not the functional of P5 (1.34); see the module docstring. -/
noncomputable def d7SizeE (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (X : Finset (Torus S.d (n k))) : ENNReal :=
  d7SizeAtE F k (A.H.omegaPost k) X

/-- **The size of a boundary domain after `R`**: the real value of `d7SizeE` (`0` when
`d7SizeE = ⊤`; the bound of (D7) is stated only for `FineValid` domains). -/
noncomputable def d7Size (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (X : Finset (Torus S.d (n k))) : ℝ :=
  d7SizeAt F k (A.H.omegaPost k) X

/-- **The valid labels of the boundary terms after `R`**: `FineValidAt` at the post-`R` region. -/
def FineValid (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (X : Finset (Torus S.d (n k))) : Prop :=
  FineValidAt F k (A.H.omegaPost k) X

/-- **The boundary domains of the post-`R` class**: the domains `X ∈ 𝒟_k(mod (Ω_k^post)^c)`
meeting `Z` and its complement (`bdryDoms` at the post-`R` region) that are `FineValid`. -/
noncomputable def bdryDomsPost (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (Z : Set (Torus S.d (n k))) : Finset (Finset (Torus S.d (n k))) :=
  bdryDomsAt F k (A.H.omegaPost k) Z

/-- **The size of a boundary domain before `R`, in `[0, ∞]`**: the fine chosen-cover modular size
of the fine set of `X` modulo the complement of the fine set of the raw region `Ω_k^pre(𝔸)`
(`OmegaCube`); `d7SizeAtE` at that region. -/
noncomputable def d7SizePreE (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (X : Finset (Torus S.d (n k))) : ENNReal :=
  d7SizeAtE F k (OmegaCube A.H k) X

/-- **The size of a boundary domain before `R`**: the real value of `d7SizePreE`. -/
noncomputable def d7SizePre (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (X : Finset (Torus S.d (n k))) : ℝ :=
  d7SizeAt F k (OmegaCube A.H k) X

/-- **The valid labels of the boundary terms before `R`**: `FineValidAt` at the raw region. -/
def FineValidPre (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (X : Finset (Torus S.d (n k))) : Prop :=
  FineValidAt F k (OmegaCube A.H k) X

/-- **The boundary domains of the pre-`R` class**: the domains `X ∈ 𝒟_k(mod (Ω_k^pre)^c)` meeting
`Z` and its complement (`bdryDoms` at the raw region) that are `FineValidPre`. -/
noncomputable def bdryDomsPre (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (Z : Set (Torus S.d (n k))) : Finset (Finset (Torus S.d (n k))) :=
  bdryDomsAt F k (OmegaCube A.H k) Z

variable {F : FineSizeFrame S n M K m₀ m₁} {A : LabHist S n R k0 K} {k : ℕ}
  {Z : Set (Torus S.d (n k))} {X : Finset (Torus S.d (n k))}

/-- The size after `R` in terms of the size of the fluctuation step. -/
theorem d7Size_eq (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (X : Finset (Torus S.d (n k))) :
    d7Size F A k X = (Fluctuation.dcovModE m₀ k (d7Pull F k (A.H.omegaPost k))
      (d7Pull F k (X : Set (Torus S.d (n k))))).toReal := rfl

/-- The size before `R` in terms of the size of the fluctuation step. -/
theorem d7SizePre_eq (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (X : Finset (Torus S.d (n k))) :
    d7SizePre F A k X = (Fluctuation.dcovModE m₀ k (d7Pull F k (OmegaCube A.H k))
      (d7Pull F k (X : Set (Torus S.d (n k))))).toReal := rfl

theorem mem_bdryDomsPost :
    X ∈ bdryDomsPost F A k Z ↔ X ∈ bdryDoms (A.H.omegaPost k) Z ∧ FineValid F A k X :=
  mem_bdryDomsAt

theorem mem_bdryDomsPre :
    X ∈ bdryDomsPre F A k Z ↔ X ∈ bdryDoms (OmegaCube A.H k) Z ∧ FineValidPre F A k X :=
  mem_bdryDomsAt

theorem d7Size_nonneg (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (X : Finset (Torus S.d (n k))) : 0 ≤ d7Size F A k X :=
  ENNReal.toReal_nonneg

theorem d7SizePre_nonneg (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (X : Finset (Torus S.d (n k))) : 0 ≤ d7SizePre F A k X :=
  ENNReal.toReal_nonneg

theorem d7SizeE_ne_top_of_mem (h : X ∈ bdryDomsPost F A k Z) : d7SizeE F A k X ≠ ⊤ :=
  (mem_bdryDomsPost.1 h).2.2

theorem d7SizePreE_ne_top_of_mem (h : X ∈ bdryDomsPre F A k Z) : d7SizePreE F A k X ≠ ⊤ :=
  (mem_bdryDomsPre.1 h).2.2

/-- The size is finite when the fine set of `X` belongs to `𝒟_k` (a nonempty nearest-neighbour
connected union of `π'_k`-cubes). -/
theorem d7SizeE_ne_top_of_isDj [NeZero S.L] (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) {k : ℕ} {X : Finset (Torus S.d (n k))}
    (h : Fluctuation.IsDj m₀ k (d7Pull F k (X : Set (Torus S.d (n k))))) :
    d7SizeE F A k X ≠ ⊤ :=
  d7SizeAtE_ne_top_of_isDj h

/-- A domain whose fine set belongs to `𝒟_k(mod Ω_f^c)` is a valid label: the finiteness of the
size follows. -/
theorem fineValid_of_djMod [NeZero S.L] (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) {k : ℕ} {X : Finset (Torus S.d (n k))}
    (h : Fluctuation.DjMod m₀ k (d7Pull F k (A.H.omegaPost k))
      (d7Pull F k (X : Set (Torus S.d (n k))))) : FineValid F A k X :=
  fineValidAt_of_djMod h

/-- The pre-`R` form of `fineValid_of_djMod`. -/
theorem fineValidPre_of_djMod [NeZero S.L] (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) {k : ℕ} {X : Finset (Torus S.d (n k))}
    (h : Fluctuation.DjMod m₀ k (d7Pull F k (OmegaCube A.H k))
      (d7Pull F k (X : Set (Torus S.d (n k))))) : FineValidPre F A k X :=
  fineValidAt_of_djMod h

/-! ### The relation between the pre-`R` and the post-`R` labels and sizes

`Ω_k^pre ⊆ Ω_k^post` (`RegionHistory.OmegaCube_subset_omegaPost`).  Hence: a valid label before
`R` is a valid label after `R`; the size before `R` is at most the size after `R`; a bound
`fac · e^{-rate · d7Size}` after `R` is at most the bound `fac · e^{-rate · d7SizePre}` before `R`
with the same constants.  The post-`R` bound is therefore the stronger statement: it does not
follow from the pre-`R` bound by a comparison of sizes, and the decay in the additional length
(the part of the cover of `X ∩ Ω_k^post` over the removed components) is an obligation of the
operation `R`.  When no component is removed at scale `k` the two regions, sizes and label sets
coincide. -/

/-- **A valid label before `R` is a valid label after `R`.**  (The converse does not follow: the
fine set of `X` may contain a part of a removed component and miss the rest.) -/
theorem fineValid_of_fineValidPre [NeZero S.L] (h : FineValidPre F A k X) : FineValid F A k X :=
  fineValidAt_mono (A.H.OmegaCube_subset_omegaPost k) h

/-- **The boundary domains of the pre-`R` class are boundary domains of the post-`R` class**, for
the same region `Z`. -/
theorem bdryDomsPre_subset_bdryDomsPost [NeZero S.L] (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) (k : ℕ) (Z : Set (Torus S.d (n k))) :
    bdryDomsPre F A k Z ⊆ bdryDomsPost F A k Z :=
  bdryDomsAt_mono F k (A.H.OmegaCube_subset_omegaPost k) Z

/-- **From the labels of `IsRep^pre_k` to the labels of `IsRep_k`**: a boundary domain of the
pre-`R` class for `Z^pre_k` that still meets `Z_k = Z^pre_k ∖ ⋃ Rem_k` is a boundary domain of the
post-`R` class for `Z_k`.  (A pre-`R` boundary domain that meets only removed components is not
a boundary domain after `R`.) -/
theorem mem_bdryDomsPost_of_mem_bdryDomsPre [NeZero S.L]
    (hX : X ∈ bdryDomsPre F A k (A.H.F.Zpre k))
    (hne : ((X : Set (Torus S.d (n k))) ∩ (A.H.step k).Z).Nonempty) :
    X ∈ bdryDomsPost F A k (A.H.step k).Z := by
  obtain ⟨hb, hv⟩ := mem_bdryDomsPre.1 hX
  obtain ⟨hD, -, x, hxX, hxZ⟩ := mem_bdryDoms.1 hb
  exact mem_bdryDomsPost.2 ⟨mem_bdryDoms.2 ⟨dmodOmega_mono (A.H.OmegaCube_subset_omegaPost k) hD,
    hne, x, hxX, fun h => hxZ (A.H.Z_subset_Zpre k h)⟩, fineValid_of_fineValidPre hv⟩

/-- **The size before `R` is at most the size after `R`**, in `[0, ∞]`. -/
theorem d7SizePreE_le_d7SizeE (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (X : Finset (Torus S.d (n k))) : d7SizePreE F A k X ≤ d7SizeE F A k X :=
  d7SizeAtE_mono (A.H.OmegaCube_subset_omegaPost k) X

/-- The size before `R` is at most the size after `R`, when the latter is finite. -/
theorem d7SizePre_le_d7Size (h : d7SizeE F A k X ≠ ⊤) : d7SizePre F A k X ≤ d7Size F A k X :=
  d7SizeAt_mono (A.H.OmegaCube_subset_omegaPost k) h

/-- **The bound after `R` is the smaller one**: for `fac, rate ≥ 0`, at a label of finite size,
`fac · e^{-rate · d7Size} ≤ fac · e^{-rate · d7SizePre}`.  So a bound in the post-`R` size implies
the bound in the pre-`R` size with the same constants, and not conversely. -/
theorem exp_d7Size_le_exp_d7SizePre {fac rate : ℝ} (hfac : 0 ≤ fac) (hrate : 0 ≤ rate)
    (h : d7SizeE F A k X ≠ ⊤) :
    fac * Real.exp (-rate * d7Size F A k X) ≤ fac * Real.exp (-rate * d7SizePre F A k X) := by
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hfac
  rw [neg_mul, neg_mul]
  exact neg_le_neg (mul_le_mul_of_nonneg_left (d7SizePre_le_d7Size h) hrate)

/-- When no component is removed at scale `k`, the size after `R` is the size before `R`. -/
theorem d7SizeE_eq_d7SizePreE_of_rem_empty (F : FineSizeFrame S n M K m₀ m₁)
    (X : Finset (Torus S.d (n k))) (h : A.H.rem k = ∅) : d7SizeE F A k X = d7SizePreE F A k X := by
  unfold d7SizeE d7SizePreE
  rw [A.H.omegaPost_eq_OmegaCube_of_rem_empty h]

/-- When no component is removed at scale `k`, the real sizes coincide. -/
theorem d7Size_eq_d7SizePre_of_rem_empty (F : FineSizeFrame S n M K m₀ m₁)
    (X : Finset (Torus S.d (n k))) (h : A.H.rem k = ∅) : d7Size F A k X = d7SizePre F A k X := by
  unfold d7Size d7SizePre
  rw [A.H.omegaPost_eq_OmegaCube_of_rem_empty h]

/-- When no component is removed at scale `k`, the valid labels coincide. -/
theorem fineValid_iff_fineValidPre_of_rem_empty (F : FineSizeFrame S n M K m₀ m₁)
    (X : Finset (Torus S.d (n k))) (h : A.H.rem k = ∅) :
    FineValid F A k X ↔ FineValidPre F A k X := by
  unfold FineValid FineValidPre
  rw [A.H.omegaPost_eq_OmegaCube_of_rem_empty h]

/-- When no component is removed at scale `k`, the boundary domains of the two classes coincide
(for the same region `Z`). -/
theorem bdryDomsPost_eq_bdryDomsPre_of_rem_empty (F : FineSizeFrame S n M K m₀ m₁)
    (Z : Set (Torus S.d (n k))) (h : A.H.rem k = ∅) :
    bdryDomsPost F A k Z = bdryDomsPre F A k Z := by
  unfold bdryDomsPost bdryDomsPre
  rw [A.H.omegaPost_eq_OmegaCube_of_rem_empty h]

end PrePost

end Balaban.LargeField.Def7
