/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldH7Loc
public import Balaban.Spine.LFOldResum

/-!
# Reading HS-2: the repairs D1–D3 of the local pair of an old boundary term

The refutation of `H7MixedDatumLoc` (`Spine/LFOldH7Refute.lean`) and the analysis recorded in
`notes/phase1/PLAN-B.md` ("Obstruction (W1154b, 2026-10-21)") found three defects of reading HS-1′
independent of the complex radius of the H7 domain.  This file gives the repaired objects beside the
landed ones (reading HS-2) and restates the two named inputs of OPEN-H7-MIXED with them.

* D3, the datum: `holeStepLoc2` — the step on a region restricted to `𝔹_{k+1}(V)` whose datum is the
  restriction of the global mixed lift (`θ = z ψ_{k+1}` on every block of `Ω_{k+1}`);
  `holeStepLoc2_G'`, `holeStepLoc2_D'_Ψ`, `holeStepLoc2_D'_Ψ_eq` (it is the global datum at the common
  data sites), `holeStepLoc2_D'_Ψ_congr` (it does not read `ψ_k` on `Ω_{k+1}`);
* D2, the local set: `stencilX` (the cubes of `𝕋_k` within `3` cubes of `X`), `locSetXJ2` (the local
  set with the core the `r`-collar of `Ω_{k+1} ∩ X^{∼3}`), `locSetXJ_subset_locSetXJ2`,
  `mem_top_locG'_locSetXJ2` (the sites of `Ω_{k+1}` in the stencil of `X` are unit points of the local
  pair); the cell count `card_cells_stencilCore_le` (`9^d c₁ (1 + d_k(X))`) and
  **`oldResumSite2_holds`**: the resummation at a mark site for these local sets
  (`oldResumSiteAt_holds` with `σ = stencilX`);
* D1, the set `Y_f`: `CubesOfIn` (the cubes of `𝕋_{k+1}` of the sites read lie in `Y_f`; for `Y_f`
  the fine set of a set of cubes this is the inclusion of the sites, `cubesOfIn_fineSet`),
  `subset_of_cubesOfIn`;
* the restated named inputs `H7MixedInnerLoc2`, `H7MixedDatumLoc2` (open; with the cube domains of
  ruling request R14, `Ψ̃^c(ε, ε)`, which exclude the complex rotations that refuted the predecessor
  of the second, `not_mem_deltaC_of_im`), and
  `h7Domain_composedMulti_loc2` (the analogue of `h7Domain_composedMulti_loc`).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background

namespace Balaban.RootFSpine

section HS2

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-! ### D3: the datum of the local pair is the restriction of the global mixed lift -/

/-- **The step on a region restricted to `𝔹_{k+1}(V)` with the restricted global datum** (reading
HS-2, repair D3): the sets of `holeStepLoc`, and the datum the mixed lift of `ψ_k` and
`θ = z ψ_{k+1}` with `θ` on every block of the global top layer `Ω_{k+1}` (not only on the top layer
of the restricted set): at every site of `Ω_{k+1}` the datum is a value of `θ` (`holeStepLocAt` at
`glob = true`). -/
noncomputable abbrev holeStepLoc2 (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N (minSep S.L g.M1) (minSep S.L g.M1) :=
  holeStepLocAt g hnn hM1 true H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V

omit [NeZero M] in
/-- The sets of `holeStepLoc2` are those of `holeStepLoc`. -/
theorem holeStepLoc2_G' (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' =
      (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' := rfl

omit [NeZero M] in
theorem holeStepLoc2_G'_eq (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' = locG' g hnn hM1 H hk hρ V := rfl

omit [NeZero M] in
/-- **The datum of `holeStepLoc2`** at a data site: `θ = z ψ_{k+1}` on the blocks of the global top
layer `Ω_{k+1}`, `ψ_k` elsewhere. -/
theorem holeStepLoc2_D'_Ψ (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {x : Torus S.d ((g.c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))}
    (hx : x ∈ dataSites (locG' g hnn hM1 H hk hρ V)) :
    (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D'.Ψ x =
      mixedLift ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.Ω (k + 1))
        (coverField g hnn hM1 hk ψ k (Nat.le_succ k))
        (coverField g hnn hM1 hk (scaleMulti z ψ) (k + 1) le_rfl) x :=
  liftMixed_Ψ _ ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.blockUnion (k + 1)
    (by omega) le_rfl) (GeneratingSet.inter_Ω_subset_left _ _ (k + 1)) _ _ _ hx

omit [NeZero M] in
/-- **The datum of `holeStepLoc2` is the restriction of the global datum** (`holeStepLF`) at the
common data sites. -/
theorem holeStepLoc2_D'_Ψ_eq (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {x : Torus S.d ((g.c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))}
    (hx : x ∈ dataSites (locG' g hnn hM1 H hk hρ V))
    (hx' : x ∈ dataSites (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G') :
    (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D'.Ψ x =
      (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).D'.Ψ x := by
  rw [holeStepLoc2_D'_Ψ g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V hx]
  exact (liftMixed_Ψ _ ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.blockUnion (k + 1)
    (by omega) le_rfl) subset_rfl _ _ _ hx').symm

omit [NeZero M] in
/-- **The datum of `holeStepLoc2` does not read `ψ_k` on `Ω_{k+1}`** (the variable integrated by the
step): two multiscale fields with the same component `k + 1` and the same component `k` off the
blocks of `Ω_{k+1}` give the same datum. -/
theorem holeStepLoc2_D'_Ψ_congr (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) {ψ ψ' : MultiFieldC S n M K N} (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hsucc : ψ (k + 1) = ψ' (k + 1))
    (hout : ∀ x ∉ (stepG' g hnn hM1 H hk hρ).Ω (k + 1),
      coverField g hnn hM1 hk ψ k (Nat.le_succ k) (jBlock S.d S.L (g.c * n (k + 1) * S.L ^ m₁)
        (k + 1) k x) =
      coverField g hnn hM1 hk ψ' k (Nat.le_succ k) (jBlock S.d S.L (g.c * n (k + 1) * S.L ^ m₁)
        (k + 1) k x))
    {x : Torus S.d ((g.c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))}
    (hx : x ∈ dataSites (locG' g hnn hM1 H hk hρ V)) :
    (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D'.Ψ x =
      (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ' z h₀ a₁ ν β p₁ δ V).D'.Ψ x := by
  rw [holeStepLoc2_D'_Ψ g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V hx,
    holeStepLoc2_D'_Ψ g hnn hM1 H hk hk1 hρ ψ' z h₀ a₁ ν β p₁ δ V hx]
  unfold mixedLift blockLift
  by_cases h : x ∈ (stepG' g hnn hM1 H hk hρ).Ω (k + 1)
  · have h1 : x ∈ (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.Ω (k + 1) := h
    have h2 : x ∈ (holeStepLF g hnn hM1 H hk hk1 hρ ψ' z h₀ a₁ ν β p₁ δ).G'.Ω (k + 1) := h
    simp only [h1, h2, ↓reduceIte, coverField]
    unfold scaleMulti
    rw [hsucc]
  · have h1 : x ∉ (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.Ω (k + 1) := h
    have h2 : x ∉ (holeStepLF g hnn hM1 H hk hk1 hρ ψ' z h₀ a₁ ν β p₁ δ).G'.Ω (k + 1) := h
    simp only [h1, h2, ↓reduceIte]
    exact hout x h

/-! ### D2: the local set covers the stencil of the old label in `Ω_{k+1}` -/

open Classical in
/-- **The stencil of an old label** (repair D2): the cubes of `𝕋_k` within `3` cubes of `X`, the
cubes on which the cube tests of the H7 domain of scale `k` at `X` read the field
(`deltaC_stencil`). -/
noncomputable def stencilX {k : ℕ} (X : Finset (Torus S.d (n k))) : Finset (Torus S.d (n k)) :=
  Finset.univ.filter fun u => u ∈ nbhd 3 (X : Set (Torus S.d (n k)))

omit [NeZero S.L] in
theorem mem_stencilX {k : ℕ} {X : Finset (Torus S.d (n k))} {u : Torus S.d (n k)} :
    u ∈ stencilX X ↔ u ∈ nbhd 3 (X : Set (Torus S.d (n k))) := by
  classical
  simp [stencilX]

omit [NeZero S.L] in
theorem subset_stencilX {k : ℕ} (X : Finset (Torus S.d (n k))) : X ⊆ stencilX X :=
  fun _ hu => mem_stencilX.2 (subset_nbhd 3 _ hu)

omit [NeZero M] [NeZero S.L] in
/-- The fine set of `X` lies in that of its stencil. -/
theorem fineSet_mono_stencil {k : ℕ} {X : Finset (Torus S.d (n k))}
    {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : x ∈ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) :
    x ∈ fineSet (S := S) (n := n) M K k (stencilX X : Set (Torus S.d (n k))) :=
  subset_stencilX X hx

/-- **The local set of reading HS-2** (repair D2): the sites within `r′` of the `r`-collar of the
sites of `Ω_{k+1}` in the stencil of `X` (`Ω_{k+1} ∩ X^{∼3}`) or of a cube of `J`
(`locSetXJ` at the stencil). -/
def locSetXJ2 (H : RegionHistory S n R k0 K) {k : ℕ} (r r' : ℕ) (X : Finset (Torus S.d (n k)))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :=
  locSetXJ g hM1 H r r' (stencilX X) J

omit [NeZero M] in
/-- `A_X` grows with `X`. -/
theorem activeCoreC_mono (H : RegionHistory S n R k0 K) {k : ℕ} {X X' : Finset (Torus S.d (n k))}
    (h : X ⊆ X') :
    activeCoreC (c := g.c) (n1 := n (k + 1)) (n0 := n k) (k := k) (H.step k) hM1 X ⊆
      activeCoreC (c := g.c) (n1 := n (k + 1)) (n0 := n k) (k := k) (H.step k) hM1 X' :=
  fun _ hx => (mem_activeCoreC _).2 ⟨h ((mem_activeCoreC _).1 hx).1, ((mem_activeCoreC _).1 hx).2⟩

omit [NeZero M] in
/-- The local set of reading HS-1′ lies in that of reading HS-2. -/
theorem locSetXJ_subset_locSetXJ2 (H : RegionHistory S n R k0 K) {k : ℕ} (r r' : ℕ)
    (X : Finset (Torus S.d (n k))) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    locSetXJ g hM1 H r r' X J ⊆ locSetXJ2 g hM1 H r r' X J := by
  rintro x ⟨y, hy, hxy⟩
  refine ⟨y, ?_, hxy⟩
  rcases hy with hy | hy
  · left
    obtain ⟨y', hy', hyy'⟩ := (mem_collarCoreC _).1 hy
    exact (mem_collarCoreC _).2 ⟨y', activeCoreC_mono g hM1 H (subset_stencilX X) hy', hyy'⟩
  · exact Or.inr hy

omit [NeZero M] in
/-- **The sites of `Ω_{k+1}` in the stencil of `X` are unit points of the local pair of reading
HS-2** (the property D2 needs): a site whose cube of `𝕋_k` lies within `3` cubes of `X` and whose
cube of `𝕋_{k+1}` lies in `Ω_{k+1}` is in the top layer of `G′_V`, `V = locSetXJ2 X J`, when
`r′ ≥ L^{k+1+m₁}` (its cell of side `L^{k+1+m₁}` lies in `V`). -/
theorem mem_top_locG'_locSetXJ2 (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) {r r' : ℕ} (hr' : S.L ^ (k + 1 + m₁) ≤ r')
    (X : Finset (Torus S.d (n k))) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (hxk : cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x ∈
      nbhd 3 (X : Set (Torus S.d (n k))))
    (hxΩ : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ (H.step k).Omega) :
    x ∈ (locG' g hnn hM1 H hk hρ (locSetXJ2 g hM1 H r r' X J)).Ω (k + 1) := by
  have hc := g.hc
  refine Finset.mem_inter.2 ⟨?_, ?_⟩
  · change x ∈ (p6TopC (k := k) (H.step k) hM1 (hnn k (by omega)) hρ (by omega)).Ω (k + 1)
    rw [p6TopC, mem_castN_Ω, p6Top_Ω_top, mem_fineK1]
    exact hxΩ
  · refine (mem_localB_Ω_top_sameCell le_rfl _ (minSep_le_locB g hM1) x).2 fun w hw => ?_
    refine ⟨x, Or.inl ((mem_collarCoreC _).2 ⟨x, (mem_activeCoreC _).2
      ⟨mem_stencilX.2 hxk, hxΩ⟩, by rw [LargeField.supDist_self]; exact Nat.zero_le _⟩), ?_⟩
    exact (supDist_le_of_sameCell (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _) hw).trans hr'

/-! ### D1: the set `Y_f` contains the cubes of the sites read -/

/-- **The cubes of a set of sites lie in `Y_f`** (repair D1): the cube of `𝕋_j` of every site of `S_f`
lies in `Y_f` (the H7 domain at `Y_f` tests only the cubes inside `Y_f`; each test at a cube reads the
field on the cube and its neighbours).  For `Y_f` the fine set of a set of cubes of `𝕋_j`, this is
`S_f ⊆ Y_f` (`cubesOfIn_fineSet`). -/
def CubesOfIn (j : ℕ) (Yf Sf : Set (Torus S.d (M * n K * S.L ^ K))) : Prop :=
  ∀ x ∈ Sf, CubeSub (S := S) (n := n) M K j (LargeField.cubeMap n S.L M K j x) Yf

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- `CubesOfIn` is satisfiable (rule 10): it holds at `Y_f = 𝕋`. -/
theorem cubesOfIn_univ (j : ℕ) (Sf : Set (Torus S.d (M * n K * S.L ^ K))) :
    CubesOfIn (S := S) (n := n) (M := M) (K := K) j Set.univ Sf := fun _ _ _ _ => Set.mem_univ _

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- The sites of `S_f` lie in `Y_f` when their cubes do. -/
theorem subset_of_cubesOfIn {j : ℕ} {Yf Sf : Set (Torus S.d (M * n K * S.L ^ K))}
    (h : CubesOfIn (S := S) (n := n) (M := M) (K := K) j Yf Sf) : Sf ⊆ Yf := fun x hx =>
  h x hx x rfl

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- **The condition D1 at the fine set of a set of cubes**: the cubes of the sites of `S_f` lie in the
fine set of `Y` when `S_f` does. -/
theorem cubesOfIn_fineSet {j : ℕ} {Y : Set (Torus S.d (n j))}
    {Sf : Set (Torus S.d (M * n K * S.L ^ K))}
    (h : Sf ⊆ fineSet (S := S) (n := n) M K j Y) :
    CubesOfIn (S := S) (n := n) (M := M) (K := K) j (fineSet (S := S) (n := n) M K j Y) Sf :=
  fun x hx x' hx' => by
    show LargeField.cubeMap n S.L M K j x' ∈ Y
    rw [hx']
    exact h hx

/-! ### The two named inputs, restated (reading HS-2) -/

/-- **OPEN-H7-MIXED, the remaining part, for the local pair of reading HS-2** (restatement of
`H7MixedInnerLoc` with the repairs D1–D3; **open**): for an old label `X`, a family `J`, the local set
`V = locSetXJ2 X J`, a field of the H7 domain of scale `k + 1` at a set `Y_f` containing the cubes of
`𝕋_{k+1}` of the sites of the stencil `X^{∼3}` and of the data sites of `G′_V`, a fluctuation field
`|ψ̂| < r_ψ` and a parameter `|s_P| < R`: at every cube `□ ⊂ X` of `𝕋_k` outside `(Ω^c_k)^{∼3}` with a
cube of `𝕋_{k+1}` in `Ω^{∼3}_{k+1}`, the composed multiscale field of the local composite lies in
`Δ^c_k(□; 1, ε_k)`. -/
def H7MixedInnerLoc2 (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ ρc : ℝ) (ρ r r' : ℕ)
    (aw μs ε ε1 νs : ℕ → ℝ) (h : Fin N → ℂ) (Rp rψ : ℝ) : Prop :=
  ∀ (X : Finset (Torus S.d (n k))) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (Yf : Set (Torus S.d (M * n K * S.L ^ K))) (ψ ψ' : MultiFieldC S n M K N)
    (gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ),
    H7Domain g.M1 g.c g.hM hnn (globalLH H M) (k + 1) hk Yf aw μs ε ε1 νs h ψ ψ' gf →
    CubesOfIn (S := S) (n := n) (M := M) (K := K) (k + 1) Yf
      (fineSet (S := S) (n := n) M K k (stencilX X : Set (Torus S.d (n k))) ∪
        fineOfC g hnn hM1 hk '' (dataSites (locG' g hnn hM1 H hk hρ (locSetXJ2 g hM1 H r r' X J)) :
          Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))) →
    ∀ ψhat : (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ2 g hM1 H r r' X J)).U → Fin N → ℂ,
    (∀ b, vn (ψhat b) < rψ) →
    ∀ s : Dec2.DecParams (coverOf (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ2 g hM1 H r r' X J)).G'),
    (∀ P, ‖s P‖ < Rp) →
    ∀ y : Torus S.d (n k),
      CubeSub (S := S) (n := n) M K k y (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) →
      y ∉ omegaCNb (globalLH H M) 3 k →
      (¬ ∀ x, LargeField.cubeMap n S.L M K k x = y →
        LargeField.cubeMap n S.L M K (k + 1) x ∉ omegaNb (globalLH H M) (k + 1) 3 (k + 1)) →
      (fun z' => composedMulti g hnn hM1 hk
          (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ2 g hM1 H r r' X J)).G' ψ
          ((holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ2 g hM1 H r r' X J)).composed
            (coverOf (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
              (locSetXJ2 g hM1 H r r' X J)).G') ρc
            ((holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
              (locSetXJ2 g hM1 H r r' X J)).slocOf
              (coverOf (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
                (locSetXJ2 g hM1 H r r' X J)).G')
              (locDomsLF g hM1 (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
                (locSetXJ2 g hM1 H r r' X J)) ρ)
              (HoleStep.coreExt
                (coverOf (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
                  (locSetXJ2 g hM1 H r r' X J)).G')
                (collarCoreC (c := g.c) (H.step k) hM1 r X) s)) ψhat) k
          (LargeField.torusCast (histScale_eq g.hM hnn le_rfl (Nat.le_of_succ_le hk)) z')) ∈
        DeltaC (M1 := g.M1) (N₁ := g.c * n k) (L := S.L) (q := k) aw (μs k) (ε k) h g.c (n k) y

/-- **OPEN-H7-MIXED, the background part, for the local pair of reading HS-2** (restatement of
`H7MixedDatumLoc` with the repairs D1, D3; **open**; with the cube domains of ruling request R14,
which exclude the complex rotations of size `≥ 2 ε`, `not_mem_deltaC_of_im`): for every set `V` and
every field of the H7 domain of scale `k + 1` at a set `Y_f` containing the cubes of `𝕋_{k+1}` of the
data sites of `G′_V`, the restricted global datum of the local pair (`holeStepLoc2`) lies in
`Ψ̃^c(G′_V; δ_b, δ_b)`. -/
def H7MixedDatumLoc2 (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ)
    (aw μs ε ε1 νs : ℕ → ℝ) (h : Fin N → ℂ) (νb δb : ℝ) : Prop :=
  ∀ (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (Yf : Set (Torus S.d (M * n K * S.L ^ K))) (ψ ψ' : MultiFieldC S n M K N)
    (gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ),
    H7Domain g.M1 g.c g.hM hnn (globalLH H M) (k + 1) hk Yf aw μs ε ε1 νs h ψ ψ' gf →
    CubesOfIn (S := S) (n := n) (M := M) (K := K) (k + 1) Yf
      (fineOfC g hnn hM1 hk '' (dataSites (locG' g hnn hM1 H hk hρ V) :
        Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))) →
    InDomainC (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' νb δb δb
      (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D'

/-- **The composite of the local pair of reading HS-2 lies in the source H7 domain** (from the
transfer `h7Domain_composedMulti_of_inner` and `H7MixedInnerLoc2`; the analogue of
`h7Domain_composedMulti_loc`). -/
theorem h7Domain_composedMulti_loc2 (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ ρc : ℝ)
    (ρ r r' : ℕ) (aw μs ε ε1 νs : ℕ → ℝ) (h : Fin N → ℂ) {Rp rψ : ℝ} (hL : 2 ≤ S.L)
    (hIn : H7MixedInnerLoc2 g hnn hM1 H hk hk1 hρ z h₀ a₁ ν β p₁ δ ρc ρ r r' aw μs ε ε1 νs h Rp rψ)
    (X : Finset (Torus S.d (n k))) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {Yf : Set (Torus S.d (M * n K * S.L ^ K))} {ψ ψ' : MultiFieldC S n M K N}
    {gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ}
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLH H M) (k + 1) hk Yf aw μs ε ε1 νs h ψ ψ' gf)
    (hY : CubesOfIn (S := S) (n := n) (M := M) (K := K) (k + 1) Yf
      (fineSet (S := S) (n := n) M K k (stencilX X : Set (Torus S.d (n k))) ∪
        fineOfC g hnn hM1 hk '' (dataSites (locG' g hnn hM1 H hk hρ (locSetXJ2 g hM1 H r r' X J)) :
          Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))))
    {ψhat : (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ2 g hM1 H r r' X J)).U → Fin N → ℂ}
    (hψhat : ∀ b, vn (ψhat b) < rψ)
    {s : Dec2.DecParams (coverOf (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ2 g hM1 H r r' X J)).G')}
    (hs : ∀ P, ‖s P‖ < Rp) :
    H7Domain g.M1 g.c g.hM hnn (globalLH H M) k (Nat.le_of_succ_le hk)
      (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
      (composedMulti g hnn hM1 hk
        (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ2 g hM1 H r r' X J)).G' ψ
        ((holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ2 g hM1 H r r' X J)).composed
          (coverOf (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
            (locSetXJ2 g hM1 H r r' X J)).G') ρc
          ((holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ2 g hM1 H r r' X J)).slocOf
            (coverOf (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
              (locSetXJ2 g hM1 H r r' X J)).G')
            (locDomsLF g hM1 (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
              (locSetXJ2 g hM1 H r r' X J)) ρ)
            (HoleStep.coreExt
              (coverOf (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
                (locSetXJ2 g hM1 H r r' X J)).G')
              (collarCoreC (c := g.c) (H.step k) hM1 r X) s)) ψhat))
      ψ' gf :=
  h7Domain_composedMulti_of_inner g hnn hM1 H hk (by omega) hL
    (fun b => cubeOfC_mem_of_unitPts_loc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ2 g hM1 H r r' X J) b) ψ _
    (fun x hx => subset_of_cubesOfIn hY (Or.inl (fineSet_mono_stencil hx))) aw μs ε ε1 νs h ψ' gf htgt
    fun y hyX hyC hnear => hIn X J Yf ψ ψ' gf htgt hY ψhat hψhat s hs y hyX hyC hnear

/-! ### D2: the cell count of the stencil core -/

omit [∀ k, NeZero (n k)] [NeZero S.L] in
/-- The cells of side `1` are the sites. -/
theorem cbase_one' {n' : ℕ} [NeZero n'] (x : Torus S.d n') : cbase 1 x = x := by
  funext μ
  simp only [cbase, one_mul, Nat.div_one]
  exact ZMod.natCast_zmod_val _

include hnn in
open Classical in
/-- **The cells of the stencil core** (repair D2; the cell count of `OldResumSite` for the local set
of reading HS-2): the cells of scale `k + 1` of `A⁺_X = Ω_{k+1} ∩ X^{∼3}` (the sites of the cover
torus whose cube of `𝕋_k` lies within `3` cubes of `X` and whose cube of `𝕋_{k+1}` lies in
`Ω_{k+1}`) are at most `9^d c₁ (1 + d_k(X mod Ω_k^c))` for a valid old label `X`: a cube of `𝕋_k` within
`3` cubes of a cube `u ∈ X` and whose coarse cube lies in `Ω_{k+1}` forces `u ∉ Z_k` (P5 (2.3),
`blockMap_notMem_Omega_of_near`), so `u ∈ Ω_k^post`. -/
theorem card_cells_stencilCore_le {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊)
    {X : Finset (Torus S.d (n k))} (hX : FineValidAt F k (H.omegaPost k) X) :
    (((activeCoreC (c := g.c) (n1 := n (k + 1)) (n0 := n k) (k := k) (H.step k) hM1
        (stencilX X)).image (cbase (cellSide S.L m₀ m₁ (k + 1)))).card : ℝ) ≤
      9 ^ S.d * (c1 S.d S.L * (1 + d7SizeAt F k (H.omegaPost k) X)) := by
  set cs := cellSide S.L m₀ m₁ (k + 1) with hcs
  set ck := cellSide S.L m₀ m₁ k with hck
  have hck0 : 0 < ck := cellSide_pos m₀ m₁ k
  have hkK : k ≤ K := Nat.le_of_succ_le hk
  have hdk : ck ∣ cs := by
    rw [hck, hcs]; unfold cellSide; exact pow_dvd_pow _ (by omega)
  set A := activeCoreC (c := g.c) (n1 := n (k + 1)) (n0 := n k) (k := k) (H.step k) hM1
    (stencilX X) with hA
  set Wf : Finset (Torus S.d (n k)) :=
    (stencilX X).filter fun u => blockMap S.L (n (k + 1)) u ∈ (H.step k).Omega with hWf
  set Xp : Finset (Torus S.d (n k)) := X.filter fun u => u ∉ (H.step k).Z with hXp
  -- the cells of the cover torus are those of the frame
  have hcast : ((A.image (toFrame g hnn hM1 F hk)).image (cbase cs)).card = (A.image (cbase cs)).card := by
    have e : (A.image (toFrame g hnn hM1 F hk)).image (cbase cs) =
        (A.image (cbase cs)).image (toFrame g hnn hM1 F hk) := by
      rw [Finset.image_image, Finset.image_image]
      congr 1
      funext x
      exact (toFrame_cbase g hnn hM1 F hk cs x).symm
    rw [e, Finset.card_image_of_injective _ (toFrame_injective g hnn hM1 F hk)]
  -- the frame sites of `A⁺_X` lie in the fine lift of `Wf`
  have hAW : ∀ x ∈ A, toFrame g hnn hM1 F hk x ∈ d7Pull F k (Wf : Set (Torus S.d (n k))) := by
    intro x hx
    obtain ⟨hxs, hxΩ⟩ := (mem_activeCoreC _).1 hx
    rw [toFrame_mem_d7Pull_iff, cubeMap_fineOfC_k]
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hxs, ?_⟩)
    rw [← cubeMap_fineOfC_k g hnn hM1 hk x, cubeMap_succ hnn hk, cubeMap_fineOfC_succ]
    exact hxΩ
  -- the cells of scale `k + 1` of the frame sites by the cells of scale `k` of `Wf`
  have hcell : ∀ {x}, x ∈ d7Pull F k (Wf : Set (Torus S.d (n k))) →
      Localization.box (cbase ck x) ck ⊆ d7Pull F k (Wf : Set (Torus S.d (n k))) := fun {x} hx => by
    rcases cell_dichotomy F.divN₁ hkK (d7Pull_isPiUnion F hnn hkK _)
        (aligned_cbase (a := ck) x) with h | h
    · exact h
    · exact absurd hx (h (mem_box_cbase hck0 x))
  have hsub : (A.image (toFrame g hnn hM1 F hk)).image (cbase cs) ⊆
      (cellsIn (L := S.L) m₀ k (d7Pull F k (Wf : Set (Torus S.d (n k))))).image (cbase cs) := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have hxW := hAW x hx
    refine Finset.mem_image.2 ⟨cbase ck (toFrame g hnn hM1 F hk x), ?_, ?_⟩
    · simp only [cellsIn, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨aligned_cbase _, hcell hxW⟩
    · exact cbase_eq_of_sameCell (SameCell.of_dvd hdk (sameCell_cbase_self _)).symm
  have h1 : (A.image (cbase cs)).card ≤ Wf.card := by
    rw [← hcast, ← card_cellsIn_d7Pull F hnn hkK Wf]
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  -- the cubes of `Wf` lie within `3` of the cubes of `X` off `Z_k`
  have hWN : Wf ⊆ Finset.univ.filter fun u => ∃ v ∈ Xp, LargeField.supDist u v ≤ 3 := by
    intro u hu
    obtain ⟨hus, huΩ⟩ := Finset.mem_filter.1 hu
    obtain ⟨v, hvX, hv⟩ := mem_nbhd.1 (mem_stencilX.1 hus)
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, v, Finset.mem_filter.2 ⟨hvX, fun hvZ => ?_⟩, hv⟩
    have hL1 : 1 ≤ S.L := Nat.one_le_iff_ne_zero.2 (NeZero.ne S.L)
    exact (H.step k).blockMap_notMem_Omega_of_near (mem_nbhd.2 ⟨v, hvZ, by omega⟩) huΩ
  have h2 : Wf.card ≤ 9 ^ S.d * Xp.card := by
    have hN := card_cbase_nbhd_le (d := S.d) (n := n k) (a := 1) (one_dvd _) one_pos Xp 3
    have hc1 : (cbase 1 : Torus S.d (n k) → Torus S.d (n k)) = id := funext cbase_one'
    rw [hc1, Finset.image_id, Finset.image_id] at hN
    norm_num at hN
    exact (Finset.card_le_card hWN).trans hN
  -- the cubes of `X` off `Z_k` are cells of `X ∩ Ω_k^post`
  have h3 : (Xp.card : ℝ) ≤ c1 S.d S.L * (1 + d7SizeAt F k (H.omegaPost k) X) := by
    have h4 := hX.cellCount_le F.divN₁ hkK
    rw [← card_cellsIn_eq_cellCount] at h4
    refine le_trans ?_ h4
    rw [← card_cellsIn_d7Pull F hnn hkK Xp]
    exact_mod_cast Finset.card_le_card fun t ht => by
      obtain ⟨hta, htb⟩ := (mem_cellsIn).1 ht
      refine (mem_cellsIn).2 ⟨hta, fun z hz => ?_⟩
      have hz' := htb hz
      rw [mem_d7Pull] at hz'
      obtain ⟨hzX, hzZ⟩ := Finset.mem_filter.1 hz'
      refine ⟨mem_d7Pull.2 hzX, mem_d7Pull.2 ?_⟩
      by_contra hc
      exact hzZ (H.compl_omegaPost_subset_Z k hc)
  have h12 : ((A.image (cbase cs)).card : ℝ) ≤ 9 ^ S.d * Xp.card := by exact_mod_cast h1.trans h2
  calc ((A.image (cbase cs)).card : ℝ) ≤ 9 ^ S.d * Xp.card := h12
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- **`OldResumSite` for the local sets of reading HS-2** (repair D2): the resummation at a mark site
holds for the local sets `V(X^{∼3}, J)`, with the constants of `oldResumSiteAt_holds` at
`c_S = 9^d c₁` (`card_cells_stencilCore_le`). -/
theorem oldResumSite2_holds {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊)
    {ρ r r' : ℕ} (hL2 : 2 ≤ S.L) (hgc : S.L ^ m₀ ∣ g.c * n (k + 1))
    (hr' : S.L ^ (k + 1 + m₁) ≤ r') {κ₁ β : ℝ} (hβκ : β < κ₁ - 1) :
    OldResumSiteAt g hnn hM1 F H hk hρ ρ r r' stencilX κ₁
      ((κ₁ - 1 - β) / (resumTree S.d S.L * resumNbhd S.d S.L m₀ m₁ k r r') * resumTree S.d S.L *
        (c1 S.d S.L + resumNbhd S.d S.L m₀ m₁ k r r' * (9 ^ S.d * c1 S.d S.L) + 3 ^ S.d / S.L))
      ((κ₁ - 1 - β) / (resumTree S.d S.L * resumNbhd S.d S.L m₀ m₁ k r r') -
        Real.exp (-β) * resumCubes S.d S.L m₀)
      (Real.exp (Real.exp (-β) * resumCubes S.d S.L m₀ +
        (κ₁ - 1 - β) / (resumTree S.d S.L * resumNbhd S.d S.L m₀ m₁ k r r') * resumTree S.d S.L *
          (c1 S.d S.L + resumNbhd S.d S.L m₀ m₁ k r r' * (9 ^ S.d * c1 S.d S.L) + 3 ^ S.d))) := by
  classical
  exact oldResumSiteAt_holds g hnn hM1 F H hk hρ (ρ := ρ) (r := r) hL2 hgc hr' stencilX
    (fun _ hXd => (card_cells_stencilCore_le g hnn hM1 F H hk hρ
      (mem_bdryDomsAt.1 (Finset.mem_filter.1 hXd).1).2).trans_eq (by ring)) hβκ

end HS2

end Balaban.RootFSpine
