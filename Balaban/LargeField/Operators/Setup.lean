module

public import Balaban.LargeField.Operators.Kernel
public import Balaban.LargeField.Operators.HistGen
public import Balaban.LargeField.Operators.Variables
public import Balaban.LargeField.Characteristic.Analytic
public import Balaban.Model.Symmetry

/-!
# Setting of the localized operators (Part II, §II.5)

* `Geo`: the geometric typing data of the localized operators: the cube factor `M = c M₁` with
  `c ≥ 14` (so that the generating sets of Definition II.2.4 exist) and `R_j ≥ R_base`
  (Lemma II.1.2 (a));
* `OpConsts`: the running constants that enter the operators: weights, masses, tolerances,
  renormalizations;
* the output sets `Vblk` (`V_Z = (Z^≈)^∼` as a set of blocks), output configurations `OutT`, the new
  internal variables `newVars`, the index set `GIdx` of the external field `g`;
* the transport `blockCfgOf` of a field on the blocks to the level-`q` torus of the characteristic
  functions;
* the action of `O(N)` on all variables, parameters and data (`rotSub`, `rotOut`, `rotG`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

/-- Geometric typing data of the localized operators. -/
structure Geo (S : Setting) (n : ℕ → ℕ) (R : ℕ → ℝ) (M : ℕ) where
  /-- the unit `M₁` of the generating sets -/
  M1 : ℕ
  /-- the factor `c` with `M = c M₁` -/
  c : ℕ
  neM1 : NeZero M1
  nec : NeZero c
  hM : M = c * M1
  hc : 14 ≤ c
  /-- `R_j ≥ R_base` (Lemma II.1.2 (a)) -/
  hRlow : ∀ j, S.Rb ≤ R j
  /-- `⌊R_{j-1}⌋ ≤ ⌊R_j⌋` (the radii `R_j = R_base λ_j²` are nondecreasing) -/
  hRmono : ∀ j, ⌊R (j - 1)⌋₊ ≤ ⌊R j⌋₊

attribute [instance] Geo.neM1 Geo.nec

/-- The running constants of the localized operators (all indexed by the scale). -/
structure OpConsts where
  /-- the weights `a_n` of the multiscale actions -/
  aw : ℕ → ℝ
  /-- the fine-unit mass `μ_j` of the backgrounds (zero for `j ≤ k₀`) -/
  mu : ℕ → ℝ
  /-- the mass `ν_j L^{-2j}` of the main action (present for every scale) -/
  muAct : ℕ → ℝ
  /-- the dimensionless mass `ν_j` of the `h`-conditions -/
  nu : ℕ → ℝ
  /-- the tolerances `δ_j` -/
  delta : ℕ → ℝ
  /-- `p_0(β_j)` -/
  p0 : ℕ → ℝ
  /-- `C_{ψ'}` -/
  Cpsi : ℝ
  /-- the coupling `β_j` -/
  beta : ℕ → ℝ
  /-- the field renormalization `z_j` -/
  z : ℕ → ℝ
  /-- the constant `a` of the Gaussian kernel of `T^{(k)}` -/
  aKer : ℝ
  /-- `C_b` and `B_0` of the bound (S0) -/
  Cb : ℝ
  B0 : ℝ

section Types


variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L]

variable {k0 : ℕ}

/-- The localized history of a component `Zc` (a finset of `𝕋_k`-cubes) of a region history `Hl`
without removals: the records of `Hl` intersected with the fine set of `Zc`.  For the lineage
localization `H.locRH k Z` of a component `Z` of a region history `H` and `Zc = Z.1` this is
`H.localHistory M K k Z` (by `rfl`). -/
def locHist (Hl : RegionHistory S n R k0 K) (M K k : ℕ) (Zc : Finset (Torus S.d (n k))) :
    LocalHistory S n M K where
  Z j := fineSet (S := S) (n := n) M K j (Hl.step j).Z ∩ fineSet M K k Zc
  P j := fineSet M K (j + 1) (Hl.step j).P ∩ fineSet M K k Zc
  Q j := fineSet M K (j + 1) (Hl.step j).Q ∩ fineSet M K k Zc
  R j := fineSet M K (j + 1) (Hl.step j).R ∩ fineSet M K k Zc
  Sset j := fineSet M K (j + 1) (Hl.step j).S ∩ fineSet M K k Zc
  OmegaPrime j := fineSet M K (j + 1) (Hl.step j).OmegaPrime ∩ fineSet M K k Zc
  Omega j := fineSet M K (j + 1) (Hl.step j).Omega ∩ fineSet M K k Zc
  OmegaDD j := fineSet M K (j + 1) (Hl.step j).OmegaDD ∩ fineSet M K k Zc

theorem locHist_locRH (H : RegionHistory S n R k0 K) (M K k : ℕ) (Z : H.Comp k) :
    locHist (H.locRH k Z) M K k Z.1 = H.localHistory M K k Z := rfl

theorem locComp_mem (H : RegionHistory S n R k0 K) {k : ℕ} (hkK : k ≤ K) (Z : H.Comp k) :
    Z.1 ∈ comps (S.omega k) ((H.locRH k Z).F.Zp k) := by
  rw [locRH_comps hkK Z]
  exact Finset.mem_singleton_self _

/-- The index set of the external field `g : 𝕋 → ℂ^N`. -/
abbrev GIdx (S : Setting) (n : ℕ → ℕ) (M K N : ℕ) : Type :=
  Torus S.d (M * n K * S.L ^ K) × Fin N

/-- The cubes of `𝕋_j` whose fine set lies in the `j`-th record `Z_j` of a localized history. -/
def Zcubes (a : LocalHistory S n M K) (j : ℕ) : Set (Torus S.d (n j)) :=
  {y | CubeSub (S := S) (n := n) M K j y (a.Z j)}

/-- The cubes of `V = (Z^≈)^∼` at scale `k` (`≈` adds `⌊R_{k-1}⌋ + 1`, `∼` adds `1`). -/
def Vcubes (R : ℕ → ℝ) (a : LocalHistory S n M K) (k : ℕ) : Set (Torus S.d (n k)) :=
  nbhd 1 (thick ⌊R (k - 1)⌋₊ (Zcubes a k))

/-- The `k`-blocks of `V`. -/
def Vblk (R : ℕ → ℝ) (a : LocalHistory S n M K) (k : ℕ) : Set (BlockAt S n M K k) :=
  {y | blockCube S n M K k y ∈ Vcubes R a k}

/-- Output configurations `ψ_k` on `T^{(k)} ∩ V`. -/
abbrev OutT (N : ℕ) (R : ℕ → ℝ) (a : LocalHistory S n M K) (k : ℕ) : Type :=
  OutConfig N (Vblk R a k)

/-- The new internal variables `I^new_k` of the step `k → k + 1`: those of scale `k`. -/
def newVars (a : LocalHistory S n M K) (k : ℕ) : Set (InternalVars a (k + 1)) :=
  {p | p.1.1.val = k}

/-- Configurations of the new internal variables `I^new_k` of the step `k → k + 1`. -/
abbrev NewCfg (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) : Type :=
  SubCfg N a (k + 1) (newVars a k)

/-- The fine sites in the sets of blocks `V` (the support of `g` for the operators). -/
def Vsites (R : ℕ → ℝ) (a : LocalHistory S n M K) (k : ℕ) : Set (Torus S.d (M * n K * S.L ^ K)) :=
  {x | cubeMap n S.L M K k x ∈ Vcubes R a k}

end Types

section Transport

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- A field on the `i`-blocks of the fine torus, transported to the level-`q` torus
`Torus d (M₁ (c n_q) L^{q-i})` of the characteristic functions (`i ≤ q ≤ K`). -/
def blockCfgOf (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {q i : ℕ} (hiq : i ≤ q)
    (hqK : q ≤ K) (f : BlockAt S n M K i → EuclideanSpace ℝ (Fin N)) :
    BlockCfg S.d (g.M1 * (g.c * n q)) S.L q i N :=
  fun z j => f (torusCast (histScale_eq g.hM hnn hiq hqK) z) j

end Transport

/-! ### The action of `O(N)` -/

section Rotation

variable {N : ℕ}

/-- An element of `O(N)`. -/
abbrev OrthN (N : ℕ) : Type :=
  EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)

/-- Rotation of a variable (spins stay on the sphere). -/
def VarVal.rot (R : OrthN N) : (b : Bool) → VarVal N b → VarVal N b
  | true, v => ⟨R v.1, by
      have h := v.2
      simp only [mem_sphere_iff_norm, sub_zero] at h ⊢
      rw [LinearIsometryEquiv.norm_map, h]⟩
  | false, v => R v

theorem VarVal.toEuc_rot (R : OrthN N) : ∀ (b : Bool) (v : VarVal N b),
    VarVal.toEuc (VarVal.rot R b v) = R (VarVal.toEuc v)
  | true, _ => rfl
  | false, _ => rfl

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]

/-- Rotation of a configuration of internal variables. -/
def rotSub (R : OrthN N) {a : LocalHistory S n M K} {k : ℕ} {A : Set (InternalVars a k)}
    (x : SubCfg N a k A) : SubCfg N a k A :=
  fun p => VarVal.rot R _ (x p)

/-- Rotation of the output configuration. -/
def rotOut (R : OrthN N) {α : Type} {V : Set α} (o : OutConfig N V) : OutConfig N V :=
  fun y => R (o y)

/-- Rotation of the external field: `(R g)(x) = R g(x)` (the matrix of `R` acting on the
coordinates, extended to `ℂ^N`). -/
noncomputable def rotG (R : OrthN N) (g : GIdx S n M K N → ℂ) : GIdx S n M K N → ℂ :=
  fun p => ∑ j, (rotEntry R p.2 j : ℂ) * g (p.1, j)

end Rotation

end Balaban.LargeField
