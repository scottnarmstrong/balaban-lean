module

public import Balaban.LargeField.Def7Hist
public import Balaban.SmallField.Def6

/-!
# Def-7, part 2: the small-field data `𝔰` and the restricted small-field functions — DRAFT

LF-RECONSTRUCTION v1.3 §II.6.1, first item and "derived objects": the small-field data `𝔰` of a
representation at scale `k` and the restricted small-field functions of P5 (1.6)-(1.19) on the
small-field region `Y = Z^c_k` of a history:
```
𝒜_k(Y; ψ_k, h) = -β_k A*_k(Y; ψ_k, φ_k) + ℰ_k(Y; ψ_k, h) - E_k |Y|_k,          (1.6)-(1.7)
ℰ^{(j)}(Y; ψ_j, h) = ∑_{y ∈ Y ∩ T^{(j)}} ∑_{X ∈ 𝒟_j, y ∈ X ⊂ Y^≈} ℰ^{(j)}(y, X; ψ_j, h)
                    - ∑_{y ∈ Y ∩ T^{(j)}} ∑_{x ∈ Y^≈ ∩ T^{(j)}} [½ v₁ (ψ²(x) - ψ²(y)) + v₂ (…)],   (1.8)
ℱ_k(Y; ψ_k, h, g) = ⟨χ_Y g, φ_k⟩₁ + ∑_j ⟨χ_Y g, ℳ^{(j)}(Y; ψ^{(j)}_k, h, g)⟩₁,             (1.10)-(1.13)
ℛ^{(k)}(Y; ψ_k, h, g) = ∑_{n=1}^m ∑_{X ∈ 𝒟_k, X ⊂ Y} ℛ^{(k)}_n(X; ψ_k, h, g),                 (1.16)-(1.17)
χ_k(Y) = ∏_{□ ⊂ Y} χ_k(□),                                                              (1.18)-(1.19)
```
and the small-field factor `sfFactor = χ_k(Y) exp(𝒜_k + ℱ_k + ℛ^{(k)})(Y)` of (D1).

**Tori.**  The terms of Def-6 live on the Def-6 tori `CTorus d L N₁ m₁ k` (all `N₁`); the
backgrounds `φ_k = bgSF`, `ψ^{(j)}_k = psiSF` of Definition II.2.7 (iii) on the level-`k` torus
`BgT geo k = Torus d (M₁ (c n_k) L^k)`; the history on the fine torus `Torus d (M n_K L^K)`.  They
are the same torus (side `ℓ`) when `N₁ L^{m₁} = M₁ c n_k` (`hT`) and `M = c M₁` (`Geo`); the maps
`sfToBg`, `bgToFine` are the identifications (`torusCast`).

**Open point (recorded, not resolved): the correction term of (1.8).**  The second sum of P5
(1.8) uses functions `v^{(j)}_{1,2}(y, x)` "determined by `ℰ^{(j)}` on the whole lattice through
P1 (3.106)" and a field `(ψ_j)_0`; neither is defined in LFR v1.3 nor landed (P1 (3.106) is only
summarized in `review/papers/P1-LTE-I-RG-flow.md`, Lemma 3.8).  The pair terms
`½ v₁(y,x)(ψ_j²(x) - ψ_j²(y)) + v₂(y,x)(ν_j h·(ψ_j)_0(x) - ν_j h·(ψ_j)_0(y))` are therefore carried
as a datum `corr` of `𝔰` (`SFData.corr`); the clause tying `corr` to `ℰ^{(j)}` (P1 (3.106)) is
missing, so the class contains representations with an arbitrary correction.  See the handoff.

**Units of the action.**  `β_k A*_k` is `β^{(k)}_0 (A + ¼ ∑_{st} |∂φ̄|²)` with the fine-unit action
`A` (`actionG`) and `β^{(k)}_0 = β_k L^{-k(d-2)}` (`betaCanon`), as in Definition II.5.4 and SF (H.1)
(`A_k` in `η`-units, `η = L^{-k}`).  Def-6's `IsSF.density` writes `-β_k · action` with the
fine-unit Def-5 `action` (recorded in the handoff as a units discrepancy to be checked).

**Masses (open point Q13).**  The background `φ_k` and the characteristic functions use the
solver mass `cs.mu k` (`0` for `k ≤ k₀`, P5 (1.9)); the small-field action `A*_k` uses
`sfActMass` (currently the same, as in Def-6's `IsSF`, where the `ν`-term is carried by `ℰ`).
The pinned-field proposal of `notes/phase1/Q13-ANSWER-astra.md` would change `sfActMass` to the
physical mass; this is the only place where it enters.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Def7

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory
open Balaban.SmallField

/-! ### The small-field data -/

/-- **The small-field data `𝔰` at scale `k`** (§II.6.1, first item): the running constants
`(β_j, ν_j)_{j ≤ k}`, `(z_j)_{1 ≤ j ≤ k}`, the coefficients `a_j` of the flow (Def-6, (H.6)), the
constant `E_k` of the vacuum term (on each Def-6 torus `N₁`, as in Def-6), and on every Def-6 torus:
the localized functions `ℰ^{(j)}(y, X)`, `ℳ^{(j)}(x, X)` with the generating sets `𝔹_j(X)`
(`Def6.Terms`), the terms `ℛ^{(k)}_n(X; ψ_k, h, g)` (`1 ≤ n ≤ m`, `L^m = M`, `X ∈ 𝒟_k`; P5 H4),
and the correction pair terms of (1.8) (`corr`; see the module docstring: open point). -/
structure SFData (d L m₁ k N : ℕ) [NeZero L] (ϱ : ℝ) where
  /-- the running couplings `β_j` -/
  β : ℕ → ℝ
  /-- the running masses `ν_j` -/
  ν : ℕ → ℝ
  /-- the field renormalizations `z_j` -/
  z : ℕ → ℝ
  /-- the running coefficients `a_j` (Def-6 (H.6)) -/
  a : ℕ → ℝ
  /-- the constant `E_k` of `E_k |T^{(k)}_1|` on the Def-6 torus `N₁` -/
  E : ℕ → ℝ
  /-- the localized terms `ℰ^{(j)}(y, X)`, `ℳ^{(j)}(x, X)` and the sets `𝔹_j(X)` -/
  Tm : ∀ (N₁ : ℕ) [NeZero N₁], Def6.Terms d L N₁ m₁ k N ϱ
  /-- the terms `ℛ^{(k)}_n(X; ψ_k, h, g)` -/
  Rt : ∀ (N₁ : ℕ) [NeZero N₁], ℕ → Set (Localization.CTorus d L N₁ m₁ k) → Def6.Fld d L N₁ m₁ k N →
    Def6.Fld d L N₁ m₁ k N → Def6.Fld d L N₁ m₁ k N → ℂ
  /-- the pair terms of the second sum of P5 (1.8) at the scale `j` (open point, see above) -/
  corr : ∀ (N₁ : ℕ) [NeZero N₁], ℕ → Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k →
    Def6.Fld d L N₁ m₁ k N → Def6.Fld d L N₁ m₁ k N → ℂ

/-- **The mass of the small-field action `A*_k`** under the convention of LFR v1.3 and Def-6
(P5 (1.9): for `β_k ν_k ≤ 1` the `ν_k`-term is omitted from the variational problems and carried
by `ℰ`): the solver mass `cs.mu k`.  Open point Q13 (`notes/QUESTIONS-ROLAND-2.md` item 13,
`notes/phase1/Q13-ANSWER-astra.md`): the pinned-field repair keeps the physical mass in the
action; it would replace this definition by `cs.muAct k`. -/
def sfActMass (cs : OpConsts) (k : ℕ) : ℝ := cs.mu k

/-! ### The level generating set and the identifications of the tori -/

section Level

variable {d L N₀ : ℕ} [NeZero L] [NeZero N₀] {ϱ : ℝ}

open Classical in
/-- The whole-lattice generating set of level `q` on `Torus d (N₀ L^q)` (`Ω_i = 𝕋` for `i ≤ q`):
the generating set `T^{(q)}_1` of the single-scale action `A*_q` (P5 (1.5)). -/
noncomputable def levelGen (q : ℕ) : GeneratingSet d L N₀ q ϱ where
  Ω := fun i => if i ≤ q then Finset.univ else ∅
  top := by simp
  subset := fun j _ hjq => by
    intro x _
    simp [hjq]
  blockUnion := fun i _ _ x x' _ => by split_ifs; simp
  separation := fun j _ hjq x hx y _ => by
    exfalso
    have : j ≤ q := hjq.le
    simp [this] at hx

end Level

section Bridge

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] (geo : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ}
  (hkK : k ≤ K)

/-- The level-`k` torus of the small-field backgrounds (`genSF`, `bgSF`, `psiSF` with
`N₁ = c n_k`, `M₁ = geo.M1`). -/
abbrev BgT (geo : Geo S n R M) (k : ℕ) : Type := Torus S.d (geo.M1 * (geo.c * n k) * S.L ^ k)

/-- The identification of the background torus with the fine torus of the history. -/
def bgToFine : BgT geo k → Torus S.d (M * n K * S.L ^ K) :=
  torusCast (histScale_eq geo.hM hnn (Nat.zero_le k) hkK)

/-- The identification of the `k`-blocks of the level-`k` torus with the `k`-blocks `T^{(k)}` of
the history. -/
def blkToBlock : Torus S.d (geo.M1 * (geo.c * n k) * S.L ^ (k - k)) → BlockAt S n M K k :=
  torusCast (histScale_eq geo.hM hnn le_rfl hkK)

variable {m₁ N₁ : ℕ} [NeZero N₁]
  (hT : N₁ * S.L ^ m₁ * S.L ^ k = geo.M1 * (geo.c * n k) * S.L ^ k)

/-- The identification of the Def-6 torus `CTorus d L N₁ m₁ k` with the background torus. -/
def sfToBg : Localization.CTorus S.d S.L N₁ m₁ k → BgT geo k := torusCast hT

/-- The fine set, on the Def-6 torus, of a set `Y` of cubes of `𝕋_k`. -/
def sfSet (Y : Set (Torus S.d (n k))) : Set (Localization.CTorus S.d S.L N₁ m₁ k) :=
  {x | cubeMap n S.L M K k (bgToFine geo hnn hkK (sfToBg geo hT x)) ∈ Y}

/-- A field on the background torus, read on the Def-6 torus. -/
def sfPull {N : ℕ} (f : BgT geo k → Fin N → ℂ) : Def6.Fld S.d S.L N₁ m₁ k N :=
  fun x => f (sfToBg geo hT x)

/-- The external field `g` (a function on the fine sites of the history), read on the Def-6
torus. -/
def sfG {N : ℕ} (g : GIdx S n M K N → ℂ) : Def6.Fld S.d S.L N₁ m₁ k N :=
  fun x i => g (bgToFine geo hnn hkK (sfToBg geo hT x), i)

/-- The lift of `ψ_k` (a field on the `k`-blocks) to the sites of the Def-6 torus (constant on the
`k`-blocks). -/
def sfLiftK {N : ℕ} (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    Def6.Fld S.d S.L N₁ m₁ k N :=
  fun x i => ((ψk (jBlock S.d S.L (M * n K) K k (bgToFine geo hnn hkK (sfToBg geo hT x)))) i : ℂ)

end Bridge

/-! ### The restricted small-field functions -/

section Restricted

/-- **The typing context of the restricted small-field functions** on one torus of the history
(`n`, horizon `K`) at scale `k ≤ K`: the geometric typing data, the running constants of the
operators, the polymer exponent `m₀` of Def-6, the small-field data `𝔰`, and the Def-6 torus
`N₁` identified with the level-`k` torus (`hT`). -/
structure SFCtx (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (R : ℕ → ℝ) (M K : ℕ) [NeZero M]
    [NeZero S.L] (N k m₁ : ℕ) (ϱ : ℝ) where
  /-- the geometric typing data -/
  geo : Geo S n R M
  /-- `n_i = L n_{i+1}` below the horizon -/
  hnn : ∀ i, i < K → n i = S.L * n (i + 1)
  /-- the scale is below the horizon -/
  hkK : k ≤ K
  /-- the running constants of the operators -/
  cs : OpConsts
  /-- the polymer exponent of Def-6 (`𝒟_j`: unions of cubes of side `L^{j+1+m₀+m₁}`) -/
  m₀ : ℕ
  /-- the small-field data -/
  sf : SFData S.d S.L m₁ k N ϱ
  /-- the Def-6 torus -/
  N₁ : ℕ
  [nz : NeZero N₁]
  /-- the Def-6 torus is the level-`k` torus -/
  hT : N₁ * S.L ^ m₁ * S.L ^ k = geo.M1 * (geo.c * n k) * S.L ^ k

attribute [instance] SFCtx.nz

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (Y : Set (Torus S.d (n k))) (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
  (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)

namespace SFCtx

/-- The fine set, on the Def-6 torus, of a set of cubes of `𝕋_k`. -/
def sset (A : Set (Torus S.d (n k))) : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) :=
  sfSet C.geo C.hnn C.hkK C.hT A

/-- The weights `a^{(k)}_n` of the connecting problems at scale `k` (the ideal flow matched at
step `k`, as in Def-6's `IsSF`). -/
noncomputable def weights : ℕ → ℝ := Def6.aIdeal S.L k (C.sf.a k)

end SFCtx

/-- `Y^≈`: the thickening of `Y` by `⌊R_{k-1}⌋ + 1` cubes (scale `k`), as in `V = (Z^≈)^∼`
(`Vcubes`). -/
def thickY (R : ℕ → ℝ) {k : ℕ} (Y : Set (Torus S.d (n k))) : Set (Torus S.d (n k)) :=
  thick ⌊R (k - 1)⌋₊ Y

/-- `W_k = Y^{≈2}` (P5 (1.4), §II.2.3): the support of the small-field generating set
`𝔹_k(W_k)`. -/
def W2 (R : ℕ → ℝ) {k : ℕ} (Y : Set (Torus S.d (n k))) : Set (Torus S.d (n k)) :=
  thick ⌊R (k - 1)⌋₊ (thick ⌊R (k - 1)⌋₊ Y)

/-- The volume `|A|_k` in scale-`k` units: the number of `k`-blocks of `A` (`M^d` per cube). -/
noncomputable def volK (M : ℕ) {k : ℕ} (A : Set (Torus S.d (n k))) : ℝ :=
  (A.ncard : ℝ) * (M : ℝ) ^ S.d

/-- The multiscale field equal to `ψ_k` at the scale `k` and to `0` at the other scales. -/
def singleScale {M K N : ℕ} (k : ℕ) (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    MultiField S n M K N :=
  fun m y => if hm : m = k then ψk (hm ▸ y) else 0

/-- The physical field as a complex vector. -/
def hC (hv : EuclideanSpace ℝ (Fin N)) : Fin N → ℂ := fun i => ((hv i : ℝ) : ℂ)

namespace SFCtx

/-- The lifted data `lift_k ψ_k` of the level-`k` torus (complex). -/
noncomputable def liftData :
    Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) → Fin N → ℂ :=
  (blockCfgOf C.geo C.hnn le_rfl C.hkK ψk).toC

/-- The small-field generating set `𝔹_k(W_k)` (Definition II.2.4 (iii)). -/
noncomputable abbrev genW : GeneratingSet S.d S.L (C.geo.M1 * (C.geo.c * n k)) k
    (minSep S.L C.geo.M1) :=
  genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L) (c := C.geo.c) (n := n k) (le_refl k)
    (W2 R Y)

/-- **`φ_k = bg(𝔹_k(W_k); lift_k ψ_k)`** (Definition II.2.7 (iii); P5 (1.4)), mass `cs.mu k`. -/
noncomputable def phiK : (C.genW Y).Ω 1 × Fin N → ℂ :=
  bgSF C.weights (C.cs.mu k) (bgC0 S.d S.L N) (W2 R Y) (C.liftData ψk) (hC hv)

/-- The real background `φ̄_k` on all sites of the level-`k` torus (extended by the data off
`Ω_1`); real for real data on the domain of BG Theorem 7.1. -/
noncomputable def phiBar : BgT C.geo k → EuclideanSpace ℝ (Fin N) :=
  fun z => WithLp.toLp 2 fun i =>
    (barField (C.genW Y) (liftSingle (C.genW Y) (C.liftData ψk) (hC hv)).Ψ
      (C.phiK Y ψk hv) z i).re

/-- **`ψ^{(j)}_k = composeField (𝔹_j(W_k), 𝔹_k(W_k), a; φ_k, lift_k ψ_k)`** (Definition II.2.7
(iii); P5 (1.4)), read on the Def-6 torus (`0` for `j > k`). -/
noncomputable def psiJ (j : ℕ) : Def6.Fld S.d S.L C.N₁ m₁ k N :=
  if hj : j ≤ k then
    sfPull C.geo C.hT (psiSF (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L) (c := C.geo.c)
      (n := n k) C.weights (C.cs.mu k) (bgC0 S.d S.L N) hj (W2 R Y) (C.liftData ψk) (hC hv))
  else 0

/-- The level-`k` multiscale field of the single-scale action: `ψ_k` on the `k`-blocks. -/
noncomputable def psiLevelK : (m : ℕ) → LargeField.Blk S.d S.L (C.geo.M1 * (C.geo.c * n k)) k m →
    EuclideanSpace ℝ (Fin N) :=
  fun m y => if hm : m ≤ k then
    singleScale k ψk m (torusCast (histScale_eq C.geo.hM C.hnn hm C.hkK) y) else 0

open Classical in
/-- The fine sites of `A` on the level-`k` torus. -/
noncomputable def bgSet (A : Set (Torus S.d (n k))) : Finset (BgT C.geo k) :=
  Finset.univ.filter fun x => cubeMap n S.L M K k (bgToFine C.geo C.hnn C.hkK x) ∈ A

/-- **The single-scale action with half star bonds** `A*_k(Y; ψ_k, φ_k)` (P5 (1.5); generating
set `T^{(k)}_1`, weight `a_k`, mass `sfActMass`): `A_{T^{(k)}_1}(Y; ψ_k, φ̄_k) + ¼ ∑_{b ∈ st(Y)}
|∂φ̄_k(b)|²`, `A` the action of §II.4 (`actionG`). -/
noncomputable def actStar : ℝ :=
  actionG (levelGen (ϱ := (1 : ℝ)) k) C.weights (sfActMass C.cs k) hv (C.bgSet Y)
      (C.psiLevelK ψk) (C.phiBar Y ψk hv) +
    1 / 4 * starBondE (C.bgSet Y) (C.phiBar Y ψk hv)

open Classical in
/-- The `L^j`-aligned sites of the Def-6 torus in the fine set of `A` (the points
`y ∈ A ∩ T^{(j)}`). -/
noncomputable def alignedIn (j : ℕ) (A : Set (Torus S.d (n k))) :
    Finset (Localization.CTorus S.d S.L C.N₁ m₁ k) :=
  Finset.univ.filter fun y => Localization.Aligned (S.L ^ j) y ∧ y ∈ C.sset A

open Classical in
/-- **`ℰ^{(j)}(Y; ψ_j, h)`** (P5 (1.8)): the localized terms of `ℰ^{(j)}` with `y ∈ Y`,
`X ⊂ Y^≈`, minus the correction pair terms (the datum `corr`; open point, module docstring). -/
noncomputable def EresJ (j : ℕ) : ℂ :=
  (∑ y ∈ C.alignedIn j Y,
      ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) | Def6.IsPolyDom C.m₀ j X ∧
          y ∈ X ∧ X ⊆ C.sset (thickY R Y)},
        (C.sf.Tm C.N₁).E j y X (C.psiJ Y ψk hv j) (Def6.constFld (hC hv))) -
    ∑ y ∈ C.alignedIn j Y, ∑ x ∈ C.alignedIn j (thickY R Y),
      C.sf.corr C.N₁ j y x (C.psiJ Y ψk hv j) (Def6.constFld (hC hv))

/-- **`ℰ_k(Y; ψ_k, h) = ∑_{j=1}^k ℰ^{(j)}(Y; ψ^{(j)}_k, h)`** (P5 (1.7)). -/
noncomputable def EresK : ℂ := ∑ j ∈ Finset.Icc 1 k, C.EresJ Y ψk hv j

/-- **`𝒜_k(Y; ψ_k, h) = -β_k A*_k(Y; ψ_k, φ_k) + ℰ_k(Y; ψ_k, h) - E_k |Y|_k`** (P5 (1.6)).  As in
Definition II.5.4, `β_k A*_k` with `A*_k` in the units of scale `k` is
`β^{(k)}_0 (A + ¼ ∑_{st} |∂φ̄|²)` with the fine-unit action `A` and
`β^{(k)}_0 = β_k L^{-k(d-2)}` (`betaCanon`). -/
noncomputable def Ares : ℂ :=
  -((betaCanon S.d S.L (C.sf.β k) k 0 : ℝ) : ℂ) * ((C.actStar Y ψk hv : ℝ) : ℂ) +
    C.EresK Y ψk hv - ((C.sf.E C.N₁ * volK M Y : ℝ) : ℂ)

open Classical in
/-- **`ℳ^{(j)}(x, Y) = ∑_{X ∈ 𝒟_j, x ∈ X ⊂ Y^≈} ℳ^{(j)}(x, X)`** (P5 (1.13)). -/
noncomputable def MresJ (j : ℕ) (x : Localization.CTorus S.d S.L C.N₁ m₁ k) : Fin N → ℂ :=
  ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) | Def6.IsPolyDom C.m₀ j X ∧ x ∈ X ∧
      X ⊆ C.sset (thickY R Y)},
    (C.sf.Tm C.N₁).M j x X (C.psiJ Y ψk hv j) (Def6.constFld (hC hv))
      (sfG C.geo C.hnn C.hkK C.hT g)

open Classical in
/-- **`ℱ_k(Y; ψ_k, h, g) = ⟨χ_Y g, φ_k⟩₁ + ∑_{j=1}^k ⟨χ_Y g, ℳ^{(j)}(Y; ψ^{(j)}_k, h, g)⟩₁`**
(P5 (1.10)-(1.13)). -/
noncomputable def Fres : ℂ :=
  (∑ x ∈ C.bgSet Y, ∑ i : Fin N,
      g (bgToFine C.geo C.hnn C.hkK x, i) * (((C.phiBar Y ψk hv x) i : ℝ) : ℂ)) +
    ∑ j ∈ Finset.Icc 1 k, ∑ x : Localization.CTorus S.d S.L C.N₁ m₁ k,
      if x ∈ C.sset Y then
        ∑ i : Fin N, sfG C.geo C.hnn C.hkK C.hT g x i * C.MresJ Y ψk hv g j x i
      else 0

open Classical in
/-- **`ℛ^{(k)}(Y; ψ_k, h, g) = ∑_{n=1}^m ∑_{X ∈ 𝒟_k, X ⊂ Y} ℛ^{(k)}_n(X; ψ_k, h, g)`**
(P5 (1.16)-(1.17); `m = m₀ + m₁`, `L^m = M`). -/
noncomputable def Rres : ℂ :=
  ∑ nn ∈ Finset.Icc 1 (C.m₀ + m₁), ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) |
      Def6.IsPolyDom C.m₀ k X ∧ X ⊆ C.sset Y},
    C.sf.Rt C.N₁ nn X (sfLiftK C.geo C.hnn C.hkK C.hT ψk) (Def6.constFld (hC hv))
      (sfG C.geo C.hnn C.hkK C.hT g)

/-- **`χ_k(Y) = ∏_{□ ⊂ Y} χ_k(□)`** (Definition II.3.2 item 1; P5 (1.18)-(1.19)): weights
`a^{(k)}`, mass `cs.mu k` (the `h`-conditions are present only for a positive mass), tolerance
`δ_k = cs.delta k`. -/
noncomputable def chiY : ℝ :=
  cubeProd (fun y0 => chiK (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L) (q := k) (N := N)
      C.weights (C.cs.mu k) (C.cs.delta k) (fun i => hv i) C.geo.c (n k) y0)
    (cubeFin Y) (blockCfgOf C.geo C.hnn le_rfl C.hkK ψk)

/-- **The small-field factor of (D1)**: `χ_k(Y) exp(𝒜_k + ℱ_k + ℛ^{(k)})(Y; ψ_k, h, g)` on the
small-field region `Y = Z^c_k` of a history. -/
noncomputable def sfFactor : ℂ :=
  ((C.chiY Y ψk hv : ℝ) : ℂ) * Complex.exp (C.Ares Y ψk hv + C.Fres Y ψk hv g + C.Rres Y ψk hv g)

end SFCtx

end Restricted

end Balaban.LargeField.Def7
