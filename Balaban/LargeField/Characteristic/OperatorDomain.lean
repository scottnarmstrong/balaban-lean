module

public import Balaban.LargeField.History.LocalHistory
public import Balaban.LargeField.Background.StepGenSets
public import Balaban.Background.Data
public import Balaban.LargeField.Characteristic.Functions
import Mathlib.Tactic.Linarith

/-!
# The operator domain (Part II, Definition II.3.4; P5 (1.24)-(1.25))

For a component `Z` of `Z_k` with localized history `a` (fine sets, `LocalHistory`; note the index
shift `a.Omega j = Ω_{j+1} ∩ Z`, `a.OmegaDD j = Ω''_{j+1} ∩ Z`, `a.Z j = Z_j ∩ Z`), the
generating set `B = 𝔹_k` and a multiscale field `ψ`, the indicator `chiDom` of the conditions
(1.24)-(1.25).

*Blocks.* The multiscale field and the fluctuation field are indexed by the `j`-blocks of the
fine torus (`BlockPt`, the corners of `T^{(j)}`; `jBlock`), as in the source. (The index set
`InternalVars` of `Balaban/LargeField/Operators/Variables.lean` is indexed by cubes of `𝕋_j`; the
identification of the two indexings is the user's responsibility, see the handoff note.)

* `PsiTildeMulti` is `Ψ̃(Y; δ)`: for a set `Y` of blocks, `|ψ(y) - ψ(y')| < δ` for adjacent
  blocks of layers `n' ∈ {n, n - 1}` and `||ψ(y)|² - 1| < δ`;
* `genBlocksIn` is `𝔹_k ∩ □^∼` (the blocks of `B` with their layer), `scaleBlocksIn` is
  `T_j(□^∼)`;
* **`lhOmega`, `lhOmegaSim`**: Definition II.3.4 reads "the domains `Ω_j` of the lineage" of the
  localized history, i.e. of the lineage localization of the region history (Definition I.4.4,
  Lemma I.3.9 (b)), which contain the complement of the component (`Ωᶜ(loc) = Ωᶜ ∩ Lin`).  The
  records of `LocalHistory` are intersected with the component; `lhOmega a k j` adds the complement
  `(a.Z k)ᶜ`, and `lhOmegaSim` is the neighbourhood `Ω^∼_j` of these cubes.  The conditions (1.24)
  for a cube `□ ⊂ Ω^∼_{j+1}` at the boundary of the component thereby involve the blocks of its
  neighbours outside the component, whose field is the output `ψ_k` (Variables.lean).  This is
  what makes the domain identity of the proof of Lemma II.5.13 hold at the boundary cubes of an
  old part (`DomainIdentity.lean`).  `omegaNb`/`omegaSim` (records intersected with the component)
  remain for the quiet-kernel factors and the analyticity domain `H7Domain`.
* the cubes `□` are points of the cube torus `Torus d (n j)`, `□^∼ = nbhd 1 {□}`,
  `Ω^∼_{j} = nbhd 1 (cubes of Ω_j)` (`omegaSim`, with `Ω^∼_{k+1} := ∅`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory

set_option linter.unusedSectionVars false

section Dom

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]
  {ϱ : ℝ} {N : ℕ}

/-- A `j`-block of the level-`K` fine torus (the corner of a point of `T^{(j)}`). -/
abbrev BlockPt (S : Setting) (n : ℕ → ℕ) (M K : ℕ) : Type :=
  (j : ℕ) × Torus S.d (M * n K * S.L ^ (K - j))

/-- A field `y ↦ ψ_j(y) ∈ ℝ^N` on the `j`-blocks, for every scale `j`. -/
abbrev MultiField (S : Setting) (n : ℕ → ℕ) (M K N : ℕ) : Type :=
  (j : ℕ) → Torus S.d (M * n K * S.L ^ (K - j)) → EuclideanSpace ℝ (Fin N)

/-- Two blocks are adjacent if some of their sites are neighbours. -/
def BlockAdj (b b' : BlockPt S n M K) : Prop :=
  ∃ x x' : Torus S.d (M * n K * S.L ^ K),
    jBlock S.d S.L (M * n K) K b.1 x = b.2 ∧ jBlock S.d S.L (M * n K) K b'.1 x' = b'.2 ∧
      Adj x x'

/-- **`Ψ̃(Y; δ)`** (BG (R1)-(R2) on a set `Y` of blocks): `|ψ(y) - ψ(y')| < δ` for adjacent blocks
`y, y' ∈ Y` of layers `n' ∈ {n, n - 1}` (`b'.1 = b.1` or `b'.1 + 1 = b.1`) and
`||ψ(y)|² - 1| < δ` for `y ∈ Y`. -/
def PsiTildeMulti (ψ : MultiField S n M K N) (Y : Set (BlockPt S n M K)) (δ : ℝ) : Prop :=
  (∀ b ∈ Y, ∀ b' ∈ Y, (b'.1 = b.1 ∨ b'.1 + 1 = b.1) → BlockAdj b b' →
      ‖ψ b.1 b.2 - ψ b'.1 b'.2‖ < δ) ∧
    ∀ b ∈ Y, |‖ψ b.1 b.2‖ ^ 2 - 1| < δ

/-- The blocks of the generating set `B` (with their layers `1 ≤ j ≤ K`) whose cube at scale `j'`
lies in `W`: `𝔹_k ∩ W`. -/
def genBlocksIn (B : GeneratingSet S.d S.L (M * n K) K ϱ) (j' : ℕ)
    (W : Set (Torus S.d (n j'))) : Set (BlockPt S n M K) :=
  {b | 1 ≤ b.1 ∧ b.1 ≤ K ∧ ∃ x ∈ B.layer b.1, jBlock S.d S.L (M * n K) K b.1 x = b.2 ∧
    cubeMap n S.L M K j' x ∈ W}

/-- The `j`-blocks whose cube at scale `j` lies in `W`: `T_j(W)`. -/
def scaleBlocksIn (j : ℕ) (W : Set (Torus S.d (n j))) : Set (BlockPt S n M K) :=
  {b | ∃ y : Torus S.d (M * n K * S.L ^ (K - j)), b = ⟨j, y⟩ ∧
    ∃ x : Torus S.d (M * n K * S.L ^ K),
      jBlock S.d S.L (M * n K) K j x = y ∧ cubeMap n S.L M K j x ∈ W}

/-- All sites of the cube `y ∈ 𝕋_j` lie in the fine set `B`. -/
def CubeSub (M K j : ℕ) (y : Torus S.d (n j)) (B : Set (Torus S.d (M * n K * S.L ^ K))) : Prop :=
  ∀ x, cubeMap n S.L M K j x = y → x ∈ B

/-- All sites of the `j`-block `y` lie in the fine set `B`. -/
def BlockSub (j : ℕ) (y : Torus S.d (M * n K * S.L ^ (K - j)))
    (B : Set (Torus S.d (M * n K * S.L ^ K))) : Prop :=
  ∀ x, jBlock S.d S.L (M * n K) K j x = y → x ∈ B

variable (a : LocalHistory S n M K) (k : ℕ)

/-- `Ω^{∼r}_j` in the cube torus `𝕋_j`: the `r`-neighbourhood of the cubes of `Ω_j`
(`a.Omega (j - 1)`), with `Ω^{∼r}_{k+1} := ∅`. -/
def omegaNb (r j : ℕ) : Set (Torus S.d (n j)) :=
  if j = k + 1 then ∅ else nbhd r {y | CubeSub (S := S) (n := n) M K j y (a.Omega (j - 1))}

/-- `Ω^∼_j` (`r = 1`). -/
abbrev omegaSim (j : ℕ) : Set (Torus S.d (n j)) := omegaNb a k 1 j

/-- `Ω_j` of the *localized region history* of the component `Z` of `a` (the lineage localization
`locRH`, Lemma I.3.9 (b); Definition II.3.4 reads the domains `Ω_j` "of the lineage"), as fine
sites: the localized record `a.Omega (j - 1) = Ω_j ∩ Z` together with the complement of the
component, `(a.Z k)ᶜ` (`a.Z k` is the fine set of `Z` for the localized history of a component `Z`
of `Z_k`): the localized step has `Ω_j(loc) ⊇ Lin_j(Z)ᶜ`, so every site outside `Z` lies in
every `Ω_j(loc)`, `j ≤ k`. -/
def lhOmega (j : ℕ) : Set (Torus S.d (M * n K * S.L ^ K)) := a.Omega (j - 1) ∪ (a.Z k)ᶜ

/-- `Ω^{∼r}_j` of the localized region history: the `r`-neighbourhood of the cubes of `lhOmega`,
with `Ω^{∼r}_{k+1} := ∅`. -/
def lhOmegaNb (r j : ℕ) : Set (Torus S.d (n j)) :=
  if j = k + 1 then ∅ else nbhd r {y | CubeSub (S := S) (n := n) M K j y (lhOmega a k j)}

/-- `Ω^∼_j` of the localized region history (`r = 1`). -/
abbrev lhOmegaSim (j : ℕ) : Set (Torus S.d (n j)) := lhOmegaNb a k 1 j

variable (B : GeneratingSet S.d S.L (M * n K) K ϱ) (Zc : Set (Torus S.d (M * n K * S.L ^ K)))
  (δ p0 : ℕ → ℝ) (Cpsi : ℝ)

/-- **Definition II.3.4**, the condition (1.24)-(1.25) for the pair (multiscale field `ψ`,
fluctuation field `ψ'`): `Zc` is the fine set of the component `Z`, `δ j = δ_j`,
`p0 j = p_0(β_j)`, `Cpsi = C_{ψ'}`. -/
def ChiDomProp (ψ ψ' : MultiField S n M K N) : Prop :=
  (∀ j, j < k → ∀ y : Torus S.d (n (j + 1)),
      CubeSub (S := S) (n := n) M K (j + 1) y (a.Z (j + 1)) → y ∈ lhOmegaSim a k (j + 1) →
        PsiTildeMulti ψ (genBlocksIn B (j + 1) (nbhd 1 {y}))
          (3 * S.d * S.L * δ j)) ∧
  (∀ j, 1 ≤ j → j ≤ k → ∀ y : Torus S.d (n j),
      CubeSub (S := S) (n := n) M K j y Zc → (∀ x, cubeMap n S.L M K j x = y → x ∉ a.Z j) →
        (∀ x, cubeMap n S.L M K j x = y → cubeMap n S.L M K (j + 1) x ∉ lhOmegaSim a k (j + 1)) →
          PsiTildeMulti ψ (scaleBlocksIn j (nbhd 1 {y})) (3 * δ j)) ∧
  (∀ j, j < k → ∀ y : Torus S.d (M * n K * S.L ^ (K - j)),
      BlockSub (S := S) (n := n) j y (a.Omega j \ a.OmegaDD j) → ‖ψ' j y‖ < Cpsi * p0 j)

/-- `χ^{dom}_k(Z, 𝔞)(ψ, ψ')` (P5 (1.24)-(1.25)). -/
noncomputable def chiDom : MultiField S n M K N × MultiField S n M K N → ℝ :=
  charFn fun p => ChiDomProp a k B Zc δ p0 Cpsi p.1 p.2

end Dom

end Balaban.LargeField
