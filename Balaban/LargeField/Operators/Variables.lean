module

public import Balaban.LargeField.History.LocalRegion
public import Balaban.LargeField.Characteristic.OperatorDomain
public import Balaban.Frozen.Model.AprioriMeasure

/-!
# Variables of a localized history and the reference measure (Part II, Definition II.5.1)

**Indexing convention (block convention).**  The variables `ψ_j(y)` are indexed by the `j`-blocks
`y ∈ T^{(j)}` of the level-`K` fine torus, `y : Torus d (M * n K * L^(K-j))` (`BlockPt`, `jBlock`),
as in the source and as in the block-indexed `MultiField`, `MultiFieldC` and `H7Domain` of
`Balaban/LargeField/Characteristic/*`.  (The first version of this file indexed `ψ_j` by the *cubes*
of `𝕋_j`; a cube of `𝕋_j` contains `M^d` blocks of `T^{(j)}`, so that was wrong by that factor.)
The cube-indexed records of a localized history (fine sets, `LocalHistory`) are bridged to the block
convention by `blockCube` (the cube of `𝕋_j` containing a `j`-block), `cubeMap_jBlock`, and
`blockSub_fineSet_iff`: a block lies in the fine set of a set of cubes iff its cube does.

For a localized history `a` (fine sets, `LocalHistory`) and a level `k`:

* `InternalVars a k`: the index set `I(Z, 𝔞)` of the internal variables — for `0 ≤ j < k` the
  large-field variables `ψ_j(y)`, `y ∈ T^{(j)} ∩ Ω^c_{j+1} ∩ Z`, and the fluctuation variables
  `ψ'_j(y)`, `y ∈ T^{(j)} ∩ (Ω_{j+1} ∖ Ω''_{j+1}) ∩ Z`.  As all sets of a `LocalHistory` are
  already intersected with `Z`, `Ω^c_{j+1} ∩ Z` is `Z_{j+1} ∩ Z ∖ Ω_{j+1}` (Lemma I.3.5 (e):
  `Ω^c_{j+1} ⊂ Z_{j+1}`).  A block belongs to a fine set if all its fine sites do.
* **Localized region history (fix of the domain identity, W86).**  The localized history of a
  component `Z` of `Z_k` is, in the source, the *lineage localization* of the region history
  (Definition I.4.4, Lemma I.3.9): its domains `Ω_j`, `Ω''_j` are the global ones inside the lineage
  of `Z` and contain *everything outside it* (Lemma I.3.9 (b): `Ωᶜ(loc) = Ωᶜ ∩ Lin(Z)`).  The records
  of `LocalHistory` are intersected with `Z` (Definition II.5.1: "all sets are intersected with `Z`
  as fine sets"), which is right for the *variables* (they live in `Z`), but the multiscale field
  `ψ = ψ_j` on `Λ_j = Ω_j ∖ Ω_{j+1}` of Definition II.3.4 must be read with the `Ω_j` of the
  localized region history: outside `Z` and inside the margin `V_Z ∖ Z` the history is
  `Ω_1 ⊇ ⋯ ⊇ Ω_k`, so the field there is the output `ψ_k` on `V_Z` (Definition II.5.1, output
  variables on `T^{(k)} ∩ V_Z`; the proof of Lemma II.5.13 (3) treats "its outputs on `V_Y ∖ Y`" of an
  old part `Y` as parameters).  `lhOmega a k j = a.Omega (j - 1) ∪ (a.Z k)ᶜ` (OperatorDomain) is this
  `Ω_j`; the gate of `multiscaleField` and `subMultiscaleField` uses it.  (Before, the field
  vanished on the blocks of the margin that the generating set `𝔹_K` of the localization still
  contains, so `χ^dom_k(Z)` failed identically at the outer boundary cubes and the identity
  `χ^dom_{k+1}(Z') = χ^new_k(Z') ∏_Y χ^dom_k(Y)`, Lemma II.5.13, was false.)
* `refMeasure`: the product of the surface measures `volume.toSphere` (total mass `N v_N`, not
  normalized; D-IV.4) on the scale-`0` large-field variables (the spins) and Lebesgue measure on
  the others.
* `varField`, `fluctField`, `multiscaleField`: the large-field variable `ψ_j`, the fluctuation
  variable `ψ'_j`, and the multiscale field `ψ` as functions of the internal and output variables.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

/-- The unit sphere `S^{N-1} ⊂ ℝ^N`. -/
abbrev SpinSphere (N : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

/-- Values of a variable: spins (`true`) live on the sphere, all others in `ℝ^N`. -/
def VarVal (N : ℕ) : Bool → Type
  | true => SpinSphere N
  | false => EuclideanSpace ℝ (Fin N)

noncomputable instance (N : ℕ) : (b : Bool) → MeasurableSpace (VarVal N b)
  | true => inferInstanceAs (MeasurableSpace (SpinSphere N))
  | false => inferInstanceAs (MeasurableSpace (EuclideanSpace ℝ (Fin N)))

/-- The reference measure of one variable: `volume.toSphere` on the sphere (total mass `N v_N`),
Lebesgue measure on `ℝ^N`. -/
noncomputable def varMeasure (N : ℕ) : (b : Bool) → Measure (VarVal N b)
  | true => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere
  | false => (volume : Measure (EuclideanSpace ℝ (Fin N)))

instance (N : ℕ) : (b : Bool) → SigmaFinite (varMeasure N b)
  | true => by
      show SigmaFinite (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere
      infer_instance
  | false => by
      show SigmaFinite (volume : Measure (EuclideanSpace ℝ (Fin N)))
      infer_instance

/-- The value of a variable as a vector of `ℝ^N`. -/
def VarVal.toEuc {N : ℕ} : {b : Bool} → VarVal N b → EuclideanSpace ℝ (Fin N)
  | true, v => (show SpinSphere N from v).1
  | false, v => v

theorem VarVal.measurable_toEuc (N : ℕ) : ∀ b : Bool, Measurable (@VarVal.toEuc N b)
  | true => (measurable_subtype_coe (α := EuclideanSpace ℝ (Fin N))
      (p := fun x => x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1))
  | false => measurable_id

/-- The two kinds of internal variables. -/
inductive VarKind
  | large
  | fluct
  deriving DecidableEq

instance : Finite VarKind :=
  Finite.of_injective (fun k : VarKind => (k = VarKind.large : Prop)) (by
    intro a b h
    cases a <;> cases b <;> simp_all)

section Vars

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]

/-- The `j`-blocks of the level-`K` fine torus: the set `T^{(j)}`. -/
abbrev BlockAt (S : Setting) (n : ℕ → ℕ) (M K j : ℕ) : Type :=
  Torus S.d (M * n K * S.L ^ (K - j))

/-- The cube of `𝕋_j` containing a `j`-block. -/
def blockCube (S : Setting) (n : ℕ → ℕ) (M K j : ℕ) (y : BlockAt S n M K j) : Torus S.d (n j) :=
  blockMap M (n j) y

/-- Membership of a block of scale `j` in the variable set of the given kind. -/
def varSet (a : LocalHistory S n M K) (j : ℕ) :
    VarKind → Set (Torus S.d (M * n K * S.L ^ K))
  | .large => a.Z (j + 1) \ a.Omega j
  | .fluct => a.Omega j \ a.OmegaDD j

/-- The index set `I(Z, 𝔞)` of the internal variables of a localized history at level `k`:
the pairs (scale `j < k`, kind) with a `j`-block `y` all of whose sites lie in the variable set. -/
def InternalVars (a : LocalHistory S n M K) (k : ℕ) : Type :=
  {p : (j : Fin k) × VarKind × BlockAt S n M K j //
    BlockSub (S := S) (n := n) (M := M) (K := K) p.1 p.2.2 (varSet a p.1 p.2.1)}

noncomputable instance (a : LocalHistory S n M K) (k : ℕ) : Fintype (InternalVars a k) :=
  haveI : Finite (InternalVars a k) := by unfold InternalVars; infer_instance
  Fintype.ofFinite (InternalVars a k)

/-- Is the variable a spin (large-field variable of scale `0`)? -/
def InternalVars.isSpin {a : LocalHistory S n M K} {k : ℕ} (p : InternalVars a k) : Bool :=
  decide (p.1.1.val = 0 ∧ p.1.2.1 = VarKind.large)

/-- Configurations of the internal variables. -/
abbrev IntConfig (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) : Type :=
  (p : InternalVars a k) → VarVal N p.isSpin

/-- The reference measure `μ_{Z,𝔞}` on the internal variables (Definition II.5.1, D-IV.4). -/
noncomputable def refMeasure (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) :
    Measure (IntConfig N a k) :=
  Measure.pi fun p => varMeasure N p.isSpin

instance (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) : SigmaFinite (refMeasure N a k) := by
  unfold refMeasure; infer_instance

/-- Output variables `ψ_k(y)`, `y ∈ T^{(k)} ∩ V` (`V` a set of `k`-blocks). -/
abbrev OutConfig (N : ℕ) {α : Type} (V : Set α) : Type :=
  V → EuclideanSpace ℝ (Fin N)

/-- Lebesgue measure on the output variables (`V` finite). -/
noncomputable def outMeasure (N : ℕ) {α : Type} (V : Set α) [Finite V] :
    Measure (OutConfig N V) :=
  haveI := Fintype.ofFinite V
  Measure.pi fun _ => volume

open Classical in
/-- The large-field variable `ψ_j(y)` of the configuration `x` (zero where it is not a variable):
`j < k`, the block `y` lies in `Ω^c_{j+1} ∩ Z`. -/
noncomputable def varField (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) (x : IntConfig N a k)
    (j : ℕ) (y : BlockAt S n M K j) : EuclideanSpace ℝ (Fin N) :=
  if h : j < k ∧ BlockSub (S := S) (n := n) (M := M) (K := K) j y (varSet a j .large) then
    VarVal.toEuc (x ⟨⟨⟨j, h.1⟩, .large, y⟩, h.2⟩)
  else 0

open Classical in
/-- The fluctuation variable `ψ'_j(y)` (zero where it is not a variable). -/
noncomputable def fluctVarField (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) (x : IntConfig N a k)
    (j : ℕ) (y : BlockAt S n M K j) : EuclideanSpace ℝ (Fin N) :=
  if h : j < k ∧ BlockSub (S := S) (n := n) (M := M) (K := K) j y (varSet a j .fluct) then
    VarVal.toEuc (x ⟨⟨⟨j, h.1⟩, .fluct, y⟩, h.2⟩)
  else 0

open Classical in
/-- The output variable `ψ_k(y)` (zero off `V`). -/
noncomputable def outField (N : ℕ) {α : Type} {V : Set α} (o : OutConfig N V) (y : α) :
    EuclideanSpace ℝ (Fin N) :=
  if h : y ∈ V then o ⟨y, h⟩ else 0

open Classical in
/-- The multiscale field `ψ` of the history (II.3): `ψ_j` on `Λ_j = Ω_j ∖ Ω_{j+1}` for `j < k`
(`Ω_0` is everything), and `ψ_k` on `Ω_k ∩ V`; zero elsewhere. -/
noncomputable def multiscaleField (N : ℕ) (a : LocalHistory S n M K) (k : ℕ)
    (V : Set (BlockAt S n M K k)) (x : IntConfig N a k) (o : OutConfig N V) : MultiField S n M K N :=
  fun j y =>
    if j < k then
      if j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j y (lhOmega a k j) then
        varField N a k x j y
      else 0
    else if hjk : j = k then
      if j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j y (lhOmega a k j) then
        (by subst hjk; exact outField N o y) else 0
    else 0

/-- The fluctuation field `ψ'` of the configuration. -/
noncomputable def fluctField (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) (x : IntConfig N a k) :
    MultiField S n M K N :=
  fun j y => fluctVarField N a k x j y

/-! ### Measurability of the readers -/

theorem measurable_varField (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) (j : ℕ)
    (y : BlockAt S n M K j) : Measurable fun x : IntConfig N a k => varField N a k x j y := by
  classical
  unfold varField
  by_cases h : j < k ∧ BlockSub (S := S) (n := n) (M := M) (K := K) j y (varSet a j .large)
  · simp only [h]
    exact (VarVal.measurable_toEuc N _).comp (measurable_pi_apply _)
  · simp only [h, ↓reduceDIte]
    exact measurable_const

theorem measurable_fluctVarField (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) (j : ℕ)
    (y : BlockAt S n M K j) : Measurable fun x : IntConfig N a k => fluctVarField N a k x j y := by
  classical
  unfold fluctVarField
  by_cases h : j < k ∧ BlockSub (S := S) (n := n) (M := M) (K := K) j y (varSet a j .fluct)
  · simp only [h]
    exact (VarVal.measurable_toEuc N _).comp (measurable_pi_apply _)
  · simp only [h, ↓reduceDIte]
    exact measurable_const

theorem measurable_outField (N : ℕ) {α : Type} (V : Set α) (y : α) :
    Measurable fun o : OutConfig N V => outField N o y := by
  classical
  unfold outField
  by_cases h : y ∈ V
  · simp only [h, ↓reduceDIte]
    exact measurable_pi_apply _
  · simp only [h, ↓reduceDIte]
    exact measurable_const

theorem measurable_multiscaleField (N : ℕ) (a : LocalHistory S n M K) (k : ℕ)
    (V : Set (BlockAt S n M K k)) (j : ℕ) (y : BlockAt S n M K j) :
    Measurable fun p : IntConfig N a k × OutConfig N V => multiscaleField N a k V p.1 p.2 j y := by
  classical
  unfold multiscaleField
  by_cases hj : j < k
  · simp only [hj, ↓reduceIte]
    by_cases hc : j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j y (lhOmega a k j)
    · simp only [hc, ↓reduceIte]
      exact (measurable_varField N a k j y).comp measurable_fst
    · simp only [hc, ↓reduceIte]
      exact measurable_const
  · simp only [hj, ↓reduceIte]
    by_cases hjk : j = k
    · subst hjk
      simp only [↓reduceDIte]
      by_cases hc : j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j y (lhOmega a j j)
      · simp only [hc, ↓reduceIte]
        exact (measurable_outField N V y).comp measurable_snd
      · simp only [hc, ↓reduceIte]
        exact measurable_const
    · simp only [hjk, ↓reduceDIte]
      exact measurable_const

theorem measurable_fluctField (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) (j : ℕ)
    (y : BlockAt S n M K j) :
    Measurable fun x : IntConfig N a k => fluctField N a k x j y :=
  measurable_fluctVarField N a k j y


/-! ### Configurations of a subset of the internal variables

An operator integrates over a subset `A ⊆ I(Z, 𝔞)` of the internal variables (the variables of a
kept ancestor outside `I''` are not integrated, Definition II.5.7 (S3)).  `SubCfg` is the space
of configurations of `A` with its reference measure `subMeasure`. -/

section Sub

variable {N : ℕ} {a : LocalHistory S n M K} {k : ℕ}

/-- Configurations of the variables in `A ⊆ I(Z, 𝔞)`. -/
abbrev SubCfg (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) (A : Set (InternalVars a k)) : Type :=
  (p : A) → VarVal N p.1.isSpin

noncomputable instance (A : Set (InternalVars a k)) : Fintype A := Fintype.ofFinite A

/-- The reference measure on the variables in `A`. -/
noncomputable def subMeasure (N : ℕ) (a : LocalHistory S n M K) (k : ℕ)
    (A : Set (InternalVars a k)) : Measure (SubCfg N a k A) :=
  Measure.pi fun p => varMeasure N p.1.isSpin

instance (A : Set (InternalVars a k)) : SigmaFinite (subMeasure N a k A) := by
  unfold subMeasure; infer_instance

/-- Restriction of a configuration to a subset of its variables. -/
def restrictSub {A B : Set (InternalVars a k)} (h : A ⊆ B) (x : SubCfg N a k B) : SubCfg N a k A :=
  fun p => x ⟨p.1, h p.2⟩

theorem measurable_restrictSub {A B : Set (InternalVars a k)} (h : A ⊆ B) :
    Measurable (restrictSub (N := N) h) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- The internal variable `(j, κ, y)` of a block `y` of scale `j < k` in the variable set. -/
def mkVar (a : LocalHistory S n M K) (k j : ℕ) (κ : VarKind) (y : BlockAt S n M K j) (hj : j < k)
    (hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y (varSet a j κ)) : InternalVars a k :=
  ⟨⟨⟨j, hj⟩, κ, y⟩, hb⟩

open Classical in
/-- The large-field variable `ψ_j(y)` read from a configuration of `A` (zero where it is not a
variable of `A`). -/
noncomputable def subVarField (N : ℕ) {a : LocalHistory S n M K} {k : ℕ}
    {A : Set (InternalVars a k)} (x : SubCfg N a k A) (j : ℕ) (y : BlockAt S n M K j) :
    EuclideanSpace ℝ (Fin N) :=
  if h : ∃ hj : j < k, ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y (varSet a j .large),
      mkVar a k j .large y hj hb ∈ A then
    VarVal.toEuc (x ⟨mkVar a k j .large y h.1 h.2.1, h.2.2⟩)
  else 0

open Classical in
/-- The fluctuation variable `ψ'_j(y)` read from a configuration of `A`. -/
noncomputable def subFluctVarField (N : ℕ) {a : LocalHistory S n M K} {k : ℕ}
    {A : Set (InternalVars a k)} (x : SubCfg N a k A) (j : ℕ) (y : BlockAt S n M K j) :
    EuclideanSpace ℝ (Fin N) :=
  if h : ∃ hj : j < k, ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y (varSet a j .fluct),
      mkVar a k j .fluct y hj hb ∈ A then
    VarVal.toEuc (x ⟨mkVar a k j .fluct y h.1 h.2.1, h.2.2⟩)
  else 0

theorem measurable_subVarField {A : Set (InternalVars a k)} (j : ℕ) (y : BlockAt S n M K j) :
    Measurable fun x : SubCfg N a k A => subVarField N x j y := by
  classical
  unfold subVarField
  by_cases h : ∃ hj : j < k, ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y
      (varSet a j .large), mkVar a k j .large y hj hb ∈ A
  · simp only [h]
    exact (VarVal.measurable_toEuc N _).comp (measurable_pi_apply _)
  · simp only [h, ↓reduceDIte]
    exact measurable_const

theorem measurable_subFluctVarField {A : Set (InternalVars a k)} (j : ℕ) (y : BlockAt S n M K j) :
    Measurable fun x : SubCfg N a k A => subFluctVarField N x j y := by
  classical
  unfold subFluctVarField
  by_cases h : ∃ hj : j < k, ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y
      (varSet a j .fluct), mkVar a k j .fluct y hj hb ∈ A
  · simp only [h]
    exact (VarVal.measurable_toEuc N _).comp (measurable_pi_apply _)
  · simp only [h, ↓reduceDIte]
    exact measurable_const

open Classical in
/-- The multiscale field of a configuration of `A` and an output configuration. -/
noncomputable def subMultiscaleField (N : ℕ) (a : LocalHistory S n M K) (k : ℕ)
    (V : Set (BlockAt S n M K k)) {A : Set (InternalVars a k)} (x : SubCfg N a k A)
    (o : OutConfig N V) : MultiField S n M K N :=
  fun j y =>
    if j < k then
      if j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j y (lhOmega a k j) then
        subVarField N x j y
      else 0
    else if hjk : j = k then
      if j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j y (lhOmega a k j) then
        (by subst hjk; exact outField N o y) else 0
    else 0

/-- The fluctuation field of a configuration of `A`. -/
noncomputable def subFluctField (N : ℕ) (a : LocalHistory S n M K) (k : ℕ)
    {A : Set (InternalVars a k)} (x : SubCfg N a k A) : MultiField S n M K N :=
  fun j y => subFluctVarField N x j y

theorem measurable_subMultiscaleField (V : Set (BlockAt S n M K k)) {A : Set (InternalVars a k)}
    (j : ℕ) (y : BlockAt S n M K j) :
    Measurable fun p : SubCfg N a k A × OutConfig N V =>
      subMultiscaleField N a k V p.1 p.2 j y := by
  classical
  unfold subMultiscaleField
  by_cases hj : j < k
  · simp only [hj, ↓reduceIte]
    by_cases hc : j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j y (lhOmega a k j)
    · simp only [hc, ↓reduceIte]
      exact (measurable_subVarField j y).comp measurable_fst
    · simp only [hc, ↓reduceIte]
      exact measurable_const
  · simp only [hj, ↓reduceIte]
    by_cases hjk : j = k
    · subst hjk
      simp only [↓reduceDIte]
      by_cases hc : j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j y (lhOmega a j j)
      · simp only [hc, ↓reduceIte]
        exact (measurable_outField N V y).comp measurable_snd
      · simp only [hc, ↓reduceIte]
        exact measurable_const
    · simp only [hjk, ↓reduceDIte]
      exact measurable_const

theorem measurable_subFluctField {A : Set (InternalVars a k)} (j : ℕ) (y : BlockAt S n M K j) :
    Measurable fun x : SubCfg N a k A => subFluctField N a k x j y :=
  measurable_subFluctVarField j y

end Sub

/-! ### The bridge between the cube and the block convention -/

section Bridge



/-- A site of the fine torus lying in a given block of scale `j ≤ K` exists. -/
theorem exists_site_in_block {j : ℕ} (hjK : j ≤ K)
    (y : BlockAt S n M K j) :
    ∃ x : Torus S.d (M * n K * S.L ^ K), Multiscale.jBlock S.d S.L (M * n K) K j x = y := by
  classical
  have hmy : NeZero (M * n K * S.L ^ (K - j)) := inferInstance
  have hℓ : M * n K * S.L ^ K = S.L ^ j * (M * n K * S.L ^ (K - j)) := Multiscale.side_eq hjK
  have hpos : 0 < S.L ^ j := Nat.pos_of_ne_zero (by have := NeZero.ne S.L; positivity)
  refine ⟨fun i => (((y i).val * S.L ^ j : ℕ) : ZMod (M * n K * S.L ^ K)), ?_⟩
  funext i
  unfold Multiscale.jBlock blockMap blockCoord
  have hlt : (y i).val * S.L ^ j < M * n K * S.L ^ K := by
    rw [hℓ, mul_comm (S.L ^ j)]
    exact Nat.mul_lt_mul_of_pos_right (ZMod.val_lt (y i)) hpos
  rw [ZMod.val_natCast_of_lt hlt, Nat.mul_div_cancel _ hpos]
  exact ZMod.natCast_zmod_val (y i)

/-- The cube of a site is the cube of its `j`-block. -/
theorem cubeMap_jBlock (hnn : ∀ i, n i = S.L * n (i + 1)) {j : ℕ} (hjK : j ≤ K)
    (x : Torus S.d (M * n K * S.L ^ K)) :
    blockCube S n M K j (Multiscale.jBlock S.d S.L (M * n K) K j x) = cubeMap n S.L M K j x :=
  cubeMap_eq_comp hnn hjK x

/-- **The bridge.** A block lies in the fine set of a set of cubes iff its cube does. -/
theorem blockSub_fineSet_iff (hnn : ∀ i, n i = S.L * n (i + 1)) {j : ℕ} (hjK : j ≤ K)
    (A : Set (Torus S.d (n j))) (y : BlockAt S n M K j) :
    BlockSub (S := S) (n := n) (M := M) (K := K) j y (fineSet (S := S) (n := n) M K j A) ↔
      blockCube S n M K j y ∈ A := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := exists_site_in_block hjK y
    have := h x hx
    simpa [fineSet, ← cubeMap_jBlock hnn hjK x, hx] using this
  · intro h x hx
    show cubeMap n S.L M K j x ∈ A
    rw [← cubeMap_jBlock hnn hjK x, hx]
    exact h

theorem blockSub_inter (j : ℕ) (y : BlockAt S n M K j) (A B : Set (Torus S.d (M * n K * S.L ^ K))) :
    BlockSub (S := S) (n := n) (M := M) (K := K) j y (A ∩ B) ↔
      BlockSub (S := S) (n := n) (M := M) (K := K) j y A ∧
        BlockSub (S := S) (n := n) (M := M) (K := K) j y B :=
  ⟨fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩,
    fun h x hx => ⟨h.1 x hx, h.2 x hx⟩⟩

end Bridge

section LocalFacts

variable {R : ℕ → ℝ} {k0 : ℕ} {H : RegionHistory S n R k0}

/-- The record `Z_k` of the localized history of a component `Z` of `Z_k` is the fine set of `Z`. -/
theorem mem_localHistory_Z_top {k : ℕ} (Z : H.Comp k) (x : Torus S.d (M * n K * S.L ^ K)) :
    x ∈ (H.localHistory M K k Z).Z k ↔ cubeMap n S.L M K k x ∈ Z.1 := by
  show (cubeMap n S.L M K k x ∈ ((H.locRH k Z).step k).Z ∧ cubeMap n S.L M K k x ∈ Z.1) ↔ _
  rw [locRH_Z Z le_rfl, lin_self]
  simp

/-- A site outside the fine set of `Z` lies in `lhOmega`. -/
theorem mem_lhOmega_of_not_mem {a : LocalHistory S n M K} {k : ℕ} (j : ℕ)
    {x : Torus S.d (M * n K * S.L ^ K)} (hx : x ∉ a.Z k) : x ∈ lhOmega a k j :=
  Or.inr hx

end LocalFacts

end Vars

end Balaban.LargeField
