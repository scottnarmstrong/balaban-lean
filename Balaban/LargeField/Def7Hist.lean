module

public import Balaban.LargeField.Operators.LocOpBound
public import Balaban.LargeField.Geometry.DomainsMod
public import Balaban.LargeField.Region.SymmStep

/-!
# Def-7, part 1: histories, global operators, boundary domains — DRAFT

LF-RECONSTRUCTION v1.3, §II.6.1 (the history set `𝔄` of a representation) and Definition II.5.8
(the global operators `𝕋_k(Z_k, 𝔸) = ⨂_Z 𝕋_k(Z, 𝔸 ∩ Z)`), on the landed finite-horizon histories
`RegionHistory S n R k₀ K` and the localized operators `locOp`.

* `LabHist`: a global history `𝔸` with its `R`-records: an admissible region history (its
  removed components are ripe, Definition I.4.1) and the labels `ϰ ∈ 𝔎 = Fin 5` of the kept
  components (Definition II.5.7 (S3)).
* `LabHist.Agree k r`: two histories have the same records up to scale `k` (the step records of
  the steps `j → j + 1`, `j < k`, and the `R`-records with the kept labels at the scales
  `j < r`; `r = k + 1` for the post-`R` class, `r = k` for the pre-`R` class, which has no
  `R`-record at scale `k`).  A landed `RegionHistory` carries steps at every scale (geometry-free
  beyond the horizon), so a *history up to scale `k`* is an `Agree`-class.
* `IsComplete k r 𝔄`: `𝔄` contains exactly one history of every class — §II.6.1: "`𝔄`: **the
  set of all** admissible global region histories up to scale `k`"; `exists_isComplete`: such a
  finite set exists (the classes are finite: `finite_agreeQuot`).
* `PostComp`, `postOp`, `preOpTop`: the components of `Z_k(𝔸)` (resp. `Z^pre_k(𝔸)`) and their
  operators `𝕋_k(Z, 𝔸 ∩ Z)` (resp. `𝕋^pre_k`).
* `gMeasure`, `gWeight`, `gOp`, `GConv`: the global operator on a finite family of components
  (the product kernel of Lemma II.5.3 (a) on the product of the reference measures).
* `gMulti`, `gFluct`: the global multiscale field `ψ` (`ψ_j` on `Λ_j`, Definition II.5.1) and
  fluctuation field `ψ'` read from `ψ_k` and the internal variables of all components.
* `OmegaCube`, `IsBdryDom`, `bdryDoms`: the localization domains `X ∈ 𝒟_k(mod Ω^c_k(𝔸))` with
  `X ∩ Z ≠ ∅ ≠ X ∩ Zᶜ` of the boundary terms (P5 (1.38)).
* `dCovMod`: a cube-level modular covering size (continuous segments through closed cubes, chosen
  cover).  It is the size in the bound of the pre-`R` records `D7Bdry`, `D7Bdry2` only; the
  post-`R` records use the fine size `d7Size` of `Def7FineSize`.
* `globalLH`: the records of a global history as fine sets (the history argument of
  `H7Domain`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Def7

open MeasureTheory Balaban RegionHistory

/-! ### Histories with `R`-records -/

section Hist

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-- **A global history `𝔸` with its `R`-records** (LFR §II.6.1, Definition I.4.1): an
admissible region history (each removed component of `Z^pre_j` is ripe; the overwrite of
Definition I.3.11 is the lineage localization of the landed `localHistory`) together with the
labels `ϰ ∈ 𝔎 = Fin 5` of its kept components (the ripe components of `Z^pre_j`,
`1 ≤ j ≤ k₀`, that are not removed; Definition II.5.7 (S3), Part III Definition III.5.2).  The
values of `lab` at the other components are never read (`keptLab`). -/
structure LabHist (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (R : ℕ → ℝ) (k0 K : ℕ) where
  /-- the region history -/
  H : RegionHistory S n R k0 K
  /-- the removed components are ripe -/
  adm : H.Admissible
  /-- the labels of the kept components (a function of the component's set of cubes) -/
  lab : ∀ j, Finset (Torus S.d (n j)) → Fin 5

open Classical in
/-- The kept-label record of `𝔸` at scale `j`: `some ϰ` at a kept component (ripe, not removed,
`1 ≤ j ≤ k₀`) with label `ϰ`, `none` at every other finite set of cubes. -/
noncomputable def LabHist.keptLab (A : LabHist S n R k0 K) (j : ℕ)
    (c : Finset (Torus S.d (n j))) : Option (Fin 5) :=
  if h : c ∈ comps (S.omega j) (A.H.Zp j) then
    if IsKept A.H j ⟨c, h⟩ ∧ c ∉ A.H.rem j then some (A.lab j c) else none
  else none

/-- **Equality of records up to scale `k`**: the step records `(P, Q, R, S)` of the steps
`j → j + 1`, `j < k`, and the `R`-records (`Rem_j` and the kept labels) at the scales `j < r`.
Two histories with the same records are the same history up to scale `k` (Definition I.4.1:
the regions `Z_j`, `Z^pre_j` and the bookkeeping are functions of the records). -/
def LabHist.Agree (k r : ℕ) (A B : LabHist S n R k0 K) : Prop :=
  (∀ j, j < k → (A.H.step j).P = (B.H.step j).P ∧ (A.H.step j).Q = (B.H.step j).Q ∧
      (A.H.step j).R = (B.H.step j).R ∧ (A.H.step j).S = (B.H.step j).S) ∧
    ∀ j, j < r → A.H.rem j = B.H.rem j ∧ A.keptLab j = B.keptLab j

/-- The records of a history up to scale `k` (with `R`-records below `r`), as an element of a
finite type. -/
abbrev Rec (S : Setting) (n : ℕ → ℕ) (k r : ℕ) : Type :=
  ((j : Fin k) → Set (Torus S.d (n (j + 1))) × Set (Torus S.d (n (j + 1))) ×
      Set (Torus S.d (n (j + 1))) × Set (Torus S.d (n (j + 1)))) ×
    ((j : Fin r) → Finset (Finset (Torus S.d (n j))) ×
      (Finset (Torus S.d (n j)) → Option (Fin 5)))

/-- The records of `𝔸` up to scale `k`. -/
noncomputable def LabHist.records (k r : ℕ) (A : LabHist S n R k0 K) : Rec S n k r :=
  (fun j => ((A.H.step j).P, (A.H.step j).Q, (A.H.step j).R, (A.H.step j).S),
    fun j => (A.H.rem j, A.keptLab j))

theorem LabHist.agree_iff_rec (k r : ℕ) (A B : LabHist S n R k0 K) :
    A.Agree k r B ↔ A.records k r = B.records k r := by
  constructor
  · rintro ⟨h1, h2⟩
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · obtain ⟨a, b, c, d⟩ := h1 j j.2
      simp only [LabHist.records, a, b, c, d]
    · obtain ⟨a, b⟩ := h2 j j.2
      simp only [LabHist.records, a, b]
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have := congrFun (congrArg Prod.fst h) ⟨j, hj⟩
      simpa only [LabHist.records, Prod.mk.injEq] using this
    · have := congrFun (congrArg Prod.snd h) ⟨j, hj⟩
      simpa only [LabHist.records, Prod.mk.injEq] using this

theorem LabHist.agree_refl (k r : ℕ) (A : LabHist S n R k0 K) : A.Agree k r A :=
  (A.agree_iff_rec k r A).mpr rfl

theorem LabHist.agree_symm {k r : ℕ} {A B : LabHist S n R k0 K} (h : A.Agree k r B) :
    B.Agree k r A :=
  (B.agree_iff_rec k r A).mpr ((A.agree_iff_rec k r B).mp h).symm

theorem LabHist.agree_trans {k r : ℕ} {A B C : LabHist S n R k0 K} (h : A.Agree k r B)
    (h' : B.Agree k r C) : A.Agree k r C :=
  (A.agree_iff_rec k r C).mpr
    (((A.agree_iff_rec k r B).mp h).trans ((B.agree_iff_rec k r C).mp h'))

/-- The equivalence relation "same history up to scale `k`". -/
def agreeSetoid (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (R : ℕ → ℝ) (k0 K k r : ℕ) :
    Setoid (LabHist S n R k0 K) where
  r := LabHist.Agree k r
  iseqv := ⟨LabHist.agree_refl k r, LabHist.agree_symm, LabHist.agree_trans⟩

/-- The histories up to scale `k` are finitely many. -/
theorem finite_agreeQuot (k r : ℕ) : Finite (Quotient (agreeSetoid S n R k0 K k r)) :=
  Finite.of_injective
    (Quotient.lift (LabHist.records k r) fun A B h => (A.agree_iff_rec k r B).mp h)
    (by
      rintro ⟨A⟩ ⟨B⟩ h
      exact Quotient.sound ((A.agree_iff_rec k r B).mpr h))

/-- **`𝔄` is the set of all histories up to scale `k`** (§II.6.1; P5's "maximal set of the
multi-indices", p. 494): every global history agrees up to scale `k` with exactly one element of
`𝔄`. -/
def IsComplete (k r : ℕ) (𝔄 : Finset (LabHist S n R k0 K)) : Prop :=
  ∀ A : LabHist S n R k0 K, ∃! B, B ∈ 𝔄 ∧ A.Agree k r B

/-- A complete finite set of histories up to scale `k` exists. -/
theorem exists_isComplete (k r : ℕ) : ∃ 𝔄 : Finset (LabHist S n R k0 K), IsComplete k r 𝔄 := by
  classical
  have := finite_agreeQuot (S := S) (n := n) (R := R) (k0 := k0) (K := K) k r
  have := Fintype.ofFinite (Quotient (agreeSetoid S n R k0 K k r))
  refine ⟨Finset.univ.image fun q : Quotient (agreeSetoid S n R k0 K k r) => q.out,
    fun A => ⟨(⟦A⟧ : Quotient
    (agreeSetoid S n R k0 K k r)).out, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩⟩
  · exact LabHist.agree_symm (Quotient.mk_out (s := agreeSetoid S n R k0 K k r) A)
  · rintro B ⟨hB, hAB⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hB
    have h1 : (⟦A⟧ : Quotient (agreeSetoid S n R k0 K k r)) = ⟦q.out⟧ := Quotient.sound hAB
    rw [Quotient.out_eq] at h1
    rw [h1]

/-- The components of `Z_k(𝔸)`: the components of `Z^pre_k` that are not removed by
`R^{(k)}`. -/
abbrev PostComp (A : LabHist S n R k0 K) (k : ℕ) : Type := {c : A.H.Comp k // c.1 ∉ A.H.rem k}

noncomputable instance (A : LabHist S n R k0 K) (k : ℕ) : Fintype (PostComp A k) :=
  Fintype.ofFinite _

/-- `Ω_j(𝔸)` as a set of cubes of `𝕋_j` (`Ω_0 = 𝕋_0`; `Ω_{j+1}` is produced by the step
`j → j + 1`). -/
def OmegaCube (H : RegionHistory S n R k0 K) : ∀ j, Set (Torus S.d (n j))
  | 0 => Set.univ
  | j + 1 => (H.step j).Omega

end Hist

/-! ### The global operator of a finite family of components -/

section Global

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- The output variables `ψ_k` on `T^{(k)} ∩ V` of a localized history, read from a field `ψ_k`
on all `k`-blocks. -/
def outOf (R : ℕ → ℝ) (b : LocalHistory S n M K) (k : ℕ)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) : OutT N R b k :=
  fun y => ψk y.1

variable {ι : Type} [Fintype ι] (a : ι → LocalHistory S n M K) (k : ℕ)
  (P : ∀ i, OpPkg N R (a i) k)

/-- The configurations of the internal variables of all components of the family. -/
abbrev GCfg : Type := (i : ι) → SubCfg N (a i) k (P i).A

/-- The reference measure of the family: the product of the reference measures
`μ_{Z, 𝔸 ∩ Z}` of the components (Definition II.5.1). -/
noncomputable def gMeasure : Measure (GCfg a k P) :=
  Measure.pi fun i => subMeasure N (a i) k (P i).A

/-- The product kernel `∏_Z K_Z e^{b_Z}` of the family at `(ψ_k, x; h, g)` (Lemma II.5.3 (a)). -/
noncomputable def gWeight (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) (x : GCfg a k P) : ℂ :=
  ∏ i, (P i).T.w (outOf R (a i) k ψk) (x i) hv g

/-- **The global operator** `𝕋_k(Z_k, 𝔸) F (ψ_k) = ∫ ∏_Z K_Z e^{b_Z} F dμ` (Definition II.5.8,
last item; P5 (1.21)-(1.22)). -/
noncomputable def gOp (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) (F : GCfg a k P → ℂ) : ℂ :=
  ∫ x, gWeight a k P ψk hv g x * F x ∂(gMeasure a k P)

/-- The integral defining `gOp` converges absolutely. -/
def GConv (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (F : GCfg a k P → ℂ) : Prop :=
  Integrable (fun x => gWeight a k P ψk hv g x * F x) (gMeasure a k P)

open Classical in
/-- **The global multiscale field** `ψ` of the configuration (Definition II.5.1, P5 p. 492):
for `j < k`, on a block of a component the multiscale field of that component (`ψ_j` on
`Λ_j = Ω_j ∖ Ω_{j+1}`; for `j < k`, `Λ_j ⊂ Ω^c_{j+1} ⊂ Z_k` lies in the components); for
`j = k`, the output `ψ_k` on the blocks of `Ω_k` (`Om`, the fine set of `Ω_k(𝔸)`); zero
elsewhere.  `car i` is the fine set of the component `i`. -/
noncomputable def gMulti (car : ι → Set (Torus S.d (M * n K * S.L ^ K)))
    (Om : Set (Torus S.d (M * n K * S.L ^ K)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (x : GCfg a k P) :
    MultiField S n M K N :=
  fun j y =>
    if j < k then
      (if h : ∃ i, BlockSub (S := S) (n := n) (M := M) (K := K) j y (car i) then
        subMultiscaleField N (a h.choose) k (Vblk R (a h.choose) k) (x h.choose)
          (outOf R (a h.choose) k ψk) j y
      else 0)
    else if hjk : j = k then
      (if BlockSub (S := S) (n := n) (M := M) (K := K) j y Om then
        (by subst hjk; exact ψk y) else 0)
    else 0

open Classical in
/-- **The global fluctuation field** `ψ'`: on a block of a component, the fluctuation variable
of that component (Definition II.5.1); zero elsewhere. -/
noncomputable def gFluct (car : ι → Set (Torus S.d (M * n K * S.L ^ K))) (x : GCfg a k P) :
    MultiField S n M K N :=
  fun j y =>
    if h : ∃ i, BlockSub (S := S) (n := n) (M := M) (K := K) j y (car i) then
      subFluctField N (a h.choose) k (x h.choose) j y
    else 0

end Global

/-- The complexification of a real block field. -/
def MultiField.toC {S : Setting} {n : ℕ → ℕ} {M K N : ℕ} (ψ : MultiField S n M K N) :
    MultiFieldC S n M K N :=
  fun j y i => ((ψ j y) i : ℂ)

/-! ### The operators of a history -/

section Ops

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (geo : Geo S n R M) (cs : OpConsts) {κs κ : ℕ → LocalHistory S n M K → ℝ}
  {lamHat : ℕ → ℝ} (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ lamHat)

/-- **The post-`R` operators** `𝕋_k(Z, 𝔸 ∩ Z)` of the components `Z` of `Z_k(𝔸)`
(Definition II.5.8, second item; the kept components carry the kept kernel with their label). -/
noncomputable def postOp (A : LabHist S n R k0 K) {k : ℕ} (hk : k ≤ K) (c : PostComp A k) :
    OpPkg N R (A.H.localHistory M K k c.1) k :=
  locOp geo cs SD KD A.adm (fun j c => A.lab j c.1) k hk c.1

/-- **The pre-`R` operators** `𝕋^pre_k(Z, 𝔸 ∩ Z)` of the components `Z` of `Z^pre_k(𝔸)`
(Definition II.5.8, first item): the step kernel `(K_{k-1}, b_{k-1})(Z)` composed with the
post-`R` operators of the old parts.  There are no components at `k = 0`. -/
noncomputable def preOpTop (A : LabHist S n R k0 K) :
    ∀ (k : ℕ), k ≤ K → (Z : A.H.Comp k) → OpPkg N R (A.H.localHistory M K k Z) k
  | 0, _, Z => (A.H.F.isEmpty_comp_zero.false Z).elim
  | k + 1, hk, Z' => preOp geo cs SD A.adm hk Z'
      (fun Y _ => locOp geo cs SD KD A.adm (fun j c => A.lab j c.1) k (by omega) Y)

end Ops

/-! ### Boundary domains, the covering size, the global records -/

section Bdry

variable {d n : ℕ}

/-- **The localization domains of the boundary terms** (P5 (1.38); §II.6.1): `X ∈ 𝒟_k(mod Ω^c)`
(`DmodOmega`, Definition I.2.15) meeting both `Z` and its complement (`Z = Z_k(𝔸)`, resp.
`Z^pre_k(𝔸)` for the pre-`R` class). -/
def IsBdryDom (Om Z : Set (Torus d n)) (X : Finset (Torus d n)) : Prop :=
  DmodOmega Om X ∧ ((X : Set (Torus d n)) ∩ Z).Nonempty ∧ ((X : Set (Torus d n)) \ Z).Nonempty

open Classical in
/-- The finite set of the boundary domains. -/
noncomputable def bdryDoms [NeZero n] (Om Z : Set (Torus d n)) : Finset (Finset (Torus d n)) :=
  Finset.univ.filter (IsBdryDom Om Z)

theorem mem_bdryDoms [NeZero n] {Om Z : Set (Torus d n)} {X : Finset (Torus d n)} :
    X ∈ bdryDoms Om Z ↔ IsBdryDom Om Z X := by
  classical
  simp [bdryDoms]

/-- An admissible curve for the cube-level size `dCovMod`: a set `𝒦` of `L`-blocks of cubes with
corners at the multiples of `L`, contained in `X`, whose union covers `X ∩ Ω`, and a connected
finite union of straight segments of the continuous torus inside the union `⋃_{x ∈ X} □_x` of the
*closed* cubes of `X`, meeting every chosen block.  (Two blocks of `X` whose closed cubes share
only a corner are met by the single corner point, a segment of length `0`.) -/
def IsCovCurve [NeZero n] (L : ℕ) (Ω : Set (Torus d n)) (X : Finset (Torus d n))
    (𝒦 : Set (Torus d n)) (Γ : Finset (Seg d n)) : Prop :=
  (∀ c ∈ 𝒦, (∀ i, L ∣ (c i).val) ∧ lblock L c ⊆ (X : Set (Torus d n))) ∧
  (∀ x ∈ X, x ∈ Ω → ∃ c ∈ 𝒦, x ∈ lblock L c) ∧
  IsConnected (⋃ s ∈ Γ, s.carrier) ∧
  (⋃ s ∈ Γ, s.carrier) ⊆ ⋃ x ∈ X, cube x ∧
  ∀ c ∈ 𝒦, ∃ y ∈ lblock L c, ∃ q ∈ ⋃ s ∈ Γ, s.carrier, q ∈ cube y

/-- **A cube-level modular covering size**, in cube units of `𝕋_k`: choose `L`-blocks of cubes
contained in `X` whose union covers `X ∩ Ω`, minimize the total length of a connected finite union
of straight segments, inside the union of the closed cubes of `X`, meeting each chosen block
(`IsCovCurve`).  `⊤` if there is no admissible choice; its real value is then `0`, so the bound
of `D7Bdry` at such a domain is `fac`.

**Status.**  This is the size in the bound of the pre-`R` records `D7Bdry`, `D7Bdry2` (used by
`IsRepPre`, `IsRepPre2`).  It is no longer the size of (D7) for the post-`R` classes `IsRep`,
`IsRepFlat`, `IsRep2`, `IsRepFlat2`: their records `D7BdryPost`, `D7Bdry2Post` use the fine
chosen-cover modular size `d7Size` (`Def7FineSize`), the size of the fluctuation step
(`Fluctuation.dcovModE`).  The two sizes are not comparable: for two blocks meeting at a corner
and joined inside `X` by a long chain of blocks, this size is `0` (the corner point) while the
fine size is large, because there is no nearest-neighbour bond across a corner
(`notes/phase1/VMOD-25.md` §2).  No inequality between this size and `treeLengthMod`, the papers'
`d_k(X mod Ω^c)` (P5 (1.34), open cubes and all cover cubes) or the fine size is proved. -/
noncomputable def dCovMod [NeZero n] (L : ℕ) (Ω : Set (Torus d n)) (X : Finset (Torus d n)) :
    ENNReal :=
  ⨅ (𝒦 : Set (Torus d n)) (Γ : Finset (Seg d n)) (_ : IsCovCurve L Ω X 𝒦 Γ),
    ENNReal.ofReal (∑ s ∈ Γ, s.length)

end Bdry

section GlobalRec

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-- The records of a global history as fine sets (the domains `Z_j`, `Ω_{j+1}`, … of the history,
not intersected with a component): the history argument of the H7 domain of a boundary term. -/
def globalLH (H : RegionHistory S n R k0 K) (M : ℕ) : LocalHistory S n M K where
  Z j := fineSet (S := S) (n := n) M K j (H.step j).Z
  P j := fineSet M K (j + 1) (H.step j).P
  Q j := fineSet M K (j + 1) (H.step j).Q
  R j := fineSet M K (j + 1) (H.step j).R
  Sset j := fineSet M K (j + 1) (H.step j).S
  OmegaPrime j := fineSet M K (j + 1) (H.step j).OmegaPrime
  Omega j := fineSet M K (j + 1) (H.step j).Omega
  OmegaDD j := fineSet M K (j + 1) (H.step j).OmegaDD

end GlobalRec

end Balaban.LargeField.Def7
