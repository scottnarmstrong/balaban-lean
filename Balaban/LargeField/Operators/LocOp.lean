module

public import Balaban.LargeField.Operators.StepData
public import Balaban.LargeField.Operators.Pullback
public import Balaban.LargeField.Region.Lineage
public import Balaban.LargeField.History.RipeWindow

/-!
# The localized operators and Lemma F (Part II, Definition II.5.8, Lemma II.5.9, blocks J6)

`locOp` defines the large-field operator `𝕋_k(Z, 𝔞)` of every component `Z` of `Z_k` of a region
history `H`, by recursion along the lineage:

* if `Z'` is not kept, `𝕋_{k+1}(Z') = (K_k, b_k)(Z') ∘ ⨂_{Y ∈ Anc_k(Z')} 𝕋_k(Y)` (`preOp`): the
  kernel is `K_k · ∏_Y K_Y(ψ_k|_{V_Y}, x|_Y)` and the exponent `b_k + ∑_Y b_Y`, the outputs of the
  ancestors being internal variables `ψ_k` of `Z'` and their internal variables being a subset of
  those of `Z'` (`ancInc`);
* if `Z` is ripe at scale `1 ≤ k ≤ k₀` it is kept with a label `ϰ` and its operator is the kept
  kernel of the data (`keptOp`).

The operator integrates over the subset `A ⊆ I(Z, 𝔞)` of internal variables recorded in the
package (`OpPkg.A`): the new variables and the variables of the ancestors' operators
(a kept ancestor contributes only `I''`).

**Lemma II.5.9** (structural half of Lemma F):
(a) `locOp_support`: the variables are located in `Z` and `b` depends on `g` only through `g|_V`
    (`V_Y ⊆ V_{Z'}`, Lemma I.3.15), while the kernel is a function of the output on `V` and of the
    variables in `A` (by its type);
(b) `locOp_factor`: for distinct components the sets `V` are disjoint (Lemma I.2.13) and no block is
    a variable of both;
(c) `locOp_level`: the definition at a non-kept component;
(d) `locOp_domain`: the kernel vanishes off the domain (`χ^new_k` times the domains of the
    ancestors).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section LocOp

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- An operator of a localized history at level `k`: the set `A` of internal variables it
integrates, its kernel `(K, b)`, and its domain (on which the kernel can be non-zero). -/
structure OpPkg (N : ℕ) (R : ℕ → ℝ) (a : LocalHistory S n M K) (k : ℕ) where
  /-- the internal variables integrated by the operator -/
  A : Set (InternalVars a k)
  /-- the kernel `(K, b)` -/
  T : LFKernel (OutT N R a k) (SubCfg N a k A) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N)
  /-- the domain: the kernel vanishes off it -/
  dom : OutT N R a k → SubCfg N a k A → Prop
  vanish : ∀ o x hv, ¬ dom o x → T.K o x hv = 0

/-! ### The geometry of the lineage -/

section Geometry

variable {H : RegionHistory S n R k0}

/-- Every cube of `𝕋_k` is the cube of a site of the fine torus (`k ≤ K`). -/
theorem exists_site_of_cube (hnn : ∀ i, n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
    (y : Torus S.d (n k)) : ∃ x : Torus S.d (M * n K * S.L ^ K), cubeMap n S.L M K k x = y := by
  have hℓ : M * n K * S.L ^ K = (S.L ^ k * M) * n k := fine_eq hnn hkK
  have hc := card_blockFibre (d := S.d) (ℓ := M * n K * S.L ^ K) (N := S.L ^ k * M) (m := n k)
    hℓ y
  have hpos' : 0 < (blockFibre (S.L ^ k * M) (n k) y :
      Finset (Torus S.d (M * n K * S.L ^ K))).card := by
    rw [hc]
    have := NeZero.ne S.L
    have := NeZero.ne M
    positivity
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos'
  exact ⟨x, mem_blockFibre.mp hx⟩

/-- The cubes of `Z_k` of the localized history of `Y` lie in `Y`. -/
theorem Zcubes_loc_sub {k : ℕ} (hkK : k ≤ K) (Y : H.Comp k) :
    Zcubes (H.localHistory M K k Y) k ⊆ (Y.1 : Set (Torus S.d (n k))) := by
  intro y hy
  obtain ⟨x, hx⟩ := exists_site_of_cube (M := M) H.F.hnn hkK y
  have h := hy x hx
  have h2 : cubeMap n S.L M K k x ∈ (Y.1 : Set (Torus S.d (n k))) := h.2
  rwa [hx] at h2

/-- The component `Z'` lies in the cubes of `Z_{k+1}` of its localized history. -/
theorem Zcubes_loc_top {k : ℕ} (Z : H.Comp k) :
    (Z.1 : Set (Torus S.d (n k))) ⊆ Zcubes (H.localHistory M K k Z) k := by
  intro y hy x hx
  refine ⟨?_, ?_⟩
  · show cubeMap n S.L M K k x ∈ ((H.locRH k Z).step k).Z
    rw [locRH_Z Z le_rfl, lin_self, hx]
    exact hy
  · show cubeMap n S.L M K k x ∈ (Z.1 : Set (Torus S.d (n k)))
    rw [hx]; exact hy

theorem thick_mono' {m : ℕ} [NeZero m] (r : ℕ) {X Y : Set (Torus S.d m)} (h : X ⊆ Y) :
    thick r X ⊆ thick r Y := nbhd_mono le_rfl h

/-- **Lemma I.3.15**: `V_Y ⊆ V_{Z'}` for an old part `Y` of `Z'`, on fine sites. -/
theorem Vsites_anc (geo : Geo S n R M) {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k}
    {Z' : H.Comp (k + 1)} (hY : Y ∈ H.parts k Z') :
    Vsites R (H.localHistory M K k Y) k ⊆ Vsites R (H.localHistory M K (k + 1) Z') (k + 1) := by
  intro x hx
  obtain ⟨hrem, hs⟩ := (H.mem_parts k Y Z').mp hY
  have hL : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne _)
  have hYY : blockMap S.L (n (k + 1)) '' Zcubes (H.localHistory M K k Y) k ⊆
      (Z'.1 : Set (Torus S.d (n (k + 1)))) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := H.succ_spec k hrem ⟨y, Zcubes_loc_sub (by omega) Y hy, rfl⟩
    rwa [hs] at h1
  have h1 := thick_nbhd_coarsen (H.F.hnn k) hL (geo.hRmono k) hYY hx
  rw [cubeMap_succ H.F.hnn (by omega : k ≤ K)] at h1
  have hdiv : (1 + S.L - 1) / S.L ≤ 1 := by
    rw [show 1 + S.L - 1 = S.L by omega, Nat.div_self hL]
  exact nbhd_mono hdiv (thick_mono' _ (Zcubes_loc_top Z')) h1

end Geometry

/-! ### The variables of the ancestors inside those of the component -/

section Anc

variable {H : RegionHistory S n R k0}

/-- The internal variable of the component `Z'` that is the variable `p` of its old part `Y`
(`j < k` is also `< k + 1`). -/
def ancInc {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k} {Z' : H.Comp (k + 1)} (hY : Y ∈ H.parts k Z')
    (p : InternalVars (H.localHistory M K k Y) k) :
    InternalVars (H.localHistory M K (k + 1) Z') (k + 1) :=
  ⟨⟨Fin.castSucc p.1.1, p.1.2.1, p.1.2.2⟩,
    fun x hx => varSet_mono hK hY p.1.1.2 p.1.2.1 (p.2 x hx)⟩

theorem isSpin_ancInc {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k} {Z' : H.Comp (k + 1)}
    (hY : Y ∈ H.parts k Z') (p : InternalVars (H.localHistory M K k Y) k) :
    (ancInc hK hY p).isSpin = p.isSpin := rfl

/-- The restriction of a configuration of the variables `A'` of `Z'` to those of its old part
`Y`, given that the variables `A_Y` of `Y` are among `A'`. -/
def ancRestrict {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k} {Z' : H.Comp (k + 1)}
    (hY : Y ∈ H.parts k Z') {AY : Set (InternalVars (H.localHistory M K k Y) k)}
    {A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
    (hA : ∀ p ∈ AY, ancInc hK hY p ∈ A') (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A') :
    SubCfg N (H.localHistory M K k Y) k AY :=
  fun p => x ⟨ancInc hK hY p.1, hA p.1 p.2⟩

theorem measurable_ancRestrict {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k} {Z' : H.Comp (k + 1)}
    (hY : Y ∈ H.parts k Z') {AY : Set (InternalVars (H.localHistory M K k Y) k)}
    {A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
    (hA : ∀ p ∈ AY, ancInc hK hY p ∈ A') :
    Measurable (ancRestrict (N := N) hK hY hA) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- The output of the old part `Y`: the large-field variable `ψ_k` of `Z'` on the blocks of `V_Y`. -/
noncomputable def ancOut {k : ℕ} (Y : H.Comp k) (Z' : H.Comp (k + 1))
    {A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A') :
    OutT N R (H.localHistory M K k Y) k :=
  fun y => subVarField N x k y.1

theorem measurable_ancOut {k : ℕ} (Y : H.Comp k) (Z' : H.Comp (k + 1))
    (A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))) :
    Measurable (ancOut (N := N) (R := R) Y Z' (A' := A')) :=
  Measurable.of_eval fun y => measurable_subVarField k y.1

/-- Restriction of a configuration of `A'` to the new variables. -/
def newRestrict {k : ℕ} (a : LocalHistory S n M K) {A' : Set (InternalVars a (k + 1))}
    (h : newVars a k ⊆ A') (x : SubCfg N a (k + 1) A') : NewCfg N a k :=
  restrictSub h x

theorem measurable_newRestrict {k : ℕ} (a : LocalHistory S n M K) {A' : Set (InternalVars a (k + 1))}
    (h : newVars a k ⊆ A') : Measurable (newRestrict (N := N) a h) :=
  measurable_restrictSub h

end Anc

/-! ### The recursion -/

section Recursion

variable (geo : Geo S n R M) (cs : OpConsts) {κs κ : ℕ → LocalHistory S n M K → ℝ}
  {lamHat : ℕ → ℝ} (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ lamHat)
  {H : RegionHistory S n R k0}

/-- The variables integrated by the pre-operator of `Z'`: the new variables and the variables of
the operators of the old parts. -/
def preVars {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k) :
    Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1)) :=
  {p | p ∈ newVars (H.localHistory M K (k + 1) Z') k ∨
    ∃ (Y : H.Comp k) (hY : Y ∈ H.parts k Z') (q : InternalVars (H.localHistory M K k Y) k),
      q ∈ (sub Y hY).A ∧ ancInc hK hY q = p}

theorem preVars_new {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k) :
    newVars (H.localHistory M K (k + 1) Z') k ⊆ preVars hK Z' sub :=
  fun _ hp => Or.inl hp

theorem preVars_anc {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (Y : H.Comp k) (hY : Y ∈ H.parts k Z') :
    ∀ p ∈ (sub Y hY).A, ancInc hK hY p ∈ preVars hK Z' sub :=
  fun p hp => Or.inr ⟨Y, hY, p, hp, rfl⟩

/-- The kernel of the pre-operator of `Z'`: `K_k · ∏_Y K_Y(ψ_k|_{V_Y}, x|_Y)` and
`b_k + ∑_Y b_Y(ψ_k|_{V_Y}, x|_Y)`. -/
noncomputable def preKernel {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (T₀ : LFKernel (OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
      (NewCfg N (H.localHistory M K (k + 1) Z') k) (EuclideanSpace ℝ (Fin N))
      (GIdx S n M K N)) :
    LFKernel (OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
      (SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub))
      (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N) :=
  T₀.mulPull (newRestrict (N := N) (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub)) (measurable_newRestrict (H.localHistory M K (k + 1) Z') _)
    (Finset.univ : Finset ↥(H.parts k Z'))
    (O' := fun Y : ↥(H.parts k Z') => OutT N R (H.localHistory M K k Y.1) k)
    (X' := fun Y : ↥(H.parts k Z') => SubCfg N (H.localHistory M K k Y.1) k (sub Y.1 Y.2).A)
    (fun Y => (sub Y.1 Y.2).T)
    (fun Y x => ancOut Y.1 Z' x)
    (fun Y x => ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) x)
    (fun Y => measurable_ancOut Y.1 Z' _)
    (fun Y => measurable_ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2))

theorem preKernel_K {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (T₀ : LFKernel (OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
      (NewCfg N (H.localHistory M K (k + 1) Z') k) (EuclideanSpace ℝ (Fin N))
      (GIdx S n M K N)) (o) (x) (hv) :
    (preKernel hK Z' sub T₀).K o x hv = T₀.K o (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x) hv *
      ∏ Y : ↥(H.parts k Z'), (sub Y.1 Y.2).T.K (ancOut Y.1 Z' x)
        (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) x) hv := rfl

theorem preKernel_b {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (T₀ : LFKernel (OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
      (NewCfg N (H.localHistory M K (k + 1) Z') k) (EuclideanSpace ℝ (Fin N))
      (GIdx S n M K N)) (o) (x) (hv) (g) :
    (preKernel hK Z' sub T₀).b o x hv g = T₀.b o (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x) hv g +
      ∑ Y : ↥(H.parts k Z'), (sub Y.1 Y.2).T.b (ancOut Y.1 Z' x)
        (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) x) hv g := rfl

theorem preKernel_vanish (hH : H.Admissible) {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub))
    (hv : EuclideanSpace ℝ (Fin N))
    (hnd : ¬ (ChiNewAt geo cs H k Z' o
        (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x) ∧
      ∀ Y : ↥(H.parts k Z'), (sub Y.1 Y.2).dom (ancOut Y.1 Z' x)
        (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) x))) :
    (preKernel hK Z' sub (SD.ker k (H.localHistory M K (k + 1) Z'))).K o x hv = 0 := by
  classical
  rw [preKernel_K]
  by_cases hc : ChiNewAt geo cs H k Z' o
      (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x)
  · have : ∃ Y : ↥(H.parts k Z'), ¬ (sub Y.1 Y.2).dom (ancOut Y.1 Z' x)
        (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) x) := by
      by_contra hne
      push Not at hne
      exact hnd ⟨hc, hne⟩
    obtain ⟨Y, hY⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ Y) ((sub Y.1 Y.2).vanish _ _ hv hY), mul_zero]
  · rw [SD.dom H hH k Z' o
      (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x) hv hc, zero_mul]

/-- **The pre-operator** `𝕋^pre_{k+1}(Z', 𝔞) = (K_k, b_k)(Z', 𝔞) ∘ ⨂_{Y ∈ Anc_k(Z')} 𝕋_k(Y, 𝔞|_Y)`
(Definition II.5.8), given the operators `sub` of the old parts. -/
noncomputable def preOp (hH : H.Admissible) {k : ℕ} (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k) :
    OpPkg N R (H.localHistory M K (k + 1) Z') (k + 1) where
  A := preVars hK Z' sub
  T := preKernel hK Z' sub (SD.ker k (H.localHistory M K (k + 1) Z'))
  dom := fun o x =>
    ChiNewAt geo cs H k Z' o (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hK Z' sub) x) ∧
      ∀ Y : ↥(H.parts k Z'), (sub Y.1 Y.2).dom (ancOut Y.1 Z' x)
        (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) x)
  vanish := fun o x hv hnd => preKernel_vanish geo cs SD hH hK Z' sub o x hv hnd

/-- The kept operator of a ripe kept component with label `ϰ` (Definition II.5.7 (S3)). -/
noncomputable def keptOp (hH : H.Admissible) {k : ℕ} (Z : H.Comp k) (hk1 : 1 ≤ k) (hk0 : k ≤ k0)
    (hrip : S.Ripe k (H.bk k Z)) (ϰ : Fin 5) : OpPkg N R (H.localHistory M K k Z) k where
  A := (KD.datum k (H.localHistory M K k Z) ϰ).Ikeep
  T := (KD.datum k (H.localHistory M K k Z) ϰ).ker
  dom := fun o x => ChiDomAt geo cs H k Z o x
  vanish := fun o x hv hd => (KD.bound H hH k Z hk1 hk0 hrip ϰ).1 o x hv hd

/-- A component is *kept* if it is ripe at a scale `1 ≤ k ≤ k₀` (removed components do not occur
in the lineage, so every ripe component of `Z_k` is kept; Definition II.5.8). -/
def IsKept (H : RegionHistory S n R k0) (k : ℕ) (Z : H.Comp k) : Prop :=
  1 ≤ k ∧ k ≤ k0 ∧ S.Ripe k (H.bk k Z)

open Classical in
/-- **Definition II.5.8**: the localized operator `𝕋_k(Z, 𝔞)` of the component `Z` of `Z_k`
(`k ≤ K`), by recursion along the lineage; `lab` assigns the kept labels `ϰ`. -/
noncomputable def locOp (hH : H.Admissible) (lab : ∀ k, H.Comp k → Fin 5) :
    (k : ℕ) → k ≤ K → (Z : H.Comp k) → OpPkg N R (H.localHistory M K k Z) k
  | 0, _, Z => (H.F.isEmpty_comp_zero.false Z).elim
  | k + 1, hk, Z' =>
    if hc : IsKept H (k + 1) Z' then
      keptOp geo cs KD hH Z' hc.1 hc.2.1 hc.2.2 (lab (k + 1) Z')
    else
      preOp geo cs SD hH hk Z' (fun Y _ => locOp hH lab k (by omega) Y)

/-! ### Lemma II.5.9 -/

section Lemma59

variable {lab : ∀ k, H.Comp k → Fin 5} {hH : H.Admissible}

/-- **Lemma II.5.9 (c)** (levels; P5 (1.23)): at a component `Z'` that is not kept, the operator
is the step kernel composed with the operators of the old parts. -/
theorem locOp_level {k : ℕ} (hk : k + 1 ≤ K) {Z' : H.Comp (k + 1)} (h : ¬ IsKept H (k + 1) Z') :
    locOp geo cs SD KD hH lab (k + 1) hk Z' =
      preOp geo cs SD hH hk Z' (fun Y _ => locOp geo cs SD KD hH lab k (by omega) Y) := by
  rw [locOp]; simp only [h, ↓reduceDIte]

/-- The operator of a ripe component is the kept operator. -/
theorem locOp_kept {k : ℕ} (hk : k + 1 ≤ K) {Z' : H.Comp (k + 1)} (h : IsKept H (k + 1) Z') :
    locOp geo cs SD KD hH lab (k + 1) hk Z' =
      keptOp geo cs KD hH Z' h.1 h.2.1 h.2.2 (lab (k + 1) Z') := by
  rw [locOp]; simp only [h, ↓reduceDIte]

/-- **Lemma II.5.9 (d)** (domain; P5 (1.24)-(1.25)): the kernel of the operator vanishes off its
domain `dom`: for a component that is not kept this is `χ^new_k(Z')` and the domains of the old
parts (`preOp`), for a kept component it is `χ^dom_k(Z, 𝔞)` (`keptOp`). -/
theorem locOp_domain {k : ℕ} (hk : k ≤ K) (Z : H.Comp k)
    (o : OutT N R (H.localHistory M K k Z) k)
    (x : SubCfg N (H.localHistory M K k Z) k (locOp geo cs SD KD hH lab k hk Z).A)
    (hv : EuclideanSpace ℝ (Fin N)) (hd : ¬ (locOp geo cs SD KD hH lab k hk Z).dom o x) :
    (locOp geo cs SD KD hH lab k hk Z).T.K o x hv = 0 :=
  (locOp geo cs SD KD hH lab k hk Z).vanish o x hv hd

/-- The domain of the pre-operator, explicitly. -/
theorem preOp_dom {k : ℕ} (hk : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hk Z' sub)) :
    (preOp geo cs SD hH hk Z' sub).dom o x ↔
      ChiNewAt geo cs H k Z' o (newRestrict (H.localHistory M K (k + 1) Z') (preVars_new hk Z' sub) x) ∧
        ∀ Y : ↥(H.parts k Z'), (sub Y.1 Y.2).dom (ancOut Y.1 Z' x)
          (ancRestrict hk Y.2 (preVars_anc hk Z' sub Y.1 Y.2) x) := Iff.rfl

/-! (a) Support -/

theorem varSet_sub_fine {k : ℕ} (Z : H.Comp k) (j : ℕ) (κ : VarKind) :
    varSet (H.localHistory M K k Z) j κ ⊆
      fineSet (S := S) (n := n) M K k (Z.1 : Set (Torus S.d (n k))) := by
  intro x hx
  cases κ with
  | large => exact hx.1.2
  | fluct => exact hx.1.2

/-- **Lemma II.5.9 (a)**, location: every internal variable of the localized history of `Z` is
a block of the fine set of `Z` (so the variables of different components are different). -/
theorem internalVar_located {k : ℕ} (Z : H.Comp k) (p : InternalVars (H.localHistory M K k Z) k) :
    BlockSub (S := S) (n := n) (M := M) (K := K) p.1.1 p.1.2.2
      (fineSet (S := S) (n := n) M K k (Z.1 : Set (Torus S.d (n k)))) :=
  fun x hx => varSet_sub_fine Z _ _ (p.2 x hx)

theorem preOp_b_supp {k : ℕ} (hk : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (hsub : ∀ Y (hY : Y ∈ H.parts k Z') o x hv (g g' : GIdx S n M K N → ℂ),
      (∀ i : GIdx S n M K N, i.1 ∈ Vsites R (H.localHistory M K k Y) k → g i = g' i) →
        (sub Y hY).T.b o x hv g = (sub Y hY).T.b o x hv g')
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hk Z' sub))
    (hv : EuclideanSpace ℝ (Fin N)) (g g' : GIdx S n M K N → ℂ)
    (hg : ∀ i : GIdx S n M K N, i.1 ∈ Vsites R (H.localHistory M K (k + 1) Z') (k + 1) → g i = g' i) :
    (preOp geo cs SD hH hk Z' sub).T.b o x hv g = (preOp geo cs SD hH hk Z' sub).T.b o x hv g' := by
  show (preKernel hk Z' sub (SD.ker k (H.localHistory M K (k + 1) Z'))).b o x hv g =
    (preKernel hk Z' sub (SD.ker k (H.localHistory M K (k + 1) Z'))).b o x hv g'
  rw [preKernel_b, preKernel_b]
  congr 1
  · exact SD.b_supp k _ o _ hv g g' hg
  · exact Finset.sum_congr rfl fun Y _ =>
      hsub Y.1 Y.2 _ _ hv g g' fun i hi => hg i (Vsites_anc geo hk Y.2 hi)

/-- **Lemma II.5.9 (a)**, support in `g`: the exponent of the operator depends on the external
field only through `g|_{V_Z}` (`V_Y ⊆ V_{Z'}` for the old parts, Lemma I.3.15). -/
theorem locOp_b_supp (k : ℕ) : ∀ (hk : k ≤ K) (Z : H.Comp k)
    (o : OutT N R (H.localHistory M K k Z) k)
    (x : SubCfg N (H.localHistory M K k Z) k (locOp geo cs SD KD hH lab k hk Z).A)
    (hv : EuclideanSpace ℝ (Fin N)) (g g' : GIdx S n M K N → ℂ),
    (∀ i : GIdx S n M K N, i.1 ∈ Vsites R (H.localHistory M K k Z) k → g i = g' i) →
      (locOp geo cs SD KD hH lab k hk Z).T.b o x hv g =
        (locOp geo cs SD KD hH lab k hk Z).T.b o x hv g' := by
  induction k with
  | zero => intro hk Z; exact (H.F.isEmpty_comp_zero.false Z).elim
  | succ k ih =>
    intro hk Z' o x hv g g' hg
    by_cases hc : IsKept H (k + 1) Z'
    · have e := locOp_kept geo cs SD KD (lab := lab) (hH := hH) hk hc
      have key : ∀ P : OpPkg N R (H.localHistory M K (k + 1) Z') (k + 1),
          P = keptOp geo cs KD hH Z' hc.1 hc.2.1 hc.2.2 (lab (k + 1) Z') →
          ∀ (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A),
            P.T.b o x hv g = P.T.b o x hv g' := by
        intro P hP
        subst hP
        intro x
        exact KD.b_supp (k + 1) _ _ o x hv g g' hg
      exact key _ e x
    · have e := locOp_level geo cs SD KD (lab := lab) (hH := hH) hk hc
      have key : ∀ P : OpPkg N R (H.localHistory M K (k + 1) Z') (k + 1),
          P = preOp geo cs SD hH hk Z'
            (fun Y _ => locOp geo cs SD KD hH lab k (by omega) Y) →
          ∀ (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A),
            P.T.b o x hv g = P.T.b o x hv g' := by
        intro P hP
        subst hP
        intro x
        exact preOp_b_supp geo cs SD hk Z' _ (fun Y hY o x hv g g' hg => ih _ Y o x hv g g' hg)
          o x hv g g' hg
      exact key _ e x

/-! (b) Factorization -/

/-- **Lemma II.5.9 (b)** (factorization; P5 (1.22)): for distinct components `Z_1 ≠ Z_2` of
`Z_k` the sets `V_{Z_1}`, `V_{Z_2}` are disjoint (Lemma I.2.13) and no block is an internal
variable of both. -/
theorem locOp_factor {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ K) {Z1 Z2 : H.Comp k} (hne : Z1 ≠ Z2) :
    Disjoint (Vcubes R (H.localHistory M K k Z1) k) (Vcubes R (H.localHistory M K k Z2) k) ∧
    ∀ (j : ℕ), j ≤ K → ∀ (y : BlockAt S n M K j) (κ1 κ2 : VarKind),
      ¬ (BlockSub (S := S) (n := n) (M := M) (K := K) j y (varSet (H.localHistory M K k Z1) j κ1) ∧
        BlockSub (S := S) (n := n) (M := M) (K := K) j y (varSet (H.localHistory M K k Z2) j κ2)) := by
  refine ⟨?_, ?_⟩
  · refine Disjoint.mono ?_ ?_ (core_thick_disjoint H.F.RH hk1 hne (m := 1) (by omega))
    · exact nbhd_mono le_rfl (thick_mono' _ (Zcubes_loc_sub hk Z1))
    · exact nbhd_mono le_rfl (thick_mono' _ (Zcubes_loc_sub hk Z2))
  · rintro j hj y κ1 κ2 ⟨h1, h2⟩
    obtain ⟨x, hx⟩ := exists_site_in_block (S := S) (n := n) (M := M) hj y
    have e1 : cubeMap n S.L M K k x ∈ (Z1.1 : Set (Torus S.d (n k))) :=
      varSet_sub_fine Z1 j κ1 (h1 x hx)
    have e2 : cubeMap n S.L M K k x ∈ (Z2.1 : Set (Torus S.d (n k))) :=
      varSet_sub_fine Z2 j κ2 (h2 x hx)
    exact hne (Subtype.ext (comp_eq_of_mem Z1.2 Z2.2 e1 e2))

/-- The operators of two components commute (Fubini-Tonelli, Lemma II.5.3 (a)). -/
theorem locOp_commute {k : ℕ} (hk : k ≤ K) (Z1 Z2 : H.Comp k) (o1 o2) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ)
    (F : SubCfg N (H.localHistory M K k Z1) k (locOp geo cs SD KD hH lab k hk Z1).A →
      SubCfg N (H.localHistory M K k Z2) k (locOp geo cs SD KD hH lab k hk Z2).A → ℂ)
    (hint : Integrable (fun q => (locOp geo cs SD KD hH lab k hk Z1).T.w o1 q.1 hv g *
      ((locOp geo cs SD KD hH lab k hk Z2).T.w o2 q.2 hv g * F q.1 q.2))
      ((subMeasure N (H.localHistory M K k Z1) k (locOp geo cs SD KD hH lab k hk Z1).A).prod
        (subMeasure N (H.localHistory M K k Z2) k (locOp geo cs SD KD hH lab k hk Z2).A))) :
    (locOp geo cs SD KD hH lab k hk Z1).T.pint
        (subMeasure N (H.localHistory M K k Z1) k (locOp geo cs SD KD hH lab k hk Z1).A) hv g o1
        (fun x1 => (locOp geo cs SD KD hH lab k hk Z2).T.pint
          (subMeasure N (H.localHistory M K k Z2) k (locOp geo cs SD KD hH lab k hk Z2).A) hv g o2
          (F x1)) =
      (locOp geo cs SD KD hH lab k hk Z2).T.pint
        (subMeasure N (H.localHistory M K k Z2) k (locOp geo cs SD KD hH lab k hk Z2).A) hv g o2
        (fun x2 => (locOp geo cs SD KD hH lab k hk Z1).T.pint
          (subMeasure N (H.localHistory M K k Z1) k (locOp geo cs SD KD hH lab k hk Z1).A)
          hv g o1 (fun x1 => F x1 x2)) :=
  LFKernel.op_comm _ _ _ _ hv g o1 o2 F hint

end Lemma59

end Recursion

end LocOp

end Balaban.LargeField
