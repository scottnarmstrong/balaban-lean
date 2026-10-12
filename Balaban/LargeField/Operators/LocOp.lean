module

public import Balaban.LargeField.Operators.StepData
public import Balaban.LargeField.Operators.AncVars
public import Balaban.LargeField.Operators.DomainIdentity
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


/-! ### The recursion -/

section Recursion

variable (geo : Geo S n R M) (cs : OpConsts) {κs κ : ℕ → LocalHistory S n M K → ℝ}
  {lamHat : ℕ → ℝ} (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ lamHat)
  {H : RegionHistory S n R k0}

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

/-- Typing data: the variables integrated by the pre-operator are the new variables and the
images of the variables of the old parts. -/
theorem preVars_cover {k : ℕ} (hk : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k) :
    AncCover hk Z' (fun Y hY => (sub Y hY).A) (preVars hk Z' sub) where
  new := preVars_new hk Z' sub
  anc := preVars_anc hk Z' sub
  cov := fun _ hp hn => by
    rcases hp with h | h
    · exact absurd h hn
    · exact h

/-- **The domain of the pre-operator is `χ^dom_{k+1}(Z')`** (the domain identity of the proof of
Lemma II.5.13, `chiDomAt_succ_iff`): if the domains of the operators of the old parts are
`χ^dom_k(Y)`, the domain `χ^new_k(Z') ∏_Y dom_Y` of `preOp` is `χ^dom_{k+1}(Z')`. -/
theorem preOp_dom_iff_chiDom {k : ℕ} (hk : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (hsub : ∀ (Y : H.Comp k) (hY : Y ∈ H.parts k Z') o x,
      (sub Y hY).dom o x ↔ ChiDomAt geo cs H k Y o x)
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hk Z' sub)) :
    (preOp geo cs SD hH hk Z' sub).dom o x ↔ ChiDomAt geo cs H (k + 1) Z' o x := by
  rw [preOp_dom, chiDomAt_succ_iff geo cs hk (preVars_cover hk Z' sub) o x]
  refine and_congr Iff.rfl ⟨fun h Y hY => (hsub Y hY _ _).mp (h ⟨Y, hY⟩),
    fun h Y => (hsub Y.1 Y.2 _ _).mpr (h Y.1 Y.2)⟩

/-- **Lemma II.5.9 (d), domain identified**: the domain of the operator of every component of
`Z_k` (`1 ≤ k`) is `χ^dom_k(Z, 𝔞)` (Definition II.3.4), at every level of the recursion. -/
theorem locOp_dom_iff {lab : ∀ k, H.Comp k → Fin 5} {hH : H.Admissible} :
    ∀ (k : ℕ) (hk : k ≤ K) (Z : H.Comp k)
      (P : OpPkg N R (H.localHistory M K k Z) k), P = locOp geo cs SD KD hH lab k hk Z →
      ∀ (o : OutT N R (H.localHistory M K k Z) k) (x : SubCfg N (H.localHistory M K k Z) k P.A),
        P.dom o x ↔ ChiDomAt geo cs H k Z o x
  | 0, _, Z, _, _ => (H.F.isEmpty_comp_zero.false Z).elim
  | k + 1, hk, Z', P, hP => by
    by_cases hc : IsKept H (k + 1) Z'
    · rw [locOp_kept geo cs SD KD hk hc] at hP
      subst hP
      intro o x
      exact Iff.rfl
    · rw [locOp_level geo cs SD KD hk hc] at hP
      subst hP
      intro o x
      exact preOp_dom_iff_chiDom geo cs SD hk Z' _
        (fun Y hY o' x' => locOp_dom_iff k (by omega) Y _ rfl o' x') o x

/-- **Lemma II.5.9 (d)**: the kernel of `𝕋_k(Z, 𝔞)` vanishes unless `χ^dom_k(Z, 𝔞) = 1`
(Definition II.3.4). -/
theorem locOp_vanish_chiDom {lab : ∀ k, H.Comp k → Fin 5} {hH : H.Admissible} {k : ℕ} (hk : k ≤ K)
    (Z : H.Comp k) (o : OutT N R (H.localHistory M K k Z) k)
    (x : SubCfg N (H.localHistory M K k Z) k (locOp geo cs SD KD hH lab k hk Z).A)
    (hv : EuclideanSpace ℝ (Fin N)) (hd : ¬ ChiDomAt geo cs H k Z o x) :
    (locOp geo cs SD KD hH lab k hk Z).T.K o x hv = 0 :=
  (locOp geo cs SD KD hH lab k hk Z).vanish o x hv
    (fun h => hd ((locOp_dom_iff geo cs SD KD k hk Z _ rfl o x).mp h))

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

/-- **Lemma II.5.9 (a)** (support; P5 H5, P6 p. 16): the operator of `Z` integrates over
variables located in `Z` (so over blocks of the fine set of `Z`), has output on `V_Z` and
internal variables in `A` by its type, and its exponent depends on the external field only through
`g|_{V_Z}`. -/
theorem locOp_support {k : ℕ} (hk : k ≤ K) (Z : H.Comp k) :
    (∀ p : InternalVars (H.localHistory M K k Z) k,
      BlockSub (S := S) (n := n) (M := M) (K := K) p.1.1 p.1.2.2
        (fineSet (S := S) (n := n) M K k (Z.1 : Set (Torus S.d (n k))))) ∧
    ∀ (o : OutT N R (H.localHistory M K k Z) k)
      (x : SubCfg N (H.localHistory M K k Z) k (locOp geo cs SD KD hH lab k hk Z).A)
      (hv : EuclideanSpace ℝ (Fin N)) (g g' : GIdx S n M K N → ℂ),
      (∀ i : GIdx S n M K N, i.1 ∈ Vsites R (H.localHistory M K k Z) k → g i = g' i) →
        (locOp geo cs SD KD hH lab k hk Z).T.b o x hv g =
          (locOp geo cs SD KD hH lab k hk Z).T.b o x hv g' :=
  ⟨internalVar_located Z, fun o x hv g g' hg => locOp_b_supp geo cs SD KD k hk Z o x hv g g' hg⟩

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
