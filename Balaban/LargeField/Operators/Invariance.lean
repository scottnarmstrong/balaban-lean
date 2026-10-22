module

public import Balaban.LargeField.Operators.LocOp

/-!
# Invariance of the localized operators (Part II, Lemma II.5.10, block J7)

**`O(N)`** (`locOp_rot_invariant`).  The data (S0), (S1), (S3) are invariant under `O(N)` acting
on all spin-valued variables, on the output, on `h` and on `g` (`StepData.rot_K`, `rot_b`,
`KeptData.rot_K`, `rot_b`), and the reading maps of the recursion (restriction to the new variables,
to the variables of an old part, and the output of an old part, i.e. the variable `ψ_k`) commute
with the rotation.  Hence the localized operators are invariant.

**Euclidean symmetries** (`locOp_euclid_invariant`).  A Euclidean symmetry `σ` of the torus
(`TorusSym`) that maps the region history `H` to `H'` (`HistIso`: matching of the components, of
the localized histories, of the old parts and of the ripe components) acts on the internal variables
(`symVar`), the output and `g`; the data are covariant (`StepData.euclid_K`, `euclid_b`,
`KeptData.euclid_I`, `euclid_K`, `euclid_b`), and the operators of corresponding components take
the same values at corresponding configurations (`RelOut`, `RelVal`, `RelG`), the integrated
variables corresponding (`SubCorr`).

The invariance of the *quiet kernel itself* (`quietKernel`; Lemma II.5.10 for the explicit kernel) is
not proved here: it needs the equivariance of the Def-5 background under rotations of the data and
under the symmetries of the generating sets, which is not in the landed background layer.  The
data are required to be invariant, as P5 H5 asks.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section Rot

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

theorem subVarField_rot (ρ : OrthN N) {a : LocalHistory S n M K} {k : ℕ}
    {A : Set (InternalVars a k)} (x : SubCfg N a k A) (j : ℕ) (y : BlockAt S n M K j) :
    subVarField N (rotSub ρ x) j y = ρ (subVarField N x j y) := by
  classical
  unfold subVarField
  by_cases h : ∃ hj : j < k, ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y
      (varSet a j .large), mkVar a k j .large y hj hb ∈ A
  · simp only [h, ↓reduceDIte]
    exact VarVal.toEuc_rot ρ _ (x _)
  · simp only [h, ↓reduceDIte]
    simp

variable {H : RegionHistory S n R k0 K}

theorem rotSub_newRestrict (ρ : OrthN N) {k : ℕ} (a : LocalHistory S n M K)
    {A' : Set (InternalVars a (k + 1))} (h : newVars a k ⊆ A') (x : SubCfg N a (k + 1) A') :
    newRestrict a h (rotSub ρ x) = rotSub ρ (newRestrict a h x) := rfl

theorem rotSub_ancRestrict (ρ : OrthN N) {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k}
    {Z' : H.Comp (k + 1)} (hY : Y ∈ H.parts k Z')
    {AY : Set (InternalVars (H.localHistory M K k Y) k)}
    {A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
    (hA : ∀ p ∈ AY, ancInc hK hY p ∈ A')
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A') :
    ancRestrict hK hY hA (rotSub ρ x) = rotSub ρ (ancRestrict hK hY hA x) := rfl

theorem rotOut_ancOut (ρ : OrthN N) {k : ℕ} (Y : H.Comp k) (Z' : H.Comp (k + 1))
    {A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A') :
    ancOut (R := R) Y Z' (rotSub ρ x) = rotOut ρ (ancOut Y Z' x) :=
  funext fun y => subVarField_rot ρ x k y.1

variable (geo : Geo S n R M) (cs : OpConsts) {κs κ : ℕ → LocalHistory S n M K → ℝ}
  {lamHat : ℕ → ℝ} (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

theorem preKernel_rot {k : ℕ} (hk : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (T₀ : LFKernel (OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
      (NewCfg N (H.localHistory M K (k + 1) Z') k) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N))
    (ρ : OrthN N)
    (h0 : ∀ o x hv (g : GIdx S n M K N → ℂ),
      T₀.K (rotOut ρ o) (rotSub ρ x) (ρ hv) = T₀.K o x hv ∧
      T₀.b (rotOut ρ o) (rotSub ρ x) (ρ hv) (rotG ρ g) = T₀.b o x hv g)
    (hsub : ∀ Y (hY : Y ∈ H.parts k Z') o x hv (g : GIdx S n M K N → ℂ),
      (sub Y hY).T.K (rotOut ρ o) (rotSub ρ x) (ρ hv) = (sub Y hY).T.K o x hv ∧
      (sub Y hY).T.b (rotOut ρ o) (rotSub ρ x) (ρ hv) (rotG ρ g) = (sub Y hY).T.b o x hv g)
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hk Z' sub))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) :
    (preKernel hk Z' sub T₀).K (rotOut ρ o) (rotSub ρ x) (ρ hv) =
      (preKernel hk Z' sub T₀).K o x hv ∧
    (preKernel hk Z' sub T₀).b (rotOut ρ o) (rotSub ρ x) (ρ hv) (rotG ρ g) =
      (preKernel hk Z' sub T₀).b o x hv g := by
  refine ⟨?_, ?_⟩
  · rw [preKernel_K, preKernel_K, rotSub_newRestrict, (h0 _ _ _ g).1]
    congr 1
    refine Finset.prod_congr rfl fun Y _ => ?_
    rw [rotOut_ancOut, rotSub_ancRestrict]
    exact (hsub Y.1 Y.2 _ _ hv g).1
  · rw [preKernel_b, preKernel_b, rotSub_newRestrict, (h0 _ _ _ g).2]
    congr 1
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [rotOut_ancOut, rotSub_ancRestrict]
    exact (hsub Y.1 Y.2 _ _ hv g).2

theorem preOp_rot {k : ℕ} (hk : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (ρ : OrthN N)
    (hsub : ∀ Y (hY : Y ∈ H.parts k Z') o x hv (g : GIdx S n M K N → ℂ),
      (sub Y hY).T.K (rotOut ρ o) (rotSub ρ x) (ρ hv) = (sub Y hY).T.K o x hv ∧
      (sub Y hY).T.b (rotOut ρ o) (rotSub ρ x) (ρ hv) (rotG ρ g) = (sub Y hY).T.b o x hv g)
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hk Z' sub))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) :
    (preKernel hk Z' sub (SD.ker k (H.localHistory M K (k + 1) Z'))).K (rotOut ρ o) (rotSub ρ x)
        (ρ hv) = (preKernel hk Z' sub (SD.ker k (H.localHistory M K (k + 1) Z'))).K o x hv ∧
    (preKernel hk Z' sub (SD.ker k (H.localHistory M K (k + 1) Z'))).b (rotOut ρ o) (rotSub ρ x)
        (ρ hv) (rotG ρ g) =
      (preKernel hk Z' sub (SD.ker k (H.localHistory M K (k + 1) Z'))).b o x hv g :=
  preKernel_rot hk Z' sub _ ρ
    (fun o x hv g => ⟨SD.rot_K k _ ρ o x hv, SD.rot_b k _ ρ o x hv g⟩) hsub o x hv g

/-- **Lemma II.5.10 (invariance under `O(N)`)**: the localized operators are invariant under
`O(N)` acting on all spin-valued variables, the output, `h` and `g`. -/
theorem locOp_rot_invariant (ρ : OrthN N) (k : ℕ) : ∀ (hk : k ≤ K) (Z : H.Comp k)
    (o : OutT N R (H.localHistory M K k Z) k)
    (x : SubCfg N (H.localHistory M K k Z) k (locOp geo cs SD KD hH lab k hk Z).A)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ),
    (locOp geo cs SD KD hH lab k hk Z).T.K (rotOut ρ o) (rotSub ρ x) (ρ hv) =
        (locOp geo cs SD KD hH lab k hk Z).T.K o x hv ∧
      (locOp geo cs SD KD hH lab k hk Z).T.b (rotOut ρ o) (rotSub ρ x) (ρ hv) (rotG ρ g) =
        (locOp geo cs SD KD hH lab k hk Z).T.b o x hv g := by
  induction k with
  | zero => intro hk Z; exact (H.F.isEmpty_comp_zero.false Z).elim
  | succ k ih =>
    intro hk Z' o x hv g
    by_cases hc : IsKept H (k + 1) Z'
    · have e := locOp_kept geo cs SD KD (lab := lab) (hH := hH) hk hc
      have key : ∀ P : OpPkg N R (H.localHistory M K (k + 1) Z') (k + 1),
          P = keptOp geo cs KD hH lab Z' hc.1 hc.2.1 hc.2.2 (lab (k + 1) Z') →
          ∀ (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A),
            P.T.K (rotOut ρ o) (rotSub ρ x) (ρ hv) = P.T.K o x hv ∧
            P.T.b (rotOut ρ o) (rotSub ρ x) (ρ hv) (rotG ρ g) = P.T.b o x hv g := by
        intro P hP
        subst hP
        intro x
        exact ⟨KD.rot_K (k + 1) _ _ _ ρ o x hv, KD.rot_b (k + 1) _ _ _ ρ o x hv g⟩
      exact key _ e x
    · have e := locOp_level geo cs SD KD (lab := lab) (hH := hH) hk hc
      have key : ∀ P : OpPkg N R (H.localHistory M K (k + 1) Z') (k + 1),
          P = preOp geo cs SD hH hk Z'
            (fun Y _ => locOp geo cs SD KD hH lab k (by omega) Y) →
          ∀ (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A),
            P.T.K (rotOut ρ o) (rotSub ρ x) (ρ hv) = P.T.K o x hv ∧
            P.T.b (rotOut ρ o) (rotSub ρ x) (ρ hv) (rotG ρ g) = P.T.b o x hv g := by
        intro P hP
        subst hP
        intro x
        exact preOp_rot geo cs SD hk Z' _ ρ
          (fun Y hY o x hv g => ih _ Y o x hv g) o x hv g
      exact key _ e x

end Rot

/-! ### Euclidean symmetries -/

section Euclid

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- A Euclidean symmetry `σ` maps the region history `H` to the region history `H'`: it matches
the components of every scale, the localized histories (`H'` at the image component is the image
of `H` at the component), the old parts of every component, and the ripe components. -/
structure HistIso (H H' : RegionHistory S n R k0 K) (σ : TorusSym S n M K) where
  /-- the matching of the components -/
  e : ∀ k, H.Comp k ≃ H'.Comp k
  /-- the localized histories correspond -/
  loc : ∀ k, k ≤ K → ∀ Z : H.Comp k,
    HistImage σ (H.localHistory M K k Z) (H'.localHistory M K k (e k Z))
  /-- the old parts correspond -/
  parts : ∀ (k : ℕ) (Z' : H.Comp (k + 1)) (Y : H.Comp k),
    e k Y ∈ H'.parts k (e (k + 1) Z') ↔ Y ∈ H.parts k Z'
  /-- ripe components correspond -/
  kept : ∀ (k : ℕ) (Z : H.Comp k), IsKept H' k (e k Z) ↔ IsKept H k Z

variable {H H' : RegionHistory S n R k0 K} {σ : LatTorusSym S n M K}

/-- The old parts of corresponding components correspond (`HistIso.parts`). -/
def HistIso.partsEquiv (hiso : HistIso H H' σ.toTorusSym) (k : ℕ) (Z' : H.Comp (k + 1)) :
    ↥(H.parts k Z') ≃ ↥(H'.parts k (hiso.e (k + 1) Z')) where
  toFun Y := ⟨hiso.e k Y.1, (hiso.parts k Z' Y.1).mpr Y.2⟩
  invFun Y' := ⟨(hiso.e k).symm Y'.1, (hiso.parts k Z' _).mp (by
    rw [Equiv.apply_symm_apply]; exact Y'.2)⟩
  left_inv Y := Subtype.ext (by simp)
  right_inv Y' := Subtype.ext (by simp)

/-- The variable of an old part inside the component commutes with `σ`, for any old parts `Y`, `Y'`
of components `Z'`, `Z''` with `H'` at `Z''`, `Y'` the images of `H` at `Z'`, `Y`. -/
theorem symVar_ancInc_of {k : ℕ} {Z' : H.Comp (k + 1)} {Z'' : H'.Comp (k + 1)} {Y : H.Comp k}
    {Y' : H'.Comp k}
    (hI : HistImage σ.toTorusSym (H.localHistory M K (k + 1) Z') (H'.localHistory M K (k + 1) Z''))
    (hIY : HistImage σ.toTorusSym (H.localHistory M K k Y) (H'.localHistory M K k Y'))
    (hk : k ≤ K) (hK : k + 1 ≤ K) (hY : Y ∈ H.parts k Z') (hY' : Y' ∈ H'.parts k Z'')
    (q : InternalVars (H.localHistory M K k Y) k) :
    symVar hI hK (ancInc hK hY q) = ancInc hK hY' (symVar hIY hk q) := by
  apply Subtype.ext
  unfold symVar ancInc
  rfl

theorem symVar_ancInc (hiso : HistIso H H' σ.toTorusSym) {k : ℕ} (hk : k ≤ K) (hK : k + 1 ≤ K) {Y : H.Comp k}
    {Z' : H.Comp (k + 1)} (hY : Y ∈ H.parts k Z') (hY' : hiso.e k Y ∈ H'.parts k (hiso.e (k + 1) Z'))
    (q : InternalVars (H.localHistory M K k Y) k) :
    symVar (hiso.loc (k + 1) hK Z') hK (ancInc hK hY q) =
      ancInc hK hY' (symVar (hiso.loc k hk Y) hk q) :=
  symVar_ancInc_of (hiso.loc (k + 1) hK Z') (hiso.loc k hk Y) hk hK hY hY' q

theorem sub_congr {a : LocalHistory S n M K} {k : ℕ} {A : Set (InternalVars a k)}
    (x : SubCfg N a k A) {p q : InternalVars a k} (hpq : p = q) (hp : p ∈ A) (hq : q ∈ A) :
    VarVal.toEuc (x ⟨p, hp⟩) = VarVal.toEuc (x ⟨q, hq⟩) := by
  subst hpq; rfl

/-- The outputs of old parts correspond under `σ` when the internal variables of the components
do (for any old parts with corresponding localized histories). -/
theorem relOut_ancOut_of {k : ℕ} {Y : H.Comp k} {Y' : H'.Comp k} {Z' : H.Comp (k + 1)}
    {Z'' : H'.Comp (k + 1)}
    (hI : HistImage σ.toTorusSym (H.localHistory M K (k + 1) Z') (H'.localHistory M K (k + 1) Z''))
    (hIY : HistImage σ.toTorusSym (H.localHistory M K k Y) (H'.localHistory M K k Y'))
    (hK : k + 1 ≤ K)
    {A : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
    {A' : Set (InternalVars (H'.localHistory M K (k + 1) Z'') (k + 1))}
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A)
    (x' : SubCfg N (H'.localHistory M K (k + 1) Z'') (k + 1) A')
    (h : RelSub hI hK x x') :
    RelOut σ.toTorusSym (ancOut (R := R) Y Z' x) (ancOut (R := R) Y' Z'' x') := by
  intro y
  classical
  by_cases hy : y ∈ Vblk R (H.localHistory M K k Y) k
  · have hy' : σ.eb k y ∈ Vblk R (H'.localHistory M K k Y') k :=
      (hIY.mem_Vblk H.F.hnn R (by omega) y).mpr hy
    simp only [outField, hy, hy', ↓reduceDIte, ancOut]
    exact h.read_large k y
  · have hy' : σ.eb k y ∉ Vblk R (H'.localHistory M K k Y') k := fun hh =>
      hy ((hIY.mem_Vblk H.F.hnn R (by omega) y).mp hh)
    simp only [outField, hy, hy', ↓reduceDIte]

/-- The outputs of an old part correspond under `σ` when the internal variables of the component
do. -/
theorem relOut_ancOut (hiso : HistIso H H' σ.toTorusSym) {k : ℕ} (hK : k + 1 ≤ K) (Y : H.Comp k)
    (Z' : H.Comp (k + 1))
    {A : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
    {A' : Set (InternalVars (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z')) (k + 1))}
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A)
    (x' : SubCfg N (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z')) (k + 1) A')
    (h : RelSub (hiso.loc (k + 1) hK Z') hK x x') :
    RelOut σ.toTorusSym (ancOut (R := R) Y Z' x) (ancOut (R := R) (hiso.e k Y) (hiso.e (k + 1) Z') x') :=
  relOut_ancOut_of (hiso.loc (k + 1) hK Z') (hiso.loc k (by omega) Y) hK x x' h

theorem ancRestrict_toEuc {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k} {Z' : H.Comp (k + 1)}
    (hY : Y ∈ H.parts k Z') {AY : Set (InternalVars (H.localHistory M K k Y) k)}
    {A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
    (hA : ∀ p ∈ AY, ancInc hK hY p ∈ A') (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A')
    (q : InternalVars (H.localHistory M K k Y) k) (hq : q ∈ AY) :
    VarVal.toEuc ((ancRestrict hK hY hA x) ⟨q, hq⟩) = VarVal.toEuc (x ⟨ancInc hK hY q, hA q hq⟩) :=
  rfl

theorem relSub_newRestrict {k : ℕ} {a a' : LocalHistory S n M K}
    {A : Set (InternalVars a (k + 1))} {A' : Set (InternalVars a' (k + 1))}
    (hI : HistImage σ.toTorusSym a a') (hk : k + 1 ≤ K) (h : newVars a k ⊆ A) (h' : newVars a' k ⊆ A')
    (x : SubCfg N a (k + 1) A) (x' : SubCfg N a' (k + 1) A') (hval : RelVal hI hk x x') :
    RelSub hI hk (newRestrict a h x) (newRestrict a' h' x') :=
  ⟨subCorr_newVars hI hk, fun p hp hp' => hval p (h hp) (h' hp')⟩

/-- The restrictions to old parts of corresponding configurations correspond (for any old parts
with corresponding localized histories). -/
theorem relVal_anc_of {k : ℕ} {Y : H.Comp k} {Y' : H'.Comp k} {Z' : H.Comp (k + 1)}
    {Z'' : H'.Comp (k + 1)}
    (hI : HistImage σ.toTorusSym (H.localHistory M K (k + 1) Z') (H'.localHistory M K (k + 1) Z''))
    (hIY : HistImage σ.toTorusSym (H.localHistory M K k Y) (H'.localHistory M K k Y'))
    (hk : k ≤ K) (hK : k + 1 ≤ K) (hY : Y ∈ H.parts k Z') (hY' : Y' ∈ H'.parts k Z'')
    {AY : Set (InternalVars (H.localHistory M K k Y) k)}
    {AY' : Set (InternalVars (H'.localHistory M K k Y') k)}
    {A : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
    {A' : Set (InternalVars (H'.localHistory M K (k + 1) Z'') (k + 1))}
    (hA : ∀ p ∈ AY, ancInc hK hY p ∈ A)
    (hA' : ∀ p ∈ AY', ancInc hK hY' p ∈ A')
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A)
    (x' : SubCfg N (H'.localHistory M K (k + 1) Z'') (k + 1) A')
    (hval : RelVal hI hK x x') :
    RelVal hIY hk (ancRestrict hK hY hA x) (ancRestrict hK hY' hA' x') := by
  intro q hq hq'
  have e := symVar_ancInc_of hI hIY hk hK hY hY' q
  have hp' : symVar hI hK (ancInc hK hY q) ∈ A' := by
    rw [e]; exact hA' _ hq'
  have h1 := hval (ancInc hK hY q) (hA q hq) hp'
  have h2 : VarVal.toEuc (x' ⟨ancInc hK hY' (symVar hIY hk q), hA' _ hq'⟩) =
      VarVal.toEuc (x' ⟨symVar hI hK (ancInc hK hY q), hp'⟩) :=
    sub_congr x' e.symm _ _
  exact (ancRestrict_toEuc hK hY' hA' x' _ hq').trans
    (h2.trans (h1.trans (ancRestrict_toEuc hK hY hA x q hq).symm))

theorem relVal_anc (hiso : HistIso H H' σ.toTorusSym) {k : ℕ} (hk : k ≤ K) (hK : k + 1 ≤ K) {Y : H.Comp k}
    {Z' : H.Comp (k + 1)} (hY : Y ∈ H.parts k Z')
    (hY' : hiso.e k Y ∈ H'.parts k (hiso.e (k + 1) Z'))
    {AY : Set (InternalVars (H.localHistory M K k Y) k)}
    {AY' : Set (InternalVars (H'.localHistory M K k (hiso.e k Y)) k)}
    {A : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
    {A' : Set (InternalVars (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z')) (k + 1))}
    (hA : ∀ p ∈ AY, ancInc hK hY p ∈ A)
    (hA' : ∀ p ∈ AY', ancInc hK hY' p ∈ A')
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A)
    (x' : SubCfg N (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z')) (k + 1) A')
    (hval : RelVal (hiso.loc (k + 1) hK Z') hK x x') :
    RelVal (hiso.loc k hk Y) hk (ancRestrict hK hY hA x) (ancRestrict hK hY' hA' x') :=
  relVal_anc_of (hiso.loc (k + 1) hK Z') (hiso.loc k hk Y) hk hK hY hY' hA hA' x x' hval

variable (geo : Geo S n R M) (cs : OpConsts) {κs κ : ℕ → LocalHistory S n M K → ℝ}
  {lamHat : ℕ → ℝ} (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ lamHat)
  {hH : H.Admissible} {hH' : H'.Admissible}

/-- The variables of the pre-operators of two components whose old parts correspond (`eqv`), with
corresponding localized histories, correspond: forward inclusion. -/
theorem preVars_corr_fwd_of {k : ℕ} {Z' : H.Comp (k + 1)} {Z'' : H'.Comp (k + 1)}
    (hI : HistImage σ.toTorusSym (H.localHistory M K (k + 1) Z') (H'.localHistory M K (k + 1) Z''))
    (eqv : ↥(H.parts k Z') ≃ ↥(H'.parts k Z''))
    (hIY : ∀ Y : ↥(H.parts k Z'), HistImage σ.toTorusSym (H.localHistory M K k Y.1)
      (H'.localHistory M K k (eqv Y).1))
    (hk' : k ≤ K) (hK : k + 1 ≤ K)
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (sub' : ∀ Y : H'.Comp k, Y ∈ H'.parts k Z'' → OpPkg N R (H'.localHistory M K k Y) k)
    (hcorr : ∀ Y : ↥(H.parts k Z'),
      SubCorr (hIY Y) hk' (sub Y.1 Y.2).A (sub' (eqv Y).1 (eqv Y).2).A)
    (p : InternalVars (H.localHistory M K (k + 1) Z') (k + 1)) (hp : p ∈ preVars hK Z' sub) :
    symVar hI hK p ∈ preVars hK Z'' sub' := by
  rcases hp with hp | ⟨Y, hY, q, hq, hqp⟩
  · exact Or.inl ((subCorr_newVars hI hK p).mp hp)
  · refine Or.inr ⟨(eqv ⟨Y, hY⟩).1, (eqv ⟨Y, hY⟩).2, symVar (hIY ⟨Y, hY⟩) hk' q,
      (hcorr ⟨Y, hY⟩ q).mp hq, ?_⟩
    rw [← hqp]
    exact (symVar_ancInc_of hI (hIY ⟨Y, hY⟩) hk' hK hY (eqv ⟨Y, hY⟩).2 q).symm

theorem preVars_corr_fwd (hiso : HistIso H H' σ.toTorusSym) {k : ℕ} (hk' : k ≤ K) (hK : k + 1 ≤ K)
    (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (sub' : ∀ Y : H'.Comp k, Y ∈ H'.parts k (hiso.e (k + 1) Z') →
      OpPkg N R (H'.localHistory M K k Y) k)
    (hcorr : ∀ Y (hY : Y ∈ H.parts k Z') (hY' : hiso.e k Y ∈ H'.parts k (hiso.e (k + 1) Z')),
      SubCorr (hiso.loc k hk' Y) hk' (sub Y hY).A (sub' (hiso.e k Y) hY').A)
    (p : InternalVars (H.localHistory M K (k + 1) Z') (k + 1)) (hp : p ∈ preVars hK Z' sub) :
    symVar (hiso.loc (k + 1) hK Z') hK p ∈ preVars hK (hiso.e (k + 1) Z') sub' :=
  preVars_corr_fwd_of (hiso.loc (k + 1) hK Z') (hiso.partsEquiv k Z') (fun Y => hiso.loc k hk' Y.1)
    hk' hK sub sub' (fun Y => hcorr Y.1 Y.2 (hiso.partsEquiv k Z' Y).2) p hp

/-- The variables of the pre-operators of two components whose old parts correspond correspond:
backward inclusion. -/
theorem preVars_corr_bwd_of {k : ℕ} {Z' : H.Comp (k + 1)} {Z'' : H'.Comp (k + 1)}
    (hI : HistImage σ.toTorusSym (H.localHistory M K (k + 1) Z') (H'.localHistory M K (k + 1) Z''))
    (eqv : ↥(H.parts k Z') ≃ ↥(H'.parts k Z''))
    (hIY : ∀ Y : ↥(H.parts k Z'), HistImage σ.toTorusSym (H.localHistory M K k Y.1)
      (H'.localHistory M K k (eqv Y).1))
    (hk' : k ≤ K) (hK : k + 1 ≤ K)
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (sub' : ∀ Y : H'.Comp k, Y ∈ H'.parts k Z'' → OpPkg N R (H'.localHistory M K k Y) k)
    (hcorr : ∀ Y : ↥(H.parts k Z'),
      SubCorr (hIY Y) hk' (sub Y.1 Y.2).A (sub' (eqv Y).1 (eqv Y).2).A)
    (p : InternalVars (H.localHistory M K (k + 1) Z') (k + 1))
    (hp : symVar hI hK p ∈ preVars hK Z'' sub') :
    p ∈ preVars hK Z' sub := by
  rcases hp with hp | ⟨Y', hY', q', hq', hq'p⟩
  · exact Or.inl ((subCorr_newVars hI hK p).mpr hp)
  · obtain ⟨Y, hYe⟩ := eqv.surjective ⟨Y', hY'⟩
    have hY1 : (eqv Y).1 = Y' := congrArg Subtype.val hYe
    subst hY1
    obtain ⟨q, rfl⟩ := symVar_surjective (hIY Y) hk' q'
    refine Or.inr ⟨Y.1, Y.2, q, ((hcorr Y) q).mpr hq', ?_⟩
    apply symVar_injective hI hK
    rw [symVar_ancInc_of hI (hIY Y) hk' hK Y.2 hY']
    exact hq'p

theorem preVars_corr_bwd (hiso : HistIso H H' σ.toTorusSym) {k : ℕ} (hk' : k ≤ K) (hK : k + 1 ≤ K)
    (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (sub' : ∀ Y : H'.Comp k, Y ∈ H'.parts k (hiso.e (k + 1) Z') →
      OpPkg N R (H'.localHistory M K k Y) k)
    (hcorr : ∀ Y (hY : Y ∈ H.parts k Z') (hY' : hiso.e k Y ∈ H'.parts k (hiso.e (k + 1) Z')),
      SubCorr (hiso.loc k hk' Y) hk' (sub Y hY).A (sub' (hiso.e k Y) hY').A)
    (p : InternalVars (H.localHistory M K (k + 1) Z') (k + 1))
    (hp : symVar (hiso.loc (k + 1) hK Z') hK p ∈ preVars hK (hiso.e (k + 1) Z') sub') :
    p ∈ preVars hK Z' sub :=
  preVars_corr_bwd_of (hiso.loc (k + 1) hK Z') (hiso.partsEquiv k Z') (fun Y => hiso.loc k hk' Y.1)
    hk' hK sub sub' (fun Y => hcorr Y.1 Y.2 (hiso.partsEquiv k Z' Y).2) p hp

/-- **The pre-operators of two components correspond** when their localized histories correspond
(`hI`) and their old parts correspond (`eqv`) with corresponding localized histories (`hIY`) and
corresponding operators (`hcorr`, `hval`). -/
theorem preOp_euclid_of {k : ℕ} {Z' : H.Comp (k + 1)} {Z'' : H'.Comp (k + 1)}
    (hI : HistImage σ.toTorusSym (H.localHistory M K (k + 1) Z') (H'.localHistory M K (k + 1) Z''))
    (eqv : ↥(H.parts k Z') ≃ ↥(H'.parts k Z''))
    (hIY : ∀ Y : ↥(H.parts k Z'), HistImage σ.toTorusSym (H.localHistory M K k Y.1)
      (H'.localHistory M K k (eqv Y).1))
    (hk' : k ≤ K) (hK : k + 1 ≤ K)
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (sub' : ∀ Y : H'.Comp k, Y ∈ H'.parts k Z'' → OpPkg N R (H'.localHistory M K k Y) k)
    (hcorr : ∀ Y : ↥(H.parts k Z'),
      SubCorr (hIY Y) hk' (sub Y.1 Y.2).A (sub' (eqv Y).1 (eqv Y).2).A)
    (hval : ∀ Y : ↥(H.parts k Z'), ∀ o o' x x' hv (g g' : GIdx S n M K N → ℂ),
      RelOut σ.toTorusSym o o' → RelVal (hIY Y) hk' x x' → RelG σ.toTorusSym g g' →
      (sub' (eqv Y).1 (eqv Y).2).T.K o' x' hv = (sub Y.1 Y.2).T.K o x hv ∧
      (sub' (eqv Y).1 (eqv Y).2).T.b o' x' hv g' = (sub Y.1 Y.2).T.b o x hv g) :
    SubCorr hI hK (preVars hK Z' sub) (preVars hK Z'' sub') ∧
      ∀ o o' (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub))
        (x' : SubCfg N (H'.localHistory M K (k + 1) Z'') (k + 1) (preVars hK Z'' sub')) hv
        (g g' : GIdx S n M K N → ℂ), RelOut σ.toTorusSym o o' →
        RelVal hI hK x x' → RelG σ.toTorusSym g g' →
        (preKernel hK Z'' sub' (SD.ker k (H'.localHistory M K (k + 1) Z''))).K o' x' hv =
          (preKernel hK Z' sub (SD.ker k (H.localHistory M K (k + 1) Z'))).K o x hv ∧
        (preKernel hK Z'' sub' (SD.ker k (H'.localHistory M K (k + 1) Z''))).b o' x' hv g' =
          (preKernel hK Z' sub (SD.ker k (H.localHistory M K (k + 1) Z'))).b o x hv g := by
  have hcorrPre : SubCorr hI hK (preVars hK Z' sub) (preVars hK Z'' sub') := fun p =>
    ⟨preVars_corr_fwd_of hI eqv hIY hk' hK sub sub' hcorr p,
      preVars_corr_bwd_of hI eqv hIY hk' hK sub sub' hcorr p⟩
  refine ⟨hcorrPre, ?_⟩
  intro o o' x x' hv g g' hOut hVal hG
  have hRel : RelSub hI hK x x' := ⟨hcorrPre, hVal⟩
  have hnewRel := relSub_newRestrict hI hK (preVars_new hK Z' sub) (preVars_new hK _ sub') x x' hVal
  have hstepK := SD.euclid_K k σ _ _ hI hK o o' _ _ hv hOut hnewRel
  have hstepb := SD.euclid_b k σ _ _ hI hK o o' _ _ hv g g' hOut hnewRel hG
  have hAnc : ∀ Y : ↥(H.parts k Z'),
      RelOut σ.toTorusSym (ancOut (R := R) Y.1 Z' x) (ancOut (R := R) (eqv Y).1 Z'' x') :=
    fun Y => relOut_ancOut_of hI (hIY Y) hK x x' hRel
  have hAncVal : ∀ Y : ↥(H.parts k Z'),
      RelVal (hIY Y) hk'
        (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) x)
        (ancRestrict hK (eqv Y).2 (preVars_anc hK _ sub' (eqv Y).1 (eqv Y).2) x') :=
    fun Y => relVal_anc_of hI (hIY Y) hk' hK Y.2 (eqv Y).2 _ _ x x' hVal
  refine ⟨?_, ?_⟩
  · have e1 := preKernel_K hK Z'' sub' (SD.ker k (H'.localHistory M K (k + 1) Z'')) o' x' hv
    have e2 := preKernel_K hK Z' sub (SD.ker k (H.localHistory M K (k + 1) Z')) o x hv
    have hprod := Fintype.prod_equiv eqv
      (fun Y : ↥(H.parts k Z') => (sub Y.1 Y.2).T.K (ancOut Y.1 Z' x)
        (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) x) hv)
      (fun Y' : ↥(H'.parts k Z'') => (sub' Y'.1 Y'.2).T.K
        (ancOut Y'.1 Z'' x')
        (ancRestrict hK Y'.2 (preVars_anc hK _ sub' Y'.1 Y'.2) x') hv)
      (fun Y => ((hval Y _ _ _ _ hv g g' (hAnc Y) (hAncVal Y) hG).1).symm)
    exact e1.trans ((congrArg₂ (· * ·) hstepK hprod.symm).trans e2.symm)
  · have e1 := preKernel_b hK Z'' sub' (SD.ker k (H'.localHistory M K (k + 1) Z'')) o' x' hv g'
    have e2 := preKernel_b hK Z' sub (SD.ker k (H.localHistory M K (k + 1) Z')) o x hv g
    have hsum := Fintype.sum_equiv eqv
      (fun Y : ↥(H.parts k Z') => (sub Y.1 Y.2).T.b (ancOut Y.1 Z' x)
        (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) x) hv g)
      (fun Y' : ↥(H'.parts k Z'') => (sub' Y'.1 Y'.2).T.b
        (ancOut Y'.1 Z'' x')
        (ancRestrict hK Y'.2 (preVars_anc hK _ sub' Y'.1 Y'.2) x') hv g')
      (fun Y => ((hval Y _ _ _ _ hv g g' (hAnc Y) (hAncVal Y) hG).2).symm)
    exact e1.trans ((congrArg₂ (· + ·) hstepb hsum.symm).trans e2.symm)

/-- The pre-operators of corresponding components correspond. -/
theorem preOp_euclid (hiso : HistIso H H' σ.toTorusSym) {k : ℕ} (hk' : k ≤ K) (hK : k + 1 ≤ K)
    (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (sub' : ∀ Y : H'.Comp k, Y ∈ H'.parts k (hiso.e (k + 1) Z') →
      OpPkg N R (H'.localHistory M K k Y) k)
    (hcorr : ∀ Y (hY : Y ∈ H.parts k Z') (hY' : hiso.e k Y ∈ H'.parts k (hiso.e (k + 1) Z')),
      SubCorr (hiso.loc k hk' Y) hk' (sub Y hY).A (sub' (hiso.e k Y) hY').A)
    (hval : ∀ Y (hY : Y ∈ H.parts k Z') (hY' : hiso.e k Y ∈ H'.parts k (hiso.e (k + 1) Z'))
      o o' x x' hv (g g' : GIdx S n M K N → ℂ), RelOut σ.toTorusSym o o' →
      RelVal (hiso.loc k hk' Y) hk' x x' → RelG σ.toTorusSym g g' →
      (sub' (hiso.e k Y) hY').T.K o' x' hv = (sub Y hY).T.K o x hv ∧
      (sub' (hiso.e k Y) hY').T.b o' x' hv g' = (sub Y hY).T.b o x hv g) :
    SubCorr (hiso.loc (k + 1) hK Z') hK (preVars hK Z' sub)
        (preVars hK (hiso.e (k + 1) Z') sub') ∧
      ∀ o o' (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub))
        (x' : SubCfg N (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z')) (k + 1)
          (preVars hK (hiso.e (k + 1) Z') sub')) hv (g g' : GIdx S n M K N → ℂ), RelOut σ.toTorusSym o o' →
        RelVal (hiso.loc (k + 1) hK Z') hK x x' → RelG σ.toTorusSym g g' →
        (preKernel hK (hiso.e (k + 1) Z') sub'
          (SD.ker k (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z')))).K o' x' hv =
          (preKernel hK Z' sub (SD.ker k (H.localHistory M K (k + 1) Z'))).K o x hv ∧
        (preKernel hK (hiso.e (k + 1) Z') sub'
          (SD.ker k (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z')))).b o' x' hv g' =
          (preKernel hK Z' sub (SD.ker k (H.localHistory M K (k + 1) Z'))).b o x hv g :=
  preOp_euclid_of geo cs SD (hiso.loc (k + 1) hK Z') (hiso.partsEquiv k Z')
    (fun Y => hiso.loc k hk' Y.1) hk' hK sub sub'
    (fun Y => hcorr Y.1 Y.2 (hiso.partsEquiv k Z' Y).2)
    (fun Y => hval Y.1 Y.2 (hiso.partsEquiv k Z' Y).2)

variable {lab : ∀ k, H.Comp k → Fin 5} {lab' : ∀ k, H'.Comp k → Fin 5}

/-- The descent relation from a component to itself is the equality. -/
theorem desc_self_iff {H₀ : RegionHistory S n R k0 K} {a : ℕ} {Y Z : H₀.Comp a} :
    H₀.Desc a a Y Z ↔ Y = Z := by
  classical
  rw [← mem_ancFin, ancFin_self, Finset.mem_singleton]

/-- The image of a localized history under `σ` is unique. -/
theorem HistImage.unique {σ' : TorusSym S n M K} {a a' a'' : LocalHistory S n M K}
    (h' : HistImage σ' a a') (h'' : HistImage σ' a a'') : a' = a'' := by
  cases a'
  cases a''
  congr 1 <;> funext j
  · exact (h'.Z j).trans (h''.Z j).symm
  · exact (h'.P j).trans (h''.P j).symm
  · exact (h'.Q j).trans (h''.Q j).symm
  · exact (h'.R j).trans (h''.R j).symm
  · exact (h'.Sset j).trans (h''.Sset j).symm
  · exact (h'.OmegaPrime j).trans (h''.OmegaPrime j).symm
  · exact (h'.Omega j).trans (h''.Omega j).symm
  · exact (h'.OmegaDD j).trans (h''.OmegaDD j).symm

/-- **The lineages of related components are related** (from the bijections of the old parts of
related components): every ancestor of `Z` is related to an ancestor of `Z'`, and conversely. -/
theorem desc_of_corr (C : ∀ k, H.Comp k → H'.Comp k → Prop)
    (hparts : ∀ k (Z : H.Comp (k + 1)) (Z' : H'.Comp (k + 1)), C (k + 1) Z Z' →
      ∃ eqv : ↥(H.parts k Z) ≃ ↥(H'.parts k Z'), ∀ Y, C k Y.1 (eqv Y).1) (j : ℕ) (k : ℕ) :
    ∀ (Z : H.Comp k) (Z' : H'.Comp k), C k Z Z' →
      (∀ Y, H.Desc j k Y Z → ∃ Y', H'.Desc j k Y' Z' ∧ C j Y Y') ∧
      (∀ Y', H'.Desc j k Y' Z' → ∃ Y, H.Desc j k Y Z ∧ C j Y Y') := by
  induction k with
  | zero =>
    intro Z Z' hc
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      refine ⟨fun Y hY => ⟨Z', Desc.refl _, (desc_self_iff.1 hY) ▸ hc⟩,
        fun Y' hY' => ⟨Z, Desc.refl _, (desc_self_iff.1 hY') ▸ hc⟩⟩
    · exact ⟨fun Y hY => absurd hY.le (by omega), fun Y' hY' => absurd hY'.le (by omega)⟩
  | succ k ih =>
    intro Z Z' hc
    by_cases hjk : j ≤ k
    · obtain ⟨eqv, heqv⟩ := hparts k Z Z' hc
      constructor
      · intro Y hY
        obtain ⟨c, hcm, hd⟩ := (desc_succ_iff hjk).1 hY
        obtain ⟨Y', hd', hC⟩ := (ih c (eqv ⟨c, hcm⟩).1 (heqv ⟨c, hcm⟩)).1 Y hd
        exact ⟨Y', (desc_succ_iff hjk).2 ⟨_, (eqv ⟨c, hcm⟩).2, hd'⟩, hC⟩
      · intro Y' hY'
        obtain ⟨c', hcm', hd'⟩ := (desc_succ_iff hjk).1 hY'
        have hrel := heqv (eqv.symm ⟨c', hcm'⟩)
        rw [Equiv.apply_symm_apply] at hrel
        obtain ⟨Y, hd, hC⟩ := (ih _ c' hrel).2 Y' hd'
        exact ⟨Y, (desc_succ_iff hjk).2 ⟨_, (eqv.symm ⟨c', hcm'⟩).2, hd⟩, hC⟩
    · rcases Nat.lt_or_ge (k + 1) j with hlt | hge
      · exact ⟨fun Y hY => absurd hY.le (by omega), fun Y' hY' => absurd hY'.le (by omega)⟩
      · obtain rfl : j = k + 1 := by omega
        refine ⟨fun Y hY => ⟨Z', Desc.refl _, (desc_self_iff.1 hY) ▸ hc⟩,
          fun Y' hY' => ⟨Z, Desc.refl _, (desc_self_iff.1 hY') ▸ hc⟩⟩

/-- **The kept-label records of related components correspond** (ruling R28): the kept lineage
components of related components are related, with corresponding localized histories (`hloc`),
ripeness (`hkept`) and labels (`hlab`). -/
theorem locLab_image_of_corr (C : ∀ k, H.Comp k → H'.Comp k → Prop)
    (hloc : ∀ k, k ≤ K → ∀ (Z : H.Comp k) (Z' : H'.Comp k), C k Z Z' →
      HistImage σ.toTorusSym (H.localHistory M K k Z) (H'.localHistory M K k Z'))
    (hkept : ∀ k (Z : H.Comp k) (Z' : H'.Comp k), C k Z Z' → (IsKept H' k Z' ↔ IsKept H k Z))
    (hlab : ∀ k (Z : H.Comp k) (Z' : H'.Comp k), C k Z Z' → IsKept H k Z → lab' k Z' = lab k Z)
    (hparts : ∀ k (Z : H.Comp (k + 1)) (Z' : H'.Comp (k + 1)), C (k + 1) Z Z' →
      ∃ eqv : ↥(H.parts k Z) ≃ ↥(H'.parts k Z'), ∀ Y, C k Y.1 (eqv Y).1)
    {k : ℕ} (hk : k ≤ K) (Z : H.Comp k) (Z' : H'.Comp k) (hc : C k Z Z') :
    LabImage σ.toTorusSym (H.locLab M lab k Z) (H'.locLab M lab' k Z') := by
  intro j a' ϰ
  simp only [RegionHistory.mem_locLab]
  constructor
  · rintro ⟨Y', hj, hd', hkept', hloc', hlab'⟩
    obtain ⟨Y, hd, hC⟩ := (desc_of_corr C hparts j k Z Z' hc).2 Y' hd'
    have hkY : IsKept H j Y := (hkept j Y Y' hC).1 hkept'
    refine ⟨H.localHistory M K j Y, ⟨Y, hj, hd, hkY, rfl, ?_⟩, ?_⟩
    · rw [← hlab j Y Y' hC hkY]; exact hlab'
    · rw [← hloc']; exact hloc j (by omega) Y Y' hC
  · rintro ⟨a, ⟨Y, hj, hd, hkY, hlocY, hlabY⟩, hI⟩
    obtain ⟨Y', hd', hC⟩ := (desc_of_corr C hparts j k Z Z' hc).1 Y hd
    refine ⟨Y', hj, hd', (hkept j Y Y' hC).2 hkY, ?_, ?_⟩
    · subst hlocY
      exact HistImage.unique (hloc j (by omega) Y Y' hC) hI
    · rw [hlab j Y Y' hC hkY]; exact hlabY

/-- **The operators of corresponding components correspond** (the core of Lemma II.5.10): for a
relation `C` between the components of `H` and of `H'` under which the localized histories
correspond (`hloc`), the ripe components correspond (`hkept`), the labels of the kept components
agree (`hlab`), and the old parts of related components are matched by a bijection of related parts
(`hparts`), the operators of related components correspond. -/
theorem locOp_euclid_of_corr (C : ∀ k, H.Comp k → H'.Comp k → Prop)
    (hloc : ∀ k, k ≤ K → ∀ (Z : H.Comp k) (Z' : H'.Comp k), C k Z Z' →
      HistImage σ.toTorusSym (H.localHistory M K k Z) (H'.localHistory M K k Z'))
    (hkept : ∀ k (Z : H.Comp k) (Z' : H'.Comp k), C k Z Z' → (IsKept H' k Z' ↔ IsKept H k Z))
    (hlab : ∀ k (Z : H.Comp k) (Z' : H'.Comp k), C k Z Z' → IsKept H k Z → lab' k Z' = lab k Z)
    (hparts : ∀ k (Z : H.Comp (k + 1)) (Z' : H'.Comp (k + 1)), C (k + 1) Z Z' →
      ∃ eqv : ↥(H.parts k Z) ≃ ↥(H'.parts k Z'), ∀ Y, C k Y.1 (eqv Y).1)
    (k : ℕ) :
    ∀ (hk : k ≤ K) (Z : H.Comp k) (Z' : H'.Comp k) (hc : C k Z Z'),
      SubCorr (hloc k hk Z Z' hc) hk (locOp geo cs SD KD hH lab k hk Z).A
        (locOp geo cs SD KD hH' lab' k hk Z').A ∧
      ∀ o o' (x : SubCfg N (H.localHistory M K k Z) k (locOp geo cs SD KD hH lab k hk Z).A)
        (x' : SubCfg N (H'.localHistory M K k Z') k (locOp geo cs SD KD hH' lab' k hk Z').A) hv
        (g g' : GIdx S n M K N → ℂ),
        RelOut σ.toTorusSym o o' → RelVal (hloc k hk Z Z' hc) hk x x' → RelG σ.toTorusSym g g' →
        (locOp geo cs SD KD hH' lab' k hk Z').T.K o' x' hv =
            (locOp geo cs SD KD hH lab k hk Z).T.K o x hv ∧
          (locOp geo cs SD KD hH' lab' k hk Z').T.b o' x' hv g' =
            (locOp geo cs SD KD hH lab k hk Z).T.b o x hv g := by
  induction k with
  | zero => intro hk Z; exact (H.F.isEmpty_comp_zero.false Z).elim
  | succ k ih =>
    intro hk Z' Z'' hc
    have hk0 : k ≤ K := by omega
    by_cases hkc : IsKept H (k + 1) Z'
    · have hc' : IsKept H' (k + 1) Z'' := (hkept (k + 1) Z' Z'' hc).mpr hkc
      have e := locOp_kept geo cs SD KD (lab := lab) (hH := hH) hk hkc
      have e' := locOp_kept geo cs SD KD (lab := lab') (hH := hH') hk hc'
      have key : ∀ (P : OpPkg N R (H.localHistory M K (k + 1) Z') (k + 1))
          (P' : OpPkg N R (H'.localHistory M K (k + 1) Z'') (k + 1)),
          P = keptOp geo cs KD hH lab Z' hkc.1 hkc.2.1 hkc.2.2 (lab (k + 1) Z') →
          P' = keptOp geo cs KD hH' lab' Z'' hc'.1 hc'.2.1 hc'.2.2 (lab' (k + 1) Z'') →
          SubCorr (hloc (k + 1) hk Z' Z'' hc) hk P.A P'.A ∧
          ∀ o o' (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A)
            (x' : SubCfg N (H'.localHistory M K (k + 1) Z'') (k + 1) P'.A) hv
            (g g' : GIdx S n M K N → ℂ),
            RelOut σ.toTorusSym o o' → RelVal (hloc (k + 1) hk Z' Z'' hc) hk x x' →
            RelG σ.toTorusSym g g' →
            P'.T.K o' x' hv = P.T.K o x hv ∧ P'.T.b o' x' hv g' = P.T.b o x hv g := by
        intro P P' hP hP'
        subst hP hP'
        have hℓ := locLab_image_of_corr (M := M) C hloc hkept hlab hparts hk Z' Z'' hc
        rw [hlab (k + 1) Z' Z'' hc hkc]
        refine ⟨fun p => KD.euclid_I (k + 1) σ _ _ _ _ (hloc (k + 1) hk Z' Z'' hc) hℓ hk _ p, ?_⟩
        intro o o' x x' hv g g' hOut hVal hG
        exact ⟨KD.euclid_K (k + 1) σ _ _ _ _ (hloc (k + 1) hk Z' Z'' hc) hℓ hk _ o o' x x' hv hOut
            ⟨fun p => KD.euclid_I (k + 1) σ _ _ _ _ (hloc (k + 1) hk Z' Z'' hc) hℓ hk _ p, hVal⟩,
          KD.euclid_b (k + 1) σ _ _ _ _ (hloc (k + 1) hk Z' Z'' hc) hℓ hk _ o o' x x' hv g g'
            hOut ⟨fun p => KD.euclid_I (k + 1) σ _ _ _ _ (hloc (k + 1) hk Z' Z'' hc) hℓ hk _ p,
              hVal⟩ hG⟩
      exact key _ _ e e'
    · have hc' : ¬ IsKept H' (k + 1) Z'' := fun h => hkc ((hkept (k + 1) Z' Z'' hc).mp h)
      have e := locOp_level geo cs SD KD (lab := lab) (hH := hH) hk hkc
      have e' := locOp_level geo cs SD KD (lab := lab') (hH := hH') hk hc'
      obtain ⟨eqv, heqv⟩ := hparts k Z' Z'' hc
      have key : ∀ (P : OpPkg N R (H.localHistory M K (k + 1) Z') (k + 1))
          (P' : OpPkg N R (H'.localHistory M K (k + 1) Z'') (k + 1)),
          P = preOp geo cs SD hH hk Z'
            (fun Y _ => locOp geo cs SD KD hH lab k hk0 Y) →
          P' = preOp geo cs SD hH' hk Z''
            (fun Y _ => locOp geo cs SD KD hH' lab' k hk0 Y) →
          SubCorr (hloc (k + 1) hk Z' Z'' hc) hk P.A P'.A ∧
          ∀ o o' (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A)
            (x' : SubCfg N (H'.localHistory M K (k + 1) Z'') (k + 1) P'.A) hv
            (g g' : GIdx S n M K N → ℂ),
            RelOut σ.toTorusSym o o' → RelVal (hloc (k + 1) hk Z' Z'' hc) hk x x' →
            RelG σ.toTorusSym g g' →
            P'.T.K o' x' hv = P.T.K o x hv ∧ P'.T.b o' x' hv g' = P.T.b o x hv g := by
        intro P P' hP hP'
        subst hP hP'
        exact preOp_euclid_of geo cs SD (hloc (k + 1) hk Z' Z'' hc) eqv
          (fun Y => hloc k hk0 Y.1 (eqv Y).1 (heqv Y)) hk0 hk _ _
          (fun Y => (ih hk0 Y.1 (eqv Y).1 (heqv Y)).1)
          (fun Y o o' x x' hv g g' hOut hVal hG =>
            (ih hk0 Y.1 (eqv Y).1 (heqv Y)).2 o o' x x' hv g g' hOut hVal hG)
      exact key _ _ (by rw [e]) (by rw [e'])

/-- **Lemma II.5.10 (Euclidean covariance)**: if a Euclidean symmetry `σ` maps the region history
`H` to `H'` (`HistIso`), the operators of corresponding components correspond: the integrated
variables correspond (`SubCorr`) and the kernels and exponents take the same values at
corresponding configurations of the output, of the internal variables and of the external field.
The statement is by induction along the lineage, using the Euclidean covariance of the step and
kept data (`locOp_euclid_of_corr` at the relation `Z' = e Z`). -/
theorem locOp_euclid_invariant (hiso : HistIso H H' σ.toTorusSym)
    (hlab : ∀ k (Z : H.Comp k), lab' k (hiso.e k Z) = lab k Z) (k : ℕ) :
    ∀ (hk : k ≤ K) (Z : H.Comp k),
      SubCorr (hiso.loc k hk Z) hk (locOp geo cs SD KD hH lab k hk Z).A
        (locOp geo cs SD KD hH' lab' k hk (hiso.e k Z)).A ∧
      ∀ o o' (x : SubCfg N (H.localHistory M K k Z) k (locOp geo cs SD KD hH lab k hk Z).A)
        (x' : SubCfg N (H'.localHistory M K k (hiso.e k Z)) k
          (locOp geo cs SD KD hH' lab' k hk (hiso.e k Z)).A) hv (g g' : GIdx S n M K N → ℂ),
        RelOut σ.toTorusSym o o' → RelVal (hiso.loc k hk Z) hk x x' → RelG σ.toTorusSym g g' →
        (locOp geo cs SD KD hH' lab' k hk (hiso.e k Z)).T.K o' x' hv =
            (locOp geo cs SD KD hH lab k hk Z).T.K o x hv ∧
          (locOp geo cs SD KD hH' lab' k hk (hiso.e k Z)).T.b o' x' hv g' =
            (locOp geo cs SD KD hH lab k hk Z).T.b o x hv g := fun hk Z =>
  locOp_euclid_of_corr geo cs SD KD (fun k Z Z' => Z' = hiso.e k Z)
    (fun k hk Z Z' h => by subst h; exact hiso.loc k hk Z)
    (fun k Z Z' h => by subst h; exact hiso.kept k Z)
    (fun k Z Z' h _ => by subst h; exact hlab k Z)
    (fun k Z Z' h => by subst h; exact ⟨hiso.partsEquiv k Z, fun _ => rfl⟩)
    k hk Z (hiso.e k Z) rfl

end Euclid

end Balaban.LargeField
