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

variable {H : RegionHistory S n R k0}

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
          P = keptOp geo cs KD hH Z' hc.1 hc.2.1 hc.2.2 (lab (k + 1) Z') →
          ∀ (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A),
            P.T.K (rotOut ρ o) (rotSub ρ x) (ρ hv) = P.T.K o x hv ∧
            P.T.b (rotOut ρ o) (rotSub ρ x) (ρ hv) (rotG ρ g) = P.T.b o x hv g := by
        intro P hP
        subst hP
        intro x
        exact ⟨KD.rot_K (k + 1) _ _ ρ o x hv, KD.rot_b (k + 1) _ _ ρ o x hv g⟩
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
structure HistIso (H H' : RegionHistory S n R k0) (σ : TorusSym S n M K) where
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

variable {H H' : RegionHistory S n R k0} {σ : TorusSym S n M K}

theorem symVar_ancInc (hiso : HistIso H H' σ) {k : ℕ} (hk : k ≤ K) (hK : k + 1 ≤ K) {Y : H.Comp k}
    {Z' : H.Comp (k + 1)} (hY : Y ∈ H.parts k Z') (hY' : hiso.e k Y ∈ H'.parts k (hiso.e (k + 1) Z'))
    (q : InternalVars (H.localHistory M K k Y) k) :
    symVar (hiso.loc (k + 1) hK Z') hK (ancInc hK hY q) =
      ancInc hK hY' (symVar (hiso.loc k hk Y) hk q) := by
  apply Subtype.ext
  unfold symVar ancInc
  rfl

theorem sub_congr {a : LocalHistory S n M K} {k : ℕ} {A : Set (InternalVars a k)}
    (x : SubCfg N a k A) {p q : InternalVars a k} (hpq : p = q) (hp : p ∈ A) (hq : q ∈ A) :
    VarVal.toEuc (x ⟨p, hp⟩) = VarVal.toEuc (x ⟨q, hq⟩) := by
  subst hpq; rfl

/-- The outputs of an old part correspond under `σ` when the internal variables of the component
do. -/
theorem relOut_ancOut (hiso : HistIso H H' σ) {k : ℕ} (hK : k + 1 ≤ K) (Y : H.Comp k)
    (Z' : H.Comp (k + 1))
    {A : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
    {A' : Set (InternalVars (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z')) (k + 1))}
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A)
    (x' : SubCfg N (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z')) (k + 1) A')
    (h : RelSub (hiso.loc (k + 1) hK Z') hK x x') :
    RelOut σ (ancOut (R := R) Y Z' x) (ancOut (R := R) (hiso.e k Y) (hiso.e (k + 1) Z') x') := by
  intro y
  classical
  by_cases hy : y ∈ Vblk R (H.localHistory M K k Y) k
  · have hy' : σ.eb k y ∈ Vblk R (H'.localHistory M K k (hiso.e k Y)) k :=
      ((hiso.loc k (by omega) Y).mem_Vblk H.F.hnn R (by omega) y).mpr hy
    simp only [outField, hy, hy', ↓reduceDIte, ancOut]
    exact h.read_large k y
  · have hy' : σ.eb k y ∉ Vblk R (H'.localHistory M K k (hiso.e k Y)) k := fun hh =>
      hy (((hiso.loc k (by omega) Y).mem_Vblk H.F.hnn R (by omega) y).mp hh)
    simp only [outField, hy, hy', ↓reduceDIte]

theorem ancRestrict_toEuc {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k} {Z' : H.Comp (k + 1)}
    (hY : Y ∈ H.parts k Z') {AY : Set (InternalVars (H.localHistory M K k Y) k)}
    {A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
    (hA : ∀ p ∈ AY, ancInc hK hY p ∈ A') (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A')
    (q : InternalVars (H.localHistory M K k Y) k) (hq : q ∈ AY) :
    VarVal.toEuc ((ancRestrict hK hY hA x) ⟨q, hq⟩) = VarVal.toEuc (x ⟨ancInc hK hY q, hA q hq⟩) :=
  rfl

theorem relSub_newRestrict {k : ℕ} {a a' : LocalHistory S n M K}
    {A : Set (InternalVars a (k + 1))} {A' : Set (InternalVars a' (k + 1))}
    (hI : HistImage σ a a') (hk : k + 1 ≤ K) (h : newVars a k ⊆ A) (h' : newVars a' k ⊆ A')
    (x : SubCfg N a (k + 1) A) (x' : SubCfg N a' (k + 1) A') (hval : RelVal hI hk x x') :
    RelSub hI hk (newRestrict a h x) (newRestrict a' h' x') :=
  ⟨subCorr_newVars hI hk, fun p hp hp' => hval p (h hp) (h' hp')⟩

theorem relVal_anc (hiso : HistIso H H' σ) {k : ℕ} (hk : k ≤ K) (hK : k + 1 ≤ K) {Y : H.Comp k}
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
    RelVal (hiso.loc k hk Y) hk (ancRestrict hK hY hA x) (ancRestrict hK hY' hA' x') := by
  intro q hq hq'
  have e := symVar_ancInc hiso hk hK hY hY' q
  have hp' : symVar (hiso.loc (k + 1) hK Z') hK (ancInc hK hY q) ∈ A' := by
    rw [e]; exact hA' _ hq'
  have h1 := hval (ancInc hK hY q) (hA q hq) hp'
  have h2 : VarVal.toEuc (x' ⟨ancInc hK hY' (symVar (hiso.loc k hk Y) hk q), hA' _ hq'⟩) =
      VarVal.toEuc (x' ⟨symVar (hiso.loc (k + 1) hK Z') hK (ancInc hK hY q), hp'⟩) :=
    sub_congr x' e.symm _ _
  exact (ancRestrict_toEuc hK hY' hA' x' _ hq').trans
    (h2.trans (h1.trans (ancRestrict_toEuc hK hY hA x q hq).symm))

variable (geo : Geo S n R M) (cs : OpConsts) {κs κ : ℕ → LocalHistory S n M K → ℝ}
  {lamHat : ℕ → ℝ} (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ lamHat)
  {hH : H.Admissible} {hH' : H'.Admissible}

theorem preVars_corr_fwd (hiso : HistIso H H' σ) {k : ℕ} (hk' : k ≤ K) (hK : k + 1 ≤ K)
    (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (sub' : ∀ Y : H'.Comp k, Y ∈ H'.parts k (hiso.e (k + 1) Z') →
      OpPkg N R (H'.localHistory M K k Y) k)
    (hcorr : ∀ Y (hY : Y ∈ H.parts k Z') (hY' : hiso.e k Y ∈ H'.parts k (hiso.e (k + 1) Z')),
      SubCorr (hiso.loc k hk' Y) hk' (sub Y hY).A (sub' (hiso.e k Y) hY').A)
    (p : InternalVars (H.localHistory M K (k + 1) Z') (k + 1)) (hp : p ∈ preVars hK Z' sub) :
    symVar (hiso.loc (k + 1) hK Z') hK p ∈ preVars hK (hiso.e (k + 1) Z') sub' := by
  rcases hp with hp | ⟨Y, hY, q, hq, hqp⟩
  · exact Or.inl ((subCorr_newVars (hiso.loc (k + 1) hK Z') hK p).mp hp)
  · have hY' := (hiso.parts k Z' Y).mpr hY
    refine Or.inr ⟨hiso.e k Y, hY', symVar (hiso.loc k hk' Y) hk' q, (hcorr Y hY hY' q).mp hq, ?_⟩
    rw [← hqp]
    exact (symVar_ancInc hiso hk' hK hY hY' q).symm

theorem preVars_corr_bwd (hiso : HistIso H H' σ) {k : ℕ} (hk' : k ≤ K) (hK : k + 1 ≤ K)
    (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (sub' : ∀ Y : H'.Comp k, Y ∈ H'.parts k (hiso.e (k + 1) Z') →
      OpPkg N R (H'.localHistory M K k Y) k)
    (hcorr : ∀ Y (hY : Y ∈ H.parts k Z') (hY' : hiso.e k Y ∈ H'.parts k (hiso.e (k + 1) Z')),
      SubCorr (hiso.loc k hk' Y) hk' (sub Y hY).A (sub' (hiso.e k Y) hY').A)
    (p : InternalVars (H.localHistory M K (k + 1) Z') (k + 1))
    (hp : symVar (hiso.loc (k + 1) hK Z') hK p ∈ preVars hK (hiso.e (k + 1) Z') sub') :
    p ∈ preVars hK Z' sub := by
  rcases hp with hp | ⟨Y', hY', q', hq', hq'p⟩
  · exact Or.inl ((subCorr_newVars (hiso.loc (k + 1) hK Z') hK p).mpr hp)
  · obtain ⟨Y, rfl⟩ := (hiso.e k).surjective Y'
    obtain ⟨q, rfl⟩ := symVar_surjective (hiso.loc k hk' Y) hk' q'
    have hY : Y ∈ H.parts k Z' := (hiso.parts k Z' Y).mp hY'
    refine Or.inr ⟨Y, hY, q, ((hcorr Y hY hY') q).mpr hq', ?_⟩
    apply symVar_injective (hiso.loc (k + 1) hK Z') hK
    rw [symVar_ancInc hiso hk' hK hY hY']
    exact hq'p

/-- The pre-operators of corresponding components correspond. -/
theorem preOp_euclid (hiso : HistIso H H' σ) {k : ℕ} (hk' : k ≤ K) (hK : k + 1 ≤ K)
    (Z' : H.Comp (k + 1))
    (sub : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → OpPkg N R (H.localHistory M K k Y) k)
    (sub' : ∀ Y : H'.Comp k, Y ∈ H'.parts k (hiso.e (k + 1) Z') →
      OpPkg N R (H'.localHistory M K k Y) k)
    (hcorr : ∀ Y (hY : Y ∈ H.parts k Z') (hY' : hiso.e k Y ∈ H'.parts k (hiso.e (k + 1) Z')),
      SubCorr (hiso.loc k hk' Y) hk' (sub Y hY).A (sub' (hiso.e k Y) hY').A)
    (hval : ∀ Y (hY : Y ∈ H.parts k Z') (hY' : hiso.e k Y ∈ H'.parts k (hiso.e (k + 1) Z'))
      o o' x x' hv (g g' : GIdx S n M K N → ℂ), RelOut σ o o' →
      RelVal (hiso.loc k hk' Y) hk' x x' → RelG σ g g' →
      (sub' (hiso.e k Y) hY').T.K o' x' hv = (sub Y hY).T.K o x hv ∧
      (sub' (hiso.e k Y) hY').T.b o' x' hv g' = (sub Y hY).T.b o x hv g) :
    SubCorr (hiso.loc (k + 1) hK Z') hK (preVars hK Z' sub)
        (preVars hK (hiso.e (k + 1) Z') sub') ∧
      ∀ o o' (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) (preVars hK Z' sub))
        (x' : SubCfg N (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z')) (k + 1)
          (preVars hK (hiso.e (k + 1) Z') sub')) hv (g g' : GIdx S n M K N → ℂ), RelOut σ o o' →
        RelVal (hiso.loc (k + 1) hK Z') hK x x' → RelG σ g g' →
        (preKernel hK (hiso.e (k + 1) Z') sub'
          (SD.ker k (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z')))).K o' x' hv =
          (preKernel hK Z' sub (SD.ker k (H.localHistory M K (k + 1) Z'))).K o x hv ∧
        (preKernel hK (hiso.e (k + 1) Z') sub'
          (SD.ker k (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z')))).b o' x' hv g' =
          (preKernel hK Z' sub (SD.ker k (H.localHistory M K (k + 1) Z'))).b o x hv g := by
  have hcorrPre : SubCorr (hiso.loc (k + 1) hK Z') hK (preVars hK Z' sub)
      (preVars hK (hiso.e (k + 1) Z') sub') := fun p =>
    ⟨preVars_corr_fwd hiso hk' hK Z' sub sub' hcorr p, preVars_corr_bwd hiso hk' hK Z' sub sub' hcorr p⟩
  refine ⟨hcorrPre, ?_⟩
  intro o o' x x' hv g g' hOut hVal hG
  have hRel : RelSub (hiso.loc (k + 1) hK Z') hK x x' := ⟨hcorrPre, hVal⟩
  let eqv : ↥(H.parts k Z') ≃ ↥(H'.parts k (hiso.e (k + 1) Z')) :=
    { toFun := fun Y => ⟨hiso.e k Y.1, (hiso.parts k Z' Y.1).mpr Y.2⟩
      invFun := fun Y' => ⟨(hiso.e k).symm Y'.1, (hiso.parts k Z' _).mp (by
        rw [Equiv.apply_symm_apply]; exact Y'.2)⟩
      left_inv := fun Y => Subtype.ext (by simp)
      right_inv := fun Y' => Subtype.ext (by simp) }
  have hnewRel := relSub_newRestrict (hiso.loc (k + 1) hK Z') hK (preVars_new hK Z' sub)
    (preVars_new hK _ sub') x x' hVal
  have hstepK := SD.euclid_K k σ _ _ (hiso.loc (k + 1) hK Z') hK o o' _ _ hv hOut hnewRel
  have hstepb := SD.euclid_b k σ _ _ (hiso.loc (k + 1) hK Z') hK o o' _ _ hv g g' hOut hnewRel hG
  have hAnc : ∀ Y : ↥(H.parts k Z'),
      RelOut σ (ancOut (R := R) Y.1 Z' x) (ancOut (R := R) (hiso.e k Y.1) (hiso.e (k + 1) Z') x') :=
    fun Y => relOut_ancOut hiso hK Y.1 Z' x x' hRel
  have hAncVal : ∀ Y : ↥(H.parts k Z'),
      RelVal (hiso.loc k hk' Y.1) hk'
        (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) x)
        (ancRestrict hK (eqv Y).2 (preVars_anc hK _ sub' (hiso.e k Y.1) (eqv Y).2) x') :=
    fun Y => relVal_anc hiso hk' hK Y.2 (eqv Y).2 _ _ x x' hVal
  refine ⟨?_, ?_⟩
  · have e1 := preKernel_K hK (hiso.e (k + 1) Z') sub'
      (SD.ker k (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z'))) o' x' hv
    have e2 := preKernel_K hK Z' sub (SD.ker k (H.localHistory M K (k + 1) Z')) o x hv
    have hprod := Fintype.prod_equiv eqv
      (fun Y : ↥(H.parts k Z') => (sub Y.1 Y.2).T.K (ancOut Y.1 Z' x)
        (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) x) hv)
      (fun Y' : ↥(H'.parts k (hiso.e (k + 1) Z')) => (sub' Y'.1 Y'.2).T.K
        (ancOut Y'.1 (hiso.e (k + 1) Z') x')
        (ancRestrict hK Y'.2 (preVars_anc hK _ sub' Y'.1 Y'.2) x') hv)
      (fun Y => ((hval Y.1 Y.2 (eqv Y).2 _ _ _ _ hv g g' (hAnc Y) (hAncVal Y) hG).1).symm)
    exact e1.trans ((congrArg₂ (· * ·) hstepK hprod.symm).trans e2.symm)
  · have e1 := preKernel_b hK (hiso.e (k + 1) Z') sub'
      (SD.ker k (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z'))) o' x' hv g'
    have e2 := preKernel_b hK Z' sub (SD.ker k (H.localHistory M K (k + 1) Z')) o x hv g
    have hsum := Fintype.sum_equiv eqv
      (fun Y : ↥(H.parts k Z') => (sub Y.1 Y.2).T.b (ancOut Y.1 Z' x)
        (ancRestrict hK Y.2 (preVars_anc hK Z' sub Y.1 Y.2) x) hv g)
      (fun Y' : ↥(H'.parts k (hiso.e (k + 1) Z')) => (sub' Y'.1 Y'.2).T.b
        (ancOut Y'.1 (hiso.e (k + 1) Z') x')
        (ancRestrict hK Y'.2 (preVars_anc hK _ sub' Y'.1 Y'.2) x') hv g')
      (fun Y => ((hval Y.1 Y.2 (eqv Y).2 _ _ _ _ hv g g' (hAnc Y) (hAncVal Y) hG).2).symm)
    exact e1.trans ((congrArg₂ (· + ·) hstepb hsum.symm).trans e2.symm)

variable {lab : ∀ k, H.Comp k → Fin 5} {lab' : ∀ k, H'.Comp k → Fin 5}

/-- **Lemma II.5.10 (Euclidean covariance)**: if a Euclidean symmetry `σ` maps the region history
`H` to `H'` (`HistIso`), the operators of corresponding components correspond: the integrated
variables correspond (`SubCorr`) and the kernels and exponents take the same values at
corresponding configurations of the output, of the internal variables and of the external field.
The statement is by induction along the lineage, using the Euclidean covariance of the step and
kept data. -/
theorem locOp_euclid_invariant (hiso : HistIso H H' σ)
    (hlab : ∀ k (Z : H.Comp k), lab' k (hiso.e k Z) = lab k Z) (k : ℕ) :
    ∀ (hk : k ≤ K) (Z : H.Comp k),
      SubCorr (hiso.loc k hk Z) hk (locOp geo cs SD KD hH lab k hk Z).A
        (locOp geo cs SD KD hH' lab' k hk (hiso.e k Z)).A ∧
      ∀ o o' (x : SubCfg N (H.localHistory M K k Z) k (locOp geo cs SD KD hH lab k hk Z).A)
        (x' : SubCfg N (H'.localHistory M K k (hiso.e k Z)) k
          (locOp geo cs SD KD hH' lab' k hk (hiso.e k Z)).A) hv (g g' : GIdx S n M K N → ℂ),
        RelOut σ o o' → RelVal (hiso.loc k hk Z) hk x x' → RelG σ g g' →
        (locOp geo cs SD KD hH' lab' k hk (hiso.e k Z)).T.K o' x' hv =
            (locOp geo cs SD KD hH lab k hk Z).T.K o x hv ∧
          (locOp geo cs SD KD hH' lab' k hk (hiso.e k Z)).T.b o' x' hv g' =
            (locOp geo cs SD KD hH lab k hk Z).T.b o x hv g := by
  induction k with
  | zero => intro hk Z; exact (H.F.isEmpty_comp_zero.false Z).elim
  | succ k ih =>
    intro hk Z'
    have hk0 : k ≤ K := by omega
    by_cases hc : IsKept H (k + 1) Z'
    · have hc' : IsKept H' (k + 1) (hiso.e (k + 1) Z') := (hiso.kept (k + 1) Z').mpr hc
      have e := locOp_kept geo cs SD KD (lab := lab) (hH := hH) hk hc
      have e' := locOp_kept geo cs SD KD (lab := lab') (hH := hH') hk hc'
      have key : ∀ (P : OpPkg N R (H.localHistory M K (k + 1) Z') (k + 1))
          (P' : OpPkg N R (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z')) (k + 1)),
          P = keptOp geo cs KD hH Z' hc.1 hc.2.1 hc.2.2 (lab (k + 1) Z') →
          P' = keptOp geo cs KD hH' (hiso.e (k + 1) Z') hc'.1 hc'.2.1 hc'.2.2
            (lab' (k + 1) (hiso.e (k + 1) Z')) →
          SubCorr (hiso.loc (k + 1) hk Z') hk P.A P'.A ∧
          ∀ o o' (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A)
            (x' : SubCfg N (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z')) (k + 1) P'.A) hv
            (g g' : GIdx S n M K N → ℂ),
            RelOut σ o o' → RelVal (hiso.loc (k + 1) hk Z') hk x x' → RelG σ g g' →
            P'.T.K o' x' hv = P.T.K o x hv ∧ P'.T.b o' x' hv g' = P.T.b o x hv g := by
        intro P P' hP hP'
        subst hP hP'
        rw [hlab (k + 1) Z']
        refine ⟨fun p => KD.euclid_I (k + 1) σ _ _ (hiso.loc (k + 1) hk Z') hk _ p, ?_⟩
        intro o o' x x' hv g g' hOut hVal hG
        exact ⟨KD.euclid_K (k + 1) σ _ _ (hiso.loc (k + 1) hk Z') hk _ o o' x x' hv hOut
            ⟨fun p => KD.euclid_I (k + 1) σ _ _ (hiso.loc (k + 1) hk Z') hk _ p, hVal⟩,
          KD.euclid_b (k + 1) σ _ _ (hiso.loc (k + 1) hk Z') hk _ o o' x x' hv g g' hOut
            ⟨fun p => KD.euclid_I (k + 1) σ _ _ (hiso.loc (k + 1) hk Z') hk _ p, hVal⟩ hG⟩
      exact key _ _ e e'
    · have hc' : ¬ IsKept H' (k + 1) (hiso.e (k + 1) Z') := fun h => hc ((hiso.kept (k + 1) Z').mp h)
      have e := locOp_level geo cs SD KD (lab := lab) (hH := hH) hk hc
      have e' := locOp_level geo cs SD KD (lab := lab') (hH := hH') hk hc'
      have key : ∀ (P : OpPkg N R (H.localHistory M K (k + 1) Z') (k + 1))
          (P' : OpPkg N R (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z')) (k + 1)),
          P = preOp geo cs SD hH hk Z'
            (fun Y _ => locOp geo cs SD KD hH lab k hk0 Y) →
          P' = preOp geo cs SD hH' hk (hiso.e (k + 1) Z')
            (fun Y _ => locOp geo cs SD KD hH' lab' k hk0 Y) →
          SubCorr (hiso.loc (k + 1) hk Z') hk P.A P'.A ∧
          ∀ o o' (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A)
            (x' : SubCfg N (H'.localHistory M K (k + 1) (hiso.e (k + 1) Z')) (k + 1) P'.A) hv
            (g g' : GIdx S n M K N → ℂ),
            RelOut σ o o' → RelVal (hiso.loc (k + 1) hk Z') hk x x' → RelG σ g g' →
            P'.T.K o' x' hv = P.T.K o x hv ∧ P'.T.b o' x' hv g' = P.T.b o x hv g := by
        intro P P' hP hP'
        subst hP hP'
        exact preOp_euclid geo cs SD hiso hk0 hk Z' _ _
          (fun Y hY hY' => (ih hk0 Y).1)
          (fun Y hY hY' o o' x x' hv g g' hOut hVal hG => (ih hk0 Y).2 o o' x x' hv g g' hOut hVal hG)
      exact key _ _ (by rw [e]) (by rw [e'])

end Euclid

end Balaban.LargeField
