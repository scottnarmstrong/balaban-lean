module

public import Balaban.LargeField.Operators.LocOp

/-!
# Invariance of the localized operators (Part II, Lemma II.5.10, block J7)

The data (S0), (S1), (S3) are invariant under `O(N)` acting on all spin-valued variables, on the
output, on `h` and on `g` (`StepData.rot_K`, `rot_b`, `KeptData.rot_K`, `rot_b`), and the
reading maps of the recursion (restriction to the new variables, to the variables of an old part,
and the output of an old part, i.e. the variable `ψ_k`) commute with the rotation.  Hence the
localized operators are invariant (`locOp_rot_invariant`).

Euclidean invariance (`locOp_euclid_invariant`): a Euclidean symmetry of the torus that
preserves the localized history and the sets of blocks acts on the variables by permuting
blocks; the data are required to be invariant under such symmetries (`SymData`), and the
operators then are, by the same induction.
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

end Balaban.LargeField
