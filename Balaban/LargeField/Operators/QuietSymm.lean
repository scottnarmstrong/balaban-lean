/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.Quiet
public import Balaban.LargeField.Operators.Invariance
public import Balaban.Model.BlockStructure
public import Balaban.Background.EquivarianceDomain

/-!
# `O(N)`-invariance of the main action and of the quiet kernel (Part II, Lemma II.5.10)

For a rotation `ρ ∈ O(N)` (`OrthN N`) acting on the output variables (`rotOut`), the new internal
variables (`rotSub`) and the external direction `h`:

* `mainActionLoc_rot`: `mainActionLoc (ρ•o) (ρ•x) (ρ h) = mainActionLoc o x h`;
* `quietKernel_rot`: `quietKernel (ρ•o) (ρ•x) (ρ h) = quietKernel o x h`.

The proof uses the covariance of the Def-5 background (`Balaban/Background/Equivariance.lean`):
the lifted data of the local background rotate (`locData_rot`), hence so does the local background
(`locBg_rot`) and the field `φ̄` (`locPhi_rot`), while the characteristic functions, the Gaussians,
the domain indicator and the multiscale action depend on the rotated objects through Euclidean
norms, scalar products and the bilinear constraint, all `O(N)`-invariant (`reg_rot_iff`,
`regMixedIneq_rot_iff`, `chiK_rot`, `chiPrimeNew_rot`, `chiNew_rot`, `gaussProd_rot`,
`actionG_rot`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField
open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory Matrix

section Prelim

variable {N : ℕ}

/-- The real matrix `(R_{ij})` of an element `R` of `O(N)`. -/
noncomputable def rotMat (ρ : OrthN N) : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j => rotEntry ρ i j

theorem rotMat_mul_transpose (ρ : OrthN N) : rotMat ρ * (rotMat ρ)ᵀ = 1 := by
  ext i k
  simp only [Matrix.mul_apply, rotMat, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [rotEntry_orth]

theorem rotMat_transpose_mul (ρ : OrthN N) : (rotMat ρ)ᵀ * rotMat ρ = 1 :=
  mul_eq_one_comm.1 (rotMat_mul_transpose ρ)

theorem rot_apply_eq (ρ : OrthN N) (v : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    (ρ v : EuclideanSpace ℝ (Fin N)) i = (rotMat ρ *ᵥ fun j => v j) i := by
  rw [rot_apply_coord]; rfl


/-- The rotation `ψ ↦ Q ψ` of a real block configuration. -/
def rotBC {d N₀ L k j : ℕ} (Q : Matrix (Fin N) (Fin N) ℝ) (ψ : BlockCfg d N₀ L k j N) :
    BlockCfg d N₀ L k j N := fun z => Q *ᵥ ψ z

theorem rotBC_toC {d N₀ L k j : ℕ} (Q : Matrix (Fin N) (Fin N) ℝ) (ψ : BlockCfg d N₀ L k j N) :
    (rotBC Q ψ).toC = fun z => cmat Q *ᵥ ψ.toC z := by
  funext z i
  exact cmat_mulVec Q (ψ z) i

theorem cmat_mulVec_fun (Q : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) :
    (fun i => ((Q *ᵥ v) i : ℂ)) = cmat Q *ᵥ fun j => (v j : ℂ) :=
  funext fun i => cmat_mulVec Q v i

section Lift

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem liftSingle_rot (G : GeneratingSet d L N₀ k ϱ) (R : Matrix (Fin N) (Fin N) ℂ)
    (ψ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) (h : Fin N → ℂ) :
    liftSingle G (fun z => R *ᵥ ψ z) (R *ᵥ h) = (liftSingle G ψ h).rot R := by
  classical
  refine Balaban.Background.BgData.ext' (funext fun x => ?_) (funext fun x => ?_)
  · by_cases hx : x ∈ dataSites G
    · simp [liftSingle, BgData.clip, BgData.rot, hx, blockLift]
    · simp [liftSingle, BgData.clip, BgData.rot, hx]
  · by_cases hx : x ∈ G.Ω 1
    · simp [liftSingle, BgData.clip, BgData.rot, hx]
    · simp [liftSingle, BgData.clip, BgData.rot, hx]


theorem liftMixed_rot (G : GeneratingSet d L N₀ (k + 1) ϱ)
    {Ω : Finset (Torus d (N₀ * L ^ (k + 1)))} (hΩ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω)
    (hG : G.Ω (k + 1) ⊆ Ω) (R : Matrix (Fin N) (Fin N) ℂ)
    (ψ : Torus d (N₀ * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ) :
    liftMixed G hΩ hG (fun z => R *ᵥ ψ z) (fun z => R *ᵥ ϑ z) (R *ᵥ h) =
      (liftMixed G hΩ hG ψ ϑ h).rot R := by
  classical
  refine Balaban.Background.BgData.ext' (funext fun x => ?_) (funext fun x => ?_)
  · by_cases hx : x ∈ dataSites G
    · by_cases hΩx : x ∈ Ω
      · simp [liftMixed, BgData.clip, BgData.rot, hx, mixedLift, hΩx, blockLift]
      · simp [liftMixed, BgData.clip, BgData.rot, hx, mixedLift, hΩx, blockLift]
    · simp [liftMixed, BgData.clip, BgData.rot, hx]
  · by_cases hx : x ∈ G.Ω 1
    · simp [liftMixed, BgData.clip, BgData.rot, hx]
    · simp [liftMixed, BgData.clip, BgData.rot, hx]

end Lift

section Reg

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ q ϱ)

theorem barVec_rot (R : Matrix (Fin N) (Fin N) ℂ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ q)) :
    barVec G (D.rot R) (rotFld R φ) x = R *ᵥ barVec G D φ x :=
  barField_rot R D.Ψ φ x

theorem barVec_sub_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRealOrth R) (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) (x y : Torus d (N₀ * L ^ q)) :
    vn (barVec G (D.rot R) (rotFld R φ) y - barVec G (D.rot R) (rotFld R φ) x) =
      vn (barVec G D φ y - barVec G D φ x) := by
  rw [barVec_rot, barVec_rot, ← Matrix.mulVec_sub, vn_rot hR]

theorem barLap_rot (R : Matrix (Fin N) (Fin N) ℂ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ q)) :
    barLap G (D.rot R) (rotFld R φ) x = R *ᵥ barLap G D φ x := by
  unfold barLap
  simp only [barVec_rot]
  have e1 : (∑ μ : Fin d, (R *ᵥ barVec G D φ (x + Pi.single μ 1) +
      R *ᵥ barVec G D φ (x - Pi.single μ 1) - 2 • R *ᵥ barVec G D φ x)) =
      fun i => ∑ μ : Fin d, ((R *ᵥ barVec G D φ (x + Pi.single μ 1)) i +
        (R *ᵥ barVec G D φ (x - Pi.single μ 1)) i - 2 * (R *ᵥ barVec G D φ x) i) := by
    funext i
    simp [Finset.sum_apply, nsmul_eq_mul]
  have e2 : (fun i => ∑ μ : Fin d, (barVec G D φ (x + Pi.single μ 1) i +
        barVec G D φ (x - Pi.single μ 1) i - 2 * barVec G D φ x i)) =
      ∑ μ : Fin d, (barVec G D φ (x + Pi.single μ 1) + barVec G D φ (x - Pi.single μ 1) -
        2 • barVec G D φ x) := by
    funext i
    simp [Finset.sum_apply, nsmul_eq_mul]
  rw [e1, ← e2]
  exact rot_lap R d (fun μ => barVec G D φ (x + Pi.single μ 1))
    (fun μ => barVec G D φ (x - Pi.single μ 1)) (barVec G D φ x)


theorem blockDev_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRealOrth R) (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ q)) :
    blockDev G (D.rot R) (rotFld R φ) x = blockDev G D φ x := by
  have e := congrFun (blockAvg_rot R φ x)
  unfold blockDev
  show vn (fun i => (R *ᵥ D.Ψ x) i - blockAvg G (rotFld R φ) x i) = _
  simp only [e]
  rw [vn_sub_rot hR]

theorem gradClose_rot_iff {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRealOrth R) (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) (ℓ : ℝ) (S : Finset (Torus d (N₀ * L ^ q))) (δ : ℝ) :
    GradClose G (D.rot R) (rotFld R φ) α ℓ S δ ↔ GradClose G D φ α ℓ S δ := by
  unfold GradClose
  simp only [barVec_sub_rot G hR, barLap_rot, vn_rot hR]

theorem fieldClose_rot_iff {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRealOrth R) (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) (ν : ℝ) (S : Finset (Torus d (N₀ * L ^ q))) (δ : ℝ) :
    FieldClose G (D.rot R) (rotFld R φ) ν S δ ↔ FieldClose G D φ ν S δ := by
  unfold FieldClose
  have e1 : ∀ (x : G.Ω 1), vn (fun i => rotFld R φ (x, i) - (D.rot R).h x i) =
      vn (fun i => φ (x, i) - D.h x i) := fun x => by
    have : (fun i => rotFld R φ (x, i) - (D.rot R).h x i) =
        fun i => (R *ᵥ fun j => φ (x, j)) i - (R *ᵥ D.h x) i := rfl
    rw [this, vn_sub_rot hR]
  have e2 : ∀ (x : G.Ω 1), ∑ i, (D.rot R).h x i * (D.rot R).h x i = ∑ i, D.h x i * D.h x i :=
    fun x => bilin_vec hR.1 (D.h x) (D.h x)
  simp only [e1, e2]

variable (a : ℕ → ℝ) (μ : ℝ)

theorem regIneq_rot_iff {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (D : BgData G N) (δ : ℝ)
    (T S : Finset (Torus d (N₀ * L ^ q))) :
    RegIneq G a μ (D.rot (cmat Q)) δ T S ↔ RegIneq G a μ D δ T S := by
  have hR := isRealOrth_ofReal hQ
  unfold RegIneq BlockClose
  rw [(bgFieldC_rot a μ hR.1 (bgC0 d L N) D).1, (bgFieldC_rot a μ hR.1 (bgC0 d L N) D).2,
    gradClose_rot_iff G hR, fieldClose_rot_iff G hR]
  simp only [blockDev_rot G hR]

theorem reg_rot_iff {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (D : BgData G N) (δ : ℝ)
    (T S : Finset (Torus d (N₀ * L ^ q))) :
    Reg G a μ (D.rot (cmat Q)) δ T S ↔ Reg G a μ D δ T S := by
  unfold Reg
  rw [inUnionDomainR_rot_iff hQ, regIneq_rot_iff G a μ hQ]

theorem regC_rot_iff {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (D : BgData G N) (δ : ℝ)
    (T S : Finset (Torus d (N₀ * L ^ q))) :
    RegC G a μ (D.rot (cmat Q)) δ T S ↔ RegC G a μ D δ T S := by
  unfold RegC
  rw [inUnionDomainC_rot_iff hQ, regIneq_rot_iff G a μ hQ]

theorem regMixedIneq_rot_iff {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (D : BgData G N)
    (ℓ νk δ : ℝ) (Tfar Tnear S : Finset (Torus d (N₀ * L ^ q))) :
    RegMixedIneq G a μ (D.rot (cmat Q)) ℓ νk δ Tfar Tnear S ↔
      RegMixedIneq G a μ D ℓ νk δ Tfar Tnear S := by
  have hR := isRealOrth_ofReal hQ
  unfold RegMixedIneq BlockClose
  rw [(bgFieldC_rot a μ hR.1 (bgC0 d L N) D).1, (bgFieldC_rot a μ hR.1 (bgC0 d L N) D).2,
    gradClose_rot_iff G hR, fieldClose_rot_iff G hR]
  simp only [blockDev_rot G hR]

end Reg

theorem charFn_congr_apply {X Y : Type*} {P : X → Prop} {P' : Y → Prop} {x : X} {y : Y}
    (h : P x ↔ P' y) : charFn P x = charFn P' y := by
  classical
  rw [charFn_apply, charFn_apply]
  exact if_congr h rfl rfl

section Chi

variable {d M1 N₁ L : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

theorem chiK_rot {q : ℕ} (a : ℕ → ℝ) (μ δ : ℝ) (c n : ℕ) (y0 : Torus d n)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (h : Fin N → ℝ)
    (ψ : BlockCfg d (M1 * N₁) L q q N) :
    chiK (M1 := M1) (N₁ := N₁) (L := L) a μ δ (Q *ᵥ h) c n y0 (rotBC Q ψ) =
      chiK (M1 := M1) (N₁ := N₁) (L := L) a μ δ h c n y0 ψ := by
  unfold chiK
  have : ChiKProp (M1 := M1) (N₁ := N₁) (L := L) a μ δ (Q *ᵥ h) c n y0 (rotBC Q ψ) ↔
      ChiKProp (M1 := M1) (N₁ := N₁) (L := L) a μ δ h c n y0 ψ := by
    unfold ChiKProp cubeData
    rw [rotBC_toC, cmat_mulVec_fun, liftSingle_rot]
    exact reg_rot_iff _ a μ hQ _ δ _ _
  exact charFn_congr_apply this


section Mixed

variable {k : ℕ} (a : ℕ → ℝ) (μ δ νk : ℝ) {c n : ℕ}
  (hm : N₁ * L ^ (k + 1 - (k + 1)) = c * n) (y0 : Torus d n)
  (Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1)))) (hOm : IsBlockUnion L (M1 * N₁) (k + 1) (k + 1) Om)

theorem mixedData_rot {Q : Matrix (Fin N) (Fin N) ℝ} (h : Fin N → ℝ)
    (ψ : BlockCfg d (M1 * N₁) L (k + 1) k N) (θ : BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N) :
    mixedData (Q *ᵥ h) hm y0 Om hOm (rotBC Q ψ) (rotBC Q θ) =
      (mixedData h hm y0 Om hOm ψ θ).rot (cmat Q) := by
  unfold mixedData
  rw [rotBC_toC, rotBC_toC, cmat_mulVec_fun, liftMixed_rot]

theorem chiPrimeNew_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (h : Fin N → ℝ)
    (ψ : BlockCfg d (M1 * N₁) L (k + 1) k N) (θ : BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N) :
    chiPrimeNew a μ δ νk (Q *ᵥ h) hm y0 Om hOm (rotBC Q ψ, rotBC Q θ) =
      chiPrimeNew a μ δ νk h hm y0 Om hOm (ψ, θ) := by
  unfold chiPrimeNew
  refine charFn_congr_apply ?_
  unfold ChiPrimeNewProp
  simp only [mixedData_rot, inUnionDomainR_rot_iff hQ, regMixedIneq_rot_iff _ a μ hQ]

end Mixed

end Chi

section Reading

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L]

theorem blockCfgOf_rot (g : Geo S n R M) (hnn : ∀ i, n i = S.L * n (i + 1)) {q i : ℕ} (hiq : i ≤ q)
    (hqK : q ≤ K) (ρ : OrthN N) (f : BlockAt S n M K i → EuclideanSpace ℝ (Fin N)) :
    blockCfgOf g hnn hiq hqK (fun y => ρ (f y)) = rotBC (rotMat ρ) (blockCfgOf g hnn hiq hqK f) := by
  funext z j
  exact rot_apply_eq ρ _ j

theorem outField_rot {α : Type} {V : Set α} (ρ : OrthN N) (o : OutConfig N V) (y : α) :
    outField N (rotOut ρ o) y = ρ (outField N o y) := by
  classical
  unfold outField rotOut
  by_cases h : y ∈ V
  · simp [h]
  · simp [h]

theorem subFluctVarField_rot (ρ : OrthN N) {a : LocalHistory S n M K} {k : ℕ}
    {A : Set (InternalVars a k)} (x : SubCfg N a k A) (j : ℕ) (y : BlockAt S n M K j) :
    subFluctVarField N (rotSub ρ x) j y = ρ (subFluctVarField N x j y) := by
  classical
  unfold subFluctVarField
  by_cases h : ∃ hj : j < k, ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y
      (varSet a j .fluct), mkVar a k j .fluct y hj hb ∈ A
  · simp only [h, ↓reduceDIte]
    exact VarVal.toEuc_rot ρ _ (x _)
  · simp only [h, ↓reduceDIte]
    simp


/-- Rotation of a multiscale field. -/
def rotMF (ρ : OrthN N) (ψ : MultiField S n M K N) : MultiField S n M K N := fun j y => ρ (ψ j y)

theorem subMultiscaleField_rot (ρ : OrthN N) (a : LocalHistory S n M K) (k : ℕ)
    (V : Set (BlockAt S n M K k)) {A : Set (InternalVars a k)} (x : SubCfg N a k A)
    (o : OutConfig N V) :
    subMultiscaleField N a k V (rotSub ρ x) (rotOut ρ o) =
      rotMF ρ (subMultiscaleField N a k V x o) := by
  classical
  funext j y
  unfold subMultiscaleField rotMF
  by_cases hj : j < k
  · simp only [hj, ↓reduceIte]
    by_cases hc : j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j y (lhOmega a k j)
    · simp only [hc, ↓reduceIte]
      exact subVarField_rot ρ x j y
    · simp only [hc, ↓reduceIte]
      simp
  · simp only [hj, ↓reduceIte]
    by_cases hjk : j = k
    · subst hjk
      simp only [↓reduceDIte]
      by_cases hc : j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j y (lhOmega a j j)
      · simp only [hc, ↓reduceIte]
        exact outField_rot ρ o y
      · simp only [hc, ↓reduceIte]
        simp
    · simp only [hjk, ↓reduceDIte]
      simp

theorem subFluctField_rot (ρ : OrthN N) (a : LocalHistory S n M K) (k : ℕ)
    {A : Set (InternalVars a k)} (x : SubCfg N a k A) :
    subFluctField N a k (rotSub ρ x) = rotMF ρ (subFluctField N a k x) := by
  funext j y
  exact subFluctVarField_rot ρ x j y


variable {ϱ : ℝ}

theorem psiTildeMulti_rot_iff (ρ : OrthN N) (ψ : MultiField S n M K N) (Y : Set (BlockPt S n M K))
    (δ : ℝ) : PsiTildeMulti (rotMF ρ ψ) Y δ ↔ PsiTildeMulti ψ Y δ := by
  unfold PsiTildeMulti rotMF
  simp only [← map_sub, LinearIsometryEquiv.norm_map]

theorem chiNewProp_rot_iff (ρ : OrthN N) (a : LocalHistory S n M K) (k : ℕ)
    (B : GeneratingSet S.d S.L (M * n K) K ϱ) (Zc : Set (Torus S.d (M * n K * S.L ^ K)))
    (δ p0 : ℕ → ℝ) (Cpsi : ℝ) (ψ ψ' : MultiField S n M K N) :
    ChiNewProp a k B Zc δ p0 Cpsi (rotMF ρ ψ) (rotMF ρ ψ') ↔ ChiNewProp a k B Zc δ p0 Cpsi ψ ψ' := by
  unfold ChiNewProp
  simp only [psiTildeMulti_rot_iff, rotMF, LinearIsometryEquiv.norm_map]

theorem chiNew_rot (ρ : OrthN N) (a : LocalHistory S n M K) (k : ℕ)
    (B : GeneratingSet S.d S.L (M * n K) K ϱ) (Zc : Set (Torus S.d (M * n K * S.L ^ K)))
    (δ p0 : ℕ → ℝ) (Cpsi : ℝ) (ψ ψ' : MultiField S n M K N) :
    chiNew a k B Zc δ p0 Cpsi (rotMF ρ ψ, rotMF ρ ψ') = chiNew a k B Zc δ p0 Cpsi (ψ, ψ') := by
  unfold chiNew
  exact charFn_congr_apply (chiNewProp_rot_iff ρ a k B Zc δ p0 Cpsi ψ ψ')

theorem qCoarseK_rot (ρ : OrthN N) {a : LocalHistory S n M K} {k : ℕ}
    {A : Set (InternalVars a (k + 1))} (x : SubCfg N a (k + 1) A) (y : BlockAt S n M K (k + 1)) :
    qCoarseK N (rotSub ρ x) y = ρ (qCoarseK N x y) := by
  unfold qCoarseK
  simp only [subVarField_rot, map_smul, map_sum]

theorem gaussT_rot (ρ : OrthN N) (c : ℝ) (ϑ w : EuclideanSpace ℝ (Fin N)) :
    gaussT N c (ρ ϑ) (ρ w) = gaussT N c ϑ w := by
  unfold gaussT
  rw [← map_sub, LinearIsometryEquiv.norm_map]

theorem gaussProd_rot (ρ : OrthN N) (a : LocalHistory S n M K) (k : ℕ) (cs : OpConsts)
    {V : Set (BlockAt S n M K (k + 1))} (o : OutConfig N V) (x : NewCfg N a k) :
    gaussProd N a k cs (rotOut ρ o) (rotSub ρ x) = gaussProd N a k cs o x := by
  unfold gaussProd
  refine Finset.prod_congr rfl fun y _ => ?_
  rw [outField_rot, qCoarseK_rot, ← map_smul, gaussT_rot]

end Reading

section Action

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ' : ℝ}

theorem bavgL_rot (ρ : OrthN N) (n : ℕ) (φ : Site d L N₀ q → EuclideanSpace ℝ (Fin N))
    (y : Blk d L N₀ q n) : bavgL d L N₀ q n (fun z => ρ (φ z)) y = ρ (bavgL d L N₀ q n φ y) := by
  unfold bavgL bavg
  simp only [map_smul, map_sum]

theorem bondTerm_rot {ℓ : ℕ} [NeZero ℓ] (ρ : OrthN N) (φ : Torus d ℓ → EuclideanSpace ℝ (Fin N))
    (μ : Fin d) (x : Torus d ℓ) : bondTerm (fun z => ρ (φ z)) μ x = bondTerm φ μ x := by
  unfold bondTerm
  rw [← map_sub, LinearIsometryEquiv.norm_map]

theorem bondE_rot {ℓ : ℕ} [NeZero ℓ] (ρ : OrthN N) (S' : Finset (Torus d ℓ))
    (φ : Torus d ℓ → EuclideanSpace ℝ (Fin N)) : bondE S' (fun z => ρ (φ z)) = bondE S' φ := by
  unfold bondE bondEdir
  simp only [bondTerm_rot]

theorem starBondE_rot {ℓ : ℕ} [NeZero ℓ] (ρ : OrthN N) (X : Finset (Torus d ℓ))
    (φ : Torus d ℓ → EuclideanSpace ℝ (Fin N)) :
    starBondE X (fun z => ρ (φ z)) = starBondE X φ := by
  unfold starBondE
  simp only [bondTerm_rot]

theorem actionG_rot (ρ : OrthN N) (G : GeneratingSet d L N₀ q ϱ') (a : ℕ → ℝ) (μ : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (X : Finset (Site d L N₀ q))
    (ψ : (m : ℕ) → Blk d L N₀ q m → EuclideanSpace ℝ (Fin N))
    (φ : Site d L N₀ q → EuclideanSpace ℝ (Fin N)) :
    actionG G a μ (ρ h) X (fun m y => ρ (ψ m y)) (fun z => ρ (φ z)) = actionG G a μ h X ψ φ := by
  unfold actionG
  simp only [bavgL_rot, bondE_rot, ← map_sub, LinearIsometryEquiv.norm_map]

end Action

section MainAct

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (cs : OpConsts) (hk : k + 1 ≤ K)

theorem locLiftPsi_rot (ρ : OrthN N) (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) :
    locLiftPsi g Hl k Zc hk (rotSub ρ x) = rotBC (rotMat ρ) (locLiftPsi g Hl k Zc hk x) := by
  unfold locLiftPsi
  have : subVarField N (rotSub ρ x) k = fun y => ρ (subVarField N x k y) :=
    funext fun y => subVarField_rot ρ x k y
  rw [this, blockCfgOf_rot]

theorem locLiftTheta_rot (ρ : OrthN N) (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1)) :
    locLiftTheta g Hl k Zc hk (rotOut ρ o) = rotBC (rotMat ρ) (locLiftTheta g Hl k Zc hk o) := by
  unfold locLiftTheta
  have : outField N (rotOut ρ o) = fun y => ρ (outField N o y) := funext fun y => outField_rot ρ o y
  rw [this, blockCfgOf_rot]

theorem locData_rot (ρ : OrthN N) (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    locData g Hl k Zc hZc hk (rotOut ρ o) (rotSub ρ x) (ρ hv) =
      (locData g Hl k Zc hZc hk o x hv).rot (cmat (rotMat ρ)) := by
  unfold locData
  rw [locLiftPsi_rot, locLiftTheta_rot, rotBC_toC, rotBC_toC]
  have : (fun i => (((ρ hv : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)) =
      cmat (rotMat ρ) *ᵥ fun i => ((hv i : ℝ) : ℂ) := by
    funext i
    rw [← cmat_mulVec, rot_apply_eq]
  rw [this, liftMixed_rot]


theorem locBg_eq (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    locBg g Hl k Zc hZc cs hk o x hv = bgFieldC (locGen g Hl k Zc hZc) cs.aw (cs.mu (k + 1))
      (bgC0 S.d S.L N) (locData g Hl k Zc hZc hk o x hv) := rfl

theorem locBg_rot (ρ : OrthN N) (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    locBg g Hl k Zc hZc cs hk (rotOut ρ o) (rotSub ρ x) (ρ hv) =
      rotFld (cmat (rotMat ρ)) (locBg g Hl k Zc hZc cs hk o x hv) := by
  rw [locBg_eq, locBg_eq, locData_rot]
  exact (bgFieldC_rot cs.aw (cs.mu (k + 1)) (isRealOrth_ofReal (rotMat_transpose_mul ρ)).1
    (bgC0 S.d S.L N) _).1

theorem re_cmat_mulVec (Q : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℂ) (i : Fin N) :
    ((cmat Q *ᵥ v) i).re = (Q *ᵥ fun j => (v j).re) i := by
  simp [Matrix.mulVec, dotProduct, Complex.re_sum]

theorem locPhi_rot (ρ : OrthN N) (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    locPhi g Hl k Zc hZc cs hk (rotOut ρ o) (rotSub ρ x) (ρ hv) =
      fun z => ρ (locPhi g Hl k Zc hZc cs hk o x hv z) := by
  funext z
  unfold locPhi
  rw [locBg_rot, locData_rot]
  refine PiLp.ext fun i => ?_
  have e := congrFun (barField_rot (cmat (rotMat ρ)) (locData g Hl k Zc hZc hk o x hv).Ψ
    (locBg g Hl k Zc hZc cs hk o x hv) z) i
  rw [rot_apply_eq]
  simp only [BgData.rot]
  rw [e, re_cmat_mulVec]

theorem psiLevel_rot (ρ : OrthN N) (ψ : MultiField S n M K N) :
    psiLevel g Hl k hk (rotMF ρ ψ) = fun m y => ρ (psiLevel g Hl k hk ψ m y) := by
  funext m y
  unfold psiLevel rotMF
  by_cases hm : m ≤ k + 1
  · simp [hm]
  · simp [hm]

theorem mainActionLoc_rot (hrem : ∀ j, Hl.rem j = ∅) (ρ : OrthN N)
    (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    mainActionLoc g Hl k Zc hZc cs hk hrem (rotOut ρ o) (rotSub ρ x) (ρ hv) =
      mainActionLoc g Hl k Zc hZc cs hk hrem o x hv := by
  unfold mainActionLoc
  rw [subMultiscaleField_rot, psiLevel_rot, locPhi_rot]
  rw [actionG_rot ρ (histGenLevel g Hl k hrem) cs.aw (cs.muAct (k + 1)) hv (Xfine g Hl k Zc)
    (psiLevel g Hl k hk (subMultiscaleField N (locHist Hl M K (k + 1) Zc) (k + 1)
      (Vblk R (locHist Hl M K (k + 1) Zc) (k + 1)) x o))
    (locPhi g Hl k Zc hZc cs hk o x hv)]
  rw [starBondE_rot]


open Classical in
/-- **Lemma II.5.10, `O(N)` part, for the explicit quiet kernel**: the quiet step kernel is
invariant under a rotation `ρ ∈ O(N)` acting on the output variables, the new internal variables
and the external direction `h`. -/
theorem quietKernel_rot (hrem : ∀ j, Hl.rem j = ∅) (ρ : OrthN N)
    (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    quietKernel g Hl k Zc hZc cs hk hrem (rotOut ρ o) (rotSub ρ x) (ρ hv) =
      quietKernel g Hl k Zc hZc cs hk hrem o x hv := by
  have hQ := rotMat_transpose_mul ρ
  have hh : (fun i => (ρ hv : EuclideanSpace ℝ (Fin N)) i) = rotMat ρ *ᵥ fun i => hv i :=
    funext fun i => rot_apply_eq ρ hv i
  have hx : subVarField N (rotSub ρ x) k = fun y => ρ (subVarField N x k y) :=
    funext fun y => subVarField_rot ρ x k y
  have ho : (fun y => cs.z (k + 1) • outField N (rotOut ρ o) y) =
      fun y => ρ (cs.z (k + 1) • outField N o y) :=
    funext fun y => by rw [outField_rot, map_smul]
  have ho' : outField N (rotOut ρ o) = fun y => ρ (outField N o y) :=
    funext fun y => outField_rot ρ o y
  unfold quietKernel
  rw [gaussProd_rot, hh, hx, ho, ho']
  simp only [blockCfgOf_rot]
  rw [subMultiscaleField_rot, subFluctField_rot, chiNew_rot, mainActionLoc_rot, locData_rot,
    inUnionDomainR_rot_iff (rotMat_transpose_mul ρ)]
  simp only [cubeProd, chiNext, chiK_rot, chiPrimeNew_rot, hQ]

end MainAct
end Prelim
end Balaban.LargeField
