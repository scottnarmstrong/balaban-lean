/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BPrimeRPair

/-!
# The cube roots of the residual of `R`: analyticity

The root of a cube `c` of `𝕋_k` (`Def7v2.cubeRoot`: the action of the cube, the corrections at its
sites and the source term) is a polynomial in the background field `φ̄ = barField(φ, lift ψ_k)`
and in the data, except for the unit directions `(ψ^{(j)})₀` of the corrections, analytic where
`ψ^{(j)} · ψ^{(j)}` lies in the slit plane.

* `analyticAt_actionGWithCube`, `analyticAt_starBondEWithCube`: the action of a class of a partition
  is analytic in the fields;
* `barField_castG`, `SFCtx.phiBarAt_cast`, `SFCtx.analyticAt_phiBarAt`: `φ̄` at a transported field;
* `SFCtx.analyticAt_gCube_joint`, `SFCtx.analyticAt_cubeRoot_joint`: analyticity jointly in a
  parameter of the source and in `(ψ_k, φ)`;
* `SFCtx.analyticAt_cubeRoot`, `SFCtx.cubePair`, `SFCtx.analyticAt_cubePair`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.GsSpec

section Generic

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q₀ : Q} {N : ℕ}

theorem analyticAt_dot_comp {v w' : Q → Fin N → ℂ} (hv : ∀ i, AnalyticAt ℂ (fun w => v w i) q₀)
    (hw : ∀ i, AnalyticAt ℂ (fun w => w' w i) q₀) :
    AnalyticAt ℂ (fun w => SmallField.dot (v w) (w' w)) q₀ := by
  unfold SmallField.dot
  exact Finset.analyticAt_fun_sum _ fun i _ => (hv i).mul (hw i)

theorem analyticAt_ite_const {P : Prop} [Decidable P] {f g : Q → ℂ} (hf : P → AnalyticAt ℂ f q₀)
    (hg : ¬P → AnalyticAt ℂ g q₀) : AnalyticAt ℂ (fun w => if P then f w else g w) q₀ := by
  by_cases h : P
  · have e : (fun w => if P then f w else g w) = f :=
      funext fun w => by simp [h]
    rw [e]
    exact hf h
  · have e : (fun w => if P then f w else g w) = g :=
      funext fun w => by simp [h]
    rw [e]
    exact hg h

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {β : Type*} [Fintype β] [DecidableEq β]
  (cs : Site d L N₀ q → β) (cb : ∀ m, Blk d L N₀ q m → β)

theorem analyticAt_bavgL (φ : Q → Site d L N₀ q → Fin N → ℂ)
    (hφ : ∀ x i, AnalyticAt ℂ (fun w => φ w x i) q₀) (m : ℕ) (y : Blk d L N₀ q m) (i : Fin N) :
    AnalyticAt ℂ (fun w => bavgL d L N₀ q m (φ w) y i) q₀ := by
  unfold bavgL bavg
  simp only [Pi.smul_apply, Finset.sum_apply, Complex.real_smul]
  exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun x _ => hφ x i)

omit [Fintype β] in
/-- **The action of a class of a partition is analytic in the fields.** -/
theorem analyticAt_actionGWithCube (G : GeneratingSet d L N₀ q ϱ) (a : ℕ → ℝ) (μ : ℝ)
    (h : Fin N → ℂ) (X : Finset (Site d L N₀ q)) (c : β)
    (ψ : Q → (m : ℕ) → Blk d L N₀ q m → Fin N → ℂ) (φ : Q → Site d L N₀ q → Fin N → ℂ)
    (hψ : ∀ m y i, AnalyticAt ℂ (fun w => ψ w m y i) q₀)
    (hφ : ∀ x i, AnalyticAt ℂ (fun w => φ w x i) q₀) :
    AnalyticAt ℂ (fun w => actionGWithCube cs cb (fun v => SmallField.dot v v) G a μ h X (ψ w)
      (φ w) c) q₀ := by
  classical
  have hb := analyticAt_bavgL φ hφ
  have hd : ∀ m y, AnalyticAt ℂ (fun w => SmallField.dot (ψ w m y - bavgL d L N₀ q m (φ w) y)
      (ψ w m y - bavgL d L N₀ q m (φ w) y)) q₀ := fun m y =>
    analyticAt_dot_comp (fun i => (hψ m y i).sub (hb m y i)) (fun i => (hψ m y i).sub (hb m y i))
  have hbond : ∀ (ν : Fin d) (x : Site d L N₀ q), AnalyticAt ℂ
      (fun w => bondTermWith (fun v => SmallField.dot v v) (φ w) ν x) q₀ := fun ν x =>
    analyticAt_dot_comp (fun i => (hφ _ i).sub (hφ x i)) (fun i => (hφ _ i).sub (hφ x i))
  have hmass : ∀ x, AnalyticAt ℂ (fun w => SmallField.dot (φ w x - h) (φ w x - h)) q₀ := fun x =>
    analyticAt_dot_comp (fun i => (hφ x i).sub analyticAt_const)
      (fun i => (hφ x i).sub analyticAt_const)
  unfold actionGWithCube
  refine ((analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun m _ =>
    Finset.analyticAt_fun_sum _ fun y _ => analyticAt_const.mul (hd m y))).add
    (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun ν _ =>
      Finset.analyticAt_fun_sum _ fun x _ => ?_))).add
    (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun x _ => hmass x))
  exact analyticAt_ite_const (fun _ => hbond ν x) (fun _ => analyticAt_const)

omit [Fintype β] in
/-- **The star bonds of a class of a partition are analytic in the field.** -/
theorem analyticAt_starBondEWithCube (X : Finset (Site d L N₀ q)) (c : β)
    (φ : Q → Site d L N₀ q → Fin N → ℂ) (hφ : ∀ x i, AnalyticAt ℂ (fun w => φ w x i) q₀) :
    AnalyticAt ℂ (fun w => starBondEWithCube cs (fun v => SmallField.dot v v) X (φ w) c) q₀ := by
  classical
  unfold starBondEWithCube
  refine Finset.analyticAt_fun_sum _ fun ν _ => Finset.analyticAt_fun_sum _ fun x _ => ?_
  exact analyticAt_ite_const (fun _ => analyticAt_dot_comp (fun i => (hφ _ i).sub (hφ x i))
    (fun i => (hφ _ i).sub (hφ x i))) (fun _ => analyticAt_const)

theorem analyticAt_coord_fst {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {p₀ : (ι → Fin N → ℂ) × F} (b : ι) (i : Fin N) :
    AnalyticAt ℂ (fun p : (ι → Fin N → ℂ) × F => p.1 b i) p₀ := by
  have h1 : AnalyticAt ℂ (fun p : (ι → Fin N → ℂ) × F => p.1) p₀ := analyticAt_fst
  have h2 : AnalyticAt ℂ (fun p : (ι → Fin N → ℂ) × F => p.1 b) p₀ := analyticAt_pi_iff.1 h1 b
  exact analyticAt_pi_iff.1 h2 i

end Generic

section Cast

variable {d L k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The extended field commutes with the transport.** -/
theorem barField_castG {N₀' N₀ : ℕ} [NeZero N₀'] [NeZero N₀] (h : N₀' = N₀)
    (G : GeneratingSet d L N₀' k ϱ) (Ψ : Torus d (N₀' * L ^ k) → Fin N → ℂ)
    (φ : (castG h G).Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    barField (castG h G) (castTField h Ψ) φ x i =
      barField G Ψ (castΩField h G φ) (GsSpec.torusCast x) i := by
  subst h
  rw [torusCast_self']
  rfl

end Cast

namespace Def7.SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (Y : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N))

theorem torusCast_torusCast_bg (z : BgT C.geo k) :
    (GsSpec.torusCast (GsSpec.torusCast z : Localization.CTorus S.d S.L C.N₁ m₁ k) : BgT C.geo k) =
      z := by
  funext μ
  apply ZMod.val_injective
  rw [GsSpec.torusCast_val C.hT, GsSpec.torusCast_val C.hT.symm]

/-- **`φ̄` at a transported field** is the extended field of `genWC Y` at the transported site. -/
theorem phiBarAt_cast (u : BlockAt S n M K k → Fin N → ℂ) (φ : (C.genWC Y).Ω 1 × Fin N → ℂ)
    (z : BgT C.geo k) (i : Fin N) :
    C.phiBarAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) z i =
      barField (C.genWC Y) (C.liftWC Y hv u) φ
        (GsSpec.torusCast z : Localization.CTorus S.d S.L C.N₁ m₁ k) i := by
  have h := barField_castG C.coarseSide_eq (C.genW Y)
    (liftSingle (C.genW Y) (C.liftDataC u) (hC hv)).Ψ φ
    (GsSpec.torusCast z : Localization.CTorus S.d S.L C.N₁ m₁ k) i
  rw [C.torusCast_torusCast_bg] at h
  exact h.symm

/-- **`φ̄` is analytic in `(ψ_k, φ)`** (a coordinate of `φ` or of the lift). -/
theorem analyticAt_phiBarAt
    (q₀ : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ)) (z : BgT C.geo k)
    (i : Fin N) :
    AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
      C.phiBarAt Y q.1 hv (castΩField C.coarseSide_eq (C.genW Y) q.2) z i) q₀ := by
  classical
  simp only [C.phiBarAt_cast Y hv]
  unfold barField
  by_cases hx : (GsSpec.torusCast z : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈ (C.genWC Y).Ω 1
  · simp only [hx, ↓reduceDIte]
    exact analyticAt_pi_iff.1 analyticAt_snd _
  · simp only [hx, ↓reduceDIte]
    exact C.analyticAt_liftWC Y hv (fun q : (BlockAt S n M K k → Fin N → ℂ) ×
      ((C.genWC Y).Ω 1 × Fin N → ℂ) => q.1) analyticAt_fst _ i

/-- The coordinates of the data on the blocks are analytic in `(ψ_k, φ)`. -/
theorem analyticAt_psiLevelKOf
    (q₀ : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ)) (m : ℕ)
    (y : LargeField.Blk S.d S.L (C.geo.M1 * (C.geo.c * n k)) k m) (i : Fin N) :
    AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
      C.psiLevelKOf q.1 m y i) q₀ := by
  unfold psiLevelKOf singleScaleOf
  by_cases hm : m ≤ k
  · by_cases hmk : m = k
    · simp only [hmk, le_refl, ↓reduceDIte]
      exact analyticAt_coord_fst (ι := BlockAt S n M K k) (F := (C.genWC Y).Ω 1 × Fin N → ℂ) _ i
    · simp only [hm, hmk, ↓reduceDIte, Pi.zero_apply]
      exact analyticAt_const
  · simp only [hm, ↓reduceDIte, Pi.zero_apply]
    exact analyticAt_const

/-- **The action of a cube is analytic in `(ψ_k, φ)`.** -/
theorem analyticAt_actCube (μ : ℝ)
    (q₀ : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ)) (c : Torus S.d (n k)) :
    AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
      C.actCube Y q.1 hv μ (castΩField C.coarseSide_eq (C.genW Y) q.2) c) q₀ := by
  have h1 := analyticAt_actionGWithCube (q₀ := q₀) C.tCubeOfBg C.tCubeOfBlk
    (levelGen (ϱ := (1 : ℝ)) k) C.weights μ (hC hv) (C.bgSet Y) c
    (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
      C.psiLevelKOf q.1)
    (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
      C.phiBarAt Y q.1 hv (castΩField C.coarseSide_eq (C.genW Y) q.2))
    (C.analyticAt_psiLevelKOf Y q₀) (C.analyticAt_phiBarAt Y hv q₀)
  have h2 := analyticAt_starBondEWithCube (q₀ := q₀) C.tCubeOfBg (C.bgSet Y) c
    (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
      C.phiBarAt Y q.1 hv (castΩField C.coarseSide_eq (C.genW Y) q.2))
    (C.analyticAt_phiBarAt Y hv q₀)
  exact h1.add (analyticAt_const.mul h2)

/-- The coordinates of `ψ^{(j)}` at a site are analytic in `(ψ_k, φ)`. -/
theorem analyticAt_psiJAt_site
    (q₀ : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ)) (j : ℕ)
    (s : Localization.CTorus S.d S.L C.N₁ m₁ k) :
    AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
      C.psiJAt Y q.1 hv (castΩField C.coarseSide_eq (C.genW Y) q.2) j s) q₀ :=
  analyticAt_pi_iff.1 (C.analyticAt_psiJAt_cast Y hv (j := j) q₀) s

/-- **The source term of a cube is analytic jointly in a parameter of the source and in
`(ψ_k, φ)`** (it is bilinear in `g` and `φ̄`). -/
theorem analyticAt_gCube_joint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (gq : E → GIdx S n M K N → ℂ) (e₀ : E) (hgq : AnalyticAt ℂ gq e₀)
    (q₀ : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ)) (c : Torus S.d (n k)) :
    AnalyticAt ℂ (fun p : E × ((BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ)) =>
      Def7v2.gCube C Y p.2.1 hv (gq p.1) (castΩField C.coarseSide_eq (C.genW Y) p.2.2) c)
      (e₀, q₀) := by
  unfold Def7v2.gCube
  exact Finset.analyticAt_fun_sum _ fun x _ => Finset.analyticAt_fun_sum _ fun i _ =>
    (analyticAt_prodFst (analyticAt_pi_iff.1 hgq _)).mul
      (analyticAt_prodSnd (C.analyticAt_phiBarAt Y hv q₀ x i))

/-- **The source term of a cube is analytic in `(ψ_k, φ)`.** -/
theorem analyticAt_gCube (g : GIdx S n M K N → ℂ)
    (q₀ : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ)) (c : Torus S.d (n k)) :
    AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
      Def7v2.gCube C Y q.1 hv g (castΩField C.coarseSide_eq (C.genW Y) q.2) c) q₀ :=
  (C.analyticAt_gCube_joint Y hv (fun _ : ℂ => g) 0 analyticAt_const q₀ c).comp
    (analyticAt_const.prod analyticAt_id)

/-- **The corrections of a cube are analytic in `(ψ_k, φ)`** where `ψ^{(j)} · ψ^{(j)}` lies in the
slit plane at the sites of the cube in `Y^≈` (the coefficients vanish at the other sites). -/
theorem analyticAt_corrCube (vc : Def7v2.CorrCoef S.d)
    (q₀ : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ)) (j : ℕ)
    (c : Torus S.d (n k))
    (hslit : ∀ s, C.tCubeOfC s = c → s ∈ C.sset (thickY R Y) →
      SmallField.dot (C.psiJAt Y q₀.1 hv (castΩField C.coarseSide_eq (C.genW Y) q₀.2) j s)
        (C.psiJAt Y q₀.1 hv (castΩField C.coarseSide_eq (C.genW Y) q₀.2) j s) ∈
        Complex.slitPlane) :
    AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
      Def7v2.corrCube C vc Y q.1 hv (castΩField C.coarseSide_eq (C.genW Y) q.2) j c) q₀ := by
  classical
  unfold Def7v2.corrCube
  refine Finset.analyticAt_fun_sum _ fun s hs => ?_
  have hsc : C.tCubeOfC s = c := (Finset.mem_filter.1 hs).2
  have hψ := C.analyticAt_psiJAt_site Y hv q₀ j s
  have hψi : ∀ i, AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) ×
      ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
      C.psiJAt Y q.1 hv (castΩField C.coarseSide_eq (C.genW Y) q.2) j s i) q₀ :=
    fun i => analyticAt_pi_iff.1 hψ i
  by_cases hsT : s ∈ C.sset (thickY R Y)
  · have hu := AnalyticAt.comp (g := Def7v2.unitDirC (N := N))
      (f := fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
        C.psiJAt Y q.1 hv (castΩField C.coarseSide_eq (C.genW Y) q.2) j s) (x := q₀)
      (Def7v2.unitDirC_analyticAt (hslit s hsc hsT)) hψ
    exact (analyticAt_const.mul (analyticAt_dot_comp hψi hψi)).add
      (analyticAt_const.mul (analyticAt_const.mul
        (analyticAt_dot_comp (fun _ => analyticAt_const) (fun i => analyticAt_pi_iff.1 hu i))))
  · have hB : s ∉ C.alignedIn j (thickY R Y) := fun h => hsT (Finset.mem_filter.1 h).2.2
    have hA : s ∉ C.alignedIn j Y := fun h =>
      hsT (subset_nbhd _ Y (Finset.mem_filter.1 h).2.2)
    have h0 : ∀ v : Localization.CTorus S.d S.L C.N₁ m₁ k →
        Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ,
        corrCoefSite v (C.alignedIn j Y) (C.alignedIn j (thickY R Y)) s = 0 := by
      intro v
      simp [corrCoefSite, hA, hB]
    simp only [h0, mul_zero, zero_mul, add_zero]
    exact analyticAt_const

/-- **The root of a cube is analytic jointly in a parameter of the source and in `(ψ_k, φ)`**
where `ψ^{(j)} · ψ^{(j)}` lies in the slit plane at the sites of the cube in `Y^≈`. -/
theorem analyticAt_cubeRoot_joint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (vc : Def7v2.CorrCoef S.d) (gq : E → GIdx S n M K N → ℂ) (e₀ : E) (hgq : AnalyticAt ℂ gq e₀)
    (q₀ : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ)) (c : Torus S.d (n k))
    (hslit : ∀ j ∈ Finset.Icc 1 k, ∀ s, C.tCubeOfC s = c → s ∈ C.sset (thickY R Y) →
      SmallField.dot (C.psiJAt Y q₀.1 hv (castΩField C.coarseSide_eq (C.genW Y) q₀.2) j s)
        (C.psiJAt Y q₀.1 hv (castΩField C.coarseSide_eq (C.genW Y) q₀.2) j s) ∈
        Complex.slitPlane) :
    AnalyticAt ℂ (fun p : E × ((BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ)) =>
      Def7v2.cubeRoot C vc Y p.2.1 hv (gq p.1) (castΩField C.coarseSide_eq (C.genW Y) p.2.2) c)
      (e₀, q₀) := by
  unfold Def7v2.cubeRoot
  exact ((analyticAt_const.mul (analyticAt_prodSnd (C.analyticAt_actCube Y hv _ q₀ c))).sub
    (Finset.analyticAt_fun_sum _ fun j hj =>
      analyticAt_prodSnd (C.analyticAt_corrCube Y hv vc q₀ j c (hslit j hj)))).add
    (C.analyticAt_gCube_joint Y hv gq e₀ hgq q₀ c)

/-- **The root of a cube is analytic in `(ψ_k, φ)`** where the composed fields of all levels lie in
the slit plane at the sites of the cube in `Y^≈`. -/
theorem analyticAt_cubeRoot (vc : Def7v2.CorrCoef S.d) (g : GIdx S n M K N → ℂ)
    (q₀ : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ)) (c : Torus S.d (n k))
    (hslit : ∀ j ∈ Finset.Icc 1 k, ∀ s, C.tCubeOfC s = c → s ∈ C.sset (thickY R Y) →
      SmallField.dot (C.psiJAt Y q₀.1 hv (castΩField C.coarseSide_eq (C.genW Y) q₀.2) j s)
        (C.psiJAt Y q₀.1 hv (castΩField C.coarseSide_eq (C.genW Y) q₀.2) j s) ∈
        Complex.slitPlane) :
    AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
      Def7v2.cubeRoot C vc Y q.1 hv g (castΩField C.coarseSide_eq (C.genW Y) q.2) c) q₀ :=
  (C.analyticAt_cubeRoot_joint Y hv vc (fun _ : ℂ => g) 0 analyticAt_const q₀ c hslit).comp
    (analyticAt_const.prod analyticAt_id)

variable (Y₁ Y₂ : Set (Torus S.d (n k)))

/-- **The pair functional of a cube root of the residual of `R`**: the root of the cube `c` for
the old region `Y₁` at a field of `genWC Y₁`, minus the one for the new region `Y₂`. -/
noncomputable def cubePair (vc : Def7v2.CorrCoef S.d) (g : GIdx S n M K N → ℂ) (c : Torus S.d (n k))
    (u : BlockAt S n M K k → Fin N → ℂ) (φ₁ : (C.genWC Y₁).Ω 1 × Fin N → ℂ)
    (φ₂ : (C.genWC Y₂).Ω 1 × Fin N → ℂ) : ℂ :=
  Def7v2.cubeRoot C vc Y₁ u hv g (castΩField C.coarseSide_eq (C.genW Y₁) φ₁) c -
    Def7v2.cubeRoot C vc Y₂ u hv g (castΩField C.coarseSide_eq (C.genW Y₂) φ₂) c

/-- **The pair functional of a cube root is analytic** in `(ψ_k, φ₁, φ₂)` where the composed fields
lie in the slit plane at the sites of the cube in `Y₁^≈`, resp. `Y₂^≈`. -/
theorem analyticAt_cubePair (vc : Def7v2.CorrCoef S.d) (g : GIdx S n M K N → ℂ) (c : Torus S.d (n k))
    (u : BlockAt S n M K k → Fin N → ℂ) (φ₁ : (C.genWC Y₁).Ω 1 × Fin N → ℂ)
    (φ₂ : (C.genWC Y₂).Ω 1 × Fin N → ℂ)
    (hslit₁ : ∀ j ∈ Finset.Icc 1 k, ∀ s, C.tCubeOfC s = c → s ∈ C.sset (thickY R Y₁) →
      SmallField.dot (C.psiJAt Y₁ u hv (castΩField C.coarseSide_eq (C.genW Y₁) φ₁) j s)
        (C.psiJAt Y₁ u hv (castΩField C.coarseSide_eq (C.genW Y₁) φ₁) j s) ∈ Complex.slitPlane)
    (hslit₂ : ∀ j ∈ Finset.Icc 1 k, ∀ s, C.tCubeOfC s = c → s ∈ C.sset (thickY R Y₂) →
      SmallField.dot (C.psiJAt Y₂ u hv (castΩField C.coarseSide_eq (C.genW Y₂) φ₂) j s)
        (C.psiJAt Y₂ u hv (castΩField C.coarseSide_eq (C.genW Y₂) φ₂) j s) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y₁).Ω 1 × Fin N → ℂ) ×
        ((C.genWC Y₂).Ω 1 × Fin N → ℂ) => C.cubePair hv Y₁ Y₂ vc g c q.1 q.2.1 q.2.2)
      (u, φ₁, φ₂) := by
  have h1 := C.analyticAt_cubeRoot Y₁ hv vc g (u, φ₁) c hslit₁
  have h2 := C.analyticAt_cubeRoot Y₂ hv vc g (u, φ₂) c hslit₂
  have p1 : AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) ×
      ((C.genWC Y₁).Ω 1 × Fin N → ℂ) × ((C.genWC Y₂).Ω 1 × Fin N → ℂ) => (q.1, q.2.1))
      (u, φ₁, φ₂) := analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
  have p2 : AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) ×
      ((C.genWC Y₁).Ω 1 × Fin N → ℂ) × ((C.genWC Y₂).Ω 1 × Fin N → ℂ) => (q.1, q.2.2))
      (u, φ₁, φ₂) := analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have c1 := AnalyticAt.comp (g := fun q : (BlockAt S n M K k → Fin N → ℂ) ×
      ((C.genWC Y₁).Ω 1 × Fin N → ℂ) =>
      Def7v2.cubeRoot C vc Y₁ q.1 hv g (castΩField C.coarseSide_eq (C.genW Y₁) q.2) c)
    (f := fun q : (BlockAt S n M K k → Fin N → ℂ) ×
      ((C.genWC Y₁).Ω 1 × Fin N → ℂ) × ((C.genWC Y₂).Ω 1 × Fin N → ℂ) => (q.1, q.2.1))
    (x := (u, φ₁, φ₂)) h1 p1
  have c2 := AnalyticAt.comp (g := fun q : (BlockAt S n M K k → Fin N → ℂ) ×
      ((C.genWC Y₂).Ω 1 × Fin N → ℂ) =>
      Def7v2.cubeRoot C vc Y₂ q.1 hv g (castΩField C.coarseSide_eq (C.genW Y₂) q.2) c)
    (f := fun q : (BlockAt S n M K k → Fin N → ℂ) ×
      ((C.genWC Y₁).Ω 1 × Fin N → ℂ) × ((C.genWC Y₂).Ω 1 × Fin N → ℂ) => (q.1, q.2.2))
    (x := (u, φ₁, φ₂)) h2 p2
  exact c1.sub c2

end Def7.SFCtx

end Balaban.LargeField
