/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroData
public import Balaban.Background.ApproxAnalytic

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Smooth

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)

/-- The BG action written on the raw data `(Ψ, h)`. -/
noncomputable def actionRaw (a : ℕ → ℝ) (ν : ℝ) (Ψ h : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (φ : G.Ω 1 × Fin N → ℂ) : ℝ :=
  (1 / 2) * ∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) *
      ∑ i, ‖Ψ x i - blockAvg G φ x i‖ ^ 2 +
  (1 / 2) * ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, ‖barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i‖ ^ 2 else 0) +
  ν / 2 * ∑ x : G.Ω 1, ∑ i, ‖φ (x, i) - h x i‖ ^ 2

theorem action_eq_raw (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    action G a ν D φ = actionRaw G a ν D.Ψ D.h φ := rfl

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : WithTop ℕ∞}

theorem contDiff_ite_const {p : Prop} [Decidable p] {f g : V → ℝ} (hf : p → ContDiff ℝ n f)
    (hg : ¬ p → ContDiff ℝ n g) : ContDiff ℝ n (fun v => if p then f v else g v) := by
  by_cases hp : p
  · rw [show (fun v => if p then f v else g v) = f from funext fun v => by simp [hp]]
    exact hf hp
  · rw [show (fun v => if p then f v else g v) = g from funext fun v => by simp [hp]]
    exact hg hp

theorem contDiff_svec {φ : V → G.Ω 1 × Fin N → ℂ} (hφ : ContDiff ℝ n φ) (y : Torus d (N₀ * L ^ k))
    (i : Fin N) : ContDiff ℝ n (fun v => svec G (φ v) y i) := by
  by_cases hy : y ∈ G.Ω 1
  · have : (fun v => svec G (φ v) y i) = fun v => φ v (⟨y, hy⟩, i) :=
      funext fun v => svec_of_mem G (φ v) ⟨y, hy⟩ i
    rw [this]
    exact contDiff_pi.1 hφ (⟨y, hy⟩, i)
  · have : (fun v => svec G (φ v) y i) = fun _ => 0 := funext fun v => svec_of_not_mem G (φ v) hy i
    rw [this]
    exact contDiff_const

theorem contDiff_blockAvg {φ : V → G.Ω 1 × Fin N → ℂ} (hφ : ContDiff ℝ n φ) (x : Torus d (N₀ * L ^ k))
    (i : Fin N) : ContDiff ℝ n (fun v => blockAvg G (φ v) x i) := by
  unfold blockAvg
  exact contDiff_const.mul (ContDiff.sum fun y _ => contDiff_svec G hφ y i)

theorem contDiff_barField {Ψ : V → Torus d (N₀ * L ^ k) → Fin N → ℂ} {φ : V → G.Ω 1 × Fin N → ℂ}
    (hΨ : ContDiff ℝ n Ψ) (hφ : ContDiff ℝ n φ) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    ContDiff ℝ n (fun v => barField G (Ψ v) (φ v) x i) := by
  unfold barField
  by_cases hx : x ∈ G.Ω 1
  · simp only [hx, dite_true]
    exact contDiff_pi.1 hφ (⟨x, hx⟩, i)
  · simp only [hx, dite_false]
    exact contDiff_pi.1 (contDiff_pi.1 hΨ x) i

theorem contDiff_actionRaw (a : ℕ → ℝ) (ν : ℝ) {Ψ h : V → Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {φ : V → G.Ω 1 × Fin N → ℂ} (hΨ : ContDiff ℝ n Ψ) (hh : ContDiff ℝ n h) (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (fun v => actionRaw G a ν (Ψ v) (h v) (φ v)) := by
  unfold actionRaw
  refine ((contDiff_const.mul ?_).add (contDiff_const.mul ?_)).add (contDiff_const.mul ?_)
  · refine ContDiff.sum fun x _ => contDiff_const.mul (ContDiff.sum fun i _ => ?_)
    exact (contDiff_norm_sq ℝ).comp
      ((contDiff_pi.1 (contDiff_pi.1 hΨ x) i).sub (contDiff_blockAvg G hφ x i))
  · refine ContDiff.sum fun x _ => ContDiff.sum fun μ _ => contDiff_ite_const (fun _ => ?_) (fun _ => contDiff_const)
    exact ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      ((contDiff_barField G hΨ hφ _ i).sub (contDiff_barField G hΨ hφ x i))
  · refine ContDiff.sum fun x _ => ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp ?_
    exact (contDiff_pi.1 hφ (x, i)).sub (contDiff_pi.1 (contDiff_pi.1 hh x) i)

/-- The raw data `(Ψ, h)` of the lifted real block field. -/
noncomputable def rawMap (ψ : BlockField d L N₀ k N) : RawData d L N₀ k N :=
  ((dataR G ψ).Ψ, (dataR G ψ).h)

theorem contDiff_rawMap : ContDiff ℝ n (rawMap G (N := N)) := by
  classical
  refine ContDiff.prodMk ?_ ?_ <;> refine contDiff_pi.2 fun x => contDiff_pi.2 fun i => ?_
  · by_cases hx : x ∈ dataSites G
    · have : (fun ψ : BlockField d L N₀ k N => (dataR G ψ).Ψ x i) =
          fun ψ => (ψ (jBlock d L N₀ k k x) i : ℂ) :=
        funext fun ψ => by simpa [liftR] using dataR_Ψ G ψ hx i
      rw [this]
      exact Complex.ofRealCLM.contDiff.comp
        (contDiff_pi.1 (contDiff_pi.1 contDiff_id (jBlock d L N₀ k k x)) i)
    · have : (fun ψ : BlockField d L N₀ k N => (dataR G ψ).Ψ x i) = fun _ => 0 :=
        funext fun ψ => by simp [(dataR G ψ).Ψ_zero x hx]
      rw [this]
      exact contDiff_const
  · have : (fun ψ : BlockField d L N₀ k N => (dataR G ψ).h x i) = fun _ => 0 := by
      funext ψ
      by_cases hx : x ∈ G.Ω 1
      · simpa using dataR_h G ψ hx i
      · simp [(dataR G ψ).h_zero x hx]
    rw [this]
    exact contDiff_const

variable {a : ℕ → ℝ}

/-- The action as a smooth function of the triple `(raw data, background)`. -/
theorem contDiff_actionRaw_prod : ContDiff ℝ n (fun p : RawData d L N₀ k N × ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) =>
      actionRaw G a 0 p.1.1 p.1.2 p.2.1) := by
  have h1 : ContDiff ℝ n (fun p : RawData d L N₀ k N × ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) => p.1.1) :=
    contDiff_fst.fst
  have h2 : ContDiff ℝ n (fun p : RawData d L N₀ k N × ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) => p.1.2) :=
    contDiff_fst.snd
  have h3 : ContDiff ℝ n (fun p : RawData d L N₀ k N × ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) => p.2.1) :=
    contDiff_snd.fst
  exact contDiff_actionRaw G a 0 h1 h2 h3


/-- **The effective action is smooth on the tube**: on a set of block fields whose lifts lie in
`Ψ̃(𝔹; δ)` with `δ ≤ min (c₀, c₁)`, the effective action is `C^n` (Theorem 5.2 (2): the Def-5 background is
analytic in the data). -/
theorem contDiffOn_effAction (H : BgHyp d L k ϱ a 0) {δ : ℝ} (hδ : 0 < δ) (hδ0 : δ ≤ bgC0 d L N)
    (hδ1 : δ ≤ bgC1 d L N) {U : Set (BlockField d L N₀ k N)}
    (hT : ∀ ψ ∈ U, TubeOn G Set.univ δ ψ) : ContDiffOn ℝ n (effAction G a) U := by
  obtain ⟨Φ, hΦ, hΦe⟩ := theorem72_analytic (G := G) (N := N) H
  have hmaps : Set.MapsTo (rawMap G (N := N)) U
      {p | ∃ D : BgData G N, InUnionDomainC G (bgC0 d L N) (bgC1 d L N) 0 D ∧ p = (D.Ψ, D.h)} :=
    fun ψ hψ => ⟨dataR G ψ, inUnionDomainC_of_tube G hδ hδ0 hδ1 (hT ψ hψ), rfl⟩
  have hΦr : ContDiffOn ℝ n Φ
      {p | ∃ D : BgData G N, InUnionDomainC G (bgC0 d L N) (bgC1 d L N) 0 D ∧ p = (D.Ψ, D.h)} :=
    fun p hp => ((hΦ p hp).contDiffAt.restrict_scalars ℝ).contDiffWithinAt
  have hΦ' : ContDiffOn ℝ n (fun ψ => Φ (rawMap G ψ)) U :=
    hΦr.comp (contDiff_rawMap G).contDiffOn hmaps
  have hA := contDiff_actionRaw_prod (n := n) (a := a) (N := N) G
  have hcomp := hA.comp_contDiffOn ((contDiff_rawMap G (n := n)).contDiffOn.prodMk hΦ')
  refine hcomp.congr fun ψ hψ => ?_
  show effAction G a ψ = actionRaw G a 0 (rawMap G ψ).1 (rawMap G ψ).2 (Φ (rawMap G ψ)).1
  have hR := inUnionDomainR_of_tube G hδ hδ1 (hT ψ hψ)
  have hC := inUnionDomainC_of_tube G hδ hδ0 hδ1 (hT ψ hψ)
  have e1 := (theorem72_real H hR).1
  have e2 := hΦe (dataR G ψ) hC
  unfold effAction
  rw [action_eq_raw, ← e1]
  simp only [rawMap]
  rw [e2]

end Smooth

section Symm

open Matrix

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)

/-- The rotated block field `Q ψ_k`. -/
def rotBlock (Q : Matrix (Fin N) (Fin N) ℝ) (ψ : BlockField d L N₀ k N) : BlockField d L N₀ k N :=
  fun z => Q *ᵥ ψ z

theorem dataR_rot {Q : Matrix (Fin N) (Fin N) ℝ} (ψ : BlockField d L N₀ k N) :
    dataR G (rotBlock Q ψ) = (dataR G ψ).rot (cmat Q) := by
  refine BgData.ext' ?_ ?_
  · funext x
    by_cases hx : x ∈ dataSites G
    · funext i
      have h1 : (dataR G ψ).Ψ x = fun j => (ψ (jBlock d L N₀ k k x) j : ℂ) :=
        funext fun j => by simpa [liftR] using dataR_Ψ G ψ hx j
      simp only [BgData.rot]
      rw [h1, dataR_Ψ G _ hx, ← cmat_mulVec]
      rfl
    · simp [BgData.rot, (dataR G ψ).Ψ_zero x hx, (dataR G (rotBlock Q ψ)).Ψ_zero x hx]
  · funext x
    by_cases hx : x ∈ G.Ω 1
    · funext i
      have h1 : (dataR G ψ).h x = fun _ => 0 := funext fun j => by simpa using dataR_h G ψ hx j
      have h2 : (dataR G (rotBlock Q ψ)).h x i = 0 := by simpa using dataR_h G (rotBlock Q ψ) hx i
      simp only [BgData.rot, h1, h2]
      simp [Matrix.mulVec, dotProduct]
    · simp [BgData.rot, (dataR G ψ).h_zero x hx, (dataR G (rotBlock Q ψ)).h_zero x hx]

variable {a : ℕ → ℝ}

/-- **`O(N)`-invariance of the effective action**: `A_k(𝔹; Qψ̃, φ(Qψ̃)) = A_k(𝔹; ψ̃, φ(ψ̃))`. -/
theorem effAction_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (ψ : BlockField d L N₀ k N) :
    effAction G a (rotBlock Q ψ) = effAction G a ψ := by
  have hR := isRealOrth_ofReal hQ
  unfold effAction
  rw [dataR_rot, bgField_rot a 0 hR, action_rot hR]

end Symm

end Balaban.LargeField
