/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormTermwiseProps
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Lemma 3.2 (ii): analyticity of the termwise objects

The data `(ψ, b)` enter `T_X, A_{y,X}, Φ_{y,X}, I(y,X)` through finitely many coordinates: those on
`W ⊇ X ∪ star`.  For `c : Cfg d N W`, `unpsi W c` is the field equal to `c` on `W` and `0` outside
and `unb c` the field `b`.  We prove analyticity of `c ↦ Ttw (unpsi W c) (unb c)` etc.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

/-- The field determined by the coordinates `c` on `W` (zero outside `W`). -/
def unpsi (W : Finset (Site d)) (c : Cfg d N W) : Site d → Spin N :=
  fun x i => if h : x ∈ W then c (Sum.inl (⟨x, h⟩, i)) else 0

/-- The field `b` determined by the coordinates `c`. -/
def unb (W : Finset (Site d)) (c : Cfg d N W) : Spin N := fun i => c (Sum.inr i)

/-- The inclusion of coordinate indices for `X ⊆ W`. -/
def idxMap {X W : Finset (Site d)} (h : X ⊆ W) : Idx d N X → Idx d N W
  | Sum.inl (x, i) => Sum.inl (⟨x.1, h x.2⟩, i)
  | Sum.inr i => Sum.inr i

/-- The restriction of coordinates from `W` to `X ⊆ W` as a continuous linear map. -/
noncomputable def restrCfg {X W : Finset (Site d)} (h : X ⊆ W) : Cfg d N W →L[ℂ] Cfg d N X :=
  LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ (idxMap h))

theorem restrCfg_apply {X W : Finset (Site d)} (h : X ⊆ W) (c : Cfg d N W) (j : Idx d N X) :
    restrCfg h c j = c (idxMap h j) := rfl

theorem pack_unpsi {X W : Finset (Site d)} (h : X ⊆ W) (c : Cfg d N W) :
    pack X (unpsi W c) (unb W c) = restrCfg h c := by
  ext (⟨x, i⟩ | i)
  · simp [pack, unpsi, restrCfg_apply, idxMap, h x.2]
  · simp [pack, unb, restrCfg_apply, idxMap]

section Analytic

variable {W : Finset (Site d)}

theorem analyticAt_unpsi {x : Site d} (hx : x ∈ W) (i : Fin N) (c₀ : Cfg d N W) :
    AnalyticAt ℂ (fun c : Cfg d N W => unpsi W c x i) c₀ := by
  have : (fun c : Cfg d N W => unpsi W c x i) =
      fun c => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Idx d N W => ℂ)
        (Sum.inl (⟨x, hx⟩, i))) c := by
    funext c; simp [unpsi, hx]
  rw [this]
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Idx d N W => ℂ)
    (Sum.inl (⟨x, hx⟩, i))).analyticAt c₀

theorem analyticAt_unb (i : Fin N) (c₀ : Cfg d N W) :
    AnalyticAt ℂ (fun c : Cfg d N W => unb W c i) c₀ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Idx d N W => ℂ) (Sum.inr i)).analyticAt c₀

theorem analyticAt_dotF {f g : Cfg d N W → Spin N} {c₀ : Cfg d N W}
    (hf : ∀ i, AnalyticAt ℂ (fun c => f c i) c₀) (hg : ∀ i, AnalyticAt ℂ (fun c => g c i) c₀) :
    AnalyticAt ℂ (fun c => dot (f c) (g c)) c₀ := by
  unfold dot
  exact Finset.analyticAt_fun_sum _ fun i _ => (hf i).mul (hg i)

theorem analyticAt_psi_dot {x y : Site d} (hx : x ∈ W) (hy : y ∈ W) (c₀ : Cfg d N W) :
    AnalyticAt ℂ (fun c : Cfg d N W => dot (unpsi W c x) (unpsi W c y)) c₀ :=
  analyticAt_dotF (fun i => analyticAt_unpsi hx i c₀) (fun i => analyticAt_unpsi hy i c₀)

theorem analyticAt_psi_dot_b {x : Site d} (hx : x ∈ W) (c₀ : Cfg d N W) :
    AnalyticAt ℂ (fun c : Cfg d N W => dot (unpsi W c x) (unb W c)) c₀ :=
  analyticAt_dotF (fun i => analyticAt_unpsi hx i c₀) (fun i => analyticAt_unb i c₀)

theorem sqrtC_ne_zero {z : ℂ} (hz : z ≠ 0) : sqrtC z ≠ 0 := by
  intro h
  have := sqrtC_mul_self z
  rw [h, mul_zero] at this
  exact hz this.symm

theorem analyticAt_uInv (h0 : (0 : Site d) ∈ W) (c₀ : Cfg d N W)
    (hc : dot (unpsi W c₀ 0) (unpsi W c₀ 0) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun c : Cfg d N W => uInv (unpsi W c)) c₀ := by
  unfold uInv sqrtC
  exact (analyticAt_psi_dot h0 h0 c₀).cpow analyticAt_const hc

theorem analyticAt_vInv (h0 : (0 : Site d) ∈ W) (c₀ : Cfg d N W)
    (hc : dot (unpsi W c₀ 0) (unpsi W c₀ 0) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun c : Cfg d N W => vInv (unpsi W c) (unb W c)) c₀ := by
  unfold vInv
  refine (analyticAt_dotF (fun i => analyticAt_unpsi h0 i c₀)
    (fun i => analyticAt_unb i c₀)).div (analyticAt_uInv h0 c₀ hc) ?_
  exact sqrtC_ne_zero (Complex.slitPlane_ne_zero hc)

/-- `T_X` is analytic in the data wherever `ψ(y)·ψ(y)` avoids the closed negative axis. -/
theorem Ttw_analytic (T : TermFamily d N) (i₀ : Fin N) (ν : ℝ) (X : Finset (Site d))
    (h0 : (0 : Site d) ∈ W) :
    AnalyticOnNhd ℂ (fun c : Cfg d N W => Ttw T i₀ ν X (unpsi W c) (unb W c))
      {c | dot (unpsi W c 0) (unpsi W c 0) ∈ Complex.slitPlane} := by
  intro c₀ hc
  unfold Ttw
  have hu := analyticAt_uInv h0 c₀ hc
  have hv := analyticAt_vInv h0 c₀ hc
  exact ((analyticAt_const.add ((hu.sub analyticAt_const).mul analyticAt_const)).add
    ((hv.sub analyticAt_const).mul analyticAt_const))

/-- `A_{y,X}` is entire in the coordinates of the data. -/
theorem Ax_analytic (T : TermFamily d N) (i₀ : Fin N) (ν : ℝ) {X : Finset (Site d)}
    (hXW : X ⊆ W) (h0 : (0 : Site d) ∈ W) :
    AnalyticOnNhd ℂ (fun c : Cfg d N W => Ax T i₀ ν (unpsi W c) X) univ := by
  intro c₀ _
  unfold Ax
  refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun x _ => analyticAt_const.mul ?_)
  exact (analyticAt_psi_dot (hXW x.2) (hXW x.2) c₀).sub (analyticAt_psi_dot h0 h0 c₀)

theorem analyticAt_gradInv (hs : starSet d ⊆ W) (μ μ' : Fin d) (c₀ : Cfg d N W)
    (hc : dot (unpsi W c₀ 0) (unpsi W c₀ 0) ≠ 0) :
    AnalyticAt ℂ (fun c : Cfg d N W => gradInv (unpsi W c) μ μ') c₀ := by
  have h0 : (0 : Site d) ∈ W := hs zero_mem_starSet
  have hμ : eU μ ∈ W := hs (eU_mem_starSet μ)
  have hμ' : eU μ' ∈ W := hs (eU_mem_starSet μ')
  have hdiff : ∀ y ∈ W, ∀ i, AnalyticAt ℂ (fun c : Cfg d N W => (unpsi W c y - unpsi W c 0) i) c₀ :=
    fun y hy i => (analyticAt_unpsi hy i c₀).sub (analyticAt_unpsi h0 i c₀)
  unfold gradInv
  refine (analyticAt_dotF (hdiff _ hμ) (hdiff _ hμ')).sub ?_
  exact ((analyticAt_dotF (fun i => analyticAt_unpsi h0 i c₀) (hdiff _ hμ)).mul
    (analyticAt_dotF (fun i => analyticAt_unpsi h0 i c₀) (hdiff _ hμ'))).div
    (analyticAt_psi_dot h0 h0 c₀) hc

/-- `Φ_{y,X}` is analytic in the data wherever `ψ(y)·ψ(y) ≠ 0`. -/
theorem Phitw_analytic (T : TermFamily d N) (i₀ i₁ : Fin N) (ν : ℝ) (X : Finset (Site d))
    (hs : starSet d ⊆ W) :
    AnalyticOnNhd ℂ (fun c : Cfg d N W => Phitw T i₀ i₁ ν X (unpsi W c))
      {c | dot (unpsi W c 0) (unpsi W c 0) ≠ 0} := by
  intro c₀ hc
  unfold Phitw
  refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun μ _ =>
    Finset.analyticAt_fun_sum _ fun μ' _ => (analyticAt_gradInv hs μ μ' c₀ hc).mul analyticAt_const)

/-- **(ii), analyticity**: `I(y,X)` is analytic in the data wherever `𝓔(y,X)` is (the `Tube`),
and `ψ(y)·ψ(y)` avoids the closed negative axis. -/
theorem Itw_analytic {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom)
    {X : Finset (Site d)} (hX : X ∈ T.polys) (hXW : X ⊆ W) (hs : starSet d ⊆ W) :
    AnalyticOnNhd ℂ (fun c : Cfg d N W => Itw T i₀ i₁ ν X (unpsi W c) (unb W c))
      {c | restrCfg hXW c ∈ Tube i₀ ν ρ X ∧
        dot (unpsi W c 0) (unpsi W c 0) ∈ Complex.slitPlane} := by
  have h0 : (0 : Site d) ∈ W := hs zero_mem_starSet
  have hE : AnalyticOnNhd ℂ (fun c : Cfg d N W => T.term X (restrCfg hXW c))
      (restrCfg hXW ⁻¹' Tube i₀ ν ρ X) :=
    (hP.analytic X hX).compContinuousLinearMap (u := restrCfg hXW)
  intro c₀ ⟨hc1, hc2⟩
  have e : (fun c : Cfg d N W => Itw T i₀ i₁ ν X (unpsi W c) (unb W c)) =
      fun c => T.term X (restrCfg hXW c) - Ttw T i₀ ν X (unpsi W c) (unb W c) -
        Ax T i₀ ν (unpsi W c) X - Phitw T i₀ i₁ ν X (unpsi W c) := by
    funext c; unfold Itw; rw [pack_unpsi hXW]
  rw [e]
  exact (((hE c₀ hc1).sub (Ttw_analytic T i₀ ν X h0 c₀ hc2)).sub
    (Ax_analytic T i₀ ν hXW h0 c₀ trivial)).sub
    (Phitw_analytic T i₀ i₁ ν X hs c₀ (Complex.slitPlane_ne_zero hc2))

end Analytic

end Balaban.SmallField
