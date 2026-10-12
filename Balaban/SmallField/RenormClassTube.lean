/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgTube
public import Balaban.SmallField.RenormAnisoDefs

/-!
# The extension to the anisotropic tube by complex orthogonal rotations

The analogue of `trickFn`, `TubeHyp` of `Def6AvgTube` with the isotropic ball around the reference
point replaced by the anisotropic polydisc `polyAniso` (CLASS-RULINGS Q-D):

* `mem_polyAniso_reCfg`: reindexing along a pair of mutually inverse maps preserves the polydisc;
* `trickFnA`: the extension of a function on the polydisc to `TubeAniso`;
* `TubeHypA`: analyticity on the polydisc and rotation invariance between points of the polydisc;
  it gives well-definedness (`TubeHypA.trickFnA_eq`), analyticity on `TubeAniso`, the bound,
  rotation invariance, and compatibility with reindexing (`trickFnA_comp`).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.SmallField Metric Set

variable {d N : ℕ}

theorem mem_polyAniso_reCfg {X X' : Finset (Site d)} (σ τ : Site d → Site d)
    (hσ : ∀ x ∈ X, σ x ∈ X') (hτ : ∀ x ∈ X', τ x ∈ X) (hστ : ∀ x ∈ X', σ (τ x) = x)
    (i₀ : Fin N) (ν r : ℝ) (c : Cfg d N X') :
    reCfg σ hσ c ∈ polyAniso i₀ ν r X ↔ c ∈ polyAniso i₀ ν r X' := by
  constructor
  · intro h p
    rcases p with ⟨x', i⟩ | i
    · have := h (Sum.inl (⟨τ x'.1, hτ _ x'.2⟩, i))
      rw [reCfg_inl, refPt_inl] at this
      have e : (⟨σ (τ x'.1), hσ _ (hτ _ x'.2)⟩ : ↥X') = x' := Subtype.ext (hστ _ x'.2)
      simp only [e] at this
      rw [refPt_inl, anisoWt_inl]
      simpa [anisoWt_inl] using this
    · have := h (Sum.inr i)
      rwa [reCfg_inr, refPt_inr] at this
  · intro h p
    rcases p with ⟨x, i⟩ | i
    · have := h (Sum.inl (⟨σ x.1, hσ _ x.2⟩, i))
      rw [reCfg_inl, refPt_inl]
      simpa [refPt_inl, anisoWt_inl] using this
    · have := h (Sum.inr i)
      rwa [reCfg_inr, refPt_inr]

section Trick

variable {X : Finset (Site d)}

open Classical in
/-- **The extension of a function on the anisotropic polydisc to the anisotropic tube**: at a
configuration of the tube, the value at any complex orthogonal rotation of bounded entries that
carries the configuration into the polydisc; elsewhere the function itself. -/
noncomputable def trickFnA (i₀ : Fin N) (νj r : ℝ) (F : Cfg d N X → ℂ) (c : Cfg d N X) : ℂ :=
  if h : ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
      rotCfgL R X c ∈ polyAniso i₀ νj r X then F (rotCfgL (Classical.choose h) X c) else F c

/-- The properties of a function `F` on the polydisc around the reference point that make its
extension to the tube well defined and analytic. -/
structure TubeHypA (i₀ : Fin N) (νj r : ℝ) (F : Cfg d N X → ℂ) : Prop where
  analytic : ∀ c ∈ polyAniso i₀ νj r X, AnalyticAt ℂ F c
  rot : ∀ M : Matrix (Fin N) (Fin N) ℂ, IsOrth M → (∀ i k, ‖M i k‖ ≤ rotB N) →
    ∀ u u' : Cfg d N X, u ∈ polyAniso i₀ νj r X → u' ∈ polyAniso i₀ νj r X →
      rotCfgL M X u = u' → F u' = F u

variable {i₀ : Fin N} {νj r : ℝ} {F : Cfg d N X → ℂ}

theorem TubeHypA.witness (hT : TubeHypA i₀ νj r F) {c : Cfg d N X}
    {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsOrth A) (hB : IsOrth B) {ma mb : ℝ}
    (hAb : ∀ i k, ‖A i k‖ ≤ ma) (hBb : ∀ i k, ‖B i k‖ ≤ mb) (ha : 0 ≤ ma)
    (hab : (N : ℝ) * (ma * mb) ≤ rotB N)
    (hcA : rotCfgL A X c ∈ polyAniso i₀ νj r X)
    (hcB : rotCfgL B X c ∈ polyAniso i₀ νj r X) :
    F (rotCfgL A X c) = F (rotCfgL B X c) := by
  have hBBt : B * B.transpose = 1 := isOrth_mul_transpose hB
  have hM : IsOrth (A * B.transpose) := by
    unfold IsOrth
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc A.transpose, hA, Matrix.one_mul, hBBt]
  refine hT.rot (A * B.transpose) hM
    (fun i k => (mul_entry_le hAb (transpose_entry_le hBb) ha i k).trans hab) _ _ hcB hcA ?_
  rw [← rotCfgL_mul, Matrix.mul_assoc, show B.transpose * B = 1 from hB, Matrix.mul_one]

theorem TubeHypA.trickFnA_eq (hT : TubeHypA i₀ νj r F) {c : Cfg d N X}
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsOrth R) (hRb : EntryBd N R)
    (hRc : rotCfgL R X c ∈ polyAniso i₀ νj r X) :
    trickFnA i₀ νj r F c = F (rotCfgL R X c) := by
  have hex : ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
      rotCfgL R X c ∈ polyAniso i₀ νj r X := ⟨R, hR, hRb, hRc⟩
  unfold trickFnA
  simp only [hex, dite_true]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hex
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  refine hT.witness h1 hR (entryBd_bound h2) (entryBd_bound hRb) (by norm_num) ?_ h3 hRc
  unfold rotB; nlinarith

theorem trickFnA_of_poly (hT : TubeHypA i₀ νj r F) {c : Cfg d N X}
    (hc : c ∈ polyAniso i₀ νj r X) : trickFnA i₀ νj r F c = F c := by
  rw [hT.trickFnA_eq isOrth_one entryBd_one (by rwa [rotCfgL_one]), rotCfgL_one]

theorem TubeHypA.trickFnA_analytic (hT : TubeHypA i₀ νj r F) :
    AnalyticOnNhd ℂ (trickFnA i₀ νj r F) (TubeAniso i₀ νj r X) := by
  intro c₀ hc₀
  obtain ⟨R₀, h1, h2, h3⟩ := hc₀
  have hcont : Continuous (rotCfgL R₀ X) := LinearMap.continuous_of_finiteDimensional _
  have hopen : IsOpen {c : Cfg d N X | rotCfgL R₀ X c ∈ polyAniso i₀ νj r X} :=
    isOpen_polyAniso.preimage hcont
  have hAn : AnalyticAt ℂ (fun c => F (rotCfgL R₀ X c)) c₀ :=
    AnalyticAt.comp (g := F) (hT.analytic _ h3)
      ((LinearMap.toContinuousLinearMap (rotCfgL R₀ X)).analyticAt c₀)
  refine hAn.congr ?_
  filter_upwards [hopen.mem_nhds h3] with c hc
  exact (hT.trickFnA_eq h1 h2 hc).symm

theorem TubeHypA.trickFnA_bound (hT : TubeHypA i₀ νj r F) {B : ℝ}
    (hB : ∀ c ∈ polyAniso i₀ νj r X, ‖F c‖ ≤ B) {c : Cfg d N X}
    (hc : c ∈ TubeAniso i₀ νj r X) : ‖trickFnA i₀ νj r F c‖ ≤ B := by
  obtain ⟨R, h1, h2, h3⟩ := hc
  rw [hT.trickFnA_eq h1 h2 h3]
  exact hB _ h3

theorem TubeHypA.trickFnA_rot (hT : TubeHypA i₀ νj r F) {c : Cfg d N X}
    (hc : c ∈ TubeAniso i₀ νj r X) {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsOrth R)
    (hRb : EntryBd N R) (hRc : rotCfgL R X c ∈ TubeAniso i₀ νj r X) :
    trickFnA i₀ νj r F (rotCfgL R X c) = trickFnA i₀ νj r F c := by
  obtain ⟨W, hW1, hW2, hW3⟩ := hc
  obtain ⟨W', hW1', hW2', hW3'⟩ := hRc
  rw [hT.trickFnA_eq hW1' hW2' hW3', hT.trickFnA_eq hW1 hW2 hW3]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hWR : IsOrth (W' * R) := by
    unfold IsOrth
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc W'.transpose, hW1',
      Matrix.one_mul, hR]
  have := hT.witness hWR hW1 (ma := (N : ℝ) * (40 * 40)) (mb := 40)
    (mul_entry_le (entryBd_bound hW2') (entryBd_bound hRb) (by norm_num))
    (entryBd_bound hW2) (by positivity) (by unfold rotB; nlinarith)
    (by rw [rotCfgL_mul]; exact hW3') hW3
  rw [rotCfgL_mul] at this
  exact this

section Comp

variable {X' : Finset (Site d)}

/-- A reindexing linear map that commutes with the rotations and respects the polydiscs. -/
theorem TubeHypA.comp (hT : TubeHypA i₀ νj r F) (Lm : Cfg d N X' →ₗ[ℂ] Cfg d N X)
    (hrot : ∀ (R : Matrix (Fin N) (Fin N) ℂ) (c : Cfg d N X'),
      Lm (rotCfgL R X' c) = rotCfgL R X (Lm c))
    (hball : ∀ c, Lm c ∈ polyAniso i₀ νj r X ↔ c ∈ polyAniso i₀ νj r X') :
    TubeHypA i₀ νj r (fun c => F (Lm c)) where
  analytic := fun c hc => AnalyticAt.comp (g := F) (hT.analytic _ ((hball c).2 hc))
    ((LinearMap.toContinuousLinearMap Lm).analyticAt c)
  rot := fun M hM hMb u u' hu hu' hr => by
    refine hT.rot M hM hMb _ _ ((hball u).2 hu) ((hball u').2 hu') ?_
    rw [← hrot, hr]

theorem trickFnA_comp (hT : TubeHypA i₀ νj r F) (Lm : Cfg d N X' →ₗ[ℂ] Cfg d N X)
    (hrot : ∀ (R : Matrix (Fin N) (Fin N) ℂ) (c : Cfg d N X'),
      Lm (rotCfgL R X' c) = rotCfgL R X (Lm c))
    (hball : ∀ c, Lm c ∈ polyAniso i₀ νj r X ↔ c ∈ polyAniso i₀ νj r X')
    (c : Cfg d N X') :
    trickFnA i₀ νj r (fun c => F (Lm c)) c = trickFnA i₀ νj r F (Lm c) := by
  by_cases hex : ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
      rotCfgL R X' c ∈ polyAniso i₀ νj r X'
  · obtain ⟨R, h1, h2, h3⟩ := hex
    have hT' := hT.comp Lm hrot hball
    rw [hT'.trickFnA_eq h1 h2 h3]
    rw [hT.trickFnA_eq h1 h2 (by rw [← hrot]; exact (hball _).2 h3), hrot]
  · have hex' : ¬ ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
        rotCfgL R X (Lm c) ∈ polyAniso i₀ νj r X := by
      rintro ⟨R, h1, h2, h3⟩
      exact hex ⟨R, h1, h2, (hball _).1 (by rw [hrot]; exact h3)⟩
    unfold trickFnA
    simp only [hex, hex', dite_false]

end Comp

end Trick

end Balaban.SmallField.Def6
