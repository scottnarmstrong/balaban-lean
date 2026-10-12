/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgLiftC

/-!
# Reynolds averaging: reindexing of configurations and the extension to the tube

* `reCfg`, `reCfgL`: the configuration on a polymer `X` induced by a configuration on `X'` along a
  map `X → X'`; it commutes with the rotations, maps the reference point to the reference point and
  is an isometry for a bijection (`reCfg_rot`, `reCfg_refPt`, `mem_ball_reCfg`);
* `trickFn`: the extension of a function on the ball around the reference point to the tube by
  complex orthogonal rotations of bounded entries (as `termL` of `Def6BridgeLift`), abstractly:
  `TubeHyp` (analyticity on the ball and rotation invariance between points of the ball) gives
  well-definedness (`TubeHyp.trickFn_eq`), analyticity on the tube, the bound, rotation invariance,
  and compatibility with reindexing (`trickFn_comp`).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.SmallField Metric Set

variable {d N : ℕ}

/-- **Reindexing of configurations**: the configuration on `X` obtained from a configuration on `X'`
along `σ : X → X'`. -/
def reCfg {X X' : Finset (Site d)} (σ : Site d → Site d) (hσ : ∀ x ∈ X, σ x ∈ X')
    (c : Cfg d N X') : Cfg d N X :=
  fun i => Sum.elim (fun p : ↥X × Fin N => c (Sum.inl (⟨σ p.1.1, hσ _ p.1.2⟩, p.2)))
    (fun i => c (Sum.inr i)) i

theorem reCfg_inl {X X' : Finset (Site d)} (σ : Site d → Site d) (hσ : ∀ x ∈ X, σ x ∈ X')
    (c : Cfg d N X') (p : ↥X × Fin N) :
    reCfg σ hσ c (Sum.inl p) = c (Sum.inl (⟨σ p.1.1, hσ _ p.1.2⟩, p.2)) := rfl

theorem reCfg_inr {X X' : Finset (Site d)} (σ : Site d → Site d) (hσ : ∀ x ∈ X, σ x ∈ X')
    (c : Cfg d N X') (i : Fin N) : reCfg σ hσ c (Sum.inr i) = c (Sum.inr i) := rfl

theorem reCfg_add {X X' : Finset (Site d)} (σ : Site d → Site d) (hσ : ∀ x ∈ X, σ x ∈ X')
    (c c' : Cfg d N X') : reCfg σ hσ (c + c') = reCfg σ hσ c + reCfg σ hσ c' := by
  ext (p | i) <;> rfl

theorem reCfg_sub {X X' : Finset (Site d)} (σ : Site d → Site d) (hσ : ∀ x ∈ X, σ x ∈ X')
    (c c' : Cfg d N X') : reCfg σ hσ (c - c') = reCfg σ hσ c - reCfg σ hσ c' := by
  ext (p | i) <;> rfl

theorem reCfg_smul {X X' : Finset (Site d)} (σ : Site d → Site d) (hσ : ∀ x ∈ X, σ x ∈ X')
    (t : ℂ) (c : Cfg d N X') : reCfg σ hσ (t • c) = t • reCfg σ hσ c := by
  ext (p | i) <;> rfl

/-- The reindexing as a linear map. -/
def reCfgL {X X' : Finset (Site d)} (σ : Site d → Site d) (hσ : ∀ x ∈ X, σ x ∈ X') :
    Cfg d N X' →ₗ[ℂ] Cfg d N X where
  toFun := reCfg σ hσ
  map_add' := reCfg_add σ hσ
  map_smul' := reCfg_smul σ hσ

theorem reCfg_rot {X X' : Finset (Site d)} (σ : Site d → Site d) (hσ : ∀ x ∈ X, σ x ∈ X')
    (R : Matrix (Fin N) (Fin N) ℂ) (c : Cfg d N X') :
    reCfg σ hσ (rotCfgL R X' c) = rotCfgL R X (reCfg σ hσ c) := by
  ext (p | i)
  · simp [reCfg_inl, rotCfgL_apply_inl]
  · simp [reCfg_inr, rotCfgL_apply_inr]

theorem reCfg_refPt {X X' : Finset (Site d)} (σ : Site d → Site d) (hσ : ∀ x ∈ X, σ x ∈ X')
    (i₀ : Fin N) (ν : ℝ) : reCfg σ hσ (refPt i₀ ν X') = refPt i₀ ν X := by
  ext (p | i)
  · simp [reCfg_inl, refPt, pack]
  · simp [reCfg_inr, refPt, pack]

theorem norm_reCfg_le {X X' : Finset (Site d)} (σ : Site d → Site d) (hσ : ∀ x ∈ X, σ x ∈ X')
    (c : Cfg d N X') : ‖reCfg σ hσ c‖ ≤ ‖c‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg c)).2 fun i => ?_
  rcases i with p | i
  · exact norm_le_pi_norm c _
  · exact norm_le_pi_norm c _

theorem norm_reCfg_eq {X X' : Finset (Site d)} (σ τ : Site d → Site d) (hσ : ∀ x ∈ X, σ x ∈ X')
    (hτ : ∀ x ∈ X', τ x ∈ X) (hστ : ∀ x ∈ X', σ (τ x) = x) (c : Cfg d N X') :
    ‖reCfg σ hσ c‖ = ‖c‖ := by
  refine le_antisymm (norm_reCfg_le σ hσ c) ?_
  have : reCfg τ hτ (reCfg σ hσ c) = c := by
    ext (p | i)
    · simp only [reCfg_inl, hστ _ p.1.2]
    · rfl
  calc ‖c‖ = ‖reCfg τ hτ (reCfg σ hσ c)‖ := by rw [this]
    _ ≤ ‖reCfg σ hσ c‖ := norm_reCfg_le τ hτ _

theorem mem_ball_reCfg {X X' : Finset (Site d)} (σ τ : Site d → Site d) (hσ : ∀ x ∈ X, σ x ∈ X')
    (hτ : ∀ x ∈ X', τ x ∈ X) (hστ : ∀ x ∈ X', σ (τ x) = x) (i₀ : Fin N) (ν ρ : ℝ)
    (c : Cfg d N X') :
    reCfg σ hσ c ∈ ball (refPt i₀ ν X) ρ ↔ c ∈ ball (refPt i₀ ν X') ρ := by
  rw [mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, ← reCfg_refPt σ hσ i₀ ν, ← reCfg_sub,
    norm_reCfg_eq σ τ hσ hτ hστ]

/-! ### The rotation trick, abstractly -/

section Trick

variable {X : Finset (Site d)}

open Classical in
/-- **The extension of a function on the ball to the tube**: at a configuration of the tube, the
value at any complex orthogonal rotation of bounded entries that carries the configuration into
the ball; elsewhere the function itself (CLASS-RULINGS Q-D). -/
noncomputable def trickFn (i₀ : Fin N) (νj ρ : ℝ) (F : Cfg d N X → ℂ) (c : Cfg d N X) : ℂ :=
  if h : ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
      rotCfgL R X c ∈ ball (refPt i₀ νj X) ρ then F (rotCfgL (Classical.choose h) X c) else F c

/-- The properties of a function `F` on the ball around the reference point that make its
extension to the tube well defined and analytic: analyticity at the points of the ball and
invariance under complex orthogonal rotations of bounded entries between points of the ball. -/
structure TubeHyp (i₀ : Fin N) (νj ρ : ℝ) (F : Cfg d N X → ℂ) : Prop where
  analytic : ∀ c ∈ ball (refPt i₀ νj X) ρ, AnalyticAt ℂ F c
  rot : ∀ M : Matrix (Fin N) (Fin N) ℂ, IsOrth M → (∀ i k, ‖M i k‖ ≤ rotB N) →
    ∀ u u' : Cfg d N X, u ∈ ball (refPt i₀ νj X) ρ → u' ∈ ball (refPt i₀ νj X) ρ →
      rotCfgL M X u = u' → F u' = F u

variable {i₀ : Fin N} {νj ρ : ℝ} {F : Cfg d N X → ℂ}

theorem TubeHyp.witness (hT : TubeHyp i₀ νj ρ F) {c : Cfg d N X}
    {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsOrth A) (hB : IsOrth B) {ma mb : ℝ}
    (hAb : ∀ i k, ‖A i k‖ ≤ ma) (hBb : ∀ i k, ‖B i k‖ ≤ mb) (ha : 0 ≤ ma)
    (hab : (N : ℝ) * (ma * mb) ≤ rotB N)
    (hcA : rotCfgL A X c ∈ ball (refPt i₀ νj X) ρ)
    (hcB : rotCfgL B X c ∈ ball (refPt i₀ νj X) ρ) :
    F (rotCfgL A X c) = F (rotCfgL B X c) := by
  have hBBt : B * B.transpose = 1 := isOrth_mul_transpose hB
  have hM : IsOrth (A * B.transpose) := by
    unfold IsOrth
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc A.transpose, hA, Matrix.one_mul, hBBt]
  refine hT.rot (A * B.transpose) hM
    (fun i k => (mul_entry_le hAb (transpose_entry_le hBb) ha i k).trans hab) _ _ hcB hcA ?_
  rw [← rotCfgL_mul, Matrix.mul_assoc, show B.transpose * B = 1 from hB, Matrix.mul_one]

theorem TubeHyp.trickFn_eq (hT : TubeHyp i₀ νj ρ F) {c : Cfg d N X}
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsOrth R) (hRb : EntryBd N R)
    (hRc : rotCfgL R X c ∈ ball (refPt i₀ νj X) ρ) :
    trickFn i₀ νj ρ F c = F (rotCfgL R X c) := by
  have hex : ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
      rotCfgL R X c ∈ ball (refPt i₀ νj X) ρ := ⟨R, hR, hRb, hRc⟩
  unfold trickFn
  simp only [hex, dite_true]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hex
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  refine hT.witness h1 hR (entryBd_bound h2) (entryBd_bound hRb) (by norm_num) ?_ h3 hRc
  unfold rotB; nlinarith

theorem trickFn_of_ball (hT : TubeHyp i₀ νj ρ F) {c : Cfg d N X}
    (hc : c ∈ ball (refPt i₀ νj X) ρ) : trickFn i₀ νj ρ F c = F c := by
  rw [hT.trickFn_eq isOrth_one entryBd_one (by rwa [rotCfgL_one]), rotCfgL_one]

theorem TubeHyp.trickFn_analytic (hT : TubeHyp i₀ νj ρ F) :
    AnalyticOnNhd ℂ (trickFn i₀ νj ρ F) (Tube i₀ νj ρ X) := by
  intro c₀ hc₀
  obtain ⟨R₀, h1, h2, h3⟩ := hc₀
  have hcont : Continuous (rotCfgL R₀ X) := LinearMap.continuous_of_finiteDimensional _
  have hopen : IsOpen {c : Cfg d N X | rotCfgL R₀ X c ∈ ball (refPt i₀ νj X) ρ} :=
    isOpen_ball.preimage hcont
  have hAn : AnalyticAt ℂ (fun c => F (rotCfgL R₀ X c)) c₀ :=
    AnalyticAt.comp (g := F) (hT.analytic _ h3)
      ((LinearMap.toContinuousLinearMap (rotCfgL R₀ X)).analyticAt c₀)
  refine hAn.congr ?_
  filter_upwards [hopen.mem_nhds h3] with c hc
  exact (hT.trickFn_eq h1 h2 hc).symm

theorem TubeHyp.trickFn_bound (hT : TubeHyp i₀ νj ρ F) {B : ℝ}
    (hB : ∀ c ∈ ball (refPt i₀ νj X) ρ, ‖F c‖ ≤ B) {c : Cfg d N X} (hc : c ∈ Tube i₀ νj ρ X) :
    ‖trickFn i₀ νj ρ F c‖ ≤ B := by
  obtain ⟨R, h1, h2, h3⟩ := hc
  rw [hT.trickFn_eq h1 h2 h3]
  exact hB _ h3

theorem TubeHyp.trickFn_rot (hT : TubeHyp i₀ νj ρ F) {c : Cfg d N X}
    (hc : c ∈ Tube i₀ νj ρ X) {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsOrth R) (hRb : EntryBd N R)
    (hRc : rotCfgL R X c ∈ Tube i₀ νj ρ X) :
    trickFn i₀ νj ρ F (rotCfgL R X c) = trickFn i₀ νj ρ F c := by
  obtain ⟨W, hW1, hW2, hW3⟩ := hc
  obtain ⟨W', hW1', hW2', hW3'⟩ := hRc
  rw [hT.trickFn_eq hW1' hW2' hW3', hT.trickFn_eq hW1 hW2 hW3]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hWR : IsOrth (W' * R) := by
    unfold IsOrth
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc W'.transpose, hW1', Matrix.one_mul,
      hR]
  have := hT.witness hWR hW1 (ma := (N : ℝ) * (40 * 40)) (mb := 40)
    (mul_entry_le (entryBd_bound hW2') (entryBd_bound hRb) (by norm_num))
    (entryBd_bound hW2) (by positivity) (by unfold rotB; nlinarith)
    (by rw [rotCfgL_mul]; exact hW3') hW3
  rw [rotCfgL_mul] at this
  exact this

section Comp

variable {X' : Finset (Site d)}

/-- A reindexing linear map that commutes with the rotations and respects the balls. -/
theorem TubeHyp.comp (hT : TubeHyp i₀ νj ρ F) (Lm : Cfg d N X' →ₗ[ℂ] Cfg d N X)
    (hrot : ∀ (R : Matrix (Fin N) (Fin N) ℂ) (c : Cfg d N X'),
      Lm (rotCfgL R X' c) = rotCfgL R X (Lm c))
    (hball : ∀ c, Lm c ∈ ball (refPt i₀ νj X) ρ ↔ c ∈ ball (refPt i₀ νj X') ρ) :
    TubeHyp i₀ νj ρ (fun c => F (Lm c)) where
  analytic := fun c hc => AnalyticAt.comp (g := F) (hT.analytic _ ((hball c).2 hc))
    ((LinearMap.toContinuousLinearMap Lm).analyticAt c)
  rot := fun M hM hMb u u' hu hu' hr => by
    refine hT.rot M hM hMb _ _ ((hball u).2 hu) ((hball u').2 hu') ?_
    rw [← hrot, hr]

theorem trickFn_comp (hT : TubeHyp i₀ νj ρ F) (Lm : Cfg d N X' →ₗ[ℂ] Cfg d N X)
    (hrot : ∀ (R : Matrix (Fin N) (Fin N) ℂ) (c : Cfg d N X'),
      Lm (rotCfgL R X' c) = rotCfgL R X (Lm c))
    (hball : ∀ c, Lm c ∈ ball (refPt i₀ νj X) ρ ↔ c ∈ ball (refPt i₀ νj X') ρ)
    (c : Cfg d N X') :
    trickFn i₀ νj ρ (fun c => F (Lm c)) c = trickFn i₀ νj ρ F (Lm c) := by
  by_cases hex : ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
      rotCfgL R X' c ∈ ball (refPt i₀ νj X') ρ
  · obtain ⟨R, h1, h2, h3⟩ := hex
    have hT' := hT.comp Lm hrot hball
    rw [hT'.trickFn_eq h1 h2 h3]
    rw [hT.trickFn_eq h1 h2 (by rw [← hrot]; exact (hball _).2 h3), hrot]
  · have hex' : ¬ ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
        rotCfgL R X (Lm c) ∈ ball (refPt i₀ νj X) ρ := by
      rintro ⟨R, h1, h2, h3⟩
      exact hex ⟨R, h1, h2, (hball _).1 (by rw [hrot]; exact h3)⟩
    unfold trickFn
    simp only [hex, hex', dite_false]

end Comp

end Trick

end Balaban.SmallField.Def6
