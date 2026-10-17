module

public import Balaban.LargeField.Base.BaseFirstCut

/-!
# Positivity of the first cut Hessian on local record-supported data

The real cut operator and both principal blocks are positive definite. The cut is indexed by
an arbitrary predicate on the local coordinate set; a geometric first-block union is used later
for factorization.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Green
open Balaban.LargeField.Base Matrix Classical

open Classical in
/-- The cut first-step Hessian on a record-supported local background is positive definite,
as are the matrices on the integrated and retained coordinate sets. -/
theorem baseFirstCut_posDef_of_spinSupport
    {d L N₀ N : ℕ} [NeZero N₀] [NeZero L] {ϱ ν δ₀ : ℝ}
    (G : GeneratingSet d L N₀ 1 ϱ) (a : ℕ → ℝ)
    (φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ) (h : Fin N → ℝ)
    (D : BgData G N) (H : BgHyp d L 1 ϱ a ν)
    (S : BaseSpinSupport G ν δ₀ φ h D)
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4)
    (s : FineBond d L N₀ → ℂ) (hs : s ∈ baseParamNbhd G 0)
    (hsr : ∀ b ∈ baseCutBonds G, (s b).im = 0)
    (P : G.Ω 1 × Fin N → Prop) :
    let e : G.Ω 1 → Fin N → ℝ := fun z i => (bgField G a ν D (z, i)).re
    let A := baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a ν (bgMult G a ν D) s)
    let K := A.map Complex.re
    let vI : {p // P p} → G.Ω 1 × Fin N := Subtype.val
    let vJ : {p // ¬ P p} → G.Ω 1 × Fin N := Subtype.val
    K.PosDef ∧ (K.submatrix vI vI).PosDef ∧ (K.submatrix vJ vJ).PosDef := by
  dsimp only
  let e : G.Ω 1 → Fin N → ℝ := fun z i => (bgField G a ν D (z, i)).re
  let A := baseOp N (fun z i => (e z i : ℂ))
    (baseHamiltonian G a ν (bgMult G a ν D) s)
  have he : ∀ z, ∑ i, e z i ^ 2 = 1 := fun z =>
    (spins_near_background (G := G) H S hΛ1 hΛ2 z).1
  have hα : ∀ z, ‖bgMult G a ν D z‖ ≤ 1 / (8 * (L : ℝ) ^ 2) :=
    baseFirstCut_multiplier_bound G a φ h D H S hΛ1
  have hreal : ∀ z, (bgMult G a ν D z).im = 0 :=
    baseFirstCut_multiplier_real G a φ h D H S hΛ1
  have hd : 0 < d := by have := H.hd; omega
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hγ : 0 < baseCoercivity L / 2 := half_pos (baseCoercivity_pos hL)
  have hη : (0 : ℝ) ≤ baseCoercivity L / (8 * d) := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hcpos := baseCoercivity_pos hL
    positivity
  have hA : IsCoercive A (baseCoercivity L / 2) :=
    baseOp_isCoercive_of_close G H.mass H.weights hα le_rfl hη hs e he
  obtain ⟨Kr, hKr, hAeq⟩ := baseOp_exists_real e
    (baseHamiltonian G a ν (bgMult G a ν D) s)
    (baseHamiltonian_im_eq_zero G a ν (bgMult G a ν D) s hreal hsr)
    (baseHamiltonian_symm G a ν (bgMult G a ν D) s)
  change A = Kr.map (algebraMap ℝ ℂ) at hAeq
  have hK : A.map Complex.re = Kr := by
    rw [hAeq]
    ext p q
    simp
  have hsym : (A.map Complex.re).IsSymm := by rw [hK]; exact hKr
  have hmap : (A.map Complex.re).map (algebraMap ℝ ℂ) = A := by
    rw [hK, hAeq]
  have hp := posDef_blocks_of_real_coercive A hsym hmap hγ hA P
  exact ⟨hp.1, hp.2.1, hp.2.2.1⟩

end Balaban.LargeField
