/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.H7Bridge
public import Balaban.LargeField.Characteristic.Analytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The H7 domain and the BG data (FLUCTUATION.md §4.2, Step 1, cube level)

For the generating set `G_q(□) = genCube` of a cube `□` (Definition II.2.4 (i)) and a complex block
field `ψ ∈ Δ^c_q(□; 1, r)` (`DeltaC`, Definition II.3.5 (a)), the lifted data
`liftSingle G ψ h` lie in the BG domain `𝒟` and satisfy the regularity inequalities on the
neighbourhood `□^{∼1}`:

* `deltaC_inUnionDomainC`, `deltaC_regIneq`: the inclusion of the H7 cube domain into the BG data;
* `liftSingle_sub`: the lifts of two block fields differ by the lift of the difference
  (the affine composition `(6.2)` at the cube level);
* `vn_sub_le_of_close`: two fields within `ρ`, `ρ'` of a common reference differ by `ρ + ρ'`
  (the data-change bound `δ₁ ≤ C_δ r` of Step 1);
* `h7_cube_step3`: the undecoupled Step 3 bound for the cube action on `genCube`, with the H7
  membership `ψ, ψ' ∈ Δ^c_q(□; 1, r)`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField

section Inclusion

variable {d M1 N₁ L N q c n : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] (a : ℕ → ℝ) (μ ε : ℝ)
  (h : Fin N → ℂ) (y0 : Torus d n)

/-- **Step 1, the inclusion**: block fields of `Δ^c_q(□; 1, ε)` have lifted data in the BG domain
`𝒟` of Theorem 5.2. -/
theorem deltaC_inUnionDomainC {ψ : Torus d (M1 * N₁ * L ^ (q - q)) → Fin N → ℂ}
    (hψ : ψ ∈ DeltaC (q := q) (M1 := M1) (N₁ := N₁) (L := L) a μ ε h c n y0) :
    InUnionDomainC (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0)
      (bgC0 d L N) (bgC1 d L N) μ
      (liftSingle (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) ψ h) :=
  hψ.1

/-- **Step 1, the inclusion**: the regularity inequalities of `Δ^c_q(□; 1, ε)` on `□^{∼1}`. -/
theorem deltaC_regIneq {ψ : Torus d (M1 * N₁ * L ^ (q - q)) → Fin N → ℂ}
    (hψ : ψ ∈ DeltaC (q := q) (M1 := M1) (N₁ := N₁) (L := L) a μ ε h c n y0) :
    RegIneq (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) a μ
      (liftSingle (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) ψ h) ε
      (cubeNbhd M1 N₁ L q c n 1 y0) (cubeNbhd M1 N₁ L q c n 1 y0) :=
  hψ.2

end Inclusion

section Lift

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The data change of two lifts: `(lift ψ' - lift ψ)` on the data sites, zero elsewhere. -/
noncomputable def liftDiff (G : GeneratingSet d L N₀ k ϱ)
    (ψ ψ' : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) : Fin N → ℂ :=
  open Classical in
  if x ∈ dataSites G then fun i => ψ' (jBlock d L N₀ k k x) i - ψ (jBlock d L N₀ k k x) i
  else 0

/-- **The composition (6.2) at the cube level is affine**: `lift ψ' = lift ψ + (lift ψ' - lift ψ)`
with the difference supported on the data sites whose block differs. -/
theorem liftSingle_sub (G : GeneratingSet d L N₀ k ϱ)
    (ψ ψ' : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) (h : Fin N → ℂ) (x : Torus d (N₀ * L ^ k))
    (i : Fin N) :
    (liftSingle G ψ' h).Ψ x i = (liftSingle G ψ h).Ψ x i + liftDiff G ψ ψ' x i := by
  classical
  by_cases hx : x ∈ dataSites G
  · rw [liftSingle_Ψ G ψ' h hx, liftSingle_Ψ G ψ h hx]
    simp [liftDiff, hx]
  · rw [(liftSingle G ψ' h).Ψ_zero x hx, (liftSingle G ψ h).Ψ_zero x hx]
    simp [liftDiff, hx]

theorem liftSingle_h_eq (G : GeneratingSet d L N₀ k ϱ)
    (ψ ψ' : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) (h : Fin N → ℂ) (x : Torus d (N₀ * L ^ k))
    (i : Fin N) : (liftSingle G ψ' h).h x i = (liftSingle G ψ h).h x i := by
  classical
  by_cases hx : x ∈ G.Ω 1
  · rw [liftSingle_h G ψ' h hx, liftSingle_h G ψ h hx]
  · rw [(liftSingle G ψ' h).h_zero x hx, (liftSingle G ψ h).h_zero x hx]

theorem liftDiff_eq_zero (G : GeneratingSet d L N₀ k ϱ)
    (ψ ψ' : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) (W : Finset (Torus d (N₀ * L ^ k)))
    (hW : ∀ x ∈ dataSites G, x ∉ W → ψ' (jBlock d L N₀ k k x) = ψ (jBlock d L N₀ k k x))
    (y : Torus d (N₀ * L ^ k)) (hy : y ∉ W) : liftDiff G ψ ψ' y = 0 := by
  classical
  unfold liftDiff
  by_cases hyd : y ∈ dataSites G
  · simp only [hyd, ↓reduceIte]
    funext i
    simp [hW y hyd hy]
  · simp [hyd]

theorem vn_liftDiff_le (G : GeneratingSet d L N₀ k ϱ)
    (ψ ψ' : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) {δ₁ : ℝ} (hδ₁ : 0 ≤ δ₁)
    (hb : ∀ b, vn (fun i => ψ' b i - ψ b i) ≤ δ₁) (x : Torus d (N₀ * L ^ k)) :
    vn (liftDiff G ψ ψ' x) ≤ δ₁ := by
  classical
  unfold liftDiff
  by_cases hx : x ∈ dataSites G
  · simp only [hx, ↓reduceIte]
    exact hb _
  · simp only [hx, ↓reduceIte]
    have : vn (0 : Fin N → ℂ) = 0 := by simp [vn]
    rw [this]; exact hδ₁

/-- **The data-change bound of Step 1**: two block fields within `ρ`, `ρ'` of a common (real)
reference differ by at most `ρ + ρ'`. -/
theorem vn_sub_le_of_close {ψ ψ' ψr : Fin N → ℂ} {ρ ρ' : ℝ} (h : vn (fun i => ψ i - ψr i) ≤ ρ)
    (h' : vn (fun i => ψ' i - ψr i) ≤ ρ') : vn (fun i => ψ' i - ψ i) ≤ ρ + ρ' := by
  have e : (fun i => ψ' i - ψ i) = (fun i => ψ' i - ψr i) - (fun i => ψ i - ψr i) := by
    funext i; simp
  unfold vn at *
  have e2 : (WithLp.toLp 2 (fun i => ψ' i - ψ i) : EuclideanSpace ℂ (Fin N)) =
      WithLp.toLp 2 (fun i => ψ' i - ψr i) - WithLp.toLp 2 (fun i => ψ i - ψr i) := by
    ext i; simp
  rw [e2]
  exact (norm_sub_le _ _).trans (add_le_add h' h) |>.trans_eq (add_comm _ _)

end Lift

section Step3

variable {d : ℕ} {L : ℕ} [NeZero L] {N : ℕ}

/-- **Theorem 4.2, Steps 1 and 3 at the cube level (undecoupled).**  Let `ψ, ψ'` be complex block
fields in `Δ^c_q(□; 1, r)` (`DeltaC`: the H7 membership of Definition II.3.5 (a)), both within `ρ`,
`ρ'` of a common reference field, with `ρ + ρ' ≤ C_δ r` and `ψ' = ψ` on the blocks off `W`.  Then
the cube action `A_Q` at the two backgrounds `bg(G_q(□); lift ψ)`, `bg(G_q(□); lift ψ')` differs
by `|β (A_Q(φ') - A_Q(φ))| ≤ C_F β |Q| r² e^{-γ_w Dist}` when `Dist` bounds the distance from
`R ∩ Ω₁` to the shadow of `W` (`R = □^{∼1}` carries the regularity inequalities).  The domain
radii `(δ, ε)` of the two data are the typing data of the BG domain `𝒟` (they exist by
`deltaC_inUnionDomainC`; their numerical smallness is the premise of Lemma 4.1). -/
theorem h7_cube_step3 (hd : 3 ≤ d) (hL : 3 ≤ L) {Cδ : ℝ} (hCδ : 0 ≤ Cδ) :
    ∃ CF δw : ℝ, 0 < CF ∧ 0 < δw ∧
      ∀ {M1 N₁ q c n : ℕ} [NeZero M1] [NeZero N₁] {a : ℕ → ℝ} {μ : ℝ} {h : Fin N → ℂ},
        BgHyp d L q (minSep L M1) a μ →
        2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1) →
        ∀ (y0 : Torus d n) {r : ℝ}
        {ψ ψ' : Torus d (M1 * N₁ * L ^ (q - q)) → Fin N → ℂ},
        ψ ∈ DeltaC (q := q) (M1 := M1) (N₁ := N₁) (L := L) a μ r h c n y0 →
        ψ' ∈ DeltaC (q := q) (M1 := M1) (N₁ := N₁) (L := L) a μ r h c n y0 →
        ∀ {δ ε δ' ε' : ℝ},
        0 < δ → δ ≤ ε → ε ≤ bgC0 d L N → δ ≤ bgC1 d L N →
        μ * ((L : ℝ) ^ q) ^ 2 * ε ^ 2 ≤ δ ^ 2 →
        InDomainC (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) μ δ ε
          (liftSingle (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) ψ h) →
        0 < δ' → δ' ≤ ε' → ε' ≤ bgC0 d L N → δ' ≤ bgC1 d L N →
        μ * ((L : ℝ) ^ q) ^ 2 * ε' ^ 2 ≤ δ' ^ 2 →
        InDomainC (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) μ δ' ε'
          (liftSingle (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) ψ' h) →
        bgK1 d L N * δ ≤ deltaStar d L N → bgK1 d L N * δ ≤ δw →
        ∀ (ψr : Torus d (M1 * N₁ * L ^ (q - q)) → Fin N → ℂ) {ρ ρ' : ℝ}, 0 ≤ ρ → 0 ≤ ρ' →
        (∀ b, vn (fun i => ψ b i - ψr b i) ≤ ρ) → (∀ b, vn (fun i => ψ' b i - ψr b i) ≤ ρ') →
        ρ + ρ' ≤ deltaStar d L N → ρ + ρ' ≤ δw → ρ + ρ' ≤ Cδ * r →
        ∀ (W : Finset (Torus d (M1 * N₁ * L ^ q))),
        (∀ x ∈ dataSites (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0), x ∉ W →
          ψ' (jBlock d L (M1 * N₁) q q x) = ψ (jBlock d L (M1 * N₁) q q x)) →
        ∀ (Q : Finset (Torus d (M1 * N₁ * L ^ q))) {Dist : ℝ}, 0 ≤ r → 0 ≤ Dist →
        Q ⊆ cubeNbhd M1 N₁ L q c n 1 y0 →
        (∀ x ∈ Q, ∀ μ' : Fin d, x + Pi.single μ' 1 ∈ cubeNbhd M1 N₁ L q c n 1 y0) →
        (∀ x ∈ Q, x ∈ (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0).Ω 1 →
          ∀ y ∈ (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0).blk
            ((genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0).layerIndex x) x,
            y ∈ cubeNbhd M1 N₁ L q c n 1 y0) →
        (∀ y ∈ cubeNbhd M1 N₁ L q c n 1 y0,
          y ∈ (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0).Ω 1 →
          ∀ w ∈ shadowN (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) W,
            ENNReal.ofReal Dist ≤
              (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0).pathDist y w) →
        ∀ β : ℝ, 0 ≤ β →
        ‖(β : ℂ) * (cubeActionC (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) a μ Q
              (liftSingle (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) ψ h)
              (bgFieldC (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) a μ
                (bgC0 d L N)
                (liftSingle (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) ψ' h)) -
            cubeActionC (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) a μ Q
              (liftSingle (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) ψ h)
              (bgFieldC (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) a μ
                (bgC0 d L N)
                (liftSingle (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) ψ h)))‖ ≤
          CF * β * Q.card * r ^ 2 * Real.exp (-(gammaW d * Dist)) := by
  obtain ⟨CF, δw, hCF, hδw, hstep⟩ := cubeDiff_step3_quadratic_gen (N := N) hd hL hCδ
  refine ⟨CF, δw, hCF, hδw, ?_⟩
  intro M1 N₁ q c n _ _ a μ h H hsep y0 r ψ ψ' hψ hψ' δ ε δ' ε' hδ0 hδε hε hδ1 hνε hD hδ0' hδε' hε'
    hδ1' hνε' hDu hK1 hKw ψr ρ ρ' hρ hρ' hcl hcl' hs1 hs2 hs3 W hW Q Dist hr hDist hQR hQR1 hQblk
    hdist β hβ
  have hδ₁ : ∀ b, vn (fun i => ψ' b i - ψ b i) ≤ ρ + ρ' :=
    fun b => vn_sub_le_of_close (hcl b) (hcl' b)
  exact hstep (N₁ := M1 * N₁) (m₁ := 0) (by simp) H hsep hδ0 hδε hε hδ1 hνε hD hδ0' hδε' hε' hδ1'
    hνε' hDu hK1 hKw (δΨ := liftDiff _ ψ ψ') W
    (fun y hy => liftDiff_eq_zero _ ψ ψ' W hW y hy |> fun e => by simp [e])
    (fun x i => liftSingle_sub _ ψ ψ' h x i) (fun x i => liftSingle_h_eq _ ψ ψ' h x i)
    (add_nonneg hρ hρ') hs1 hs2 (fun x _ => vn_liftDiff_le _ ψ ψ' (add_nonneg hρ hρ') hδ₁ x)
    Q _ hr hDist hs3 hQR hQR1 hQblk (deltaC_regIneq a μ r h y0 hψ) hdist β hβ

end Step3

end Balaban.Fluctuation
