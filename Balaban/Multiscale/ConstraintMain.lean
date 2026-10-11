/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.ConstraintPerturb
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# G-1(d) and G-2(v) for the hard-spin constrained operator: statements on the unit lattice

Summary of the files `Balaban/Multiscale/Constrain*.lean` (GREEN.md (1.8′), §4.5a, §4.5b):

* definition: `Balaban.Multiscale.constrainedOp` (`Π = Ĝ φ₀ [φ₀ · Ĝ φ₀]⁻¹ φ₀ · Ĝ`, bilinear dot
  product), `Balaban.Multiscale.constraintForm` (`φ₀ · G φ₀`);
* G-2(v): `Balaban.Multiscale.constraintForm_isUnit`, `Balaban.Multiscale.constraintForm_inv`
  (`[φ₀ · G φ₀]⁻¹ = M⁻¹ H`), `Balaban.Multiscale.constrained_weighted_bounds` (`L²` and gradient
  bounds in the weighted norm `w = e^{ε r}`), `Balaban.Multiscale.constrained_G2v` (block-to-block
  decay in the path metric), `Balaban.Multiscale.agmonSource_commK_le` (the constraint sandwich
  `‖ℓ w K(φ₀) s‖² ≤ c δ² (‖w ∂ s‖² + ‖ℓ⁻¹ w s‖²)`);
* G-1(d)(1): `Balaban.Multiscale.constrainedOp_dirichlet_posSemidef`,
  `Balaban.Multiscale.unitSandwich_nonneg`;
* G-1(d)(2): `Balaban.Multiscale.constrained_complex_lower`,
  `Balaban.Multiscale.unitSandwich_re_lower`;
* G-1(d)(3): `Balaban.Multiscale.unitKernel_bound`.
-/

@[expose] public section

namespace Balaban.Multiscale

open Matrix Finset
open scoped ComplexOrder

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Imag

theorem vn_I_mul (v : Fin N → ℂ) : vn (fun j => Complex.I * v j) = vn v := by
  rw [vn_eq_sqrt, vn_eq_sqrt]
  simp

variable {G : GeneratingSet d L N₀ k ϱ}

theorem IsSmoothField.I_mul {ε : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (h : IsSmoothField G ε φ) :
    IsSmoothField G ε (fun x j => Complex.I * φ x j) where
  grad x hx μ := by
    obtain ⟨h1, h2⟩ := h.grad x hx μ
    refine ⟨?_, ?_⟩
    · have : ((fun x j => Complex.I * φ x j) (x + Pi.single μ 1) -
          (fun x j => Complex.I * φ x j) x) = fun j => Complex.I * (φ (x + Pi.single μ 1) - φ x) j := by
        funext j; simp only [Pi.sub_apply]; ring
      rw [this, vn_I_mul]; exact h1
    · have : ((fun x j => Complex.I * φ x j) (x - Pi.single μ 1) -
          (fun x j => Complex.I * φ x j) x) = fun j => Complex.I * (φ (x - Pi.single μ 1) - φ x) j := by
        funext j; simp only [Pi.sub_apply]; ring
      rw [this, vn_I_mul]; exact h2
  lap x hx := by
    have := h.lap x hx
    have e : (fun i => ∑ μ : Fin d, ((fun x j => Complex.I * φ x j) (x + Pi.single μ 1) i +
        (fun x j => Complex.I * φ x j) (x - Pi.single μ 1) i -
        2 * (fun x j => Complex.I * φ x j) x i)) =
        fun i => Complex.I * ∑ μ : Fin d, (φ (x + Pi.single μ 1) i + φ (x - Pi.single μ 1) i -
          2 * φ x i) := by
      funext i; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun μ _ => by ring
    rw [e, vn_I_mul]; exact this

end Imag

section Complex

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **G-1(d)(2), fine form.**  Let `φ₀ = φ_r + i φ_i`, `α = α_r + i α_i` with `(α_r, φ_r)` real data
and both `(α_r, φ_r)` and `(α, φ₀)` obeying the hypotheses of G-2(v) (smallness `δ ≤ δ_*(d)`,
`Standing`), and `(α_i, φ_i)` of size `ε` (`ℓ² |α_i| ≤ ε`, `ℓ |∂ φ_i| ≤ ε`, `ℓ² |Δ φ_i| ≤ ε`,
`|φ_i| ≤ ε`).  Then for every vector field `f` on `Ω₁`

`Re ⟨f, Π f⟩ ≥ - C(d)^{1/2} ε ‖ℓ f‖²`,

where `Π` is the constrained operator of `(α, φ₀)`, `C(d) = pertConst d`.  (Reality of `φ_i`, `α_i`
is not used.) -/
theorem constrained_complex_lower {αr αi : G.Ω 1 → ℂ} {φr φi : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {δ ε : ℝ} (St_r : Standing G a ν αr δ φr)
    (St : Standing G a ν (fun x => αr x + Complex.I * αi x) δ
      (fun x j => φr x j + Complex.I * φi x j))
    (hαr : ∀ x, star (αr x) = αr x) (hφr : ∀ x i, star (φr x i) = φr x i)
    (hε : 0 ≤ ε) (hαi : ∀ x : G.Ω 1, ‖αi x‖ ≤ ε / G.spacing x ^ 2)
    (hsm : IsSmoothField G ε φi) (hb : ∀ x ∈ G.Ω 1, vn (φi x) ≤ ε)
    (f : G.Ω 1 × Fin N → ℂ) :
    -(Real.sqrt (pertConst d) * ε * vecSrc G 0 (fun _ => 0) f) ≤
      (star f ⬝ᵥ (constrainedOp
        (dirichletOperator G a ν (fun x => αr x + Complex.I * αi x))⁻¹
        (restrictField G (fun x j => φr x j + Complex.I * φi x j)) *ᵥ f)).re := by
  have hP : PertData G a ν (fun x => αr x + Complex.I * αi x) αr δ δ ε
      (fun x j => φr x j + Complex.I * φi x j) φr :=
    { st₁ := St
      st₂ := St_r
      close :=
        { nonneg := hε
          alpha := fun x => by
            have : αr x - (αr x + Complex.I * αi x) = -(Complex.I * αi x) := by ring
            rw [this, norm_neg, norm_mul, Complex.norm_I, one_mul]
            exact hαi x
          smooth := by
            have e : (fun x j => (φr x j + Complex.I * φi x j) - φr x j) =
                fun x j => Complex.I * φi x j := by funext x j; ring
            rw [e]; exact hsm.I_mul
          bound := fun x hx => by
            have e : (fun j => (φr x j + Complex.I * φi x j) - φr x j) =
                fun j => Complex.I * φi x j := by funext j; ring
            rw [e, vn_I_mul]; exact hb x hx } }
  exact constrained_re_lower hP hαr hφr f

end Complex

section Unit

variable (G : GeneratingSet d L N₀ k ϱ)

/-- `Q_k^* ψ`: the pullback of a unit-lattice field `ψ` (a field on the `k`-blocks, values in `ℂ^N`)
to the fine lattice. -/
def unitPullback (ψ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) : G.Ω 1 × Fin N → ℂ :=
  fun p => ψ (jBlock d L N₀ k k p.1) p.2

/-- `‖ψ‖²` on the unit lattice (weight `1` per unit block). -/
noncomputable def unitNormSq (ψ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) : ℝ :=
  ∑ y, ∑ i, ‖ψ y i‖ ^ 2

/-- `ψ` is supported in `Λ_k` (the unit blocks inside `Ω_k`). -/
def IsUnitSupported (ψ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) : Prop :=
  ∀ y, (∀ x ∈ G.Ω k, jBlock d L N₀ k k x ≠ y) → ∀ i, ψ y i = 0

/-- **The unit-lattice sandwich** `⟨ψ, Q_k Π Q_k^* ψ⟩ = L^{-(k d + 2 k)} ⟨Q_k^* ψ, Π Q_k^* ψ⟩`
(see `Balaban/Multiscale/ConstraintKernel.lean` for the dictionary). -/
noncomputable def unitSandwich (Pm : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (ψ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) : ℂ :=
  (((L : ℝ) ^ (k * d + 2 * k))⁻¹ : ℝ) *
    (star (unitPullback G ψ) ⬝ᵥ (Pm *ᵥ unitPullback G ψ))

/-- **G-1(d)(1) on the unit lattice**: `Q_k Π Q_k^* ⪰ 0`. -/
theorem unitSandwich_nonneg {Pm : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ} (hP : Pm.PosSemidef)
    (ψ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) : 0 ≤ unitSandwich G Pm ψ := by
  unfold unitSandwich
  have h := hP.dotProduct_mulVec_nonneg (unitPullback G ψ)
  have hL : (0 : ℝ) ≤ (((L : ℝ) ^ (k * d + 2 * k))⁻¹ : ℝ) := by positivity
  have : (0 : ℂ) ≤ ((((L : ℝ) ^ (k * d + 2 * k))⁻¹ : ℝ) : ℂ) := by
    rw [Complex.nonneg_iff]
    exact ⟨by rw [Complex.ofReal_re]; exact hL, (Complex.ofReal_im _).symm⟩
  exact mul_nonneg this h

theorem mem_Ωk_of_ne_zero (hk : 1 ≤ k) {ψ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ}
    (hψ : IsUnitSupported G ψ) {x : Torus d (N₀ * L ^ k)} {i : Fin N}
    (hx : ψ (jBlock d L N₀ k k x) i ≠ 0) : x ∈ G.Ω k := by
  by_contra hxn
  refine hx (hψ _ (fun x' hx' h => hxn ?_) i)
  exact (G.blockUnion k hk le_rfl x x' h.symm).2 hx'

theorem spacing_of_mem_Ωk (hk : 1 ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω k) :
    G.spacing x = (L : ℝ) ^ k :=
  G.spacing_eq hk le_rfl (G.mem_layer.2 ⟨hx, by rw [G.top]; simp⟩)

/-- The weighted norm of a pullback: `‖ℓ Q_k^* ψ‖² = L^{k d + 2 k} ‖ψ‖²`. -/
theorem vecSrc_unitPullback (hk : 1 ≤ k) {ψ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ}
    (hψ : IsUnitSupported G ψ) :
    vecSrc G 0 (fun _ => 0) (unitPullback G ψ) = (L : ℝ) ^ (k * d + 2 * k) * unitNormSq ψ := by
  set F : Torus d (N₀ * L ^ (k - k)) → ℝ := fun y => ∑ i, ‖ψ y i‖ ^ 2 with hF
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  -- the support of `F ∘ jBlock`
  have hsupp : ∀ x : Torus d (N₀ * L ^ k), x ∉ G.Ω k → F (jBlock d L N₀ k k x) = 0 := by
    intro x hx
    refine Finset.sum_eq_zero fun i _ => ?_
    by_contra hne
    have : ψ (jBlock d L N₀ k k x) i ≠ 0 := fun h => hne (by simp [h])
    exact hx (mem_Ωk_of_ne_zero G hk hψ this)
  rw [vecSrc0_eq]
  have h1 : ∀ x : G.Ω 1, ∑ i, G.spacing x ^ 2 * ‖unitPullback G ψ (x, i)‖ ^ 2 =
      ((L : ℝ) ^ k) ^ 2 * F (jBlock d L N₀ k k x) := by
    intro x
    by_cases hx : (x : Torus d (N₀ * L ^ k)) ∈ G.Ω k
    · rw [spacing_of_mem_Ωk G hk hx, hF, Finset.mul_sum]
      rfl
    · rw [hsupp x hx, mul_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      have : ψ (jBlock d L N₀ k k x) i = 0 := by
        by_contra hne
        exact hx (mem_Ωk_of_ne_zero G hk hψ hne)
      simp [unitPullback, this]
  rw [Finset.sum_congr rfl fun x _ => h1 x, ← Finset.mul_sum]
  have hsub : G.Ω k ⊆ G.Ω 1 := G.Ω_antitone le_rfl hk (by omega)
  have h2 : ∑ x : G.Ω 1, F (jBlock d L N₀ k k x) = ∑ x ∈ G.Ω k, F (jBlock d L N₀ k k x) := by
    rw [Finset.sum_coe_sort (G.Ω 1) (fun x => F (jBlock d L N₀ k k x))]
    exact (Finset.sum_subset hsub (fun x _ hx => hsupp x hx)).symm
  have h3 : ∀ y : Torus d (N₀ * L ^ (k - k)),
      ∑ x ∈ (G.Ω k).filter (fun x => jBlock d L N₀ k k x = y), F (jBlock d L N₀ k k x) =
        ((L : ℝ) ^ k) ^ d * F y := by
    intro y
    by_cases hy : F y = 0
    · rw [hy, mul_zero]
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [(Finset.mem_filter.1 hx).2, hy]
    · have hex : ∃ x₀ ∈ G.Ω k, jBlock d L N₀ k k x₀ = y := by
        by_contra hne
        push Not at hne
        exact hy (Finset.sum_eq_zero fun i _ => by simp [hψ y hne i])
      obtain ⟨x₀, hx₀, rfl⟩ := hex
      have hfil : (G.Ω k).filter (fun x => jBlock d L N₀ k k x = jBlock d L N₀ k k x₀) =
          G.blk k x₀ := by
        ext x
        simp only [Finset.mem_filter, GeneratingSet.mem_blk]
        exact ⟨fun h => h.2, fun h => ⟨(G.blockUnion k hk le_rfl x x₀ h).2 hx₀, h⟩⟩
      rw [hfil, Finset.sum_congr rfl fun x hx => by rw [G.mem_blk.1 hx], Finset.sum_const,
        nsmul_eq_mul, card_blk G k le_rfl]
  have h4 : ∑ x ∈ G.Ω k, F (jBlock d L N₀ k k x) = ((L : ℝ) ^ k) ^ d * ∑ y, F y := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := jBlock d L N₀ k k) (t := Finset.univ)
      (fun x _ => Finset.mem_univ _)]
    rw [Finset.sum_congr rfl fun y _ => h3 y, ← Finset.mul_sum]
  rw [h2, h4]
  unfold unitNormSq
  have : (L : ℝ) ^ (k * d + 2 * k) = ((L : ℝ) ^ k) ^ 2 * ((L : ℝ) ^ k) ^ d := by
    rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  rw [this]
  simp only [hF]
  ring

variable {G}

/-- **G-1(d)(2) on the unit lattice**: for `ψ` supported in `Λ_k` and complex data `ε`-close to real
data, `Re ⟨ψ, Q_k Π Q_k^* ψ⟩ ≥ - C(d)^{1/2} ε ‖ψ‖²`. -/
theorem unitSandwich_re_lower {a : ℕ → ℝ} {ν : ℝ} {αr αi : G.Ω 1 → ℂ}
    {φr φi : Torus d (N₀ * L ^ k) → Fin N → ℂ} {δ ε : ℝ} (hk : 1 ≤ k)
    (St_r : Standing G a ν αr δ φr)
    (St : Standing G a ν (fun x => αr x + Complex.I * αi x) δ
      (fun x j => φr x j + Complex.I * φi x j))
    (hαr : ∀ x, star (αr x) = αr x) (hφr : ∀ x i, star (φr x i) = φr x i)
    (hε : 0 ≤ ε) (hαi : ∀ x : G.Ω 1, ‖αi x‖ ≤ ε / G.spacing x ^ 2)
    (hsm : IsSmoothField G ε φi) (hb : ∀ x ∈ G.Ω 1, vn (φi x) ≤ ε)
    {ψ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ} (hψ : IsUnitSupported G ψ) :
    -(Real.sqrt (pertConst d) * ε * unitNormSq ψ) ≤
      (unitSandwich G (constrainedOp
        (dirichletOperator G a ν (fun x => αr x + Complex.I * αi x))⁻¹
        (restrictField G (fun x j => φr x j + Complex.I * φi x j))) ψ).re := by
  have h := constrained_complex_lower St_r St hαr hφr hε hαi hsm hb (unitPullback G ψ)
  rw [vecSrc_unitPullback G hk hψ] at h
  have hL : (0 : ℝ) < (L : ℝ) ^ (k * d + 2 * k) := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  unfold unitSandwich
  rw [Complex.re_ofReal_mul]
  have h2 := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hL.le)
  have e : ((L : ℝ) ^ (k * d + 2 * k))⁻¹ *
      -(Real.sqrt (pertConst d) * ε * ((L : ℝ) ^ (k * d + 2 * k) * unitNormSq ψ)) =
      -(Real.sqrt (pertConst d) * ε * unitNormSq ψ) := by
    field_simp
  linarith

/-- **G-1(d)(1), unit lattice, for the Dirichlet Green's function**: real data give
`Q_k Π Q_k^* ⪰ 0`, hence `Δ^{(k)} ≥ Δ^{(k)}_unc` (GREEN.md §4.5b (1)). -/
theorem unitSandwich_dirichlet_nonneg {a : ℕ → ℝ} {ν : ℝ} (hd : 0 < d) (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    (hreal : ∀ x, star (α x) = α x) {φ : G.Ω 1 → Fin N → ℂ}
    (hφ : ∀ x i, star (φ x i) = φ x i) (ψ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) :
    0 ≤ unitSandwich G (constrainedOp (dirichletOperator G a ν α)⁻¹ φ) ψ :=
  unitSandwich_nonneg G (constrainedOp_dirichlet_posSemidef G hd hν ha α hα hreal hφ) ψ

end Unit

end Balaban.Multiscale
