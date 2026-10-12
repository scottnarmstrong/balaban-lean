/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormMain

/-!
# Isotropy of the second moment tensor

From the scalar second moment (H.5)(4) and the Euclid invariance (H.3) under the reflections and
the coordinate exchanges, `Σ_X Σ_{x,x'} B_X(x,x') (x - x')_μ (x - x')_ν = 0` for all `μ, ν`.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

theorem latFlip_invol (μ : Fin d) (x : Site d) : latFlip μ (latFlip μ x) = x := by
  ext ν
  by_cases h : ν = μ <;> simp [latFlip, h]

theorem latSwap_invol (μ ν : Fin d) (x : Site d) : latSwap μ ν (latSwap μ ν x) = x := by
  ext ρ
  simp [latSwap]

theorem IsLatGen.invol {r : Site d → Site d} (hr : IsLatGen r) (x : Site d) : r (r x) = x := by
  rcases hr with ⟨μ, rfl⟩ | ⟨μ, ν, rfl⟩
  · exact latFlip_invol μ x
  · exact latSwap_invol μ ν x

theorem IsLatGen.sub {r : Site d → Site d} (hr : IsLatGen r) (x y : Site d) :
    r (x - y) = r x - r y := by
  rcases hr with ⟨μ, rfl⟩ | ⟨μ, ν, rfl⟩
  · ext ρ
    by_cases h : ρ = μ <;> simp [latFlip, h]; ring
  · ext ρ
    simp [latSwap]

theorem IsLatGen.add {r : Site d → Site d} (hr : IsLatGen r) (x y : Site d) :
    r (x + y) = r x + r y := by
  rcases hr with ⟨μ, rfl⟩ | ⟨μ, ν, rfl⟩
  · ext ρ
    by_cases h : ρ = μ <;> simp [latFlip, h]; ring
  · ext ρ
    simp [latSwap]

theorem IsLatGen.zero {r : Site d → Site d} (hr : IsLatGen r) : r 0 = 0 := by
  rcases hr with ⟨μ, rfl⟩ | ⟨μ, ν, rfl⟩
  · ext ρ
    by_cases h : ρ = μ <;> simp [latFlip, h]
  · ext ρ
    simp [latSwap]

/-- The involution `r` as a permutation. -/
def IsLatGen.perm {r : Site d → Site d} (hr : IsLatGen r) : Equiv.Perm (Site d) :=
  Function.Involutive.toPerm r (fun x => hr.invol x)

theorem IsLatGen.perm_apply {r : Site d → Site d} (hr : IsLatGen r) (x : Site d) :
    hr.perm x = r x := rfl

/-- The bijection `X ≃ r(X)`. -/
def IsLatGen.imageEquiv {r : Site d → Site d} (hr : IsLatGen r) (X : Finset (Site d)) :
    ↥X ≃ ↥(X.image r) :=
  Equiv.subtypeEquiv hr.perm (fun a => by
    constructor
    · intro h; exact Finset.mem_image_of_mem r h
    · intro h
      obtain ⟨y, hy, hya⟩ := Finset.mem_image.mp h
      have h2 : r (r y) = r (r a) := by
        rw [hya]; rfl
      rw [hr.invol, hr.invol] at h2
      rw [← h2]; exact hy)

theorem IsLatGen.imageEquiv_val {r : Site d → Site d} (hr : IsLatGen r) (X : Finset (Site d))
    (x : ↥X) : (hr.imageEquiv X x).1 = r x.1 := rfl

/-- The second derivative along the line `t ↦ P₀ + t · pack X dir 0`. -/
noncomputable def lineQ (T : TermFamily d N) (i₀ : Fin N) (ν : ℝ) (X : Finset (Site d))
    (dir : Site d → Spin N) : ℂ :=
  iteratedDeriv 2 (fun t : ℂ => T.term X (refPt i₀ ν X + t • pack X dir 0)) 0

theorem refPt_add_smul_pack (i₀ : Fin N) (ν : ℝ) (X : Finset (Site d)) (φ : Site d → Spin N)
    (t : ℂ) : refPt i₀ ν X + t • pack X φ 0 =
      pack X (fun y => (Pi.single i₀ 1 : Spin N) + t • φ y) ((ν : ℂ) • Pi.single i₀ 1) := by
  ext (⟨x, j⟩ | j) <;> simp [refPt, pack]

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)}

theorem lineQ_cov (hP : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) {r : Site d → Site d}
    (hr : IsLatGen r) {X : Finset (Site d)} (hX : X ∈ T.polys) (dir : Site d → Spin N) :
    lineQ T i₀ ν (X.image r) (fun y => dir (r y)) = lineQ T i₀ ν X dir := by
  unfold lineQ
  congr 1
  funext t
  rw [refPt_add_smul_pack, refPt_add_smul_pack]
  exact hP.sym_inv r hr X hX (fun x => (Pi.single i₀ 1 : Spin N) + t • dir x) ((ν : ℂ) • Pi.single i₀ 1)

/-- The unit field at the site `z` in the direction `i`. -/
def dirD (z : Site d) (i : Fin N) : Site d → Spin N := fun y => if y = z then Pi.single i 1 else 0

theorem dirD_comp {r : Site d → Site d} (hr : IsLatGen r) (z : Site d) (i : Fin N) :
    (fun y => dirD z i (r y)) = dirD (r z) i := by
  funext y
  unfold dirD
  by_cases h : y = r z
  · subst h; simp [hr.invol]
  · have : r y ≠ z := fun h' => h (by rw [← h', hr.invol])
    simp [h, this]

theorem dirD_add_comp {r : Site d → Site d} (hr : IsLatGen r) (z z' : Site d) (i : Fin N) :
    (fun y => (dirD z i + dirD z' i) (r y)) = dirD (r z) i + dirD (r z') i := by
  funext y
  have h1 := congrFun (dirD_comp hr z i) y
  have h2 := congrFun (dirD_comp hr z' i) y
  simp only [Pi.add_apply] at h1 h2 ⊢
  rw [h1, h2]

theorem TermOK.tensB_eq_lineQ {X : Finset (Site d)} (hf : TermOK i₀ ν ρ X (T.term X))
    (x x' : ↥X) :
    tensB i₀ i₁ ν X (T.term X) x x' =
      (1 / 2 : ℂ) * (lineQ T i₀ ν X (dirD x.1 i₁ + dirD x'.1 i₁) -
        lineQ T i₀ ν X (dirD x.1 i₁) - lineQ T i₀ ν X (dirD x'.1 i₁)) := by
  have hρ := hf.rho_pos
  have hana := hf.analytic_ball
  have hsym := D2_symm (hana (refPt i₀ ν X) (mem_ball_self hρ))
  have hQ : ∀ dir : Site d → Spin N, lineQ T i₀ ν X dir =
      D2 (T.term X) (refPt i₀ ν X) (pack X dir 0) (pack X dir 0) := fun dir => by
    unfold lineQ; exact iteratedDeriv_two_line hρ hana
  have hv : (Pi.single (Sum.inl (x, i₁)) (1 : ℂ) : Cfg d N X) = pack X (dirD x.1 i₁) 0 :=
    single_inl_eq_pack X x i₁
  have hw : (Pi.single (Sum.inl (x', i₁)) (1 : ℂ) : Cfg d N X) = pack X (dirD x'.1 i₁) 0 :=
    single_inl_eq_pack X x' i₁
  have hsum : pack X (dirD x.1 i₁ + dirD x'.1 i₁) 0 = pack X (dirD x.1 i₁) 0 +
      pack X (dirD x'.1 i₁) 0 := by
    have := pack_add X (dirD x.1 i₁) (dirD x'.1 i₁) 0 0
    rw [add_zero] at this
    exact this
  rw [hQ, hQ, hQ, hsum, ← hv, ← hw]
  have e : D2 (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inl (x, i₁)) 1 + Pi.single (Sum.inl (x', i₁)) 1)
      (Pi.single (Sum.inl (x, i₁)) 1 + Pi.single (Sum.inl (x', i₁)) 1) =
      D2 (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inl (x, i₁)) 1) (Pi.single (Sum.inl (x, i₁)) 1)
      + 2 * D2 (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inl (x, i₁)) 1) (Pi.single (Sum.inl (x', i₁)) 1)
      + D2 (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inl (x', i₁)) 1) (Pi.single (Sum.inl (x', i₁)) 1) := by
    simp only [D2_add_left, D2_add_right]
    rw [hsym (Pi.single (Sum.inl (x', i₁)) 1) (Pi.single (Sum.inl (x, i₁)) 1)]; ring
  rw [e]
  unfold tensB
  ring

theorem Premises.termOK (hP : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ)
    {X : Finset (Site d)} (hX : X ∈ T.polys) : TermOK i₀ ν ρ X (T.term X) :=
  ⟨hρ, hP.analytic X hX, fun c' hc' R' hR' hbd hmem => hP.rot_inv X hX c' hc' R' hR' hbd hmem⟩

theorem tensB_cov (hP : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ) {r : Site d → Site d}
    (hr : IsLatGen r) {X : Finset (Site d)} (hX : X ∈ T.polys) (x x' : ↥X) :
    tensB i₀ i₁ ν (X.image r) (T.term (X.image r)) (hr.imageEquiv X x) (hr.imageEquiv X x') =
      tensB i₀ i₁ ν X (T.term X) x x' := by
  have hX' : X.image r ∈ T.polys := hP.sym_mem r hr X hX
  rw [(hP.termOK hρ hX').tensB_eq_lineQ, (hP.termOK hρ hX).tensB_eq_lineQ]
  simp only [IsLatGen.imageEquiv_val]
  have c1 : ∀ z : Site d, lineQ T i₀ ν (X.image r) (dirD (r z) i₁) =
      lineQ T i₀ ν X (dirD z i₁) := fun z => by
    have := lineQ_cov hP hr hX (dirD z i₁)
    rwa [dirD_comp hr] at this
  have c3 : lineQ T i₀ ν (X.image r) (dirD (r x.1) i₁ + dirD (r x'.1) i₁) =
      lineQ T i₀ ν X (dirD x.1 i₁ + dirD x'.1 i₁) := by
    have := lineQ_cov hP hr hX (dirD x.1 i₁ + dirD x'.1 i₁)
    rwa [dirD_add_comp hr] at this
  rw [c3, c1, c1]

/-- The second moment tensor of a polymer: `Σ_{x,x'} B_X(x,x') (x - x')_μ (x - x')_{ν'}`. -/
noncomputable def Sx (T : TermFamily d N) (i₀ i₁ : Fin N) (ν : ℝ) (X : Finset (Site d))
    (μ ν' : Fin d) : ℂ :=
  ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
    ((((x.1 - x'.1) μ : ℤ) : ℂ) * (((x.1 - x'.1) ν' : ℤ) : ℂ))

theorem Sx_cov (hP : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ) {r : Site d → Site d}
    (hr : IsLatGen r) {X : Finset (Site d)} (hX : X ∈ T.polys) (μ ν' : Fin d) :
    Sx T i₀ i₁ ν (X.image r) μ ν' =
      ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
        ((((r (x.1 - x'.1)) μ : ℤ) : ℂ) * (((r (x.1 - x'.1)) ν' : ℤ) : ℂ)) := by
  unfold Sx
  set e := hr.imageEquiv X with he
  have h : ∀ F : ↥(X.image r) → ↥(X.image r) → ℂ, ∑ y : ↥(X.image r), ∑ y' : ↥(X.image r), F y y' =
      ∑ x : ↥X, ∑ x' : ↥X, F (e x) (e x') := by
    intro F
    rw [← e.sum_comp (fun y => ∑ y' : ↥(X.image r), F y y')]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← e.sum_comp (fun y' => F (e x) y')]
  rw [h]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  rw [he, tensB_cov hP hρ hr hX x x']
  simp only [IsLatGen.imageEquiv_val, ← hr.sub]

theorem latFlip_apply (α : Fin d) (z : Site d) (μ : Fin d) :
    latFlip α z μ = if μ = α then -z μ else z μ := by
  by_cases h : μ = α <;> simp [latFlip, h]

theorem latSwap_apply (α β : Fin d) (z : Site d) (μ : Fin d) :
    latSwap α β z μ = z (Equiv.swap α β μ) := rfl

theorem Sx_flip (hP : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ) (α : Fin d)
    {X : Finset (Site d)} (hX : X ∈ T.polys) (μ ν' : Fin d) :
    Sx T i₀ i₁ ν (X.image (latFlip α)) μ ν' =
      (if μ = α then (-1 : ℂ) else 1) * (if ν' = α then (-1 : ℂ) else 1) * Sx T i₀ i₁ ν X μ ν' := by
  rw [Sx_cov hP hρ (Or.inl ⟨α, rfl⟩) hX]
  unfold Sx
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  have hs : ∀ (z : Site d) (ρ' : Fin d), (((latFlip α z) ρ' : ℤ) : ℂ) =
      (if ρ' = α then (-1 : ℂ) else 1) * ((z ρ' : ℤ) : ℂ) := by
    intro z ρ'
    rw [latFlip_apply]; split_ifs <;> simp
  rw [hs, hs]
  ring

theorem Sx_swap (hP : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ) (α β : Fin d)
    {X : Finset (Site d)} (hX : X ∈ T.polys) (μ ν' : Fin d) :
    Sx T i₀ i₁ ν (X.image (latSwap α β)) μ ν' =
      Sx T i₀ i₁ ν X (Equiv.swap α β μ) (Equiv.swap α β ν') := by
  rw [Sx_cov hP hρ (Or.inr ⟨α, β, rfl⟩) hX]
  unfold Sx
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  simp only [latSwap_apply]

/-- The permutation of the polymers induced by an involution of the lattice. -/
def IsLatGen.polysEquiv (hP : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) {r : Site d → Site d}
    (hr : IsLatGen r) : T.polys ≃ T.polys where
  toFun X := ⟨X.1.image r, hP.sym_mem r hr X.1 X.2⟩
  invFun X := ⟨X.1.image r, hP.sym_mem r hr X.1 X.2⟩
  left_inv X := by
    apply Subtype.ext
    simp only [Finset.image_image]
    have : r ∘ r = id := funext hr.invol
    rw [this, Finset.image_id]
  right_inv X := by
    apply Subtype.ext
    simp only [Finset.image_image]
    have : r ∘ r = id := funext hr.invol
    rw [this, Finset.image_id]

theorem tsum_image_eq (hP : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) {r : Site d → Site d}
    (hr : IsLatGen r) (g : Finset (Site d) → ℂ) :
    ∑' X : T.polys, g (X.1.image r) = ∑' X : T.polys, g X.1 :=
  Equiv.tsum_eq (hr.polysEquiv hP) (fun X => g X.1)

theorem norm_coord_le (z : Site d) (μ : Fin d) : ‖(((z μ : ℤ)) : ℂ)‖ ≤ (l1 z : ℝ) := by
  rw [Complex.norm_intCast]
  have : (z μ).natAbs ≤ l1 z := by
    unfold l1
    exact Finset.single_le_sum (f := fun ν => (z ν).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ μ)
  calc |((z μ : ℤ) : ℝ)| = ((z μ).natAbs : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast this

theorem Sx_le (hP : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ) (hE0 : 0 ≤ E₀) (hA : 0 ≤ A)
    {X : Finset (Site d)} (hX : X ∈ T.polys) (μ ν' : Fin d) :
    ‖Sx T i₀ i₁ ν X μ ν'‖ ≤ (X.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X)) / ρ ^ 2) *
      (2 * (A * (1 + T.dist X))) ^ 2 := by
  have hok := hP.termOK hρ hX
  have hM : ∀ y ∈ ball (refPt i₀ ν X) ρ, ‖T.term X y‖ ≤ E₀ * Real.exp (-κ * T.dist X) :=
    fun y hy => hP.bdd_tube X hX y (ball_subset_tube i₀ ν ρ X hy)
  have hd0 : 0 ≤ T.dist X := hP.dist_nonneg X hX
  have hcard : (Fintype.card ↥X : ℝ) = X.card := by simp
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X) := by positivity
  unfold Sx
  have h1 : ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
      ((((x.1 - x'.1) μ : ℤ) : ℂ) * (((x.1 - x'.1) ν' : ℤ) : ℂ))‖ ≤
      (Fintype.card ↥X : ℝ) * ((Fintype.card ↥X : ℝ) *
        (4 * (E₀ * Real.exp (-κ * T.dist X)) / ρ ^ 2 * (2 * (A * (1 + T.dist X))) ^ 2)) := by
    refine norm_sum_le_card _ fun x => ?_
    refine norm_sum_le_card _ fun x' => ?_
    rw [norm_mul, norm_mul]
    have hl : (l1 (x.1 - x'.1) : ℝ) ≤ 2 * (A * (1 + T.dist X)) := by
      have := l1_sub_le x.1 x'.1
      have h3 : (l1 (x.1 - x'.1) : ℝ) ≤ l1 x.1 + l1 x'.1 := by exact_mod_cast this
      have h4 : (l1 x.1 : ℝ) ≤ A * (1 + T.dist X) := by
        rw [l1_cast]; exact hP.diam X hX x.1 x.2
      have h5 : (l1 x'.1 : ℝ) ≤ A * (1 + T.dist X) := by
        rw [l1_cast]; exact hP.diam X hX x'.1 x'.2
      linarith
    have hc1 := norm_coord_le (x.1 - x'.1) μ
    have hc2 := norm_coord_le (x.1 - x'.1) ν'
    have hl0 : (0 : ℝ) ≤ l1 (x.1 - x'.1) := Nat.cast_nonneg _
    have hz : ‖(((x.1 - x'.1) μ : ℤ) : ℂ)‖ * ‖(((x.1 - x'.1) ν' : ℤ) : ℂ)‖ ≤
        (2 * (A * (1 + T.dist X))) ^ 2 := by
      have h6 : (l1 (x.1 - x'.1) : ℝ) * l1 (x.1 - x'.1) ≤
          (2 * (A * (1 + T.dist X))) * (2 * (A * (1 + T.dist X))) :=
        mul_le_mul hl hl hl0 (by positivity)
      have h7 := mul_le_mul hc1 hc2 (norm_nonneg _) hl0
      nlinarith
    exact mul_le_mul (hok.norm_D2_basis_le hM _ _) hz (by positivity) (by positivity)
  rw [hcard] at h1
  refine h1.trans (le_of_eq ?_)
  ring

theorem Sx_summable (hP : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ) (hE0 : 0 ≤ E₀)
    (hA : 0 ≤ A) (μ ν' : Fin d) : Summable fun X : T.polys => Sx T i₀ i₁ ν X.1 μ ν' := by
  refine Summable.of_norm_bounded (hP.count_summable.mul_left (E₀ * (4 / ρ ^ 2 * (2 * A) ^ 2))) ?_
  intro X
  have h1 := Sx_le hP hρ hE0 hA X.2 μ ν'
  have h2 := wt_ge (κ := κ) X.1 (hP.dist_nonneg X.1 X.2)
    (Finset.card_pos.mpr ⟨0, hP.zero_mem X.1 X.2⟩) 2 2 le_rfl (by norm_num)
  refine h1.trans ?_
  have hd0 := hP.dist_nonneg X.1 X.2
  calc (X.1.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X.1)) / ρ ^ 2) *
        (2 * (A * (1 + T.dist X.1))) ^ 2
      = (4 / ρ ^ 2 * (2 * A) ^ 2) * E₀ * ((X.1.card : ℝ) ^ 2 * (1 + T.dist X.1) ^ 2 *
          Real.exp (-κ * T.dist X.1)) := by ring
    _ ≤ (4 / ρ ^ 2 * (2 * A) ^ 2) * E₀ * wt κ X.1 (T.dist X.1) := by
        have : 0 ≤ (4 / ρ ^ 2 * (2 * A) ^ 2) * E₀ := by positivity
        exact mul_le_mul_of_nonneg_left h2 this
    _ = _ := by ring

theorem moment_tensor (hP : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ) (hE0 : 0 ≤ E₀)
    (hA : 0 ≤ A) (μ ν' : Fin d) : ∑' X : T.polys, Sx T i₀ i₁ ν X.1 μ ν' = 0 := by
  by_cases hne : μ = ν'
  · subst hne
    -- the diagonal entries are all equal
    have hdiag : ∀ α β : Fin d, ∑' X : T.polys, Sx T i₀ i₁ ν X.1 α α =
        ∑' X : T.polys, Sx T i₀ i₁ ν X.1 β β := by
      intro α β
      have h := tsum_image_eq hP (r := latSwap α β) (Or.inr ⟨α, β, rfl⟩)
        (fun X => Sx T i₀ i₁ ν X α α)
      have h2 : ∀ X : T.polys, Sx T i₀ i₁ ν (X.1.image (latSwap α β)) α α =
          Sx T i₀ i₁ ν X.1 β β := fun X => by
        rw [Sx_swap hP hρ α β X.2]; simp
      simp only [h2] at h
      exact h.symm
    -- the trace vanishes
    have htrace : ∑ α : Fin d, ∑' X : T.polys, Sx T i₀ i₁ ν X.1 α α = 0 := by
      rw [← Summable.tsum_finsetSum (fun α _ => Sx_summable hP hρ hE0 hA α α)]
      have hm := hP.moment
      convert hm using 2
      ext X
      unfold Sx
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x' _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [Pi.sub_apply]
      ring
    have hcard : ∑ α : Fin d, ∑' X : T.polys, Sx T i₀ i₁ ν X.1 α α =
        (d : ℂ) * ∑' X : T.polys, Sx T i₀ i₁ ν X.1 μ μ := by
      rw [Finset.sum_congr rfl fun α _ => hdiag α μ]
      simp
    rw [hcard] at htrace
    have hd : (d : ℂ) ≠ 0 := by
      have : 0 < d := Fin.pos μ
      exact_mod_cast this.ne'
    exact (mul_eq_zero.mp htrace).resolve_left hd
  · have h := tsum_image_eq hP (r := latFlip μ) (Or.inl ⟨μ, rfl⟩) (fun X => Sx T i₀ i₁ ν X μ ν')
    have h2 : ∀ X : T.polys, Sx T i₀ i₁ ν (X.1.image (latFlip μ)) μ ν' =
        -Sx T i₀ i₁ ν X.1 μ ν' := fun X => by
      rw [Sx_flip hP hρ μ X.2]
      simp [Ne.symm hne]
    simp only [h2, tsum_neg] at h
    have : (2 : ℂ) * ∑' X : T.polys, Sx T i₀ i₁ ν X.1 μ ν' = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero

end Balaban.SmallField
