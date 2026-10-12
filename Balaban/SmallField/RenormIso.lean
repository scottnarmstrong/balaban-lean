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

end Balaban.SmallField
