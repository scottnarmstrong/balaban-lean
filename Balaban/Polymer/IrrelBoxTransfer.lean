/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.InheritedAgreeGeom
public import Balaban.Polymer.TwoTorusStepGeometry
public import Balaban.Polymer.FderivTransfer
public import Balaban.SmallField.IrrelTorus

/-!
# The terms of the small-field class on two tori in box form

`E_boxAgree`: the torus independence of the terms (P4 (H.4), the clause `TorusIndep`), in the box
form needed to compare two tori: for a polymer `X` of `𝒟_j` inside the centred box of radius `R`
of the torus `N₁` and its image `boxMap '' X` on the torus `N₂`, the terms `ℰ^{(j)}(y, X; Ψ, h)`
and `ℰ^{(j)}(boxMap y, boxMap '' X; Ψ', h')` agree when the fields agree on `X` under `boxMap`.
The proof sends `X` to a polymer of `ℤ^d` through the centred representatives, where the clause
`TorusIndep` applies, and returns by the locality of the terms.

`xferT`, `xferT'`: the transport of fields on `X` to fields on `boxMap '' X` and back; the terms
`Ψ ↦ ℰ(y, X; Ψ, h)` on the two tori are related by them as in `fderiv_eq_of_transfer`, whence the
agreement of the first and second derivatives of the terms at corresponding points and directions
(`fderiv_E_boxAgree`, `fderiv_E_boxAgree_h`, `D2_E_boxAgree`).
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep


open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6 Balaban.RootFSpine
  Balaban.Multiscale

section Gen

variable {d n : ℕ}

theorem dvd_valMinAbs_of_aligned [NeZero n] {a : ℕ} (ha : a ∣ n) {b : Torus d n}
    (hb : Aligned a b) (μ : Fin d) : (a : ℤ) ∣ (b μ).valMinAbs := by
  have h1 := hb μ
  have e : (((b μ).val : ℤ) : ZMod n) = (((b μ).valMinAbs : ℤ) : ZMod n) := by
    rw [ZMod.coe_valMinAbs]; simp
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at e
  have h2 : (a : ℤ) ∣ ((b μ).val : ℤ) := by
    exact_mod_cast Nat.dvd_of_mod_eq_zero h1
  have h3 : (a : ℤ) ∣ (n : ℤ) := by exact_mod_cast ha
  have h4 := dvd_add (dvd_trans h3 e) h2
  simpa using h4

end Gen

variable {d L N₁ N₂ m₁ K N : ℕ} [NeZero L] [NeZero N₁] [NeZero N₂] {ϱ : ℝ}

/-- The centred integer vector of a site of the torus. -/
def centred (x : CTorus d L N₁ m₁ K) : Fin d → ℤ := fun μ => (x μ).valMinAbs

omit [NeZero L] [NeZero N₁] in
theorem toTorus_centred (x : CTorus d L N₁ m₁ K) :
    toTorus L N₁ m₁ K (centred x) = x := by
  funext μ; simp [toTorus, centred, ZMod.coe_valMinAbs]

omit [NeZero L] [NeZero N₁] [NeZero N₂] in
theorem toTorus_centred_boxMap (x : CTorus d L N₁ m₁ K) :
    toTorus L N₂ m₁ K (centred x) = boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x := rfl


omit [NeZero L] [NeZero N₁] in
theorem centred_quarter {R : ℕ} (hR : 4 * R < N₁ * L ^ m₁ * L ^ K) {x : CTorus d L N₁ m₁ K}
    (hx : InBox d R ((N₁ * L ^ m₁) * L ^ K) x) : QBox d (N₁ * L ^ m₁ * L ^ K) (centred x) := by
  intro μ
  have := hx μ
  simp only [centred]
  have h2 : (4 * R : ℤ) < ((N₁ * L ^ m₁ * L ^ K : ℕ) : ℤ) := by exact_mod_cast hR
  have : 4 * |(x μ).valMinAbs| ≤ 4 * (R : ℤ) := by linarith
  linarith

open Classical in
/-- **The torus independence of the terms in box form** (P4 (H.4)): `ℰ^{(j)}(y, X; Ψ, h)` on two tori
agrees at the polymer `X` of the box and its image, when the fields agree on `X` under `boxMap`. -/
theorem E_boxAgree {Tm : ∀ (M : ℕ) [NeZero M], Terms d L M m₁ K N ϱ} {m₀ j : ℕ} (hj1 : 1 ≤ j)
    (hjK : j ≤ K) (hT : TorusIndep m₀ Tm)
    (hlocB : ∀ j y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      (Tm N₂).E j y X Ψ h = (Tm N₂).E j y X Ψ' h')
    (hN₁ : L ^ m₀ ∣ N₁) (hN₂ : L ^ m₀ ∣ N₂) (hM8 : 8 ≤ L ^ (m₀ + m₁)) {R : ℕ}
    (hR₁ : 4 * R < N₁ * L ^ m₁ * L ^ K) (hR₂ : 4 * R < N₂ * L ^ m₁ * L ^ K)
    {y : CTorus d L N₁ m₁ K} {X : Set (CTorus d L N₁ m₁ K)} (hy : Aligned (L ^ j) y) (hyX : y ∈ X)
    (hX : IsPolyDom m₀ j X) (hXR : ∀ x ∈ X, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (Ψ h : Fld d L N₁ m₁ K N) (Ψ' h' : Fld d L N₂ m₁ K N)
    (hΨ : ∀ x ∈ X, Ψ' (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x) = Ψ x)
    (hh : ∀ x ∈ X, h' (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x) = h x) :
    (Tm N₂).E j (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) y)
      (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) '' X) Ψ' h' =
    (Tm N₁).E j y X Ψ h := by
  set n₁ := (N₁ * L ^ m₁) * L ^ K with hn₁
  set n₂ := (N₂ * L ^ m₁) * L ^ K with hn₂
  set A : Finset (Fin d → ℤ) := (Finset.univ.filter (fun x => x ∈ X)).image centred with hA
  have hQ₁ : ∀ a ∈ A, QBox d (N₁ * L ^ m₁ * L ^ K) a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    exact centred_quarter hR₁ (hXR x (Finset.mem_filter.1 hx).2)
  have hQ₂ : ∀ a ∈ A, QBox d (N₂ * L ^ m₁ * L ^ K) a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    have := hXR x (Finset.mem_filter.1 hx).2
    intro μ
    have h1 := this μ
    simp only [centred]
    have h2 : (4 * R : ℤ) < ((N₂ * L ^ m₁ * L ^ K : ℕ) : ℤ) := by exact_mod_cast hR₂
    have : 4 * |(x μ).valMinAbs| ≤ 4 * (R : ℤ) := by linarith
    linarith
  have hXA₁ : toTorus L N₁ m₁ K '' (A : Set (Fin d → ℤ)) = X := by
    ext x
    simp only [hA, Set.mem_image, Finset.mem_coe, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ⟨z, hz, rfl⟩, rfl⟩
      rw [toTorus_centred]; exact hz
    · intro hx
      exact ⟨centred x, ⟨x, hx, rfl⟩, toTorus_centred x⟩
  have hXA₂ : toTorus L N₂ m₁ K '' (A : Set (Fin d → ℤ)) =
      boxMap n₁ n₂ '' X := by
    ext x
    simp only [hA, Set.mem_image, Finset.mem_coe, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨centred z, ⟨z, hz, rfl⟩, rfl⟩
  have hpoly₁ : PolyZ L m₀ m₁ j (A : Set (Fin d → ℤ)) :=
    (isPolyDom_toTorus_iff (N₁ := N₁) hjK hN₁ hM8 hQ₁).1 (by rw [hXA₁]; exact hX)
  have hpoly₂ : IsPolyDom (L := L) (N₁ := N₂) (m₁ := m₁) (k := K) m₀ j
      (boxMap n₁ n₂ '' X) := by
    rw [← hXA₂]; exact (isPolyDom_toTorus_iff (N₁ := N₂) hjK hN₂ hM8 hQ₂).2 hpoly₁
  have hR8₁ := eight_le_R (L := L) (m₁ := m₁) (k := K) (j := j) hN₁ hM8
  have hR8₂ := eight_le_R (L := L) (m₁ := m₁) (k := K) (j := j) hN₂ hM8

  have hY₁ := Ypoly_eq_toTorus_image (N₁ := N₁) (m₀ := m₀) hjK hQ₁ hR8₁ hpoly₁
  have hY₂ := Ypoly_eq_toTorus_image (N₁ := N₂) (m₀ := m₀) hjK hQ₂ hR8₂ hpoly₁
  have hNW₁ := nonWind_blocks (N₁ := N₁) (L := L) (m₁ := m₁) hjK hQ₁ hR8₁
  have hNW₂ := nonWind_blocks (N₁ := N₂) (L := L) (m₁ := m₁) hjK hQ₂ hR8₂
  have hp : (0 : ℤ) < ((L ^ j : ℕ) : ℤ) := by exact_mod_cast pow_pos (NeZero.pos L) j
  have hsmall₂ : ∀ a ∈ A, ∀ μ, 2 * |a μ / ((L ^ j : ℕ) : ℤ)| <
      ((N₂ * L ^ m₁ * L ^ (K - j) : ℕ) : ℤ) := by
    intro a ha μ
    have h := hQ₂ a ha μ
    rw [ell_eq (N₁ := N₂) (L := L) (m₁ := m₁) hjK] at h
    have := ediv_small hp (R := ((N₂ * L ^ m₁ * L ^ (K - j) : ℕ) : ℤ)) (by exact_mod_cast hR8₂)
      (x := a μ) (by push_cast at h ⊢; exact h)
    have h0 := abs_nonneg (a μ / ((L ^ j : ℕ) : ℤ))
    omega
  have hdvd : ∀ μ, ((L ^ j : ℕ) : ℤ) ∣ (y μ).valMinAbs := fun μ =>
    dvd_valMinAbs_of_aligned (dvd_mul_of_dvd_right (pow_dvd_pow L hjK) _) hy μ
  have hyA : centred y ∈ A := Finset.mem_image.2 ⟨y, by simpa using hyX, rfl⟩
  set y₀ : Fin d → ℤ := Balaban.SmallField.Def6.blockOf L j (centred y) with hy₀
  have hy₀X' : y₀ ∈ A.image (Balaban.SmallField.Def6.blockOf L j) := Finset.mem_image.2 ⟨centred y, hyA, rfl⟩
  have hbp : ∀ μ, y₀ μ * ((L ^ j : ℕ) : ℤ) = (y μ).valMinAbs := fun μ =>
    Int.ediv_mul_cancel (hdvd μ)
  have hbp₁ : blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) j y₀ = y := by
    funext μ
    show (((y₀ μ * ((L ^ j : ℕ) : ℤ) : ℤ)) : ZMod ((N₁ * L ^ m₁) * L ^ K)) = y μ
    rw [hbp, ZMod.coe_valMinAbs]
  have hbp₂ : blockPt (L := L) (N₁ := N₂) (m₁ := m₁) (k := K) j y₀ = boxMap n₁ n₂ y := by
    funext μ
    show (((y₀ μ * ((L ^ j : ℕ) : ℤ) : ℤ)) : ZMod ((N₂ * L ^ m₁) * L ^ K)) = _
    rw [hbp]; rfl
  set ψ : InfFld d N := fun w => Ψ (toTorus L N₁ m₁ K w) with hψ
  set ψh : InfFld d N := fun w => h (toTorus L N₁ m₁ K w) with hψh
  have hpull₁ : ∀ f : Fld d L N₁ m₁ K N,
      pullFld (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) j (fun w => f (toTorus L N₁ m₁ K w)) = f := by
    intro f
    funext x
    show f (toTorus L N₁ m₁ K (fineLift j x)) = f x
    rw [toTorus_fineLift hjK]
  have hpull₂ : ∀ (f : Fld d L N₁ m₁ K N) (g : Fld d L N₂ m₁ K N), (∀ x ∈ X, g (boxMap n₁ n₂ x) = f x) →
      ∀ x ∈ X, pullFld (L := L) (N₁ := N₂) (m₁ := m₁) (k := K) j
        (fun w => f (toTorus L N₁ m₁ K w)) (boxMap n₁ n₂ x) = g (boxMap n₁ n₂ x) := by
    intro f g hfg x hx
    show f (toTorus L N₁ m₁ K (fineLift j (toTorus L N₂ m₁ K (centred x)))) = _
    rw [fineLift_toTorus hjK (centred x) (hsmall₂ _ (Finset.mem_image.2 ⟨x, by simpa using hx, rfl⟩)),
      toTorus_centred, hfg x hx]
  have hE := hT.E_eq j hj1 hjK y₀ (A.image (Balaban.SmallField.Def6.blockOf L j)) hy₀X' ψ ψh N₁ N₂ hNW₁ hNW₂
    (by rw [hY₁, hXA₁]; exact hX) (by rw [hY₂, hXA₂]; exact hpoly₂)
  rw [hbp₁, hY₁, hXA₁] at hE
  rw [hbp₂, hY₂, hXA₂] at hE
  have h1 : (Tm N₁).E j y X (pullFld j ψ) (pullFld j ψh) = (Tm N₁).E j y X Ψ h := by
    rw [hψ, hψh, hpull₁, hpull₁]
  have h2 := hlocB j (boxMap n₁ n₂ y) (boxMap n₁ n₂ '' X) Ψ' (pullFld j ψ) h' (pullFld j ψh)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨(hpull₂ Ψ Ψ' hΨ x hx).symm, (hpull₂ h h' hh x hx).symm⟩)
  rw [h2, ← hE, h1]



/-! ### The transport of fields on a polymer -/

section Xfer

variable {X : Set (CTorus d L N₁ m₁ K)}

open Classical in
/-- **The transport of a field on `X` to the image `boxMap '' X`**: the value at `boxMap x` of the
transported field is the value at `x`, and the transported field vanishes off `boxMap '' X`. -/
noncomputable def xferT (X : Set (CTorus d L N₁ m₁ K)) (N₂ : ℕ) [NeZero N₂] :
    Fld d L N₁ m₁ K N →ₗ[ℂ] Fld d L N₂ m₁ K N where
  toFun Ψ := fun w i => ∑ x ∈ Finset.univ.filter (fun x => x ∈ X),
    if boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x = w then Ψ x i else 0
  map_add' Ψ Φ := by
    funext w i
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  map_smul' c Ψ := by
    funext w i
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp

open Classical in
/-- **The pullback of a field on `boxMap '' X` to `X`**, zero off `X`. -/
noncomputable def xferT' (X : Set (CTorus d L N₁ m₁ K)) (N₂ : ℕ) [NeZero N₂] :
    Fld d L N₂ m₁ K N →ₗ[ℂ] Fld d L N₁ m₁ K N where
  toFun Ψ := fun x i => if x ∈ X then Ψ (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x) i
    else 0
  map_add' Ψ Φ := by
    funext x i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c Ψ := by
    funext x i
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp

theorem xferT_apply_boxMap
    (hinj : Set.InjOn (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K)) X)
    (Ψ : Fld d L N₁ m₁ K N) {x : CTorus d L N₁ m₁ K} (hx : x ∈ X) :
    xferT X N₂ Ψ (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x) = Ψ x := by
  classical
  funext i
  simp only [xferT, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single x]
  · simp
  · intro x' hx' hne
    have hx'X := (Finset.mem_filter.1 hx').2
    exact ite_eq_right_iff.2 fun h => absurd (hinj hx'X hx h) hne
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩) h

theorem xferT_apply_of_not_mem (Ψ : Fld d L N₁ m₁ K N) {w : CTorus d L N₂ m₁ K}
    (hw : w ∉ boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) '' X) :
    xferT X N₂ Ψ w = 0 := by
  classical
  funext i
  simp only [xferT, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  exact ite_eq_right_iff.2 fun h => absurd ⟨x, (Finset.mem_filter.1 hx).2, h⟩ hw

theorem xferT_congr (Ψ Φ : Fld d L N₁ m₁ K N) (h : ∀ x ∈ X, Ψ x = Φ x) :
    xferT X N₂ Ψ = xferT X N₂ Φ := by
  classical
  funext w i
  simp only [xferT, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [h x (Finset.mem_filter.1 hx).2]

omit [NeZero L] [NeZero N₁] in
theorem xferT'_apply_of_mem (Ψ : Fld d L N₂ m₁ K N) {x : CTorus d L N₁ m₁ K} (hx : x ∈ X) :
    xferT' X N₂ Ψ x = Ψ (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x) := by
  classical
  funext i
  simp only [xferT', LinearMap.coe_mk, AddHom.coe_mk, hx, ↓reduceIte]

omit [NeZero L] [NeZero N₁] in
theorem xferT'_apply_of_not_mem (Ψ : Fld d L N₂ m₁ K N) {x : CTorus d L N₁ m₁ K} (hx : x ∉ X) :
    xferT' X N₂ Ψ x = 0 := by
  classical
  funext i
  simp only [xferT', LinearMap.coe_mk, AddHom.coe_mk, hx, ↓reduceIte, Pi.zero_apply]

theorem xferT_xferT'_xferT
    (hinj : Set.InjOn (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K)) X)
    (Ψ : Fld d L N₁ m₁ K N) :
    xferT X N₂ (xferT' X N₂ (xferT X N₂ Ψ)) = xferT X N₂ Ψ :=
  xferT_congr _ _ fun x hx => by
    rw [xferT'_apply_of_mem _ hx, xferT_apply_boxMap hinj _ hx]

theorem xferT'_xferT_xferT'
    (hinj : Set.InjOn (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K)) X)
    (Ψ : Fld d L N₂ m₁ K N) :
    xferT' X N₂ (xferT X N₂ (xferT' X N₂ Ψ)) = xferT' X N₂ Ψ := by
  funext x
  by_cases hx : x ∈ X
  · rw [xferT'_apply_of_mem _ hx, xferT_apply_boxMap hinj _ hx]
  · rw [xferT'_apply_of_not_mem _ hx, xferT'_apply_of_not_mem _ hx]
omit [NeZero N₁] in
theorem boxMap_injOn_of_box {m₀ : ℕ} (hN₂ : L ^ m₀ ∣ N₂) (hM8 : 8 ≤ L ^ (m₀ + m₁)) {R : ℕ}
    (hR₂ : 4 * R < N₂ * L ^ m₁ * L ^ K) (hXR : ∀ x ∈ X, InBox d R ((N₁ * L ^ m₁) * L ^ K) x) :
    Set.InjOn (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K)) X := by
  have hR8 := eight_le_R (L := L) (m₁ := m₁) (k := K) (j := K) hN₂ hM8
  have hle : N₂ * L ^ m₁ * L ^ (K - K) ≤ N₂ * L ^ m₁ * L ^ K :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (NeZero.pos L) (Nat.sub_le _ _))
  intro a ha b hb hab
  exact boxMap_inj (hm' := by omega) (hXR a ha) (hXR b hb) hab

section Deriv

variable {Tm : ∀ (M : ℕ) [NeZero M], Terms d L M m₁ K N ϱ} {m₀ j : ℕ} (hj1 : 1 ≤ j)
  (hjK : j ≤ K) (hT : TorusIndep m₀ Tm)
  (hlocB : ∀ j y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
    (Tm N₂).E j y X Ψ h = (Tm N₂).E j y X Ψ' h')
  (hN₁ : L ^ m₀ ∣ N₁) (hN₂ : L ^ m₀ ∣ N₂) (hM8 : 8 ≤ L ^ (m₀ + m₁)) {R : ℕ}
  (hR₁ : 4 * R < N₁ * L ^ m₁ * L ^ K) (hR₂ : 4 * R < N₂ * L ^ m₁ * L ^ K)
  {y : CTorus d L N₁ m₁ K} {X : Set (CTorus d L N₁ m₁ K)} (hy : Aligned (L ^ j) y) (hyX : y ∈ X)
  (hX : IsPolyDom m₀ j X) (hXR : ∀ x ∈ X, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
include hj1 hjK hT hlocB hN₁ hN₂ hM8 hR₁ hR₂ hy hyX hX hXR

/-- **The first derivative in the field of a term on two tori.** -/
theorem fderiv_E_boxAgree (h₁ : Fld d L N₁ m₁ K N) (h₂ : Fld d L N₂ m₁ K N)
    (hh : ∀ x ∈ X, h₂ (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x) = h₁ x)
    {p v : Fld d L N₁ m₁ K N} {q w : Fld d L N₂ m₁ K N}
    (hp : ∀ x ∈ X, q (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x) = p x)
    (hv : ∀ x ∈ X, w (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x) = v x) :
    fderiv ℂ (fun Ψ => (Tm N₁).E j y X Ψ h₁) p v =
      fderiv ℂ (fun Ψ => (Tm N₂).E j (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) y)
        (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) '' X) Ψ h₂) q w := by
  have hinj := boxMap_injOn_of_box hN₂ hM8 hR₂ hXR
  refine fderiv_eq_of_transfer (LinearMap.toContinuousLinearMap (xferT X N₂))
    (LinearMap.toContinuousLinearMap (xferT' X N₂)) (fun Ψ => xferT_xferT'_xferT hinj Ψ)
    (fun Ψ => ?_) (fun Ψ => ?_) ?_ ?_
  · exact (E_boxAgree hj1 hjK hT hlocB hN₁ hN₂ hM8 hR₁ hR₂ hy hyX hX hXR Ψ h₁ _ h₂
      (fun x hx => xferT_apply_boxMap hinj Ψ hx) hh).symm
  · exact E_boxAgree hj1 hjK hT hlocB hN₁ hN₂ hM8 hR₁ hR₂ hy hyX hX hXR _ h₁ Ψ h₂
      (fun x hx => (xferT'_apply_of_mem Ψ hx).symm) hh
  · exact xferT_congr _ _ fun x hx => by
      simp only [LinearMap.coe_toContinuousLinearMap']
      rw [xferT'_apply_of_mem _ hx, hp x hx]
  · exact xferT_congr _ _ fun x hx => by
      simp only [LinearMap.coe_toContinuousLinearMap']
      rw [xferT'_apply_of_mem _ hx, hv x hx]

/-- **The first derivative in the source of a term on two tori.** -/
theorem fderiv_E_boxAgree_h (Ψ₁ : Fld d L N₁ m₁ K N) (Ψ₂ : Fld d L N₂ m₁ K N)
    (hΨ : ∀ x ∈ X, Ψ₂ (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x) = Ψ₁ x)
    {p v : Fld d L N₁ m₁ K N} {q w : Fld d L N₂ m₁ K N}
    (hp : ∀ x ∈ X, q (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x) = p x)
    (hv : ∀ x ∈ X, w (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x) = v x) :
    fderiv ℂ (fun h => (Tm N₁).E j y X Ψ₁ h) p v =
      fderiv ℂ (fun h => (Tm N₂).E j (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) y)
        (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) '' X) Ψ₂ h) q w := by
  have hinj := boxMap_injOn_of_box (X := X) hN₂ hM8 hR₂ hXR
  refine fderiv_eq_of_transfer (LinearMap.toContinuousLinearMap (xferT X N₂))
    (LinearMap.toContinuousLinearMap (xferT' X N₂)) (fun Ψ => xferT_xferT'_xferT hinj Ψ)
    (fun h => ?_) (fun h => ?_) ?_ ?_
  · exact (E_boxAgree hj1 hjK hT hlocB hN₁ hN₂ hM8 hR₁ hR₂ hy hyX hX hXR Ψ₁ h Ψ₂ _ hΨ
      (fun x hx => xferT_apply_boxMap hinj h hx)).symm
  · exact E_boxAgree hj1 hjK hT hlocB hN₁ hN₂ hM8 hR₁ hR₂ hy hyX hX hXR Ψ₁ _ Ψ₂ h hΨ
      (fun x hx => (xferT'_apply_of_mem h hx).symm)
  · exact xferT_congr _ _ fun x hx => by
      simp only [LinearMap.coe_toContinuousLinearMap']
      rw [xferT'_apply_of_mem _ hx, hp x hx]
  · exact xferT_congr _ _ fun x hx => by
      simp only [LinearMap.coe_toContinuousLinearMap']
      rw [xferT'_apply_of_mem _ hx, hv x hx]

/-- **The second derivative in the field of a term on two tori.** -/
theorem D2_E_boxAgree (h₁ : Fld d L N₁ m₁ K N) (h₂ : Fld d L N₂ m₁ K N)
    (hh : ∀ x ∈ X, h₂ (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x) = h₁ x)
    {p v v' : Fld d L N₁ m₁ K N} {q w w' : Fld d L N₂ m₁ K N}
    (hp : ∀ x ∈ X, q (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x) = p x)
    (hv : ∀ x ∈ X, w (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x) = v x)
    (hv' : ∀ x ∈ X, w' (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) x) = v' x) :
    Balaban.SmallField.D2 (fun Ψ => (Tm N₁).E j y X Ψ h₁) p v v' =
      Balaban.SmallField.D2 (fun Ψ => (Tm N₂).E j (boxMap ((N₁ * L ^ m₁) * L ^ K)
        ((N₂ * L ^ m₁) * L ^ K) y)
        (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K) '' X) Ψ h₂) q w w' := by
  have hinj := boxMap_injOn_of_box (X := X) hN₂ hM8 hR₂ hXR
  refine D2_eq_of_transfer (LinearMap.toContinuousLinearMap (xferT X N₂))
    (LinearMap.toContinuousLinearMap (xferT' X N₂)) (fun Ψ => xferT_xferT'_xferT hinj Ψ)
    (fun Ψ => xferT'_xferT_xferT' hinj Ψ) (fun Ψ => ?_) (fun Ψ => ?_) ?_ ?_ ?_
  · exact (E_boxAgree hj1 hjK hT hlocB hN₁ hN₂ hM8 hR₁ hR₂ hy hyX hX hXR Ψ h₁ _ h₂
      (fun x hx => xferT_apply_boxMap hinj Ψ hx) hh).symm
  · exact E_boxAgree hj1 hjK hT hlocB hN₁ hN₂ hM8 hR₁ hR₂ hy hyX hX hXR _ h₁ Ψ h₂
      (fun x hx => (xferT'_apply_of_mem Ψ hx).symm) hh
  · exact xferT_congr _ _ fun x hx => by
      simp only [LinearMap.coe_toContinuousLinearMap']
      rw [xferT'_apply_of_mem _ hx, hp x hx]
  · exact xferT_congr _ _ fun x hx => by
      simp only [LinearMap.coe_toContinuousLinearMap']
      rw [xferT'_apply_of_mem _ hx, hv x hx]
  · exact xferT_congr _ _ fun x hx => by
      simp only [LinearMap.coe_toContinuousLinearMap']
      rw [xferT'_apply_of_mem _ hx, hv' x hx]

end Deriv

end Xfer

end Balaban.Polymer.TwoTorusStep
