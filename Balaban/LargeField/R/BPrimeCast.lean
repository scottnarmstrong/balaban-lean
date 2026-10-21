/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BPrimeGenW
public import Balaban.LargeField.Def7SmallFieldC

/-!
# Fields and data along the transport `castG` of a generating set

The decoupled background fields of the residual of `R` are those of the transported set
`genWC Y = castG (𝔹_k(W))` on the Def-6 torus (`BPrimeGenW`), while the small-field functions of
Def-7 read fields of `𝔹_k(W)` on the level-`k` torus.  Along `castG h` (`h : N₀' = N₀`) fields on
`Ω₁`, fields on the torus and data are transported (`castΩField`, `castTField`, `castData`), and
the composed field, the background field and the extension commute with the transport.

* `castΩField`, `castTField`, `castData`; `castTField_apply` (the transported field is read through
  `torusCast`);
* `composeField_castG`, `bgFieldC_castG`;
* `SFCtx.genWCj`: the transported `𝔹_j(W)`; `SFCtx.psiJAt_cast`: the composed field `ψ^{(j)}` of
  Def-7 at a transported background field is the composed field of the transported sets.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.GsSpec

section Cast

variable {d L k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- The transport of a field on `Ω₁` of `castG h G` to a field on `Ω₁` of `G`. -/
def castΩField {N₀' N₀ : ℕ} [NeZero N₀'] [NeZero N₀] (h : N₀' = N₀)
    (G : GeneratingSet d L N₀' k ϱ) (φ : (castG h G).Ω 1 × Fin N → ℂ) : G.Ω 1 × Fin N → ℂ := by
  subst h; exact φ

/-- The transport of a field on the torus of side `N₀' L^k` to the torus of side `N₀ L^k`. -/
def castTField {N₀' N₀ : ℕ} (h : N₀' = N₀) (Ψ : Torus d (N₀' * L ^ k) → Fin N → ℂ) :
    Torus d (N₀ * L ^ k) → Fin N → ℂ := by
  subst h; exact Ψ

/-- The transport of data of `G` to data of `castG h G`. -/
def castData {N₀' N₀ : ℕ} [NeZero N₀'] [NeZero N₀] (h : N₀' = N₀)
    (G : GeneratingSet d L N₀' k ϱ) (D : BgData G N) : BgData (castG h G) N := by
  subst h; exact D

theorem torusCast_self' {a : ℕ} [NeZero a] (y : Torus d a) : (GsSpec.torusCast y : Torus d a) = y := by
  funext μ; simp [GsSpec.torusCast]

/-- The transported field on the torus is read through `torusCast`. -/
theorem castTField_apply {N₀' N₀ : ℕ} [NeZero N₀'] [NeZero N₀] (h : N₀' = N₀)
    (Ψ : Torus d (N₀' * L ^ k) → Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) :
    castTField h Ψ x = Ψ (GsSpec.torusCast x) := by
  subst h
  rw [torusCast_self']
  rfl

/-- The data of the transported data are the transported data. -/
theorem castData_Ψ {N₀' N₀ : ℕ} [NeZero N₀'] [NeZero N₀] (h : N₀' = N₀)
    (G : GeneratingSet d L N₀' k ϱ) (D : BgData G N) :
    (castData h G D).Ψ = castTField h D.Ψ := by
  subst h; rfl

/-- The data of the transported data are the transported data (the field `h̃`). -/
theorem castData_h {N₀' N₀ : ℕ} [NeZero N₀'] [NeZero N₀] (h : N₀' = N₀)
    (G : GeneratingSet d L N₀' k ϱ) (D : BgData G N) :
    (castData h G D).h = castTField h D.h := by
  subst h; rfl

/-- **The composed field commutes with the transport.** -/
theorem composeField_castG {N₀' N₀ : ℕ} [NeZero N₀'] [NeZero N₀] (h : N₀' = N₀) {ϱ' : ℝ}
    (G : GeneratingSet d L N₀' k ϱ) (G' : GeneratingSet d L N₀' k ϱ') (a : ℕ → ℝ)
    (φ : (castG h G').Ω 1 × Fin N → ℂ) (Ψ : Torus d (N₀' * L ^ k) → Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    composeField (castG h G) (castG h G') a φ (castTField h Ψ) x i =
      composeField G G' a (castΩField h G' φ) Ψ (GsSpec.torusCast x) i := by
  subst h
  rw [torusCast_self']
  rfl

/-- **The background field commutes with the transport.** -/
theorem bgFieldC_castG {N₀' N₀ : ℕ} [NeZero N₀'] [NeZero N₀] (h : N₀' = N₀)
    (G : GeneratingSet d L N₀' k ϱ) (a : ℕ → ℝ) (ν c₀ : ℝ) (D : BgData G N) :
    castΩField h G (bgFieldC (castG h G) a ν c₀ (castData h G D)) = bgFieldC G a ν c₀ D := by
  subst h; rfl

end Cast

namespace Def7.SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

/-- **The transported `𝔹_j(W_k)`** on the Def-6 torus. -/
noncomputable def genWCj {j : ℕ} (hj : j ≤ k) (Y : Set (Torus S.d (n k))) :
    GeneratingSet S.d S.L (C.N₁ * S.L ^ m₁) k (minSep S.L C.geo.M1) :=
  castG C.coarseSide_eq (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L) (c := C.geo.c)
    (n := n k) hj (W2 R Y))

/-- `sfToBg` is the value cast `torusCast`. -/
theorem sfToBg_eq_torusCast (x : Localization.CTorus S.d S.L C.N₁ m₁ k) :
    sfToBg C.geo C.hT x = (GsSpec.torusCast x : BgT C.geo k) := by
  funext μ
  apply ZMod.val_injective
  rw [GsSpec.torusCast_val C.hT, sfToBg, LargeField.torusCast_val]

/-- **The composed field `ψ^{(j)}` of Def-7 at a transported background field** is the composed
field of the transported sets `genWCj ≺ genWC` at the field, with the transported data. -/
theorem psiJAt_cast (Y : Set (Torus S.d (n k))) (ψC : BlockAt S n M K k → Fin N → ℂ)
    (hv : EuclideanSpace ℝ (Fin N)) (φ : (C.genWC Y).Ω 1 × Fin N → ℂ) {j : ℕ} (hj : j ≤ k)
    (x : Localization.CTorus S.d S.L C.N₁ m₁ k) (i : Fin N) :
    C.psiJAt Y ψC hv (castΩField C.coarseSide_eq (C.genW Y) φ) j x i =
      composeField (C.genWCj hj Y) (C.genWC Y) C.weights φ
        (castTField C.coarseSide_eq (liftSingle (C.genW Y) (C.liftDataC ψC) (hC hv)).Ψ) x i := by
  refine Eq.trans ?_ (LargeField.composeField_castG C.coarseSide_eq
    (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L) (c := C.geo.c) (n := n k) hj
      (W2 R Y)) (C.genW Y) C.weights φ (liftSingle (C.genW Y) (C.liftDataC ψC) (hC hv)).Ψ
    x i).symm
  unfold psiJAt
  simp only [hj, ↓reduceDIte]
  show composeField _ _ _ _ _ (sfToBg C.geo C.hT x) i = _
  rw [sfToBg_eq_torusCast]

end Def7.SFCtx

end Balaban.LargeField
