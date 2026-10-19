/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.D1ParentDomain
public import Balaban.LargeField.R.WindowComposeCore
public import Balaban.LargeField.R.RRemovedLocality

/-!
# The post-weight support of the window output (blocker 4)

P7 (2.11)–(2.16), (1.32)[5]: the window configuration is taken where all the characteristic
functions of the history are nonzero, including `χ_Y` of the post weight at the scale `m' + 1` and
the domain factors of the retained components.  As a condition on the output `o` of the window
component `Z` (scale `k = j + 1`), the support of that weight is: there is a global field `ψ_k` on
the `k`-blocks that agrees with `o` on the blocks of `V_Z` off `Z₀`, with `χ_Y(ψ_k) ≠ 0` for
`Y = Z_kᶜ`, and with `ChiDomAt` of every retained component that meets the data region of the
small-field generating set, at `outOf ψ_k`.

The values of `ψ_k` on `Z₀` are free, so the predicate reads `o` off `Z₀` only; this is the
locality `hPloc` of `window_hid_core_action` (`windowPostSupport_loc`).  The true post weight at an
output `o` gives the predicate with `ψ_k` the actual field.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.LargeField.Def7

section PostSupport

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (H : RegionHistory S n R k0 K)
  (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- **The support of the post weight at the window output** (see the module docstring). -/
def WindowPostSupport (hv : EuclideanSpace ℝ (Fin N)) {Z : H.Comp (j + 1)}
    (Z0 : Set (BlockAt S n M K (j + 1))) (o : OutT N R (H.localHistory M K (j + 1) Z) (j + 1)) :
    Prop :=
  ∃ ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N),
    (∀ b ∈ Vblk R (H.localHistory M K (j + 1) Z) (j + 1), b ∉ Z0 → ψk b = outField N o b) ∧
    Cx.chiY ((H.step (j + 1)).Z)ᶜ ψk hv ≠ 0 ∧
    ∀ C : H.Comp (j + 1), C.1 ∉ H.rem (j + 1) →
      (∃ t ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ), parentSiteCube Cx t ∈ C.1) →
      ∃ (A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1)))
        (x : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A),
        ChiDomAt Cx.geo Cx.cs H (j + 1) C (outOf R (H.localHistory M K (j + 1) C) (j + 1) ψk) x

/-- **The support of the post weight at some direction**: `WindowPostSupport` for some `h`.
The sphere and pair bounds read from `χ_Y` do not involve the direction, so the window domain facts
need the support at one direction only; this predicate does not depend on `h`. -/
def WindowPostSupportAny (Z0 : Set (BlockAt S n M K (j + 1))) {Z : H.Comp (j + 1)}
    (o : OutT N R (H.localHistory M K (j + 1) Z) (j + 1)) : Prop :=
  ∃ hv : EuclideanSpace ℝ (Fin N), WindowPostSupport H Cx hv Z0 o

variable {H Cx}

/-- **`WindowPostSupport` reads the output off `Z₀` only** (the premise `hPloc` of
`window_hid_core_action`). -/
theorem windowPostSupport_loc {hv : EuclideanSpace ℝ (Fin N)} {Z : H.Comp (j + 1)}
    (Z0 : Set (BlockAt S n M K (j + 1)))
    (o o' : OutT N R (H.localHistory M K (j + 1) Z) (j + 1))
    (h : (remZeroSplit (H.localHistory M K (j + 1) Z) (j + 1) Z0 o).2 =
      (remZeroSplit (H.localHistory M K (j + 1) Z) (j + 1) Z0 o').2) :
    WindowPostSupport H Cx hv Z0 o → WindowPostSupport H Cx hv Z0 o' := by
  rintro ⟨ψk, hψ, hχ, hC⟩
  refine ⟨ψk, fun b hb hb0 => ?_, hχ, hC⟩
  rw [hψ b hb hb0]
  exact outField_eq_of_split_snd (H.localHistory M K (j + 1) Z) (j + 1) Z0 h hb0

/-- **`WindowPostSupportAny` reads the output off `Z₀` only.** -/
theorem windowPostSupportAny_loc {Z : H.Comp (j + 1)}
    (Z0 : Set (BlockAt S n M K (j + 1)))
    (o o' : OutT N R (H.localHistory M K (j + 1) Z) (j + 1))
    (h : (remZeroSplit (H.localHistory M K (j + 1) Z) (j + 1) Z0 o).2 =
      (remZeroSplit (H.localHistory M K (j + 1) Z) (j + 1) Z0 o').2) :
    WindowPostSupportAny (H := H) Cx Z0 o → WindowPostSupportAny (H := H) Cx Z0 o' :=
  fun ⟨hv, hs⟩ => ⟨hv, windowPostSupport_loc Z0 o o' h hs⟩

/-- **A nonzero kernel times a weight carrying `1[Pp]` gives the kernel nonzero and `Pp`**: the form in
which the window points of nonzero weight enter `hnamedCU`. -/
theorem ne_zero_and_of_mul_supInd {α : Type*} {P : α → Prop} {o : α} {Kv wt wg : ℝ}
    (hwt : wt = wg * supInd P o) (h : Kv * wt ≠ 0) : Kv ≠ 0 ∧ P o := by
  refine ⟨left_ne_zero_of_mul h, ?_⟩
  by_contra hP
  apply right_ne_zero_of_mul h
  rw [hwt]
  simp [supInd, hP]

end PostSupport

end Balaban.LargeField
