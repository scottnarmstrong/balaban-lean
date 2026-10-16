/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GasCoreSize
public import Balaban.LargeField.Def7FineSize

/-!
# The core gas against the modular size of the large-field class (blocker 4)

`notes/phase1/VMOD-43.md` §5b.  The gas of `Polymer/GasCoreSize.lean` is a gas on sets of active
`π_k`-cells of the region `Ω_f = d7Pull F k Ω` (`CubeB m₀ k Ω_f`), with the size `dExt`.  The
large-field class bounds its boundary terms in the fine modular size `d7SizeAt F k Ω X`
(`Def7FineSize.lean`), the real value of `dcovModE m₀ k Ω_f X_f`.

* `dExt_core_eq_d7SizeAt`: if the fine set `X_f` of a domain `X` is `Ŷ(S)` for the set `S` of
  cells of a core `T` (that is, `X_f` is `sitesOf T` together with the components of `Ω_f^c` it
  touches), `X_f` is site-connected and `d7SizeAtE ≠ ⊤`, then `dExt T = d7SizeAt F k Ω X`:
  equality, so a bound with decay in the modular size is a bound with the same decay in `dExt` of
  the core.  When `d7SizeAtE = ⊤` the real value `d7SizeAt` is `0` while `dExt` is `Mbig`, so no
  inequality holds there; the bounds of (D7) are stated only for `FineValid` domains.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Polymer Balaban.LargeField.Def7

variable {S : Setting} {n : ℕ → ℕ} {M K m₀ m₁ : ℕ} [NeZero S.L]

/-- **The size of a core is the modular size of its domain.**  The core `T` is a set of active
`π_k`-cells of the fine region `d7Pull F k Om`; if the fine set of `X` is `Ŷ(sitesOf T)`, is
site-connected and has finite modular size, then `dExt T = d7SizeAt F k Om X`. -/
theorem dExt_core_eq_d7SizeAt (F : FineSizeFrame S n M K m₀ m₁) (k : ℕ)
    (Om : Set (Torus S.d (n k)))
    (T : Finset (CubeB (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ k (d7Pull F k Om)))
    (X : Finset (Torus S.d (n k)))
    (hX : d7Pull F k (X : Set (Torus S.d (n k))) = Yhat (d7Pull F k Om) (sitesOf T))
    (hcon : SiteConnected (d7Pull F k (X : Set (Torus S.d (n k)))))
    (hfin : d7SizeAtE F k Om X ≠ ⊤) :
    dExt (d := S.d) T = d7SizeAt F k Om X := by
  have h1 : dOmega m₀ k (d7Pull F k Om) (sitesOf T) = d7SizeAtE F k Om X := by
    unfold dOmega d7SizeAtE
    rw [← hX]
    simp [hcon]
  rw [dExt_eq_toReal (by rw [h1]; exact hfin), h1]
  rfl

/-- The same for the size `d7Size` after `R`: the region is `Ω_k^post(𝔸)`. -/
theorem dExt_core_eq_d7Size {R : ℕ → ℝ} {k0 : ℕ} [∀ k, NeZero (n k)]
    (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (T : Finset (CubeB (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull F k (A.H.omegaPost k))))
    (X : Finset (Torus S.d (n k)))
    (hX : d7Pull F k (X : Set (Torus S.d (n k))) =
      Yhat (d7Pull F k (A.H.omegaPost k)) (sitesOf T))
    (hcon : SiteConnected (d7Pull F k (X : Set (Torus S.d (n k)))))
    (hfin : d7SizeE F A k X ≠ ⊤) :
    dExt (d := S.d) T = d7Size F A k X :=
  dExt_core_eq_d7SizeAt F k _ T X hX hcon hfin

end Balaban.LargeField
