/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RadiiHist
public import Balaban.Inhabited.RadiiSetting
public import Balaban.LargeField.R.WindowOfHistory

/-!
# The actual window of a ripe component, instantiated

The genuine-radii family (`RadiiSet`, `RadiiHist`): `d = L = 3`, `M = 14 M₁`, `R_base = 32`,
`R_j = R_base λ_j²`, so `Geo` holds with `c = 14` (`RadiiSet.wGeo`; LF-RECONSTRUCTION §I.1.3: the
order of constants `M = c M₁`, `c ≥ 14`, `R_j ≥ R_base`).  The history `RadiiHist.histT` has a ripe
component `Z` at scale `T = t^*`.  Here the window of Definition III.2.1 (`windowOfHistory`) is formed
for it and the landed geometric theorems of Lemma III.1.2 are applied to it.
-/

@[expose] public section

namespace Balaban.Inhabited.RipeGeo

open Balaban Balaban.LargeField Balaban.Inhabited Balaban.Multiscale

/-- The setting. -/
noncomputable abbrev S0 : Setting := RadiiSet.wS

instance : NeZero S0.M := ⟨by
  show 14 * RadiiSet.M1 ≠ 0
  have := RadiiSet.M1_pos; omega⟩

/-- The scale of the ripe component. -/
noncomputable abbrev T : ℕ := RadiiHist.Tstar S0

/-- The side lengths `n_k = N L^{T-k}`. -/
noncomputable abbrev n0 : ℕ → ℕ := RadiiHist.side S0 (RadiiHist.bigN S0) T

/-- The history with `K = k₀ = T`. -/
noncomputable abbrev H0 : RegionHistory S0 n0 RadiiSet.wR T T :=
  RadiiHist.histT RadiiSet.wS_ok le_rfl le_rfl RadiiSet.wRH (RadiiHist.bigN S0)

theorem exists_ripe0 : ∃ c : H0.Comp T, H0.RipeWindow T c :=
  RadiiHist.ripeWindow_exists RadiiSet.wS_ok le_rfl le_rfl RadiiSet.wRH RadiiSet.wS_good

/-- The ripe component. -/
noncomputable def Z0 : H0.Comp T := exists_ripe0.choose

theorem hW0 : H0.RipeWindow T Z0 := exists_ripe0.choose_spec

/-- The datum `Geo` of the witness: `M = 14 M₁`, `R_j = 32 λ_j² ≥ R_base`. -/
noncomputable def g0 : Geo S0 n0 RadiiSet.wR S0.M := RadiiSet.wGeo n0

theorem hkK0 : T ≤ T := le_rfl

/-- **A ripe window together with a `Geo`** (with `3 ≤ L`). -/
theorem exists_ripeWindow_geo :
    ∃ (S : Setting) (n : ℕ → ℕ) (_ : ∀ k, NeZero (n k)) (R : ℕ → ℝ) (k0 K : ℕ)
      (H : RegionHistory S n R k0 K) (k : ℕ) (Z : H.Comp k),
      S.Good ∧ 3 ≤ S.L ∧ H.RipeWindow k Z ∧ Nonempty (Geo S n R S.M) :=
  ⟨S0, n0, inferInstance, RadiiSet.wR, T, T, H0, T, Z0, RadiiSet.wS_good, le_refl _, hW0,
    ⟨g0⟩⟩

/-- The window of the ripe component. -/
noncomputable abbrev W0 := H0.windowOfHistory Z0 g0 hkK0 hW0

/-- `Hyp` for the window of the witness (Lemma III.1.2, Definition III.2.1). -/
theorem W0_hyp : W0.Hyp := H0.windowOfHistory_hyp hkK0 hW0

/-- The generating set of the window. -/
noncomputable abbrev G0 := W0.windowGenSet W0_hyp

theorem W0_hZ : W0.Zk1 ⊆ W0.Z := H0.windowOfHistory_hZ (g := g0) hkK0 hW0

theorem W0_hOmK1 : ∀ x, x ∉ W0.Zk1 → x ∈ W0.full.Ω 1 :=
  H0.windowOfHistory_hOmK1 (g := g0) hkK0 hW0

theorem W0_hOmK : ∀ x, x ∉ W0.Z → x ∈ W0.full.Ω T :=
  H0.windowOfHistory_hOmK (g := g0) hkK0 hW0 (RadiiHist.one_le_Tstar S0)

theorem W0_hZk1top : ∀ x ∈ W0.Zk1, x ∉ W0.full.Ω (S0.k1 T + 1) :=
  H0.windowOfHistory_hZk1top (g := g0) hkK0 hW0

theorem W0_hsupp : ∀ x ∈ W0.bdry.Ω 1, x ∈ W0.Unb :=
  H0.windowOfHistory_hsupp (g := g0) hkK0 hW0

theorem W0_hbdry : ∀ m, 1 ≤ m → m ≤ T → W0.bdry.Ω m ∩ (W0.Unb \ W0.Z) ⊆ W0.full.Ω m :=
  H0.windowOfHistory_hbdry (g := g0) hkK0 hW0

theorem W0_hmargin : ∀ x ∈ G0.Ω 1, ∀ c, Adj x c → c ∈ W0.Zk1 → c ∈ W0.full.Ω (S0.k1 T) :=
  H0.windowOfHistory_hmargin (g := g0) hkK0 hW0

theorem W0_hcore : ∀ m, 1 ≤ m → m ≤ T → W0.core.Ω m ∩ W0.Zk1 ⊆ W0.full.Ω m :=
  H0.windowOfHistory_hcore (g := g0) hkK0 hW0

theorem W0_hexitLayer :
    ∀ x, x ∉ W0.Zk1 → ∀ c, Adj x c → c ∈ W0.Zk1 → x ∈ W0.full.layer (S0.k1 T) :=
  H0.windowOfHistory_hexitLayer (g := g0) hkK0 hW0

end Balaban.Inhabited.RipeGeo
