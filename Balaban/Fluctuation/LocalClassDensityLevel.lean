/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensitySource
public import Balaban.Fluctuation.RootMarkedBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The new level of the successor class for the class sequence

**The rooted per-centre sum.**  Theorem 3.1 (a) (`thm31aC_of_input`, `e0CoeffFamily_value_fromTowerG`)
writes the per-block density as `ℰ₀^{(k+1)}(z) = Σ_T e z T`, a sum over the finite sets `T` of
`π_{k+1}`-cubes; the rooted terms of ROOT.md are `rootedSum e y X` (the term of the root site
`y = rootSite z` on the polymer `X = sitesOf T`).  `finsum_polysAt_rootedSum`: if every non-zero
`e z T` lives on a polymer containing the root site, then
`Σ_{X ∋ rootSite z} rootedSum e (rootSite z) X = Σ_T e z T`, which is the left side of the
expansion identity `hDz` in the indexing of the class (`polysAt`).

**The new level.**  `localClass_newLevel_of_expansion` assembles, for the class sequence
`ε_j = P.eps d L j` and the larger sequence `εL_j = K_loc ε_j`, `K_loc = (2 K₁ + 2) C₁`
(`levelGS_xiFieldDom_sub_localB_eps`, under the smallness of `α₀`), the slices at `j = k + 1` of the
term clauses of the energy terms (from per-label pieces, `hsum`), `eucEloc` for the full group, the
density identity (P4 (4.22)), the clauses of the source terms, `eucMloc` for the full group and
the per-site identity.  The chart inclusion `hchart` is discharged.  What remains is displayed in
the hypotheses:

* `hDz`, `hDM`: the expansion identities of the actual densities `𝒟`, `𝒟_M` (P4 (2.57), (4.18),
  (4.22)) on the whole-level domain at the class radius;
* `hDzfull`, `hDzblock`, `hDMfull`: the covariance of `𝒟`, `𝒟_M` under `fullJSymGroup L (k + 1)`;
* `hsum`: the per-centre resummation of the per-label bounds (decision D3(b));
* the per-label hypotheses on the class chart and the locality on the larger chart.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.LargeField Balaban.Fluctuation
  Finset Matrix

/-! ### The rooted per-centre sum -/

section Rooted

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {m₀ : ℕ}

open Classical in
/-- **The rooted per-centre sum over the polymers of the root site.**  For a coefficient family
`e z T` (roots `z`, finite sets `T` of level-`K` cubes) whose non-zero coefficients at the root `z`
live on polymers `sitesOf T` containing the root site, the sum over the polymers `X ∋ rootSite z`
of the rooted terms is the sum of all coefficients of `z`. -/
theorem finsum_polysAt_rootedSum
    (e : RootIdx d L N₁ m₁ K →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) → ℂ)
    (z : RootIdx d L N₁ m₁ K)
    (hsupp : ∀ T, e z T ≠ 0 →
      IsPolyDom m₀ K (sitesOf T) ∧ rootSite z ∈ sitesOf T) :
    ∑ᶠ X ∈ polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (rootSite z),
        rootedSum e (rootSite z) X = ∑ T, e z T := by
  have hfin : (polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (rootSite z)).Finite :=
    Set.toFinite _
  have hroot : ∀ X, rootedSum e (rootSite z) X =
      ∑ T ∈ Finset.univ.filter (fun T => sitesOf T = X), e z T := by
    intro X
    unfold rootedSum
    have h1 : Finset.univ.filter (fun z' : RootIdx d L N₁ m₁ K => rootSite z' = rootSite z) =
        {z} := by
      ext z'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => rootSite_injective h, fun h => h ▸ rfl⟩
    rw [h1, Finset.sum_singleton]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  simp_rw [hroot]
  set s := Finset.univ.filter (fun T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
    (K := K) m₀ K Set.univ) => sitesOf T ∈ polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K
      (rootSite z)) with hs
  have hfib := Finset.sum_fiberwise_of_maps_to (s := s) (t := hfin.toFinset) (g := sitesOf)
    (fun T hT => by simpa [hs] using hT) (fun T => e z T)
  have hin : ∀ X ∈ hfin.toFinset,
      ∑ T ∈ Finset.univ.filter (fun T => sitesOf T = X), e z T =
        ∑ T ∈ s.filter (fun T => sitesOf T = X), e z T := by
    intro X hX
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs]
    constructor
    · intro h
      refine ⟨?_, h⟩
      rw [h]
      simpa using hX
    · exact fun h => h.2
  rw [Finset.sum_congr rfl hin, hfib]
  refine Finset.sum_subset (Finset.subset_univ _) fun T _ hT => ?_
  by_contra h
  obtain ⟨h1, h2⟩ := hsupp T h
  exact hT (by simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2⟩)

end Rooted

/-! ### The new level for the class sequence -/

section NewLevel

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

open Classical in
/-- **The new level of the successor class for the class sequence, conditional on the expansion
identities and the covariance of the actual densities.**  Class radius `ε_j = P.eps d L j`; the
completion of the terms of a polymer `Y` is taken in the larger chart at radius
`εL_j = K_loc ε_j` of `𝔹_{k+1}(Y⁺)`; `α₀` small (`(4d+6)(2d+1) 3α₀ ≤ 1`, `C₁ 3α₀ ≤ c₀, c₁`).
Energy terms: `TE z Y = Σ_{τ ∈ 𝒯E} Tl τ z Y`, the per-label pieces analytic, bounded by
`EbE τ z Y` and invariant under real rotations on the class chart, local on the larger chart,
`hsum` the per-centre resummation; `Tm.E (k + 1) y Y = AE y Y` (`y ∈ Y`).  Source terms: `TM x Y`
with the hypotheses of `localClass_termClausesM_chart`; `Tm.M (k + 1) x Y = AM x Y`.  Remaining
inputs: the expansion identities `hDz`, `hDM` and the full-group covariance `hDzfull`, `hDzblock`,
`hDMfull` of the densities `𝒟`, `𝒟_M` on the whole-level domain.  Conclusion: the slices at
`j = k + 1` of `gs_spec`, `gsStrong`, `pavingGS`, `analyticE`, `rotE`, `eucE`, `localE`, `boundE`,
`eucEloc` (full group), the density identity `Edens_{k+1} = Σ_z 𝒟(z)`, `analyticM`, `rotM` (real
matrices), `eucM`, `localM`, `boundM`, `eucMloc` (full group) and `Mloc_{k+1} = 𝒟_M`. -/
theorem localClass_newLevel_of_expansion {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))]
    {a : ℕ → ℝ} {ν : ℝ}
    (HB : BgHyp d L (k + 1) (minSep L (L ^ m₁)) a ν) (hα₀ : 0 ≤ P.α₀) (hα : 0 ≤ P.alpha d)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * (3 * P.α₀)) ≤ 1)
    (hc0 : xiC1 d * (3 * P.α₀) ≤ bgC0 d L N) (hc1 : xiC1 d * (3 * P.α₀) ≤ bgC1 d L N)
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ Y z, z ∈ Yp Y ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (Tm : Terms d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁)))
    (hgs : ∀ Y, Tm.gs (k + 1) Y =
      localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁))))
    (cpl : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ Y p, cpl Y p = Classical.epsilon
      (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (xiFieldDom a ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
          FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2 ∧
        ∀ z ∈ Y,
          q.1 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).1 z ∧
          q.2 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).2 z))
    -- the energy terms, per label
    {τι : Type*} (𝒯E : Finset τι)
    (Tl : τι → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTlblock : ∀ τ ∈ 𝒯E, ∀ z z' Y p,
      blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) z =
        blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) z' →
      Tl τ z Y p = Tl τ z' Y p)
    (hTlan : ∀ τ ∈ 𝒯E, ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → AnalyticOnNhd ℂ (Tl τ z Y)
      {p | (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2})
    (hTlloc : ∀ τ ∈ 𝒯E, ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → Tl τ z Y p = Tl τ z Y p')
    (EbE : τι → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) → ℝ)
    (hTlbd : ∀ τ ∈ 𝒯E, ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → z ∈ Y →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      ‖Tl τ z Y p‖ ≤ EbE τ z Y)
    (hsum : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → z ∈ Y →
      ∑ τ ∈ 𝒯E, EbE τ z Y ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y))
    (hTlrot : ∀ τ ∈ 𝒯E, ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      Tl τ z Y (rotField (cmat Q) p.1, rotField (cmat Q) p.2) = Tl τ z Y p)
    (AE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hAE : ∀ z Y p, AE z Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        ∑ τ ∈ 𝒯E, Tl τ (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) z)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)))
    (hE : ∀ y Y Ψ h, Tm.E (k + 1) y Y Ψ h = if y ∈ Y then AE y Y (Ψ, h) else 0)
    -- the energy density: expansion identity and covariance (remaining inputs)
    (Dz : CTorus d L N₁ m₁ (k + 1) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hDz : ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      ∑ᶠ Y ∈ polysAt P.m₀ (k + 1) y, ∑ τ ∈ 𝒯E, Tl τ y Y q = Dz y q)
    (hDzblock : ∀ y y' q, blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y' → Dz y q = Dz y' q)
    (hDzfull : ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1),
      ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      Dz (r y) (actField r q.1, actField r q.2) = Dz y q)
    -- the source terms
    (TM : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hTMan : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y → AnalyticOnNhd ℂ (TM x Y)
      ({p | (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2} ×ˢ
        {g | Def6.l1 g < 1}))
    (hTMloc : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → ∀ g, TM x Y (p, g) = TM x Y (p', g))
    (hTMsrc : ∀ x Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
      (g g' : Fld d L N₁ m₁ (k + 1) N), (∀ z ∈ Y, g z = g' z) → TM x Y (p, g) = TM x Y (p, g'))
    {BM : ℝ}
    (hBM : BM < P.c₉ * ((L : ℝ) ^ (k + 1))⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hTMbd : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y → x ∈ Y →
      ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      Def6.l1 g < 1 → vn (TM x Y (p, g)) ≤ BM * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y))
    (hTMrot : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y → ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      Def6.l1 g < 1 →
      TM x Y ((rotField (cmat Q) p.1, rotField (cmat Q) p.2), rotField (cmat Q) g) =
        (cmat Q) *ᵥ TM x Y (p, g))
    (AM : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hAM : ∀ x Y q, AM x Y q =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        TM (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.2),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.2))
    (hM : ∀ x Y Ψ h g, Tm.M (k + 1) x Y Ψ h g = AM x Y ((Ψ, h), g))
    -- the source density: expansion identity and covariance (remaining inputs)
    (DM : CTorus d L N₁ m₁ (k + 1) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hDM : ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      ∑ᶠ Y ∈ polysAt P.m₀ (k + 1) x, TM x Y (q, g) = DM x (q, g))
    (hDMfull : ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1),
      ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      DM (r x) ((actField r q.1, actField r q.2), actField r g) = DM x (q, g)) :
    -- `gs_spec`
    (∀ X, IsPolyDom P.m₀ (k + 1) X →
      X ⊆ ↑((Tm.gs (k + 1) X).Ω 1) ∧ ∀ i, k + 1 < i → (Tm.gs (k + 1) X).Ω i = ∅) ∧
    -- `gsStrong`
    (∀ X, IsPolyDom P.m₀ (k + 1) X →
      GsSpecStrong (k + 1) (le_refl (k + 1)) X (Tm.gs (k + 1) X)) ∧
    -- `pavingGS`
    (∀ X, IsPolyDom P.m₀ (k + 1) X →
      ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1), ∀ i,
        (((Tm.gs (k + 1) (r '' X)).Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) :
            Set (CTorus d L N₁ m₁ (k + 1))) =
          r '' (((Tm.gs (k + 1) X).Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) :
            Set (CTorus d L N₁ m₁ (k + 1)))) ∧
    -- `analyticE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X →
      AnalyticOnNhd ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Tm.E (k + 1) y X p.1 p.2)
        {p | (xiFieldDom a ν (P.eps d L) :
          FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (Tm.gs (k + 1) X) p.1 p.2}) ∧
    -- `rotE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ, IsRot R →
      ∀ Ψ h,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) (rotField R Ψ) (rotField R h) →
      Tm.E (k + 1) y X (rotField R Ψ) (rotField R h) = Tm.E (k + 1) y X Ψ h) ∧
    -- `eucE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X →
      ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1), ∀ Ψ h,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) (r '' X)) (actField r Ψ) (actField r h) →
      Tm.E (k + 1) (blockBase L (k + 1) (r y)) (r '' X) (actField r Ψ) (actField r h) =
        Tm.E (k + 1) y X Ψ h) ∧
    -- `localE`
    (∀ y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      Tm.E (k + 1) y X Ψ h = Tm.E (k + 1) y X Ψ' h') ∧
    -- `boundE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X → ∀ Ψ h,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      ‖Tm.E (k + 1) y X Ψ h‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) X)) ∧
    -- `eucEloc`, full group
    (∀ hjk : k + 1 ≤ k + 1, ∀ y,
      ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1), ∀ Ψ h,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) hjk) Ψ h →
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) hjk)
        (actField r Ψ) (actField r h) →
      Eloc P.m₀ Tm (k + 1) (blockBase L (k + 1) (r y)) (actField r Ψ) (actField r h) =
        Eloc P.m₀ Tm (k + 1) y Ψ h) ∧
    -- the density (P4 (4.22))
    (∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        p.1 p.2 →
      Edens P.m₀ Tm (k + 1) p.1 p.2 =
        ∑ z ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))).filter (Aligned (L ^ (k + 1))),
          Dz z p) ∧
    -- `analyticM`
    (∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N => Tm.M (k + 1) x X p.1 p.2.1 p.2.2)
        {p | (xiFieldDom a ν (P.eps d L) :
          FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (Tm.gs (k + 1) X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1}) ∧
    -- `rotM`, real matrices
    (∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ, IsRot R →
      (∀ i j, (R i j).im = 0) → ∀ Ψ h g, Def6.l1 g < 1 →
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) (rotField R Ψ) (rotField R h) →
      Tm.M (k + 1) x X (rotField R Ψ) (rotField R h) (rotField R g) =
        R *ᵥ Tm.M (k + 1) x X Ψ h g) ∧
    -- `eucM`
    (∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X →
      ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1), ∀ Ψ h g,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) (r '' X)) (actField r Ψ) (actField r h) →
      Tm.M (k + 1) (r x) (r '' X) (actField r Ψ) (actField r h) (actField r g) =
        Tm.M (k + 1) x X Ψ h g) ∧
    -- `localM`
    (∀ x X Ψ Ψ' h h' g g', (∀ z ∈ X, Ψ z = Ψ' z ∧ h z = h' z ∧ g z = g' z) →
      Tm.M (k + 1) x X Ψ h g = Tm.M (k + 1) x X Ψ' h' g') ∧
    -- `boundM`
    (∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X → ∀ Ψ h g,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h → Def6.l1 g < 1 →
      vn (Tm.M (k + 1) x X Ψ h g) <
        P.c₉ * ((L : ℝ) ^ (k + 1))⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
          Real.exp (-P.κ * sizeJ P.m₀ (k + 1) X)) ∧
    -- `eucMloc`, full group
    (∀ hjk : k + 1 ≤ k + 1, ∀ x,
      ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1), ∀ Ψ h g,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) hjk) Ψ h →
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) hjk)
        (actField r Ψ) (actField r h) →
      Mloc P.m₀ Tm (k + 1) (r x) (actField r Ψ) (actField r h) (actField r g) =
        Mloc P.m₀ Tm (k + 1) x Ψ h g) ∧
    -- the per-site identity of the source terms
    (∀ x (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        p.1 p.2 →
      Mloc P.m₀ Tm (k + 1) x p.1 p.2 g = DM x (p, g)) := by
  -- the two radius sequences and the chart inclusion
  have hεL : P.eps d L (k + 1) ≤ (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L (k + 1) := by
    have he : 0 ≤ P.eps d L (k + 1) := epsSeq_nonneg' L (P.alpha d) P.α₀ hα₀ (k + 1)
    have hK := bgK1_pos d L N
    have hx := one_le_xiC1 d
    have h1 : 1 ≤ (2 * bgK1 d L N + 2) * xiC1 d := by nlinarith
    nlinarith
  have hchart : ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2 :=
    fun Y _ q hq => levelGS_xiFieldDom_sub_localB_eps P HB hα₀ hα hsmall hc0 hc1 (Yp Y) hq
  -- the energy terms as per-label sums
  set TE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ :=
    fun z Y p => ∑ τ ∈ 𝒯E, Tl τ z Y p with hTE
  have hTEloc : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → TE z Y p = TE z Y p' :=
    fun z Y hY p p' hp hp' hpp => Finset.sum_congr rfl fun τ hτ =>
      hTlloc τ hτ z Y hY p p' hp hp' hpp
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ :=
    localClass_termClausesE_centre_chart hN hεL HB Yp hYp Tm hgs cpl hcpl TE
      (fun z z' Y p hzz => Finset.sum_congr rfl fun τ hτ => hTlblock τ hτ z z' Y p hzz)
      (fun z Y hY p hp => Finset.analyticAt_fun_sum _ fun τ hτ => hTlan τ hτ z Y hY p hp)
      hTEloc
      (fun z Y hY hz p hp => (norm_sum_le _ _).trans
        ((Finset.sum_le_sum fun τ hτ => hTlbd τ hτ z Y hY hz p hp).trans (hsum z Y hY hz)))
      (fun z Y hY Q hQ p hp => Finset.sum_congr rfl fun τ hτ => hTlrot τ hτ z Y hY Q hQ p hp)
      AE hAE hE
  obtain ⟨m1, m2, m3, m4, m5⟩ :=
    localClass_termClausesM_chart hN hεL HB Yp hYp Tm hgs cpl hcpl TM hTMan hTMloc hTMsrc hBM
      hTMbd hTMrot AM hAM hM
  have hle : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) ≤
      fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) :=
    symGroupBy_le_of_dvd pow_dvd_cellSide (cellSide_pos (L := L) P.m₀ m₁ (k + 1))
  refine ⟨c1, c2, c3, c4, c5, c6, c7, c8,
    localClass_eucEloc_centre_chart hN Yp Tm cpl hcpl TE hTEloc AE hAE hE hchart Dz hDz hDzblock
      hDzfull,
    fun p hp => localClass_centre_Edens_eq_chart hN Yp Tm cpl hcpl TE hTEloc AE hAE hE hchart Dz
      hDz (fun r hr => hDzfull r (hle hr)) hp,
    m1, m2, m3, m4, m5,
    localClass_eucMloc_site_chart hN Yp Tm cpl hcpl TM hTMloc AM hAM hM hchart DM hDM hDMfull,
    fun x p g hp => localClass_site_Mloc_eq_chart hN Yp Tm cpl hcpl TM hTMloc AM hAM hM hchart DM
      hDM (fun r hr => hDMfull r (hle hr)) x hp g⟩

end NewLevel

end Balaban.Localization
