/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassLocal
public import Mathlib.LinearAlgebra.Projection

/-!
# The local terms on all pairs of fields: extension by completion in the class domain

The class clause `SFTermClauses.localE` asks that the term of a polymer `Y` take the same value at
two pairs of fields `(Ψ, h)`, `(Ψ', h')` equal on `Y`, for **all** pairs of fields, while the clauses
`analyticE`, `boundE`, `rotE`, `eucE` are stated on the class domain `Ξ^c_{k+1}(𝔹; 1, ε_{k+1})` of the
generating set `𝔹 = 𝔹_{k+1}(Y⁺)` of the term.  The recomputed term `E(Y) ∘ clipRaw 𝔹`
(`localB_eTermHat_evTerm_xiFieldDom`) reads the pair on all data sites of `𝔹` (`⊋ Y`); on the class
domain it depends only on the restriction to `Y` (`localB_eTermHat_evTerm_local`).  This file
extends it from the class domain to all pairs.

**No fixed reference configuration.**  Keeping `(Ψ, h)` on `Y` and replacing it off `Y` by a fixed
pair does not stay in the class domain: the domain bounds the gradient of the real background
field (`|∂φ̄| < ε/ℓ`) and its distance to the data (`|Ψ₀ - Qφ| < ε`) on all of `Ω₁(𝔹) ⊋ Y`, so the
data of neighbouring blocks across `∂Y` differ by `O(ε)`, while the domain contains the constant
pairs `(e, e)` for every unit vector `e` (`xiDom_of_close`); for `e` away from the reference the
filled pair jumps by `O(1)` across `∂Y`.  A reference depending on `(Ψ, h)|_Y` would have to place
the background of the filled datum in the domain at the same radius `ε_{k+1}`; the landed
membership results (`xiDom_of_close`, `psiTildeC_subset_xiC`) cover only data near a constant, or
lose the factor `2 K₁ + 2` in the radius.

**The completion.**  The class domain is contained in the layer-constant pairs `layerSub 𝔹`
(`xiDom_mem_layerSub`) and is open relative to them (`xiDom_eventually`), but it is not open: the
clause `analyticE` asks analyticity in a neighbourhood in the space of all pairs.  So the extension
first projects:
* `exists_layerProj`: a linear map `Q` of pairs of fields onto `layerSub 𝔹` that depends only on
  the restriction to `Y` and does not change a layer-constant pair on `Y` (finite-dimensional
  linear algebra, `exists_linearMap_proj_mod`);
* the completion `cpl(Ψ, h)` is a chosen pair of the class domain equal to `Q(Ψ, h)` on `Y`
  (`Classical.epsilon`; an arbitrary pair if there is none).  It depends only on `(Ψ, h)|_Y`, and
  for `(Ψ, h)` in the domain it lies in the domain and equals `(Ψ, h)` on `Y`
  (`fieldDom_completion_spec`).

The extended term is `T ∘ cpl`.  For a term `T` analytic on a field domain contained in
`layerSub 𝔹`, open relative to it, and depending on `Y` only on the domain:
* `fieldDom_completion_extension`: `T ∘ cpl` depends only on `(Ψ, h)|_Y` for all pairs, equals `T`
  on the domain, and is analytic on the domain (near a point `p₀` of the domain,
  `T(cpl p) = T(p₀ + Q p - Q p₀)` by the locality of `T`);
* `xiFieldDom_completion_extension`: the same for the class domain `xiFieldDom`;
* `localB_eTermHat_evTerm_ext`: **the instance at the recomputed term of `Y`** on
  `𝔹 = 𝔹_{k+1}(Y⁺)`: the clause `localE` for all pairs, equality with the recomputed term on the
  class domain, the clause `analyticE`, and the per-`X` bound of `boundE`.

The clauses `rotE`, `eucE` compare values at points of the domain only, where the extension equals
the recomputed term; they transfer without any covariance of the completion.  The values off the
domain are those of the chosen completion and carry no symmetry.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Filter Topology Matrix

section Abstract

/-- **A linear projection onto a subspace modulo a second subspace.**  For subspaces `U`, `K` of a
vector space there is a linear map `Q` with values in `U`, vanishing on `K`, with `Q u - u ∈ K` for
`u ∈ U`: the composite of the quotient map by `K`, a projection of the quotient onto the image of
`U`, and a linear right inverse of `U → V / K` on that image. -/
theorem exists_linearMap_proj_mod {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U Kr : Submodule 𝕜 V) :
    ∃ Q : V →ₗ[𝕜] V, (∀ p, Q p ∈ U) ∧ (∀ p ∈ Kr, Q p = 0) ∧ ∀ u ∈ U, Q u - u ∈ Kr := by
  set f : U →ₗ[𝕜] V ⧸ Kr := Kr.mkQ.comp U.subtype with hf
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict
    (LinearMap.range_rangeRestrict f)
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (LinearMap.range f)
  set π := Submodule.projectionOnto _ q hq with hπ
  refine ⟨U.subtype.comp (g.comp (π.comp Kr.mkQ)), fun p => (g _).2, fun p hp => ?_,
    fun u hu => ?_⟩
  · simp [(Submodule.Quotient.mk_eq_zero Kr).2 hp]
  · rw [← Submodule.Quotient.eq]
    have hmem : Kr.mkQ u ∈ LinearMap.range f := ⟨⟨u, hu⟩, rfl⟩
    have h1 : π (Kr.mkQ u) = ⟨Kr.mkQ u, hmem⟩ :=
      Submodule.projectionOnto_apply_left hq ⟨Kr.mkQ u, hmem⟩
    have h2 := congrArg Subtype.val (LinearMap.congr_fun hg (π (Kr.mkQ u)))
    have h1' : π (Submodule.Quotient.mk u) = ⟨Kr.mkQ u, hmem⟩ := h1
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.codRestrict_apply, hf,
      Submodule.subtype_apply] at h2
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply] at h2 ⊢
    rw [h1'] at h2 ⊢
    exact h2

end Abstract

section Fields

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The projection of pairs of fields onto the layer-constant pairs, seen from `Y`.**  A linear map
`Q` of pairs of fields with values in `layerSub G`, vanishing on the pairs that vanish on `Y` (so
`Q (Ψ, h)` depends only on `(Ψ, h)|_Y`), and equal on `Y` to every layer-constant pair it is applied
to. -/
theorem exists_layerProj (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (Y : Set (CTorus d L N₁ m₁ K)) :
    ∃ Q : (Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) →ₗ[ℂ]
        (Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N),
      (∀ p, Q p ∈ layerSub G) ∧ (∀ p, (∀ z ∈ Y, p.1 z = 0 ∧ p.2 z = 0) → Q p = 0) ∧
        ∀ u ∈ layerSub G, ∀ z ∈ Y, (Q u).1 z = u.1 z ∧ (Q u).2 z = u.2 z := by
  let U : Submodule ℂ (Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) :=
    { carrier := layerSub G
      add_mem' := fun {a b} ha hb =>
        ⟨fun n h1 h2 x hx x' hx' => by
            simp only [Prod.fst_add, Pi.add_apply, ha.1 n h1 h2 x hx x' hx',
              hb.1 n h1 h2 x hx x' hx'],
          fun n h1 h2 x hx x' hx' => by
            simp only [Prod.snd_add, Pi.add_apply, ha.2 n h1 h2 x hx x' hx',
              hb.2 n h1 h2 x hx x' hx']⟩
      zero_mem' := ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
      smul_mem' := fun c a ha =>
        ⟨fun n h1 h2 x hx x' hx' => by
            simp only [Prod.smul_fst, Pi.smul_apply, ha.1 n h1 h2 x hx x' hx'],
          fun n h1 h2 x hx x' hx' => by
            simp only [Prod.smul_snd, Pi.smul_apply, ha.2 n h1 h2 x hx x' hx']⟩ }
  let Kr : Submodule ℂ (Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) :=
    { carrier := {p | ∀ z ∈ Y, p.1 z = 0 ∧ p.2 z = 0}
      add_mem' := fun {a b} ha hb z hz => by
        simp [(ha z hz).1, (ha z hz).2, (hb z hz).1, (hb z hz).2]
      zero_mem' := fun z _ => ⟨rfl, rfl⟩
      smul_mem' := fun c a ha z hz => by
        simp [(ha z hz).1, (ha z hz).2] }
  obtain ⟨Q, hQU, hQK, hQid⟩ := exists_linearMap_proj_mod U Kr
  refine ⟨Q, hQU, fun p hp => hQK p hp, fun u hu z hz => ?_⟩
  obtain ⟨e1, e2⟩ := hQid u hu z hz
  exact ⟨sub_eq_zero.1 e1, sub_eq_zero.1 e2⟩

/-- **The class domain lies in the layer-constant pairs**: a pair of `Ξ^c_n(G; 1, ε)` agrees on
`Ω₁` with the complex datum of its witness, which is constant on the blocks of every layer. -/
theorem xiDom_mem_layerSub {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
    {n : ℕ} {ε : ℝ} {p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N}
    (hp : XiDom G a ν n ε p.1 p.2) : p ∈ layerSub G := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hΨ, hh, hXi⟩ := hp
  obtain ⟨-, -, -, Dc, -, hC, -, -⟩ := hXi
  refine ⟨fun n h1 h2 x hx x' hx' => funext fun i => ?_,
    fun n h1 h2 x hx x' hx' => funext fun i => ?_⟩
  · have hx1 : x ∈ G.Ω 1 := G.layer_subset h1 h2 hx
    have hx'1 : x' ∈ G.Ω 1 := blk_subset_Ω G h1 h2 hx hx'
    rw [hΨ x' i, hΨ x i, ← hC.1 x' ((mem_dataSites G).2 (Or.inl hx'1)) i,
      ← hC.1 x ((mem_dataSites G).2 (Or.inl hx1)) i, Dc.Ψ_layerConst n h1 h2 x hx x' hx']
  · have hx1 : x ∈ G.Ω 1 := G.layer_subset h1 h2 hx
    have hx'1 : x' ∈ G.Ω 1 := blk_subset_Ω G h1 h2 hx hx'
    rw [hh x' i, hh x i, ← hC.2 x' hx'1 i, ← hC.2 x hx1 i,
      Dc.h_layerConst n h1 h2 x hx x' hx']

/-- **The completion of a pair of fields in a field domain, at a polymer `Y`.**  The completion
`cpl (Ψ, h)` is a chosen pair of the domain `Dom.dom j G` equal on `Y` to the projection
`Q (Ψ, h)` of `exists_layerProj`.  It depends only on `(Ψ, h)|_Y`; for a pair of the domain it lies
in the domain and equals the pair on `Y`. -/
theorem fieldDom_completion_spec (Dom : FieldDom d L N₁ m₁ K N ϱ) (j : ℕ)
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (Y : Set (CTorus d L N₁ m₁ K))
    (c : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N)
    (hc : ∀ p, c p = Classical.epsilon (fun q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
      Dom.dom j G q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) G Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) G Y) p).2 z))
    (hDL : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G p.1 p.2 → p ∈ layerSub G) :
    (∀ Ψ Ψ' h h' : Fld d L N₁ m₁ K N, (∀ x ∈ Y, Ψ x = Ψ' x ∧ h x = h' x) →
      c (Ψ, h) = c (Ψ', h')) ∧
    ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G p.1 p.2 →
      Dom.dom j G (c p).1 (c p).2 ∧ ∀ z ∈ Y, (c p).1 z = p.1 z ∧ (c p).2 z = p.2 z := by
  obtain ⟨hQU, hQK, hQid⟩ := Classical.choose_spec (exists_layerProj (N := N) G Y)
  set Q := Classical.choose (exists_layerProj (N := N) G Y) with hQ
  refine ⟨fun Ψ Ψ' h h' hY => ?_, fun p hp => ?_⟩
  · have hQe : Q (Ψ, h) = Q (Ψ', h') := by
      have h0 := hQK ((Ψ, h) - (Ψ', h')) fun z hz => by
        simp [(hY z hz).1, (hY z hz).2]
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    rw [hc, hc, hQe]
  · have hex : ∃ q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Q p).1 z ∧ q.2 z = (Q p).2 z :=
      ⟨p, hp, fun z hz => ⟨(hQid p (hDL p hp) z hz).1.symm, (hQid p (hDL p hp) z hz).2.symm⟩⟩
    obtain ⟨h1, h2⟩ := Classical.epsilon_spec hex
    rw [hc]
    refine ⟨h1, fun z hz => ⟨?_, ?_⟩⟩
    · rw [(h2 z hz).1, (hQid p (hDL p hp) z hz).1]
    · rw [(h2 z hz).2, (hQid p (hDL p hp) z hz).2]

/-- `p + (a - b)` is layer constant if `p`, `a`, `b` are. -/
theorem add_sub_mem_layerSub {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {p a b : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N} (hp : p ∈ layerSub G) (ha : a ∈ layerSub G)
    (hb : b ∈ layerSub G) : p + (a - b) ∈ layerSub G :=
  ⟨fun n h1 h2 x hx x' hx' => by
      simp only [Prod.fst_add, Prod.fst_sub, Pi.add_apply, Pi.sub_apply,
        hp.1 n h1 h2 x hx x' hx', ha.1 n h1 h2 x hx x' hx', hb.1 n h1 h2 x hx x' hx'],
    fun n h1 h2 x hx x' hx' => by
      simp only [Prod.snd_add, Prod.snd_sub, Pi.add_apply, Pi.sub_apply,
        hp.2 n h1 h2 x hx x' hx', ha.2 n h1 h2 x hx x' hx', hb.2 n h1 h2 x hx x' hx']⟩


open Filter Topology in
/-- **The completion extension with a parameter** (`fieldDom_completion_extension`, analyticity
clause, with an extra analytic parameter `g`).  Let the domain `Dom.dom j G` lie in the
layer-constant pairs and be open relative to them, let `T` be analytic on the domain times a set
`Sp` of parameters, and for every parameter let `T` depend only on the restriction to `Y` for
pairs of the domain.  Then `(p, g) ↦ T (cpl p, g)` is analytic on the domain times `Sp`.  Near a
point `p₀` of the domain `T (cpl p, g) = T (p₀ + Q p - Q p₀, g)`, as in the landed proof for a
function of the pair alone. -/
theorem fieldDom_completion_analytic_param {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Dom : FieldDom d L N₁ m₁ K N ϱ) (j : ℕ)
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (Y : Set (CTorus d L N₁ m₁ K))
    (c : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N)
    (hc : ∀ p, c p = Classical.epsilon (fun q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
      Dom.dom j G q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) G Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) G Y) p).2 z))
    (hDL : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G p.1 p.2 → p ∈ layerSub G)
    (hDo : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G p.1 p.2 →
      ∀ᶠ q in 𝓝[layerSub G] p, Dom.dom j G q.1 q.2)
    {Sp : Set P}
    (T : (Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) × P → F)
    (hT : AnalyticOnNhd ℂ T ({p | Dom.dom j G p.1 p.2} ×ˢ Sp))
    (hloc : ∀ p p' : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G p.1 p.2 →
      Dom.dom j G p'.1 p'.2 → (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → ∀ g, T (p, g) = T (p', g)) :
    AnalyticOnNhd ℂ (fun q : (Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) × P => T (c q.1, q.2))
      ({p | Dom.dom j G p.1 p.2} ×ˢ Sp) := by
  rintro ⟨p₀, g₀⟩ ⟨hp₀, hg₀⟩
  obtain ⟨hQU, hQK, hQid⟩ := Classical.choose_spec (exists_layerProj (N := N) G Y)
  set Q := Classical.choose (exists_layerProj (N := N) G Y) with hQ
  have hQc : Continuous Q := LinearMap.continuous_of_finiteDimensional Q
  have hφc : Continuous (fun p => p₀ + (Q p - Q p₀)) :=
    continuous_const.add (hQc.sub continuous_const)
  have hTφ : Tendsto (fun p => p₀ + (Q p - Q p₀)) (𝓝 p₀) (𝓝[layerSub G] p₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun p =>
      add_sub_mem_layerSub (hDL p₀ hp₀) (hQU p) (hQU p₀)⟩
    have h := hφc.tendsto p₀
    simp only [sub_self, add_zero] at h
    exact h
  have hφa : AnalyticAt ℂ (fun p => p₀ + (Q p - Q p₀)) p₀ := by
    have hQa : AnalyticAt ℂ (fun p => Q p) p₀ := by
      have := (LinearMap.toContinuousLinearMap Q).analyticAt p₀
      simpa using this
    exact analyticAt_const.add (hQa.sub analyticAt_const)
  have hTa : AnalyticAt ℂ (fun q : (Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) × P =>
      T (p₀ + (Q q.1 - Q p₀), q.2)) (p₀, g₀) :=
    AnalyticAt.comp_of_eq (g := T) (f := fun q : (Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) × P =>
      (p₀ + (Q q.1 - Q p₀), q.2)) (y := (p₀, g₀)) (hT (p₀, g₀) ⟨hp₀, hg₀⟩)
      ((hφa.comp_of_eq analyticAt_fst rfl).prod analyticAt_snd) (by simp)
  refine hTa.congr ?_
  have hev : ∀ᶠ p in 𝓝 p₀, Dom.dom j G (p₀ + (Q p - Q p₀)).1 (p₀ + (Q p - Q p₀)).2 :=
    hTφ.eventually (hDo p₀ hp₀)
  have hev2 : ∀ᶠ q in 𝓝 (p₀, g₀), Dom.dom j G (p₀ + (Q q.1 - Q p₀)).1
      (p₀ + (Q q.1 - Q p₀)).2 := (continuous_fst.tendsto (p₀, g₀)).eventually hev
  filter_upwards [hev2] with q hq
  have hY : ∀ z ∈ Y, (p₀ + (Q q.1 - Q p₀)).1 z = (Q q.1).1 z ∧
      (p₀ + (Q q.1 - Q p₀)).2 z = (Q q.1).2 z :=
    fun z hz => by
      obtain ⟨e1, e2⟩ := hQid p₀ (hDL p₀ hp₀) z hz
      simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub, Pi.add_apply,
        Pi.sub_apply, e1, e2]
      exact ⟨by abel, by abel⟩
  have hex : ∃ q' : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G q'.1 q'.2 ∧ ∀ z ∈ Y,
      q'.1 z = (Q q.1).1 z ∧ q'.2 z = (Q q.1).2 z := ⟨_, hq, hY⟩
  obtain ⟨h1, h2⟩ := Classical.epsilon_spec hex
  rw [← hc] at h1 h2
  exact hloc _ _ hq h1 (fun z hz => ⟨((hY z hz).1.trans (h2 z hz).1.symm),
    ((hY z hz).2.trans (h2 z hz).2.symm)⟩) q.2

/-- **The extension of a term from a field domain by completion.**  Let the domain `Dom.dom j G` lie
in the layer-constant pairs and be open relative to them, and let `T` be analytic on it and depend
only on the restriction to `Y` for pairs of the domain.  Then `T ∘ cpl` depends only on the
restriction to `Y` for **all** pairs of fields (the form of the clause `localE`), equals `T` on the
domain, and is analytic on the domain (the form of the clause `analyticE`).  Near a point `p₀` of
the domain, `p₀ + Q p - Q p₀` is a pair of the domain equal on `Y` to `Q p`, so
`T (cpl p) = T (p₀ + Q p - Q p₀)`, analytic in `p`. -/
theorem fieldDom_completion_extension {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Dom : FieldDom d L N₁ m₁ K N ϱ) (j : ℕ)
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (Y : Set (CTorus d L N₁ m₁ K))
    (c : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N)
    (hc : ∀ p, c p = Classical.epsilon (fun q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
      Dom.dom j G q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) G Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) G Y) p).2 z))
    (hDL : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G p.1 p.2 → p ∈ layerSub G)
    (hDo : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G p.1 p.2 →
      ∀ᶠ q in 𝓝[layerSub G] p, Dom.dom j G q.1 q.2)
    (T : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F)
    (hT : AnalyticOnNhd ℂ T {p | Dom.dom j G p.1 p.2})
    (hloc : ∀ p p' : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G p.1 p.2 →
      Dom.dom j G p'.1 p'.2 → (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → T p = T p') :
    (∀ Ψ Ψ' h h' : Fld d L N₁ m₁ K N, (∀ x ∈ Y, Ψ x = Ψ' x ∧ h x = h' x) →
      T (c (Ψ, h)) = T (c (Ψ', h'))) ∧
    (∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G p.1 p.2 → T (c p) = T p) ∧
    AnalyticOnNhd ℂ (fun p => T (c p)) {p | Dom.dom j G p.1 p.2} := by
  obtain ⟨c1, c2⟩ := fieldDom_completion_spec Dom j G Y c hc hDL
  obtain ⟨hQU, hQK, hQid⟩ := Classical.choose_spec (exists_layerProj (N := N) G Y)
  set Q := Classical.choose (exists_layerProj (N := N) G Y) with hQ
  refine ⟨fun Ψ Ψ' h h' hY => by rw [c1 Ψ Ψ' h h' hY], fun p hp =>
    hloc _ _ (c2 p hp).1 hp (c2 p hp).2, ?_⟩
  have h := fieldDom_completion_analytic_param (P := ℂ) (Sp := Set.univ) Dom j G Y c hc hDL hDo
    (fun q => T q.1) (fun q hq => (hT q.1 hq.1).comp_of_eq analyticAt_fst rfl)
    (fun p p' hp hp' hY _ => hloc p p' hp hp' hY)
  intro p₀ hp₀
  exact (h (p₀, 0) ⟨hp₀, Set.mem_univ _⟩).comp_of_eq
    (analyticAt_id.prod analyticAt_const) rfl

/-- **The extension by completion on the class domain `xiFieldDom`** (`xiDom_mem_layerSub`,
`xiDom_eventually`). -/
theorem xiFieldDom_completion_extension {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {a : ℕ → ℝ} {ν : ℝ} {εseq : ℕ → ℝ} (H : BgHyp d L K ϱ a ν) (j : ℕ)
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (Y : Set (CTorus d L N₁ m₁ K))
    (c : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N)
    (hc : ∀ p, c p = Classical.epsilon (fun q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j G q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) G Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) G Y) p).2 z))
    (T : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F)
    (hT : AnalyticOnNhd ℂ T {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j G p.1 p.2})
    (hloc : ∀ p p' : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j G p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j G p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → T p = T p') :
    (∀ Ψ Ψ' h h' : Fld d L N₁ m₁ K N, (∀ x ∈ Y, Ψ x = Ψ' x ∧ h x = h' x) →
      T (c (Ψ, h)) = T (c (Ψ', h'))) ∧
    (∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j G p.1 p.2 → T (c p) = T p) ∧
    AnalyticOnNhd ℂ (fun p => T (c p))
      {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ K N ϱ).dom j G p.1 p.2} :=
  fieldDom_completion_extension _ j G Y c hc (fun _ hp => xiDom_mem_layerSub hp)
    (fun _ hp => xiDom_eventually H hp) T hT hloc

end Fields

section LocalB

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a₁ ν : ℝ}

open MeasureTheory

/-- **The local E-term of `Y` on all pairs of fields** (P3 (4.46)-(4.47); the clauses `localE`,
`analyticE` and the per-`X` bound of `boundE` of the local successor class).  Let `T` be the term
of the polymer `Y` recomputed on `𝔹 = 𝔹_{k+1}(Y⁺) = localB (k + 1) … Y⁺`
(`localB_eTermHat_evTerm_xiFieldDom` at `t = k + 1`) and `cpl` the completion in the class domain
`Ξ^c_{k+1}(𝔹; 1, ε_{k+1})` at `Y` (`fieldDom_completion_spec`).  The hypotheses are those of
`localB_eTermHat_evTerm_xiFieldDom` and the two properties `hσ0`, `hσY` of the parameter map of
`localB_eTermHat_evTerm_local`.  Then `T ∘ cpl`
1. takes the same value at two pairs of fields equal on `Y` (all pairs: `localE`);
2. equals `T` on the class domain (so `rotE`, `eucE`, stated on the domain, transfer from `T`);
3. is analytic on the class domain (`analyticE`);
4. is bounded there by `Eb γ(K) e^{-κ₀ d^{cov,1}_{j'}(X) - 2 κ d̃^{cov}(Y)}`. -/
theorem localB_eTermHat_evTerm_ext {ι : Type*} [DecidableEq ι] [Fintype ι] {ϱa : ℝ}
    {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa} {cI : ι → ℕ × CTorus d L N₁ m₁ (k + 1)}
    {m₀ j' : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} (hcov : CovSetup Ga m₀ j' X 𝒦X)
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hcI : ∀ i, cI i ∈ cubeIdx Ga) (hcinj : Function.Injective cI)
    (hdisj : ∀ i, Disjoint (Pset m₁ (cI i)) (X1 Ga m₀ j' 𝒦X))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j' 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j') E₀ = treeLenCovOne m₀ j' X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec) (hEb0 : 0 ≤ Eb)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) (hk : k + 1 ≤ k + 1)
    (Yp : Set (CTorus d L N₁ m₁ (k + 1))) (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG) (hk1 : 1 ≤ k)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    (HBp : BgHyp d L (k + 1) (minSep L (L ^ m₁)) (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν)
    (hP : Precedes Gk (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1)
      (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {κ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ (4 * d * (L : ℝ) ^ 3 + L) eps δ₃)
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 →
      ∀ y : CTorus d L N₁ m₁ (k + 1), Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ * (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L
          (L ^ m₁)))).spacing x → y ∈ X₁f)
    {j : ℕ} (hj : j ≤ k + 1) {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L
      (L ^ m₁)))) Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    (hHm : Hm.Ω (k + 1) = ∅)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hE : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {F₁ : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
      × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData
      (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N,
      InUnionDomainC (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N), (∀ P, ‖s P‖
        < Real.exp κ) →
      InUnionDomainC (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D → ∀ (φ : (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1
          × Fin N → ℂ)
        (α : (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
      × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
      × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L
          (L ^ m₁))))) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) Hm
          (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) Hm
            (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L
      (L ^ m₁)))))} (hσan : ∀ w, AnalyticAt ℂ σ w)
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf (GsSpec.localB (k + 1) hk Yp
      (le_refl (minSep L (L ^ m₁))))).cubeIdx),
      P ∉ (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).parCubes X₁f
        → σ w ⟨P, hP⟩ = 1)
    (hσ0 : ∀ w, ∀ P ∈ (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^
      m₁))))).cubeIdx, P.2 ∉ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) →
      Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (σ w) P = 0)
    (hσY : ∀ C ∈ connFams cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Y, ∀ w ∈ supN C (Real.exp κ),
      ∀ P ∈ (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx,
        Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (σ w) P ≠ 0
          →
        ∀ y, SameCell (L ^ (P.1 + m₁)) y P.2 → y ∈ Y)
    {γ : Measure (unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)}
      {K : Set (unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)}
    (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ) (hγ : γ K < ⊤)
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
        ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j' X))
    {εseq : ℕ → ℝ} (hεseq : εseq (k + 1) ≤ eps)
    (T : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hT : ∀ p, T p =
      evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X)
            (fun (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ) =>
            ∫ ψ in K,
              eTermFun (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj Hm
                (compWeight L a₁) Fk E (F₁ (σ w, Θ))
          (Sol (σ w, flEdat (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Hm (F₁ (σ w, Θ)) Θ.1
            (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
                (cc • (decCovSqrt (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (compWeight L a₁) a₁ ν
                  (F₁ (σ w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L
                    (L ^ m₁))))) (σ w))
                  (barField (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁
                    (σ w, Θ)).1) (unitQ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                      (unitP (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                        (ψ r : ℂ))))
                  (⟨unitBlock x, h⟩, i)
              else 0))).1
          (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
                (cc • (decCovSqrt (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (compWeight L a₁) a₁ ν
                  (F₁ (σ w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L
                    (L ^ m₁))))) (σ w))
                  (barField (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁
                    (σ w, Θ)).1) (unitQ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                      (unitP (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                        (ψ r : ℂ))))
                  (⟨unitBlock x, h⟩, i)
              else 0) ∂γ) Y (clipRaw (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) p))
    (cpl : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ p, cpl p = Classical.epsilon (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Y) p).2 z)) :
    (∀ Ψ Ψ' h h' : Fld d L N₁ m₁ (k + 1) N, (∀ x ∈ Y, Ψ x = Ψ' x ∧ h x = h' x) →
      T (cpl (Ψ, h)) = T (cpl (Ψ', h'))) ∧
    (∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) p.1 p.2 → T (cpl p) = T p) ∧
    AnalyticOnNhd ℂ (fun p => T (cpl p)) {p | (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) p.1 p.2} ∧
    ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      ‖T (cpl p)‖ ≤ Eb * (γ K).toReal *
        Real.exp (-κ₀ * treeLenCovOne m₀ j' X - 2 * κdec * treeLenCov Ga m₀ Y) := by
  have hW := localB_eTermHat_evTerm_xiFieldDom hcov hd hL hcI hcinj hdisj hopt hκ₀ hκdec hEb0 Y
    hb₁ hbC hk Yp hN₁ hMM hag hS hk1 ha₁ ha₂ HBp HBk HBj hP hq colk colj hκ hM hκκ h1 hlog hMX
    hnum dsX₀ hN hj hF hHm hFkan hFk hE hmarD hαD hsm cc hcψ hδ₁ hF₁an hF₁ hSolan hSol hσan hσκ
    hσ1 hKc hKb hγ hEb hεseq
  have hTf := funext hT
  have hA : AnalyticOnNhd ℂ T {p | (xiFieldDom (compWeight L a₁) ν εseq :
      FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
      (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) p.1 p.2} := by
    rw [hTf]; exact hW.1
  have hloc : ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → T p = T p' := by
    intro p p' hp hp' hpp
    rw [hT p, hT p']
    exact localB_eTermHat_evTerm_local (X₁ := X1 Ga m₀ j' 𝒦X) Y hk1 hk Yp hN₁ hMM hag hS ha₁ ha₂
      HBp hP colk hκ hM hMX hnum dsX₀ hN hF hHm Fk E hmarD hαD hsm cc hcψ hδ₁ hF₁ hSol hσκ hσ1
      hσ0 hσY hKc hKb hεseq hp hp' hpp
  obtain ⟨e1, e2, e3⟩ := xiFieldDom_completion_extension HBp (k + 1) (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Y cpl hcpl T hA hloc
  refine ⟨e1, e2, e3, fun p hp => ?_⟩
  rw [e2 p hp, hT p]
  exact hW.2 p hp

end LocalB

end Balaban.Localization
