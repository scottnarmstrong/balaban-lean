/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The source terms `ℳ` on the local chart: analyticity, locality and the bound

The term of a polymer `Y` of level `k + 1` coming from an inherited source term `ℳ^{(j)}_i(y, X)`
is, for a fixed component `i`, the term of `LocalHatTerm.lean` with the old-term functional
`E_g(r) = ℳ^{(j)}_i(y, X; r.1, r.2, g)`, which depends on the source `g` as a parameter.  The clause
`analyticM` asks analyticity jointly in the fields and in `g`, and `localM` asks that the term not
change when `(Ψ, h, g)` is changed off `Y`, for all fields and all sources; the landed results for
the energy terms are analytic in the fields for one fixed functional, and local for fixed `g`.  This
file carries a parameter `g` through the chain without re-proving it.

* `analyticOnNhd_of_forall_clm`, `analyticOnNhd_mem_of_transfer`: a map into a finite-dimensional
  space is analytic when every continuous linear functional of it is; if the bound `0` of every
  function bounded by `0` on a set `Dm` transfers, the values of the map lie in `Dm`.  Applied to
  the triple map `((Θ, ψ̂), w) ↦ (F₁(σ w, Θ), Sol(σ w, …), (Θ, ψ'))` (from
  `fanLocalHat_analytic_cover`, `fanLocalHat_norm_le_cover`) and to `D2raw ∘ d1Triple` (from
  `localB_eTermFun_analytic`, `localB_eTermFun_bound`), the maps are analytic and take values in
  the realizable triples, resp. in the chart of the old term, with no change to the landed proofs;
* `localB_mTermHat_integral_param`: the `ψ̂`-integral of `E (·) g` is analytic in `((Θ, g), w)`
  on the chart times `Sg` times the polydisc, and bounded by `Bd γ(K)`;
* `localB_mTermHat_evTerm_xiFieldDom`: `analyticM` (jointly in the pair of fields and the source,
  on the class domain times `Sg`) and the per-label bound of `boundM`, for the term of `Y` read
  through the cut-off `clipRaw 𝔹`, `E` analytic on the chart times `Sg`;
* `evTerm_congr_fun`, `evTerm_source_congr`: the term depends on a source parameter only through
  its restriction to `X ⊆ X₁ ⊆ Y` (it vanishes unless `X₁ ⊆ Y`);
* `localB_mTermHat_evTerm_local`: exact locality of the term on the class domain, for every source;
* `fieldDom_completion_analytic_param`: the completion extension with an analytic parameter
  (`fieldDom_completion_extension`, analyticity clause, for a function of the pair and a
  parameter; the landed statement is the case without parameter, which this file does not edit);
* `localB_mTermHat_evTerm_ext_loc`, `…_ext_an`, `…_ext`: the term composed with the completion
  `cpl` at `Y`: the same value at two triples `(Ψ, h, g)`, `(Ψ', h', g')` equal on `Y` (all fields and
  all sources: `localM`), equal to the recomputed term on the class domain (so `rotM`, `eucM`
  transfer), analytic on the class domain times `Sg` (`analyticM`), and bounded there;
* `analyticOnNhd_vec_sum`, `norm_sum_evTerm_vn_le_boundM`: the sum over old labels, componentwise,
  and in the Euclidean norm of `ℂ^N` with the factor `√N` (`boundM`, with `≤`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Finset Matrix MeasureTheory
section Transfer

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- A map into a finite-dimensional space is analytic on a set when all its continuous linear
functionals are. -/
theorem analyticOnNhd_of_forall_clm {S : Set X} {F : X → V}
    (h : ∀ ℓ : V →L[ℂ] ℂ, AnalyticOnNhd ℂ (fun x => ℓ (F x)) S) : AnalyticOnNhd ℂ F S := by
  classical
  intro x hx
  let b := Module.finBasis ℂ V
  have hF : F = fun y => ∑ i, (LinearMap.toContinuousLinearMap (b.coord i) (F y)) • b i := by
    funext y
    simp [Module.Basis.sum_repr]
  rw [hF]
  exact Finset.analyticAt_fun_sum _ fun i _ => (h _ x hx).smul analyticAt_const

theorem analyticOnNhd_mem_of_transfer {S : Set X} {Dm : Set V} {F : X → V}
    (hA : ∀ Φ : V → ℂ, AnalyticOnNhd ℂ Φ Dm → AnalyticOnNhd ℂ (fun x => Φ (F x)) S)
    (hB : ∀ Φ : V → ℂ, (∀ v ∈ Dm, ‖Φ v‖ ≤ 0) → ∀ x ∈ S, ‖Φ (F x)‖ ≤ 0) :
    AnalyticOnNhd ℂ F S ∧ ∀ x ∈ S, F x ∈ Dm := by
  classical
  refine ⟨analyticOnNhd_of_forall_clm fun ℓ => hA ℓ (ℓ.analyticOnNhd _), fun x hx => ?_⟩
  by_contra hn
  have := hB (fun v => if v ∈ Dm then 0 else 1) (fun v hv => by simp [hv]) x hx
  simp [hn] at this
  norm_num at this

end Transfer

section FinDim

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}

theorem finDim_rawData : FiniteDimensional ℂ (RawData d L (N₁ * L ^ m₁) (k + 1) N) :=
  inferInstance

theorem finDim_fld : FiniteDimensional ℂ (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :=
  inferInstance

theorem finDim_omega (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) :
    FiniteDimensional ℂ (G.Ω 1 × Fin N → ℂ) := inferInstance

theorem finDim_omega' (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) :
    FiniteDimensional ℂ (G.Ω 1 → ℂ) := inferInstance

theorem finDim_triple (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm) :
    FiniteDimensional ℂ (((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))) := by
  have := finDim_rawData (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N)
  have := finDim_fld (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N)
  have := finDim_omega (N := N) G
  have := finDim_omega' G
  have := finDim_omega (N := N) Hm
  exact inferInstance

end FinDim

section EvCongr

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {c : ι → ℕ × CTorus d L N₁ m₁ K} {U U' : Type*}

/-- The term `𝓔(X, Y)` at an argument depends on the family only through its value there. -/
theorem evTerm_congr_fun {X₁ Y : Set (CTorus d L N₁ m₁ K)} {F : U → (ι → ℂ) → ℂ}
    {F' : U' → (ι → ℂ) → ℂ} {u : U} {u' : U'} (h : F u = F' u') :
    evTerm c G m₀ X₁ F Y u = evTerm c G m₀ X₁ F' Y u' := by
  unfold evTerm
  rw [h]

open Classical in
/-- **A term `𝓔(X, Y)` depends on a parameter `g` only through `g|_X ⊆ g|_{X₁}` and vanishes unless
`X₁ ⊆ Y`.**  If the family `F (u, g)` does not change when `g` is changed off `X ⊆ X₁`, then
`evTerm … Y (u, g)` does not change when `g` is changed off `Y`: if `X₁ ⊆ Y` the two sources agree
on `X`, and otherwise both terms are `0` (`evTerm_eq_zero_of_not_subset`). -/
theorem evTerm_source_congr {X X₁ Y : Set (CTorus d L N₁ m₁ K)} (hXX : X ⊆ X₁) {V : Type*}
    {P : Type*} {F : V × (CTorus d L N₁ m₁ K → P) → (ι → ℂ) → ℂ}
    (hF : ∀ (g g' : CTorus d L N₁ m₁ K → P), (∀ z ∈ X, g z = g' z) → ∀ u w,
      F (u, g) w = F (u, g') w)
    {g g' : CTorus d L N₁ m₁ K → P} (hg : ∀ z ∈ Y, g z = g' z) (u : V) :
    evTerm c G m₀ X₁ F Y (u, g) = evTerm c G m₀ X₁ F Y (u, g') := by
  by_cases hXY : X₁ ⊆ Y
  · exact evTerm_congr_fun (funext (hF g g' (fun z hz => hg z (hXY (hXX hz))) u))
  · rw [evTerm_eq_zero_of_not_subset hXY, evTerm_eq_zero_of_not_subset hXY]

end EvCongr

section CompletionParam

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

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

end CompletionParam

section ParamM

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a₁ ν : ℝ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {t : ℕ} (ht : t ≤ k + 1)
  (Yp : Set (CTorus d L N₁ m₁ (k + 1))) (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
  (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {c BG : ℝ}
  (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG) (hk1 : 1 ≤ k)
  (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
  (HBp : BgHyp d L (k + 1) (minSep L (L ^ m₁)) (compWeight L a₁) ν)
  (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
  (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν)

set_option hygiene false in
local notation "𝔹ₗ" => GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))

variable (hP : Precedes Gk 𝔹ₗ) (hq : Precedes Gj Gk)
  (colk : ∀ z ∈ collar Gk, z ∈ (𝔹ₗ).Ω 1) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
  {κ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hnum : ChainNum d L N m₁ BG κ (4 * d * (L : ℝ) ^ 3 + L) eps δ₃)
  {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
  (hN : ∀ x ∈ X₀, x ∈ (𝔹ₗ).Ω 1 →
    ∀ y : CTorus d L N₁ m₁ (k + 1), Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
      (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ * (𝔹ₗ).spacing x → y ∈ X₁f)
  {j : ℕ} (hj : j ≤ k + 1) {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
  (hF : FlSetting N 𝔹ₗ Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
  (hHm : Hm.Ω (k + 1) = ∅)
  {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
  (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
    InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
  (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
    Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
      bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
  {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
  (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
  {F₁ : Dec2.DecParams (coverOf 𝔹ₗ) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
    ((𝔹ₗ).Ω 1 × Fin N → ℂ) × ((𝔹ₗ).Ω 1 → ℂ)}
  (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData 𝔹ₗ N,
    InUnionDomainC 𝔹ₗ (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
  (hF₁ : ∀ (s : Dec2.DecParams (coverOf 𝔹ₗ)) (D : BgData 𝔹ₗ N), (∀ P, ‖s P‖ < Real.exp κ) →
    InUnionDomainC 𝔹ₗ (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (𝔹ₗ).Ω 1 × Fin N → ℂ)
      (α : (𝔹ₗ).Ω 1 → ℂ),
      Dec2.IsDecBg (coverOf 𝔹ₗ) 𝔹ₗ (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
      F₁ (s, rawOf D) = (φ, α))
  {Sol : Dec2.DecParams (coverOf 𝔹ₗ) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
  (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
    StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
  (hSol : ∀ p : Dec2.DecParams (coverOf 𝔹ₗ) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
    StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
      (Sol p).1 = dphi Hm (Dec2.decG (coverOf 𝔹ₗ) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
        (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
      Dec2.DecFixed (coverOf 𝔹ₗ) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
        (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
      Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
      Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
      SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
      (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
        Dec2.DecFixed (coverOf 𝔹ₗ) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
  {σ : (ι → ℂ) → Dec2.DecParams (coverOf 𝔹ₗ)} (hσan : ∀ w, AnalyticAt ℂ σ w)
  (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
  (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf 𝔹ₗ).cubeIdx),
    P ∉ (coverOf 𝔹ₗ).parCubes X₁f → σ w ⟨P, hP⟩ = 1)
  {γ : Measure (unitPts 𝔹ₗ × Fin N → ℝ)} {K : Set (unitPts 𝔹ₗ × Fin N → ℝ)}
  (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ) (hγ : γ K < ⊤)

include hb₁ hbC hN₁ hMM hag hS hk1 ha₁ ha₂ HBp HBk HBj hP hq colk colj hκ hM hMX hnum dsX₀ hN hj
  hF hHm hFkan hFk hmarD hαD hsm hcψ hδ₁ hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hKc hKb hγ

omit [DecidableEq ι] in
theorem localB_mTermHat_integral_param {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] {Sg : Set G}
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → G → ℂ}
    (hE : AnalyticOnNhd ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × G => E q.1 q.2)
      (XiCRaw Gj (compWeight L a₁) ν j b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ×ˢ Sg))
    {Bd : ℝ} (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ∀ g ∈ Sg, ‖E r g‖ ≤ Bd)
    (Fi : (RawData d L (N₁ * L ^ m₁) (k + 1) N × G) × (ι → ℂ) → ℂ)
    (hFi : ∀ q, Fi q =
        ∫ ψ in K,
          eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk (fun r => E r q.1.2) (F₁ (σ q.2, q.1.1))
        (Sol (σ q.2, flEdat 𝔹ₗ Hm (F₁ (σ q.2, q.1.1)) q.1.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ q.2, q.1.1)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ q.2))
                (barField 𝔹ₗ q.1.1.1 (F₁ (σ q.2, q.1.1)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (q.1.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ q.2, q.1.1)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ q.2))
                (barField 𝔹ₗ q.1.1.1 (F₁ (σ q.2, q.1.1)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ) :
    AnalyticOnNhd ℂ Fi ((XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps ×ˢ Sg) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) ∧
      ∀ q ∈ (XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps ×ˢ Sg) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ‖Fi q‖ ≤ Bd * (γ K).toReal := by
  classical
  have hcd := localB_coverData ht Yp hN₁ hMM hag HBp
  have ha₁0 : 0 < a₁ := by linarith
  have hfdT := finDim_triple (N := N) 𝔹ₗ Hm
  have hfdR := finDim_rawData (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N)
  -- the triple map of the local hat variable
  obtain ⟨Tmap, hTmap⟩ : ∃ Tmap : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts 𝔹ₗ × Fin N → ℂ)) × (ι → ℂ) →
      (((𝔹ₗ).Ω 1 × Fin N → ℂ) × ((𝔹ₗ).Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)),
      ∀ p, Tmap p = (F₁ (σ p.2, p.1.1),
        (Sol (σ p.2, flEdat 𝔹ₗ Hm (F₁ (σ p.2, p.1.1)) p.1.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν (F₁ (σ p.2, p.1.1)).2
                (Dec2.extS (coverOf 𝔹ₗ) (σ p.2)) (barField 𝔹ₗ p.1.1.1 (F₁ (σ p.2, p.1.1)).1)
                (unitQ 𝔹ₗ) (unitP 𝔹ₗ) *ᵥ p.1.2)) (⟨unitBlock x, h⟩, i)
            else 0))).1,
        (p.1.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν (F₁ (σ p.2, p.1.1)).2
                (Dec2.extS (coverOf 𝔹ₗ) (σ p.2)) (barField 𝔹ₗ p.1.1.1 (F₁ (σ p.2, p.1.1)).1)
                (unitQ 𝔹ₗ) (unitP 𝔹ₗ) *ᵥ p.1.2)) (⟨unitBlock x, h⟩, i)
            else 0)) := ⟨_, fun _ => rfl⟩
  have hT := analyticOnNhd_mem_of_transfer
    (S := (XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts 𝔹ₗ × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ))
    (Dm := FlRealLC 𝔹ₗ Hm a₁ ν BG κ eps X₁f BG₂ δ₁) (F := Tmap)
    (fun Φ hΦ => by
      have := fanLocalHat_analytic_cover hk1 ha₁ ha₂ hS hcd.1 HBp hκ hM hMX (Cchi_nonneg d L)
        hnum.eps_pos hnum.small1 hnum.c7le hF.num.phi_lt hmarD hαD hsm cc hcψ hF.num.δ₁_pos hδ₁
        hF.hPmp hHm hF₁an hF₁ hSolan hSol hσan hσκ hσ1
        (Φ := fun pa δφ u => Φ (pa, δφ, u)) hΦ
      simpa only [hTmap] using this)
    (fun Φ hΦ p hp => by
      have := fanLocalHat_norm_le_cover hk1 ha₁ ha₂ hS hcd.1 HBp hκ hM hMX (Cchi_nonneg d L)
        hnum.eps_pos hnum.small1 hnum.c7le hF.num.phi_lt hmarD hαD hsm cc hcψ hF.num.δ₁_pos hδ₁
        hF.hPmp hHm hF₁ hSol hσκ hσ1
        (Φ := fun pa δφ u => Φ (pa, δφ, u)) (B := 0) hΦ p hp
      simpa only [hTmap] using this)
  obtain ⟨Cmap, hCmap⟩ : ∃ Cmap : (((𝔹ₗ).Ω 1 × Fin N → ℂ) × ((𝔹ₗ).Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N, ∀ τ, Cmap τ = D2raw Gk Gj (compWeight L a₁) Fk
      (d1Triple 𝔹ₗ Gk Hm (compWeight L a₁) τ.1.1 τ.2.1 τ.2.2) := ⟨_, fun _ => rfl⟩
  have hC := analyticOnNhd_mem_of_transfer
    (S := FlRealLC 𝔹ₗ Hm a₁ ν BG κ eps X₁f BG₂ δ₁)
    (Dm := XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl))
    (F := Cmap)
    (fun Φ hΦ => by
      have := localB_eTermFun_analytic hb₁ hbC ht Yp hN₁ hMM hag hS ha₁0 HBp HBk HBj hP hq
        colk colj hκ hM hnum dsX₀ hN hj hF hFkan hFk (E := Φ) hΦ
      simpa only [hCmap, eTermFun] using this)
    (fun Φ hΦ τ hτ => by
      have := localB_eTermFun_bound hb₁ hbC ht Yp hN₁ hMM hag hS ha₁0 HBp HBk HBj hP hq
        colk colj hκ hM hnum dsX₀ hN hj hF hFk (E := Φ) (Bd := 0) hΦ hτ
      simpa only [hCmap, eTermFun] using this)
  have hPfd : FiniteDimensional ℂ ((RawData d L (N₁ * L ^ m₁) (k + 1) N × G) × (ι → ℂ)) :=
    inferInstance
  have heq : Fi = fun q => ∫ ψ in K, E (Cmap (Tmap ((q.1.1, fun r => (ψ r : ℂ)), q.2))) q.1.2 ∂γ := by
    funext q
    rw [hFi q]
    simp only [hTmap, hCmap, eTermFun]
  rw [heq]
  refine analyticOnNhd_setIntegral_compact (P := (RawData d L (N₁ * L ^ m₁) (k + 1) N × G) × (ι → ℂ))
    (I := unitPts 𝔹ₗ × Fin N) (B := Bd) (γ := γ)
    (F := fun q v => E (Cmap (Tmap ((q.1.1, v), q.2))) q.1.2) hKc hKb hγ ?_ ?_
  · intro q hq v hv
    obtain ⟨⟨hΘ, hg⟩, hw⟩ := hq
    have hmemT : ((q.1.1, v), q.2) ∈ (XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts 𝔹ₗ × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ) := ⟨⟨hΘ, hv⟩, hw⟩
    have hρ : AnalyticAt ℂ (fun x : ((RawData d L (N₁ * L ^ m₁) (k + 1) N × G) × (ι → ℂ)) ×
        (unitPts 𝔹ₗ × Fin N → ℂ) => ((x.1.1.1, x.2), x.1.2)) (q, v) :=
      ((analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)).prod analyticAt_snd).prod
        (analyticAt_snd.comp analyticAt_fst)
    have h1 := hT.1 _ hmemT
    have h2 := hC.1 _ (hT.2 _ hmemT)
    have h3 : AnalyticAt ℂ (fun z : RawData d L (N₁ * L ^ m₁) (k + 1) N × G => E z.1 z.2)
        (Cmap (Tmap ((q.1.1, v), q.2)), q.1.2) := hE _ ⟨hC.2 _ (hT.2 _ hmemT), hg⟩
    exact h3.comp_of_eq ((h2.comp_of_eq (h1.comp_of_eq hρ rfl) rfl).prod
      (analyticAt_snd.comp (analyticAt_fst.comp analyticAt_fst))) rfl
  · intro q hq v hv
    obtain ⟨⟨hΘ, hg⟩, hw⟩ := hq
    have hmemT : ((q.1.1, v), q.2) ∈ (XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts 𝔹ₗ × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ) := ⟨⟨hΘ, hv⟩, hw⟩
    exact hEb _ (hC.2 _ (hT.2 _ hmemT)) q.1.2 hg

variable {ϱa : ℝ} {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa}
  {cI : ι → ℕ × CTorus d L N₁ m₁ (k + 1)} {m₀ j' : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
  (hcov : CovSetup Ga m₀ j' X 𝒦X) (hd : 3 ≤ d) (hL : 3 ≤ L) (hcI : ∀ i, cI i ∈ cubeIdx Ga)
  (hcinj : Function.Injective cI) (hdisj : ∀ i, Disjoint (Pset m₁ (cI i)) (X1 Ga m₀ j' 𝒦X))
  (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
    ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j' 𝒦X W₀ ∧
      bondCost (scaleW L m₀ m₁ j') E₀ = treeLenCovOne m₀ j' X)
  {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec) (hEb0 : 0 ≤ Eb)
  (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
  (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
  {εseq : ℕ → ℝ} (hεseq : εseq (k + 1) ≤ eps)

include hcov hd hL hcI hcinj hdisj hopt hκ₀ hκdec hEb0 hκκ h1 hlog hεseq

theorem localB_mTermHat_evTerm_xiFieldDom {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] {Sg : Set G}
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → G → ℂ}
    (hE : AnalyticOnNhd ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × G => E q.1 q.2)
      (XiCRaw Gj (compWeight L a₁) ν j b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ×ˢ Sg))
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ∀ g ∈ Sg,
        ‖E r g‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j' X))
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (Fi : RawData d L (N₁ * L ^ m₁) (k + 1) N × G → (ι → ℂ) → ℂ)
    (hFi : ∀ u w, Fi u w =
        ∫ ψ in K,
          eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk (fun r => E r u.2) (F₁ (σ w, u.1))
        (Sol (σ w, flEdat 𝔹ₗ Hm (F₁ (σ w, u.1)) u.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, u.1)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ u.1.1 (F₁ (σ w, u.1)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (u.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, u.1)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ u.1.1 (F₁ (σ w, u.1)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ) :
    AnalyticOnNhd ℂ (fun p : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × G =>
        evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Fi Y (clipRaw 𝔹ₗ p.1, p.2))
      {p | (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1.1 p.1.2 ∧ p.2 ∈ Sg} ∧
    ∀ p : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × G,
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1.1 p.1.2 →
      p.2 ∈ Sg →
      ‖evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Fi Y (clipRaw 𝔹ₗ p.1, p.2)‖ ≤
        Eb * (γ K).toReal *
          Real.exp (-κ₀ * treeLenCovOne m₀ j' X - 2 * κdec * treeLenCov Ga m₀ Y) := by
  classical
  have hγ0 : 0 ≤ (γ K).toReal := ENNReal.toReal_nonneg
  obtain ⟨hA, hB⟩ := localB_mTermHat_integral_param hb₁ hbC ht Yp hN₁ hMM hag hS hk1 ha₁ ha₂ HBp HBk
    HBj hP hq colk colj hκ hM hMX hnum dsX₀ hN hj hF hHm hFkan hFk hmarD hαD hsm cc hcψ hδ₁ hF₁an
    hF₁ hSolan hSol hσan hσκ hσ1 hKc hKb hγ hE (Bd := Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j' X))
    hEb (fun q => Fi q.1 q.2) (fun q => hFi q.1 q.2)
  have hEv := evTerm_bound_analyticOnNhd_of_bd (c := cI)
    (U := RawData d L (N₁ * L ^ m₁) (k + 1) N × G) (F := Fi)
    hcov hd hL hcI hcinj hdisj hopt hκ₀ hκdec hκκ h1 hlog (mul_nonneg hEb0 hγ0)
    (S := XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps ×ˢ Sg) hA
    (fun u hu s hs => by
      have := hB (u, s) ⟨hu, hs⟩
      rw [mul_right_comm]
      exact this)
  refine ⟨fun p hp => ?_, fun p hp hg => ?_⟩
  · have hmem : clipRaw 𝔹ₗ p.1 ∈ XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps :=
      clipRaw_mem_xiCRaw_of_xiDom hεseq hp.1
    exact (hEv.2 Y (clipRaw 𝔹ₗ p.1, p.2) ⟨hmem, hp.2⟩).comp_of_eq
      (((analyticAt_clipRaw p.1).comp analyticAt_fst).prod analyticAt_snd) rfl
  · exact hEv.1 Y (clipRaw 𝔹ₗ p.1, p.2) ⟨clipRaw_mem_xiCRaw_of_xiDom hεseq hp, hg⟩

omit hb₁ hbC HBk HBj hq colj hj hFkan hFk hcov hd hL hcI hcinj hdisj hopt hκ₀ hκdec hEb0 hκκ h1 hlog in
/-- **Exact locality of the local source term on the class domain, for every source** (P3 (4.47);
`localB_eTermHat_evTerm_local` for the functional `E (·) g`, which needs no analyticity of `E`).
Two pairs of fields of the class domain equal on `Y` give the same term, at every source `g`. -/
theorem localB_mTermHat_evTerm_local (htk : t = k + 1)
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → Fld d L N₁ m₁ (k + 1) N → ℂ}
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hσ0 : ∀ w, ∀ P ∈ (coverOf 𝔹ₗ).cubeIdx, P.2 ∉ (𝔹ₗ).Ω (k + 1) →
      Dec2.extS (coverOf 𝔹ₗ) (σ w) P = 0)
    (hσY : ∀ C ∈ connFams cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Y, ∀ w ∈ supN C (Real.exp κ),
      ∀ P ∈ (coverOf 𝔹ₗ).cubeIdx, Dec2.extS (coverOf 𝔹ₗ) (σ w) P ≠ 0 →
        ∀ y, SameCell (L ^ (P.1 + m₁)) y P.2 → y ∈ Y)
    (Fi : RawData d L (N₁ * L ^ m₁) (k + 1) N × Fld d L N₁ m₁ (k + 1) N → (ι → ℂ) → ℂ)
    (hFi : ∀ u w, Fi u w =
        ∫ ψ in K,
          eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk (fun r => E r u.2) (F₁ (σ w, u.1))
        (Sol (σ w, flEdat 𝔹ₗ Hm (F₁ (σ w, u.1)) u.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, u.1)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ u.1.1 (F₁ (σ w, u.1)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (u.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, u.1)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ u.1.1 (F₁ (σ w, u.1)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ)
    (p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N)
    (hp : (xiFieldDom (compWeight L a₁) ν εseq :
      FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1 p.2)
    (hp' : (xiFieldDom (compWeight L a₁) ν εseq :
      FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p'.1 p'.2)
    (hpp : ∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) :
    evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Fi Y (clipRaw 𝔹ₗ p, g) =
      evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Fi Y (clipRaw 𝔹ₗ p', g) := by
  subst htk
  have := localB_eTermHat_evTerm_local (X₁ := X1 Ga m₀ j' 𝒦X) (γ := γ) (Gj := Gj) Y hk1 ht Yp hN₁
    hMM hag hS ha₁ ha₂ HBp hP colk hκ hM hMX hnum dsX₀ hN hF hHm Fk (fun r => E r g) hmarD hαD
    hsm cc hcψ hδ₁ hF₁ hSol hσκ hσ1 hσ0 hσY hKc hKb hεseq hp hp' hpp
  refine (evTerm_congr_fun ?_).trans (this.trans (evTerm_congr_fun ?_))
  · funext w
    exact hFi _ _
  · funext w
    exact (hFi (clipRaw (GsSpec.localB (k + 1) ht Yp (le_refl (minSep L (L ^ m₁)))) p', g) w).symm

omit hb₁ hbC HBk HBj hq colj hj hFkan hFk hd hL hcI hcinj hdisj hopt hκ₀ hκdec hEb0 hκκ h1 hlog in
omit hb₁ hbC HBk HBj hq colj hj hFkan hFk hd hL hcI hcinj hdisj hopt hκ₀ hκdec hEb0 hκκ h1 hlog in
/-- **The local source term on all pairs of fields and sources: locality and agreement with the
recomputed term** (`localB_eTermHat_evTerm_ext`, clauses 1-2, with the source `g`).  With `T` the
term of `Y` for the family `Fi` of `localB_mTermHat_evTerm_xiFieldDom` read through the cut-off, and
`cpl` the completion in the class domain at `Y`: `T ∘ cpl` takes the same value at two triples
`(Ψ, h, g)`, `(Ψ', h', g')` equal on `Y` (all pairs and all sources: the clause `localM`), and it
equals `T` on the class domain.  The dependence on `g` is through `g|_X`, `X ⊆ X₁ ⊆ Y`
(`evTerm_source_congr`), given that `E (·) g` depends on `g` only on `X` (`hEg`). -/
theorem localB_mTermHat_evTerm_ext_loc (htk : t = k + 1)
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → Fld d L N₁ m₁ (k + 1) N → ℂ}
    (hEg : ∀ g g' : Fld d L N₁ m₁ (k + 1) N, (∀ z ∈ X, g z = g' z) → ∀ r, E r g = E r g')

    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hσ0 : ∀ w, ∀ P ∈ (coverOf 𝔹ₗ).cubeIdx, P.2 ∉ (𝔹ₗ).Ω (k + 1) →
      Dec2.extS (coverOf 𝔹ₗ) (σ w) P = 0)
    (hσY : ∀ C ∈ connFams cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Y, ∀ w ∈ supN C (Real.exp κ),
      ∀ P ∈ (coverOf 𝔹ₗ).cubeIdx, Dec2.extS (coverOf 𝔹ₗ) (σ w) P ≠ 0 →
        ∀ y, SameCell (L ^ (P.1 + m₁)) y P.2 → y ∈ Y)
    (Fi : RawData d L (N₁ * L ^ m₁) (k + 1) N × Fld d L N₁ m₁ (k + 1) N → (ι → ℂ) → ℂ)
    (hFi : ∀ u w, Fi u w =
        ∫ ψ in K,
          eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk (fun r => E r u.2) (F₁ (σ w, u.1))
        (Sol (σ w, flEdat 𝔹ₗ Hm (F₁ (σ w, u.1)) u.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, u.1)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ u.1.1 (F₁ (σ w, u.1)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (u.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, u.1)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ u.1.1 (F₁ (σ w, u.1)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ)
    (T : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hT : ∀ p, T p = evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Fi Y (clipRaw 𝔹ₗ p.1, p.2))
    (cpl : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ p, cpl p = Classical.epsilon (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) 𝔹ₗ Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) 𝔹ₗ Y) p).2 z)) :
    (∀ Ψ Ψ' h h' g g' : Fld d L N₁ m₁ (k + 1) N,
      (∀ x ∈ Y, Ψ x = Ψ' x ∧ h x = h' x ∧ g x = g' x) → T (cpl (Ψ, h), g) = T (cpl (Ψ', h'), g')) ∧
    (∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1 p.2 →
      T (cpl p, g) = T (p, g)) := by
  classical
  have hDL : ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1 p.2 →
      p ∈ layerSub 𝔹ₗ := fun _ hp => xiDom_mem_layerSub hp
  obtain ⟨c1, c2⟩ := fieldDom_completion_spec (xiFieldDom (compWeight L a₁) ν εseq :
    FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))) (k + 1) 𝔹ₗ Y cpl hcpl hDL
  have loc : ∀ (p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
      (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1 p.2 →
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → T (p, g) = T (p', g) := by
    intro p p' g hp hp' hpp
    rw [hT, hT]
    exact localB_mTermHat_evTerm_local ht Yp hN₁ hMM hag hS hk1 ha₁ ha₂ HBp hP colk hκ hM hMX hnum dsX₀ hN hF hHm hmarD hαD hsm cc hcψ hδ₁ hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hKc hKb hγ hεseq htk Y hσ0 hσY Fi hFi p p' g hp hp' hpp
  have hsrc : ∀ (g g' : Fld d L N₁ m₁ (k + 1) N), (∀ x ∈ Y, g x = g' x) →
      ∀ u, evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Fi Y (u, g) =
        evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Fi Y (u, g') := fun g g' hg u =>
    evTerm_source_congr hcov.X_sub (fun g g' hgg u w => by
      simp only [hFi, show (fun r => E r g) = (fun r => E r g') from funext (hEg g g' hgg)]) hg u
  have hext2 : ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1 p.2 →
      T (cpl p, g) = T (p, g) := fun p g hp =>
    loc _ _ g (c2 p hp).1 hp (fun z hz => (c2 p hp).2 z hz)
  refine ⟨fun Ψ Ψ' h h' g g' hag => ?_, hext2⟩
  rw [c1 Ψ Ψ' h h' fun x hx => ⟨(hag x hx).1, (hag x hx).2.1⟩, hT, hT]
  exact hsrc g g' (fun x hx => (hag x hx).2.2) _

/-- **The local source term on all pairs of fields and sources: analyticity and the bound**
(`localB_eTermHat_evTerm_ext`, clauses 3-4, with the source `g`): `(p, g) ↦ T (cpl p, g)` is
analytic on the class domain times `Sg` (`fieldDom_completion_analytic_param` with
`localB_mTermHat_evTerm_xiFieldDom` and the locality `localB_mTermHat_evTerm_local`) and bounded
there by `Eb γ(K) e^{-κ₀ d^{cov,1}_{j'}(X) - 2 κ_dec d̃^{cov}(Y)}`. -/
theorem localB_mTermHat_evTerm_ext_an (htk : t = k + 1)
    {Sg : Set (Fld d L N₁ m₁ (k + 1) N)}
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → Fld d L N₁ m₁ (k + 1) N → ℂ}
    (hE : AnalyticOnNhd ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        E q.1 q.2)
      (XiCRaw Gj (compWeight L a₁) ν j b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ×ˢ Sg))
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ∀ g ∈ Sg,
        ‖E r g‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j' X))

    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hσ0 : ∀ w, ∀ P ∈ (coverOf 𝔹ₗ).cubeIdx, P.2 ∉ (𝔹ₗ).Ω (k + 1) →
      Dec2.extS (coverOf 𝔹ₗ) (σ w) P = 0)
    (hσY : ∀ C ∈ connFams cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Y, ∀ w ∈ supN C (Real.exp κ),
      ∀ P ∈ (coverOf 𝔹ₗ).cubeIdx, Dec2.extS (coverOf 𝔹ₗ) (σ w) P ≠ 0 →
        ∀ y, SameCell (L ^ (P.1 + m₁)) y P.2 → y ∈ Y)
    (Fi : RawData d L (N₁ * L ^ m₁) (k + 1) N × Fld d L N₁ m₁ (k + 1) N → (ι → ℂ) → ℂ)
    (hFi : ∀ u w, Fi u w =
        ∫ ψ in K,
          eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk (fun r => E r u.2) (F₁ (σ w, u.1))
        (Sol (σ w, flEdat 𝔹ₗ Hm (F₁ (σ w, u.1)) u.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, u.1)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ u.1.1 (F₁ (σ w, u.1)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (u.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, u.1)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ u.1.1 (F₁ (σ w, u.1)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ)
    (T : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hT : ∀ p, T p = evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Fi Y (clipRaw 𝔹ₗ p.1, p.2))
    (cpl : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ p, cpl p = Classical.epsilon (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) 𝔹ₗ Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) 𝔹ₗ Y) p).2 z)) :
    (AnalyticOnNhd ℂ (fun q : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) ×
        Fld d L N₁ m₁ (k + 1) N => T (cpl q.1, q.2))
      {q | (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ q.1.1 q.1.2 ∧ q.2 ∈ Sg}) ∧
    (∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1 p.2 → g ∈ Sg →
      ‖T (cpl p, g)‖ ≤ Eb * (γ K).toReal *
        Real.exp (-κ₀ * treeLenCovOne m₀ j' X - 2 * κdec * treeLenCov Ga m₀ Y)) := by
  classical
  have hDL : ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1 p.2 →
      p ∈ layerSub 𝔹ₗ := fun _ hp => xiDom_mem_layerSub hp
  obtain ⟨c1, c2⟩ := fieldDom_completion_spec (xiFieldDom (compWeight L a₁) ν εseq :
    FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))) (k + 1) 𝔹ₗ Y cpl hcpl hDL
  have loc : ∀ (p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
      (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1 p.2 →
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → T (p, g) = T (p', g) := by
    intro p p' g hp hp' hpp
    rw [hT, hT]
    exact localB_mTermHat_evTerm_local ht Yp hN₁ hMM hag hS hk1 ha₁ ha₂ HBp hP colk hκ hM hMX hnum dsX₀ hN hF hHm hmarD hαD hsm cc hcψ hδ₁ hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hKc hKb hγ hεseq htk Y hσ0 hσY Fi hFi p p' g hp hp' hpp
  obtain ⟨hA, hBd⟩ := localB_mTermHat_evTerm_xiFieldDom hb₁ hbC ht Yp hN₁ hMM hag hS hk1 ha₁ ha₂ HBp HBk HBj hP hq colk colj hκ hM hMX hnum dsX₀ hN hj hF hHm hFkan hFk hmarD hαD hsm cc hcψ hδ₁ hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hKc hKb hγ hcov hd hL hcI hcinj hdisj hopt hκ₀ hκdec hEb0 hκκ h1 hlog hεseq hE hEb Y Fi hFi
  have hTf : T = fun p => evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Fi Y (clipRaw 𝔹ₗ p.1, p.2) := funext hT
  have hAT : AnalyticOnNhd ℂ T ({p | (xiFieldDom (compWeight L a₁) ν εseq :
      FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1 p.2} ×ˢ Sg) := by
    rw [hTf]; exact hA
  have hext2 : ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1 p.2 →
      T (cpl p, g) = T (p, g) := fun p g hp =>
    loc _ _ g (c2 p hp).1 hp (fun z hz => (c2 p hp).2 z hz)
  refine ⟨?_, fun p g hp hg => ?_⟩
  · exact fieldDom_completion_analytic_param _ (k + 1) 𝔹ₗ Y cpl hcpl hDL
      (fun _ hp => xiDom_eventually HBp hp) T hAT
      (fun p p' hp hp' hpp g => loc p p' g hp hp' hpp)
  · rw [hext2 p g hp, hT]
    exact hBd (p, g) hp hg

/-- **The local source term of `Y` on all pairs of fields and sources** (P3 (4.46)-(4.47); the
clauses `localM`, `analyticM` and the per-label bound of `boundM` of the local successor class, with
the source `g` carried along): the conjunction of `localB_mTermHat_evTerm_ext_loc` and
`localB_mTermHat_evTerm_ext_an`. -/
theorem localB_mTermHat_evTerm_ext (htk : t = k + 1)
    {Sg : Set (Fld d L N₁ m₁ (k + 1) N)}
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → Fld d L N₁ m₁ (k + 1) N → ℂ}
    (hE : AnalyticOnNhd ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        E q.1 q.2)
      (XiCRaw Gj (compWeight L a₁) ν j b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ×ˢ Sg))
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ∀ g ∈ Sg,
        ‖E r g‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j' X))
    (hEg : ∀ g g' : Fld d L N₁ m₁ (k + 1) N, (∀ z ∈ X, g z = g' z) → ∀ r, E r g = E r g')

    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hσ0 : ∀ w, ∀ P ∈ (coverOf 𝔹ₗ).cubeIdx, P.2 ∉ (𝔹ₗ).Ω (k + 1) →
      Dec2.extS (coverOf 𝔹ₗ) (σ w) P = 0)
    (hσY : ∀ C ∈ connFams cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Y, ∀ w ∈ supN C (Real.exp κ),
      ∀ P ∈ (coverOf 𝔹ₗ).cubeIdx, Dec2.extS (coverOf 𝔹ₗ) (σ w) P ≠ 0 →
        ∀ y, SameCell (L ^ (P.1 + m₁)) y P.2 → y ∈ Y)
    (Fi : RawData d L (N₁ * L ^ m₁) (k + 1) N × Fld d L N₁ m₁ (k + 1) N → (ι → ℂ) → ℂ)
    (hFi : ∀ u w, Fi u w =
        ∫ ψ in K,
          eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk (fun r => E r u.2) (F₁ (σ w, u.1))
        (Sol (σ w, flEdat 𝔹ₗ Hm (F₁ (σ w, u.1)) u.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, u.1)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ u.1.1 (F₁ (σ w, u.1)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (u.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, u.1)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ u.1.1 (F₁ (σ w, u.1)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ)
    (T : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hT : ∀ p, T p = evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Fi Y (clipRaw 𝔹ₗ p.1, p.2))
    (cpl : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ p, cpl p = Classical.epsilon (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) 𝔹ₗ Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) 𝔹ₗ Y) p).2 z)) :
    (∀ Ψ Ψ' h h' g g' : Fld d L N₁ m₁ (k + 1) N,
      (∀ x ∈ Y, Ψ x = Ψ' x ∧ h x = h' x ∧ g x = g' x) → T (cpl (Ψ, h), g) = T (cpl (Ψ', h'), g')) ∧
    (∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1 p.2 →
      T (cpl p, g) = T (p, g)) ∧
    (AnalyticOnNhd ℂ (fun q : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) ×
        Fld d L N₁ m₁ (k + 1) N => T (cpl q.1, q.2))
      {q | (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ q.1.1 q.1.2 ∧ q.2 ∈ Sg}) ∧
    (∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1 p.2 → g ∈ Sg →
      ‖T (cpl p, g)‖ ≤ Eb * (γ K).toReal *
        Real.exp (-κ₀ * treeLenCovOne m₀ j' X - 2 * κdec * treeLenCov Ga m₀ Y)) :=
  have hl1 := localB_mTermHat_evTerm_ext_loc ht Yp hN₁ hMM hag hS hk1 ha₁ ha₂ HBp hP colk hκ hM hMX hnum dsX₀ hN hF hHm hmarD hαD hsm cc hcψ hδ₁ hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hKc hKb hγ hcov hεseq htk hEg Y hσ0 hσY Fi hFi T hT cpl hcpl
  have hl2 := localB_mTermHat_evTerm_ext_an hb₁ hbC ht Yp hN₁ hMM hag hS hk1 ha₁ ha₂ HBp HBk HBj hP hq colk colj hκ hM hMX hnum dsX₀ hN hj hF hHm hFkan hFk hmarD hαD hsm cc hcψ hδ₁ hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hKc hKb hγ hcov hd hL hcI hcinj hdisj hopt hκ₀ hκdec hEb0 hκκ h1 hlog hεseq htk hE hEb Y hσ0 hσY Fi hFi T hT cpl hcpl
  ⟨hl1.1, hl1.2, hl2.1, hl2.2⟩

end ParamM

section Sum

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱa : ℝ}

/-- **The vector of a family of component-wise analytic functions is analytic.**  A finite sum over
labels, componentwise in `Fin N`. -/
theorem analyticOnNhd_vec_sum {X τι : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {S : Set X}
    (𝒯 : Finset τι) (T : Fin N → τι → X → ℂ)
    (h : ∀ i, ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (T i τ) S) :
    AnalyticOnNhd ℂ (fun x i => ∑ τ ∈ 𝒯, T i τ x) S := fun x hx =>
  analyticAt_pi_iff.2 fun i => Finset.analyticAt_fun_sum _ fun τ hτ => h i τ hτ x hx

/-- **The clause `boundM` for a sum of source terms of the localization expansion over old
labels** (`norm_sum_evTerm_le_boundE` for the components of a vector).  The terms
`evTerm … (X₁(τ)) (F i τ) Y u` of the labels `τ ∈ 𝒯E`, each of which satisfies the per-label bound
`Eb_τ γ e^{-κ₀ d_{j_τ}(X_τ) - 2 κ_dec d̃^cov(Y)}` in every component `i` at the argument `u` (for the
extended terms, `localB_mTermHat_evTerm_ext_an`, clause 4, at `u = (clipRaw 𝔹 (cpl p), g)`), with
roots in `X₁(τ)` and per-site sums of `Eb_τ e^{-κ₀ d_{j_τ}(X_τ)}` at most `ρ_M`, add up in the
Euclidean norm of `ℂ^N` to at most `√N E₀ e^{-κ sizeJ(Y)}`, for `Y ∈ 𝒟_{lev}`, a generating set of
level `lev`, `γ ρ_M c₁ (L^{lev} L^{m₀ + m₁})^d ≤ E₀` and `κ ≤ 2 κ_dec - 1`.  The factor `√N`
is `vn_le_sqrt_mul`. -/
theorem norm_sum_evTerm_vn_le_boundM {τι ι U : Type*} [DecidableEq τι] [DecidableEq ι] [Fintype ι]
    (cI : ι → ℕ × CTorus d L N₁ m₁ K) (𝒯E : Finset τι)
    {Ga : GeneratingSet d L (N₁ * L ^ m₁) K ϱa} {lev m₀ : ℕ} (hGa : IsLevel Ga lev)
    (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsPolyDom m₀ lev Y)
    (rE : τι → CTorus d L N₁ m₁ K) (jE : τι → ℕ) (XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ K))
    (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X1 Ga m₀ (jE τ) (𝒦XE τ))
    (EbE : τι → ℝ) (hEb0 : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {κ₀ ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ K, ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {γ κdec κ E₀ : ℝ} (hγ : 0 ≤ γ) (hκ : κ ≤ 2 * κdec - 1)
    (hE₀ : γ * ρE * c1 d L * ((L : ℝ) ^ lev) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d ≤ E₀)
    (F : Fin N → τι → U → (ι → ℂ) → ℂ) (u : U)
    (hT : ∀ i, ∀ τ ∈ 𝒯E, ‖evTerm cI Ga m₀ (X1 Ga m₀ (jE τ) (𝒦XE τ)) (F i τ) Y u‖ ≤ EbE τ * γ *
      Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ) - 2 * κdec * treeLenCov Ga m₀ Y)) :
    Balaban.Multiscale.vn (fun i => ∑ τ ∈ 𝒯E,
        evTerm cI Ga m₀ (X1 Ga m₀ (jE τ) (𝒦XE τ)) (F i τ) Y u) ≤
      Real.sqrt N * (E₀ * Real.exp (-κ * sizeJ m₀ lev Y)) := by
  have hE0 : 0 ≤ E₀ * Real.exp (-κ * sizeJ m₀ lev Y) := by
    have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
    have : 0 ≤ γ * ρE * c1 d L * ((L : ℝ) ^ lev) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d := by positivity
    exact mul_nonneg (this.trans hE₀) (Real.exp_pos _).le
  exact vn_le_sqrt_mul hE0 fun i =>
    norm_sum_evTerm_le_boundE cI 𝒯E hGa hN hY rE jE XE 𝒦XE hrE EbE hEb0 hρE0 hρE hγ hκ hE₀ (F i) u
      (hT i)

end Sum

end Balaban.Localization
