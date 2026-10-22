/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalBoxLocPoly
public import Balaban.Spine.FinalSfUniv

/-!
# The terms `ℛ^{(k)}` of the class as rooted terms of the block field (A6-3, (L3)-(L4))

The level-`k` terms of the exponent of the small-field factor, `ℛ^{(k)}(T; ψ_k, h, g) =
∑_{1 ≤ n ≤ m} ∑_{X ∈ 𝒟_k} ℛ^{(k)}_n(X; ψ_k, h, g)` (P5 (1.16)-(1.17); `RresC`), read the block field
`ψ_k` through `sfLiftKC`, i.e. only on the blocks of `X`.  As functions of the complex block field
`ψ : Λ × Fin N → ℂ` (`Λ` the `k`-blocks):

* `RIdx C`: the labels `(n, X)`; `boxLocRTerm C hv g a ψ = ℛ^{(k)}_n(X; lift ψ, h, g)`; the root
  `rRoot C a = blocksOf C X` (a connected set of blocks, `isAnimal_rRoot`);
* `readsOn_boxLocRTerm`: the term reads `ψ` on `rRoot × Fin N`; `boxLocRTerm_congr_g`: it reads the source at the
  fine sites of the blocks of its root;
* `sum_boxLocRTerm`: `∑_a boxLocRTerm a ψ = ℛ^{(k)}(T; ψ, h, g)` (`RresC` of the whole torus);
* `boxLocRTerm_dom`: for `‖g‖₁ < 1` and `ψ` in the sup ball of radius `r` around `h`, the data lie in the
  analyticity domain of the class clause `RTermsH4` (`xiDom_of_close_unit`, radius `r` with
  `N r < δ²`, `0 < δ ≤ min (c₀, c₁)`, `(2K₁ + 2) δ ≤ ε_k`);
* `analyticOnNhd_boxLocRTerm`: joint analyticity in `(g, ψ)` there; `norm_boxLocRTerm_le`: the bound
  `fac_n β_k^{-n-1} e^{-κ d_k(X)}` of `RTermsH4`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.LargeField Balaban.LargeField.Def7 Balaban.Localization
  Balaban.Green Balaban.SmallField Balaban.Background Finset

section RTerms

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (hv : EuclideanSpace ℝ (Fin N))

/-- **The labels of the terms `ℛ^{(k)}_n(X)`**: `1 ≤ n ≤ m₀ + m₁` and `X ∈ 𝒟_k`. -/
abbrev RIdx : Type :=
  {nn // nn ∈ Finset.Icc 1 (C.m₀ + m₁)} ×
    {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) // Def6.IsPolyDom C.m₀ k X}

open Classical in
noncomputable instance : Fintype (RIdx C) := inferInstance

/-- **The term `ℛ^{(k)}_n(X; ψ, h, g)`** as a function of the complex block field. -/
noncomputable def boxLocRTerm (g : GIdx S n M K N → ℂ) (a : RIdx C)
    (ψ : BlockAt S n M K k × Fin N → ℂ) : ℂ :=
  C.sf.Rt C.N₁ a.1.1 a.2.1 (C.sfLiftKC (fun b i => ψ (b, i))) (Def6.constFld (hC hv))
    (sfG C.geo C.hnn C.hkK C.hT g)

/-- The root of the term `(n, X)`: the blocks of `X`. -/
noncomputable def rRoot (a : RIdx C) : Finset (BlockAt S n M K k) := blocksOf C a.2.1

theorem isAnimal_rRoot (a : RIdx C) :
    Polymer.IsAnimal (Polymer.blockGraph S.d (M * n K * S.L ^ (K - k))) (rRoot C a) :=
  isAnimal_blocksOf C a.2.2

variable {C} {fac : ℕ → ℝ} {P6 : Def6.Consts}

/-- **The term reads the block field on its root.** -/
theorem readsOn_boxLocRTerm
    (hR : Def7.RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (g : GIdx S n M K N → ℂ) (a : RIdx C) :
    ReadsOn (blockSites N (rRoot C a)) (boxLocRTerm C hv g a) := by
  intro ψ ψ' hψ
  unfold boxLocRTerm
  refine hR.loc _ _ _ _ _ _ _ _ fun z hz => ⟨?_, rfl, rfl⟩
  funext i
  rw [sfLiftKC_apply, sfLiftKC_apply]
  exact hψ (sfBlockOf C z, i) ((mem_blocksOf C).2 ⟨z, hz, rfl⟩)

/-- **The term reads the source at the fine sites of the blocks of its root.** -/
theorem boxLocRTerm_congr_g
    (hR : Def7.RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    {g g' : GIdx S n M K N → ℂ} (a : RIdx C)
    (hgg : ∀ x, jBlock S.d S.L (M * n K) K k x ∈ rRoot C a → ∀ i, g (x, i) = g' (x, i))
    (ψ : BlockAt S n M K k × Fin N → ℂ) : boxLocRTerm C hv g a ψ = boxLocRTerm C hv g' a ψ := by
  unfold boxLocRTerm
  refine hR.loc _ _ _ _ _ _ _ _ fun z hz => ⟨rfl, rfl, ?_⟩
  funext i
  exact hgg _ ((mem_blocksOf C).2 ⟨z, hz, rfl⟩) i

variable (C)

open Classical in
/-- **The sum of the terms is `ℛ^{(k)}` of the whole torus.** -/
theorem sum_boxLocRTerm (g : GIdx S n M K N → ℂ) (ψ : BlockAt S n M K k × Fin N → ℂ) :
    ∑ a : RIdx C, boxLocRTerm C hv g a ψ =
      C.RresC Set.univ (fun b i => ψ (b, i)) hv g := by
  unfold SFCtx.RresC
  rw [Fintype.sum_prod_type]
  rw [← Finset.sum_coe_sort (Finset.Icc 1 (C.m₀ + m₁))]
  refine Finset.sum_congr rfl fun nn _ => ?_
  rw [sset_univ]
  have hset : {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) |
      Def6.IsPolyDom C.m₀ k X ∧ X ⊆ Set.univ} = {X | Def6.IsPolyDom C.m₀ k X} := by
    ext X; simp
  rw [hset, finsum_mem_def, finsum_eq_sum_of_fintype]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (Finset.univ.filter fun X => Def6.IsPolyDom C.m₀ k X)
    (p := fun X => Def6.IsPolyDom C.m₀ k X) (fun X => by simp)]
  rfl

theorem torusCast_bijective {d m m' : ℕ} (h : m = m') :
    Function.Bijective (torusCast (d := d) h) := by
  subst h; exact Function.bijective_id

/-- The source read on the Def-6 torus has the component `ℓ¹` norm of the source. -/
theorem sum_norm_sfG_eq (g : GIdx S n M K N → ℂ) :
    ∑ x, ∑ i, ‖sfG C.geo C.hnn C.hkK C.hT g x i‖ = ∑ q, ‖g q‖ := by
  have hbij : Function.Bijective fun x : Localization.CTorus S.d S.L C.N₁ m₁ k =>
      bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT x) :=
    (torusCast_bijective _).comp (torusCast_bijective _)
  rw [Fintype.sum_prod_type]
  exact hbij.sum_comp (fun y => ∑ i, ‖g (y, i)‖)

/-- The source read on the Def-6 torus has at most the `ℓ¹` norm of the source. -/
theorem l1_sfG_le (g : GIdx S n M K N → ℂ) :
    Def6.l1 (sfG C.geo C.hnn C.hkK C.hT g) ≤ ∑ q, ‖g q‖ :=
  (l1_le_sum _).trans (le_of_eq (sum_norm_sfG_eq C g))

/-- The layers above `k` of the generating set of the class terms are empty. -/
theorem topGS_Ω_empty {i : ℕ} (hi : k < i) :
    (Def6.topGS S.d S.L C.N₁ m₁ k ϱ).Ω i = ∅ := by
  ext x
  simp [Def6.topGS, Def6.levelGS, show ¬ i ≤ k by omega]

/-- **The data of the terms lie in the analyticity domain of the class clause**, for sources of the
unit ball and block fields within `r` of `h` (`N r < δ²`, `0 < δ ≤ min (c₀, c₁)`,
`(2K₁ + 2) δ ≤ ε_k`). -/
theorem boxLocRTerm_dom
    (H : BgHyp S.d S.L k ϱ (Def6.aIdeal S.L k (C.sf.a k))
      (Def6.bgMass S.L k (C.sf.β k) (C.sf.ν k)))
    (hunit : ‖hv‖ = 1) {δ r : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 S.d S.L N)
    (hδc1 : δ ≤ bgC1 S.d S.L N) (hr0 : 0 < r) (hr : (N : ℝ) * r < δ ^ 2)
    (hε : (2 * bgK1 S.d S.L N + 2) * δ ≤ P6.eps S.d S.L k)
    {p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ)} (hp : p ∈ rDom hv r) :
    Def6.XiDom (Def6.topGS S.d S.L C.N₁ m₁ k ϱ) (Def6.aIdeal S.L k (C.sf.a k))
        (Def6.bgMass S.L k (C.sf.β k) (C.sf.ν k)) k (P6.eps S.d S.L k)
        (C.sfLiftKC (fun b i => p.2 (b, i))) (Def6.constFld (hC hv)) ∧
      (∀ x, Def6.constFld (d := S.d) (L := S.L) (N₁ := C.N₁) (m₁ := m₁) (k := k) (hC hv) x ∈ hDomR N) ∧
      Def6.l1 (sfG C.geo C.hnn C.hkK C.hT p.1) < 1 := by
  obtain ⟨hg, hψ⟩ := hp
  refine ⟨?_, fun _ => Set.mem_univ _, (l1_sfG_le C p.1).trans_lt hg⟩
  have hu := sum_sq_eq_one_of_norm_eq_one hv hunit
  have hball : ∀ q, ‖p.2 q - hvField hv q‖ < r := by
    intro q
    have := (dist_pi_lt_iff hr0).1 (Metric.mem_ball.1 hψ) q
    rwa [dist_eq_norm] at this
  refine Def6.xiDom_of_close_unit H (fun i hi => topGS_Ω_empty C hi) le_rfl
    (u := fun i => hv i) hu hδ0 hδc0 hδc1 hr0 hr hε _ (hC hv) (fun x i => ?_) (fun x x' hxx => ?_)
    (fun i => ?_)
  · rw [sfLiftKC_apply]
    exact (hball (sfBlockOf C x, i)).le
  · funext i
    rw [sfLiftKC_apply, sfLiftKC_apply, sfBlockOf_eq_of_jBlock C hxx]
  · have : hC hv i - ((hv i : ℝ) : ℂ) = 0 := sub_self _
    rw [this, norm_zero, mul_zero]
    exact hr0.le

/-- The data map of the terms is analytic in `(g, ψ)`. -/
theorem analyticAt_rData (p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ)) :
    AnalyticAt ℂ (fun p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ) =>
      (C.sfLiftKC (fun b i => p.2 (b, i)), Def6.constFld (d := S.d) (L := S.L) (N₁ := C.N₁) (m₁ := m₁)
        (k := k) (hC hv), sfG C.geo C.hnn C.hkK C.hT p.1)) p := by
  refine AnalyticAt.prod ?_ (AnalyticAt.prod analyticAt_const ?_)
  · refine analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : BlockAt S n M K k × Fin N => ℂ)
      (sfBlockOf C x, i)).comp (ContinuousLinearMap.snd ℂ (GIdx S n M K N → ℂ)
        (BlockAt S n M K k × Fin N → ℂ))).analyticAt p
  · refine analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : GIdx S n M K N => ℂ)
      (bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT x), i)).comp
        (ContinuousLinearMap.fst ℂ (GIdx S n M K N → ℂ)
          (BlockAt S n M K k × Fin N → ℂ))).analyticAt p

/-- **The terms are analytic in `(g, ψ)`** on the domain. -/
theorem analyticOnNhd_boxLocRTerm
    (hR : Def7.RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (hm₀ : P6.m₀ = C.m₀)
    (H : BgHyp S.d S.L k ϱ (Def6.aIdeal S.L k (C.sf.a k))
      (Def6.bgMass S.L k (C.sf.β k) (C.sf.ν k)))
    (hunit : ‖hv‖ = 1) {δ r : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 S.d S.L N)
    (hδc1 : δ ≤ bgC1 S.d S.L N) (hr0 : 0 < r) (hr : (N : ℝ) * r < δ ^ 2)
    (hε : (2 * bgK1 S.d S.L N + 2) * δ ≤ P6.eps S.d S.L k) (a : RIdx C) :
    AnalyticOnNhd ℂ (fun p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ) =>
      boxLocRTerm C hv p.1 a p.2) (rDom hv r) := by
  intro p hp
  have hn := Finset.mem_Icc.1 a.1.2
  have hA := hR.analytic a.1.1 hn.1 (by rw [hm₀]; exact hn.2) a.2.1 (by rw [hm₀]; exact a.2.2)
    (C.sfLiftKC (fun b i => p.2 (b, i)), Def6.constFld (d := S.d) (L := S.L) (N₁ := C.N₁)
      (m₁ := m₁) (k := k) (hC hv), sfG C.geo C.hnn C.hkK C.hT p.1)
    (boxLocRTerm_dom (P6 := P6) C hv H hunit hδ0 hδc0 hδc1 hr0 hr hε hp)
  exact AnalyticAt.comp (g := fun q : Def6.Fld S.d S.L C.N₁ m₁ k N × Def6.Fld S.d S.L C.N₁ m₁ k N ×
      Def6.Fld S.d S.L C.N₁ m₁ k N => C.sf.Rt C.N₁ a.1.1 a.2.1 q.1 q.2.1 q.2.2)
    (f := fun p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ) =>
      (C.sfLiftKC (fun b i => p.2 (b, i)), Def6.constFld (d := S.d) (L := S.L) (N₁ := C.N₁)
        (m₁ := m₁) (k := k) (hC hv), sfG C.geo C.hnn C.hkK C.hT p.1)) hA
    (analyticAt_rData C hv p)

/-- **The bound of the terms** on the domain (`RTermsH4`). -/
theorem norm_boxLocRTerm_le
    (hR : Def7.RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (hm₀ : P6.m₀ = C.m₀)
    (H : BgHyp S.d S.L k ϱ (Def6.aIdeal S.L k (C.sf.a k))
      (Def6.bgMass S.L k (C.sf.β k) (C.sf.ν k)))
    (hunit : ‖hv‖ = 1) {δ r : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 S.d S.L N)
    (hδc1 : δ ≤ bgC1 S.d S.L N) (hr0 : 0 < r) (hr : (N : ℝ) * r < δ ^ 2)
    (hε : (2 * bgK1 S.d S.L N + 2) * δ ≤ P6.eps S.d S.L k) (a : RIdx C)
    {p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ)} (hp : p ∈ rDom hv r) :
    ‖boxLocRTerm C hv p.1 a p.2‖ ≤
      fac a.1.1 * (C.sf.β k)⁻¹ ^ (a.1.1 + 1) * Real.exp (-P6.κ * Def6.sizeJ C.m₀ k a.2.1) := by
  have hn := Finset.mem_Icc.1 a.1.2
  obtain ⟨h1, h2, h3⟩ := boxLocRTerm_dom (P6 := P6) C hv H hunit hδ0 hδc0 hδc1 hr0 hr hε hp
  have := hR.bound a.1.1 hn.1 (by rw [hm₀]; exact hn.2) a.2.1 (by rw [hm₀]; exact a.2.2) _ _ _
    h1 h2 h3
  rw [hm₀] at this
  exact this

end RTerms

end Balaban.RootFSpine
