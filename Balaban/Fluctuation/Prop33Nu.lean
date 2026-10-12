/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Prop33Bound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The `ν`-part of the localized interaction (FLUCTUATION §3.3, Proposition 3.3, `k ≤ k₀`)

With the `ν`-free convention (D-FL.1; `expansion_nuFree`) the mass variation is
`V_ν(ψ') = ν ⟨φ', φ^0_{k+1} - h⟩ + (ν/2) ‖φ'‖²` (`massVar`), and `V_{ν,1} = ν⁻¹ V_ν`.  The `ν`-part of
(3.3) is the first-derivative term `σ ∫₀¹ ∂_w V_{ν,1}(σ t' x₀) dt'`.  Along the decoupled fluctuation
field (`flFieldOne`, which is the exact fluctuation by `exact_fluct_eq_flFieldOne`)

`V_{ν,1}(ψ') = ∑_x ∑_i [δφ_i(x) (φ_{k+1,i}(x) - h_i(x)) + ½ δφ_i(x)²] =: ∑_z 𝒩_z`

is a sum of block functionals of the decoupled objects `(φ_{k+1}(s), δφ(s), Θ)`; each is expanded by
Lemma AE (`i5_functional`) over the domains `Y ⊃ X₁(z)`.  The bound of the block functional needs
a bound on the external field `h̃` (`‖h̃‖ ≤ Bh`, the source premise `|φ^0_{k+1} - h| ≤ 2` of the
proof of Proposition 3.3): for `ν = 0` (the `ν`-free objects) it is not a consequence of the data
domain.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix Set Metric

section Nu

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {n : ℕ} {a₁ ν c BG κ eps : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ K)}
variable {Kc Cx c₂ BG₂ δ₁ : ℝ}

variable (Gp Hm) in
/-- **The density of the mass variation `V_{ν,1}` at a site `x`**:
`∑_i [δφ_i(x) (φ_{k+1,i}(x) - h_i(x)) + ½ δφ_i(x)²]`. -/
noncomputable def nuDensity (δφ : Hm.Ω 1 × Fin N → ℂ) (φ₁ : Gp.Ω 1 × Fin N → ℂ)
    (hh : CTorus d L N₁ m₁ K → Fin N → ℂ) (x : CTorus d L N₁ m₁ K) : ℂ :=
  ∑ i, (svec Hm δφ x i * (svec Gp φ₁ x i - hh x i) + (1 / 2) * (svec Hm δφ x i * svec Hm δφ x i))

variable (Gp Hm) in
/-- **The block functional of `V_{ν,1}`**: the sum of `nuDensity` over the block `B_{n+1}(z)`,
as a function of `((φ₁, α₁), δφ, (Θ, ψ'))`. -/
noncomputable def nuBlockFun (n : ℕ) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ :=
  fun pa δφ u => ∑ x ∈ blockSites d L N₁ m₁ K n z, nuDensity Gp Hm δφ pa.1 u.1.2 x

theorem nuBlockFun_analytic (n : ℕ) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    AnalyticOnNhd ℂ (fun t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) =>
      nuBlockFun Gp Hm n z t.1 t.2.1 t.2.2) Set.univ := by
  intro t0 _
  unfold nuBlockFun nuDensity
  refine Finset.analyticAt_fun_sum _ fun x _ => Finset.analyticAt_fun_sum _ fun i _ => ?_
  have h1 := analyticAt_svec' (Hm := Hm) (Q := ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) × (RawData d L (N₁ * L ^ m₁) K N ×
        (CTorus d L N₁ m₁ K → Fin N → ℂ))) (q₀ := t0) (fun t => t.2.1)
    (fun r => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Hm.Ω 1 × Fin N => ℂ) r).analyticAt _).comp
      (analyticAt_fst.comp analyticAt_snd)) x i
  have h2 := analyticAt_svec' (Hm := Gp) (Q := ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) × (RawData d L (N₁ * L ^ m₁) K N ×
        (CTorus d L N₁ m₁ K → Fin N → ℂ))) (q₀ := t0) (fun t => t.1.1)
    (fun r => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Gp.Ω 1 × Fin N => ℂ) r).analyticAt _).comp
      (analyticAt_fst.comp analyticAt_fst)) x i
  have h3 : AnalyticAt ℂ (fun t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) => t.2.2.1.2 x i) t0 :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).analyticAt _).comp
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ K =>
        Fin N → ℂ) x).analyticAt _).comp
        (analyticAt_snd.comp (analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd))))
  exact (h1.mul (h2.sub h3)).add (analyticAt_const.mul (h1.mul h1))

/-- **The decoupled background is within `B` of the external field.**  On the realizable triples
`‖φ_{k+1}(s)(x)_i - h̃(x)_i‖ ≤ K₄ δ + (1 + 3 δ) + B_h`, `δ = xiC1 ε`, where `‖h̃‖ ≤ B_h` on the
data domain (the closeness of `φ` to the data `Ψ`, `|Ψ| ≤ 1 + 3δ` on the domain). -/
theorem flReal_phiSub_bound (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {lev : ℕ} (hG' : IsLevel Gp lev) {Bh : ℝ}
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ))}
    (ht : t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) (x : CTorus d L N₁ m₁ K) (i : Fin N) :
    ‖svec Gp t.1.1 x i - t.2.2.1.2 x i‖ ≤
      K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh := by
  classical
  obtain ⟨s, D, ψ', δα, hs, -, hD, hψ, hI, ht22, -⟩ := ht
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hε := hC.eps_pos
  have hc1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hsle : ∀ P, ‖s P‖ ≤ Real.exp κ := fun P => (hs P).le
  obtain ⟨φ', α', hI', hu', -, -, hbb⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    hsle hδ0 le_rfl hδ0' hδ1 hνε hDom
  have e := (hu' _ _ hI).1
  have hxΩ : x ∈ Gp.Ω 1 := (hG' x).1
  have hxd : x ∈ dataSites Gp := (mem_dataSites Gp).2 (Or.inl hxΩ)
  have hh : t.2.2.1.2 x i = D.h x i := by rw [ht22]; rfl
  rw [svec_of_mem' _ hxΩ, hh, e]
  have h1 : ‖φ' (⟨x, hxΩ⟩, i) - D.Ψ x i‖ ≤ K4 d L N BG κ * (xiC1 d * eps) :=
    (norm_le_vn (fun i => φ' (⟨x, hxΩ⟩, i) - D.Ψ x i) i).trans (hbb.val ⟨x, hxΩ⟩)
  have h2 : ‖D.Ψ x i‖ ≤ 1 + 3 * (xiC1 d * eps) := by
    obtain ⟨Ψr, hr', Ψc, hc', hP, hΨ, -⟩ := hDom
    rw [hΨ x hxd i]
    have hr2 := hP.r2 x hxd
    have hc2 := hP.c2a x hxd
    have hsq : (Ψr x i) ^ 2 ≤ ∑ j, Ψr x j ^ 2 :=
      Finset.single_le_sum (f := fun j => Ψr x j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    have hlt : (Ψr x i) ^ 2 < (1 + xiC1 d * eps) ^ 2 := by
      have := abs_lt.1 hr2
      nlinarith [this.2, sq_nonneg (xiC1 d * eps)]
    have hr3 : |Ψr x i| < 1 + xiC1 d * eps := abs_lt_of_sq_lt_sq hlt (by positivity)
    have hc3 : ‖Ψc x i‖ ≤ xiC1 d * eps + xiC1 d * eps :=
      (norm_le_vn (Ψc x) i).trans hc2.le
    calc ‖((Ψr x i : ℝ) : ℂ) + Ψc x i‖ ≤ ‖((Ψr x i : ℝ) : ℂ)‖ + ‖Ψc x i‖ := norm_add_le _ _
      _ ≤ (1 + xiC1 d * eps) + (xiC1 d * eps + xiC1 d * eps) := by
          refine add_le_add ?_ hc3
          rw [Complex.norm_real]; exact hr3.le
      _ = 1 + 3 * (xiC1 d * eps) := by ring
  calc ‖φ' (⟨x, hxΩ⟩, i) - D.h x i‖ ≤ ‖φ' (⟨x, hxΩ⟩, i) - D.Ψ x i‖ + ‖D.Ψ x i‖ + ‖D.h x i‖ := by
        calc ‖φ' (⟨x, hxΩ⟩, i) - D.h x i‖
            = ‖(φ' (⟨x, hxΩ⟩, i) - D.Ψ x i) + D.Ψ x i - D.h x i‖ := by ring_nf
          _ ≤ ‖φ' (⟨x, hxΩ⟩, i) - D.Ψ x i + D.Ψ x i‖ + ‖D.h x i‖ := norm_sub_le _ _
          _ ≤ _ := by
              have := norm_add_le (φ' (⟨x, hxΩ⟩, i) - D.Ψ x i) (D.Ψ x i)
              linarith
    _ ≤ K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh :=
        add_le_add (add_le_add h1 h2) (hBh D hD x i)

variable (d L N) in
/-- The bound of a block functional of `V_{ν,1}`: `(L^{n+1})^d N (V B + ½ V²)`. -/
noncomputable def nuBd (n : ℕ) (V B : ℝ) : ℝ := ((L : ℝ) ^ (n + 1)) ^ d * (N * (V * B + (1 / 2) * (V * V)))

/-- **The block functional is bounded on the realizable triples.** -/
theorem nuBlockFun_bound (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {n : ℕ} (hp : n + 1 ≤ K) (hG' : IsLevel Gp (n + 1)) {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ))}
    (ht : t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :
    ‖nuBlockFun Gp Hm n z t.1 t.2.1 t.2.2‖ ≤ nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) := by
  classical
  obtain ⟨-, hsup, -⟩ := flReal_facts ht
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hB1 : 0 ≤ K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh := by
    have hK4 : 0 < K4 d L N BG κ := K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0
    have hx1 := one_le_xiC1 d
    have hx2 := hC.eps_pos
    have hx3 : 0 ≤ xiC1 d * eps := by positivity
    have hx4 := mul_nonneg hK4.le hx3
    linarith
  set V := cK2' d L N (famConst d L BG₂ κ) * δ₁ with hVdef
  set B := K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh with hBdef
  have hterm : ∀ x ∈ blockSites d L N₁ m₁ K n z, ∀ i : Fin N,
      ‖svec Hm t.2.1 x i * (svec Gp t.1.1 x i - t.2.2.1.2 x i) +
        (1 / 2) * (svec Hm t.2.1 x i * svec Hm t.2.1 x i)‖ ≤ V * B + (1 / 2) * (V * V) := by
    intro x _ i
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul (hsup.val x i) (flReal_phiSub_bound hC hG' hBh ht x i) (norm_nonneg _) hV
    · rw [norm_mul, norm_mul]
      have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      rw [h12]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hsup.val x i) (hsup.val x i) (norm_nonneg _) hV)
        (by norm_num)
  unfold nuBlockFun nuDensity nuBd
  refine (norm_sum_le _ _).trans ?_
  have hcard : ((blockSites d L N₁ m₁ K n z).card : ℝ) = ((L : ℝ) ^ (n + 1)) ^ d := by
    rw [card_blockSites_eq hp z]; push_cast; rfl
  calc ∑ x ∈ blockSites d L N₁ m₁ K n z, ‖∑ i : Fin N, (svec Hm t.2.1 x i *
          (svec Gp t.1.1 x i - t.2.2.1.2 x i) + (1 / 2) * (svec Hm t.2.1 x i * svec Hm t.2.1 x i))‖
      ≤ ∑ x ∈ blockSites d L N₁ m₁ K n z, ((N : ℝ) * (V * B + (1 / 2) * (V * V))) := by
        refine Finset.sum_le_sum fun x hx => (norm_sum_le _ _).trans ?_
        calc ∑ i : Fin N, ‖svec Hm t.2.1 x i * (svec Gp t.1.1 x i - t.2.2.1.2 x i) +
              (1 / 2) * (svec Hm t.2.1 x i * svec Hm t.2.1 x i)‖
            ≤ ∑ i : Fin N, (V * B + (1 / 2) * (V * V)) :=
              Finset.sum_le_sum fun i _ => hterm x hx i
          _ = (N : ℝ) * (V * B + (1 / 2) * (V * V)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ((L : ℝ) ^ (n + 1)) ^ d * ((N : ℝ) * (V * B + (1 / 2) * (V * V))) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-- **Locality of the block functional**: it reads the background, the fluctuation and the
external field on the block only. -/
theorem nuBlockFun_local (n : ℕ) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    {t t' : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ))}
    (hφ : ∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ (↑(blockSites d L N₁ m₁ K n z) :
      Set (CTorus d L N₁ m₁ K)) → ∀ i, t.1.1 (y, i) = t'.1.1 (y, i))
    (hδ : ∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ (↑(blockSites d L N₁ m₁ K n z) :
      Set (CTorus d L N₁ m₁ K)) → ∀ i, t.2.1 (y, i) = t'.2.1 (y, i))
    (hag : agreeOn (thickSet Gp (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)))
      t.2.2.1 t'.2.2.1) :
    nuBlockFun Gp Hm n z t.1 t.2.1 t.2.2 = nuBlockFun Gp Hm n z t'.1 t'.2.1 t'.2.2 := by
  classical
  unfold nuBlockFun nuDensity
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
  have hxZ : x ∈ (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)) := hx
  have h1 : svec Hm t.2.1 x i = svec Hm t'.2.1 x i := by
    by_cases hxΩ : x ∈ Hm.Ω 1
    · rw [svec_of_mem' _ hxΩ, svec_of_mem' _ hxΩ]; exact hδ ⟨x, hxΩ⟩ hxZ i
    · rw [svec_of_not_mem Hm _ hxΩ, svec_of_not_mem Hm _ hxΩ]
  have h2 : svec Gp t.1.1 x i = svec Gp t'.1.1 x i := by
    by_cases hxΩ : x ∈ Gp.Ω 1
    · rw [svec_of_mem' _ hxΩ, svec_of_mem' _ hxΩ]; exact hφ ⟨x, hxΩ⟩ hxZ i
    · rw [svec_of_not_mem Gp _ hxΩ, svec_of_not_mem Gp _ hxΩ]
  have h3 : t.2.2.1.2 x i = t'.2.2.1.2 x i := by
    have := (hag x (Or.inl hxZ)).2
    rw [this]
  rw [h1, h2, h3]

variable {j m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

/-- **The block functional of `V_{ν,1}` expands over the domains `Y ⊃ X₁`** (Lemma AE for the
decoupled objects, `i5_functional`). -/
theorem nublock_expansion (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {n : ℕ} (hp : n + 1 ≤ K) (hG' : IsLevel Gp (n + 1)) {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    (hZ : (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)) ⊆ ↑X₁f) :
    ∃ Ev : Set (CTorus d L N₁ m₁ K) →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁,
        nuBlockFun Gp Hm n z (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ')
          (rawOf D, ψ') = ∑ Y ∈ polyDom Gp X₁f m₀ j 𝒦X, Ev Y (rawOf D, ψ')) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet Gp Y) u.1 u'.1 → (∀ y ∈ psiThick Y, u.2 y = u'.2 y) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ‖Ev Y u‖ ≤ nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁)) := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hB1 : 0 ≤ K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh := by
    have hK4 : 0 < K4 d L N BG κ := K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0
    have hx1 := one_le_xiC1 d
    have hx2 := hC.eps_pos
    have hx3 : 0 ≤ xiC1 d * eps := by positivity
    have hx4 := mul_nonneg hK4.le hx3
    linarith
  have hEb : 0 ≤ nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) := by
    unfold nuBd; positivity
  obtain ⟨Ev, h1', h2', h3', h4'⟩ := i5_functional hC hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog
    hEb (Φ := nuBlockFun Gp Hm n z) ((nuBlockFun_analytic (Gp := Gp) (Hm := Hm) n z).mono
      (Set.subset_univ _))
    (fun t ht => by
      rw [hΔ]; simpa using nuBlockFun_bound hC hp hG' hBh0 hBh z ht)
    (Z := ↑(blockSites d L N₁ m₁ K n z)) (Zα := ∅) hZ (fun x hx => absurd hx (Set.notMem_empty x))
    (fun t _ t' _ hφ _ hδ hag _ => nuBlockFun_local n z hφ hδ hag)
  refine ⟨Ev, h1', h2', fun Y u hu => ?_, h4'⟩
  have := h3' Y u hu
  rw [hΔ] at this
  simpa using this

/-- **The `ν`-part of the localized interaction, one block.**  The first derivative along `w` of
the block functional of `V_{ν,1}` is a localized expansion over the domains `Y ⊃ X₁` with the bound
`|σ| M_ω 𝒩 e^{-2 κ d̃^{cov}_{k+1}(Y)} / r`, `𝒩 = nuBd`. -/
theorem nublock_locInt (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {n : ℕ} (hp : n + 1 ≤ K) (hG' : IsLevel Gp (n + 1)) {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    (hZ : (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)) ⊆ ↑X₁f)
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ K) →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (polyDom Gp X₁f m₀ j 𝒦X)
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => dirTermSrc (onXi Gp a₁ ν eps
          (fun D ψ' => nuBlockFun Gp Hm n z (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ')
            (rawOf D, ψ'))) ω x₀ w σ Θ)
        (fun Y => Mω * ((nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
  classical
  obtain ⟨Ev, hsum, hloc, hbd, hanY⟩ := nublock_expansion hC hp hG' hBh0 hBh hcov hX₁ hconn hrow
    hopt hΔ hκ₀ hκdec hκ h1 hlog z hZ
  refine ⟨Ev, ?_⟩
  exact locInt_dir1 (S := XiCRaw Gp (compWeight L a₁) ν K 1 eps) (B := FlBall Hm δ₁)
    (f := onXi Gp a₁ ν eps
      (fun D ψ' => nuBlockFun Gp Hm n z (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ')
        (rawOf D, ψ')))
    (polyDom Gp X₁f m₀ j 𝒦X) (Evs := Ev)
    (b := fun Y => nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
        Real.exp (-2 * κdec * treeLenCov Gp m₀ Y))
    (AgΘ := fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
    (AgF := fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) (Rσ := Rσ) hR₁ hω hωc hMω hωb hr
    (isOpen_flBall (N := N) Hm δ₁) hanY (fun Y u hu => hbd Y u hu)
    (fun Y a a' c' c'' p q ha hb y hy => by simp [ha y hy, hb y hy])
    (fun Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2' => hloc Y (Θ, z) ⟨hΘ, hz⟩ (Θ', z') ⟨hΘ', hz'⟩ h1' h2')
    (fun Θ hΘ ψ' hψ => by
      obtain ⟨D, hD, rfl⟩ := hΘ
      rw [onXi_rawOf hD]
      exact hsum D hD ψ' hψ)

section NuTotal

variable (Gp Hm) in
/-- **The mass variation `V_{ν,1}` along the decoupled fluctuation**:
`∑_x ∑_i [δφ_i(x) (φ_{k+1,i}(x) - h_i(x)) + ½ δφ_i(x)²]`, `δφ = flFieldOne`. -/
noncomputable def nuTotal (a₁ ν BG₂ κ : ℝ) (D : BgData Gp N)
    (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ) : ℂ :=
  ∑ x : CTorus d L N₁ m₁ K, nuDensity Gp Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ')
    (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D) D.h x

/-- The blocks partition the torus: `V_{ν,1} = ∑_z 𝒩_z`. -/
theorem sum_nuBlockFun {n : ℕ} (a₁ ν BG₂ κ : ℝ) (D : BgData Gp N)
    (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ) :
    ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))),
      nuBlockFun Gp Hm n z (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ')
        (rawOf D, ψ') = nuTotal Gp Hm a₁ ν BG₂ κ D ψ' := by
  classical
  unfold nuBlockFun nuTotal
  exact Finset.sum_fiberwise (Finset.univ : Finset (CTorus d L N₁ m₁ K))
    (fun x => jBlock d L (N₁ * L ^ m₁) K (n + 1) x)
    (fun x => nuDensity Gp Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ')
      (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D) D.h x)

end NuTotal

section Bridge

/-- **`V_{ν,1}` is the mass variation of the exact fluctuation.**  With the hypotheses of
`exact_fluct_eq_flFieldOne`, the physical mass variation per unit mass,
`ν⁻¹ V_ν(ψ') = massVar 1 …` of the fluctuation `φ_k(ψ) - φ_{k+1}`, equals `nuTotal`, the same
expression along the decoupled fluctuation `flFieldOne`. -/
theorem massVar_one_eq_nuTotal (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {n : ℕ} (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (hp : n + 1 ≤ K) (ha₁ : 0 < a₁)
    (H : BgHyp d L K ϱm (compWeight L a₁) ν)
    (D' : BgData Gp N) (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D')
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    (D : BgData Hm N) (hh : ∀ x i, D.h x i = D'.h x i)
    (hψ : compTangent hG hG' hp (compWeight L a₁)
      (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D ∈ FlBall Hm δ₁)
    {R : ℝ} (hR : 2 ≤ R)
    (hdisc : ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
      ((composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
        (tangentData D (composeData (hG.precedes hG' hp) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) :
    massVar 1 (hG.precedes hG' hp) (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D'.h
        (bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) D -
          (hG.precedes hG' hp).restrictφ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D')) =
      nuTotal Gp Hm a₁ ν BG₂ κ D' (compTangent hG hG' hp (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D) := by
  classical
  have e := exact_fluct_eq_flFieldOne hC hG hG' hp ha₁ H D' hD hc7 D hh hψ hR hdisc hRs hsmall
    hnum hnum'
  rw [e]
  set φ₁ := bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D' with hφ₁
  set φ'' := flFieldOne Gp Hm BG₂ κ a₁ ν D' (compTangent hG hG' hp (compWeight L a₁) φ₁ D' D)
    with hφ''
  unfold massVar nuTotal nuDensity
  have hs1 : ∀ x : Hm.Ω 1, ∀ i, φ'' (x, i) = svec Hm φ'' x i := fun x i =>
    (svec_of_mem Hm φ'' x i).symm
  have hs2 : ∀ x : Hm.Ω 1, ∀ i, (hG.precedes hG' hp).restrictφ φ₁ (x, i) = svec Gp φ₁ x i := by
    intro x i
    have hx : (x : CTorus d L N₁ m₁ K) ∈ Gp.Ω 1 := (hG.precedes hG' hp).mem_Ω1 x.2
    rw [svec_of_mem' _ hx]; rfl
  have hA : ∑ x : Hm.Ω 1, ∑ i, φ'' (x, i) * ((hG.precedes hG' hp).restrictφ φ₁ (x, i) - D'.h x i) =
      ∑ x : CTorus d L N₁ m₁ K, ∑ i, svec Hm φ'' x i * (svec Gp φ₁ x i - D'.h x i) := by
    rw [← hG.sum_ΩC (fun x => ∑ i, svec Hm φ'' x i * (svec Gp φ₁ x i - D'.h x i))]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hs1, hs2]
  have hB : ∑ x : Hm.Ω 1, ∑ i, φ'' (x, i) * φ'' (x, i) =
      ∑ x : CTorus d L N₁ m₁ K, ∑ i, svec Hm φ'' x i * svec Hm φ'' x i := by
    rw [← hG.sum_ΩC (fun x => ∑ i, svec Hm φ'' x i * svec Hm φ'' x i)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hs1]
  rw [hA, hB]
  simp only [Finset.sum_add_distrib, Complex.ofReal_one, one_mul, ← Finset.mul_sum]
  ring

open Classical in
/-- **The mass variation `V_{ν,1}(ψ')` as a function of the raw data and the tangent**
(`0` for unrealizable data), as `interactionOne`: `Θ = rawOf D'`, `ψ'` the tangent `D.Ψ - ψ^{(k)}`
of a datum `D` of level `n` with the same `h̃`. -/
noncomputable def nuOne (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (hp : n + 1 ≤ K)
    (a₁ ν eps : ℝ)
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) : ℂ :=
  if h : ∃ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D' ∧ u.1 = rawOf D' then
    if h2 : ∃ D : BgData Hm N, (∀ x i, D.h x i = h.choose.h x i) ∧
        compTangent hG hG' hp (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) h.choose) h.choose D = u.2 then
      massVar 1 (hG.precedes hG' hp)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) h.choose) h.choose.h
        (bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) h2.choose -
          (hG.precedes hG' hp).restrictφ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) h.choose))
    else 0
  else 0

theorem nuOne_eq (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (hp : n + 1 ≤ K)
    {a₁ ν eps : ℝ} {D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D')
    {D : BgData Hm N} (hh : ∀ x i, D.h x i = D'.h x i) :
    nuOne hG hG' hp a₁ ν eps (rawOf D', compTangent hG hG' hp (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D) =
      massVar 1 (hG.precedes hG' hp) (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D'.h
        (bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) D -
          (hG.precedes hG' hp).restrictφ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D')) := by
  classical
  have h : ∃ D'' : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D'' ∧ rawOf D' = rawOf D'' :=
    ⟨D', hD, rfl⟩
  have e1 : h.choose = D' := (BgData.eq_of_raw h.choose_spec.2).symm
  have h2 : ∃ D₂ : BgData Hm N, (∀ x i, D₂.h x i = h.choose.h x i) ∧
      compTangent hG hG' hp (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) h.choose) h.choose D₂ =
      compTangent hG hG' hp (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D := by
    rw [e1]; exact ⟨D, hh, rfl⟩
  unfold nuOne
  simp only [h, h2, dite_true]
  have e2 : h2.choose = D := by
    obtain ⟨hh2, ht2⟩ := h2.choose_spec
    have e3 : composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) h.choose) h.choose =
        composeData (hG.precedes hG' hp) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' := by rw [e1]
    have hΨ : h2.choose.Ψ = D.Ψ := by
      funext x i
      have := congrFun (congrFun ht2 x) i
      simp only [compTangent, e3] at this
      linear_combination this
    have hhh : h2.choose.h = D.h := by
      funext x i; rw [hh2 x i, hh x i, e1]
    exact BgData.eq_of_raw (Prod.ext hΨ hhh)
  have key : ∀ (A : BgData Gp N) (B : BgData Hm N), A = D' → B = D →
      massVar 1 (hG.precedes hG' hp) (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) A) A.h
        (bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) B -
          (hG.precedes hG' hp).restrictφ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) A)) =
      massVar 1 (hG.precedes hG' hp) (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D'.h
        (bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) D -
          (hG.precedes hG' hp).restrictφ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D')) := by
    rintro A B rfl rfl; rfl
  exact key _ _ e1 e2

end Bridge

/-- A derivative along a line only depends on the function on the line. -/
theorem lineD_congr_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ}
    {z w : E} {r : ℝ} (hr : 0 < r)
    (h : ∀ τ : ℂ, ‖τ‖ < r → f (z + τ • w) = g (z + τ • w)) : lineD w f z = lineD w g z := by
  unfold lineD
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with τ hτ using h τ (by simpa using hτ)


section NuPart

variable {j : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → ℕ}
variable {X 𝒦X : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Set (CTorus d L N₁ m₁ K)}
variable {X₁z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Finset (CTorus d L N₁ m₁ K)}
variable {m₀ : ℕ}

/-- **The `ν`-part of the localized interaction** (FLUCTUATION Prop. 3.3, `V_{ν,1}`, `k ≤ k₀`):
`σ ∫₀¹ ω(t') ∂_w V_{ν,1}(σ t' x₀) dt'` (`V_{ν,1}` along the decoupled fluctuation, `nuTotal`) is a
localized expansion over the domains `Y ⊃ X₁(z)`, with the bound
`|σ| M_ω (∑_{z : Y ∈ 𝒴_z} 𝒩 e^{-2κ d̃^cov(Y)}) / r`. -/
theorem nupart_locInt (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hp : n + 1 ≤ K) (hG' : IsLevel Gp (n + 1)) {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : ∀ z, CovSetup Gp m₀ (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁z z) : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne m₀ (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (j z)) E₀ = treeLenCovOne m₀ (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne m₀ (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZ : ∀ z, (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)) ⊆ ↑(X₁z z))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ T : Set (CTorus d L N₁ m₁ K) → (CTorus d L N₁ m₁ K → Fin N → ℂ) →
        (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) K N → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) T
        (fun x₀ w σ Θ => dirTermSrc (onXi Gp a₁ ν eps
          (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ')) ω x₀ w σ Θ)
        (fun Y => Mω * ((∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
          nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
            Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) else 0) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
  classical
  have hex : ∀ z, ∃ Ev : Set (CTorus d L N₁ m₁ K) →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁,
        nuBlockFun Gp Hm n z (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ')
          (rawOf D, ψ') = ∑ Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z), Ev Y (rawOf D, ψ')) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet Gp Y) u.1 u'.1 → (∀ y ∈ psiThick Y, u.2 y = u'.2 y) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ‖Ev Y u‖ ≤ nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁)) :=
    fun z => nublock_expansion hC hp hG' hBh0 hBh (hcov z) (hX₁ z) hconn hrow (hopt z) (hΔ z)
      hκ₀ hκdec hκ h1 hlog z (hZ z)
  choose Ev hsum hloc hbd han using hex
  refine ⟨fun Y x₀ w σ Θ => dirTerm (fun u => ∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
    Ev z Y u else 0) ω x₀ w σ Θ, ?_⟩
  refine locInt_dir1 (S := XiCRaw Gp (compWeight L a₁) ν K 1 eps) (B := FlBall Hm δ₁)
    (f := onXi Gp a₁ ν eps (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ'))
    (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z))
    (Evs := fun Y u => ∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then Ev z Y u else 0)
    (b := fun Y => ∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
      nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
        (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
        Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) else 0)
    (AgΘ := fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
    (AgF := fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) (Rσ := Rσ) hR₁ hω hωc hMω hωb hr
    (isOpen_flBall (N := N) Hm δ₁) ?_ ?_ ?_ ?_ ?_
  · intro Y u hu
    refine Finset.analyticAt_fun_sum _ fun z _ => ?_
    by_cases hY : Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)
    · simpa only [hY, ite_true] using han z Y u hu
    · simp only [hY, ite_false]; exact analyticAt_const
  · intro Y u hu
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
    by_cases hY : Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)
    · simpa only [hY, ite_true] using hbd z Y u hu
    · simp [hY]
  · intro Y a a' c' c'' p q ha hb y hy
    simp [ha y hy, hb y hy]
  · intro Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2'
    refine Finset.sum_congr rfl fun z'' _ => ?_
    by_cases hY : Y ∈ polyDom Gp (X₁z z'') m₀ (j z'') (𝒦X z'')
    · simp only [hY, ite_true]
      exact hloc z'' Y (Θ, z) ⟨hΘ, hz⟩ (Θ', z') ⟨hΘ', hz'⟩ h1' h2'
    · simp [hY]
  · rintro Θ ⟨D, hD, rfl⟩ ψ' hψ
    rw [onXi_rawOf hD, ← sum_nuBlockFun (n := n) a₁ ν BG₂ κ D ψ', Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hsum z D hD ψ' hψ, Finset.sum_ite_mem,
      Finset.inter_eq_right.2 (Finset.subset_biUnion_of_mem
        (fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) (Finset.mem_univ z))]

theorem nupart_locInt_bound (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hp : n + 1 ≤ K) (hG' : IsLevel Gp (n + 1)) {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : ∀ z, CovSetup Gp m₀ (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁z z) : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne m₀ (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (j z)) E₀ = treeLenCovOne m₀ (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne m₀ (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZ : ∀ z, (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)) ⊆ ↑(X₁z z))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ T : Set (CTorus d L N₁ m₁ K) → (CTorus d L N₁ m₁ K → Fin N → ℂ) →
        (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) K N → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) T
        (fun x₀ w σ Θ => dirTermSrc (onXi Gp a₁ ν eps
          (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ')) ω x₀ w σ Θ)
        (fun Y => Mω * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
          nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hB1 : 0 ≤ K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh := by
    have hK4 : 0 < K4 d L N BG κ := K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0
    have hx1 := one_le_xiC1 d
    have hx2 := hC.eps_pos
    have hx3 : 0 ≤ xiC1 d * eps := by positivity
    have hx4 := mul_nonneg hK4.le hx3
    linarith
  have hEb : 0 ≤ nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) := by
    unfold nuBd; positivity
  obtain ⟨T, hT⟩ := nupart_locInt hC hp hG' hBh0 hBh hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1
    hlog hZ hωc hR₁ hω hMω hωb hr (Rσ := Rσ)
  refine ⟨T, hT.mono_on fun Y hY => ?_⟩
  obtain ⟨z₀, -, hz₀⟩ := Finset.mem_biUnion.1 hY
  have hMD := polyDom_isMultiDom (hcov z₀) hd (hopt z₀) hz₀
  have hcard : ((Finset.univ.filter fun z => Y ∈ polyDom Gp (X₁z z) m₀ (j z)
      (𝒦X z)).card : ℝ) ≤ c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCov Gp m₀ Y) := by
    refine card_blocks_filter_le hG' hp (hcov z₀).hN hMD _ (fun z hz => ?_)
    have h1' := subset_polyDom (Finset.mem_filter.1 hz).2
    rw [← hX₁ z] at h1'
    exact fun x hx => h1' (hZ z hx)
  have ht0 := treeLenCov_nonneg Gp m₀ Y
  have hv : 0 ≤ nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
        Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) := by positivity
  have hs := sum_ite_card_le _ hv hcard
  rw [← treeLenCov_eq_treeLenCovOne hG' m₀ Y]
  have key := one_add_mul_exp_le (treeLenCov Gp m₀ Y) κdec
  have hCn : 0 ≤ Mω * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
      nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
        (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) := by positivity
  calc Mω * ((∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
          nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
            Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) else 0) / r)
      ≤ Mω * ((c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCov Gp m₀ Y) *
          (nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
            Real.exp (-2 * κdec * treeLenCov Gp m₀ Y))) / r) := by
        refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hs hr.le) hMω
    _ = (Mω * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
          nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r)) *
          ((1 + treeLenCov Gp m₀ Y) * Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key hCn

theorem nupart_locInt_phys (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hp : n + 1 ≤ K) (hG' : IsLevel Gp (n + 1)) {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hG : IsLevel Hm n) (ha₁ : 0 < a₁) (H : BgHyp d L K ϱm (compWeight L a₁) ν)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hreal : ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D' →
      ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' hp (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' hp) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' hp) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : ∀ z, CovSetup Gp m₀ (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁z z) : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne m₀ (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (j z)) E₀ = treeLenCovOne m₀ (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne m₀ (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZ : ∀ z, (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)) ⊆ ↑(X₁z z))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ T : Set (CTorus d L N₁ m₁ K) → (CTorus d L N₁ m₁ K → Fin N → ℂ) →
        (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) K N → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
          IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2} Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) T
        (fun x₀ w σ Θ => dirTermSrc (nuOne hG hG' hp a₁ ν eps) ω x₀ w σ Θ)
        (fun Y => Mω * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
          nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
  classical
  obtain ⟨T, hT⟩ := nupart_locInt_bound hC hp hG' hBh0 hBh hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ
    h1 hlog hZ hωc hR₁ hω hMω hωb hr (Rσ := Rσ)
  refine ⟨T, (hT.mono_XW (fun xw hxw => hxw.1)).congr_val ?_⟩
  rintro ⟨x₀, w⟩ ⟨hxw, hx0, hw⟩ σ hσ Θ ⟨D', hD, rfl⟩
  unfold dirTermSrc
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  simp only
  congr 1
  refine lineD_congr_line hr ?_
  intro τ hτ
  have ht' : ‖(t : ℂ)‖ < R₁ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  have hz1 : (σ * (t : ℂ)) • x₀ + τ • w ∈ FlBall Hm δ₁ := hxw σ hσ t ht' τ hτ.le
  have hlc : IsLayerConstant Hm ((σ * (t : ℂ)) • x₀ + τ • w) :=
    isLayerConstant_line (isLayerConstant_smul hx0 _) hw τ
  obtain ⟨D, hh, htan, hdisc⟩ := hreal D' hD _ hz1 hlc
  have hψ : compTangent hG hG' hp (compWeight L a₁)
      (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D ∈ FlBall Hm δ₁ := by
    rw [htan]; exact hz1
  show nuOne hG hG' hp a₁ ν eps (rawOf D', (σ * (t : ℂ)) • x₀ + τ • w) =
    onXi Gp a₁ ν eps (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ')
      (rawOf D', (σ * (t : ℂ)) • x₀ + τ • w)
  rw [onXi_rawOf hD, ← htan, nuOne_eq hG hG' hp hD hh]
  exact massVar_one_eq_nuTotal hC hG hG' hp ha₁ H D' hD hc7 D hh hψ hR hdisc hRs hsmall hnum hnum'

end NuPart

end Nu
