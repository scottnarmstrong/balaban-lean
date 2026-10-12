/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiProps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (Ξ2): membership under perturbation of the complex displacement

For `(Ψ₀ + Ψ'', h₀ + h'') ∈ Ξ^c_k(𝔹; 1, ε')` and a perturbation `δΨ` of the complex data of sup
size `≤ δ₃`, the perturbed datum `(Ψ₀ + Ψ'' + δΨ, h₀ + h'')` lies in `Ξ^c_k(𝔹; 1, ε' + K₂' δ₃)`
(`Balaban.SmallField.xiC_perturb`; `K₂' = xiK2`), the real part being unchanged.  The proof uses
`theorem52_perturb_eq` (BACKGROUND.md Theorem 5.2 (6)) for the increments `(δφ, δα)` of the
solution and `bgBounds_of_parts` for the bounds of the increment of the extension `φ̄`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}

/-- **The perturbed data domain**: if `(Ψ₀ + Ψ'', h₀ + h'') ∈ Ψ̃^c(δ, δ)` and `|δΨ| ≤ δ₃`, then
`(Ψ₀ + Ψ'' + δΨ, h₀ + h'') ∈ Ψ̃^c(δ + 5 δ₃, δ + 5 δ₃)` (for `δ ≤ 1/4`, `δ₃ ≤ 1`). -/
theorem perturb_inPsiTildeC {δ δ₃ : ℝ} (hδ : δ ≤ 1 / 4) (hδ₃ : 0 ≤ δ₃) (hδ₃1 : δ₃ ≤ 1)
    (hP : InPsiTildeC G ν δ δ Ψ₀ h₀ Ψ'' h'') {δΨ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hδΨc : IsLayerConstant G δΨ) (hδΨ : ∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₃) :
    InPsiTildeC G ν (δ + 5 * δ₃) (δ + 5 * δ₃) Ψ₀ h₀ (fun x i => Ψ'' x i + δΨ x i) h'' := by
  have hδ0 : 0 < δ := hP.eps_pos
  have hle : δ ≤ δ + 5 * δ₃ := by linarith
  refine ⟨hP.toInPsiTilde.mono hδ0.le hle, by linarith, ?_, hP.hLayerConst', ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn1 hnk x hx x' hx'
    funext i
    show Ψ'' x' i + δΨ x' i = Ψ'' x i + δΨ x i
    rw [congrFun (hP.layerConst' n hn1 hnk x hx x' hx') i,
      congrFun (hδΨc n hn1 hnk x hx x' hx') i]
  · intro x x' hxx'
    have h1 := hP.c1 x x' hxx'
    have h2 := hδΨ x hxx'.1
    have h3 := hδΨ x' hxx'.2.1
    have e : (fun i => Ψ'' x i + δΨ x i) - (fun i => Ψ'' x' i + δΨ x' i) =
        (fun i => (Ψ'' x - Ψ'' x') i + (δΨ x - δΨ x') i) := by
      funext i; simp only [Pi.sub_apply]; ring
    show vn ((fun i => Ψ'' x i + δΨ x i) - (fun i => Ψ'' x' i + δΨ x' i)) < _
    rw [e]
    have t := vn_add' (Ψ'' x - Ψ'' x') (δΨ x - δΨ x')
    have t2 := vn_sub_le_add (δΨ x) (δΨ x')
    linarith
  · intro x hx
    have h1 := hP.c2a x hx
    have h2 := hδΨ x hx
    have t := vn_add' (Ψ'' x) (δΨ x)
    linarith
  · intro x hx
    have hold := hP.c2b x hx
    have hr2 := hP.r2 x hx
    have hrn : rn (Ψ₀ x) ≤ 3 / 2 := by
      have hsq : rn (Ψ₀ x) ^ 2 ≤ 5 / 4 := by
        rw [rn_sq_sum]; have := (abs_lt.1 hr2).2; linarith
      nlinarith [rn_nonneg (Ψ₀ x)]
    have hΨ'' := hP.c2a x hx
    have hw : vn (fun i => (Ψ₀ x i : ℂ) + Ψ'' x i) ≤ 2 := by
      have e : vn (fun i => (Ψ₀ x i : ℂ)) = rn (Ψ₀ x) := vn_ofReal _
      have := vn_add' (fun i => (Ψ₀ x i : ℂ)) (Ψ'' x)
      linarith
    have h2 := hδΨ x hx
    have key : ∀ i, ((Ψ₀ x i : ℂ) + (Ψ'' x i + δΨ x i)) * ((Ψ₀ x i : ℂ) + (Ψ'' x i + δΨ x i)) -
        (Ψ₀ x i : ℂ) * (Ψ₀ x i : ℂ) =
        (((Ψ₀ x i : ℂ) + Ψ'' x i) * ((Ψ₀ x i : ℂ) + Ψ'' x i) - (Ψ₀ x i : ℂ) * (Ψ₀ x i : ℂ)) +
        (2 * (((Ψ₀ x i : ℂ) + Ψ'' x i) * δΨ x i) + δΨ x i * δΨ x i) := fun i => by ring
    have e : ∑ i, ((Ψ₀ x i : ℂ) + (Ψ'' x i + δΨ x i)) * ((Ψ₀ x i : ℂ) + (Ψ'' x i + δΨ x i)) -
        ∑ i, (Ψ₀ x i : ℂ) * (Ψ₀ x i : ℂ) =
        (∑ i, ((Ψ₀ x i : ℂ) + Ψ'' x i) * ((Ψ₀ x i : ℂ) + Ψ'' x i) -
          ∑ i, (Ψ₀ x i : ℂ) * (Ψ₀ x i : ℂ)) +
        (2 * ∑ i, ((Ψ₀ x i : ℂ) + Ψ'' x i) * δΨ x i + ∑ i, δΨ x i * δΨ x i) := by
      rw [← Finset.sum_sub_distrib]
      simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
    show ‖∑ i, ((Ψ₀ x i : ℂ) + (Ψ'' x i + δΨ x i)) * ((Ψ₀ x i : ℂ) + (Ψ'' x i + δΨ x i)) -
      ∑ i, (Ψ₀ x i : ℂ) * (Ψ₀ x i : ℂ)‖ < _
    rw [e]
    have t1 : ‖∑ i, ((Ψ₀ x i : ℂ) + Ψ'' x i) * δΨ x i‖ ≤ 2 * δ₃ :=
      (norm_dot_le _ _).trans (mul_le_mul hw h2 (vn_nonneg _) (by norm_num))
    have t2 : ‖∑ i, δΨ x i * δΨ x i‖ ≤ δ₃ * δ₃ :=
      (norm_dot_le _ _).trans (mul_le_mul h2 h2 (vn_nonneg _) hδ₃)
    have n2 : ‖(2 : ℂ)‖ = 2 := by simp
    have hB : ‖2 * ∑ i, ((Ψ₀ x i : ℂ) + Ψ'' x i) * δΨ x i + ∑ i, δΨ x i * δΨ x i‖ ≤
        2 * (2 * δ₃) + δ₃ * δ₃ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ t2)
      rw [norm_mul, n2]
      exact mul_le_mul_of_nonneg_left t1 (by norm_num)
    have hA := norm_add_le (∑ i, ((Ψ₀ x i : ℂ) + Ψ'' x i) * ((Ψ₀ x i : ℂ) + Ψ'' x i) -
      ∑ i, (Ψ₀ x i : ℂ) * (Ψ₀ x i : ℂ)) (2 * ∑ i, ((Ψ₀ x i : ℂ) + Ψ'' x i) * δΨ x i +
        ∑ i, δΨ x i * δΨ x i)
    nlinarith
  · intro x hx
    have h := hP.c3a x hx
    have e : δ ^ 2 / δ = δ := by field_simp
    have e2 : (δ + 5 * δ₃) ^ 2 / (δ + 5 * δ₃) = δ + 5 * δ₃ := by
      have : 0 < δ + 5 * δ₃ := by linarith
      field_simp
    rw [e] at h
    rw [e2]
    linarith
  · intro x hx
    have h := hP.c3b x hx
    refine h.trans_le (pow_le_pow_left₀ hδ0.le hle 2)

/-- The constant `K₂'` of (Ξ2): `1 + L + 2 d L² + (N + 1) K₂`. -/
noncomputable def xiK2 (d L N : ℕ) [NeZero L] : ℝ :=
  1 + L + 2 * d * (L : ℝ) ^ 2 + (N + 1) * cK2 d L N

theorem xiBounds_mono {ν σ ε ε₂ : ℝ} {n : ℕ} {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ}
    {α : G.Ω 1 → ℂ} (hσ : 0 ≤ σ) (hε0 : 0 ≤ ε) (hε : ε ≤ ε₂) (hb : XiBounds G ν n σ ε D h₀ φ α) :
    XiBounds G ν n σ ε₂ D h₀ φ α := by
  have h1 : σ * ε ≤ σ * ε₂ := mul_le_mul_of_nonneg_left hε hσ
  have h2 : σ ^ 2 * ε ≤ σ ^ 2 * ε₂ := mul_le_mul_of_nonneg_left hε (by positivity)
  have hp : ∀ x : Torus d (N₀ * L ^ k), 0 < G.spacing x := fun x => by
    have := G.spacing_ge_one x; linarith
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x hx => ?_, fun z hz z' hz' hadj => ?_,
    fun z => ?_, ?_⟩
  · obtain ⟨g1, g2⟩ := hb.grad x hx μ
    exact ⟨g1.trans_le (div_le_div_of_nonneg_right h1 (hp x).le),
      g2.trans_le (div_le_div_of_nonneg_right h1 (hp x).le)⟩
  · exact (hb.lap x hx).trans_le (div_le_div_of_nonneg_right h2 (by have := hp x; positivity))
  · exact (hb.mult x).trans_le h2
  · exact (hb.close x hx).trans_le h2
  · exact (hb.collarBond z hz z' hz' hadj).trans_le h1
  · exact (hb.mass z).trans_le h1
  · exact hb.hnorm.trans_le (pow_le_pow_left₀ (mul_nonneg hσ hε0) h1 2)

omit [NeZero N₀] [NeZero L] in
theorem vn_add_diff (A1 A0 E1 E0 : Fin N → ℂ) :
    vn (fun i => (A1 i + E1 i) - (A0 i + E0 i)) ≤
      vn (fun i => A1 i - A0 i) + vn (fun i => E1 i - E0 i) := by
  have := vn_add' (fun i => A1 i - A0 i) (fun i => E1 i - E0 i)
  have e : (fun i => (A1 i + E1 i) - (A0 i + E0 i)) =
      fun i => (A1 i - A0 i) + (E1 i - E0 i) := by funext i; ring
  rw [e]; exact this

omit [NeZero N₀] [NeZero L] in
theorem lap_add (A E : Torus d (N₀ * L ^ k) → Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) {r₁ r₂ : ℝ}
    (hA : vn (fun i => ∑ μ : Fin d,
      (A (x + Pi.single μ 1) i + A (x - Pi.single μ 1) i - 2 * A x i)) < r₁)
    (hE : vn (fun i => ∑ μ : Fin d,
      (E (x + Pi.single μ 1) i + E (x - Pi.single μ 1) i - 2 * E x i)) ≤ r₂) :
    vn (fun i => ∑ μ : Fin d, ((A (x + Pi.single μ 1) i + E (x + Pi.single μ 1) i) +
      (A (x - Pi.single μ 1) i + E (x - Pi.single μ 1) i) - 2 * (A x i + E x i))) < r₁ + r₂ := by
  have h := vn_add' (fun i => ∑ μ : Fin d,
      (A (x + Pi.single μ 1) i + A (x - Pi.single μ 1) i - 2 * A x i))
    (fun i => ∑ μ : Fin d, (E (x + Pi.single μ 1) i + E (x - Pi.single μ 1) i - 2 * E x i))
  have e : (fun i => ∑ μ : Fin d, ((A (x + Pi.single μ 1) i + E (x + Pi.single μ 1) i) +
      (A (x - Pi.single μ 1) i + E (x - Pi.single μ 1) i) - 2 * (A x i + E x i))) =
      fun i => (∑ μ : Fin d, (A (x + Pi.single μ 1) i + A (x - Pi.single μ 1) i - 2 * A x i)) +
        ∑ μ : Fin d, (E (x + Pi.single μ 1) i + E (x - Pi.single μ 1) i - 2 * E x i) := by
    funext i
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun μ _ => by ring
  rw [e]
  linarith

section Perturb

variable (G)

/-- The datum `Ψ^c + δΨ` (on `Ω₁ ∪ C(Ω₁)`) with the same `h̃`. -/
noncomputable def perturbData (Dc : BgData G N) (δΨ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hδΨc : IsLayerConstant G δΨ) : BgData G N where
  Ψ := fun x i => Dc.Ψ x i + (by classical exact if x ∈ dataSites G then δΨ x i else 0)
  h := Dc.h
  Ψ_layerConst := by
    intro n hn1 hnk x hx x' hx'
    have hxΩ : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
    have hx'l : x' ∈ G.layer n := (G.mem_layer_iff hn1 hnk (GeneratingSet.mem_blk.1 hx')).2 hx
    have hx'Ω : x' ∈ G.Ω 1 := G.layer_subset hn1 hnk hx'l
    have h1 : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hxΩ)
    have h2 : x' ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx'Ω)
    funext i
    simp only [h1, h2, ↓reduceIte]
    rw [congrFun (Dc.Ψ_layerConst n hn1 hnk x hx x' hx') i,
      congrFun (hδΨc n hn1 hnk x hx x' hx') i]
  h_layerConst := Dc.h_layerConst
  Ψ_zero := by
    intro x hx
    funext i
    simp [hx, Dc.Ψ_zero x hx]
  h_zero := Dc.h_zero

variable {G}

theorem perturbData_Ψ {Dc : BgData G N} {δΨ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {hδΨc : IsLayerConstant G δΨ} {y : Torus d (N₀ * L ^ k)} (hy : y ∈ dataSites G) (i : Fin N) :
    (perturbData G Dc δΨ hδΨc).Ψ y i = Dc.Ψ y i + δΨ y i := by
  simp [perturbData, hy]

end Perturb

/-- **(Ξ2)** (BACKGROUND.md Theorem 5.2 (6); P3 (4.34)-(4.35)): the perturbed datum lies in
`Ξ^c_k(𝔹; 1, ε' + K₂' δ₃)`.  Hypotheses: `(Ψ₀ + Ψ'', h₀ + h'') ∈ Ξ^c_k(𝔹; 1, ε')` with
`(4d+6)(2d+1) ε' ≤ 1`, a layer-constant perturbation with `|δΨ| ≤ δ₃` on `Ω₁ ∪ C(Ω₁)`, and the
smallness conditions of Proposition 5.1 / Theorem 5.2 (6) for `δ = C₁ ε'`
(`δ₃ ≤ δ_*`, `K₁ δ ≤ δ_*`, `K₁ δ + K₂ δ₃ < c₀`) and of the data domain
(`C₁ ε' + 5 δ₃ ≤ c₁`, `δ₃ ≤ 1`). -/
theorem xiC_perturb (H : BgHyp d L k ϱ a ν) {ε' δ₃ : ℝ} (hδ₃ : 0 ≤ δ₃) (hδ₃1 : δ₃ ≤ 1)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε') ≤ 1)
    (hδ₂ : xiC1 d * ε' + 5 * δ₃ ≤ bgC1 d L N)
    (hstar : δ₃ ≤ deltaStar d L N) (hK1s : bgK1 d L N * (xiC1 d * ε') ≤ deltaStar d L N)
    (hsm : bgK1 d L N * (xiC1 d * ε') + cK2 d L N * δ₃ < bgC0 d L N)
    {δΨ : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hδΨc : IsLayerConstant G δΨ)
    (hδΨ : ∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₃)
    (hX : XiC G a ν k 1 ε' Ψ₀ h₀ Ψ'' h'') :
    XiC G a ν k 1 (ε' + xiK2 d L N * δ₃) Ψ₀ h₀ (fun x i => Ψ'' x i + δΨ x i) h'' := by
  have hP := xiC_one_subset H hsmall hX
  obtain ⟨-, hε, Dr, Dc, hXr, hC, hDcU, hb⟩ := hX
  have hd0 : 0 < d := by have := H.hd; omega
  have hc1 := one_le_xiC1 d
  have hK2 : 0 < cK2 d L N := cK2_pos d L N
  set δ := xiC1 d * ε' with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδc : δ ≤ bgC1 d L N := by linarith
  have hδ1 : δ ≤ 1 / 4 := by
    have := (approxDelta_le d L (bgC1_facts d L N hd0 hδc).1).1
    linarith
  have hP' := perturb_inPsiTildeC hδ1 hδ₃ hδ₃1 hP hδΨc hδΨ
  set Dc' := perturbData G Dc δΨ hδΨc with hDc'
  have hC' : RealizesC Dc' Ψ₀ h₀ (fun x i => Ψ'' x i + δΨ x i) h'' := by
    refine ⟨fun x hx i => ?_, fun x hx i => ?_⟩
    · rw [hDc', perturbData_Ψ hx, hC.1 x hx i]; ring
    · show Dc.h x i = _
      exact hC.2 x hx i
  have hDom' : InDomainC G ν (δ + 5 * δ₃) (δ + 5 * δ₃) Dc' :=
    ⟨Ψ₀, h₀, _, h'', hP', hC'.1, hC'.2⟩
  have hδ2c : δ + 5 * δ₃ ≤ bgC1 d L N := hδ₂
  have hδ2pos : 0 < δ + 5 * δ₃ := by linarith
  have hDcU' : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν Dc' :=
    ⟨δ + 5 * δ₃, δ + 5 * δ₃, hδ2pos, le_rfl, hδ2c.trans (bgC1_le_bgC0 d L N hd0), hδ2c, by
      have := H.massLe
      nlinarith [sq_nonneg (δ + 5 * δ₃)], hDom'⟩
  have hDDc : InDomainC G ν δ δ Dc := ⟨Ψ₀, h₀, Ψ'', h'', hP, hC.1, hC.2⟩
  obtain ⟨δφ, δα, hsup, hsmα, hf, hm⟩ := theorem52_perturb_eq (a := a) H hδ0 le_rfl
    (hδc.trans (bgC1_le_bgC0 d L N hd0)) hδc (by have := H.massLe; nlinarith [sq_nonneg δ])
    hDDc hDcU' (D' := Dc') rfl hδ₃ hstar hK1s
    (fun x hx => by
      have : Dc'.Ψ x - Dc.Ψ x = δΨ x := by
        funext i; simp only [Pi.sub_apply]; rw [hDc', perturbData_Ψ hx]; ring
      rw [this]; exact hδΨ x hx) hsm
  set c := xiK2 d L N * δ₃ with hc
  have hc0 : 0 ≤ c := by unfold xiK2 at hc; rw [hc]; positivity
  have hεb : 0 < ε' + c := by linarith
  have hxr' : XiAt G a ν k 1 (ε' + c) Dr Ψ₀ h₀ :=
    ⟨hXr.1, hXr.2.1, xiBounds_mono zero_le_one hε.le (by linarith) hXr.2.2⟩
  refine ⟨one_pos, hεb, Dr, Dc', hxr', hC', hDcU', ?_⟩
  rw [hf, hm]
  set ΔD : BgData G N := BgData.clip G δΨ (fun _ _ => 0) hδΨc (fun _ _ _ _ _ _ _ => rfl) with hΔD
  have hV : 0 ≤ cK2 d L N * δ₃ := by positivity
  have hKc : cK2 d L N * δ₃ ≤ c := by
    rw [hc]; unfold xiK2
    have : (0 : ℝ) ≤ 1 + L + 2 * d * (L : ℝ) ^ 2 := by positivity
    nlinarith [mul_nonneg hV hδ₃, mul_nonneg this hδ₃, mul_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) hV]
  have hE := bgBounds_of_parts (d := d) (L := L) (N₀ := N₀) (k := k) (N := N) (ϱ := ϱ) (G := G) (D := ΔD) (φ₀ := fun _ _ => (0 : ℂ)) (δφ := δφ) (c := c)
    (α := δα) (H.green (G := G)).sep_gt_one (by have := H.hL; omega) hδ₃ hV
    (by
      have k1 : ∀ x : Torus d (N₀ * L ^ k), 0 ≤ δ₃ / G.spacing x := fun x =>
        div_nonneg hδ₃ (by have := G.spacing_ge_one x; linarith)
      have k2 : ∀ x : Torus d (N₀ * L ^ k), 0 ≤ δ₃ / G.spacing x ^ 2 := fun x =>
        div_nonneg hδ₃ (by have := G.spacing_ge_one x; positivity)
      refine ⟨fun x hx μ => ⟨?_, ?_⟩, fun x hx => ?_⟩
      · simpa [vn_zero] using k1 x
      · simpa [vn_zero] using k1 x
      · simpa [show (fun _ : Fin N => (0 : ℂ)) = 0 from rfl, vn_zero] using k2 x)
    (fun y hy => by
      have e : ((fun _ _ => (0 : ℂ)) y - ΔD.Ψ y) = -δΨ y := by
        funext i; simp [hΔD, BgData.clip, hy]
      rw [e]
      have : vn (-δΨ y) = vn (δΨ y) := by
        have := vn_neg (δΨ y)
        exact this
      rw [this]; exact hδΨ y hy)
    hsup (fun x => (hsmα x).trans hKc) (by
      rw [hc]; unfold xiK2
      have : (0 : ℝ) ≤ cK2 d L N * δ₃ := hV
      nlinarith [mul_nonneg this (Nat.cast_nonneg N : (0:ℝ) ≤ N), hV, hδ₃])
  have hbar : ∀ (y : Torus d (N₀ * L ^ k)) (i : Fin N),
      barField G Dc'.Ψ (bgFieldC G a ν (bgC0 d L N) Dc + δφ) y i - barField G Dr.Ψ (bgField G a ν Dr) y i =
      (barField G Dc.Ψ (bgFieldC G a ν (bgC0 d L N) Dc) y i -
        barField G Dr.Ψ (bgField G a ν Dr) y i) +
      barField G ΔD.Ψ (fun p => (fun _ _ => (0 : ℂ)) p.1 p.2 + δφ p) y i := by
    intro y i
    by_cases hy : y ∈ G.Ω 1
    · simp [barField, hy]; ring
    · by_cases hd : y ∈ dataSites G
      · simp [barField, hy, hDc', hΔD, perturbData, BgData.clip, hd]; ring
      · have h0 := Dc.Ψ_zero y hd
        simp [barField, hy, hDc', hΔD, perturbData, BgData.clip, hd, h0]
  have h3L : (3 : ℝ) ≤ L := by exact_mod_cast H.hL
  have hNV : N * (cK2 d L N * δ₃) ≤ c := by
    rw [hc]; unfold xiK2
    nlinarith [mul_nonneg hV (Nat.cast_nonneg N : (0:ℝ) ≤ N), mul_nonneg hδ₃ (Nat.cast_nonneg d : (0:ℝ) ≤ d),
      mul_nonneg hδ₃ (sq_nonneg (L : ℝ)), mul_nonneg (mul_nonneg hδ₃ (Nat.cast_nonneg d : (0:ℝ) ≤ d)) (sq_nonneg (L : ℝ)), mul_nonneg hV hδ₃]
  have hNc : δ₃ + N * (cK2 d L N * δ₃) ≤ c := by
    rw [hc]; unfold xiK2
    nlinarith [mul_nonneg hV (Nat.cast_nonneg N : (0:ℝ) ≤ N), mul_nonneg hδ₃ (Nat.cast_nonneg d : (0:ℝ) ≤ d),
      mul_nonneg hδ₃ (sq_nonneg (L : ℝ)), mul_nonneg (mul_nonneg hδ₃ (Nat.cast_nonneg d : (0:ℝ) ≤ d)) (sq_nonneg (L : ℝ)), mul_nonneg hV hδ₃]
  have h2c : 2 * δ₃ ≤ c := by
    rw [hc]; unfold xiK2
    nlinarith [mul_nonneg hV (Nat.cast_nonneg N : (0:ℝ) ≤ N), mul_nonneg hδ₃ (Nat.cast_nonneg d : (0:ℝ) ≤ d),
      mul_nonneg hδ₃ (sq_nonneg (L : ℝ)), mul_nonneg (mul_nonneg hδ₃ (Nat.cast_nonneg d : (0:ℝ) ≤ d)) (sq_nonneg (L : ℝ)), mul_nonneg hV hδ₃]
  have hval : ∀ x : G.Ω 1, vn (fun i => δφ (x, i)) ≤ N * (cK2 d L N * δ₃) := fun x =>
    vn_le_card_mul hV fun i => by
      have := hsup.val x i
      rwa [svec_of_mem G δφ x i] at this
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_,
    fun z hz z' hz' hadj => ?_, fun x hx => ?_, fun x => ?_⟩
  · obtain ⟨o1, o2⟩ := hb.grad x hx μ
    obtain ⟨e1, e2⟩ := hE.grad ⟨x, hx⟩ μ
    have hs : 0 < G.spacing x := by have := G.spacing_ge_one x; linarith
    have key : 1 * (ε' + c) / G.spacing x = 1 * ε' / G.spacing x + c / G.spacing x := by ring
    simp only [hbar]
    refine ⟨lt_of_le_of_lt (vn_add_diff _ _ _ _) ?_, lt_of_le_of_lt (vn_add_diff _ _ _ _) ?_⟩
    · rw [key]; exact add_lt_add_of_lt_of_le o1 e1
    · rw [key]; exact add_lt_add_of_lt_of_le o2 e2
  · have o := hb.lap x hx
    have e := hE.lap ⟨x, hx⟩
    have hs : 0 < G.spacing x ^ 2 := by have := G.spacing_ge_one x; positivity
    have key : 1 ^ 2 * (ε' + c) / G.spacing x ^ 2 =
        1 ^ 2 * ε' / G.spacing x ^ 2 + c / G.spacing x ^ 2 := by ring
    simp only [hbar]
    refine lt_of_lt_of_le (lap_add (A := fun y i => barField G Dc.Ψ (bgFieldC G a ν (bgC0 d L N) Dc) y i -
      barField G Dr.Ψ (bgField G a ν Dr) y i) (E := fun y i => barField G ΔD.Ψ
      (fun p => (fun _ _ => (0 : ℂ)) p.1 p.2 + δφ p) y i) x o e) ?_
    exact le_of_eq (by ring)
  · -- mult
    have o := hb.mult x
    have sα := hsmα x
    have e : (bgMultC G a ν (bgC0 d L N) Dc + δα) x - bgMult G a ν Dr x =
        (bgMultC G a ν (bgC0 d L N) Dc x - bgMult G a ν Dr x) + δα x := by
      simp only [Pi.add_apply]; ring
    have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
    rw [e]
    calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
          ‖(bgMultC G a ν (bgC0 d L N) Dc x - bgMult G a ν Dr x) + δα x‖
        ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
          (‖bgMultC G a ν (bgC0 d L N) Dc x - bgMult G a ν Dr x‖ + ‖δα x‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hp
      _ = G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
          ‖bgMultC G a ν (bgC0 d L N) Dc x - bgMult G a ν Dr x‖ +
          G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖δα x‖ := by ring
      _ < 1 ^ 2 * (ε' + c) := by
          have : 1 ^ 2 * (ε' + c) = 1 ^ 2 * ε' + c := by ring
          rw [this]; linarith
  · -- val
    have o := hb.val x
    have e : (fun i => (bgFieldC G a ν (bgC0 d L N) Dc + δφ) (x, i) - bgField G a ν Dr (x, i)) =
        fun i => (bgFieldC G a ν (bgC0 d L N) Dc (x, i) - bgField G a ν Dr (x, i)) + δφ (x, i) := by
      funext i; simp only [Pi.add_apply]; ring
    rw [e]
    have t := vn_add' (fun i => bgFieldC G a ν (bgC0 d L N) Dc (x, i) - bgField G a ν Dr (x, i))
      (fun i => δφ (x, i))
    have := hval x
    linarith
  · -- close
    have o := hb.close x hx
    have hn := (G.layerIndex_spec hx).2.1
    have e : (fun i => (Ψ'' x i + δΨ x i) -
        blockAvg G ((bgFieldC G a ν (bgC0 d L N) Dc + δφ) - bgField G a ν Dr) x i) =
        fun i => (Ψ'' x i - blockAvg G (bgFieldC G a ν (bgC0 d L N) Dc - bgField G a ν Dr) x i) +
          (δΨ x i - blockAvg G δφ x i) := by
      funext i
      have : (bgFieldC G a ν (bgC0 d L N) Dc + δφ) - bgField G a ν Dr =
          (bgFieldC G a ν (bgC0 d L N) Dc - bgField G a ν Dr) + δφ := by abel
      rw [this, blockAvg_add]; ring
    rw [e]
    have t := vn_add' (fun i => Ψ'' x i -
      blockAvg G (bgFieldC G a ν (bgC0 d L N) Dc - bgField G a ν Dr) x i)
      (fun i => δΨ x i - blockAvg G δφ x i)
    have t2 := vn_sub_le_add (δΨ x) (fun i => blockAvg G δφ x i)
    have t3 : vn (fun i => blockAvg G δφ x i) ≤ N * (cK2 d L N * δ₃) := by
      have := vn_blockMean_le (G := G) hn (fun y i => svec G δφ y i) x
        (c := N * (cK2 d L N * δ₃)) (fun y hy => vn_le_card_mul hV fun i => hsup.val y i)
      exact this
    have t4 := hδΨ x ((mem_dataSites G).2 (Or.inl hx))
    have e2 : (fun i => δΨ x i - blockAvg G δφ x i) = δΨ x - fun i => blockAvg G δφ x i := rfl
    rw [e2] at t
    have : 1 ^ 2 * (ε' + c) = 1 ^ 2 * ε' + c := by ring
    rw [this]
    linarith
  · -- collar bond
    have o := hb.collarBond z hz z' hz' hadj
    have t := vn_add_diff (Ψ'' z) (Ψ'' z') (δΨ z) (δΨ z')
    have t2 := vn_sub_le_add (δΨ z) (δΨ z')
    have t3 := hδΨ z ((mem_dataSites G).2 (Or.inr hz))
    have t4 := hδΨ z' ((mem_dataSites G).2 (Or.inr hz'))
    have e : vn (fun i => δΨ z i - δΨ z' i) = vn (δΨ z - δΨ z') := rfl
    have : 1 * (ε' + c) = 1 * ε' + c := by ring
    rw [this]
    linarith
  · -- hAbs
    have o := hb.hAbs x hx
    have e1 : (1 * ε') ^ 2 / ε' = ε' := by field_simp
    have e2 : (1 * (ε' + c)) ^ 2 / (ε' + c) = ε' + c := by field_simp
    rw [e1] at o
    rw [e2]
    linarith
  · -- hDot
    have o := hb.hDot x
    exact o.trans_le (pow_le_pow_left₀ (by linarith) (by linarith) 2)

end Balaban.SmallField
