/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Def5
public import Balaban.Background.Perturb
public import Balaban.Background.Mass116
public import Balaban.Background.Composition
public import Balaban.Background.CompositionSystem
public import Balaban.Background.CompositionDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 7.3: the composition identities for the defined background fields (BACKGROUND.md §7)

Assembly of I-2 for `bgField`, `bgMult`, `bgFieldC`, `bgMultC` from the landed pieces
(`Def5`, `Theorem52*`, `Composition*`).  The weights are `a = compWeight L a₁` (6.1).

The domain constant of this theorem is `thm73C1 = c₁ / (2 C₄ K₁)` (`C₄ = compC4 d = 4d + 8`): a
datum of `𝔹'_k` with `δ ≤ thm73C1` is mapped by the composition (6.2) to a datum of `𝔹_j` with
`δ_j = 2 C₄ K₁ δ ≤ c₁` (so Theorem 5.2 applies to `𝔹_j`), `K₁ δ ≤ c₀ / 4`, and the smallness
`(4d + 6) K₁ δ ≤ 1` of `lemma62` and `K₁ δ ≤ δ_*` of Proposition 5.1 hold.  The uniqueness
statement for the composed system `𝒮` is in the class `|α|'₂ < c₀ / 2` (so that `2 (c₀ / 2) ≤ c₆`,
as `composedSystem_unique_lt` requires; the small solution has `|α|'₂ ≤ K₁ δ ≤ c₀ / 4`).
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-! ### The constant of Theorem 7.3 -/

/-- The domain constant of Theorem 7.3: `c₁ / (2 C₄ K₁)`. -/
noncomputable def thm73C1 (d L N : ℕ) [NeZero L] : ℝ :=
  bgC1 d L N / (2 * (compC4 d * bgK1 d L N))

theorem compC4_ge (d : ℕ) : (8 : ℝ) ≤ compC4 d := by
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  unfold compC4; linarith

/-- The smallness consequences of `δ ≤ thm73C1`. -/
theorem thm73_small (hd : 0 < d) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ thm73C1 d L N) :
    δ ≤ bgC1 d L N ∧ 2 * (compC4 d * (bgK1 d L N * δ)) ≤ bgC1 d L N ∧
      bgK1 d L N * δ ≤ bgC0 d L N / 4 ∧ bgK1 d L N * δ ≤ deltaStar d L N ∧
      (4 * d + 6) * (bgK1 d L N * δ) ≤ 1 := by
  have hK1 := bgK1_ge_one d L N
  have hC4 := compC4_ge d
  have hx : 0 < bgK1 d L N * δ := by positivity
  have h2 : 2 * (compC4 d * (bgK1 d L N * δ)) ≤ bgC1 d L N := by
    unfold thm73C1 at hδ
    rw [le_div_iff₀ (by positivity)] at hδ
    calc 2 * (compC4 d * (bgK1 d L N * δ)) = δ * (2 * (compC4 d * bgK1 d L N)) := by ring
      _ ≤ _ := hδ
  have hc10 := bgC1_le_bgC0 d L N hd
  have hc0 := bgC0_le d L N
  have h16 : 16 * (bgK1 d L N * δ) ≤ bgC1 d L N := by nlinarith
  have hxc1 : bgK1 d L N * δ ≤ bgC1 d L N := by linarith
  refine ⟨by nlinarith, h2, by linarith, ?_, ?_⟩
  · obtain ⟨-, h2', -, -⟩ := bgC1_facts d L N hd hxc1
    have := cB7_pos d L
    have := cB7_le_const d L
    nlinarith
  · have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    unfold compC4 at h2
    nlinarith

/-! ### From `BgBounds` to the hypotheses of the composition lemmas -/

section Bridge

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {a : ℕ → ℝ} {ν : ℝ}

theorem barField_congr_data {Ψ₁ Ψ₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hΨ : ∀ x ∈ dataSites G, ∀ i, Ψ₁ x i = Ψ₂ x i) (φ : G.Ω 1 × Fin N → ℂ)
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ dataSites G) (i : Fin N) :
    barField G Ψ₁ φ y i = barField G Ψ₂ φ y i := by
  by_cases h : y ∈ G.Ω 1
  · simp [barField, h]
  · simp only [barField, h, ↓reduceDIte]
    exact hΨ y hy i

theorem nbr_mem_dataSites {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (μ : Fin d) :
    x + Pi.single μ 1 ∈ dataSites G ∧ x - Pi.single μ 1 ∈ dataSites G := by
  classical
  refine ⟨(mem_dataSites G).2 ?_, (mem_dataSites G).2 ?_⟩
  · by_cases h : x + Pi.single μ 1 ∈ G.Ω 1
    · exact Or.inl h
    · exact Or.inr (mem_collar_of_adj G hx h (adj_add_single x μ))
  · by_cases h : x - Pi.single μ 1 ∈ G.Ω 1
    · exact Or.inl h
    · exact Or.inr (mem_collar_of_adj G hx h (adj_sub_single x μ))

/-- The bounds of Theorem 5.2 (3) (`BgBounds`) give the `FieldBounds` hypothesis of the
composition lemmas, for any lifted field `Ψ'` that agrees with the datum on `Ω₁ ∪ C(Ω₁)`. -/
theorem fieldBounds_of_bgBounds {D : BgData G N} {Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hΨ : ∀ x ∈ dataSites G, ∀ i, Ψ' x i = D.Ψ x i) {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    {c : ℝ} (hb : BgBounds G D φ α c) (hu : ∀ z : G.Ω 1, ∑ i, φ (z, i) * φ (z, i) = 1) :
    FieldBounds G c Ψ' φ := by
  have hbar : ∀ y ∈ dataSites G, barVec G Ψ' φ y = barField G D.Ψ φ y := fun y hy =>
    funext fun i => barField_congr_data hΨ φ hy i
  refine ⟨fun z => ?_, ⟨fun x hx μ => ?_, fun x hx => ?_⟩, hu⟩
  · have := hb.val z
    have e : (fun i => φ (z, i) - Ψ' z i) = fun i => φ (z, i) - D.Ψ z i :=
      funext fun i => by rw [hΨ z ((mem_dataSites G).2 (Or.inl z.2)) i]
    rw [e]; exact this
  · obtain ⟨n1, n2⟩ := nbr_mem_dataSites hx μ
    have hx' : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    obtain ⟨g1, g2⟩ := hb.grad ⟨x, hx⟩ μ
    rw [hbar _ n1, hbar _ n2, hbar _ hx']
    exact ⟨g1, g2⟩
  · have hx' : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have e : (fun i => ∑ μ : Fin d, (barVec G Ψ' φ (x + Pi.single μ 1) i +
          barVec G Ψ' φ (x - Pi.single μ 1) i - 2 * barVec G Ψ' φ x i)) =
        fun i => ∑ μ : Fin d, (barField G D.Ψ φ (x + Pi.single μ 1) i +
          barField G D.Ψ φ (x - Pi.single μ 1) i - 2 * barField G D.Ψ φ x i) := by
      funext i
      refine Finset.sum_congr rfl fun μ _ => ?_
      obtain ⟨n1, n2⟩ := nbr_mem_dataSites hx μ
      rw [hbar _ n1, hbar _ n2, hbar _ hx']
    rw [e]
    exact hb.lap ⟨x, hx⟩

/-- **The hypotheses (P1)-(P4) of Proposition 5.1 at the small solution** (`f₁ = 0`,
`δ₀ = K₁ δ`), from the bounds of Theorem 5.2 (3), for a displacement `δΨ` of size `δ₁`. -/
theorem prop51Hyp_of_bgBounds (H : BgHyp d L k ϱ a ν) {δ ε : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ bgC1 d L N) {D : BgData G N} (W : DataWit G ν δ ε D) (hε : ε ≤ bgC0 d L N)
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hunit : ∀ x : G.Ω 1, ∑ i, φ (x, i) * φ (x, i) = 1)
    (hb : BgBounds G D φ α (bgK1 d L N * δ)) (hK : bgK1 d L N * δ ≤ deltaStar d L N)
    {δΨ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {δ₁ : ℝ} (hδ₁ : 0 ≤ δ₁) (hδ₁s : δ₁ ≤ deltaStar d L N)
    (hdΨ : ∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₁) :
    Prop51Hyp G a ν α (barField G D.Ψ φ) δΨ (0 : G.Ω 1 × Fin N → ℂ) (bgK1 d L N * δ) δ₁ := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hK1 := bgK1_pos d L N
  have hK1δ : 0 ≤ bgK1 d L N * δ := by positivity
  obtain ⟨hδa, -, -, hKc⟩ := bgC1_facts d L N hd0 hδ
  have hbar : ∀ (x : Torus d (N₀ * L ^ k)) (hx : x ∈ G.Ω 1),
      barField G D.Ψ φ x = fun i => φ (⟨x, hx⟩, i) := by
    intro x hx; funext i; simp [barField, hx]
  have hphi : ∀ x ∈ G.Ω 1, vn (barField G D.Ψ φ x) ≤ 3 / 2 := by
    intro x hx
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have h1 := hb.val ⟨x, hx⟩
    have h2 := W.vn_le hδ0 hxd
    have e : barField G D.Ψ φ x = (fun i => φ (⟨x, hx⟩, i) - D.Ψ x i) + D.Ψ x := by
      rw [hbar x hx]; funext i; simp
    rw [e]
    have := vn_add (fun i => φ (⟨x, hx⟩, i) - D.Ψ x i) (D.Ψ x)
    have := W.P.eps_pos
    have hδ1024 : δ ≤ 1 / 1024 := (approxDelta_le d L hδa).1
    have := bgC0_le d L N
    linarith
  have hdot : ∀ y ∈ G.Ω 1, barField G D.Ψ φ y ⬝ᵥ barField G D.Ψ φ y = 1 := by
    intro y hy
    have := hunit ⟨y, hy⟩
    rw [hbar y hy]
    exact this
  have hg0 : ∀ x : G.Ω 1, ‖gdef G (barField G D.Ψ φ) x‖ ≤ δ₁ := by
    intro x
    have e : gdef G (barField G D.Ψ φ) x = 0 := by
      simp only [gdef]
      rw [sub_eq_zero]
      exact hdot x.1 x.2
    rw [e, norm_zero]; exact hδ₁
  have hgl : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
      ‖negLap (zeroExt (G.Ω 1) (gdef G (barField G D.Ψ φ))) (x : Torus d (N₀ * L ^ k))‖ ≤ δ₁ := by
    intro x
    rw [negLap_zeroExt_gdef hdot, norm_zero, mul_zero]; exact hδ₁
  exact ⟨H.green, hK1δ, hδ₁, hK, hδ₁s, ⟨fun x hx μ => hb.grad ⟨x, hx⟩ μ,
    fun x hx => hb.lap ⟨x, hx⟩⟩, hphi, fun x => hb.alpha x, fun x i => by simpa using hδ₁,
    hdΨ, hg0, hgl⟩

/-- The special case `δΨ = 0`, `δ₁ = 0` (local uniqueness of (EL) and of the composed system). -/
theorem prop51Hyp_zero (H : BgHyp d L k ϱ a ν) {δ ε : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ bgC1 d L N) {D : BgData G N} (W : DataWit G ν δ ε D) (hε : ε ≤ bgC0 d L N)
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hunit : ∀ x : G.Ω 1, ∑ i, φ (x, i) * φ (x, i) = 1)
    (hb : BgBounds G D φ α (bgK1 d L N * δ)) (hK : bgK1 d L N * δ ≤ deltaStar d L N) :
    Prop51Hyp G a ν α (barField G D.Ψ φ) (fun _ _ => (0 : ℂ)) 0 (bgK1 d L N * δ) 0 := by
  have hK1 := bgK1_pos d L N
  have : 0 ≤ bgK1 d L N * δ := by positivity
  exact prop51Hyp_of_bgBounds H hδ0 hδ W hε hunit hb hK le_rfl (this.trans hK)
    (fun x _ => vn_zero.le)

end Bridge

/-! ### The values of the background field of the composed datum -/

section Values

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {a : ℕ → ℝ} {ν : ℝ}

/-- If the small solution for the composed datum is unique, `(bgFieldC, bgMultC)` of the composed
datum is the restriction of the small solution `(φ', α')` of `𝔹'_k`. -/
theorem bgFieldC_compose (h : Precedes G G') (ha : ∀ j, 1 ≤ j → j ≤ k → a j ≠ 0) {c₀ : ℝ}
    (D' : BgData G' N) {φ' : G'.Ω 1 × Fin N → ℂ} {α' : G'.Ω 1 → ℂ}
    (hS : IsSmallSolution G' a ν c₀ D' φ' α')
    (hU : ∃! s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
      IsSmallSolution G a ν c₀ (composeData h a φ' D') s.1 s.2) :
    bgFieldC G a ν c₀ (composeData h a φ' D') = h.restrictφ φ' ∧
      bgMultC G a ν c₀ (composeData h a φ' D') = h.restrictα α' := by
  obtain ⟨s, hs, hu⟩ := hU
  have hU2 : ∀ φ₁ φ₂ α₁ α₂, IsSmallSolution G a ν c₀ (composeData h a φ' D') φ₁ α₁ →
      IsSmallSolution G a ν c₀ (composeData h a φ' D') φ₂ α₂ → φ₁ = φ₂ ∧ α₁ = α₂ := by
    intro φ₁ φ₂ α₁ α₂ h1 h2
    have e1 := hu (φ₁, α₁) h1
    have e2 := hu (φ₂, α₂) h2
    exact ⟨congrArg Prod.fst (e1.trans e2.symm), congrArg Prod.snd (e1.trans e2.symm)⟩
  exact bgFieldC_eq (isSmallSolution_compose h a ha ν D' hS)
    (fun φ'' α'' hs'' => compose_eq_of_unique h a ha ν D' hS hU2 hs'')

end Values

/-! ### Theorem 7.3, real data -/

section Real

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {a : ℕ → ℝ} {a₁ ν : ℝ}

/-- The (R3)-type bound `√ν ℓ' |φ' - h| ≤ K₁ δ` for the real small solution (P2 (1.16)). -/
theorem mass_bound_spacing (H : BgHyp d L k ϱ' a ν) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ bgC1 d L N)
    {D : BgData G' N} {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    (hP : InPsiTilde G' ν δ Ψ h₀) (hΨ : ∀ x ∈ dataSites G', ∀ i, D.Ψ x i = (Ψ x i : ℂ))
    (hh : ∀ x ∈ G'.Ω 1, ∀ i, D.h x i = (h₀ i : ℂ)) {φ : G'.Ω 1 × Fin N → ℂ} {α : G'.Ω 1 → ℂ}
    (hs : IsSmallSolution G' a ν (bgC0 d L N) D φ α) (z : G'.Ω 1) :
    Real.sqrt ν * G'.spacing z * vn (fun i => φ (z, i) - D.h z i) ≤ bgK1 d L N * δ := by
  have hm := bg_mass_bound H hδ0 hδ hP hΨ hh hs z
  have hℓ : 0 < G'.spacing (z : Torus d (N₀ * L ^ k)) := spacing_pos G'
  rw [le_div_iff₀ hℓ] at hm
  calc Real.sqrt ν * G'.spacing z * vn (fun i => φ (z, i) - D.h z i)
      = Real.sqrt ν * vn (fun i => φ (z, i) - D.h z i) * G'.spacing z := by ring
    _ ≤ _ := hm

/-- **Theorem 7.3 (real data; Theorem 6.1 (ii), (iv), P2 (4.39); weights (6.1)).**  Let
`𝔹_j ≺ 𝔹'_k`, let `a = compWeight L a₁` be admissible for both (`BgHyp`), and let `D'` be real
data of `𝔹'_k` with `δ ≤ thm73C1` (`𝒟_ℝ(𝔹'_k)` with `C₄ K₁ δ ≤ c₁`).  Then the composed datum
`composeData h a (bgField D') D'` lies in `𝒟_ℝ(𝔹_j)` (with `δ_j = C₄ K₁ δ ≤ c₁`), and the
background field and multiplier of the composed datum are the restrictions of those of `D'`. -/
theorem theorem73_real (ha₁ : 0 < a₁) (H : BgHyp d L k ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L k ϱ' (compWeight L a₁) ν) (h : Precedes G G') {D' : BgData G' N}
    (hD' : InUnionDomainR G' (thm73C1 d L N) ν D') :
    InUnionDomainR G (bgC1 d L N) ν
        (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν D') D') ∧
      (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν D') D').IsReal ∧
      bgField G (compWeight L a₁) ν
          (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν D') D') =
        h.restrictφ (bgField G' (compWeight L a₁) ν D') ∧
      bgMult G (compWeight L a₁) ν
          (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν D') D') =
        h.restrictα (bgMult G' (compWeight L a₁) ν D') := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hL2 : 2 ≤ L := by have := H.hL; omega
  have ha : ∀ j, 1 ≤ j → j ≤ k → compWeight L a₁ j ≠ 0 := fun j hj _ =>
    (compWeight_pos hL2 ha₁ hj).ne'
  obtain ⟨δ, hδ0, hδc, hD⟩ := hD'
  obtain ⟨hδ1, h2, hx4, hKds, hsm⟩ := thm73_small (L := L) (N := N) hd0 hδ0 hδc
  have hK1 := bgK1_ge_one d L N
  have hDU : InUnionDomainR G' (bgC1 d L N) ν D' := ⟨δ, hδ0, hδ1, hD⟩
  obtain ⟨φ, α, hs, hb, hu, hunit, -, -⟩ := bg_real H' hδ0 hδ1 hD
  obtain ⟨hfC, hmC⟩ := bgFieldC_eq hs hu
  obtain ⟨hfR, hmR⟩ := theorem72_real H' hDU
  have hf : bgField G' (compWeight L a₁) ν D' = φ := by rw [← hfR, hfC]
  have hm : bgMult G' (compWeight L a₁) ν D' = α := by rw [← hmR, hmC]
  rw [hf, hm]
  have hφre : ∀ z i, (φ (z, i)).im = 0 := fun z i => (hunit z).1 i
  obtain ⟨Ψ0, h0, hP, hΨ0, hh0⟩ := hD
  have hFB : FieldBounds G' (bgK1 d L N * δ) D'.Ψ φ :=
    fieldBounds_of_bgBounds (fun _ _ _ => rfl) hb hs.1.2
  have hmass := mass_bound_spacing H' hδ0 hδ1 hP hΨ0 hh0 hs
  obtain ⟨hdom, hreal⟩ := lemma62 hL2 h ha₁ hK1 hδ0 (by nlinarith) H'.mass H'.massLe D' ⟨Ψ0, h0, hP, hΨ0, hh0⟩ φ
    hφre hFB (fun z => hmass z)
  have hδj0 : 0 < compC4 d * (bgK1 d L N * δ) := by
    have := compC4_ge d; positivity
  have hδj : compC4 d * (bgK1 d L N * δ) ≤ bgC1 d L N := by
    have := compC4_ge d; nlinarith [mul_pos (by linarith : (0:ℝ) < compC4 d) (by positivity : 0 < bgK1 d L N * δ)]
  have hDj : InUnionDomainR G (bgC1 d L N) ν
      (composeData h (compWeight L a₁) φ D') := ⟨_, hδj0, hδj, hdom⟩
  refine ⟨hDj, hreal, ?_⟩
  -- the values
  obtain ⟨δj, hδj0', hδjc, hDj'⟩ := hDj
  obtain ⟨φ₂, α₂, hs₂, -, hu₂, -⟩ := bg_real H hδj0' hδjc hDj'
  obtain ⟨e1, e2⟩ := bgFieldC_compose h ha D' hs (existsUnique_of hs₂ hu₂)
  obtain ⟨r1, r2⟩ := theorem72_real H ⟨δj, hδj0', hδjc, hDj'⟩
  rw [← r1, ← r2]
  exact ⟨e1, e2⟩

end Real

/-! ### Theorem 7.3, complex data -/

section Complex

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {a₁ ν : ℝ}

/-- **Theorem 7.3 (complex data; Theorem 6.1, Lemma 6.3, P2 (4.39)).**  For `D'` in the complex
domain `𝒟(𝔹'_k)` with `δ ≤ thm73C1`, the composed datum with the complex background field
`bgFieldC D'` lies in `𝒟(𝔹_j)` (with `δ_j = 2 C₄ K₁ δ`, `ε_j = max ε δ_j`, P2 (4.37)), and
`(bgFieldC, bgMultC)` of the composed datum are the restrictions of those of `D'`. -/
theorem theorem73_complex (ha₁ : 0 < a₁) (H : BgHyp d L k ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L k ϱ' (compWeight L a₁) ν) (h : Precedes G G') {D' : BgData G' N}
    (hD' : InUnionDomainC G' (bgC0 d L N) (thm73C1 d L N) ν D') :
    InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν
        (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D') ∧
      bgFieldC G (compWeight L a₁) ν (bgC0 d L N)
          (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D') =
        h.restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') ∧
      bgMultC G (compWeight L a₁) ν (bgC0 d L N)
          (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D') =
        h.restrictα (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D') := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hL2 : 2 ≤ L := by have := H.hL; omega
  have ha : ∀ j, 1 ≤ j → j ≤ k → compWeight L a₁ j ≠ 0 := fun j hj _ =>
    (compWeight_pos hL2 ha₁ hj).ne'
  obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hD'
  obtain ⟨hδ1, h2, hx4, hKds, hsm⟩ := thm73_small (L := L) (N := N) hd0 hδ0 hδc
  have hK1 := bgK1_ge_one d L N
  obtain ⟨W⟩ := DataWit.exists hDC
  -- the complex small solution and the real one
  obtain ⟨φc, αc, hsc, hbc, huc⟩ := theorem52_exists H' hδ0 hδε hε hδ1 hνε hDC
  obtain ⟨hfc, hmc⟩ := bgFieldC_eq hsc huc
  have hDr : InDomainR G' ν δ W.real :=
    ⟨W.Ψ, W.h₀, W.P.toInPsiTilde, fun x hx i => W.real_Ψ hx i, fun x hx i => W.real_h hx i⟩
  obtain ⟨φr, αr, hsr, hbr, hur, hunitr, -, -⟩ := bg_real H' hδ0 hδ1 hDr
  have hφr : ∀ z i, (φr (z, i)).im = 0 := fun z i => (hunitr z).1 i
  have hdiff : ∀ z : G'.Ω 1, vn (fun i => φc (z, i) - φr (z, i)) ≤ ε + bgK1 d L N * δ := fun z =>
    theorem52_compare H' hδ0 hδε hε hδ1 hνε W W.real (fun x hx i => W.real_Ψ hx i)
      (fun x hx i => W.real_h hx i) hsc hsr z
  have hmass : ∀ z : G'.Ω 1,
      Real.sqrt ν * G'.spacing z * vn (fun i => φr (z, i) - (W.h₀ i : ℂ)) ≤ bgK1 d L N * δ := by
    intro z
    have := mass_bound_spacing H' hδ0 hδ1 W.P.toInPsiTilde (fun x hx i => W.real_Ψ hx i)
      (fun x hx i => W.real_h hx i) hsr z
    have e : (fun i => φr (z, i) - W.real.h z i) = fun i => φr (z, i) - (W.h₀ i : ℂ) :=
      funext fun i => by rw [W.real_h z.2 i]
    rwa [e] at this
  have hcons : Hyp63 G G' a₁ ν δ ε (bgK1 d L N) (bgK1 d L N * δ) W.Ψ W.h₀ W.Ψ' W.h' φr φc :=
    { prec := h, hL := hL2, ha₁ := ha₁, hK₁ := hK1, hδ := hδ0, hδε := hδε
      hε1 := hε.trans (bgC0_le d L N |>.trans (by norm_num)), hη := rfl
      hsmall := hsm, hν := H'.mass, hνk := H'.massLe, hPC := W.P, hφr := hφr
      hbr := fieldBounds_of_bgBounds (fun x hx i => (W.real_Ψ hx i).symm) hbr hsr.1.2
      hmass := hmass
      hbc := fieldBounds_of_bgBounds (fun x hx i => by rw [W.hΨ x hx i]; rfl) hbc hsc.1.2
      hdiff := hdiff }
  have hdom := lemma63_inDomainC hcons D' (fun x hx i => by rw [W.hΨ x hx i]; rfl)
    (fun x hx i => W.hh x hx i)
  rw [hfc, hmc]
  have hδj0 : 0 < 2 * (compC4 d * (bgK1 d L N * δ)) := by
    have := compC4_ge d; positivity
  have hδjc0 : 2 * (compC4 d * (bgK1 d L N * δ)) ≤ bgC0 d L N :=
    h2.trans (bgC1_le_bgC0 d L N hd0)
  have hδδj : δ ≤ 2 * (compC4 d * (bgK1 d L N * δ)) := by
    have := compC4_ge d
    nlinarith [mul_pos hδ0 (by linarith : (0 : ℝ) < bgK1 d L N)]
  have hνj : ν * ((L : ℝ) ^ k) ^ 2 * (max ε (2 * (compC4 d * (bgK1 d L N * δ)))) ^ 2 ≤
      (2 * (compC4 d * (bgK1 d L N * δ))) ^ 2 := by
    rcases le_total ε (2 * (compC4 d * (bgK1 d L N * δ))) with he | he
    · rw [max_eq_right he]
      have := H.massLe
      nlinarith [sq_nonneg (2 * (compC4 d * (bgK1 d L N * δ)))]
    · rw [max_eq_left he]
      have : δ ^ 2 ≤ (2 * (compC4 d * (bgK1 d L N * δ))) ^ 2 :=
        pow_le_pow_left₀ hδ0.le hδδj 2
      linarith
  have hDj : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν
      (composeData h (compWeight L a₁) φc D') :=
    ⟨_, _, hδj0, le_max_right _ _, max_le hε hδjc0, h2, hνj, hdom⟩
  refine ⟨hDj, ?_⟩
  exact bgFieldC_compose h ha D' hsc (theorem72 H hDj).1

end Complex

/-! ### Theorem 7.3: the composed system `𝒮` -/

section System

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {a₁ ν : ℝ}

/-- **Theorem 6.1 (iii) for the small solution**: if `(φ, α)` is the small solution for the datum
`D'` of `𝔹'_k` with the bounds of Theorem 5.2 (3) (`δ ≤ thm73C1`), then
`(composeField φ, φ, α)` solves the composed system `𝒮`, and it is the only solution with
`|α|'₂ < c₀ / 2` (`2 (c₀ / 2) ≤ c₆`); in that class `φ₂ = φ`, `α₂ = α` and `ψ₂ = Ψ` on `Ω₁`. -/
theorem system_unique_core (ha₁ : 0 < a₁) (H' : BgHyp d L k ϱ' (compWeight L a₁) ν)
    (h : Precedes G G') {δ ε : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ thm73C1 d L N) (hε : ε ≤ bgC0 d L N)
    {D' : BgData G' N} (W : DataWit G' ν δ ε D') {φ : G'.Ω 1 × Fin N → ℂ} {α : G'.Ω 1 → ℂ}
    (hs : IsSmallSolution G' (compWeight L a₁) ν (bgC0 d L N) D' φ α)
    (hb : BgBounds G' D' φ α (bgK1 d L N * δ)) :
    IsComposedSystem G G' (compWeight L a₁) ν D' (fun x i => composeField G G' (compWeight L a₁) φ D'.Ψ x i) φ α ∧
      ∀ (ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ₂ : G'.Ω 1 × Fin N → ℂ) (α₂ : G'.Ω 1 → ℂ),
        IsComposedSystem G G' (compWeight L a₁) ν D' ψ φ₂ α₂ →
        (∀ z : G'.Ω 1, G'.spacing (z : Torus d (N₀ * L ^ k)) ^ 2 * ‖α₂ z‖ < bgC0 d L N / 2) →
        φ₂ = φ ∧ α₂ = α ∧ ∀ x ∈ G.Ω 1, ψ x = composeField G G' (compWeight L a₁) φ D'.Ψ x := by
  have hd0 : 0 < d := by have := H'.hd; omega
  have hL2 : 2 ≤ L := by have := H'.hL; omega
  obtain ⟨hδ1, h2, hx4, hKds, hsm⟩ := thm73_small (L := L) (N := N) hd0 hδ0 hδ
  have hC1 : ∀ n p : ℕ, n ≤ p → ((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ p) ^ 2 *
      (compWeight L a₁ n)⁻¹ = (compWeight L a₁ p)⁻¹ - (compWeight L a₁ (p - n))⁻¹ :=
    fun n p hnp => compWeight_C1 a₁ hnp
  have hpos : ∀ r, 1 ≤ r → 0 < compWeight L a₁ r := fun r hr => compWeight_pos hL2 ha₁ hr
  have H51 := prop51Hyp_zero H' hδ0 hδ1 W hε hs.1.2 hb hKds
  have hc0 := bgC0_pos d L N hd0
  have hα : ∀ z : G'.Ω 1, G'.spacing (z : Torus d (N₀ * L ^ k)) ^ 2 * ‖α z‖ <
      bgC0 d L N / 2 := fun z => lt_of_le_of_lt (hb.alpha z) (by linarith)
  refine ⟨isComposedSystem_of_isEL h _ hC1 hpos ν D' hs.1, ?_⟩
  intro ψ φ₂ α₂ h₂ hα₂
  have hc6 : 2 * (bgC0 d L N / 2) ≤ c6 d L N := by
    have := bgC0_le_c6 d L N; linarith
  exact composedSystem_unique_lt hd0 h _ hC1 hpos ν D' hc6 H51
    (fun z i => by simp [barField, z.2])
    (isComposedSystem_of_isEL h _ hC1 hpos ν D' hs.1) h₂ hα hα₂

/-- **Theorem 7.3 (complex data), the system `𝒮`**: for `D'` in the complex domain with
`δ ≤ thm73C1`, `(Ψ, bgFieldC D', bgMultC D')` with `Ψ = composeField` is the unique solution of
`𝒮` with `|α|'₂ < c₀ / 2`. -/
theorem theorem73_system (ha₁ : 0 < a₁) (H' : BgHyp d L k ϱ' (compWeight L a₁) ν)
    (h : Precedes G G') {D' : BgData G' N}
    (hD' : InUnionDomainC G' (bgC0 d L N) (thm73C1 d L N) ν D') :
    IsComposedSystem G G' (compWeight L a₁) ν D'
        (fun x i => composeField G G' (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D'.Ψ x i)
        (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')
        (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D') ∧
      ∀ (ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ₂ : G'.Ω 1 × Fin N → ℂ) (α₂ : G'.Ω 1 → ℂ),
        IsComposedSystem G G' (compWeight L a₁) ν D' ψ φ₂ α₂ →
        (∀ z : G'.Ω 1, G'.spacing (z : Torus d (N₀ * L ^ k)) ^ 2 * ‖α₂ z‖ < bgC0 d L N / 2) →
        φ₂ = bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D' ∧
          α₂ = bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D' ∧
          ∀ x ∈ G.Ω 1, ψ x = composeField G G' (compWeight L a₁)
            (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D'.Ψ x := by
  obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hD'
  obtain ⟨W⟩ := DataWit.exists hDC
  have hd0 : 0 < d := by have := H'.hd; omega
  have hδ1 := (thm73_small (L := L) (N := N) hd0 hδ0 hδc).1
  obtain ⟨φ, α, hs, hb, hu⟩ := theorem52_exists H' hδ0 hδε hε hδ1 hνε hDC
  obtain ⟨hf, hm⟩ := bgFieldC_eq hs hu
  rw [hf, hm]
  exact system_unique_core ha₁ H' h hδ0 hδc hε W hs hb

/-- **Theorem 7.3 (real data), the system `𝒮`**: for real `D'` with `δ ≤ thm73C1`,
`(Ψ, bgField D', bgMult D')` with `Ψ = composeField` is the unique solution of `𝒮` with
`|α|'₂ < c₀ / 2`. -/
theorem theorem73_system_real (ha₁ : 0 < a₁) (H' : BgHyp d L k ϱ' (compWeight L a₁) ν)
    (h : Precedes G G') {D' : BgData G' N}
    (hD' : InUnionDomainR G' (thm73C1 d L N) ν D') :
    IsComposedSystem G G' (compWeight L a₁) ν D'
        (fun x i => composeField G G' (compWeight L a₁)
          (bgField G' (compWeight L a₁) ν D') D'.Ψ x i)
        (bgField G' (compWeight L a₁) ν D') (bgMult G' (compWeight L a₁) ν D') ∧
      ∀ (ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ₂ : G'.Ω 1 × Fin N → ℂ) (α₂ : G'.Ω 1 → ℂ),
        IsComposedSystem G G' (compWeight L a₁) ν D' ψ φ₂ α₂ →
        (∀ z : G'.Ω 1, G'.spacing (z : Torus d (N₀ * L ^ k)) ^ 2 * ‖α₂ z‖ < bgC0 d L N / 2) →
        φ₂ = bgField G' (compWeight L a₁) ν D' ∧ α₂ = bgMult G' (compWeight L a₁) ν D' ∧
          ∀ x ∈ G.Ω 1, ψ x = composeField G G' (compWeight L a₁)
            (bgField G' (compWeight L a₁) ν D') D'.Ψ x := by
  obtain ⟨δ, hδ0, hδc, hD⟩ := hD'
  have hd0 : 0 < d := by have := H'.hd; omega
  have hδ1 := (thm73_small (L := L) (N := N) hd0 hδ0 hδc).1
  obtain ⟨φ, α, hs, hb, hu, hunit, -, -⟩ := bg_real H' hδ0 hδ1 hD
  obtain ⟨hfC, hmC⟩ := bgFieldC_eq hs hu
  obtain ⟨hfR, hmR⟩ := theorem72_real H' (⟨δ, hδ0, hδ1, hD⟩ : InUnionDomainR G' (bgC1 d L N) ν D')
  have hf : bgField G' (compWeight L a₁) ν D' = φ := by rw [← hfR, hfC]
  have hm : bgMult G' (compWeight L a₁) ν D' = α := by rw [← hmR, hmC]
  rw [hf, hm]
  obtain ⟨Ψ0, h0, hP, hΨ0, hh0⟩ := hD
  exact system_unique_core ha₁ H' h hδ0 hδc (hδ1.trans (bgC1_le_bgC0 d L N hd0))
    (DataWit.ofReal hδ0 hδ0 hP D' hΨ0 hh0) hs hb

end System

/-! ### Proposition 6.4: the perturbed composition, for the increments of `theorem52_perturb` -/

section Perturbed

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {a₁ ν : ℝ}

/-- The increments of a small solution of the perturbed datum solve (P-1), (P-2) (the converse of
the computation inside `theorem52_perturb`). -/
theorem isPerturbed_of_isEL {a : ℕ → ℝ} (D D'' : BgData G' N) (hh : D''.h = D.h)
    {φ : G'.Ω 1 × Fin N → ℂ} {α : G'.Ω 1 → ℂ} (hEL : IsEL G' a ν D φ α)
    {δφ : G'.Ω 1 × Fin N → ℂ} {δα : G'.Ω 1 → ℂ} (hEL'' : IsEL G' a ν D'' (φ + δφ) (α + δα)) :
    IsPerturbed G' a ν α (barField G' D.Ψ φ) (pertSource G' a (D''.Ψ - D.Ψ) 0) δφ δα := by
  refine ⟨?_, fun x => ?_⟩
  · funext p
    have e2 := congrFun hEL''.1 p
    have hSrc := source_perturb (a := a) (ν := ν) D D'' hh p
    have hEL1 := congrFun hEL.1 p
    have hba : barField G' D.Ψ φ p.1.1 p.2 = φ p := by simp [barField, p.1.2]
    rw [liftOp_dirichlet_add, Matrix.mulVec_add] at e2
    simp only [Pi.add_apply] at e2
    rw [hEL1, hSrc] at e2
    simp only [Pi.add_apply, hba]
    linear_combination e2
  · have := hEL''.2 x
    have hba : ∀ i, barField G' D.Ψ φ x.1 i = φ (x, i) := fun i => by simp [barField, x.2]
    simpa [hba] using this

/-- Smoothness of a field for `𝔹'_k` gives smoothness for `𝔹_j ≺ 𝔹'_k` (`ℓ ≤ ℓ'`). -/
theorem isSmoothField_of_precedes (h : Precedes G G') {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀)
    {φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hφ : IsSmoothField G' δ₀ φ₀) :
    IsSmoothField G δ₀ φ₀ := by
  have hle : ∀ x ∈ G.Ω 1, G.spacing x ≤ G'.spacing x := fun x hx => by
    simpa using scaleGap_one h x hx
  refine ⟨fun x hx μ => ?_, fun x hx => ?_⟩
  · obtain ⟨g1, g2⟩ := hφ.grad x (h.mem_Ω1 hx) μ
    have hd : δ₀ / G'.spacing x ≤ δ₀ / G.spacing x :=
      div_le_div_of_nonneg_left hδ₀ (spacing_pos G) (hle x hx)
    exact ⟨g1.trans hd, g2.trans hd⟩
  · have g := hφ.lap x (h.mem_Ω1 hx)
    have hd : δ₀ / G'.spacing x ^ 2 ≤ δ₀ / G.spacing x ^ 2 :=
      div_le_div_of_nonneg_left hδ₀ (by have := spacing_pos G (x := x); positivity)
        (pow_le_pow_left₀ (spacing_pos G).le (hle x hx) 2)
    exact g.trans hd

/-- **The size of the composed displacement**: if `|δφ| ≤ c` and `|δΨ'| ≤ δ₁` on `Ω'₁ ∪ C(Ω'₁)`,
then `|composeField δφ δΨ'| ≤ 2 c + δ₁` on `Ω₁ ∪ C(Ω₁)` (`0 ≤ κ ≤ 1`; BACKGROUND.md §6.7). -/
theorem vn_composeField_le (hL2 : 2 ≤ L) (ha₁ : 0 < a₁) (h : Precedes G G') {c δ₁ : ℝ}
    (hc : 0 ≤ c) (hδ₁ : 0 ≤ δ₁) {δφ : G'.Ω 1 × Fin N → ℂ}
    {δΨ' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hφ : ∀ y, vn (svec G' δφ y) ≤ c)
    (hΨ : ∀ x ∈ dataSites G', vn (δΨ' x) ≤ δ₁) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ dataSites G) :
    vn (fun i => composeField G G' (compWeight L a₁) δφ δΨ' x i) ≤ 2 * c + δ₁ := by
  rcases (mem_dataSites G).1 hx with hxΩ | hxc
  · obtain ⟨hn1, hnk, -⟩ := G.layerIndex_spec hxΩ
    obtain ⟨hp1, hpk, -⟩ := G'.layerIndex_spec (h.mem_Ω1 hxΩ)
    obtain ⟨k0, k1⟩ := compWeight_kappa_mem hL2 ha₁ hn1 (h.layerIndex_le hxΩ)
    set κ : ℝ := compWeight L a₁ (G'.layerIndex x) / compWeight L a₁ (G.layerIndex x) *
      (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2) with hκ
    have hm1 : vn (fun i => blockMean G (G.layerIndex x) (fun y => svec G' δφ y i) x) ≤ c :=
      vn_blockMean_le (G := G) hnk (fun y => svec G' δφ y) x (fun y _ => hφ y)
    have hm2 : vn (fun i => blockMean G' (G'.layerIndex x) (fun y => svec G' δφ y i) x) ≤ c :=
      vn_blockMean_le (G := G') hpk (fun y => svec G' δφ y) x (fun y _ => hφ y)
    have hΨx := hΨ x ((mem_dataSites G').2 (Or.inl (h.mem_Ω1 hxΩ)))
    have e : (fun i => composeField G G' (compWeight L a₁) δφ δΨ' x i) = fun i =>
        blockMean G (G.layerIndex x) (fun y => svec G' δφ y i) x +
          (κ : ℂ) * (δΨ' x i - blockMean G' (G'.layerIndex x) (fun y => svec G' δφ y i) x) :=
      funext fun i => composeField_of_mem _ δφ δΨ' hxΩ i
    rw [e]
    refine (vn_add' _ _).trans ?_
    rw [vn_smul_real, abs_of_nonneg k0]
    have h3 := vn_sub_le' (δΨ' x) (fun i => blockMean G' (G'.layerIndex x)
      (fun y => svec G' δφ y i) x)
    have h4 : κ * vn (fun i => δΨ' x i - blockMean G' (G'.layerIndex x)
        (fun y => svec G' δφ y i) x) ≤ δ₁ + c := by
      calc _ ≤ 1 * (δ₁ + c) := mul_le_mul k1 (h3.trans (add_le_add hΨx hm2)) (vn_nonneg _)
            zero_le_one
        _ = _ := one_mul _
    linarith
  · rw [show (fun i => composeField G G' (compWeight L a₁) δφ δΨ' x i) =
        fun i => barField G' δΨ' δφ x i from funext fun i => composeField_of_collar _ δφ δΨ' hxc i]
    by_cases hx' : x ∈ G'.Ω 1
    · have e : (fun i => barField G' δΨ' δφ x i) = svec G' δφ x := by
        funext i; simp [barField, hx', svec, zeroExt]
      rw [e]; linarith [hφ x]
    · have e : (fun i => barField G' δΨ' δφ x i) = δΨ' x := by
        funext i; simp [barField, hx']
      rw [e]
      have := hΨ x ((mem_dataSites G').2 (Or.inr (mem_collar_of_not_mem h hxc hx')))
      linarith

/-- **Theorem 7.3, perturbed version (Proposition 6.4, P2 (4.41)-(4.43))** for the increments of
`theorem52_perturb`.  Let `D''` have the same `h̃` as `D ∈ 𝒟(𝔹'_k)`, `δ ≤ thm73C1`,
`|Ψ'' - Ψ| ≤ δ₁` with `(2 N K₂ + 1) δ₁ ≤ δ_*` (the smallness of Proposition 5.1 for `𝔹_j` with
`δ₁ ↦ (2 N K₂ + 1) δ₁`), and let `(δφ, δα)` be the increments of `theorem52_perturb`.  Then
`(δφ, δα)|_{Ω₁}` is the solution, in the class `|δα|₂ ≤ c₆`, of the perturbed system (P-1), (P-2)
for `𝔹_j` with the displacement `composeField δφ (Ψ'' - Ψ)` (formula (6.2) with `φ → δφ`), the
background field `φ̄` and the restricted `α`. -/
theorem theorem73_perturb (ha₁ : 0 < a₁) (H : BgHyp d L k ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L k ϱ' (compWeight L a₁) ν) (h : Precedes G G') {δ ε : ℝ} (hδ0 : 0 < δ)
    (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ thm73C1 d L N)
    (hνε : ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D : BgData G' N} (hD : InDomainC G' ν δ ε D)
    {D'' : BgData G' N} (hh : D''.h = D.h) {δ₁ : ℝ} (hδ₁ : 0 ≤ δ₁)
    (hδ₁s : (2 * N * cK2 d L N + 1) * δ₁ ≤ deltaStar d L N)
    (hdΨ : ∀ x ∈ dataSites G', vn (D''.Ψ x - D.Ψ x) ≤ δ₁)
    (hsmall : bgK1 d L N * δ + cK2 d L N * δ₁ < bgC0 d L N)
    {φ : G'.Ω 1 × Fin N → ℂ} {α : G'.Ω 1 → ℂ}
    (hs : IsSmallSolution G' (compWeight L a₁) ν (bgC0 d L N) D φ α)
    {δφ : G'.Ω 1 × Fin N → ℂ} {δα : G'.Ω 1 → ℂ}
    (hsol : IsSmallSolution G' (compWeight L a₁) ν (bgC0 d L N) D'' (φ + δφ) (α + δα))
    (hSup : SupBounds G' δφ (cK2 d L N * δ₁)) (hSm : Small G' δα (cK2 d L N * δ₁)) :
    Small G (h.restrictα δα) (c6 d L N) ∧
      ∀ (δφ₂ : G.Ω 1 × Fin N → ℂ) (δα₂ : G.Ω 1 → ℂ),
        IsPerturbed G (compWeight L a₁) ν (h.restrictα α) (barField G' D.Ψ φ)
          (pertSource G (compWeight L a₁)
            (fun z j => composeField G G' (compWeight L a₁) δφ (D''.Ψ - D.Ψ) z j)
            (h.restrictφ (0 : G'.Ω 1 × Fin N → ℂ))) δφ₂ δα₂ →
        Small G δα₂ (c6 d L N) → δφ₂ = h.restrictφ δφ ∧ δα₂ = h.restrictα δα := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hL2 : 2 ≤ L := by have := H.hL; omega
  have ha : ∀ j, 1 ≤ j → j ≤ k → compWeight L a₁ j ≠ 0 := fun j hj _ =>
    (compWeight_pos hL2 ha₁ hj).ne'
  obtain ⟨hδ1, h2, hx4, hKds, hsm⟩ := thm73_small (L := L) (N := N) hd0 hδ0 hδ
  obtain ⟨W⟩ := DataWit.exists hD
  obtain ⟨φ₀, α₀, hs0, hb0, hu0⟩ := theorem52_exists H' hδ0 hδε hε hδ1 hνε hD
  obtain ⟨e1, e2⟩ := hu0 φ α hs
  subst e1; subst e2
  have hK1 := bgK1_pos d L N
  have hK2 := cK2_pos d L N
  have hK1δ : 0 ≤ bgK1 d L N * δ := by positivity
  have hK2δ₁ : 0 ≤ cK2 d L N * δ₁ := by positivity
  have hδ₁d : δ₁ ≤ deltaStar d L N := by
    have : δ₁ ≤ (2 * N * cK2 d L N + 1) * δ₁ := by
      have : (0 : ℝ) ≤ 2 * N * cK2 d L N := by positivity
      nlinarith
    exact this.trans hδ₁s
  have H51' := prop51Hyp_of_bgBounds H' hδ0 hδ1 W hε hs.1.2 hb0 hKds hδ₁ hδ₁d
    (fun x hx => hdΨ x hx)
  have hP := isPerturbed_of_isEL D D'' hh hs.1 hsol.1
  have hSm6 : Small G' δα (c6 d L N) := fun x =>
    (hSm x).trans (by have := bgC0_le_c6 d L N; linarith)
  -- the hypotheses of Proposition 5.1 for `𝔹_j`
  set δG : ℝ := (2 * N * cK2 d L N + 1) * δ₁ with hδG
  have hδG0 : 0 ≤ δG := by positivity
  have hbar : ∀ (y : Torus d (N₀ * L ^ k)) (hy : y ∈ G'.Ω 1),
      barField G' D.Ψ φ y = fun i => φ (⟨y, hy⟩, i) := by
    intro y hy; funext i; simp [barField, hy]
  have hdot : ∀ y ∈ G.Ω 1, barField G' D.Ψ φ y ⬝ᵥ barField G' D.Ψ φ y = 1 := by
    intro y hy
    have := hs.1.2 ⟨y, h.mem_Ω1 hy⟩
    rw [hbar y (h.mem_Ω1 hy)]
    exact this
  have hle : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 ≤
      G'.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := fun x => by
    have := scaleGap_one h x x.2
    rw [one_mul] at this
    exact pow_le_pow_left₀ (spacing_pos G).le this 2
  have hc : 0 ≤ (N : ℝ) * (cK2 d L N * δ₁) := by positivity
  have H51G : Prop51Hyp G (compWeight L a₁) ν (h.restrictα α) (barField G' D.Ψ φ)
      (fun z j => composeField G G' (compWeight L a₁) δφ (D''.Ψ - D.Ψ) z j)
      (h.restrictφ (0 : G'.Ω 1 × Fin N → ℂ)) (bgK1 d L N * δ) δG := by
    refine ⟨H.green, hK1δ, hδG0, hKds, hδ₁s, isSmoothField_of_precedes h hK1δ H51'.smooth,
      fun x hx => H51'.phiBd x (h.mem_Ω1 hx), fun x => ?_, fun x i => ?_, fun x hx => ?_,
      fun x => ?_, fun x => ?_⟩
    · exact (mul_le_mul_of_nonneg_right (hle x) (norm_nonneg _)).trans (H51'.alpha0 (h.incl x))
    · simpa [Precedes.restrictφ] using hδG0
    · have := vn_composeField_le (a₁ := a₁) hL2 ha₁ h hc hδ₁
        (δφ := δφ) (δΨ' := D''.Ψ - D.Ψ)
        (fun y => vn_le_card_mul hK2δ₁ (fun i => hSup.val y i)) (fun x hx => hdΨ x hx) hx
      refine this.trans (le_of_eq ?_)
      rw [hδG]; ring
    · have e : gdef G (barField G' D.Ψ φ) x = 0 := by
        simp only [gdef]
        rw [sub_eq_zero]
        exact hdot x.1 x.2
      rw [e, norm_zero]; exact hδG0
    · rw [negLap_zeroExt_gdef hdot, norm_zero, mul_zero]; exact hδG0
  exact prop64 hd0 h _ ha ν hP hSm6 H51G

/-- `composeField` is affine in `(φ', Ψ')`: the difference of the composed fields of two data is
the composed field of the differences. -/
theorem composeField_sub (a : ℕ → ℝ) (φ δφ : G'.Ω 1 × Fin N → ℂ)
    (Ψ Ψ'' : Torus d (N₀ * L ^ k) → Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    composeField G G' a (φ + δφ) Ψ'' x i - composeField G G' a φ Ψ x i =
      composeField G G' a δφ (Ψ'' - Ψ) x i := by
  have hsv : ∀ y, svec G' (φ + δφ) y i = svec G' φ y i + svec G' δφ y i := fun y => by
    by_cases hy : y ∈ G'.Ω 1 <;> simp [svec, zeroExt, hy]
  by_cases hx : x ∈ G.Ω 1
  · rw [composeField_of_mem a _ _ hx, composeField_of_mem a _ _ hx, composeField_of_mem a _ _ hx]
    simp only [hsv, Pi.sub_apply]
    have e1 : blockMean G (G.layerIndex x) (fun y => svec G' φ y i + svec G' δφ y i) x =
        blockMean G (G.layerIndex x) (fun y => svec G' φ y i) x +
          blockMean G (G.layerIndex x) (fun y => svec G' δφ y i) x := blockMean_add _ _ _ _
    have e2 : blockMean G' (G'.layerIndex x) (fun y => svec G' φ y i + svec G' δφ y i) x =
        blockMean G' (G'.layerIndex x) (fun y => svec G' φ y i) x +
          blockMean G' (G'.layerIndex x) (fun y => svec G' δφ y i) x := blockMean_add _ _ _ _
    rw [e1, e2]; ring
  · by_cases hc : x ∈ collar G
    · rw [composeField_of_collar a _ _ hc, composeField_of_collar a _ _ hc,
        composeField_of_collar a _ _ hc]
      by_cases hx' : x ∈ G'.Ω 1 <;> simp [barField, hx']
    · have hn : x ∉ dataSites G := fun h' => by
        rcases (mem_dataSites G).1 h' with h' | h'
        · exact hx h'
        · exact hc h'
      rw [composeField_of_not_mem a _ _ hn, composeField_of_not_mem a _ _ hn,
        composeField_of_not_mem a _ _ hn]; ring

/-- The composed data of `(φ + δφ, D'')` and `(φ, D)` differ by the composed displacement of
`theorem73_perturb`; so `(δφ, δα)|_{Ω₁}` are the increments of Proposition 5.1 for the
composed perturbation problem of `𝔹_j`. -/
theorem composeData_sub (h : Precedes G G') (a : ℕ → ℝ) (φ δφ : G'.Ω 1 × Fin N → ℂ)
    (D D'' : BgData G' N) (hh : D''.h = D.h) :
    (composeData h a (φ + δφ) D'').h = (composeData h a φ D).h ∧
      ∀ x i, (composeData h a (φ + δφ) D'').Ψ x i - (composeData h a φ D).Ψ x i =
        composeField G G' a δφ (D''.Ψ - D.Ψ) x i := by
  refine ⟨?_, fun x i => composeField_sub a φ δφ D.Ψ D''.Ψ x i⟩
  funext x i
  simp [composeData, hh]

end Perturbed

end Balaban.Background
