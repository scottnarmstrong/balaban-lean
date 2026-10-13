/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormLocC1Zero
public import Balaban.Inhabited.RenormLocC1ZeroWitness
public import Balaban.Fluctuation.RenormStrictData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One class constant for the renormalization localization fields

The record `RenormExpInput` uses one class constant `c_K` in `locC1`, `locC2`, `locDφ`.  The landed
`locC1` fixes `c_K = 2 + 2 K₄ ξ₁`.  This file shows that the class bound is monotone in the
constant, so `locC1` holds at every larger constant, and it defines the shared constant `renCK`,
the larger of `2 + 2 K₄ ξ₁` and `K₂'(B_fam) b_* / (8 K₂)`, so that `8 c_K K₂ ≥ K₂' b_*`.

* `bgClass_mono`, `pertClass_mono`: monotonicity of the two classes;
* `HasLocPrinciple.mono_class`: the localization principle persists when the class is enlarged;
* `renLocC1_zero_of_le`, `renLocC1_scale_of_tower_of_le`: the `locC1` field at larger constants;
* `renCK`, `renCK_ge`, `renCK_mul_ge`: the shared constant and its two inequalities.

The principles `locC2`, `locDφ` are NOT proved here.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Analysis Finset

section Mono

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

/-- The class of decoupled backgrounds grows with the closeness constant. -/
theorem bgClass_mono {ν c c' : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c') (D : BgData G N) :
    bgClass G ν c D ⊆ bgClass G ν c' D := by
  rintro φ ⟨h1, h2, h3⟩
  have hs : ∀ x ∈ G.Ω 1, c / G.spacing x ≤ c' / G.spacing x := fun x hx =>
    div_le_div_of_nonneg_right hcc (spacing_pos G).le
  refine ⟨fun x hx => (h1 x hx).trans hcc, fun x hx μ => ⟨((h2 x hx μ).1).trans (hs x hx),
    ((h2 x hx μ).2).trans (hs x hx)⟩, fun x hx => (h3 x hx).trans ?_⟩
  nlinarith

/-- The class of decoupled perturbations grows with both radii. -/
theorem pertClass_mono {V V' A A' : ℝ} (hV : V ≤ V') (hA : A ≤ A') (νu : ℂ) :
    pertClass G (N := N) V A νu ⊆ pertClass G V' A' νu := fun _ ⟨h1, h2⟩ =>
  ⟨h1.mono hV, fun x => (h2 x).trans hA⟩

end Mono

section Principle

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {U : Type*} {Dom : BgData G N → Prop} {r κ Kloc : ℝ}
  {Ys : Finset (Finset (Torus d (N₀ * L ^ k)))} {dY : Finset (Torus d (N₀ * L ^ k)) → ℝ}
  {Kcl Kcl' : BgData G N → (Fin 3 → ℂ) → Set U} {f : BgData G N → U → (Fin 3 → ℂ) → E}
  {u : BgData G N → (Fin 3 → ℂ) → U}

/-- **The localization principle is monotone under enlarging the class.**  The only clause that
mentions the class is the transfer clause, where a bound over the larger class is a bound over the
smaller one. -/
theorem _root_.Balaban.Fluctuation.HasLocPrinciple.mono_class (h : HasLocPrinciple G Dom r Ys dY κ Kloc Kcl f u)
    (hK : ∀ D, Dom D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r → Kcl D ξ ⊆ Kcl' D ξ) :
    HasLocPrinciple G Dom r Ys dY κ Kloc Kcl' f u := by
  obtain ⟨term, hsum, han, hloc, hbd⟩ := h
  exact ⟨term, hsum, han, hloc, fun ξ hξ M hM Y hY D hD =>
    hbd ξ hξ M (fun D' hD' v hv => hM D' hD' v (hK D' hD' ξ hξ hv)) Y hY D hD⟩

end Principle

section LocC1

open LocalCover

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **`locC1` at any class constant `cK' ≥ 2 + 2 K₄ ξ₁`** (zero class, `K_loc = 1`): the
conclusion of `renLocC1_zero_at` with the class `bgClass Gp ν (cK' * eps)`. -/
theorem renLocC1_zero_of_le
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hconn : HatConn Gp)
    (hG' : IsLevel Gp (k + 1)) {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁)
    (hd : 3 ≤ d) (hL : 3 ≤ L) {κd κ₀ κa : ℝ} (hκ₀ : 0 ≤ κ₀) (hκd : 3 * κ₀ + 3 ≤ κd)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κd ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hout : κa ≤ 2 * κd) {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ ≤ 1 / 16)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {cK' : ℝ}
    (hcK : 2 + 2 * K4 d L N BG κ * xiC1 d ≤ cK') :
    HasLocPrinciple (N := N) Gp (XiCOneReal Gp (compWeight L a₁) ν eps) r₀
      (renYs (renCube Gp (X1 Gp m₀ k (fam m₀ (blockSite k z)))) Gp m₀
        (X1 Gp m₀ k (fam m₀ (blockSite k z))))
      (renDY Gp m₀) κa 1
      (fun D _ => bgClass Gp ν (cK' * eps) D)
      (fun D φ ξ => renC1On Gp (compWeight L a₁) ν eps (blockSites d L N₁ m₁ (k + 1) k z)
        D.Ψ D.h φ ξ)
      (fun D _ => bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D) := by
  have hd0 : 0 < d := by omega
  have hK4 := (K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0).le
  have hε := hC.eps_pos
  have hC1pos : 0 < xiC1 d := by unfold xiC1; positivity
  have h0 : 0 ≤ (2 + 2 * K4 d L N BG κ * xiC1 d) * eps := by positivity
  exact HasLocPrinciple.mono_class
    (renLocC1_zero_at hC hconn hG' hm₀ hN hd hL hκ₀ hκd hκ₁ h1 hlog hout hr₀0 hr₀1 z)
    fun D _ ξ _ => bgClass_mono h0 (mul_le_mul_of_nonneg_right hcK hε.le) D

end LocC1

section Scale

open Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField.Def6 Balaban.Inhabited Balaban.Inhabited.LevelStep LocalCover

/-- **`locC1` at every scale of the tower, at any class constant `cK' ≥ 2 + 2 K₄ ξ₁`.** -/
theorem renLocC1_scale_of_tower_of_le {κmin : ℝ} (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {κa r₀ : ℝ} (hκa : κa ≤ 2 * T.κdec)
    (hr₀0 : 0 < r₀) (hr₀1 : r₀ ≤ 1 / 16) (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))))
    {cK' : ℝ} (hcK : 2 + 2 * K4 3 3 2 T.BG T.κ * xiC1 3 ≤ cK') :
    HasLocPrinciple (N := 2) (lvTop N₁ T.m₁ k (rhoSep T.m₁))
      (XiCOneReal (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 1) ν T.t) r₀
      (renYs (renCube (lvTop N₁ T.m₁ k (rhoSep T.m₁))
          (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))))
        (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
        (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))))
      (renDY (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1) κa 1
      (fun D _ => bgClass (lvTop N₁ T.m₁ k (rhoSep T.m₁)) ν (cK' * T.t) D)
      (fun D φ ξ => renC1On (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 1) ν T.t
        (blockSites 3 3 N₁ T.m₁ (k + 1) k z) D.Ψ D.h φ ξ)
      (fun D _ => bgFieldC (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D) := by
  have hK4 := (K4_pos (d := 3) (L := 3) (N := 2) (κ := T.κ) (BG := T.BG)
    (by simpa using T.core.some.hS.fam.2.1) (by norm_num)).le
  have hC1pos : 0 < xiC1 3 := by unfold xiC1; positivity
  have h0 : 0 ≤ (2 + 2 * K4 3 3 2 T.BG T.κ * xiC1 3) * T.t := by
    have := T.t_pos; positivity
  exact HasLocPrinciple.mono_class
    (Balaban.Inhabited.renLocC1_scale_of_tower T k hk N₁ h3N hN hν0 hν hκa hr₀0 hr₀1 z)
    fun D _ ξ _ => bgClass_mono h0 (mul_le_mul_of_nonneg_right hcK T.t_pos.le) D

end Scale

section SharedConstant

variable (d L N : ℕ) [NeZero L] (BG κ : ℝ)

/-- **The shared class constant**: the larger of the constant `2 + 2 K₄ ξ₁` of `renLocC1_zero` and
`K₂'(B_fam) b_* / (8 K₂)`, with `B_fam = famConst d L BG κ`,
`b_* = 3/2 + (32/15)(3 + (K₄ + K₁) ξ₁)`. -/
noncomputable def renCK : ℝ :=
  max (2 + 2 * K4 d L N BG κ * xiC1 d)
    (cK2' d L N (famConst d L BG κ) *
      (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) / (8 * cK2 d L N))

variable {d L N BG κ}

/-- `renCK` is at least the constant of `renLocC1_zero`. -/
theorem renCK_ge : 2 + 2 * K4 d L N BG κ * xiC1 d ≤ renCK d L N BG κ := le_max_left _ _

/-- The constant inequality `8 c_K K₂ ≥ K₂' b_*` at `c_K = renCK`. -/
theorem renCK_mul_ge :
    cK2' d L N (famConst d L BG κ) *
      (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) ≤
    8 * renCK d L N BG κ * cK2 d L N := by
  have h := cK2_pos d L N
  have h2 : cK2' d L N (famConst d L BG κ) *
      (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) / (8 * cK2 d L N) ≤
      renCK d L N BG κ := le_max_right _ _
  rw [div_le_iff₀ (by positivity)] at h2
  linarith

end SharedConstant

end Balaban.Localization
