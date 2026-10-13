/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ExpSourceChart
public import Balaban.Fluctuation.PhysicalTerms
public import Balaban.Fluctuation.SourceFamilyRelative
public import Balaban.Inhabited.ExpSourceChartFromTower
import Mathlib.Tactic.Linarith

/-!
# The source part of the value bridge: `physVal` against `W₂` of a joint representation

For the zero class there are no old terms, no observable terms and no `ν`-part; the five-part
expanded function `physVal` of `physical_directTerms_eta_scaled` then has only its interaction
part and its source part (`physVal_zeroClass_eq`).  Its source argument is the physical source `g`
scaled by `1/β` (`physInclScaled (1/β)`), which is the convention `g ↦ g/β` of `W2_eq_val_sub`
(`physInclScaled_zeroClass_eq`).  With this:

* `W2_eq_physVal_sub`: at a chart point `e` of `physV` and a complex hat variable `x` whose ray
  stays within the radius `pp`, `Jr.W2 C g (rawOf D, τ • x)` is the value of `physVal` at the scaled
  point `physInclScaled (1/β) e` minus its value at the same raw datum with source `0`, along the
  segment `τ ∈ [0,1]` (both with the second hat argument `x`);
* `sourcePhysVal_W2_fromTower`: the same at the central datum of the step of the shared tower, for
  every `D : StepScaleData` (the `Jr` of `expSourceChart_scale_fromTower`).

The interaction part `W₁` is not treated here.  No activity, label or almost-everywhere statement
is asserted.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix Set

section PhysValZero

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)
variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
variable {τι μι : Type*} [DecidableEq τι] [DecidableEq μι]
variable {ϱ₁ ϱ₂ : τι → ℝ} {ϱ₁M ϱ₂M : μι → ℝ}
variable {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
  {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
  {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
  {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
  {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
  {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
  {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
  {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}

/-- **`physVal` for the zero class.**  With no old terms, no observable terms and no `ν`-part
(`𝒯E = ∅`, `𝒯M = ∅`, `cν = 0`), `cβ = β` and `cc = β_U^{-1/2}`, the function `physVal` is the sum of
its interaction part and its source part, the formula of `sourceDirectTerms_slice`. -/
theorem physVal_zeroClass_eq (𝒯E : Finset τι) (𝒯M : Finset μι)
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N S.G' (GkE τ) (GjE τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀E τ)
      (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N S.G' (GkE τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂
      BG₂ δ₁ δfl (X₁E τ))
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N S.G' (GkM τ) (GjM τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀M τ)
      (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N S.G' (GkM τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂
      BG₂ δ₁ δfl (X₁M τ))
    (cν : ℂ) (h𝒯E : 𝒯E = ∅) (h𝒯M : 𝒯M = ∅) (hcν : cν = 0) (x w σ p) :
    physVal (EE := EE) (EM := EM) S (S.β : ℂ) S.hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        𝒯E hBE hFE 𝒯M ys is hBM hFM cν x w σ p =
      (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight x.1 w.1 σ p.1 +
        (S.β : ℂ) * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
          dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi S.G' S.a₁ S.ν eps
              (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
                (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ p.1) := by
  subst h𝒯E h𝒯M hcν
  simp [physVal]

/-- **The scaling convention.**  The inclusion `physInclScaled (1/β)` keeps the raw datum and
sends the source `g` to `g/β` (the source coordinate of `val` in `W2_eq_val_sub`). -/
theorem physInclScaled_zeroClass_eq (e : physParam N S) :
    physInclScaled N S (((1 / S.β : ℝ)) : ℂ) e =
      ((e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), fun y i => e.2 y i / (S.β : ℂ)) := by
  rw [physInclScaled_apply]
  refine Prod.ext rfl (funext fun y => funext fun i => ?_)
  push_cast
  ring

end PhysValZero

namespace StepSetting.JointRep

open Filter Topology

section Chart

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ}
variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc pp r₀ δ₃ δfl : ℝ}
variable {τι μι : Type*} [DecidableEq τι] [DecidableEq μι]
variable {ϱ₁ ϱ₂ : τι → ℝ} {ϱ₁M ϱ₂M : μι → ℝ}
variable {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
  {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
  {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
  {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
  {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
  {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
  {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
  {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
variable (Jr : S.JointRep eps pp)
variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
  (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
  (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
  (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
    c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
  (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)

include Jr hC ha₁ H hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ hδ₁ in
/-- **The source side of the value bridge (T1).**  For the zero class, a chart point
`e ∈ physV S a₁ ν ε` (equivalently `physVq … 1`, `physVq_one`) with source `e.2 = g`, and a complex
hat variable `x` whose rays `r x`, `r ∈ [0,1]`, stay within the radius `pp < c_ψ`, the source
exponent `Jr.W2` on the segment `τ ↦ τ x`, `τ ∈ [0,1]`, is the difference of two values of
`physVal` (with no old terms, no observable terms and no `ν`-part, `cβ = β`, `cc = β_U^{-1/2}`):
at the scaled point `physInclScaled (1/β) e = (e.1, g/β)` and at `(e.1, 0)`, both at the hat
arguments `(x,x)`, `(x,x)` and the parameter `τ`.  The factor `1/β` enters only through the scaling
of the source. -/
theorem W2_eq_physVal_sub (hpc : pp < cψ) (e : physParam N S)
    (he : e ∈ physV S S.a₁ S.ν eps) (hβ : (S.β : ℂ) ≠ 0) (x : S.EC)
    (hxb : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → ∀ p, ‖((r : ℂ) • x) p‖ ≤ pp)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (𝒯E : Finset τι) (𝒯M : Finset μι)
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N S.G' (GkE τ) (GjE τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀E τ)
      (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N S.G' (GkE τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂
      BG₂ δ₁ δfl (X₁E τ))
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N S.G' (GkM τ) (GjM τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀M τ)
      (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N S.G' (GkM τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂
      BG₂ δ₁ δfl (X₁M τ))
    (cν : ℂ) (h𝒯E : 𝒯E = ∅) (h𝒯M : 𝒯M = ∅) (hcν : cν = 0) :
    Jr.W2 (zeroClass d L N₁ m₁ k N ϱ) e.2
        ((e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), (τ : ℂ) • x) =
      physVal (EE := EE) (EM := EM) S (S.β : ℂ) S.hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          𝒯E hBE hFE 𝒯M ys is hBM hFM cν (x, x) (x, x) (τ : ℂ)
          (physInclScaled N S (((1 / S.β : ℝ)) : ℂ) e) -
        physVal (EE := EE) (EM := EM) S (S.β : ℂ) S.hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          𝒯E hBE hFE 𝒯M ys is hBM hFM cν (x, x) (x, x) (τ : ℂ)
          (physInclScaled N S (((1 / S.β : ℝ)) : ℂ) (e.1, 0)) := by
  obtain ⟨D, hD, hq⟩ := he.1
  have hq' : (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D := hq
  rw [hq']
  have h1 := Jr.W2_eq_val_sub hC ha₁ H hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ hδ₁
    hpc hD e.2 hβ x hxb hτ
    (physVal (EE := EE) (EM := EM) S (S.β : ℂ) S.hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      𝒯E hBE hFE 𝒯M ys is hBM hFM cν)
    (physVal_zeroClass_eq S 𝒯E 𝒯M hBE hFE ys is hBM hFM cν h𝒯E h𝒯M hcν)
  rw [h1, physInclScaled_zeroClass_eq, physInclScaled_zeroClass_eq]
  have h0 : (fun y i => ((0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) y i) / (S.β : ℂ)) = 0 := by
    funext y i; simp
  simp only [hq', h0]

end Chart

end StepSetting.JointRep

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology

/-- **The source side of the value bridge at the shared tower.**  For the step
`T.step k hk N₁ ν β p₁` of the tower `T` with a per-scale package `D`, there is a `JointRep` `Jr`
such that, for every hat variable `x` with rays within `2 p₁`, every source `g` and every `τ ∈ [0,1]`,
the zero-class exponent `Jr.W2` at the central datum `rawOf S.D'` equals the difference of the values
of `physVal` (no old terms, no observable terms, no `ν`-part, `cβ = β`, `cc = β_U^{-1/2}`) at the
scaled points `physInclScaled (1/β) (rawOf S.D', g)` and `physInclScaled (1/β) (rawOf S.D', 0)`.
The constants of the unused old and observable terms are arbitrary. -/
theorem sourcePhysVal_W2_fromTower {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) (hp0 : 0 < p₁)
    (D : StepScaleData T k hk N₁ ν β p₁) :
    ∃ Jr : (T.step k hk N₁ ν β p₁).JointRep T.t (2 * p₁),
      ∀ {c BG Kc Cx c₂ δ₁ r₀ δ₃ δfl : ℝ} {τι μι : Type} [DecidableEq τι] [DecidableEq μι]
        {ϱ₁ ϱ₂ : τι → ℝ} {ϱ₁M ϱ₂M : μι → ℝ}
        {GkE : ∀ τ, GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) (ϱ₁ τ)}
        {GjE : ∀ τ, GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) (ϱ₂ τ)}
        {X₀E X₁E : τι → Finset (CTorus 3 3 N₁ T.m₁ (k + 1))} {jE : τι → ℕ}
        {GkM : ∀ τ, GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) (ϱ₁M τ)}
        {GjM : ∀ τ, GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) (ϱ₂M τ)}
        {X₀M X₁M : μι → Finset (CTorus 3 3 N₁ T.m₁ (k + 1))} {jM : μι → ℕ}
        {EE : τι → RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 → ℂ}
        {EM : μι → RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 → ℂ}
        (𝒯E : Finset τι) (𝒯M : Finset μι)
        (hBE : ∀ τ ∈ 𝒯E, BgSetting 2 (T.step k hk N₁ ν β p₁).G' (GkE τ) (GjE τ)
          (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν c BG T.κ r₀ T.t δ₃ (X₀E τ)
          (X₁E τ) (jE τ))
        (hFE : ∀ τ ∈ 𝒯E, FlSetting 2 (T.step k hk N₁ ν β p₁).G' (GkE τ)
          (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν T.κ BG T.t δ₃ Kc Cx c₂ T.BG₂ δ₁ δfl (X₁E τ))
        (ys : μι → CTorus 3 3 N₁ T.m₁ (k + 1)) (is : μι → Fin 2)
        (hBM : ∀ τ ∈ 𝒯M, BgSetting 2 (T.step k hk N₁ ν β p₁).G' (GkM τ) (GjM τ)
          (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν c BG T.κ r₀ T.t δ₃ (X₀M τ)
          (X₁M τ) (jM τ))
        (hFM : ∀ τ ∈ 𝒯M, FlSetting 2 (T.step k hk N₁ ν β p₁).G' (GkM τ)
          (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν T.κ BG T.t δ₃ Kc Cx c₂ T.BG₂ δ₁ δfl (X₁M τ))
        (cν : ℂ), 𝒯E = ∅ → 𝒯M = ∅ → cν = 0 → ∀
        (g : Fld 3 3 N₁ T.m₁ (k + 1) 2) (x : (T.step k hk N₁ ν β p₁).EC),
        (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → ∀ q, ‖((r : ℂ) • x) q‖ ≤ 2 * p₁) →
        ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) 1 →
          Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g
              (rawOf (T.step k hk N₁ ν β p₁).D', (τ : ℂ) • x) =
            physVal (EE := EE) (EM := EM) (T.step k hk N₁ ν β p₁)
                ((T.step k hk N₁ ν β p₁).β : ℂ) (T.step k hk N₁ ν β p₁).hG
                (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                𝒯E hBE hFE 𝒯M ys is hBM hFM cν (x, x) (x, x) (τ : ℂ)
                (physInclScaled 2 (T.step k hk N₁ ν β p₁)
                  ((1 / (T.step k hk N₁ ν β p₁).β : ℝ) : ℂ)
                  (⟨rawOf (T.step k hk N₁ ν β p₁).D', rawOf_mem_rawSub _⟩, g)) -
              physVal (EE := EE) (EM := EM) (T.step k hk N₁ ν β p₁)
                ((T.step k hk N₁ ν β p₁).β : ℂ) (T.step k hk N₁ ν β p₁).hG
                (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                𝒯E hBE hFE 𝒯M ys is hBM hFM cν (x, x) (x, x) (τ : ℂ)
                (physInclScaled 2 (T.step k hk N₁ ν β p₁)
                  ((1 / (T.step k hk N₁ ν β p₁).β : ℝ) : ℂ)
                  (⟨rawOf (T.step k hk N₁ ν β p₁).D', rawOf_mem_rawSub _⟩, 0)) := by
  obtain ⟨Jr, val, hval, hW⟩ := expSourceChart_scale_fromTower T k hk N₁ ν hνpos hν β p₁ hp0 D
  refine ⟨Jr, ?_⟩
  intro c BG Kc Cx c₂ δ₁ r₀ δ₃ δfl τι μι _ _ ϱ₁ ϱ₂ ϱ₁M ϱ₂M GkE GjE X₀E X₁E jE GkM GjM X₀M X₁M jM
    EE EM 𝒯E 𝒯M hBE hFE ys is hBM hFM cν h𝒯E h𝒯M hcν g x hx τ hτ
  have hv : ∀ a b σ Θ, val a b σ Θ = physVal (EE := EE) (EM := EM) (T.step k hk N₁ ν β p₁)
      ((T.step k hk N₁ ν β p₁).β : ℂ) (T.step k hk N₁ ν β p₁).hG
      (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      𝒯E hBE hFE 𝒯M ys is hBM hFM cν a b σ Θ := fun a b σ Θ =>
    (hval a b σ Θ).trans
      (physVal_zeroClass_eq (T.step k hk N₁ ν β p₁) 𝒯E 𝒯M hBE hFE ys is hBM hFM cν
        h𝒯E h𝒯M hcν a b σ Θ).symm
  rw [hW g x hx τ hτ, hv, hv, physInclScaled_zeroClass_eq, physInclScaled_zeroClass_eq]
  have h0 : (fun y i => ((0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ) y i) /
      ((T.step k hk N₁ ν β p₁).β : ℂ)) = 0 := by
    funext y i; simp
  simp only [h0]

end Balaban.Inhabited
