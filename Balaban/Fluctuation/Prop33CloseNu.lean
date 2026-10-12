/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Prop33
public import Balaban.Fluctuation.Prop33Nu
public import Balaban.Fluctuation.Prop33CloseReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The merged bound of Proposition 3.3 with the `ν`-part (W136b)

`interaction_expansion_bound_nu`: `interaction_expansion_bound` plus the `ν`-part
(`nupart_locInt_bound`), added with `LocInt.add₂` after lifting (`mulAmp`), scaling (`smul`) and pulling
back (`comap`); `interaction_expansion_bound_nu_closed`: the same with the domain premise `hreal`
replaced by the source smallness `δ₀ + 5 R δ₁ ≤ c₁` (`hreal_level`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Set Metric

section AddLift

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
variable {F F' : Type*} {ι : Type*} [DecidableEq ι]

/-- **Adding a `Θ`-only part to a localized expansion in `(Θ, g)`**: lifted by the amplitude `1`,
pulled back along a projection of the directions and scaled by `c`. -/
theorem LocInt.addLift {S : Set Λ} {SG : Set G} {Rσ : ℝ} {XW : Set (F' × F')} {XWν : Set (F × F)}
    {𝒴 𝒴ν : Finset ι} {T : ι → F' → F' → ℂ → Λ × G → ℂ} {Tν : ι → F → F → ℂ → Λ → ℂ}
    {val : F' → F' → ℂ → Λ × G → ℂ} {valν : F → F → ℂ → Λ → ℂ} {b bν : ι → ℝ}
    {AgΘ : ι → Λ → Λ → Prop} {AgG : ι → G → G → Prop} {AgF : ι → F → F → Prop}
    {AgF' : ι → F' → F' → Prop} (π : F' → F)
    (hXW : ∀ xw ∈ XW, (π xw.1, π xw.2) ∈ XWν)
    (hAg : ∀ Y a a', AgF' Y a a' → AgF Y (π a) (π a'))
    (hν : LocInt S XWν Rσ 𝒴ν Tν valν bν AgΘ AgF)
    (hL : LocInt (S ×ˢ SG) XW Rσ 𝒴 T val b (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2) AgF')
    (c : ℂ) :
    ∃ T' : ι → F' → F' → ℂ → Λ × G → ℂ,
      LocInt (S ×ˢ SG) XW Rσ (𝒴 ∪ 𝒴ν) T'
        (fun x w σ p => val x w σ p + c * valν (π x) (π w) σ p.1)
        (fun Y => (if Y ∈ 𝒴 then b Y else 0) + (if Y ∈ 𝒴ν then ‖c‖ * (1 * bν Y) else 0))
        (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2) AgF' := by
  have h1 := hν.mulAmp (SG := SG) (amp := fun _ => (1 : ℂ)) (Ma := 1)
    (analyticOnNhd_const) (fun _ _ => by simp) (AgG := AgG) (fun _ _ _ _ _ _ _ => rfl)
  have h2 := (h1.smul c).comap (F' := F') π (XW' := XW) hXW (AgF' := AgF') hAg
  exact ⟨_, (hL.add₂ h2).congr_val (fun xw hxw σ hσ p hp => by simp only [one_mul])⟩

end AddLift

end Balaban.Fluctuation

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix Set Metric

section Merged

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {n : ℕ} {a₁ ν c BG κ eps : ℝ}

/-- **Proposition 3.3 with the `ν`-part**: `interaction_expansion_bound` plus the term
`cν · dirTermSrc (nuTotal)`, with the source bound `‖h̃‖ ≤ Bh` on `Ξ^c` and the block margin
`blockSites ⊆ X₁`. -/
theorem interaction_expansion_bound_nu {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (cβ : ℂ)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    -- the potential part
    (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (hp : n + 1 ≤ K) (ha₁ : 0 < a₁)
    (H : BgHyp d L K ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
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
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Set (CTorus d L N₁ m₁ K)}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Finset (CTorus d L N₁ m₁ K)}
    (hcovV : ∀ z, CovSetup Gp (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))), Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hn1 : 1 ≤ n) (hZV : ∀ z, readSites Hm n z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin Gp (X₁V z)
      (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)))
    -- the old terms
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ K)} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ K)} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N Gp (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N Gp (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup Gp (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) K N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    -- the sites of the source
    {jF : CTorus d L N₁ m₁ K × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ K × Fin N → Set (CTorus d L N₁ m₁ K)}
    {X₁F : CTorus d L N₁ m₁ K × Fin N → Finset (CTorus d L N₁ m₁ K)}
    (hcovF : ∀ s, CovSetup Gp (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ K × Fin N, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ K × Fin N, s.1 ∈ X₁F s)
    -- the observable terms
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ K)} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ K)} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ K) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N Gp (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N Gp (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup Gp (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) K N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    -- the sizes of the old terms and of the observable terms (the source bounds of (3.2)-(3.4)):
    -- the bounds of the terms rooted at one site (resp. at one source site) add up to `ρ`
    (rE : τι → CTorus d L N₁ m₁ K) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ K, ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ K × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM)
    -- the `ν`-part: the bound on the external field and the block margin of the blocks
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh) (cν : ℂ)
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)) ⊆ ↑(X₁V z)) :
    ∃ (𝒴 : Finset (Set (CTorus d L N₁ m₁ K)))
      (T : Set (CTorus d L N₁ m₁ K) →
        ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ)) →
        ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ)) → ℂ →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ l1Ball d L N₁ m₁ K N)
        {xw : ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ)) ×
            ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ)) |
          ((xw.1.1, xw.2.1) ∈ {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) ×
              (CTorus d L N₁ m₁ K → Fin N → ℂ) |
            (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
            IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2}) ∧
          (xw.1.1, xw.2.1) ∈ {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) ×
              (CTorus d L N₁ m₁ K → Fin N → ℂ) |
            ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} ∧
          (xw.1.2, xw.2.2) ∈ {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) ×
              (CTorus d L N₁ m₁ K → Fin N → ℂ) |
            ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} ∧
          (xw.1.2, xw.2.2) ∈ {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) ×
              (CTorus d L N₁ m₁ K → Fin N → ℂ) |
            (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
            IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2}} Rσ 𝒴 T
        (fun x w σ p =>
          (-cβ) * raySrc3 (interactionOne hG hG' hp a₁ ν eps) taylorWeight x.1 w.1 σ p.1 +
          cβ * (∑ τ ∈ 𝒯E, if h : τ ∈ 𝒯E then
            dirTermSrc (flComp (hBE τ h) (hFE τ h) (EE τ)) (fun _ => (1 : ℂ)) x.1 w.1 σ p.1
            else 0) +
          cβ * (∑ s : CTorus d L N₁ m₁ K × Fin N, p.2 s.1 s.2 * dirTermSrc (onXi Gp a₁ ν eps
            (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2))
            (fun _ => (1 : ℂ)) x.2 w.2 σ p.1) +
          cβ * (∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
            p.2 (ys τ) (is τ) * dirTermSrc (flComp (hBM τ h) (hFM τ h) (EM τ))
              (fun _ => (1 : ℂ)) x.2 w.2 σ p.1 else 0) +
          cν * dirTermSrc (onXi Gp a₁ ν eps
            (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ')) (fun _ => (1 : ℂ)) x.1 w.1 σ p.1)
        (fun Y => prop33Eps d L N m₁ n m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM * ‖cβ‖ *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y) +
          ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
            nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
              (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
            Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y))) (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (fun Y a a' => (∀ y ∈ psiThick Y, a.1 y = a'.1 y) ∧ (∀ y ∈ psiThick Y, a.2 y = a'.2 y)) := by
  classical
  obtain ⟨𝒴, T, hL⟩ := interaction_expansion_bound (Rσ := Rσ) hC cβ hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hG hG' hp ha₁ H hc7 hR hRs hsmall hnum hnum' hreal hcovV hX₁V hoptV hΔV hlogV hn1 hZV hmarV 𝒯E hBE hFE hcovE hX₁E hoptE hlogE hEbE hEanE hEbdE hcovF hX₁F hoptF hΔF hlogF hyF 𝒯M ys is hys hBM hFM hcovM hX₁M hoptM hlogM hEbM hEanM hEbdM rE hrE hρE0 hρE hρM0 hρM
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  obtain ⟨Tν, hν⟩ := nupart_locInt_bound hC hp hG' hBh0 hBh hcovV hX₁V hconn hrow hoptV hΔV hκ₀
    hκdec hκ h1 (hlogV 0) hZν (ω := fun _ => (1 : ℂ)) continuous_const hR₁ analyticOnNhd_const
    (Mω := 1) zero_le_one (fun t ht => by simp) hr (Rσ := Rσ)
  obtain ⟨T', hT'⟩ := LocInt.addLift (SG := l1Ball d L N₁ m₁ K N) (π := Prod.fst) (Rσ := Rσ)
    (F := CTorus d L N₁ m₁ K → Fin N → ℂ)
    (F' := (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ))
    (AgG := fun Y (g g' : CTorus d L N₁ m₁ K → Fin N → ℂ) => ∀ x ∈ Y, g x = g' x)
    (AgF' := fun Y a a' => (∀ y ∈ psiThick Y, a.1 y = a'.1 y) ∧ (∀ y ∈ psiThick Y, a.2 y = a'.2 y))
    (fun xw hxw => hxw.2.1) (fun Y a a' h => h.1) hν hL cν
  have hL0 : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hK2 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hEps : 0 ≤ prop33Eps d L N m₁ n m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM := by
    unfold prop33Eps; positivity
  have hnu0 : 0 ≤ nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) := by
    have hK4 : 0 < K4 d L N BG κ := K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0
    have hx1 := one_le_xiC1 d
    have hx2 := hC.eps_pos
    have hx3 : 0 ≤ xiC1 d * eps := by positivity
    have hx4 := mul_nonneg hK4.le hx3
    unfold nuBd
    have : 0 ≤ K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh := by linarith
    positivity
  refine ⟨_, _, (hT'.congr_val ?_).mono fun Y => ?_⟩
  · intro xw hxw σ hσ p hp'
    rfl
  · have hb1 : 0 ≤ prop33Eps d L N m₁ n m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM * ‖cβ‖ *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y) := by positivity
    have hb2 : 0 ≤ ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
            nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
              (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
            Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y)) := by positivity
    split_ifs <;> simp only [one_mul] at * <;> linarith

/-- **Proposition 3.3 with the `ν`-part, domain premise replaced by its smallness.** -/
theorem interaction_expansion_bound_nu_closed {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (cβ : ℂ)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    -- the potential part
    (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (hp : n + 1 ≤ K) (ha₁ : 0 < a₁)
    (H : BgHyp d L K ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Set (CTorus d L N₁ m₁ K)}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Finset (CTorus d L N₁ m₁ K)}
    (hcovV : ∀ z, CovSetup Gp (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))), Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hn1 : 1 ≤ n) (hZV : ∀ z, readSites Hm n z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin Gp (X₁V z)
      (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)))
    -- the old terms
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ K)} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ K)} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N Gp (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N Gp (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup Gp (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) K N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    -- the sites of the source
    {jF : CTorus d L N₁ m₁ K × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ K × Fin N → Set (CTorus d L N₁ m₁ K)}
    {X₁F : CTorus d L N₁ m₁ K × Fin N → Finset (CTorus d L N₁ m₁ K)}
    (hcovF : ∀ s, CovSetup Gp (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ K × Fin N, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ K × Fin N, s.1 ∈ X₁F s)
    -- the observable terms
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ K)} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ K)} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ K) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N Gp (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N Gp (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup Gp (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) K N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    -- the sizes of the old terms and of the observable terms (the source bounds of (3.2)-(3.4)):
    -- the bounds of the terms rooted at one site (resp. at one source site) add up to `ρ`
    (rE : τι → CTorus d L N₁ m₁ K) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ K, ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ K × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM)
    -- the `ν`-part: the bound on the external field and the block margin of the blocks
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh) (cν : ℂ)
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)) ⊆ ↑(X₁V z)) :
    ∃ (𝒴 : Finset (Set (CTorus d L N₁ m₁ K)))
      (T : Set (CTorus d L N₁ m₁ K) →
        ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ)) →
        ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ)) → ℂ →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ l1Ball d L N₁ m₁ K N)
        {xw : ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ)) ×
            ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ)) |
          ((xw.1.1, xw.2.1) ∈ {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) ×
              (CTorus d L N₁ m₁ K → Fin N → ℂ) |
            (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
            IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2}) ∧
          (xw.1.1, xw.2.1) ∈ {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) ×
              (CTorus d L N₁ m₁ K → Fin N → ℂ) |
            ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} ∧
          (xw.1.2, xw.2.2) ∈ {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) ×
              (CTorus d L N₁ m₁ K → Fin N → ℂ) |
            ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} ∧
          (xw.1.2, xw.2.2) ∈ {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) ×
              (CTorus d L N₁ m₁ K → Fin N → ℂ) |
            (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
            IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2}} Rσ 𝒴 T
        (fun x w σ p =>
          (-cβ) * raySrc3 (interactionOne hG hG' hp a₁ ν eps) taylorWeight x.1 w.1 σ p.1 +
          cβ * (∑ τ ∈ 𝒯E, if h : τ ∈ 𝒯E then
            dirTermSrc (flComp (hBE τ h) (hFE τ h) (EE τ)) (fun _ => (1 : ℂ)) x.1 w.1 σ p.1
            else 0) +
          cβ * (∑ s : CTorus d L N₁ m₁ K × Fin N, p.2 s.1 s.2 * dirTermSrc (onXi Gp a₁ ν eps
            (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2))
            (fun _ => (1 : ℂ)) x.2 w.2 σ p.1) +
          cβ * (∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
            p.2 (ys τ) (is τ) * dirTermSrc (flComp (hBM τ h) (hFM τ h) (EM τ))
              (fun _ => (1 : ℂ)) x.2 w.2 σ p.1 else 0) +
          cν * dirTermSrc (onXi Gp a₁ ν eps
            (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ')) (fun _ => (1 : ℂ)) x.1 w.1 σ p.1)
        (fun Y => prop33Eps d L N m₁ n m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM * ‖cβ‖ *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y) +
          ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
            nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
              (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
            Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y))) (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (fun Y a a' => (∀ y ∈ psiThick Y, a.1 y = a'.1 y) ∧ (∀ y ∈ psiThick Y, a.2 y = a'.2 y)) :=
  interaction_expansion_bound_nu hC cβ hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hG hG' hp ha₁ H hc7 hR hRs hsmall hnum hnum' (hreal_level hC hG hG' hp ha₁ H hc7 (by linarith) hsm) hcovV hX₁V hoptV hΔV hlogV hn1 hZV hmarV 𝒯E hBE hFE hcovE hX₁E hoptE hlogE hEbE hEanE hEbdE hcovF hX₁F hoptF hΔF hlogF hyF 𝒯M ys is hys hBM hFM hcovM hX₁M hoptM hlogM hEbM hEanM hEbdM rE hrE hρE0 hρE hρM0 hρM hBh0 hBh cν hZν

end Merged

end Balaban.Localization
