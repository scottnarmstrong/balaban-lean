/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionHatAssemble
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Proposition 3.3 in the variable `ψ̂`: the `η`-sharpened source bounds

HAT-RATE section 3.  For a source of size `‖g‖₁ ≤ η` (`0 < η ≤ 1`) the two source parts of
`interaction_expansion_hat_bound` carry the factor `η`:

* `sum_weighted_le_eta`: the weighted rooted sum with `∑ f ≤ η` is at most `η ρ`;
* `l1BallEta`: the sources `g` with `‖g‖₁ < 1` and `‖g‖₁ ≤ η` (a subset of `l1Ball`);
* `hat_fparts_bound_eta`, `hat_mparts_bound_eta`, `interaction_expansion_hat_bound_eta`:
  the landed theorems on the parameter set `XiCRaw ×ˢ l1BallEta`, with bounds multiplied by `η`
  for the source terms;
* `prop33EpsEta` (`η = 1` is `prop33Eps`), and `prop33_physical_source_bound` for
  `η = 1/β`, `ρE = ρE_phys/β`, multiplied by `β`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Finset

section Weighted

variable {τι : Type*} {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **Weighted sums of site terms, sharpened** (HAT-RATE (3.1)).  With `∑ f ≤ η` the sum
`∑_τ f(root τ) w_τ` is at most `η ρ`. -/
theorem sum_weighted_le_eta [DecidableEq τι] (𝒯 : Finset τι) (w : τι → ℝ)
    (rt : τι → α × β) (f : α × β → ℝ) (hf : ∀ p, 0 ≤ f p) {η : ℝ} (hf1 : ∑ p, f p ≤ η) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ∀ p, ∑ τ ∈ 𝒯.filter (fun τ => rt τ = p), w τ ≤ ρ) :
    ∑ τ ∈ 𝒯, f (rt τ) * w τ ≤ η * ρ := by
  classical
  have e1 : ∑ τ ∈ 𝒯, f (rt τ) * w τ =
      ∑ p, f p * ∑ τ ∈ 𝒯.filter (fun τ => rt τ = p), w τ := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := 𝒯) (t := Finset.univ) (g := rt)
      (fun τ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ hτ => by rw [(Finset.mem_filter.1 hτ).2]
  rw [e1]
  calc ∑ p, f p * ∑ τ ∈ 𝒯.filter (fun τ => rt τ = p), w τ ≤ ∑ p, f p * ρ :=
        Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hρ p) (hf p)
    _ = (∑ p, f p) * ρ := by rw [Finset.sum_mul]
    _ ≤ η * ρ := mul_le_mul_of_nonneg_right hf1 hρ0

/-- At `η = 1` this is the landed `sum_weighted_le`. -/
theorem sum_weighted_le_of_sum_weighted_le_eta [DecidableEq τι] (𝒯 : Finset τι) (w : τι → ℝ)
    (rt : τι → α × β) (f : α × β → ℝ) (hf : ∀ p, 0 ≤ f p) (hf1 : ∑ p, f p ≤ 1) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ∀ p, ∑ τ ∈ 𝒯.filter (fun τ => rt τ = p), w τ ≤ ρ) :
    ∑ τ ∈ 𝒯, f (rt τ) * w τ ≤ ρ := by
  simpa using sum_weighted_le_eta 𝒯 w rt f hf hf1 hρ0 hρ

end Weighted

end Balaban.Fluctuation

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix Set Metric

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps : ℝ}

/-- The sources `g` with `∑ |g| < 1` (the landed `l1Ball`) and `∑ |g| ≤ η`. -/
def l1BallEta (d L N₁ m₁ K N : ℕ) [NeZero N₁] [NeZero L] (η : ℝ) : Set (CTorus d L N₁ m₁ K → Fin N → ℂ) :=
  {g | g ∈ l1Ball d L N₁ m₁ K N ∧ ∑ x, ∑ i, ‖g x i‖ ≤ η}

theorem l1BallEta_subset {K : ℕ} (η : ℝ) : l1BallEta d L N₁ m₁ K N η ⊆ l1Ball d L N₁ m₁ K N :=
  fun _ h => h.1

theorem l1BallEta_one {K : ℕ} : l1BallEta d L N₁ m₁ K N 1 = l1Ball d L N₁ m₁ K N :=
  Set.ext fun _ => ⟨fun h => h.1, fun h => ⟨h, le_of_lt h⟩⟩

/-- The amplitude of (3.2) of HAT-RATE: `η = 1` is `prop33Eps`. -/
noncomputable def prop33EpsEta (d L N m₁ n m₀ : ℕ) (a₁ ν BG BG₂ κ δ₁ r ρE ρM η : ℝ) : ℝ :=
  3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * ‖energyBd d L N (compWeight L a₁) ν n
      (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / r ^ 3 +
    ρE * c1 d L * ((L : ℝ) ^ (n + 1)) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d / r +
    η * (cK2' d L N (famConst d L BG₂ κ) * δ₁ + ρM) / r

theorem prop33EpsEta_one (d L N m₁ n m₀ : ℕ) (a₁ ν BG BG₂ κ δ₁ r ρE ρM : ℝ) :
    prop33EpsEta d L N m₁ n m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM 1 =
      prop33Eps d L N m₁ n m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM := by
  unfold prop33EpsEta prop33Eps; ring

theorem prop33EpsEta_mono (d L N m₁ n m₀ : ℕ) (a₁ ν BG BG₂ κ δ₁ r ρE ρM : ℝ) (hr : 0 < r)
    (hK : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁) (hρM : 0 ≤ ρM) {η η' : ℝ} (h : η ≤ η') :
    prop33EpsEta d L N m₁ n m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM η ≤
      prop33EpsEta d L N m₁ n m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM η' := by
  unfold prop33EpsEta
  have : η * (cK2' d L N (famConst d L BG₂ κ) * δ₁ + ρM) / r ≤
      η' * (cK2' d L N (famConst d L BG₂ κ) * δ₁ + ρM) / r :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h (by linarith)) hr.le
  linarith

/-- **HAT-RATE (3.3).**  Physical source `g/β`, `η = 1/β`, `ρE = ρE_phys/β`, times `c_β = β`:
no factor `β` on the source terms or on the old-energy term. -/
theorem prop33_physical_source_bound (d L N m₁ n m₀ : ℕ) (a₁ ν BG BG₂ κ δ₁ r ρEphys ρM β : ℝ)
    (hβ : 1 ≤ β) :
    β * prop33EpsEta d L N m₁ n m₀ a₁ ν BG BG₂ κ δ₁ r (ρEphys / β) ρM (1 / β) =
      3 * β * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * ‖energyBd d L N (compWeight L a₁) ν n
        (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / r ^ 3 +
      (ρEphys * c1 d L * ((L : ℝ) ^ (n + 1)) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d +
        cK2' d L N (famConst d L BG₂ κ) * δ₁ + ρM) / r := by
  have hβ0 : β ≠ 0 := by positivity
  unfold prop33EpsEta
  field_simp
  ring

/-- The source sites with the `η`-sharpened bound (HAT-RATE (3.1)): the bound is asserted for
`‖g‖₁ < 1`, `‖g‖₁ ≤ η`. -/
theorem hat_fparts_bound_eta {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    {η : ℝ} (hη0 : 0 < η) (_hη1 : η ≤ 1)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {m₀ : ℕ}
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup Gp (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N,
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) → (unitPts Gp × Fin N → ℂ) →
        ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1BallEta d L N₁ m₁ (k + 1) N η)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion fun s => polymerDomains
          (fun i : ParIdx Gp (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ (jF s) (𝒦XF s))) T
        (fun x w σ p => ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
          dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
            (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2)))
            (fun _ => (1 : ℂ)) x w σ p.1)
        (fun Y => (η * (cK2' d L N (famConst d L BG₂ κ) * δ₁) / r) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x) (AgHatF Gp hG') := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hK2 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hr3 : 0 < r ^ 3 := by positivity
  have hM0 : 0 ≤ ((L : ℝ) ^ (m₀ + m₁)) ^ d := by positivity
  have hP0 : 0 ≤ ((L : ℝ) ^ (k + 1)) ^ d := by positivity
  -- the sites of the source
  have hexF := fun s : CTorus d L N₁ m₁ (k + 1) × Fin N =>
    fsite_base_locInt_hat hC hk hG hG' cc hcψ hMX hdm hα hsmX hδ₁ (hcovF s) (hX₁F s) hconn hrow
      (hoptF s) (hΔF s) hκ₀ hκdec hκ h1 (hlogF s) s.1 (hyF s) s.2 (ω := fun _ => (1 : ℂ))
      continuous_const hR₁ analyticOnNhd_const (Mω := 1) zero_le_one (fun t ht => by simp) hr
      (Rσ := Rσ)
  choose EvF hEvF using hexF
  have hLF := LocInt.wsum (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) × Fin N))
    (𝒴 := fun s => polyDom Gp (X₁F s) m₀ (jF s) (𝒦XF s)) (fun s _ => hEvF s)
    (SG := l1BallEta d L N₁ m₁ (k + 1) N η) (amp := fun s g => g s.1 s.2)
    (fun s _ => (analyticOnNhd_coord s.1 s.2).mono (Set.subset_univ _))
    (AgG := fun Y (g g' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) => ∀ x ∈ Y, g x = g' x)
    (fun s _ Y hY g _ g' _ hag => by
      have h1' := subset_polyDom hY
      rw [← hX₁F s] at h1'
      exact congrFun (hag s.1 (h1' (Finset.mem_coe.2 (hyF s)))) s.2)
    (B := fun Y => (η * (cK2' d L N (famConst d L BG₂ κ) * δ₁) / r) *
      Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
    (fun Y _ g hg => by
      have ht0 := treeLenCov_nonneg Gp m₀ Y
      rw [← treeLenCov_eq_treeLenCovOne hG' m₀ Y]
      set β := 1 * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) / r) with hβ
      have hβ0 : 0 ≤ β := by positivity
      have hβle : β ≤ (cK2' d L N (famConst d L BG₂ κ) * δ₁ / r) *
          Real.exp (-(2 * κdec - 1) * treeLenCov Gp m₀ Y) := by
        rw [hβ, one_mul, mul_div_right_comm]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (by positivity)
      have hsum : ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, ‖g s.1 s.2‖ ≤ η := by
        rw [Fintype.sum_prod_type]; exact hg.2
      calc ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, (if Y ∈ polyDom Gp (X₁F s) m₀ (jF s) (𝒦XF s) then
            ‖g s.1 s.2‖ * β else 0) ≤ ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, ‖g s.1 s.2‖ * β :=
            Finset.sum_le_sum fun s _ => by
              split_ifs
              · exact le_rfl
              · exact mul_nonneg (norm_nonneg _) hβ0
        _ = (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, ‖g s.1 s.2‖) * β := by rw [Finset.sum_mul]
        _ ≤ η * β := mul_le_mul_of_nonneg_right hsum hβ0
        _ ≤ η * ((cK2' d L N (famConst d L BG₂ κ) * δ₁ / r) *
            Real.exp (-(2 * κdec - 1) * treeLenCov Gp m₀ Y)) :=
            mul_le_mul_of_nonneg_left hβle hη0.le
        _ = _ := by ring)
  exact ⟨_, hLF⟩

/-- The observable terms with the `η`-sharpened bound (HAT-RATE (3.1)). -/
theorem hat_mparts_bound_eta {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    {η : ℝ} (hη0 : 0 < η) (_hη1 : η ≤ 1)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {m₀ : ℕ}
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)} {r₀ δ₃ δfl : ℝ}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N Gp (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N Gp (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup Gp (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) → (unitPts Gp × Fin N → ℂ) →
        ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1BallEta d L N₁ m₁ (k + 1) N η)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯M.biUnion fun τ => polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ)) T
        (fun x w σ p => ∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
          p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
            (flComp (hBM τ h) (hFM τ h) (EM τ))) (fun _ => (1 : ℂ)) x w σ p.1 else 0)
        (fun Y => (η * ρM / r) * Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x) (AgHatF Gp hG') := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hK2 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hr3 : 0 < r ^ 3 := by positivity
  have hM0 : 0 ≤ ((L : ℝ) ^ (m₀ + m₁)) ^ d := by positivity
  have hP0 : 0 ≤ ((L : ℝ) ^ (k + 1)) ^ d := by positivity
  -- the observable terms
  have hexM : ∀ τ, ∃ (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ), τ ∈ 𝒯M →
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) (fun _ => (1 : ℂ)) x₀ w σ Θ)
        (fun x₀ w σ Θ => if h : τ ∈ 𝒯M then
          dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hBM τ h) (hFM τ h) (EM τ)))
            (fun _ => (1 : ℂ)) x₀ w σ Θ else 0)
        (fun Y => 1 * ((EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ)
          (XM τ) - 2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
    intro τ
    by_cases hτ : τ ∈ 𝒯M
    · obtain ⟨Ev, hEv⟩ := eterm_locInt_hat (hBM τ hτ) (hFM τ hτ) hk hG hG' cc hcψ hMX hdm hα hsmX
        hδ₁ (hcovM τ hτ) (hX₁M τ hτ) hconn hrow (hoptM τ hτ) hκ₀ hκdec hκ h1 (hlogM τ hτ)
        (hEbM τ hτ) (hEanM τ hτ) (hEbdM τ hτ) (ω := fun _ => (1 : ℂ)) continuous_const hR₁
        analyticOnNhd_const (Mω := 1) zero_le_one (fun t ht => by simp) hr (Rσ := Rσ)
      exact ⟨Ev, fun _ => by simpa [hτ] using hEv⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hτ⟩
  choose EvM hEvM using hexM
  have hLM := LocInt.wsum 𝒯M (𝒴 := fun τ => polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ))
    (fun τ hτ => hEvM τ hτ) (SG := l1BallEta d L N₁ m₁ (k + 1) N η) (amp := fun τ g => g (ys τ) (is τ))
    (fun τ _ => (analyticOnNhd_coord (ys τ) (is τ)).mono (Set.subset_univ _))
    (AgG := fun Y (g g' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) => ∀ x ∈ Y, g x = g' x)
    (fun τ hτ Y hY g _ g' _ hag => by
      have h1' := subset_polyDom hY
      rw [← hX₁M τ hτ] at h1'
      exact congrFun (hag (ys τ) (h1' (Finset.mem_coe.2 (hys τ hτ)))) (is τ))
    (B := fun Y => (η * ρM / r) * Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
    (fun Y _ g hg => by
      classical
      have ht0 := treeLenCov_nonneg Gp m₀ Y
      rw [← treeLenCov_eq_treeLenCovOne hG' m₀ Y]
      set w : μι → ℝ := fun τ => EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) with hw
      have hw0 : ∀ τ ∈ 𝒯M, 0 ≤ w τ := fun τ hτ => mul_nonneg (hEbM τ hτ) (Real.exp_pos _).le
      have hq : 0 ≤ Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r := by positivity
      have hws := sum_weighted_le_eta 𝒯M w (fun τ => (ys τ, is τ))
        (fun p : CTorus d L N₁ m₁ (k + 1) × Fin N => ‖g p.1 p.2‖) (fun p => norm_nonneg _)
        (η := η) (by rw [Fintype.sum_prod_type]; exact hg.2) hρM0 hρM
      calc ∑ τ ∈ 𝒯M, (if Y ∈ polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ) then
            ‖g (ys τ) (is τ)‖ * (1 * ((EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ)
              (XM τ) - 2 * κdec * treeLenCov Gp m₀ Y)) / r)) else 0)
          ≤ ∑ τ ∈ 𝒯M, (‖g (ys τ) (is τ)‖ * w τ) *
              (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) := by
            refine Finset.sum_le_sum fun τ hτ => ?_
            split_ifs
            · refine le_of_eq ?_
              simp only [hw, one_mul]
              rw [sub_eq_add_neg, show -κ₀ * treeLenCovOne m₀ (jM τ) (XM τ) +
                -(2 * κdec * treeLenCov Gp m₀ Y) = -κ₀ * treeLenCovOne m₀ (jM τ) (XM τ) +
                (-2 * κdec * treeLenCov Gp m₀ Y) by ring, Real.exp_add]
              ring
            · exact mul_nonneg (mul_nonneg (norm_nonneg _) (hw0 τ hτ)) hq
        _ = (∑ τ ∈ 𝒯M, ‖g (ys τ) (is τ)‖ * w τ) *
              (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) := by rw [Finset.sum_mul]
        _ ≤ (η * ρM) * (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) :=
            mul_le_mul_of_nonneg_right hws hq
        _ ≤ (η * ρM) * (Real.exp (-(2 * κdec - 1) * treeLenCov Gp m₀ Y) / r) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hη0.le hρM0)
            exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) hr.le
        _ = _ := by ring)
  have hLM' := hLM.congr_val (val' := fun x w σ p => ∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
      p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
        (flComp (hBM τ h) (hFM τ h) (EM τ))) (fun _ => (1 : ℂ)) x w σ p.1 else 0)
    (fun xw _ σ _ p _ => Finset.sum_congr rfl fun τ hτ => by simp [hτ])
  exact ⟨_, hLM'⟩

/-- **Proposition 3.3 in the variable `ψ̂`, without the mass variation** (the hat version of
`interaction_expansion_bound`). -/
theorem interaction_expansion_hat_bound_eta {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (cβ : ℂ)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    -- the hat variable
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    -- the potential part
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hreal : ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D' →
      ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' le_rfl (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup Gp (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin Gp (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    -- the old terms
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N Gp (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N Gp (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup Gp (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    -- the sites of the source
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup Gp (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    -- the observable terms
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N Gp (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N Gp (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup Gp (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    -- the sizes of the old terms and of the observable terms (the source bounds of (3.2)-(3.4)):
    -- the bounds of the terms rooted at one site (resp. at one source site) add up to `ρ`
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM) :
    ∃ (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : Set (CTorus d L N₁ m₁ (k + 1)) →
        ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) →
        ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) → ℂ →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1BallEta d L N₁ m₁ (k + 1) N η)
        {xw : ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) ×
            ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) |
          (xw.1.1, xw.2.1) ∈ HatRaysO Gp cψ R₁ Rσ r ∧ (xw.1.2, xw.2.2) ∈ HatRaysO Gp cψ R₁ Rσ r}
        Rσ 𝒴 T
        (fun x w σ p =>
          (-cβ) * raySrc3 (hatFun Gp a₁ ν eps hG' cc (interactionOne hG hG' le_rfl a₁ ν eps))
            taylorWeight x.1 w.1 σ p.1 +
          cβ * (∑ τ ∈ 𝒯E, if h : τ ∈ 𝒯E then
            dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hBE τ h) (hFE τ h) (EE τ)))
              (fun _ => (1 : ℂ)) x.1 w.1 σ p.1 else 0) +
          cβ * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
            dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
              (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ p.1) +
          cβ * (∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
            p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
              (flComp (hBM τ h) (hFM τ h) (EM τ))) (fun _ => (1 : ℂ)) x.2 w.2 σ p.1 else 0))
        (fun Y => prop33EpsEta d L N m₁ k m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM η * ‖cβ‖ *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (fun Y a a' => AgHatF Gp hG' Y a.1 a'.1 ∧ AgHatF Gp hG' Y a.2 a'.2) := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hK2 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hr3 : 0 < r ^ 3 := by positivity
  have hM0 : 0 ≤ ((L : ℝ) ^ (m₀ + m₁)) ^ d := by positivity
  have hP0 : 0 ≤ ((L : ℝ) ^ (k + 1)) ^ d := by positivity
  obtain ⟨TV, hV⟩ := hat_vpart_bound hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hk hG hG' cc hcψ hMX hdm
    hα hsmX hδ₁ ha₁ H hc7 hR hRs hsmall hnum hnum' hreal hcovV hX₁V hoptV hΔV hlogV hZV hmarV
    (Rσ := Rσ)
  obtain ⟨TE, hE⟩ := hat_eparts_bound hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hk hG hG' cc hcψ hMX
    hdm hα hsmX hδ₁ 𝒯E hBE hFE hcovE hX₁E hoptE hlogE hEbE hEanE hEbdE rE hrE hρE0 hρE
    (Rσ := Rσ)
  obtain ⟨TF, hF⟩ := hat_fparts_bound_eta hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hη0 hη1 hk hG hG' cc hcψ hMX
    hdm hα hsmX hδ₁ hcovF hX₁F hoptF hΔF hlogF hyF (Rσ := Rσ)
  obtain ⟨TM, hM⟩ := hat_mparts_bound_eta hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hη0 hη1 hk hG hG' cc hcψ hMX
    hdm hα hsmX hδ₁ 𝒯M ys is hys hBM hFM hcovM hX₁M hoptM hlogM hEbM hEanM hEbdM hρM0 hρM
    (Rσ := Rσ)
  have hnV : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), 0 ≤ (3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
      ‖energyBd d L N (compWeight L a₁) ν k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / r ^ 3) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := fun Y => by positivity
  have hnE : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), 0 ≤ (ρE * c1 d L * ((L : ℝ) ^ (k + 1)) ^ d *
      ((L : ℝ) ^ (m₀ + m₁)) ^ d / r) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := fun Y => by positivity
  have hnF : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), 0 ≤ (η * (cK2' d L N (famConst d L BG₂ κ) * δ₁) / r) *
      Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := fun Y => by positivity
  have hnM : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), 0 ≤ (η * ρM / r) *
      Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := fun Y => by positivity
  obtain ⟨𝒴, T, b, hb, hL0'⟩ := locInt_assemble
    (AgΘ := fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
    (AgG := fun Y (g g' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) => ∀ x ∈ Y, g x = g' x)
    hV hE hF hM (-cβ) cβ cβ cβ hnV hnE hnF hnM
  refine ⟨𝒴, T, (hL0'.mono_XW (XW' := {xw : ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) ×
            ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) |
          (xw.1.1, xw.2.1) ∈ HatRaysO Gp cψ R₁ Rσ r ∧ (xw.1.2, xw.2.2) ∈ HatRaysO Gp cψ R₁ Rσ r})
    (fun xw h => ⟨h.1, h.1, h.2, h.2⟩)).mono fun Y => (hb Y).trans (le_of_eq ?_)⟩
  simp only [norm_neg, prop33EpsEta]
  ring

end Balaban.Localization
