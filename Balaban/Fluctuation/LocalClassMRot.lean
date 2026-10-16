/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassRot
public import Balaban.Fluctuation.LocalClassM
public import Balaban.Green.FinalConnectedSupport

/-!
# Rotation covariance of the source terms `ℳ` on the local chart (clause `rotM`)

The coefficient `coef f C` of the localization expansion is linear in `f` for functions analytic on
a polydisc of radius `R > 1` (`coef_sum_linear`): by Möbius inversion of
`f (1_A) = ∑_{B ⊆ A} coef f B` (`sum_powerset_coef`).  Hence the term `evTerm` is linear in the
function expanded (`evTerm_sum_linear`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban.Analysis Balaban.Green Finset

section CoefLinear

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- **The expansion at a vertex of the cube**: for `f` analytic on the polydisc of radius
`R > 1`, `f (1_A) = ∑_{B ⊆ A} coef f B`, where `1_A` is the indicator of `A`. -/
theorem sum_powerset_coef {R : ℝ} (hR : 1 < R) {f : (ι → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => R))) (A : Finset ι) :
    f (fun i => if i ∈ A then 1 else 0) = ∑ B ∈ A.powerset, coef f B := by
  classical
  have hR0 : 0 < R := by linarith
  have hA := analyticOnNhd_comp_proj hf A hR0
  have h1 := sum_coef_eq hR hA
  have h1' : f (fun i => if i ∈ A then 1 else 0) =
      ∑ C : Finset ι, coef (fun s : ι → ℂ => f (fun i => if i ∈ A then s i else 0)) C := h1
  rw [h1']
  have hz : ∀ C ∈ (Finset.univ : Finset (Finset ι)), C ∉ A.powerset →
      coef (fun s : ι → ℂ => f (fun i => if i ∈ A then s i else 0)) C = 0 := by
    intro C _ hC
    rw [Finset.mem_powerset] at hC
    obtain ⟨i₀, hi₀C, hi₀A⟩ := Finset.not_subset.1 hC
    refine coef_eq_zero_of_inv hi₀C ?_
    intro w _ τ
    dsimp only
    congr 1
    funext i
    by_cases hi : i ∈ A
    · have : i ≠ i₀ := fun h => hi₀A (h ▸ hi)
      simp [hi, Pi.single_eq_of_ne this]
    · simp [hi]
  calc ∑ C : Finset ι, coef (fun s : ι → ℂ => f (fun i => if i ∈ A then s i else 0)) C
      = ∑ C ∈ A.powerset, coef (fun s : ι → ℂ => f (fun i => if i ∈ A then s i else 0)) C :=
        (Finset.sum_subset (Finset.subset_univ _) hz).symm
    _ = ∑ B ∈ A.powerset, coef f B := by
        refine Finset.sum_congr rfl fun C hC => coef_congr fun w hw => ?_
        rw [Finset.mem_powerset] at hC
        congr 1
        funext i
        by_cases hi : i ∈ A
        · simp [hi]
        · simp [hi, hw i (fun hiC => hi (hC hiC))]

/-- **The coefficient `coef` is linear** on functions analytic on the polydisc of radius `R > 1`. -/
theorem coef_sum_linear {R : ℝ} (hR : 1 < R) {J : Type*} (𝒥 : Finset J) (a : J → ℂ)
    (f : J → (ι → ℂ) → ℂ)
    (hf : ∀ j ∈ 𝒥, AnalyticOnNhd ℂ (f j) (polydisc (0 : ι → ℂ) (fun _ => R))) (C : Finset ι) :
    coef (fun s => ∑ j ∈ 𝒥, a j * f j s) C = ∑ j ∈ 𝒥, a j * coef (f j) C := by
  classical
  have hg : AnalyticOnNhd ℂ (fun s => ∑ j ∈ 𝒥, a j * f j s)
      (polydisc (0 : ι → ℂ) (fun _ => R)) := fun s hs =>
    Finset.analyticAt_fun_sum _ fun j hj => analyticAt_const.mul (hf j hj s hs)
  induction C using Finset.strongInduction with
  | H C ih =>
    have hCmem : C ∈ C.powerset := Finset.mem_powerset.2 (Finset.Subset.refl C)
    have e0 := sum_powerset_coef hR hg C
    have e1 : ∀ j ∈ 𝒥, f j (fun i => if i ∈ C then 1 else 0) = ∑ B ∈ C.powerset, coef (f j) B :=
      fun j hj => sum_powerset_coef hR (hf j hj) C
    rw [← Finset.add_sum_erase _ _ hCmem] at e0
    have e2 : ∑ j ∈ 𝒥, a j * f j (fun i => if i ∈ C then 1 else 0) =
        ∑ j ∈ 𝒥, a j * (coef (f j) C + ∑ B ∈ C.powerset.erase C, coef (f j) B) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [e1 j hj, ← Finset.add_sum_erase _ _ hCmem]
    have e3 : ∑ B ∈ C.powerset.erase C, coef (fun s => ∑ j ∈ 𝒥, a j * f j s) B =
        ∑ j ∈ 𝒥, a j * ∑ B ∈ C.powerset.erase C, coef (f j) B := by
      rw [Finset.sum_congr rfl (fun B hB => ih B (Finset.ssubset_iff_subset_ne.2 ⟨Finset.mem_powerset.1
        (Finset.mem_of_mem_erase hB), Finset.ne_of_mem_erase hB⟩)), Finset.sum_comm]
      simp only [Finset.mul_sum]
    have e4 : ∑ j ∈ 𝒥, a j * f j (fun i => if i ∈ C then 1 else 0) =
        (fun s => ∑ j ∈ 𝒥, a j * f j s) (fun i => if i ∈ C then 1 else 0) := rfl
    have := e0.symm.trans (e4.symm.trans e2)
    simp only [mul_add, Finset.sum_add_distrib] at this
    rw [e3] at this
    exact add_right_cancel this

end CoefLinear

section EvLinear

open Balaban Balaban.Multiscale

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (c : ι → ℕ × CTorus d L N₁ m₁ K)

/-- **The term `𝓔(X, Y)` is linear in the function expanded**, for functions analytic on the
polydisc of radius `R > 1` at the argument `u`. -/
theorem evTerm_sum_linear {U J : Type*} {R : ℝ} (hR : 1 < R) (𝒥 : Finset J) (a : J → ℂ)
    (X₁ Y : Set (CTorus d L N₁ m₁ K)) (F : J → U → (ι → ℂ) → ℂ) (u : U)
    (hF : ∀ j ∈ 𝒥, AnalyticOnNhd ℂ (F j u) (polydisc (0 : ι → ℂ) (fun _ => R))) :
    evTerm c G m₀ X₁ (fun u' s => ∑ j ∈ 𝒥, a j * F j u' s) Y u =
      ∑ j ∈ 𝒥, a j * evTerm c G m₀ X₁ (F j) Y u := by
  unfold evTerm
  rw [Finset.sum_congr rfl (fun C _ => coef_sum_linear hR 𝒥 a (fun j => F j u) hF C),
    Finset.sum_comm]
  simp only [Finset.mul_sum]

end EvLinear



section ParamMRot

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Finset Matrix MeasureTheory


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
/-- **The integrand of the `ψ̂`-integral of the source term is integrable**: at a datum `Θ` of the
chart, a source `g` of the parameter set and a parameter `w` of the polydisc, the function
`ψ̂ ↦ Φ_{E(·, g)}(F₁(σ w, Θ), Sol(σ w, …), (Θ, cc C^{1/2}(σ w) ψ̂))` is integrable over the compact
set `K` for the measure `γ` (it is continuous there, being the restriction of the analytic map of
`localB_mTermHat_integral_param`, and bounded). -/
theorem localB_mTermHat_integrand_integrableOn {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] [FiniteDimensional ℂ G] {Sg : Set G}
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → G → ℂ}
    (hE : AnalyticOnNhd ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × G => E q.1 q.2)
      (XiCRaw Gj (compWeight L a₁) ν j b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ×ˢ Sg))
    {Bd : ℝ} (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ∀ g ∈ Sg, ‖E r g‖ ≤ Bd)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps) {g : G} (hg : g ∈ Sg) {w : ι → ℂ}
    (hw : w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) :
    IntegrableOn (fun ψ : unitPts 𝔹ₗ × Fin N → ℝ =>
          eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk (fun r => E r g) (F₁ (σ w, Θ))
        (Sol (σ w, flEdat 𝔹ₗ Hm (F₁ (σ w, Θ)) Θ.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, Θ)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ Θ.1 (F₁ (σ w, Θ)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, Θ)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ Θ.1 (F₁ (σ w, Θ)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0)) K γ := by
  classical
  have hcd := localB_coverData ht Yp hN₁ hMM hag HBp
  have ha₁0 : 0 < a₁ := by linarith
  have hfdT := finDim_triple (N := N) 𝔹ₗ Hm
  have hfdR := finDim_rawData (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N)
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
  set Ψ : (unitPts 𝔹ₗ × Fin N → ℂ) → ℂ := fun v => E (Cmap (Tmap ((Θ, v), w))) g with hΨ
  have hmemT : ∀ v : unitPts 𝔹ₗ × Fin N → ℂ, (∀ r, ‖v r‖ ≤ cψ) →
      ((Θ, v), w) ∈ (XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts 𝔹ₗ × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ) := fun v hv => ⟨⟨hΘ, hv⟩, hw⟩
  have hΨan : ∀ v : unitPts 𝔹ₗ × Fin N → ℂ, (∀ r, ‖v r‖ ≤ cψ) → AnalyticAt ℂ Ψ v := by
    intro v hv
    have hρ : AnalyticAt ℂ (fun v : unitPts 𝔹ₗ × Fin N → ℂ => ((Θ, v), w)) v :=
      (analyticAt_const.prod analyticAt_id).prod analyticAt_const
    have h1 := hT.1 _ (hmemT v hv)
    have h2 := hC.1 _ (hT.2 _ (hmemT v hv))
    have h3 : AnalyticAt ℂ (fun z : RawData d L (N₁ * L ^ m₁) (k + 1) N × G => E z.1 z.2)
        (Cmap (Tmap ((Θ, v), w)), g) := hE _ ⟨hC.2 _ (hT.2 _ (hmemT v hv)), hg⟩
    exact h3.comp_of_eq ((h2.comp_of_eq (h1.comp_of_eq hρ rfl) rfl).prod analyticAt_const) rfl
  have hcast : Continuous (fun ψ : unitPts 𝔹ₗ × Fin N → ℝ => (fun r => (ψ r : ℂ) :
      unitPts 𝔹ₗ × Fin N → ℂ)) := by fun_prop
  have hv : ∀ ψ ∈ K, ∀ r, ‖((fun r => (ψ r : ℂ)) : unitPts 𝔹ₗ × Fin N → ℂ) r‖ ≤ cψ :=
    fun ψ hψ r => by simpa [Complex.norm_real] using hKb ψ hψ r
  have heq : (fun ψ : unitPts 𝔹ₗ × Fin N → ℝ => eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk
      (fun r => E r g) (F₁ (σ w, Θ))
        (Sol (σ w, flEdat 𝔹ₗ Hm (F₁ (σ w, Θ)) Θ.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, Θ)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ Θ.1 (F₁ (σ w, Θ)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, Θ)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ Θ.1 (F₁ (σ w, Θ)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0)) = fun ψ => Ψ (fun r => (ψ r : ℂ)) := by
    funext ψ
    simp only [hΨ, hTmap, hCmap, eTermFun]
  rw [heq]
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have : IsFiniteMeasure (γ.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hγ⟩
  have hcont : ContinuousOn (fun ψ : unitPts 𝔹ₗ × Fin N → ℝ => Ψ (fun r => (ψ r : ℂ))) K :=
    fun ψ hψ => ContinuousAt.continuousWithinAt (ContinuousAt.comp (g := Ψ)
      (f := fun ψ : unitPts 𝔹ₗ × Fin N → ℝ => (fun r => (ψ r : ℂ) : unitPts 𝔹ₗ × Fin N → ℂ))
      (hΨan _ (hv ψ hψ)).continuousAt hcast.continuousAt)
  refine Integrable.of_bound (C := Bd) (hcont.aestronglyMeasurable hKm) ?_
  refine (ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun ψ hψ => ?_)
  exact hEb _ (hC.2 _ (hT.2 _ (hmemT _ (hv ψ hψ)))) g hg


/-- **The clause `rotM` of the successor class for the source terms recomputed on
`𝔹 = localB t … Y⁺`, real rotations.**  For a real orthogonal `Q` and a source `g` of the
parameter set, let the old source terms `E i (r, g)` (`i ∈ Fin N`, the components of
`ℳ^{(j)}(x, X; r.1, r.2, g)` on the chart of `𝔹_j(X)`) be analytic and bounded in `(r, g)` and
covariant, `E i (R r, R g) = ∑ l, R i l * E l (r, g)` on the chart (`hEr`).  Then the term of `Y`
(coefficients, over the connected families of the ambient expansion, of the `ψ̂`-integrated local
source term read through the cut-off `clipRaw 𝔹`) transforms as a vector:
the `i`-th component at `(Q Ψ, Q h, Q g)` is `∑ l, Q i l` times the `l`-th component at `(Ψ, h, g)`,
on the class domain.  The compact set `K` and the measure `γ` are invariant under `ψ̂ ↦ (1 ⊗ Qᵀ) ψ̂`
(`hKQ`, `hγQ`).  Proof: `localHat_integral_rot_cover_of_cov` with the two functionals
`E i (·, R g)` and `∑ l, R i l * E l (·, g)`, the linearity of the integral (the integrands are
integrable: `localB_mTermHat_integrand_integrableOn`) and of the coefficients
(`evTerm_sum_linear`). -/
theorem localB_mTermHat_evTerm_rot {ϱa : ℝ} {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa}
    {cI : ι → ℕ × CTorus d L N₁ m₁ (k + 1)} {m₀ j' : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    {εseq : ℕ → ℝ} (hεseq : εseq (k + 1) ≤ eps)
    {Sg : Set (Fld d L N₁ m₁ (k + 1) N)}
    (E : Fin N → RawData d L (N₁ * L ^ m₁) (k + 1) N → Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hE : ∀ l, AnalyticOnNhd ℂ
      (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × Fld d L N₁ m₁ (k + 1) N => E l q.1 q.2)
      (XiCRaw Gj (compWeight L a₁) ν j b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ×ˢ Sg))
    {Bd : ℝ} (hEb : ∀ l, ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ∀ g ∈ Sg, ‖E l r g‖ ≤ Bd)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {g : Fld d L N₁ m₁ (k + 1) N} (hg : g ∈ Sg)
    (hEr : ∀ i, ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      E i (rotRaw (cmat Q) r) (rotField (cmat Q) g) = ∑ l, cmat Q i l * E l r g)
    (hKQ : ∀ ψ : unitPts 𝔹ₗ × Fin N → ℝ,
      (fun r : unitPts 𝔹ₗ × Fin N => ∑ j, Q j r.2 * ψ (r.1, j)) ∈ K ↔ ψ ∈ K)
    (hγQ : Measure.map (fun (ψ : unitPts 𝔹ₗ × Fin N → ℝ) (r : unitPts 𝔹ₗ × Fin N) =>
      ∑ j, Q j r.2 * ψ (r.1, j)) γ = γ)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (Fi : Fin N → RawData d L (N₁ * L ^ m₁) (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      (ι → ℂ) → ℂ)
    (hFi : ∀ l u w, Fi l u w =
        ∫ ψ in K,
          eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk (fun r => E l r u.2) (F₁ (σ w, u.1))
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
    (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hp : (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1 p.2) (i : Fin N) :
    evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) (Fi i) Y
        (clipRaw 𝔹ₗ (rotField (cmat Q) p.1, rotField (cmat Q) p.2), rotField (cmat Q) g) =
      ∑ l, cmat Q i l * evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) (Fi l) Y (clipRaw 𝔹ₗ p, g) := by
  classical
  have hcd := localB_coverData ht Yp hN₁ hMM hag HBp
  have ha₁0 : 0 < a₁ := by linarith
  have hp' : XiDom 𝔹ₗ (compWeight L a₁) ν (k + 1) (εseq (k + 1)) p.1 p.2 := hp
  have hmem : clipRaw 𝔹ₗ p ∈ XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps :=
    clipRaw_mem_xiCRaw_of_xiDom hεseq hp'
  -- the two functionals
  have hΦ : ∀ (bg : ((𝔹ₗ).Ω 1 × Fin N → ℂ) × ((𝔹ₗ).Ω 1 → ℂ)) δφ u,
      (bg, δφ, u) ∈ FlRealLC 𝔹ₗ Hm a₁ ν BG κ eps X₁f BG₂ δ₁ →
      ((rotFld (cmat Q) bg.1, bg.2), rotFld (cmat Q) δφ, rotU (cmat Q) u) ∈
        FlRealLC 𝔹ₗ Hm a₁ ν BG κ eps X₁f BG₂ δ₁ →
      eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk (fun r => E i r (rotField (cmat Q) g))
        (rotFld (cmat Q) bg.1, bg.2) (rotFld (cmat Q) δφ) (rotU (cmat Q) u) =
      eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk (fun r => ∑ l, cmat Q i l * E l r g)
        bg δφ u := fun bg δφ u h1 h2 =>
    eTermFun_rot_cover_of_cov (Gp := 𝔹ₗ) hb₁ hbC hS hcd.1 hcd.2.1 hcd.2.2.1 hMM ha₁0 HBp HBk HBj
      hP hq colk colj hκ hM hnum dsX₀ hN hcd.2.2.2.1 hcd.2.2.2.2 hj hF hFk hQ
      (E₁ := fun r => E i r (rotField (cmat Q) g)) (E₂ := fun r => ∑ l, cmat Q i l * E l r g)
      (fun r hr => hEr i r hr) (t := (bg, δφ, u)) h1 h2
  have hA : ∀ l, AnalyticOnNhd ℂ (fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      Fld d L N₁ m₁ (k + 1) N) × (ι → ℂ) => Fi l q.1 q.2)
      ((XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps ×ˢ Sg) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) := fun l =>
    (localB_mTermHat_integral_param hb₁ hbC ht Yp hN₁ hMM hag hS hk1 ha₁ ha₂ HBp HBk
      HBj hP hq colk colj hκ hM hMX hnum dsX₀ hN hj hF hHm hFkan hFk hmarD hαD hsm cc hcψ hδ₁
      hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hKc hKb hγ (hE l) (Bd := Bd) (hEb l)
      (fun q => Fi l q.1 q.2) (fun q => hFi l q.1 q.2)).1
  have hlin : evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X)
      (fun (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ) =>
        ∑ l, cmat Q i l * Fi l (Θ, g) w) Y (clipRaw 𝔹ₗ p) =
      ∑ l, cmat Q i l * evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) (Fi l) Y (clipRaw 𝔹ₗ p, g) := by
    rw [evTerm_sum_linear (c := cI) (G := Ga) (m₀ := m₀) (Real.one_lt_exp_iff.2 hκ) Finset.univ
      (fun l => cmat Q i l) (X1 Ga m₀ j' 𝒦X) Y
      (fun l (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) => Fi l (Θ, g)) (clipRaw 𝔹ₗ p)
      (fun l _ w hw => ?_)]
    · exact Finset.sum_congr rfl fun l _ => by
        rw [evTerm_congr_fun (c := cI) (G := Ga) (m₀ := m₀) (X₁ := X1 Ga m₀ j' 𝒦X)
          (F := fun (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) => Fi l (Θ, g)) (F' := Fi l)
          (u := clipRaw 𝔹ₗ p) (u' := (clipRaw 𝔹ₗ p, g)) rfl]
    · have h1 := hA l ((clipRaw 𝔹ₗ p, g), w) ⟨⟨hmem, hg⟩, hw⟩
      exact h1.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have key := evTerm_clipRaw_rot_of_cov (G := 𝔹ₗ) (c := cI) (Ga := Ga) (m₀ := m₀)
    (X₁ := X1 Ga m₀ j' 𝒦X) Y (Real.one_lt_exp_iff.2 hκ) (a := compWeight L a₁) (ν := ν)
    (eps := eps) (j := k + 1) (εj := εseq (k + 1)) hεseq (Q := Q)
    (Gf₁ := fun (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ) =>
      Fi i (Θ, rotField (cmat Q) g) w)
    (Gf₂ := fun (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ) =>
      ∑ l, cmat Q i l * Fi l (Θ, g) w) (p := p) ?_ hp'
  · calc evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) (Fi i) Y
          (clipRaw 𝔹ₗ (rotField (cmat Q) p.1, rotField (cmat Q) p.2), rotField (cmat Q) g)
        = evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X)
            (fun (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ) =>
              Fi i (Θ, rotField (cmat Q) g) w) Y
            (clipRaw 𝔹ₗ (rotField (cmat Q) p.1, rotField (cmat Q) p.2)) :=
          evTerm_congr_fun rfl
      _ = _ := key.trans hlin
  · intro D hD w hw
    refine localHat_integral_rot_cover_of_cov (Gp := 𝔹ₗ)
      (Φ₁ := eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk (fun r => E i r (rotField (cmat Q) g)))
      (Φ₂ := eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk (fun r => ∑ l, cmat Q i l * E l r g))
      hk1 ha₁ ha₂ hS hcd.1 HBp hκ hM hMX (Cchi_nonneg d L) hnum.eps_pos hnum.small1 hnum.c7le
      hF.num.phi_lt hmarD hαD hsm cc hcψ hF.num.δ₁_pos hδ₁ hF.hPmp hHm hF₁ hSol hσκ hσ1 hQ hΦ
      hKc hKb hKQ hγQ _ (fun Θ w => hFi i (Θ, rotField (cmat Q) g) w)
      (fun Θ w => ∑ l, cmat Q i l * Fi l (Θ, g) w) ?_ hD hw
    intro D hD w hw
    have hint : ∀ l, IntegrableOn (fun ψ : unitPts 𝔹ₗ × Fin N → ℝ =>
          eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk (fun r => E l r g) (F₁ (σ w, rawOf D))
        (Sol (σ w, flEdat 𝔹ₗ Hm (F₁ (σ w, rawOf D)) (rawOf D).1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, rawOf D)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ (rawOf D).1 (F₁ (σ w, rawOf D)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (rawOf D, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, rawOf D)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ (rawOf D).1 (F₁ (σ w, rawOf D)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0)) K γ := fun l =>
      localB_mTermHat_integrand_integrableOn hb₁ hbC ht Yp hN₁ hMM hag hS hk1 ha₁ ha₂ HBp HBk
        HBj hP hq colk colj hκ hM hMX hnum dsX₀ hN hj hF hHm hFkan hFk hmarD hαD hsm cc hcψ hδ₁
        hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hKc hKb hγ (hE l) (hEb l) ⟨D, hD, rfl⟩ hg hw
    obtain ⟨I, hI⟩ : ∃ I : Fin N → (unitPts 𝔹ₗ × Fin N → ℝ) → ℂ, ∀ l ψ, I l ψ =
        eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk (fun r => E l r g) (F₁ (σ w, rawOf D))
        (Sol (σ w, flEdat 𝔹ₗ Hm (F₁ (σ w, rawOf D)) (rawOf D).1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, rawOf D)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ (rawOf D).1 (F₁ (σ w, rawOf D)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (rawOf D, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, rawOf D)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ (rawOf D).1 (F₁ (σ w, rawOf D)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) := ⟨_, fun _ _ => rfl⟩
    have hint' : ∀ l, IntegrableOn (I l) K γ := fun l => by
      have : I l = _ := funext (hI l)
      rw [this]; exact hint l
    calc ∑ l, cmat Q i l * Fi l (rawOf D, g) w
        = ∑ l, cmat Q i l * ∫ ψ in K, I l ψ ∂γ :=
          Finset.sum_congr rfl fun l _ => by rw [hFi l (rawOf D, g) w]; simp only [hI]
      _ = ∫ ψ in K, ∑ l, cmat Q i l * I l ψ ∂γ := by
          rw [integral_finsetSum _ (fun l _ => (hint' l).const_mul (cmat Q i l))]
          exact Finset.sum_congr rfl fun l _ => (integral_const_mul _ _).symm
      _ = _ := by
          refine setIntegral_congr_fun hKc.isClosed.measurableSet fun ψ _ => ?_
          simp only [hI]
          rfl

end ParamMRot

section FreshAmp

open Matrix Balaban.Background

variable {N : ℕ}

/-- The sources enter the fresh term only through the amplitude `g(y, i)`. -/
theorem fresh_amp_rot_pair {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {τ : Fin N → ℂ}
    (g : Fin N → ℂ) :
    ∑ i, (cmat Q).mulVec g i * ∑ l, cmat Q i l * τ l = ∑ l, g l * τ l := by
  have hR : (cmat Q)ᵀ * cmat Q = 1 := (isRealOrth_ofReal hQ).1
  have h1 : ∀ i, (cmat Q).mulVec g i * ∑ l, cmat Q i l * τ l =
      ∑ l, ∑ j, (cmat Q i j * cmat Q i l) * (g j * τ l) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ l, ∑ i, ∑ j, (cmat Q i j * cmat Q i l) * (g j * τ l) = g l * τ l := by
    intro l
    rw [Finset.sum_comm]
    have : ∀ j, ∑ i, (cmat Q i j * cmat Q i l) * (g j * τ l) =
        (if j = l then 1 else 0) * (g j * τ l) := by
      intro j
      rw [← Finset.sum_mul]
      congr 1
      have := congrFun (congrFun hR j) l
      simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using this
    rw [Finset.sum_congr rfl (fun j _ => this j)]
    simp
  exact Finset.sum_congr rfl fun l _ => h2 l

end FreshAmp

section Fresh

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset Matrix MeasureTheory

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ} {ι : Type*} [Fintype ι]
variable (hk1 : 1 ≤ k) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hPmp : Precedes Hm Gp) (hHm : Hm.Ω (k + 1) = ∅)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gp N,
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf Gp)} (hσan : ∀ w, AnalyticAt ℂ σ w)
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → σ w ⟨P, hP⟩ = 1)
  {γ : Measure (unitPts Gp × Fin N → ℝ)} {K : Set (unitPts Gp × Fin N → ℝ)}
  (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ) (hγ : γ K < ⊤)

include hk1 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7 hphi hmarD hαD hsm hcψ hδ₁0 hδ₁ hPmp
  hHm hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hKc hKb hγ

/-- **The integrand of the `ψ̂`-integral of a local fan term is integrable**: for `Φ` analytic and
bounded on the realizable triples with layer-constant fluctuation, at a datum `Θ` of the chart and a
parameter `w` of the polydisc, `ψ̂ ↦ Φ(F₁(σ w, Θ), Sol(σ w, …), (Θ, cc C^{1/2}(σ w) ψ̂))` is
integrable over the compact set `K` (continuous there and bounded). -/
theorem fanLocalHat_integrableOn_cover
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    {B : ℝ} (hΦbd : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁, ‖Φ t.1 t.2.1 t.2.2‖ ≤ B)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) {w : ι → ℂ}
    (hw : w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) :
    IntegrableOn (fun ψ : unitPts Gp × Fin N → ℝ =>
        Φ (F₁ (σ w, Θ))
          (Sol (σ w, flEdat Gp Hm (F₁ (σ w, Θ)) Θ.1
            (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                  (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0))).1
          (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                  (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0)) K γ := by
  classical
  have hA := fanLocalHat_analytic_cover hk1 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7
    hphi hmarD hαD hsm cc hcψ hδ₁0 hδ₁ hPmp hHm hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hΦ
  have hB := fanLocalHat_norm_le_cover hk1 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7
    hphi hmarD hαD hsm cc hcψ hδ₁0 hδ₁ hPmp hHm hF₁ hSol hσκ hσ1 hΦbd
  have hv : ∀ ψ ∈ K, ∀ r, ‖((fun r => (ψ r : ℂ)) : unitPts Gp × Fin N → ℂ) r‖ ≤ cψ :=
    fun ψ hψ r => by simpa [Complex.norm_real] using hKb ψ hψ r
  have hcast : Continuous (fun ψ : unitPts Gp × Fin N → ℝ => (fun r => (ψ r : ℂ) :
      unitPts Gp × Fin N → ℂ)) := by fun_prop
  set Ψ : (unitPts Gp × Fin N → ℂ) → ℂ := fun v =>
    Φ (F₁ (σ w, Θ))
          (Sol (σ w, flEdat Gp Hm (F₁ (σ w, Θ)) Θ.1
            (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                  (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ v)) (⟨unitBlock x, h⟩, i)
              else 0))).1
          (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                  (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ v)) (⟨unitBlock x, h⟩, i)
              else 0) with hΨ
  have hmemT : ∀ v : unitPts Gp × Fin N → ℂ, (∀ r, ‖v r‖ ≤ cψ) →
      ((Θ, v), w) ∈ (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ) := fun v hv => ⟨⟨hΘ, hv⟩, hw⟩
  have hΨan : ∀ v : unitPts Gp × Fin N → ℂ, (∀ r, ‖v r‖ ≤ cψ) → AnalyticAt ℂ Ψ v := by
    intro v hv
    have hρ : AnalyticAt ℂ (fun v : unitPts Gp × Fin N → ℂ => ((Θ, v), w)) v :=
      (analyticAt_const.prod analyticAt_id).prod analyticAt_const
    exact (hA _ (hmemT v hv)).comp_of_eq hρ rfl
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have : IsFiniteMeasure (γ.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hγ⟩
  have hcont : ContinuousOn (fun ψ : unitPts Gp × Fin N → ℝ => Ψ (fun r => (ψ r : ℂ))) K :=
    fun ψ hψ => ContinuousAt.continuousWithinAt (ContinuousAt.comp (g := Ψ)
      (f := fun ψ : unitPts Gp × Fin N → ℝ => (fun r => (ψ r : ℂ) : unitPts Gp × Fin N → ℂ))
      (hΨan _ (hv ψ hψ)).continuousAt hcast.continuousAt)
  refine Integrable.of_bound (C := B) (hcont.aestronglyMeasurable hKm) ?_
  refine (ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun ψ hψ => ?_)
  exact hB _ (hmemT _ (hv ψ hψ))



/-- **The fresh source term `⟨g, δφ⟩` on the local chart: analyticity and the bound of the term of
`Y` for the site `y`, component `i`** (P3 (4.46), `fsite_expansion` recomputed on `𝔹`).  The
function expanded is `G_{y,i}(Θ, w) = ∫_K δφ(F₁(σ w, Θ), …)(y, i) dγ(ψ̂)`, the `ψ̂`-integral of the
site functional `siteFun` of the local fluctuation field; the source `g` enters the fresh term only
through the amplitude `g(y, i)`.  The term of `Y` read through the cut-off `clipRaw` is analytic in
the pair of fields on the class domain and bounded there by
`(cK2' δ₁) γ(K) e^{-2 κ_dec d̃^cov(Y)}`, for a root family with `treeLenCovOne = 0`
(the fresh term has no old polymer). -/
theorem localB_freshTermHat_evTerm_xiFieldDom [DecidableEq ι] {ϱa : ℝ}
    {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa} {cI : ι → ℕ × CTorus d L N₁ m₁ (k + 1)}
    {m₀ j' : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup Ga m₀ j' X 𝒦X) (hd : 3 ≤ d) (hL : 3 ≤ L) (hcI : ∀ i, cI i ∈ cubeIdx Ga)
    (hcinj : Function.Injective cI) (hdisj : ∀ i, Disjoint (Pset m₁ (cI i)) (X1 Ga m₀ j' 𝒦X))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j' 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j') E₀ = treeLenCovOne m₀ j' X)
    (hΔ : treeLenCovOne m₀ j' X = 0) (hBG₂ : 0 ≤ BG₂)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    {εseq : ℕ → ℝ} (hεseq : εseq (k + 1) ≤ eps)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    (Gi : RawData d L (N₁ * L ^ m₁) (k + 1) N → (ι → ℂ) → ℂ)
    (hGi : ∀ (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ), Gi Θ w =
      ∫ ψ in K,
        siteFun Gp Hm y i (F₁ (σ w, Θ))
          (Sol (σ w, flEdat Gp Hm (F₁ (σ w, Θ)) Θ.1
            (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                  (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0))).1
          (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                  (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0) ∂γ)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Gi Y (clipRaw Gp p))
      {p | (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) Gp
        p.1 p.2} ∧
    ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) Gp
        p.1 p.2 →
      ‖evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Gi Y (clipRaw Gp p)‖ ≤
        (cK2' d L N (famConst d L BG₂ κ) * δ₁) * (γ K).toReal *
          Real.exp (-2 * κdec * treeLenCov Ga m₀ Y) := by
  classical
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hBG₂ κ hd0; linarith
  have hBnn : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hδ₁0.le
  have hγ0 : 0 ≤ (γ K).toReal := ENNReal.toReal_nonneg
  obtain ⟨hA, hB⟩ := fanLocalHat_integral_cover hk1 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall
    hc7 hphi hmarD hαD hsm cc hcψ hδ₁0 hδ₁ hPmp hHm hF₁an hF₁ hSolan hSol hσan hσκ hσ1
    (Φ := siteFun Gp Hm y i) ((siteFun_analytic (Gp := Gp) (Hm := Hm) y i).mono (Set.subset_univ _))
    (B := cK2' d L N (famConst d L BG₂ κ) * δ₁)
    (fun t ht => by
      obtain ⟨-, hsup, -⟩ := flReal_facts ht.1
      simpa [siteFun] using hsup.val y i) hKc hKb hγ
  have hfun : (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × (ι → ℂ) => Gi q.1 q.2) =
      fun q => ∫ ψ in K,
        siteFun Gp Hm y i (F₁ (σ q.2, q.1))
          (Sol (σ q.2, flEdat Gp Hm (F₁ (σ q.2, q.1)) q.1.1
            (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ q.2, q.1)).2
                  (Dec2.extS (coverOf Gp) (σ q.2)) (barField Gp q.1.1 (F₁ (σ q.2, q.1)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0))).1
          (q.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ q.2, q.1)).2
                  (Dec2.extS (coverOf Gp) (σ q.2)) (barField Gp q.1.1 (F₁ (σ q.2, q.1)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0) ∂γ := by
    funext q
    exact hGi q.1 q.2
  have hEv := evTerm_bound_analyticOnNhd_of_bd (c := cI)
    (U := RawData d L (N₁ * L ^ m₁) (k + 1) N) (F := Gi)
    hcov hd hL hcI hcinj hdisj hopt hκ₀ hκdec hκκ h1 hlog (mul_nonneg hBnn hγ0)
    (S := XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
    (by rw [hfun]; exact hA)
    (fun u hu s hs => by
      have := hB (u, s) ⟨hu, hs⟩
      rw [hGi, hΔ, mul_zero, Real.exp_zero, mul_one]
      exact this)
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · have hmem : clipRaw Gp p ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps :=
      clipRaw_mem_xiCRaw_of_xiDom hεseq hp
    exact (hEv.2 Y (clipRaw Gp p) hmem).comp_of_eq (analyticAt_clipRaw p) rfl
  · have := hEv.1 Y (clipRaw Gp p) (clipRaw_mem_xiCRaw_of_xiDom hεseq hp)
    have e : -κ₀ * treeLenCovOne m₀ j' X - 2 * κdec * treeLenCov Ga m₀ Y =
        -2 * κdec * treeLenCov Ga m₀ Y := by rw [hΔ]; ring
    rw [e] at this
    exact this

end Fresh

end Balaban.Localization
