module

public import Balaban.LargeField.R.SmallFactorAction
public import Balaban.LargeField.R.SmallFactorConsts
public import Balaban.LargeField.R.SmallFactorConsts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The small factor of the outcome `ϰ₁` (Lemma III.5.3 (a))

If `χ̃_k = 0`, i.e. `ψ_k ∉ Ψ̃_k(Z^c_0 ∩ (Ω^c_k)^{∼3}; 3δ_k)`, then
`½ 𝒢^♮ + β_kA^*_k(X_win, 𝔹_k; ψ, φ) ≥ γ₁`,  `γ₁ = 9/8 (1 - η) γ₀ β_kδ_k² - ½`,
for the unit background field `φ`.  By Lemma III.2.2 (2.15′) the left side is
`½ 𝒢^♮ + 𝒜_win + C_{k₁,k}`.  The proof is the one of the source: LF-1 for the single-scale action
on `Z^c_0 ∩ Z` (`single_gradient_bound`, `single_point_bound`), (2.17′) (`composed_dominates`) and
the monotonicity of the action in the domain (`multiAction_mono`, `Z^c_0 ∩ Z ⊂ X_win`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {Nspin : ℕ}

/-- **Lemma III.5.3 (a)–(b), core** (level-torus form).  `Xc` is the fine set `Z^c_0 ∩ Z` (a union of
`k`-blocks in `Ω₁ ∖ Ω_k`), `Xwin ⊇ Xc` the window region; `φ` is a field of unit vectors on `Xc`
(the background field of the generating set, `|φ| = 1` on `Ω₁` by (EL)); `η`, `Σ^♮`, `N`, `M_ψ` are as in
(2.17′) and `8 (Σ^♮)² N M_ψ² ≤ 1` is (Λ19).  If `ψ_k ∉ Ψ̃(blocks ⊂ Xc; θ)` then
`𝒢^♮ + β_kA^*_k(Xwin, 𝔹_k; ψ, φ) ≥ ½(1 - η) · ½ γ₀ β_k θ² - 1`. -/
theorem smallFactor_violation (G : GeneratingSet d L N₀ k ϱ) (hk : 1 ≤ k) (hL : 2 ≤ L)
    (hd : 2 ≤ d) (hϱ : 2 * (d : ℝ) * L ≤ ϱ) {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hadm : IsAdmissibleWeights k (compWeight L a₁)) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {Xc Xwin : Finset (Site d L N₀ k)} (hXc : Xc ⊆ Xwin)
    (hXΩ : ∀ s ∈ Xc, s ∈ G.Ω 1 ∧ s ∉ G.Ω k) (hXk : IsBlockUnion L N₀ k k Xc)
    (hX : ∀ n, 1 ≤ n → n ≤ k → IsBlockUnion L N₀ k n (Xc ∩ G.layer n))
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) (hφ : ∀ x ∈ Xc, ‖φ x‖ = 1)
    {βk : ℝ} (hβ : 0 ≤ βk) (ϖ : ℕ → ℝ) (aN : Blk d L N₀ k k → ℝ) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 2)
    (haN : ∀ z ∈ tBlocks d L N₀ k k Xc, |aN z - compWeightZ G a₁ z| ≤ η * compWeightZ G a₁ z)
    {Mψ Sig Nbl : ℝ} (hM : ∀ s ∈ Xc, ‖leafField G ψ s‖ ≤ Mψ)
    (hSig : ∀ z ∈ tBlocks d L N₀ k k Xc, Real.sqrt βk * varsigmaBar G ϖ z ≤ Sig)
    (hN : ((tBlocks d L N₀ k k Xc).card : ℝ) ≤ Nbl) (hΛ19 : 8 * Sig ^ 2 * Nbl * Mψ ^ 2 ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hviol : ¬ PsiTildeSet {y : Blk d L N₀ k k | fib d L N₀ k k y ⊆ Xc} (ψ k) θ) :
    1 / 2 * (1 - η) * (1 / 2 * gamma0 d * (βk * θ ^ 2)) - 1 ≤
      composedGauss G βk aN ϖ ψ Xc + multiAction G (compWeight L a₁) βk μ h Xwin ψ φ := by
  have ha0 : ∀ n, 0 ≤ compWeight L a₁ n := compWeight_nonneg hL ha₁
  have hsing := single_smallFactor hk hd hL hϱ hadm hμ h hXk ψ φ hφ hβ hθ hviol
  have hdom := composed_dominates G hk hL hd ha₁ hadm hμ h Xc hXΩ hXk hX ψ φ hβ ϖ aN hη0 hη haN hM
    hSig hN
  have hmono := multiAction_mono G ha0 hμ hβ h hXc ψ φ
  have hη1 : 0 ≤ 1 - η := by linarith
  have := mul_le_mul_of_nonneg_left hsing (by positivity : 0 ≤ 1 / 2 * (1 - η))
  linarith

/-- **Lemma III.5.3 (a)** (`ϰ₁`, level-torus form): if `ψ_k ∉ Ψ̃(blocks ⊂ Xc; 3δ_k)` (`χ̃_k = 0`),
then `½ 𝒢^♮ + β_kA^*_k(Xwin, 𝔹_k; ψ, φ) ≥ γ₁ = 9/8 (1 - η) γ₀ β_kδ_k² - ½`, the left side being
`½ 𝒢^♮ + 𝒜_win + C_{k₁,k}` by (2.15′). -/
theorem smallFactor_one (G : GeneratingSet d L N₀ k ϱ) (hk : 1 ≤ k) (hL : 2 ≤ L) (hd : 2 ≤ d)
    (hϱ : 2 * (d : ℝ) * L ≤ ϱ) {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hadm : IsAdmissibleWeights k (compWeight L a₁)) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {Xc Xwin : Finset (Site d L N₀ k)} (hXc : Xc ⊆ Xwin)
    (hXΩ : ∀ s ∈ Xc, s ∈ G.Ω 1 ∧ s ∉ G.Ω k) (hXk : IsBlockUnion L N₀ k k Xc)
    (hX : ∀ n, 1 ≤ n → n ≤ k → IsBlockUnion L N₀ k n (Xc ∩ G.layer n))
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) (hφ : ∀ x ∈ Xc, ‖φ x‖ = 1)
    {βk : ℝ} (hβ : 0 ≤ βk) (ϖ : ℕ → ℝ) (aN : Blk d L N₀ k k → ℝ) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 2)
    (haN : ∀ z ∈ tBlocks d L N₀ k k Xc, |aN z - compWeightZ G a₁ z| ≤ η * compWeightZ G a₁ z)
    {Mψ Sig Nbl : ℝ} (hM : ∀ s ∈ Xc, ‖leafField G ψ s‖ ≤ Mψ)
    (hSig : ∀ z ∈ tBlocks d L N₀ k k Xc, Real.sqrt βk * varsigmaBar G ϖ z ≤ Sig)
    (hN : ((tBlocks d L N₀ k k Xc).card : ℝ) ≤ Nbl) (hΛ19 : 8 * Sig ^ 2 * Nbl * Mψ ^ 2 ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hviol : ¬ PsiTildeSet {y : Blk d L N₀ k k | fib d L N₀ k k y ⊆ Xc} (ψ k) (3 * δ)) :
    9 / 8 * (1 - η) * gamma0 d * (βk * δ ^ 2) - 1 / 2 ≤
      1 / 2 * composedGauss G βk aN ϖ ψ Xc +
        multiAction G (compWeight L a₁) βk μ h Xwin ψ φ := by
  have ha0 : ∀ n, 0 ≤ compWeight L a₁ n := compWeight_nonneg hL ha₁
  have hv := smallFactor_violation G hk hL hd hϱ ha₁ hadm hμ h hXc hXΩ hXk hX ψ φ hφ hβ ϖ aN hη0
    hη haN hM hSig hN hΛ19 (θ := 3 * δ) (by positivity) hviol
  have hnn := multiAction_nonneg G ha0 hμ hβ h Xwin ψ φ
  nlinarith

/-- `smallFactor_one` with the exponent `γ₁` of `SmallFactorPar`: `β_kδ_k² = A₀² λ_k^{2p₀}/a`. -/
theorem smallFactor_one_gamma1 (P : SmallFactorPar) (G : GeneratingSet d L N₀ k ϱ) (hk : 1 ≤ k)
    (hL : 2 ≤ L) (hd : 2 ≤ d) (hϱ : 2 * (d : ℝ) * L ≤ ϱ) {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hadm : IsAdmissibleWeights k (compWeight L a₁)) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {Xc Xwin : Finset (Site d L N₀ k)} (hXc : Xc ⊆ Xwin)
    (hXΩ : ∀ s ∈ Xc, s ∈ G.Ω 1 ∧ s ∉ G.Ω k) (hXk : IsBlockUnion L N₀ k k Xc)
    (hX : ∀ n, 1 ≤ n → n ≤ k → IsBlockUnion L N₀ k n (Xc ∩ G.layer n))
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) (hφ : ∀ x ∈ Xc, ‖φ x‖ = 1)
    {βk : ℝ} (hβ : 0 ≤ βk) (ϖ : ℕ → ℝ) (aN : Blk d L N₀ k k → ℝ) (hη0 : 0 ≤ P.eta)
    (hη : P.eta ≤ 1 / 2)
    (haN : ∀ z ∈ tBlocks d L N₀ k k Xc,
      |aN z - compWeightZ G a₁ z| ≤ P.eta * compWeightZ G a₁ z)
    {Mψ Sig Nbl : ℝ} (hM : ∀ s ∈ Xc, ‖leafField G ψ s‖ ≤ Mψ)
    (hSig : ∀ z ∈ tBlocks d L N₀ k k Xc, Real.sqrt βk * varsigmaBar G ϖ z ≤ Sig)
    (hN : ((tBlocks d L N₀ k k Xc).card : ℝ) ≤ Nbl) (hΛ19 : 8 * Sig ^ 2 * Nbl * Mψ ^ 2 ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hγ0 : P.gamma0 = gamma0 d)
    (hβδ : βk * δ ^ 2 = P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a)
    (hviol : ¬ PsiTildeSet {y : Blk d L N₀ k k | fib d L N₀ k k y ⊆ Xc} (ψ k) (3 * δ)) :
    P.gamma1 ≤ 1 / 2 * composedGauss G βk aN ϖ ψ Xc +
      multiAction G (compWeight L a₁) βk μ h Xwin ψ φ := by
  have := smallFactor_one G hk hL hd hϱ ha₁ hadm hμ h hXc hXΩ hXk hX ψ φ hφ hβ ϖ aN hη0 hη haN hM
    hSig hN hΛ19 hδ hviol
  have e : P.gamma1 = 9 / 8 * (1 - P.eta) * gamma0 d * (βk * δ ^ 2) - 1 / 2 := by
    unfold SmallFactorPar.gamma1
    rw [hγ0, hβδ]
    ring
  rw [e]
  exact this

/-- `smallFactor_violation` with `θ = δ_k/(6K₁)`: the exponent `γ₂` of `SmallFactorPar`
(`β_kδ_k² = A₀² λ_k^{2p₀}/a`). -/
theorem smallFactor_two_gamma2 (P : SmallFactorPar) (G : GeneratingSet d L N₀ k ϱ) (hk : 1 ≤ k)
    (hL : 2 ≤ L) (hd : 2 ≤ d) (hϱ : 2 * (d : ℝ) * L ≤ ϱ) {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hadm : IsAdmissibleWeights k (compWeight L a₁)) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {Xc Xwin : Finset (Site d L N₀ k)} (hXc : Xc ⊆ Xwin)
    (hXΩ : ∀ s ∈ Xc, s ∈ G.Ω 1 ∧ s ∉ G.Ω k) (hXk : IsBlockUnion L N₀ k k Xc)
    (hX : ∀ n, 1 ≤ n → n ≤ k → IsBlockUnion L N₀ k n (Xc ∩ G.layer n))
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) (hφ : ∀ x ∈ Xc, ‖φ x‖ = 1)
    {βk : ℝ} (hβ : 0 ≤ βk) (ϖ : ℕ → ℝ) (aN : Blk d L N₀ k k → ℝ) (hη0 : 0 ≤ P.eta)
    (hη : P.eta ≤ 1 / 2)
    (haN : ∀ z ∈ tBlocks d L N₀ k k Xc,
      |aN z - compWeightZ G a₁ z| ≤ P.eta * compWeightZ G a₁ z)
    {Mψ Sig Nbl : ℝ} (hM : ∀ s ∈ Xc, ‖leafField G ψ s‖ ≤ Mψ)
    (hSig : ∀ z ∈ tBlocks d L N₀ k k Xc, Real.sqrt βk * varsigmaBar G ϖ z ≤ Sig)
    (hN : ((tBlocks d L N₀ k k Xc).card : ℝ) ≤ Nbl) (hΛ19 : 8 * Sig ^ 2 * Nbl * Mψ ^ 2 ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hK1 : 0 < P.K1) (hγ0 : P.gamma0 = gamma0 d)
    (hβδ : βk * δ ^ 2 = P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a)
    (hviol : ¬ PsiTildeSet {y : Blk d L N₀ k k | fib d L N₀ k k y ⊆ Xc} (ψ k)
      (δ / (6 * P.K1))) :
    P.gamma2 ≤ composedGauss G βk aN ϖ ψ Xc +
      multiAction G (compWeight L a₁) βk μ h Xwin ψ φ := by
  have := smallFactor_violation G hk hL hd hϱ ha₁ hadm hμ h hXc hXΩ hXk hX ψ φ hφ hβ ϖ aN hη0 hη
    haN hM hSig hN hΛ19 (θ := δ / (6 * P.K1)) (by positivity) hviol
  have hK : P.K1 ≠ 0 := hK1.ne'
  have e : P.gamma2 = 1 / 2 * (1 - P.eta) * (1 / 2 * gamma0 d * (βk * (δ / (6 * P.K1)) ^ 2)) - 1 := by
    unfold SmallFactorPar.gamma2
    rw [hγ0]
    have : P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a = βk * δ ^ 2 := hβδ.symm
    calc (1 - P.eta) / (144 * P.K1 ^ 2) * gamma0 d * P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a - 1
        = (1 - P.eta) / (144 * P.K1 ^ 2) * gamma0 d * (P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a) - 1 := by
          ring
      _ = _ := by rw [this]; field_simp; ring
  rw [e]
  exact this

/-- `single_smallFactor` with `θ = δ_k/(6K₁)`: the exponent `γ₅` of `SmallFactorPar`. -/
theorem smallFactor_five_gamma5 (P : SmallFactorPar) (hk : 1 ≤ k) (hd : 2 ≤ d) (hL : 2 ≤ L)
    (hϱ : 2 * (d : ℝ) * L ≤ ϱ) {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {X : Finset (Site d L N₀ k)}
    (hXk : IsBlockUnion L N₀ k k X) (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) (hφ : ∀ x ∈ X, ‖φ x‖ = 1) {βk : ℝ}
    (hβ : 0 ≤ βk) {δ : ℝ} (hδ : 0 ≤ δ) (hK1 : 0 < P.K1) (hγ0 : P.gamma0 = gamma0 d)
    (hβδ : βk * δ ^ 2 = P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a)
    (hviol : ¬ PsiTildeSet {y : Blk d L N₀ k k | fib d L N₀ k k y ⊆ X} (ψ k) (δ / (6 * P.K1))) :
    P.gamma5 ≤ multiAction (singleGen d L N₀ k ϱ) a βk μ h X ψ φ := by
  have := single_smallFactor hk hd hL hϱ ha hμ h hXk ψ φ hφ hβ (θ := δ / (6 * P.K1))
    (by positivity) hviol
  have hK : P.K1 ≠ 0 := hK1.ne'
  have e : P.gamma5 = 1 / 2 * gamma0 d * (βk * (δ / (6 * P.K1)) ^ 2) := by
    unfold SmallFactorPar.gamma5
    rw [hγ0]
    have : P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a = βk * δ ^ 2 := hβδ.symm
    calc gamma0 d * P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / (72 * P.K1 ^ 2 * P.a)
        = gamma0 d * (P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a) / (72 * P.K1 ^ 2) := by
          ring
      _ = _ := by rw [this]; field_simp; ring
  rw [e]
  exact this

end Balaban.LargeField
