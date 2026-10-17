/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedFactor
public import Balaban.LargeField.R.RGasCoreFinal
public import Balaban.LargeField.Budget.Summability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# From the removed kernel bound to the gas factor `‖τ z‖ ≤ exp(-p₂ - H |c_z|)` (W878)

`notes/phase1/LF4R-PLAN.md`, leaf 3.  The removed factor `τ z` of a ripe component is a sum over
localized histories `𝔞` of integrals `∫ T_𝔞 · F_𝔞` of the removed kernel against the remaining
factor `F_𝔞` (with `‖F_𝔞‖ ≤ 1`; the factor `e^{E_k|Z|}` is absorbed in `T_𝔞`, as in Lemma III.8.7).

* `log_b_le_lamHat`: `log b_k ≤ λ̂_k` under `RunningHyp`; `p2Run_le_A2_lamHat_pow`.
* `removed_kerBound_logC_of_window`: the exponent assembly with the history weight kept: the
  exponent is `A₂ λ^{p₂} + H_k M^d c + 1 + log C(𝔞)` (the landed `removed_kerBound_of_window` drops
  `log C(𝔞) ≥ 0`, which is what the sum over histories needs).
* `norm_integral_le_of_kerBound`: `‖∫∫ w F‖ ≤ e^{-κ}` from `KerBound` and `‖F‖ ≤ 1`.
* `norm_tau_le_of_removed_kernels`: `hrem`, from the kernel bounds and `∑_𝔞 C(𝔞)^{-1} ≤ 1`.
* the composed theorem `…_of_kernel`.

Units: the budget is `H_k |Z|_k` with `|Z|_k = M^d c` (`BudgetConsts.cubeVol`), `c` the number of
cubes of the component; so the gas constant is `H := H_k M^d`, and the gas card is `c`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section Arith

variable {d L : ℕ} {β ν a ε : ℝ} {b nn : ℕ → ℝ}

/-- **`log β_k ≤ λ̂_k`** under the running hypothesis (I.2). -/
theorem log_b_le_lamHat (hrun : RunningHyp d L β ν a ε b nn) (k : ℕ) :
    Real.log (b k) ≤ lamHat d L β a k := by
  obtain ⟨γ, hγ, hlg, hb⟩ := hrun.beta_eq k
  have hL : (0 : ℝ) < L := by exact_mod_cast (by have := hrun.hL; omega : 0 < L)
  have ha : 0 < a := by linarith [hrun.ha1]
  have hβ := hrun.hβ
  have hlogb : Real.log (b k) = Real.log β + ((k * (d - 2) : ℕ) : ℝ) * Real.log L + Real.log γ := by
    rw [hb, Real.log_mul (by positivity) hγ.ne', Real.log_mul hβ.ne' (by positivity),
      Real.log_pow]
  have hla : 0 < Real.log a := Real.log_pos hrun.ha1
  have hlg1 : Real.log γ ≤ 1 := by
    have := le_abs_self (Real.log γ)
    linarith [hrun.hε]
  unfold lamHat thetaOf
  rw [hlogb, Real.log_mul hβ.ne' ha.ne']
  push_cast
  nlinarith

/-- **`p₂(β_k) ≤ A₂ λ̂_k^{p₂}`**, for `0 ≤ log β_k` and `0 ≤ A₂`. -/
theorem p2Run_le_A2_lamHat_pow (hrun : RunningHyp d L β ν a ε b nn) (k : ℕ) {A2 : ℝ} {p2 : ℕ}
    (hA2 : 0 ≤ A2) (hb0 : 0 ≤ Real.log (b k)) :
    p2Run A2 p2 b k ≤ A2 * lamHat d L β a k ^ p2 := by
  unfold p2Run
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 (log_b_le_lamHat hrun k) _) hA2

end Arith

section Window

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- The exponent assembly of `removed_kerBound_of_window` with the history weight kept: the
exponent is `A₂ λ^{p₂} + H_k M^d c + 1 + log C(𝔞)`.  Same hypotheses. -/
theorem removed_kerBound_logC_of_window {a : LocalHistory S n M K} {k : ℕ}
    {A : Set (InternalVars a k)}
    {T : LFKernel (OutT N R a k) (SubCfg N a k A) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N)}
    {P : BudgetConsts} {c : ℕ} {κpre logC Gp : ℝ}
    (hG : Gp = P.budgetG S k κpre logC c)
    (hrip : 2 * S.A2 * S.lam k ^ S.p2 + 1 ≤ Gp)
    (hCR : S.CR * S.lam k ^ (2 * S.d + 1) ≤ S.A2 * S.lam k ^ S.p2)
    (hwin : KerBound a k T (κpre - S.CR * S.lam k ^ (2 * S.d + 1))) :
    KerBound a k T
      (S.A2 * S.lam k ^ S.p2 + HRun P.H0 P.beta k * BudgetConsts.cubeVol S c + 1 + logC) := by
  refine hwin.mono ?_
  have h : Gp = κpre - logC - HRun P.H0 P.beta k * BudgetConsts.cubeVol S c := hG
  linarith

end Window

section Integral

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- **The integral of a kernel against a factor of norm `≤ 1`.**  If `T` satisfies the bound
(1.26) with exponent `κ`, then `‖∫∫ T.w · F‖ ≤ e^{-κ}` (integrals over the outputs on `Z` and the
internal variables, at fixed parameters). -/
theorem norm_integral_le_of_kerBound {a : LocalHistory S n M K} {k : ℕ}
    {A : Set (InternalVars a k)}
    {T : LFKernel (OutT N R a k) (SubCfg N a k A) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N)}
    {κ : ℝ} (hT : KerBound a k T κ) (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (hg : g ∈ l1Ball (GIdx S n M K N)) (par : OutPar N R a k)
    (F : OutT N R a k → SubCfg N a k A → ℂ) (hF : ∀ o x, ‖F o x‖ ≤ 1) :
    ‖∫ oz, ∫ x, T.w (mergeOut a k oz par) x hv g * F (mergeOut a k oz par) x
        ∂(subMeasure N a k A) ∂(outPartMeasure N (Vblk R a k) (ZBlk a k))‖ ≤ Real.exp (-κ) := by
  have h1 := enorm_integral_le_lintegral_enorm (μ := outPartMeasure N (Vblk R a k) (ZBlk a k))
    (fun oz => ∫ x, T.w (mergeOut a k oz par) x hv g * F (mergeOut a k oz par) x
        ∂(subMeasure N a k A))
  have h2 : ∀ oz, ‖∫ x, T.w (mergeOut a k oz par) x hv g * F (mergeOut a k oz par) x
        ∂(subMeasure N a k A)‖ₑ ≤ ∫⁻ x, T.absW (mergeOut a k oz par) x hv g
        ∂(subMeasure N a k A) := fun oz => by
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
    rw [enorm_mul]
    have hw : ‖T.w (mergeOut a k oz par) x hv g‖ₑ = T.absW (mergeOut a k oz par) x hv g := by
      unfold LFKernel.w LFKernel.absW
      rw [← ofReal_norm, norm_mul, Complex.norm_exp, Complex.norm_real,
        Real.norm_of_nonneg (T.K_nonneg _ _ _)]
    rw [hw]
    calc T.absW (mergeOut a k oz par) x hv g * ‖F (mergeOut a k oz par) x‖ₑ
        ≤ T.absW (mergeOut a k oz par) x hv g * 1 := by
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_one.2 (hF _ _)
      _ = _ := mul_one _
  have h3 := h1.trans ((lintegral_mono h2).trans (hT hv g hg par))
  rw [← ofReal_norm] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 h3

end Integral

section Tau

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- **The removed factor from the kernel bounds.**  Let `τ z` be, for each `z`, the sum over the
localized histories `𝔞 ∈ As z` of the component `Y z` of the integral `∫∫ T_𝔞.w · F_𝔞` over the
outputs on `Z` and the internal variables, with `‖F_𝔞‖ ≤ 1` (the identity `hτ`).  If each `T_𝔞`
satisfies (1.26) with the exponent `p + H c_z + 1 + log C_k(𝔞)` (the conclusion of
`removed_kerBound_logC_of_window`), then `‖τ z‖ ≤ exp(-p - H c_z)`, by the summability
`∑_𝔞 C_k(𝔞)^{-1} ≤ 1` (Lemma II.5.15, `L^d ≥ 8`). -/
theorem norm_tau_le_of_removed_kernels (hLd : 8 ≤ S.L ^ S.d) {k : ℕ} (hkK : k ≤ K)
    {Zt : Type*} {τ : Zt → ℂ} (Y : Zt → Finset (Torus S.d (n k)))
    (As : Zt → Finset (LocalHistory S n M K))
    (hAs : ∀ z, ∀ a ∈ As z, a ∈ histSet S n R k0 M K k (Y z))
    {Aint : ∀ a : LocalHistory S n M K, Set (InternalVars a k)}
    (T : ∀ a : LocalHistory S n M K, LFKernel (OutT N R a k) (SubCfg N a k (Aint a))
      (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N))
    (F : Zt → ∀ a : LocalHistory S n M K, OutT N R a k → SubCfg N a k (Aint a) → ℂ)
    (hF : ∀ z a o x, ‖F z a o x‖ ≤ 1) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N))
    (par : Zt → ∀ a : LocalHistory S n M K, OutPar N R a k)
    (hτ : ∀ z, τ z = ∑ a ∈ As z, ∫ oz, ∫ x, (T a).w (mergeOut a k oz (par z a)) x hv g *
        F z a (mergeOut a k oz (par z a)) x ∂(subMeasure N a k (Aint a))
        ∂(outPartMeasure N (Vblk R a k) (ZBlk a k)))
    {p H : ℝ} (c : Zt → ℕ)
    (hker : ∀ z, ∀ a ∈ As z, KerBound a k (T a) (p + H * (c z : ℝ) + 1 + a.logC k)) (z : Zt) :
    ‖τ z‖ ≤ Real.exp (-p - H * (c z : ℝ)) := by
  classical
  rw [hτ z]
  have h1 : ∀ a ∈ As z, ‖∫ oz, ∫ x, (T a).w (mergeOut a k oz (par z a)) x hv g *
        F z a (mergeOut a k oz (par z a)) x ∂(subMeasure N a k (Aint a))
        ∂(outPartMeasure N (Vblk R a k) (ZBlk a k))‖ ≤
      Real.exp (-(p + H * (c z : ℝ) + 1)) * Real.exp (-(a.logC k)) := fun a ha => by
    refine (norm_integral_le_of_kerBound (hker z a ha) hv g hg (par z a) (F z a)
      (hF z a)).trans (le_of_eq ?_)
    rw [← Real.exp_add]; congr 1; ring
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum h1).trans ?_)
  rw [← Finset.mul_sum]
  have h2 := sum_inv_logC_le_one (S := S) (R := R) (k0 := k0) (M := M) hLd k hkK (Y z) (As z)
    (hAs z)
  calc Real.exp (-(p + H * (c z : ℝ) + 1)) * ∑ a ∈ As z, Real.exp (-(a.logC k))
      ≤ Real.exp (-(p + H * (c z : ℝ) + 1)) * 1 := by gcongr
    _ ≤ Real.exp (-p - H * (c z : ℝ)) := by
        rw [mul_one]; exact Real.exp_le_exp.2 (by linarith)

end Tau

section Composed

open Balaban.Polymer RegionHistory Balaban.Background D7Reserve Balaban.Fluctuation
  Balaban.Localization Balaban.Multiscale Balaban.LargeField.Def7

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] [NeZero S.M] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {Yt Zt : Type*} [Fintype Yt] [Fintype Zt] {τ : Zt → ℂ}

open Classical in
/-- **The halo gas bound for removed components from the removed kernel bounds.**  As
`gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_run`, with `hrem` replaced by:
the identity `hτ` writing `τ z` as the sum over localized histories of the integrals of the
removed kernels `Tr a` against factors of norm `≤ 1`, the kernel bounds `hker` (the conclusion of
`removed_kerBound_logC_of_window`, exponent `A₂ λ^{p₂} + H_k M^d c + 1 + log C_k(𝔞)`), the
units `H = H_k M^d`, `P.beta = b`, `L^d ≥ 8`, `0 ≤ A₂`, `0 ≤ log β_k`. -/
theorem gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_run_of_kernel
    {m₀ m₁ : ℕ}
    {Fr : FineSizeFrame S n M K m₀ m₁}
    {hnn : ∀ i, i < K → n i = S.L * n (i + 1)} {hkK : k ≤ K}
    {rep : Rep S n R k0 K M N geo cs P k} {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))}
    {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ} {hv : EuclideanSpace ℝ (Fin N)}
    (hD : D7BdryPost Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv) {A : LabHist S n R k0 K}
    (hA : A ∈ rep.hist) {hext : Fin N → ℂ} (hhB : hext ∈ hSetB hv)
    (p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ))
    (labY : Yt → Finset (Torus S.d (n k))) (hlabY : Function.Injective labY)
    (hlabYv : ∀ y, labY y ∈ bdryDomsPost Fr A k (Zof A))
    (hp : ∀ y, H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) k hkK
        (fineSet (S := S) (n := n) M K k (labY y : Set (Torus S.d (n k)))) aw μs ε ε1 νs hext
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i)))
    (labZ : Zt → Finset (Torus S.d (n k))) (hlabZ : Function.Injective labZ)
    {cy zs cr : _ → Finset (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull Fr k (A.H.omegaPost k)))}
    (hXY : ∀ y, d7Pull Fr k (labY y : Set (Torus S.d (n k))) =
      Yhat (d7Pull Fr k (A.H.omegaPost k)) (sitesOf (cy y)))
    (hXZ : ∀ z, d7Pull Fr k (labZ z : Set (Torus S.d (n k))) =
      Yhat (d7Pull Fr k (A.H.omegaPost k)) (sitesOf (zs z)))
    (hk : 1 ≤ k) (hR : ⌊R (k - 1)⌋₊ = ⌊S.Rb * S.lam (k - 1) ^ 2⌋₊)
    (cz : Zt → A.H.Comp k) (hcz : ∀ z, (cz z).1 ∈ A.H.rem k)
    (hlabZ' : ∀ z, (labZ z : Set (Torus S.d (n k))) =
      nbhd (2 * ⌊R (k - 1)⌋₊ + 4) ((cz z).1 : Set (Torus S.d (n k))))
    {κ' p' h' : ℝ} (hfac : 0 ≤ fac) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ rate) (hp' : 0 ≤ p')
    (hκ : aEnt S.d S.L + 1 ≤ rate - κ')
    (hz : ∀ z, (zs z).Nonempty) (hcr : ∀ z, cr z ⊆ zs z)
    (β : Yt → ℂ) (hβ : ∀ y, β y = rep.B A (labY y) (extK p.1) (extK p.2.1) hext p.2.2)
    (G : S.Good) (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j)
    {H : ℝ} (hH : 0 ≤ H) (hh' : 0 ≤ h')
    {β₀ ν₀ a₀ ε₀ : ℝ} {b nn : ℕ → ℝ} (ok : S.Ok)
    (hlam : ∀ j, S.lam j = lamHat S.d S.L β₀ a₀ j)
    (hrun : RunningHyp S.d S.L β₀ ν₀ a₀ ε₀ b nn)
    (hp'2 : p' ≤ 1 / 2 * p2Run S.A2 S.p2 b k)
    (hx0 : x0 S.d h' (2 ^ S.d * ((2 * (S.c0 : ℝ) + 18) ^ S.d +
      (2 * (S.c0 : ℝ) * S.Rb + 4 * S.Rb) ^ S.d)) S.A2 ≤ Real.log (b k))
    (hLd : 8 ≤ S.L ^ S.d) (hA2 : 0 ≤ S.A2) (hb0 : 0 ≤ Real.log (b k)) (hPb : P.beta = b)
    (hHdef : H = HRun P.H0 b k * (S.M : ℝ) ^ S.d)
    (Hs : Zt → Finset (LocalHistory S n M K))
    (hHs : ∀ z, ∀ a ∈ Hs z, a ∈ histSet S n R k0 M K k (cz z).1)
    {Aint : ∀ a : LocalHistory S n M K, Set (InternalVars a k)}
    (Tr : ∀ a : LocalHistory S n M K, LFKernel (OutT N R a k) (SubCfg N a k (Aint a))
      (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N))
    (Fa : Zt → ∀ a : LocalHistory S n M K, OutT N R a k → SubCfg N a k (Aint a) → ℂ)
    (hFa : ∀ z a o x, ‖Fa z a o x‖ ≤ 1)
    (gk : GIdx S n M K N → ℂ) (hgk : gk ∈ l1Ball (GIdx S n M K N))
    (parK : Zt → ∀ a : LocalHistory S n M K, OutPar N R a k)
    (hτ : ∀ z, τ z = ∑ a ∈ Hs z, ∫ oz, ∫ x, (Tr a).w (mergeOut a k oz (parK z a)) x hv gk *
        Fa z a (mergeOut a k oz (parK z a)) x ∂(subMeasure N a k (Aint a))
        ∂(outPartMeasure N (Vblk R a k) (ZBlk a k)))
    (hker : ∀ z, ∀ a ∈ Hs z, KerBound a k (Tr a) (S.A2 * S.lam k ^ S.p2 +
      HRun P.H0 P.beta k * BudgetConsts.cubeVol S (cz z).1.card + 1 + a.logC k))
    (hh : fac * Real.exp fac * Real.exp (κ' * cG S.d S.L) *
        (1 * (K0 S.d S.L (aEnt S.d S.L + 1) + 1)) +
      κ' * (1 + cG S.d S.L) + c1 S.d S.L + 3 +
      Real.log (1 * (K0 S.d S.L (aEnt S.d S.L + 1) + 1) *
        Real.exp ((aEnt S.d S.L + 1) * 1)) ≤ h')
    (X : NePoly (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull Fr k (A.H.omegaPost k)))) :
    ‖gasK cy zs cr β τ X‖ ≤
      3 * c1 S.d S.L * Real.exp (-p') * Real.exp (-(κ' - 2) * dExt (d := S.d) X.1) := by
  have hrem : ∀ z, ‖τ z‖ ≤ Real.exp (-p2Run S.A2 S.p2 b k - H * ((cz z).1.card : ℝ)) := by
    intro z
    have h1 := norm_tau_le_of_removed_kernels (k0 := k0) hLd hkK (fun z => (cz z).1) Hs hHs Tr Fa
      hFa hv gk hgk parK hτ (p := S.A2 * S.lam k ^ S.p2) (H := H) (fun z => (cz z).1.card)
      (fun z a ha => by
        have e : S.A2 * S.lam k ^ S.p2 + H * (((cz z).1.card : ℕ) : ℝ) + 1 + a.logC k =
            S.A2 * S.lam k ^ S.p2 + HRun P.H0 P.beta k *
              BudgetConsts.cubeVol S (cz z).1.card + 1 + a.logC k := by
          rw [hHdef, hPb]; unfold BudgetConsts.cubeVol; ring
        rw [e]; exact hker z a ha) z
    refine h1.trans (Real.exp_le_exp.2 ?_)
    have h2 := p2Run_le_A2_lamHat_pow hrun k hA2 hb0 (p2 := S.p2)
    rw [← hlam k] at h2
    linarith
  exact gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_run hD hA hhB p labY hlabY
    hlabYv hp labZ hlabZ hXY hXZ hk hR cz hcz hlabZ' hfac hκ' hκ'' hp' hκ hz hcr β hβ G hT hH hh'
    ok hlam hrun hp'2 hx0 hrem hh X

end Composed

end Balaban.LargeField
