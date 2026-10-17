/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RGasCorePay

/-!
# The halo gas bound with the payment condition discharged (W874, blocker 4)

`notes/phase1/VMOD-43.md`.  `halo_pay_le_p2Run` needs `⌊R_{k-1}⌋ ≤ R_base λ_k²`; this follows from
`⌊R_{k-1}⌋ = ⌊R_base λ_{k-1}²⌋` and the monotonicity of `λ` (`Setting.Ok.lam_step`, `θ₋ > 0`).
The combined theorem is the halo gas bound with the removed factor `‖τ z‖ ≤ exp(-p₂ - H |c_z|)`,
`p₂ = p₂(β_k)`, as the only source input on `τ`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Multiscale Balaban.LargeField.Def7

section Radius

variable {S : Setting}

/-- **`⌊R_{k-1}⌋ ≤ R_base λ_k²`**, from `⌊R_{k-1}⌋ = ⌊R_base λ_{k-1}²⌋` and `λ_{k-1} ≤ λ_k`. -/
theorem floor_radius_le_Rb_lam_sq (ok : S.Ok) {R : ℕ → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hR : ⌊R (k - 1)⌋₊ = ⌊S.Rb * S.lam (k - 1) ^ 2⌋₊) :
    ((⌊R (k - 1)⌋₊ : ℕ) : ℝ) ≤ S.Rb * S.lam k ^ 2 := by
  have hRb := ok.Rb_pos
  have hstep := (ok.lam_step (k - 1)).1
  have hθ := ok.θm_pos
  have hk' : k - 1 + 1 = k := by omega
  rw [hk'] at hstep
  have hl1 : S.lam (k - 1) ≤ S.lam k := by linarith
  have hl0 : 0 ≤ S.lam (k - 1) := by
    have := ok.one_le_lam0
    have hm : Monotone S.lam := monotone_nat_of_le_succ fun j => by
      have := (ok.lam_step j).1; linarith
    linarith [hm (Nat.zero_le (k - 1))]
  rw [hR]
  calc ((⌊S.Rb * S.lam (k - 1) ^ 2⌋₊ : ℕ) : ℝ) ≤ S.Rb * S.lam (k - 1) ^ 2 :=
        Nat.floor_le (by positivity)
    _ ≤ S.Rb * S.lam k ^ 2 := by gcongr

end Radius

section Final

open Balaban.Polymer RegionHistory Balaban.Background D7Reserve

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] [NeZero S.M] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {Yt Zt : Type*} [Fintype Yt] [Fintype Zt] {τ : Zt → ℂ}

open Classical in
/-- **The halo gas bound for removed components, the payment condition discharged.**
As `gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_box` with
`p₂ = p₂(β_k) = A₂ (log β_k)^{p₂}` (`p2Run`), in the running setting (`λ_j = λ̂_j`, `RunningHyp`),
`p' ≤ ½ p₂(β_k)` and `log β_k ≥ x₀`; the condition `hpay` is replaced by these.  The only input on
`τ` is the removed factor `hrem` (P7 (3.10)). -/
theorem gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_run
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
    (hrem : ∀ z, ‖τ z‖ ≤ Real.exp (-p2Run S.A2 S.p2 b k - H * ((cz z).1.card : ℝ)))
    (hh : fac * Real.exp fac * Real.exp (κ' * cG S.d S.L) *
        (1 * (K0 S.d S.L (aEnt S.d S.L + 1) + 1)) +
      κ' * (1 + cG S.d S.L) + c1 S.d S.L + 3 +
      Real.log (1 * (K0 S.d S.L (aEnt S.d S.L + 1) + 1) *
        Real.exp ((aEnt S.d S.L + 1) * 1)) ≤ h')
    (X : NePoly (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull Fr k (A.H.omegaPost k)))) :
    ‖gasK cy zs cr β τ X‖ ≤
      3 * c1 S.d S.L * Real.exp (-p') * Real.exp (-(κ' - 2) * dExt (d := S.d) X.1) :=
  gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_box hD hA hhB p labY hlabY
    hlabYv hp labZ hlabZ hXY hXZ hk hR cz hcz hlabZ' hfac hκ' hκ'' hp' hκ hz hcr β hβ G hT hH hh'
    hrem
    (halo_pay_le_p2Run ok hlam hrun (floor_radius_le_Rb_lam_sq ok hk hR) hh' hp'2 hx0) hh X

end Final

end Balaban.LargeField
