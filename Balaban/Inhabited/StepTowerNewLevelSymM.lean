/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelSymMain

/-!
# `hDMfull` for the step source density (`StepTowerNewLevelSymM`)

The source density `ℳ₀^{(k+1)}(x; g)` of the new level (`M0H`, `densM0`) is covariant under
`fullJSymGroup L (k + 1)`, in the exact form of the input `hDMfull` of
`localClass_newLevel_of_expansion_cast`:

* `McompAtC_sym`, `FcompAtC_sym`: the old composites `ℳ_k`, `ℱ_k` at the transported datum, site
  and source (clause `eucMloc` of the old class, on the domain of the level sets);
* `M0H_sym`: the two-parameter interpolation integral of `M0H` is transported, with the same
  cores as `E0locH_sym` (`hatCovSqrt_sym`, `hatField_sym`, `nuFl_measurePreserving`,
  `integral_transport`, `phi_eventuallyEq_of_dom`);
* `densM0_fullJSymGroup`: the cast-theorem form, with the premises of `densE0_fullJSymGroup`
  (`hdom` verbatim; no analyticity premise is needed).
-/

@[expose] public section

namespace Balaban.Inhabited.StepSym

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.Localization.DecEquiv Balaban.Localization.DetUnitIncidence Matrix Filter Topology

section MOld

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {P : Consts}
  {a' : ℕ → ℝ} {μ' : ℝ} {ε' : ℕ → ℝ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
  {a : ℕ → ℝ} {ν : ℝ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}

/-- **`ℳ_k` at the transported datum, source and site**: `ℳ_k(σ E; σ g)(σ y) = ℳ_k(E; g)(y)`. -/
theorem McompAtC_sym
    (hcl : SFTermClauses P (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ) Tm)
    (hσ : σ ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1))
    (Sk : LatSymm (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
      (Nat.le_succ k)) (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
      (Nat.le_succ k)) σ)
    (E : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
      (Nat.le_succ k)) N)
    (hdom : ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        (composedPairAtC a ν (Nat.le_succ k) j E).1 (composedPairAtC a ν (Nat.le_succ k) j E).2)
    (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) :
    McompAtC P.m₀ Tm a ν (Nat.le_succ k) (Sk.sym E) (actField σ g) (σ y) =
      McompAtC P.m₀ Tm a ν (Nat.le_succ k) E g y := by
  funext i
  unfold McompAtC
  congr 1
  · rw [(Sk.bgFieldC_sym a ν (bgC0 d L N) E).1]
    exact Sk.svec_sym _ y i
  · refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
    have hjk' : j ≤ k + 1 := hjk.trans (Nat.le_succ k)
    have hσj : σ ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L j :=
      symGroupBy_le_of_dvd (pow_dvd_pow L hjk')
        (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))) hσ
    rw [composedPairAtC_sym (a := a) (ν := ν) hσ Sk hj1 hjk E]
    have h := hcl.eucMloc j hj1 hjk' y σ hσj _ _ g (hdom j hj hjk')
      ((xiFieldDom_act_levelGS hσ hj1 hjk' _ _).2 (hdom j hj hjk'))
    exact congrFun h i

/-- **`ℱ_k` at the transported datum and source equals `ℱ_k`.** -/
theorem FcompAtC_sym
    (hcl : SFTermClauses P (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ) Tm)
    (hσ : σ ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1))
    (Sk : LatSymm (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
      (Nat.le_succ k)) (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
      (Nat.le_succ k)) σ)
    (E : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
      (Nat.le_succ k)) N)
    (hdom : ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        (composedPairAtC a ν (Nat.le_succ k) j E).1 (composedPairAtC a ν (Nat.le_succ k) j E).2)
    (g : Fld d L N₁ m₁ (k + 1) N) :
    FcompAtC P.m₀ Tm a ν (Nat.le_succ k) (Sk.sym E) (actField σ g) =
      FcompAtC P.m₀ Tm a ν (Nat.le_succ k) E g := by
  rw [FcompAtC_eq_pair, FcompAtC_eq_pair, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  rw [McompAtC_sym hcl hσ Sk E hdom g x]
  simp [actField]

end MOld

section MStep

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {P : Consts}
  {a' : ℕ → ℝ} {μ' : ℝ} {ε' : ℕ → ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (C : StepClass d L N₁ m₁ k N ϱ)
variable (Sy : LatSymm S.G' S.G' σ) (Sk : LatSymm (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) σ)
  (hU : UnitBlockPres σ)

include Sy Sk hU in
/-- The old datum of a transported shift: `dataUCH (σ D) (ψ^{(k)}(σ D) + ψ ∘ u⁻¹)` is the transport
of `dataUCH D (ψ^{(k)}(D) + ψ)`. -/
theorem dataUCH_psi0H_add_sym (D : BgData S.G' N) (ψ : S.EC) :
    (S.withDatumH (Sy.sym D)).dataUCH ((S.withDatumH (Sy.sym D)).psi0H +
        fun r => ψ ((unitAct S.G' Sy hU).symm r.1, r.2)) =
      Sk.sym ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + ψ)) := by
  have h := dataUCH_sym Sy Sk hU D ((S.withDatumH D).psi0H + ψ)
  rw [← h, psi0H_sym Sy Sk hU D]
  rfl

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)

include hC hMX hdm hα hsm Sy Sk hU in
/-- **`ℳ₀^{(k+1)}(y; g)` is covariant under a lattice symmetry** (`M0H`): at the transported
datum, site and source the vector is unchanged, once the old composed pairs along the path (and a
neighbourhood of each path point) lie in the domain of the level sets of the old class. -/
theorem M0H_sym
    (hcl : SFTermClauses P (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ) C.Tm)
    (hm : P.m₀ = C.m₀)
    (hσ : σ ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1))
    (hp₁ : 0 < S.p₁) {D : BgData S.G' N}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (hdom : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ < S.p₁ →
      ∀ᶠ w in 𝓝 ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)),
        ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
        (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
          (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).1
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).2)
    (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    (S.withDatumH (Sy.sym D)).M0H C (actField σ g) (σ y) i = (S.withDatumH D).M0H C g y i := by
  classical
  have hD' : ∀ D : BgData S.G' N, (S.withDatumH D).D' = D := fun _ => rfl
  have hM := hatCovSqrt_sym hC hMX hdm hα hsm Sy hU hD
  set u := unitAct S.G' Sy hU with hu
  have hμ := nuFl_measurePreserving (S := S) hp₁ u
  have hdom0 : ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H)).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H)).2 := by
    have h0 := (hdom 0 ⟨le_rfl, zero_le_one⟩ 0 (by simpa using hp₁)).self_of_nhds
    simp only [Complex.ofReal_zero, zero_smul, add_zero] at h0
    exact h0
  have hdat0 : (S.withDatumH (Sy.sym D)).dataUCH (S.withDatumH (Sy.sym D)).psi0H =
      Sk.sym ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H) := by
    rw [psi0H_sym Sy Sk hU D, dataUCH_sym Sy Sk hU D]
  unfold StepSettingH.M0H
  simp only [hD']
  refine congrArg (fun w : ℂ => ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * w) ?_
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  unfold avgFun₂ partFun₂
  have key : ∀ᵐ x ∂S.nuFl,
      (deriv (fun r : ℝ => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
        ((S.withDatumH (Sy.sym D)).dataUCH ((S.withDatumH (Sy.sym D)).psi0H + (r : ℂ) •
          S.hatField (hatCovSqrt S.G' S.a₁ S.ν (Sy.sym D))
            (yhat (MeasurableEquiv.arrowCongr' u (MeasurableEquiv.refl (Rn N)) x))))
        (actField σ g) (σ y) i) t =
      deriv (fun r : ℝ => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
        ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + (r : ℂ) •
          S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x))) g y i) t) ∧
      ((S.withDatumH (Sy.sym D)).Phi1H C ((((1 : ℝ) : ℂ)) •
          S.hatField (hatCovSqrt S.G' S.a₁ S.ν (Sy.sym D))
            (yhat (MeasurableEquiv.arrowCongr' u (MeasurableEquiv.refl (Rn N)) x))) +
        (FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
          ((S.withDatumH (Sy.sym D)).dataUCH ((S.withDatumH (Sy.sym D)).psi0H + (t : ℂ) •
            S.hatField (hatCovSqrt S.G' S.a₁ S.ν (Sy.sym D))
              (yhat (MeasurableEquiv.arrowCongr' u (MeasurableEquiv.refl (Rn N)) x))))
          (actField σ g) -
        FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
          ((S.withDatumH (Sy.sym D)).dataUCH (S.withDatumH (Sy.sym D)).psi0H) (actField σ g))) =
      ((S.withDatumH D).Phi1H C ((((1 : ℝ) : ℂ)) •
          S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)) +
        (FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
          ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + (t : ℂ) •
            S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x))) g -
        FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
          ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H) g)) := by
    filter_upwards [S.ae_ball hp₁] with x hx
    have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp₁ x).1 hx
    have hy : yhat (MeasurableEquiv.arrowCongr' u (MeasurableEquiv.refl (Rn N)) x) =
        fun r => yhat x (u.symm r.1, r.2) := rfl
    have hh : S.hatField (hatCovSqrt S.G' S.a₁ S.ν (Sy.sym D))
        (yhat (MeasurableEquiv.arrowCongr' u (MeasurableEquiv.refl (Rn N)) x)) =
        fun r => S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x) (u.symm r.1, r.2) := by
      rw [hy, hM]; exact hatField_sym Sy hU _ _
    have hE : ∀ r : ℝ, (S.withDatumH (Sy.sym D)).dataUCH ((S.withDatumH (Sy.sym D)).psi0H +
        (r : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν (Sy.sym D))
          (yhat (MeasurableEquiv.arrowCongr' u (MeasurableEquiv.refl (Rn N)) x))) =
        Sk.sym ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + (r : ℂ) •
          S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x))) := fun r => by
      rw [hh]
      exact dataUCH_psi0H_add_sym Sy Sk hU D
        ((r : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x))
    have hpt : ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
        (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
          (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + (r : ℂ) •
              S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)))).1
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + (r : ℂ) •
              S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)))).2 :=
      fun r hr => (hdom r hr x hxn).self_of_nhds
    refine ⟨?_, ?_⟩
    · have hev : (fun r : ℝ => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
          ((S.withDatumH (Sy.sym D)).dataUCH ((S.withDatumH (Sy.sym D)).psi0H + (r : ℂ) •
            S.hatField (hatCovSqrt S.G' S.a₁ S.ν (Sy.sym D))
              (yhat (MeasurableEquiv.arrowCongr' u (MeasurableEquiv.refl (Rn N)) x))))
          (actField σ g) (σ y) i) =ᶠ[𝓝 t]
          fun r : ℝ => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + (r : ℂ) •
              S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x))) g y i := by
        have hcont : Tendsto (fun r : ℝ => (r : ℂ) •
            S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)) (𝓝 t)
            (𝓝 ((t : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x))) :=
          ((Complex.continuous_ofReal.smul continuous_const).continuousAt)
        filter_upwards [hcont.eventually (hdom t ht x hxn)] with r hr
        simp only [hE r]
        have := McompAtC_sym (a := S.a) (ν := S.ν) (P := P) hcl hσ Sk
          ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + (r : ℂ) •
            S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x))) hr g y
        rw [hm] at this
        exact congrFun this i
      exact hev.deriv_eq
    · have hΦ := (phi_eventuallyEq_of_dom C Sy Sk hU hcl hm hσ D
        (hdom 1 ⟨zero_le_one, le_rfl⟩ x hxn) hdom0).eq_of_nhds
      have hF1 := FcompAtC_sym (a := S.a) (ν := S.ν) (P := P) hcl hσ Sk
        ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + (t : ℂ) •
          S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x))) (hpt t ht) g
      have hF0 := FcompAtC_sym (a := S.a) (ν := S.ν) (P := P) hcl hσ Sk
        ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H) hdom0 g
      rw [hm] at hF1 hF0
      rw [hE t, hdat0, hF1, hF0, hh]
      exact congrArg (fun z => z + _) hΦ.symm
  refine congrArg₂ (· / ·) ?_ ?_
  · refine integral_transport hμ _ _ ?_
    filter_upwards [key] with x hx
    beta_reduce
    rw [hx.1, hx.2]
  · refine integral_transport hμ _ _ ?_
    filter_upwards [key] with x hx
    beta_reduce
    rw [hx.2]

end MStep

section MMain

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ eps pp : ℝ} {P : Consts}
  {a' : ℕ → ℝ} {μ' : ℝ} {ε' : ℕ → ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ}
variable {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}
variable (Jr : S.JointRep eps pp) (C : StepClass d L N₁ m₁ k N ϱ)
variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)

include hC hMX hdm hα hsm in
/-- **`hDMfull` for the step source density `densM0`** (the covariance of `𝒟_M = ℳ₀^{(k+1)}` under
the full level group `fullJSymGroup L (k + 1)`, in the exact form of the input `hDMfull` of
`localClass_newLevel_of_expansion_cast`), under the premises of `densE0_fullJSymGroup` (the
identity `densM0_eq` needs no analyticity premise `hE`).  The proof is `M0H_sym` at the cut-off
datum, with the old composite `ℳ_k`, `ℱ_k` transported (`McompAtC_sym`, `FcompAtC_sym`, from
`eucMloc`). -/
theorem densM0_fullJSymGroup (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    (hcl : SFTermClauses P (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ) C.Tm)
    (hm : P.m₀ = C.m₀)
    (hdom : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ < S.p₁ →
      ∀ᶠ w in 𝓝 ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)),
        ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
        (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
          (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).1
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).2)
    (hG : S.G' = levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
    (hε : P.eps d L (k + 1) ≤ eps) :
    ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1),
      ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1))) q.1 q.2 →
      (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      Jr.densM0 C (r x) ((actField r q.1, actField r q.2), actField r g) =
        Jr.densM0 C x (q, g) := by
  intro r hr x q g hq hrq
  funext i
  obtain ⟨Sy⟩ := nonempty_latSymm_of_isLevel (G := S.G') S.hG' (n := k + 1) (j := k + 1)
    le_rfl le_rfl hr
  obtain ⟨Sk⟩ := nonempty_latSymm_of_isLevel (G := stepG d L N₁ m₁ k ϱ) S.hG (n := k)
    (j := k + 1) (Nat.le_succ k) le_rfl hr
  have hU := unitBlockPres_of_fullJ hr
  have hq' : XiDom S.G' S.a S.ν (k + 1) (P.eps d L (k + 1)) q.1 q.2 := by
    rw [hG]; exact hq
  obtain ⟨D, hD, hcq⟩ := clipRaw_mem_xiCRaw_of_xiDom hε hq'
  have hD' := xiCData_sym_pair Sy hD
  have hcq' : clipRaw S.G' (actField r q.1, actField r q.2) = rawOf (Sy.sym D) := by
    rw [clipRaw_act_pair Sy q, hcq, rawOf_sym_pair Sy D]
  rw [Jr.densM0_eq C hp₁ hle hD' hcq' (actField r g) (r x) i,
    Jr.densM0_eq C hp₁ hle hD hcq g x i]
  exact M0H_sym C Sy Sk hU hC hMX hdm hα hsm hcl hm hr hp₁ hD (hdom D hD) g x i

end MMain
end Balaban.Inhabited.StepSym
