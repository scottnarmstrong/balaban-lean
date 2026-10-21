/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.BaseFlat

/-!
# The canonical constants of the first step

The record of the first step (`BaseRaw`) carries the operator constants `cs`, the budget constants
`P`, the radii `R` and the geometry `geo` as data. LFR Definition II.1.1 fixes them: the running
constants of the operators are read from the small-field data `𝔰` of the step (`β_j`, `z_j`, `ν_j`,
and the derived `δ_j`, `p₀(β_j)`, the masses), the non-running ones are the outer constants, and
the radii are `R_j = R_base λ_j²` (Definition II.1.1, Lemma II.1.2). At the scale `1` there is no
predecessor, so these are the analogues of `succOpConsts`/`succBudgetConsts` (`Spine/LFStep.lean`)
with the read at every scale `j ≤ 1`.

This file defines these constants (`baseOpConsts`, `baseBudgetConsts`, `baseR`, `baseGeo`), proves
the coherence `Coh`, the field clauses and the operator bound (D5) for them, and states the spine
condition `BaseMap.Canonical` (the record uses them: typing data). With it the parts
`BaseConstsInput` and `BaseOpBoundInput` of `Spine/BasePre.lean` are theorems of the small-field
part `BaseSFInput` / `BaseFlatSFInput` and the prefix.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation
  Balaban.Localization Balaban.Background Balaban.Multiscale RegionHistory

namespace Balaban.RootFSpine

section Consts

variable {S : Setting} [NeZero S.L] {m₁ N : ℕ} {ϱ : ℝ}

/-- **The operator constants of the first step** (LFR §II.1.1, Definition II.1.1; the scale-`1`
analogue of `succOpConsts`, no predecessor). The running constants are read from the small-field
data `sf` at every scale: the coupling `β_j` (`beta`), the field renormalization `z_j` (`z`), the
dimensionless mass `ν_j` (`nu`); the tolerances `δ_j = (β_j a)^{-1/2} p₀(β_j)` (`delta`, Definition
II.1.1, P5 p. 498) and `p₀(β_j) = A₀ λ_j^{p₀}`, `λ_j = log(β_j a)` (`p0`, Definition II.1.1); the
cutoff mass `0` for `j ≤ k₀`, `ν_j L^{-2j}` above (`mu`, P5 (1.9)) and the background and action
masses `ν_j L^{-2j}` (`muBg`, `muAct`; ruling R2, P5 p. 490). The non-running constants are the
outer ones: the weights `a_n`, `C_ψ`, `a`, `C_b` (`aw`, `Cpsi`, `aKer`, `Cb`; Definition II.1.1) and
`B₀` (`B0`, the class constant of the bound (D7)). -/
noncomputable def baseOpConsts (S : Setting) [NeZero S.L] (k0 : ℕ) (A0 : ℝ) (cs₀ : OpConsts)
    (B0 : ℝ) (sf : SFData S.d S.L m₁ 1 N ϱ) : OpConsts where
  aw := cs₀.aw
  mu := bgMass k0 S.L sf.ν
  muBg := fun j => sf.ν j / (S.L : ℝ) ^ (2 * j)
  muAct := fun j => sf.ν j / (S.L : ℝ) ^ (2 * j)
  nu := sf.ν
  delta := deltaRun A0 S.p0 cs₀.aKer sf.β
  p0 := pZero A0 S.p0 cs₀.aKer sf.β
  Cpsi := cs₀.Cpsi
  beta := sf.β
  z := sf.z
  aKer := cs₀.aKer
  Cb := cs₀.Cb
  B0 := B0

/-- **The budget constants of the first step** (LFR Definition II.5.11, §I.5.3): `c₁, c₂, H₀` are
those of the prefix `PB`, the couplings are those of the small-field data (`H_j = H₀ log β_j`). -/
noncomputable def baseBudgetConsts {d L m₁ N : ℕ} [NeZero L] {ϱ : ℝ} (PB : BudgetConsts)
    (sf : SFData d L m₁ 1 N ϱ) : BudgetConsts where
  c1 := PB.c1
  c2 := PB.c2
  H0 := PB.H0
  beta := sf.β

/-- **The radii** `R_j = R_base λ_j²` (LFR Definition II.1.1, Lemma II.1.2) on the setting `S`
(the a priori sequence `λ̂_j` of `𝒮[d, T, β, a]`, D-IV.2). -/
noncomputable def baseR (S : Setting) (j : ℕ) : ℝ := S.Rb * S.lam j ^ 2

/-- **The geometry of the first step** (LFR Lemma II.1.2 (a), §I.1.2 row 6): the unit `M₁` and the
factor `c` of `M = c M₁` with `c ≥ 14` (the prefix), the radii `baseR S` nondecreasing and at least
`R_base` on a setting satisfying (H-λ) (`Setting.Ok`: `λ_j ≥ 1` nondecreasing). -/
def baseGeo (S : Setting) (hS : S.Ok) {M : ℕ} (M1 c : ℕ) [NeZero M1] [NeZero c] (hM : M = c * M1)
    (hc : 14 ≤ c) (n : ℕ → ℕ) : Geo S n (baseR S) M where
  M1 := M1
  c := c
  neM1 := inferInstance
  nec := inferInstance
  hM := hM
  hc := hc
  hRlow := fun j => by
    have h1 := hS.one_le_lam j
    have h2 : (1 : ℝ) ≤ S.lam j ^ 2 := one_le_pow₀ h1
    have h3 : 0 ≤ S.Rb := by linarith [hS.two_le_Rb]
    show S.Rb ≤ S.Rb * S.lam j ^ 2
    nlinarith
  hRmono := fun j => by
    apply Nat.floor_le_floor
    show S.Rb * S.lam (j - 1) ^ 2 ≤ S.Rb * S.lam j ^ 2
    have h1 := hS.lam_mono (show j - 1 ≤ j by omega)
    have h2 := hS.one_le_lam (j - 1)
    have h3 : 0 ≤ S.Rb := by linarith [hS.two_le_Rb]
    have h4 : S.lam (j - 1) ^ 2 ≤ S.lam j ^ 2 := by
      have : (0 : ℝ) ≤ S.lam (j - 1) := by linarith
      gcongr
    exact mul_le_mul_of_nonneg_left h4 h3

variable {R : ℕ → ℝ} {k0 M : ℕ} {P6 : Def6.Consts} {C7 : Consts7} {β ν : ℝ}
  {sf : SFData S.d S.L C7.m₁ 1 N ϱ}

/-- **`Coh` at the scale `1` for the canonical constants** (LFR §II.1, Definition II.1.1, D-IV.2,
D-IV.11): the running constants are read from `sf`, so the ties are definitional; what remains are
the typing ties (`M = S.M = L^{m₀+m₁}`, the a priori `λ̂_j` and `k₀ = kZero`) and the free flow of
`a_1` (`compWeight`). -/
theorem baseCoh (PB : BudgetConsts) (cs₀ : OpConsts) (hM : M = S.M)
    (hMp : M = S.L ^ (P6.m₀ + C7.m₁)) (hlam : ∀ j, S.lam j = lamHat S.d S.L β cs₀.aKer j)
    (hk0 : k0 = kZero S.d S.L β ν)
    (ha : ∀ j, 1 ≤ j → j ≤ 1 → sf.a j = compWeight S.L cs₀.aKer j) :
    Coh S (baseR S) k0 M (baseOpConsts S k0 C7.A0 cs₀ C7.B0 sf) (baseBudgetConsts PB sf) P6 C7 β ν
      1 sf where
  M_eq := hM
  M_pow := hMp
  lam_eq := hlam
  R_eq := fun _ => rfl
  k0_eq := hk0
  a_free := ha
  beta_cs := fun _ _ => rfl
  beta_P := fun _ _ => rfl
  z_cs := fun _ _ => rfl
  nu_cs := fun _ _ => rfl
  delta_cs := fun _ _ => rfl
  p0_cs := fun _ _ => rfl
  B0_cs := rfl

/-- **The field clauses at the scale `1` for the canonical constants** (ruling R2; LFR Definition
II.1.1): the masses are those of `sf`, the field is a unit vector. -/
theorem baseFieldClauses (cs₀ : OpConsts) (A0 B0 : ℝ) {hv : EuclideanSpace ℝ (Fin N)}
    (hh : ‖hv‖ = 1) :
    FieldClauses S k0 1 (baseOpConsts S k0 A0 cs₀ B0 sf) sf hv where
  h_unit := hh
  mu_eq := fun _ _ => rfl
  muBg_eq := fun _ _ => rfl
  muAct_eq := fun _ _ => rfl

/-- **(D5) at the scale `1` for the canonical constants** (LFR Lemma II.6.3 (a), "(D4) implies
(D5)", `Rep.opBound_of_data_le`): the step and kept data carry (S1)–(S3) by their types, so the
operators satisfy (1.26) once `z_1 > 0` and `β_0 a L^{d-2} ≥ 0`. -/
theorem baseOpBound {n : ℕ → ℕ} [∀ k, NeZero (n k)] {K : ℕ} [NeZero M]
    {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} (A0 B0 : ℝ) (cs₀ : OpConsts)
    (hcs : cs = baseOpConsts S k0 A0 cs₀ B0 sf)
    (hz : 0 < sf.z 1) (hβ : 0 ≤ sf.β 0) (ha : 0 ≤ cs₀.aKer)
    (rep : Rep S n R k0 K M N geo cs P 1) (top : ℕ) (hkK : 1 ≤ K) : D5Bound top hkK rep := by
  subst hcs
  refine rep.opBound_of_data_le (fun j hj => ?_) (fun j hj => ?_) top hkK
  · obtain rfl : j = 0 := by omega
    exact hz
  · obtain rfl : j = 0 := by omega
    exact mul_nonneg (mul_nonneg hβ ha) (by positivity)

end Consts

section Spine

/-- The geometry of the first step on every torus of the family: `baseGeo` at the setting
`𝒮[d, T, β, a]`. -/
noncomputable def baseGeoF (d : ℕ) (T : Typing) (β a : ℝ) [NeZero T.L] (kf : ℕ) (M1 c : ℕ)
    [NeZero M1] [NeZero c] (ok : (𝒮[d, T, β, a]).Ok) (hM : T.M = c * M1) (hc : 14 ≤ c) :
    ∀ (nK : ℕ) [NeZero nK], Geo 𝒮[d, T, β, a] (sides T.L (kf + 1) nK) (baseR 𝒮[d, T, β, a]) T.M :=
  fun nK _ => baseGeo 𝒮[d, T, β, a] ok M1 c hM hc (sides T.L (kf + 1) nK)

/-- **The data of the first step with the canonical constants**: the fields of `BaseRaw` except the
radii, the geometry and the operator and budget constants, which are those of LFR Definition II.1.1
(`baseR`, `baseGeo`, `baseOpConsts`, `baseBudgetConsts`) read from the small-field data `sf`; the
later fields are typed at them. The typing data `M = c M₁`, `c ≥ 14` and (H-λ) for the setting
(`Setting.Ok`) are carried (they are what `baseGeo` needs). -/
structure BaseRawC (d N : ℕ) (T : Typing) (C7 : Consts7) (ϱ β ν : ℝ) (kf : ℕ) (cs₀ : OpConsts)
    (PB : BudgetConsts) (M1 c : ℕ) [NeZero T.L] [NeZero T.M] where
  [neM1 : NeZero M1]
  [nec : NeZero c]
  ok : (𝒮[d, T, β, cs₀.aKer]).Ok
  hM : T.M = c * M1
  hc : 14 ≤ c
  z₁ : ℝ
  sf : SFData d T.L C7.m₁ 1 N ϱ
  κK : ∀ (nK : ℕ) [NeZero nK],
    ℕ → LocalHistory 𝒮[d, T, β, cs₀.aKer] (sides T.L (kf + 1) nK) T.M (kf + 1) → ℝ
  SD : ∀ (nK : ℕ) [NeZero nK], StepData (kZero d T.L β ν)
    (baseGeoF d T β cs₀.aKer kf M1 c ok hM hc nK)
    (baseOpConsts 𝒮[d, T, β, cs₀.aKer] (kZero d T.L β ν) C7.A0 cs₀ C7.B0 sf) N
    (kappaStepLoc (K := kf + 1) 𝒮[d, T, β, cs₀.aKer] (baseBudgetConsts PB sf) T.M)
  KD : ∀ (nK : ℕ) [NeZero nK], KeptData (kZero d T.L β ν)
    (baseGeoF d T β cs₀.aKer kf M1 c ok hM hc nK)
    (baseOpConsts 𝒮[d, T, β, cs₀.aKer] (kZero d T.L β ν) C7.A0 cs₀ C7.B0 sf) N (κK nK)
    (Setting.lam 𝒮[d, T, β, cs₀.aKer])
  KDgam : ∀ (nK : ℕ) [NeZero nK] (i : ℕ) (l : Fin 5), (KD nK).gam i l =
    Real.log 5 + (𝒮[d, T, β, cs₀.aKer]).A3' * (𝒮[d, T, β, cs₀.aKer]).lam i ^
      (𝒮[d, T, β, cs₀.aKer]).pR
  B : ∀ (nK : ℕ) [NeZero nK], BTerms 𝒮[d, T, β, cs₀.aKer] (sides T.L (kf + 1) nK)
    (baseR 𝒮[d, T, β, cs₀.aKer]) (kZero d T.L β ν) (kf + 1) T.M N 1
  St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d T.L N₁ C7.m₁ 1 N
  vc : CorrCoef d
  Ev : ℕ → ℝ

/-- The record of `BaseRaw` of a record with the canonical constants. -/
noncomputable def BaseRawC.toRaw {d N : ℕ} {T : Typing} {C7 : Consts7} {ϱ β ν : ℝ} {kf : ℕ}
    {cs₀ : OpConsts} {PB : BudgetConsts} {M1 c : ℕ} [NeZero T.L] [NeZero T.M]
    (Γ : BaseRawC d N T C7 ϱ β ν kf cs₀ PB M1 c) : BaseRaw d N T C7 ϱ β ν kf cs₀.aKer where
  z₁ := Γ.z₁
  R := baseR 𝒮[d, T, β, cs₀.aKer]
  geo := haveI := Γ.neM1; haveI := Γ.nec; baseGeoF d T β cs₀.aKer kf M1 c Γ.ok Γ.hM Γ.hc
  cs := baseOpConsts 𝒮[d, T, β, cs₀.aKer] (kZero d T.L β ν) C7.A0 cs₀ C7.B0 Γ.sf
  P := baseBudgetConsts PB Γ.sf
  sf := Γ.sf
  κK := Γ.κK
  SD := Γ.SD
  KD := Γ.KD
  KDgam := Γ.KDgam
  B := Γ.B
  St := Γ.St
  vc := Γ.vc
  Ev := Γ.Ev

variable {d N : ℕ} {T : ℝ → ℝ → Typing} {P6 : ℝ → ℝ → Def6.Consts}
  {C7 : ℝ → ℝ → Consts7} {PB : ℝ → ℝ → BudgetConsts} {cs₀ : ℝ → ℝ → OpConsts}
  {M1 c : ℝ → ℝ → ℕ} {rH ϱ : ℝ → ℝ → ℝ}

/-- **The first-step map with the canonical constants** (a parameter of the sub-spine, defined by
the provider). -/
abbrev BaseMapC (d N : ℕ) (T : ℝ → ℝ → Typing) (C7 : ℝ → ℝ → Consts7)
    (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts) (M1 c : ℝ → ℝ → ℕ)
    (ϱ : ℝ → ℝ → ℝ) :=
  ∀ (κ c₉ β ν : ℝ) (_ : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
    [NeZero (T κ c₉).M], BaseRawC d N (T κ c₉) (C7 κ c₉) (ϱ κ c₉) β ν kf (cs₀ κ c₉) (PB κ c₉)
      (M1 κ c₉) (c κ c₉)

/-- The first-step map (`BaseMap`) of a map with the canonical constants. -/
noncomputable def BaseMapC.toMap (Γ : BaseMapC d N T C7 PB cs₀ M1 c ϱ) : BaseMap d N T C7 cs₀ ϱ :=
  fun κ c₉ β ν h kf _ _ => (Γ κ c₉ β ν h kf).toRaw

/-- The part of the small-field input that the bookkeeping reads: the free flow of `a_1`,
`β_0 = β`, `z₁ > 0` and `z_1 = z₁`. -/
def BaseSFCore (d N : ℕ) (T : ℝ → ℝ → Typing) (C7 : ℝ → ℝ → Consts7) (cs₀ : ℝ → ℝ → OpConsts)
    (ϱ : ℝ → ℝ → ℝ) (Reg : ℕ → Prop) (Γ : BaseMap d N T C7 cs₀ ϱ) : Prop :=
  BaseImageInput d N T C7 cs₀ ϱ Reg Γ fun κ c₉ β _ _ _ _ _ Γ =>
    (∀ j, 1 ≤ j → j ≤ 1 → Γ.sf.a j = compWeight (T κ c₉).L (cs₀ κ c₉).aKer j) ∧
    Γ.sf.β 0 = β ∧ 0 < Γ.z₁ ∧ Γ.sf.z 1 = Γ.z₁

theorem BaseSFInput.core {Reg : ℕ → Prop} {Γ : BaseMap d N T C7 cs₀ ϱ}
    (hS : BaseSFInput d N T P6 C7 cs₀ ϱ Reg Γ) : BaseSFCore d N T C7 cs₀ ϱ Reg Γ := by
  intro κ hκ c₉ hc₉
  obtain ⟨b, hb⟩ := hS κ hκ c₉ hc₉
  refine ⟨b, fun β hβ ν hν hνL h hh kf hkf _ _ hreg => ?_⟩
  obtain ⟨_, _, _, ha, hb0, _, _, hz, hz1⟩ := hb β hβ ν hν hνL h hh kf hkf hreg
  exact ⟨ha, hb0, hz, hz1⟩

theorem BaseFlatSFInput.core {Γ : BaseMap d N T C7 cs₀ ϱ}
    (hS : BaseFlatSFInput d N T P6 C7 cs₀ ϱ Γ) :
    BaseSFCore d N T C7 cs₀ ϱ (fun k => k = 0) Γ := by
  intro κ hκ c₉ hc₉
  obtain ⟨b, hb⟩ := hS κ hκ c₉ hc₉
  refine ⟨b, fun β hβ ν hν hνL h hh kf hkf _ _ hreg => ?_⟩
  obtain ⟨_, _, _, ha, hb0, _, _, hz, hz1⟩ := hb β hβ ν hν hνL h hh kf hkf hreg
  exact ⟨ha, hb0, hz, hz1⟩

/-- **`BaseConstsInput` for a map with the canonical constants** (LFR Definition II.1.1): the ties
of the constants are definitional, `Coh` is `baseCoh`, the field clauses are `baseFieldClauses`;
the typing fact `M = L^{m₀+m₁}` is that of the prefix. -/
theorem baseConstsInput_of_core {δ : ℝ} {Reg : ℕ → Prop}
    (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ) (Γ : BaseMapC d N T C7 PB cs₀ M1 c ϱ)
    (hS : BaseSFCore d N T C7 cs₀ ϱ Reg Γ.toMap) :
    BaseConstsInput d N T P6 C7 PB cs₀ M1 c ϱ Reg Γ.toMap := by
  intro κ hκ c₉ hc₉
  obtain ⟨b, hb⟩ := hS κ hκ c₉ hc₉
  obtain ⟨_, _, _, _, _, _, _, hMp, _⟩ := hP κ hκ c₉ hc₉
  refine ⟨b, fun β hβ ν hν hνL h hh kf hkf _ _ hreg => ?_⟩
  obtain ⟨ha, -, -, -⟩ := hb β hβ ν hν hνL h hh kf hkf hreg
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact baseCoh (PB κ c₉) (cs₀ κ c₉) rfl hMp (fun j => rfl) rfl ha
  · exact baseFieldClauses _ _ _ hh

/-- **`BaseOpBoundInput` for a map with the canonical constants** (LFR Lemma II.6.3 (a),
`baseOpBound`): `z_1 = z₁ > 0` and `β_0 = β ≥ 1`, `a > 1` (prefix). -/
theorem baseOpBoundInput_of_core {δ : ℝ} (r : ℕ) {Reg : ℕ → Prop}
    (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ) (Γ : BaseMapC d N T C7 PB cs₀ M1 c ϱ)
    (hS : BaseSFCore d N T C7 cs₀ ϱ Reg Γ.toMap) :
    BaseOpBoundInput d N T C7 cs₀ ϱ r Reg Γ.toMap := by
  intro κ hκ c₉ hc₉
  obtain ⟨b, hb⟩ := hS κ hκ c₉ hc₉
  obtain ⟨_, ha1, _⟩ := hP κ hκ c₉ hc₉
  refine ⟨max b 1, fun β hβ ν hν hνL h hh kf hkf _ _ hreg nK _ => ?_⟩
  obtain ⟨-, hb0, hz, hz1⟩ := hb β (le_of_max_le_left hβ) ν hν hνL h hh kf hkf hreg
  exact baseOpBound _ _ _ rfl (lt_of_lt_of_eq hz hz1.symm)
    (le_trans (by linarith [le_of_max_le_right hβ]) hb0.symm.le) (by linarith)
    (((Γ.toMap κ c₉ β ν h kf).famR r).lf nK) r _

/-- `BaseConstsInput` from `BaseSFInput` and the canonical constants. -/
theorem baseConstsInput_of_sf {δ : ℝ} {Reg : ℕ → Prop}
    (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ) (Γ : BaseMapC d N T C7 PB cs₀ M1 c ϱ)
    (hS : BaseSFInput d N T P6 C7 cs₀ ϱ Reg Γ.toMap) :
    BaseConstsInput d N T P6 C7 PB cs₀ M1 c ϱ Reg Γ.toMap :=
  baseConstsInput_of_core hP Γ hS.core

/-- `BaseConstsInput` (regime (B)) from `BaseFlatSFInput` and the canonical constants. -/
theorem baseConstsInput_of_flatSF {δ : ℝ} (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (Γ : BaseMapC d N T C7 PB cs₀ M1 c ϱ) (hS : BaseFlatSFInput d N T P6 C7 cs₀ ϱ Γ.toMap) :
    BaseConstsInput d N T P6 C7 PB cs₀ M1 c ϱ (fun k => k = 0) Γ.toMap :=
  baseConstsInput_of_core hP Γ hS.core

/-- `BaseOpBoundInput 1` (regime (A)) from `BaseSFInput` and the canonical constants. -/
theorem baseOpBoundInput_of_sf {δ : ℝ} (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (Γ : BaseMapC d N T C7 PB cs₀ M1 c ϱ)
    (hS : BaseSFInput d N T P6 C7 cs₀ ϱ (fun k => 1 ≤ k) Γ.toMap) :
    BaseOpBoundInput d N T C7 cs₀ ϱ 1 (fun k => 1 ≤ k) Γ.toMap :=
  baseOpBoundInput_of_core 1 hP Γ hS.core

/-- `BaseOpBoundInput 2` (regime (B)) from `BaseFlatSFInput` and the canonical constants. -/
theorem baseOpBoundInput_of_flatSF {δ : ℝ} (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (Γ : BaseMapC d N T C7 PB cs₀ M1 c ϱ) (hS : BaseFlatSFInput d N T P6 C7 cs₀ ϱ Γ.toMap) :
    BaseOpBoundInput d N T C7 cs₀ ϱ 2 (fun k => k = 0) Γ.toMap :=
  baseOpBoundInput_of_core 2 hP Γ hS.core

/-- **The first step in regime (A) from its parts, with the canonical constants**: the landed
assembly `basePreStepInput_of_parts` with `BaseConstsInput` and `BaseOpBoundInput 1` derived. -/
theorem basePreStepInput_of_canonical {δ : ℝ} (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (Γ : BaseMapC d N T C7 PB cs₀ M1 c ϱ)
    (hS : BaseSFInput d N T P6 C7 cs₀ ϱ (fun k => 1 ≤ k) Γ.toMap)
    (hCo : BaseCorrInput d N T P6 C7 cs₀ ϱ (fun k => 1 ≤ k) Γ.toMap)
    (hF : BaseFormInput d N T P6 C7 cs₀ ϱ (fun k => 1 ≤ k) Γ.toMap)
    (hB : BaseBdryInput d N T P6 C7 cs₀ rH ϱ (fun k => 1 ≤ k) Γ.toMap)
    (hCh : BaseCoherenceInput d N T C7 cs₀ ϱ 1 (fun k => 1 ≤ k) Γ.toMap)
    (hV : BaseVacuumInput d N T C7 cs₀ ϱ (fun k => 1 ≤ k) Γ.toMap) :
    BasePreStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ :=
  basePreStepInput_of_parts hP Γ.toMap hS (baseConstsInput_of_sf hP Γ hS) hCo hF hB
    (baseOpBoundInput_of_sf hP Γ hS) hCh hV

/-- **The first step in regime (B) from its parts, with the canonical constants**: the landed
assembly `baseFlatStepInput_of_parts` with `BaseConstsInput` and `BaseOpBoundInput 2` derived. -/
theorem baseFlatStepInput_of_canonical {δ : ℝ} (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (Γ : BaseMapC d N T C7 PB cs₀ M1 c ϱ) (hS : BaseFlatSFInput d N T P6 C7 cs₀ ϱ Γ.toMap)
    (hCo : BaseCorrInput d N T P6 C7 cs₀ ϱ (fun k => k = 0) Γ.toMap)
    (hF : BaseFlatFormInput d N T P6 C7 cs₀ ϱ Γ.toMap)
    (hB : BaseFlatBdryInput d N T P6 C7 cs₀ rH ϱ Γ.toMap)
    (hCh : BaseCoherenceInput d N T C7 cs₀ ϱ 2 (fun k => k = 0) Γ.toMap) :
    BaseFlatStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ :=
  baseFlatStepInput_of_parts hP Γ.toMap hS (baseConstsInput_of_flatSF hP Γ hS) hCo hF hB
    (baseOpBoundInput_of_flatSF hP Γ hS) hCh

end Spine

end Balaban.RootFSpine
