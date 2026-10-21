/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.BaseConstsWitness
public import Balaban.Spine.BaseStepDataSplice
public import Balaban.Inhabited.QuietImage

/-!
# `BaseRawC` is inhabited at the horizon `kf = 1` (rule 10)

The first-step record `BaseRawC` of `Spine/BaseConsts.lean` carries step data at every scale
`k < K = kf + 1`. At `kf = 1` (`K = 2`) the scale `1` is a quiet step; the step data are the
splice (`StepData.ofZeroSliceQuiet`) of the zero slice at the scale `0` and the quiet step data of
the scale `1` (`quietStepData'`, on the tori of the family, `quietStepInput'_nonempty_sides`).

The configuration is the witness of `Spine/Witness.lean` (`d = L = 3`, `N = 2`, `ν = ν₀`,
`k₀ = 1`) with the block constant `M = 27 M₁`, `M₁ = ⌈R₀(3, 3)⌉ + 1` (so that the separation
`5 L M₁` of the generating sets is at least the background radius `R₀(3, 3)`, the hypothesis
`BgHyp` of the quiet kernel), the small-field data with the couplings `β_j = 1` and the masses
`ν_j = 1/2`, and the constant `A₀ > 0` of the tolerances `δ_j = A₀ β_j^{-1/2}(log β_j a)^{p₀}`
small enough that the characteristic functions are admissible (`3 d L δ_j ≤ 1/2`).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7.Wit
  Balaban.LargeField.Def7v2 Balaban.LargeField.Def7v2.Wit Balaban.SmallField Balaban.Background
  Balaban.Multiscale RegionHistory

namespace Balaban.RootFSpine

section General

variable {S : Setting} [NeZero S.L] {m₁ N : ℕ} {ϱ : ℝ}

/-- The cutoff mass of `baseOpConsts` is admissible for the background theory when the masses
`ν_j` lie in `[0, 1]`. -/
theorem baseOpConsts_bgHyp_mu (k0 : ℕ) (A0 : ℝ) (cs₀ : OpConsts) (B0 : ℝ)
    (sf : SFData S.d S.L m₁ 1 N ϱ) (hν0 : ∀ j, 0 ≤ sf.ν j) (hν1 : ∀ j, sf.ν j ≤ 1)
    (hd : 3 ≤ S.d) (hL : 3 ≤ S.L) (M1 : ℕ) (hϱ : bgR0 S.d S.L ≤ minSep S.L M1)
    (haw : ∀ j, cs₀.aw j ∈ Set.Icc (1 / 2 : ℝ) 2) (q : ℕ) :
    BgHyp S.d S.L q (minSep S.L M1) (baseOpConsts S k0 A0 cs₀ B0 sf).aw
      ((baseOpConsts S k0 A0 cs₀ B0 sf).mu q) := by
  have hLpos : (0 : ℝ) < (S.L : ℝ) := by exact_mod_cast (by omega : 0 < S.L)
  refine ⟨hd, hL, hϱ, fun j _ _ => haw j, ?_, ?_⟩
  · show 0 ≤ bgMass k0 S.L sf.ν q
    unfold bgMass
    split_ifs
    · exact le_rfl
    · have := hν0 q; positivity
  · show bgMass k0 S.L sf.ν q * ((S.L : ℝ) ^ q) ^ 2 ≤ 1
    unfold bgMass
    split_ifs
    · simp
    · rw [← pow_mul, mul_comm q 2, div_mul_cancel₀ _ (by positivity)]
      exact hν1 q

/-- The background mass of `baseOpConsts` is admissible for the background theory when the masses
`ν_j` lie in `[0, 1]`. -/
theorem baseOpConsts_bgHyp_muBg (k0 : ℕ) (A0 : ℝ) (cs₀ : OpConsts) (B0 : ℝ)
    (sf : SFData S.d S.L m₁ 1 N ϱ) (hν0 : ∀ j, 0 ≤ sf.ν j) (hν1 : ∀ j, sf.ν j ≤ 1)
    (hd : 3 ≤ S.d) (hL : 3 ≤ S.L) (M1 : ℕ) (hϱ : bgR0 S.d S.L ≤ minSep S.L M1)
    (haw : ∀ j, cs₀.aw j ∈ Set.Icc (1 / 2 : ℝ) 2) (q : ℕ) :
    BgHyp S.d S.L q (minSep S.L M1) (baseOpConsts S k0 A0 cs₀ B0 sf).aw
      ((baseOpConsts S k0 A0 cs₀ B0 sf).muBg q) := by
  have hLpos : (0 : ℝ) < (S.L : ℝ) := by exact_mod_cast (by omega : 0 < S.L)
  refine ⟨hd, hL, hϱ, fun j _ _ => haw j, ?_, ?_⟩
  · show 0 ≤ sf.ν q / (S.L : ℝ) ^ (2 * q)
    have := hν0 q; positivity
  · show sf.ν q / (S.L : ℝ) ^ (2 * q) * ((S.L : ℝ) ^ q) ^ 2 ≤ 1
    rw [← pow_mul, mul_comm q 2, div_mul_cancel₀ _ (by positivity)]
    exact hν1 q

end General


namespace BaseWitK

/-- `M₁ = ⌈R₀(3,3)⌉ + 1`. -/
noncomputable def M1 : ℕ := ⌈bgR0 3 3⌉₊ + 1

instance : NeZero M1 := ⟨Nat.succ_ne_zero _⟩

theorem bgR0_le_minSep : bgR0 3 3 ≤ minSep 3 M1 := by
  unfold minSep M1
  have h1 : bgR0 3 3 ≤ (⌈bgR0 3 3⌉₊ : ℝ) := Nat.le_ceil _
  push_cast
  have : (0 : ℝ) ≤ (⌈bgR0 3 3⌉₊ : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- The typing of the witness with the block constant `M = 27 M₁`. -/
noncomputable def typ : Typing := { typing with M := 27 * M1 }

instance : NeZero typ.L := ⟨by show (3 : ℕ) ≠ 0; norm_num⟩
instance : NeZero typ.M := ⟨by show 27 * M1 ≠ 0; exact Nat.mul_ne_zero (by norm_num) (NeZero.ne _)⟩

/-- The outer operator constants of the witness, with the weights `a_n ≡ 1`. -/
noncomputable def cs0 : OpConsts := { wCs wν₀ (kZero 3 3 wβ wν₀) with aw := fun _ => 1 }

theorem cs0_aKer : cs0.aKer = 5 / 4 := rfl

/-- `δ₀ = 1/(54 (1 + c_shell))`. -/
noncomputable def δ0 : ℝ := 1 / (54 * (1 + cShell 2))

theorem cShell_nonneg (N : ℕ) : 0 ≤ cShell N := by
  unfold cShell
  have := ENNReal.toReal_nonneg (a := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1))
  positivity

theorem δ0_pos : 0 < δ0 := by
  have := cShell_nonneg 2
  unfold δ0; positivity

/-- The constant `K_c` with `δ_j = A₀ K_c` at the couplings `β_j = 1`. -/
noncomputable def Kc : ℝ := ((1 : ℝ) * (5 / 4)) ^ (-(1 / 2 : ℝ)) * Real.log (1 * (5 / 4)) ^ typing.p0

theorem Kc_pos : 0 < Kc := by
  unfold Kc
  have : 0 < Real.log (1 * (5 / 4) : ℝ) := Real.log_pos (by norm_num)
  positivity

/-- The Def-7 constants of the witness with `A₀ = δ₀ / K_c > 0`. -/
noncomputable def c7 : Consts7 := { wC7 with A0 := δ0 / Kc }

/-- The small-field data of the witness configuration: couplings `1`, masses `1/2`, `z ≡ 1`. -/
noncomputable def sf : SFData 3 typ.L c7.m₁ 1 2 (bgR0 3 3) :=
  { wSF2 wν₀ wC7.m₁ with β := fun _ => 1, ν := fun _ => 1 / 2, z := fun _ => 1 }


/-- The setting of the witness configuration. -/
noncomputable abbrev S : Setting := 𝒮[3, typ, wβ, cs0.aKer]

/-- The operator constants of the first step at the witness configuration. -/
noncomputable abbrev cs : OpConsts := baseOpConsts S (kZero 3 typ.L wβ wν₀) c7.A0 cs0 c7.B0 sf

theorem ok : S.Ok := by
  have h : (𝒮[3, typing, wβ, (wCs wν₀ (kZero 3 3 wβ wν₀)).aKer]).Ok := spineSetting_eq_wS ▸ wS_ok
  exact { h with one_le_M := by show 1 ≤ 27 * M1; have := NeZero.pos M1; omega }

theorem cs_delta (k : ℕ) : cs.delta k = δ0 := by
  have hK := Kc_pos.ne'
  show deltaRun c7.A0 S.p0 cs0.aKer (fun _ => 1) k = δ0
  simp only [deltaRun, pZero, runLam]
  show ((1 : ℝ) * (5 / 4)) ^ (-(1 / 2 : ℝ)) * (δ0 / Kc * Real.log (1 * (5 / 4)) ^ typing.p0) = δ0
  unfold Kc
  have h1 : ((1 : ℝ) * (5 / 4)) ^ (-(1 / 2 : ℝ)) ≠ 0 := by positivity
  have h2 : Real.log (1 * (5 / 4) : ℝ) ^ typing.p0 ≠ 0 := by
    have : 0 < Real.log (1 * (5 / 4) : ℝ) := Real.log_pos (by norm_num)
    positivity
  field_simp


theorem haw : ∀ j, cs0.aw j ∈ Set.Icc (1 / 2 : ℝ) 2 := fun _ => ⟨by show (1 / 2 : ℝ) ≤ 1; norm_num, by show (1 : ℝ) ≤ 2; norm_num⟩

theorem δ0_le : 3 * ((S.d : ℕ) : ℝ) * ((S.L : ℕ) : ℝ) * δ0 ≤ 1 / 2 := by
  show 3 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) * δ0 ≤ 1 / 2
  have := cShell_nonneg 2
  unfold δ0
  rw [mul_one_div, div_le_iff₀ (by positivity)]
  push_cast
  nlinarith

theorem δ0_le' : 3 * ((S.d : ℕ) : ℝ) * ((S.L : ℕ) : ℝ) * cShell 2 * δ0 ≤ 1 / 2 := by
  show 3 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) * cShell 2 * δ0 ≤ 1 / 2
  have := cShell_nonneg 2
  unfold δ0
  rw [mul_one_div, div_le_iff₀ (by positivity)]
  push_cast
  nlinarith

theorem hCb : cs.Cb = 0 := rfl

theorem hlogβ : ∀ k, 0 ≤ Real.log (cs.beta k) := fun k => by
  show 0 ≤ Real.log 1
  simp

/-- The step data of the witness configuration on every torus of the family. -/
noncomputable def SD (nK : ℕ) [NeZero nK] :
    StepData (kZero 3 typ.L wβ wν₀) (baseGeoF 3 typ wβ cs0.aKer 1 M1 27 ok rfl (by norm_num) nK) cs
      2 (kappaStepLoc (K := 1 + 1) S (baseBudgetConsts (budgetConsts wβ) sf) typ.M) :=
  StepData.ofZeroSliceQuiet (baseBudgetConsts (budgetConsts wβ) sf) le_rfl le_rfl
    (fun k => by show 0 ≤ Real.log 1; simp)
    (StepSlice0.zero _ cs hCb _)
    (quietStepInput'_nonempty_sides (by have := kZero_wν₀; show kZero 3 3 wβ wν₀ ≤ 1 + 1; omega) _
      cs 2 (le_of_eq hCb) (by show (0 : ℝ) ≤ 1; norm_num) hlogβ).some
    (fun _ => by show (0 : ℝ) ≤ 1; norm_num)
    (fun k => by show (0 : ℝ) ≤ 1 * (5 / 4) * ((3 : ℕ) : ℝ) ^ (3 - 2); norm_num)
    (fun _ => by show (0 : ℝ) ≤ 1; norm_num)
    (fun _ => by show (0 : ℝ) ≤ 1; norm_num)
    (fun k => by show (0 : ℝ) ≤ 1 / 2 / ((3 : ℕ) : ℝ) ^ (2 * (k + 1)); positivity)
    (baseOpConsts_bgHyp_mu _ _ _ _ _ (fun _ => by show (0 : ℝ) ≤ 1 / 2; norm_num) (fun _ => by show (1 / 2 : ℝ) ≤ 1; norm_num)
      le_rfl (by show 3 ≤ 3; norm_num) M1 bgR0_le_minSep haw)
    (baseOpConsts_bgHyp_muBg _ _ _ _ _ (fun _ => by show (0 : ℝ) ≤ 1 / 2; norm_num) (fun _ => by show (1 / 2 : ℝ) ≤ 1; norm_num)
      le_rfl (by show 3 ≤ 3; norm_num) M1 bgR0_le_minSep haw)
    le_rfl (le_of_eq hCb) (by show (0 : ℝ) * 1 ≤ 0; norm_num) hlogβ
    (fun k => by show (0 : ℝ) < 1 * (5 / 4) * ((3 : ℕ) : ℝ) ^ (3 - 2); norm_num)
    (fun k => by rw [cs_delta]; exact δ0_pos) (fun k => by rw [cs_delta]; exact δ0_le)
    (fun k => by rw [cs_delta]; exact δ0_le') (le_of_eq hCb.symm) (by show (0 : ℝ) ≤ 1; norm_num)


end BaseWitK

/-- **`BaseRawC` is inhabited at the horizon `kf = 1`** (rule 10; `K = 2`, one quiet step): the
witness configuration with the block constant `M = 27 M₁`, the zero slice at the scale `0` and the
quiet step data at the scale `1` (`StepData.ofZeroSliceQuiet`), `baseKD`, zero boundary terms. -/
theorem baseRawC_nonempty_kf_one :
    Nonempty (BaseRawC 3 2 BaseWitK.typ BaseWitK.c7 (bgR0 3 3) wβ wν₀ 1 BaseWitK.cs0
      (budgetConsts wβ) BaseWitK.M1 27) :=
  ⟨{ ok := BaseWitK.ok
     hM := rfl
     hc := by norm_num
     z₁ := 1
     sf := BaseWitK.sf
     κK := fun _ _ => kappaStepLoc (K := 1 + 1) _ (baseBudgetConsts (budgetConsts wβ) BaseWitK.sf)
       BaseWitK.typ.M
     SD := fun nK _ => BaseWitK.SD nK
     KD := fun _ _ => baseKD _ _ _
     KDgam := fun _ _ i l => baseKD_gam _ _ _ i l
     B := fun _ _ _ _ _ _ _ => 0
     St := wSt wν₀
     vc := wVc
     Ev := fun _ => 0 }⟩

end Balaban.RootFSpine
