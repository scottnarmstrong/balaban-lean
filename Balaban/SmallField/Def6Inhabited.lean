/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6BridgeInfMoment
public import Balaban.SmallField.Def6BridgeLift
public import Balaban.Localization.DecoupledBackground
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity


/-!
# Members of the small-field class `IsSFFamily` at positive scale

`d = L = 3`, `N = 2`, any `m₁`, `ϱ ≥ R₀(3, 3)`, `1 ≤ j ≤ k`.  The effective action is zero
(`zeroTerms`: `ℰ = ℳ = 0`, `𝔹_j(X)` the whole-lattice generating set of level `j`); the constants are
`γ = α₁ = 1/4`, `κ = a_ent + 4`, `E₀ = 0`, `c₉ = 1`, `B = 0`, `ν̄ = 7/72`, `m₀ = 0`, `α₀` chosen so that
`ε_j` meets the bound of `MomNum.hsmall`; the running coefficients are those of the flow with
`ξ = 0` (`β_n = 3^n`, `ν_n = (7/72) 9^{n-k}`, `a_n = 5/4`).

* `isSFFamily_witness`: every field of `IsSFFamily` (`CoeffBounds`, `TorusIndep`, `RenormCond` at
  every `j ≤ k`, and per torus `IsSF` including `pavingGS`, `eucEloc`, `eucMloc`);
* `momNum_witness`: `MomNum`;
* `BridgeInfWitness`, `nonempty_bridgeInfWitness`: the hypotheses of `IsSFFamily.bridgeInf`
  (class member, `MomNum`, `i₀ ≠ i₁`, `RepresentsInf`), and `BridgeInfWitness.liftCtx`: the
  `LiftCtx` of the same class member on every torus (radius `liftRadius`).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Topology

section Zero

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The zero effective action: `ℰ = ℳ = 0`, `𝔹_j(X) = ` the whole-lattice generating set of level
`j` (the top one outside `j ≤ k`). -/
noncomputable def zeroTerms (d L N₁ m₁ k N : ℕ) [NeZero L] [NeZero N₁] (ϱ : ℝ) :
    Terms d L N₁ m₁ k N ϱ where
  E := fun _ _ _ _ _ => 0
  M := fun _ _ _ _ _ _ => 0
  gs := fun j _ => if h : j ≤ k then levelGS j h else topGS d L N₁ m₁ k ϱ

theorem zeroTerms_gs {j : ℕ} (hjk : j ≤ k) (X : Set (CTorus d L N₁ m₁ k)) :
    (zeroTerms d L N₁ m₁ k N ϱ).gs j X = levelGS j hjk := by
  simp [zeroTerms, hjk]

theorem Eloc_zero (m₀ j : ℕ) (y : CTorus d L N₁ m₁ k) (ψ h : Fld d L N₁ m₁ k N) :
    Eloc m₀ (zeroTerms d L N₁ m₁ k N ϱ) j y ψ h = 0 := by
  simp [Eloc, zeroTerms]

theorem Mloc_zero (m₀ j : ℕ) (x : CTorus d L N₁ m₁ k) (ψ h g : Fld d L N₁ m₁ k N) :
    Mloc m₀ (zeroTerms d L N₁ m₁ k N ϱ) j x ψ h g = 0 := by
  simp [Mloc, zeroTerms]

theorem Edens_zero (m₀ j : ℕ) (ψ h : Fld d L N₁ m₁ k N) :
    Edens m₀ (zeroTerms d L N₁ m₁ k N ϱ) j ψ h = 0 := by
  simp [Edens, Eloc_zero]

theorem isSF_zero (P : Consts) (β ν a : ℕ → ℝ) (hE₀ : P.E₀ = 0) (hc₉ : 0 < P.c₉)
    (hp : ∀ x, P.p x ≤ 0) :
    IsSF P β ν a (zeroTerms d L N₁ m₁ k N ϱ) (fun _ _ _ => 0) 0 where
  density := by
    intro Ψ₀ h₀ g D _ _
    have hXi : ¬ Xi (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) k 1
        (P.p (β k) / Real.sqrt (β k)) Ψ₀ h₀ := fun h =>
      absurd h.2.1 (not_lt.2 (div_nonpos_of_nonpos_of_nonneg (hp _) (Real.sqrt_nonneg _)))
    simp [hXi]
  gs_spec := by
    intro j hj1 hjk X _
    rw [zeroTerms_gs hjk]
    refine ⟨?_, ?_⟩
    · intro x _
      simp [levelGS, hj1]
    · intro i hi
      have : ¬ i ≤ j := by omega
      simp [levelGS, this]
  analyticE := fun j _ _ y X _ _ => by
    exact analyticOnNhd_const
  analyticM := fun j _ _ x X _ _ => analyticOnNhd_const
  rotE := by intros; rfl
  pavingGS := by
    intro j hj1 hjk X _ r _ i
    rw [zeroTerms_gs hjk, zeroTerms_gs hjk]
    by_cases hi : i ≤ j <;> simp [levelGS, hi]
  eucE := by intros; rfl
  eucEloc := by
    intro j _ hjk y r _ Ψ h _ _
    rw [Eloc_zero, Eloc_zero]
  rotM := by
    intro j _ _ x X _ _ R _ Ψ h g _ _
    simp [zeroTerms]
  eucM := by intros; rfl
  eucMloc := by
    intro j _ hjk x r _ Ψ h g _ _
    rw [Mloc_zero, Mloc_zero]
  localE := by intros; rfl
  localM := by intros; rfl
  boundE := by
    intro j _ _ y X _ _ Ψ h _
    simp [zeroTerms, hE₀]
  boundM := by
    intro j _ _ x X _ _ Ψ h g _ _
    simp only [zeroTerms]
    have : vn (0 : Fin N → ℂ) = 0 := by simp [vn]
    rw [this]
    have hL : (0:ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have h1 : (0:ℝ) < ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) :=
      Real.rpow_pos_of_pos (by positivity) _
    positivity


/-- The zero family over all tori. -/
noncomputable abbrev zeroFam (d L m₁ k N : ℕ) [NeZero L] (ϱ : ℝ) :
    ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ := fun N₁ _ => zeroTerms d L N₁ m₁ k N ϱ

theorem torusIndep_zero (m₀ : ℕ) : TorusIndep (d := d) (L := L) (m₁ := m₁) (k := k) (N := N)
    (ϱ := ϱ) m₀ (zeroFam d L m₁ k N ϱ) where
  E_eq := by intros; rfl

theorem Einf_zero (m₀ j : ℕ) (y : Fin d → ℤ) (X' : Finset (Fin d → ℤ)) (ψ h : InfFld d N) :
    Einf m₀ (zeroFam d L m₁ k N ϱ) j y X' ψ h = 0 := by
  unfold Einf
  exact stabVal_eq (Filter.Eventually.of_forall fun n => rfl)

theorem ElocInf_zero (m₀ j : ℕ) (y : Fin d → ℤ) (ψ h : InfFld d N) :
    ElocInf m₀ (zeroFam d L m₁ k N ϱ) j y ψ h = 0 := by
  unfold ElocInf
  simp [Einf_zero]

theorem renormCond_zero (m₀ k' : ℕ) (νk : ℝ) (j : ℕ) :
    RenormCond (d := d) (L := L) (m₁ := m₁) (N := N) (ϱ := ϱ) m₀ k' νk
      (zeroFam d L m₁ k' N ϱ) j where
  val := fun i₀ => ElocInf_zero _ _ _ _ _
  dh := by
    intro i₀ _
    simp [ElocInf_zero]
  dpsi := by
    intro i₀
    simp [ElocInf_zero]
  moment := by
    intro i₀ i₁ _
    have : ∀ n : ℕ, (haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      momentSum m₀ (zeroFam d L m₁ k' N ϱ (n + 1)) j i₀ i₁) = 0 := by
      intro n
      have hD : ∀ (c v w : Fld d L (n + 1) m₁ k' N),
          D2 (fun ψ : Fld d L (n + 1) m₁ k' N => (0 : ℂ)) c v w = 0 := by
        intro c v w; simp [D2]
      simp [momentSum, Edens_zero, hD]
    simp only [this]
    exact tendsto_const_nhds

end Zero

/-! ### The constants and the coefficient sequences at `d = L = 3`, `N = 2` -/

section Const

theorem betaSeq_zero (L : ℝ) (d : ℕ) (β : ℂ) (n : ℕ) :
    Flow.betaSeq L d (fun _ => 0) β n = β * (L : ℂ) ^ (n * (d - 2)) := by
  rw [Flow.betaSeq_eq]; simp [Flow.gammaSeq]

theorem nuSeq_zero (L : ℝ) (ν : ℂ) (n : ℕ) :
    Flow.nuSeq L (fun _ => 0) ν n = ν * (L : ℂ) ^ (2 * n) := by
  induction n with
  | zero => simp [Flow.nuSeq]
  | succ n ih => simp [Flow.nuSeq, ih]; ring

/-- The constants of the witness: `γ = α₁ = 1/4`, `κ = a_ent + 4`, `E₀ = 0`, `c₈ = (1 - q)/2`,
`c₉ = 1`, `B = 0`, `ν̄ = 7/72`, `p ≡ 0`, `m₀ = 0`. -/
noncomputable def witnessConsts (α₀ : ℝ) : Consts where
  γ := 1 / 4
  α₁ := 1 / 4
  κ := aEnt 3 3 + 4
  E₀ := 0
  c₈ := (1 - Flow.rate ((3 : ℕ) : ℝ) (1 / 4)) / 2
  c₉ := 1
  α₀ := α₀
  B := 0
  νbar := 7 / 72
  p := fun _ => 0
  m₀ := 0

theorem rate3_pos : 0 < Flow.rate ((3 : ℕ) : ℝ) (1 / 4) := Flow.rate_pos (by norm_num) _

theorem rate3_lt : Flow.rate ((3 : ℕ) : ℝ) (1 / 4) < 1 :=
  Flow.rate_lt_one (by norm_num) (by norm_num)

theorem witnessConsts_admissible {α₀ : ℝ} (h : 0 < α₀) : (witnessConsts α₀).Admissible 3 3 where
  γ_pos := by norm_num [witnessConsts]
  γ_lt := by norm_num [witnessConsts]
  α₁_pos := by norm_num [witnessConsts]
  α₁_lt := by norm_num [witnessConsts]
  α₀_pos := h
  κ_pos := by have := aEnt_nonneg 3 3; simp only [witnessConsts]; linarith
  νbar_pos := by norm_num [witnessConsts]
  νbar_le := by norm_num [witnessConsts]
  c₈_pos := by have := rate3_lt; simp only [witnessConsts]; linarith

/-- The running coefficients: `β_n = 3^n`, `ν_n = (7/72) 9^{n-k}`, `a_n = 5/4`. -/
noncomputable def witnessβ : ℕ → ℝ := fun n => (3 : ℝ) ^ n
noncomputable def witnessν (k : ℕ) : ℕ → ℝ := fun n => 7 / 72 * 9 ^ n / 9 ^ k
noncomputable def witnessa : ℕ → ℝ := fun _ => 5 / 4

theorem witness_coeff (k : ℕ) {α₀ : ℝ} :
    CoeffBounds 3 3 k (witnessConsts α₀) witnessβ (witnessν k) witnessa where
  flow := by
    refine ⟨fun _ => 0, 1, 7 / 72 / 9 ^ k, fun n => ?_, ?_, fun n _ => ?_⟩
    · have := rate3_pos; have := rate3_lt
      simp only [witnessConsts, norm_zero]
      positivity
    · have := rate3_pos; have := rate3_lt
      simp only [witnessConsts]
      nlinarith
    · refine ⟨?_, ?_⟩
      · rw [betaSeq_zero]; simp [witnessβ]
      · rw [nuSeq_zero]
        simp only [witnessν]
        push_cast
        rw [pow_mul]
        norm_num
        ring
  beta_gt := by simp [witnessConsts, witnessβ]
  nu_pos := by simp only [witnessν]; positivity
  nu_le := by
    simp only [witnessν, witnessConsts]
    rw [mul_div_assoc, div_self (by positivity)]; norm_num
  a_ge := by norm_num [witnessa]
  a_lt := by norm_num [witnessa]

end Const

section Family

/-- The threshold of `MomNum.hsmall` at `N = 2`. -/
noncomputable def epsCap : ℝ := (2 * bgK1 3 3 2 + 2) * min (bgC0 3 3 2) (bgC1 3 3 2)

theorem epsCap_pos : 0 < epsCap := by
  have h1 := bgK1_pos 3 3 2
  have h2 := bgC0_pos 3 3 2 (by norm_num)
  have h3 := Balaban.Localization.bgC1_pos' (d := 3) (L := 3) (N := 2) (by norm_num)
  unfold epsCap
  positivity

theorem eps_witnessConsts (α₀ : ℝ) (j : ℕ) :
    (witnessConsts α₀).eps 3 3 j = α₀ * (witnessConsts 1).eps 3 3 j := by
  unfold Consts.eps epsSeq
  simp only [witnessConsts, Consts.alpha]
  ring

/-- The scale `α₀` of the witness at the level `j`. -/
noncomputable def witnessα₀ (j : ℕ) : ℝ := epsCap / (witnessConsts 1).eps 3 3 j

theorem witnessα₀_pos (j : ℕ) : 0 < witnessα₀ j :=
  div_pos epsCap_pos (eps_pos (d := 3) (L := 3) (P := witnessConsts 1) one_pos j)

theorem eps_witness (j : ℕ) : (witnessConsts (witnessα₀ j)).eps 3 3 j = epsCap := by
  rw [eps_witnessConsts, witnessα₀]
  have := eps_pos (d := 3) (L := 3) (P := witnessConsts 1) one_pos j
  field_simp

theorem isSFFamily_witness (m₁ k j : ℕ) (ϱ : ℝ) :
    IsSFFamily (d := 3) (L := 3) (m₁ := m₁) (k := k) (N := 2) (ϱ := ϱ)
      (witnessConsts (witnessα₀ j)) witnessβ (witnessν k) witnessa (zeroFam 3 3 m₁ k 2 ϱ)
      (fun _ _ _ _ _ => 0) (fun _ => 0) where
  admissible := witnessConsts_admissible (witnessα₀_pos j)
  coeff := witness_coeff k
  torus := fun _ _ => isSF_zero _ _ _ _ rfl one_pos (fun _ => le_rfl)
  torusIndep := torusIndep_zero _
  renorm := fun _ _ _ => renormCond_zero _ _ _ _

theorem momNum_witness (k j : ℕ) (ϱ : ℝ) (hϱ : bgR0 3 3 ≤ ϱ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    MomNum 3 3 2 k j ϱ (witnessConsts (witnessα₀ j)) where
  hd := le_rfl
  hL := le_rfl
  hϱ := hϱ
  hκ := by norm_num [witnessConsts]
  hj1 := hj1
  hjk := hjk
  hsmall := (eps_witness j).le
  hE0 := le_rfl

end Family

section Bundle

/-- **The hypotheses of `IsSFFamily.bridgeInf` at positive scale** (`d = L = 3`, `N = 2`,
`1 ≤ j ≤ k`): a member of the class `IsSFFamily`, the numerical conditions `MomNum`, a pair of
distinct components `i₀ ≠ i₁`, and a term family `T` that `RepresentsInf` the class term of `T∞`. -/
structure BridgeInfWitness where
  m₁ : ℕ
  k : ℕ
  j : ℕ
  ϱ : ℝ
  P : Consts
  β : ℕ → ℝ
  ν : ℕ → ℝ
  a : ℕ → ℝ
  Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms 3 3 N₁ m₁ k 2 ϱ
  ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus 3 3 N₁ m₁ k → Fin 2 → ℝ) → (Fin 2 → ℝ) →
    (CTorus 3 3 N₁ m₁ k → Fin 2 → ℝ) → ℝ
  Ek : ℕ → ℝ
  hF : IsSFFamily P β ν a Tm ρd Ek
  hn : MomNum 3 3 2 k j ϱ P
  i₀ : Fin 2
  i₁ : Fin 2
  hne : i₁ ≠ i₀
  T : TermFamily 3 2
  hT : RepresentsInf (L := 3) (m₁ := m₁) (k := k) T P Tm j i₀ (nuIdeal 3 k (ν k) j)
    (liftRadius 3 3 2 P j)

namespace BridgeInfWitness

variable (W : BridgeInfWitness)

/-- The conclusion of `IsSFFamily.bridgeInf` for `W`. -/
theorem bridge :
    PremisesCore W.T W.i₀ W.i₁ (nuIdeal 3 W.k (W.ν W.k) W.j) (liftRadius 3 3 2 W.P W.j) W.P.E₀
      W.P.κ (diamA 3 3 W.P.m₀ W.m₁)
      ((c1 3 3 * (((3 : ℕ) : ℝ) ^ (W.P.m₀ + W.m₁)) ^ 3) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
        K0 3 3 (W.P.κ - 2)) (liftDomInf W.P W.β W.ν W.a W.Tm W.j W.i₀) ∧
    SumConds W.T W.i₀ W.i₁ (nuIdeal 3 W.k (W.ν W.k) W.j) :=
  W.hF.bridgeInf W.hn W.hne W.hT

/-- The context `LiftCtx` at the same class member and scale (on any torus). -/
theorem liftCtx (N₁ : ℕ) [NeZero N₁] :
    LiftCtx W.P W.β W.ν W.a (W.Tm N₁) (W.ρd N₁) (W.Ek N₁) W.j (liftRadius 3 3 2 W.P W.j) := by
  have hε := eps_pos (d := 3) (L := 3) W.hF.admissible.α₀_pos W.j
  obtain ⟨δ, h1, h2, h3, h4, h5⟩ := liftRadius_spec (d := 3) (L := 3) (N := 2) hε
    (j := W.j) (P := W.P) W.i₀ W.hn.hsmall
  exact W.hF.liftCtx N₁ W.hn.hd W.hn.hL W.hn.hϱ W.hn.hj1 W.hn.hjk
    (liftRadius_pos hε W.i₀) ⟨δ, h1, h2, h3, h4, h5⟩

end BridgeInfWitness

/-- **`bridgeInf`, `MomNum` and `LiftCtx` are jointly satisfiable at positive scale.** -/
theorem nonempty_bridgeInfWitness (m₁ k j : ℕ) (ϱ : ℝ) (hϱ : bgR0 3 3 ≤ ϱ) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) : Nonempty BridgeInfWitness :=
  ⟨{ m₁ := m₁, k := k, j := j, ϱ := ϱ, P := witnessConsts (witnessα₀ j), β := witnessβ,
     ν := witnessν k, a := witnessa, Tm := zeroFam 3 3 m₁ k 2 ϱ,
     ρd := fun _ _ _ _ _ => 0, Ek := fun _ => 0, hF := isSFFamily_witness m₁ k j ϱ,
     hn := momNum_witness k j ϱ hϱ hj1 hjk, i₀ := 0, i₁ := 1, hne := by decide, T := _,
     hT := rfl }⟩

end Bundle

end Balaban.SmallField.Def6
