/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.ContractionCore
public import Balaban.Analysis.Contraction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Analytic.Constructions

/-!
# Analytic dependence of the fixed point of the abstract core on the parameters

BACKGROUND.md §5.1 (Proposition 5.1), LOCALIZATION.md §3.2 (Theorem I-4a), requirement R-B2.
For a family of abstract Green families, operators `H₀`, and data `(φ₀, α₀, F_s)` depending on a
parameter `p` in a complex normed space `Pr` (so that `p` may contain a coefficient `s`),
`exists_analytic_core` says that the fixed point of the core depends analytically on `p` on an
open set `P` where `Setup` holds and the entries of `𝒢` are analytic jointly in `(α, p)` on the
polydisc.  Nothing here mentions `dirichletOperator`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

@[fun_prop] theorem aa_fst' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (q : E × F) :
    AnalyticAt ℂ (fun q : E × F => q.1) q := (ContinuousLinearMap.fst ℂ E F).analyticAt q

@[fun_prop] theorem aa_snd' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (q : E × F) :
    AnalyticAt ℂ (fun q : E × F => q.2) q := (ContinuousLinearMap.snd ℂ E F).analyticAt q

@[fun_prop] theorem aa_eval' {ι β : Type*} [Fintype ι] [NormedAddCommGroup β] [NormedSpace ℂ β]
    (i : ι) (q : ι → β) : AnalyticAt ℂ (fun f : ι → β => f i) q :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => β) i).analyticAt q

section Explicit

variable {G : GeneratingSet d L N₀ k ϱ}

/-- Entry-wise formula for `𝒩` (all matrix products written out as finite sums). -/
noncomputable def Nexp (ιU : Bool) (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (Fs δφ : G.Ω 1 × Fin N → ℂ) (H : Matrix (G.Ω 1) (G.Ω 1) ℂ) (x : G.Ω 1) : ℂ :=
  ∑ i, (φ₀ x i + δφ (x, i)) * Fs (x, i)
    - ∑ y, ∑ i, H x y * (φ₀ x i - φ₀ y i) * δφ (y, i)
    + 1 / 2 * ((∑ y, H x y * ∑ i, δφ (y, i) * δφ (y, i)) -
        2 * ∑ i, δφ (x, i) * ∑ y, H x y * δφ (y, i))
    + (if ιU then 1 / 2 * ∑ y, H x y * (∑ i, φ₀ y i * φ₀ y i - 1) else 0)

theorem Nmap_explicit (H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ) (ιU : Bool)
    (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (Fs δφ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    Nmap G H₀ ιU φ₀ Fs δφ x = Nexp ιU φ₀ Fs δφ H₀ x := by
  unfold Nmap Nexp
  rw [commK_mulVec, Rvec_eq]
  have h1 : ∀ i, (liftOp N H₀ *ᵥ δφ) (x, i) = ∑ y, H₀ x y * δφ (y, i) := by
    intro i; rw [liftOp_mulVec]; rfl
  simp only [h1, restrictField]
  have h2 : (H₀ *ᵥ fun y => ∑ i, δφ (y, i) * δφ (y, i)) x =
      ∑ y, H₀ x y * ∑ i, δφ (y, i) * δφ (y, i) := rfl
  have h3 : (H₀ *ᵥ gdef G φ₀) x = ∑ y, H₀ x y * (∑ i, φ₀ y i * φ₀ y i - 1) := rfl
  rw [h2, h3]
  ring

end Explicit

section An

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]

theorem aa_sum' {ι : Type*} (s : Finset ι) {f : ι → Q → ℂ} {q : Q}
    (h : ∀ i ∈ s, AnalyticAt ℂ (f i) q) : AnalyticAt ℂ (fun q => ∑ i ∈ s, f i q) q :=
  Finset.analyticAt_fun_sum _ h

theorem an_Nexp {G : GeneratingSet d L N₀ k ϱ} {q : Q} (ιU : Bool)
    (φ : Q → Torus d (N₀ * L ^ k) → Fin N → ℂ) (Fs dφ : Q → G.Ω 1 × Fin N → ℂ)
    (Hm : Q → Matrix (G.Ω 1) (G.Ω 1) ℂ) (x : G.Ω 1)
    (hφ : ∀ y i, AnalyticAt ℂ (fun q => φ q y i) q)
    (hF : ∀ (y : G.Ω 1) i, AnalyticAt ℂ (fun q => Fs q (y, i)) q)
    (hd : ∀ (y : G.Ω 1) i, AnalyticAt ℂ (fun q => dφ q (y, i)) q)
    (hH : ∀ y z, AnalyticAt ℂ (fun q => Hm q y z) q) :
    AnalyticAt ℂ (fun q => Nexp ιU (φ q) (Fs q) (dφ q) (Hm q) x) q := by
  unfold Nexp
  have s1 : AnalyticAt ℂ (fun q => ∑ i, (φ q x i + dφ q (x, i)) * Fs q (x, i)) q :=
    aa_sum' _ fun i _ => ((hφ x i).add (hd x i)).mul (hF x i)
  have s2 : AnalyticAt ℂ (fun q => ∑ y, ∑ i, Hm q x y * (φ q x i - φ q y i) * dφ q (y, i)) q :=
    aa_sum' _ fun y _ => aa_sum' _ fun i _ =>
      ((hH x y).mul ((hφ x i).sub (hφ y i))).mul (hd y i)
  have s3 : AnalyticAt ℂ (fun q => ∑ y, Hm q x y * ∑ i, dφ q (y, i) * dφ q (y, i)) q :=
    aa_sum' _ fun y _ => (hH x y).mul (aa_sum' _ fun i _ => (hd y i).mul (hd y i))
  have s4 : AnalyticAt ℂ (fun q => ∑ i, dφ q (x, i) * ∑ y, Hm q x y * dφ q (y, i)) q :=
    aa_sum' _ fun i _ => (hd x i).mul (aa_sum' _ fun y _ => (hH x y).mul (hd y i))
  have s5 : AnalyticAt ℂ (fun q => ∑ y, Hm q x y * (∑ i, φ q y i * φ q y i - 1)) q :=
    aa_sum' _ fun y _ => (hH x y).mul ((aa_sum' _ fun i _ => (hφ y i).mul (hφ y i)).sub
      analyticAt_const)
  have s6 : AnalyticAt ℂ (fun q => if ιU then 1 / 2 * ∑ y, Hm q x y *
      (∑ i, φ q y i * φ q y i - 1) else 0) q := by
    cases ιU
    · exact analyticAt_const
    · exact analyticAt_const.mul s5
  exact (((s1.sub s2).add (analyticAt_const.mul (s3.sub (analyticAt_const.mul s4)))).add s6)

/-- The entries of `𝒢(α(q)) F(q)` are analytic when those of `𝒢(α(q))` and `F(q)` are. -/
theorem an_dphi_gen {G : GeneratingSet d L N₀ k ϱ} {q : Q}
    (M : Q → Matrix (G.Ω 1) (G.Ω 1) ℂ) (F : Q → G.Ω 1 × Fin N → ℂ)
    (hM : ∀ y z, AnalyticAt ℂ (fun q => M q y z) q)
    (hF : ∀ (y : G.Ω 1) j, AnalyticAt ℂ (fun q => F q (y, j)) q) (y : G.Ω 1) (j : Fin N) :
    AnalyticAt ℂ (fun q => (liftOp N (M q) *ᵥ F q) (y, j)) q := by
  have e : ∀ q, (liftOp N (M q) *ᵥ F q) (y, j) = ∑ z, M q y z * F q (z, j) := by
    intro q; rw [liftOp_mulVec]; rfl
  simp_rw [e]
  exact aa_sum' _ fun z _ => (hM y z).mul (hF z j)

end An

section Family

variable {G : GeneratingSet d L N₀ k ϱ} {Pr : Type*} [NormedAddCommGroup Pr] [NormedSpace ℂ Pr]
  {P : Set Pr} {γ : ℝ}

/-- Analyticity of the entries of `δφ = 𝒢(α₀ + δα) (F_s - δα φ₀)` along a parametrised curve:
`p = π(q)`, `ξ = ξ(q)`. -/
theorem an_dphi_at {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q : Q}
    (𝒢 : Pr → (G.Ω 1 → ℂ) → Matrix (G.Ω 1) (G.Ω 1) ℂ) (α₀ : Pr → G.Ω 1 → ℂ)
    (φ₀ : Pr → Torus d (N₀ * L ^ k) → Fin N → ℂ) (Fs : Pr → G.Ω 1 × Fin N → ℂ)
    (a𝒢 : ∀ y z, AnalyticOnNhd ℂ (fun r : (G.Ω 1 → ℂ) × Pr => 𝒢 r.2 r.1 y z)
      {r | Small G r.1 γ ∧ r.2 ∈ P})
    (π : Q → Pr) (ξ : Q → G.Ω 1 → ℂ) (hπ : AnalyticAt ℂ π q) (hπP : π q ∈ P)
    (hα₀ : ∀ y, AnalyticAt ℂ (fun q => α₀ (π q) y) q)
    (hξ : ∀ y, AnalyticAt ℂ (fun q => ξ q y) q)
    (hφ : ∀ y i, AnalyticAt ℂ (fun q => φ₀ (π q) y i) q)
    (hF : ∀ (y : G.Ω 1) i, AnalyticAt ℂ (fun q => Fs (π q) (y, i)) q)
    (hpoly : Small G (α₀ (π q) + toAlpha G (ξ q)) γ) (y : G.Ω 1) (j : Fin N) :
    AnalyticAt ℂ (fun q => dphi G (𝒢 (π q)) (α₀ (π q)) (φ₀ (π q)) (Fs (π q))
      (toAlpha G (ξ q)) (y, j)) q := by
  have hc : ∀ y, AnalyticAt ℂ (fun q => toAlpha G (ξ q) y) q := fun y => by
    unfold toAlpha; exact (hξ y).div_const
  have hmap : AnalyticAt ℂ (fun q => (α₀ (π q) + toAlpha G (ξ q), π q)) q :=
    AnalyticAt.prod (analyticAt_pi_iff.2 fun y => (hα₀ y).add (hc y)) hπ
  have hM : ∀ y z, AnalyticAt ℂ (fun q => 𝒢 (π q) (α₀ (π q) + toAlpha G (ξ q)) y z) q :=
    fun y z => (a𝒢 y z _ ⟨hpoly, hπP⟩).comp hmap
  exact an_dphi_gen (fun q => 𝒢 (π q) (α₀ (π q) + toAlpha G (ξ q)))
    (fun q => Fsrc (φ₀ (π q)) (Fs (π q)) (toAlpha G (ξ q))) hM
    (fun y j => (hF y j).sub ((hc y).mul (hφ y j))) y j

/-- **Analytic dependence of the fixed point on the parameter (abstract Green family, modes U
and P).**  For `p ∈ P` (open) the abstract data satisfy `Setup` and `𝒢 p` is a `GreenFamily`; the
entries of `𝒢 p α`, `H₀ p`, `φ₀ p`, `α₀ p`, `F_s p` are analytic in the parameters (for `𝒢`
jointly in `(α, p)` on the polydisc `|α|₂ ≤ γ`).  Then the unique fixed point `ξ*(p)` of `Smap` in
the ball of radius `ρ` is an analytic function of `p`, and so is `δφ = dphi (toAlpha ξ*(p))`. -/
theorem exists_analytic_core (hP : IsOpen P) {ιU : Bool} {B Kc Rc δ₀ Fb Gb ρ : ℝ}
    (𝒢 : Pr → (G.Ω 1 → ℂ) → Matrix (G.Ω 1) (G.Ω 1) ℂ) (H₀ : Pr → Matrix (G.Ω 1) (G.Ω 1) ℂ)
    (α₀ : Pr → G.Ω 1 → ℂ) (φ₀ : Pr → Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (Fs : Pr → G.Ω 1 × Fin N → ℂ)
    (hG : ∀ p ∈ P, GreenFamily G N (𝒢 p) B γ)
    (hS : ∀ p ∈ P, Setup G (H₀ p) ιU Kc Rc (α₀ p) (φ₀ p) (Fs p) δ₀ Fb Gb)
    (hC : CoreHyp N B Kc Rc γ δ₀ Fb Gb ρ)
    (aφ : ∀ y i, AnalyticOnNhd ℂ (fun p => φ₀ p y i) P)
    (aα : ∀ y, AnalyticOnNhd ℂ (fun p => α₀ p y) P)
    (aF : ∀ (y : G.Ω 1) i, AnalyticOnNhd ℂ (fun p => Fs p (y, i)) P)
    (aH : ∀ y z, AnalyticOnNhd ℂ (fun p => H₀ p y z) P)
    (a𝒢 : ∀ y z, AnalyticOnNhd ℂ (fun r : (G.Ω 1 → ℂ) × Pr => 𝒢 r.2 r.1 y z)
      {r | Small G r.1 γ ∧ r.2 ∈ P}) :
    ∃ ξs : Pr → (G.Ω 1 → ℂ), AnalyticOnNhd ℂ ξs P ∧
      (∀ p ∈ P, ξs p ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) ρ ∧
        Smap G (𝒢 p) (H₀ p) ιU (α₀ p) (φ₀ p) (Fs p) (ξs p) = ξs p ∧
        ∀ ξ ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) ρ,
          Smap G (𝒢 p) (H₀ p) ιU (α₀ p) (φ₀ p) (Fs p) ξ = ξ → ξ = ξs p) ∧
      ∀ (y : G.Ω 1) (j : Fin N), AnalyticOnNhd ℂ (fun p => dphi G (𝒢 p) (α₀ p) (φ₀ p) (Fs p)
        (toAlpha G (ξs p)) (y, j)) P := by
  have hρ := hC.ρ_nn
  have hr : δ₀ + ρ ≤ γ := by linarith [hC.poly]
  have hpoly : ∀ p ∈ P, ∀ ξ ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) ρ,
      Small G (α₀ p + toAlpha G ξ) γ := fun p hp ξ hξ => by
    rw [mem_closedBall_zero_iff] at hξ
    exact (hS p hp).poly (small_toAlpha G ξ fun x => (norm_le_pi_norm ξ x).trans hξ) hr
  have hT : AnalyticOnNhd ℂ (fun r : (G.Ω 1 → ℂ) × Pr =>
      Smap G (𝒢 r.2) (H₀ r.2) ιU (α₀ r.2) (φ₀ r.2) (Fs r.2) r.1)
      (Metric.closedBall (0 : G.Ω 1 → ℂ) ρ ×ˢ P) := by
    rintro q ⟨hq1, hq2⟩
    refine analyticAt_pi_iff.2 fun x => ?_
    have hc : ∀ y, AnalyticAt ℂ (fun r : (G.Ω 1 → ℂ) × Pr => r.1 y) q := fun y => by fun_prop
    have hφ : ∀ y i, AnalyticAt ℂ (fun r : (G.Ω 1 → ℂ) × Pr => φ₀ r.2 y i) q :=
      fun y i => (aφ y i q.2 hq2).comp (aa_snd' q)
    have hα : ∀ y, AnalyticAt ℂ (fun r : (G.Ω 1 → ℂ) × Pr => α₀ r.2 y) q :=
      fun y => (aα y q.2 hq2).comp (aa_snd' q)
    have hF : ∀ (y : G.Ω 1) i, AnalyticAt ℂ (fun r : (G.Ω 1 → ℂ) × Pr => Fs r.2 (y, i)) q :=
      fun y i => (aF y i q.2 hq2).comp (aa_snd' q)
    have hH : ∀ y z, AnalyticAt ℂ (fun r : (G.Ω 1 → ℂ) × Pr => H₀ r.2 y z) q :=
      fun y z => (aH y z q.2 hq2).comp (aa_snd' q)
    have hd := an_dphi_at (q := q) 𝒢 α₀ φ₀ Fs a𝒢 (fun r : (G.Ω 1 → ℂ) × Pr => r.2)
      (fun r => r.1) (aa_snd' q) hq2 hα hc hφ hF (hpoly q.2 hq2 q.1 hq1)
    have hN := an_Nexp (q := q) ιU (fun r : (G.Ω 1 → ℂ) × Pr => φ₀ r.2)
      (fun r => Fs r.2) (fun r => dphi G (𝒢 r.2) (α₀ r.2) (φ₀ r.2) (Fs r.2) (toAlpha G r.1))
      (fun r => H₀ r.2) x hφ hF (fun y i => hd y i) hH
    have hℓ : AnalyticAt ℂ (fun _ : (G.Ω 1 → ℂ) × Pr =>
        ((G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 : ℝ) : ℂ)) q := analyticAt_const
    refine (hℓ.mul hN).congr (Filter.Eventually.of_forall fun q' => ?_)
    simp only [Smap, Nmap_explicit]
    rfl
  obtain ⟨ξs, hξs, hanal, -⟩ := Balaban.Analysis.exists_analytic_fixedPoint
    (T := fun r : (G.Ω 1 → ℂ) × Pr =>
      Smap G (𝒢 r.2) (H₀ r.2) ιU (α₀ r.2) (φ₀ r.2) (Fs r.2) r.1) (P := P) (r := ρ)
    (θ := 1 / 2) hP hρ (by norm_num) (by norm_num) hT
    (fun p hp ξ hξ => Smap_mem_ball (hG p hp) (hS p hp) hC ξ hξ)
    (fun p hp ξ hξ ξ' hξ' => Smap_lip_norm (hG p hp) (hS p hp) hC ξ ξ' hξ hξ')
  refine ⟨ξs, hanal, hξs, fun y j p hp => ?_⟩
  have hξy : ∀ y, AnalyticAt ℂ (fun p => ξs p y) p := fun y => analyticAt_pi_iff.1 (hanal p hp) y
  exact an_dphi_at (q := p) 𝒢 α₀ φ₀ Fs a𝒢 id ξs analyticAt_id hp
    (fun y => (aα y p hp)) hξy (fun y i => aφ y i p hp) (fun y i => aF y i p hp)
    (hpoly p hp _ (hξs p hp).1) y j

end Family

end Balaban.Background
