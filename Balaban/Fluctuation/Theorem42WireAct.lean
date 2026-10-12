/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Theorem42WireStep

/-!
# The cube action difference of the real step as a function of the complex data (FLUCTUATION §4.2)

`realStepAct` is `F_Q(u) = β (A*_Q(φ^∂(u)) - A*_Q(φ^loc(u)))` of Step 3, a function of the complex
fields `u = (ψ_k, ψ_{k+1}, h)`.  On an open set of fields whose local, cube and boundary data lie
in the domain `𝒟`:

* `realStepAct_analytic`: `F_Q` is holomorphic (`liftMixed_raw_analytic`, `bgFieldC_analyticOn_raw`);
* `realStepAct_bound`: `|F_Q(u)| ≤ C_F β |Q| (r + shift)² e^{-γ_w D}` (Step 3; `D = stepDist`).

These are exactly the two hypotheses of `DecoupledCubeResponse.nonempty_of_undecoupled`
(`hact`, `hbd`) for the real step, with `act b u = F_{Q_b}(u)`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.LargeField
  RegionHistory

set_option linter.unusedSectionVars false

/-- The complex fields `(ψ_k, ψ_{k+1}, h)` on which the data of the step depend. -/
abbrev StepFields (d N₀ L k N : ℕ) : Type :=
  (Torus d (N₀ * L ^ (k + 1 - k)) → Fin N → ℂ) ×
    (Torus d (N₀ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) × (Fin N → ℂ)

section Analytic

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The raw data `(Ψ, h̃)` of the mixed lift is analytic (indeed linear) in the fields
`(ψ_k, ψ_{k+1}, h)`. -/
theorem liftMixed_raw_analytic (G : GeneratingSet d L N₀ (k + 1) ϱ)
    {Ω : Finset (Torus d (N₀ * L ^ (k + 1)))} (hΩ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω)
    (hG : G.Ω (k + 1) ⊆ Ω) :
    AnalyticOnNhd ℂ (fun u : StepFields d N₀ L k N =>
      ((liftMixed G hΩ hG u.1 u.2.1 u.2.2).Ψ, (liftMixed G hΩ hG u.1 u.2.1 u.2.2).h)) Set.univ := by
  classical
  intro u _
  have hu1 : AnalyticAt ℂ (fun u : StepFields d N₀ L k N => u.1) u := analyticAt_fst
  have hu2 : AnalyticAt ℂ (fun u : StepFields d N₀ L k N => u.2.1) u :=
    analyticAt_fst.comp analyticAt_snd
  have hu3 : AnalyticAt ℂ (fun u : StepFields d N₀ L k N => u.2.2) u :=
    analyticAt_snd.comp analyticAt_snd
  refine AnalyticAt.prod (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
    (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
  · by_cases hx : x ∈ dataSites G
    · have e : (fun u : StepFields d N₀ L k N =>
          (liftMixed G hΩ hG u.1 u.2.1 u.2.2).Ψ x i) = fun u =>
          if x ∈ Ω then u.2.1 (jBlock d L N₀ (k + 1) (k + 1) x) i
          else u.1 (jBlock d L N₀ (k + 1) k x) i := by
        funext u
        rw [liftMixed_Ψ G hΩ hG _ _ _ hx]
        unfold mixedLift blockLift
        split_ifs <;> rfl
      rw [e]
      by_cases hxΩ : x ∈ Ω
      · simp only [hxΩ, ↓reduceIte]
        exact analyticAt_pi_iff.1 (analyticAt_pi_iff.1 hu2 _) i
      · simp only [hxΩ, ↓reduceIte]
        exact analyticAt_pi_iff.1 (analyticAt_pi_iff.1 hu1 _) i
    · have e : (fun u : StepFields d N₀ L k N =>
          (liftMixed G hΩ hG u.1 u.2.1 u.2.2).Ψ x i) = fun _ => 0 := by
        funext u
        rw [(liftMixed G hΩ hG u.1 u.2.1 u.2.2).Ψ_zero x hx]; rfl
      rw [e]; exact analyticAt_const
  · by_cases hx : x ∈ G.Ω 1
    · have e : (fun u : StepFields d N₀ L k N =>
          (liftMixed G hΩ hG u.1 u.2.1 u.2.2).h x i) = fun u => u.2.2 i := by
        funext u
        rw [liftMixed_h G hΩ hG _ _ _ hx]
      rw [e]
      exact analyticAt_pi_iff.1 hu3 i
    · have e : (fun u : StepFields d N₀ L k N =>
          (liftMixed G hΩ hG u.1 u.2.1 u.2.2).h x i) = fun _ => 0 := by
        funext u
        rw [(liftMixed G hΩ hG u.1 u.2.1 u.2.2).h_zero x hx]; rfl
      rw [e]; exact analyticAt_const

variable {a : ℕ → ℝ} {ν : ℝ} {G : GeneratingSet d L N₀ (k + 1) ϱ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Holomorphy of the background in the data**: if the raw data `(Ψ, h̃)` of `Dd p` are analytic on
an open set `s` and `Dd p` lies in the domain `𝒟`, then `p ↦ bgFieldC (Dd p)` is analytic on `s`
(Theorem 7.2, analyticity). -/
theorem bgFieldC_analyticOn_raw (H : BgHyp d L (k + 1) ϱ a ν) {s : Set E} (hs : IsOpen s)
    (Dd : E → BgData G N) (hD : AnalyticOnNhd ℂ (fun p => ((Dd p).Ψ, (Dd p).h)) s)
    (hdd : ∀ p ∈ s, InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν (Dd p)) :
    AnalyticOnNhd ℂ (fun p => bgFieldC G a ν (bgC0 d L N) (Dd p)) s := by
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := G) (a := a) (ν := ν) H
  have h1 : AnalyticOnNhd ℂ (fun p => (F ((Dd p).Ψ, (Dd p).h)).1) s := fun p hp =>
    analyticAt_fst.comp (AnalyticAt.comp (hF _ ⟨Dd p, hdd p hp, rfl⟩) (hD p hp))
  refine h1.congr hs fun p hp => ?_
  show (F ((Dd p).Ψ, (Dd p).h)).1 = bgFieldC G a ν (bgC0 d L N) (Dd p)
  rw [hFe (Dd p) (hdd p hp)]

end Analytic
section Act

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1))) (hk : k + 1 ≤ K)

/-- **The cube action difference of the real step**, as a function of the complex fields
`u = (ψ_k, ψ_{k+1}, h)`: `F_Q(u) = β (A*_Q(D(u); φ^∂(u)|) - A*_Q(D(u); φ^loc(u)))`, the difference of the
star cube action of the cube set `Q` of the local family at the boundary background
`φ^∂ = φ(𝔹^∂; ψ̃)` (restricted to `Ω₁(G^{Z'})`) and at the local background `φ^loc = φ(G^{Z'}; ψ̃)`,
for the action data `D(u)` of the local family (FLUCTUATION §4.2 Step 3, `F_□` of (4.2)). -/
noncomputable def realStepAct (a₁ ν β : ℝ) (Q : Finset (Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))))
    (u : StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N) : ℂ :=
  (β : ℂ) * (cubeActionStar (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) ν Q
      (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2).Ψ (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2).h
      ((locGen_precedes_bd g Hl k Zc hZc hk).restrictφ
        (bgFieldC (bdGen g Hl k hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
          (bdDataC g Hl k hk u.1 u.2.1 u.2.2))) -
    cubeActionStar (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) ν Q
      (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2).Ψ (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2).h
      (bgFieldC (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
        (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2)))

include Hl hZc hk in
/-- **Holomorphy of the cube action difference of the real step** on an open set of fields whose
local and boundary data lie in the domain `𝒟`. -/
theorem realStepAct_analytic {a₁ ν β : ℝ}
    (H : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν)
    (Q : Finset (Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))))
    {s : Set (StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N)} (hs : IsOpen s)
    (hloc : ∀ u ∈ s, InUnionDomainC (locGen g Hl k Zc hZc hk) (bgC0 S.d S.L N) (bgC1 S.d S.L N) ν
      (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2))
    (hbd : ∀ u ∈ s, InUnionDomainC (bdGen g Hl k hk) (bgC0 S.d S.L N) (bgC1 S.d S.L N) ν
      (bdDataC g Hl k hk u.1 u.2.1 u.2.2)) :
    AnalyticOnNhd ℂ (realStepAct g Hl k Zc hZc hk a₁ ν β Q) s := by
  classical
  have hrL : AnalyticOnNhd ℂ (fun u : StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N =>
      ((locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2).Ψ, (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2).h)) s :=
    (liftMixed_raw_analytic _ _ _).mono (Set.subset_univ _)
  have hrB : AnalyticOnNhd ℂ (fun u : StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N =>
      ((bdDataC g Hl k hk u.1 u.2.1 u.2.2).Ψ, (bdDataC g Hl k hk u.1 u.2.1 u.2.2).h)) s :=
    (liftMixed_raw_analytic _ _ _).mono (Set.subset_univ _)
  have hΦ0 := bgFieldC_analyticOn_raw (a := compWeight S.L a₁) H hs
    (fun u : StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N =>
      locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2) hrL hloc
  have hΦ1 := bgFieldC_analyticOn_raw (a := compWeight S.L a₁) H hs
    (fun u : StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N =>
      bdDataC g Hl k hk u.1 u.2.1 u.2.2) hrB hbd
  intro p hp
  have hΨ : AnalyticAt ℂ (fun q : StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N =>
      (locDataC g Hl k Zc hZc hk q.1 q.2.1 q.2.2).Ψ) p := analyticAt_fst.comp (hrL p hp)
  have hh : AnalyticAt ℂ (fun q : StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N =>
      (locDataC g Hl k Zc hZc hk q.1 q.2.1 q.2.2).h) p := analyticAt_snd.comp (hrL p hp)
  have hφ1 : AnalyticAt ℂ (fun q : StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N =>
      (locGen_precedes_bd g Hl k Zc hZc hk).restrictφ
        (bgFieldC (bdGen g Hl k hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
          (bdDataC g Hl k hk q.1 q.2.1 q.2.2))) p := by
    refine analyticAt_pi_iff.2 fun z => ?_
    exact analyticAt_pi_iff.1 (hΦ1 p hp) _
  exact analyticAt_const.mul ((cubeActionStar_analyticAt Q hΨ hh hφ1).sub
    (cubeActionStar_analyticAt Q hΨ hh (hΦ0 p hp)))

include Hl hZc hk in
/-- **The bound on the cube action difference of the real step** (Theorem 4.2, Step 3): for fields
`u` whose local, cube and boundary data are in the domains and `ψ_{k+1} ∈ Δ^c_{k+1}(□; 1, r)`,
`|F_Q(u)| ≤ C_F β |Q| (r + shift)² e^{-γ_w D}`. -/
theorem realStepAct_bound (hd : 3 ≤ S.d) (hL : 3 ≤ S.L) {Cδ : ℝ} (hCδ : 0 ≤ Cδ) :
    ∃ CF Kw δw : ℝ, 0 < CF ∧ 0 < Kw ∧ 0 < δw ∧
      ∀ {a₁ ν r δ1 ε1 δ0 ε0 δb εb β : ℝ} {y0 : Torus S.d (n (k + 1))}
        (u : StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N)
        (Q : Finset (Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)))),
        0 < a₁ →
        BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν →
        2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1) →
        y0 ∈ (Zc : Set (Torus S.d (n (k + 1)))) → nbhd 4 {y0} ⊆ (Hl.step k).Omega → 0 ≤ r →
        u.2.1 ∈ DeltaC (q := k + 1) (M1 := g.M1) (N₁ := g.c * n (k + 1))
          (L := S.L) (compWeight S.L a₁) ν r u.2.2 g.c (n (k + 1)) y0 →
        0 < δ1 → δ1 ≤ ε1 → ε1 ≤ bgC0 S.d S.L N → δ1 ≤ thm73C1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε1 ^ 2 ≤ δ1 ^ 2 →
        InDomainC (locGen g Hl k Zc hZc hk) ν δ1 ε1 (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2) →
        0 < δ0 → δ0 ≤ ε0 → ε0 ≤ bgC0 S.d S.L N → δ0 ≤ bgC1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε0 ^ 2 ≤ δ0 ^ 2 →
        InDomainC (genCubeLoc g k y0) ν δ0 ε0 (liftSingle (genCubeLoc g k y0) u.2.1 u.2.2) →
        0 < δb → δb ≤ εb → εb ≤ bgC0 S.d S.L N → δb ≤ thm73C1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * εb ^ 2 ≤ δb ^ 2 →
        InDomainC (bdGen g Hl k hk) ν δb εb (bdDataC g Hl k hk u.1 u.2.1 u.2.2) →
        bgK1 S.d S.L N * δ0 ≤ deltaStar S.d S.L N → bgK1 S.d S.L N * δ0 ≤ δw →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δ1) ≤ deltaStar S.d S.L N →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δ1) ≤ δw →
        bgK1 S.d S.L N * δ1 ≤ deltaStar S.d S.L N → bgK1 S.d S.L N * δ1 ≤ δw →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δb) ≤ deltaStar S.d S.L N →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δb) ≤ δw →
        (∀ x ∈ Q, blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x = y0) →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δb) ≤ Cδ * (r + transferShift S.d S.L N (k + 1) ν Kw δ1
          (stepDist S.L g.M1 g.c k 1 (minSep S.L g.M1))) →
        0 ≤ β →
        ‖realStepAct g Hl k Zc hZc hk a₁ ν β Q u‖ ≤
          CF * β * Q.card * (r + transferShift S.d S.L N (k + 1) ν Kw δ1
            (stepDist S.L g.M1 g.c k 1 (minSep S.L g.M1))) ^ 2 *
            Real.exp (-(gammaW S.d * stepDist S.L g.M1 g.c k ⌊R k⌋₊ (minSep S.L g.M1))) := by
  obtain ⟨CF, Kw, δw, hCF, hKw, hδw, hmain⟩ :=
    realStep_cubeDiffStar_bound g Hl k Zc hZc hk hd hL hCδ
  refine ⟨CF, Kw, δw, hCF, hKw, hδw, ?_⟩
  intro a₁ ν r δ1 ε1 δ0 ε0 δb εb β y0 u Q ha₁ H hsep hy0 hΩ hr hΔ hδ10 hδε1 hε1 hδ1c hνε1 hD1
    hδ00 hδε0 hε0 hδ0c hνε0 hD0 hδb0 hδεb hεb hδbc hνεb hDb hK0 hKw0 hK1 hKw1 hK11 hKw11 hKb hKwb
    hQ hCr hβ
  have hprec := locGen_precedes_bd g Hl k Zc hZc hk
  obtain ⟨hΨ, hh⟩ := locData_eq_bd g Hl k Zc hZc hk u.1 u.2.1 u.2.2
  obtain ⟨-, hfield, -⟩ := composed_change ha₁ H H hprec hδb0 hδεb hεb hδbc hνεb hDb hΨ hh
    (E := (∅ : Set (Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)))))
    (fun x hx => absurd hx (Set.notMem_empty x))
  have := hmain (y0 := y0) u.1 u.2.1 u.2.2 Q ha₁ H hsep hy0 hΩ hr hΔ hδ10 hδε1 hε1 hδ1c hνε1 hD1
    hδ00 hδε0 hε0 hδ0c hνε0 hD0 hδb0 hδεb hεb hδbc hνεb hDb hK0 hKw0 hK1 hKw1 hK11 hKw11 hKb hKwb
    hQ hCr hβ
  unfold realStepAct
  rw [← hfield]
  exact this

end Act
end Balaban.Fluctuation
