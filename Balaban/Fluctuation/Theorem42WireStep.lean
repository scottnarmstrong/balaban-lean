/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Theorem42WireGeom
public import Balaban.Fluctuation.Theorem42RealFlow

/-!
# Theorem 4.2, Step 3 for the real step, one action cube (FLUCTUATION.md §4.2)

The local family `G^{Z'}_{k+1}` precedes the global boundary family `𝔹^∂_{k+1}` (`bdGen`), the data
`ψ̃` of both are the mixed lift of `(ψ_k, ψ_{k+1}, h)` (`locData`, `locDataBd`):

* `composed_change`: **Step 1** for nested generating sets: the composed datum `Du` of the local
  family is in the domain `𝒟`, has background `φ^∂ = φ(𝔹^∂; ψ̃)` restricted to `Ω₁(G^{Z'})`
  (BG Theorem 7.3), differs from `ψ̃` by a change `δΨ` that vanishes on `E_{Z'}` where the layers
  agree (LFR Lemma II.2.5 (c)), has the same `h`, and satisfies the H7-type bound
  `|δΨ| ≤ (2d + 2) K₁ δ'` on the data sites, `δ'` the domain parameter of the boundary datum;
* `locGen_precedes_bd`, `locGen_bd_agree`, `locData_eq_bd`: the geometry of `G^{Z'} ≺ 𝔹^∂`;
* `realStep_cubeDiffStar_bound`: **Step 3** for one action cube `Q` inside the cube `□ ∋ y0`:
  `|β (A*_Q(φ^∂) - A*_Q(φ^loc))| ≤ C_F β |Q| (r + shift)² e^{-γ_w D}` in the star convention, from the
  H7 membership of `ψ_{k+1}` in `Δ^c_{k+1}(□; 1, r)` and the domain memberships of the local, cube
  and boundary data.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.LargeField
  RegionHistory

set_option linter.unusedSectionVars false

section Change

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ0 ϱ1 : ℝ}
  {G0 : GeneratingSet d L N₀ (k + 1) ϱ0} {G1 : GeneratingSet d L N₀ (k + 1) ϱ1}

/-- **The data change of the composition (6.2) between nested generating sets** (FLUCTUATION §4.2
Step 1; LFR Lemma II.2.5 (c)): for `𝔹_j ≺ 𝔹'_k`, a datum `D'` of `𝔹'_k` in the complex domain
`𝒟` (`δ' ≤ thm73C1`) and a datum `D` of `𝔹_j` that agrees with `D'` on the data sites and on `Ω₁`,
the composed datum `Du` of `𝔹_j` lies in `𝒟`, has the background `φ(𝔹_j; Du) = φ(𝔹'_k; D')|`, and
differs from `D` by a change `δΨ` that vanishes where the layers agree, has the same `h`, and is
bounded by `(2d+2) K₁ δ'` on the data sites. -/
theorem composed_change {a₁ ν δ' ε' : ℝ} (ha₁ : 0 < a₁)
    (H0 : BgHyp d L (k + 1) ϱ0 (compWeight L a₁) ν) (H1 : BgHyp d L (k + 1) ϱ1 (compWeight L a₁) ν)
    (hprec : Precedes G0 G1) {D' : BgData G1 N} (hδ0 : 0 < δ') (hδε : δ' ≤ ε')
    (hε : ε' ≤ bgC0 d L N) (hδc : δ' ≤ thm73C1 d L N)
    (hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε' ^ 2 ≤ δ' ^ 2) (hD' : InDomainC G1 ν δ' ε' D')
    {D : BgData G0 N} (hΨ : ∀ x ∈ dataSites G0, D.Ψ x = D'.Ψ x)
    (hh : ∀ x ∈ G0.Ω 1, D.h x = D'.h x) {E : Set (Torus d (N₀ * L ^ (k + 1)))}
    (hE : ∀ x ∈ E, ∀ m, 1 ≤ m → m ≤ k + 1 → (x ∈ G0.Ω m ↔ x ∈ G1.Ω m)) :
    InUnionDomainC G0 (bgC0 d L N) (bgC1 d L N) ν
        (composeData hprec (compWeight L a₁) (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') D') ∧
      bgFieldC G0 (compWeight L a₁) ν (bgC0 d L N)
        (composeData hprec (compWeight L a₁) (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') D') =
        hprec.restrictφ (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') ∧
      (∀ y ∈ E, ∀ i, (composeData hprec (compWeight L a₁)
        (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') D').Ψ y i - D.Ψ y i = 0) ∧
      (∀ x i, (composeData hprec (compWeight L a₁)
        (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') D').h x i = D.h x i) ∧
      (∀ x ∈ dataSites G0, vn (fun i => (composeData hprec (compWeight L a₁)
        (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') D').Ψ x i - D.Ψ x i) ≤
        (2 * d + 2) * (bgK1 d L N * δ')) := by
  classical
  have hL2 : 2 ≤ L := by have := H1.hL; omega
  have hD'U : InUnionDomainC G1 (bgC0 d L N) (thm73C1 d L N) ν D' :=
    ⟨δ', ε', hδ0, hδε, hε, hδc, hνε, hD'⟩
  obtain ⟨hDuU, hfield, -⟩ := theorem73_complex ha₁ H0 H1 hprec hD'U
  have hδb : δ' ≤ bgC1 d L N := by
    have := thm73_small (L := L) (N := N) (by have := H1.hd; omega) hδ0 hδc; exact this.1
  refine ⟨hDuU, hfield, ?_, ?_, ?_⟩
  · intro y hyE i
    by_cases hyd : y ∈ dataSites G0
    · have := composeField_eq_of_layers_agree (a := compWeight L a₁)
        (fun j hj1 hj2 => (Background.compWeight_pos hL2 ha₁ hj1).ne')
        (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') D'.Ψ hE hyE hyd i
      show composeField G0 G1 _ _ D'.Ψ y i - D.Ψ y i = 0
      rw [this, hΨ y hyd]; ring
    · have h0 : composeField G0 G1 (compWeight L a₁)
          (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') D'.Ψ y i = 0 :=
        composeField_of_not_mem _ _ _ hyd i
      show composeField G0 G1 _ _ D'.Ψ y i - D.Ψ y i = 0
      rw [h0, D.Ψ_zero y hyd]; simp
  · intro x i
    show (if x ∈ G0.Ω 1 then D'.h x i else 0 : ℂ) = D.h x i
    by_cases hx : x ∈ G0.Ω 1
    · simp only [hx, ↓reduceIte]; rw [hh x hx]
    · simp only [hx, ↓reduceIte]; rw [D.h_zero x hx]; rfl
  · intro x hx
    have := composed_sub_le ha₁ H1 hprec hδ0 hδε hε hδb hνε hD' hx
    have e : (fun i => (composeData hprec (compWeight L a₁)
        (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') D').Ψ x i - D.Ψ x i) =
        fun i => composeField G0 G1 (compWeight L a₁)
          (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') D'.Ψ x i - D'.Ψ x i := by
      funext i; rw [hΨ x hx]; rfl
    rw [e]; exact this

end Change

section Step

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1))) (hk : k + 1 ≤ K)

/-- The global boundary family `𝔹^∂_{k+1}` of the step (Definition II.2.4 (iv)). -/
noncomputable abbrev bdGen :
    GeneratingSet S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (minSep S.L g.M1) :=
  genBoundary g.M1 g.c (n (k + 1)) S.L k (Hl.step k) g.hc (Hl.F.hnn k (by omega))
    Hl.F.ok.two_le_L (g.three_L_le_floor Hl (k - 1)) (Zp := Hl.F.Zpre (k + 1))
    (Omega_compl_subset_Zpre' k (Hl.step k) _ _)

include Hl in
theorem locGen_precedes_bd :
    Precedes (locGen g Hl k Zc hZc hk) (bdGen g Hl k hk) :=
  genBoundaryLocal_precedes (Hl.step k) g.hc (Hl.F.hnn k (by omega)) Hl.F.ok.two_le_L
    (g.three_L_le_floor Hl (k - 1)) (Hl.F.stepGeom (by omega)).rad.omega_rho
    (Omega_compl_subset_Zpre' k (Hl.step k) _ _) hZc

include Hl in
theorem locGen_bd_agree {x : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))}
    (hx : blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x ∈ nbhd ⌊R k⌋₊ (Zc : Set (Torus S.d (n (k + 1)))))
    (m : ℕ) :
    x ∈ (locGen g Hl k Zc hZc hk).Ω m ↔ x ∈ (bdGen g Hl k hk).Ω m :=
  genBoundaryLocal_agree (Hl.step k) g.hc (Hl.F.hnn k (by omega)) Hl.F.ok.two_le_L
    (g.three_L_le_floor Hl (k - 1)) (Hl.F.stepGeom (by omega)).rad.omega_rho
    (Omega_compl_subset_Zpre' k (Hl.step k) _ _) hZc hx m

/-- The lifted datum of the boundary family `𝔹^∂_{k+1}` for the configuration `(ψ_k, ψ_{k+1})`
(`ψ̃` of Definition II.2.7 on `𝔹^∂`). -/
noncomputable abbrev locDataBd (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (xc : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    BgData (bdGen g Hl k hk) N :=
  stepDataBd (Hl.step k) g.hc (Hl.F.hnn k (by omega)) Hl.F.ok.two_le_L
    (g.three_L_le_floor Hl (k - 1)) (Zp := Hl.F.Zpre (k + 1))
    (Omega_compl_subset_Zpre' k (Hl.step k) _ _)
    (locLiftPsi g Hl k Zc hk xc).toC (locLiftTheta g Hl k Zc hk o).toC (fun i => (hv i : ℂ))

include Hl in
theorem locData_eq_bd (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (xc : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    (∀ x ∈ dataSites (locGen g Hl k Zc hZc hk),
      (locData g Hl k Zc hZc hk o xc hv).Ψ x = (locDataBd g Hl k Zc hk o xc hv).Ψ x) ∧
    (∀ x ∈ (locGen g Hl k Zc hZc hk).Ω 1,
      (locData g Hl k Zc hZc hk o xc hv).h x = (locDataBd g Hl k Zc hk o xc hv).h x) := by
  classical
  have hprec := locGen_precedes_bd g Hl k Zc hZc hk
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have hxd : x ∈ dataSites (bdGen g Hl k hk) := by
      rcases (mem_dataSites _).1 hx with h | h
      · exact (mem_dataSites _).2 (Or.inl (hprec.mem_Ω1 h))
      · by_cases h' : x ∈ (bdGen g Hl k hk).Ω 1
        · exact (mem_dataSites _).2 (Or.inl h')
        · exact (mem_dataSites _).2 (Or.inr (mem_collar_of_not_mem hprec h h'))
    unfold locData locDataBd stepDataBd
    exact (liftMixed_Ψ _ _ _ _ _ _ hx).trans (liftMixed_Ψ _ _ _ _ _ _ hxd).symm
  · unfold locData locDataBd stepDataBd
    exact (liftMixed_h _ _ _ _ _ _ hx).trans (liftMixed_h _ _ _ _ _ _ (hprec.mem_Ω1 hx)).symm

/-- The sites of the fine cube of `y0`. -/
theorem fine_cube_mem_near {y0 : Torus S.d (n (k + 1))} {x}
    (hx : blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x = y0) :
    x ∈ stepNearSites (M1 := g.M1) (c := g.c) (L := S.L) k ({y0} : Set (Torus S.d (n (k + 1)))) :=
  mem_stepNearSites.2 ⟨x, hx, by rw [Balaban.Multiscale.torusDist_self']; norm_num⟩

include Hl hZc hk in
/-- **Theorem 4.2, Step 3 for the real step (star convention, one action cube).** -/
theorem realStep_cubeDiffStar_bound (hd : 3 ≤ S.d) (hL : 3 ≤ S.L) {Cδ : ℝ} (hCδ : 0 ≤ Cδ) :
    ∃ CF Kw δw : ℝ, 0 < CF ∧ 0 < Kw ∧ 0 < δw ∧
      ∀ {a₁ ν r δ1 ε1 δ0 ε0 δb εb β : ℝ} {y0 : Torus S.d (n (k + 1))}
        (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
        (xc : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N))
        (Q : Finset (Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)))),
        0 < a₁ →
        BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν →
        2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1) →
        y0 ∈ (Zc : Set (Torus S.d (n (k + 1)))) → nbhd 4 {y0} ⊆ (Hl.step k).Omega → 0 ≤ r →
        (locLiftTheta g Hl k Zc hk o).toC ∈ DeltaC (q := k + 1) (M1 := g.M1) (N₁ := g.c * n (k + 1))
          (L := S.L) (compWeight S.L a₁) ν r (fun i => (hv i : ℂ)) g.c (n (k + 1)) y0 →
        0 < δ1 → δ1 ≤ ε1 → ε1 ≤ bgC0 S.d S.L N → δ1 ≤ thm73C1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε1 ^ 2 ≤ δ1 ^ 2 →
        InDomainC (locGen g Hl k Zc hZc hk) ν δ1 ε1 (locData g Hl k Zc hZc hk o xc hv) →
        0 < δ0 → δ0 ≤ ε0 → ε0 ≤ bgC0 S.d S.L N → δ0 ≤ bgC1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε0 ^ 2 ≤ δ0 ^ 2 →
        InDomainC (genCubeLoc g k y0) ν δ0 ε0
          (liftSingle (genCubeLoc g k y0) (locLiftTheta g Hl k Zc hk o).toC (fun i => (hv i : ℂ))) →
        0 < δb → δb ≤ εb → εb ≤ bgC0 S.d S.L N → δb ≤ thm73C1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * εb ^ 2 ≤ δb ^ 2 →
        InDomainC (bdGen g Hl k hk) ν δb εb (locDataBd g Hl k Zc hk o xc hv) →
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
        ‖(β : ℂ) * (cubeActionStar (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) ν Q
              (locData g Hl k Zc hZc hk o xc hv).Ψ (locData g Hl k Zc hZc hk o xc hv).h
              (bgFieldC (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
                (composeData (locGen_precedes_bd g Hl k Zc hZc hk) (compWeight S.L a₁)
                  (bgFieldC (bdGen g Hl k hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
                    (locDataBd g Hl k Zc hk o xc hv)) (locDataBd g Hl k Zc hk o xc hv))) -
            cubeActionStar (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) ν Q
              (locData g Hl k Zc hZc hk o xc hv).Ψ (locData g Hl k Zc hZc hk o xc hv).h
              (bgFieldC (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
                (locData g Hl k Zc hZc hk o xc hv)))‖ ≤
          CF * β * Q.card * (r + transferShift S.d S.L N (k + 1) ν Kw δ1
            (stepDist S.L g.M1 g.c k 1 (minSep S.L g.M1))) ^ 2 *
            Real.exp (-(gammaW S.d * stepDist S.L g.M1 g.c k ⌊R k⌋₊ (minSep S.L g.M1))) := by
  classical
  obtain ⟨CF, δws, hCF, hδws, h3⟩ := cubeDiffStar_step3_quadratic_gen (N := N) (d := S.d) (L := S.L)
    hd hL hCδ
  obtain ⟨Kw, δwr, hKw, hδwr, htr⟩ := regIneq_locGen_of_deltaC g Hl k Zc hZc hk (N := N) hd hL
  refine ⟨CF, Kw, min δwr δws, hCF, hKw, lt_min hδwr hδws, ?_⟩
  intro a₁ ν r δ1 ε1 δ0 ε0 δb εb β y0 o xc hv Q ha₁ H hsep hy0 hΩ hr hΔ hδ10 hδε1 hε1 hδ1c hνε1 hD1
    hδ00 hδε0 hε0 hδ0c hνε0 hD0 hδb0 hδεb hεb hδbc hνεb hDb hK0 hKw0 hK1 hKw1 hK11 hKw11 hKb hKwb
    hQ hCr hβ
  have hmin1 : ∀ x : ℝ, x ≤ min δwr δws → x ≤ δwr := fun x h => h.trans (min_le_left _ _)
  have hmin2 : ∀ x : ℝ, x ≤ min δwr δws → x ≤ δws := fun x h => h.trans (min_le_right _ _)
  -- regularity of the local background on the cube neighbourhood
  have hreg := htr (a₁ := a₁) (ν := ν) (r := r) (δ1 := δ1) (ε1 := ε1) (δ0 := δ0) (ε0 := ε0) (y0 := y0)
    o xc hv ha₁ H hsep hy0 hΩ hΔ hδ10 hδε1 hε1 hδ1c hνε1 hD1 hδ00 hδε0 hε0 hδ0c hνε0 hD0 hK0
    (hmin1 _ hKw0) hK1 (hmin1 _ hKw1)
  -- the data change of the composition
  have hprec := locGen_precedes_bd g Hl k Zc hZc hk
  obtain ⟨hΨ, hh⟩ := locData_eq_bd g Hl k Zc hZc hk o xc hv
  obtain ⟨hDuU, hfield, hsupp, hhh, hbd⟩ := composed_change ha₁ H H hprec hδb0 hδεb hεb hδbc hνεb hDb
    hΨ hh (E := {x | blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x ∈
      nbhd ⌊R k⌋₊ (Zc : Set (Torus S.d (n (k + 1))))})
    (fun x hx m _ _ => locGen_bd_agree g Hl k Zc hZc hk hx m)
  obtain ⟨δu, εu, hδu0, hδuε, hεu, hδu1, hνεu, hDu⟩ := hDuU
  have hL2 := Hl.F.ok.two_le_L
  have hρ1 : 1 ≤ ⌊R k⌋₊ := by have := g.three_L_le_floor Hl k; omega
  have hϱ : 1 ≤ minSep S.L g.M1 := one_le_minSep S.L g.M1
  have hδb1 : δ1 ≤ bgC1 S.d S.L N := (thm73_small (L := S.L) (N := N) (by omega) hδ10 hδ1c).1
  have hShift0 : 0 ≤ transferShift S.d S.L N (k + 1) ν Kw δ1
      (stepDist S.L g.M1 g.c k 1 (minSep S.L g.M1)) := by
    unfold transferShift
    have := bgK1_pos S.d S.L N
    have := cF_pos S.d S.L
    positivity
  have hr' : 0 ≤ r + transferShift S.d S.L N (k + 1) ν Kw δ1
      (stepDist S.L g.M1 g.c k 1 (minSep S.L g.M1)) := by linarith
  have hDist0 := stepDist_nonneg (L := S.L) (M1 := g.M1) (c := g.c) (k := k) hρ1 hϱ
  have hdist := step_dist_premise (M1 := g.M1) (c := g.c) (n1 := n (k + 1)) (L := S.L) k
    (locGen g Hl k Zc hZc hk) hϱ (Zc : Set (Torus S.d (n (k + 1)))) ⌊R k⌋₊
  have hsub : ({y0} : Set (Torus S.d (n (k + 1)))) ⊆ (Zc : Set (Torus S.d (n (k + 1)))) := by
    intro z hz; have : z = y0 := hz; rw [this]; exact hy0
  have hRsub := stepNearSites_mono (M1 := g.M1) (c := g.c) (L := S.L) (k := k) hsub
  have hQtop : ∀ x ∈ Q, x ∈ (locGen g Hl k Zc hZc hk).Ω (k + 1) := fun x hx =>
    (genCubeLoc_top_subset g Hl k Zc hZc hk hy0 hΩ (by
      rw [hQ x hx]; exact mem_nbhd.2 ⟨y0, rfl, by simp [supDist_self]⟩)).2
  refine h3 (N₁ := g.M1 * (g.c * n (k + 1))) (m₁ := 0) (by simp) H hsep hδ10 hδε1 hε1 hδb1 hνε1 hD1
    hδu0 hδuε hεu hδu1 hνεu hDu hK11 (hmin2 _ hKw11)
    (stepFarSites (M1 := g.M1) (c := g.c) (L := S.L) k (Zc : Set (Torus S.d (n (k + 1)))) ⌊R k⌋₊)
    ?_ (fun x i => by ring) hhh (by have := bgK1_pos S.d S.L N; positivity) hKb (hmin2 _ hKwb) hbd
    Q (stepNearSites (M1 := g.M1) (c := g.c) (L := S.L) k ({y0} : Set (Torus S.d (n (k + 1)))))
    hr' hDist0 hCr ?_ ?_ ?_ ?_ hreg ?_ β hβ
  · intro y hy
    have hyE : blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) y ∈
        nbhd ⌊R k⌋₊ (Zc : Set (Torus S.d (n (k + 1)))) := by
      by_contra h; exact hy (mem_stepFarSites.2 h)
    funext i
    exact hsupp y hyE i
  · exact fun x hx => fine_cube_mem_near g k (hQ x hx)
  · intro x hx μ
    exact mem_stepNearSites.2 ⟨x, hQ x hx, by
      rw [Green.torusDist_comm_gen]; exact (adj_add_single x μ).torusDist_le⟩
  · intro x μ hx
    exact mem_stepNearSites.2 ⟨x + Pi.single μ 1, hQ _ hx, (adj_add_single x μ).torusDist_le⟩
  · intro x hx _ y hy
    have hli : (locGen g Hl k Zc hZc hk).layerIndex x = k + 1 :=
      (locGen g Hl k Zc hZc hk).layerIndex_eq (by omega) le_rfl
        ((GeneratingSet.mem_layer _).2 ⟨hQtop x hx, by
          rw [(locGen g Hl k Zc hZc hk).top]; exact Finset.notMem_empty _⟩)
    rw [hli] at hy
    have hb : jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (k + 1) y =
        jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (k + 1) x := GeneratingSet.mem_blk.1 hy
    have hcu : fineCubeIdx g.M1 (g.c * n (k + 1)) S.L (k + 1) (k + 1) y =
        fineCubeIdx g.M1 (g.c * n (k + 1)) S.L (k + 1) (k + 1) x := by
      rw [fineCubeIdx_eq_comp le_rfl, fineCubeIdx_eq_comp le_rfl, hb]
    have hU := isCubeUnion_fineK1 (M1 := g.M1) (c := g.c) (n1 := n (k + 1)) (L := S.L) (k := k)
      ({y0} : Set (Torus S.d (n (k + 1))))
    have hxU : x ∈ fineK1 g.M1 g.c (n (k + 1)) S.L k ({y0} : Set (Torus S.d (n (k + 1)))) := by
      rw [mem_fineK1]; exact hQ x hx
    have hyU := (hU y x hcu).2 hxU
    rw [mem_fineK1] at hyU
    exact fine_cube_mem_near g k hyU
  · intro y hy hyΩ w hw
    exact hdist y (hRsub hy) hyΩ w hw

end Step

end Balaban.Fluctuation
