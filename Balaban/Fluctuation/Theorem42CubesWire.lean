/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Theorem42CubesAgg
public import Balaban.Fluctuation.Theorem42

/-!
# The real step as an instance of Theorem 4.2 (FLUCTUATION.md §4.2)

* `torusCast`, `boxSites`, `GeneratingSet.castSize`: the cast of the real-step torus
  `Torus d (N₀ * L^K)`, `N₀ = M₁ (c n_{k+1})`, to the localization torus `CTorus d L N₁ m₁ K`
  (`N₀ = N₁ L^{m₁}`): the action cube `Q_b` is the image of the box `b + [0, L a_j)^d`.
* `realCubeAct`: the undecoupled cube differences `act b = F_{Q_b}` of the real step.
* `realStep_response_nonempty`: the `s = 1` slice of the decoupled weighted response
  (`at_one`, holomorphy in `u`, the bound `C_b`) is PROVED for the bulk cubes of H7; the structure
  `DecoupledCubeResponse` is inhabited for the actual step.
* `realStep_theorem42_undecoupled`: Theorem 4.2 for the `s`-independent family (decoupling vector
  ignored) with the trivial agreement relation (equal action differences).

What remains of the decoupled response is exactly the `s`-dependence off `s = 1`: holomorphy of
`F b u s` jointly in `(u, s)`, the bound `‖F b u s‖ ≤ C_b` on the polydisc `|s_i| < e^{κ₁}`, and
locality (AE) of `F b` with respect to a genuine agreement relation of configurations
(OPEN-NC-MIXED); `realStep_theorem42_of_input` is `theorem42_of_input` for the real `act`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.LargeField
  RegionHistory

set_option linter.unusedSectionVars false

/-- Cast of a torus point along an equality of sizes. -/
def torusCast {d a b : ℕ} (h : a = b) (x : Torus d a) : Torus d b := h ▸ x

/-- Cast of a generating set along an equality of torus sizes. -/
def _root_.Balaban.Multiscale.GeneratingSet.castSize {d L N N' k : ℕ} [NeZero N] [NeZero N']
    [NeZero L] {ϱ : ℝ} (h : N = N') (G : GeneratingSet d L N k ϱ) :
    GeneratingSet d L N' k ϱ := by
  subst h; exact G

open Classical in
/-- The sites of the real-step torus `Torus d (N₀ * L^K)` of the box `b + [0, s)^d` of the
localization torus (`N₀ = N₁ L^{m₁}`). -/
noncomputable def boxSites {d L N₀ N₁ m₁ K : ℕ} (hN : N₀ = N₁ * L ^ m₁) (b : CTorus d L N₁ m₁ K)
    (s : ℕ) : Finset (Torus d (N₀ * L ^ K)) :=
  Finset.univ.image fun w : Fin d → Fin s =>
    torusCast (d := d) (by rw [hN]) (b + natT (fun μ => (w μ : ℕ)))

theorem card_boxSites_le {d L N₀ N₁ m₁ K : ℕ} (hN : N₀ = N₁ * L ^ m₁) (b : CTorus d L N₁ m₁ K)
    (s : ℕ) : (boxSites hN b s).card ≤ s ^ d := by
  classical
  unfold boxSites
  refine Finset.card_image_le.trans ?_
  simp

section Real

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hk : k + 1 ≤ K)
  {N₁ m₁ : ℕ} [NeZero N₁] (hN : g.M1 * (g.c * n (k + 1)) = N₁ * S.L ^ m₁) (m₀ j : ℕ)

/-- **The undecoupled cube differences of the real step**: `act b = F_{Q_b}`, `Q_b` the sites of the
action cube `X_b = box b (L a_j)`. -/
noncomputable def realCubeAct (a₁ ν β : ℝ) (b : CTorus S.d S.L N₁ m₁ (k + 1))
    (u : StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N) : ℂ :=
  realStepAct g Hl k Zc hZc hk a₁ ν β
    (boxSites hN b (S.L * cellSide S.L m₀ m₁ j)) u

/-- The generating set of the localization torus: the cast of the local family. -/
noncomputable def realGenC : GeneratingSet S.d S.L (N₁ * S.L ^ m₁) (k + 1) (minSep S.L g.M1) :=
  GeneratingSet.castSize hN (locGen g Hl k Zc hZc hk)

/-- The bound constant `C_b = C_F β |Q|_max (r + shift)² e^{-γ_w D}` of Step 3. -/
noncomputable def realCubeCb (CF Kw ν r δ1 β : ℝ) : ℝ :=
  CF * β * ((S.L * cellSide S.L m₀ m₁ j) ^ S.d : ℕ) *
    (r + transferShift S.d S.L N (k + 1) ν Kw δ1
      (stepDist S.L g.M1 g.c k 1 (minSep S.L g.M1))) ^ 2 *
    Real.exp (-(gammaW S.d * stepDist S.L g.M1 g.c k ⌊R k⌋₊ (minSep S.L g.M1)))

include Hl hZc hk in
/-- **The `s = 1` slice of the decoupled weighted response of the real step is proved for the bulk
cubes** (FLUCTUATION §4.2, Steps 3-4).  For a family `𝒬` of action cubes `X_b = box b (L a_j)`, each
inside a `π_{k+1}`-cube `y0 b` with `(y0 b)^{∼4} ⊂ Ω_{k+1}`, the structure `DecoupledCubeResponse`
for the real `act = realCubeAct` is inhabited (by the `s`-independent family `F b u s = act b u`),
with the bound `C_b = realCubeCb`. -/
theorem realStep_response_nonempty (hd : 3 ≤ S.d) (hL : 3 ≤ S.L) {Cδ : ℝ} (hCδ : 0 ≤ Cδ)
    (a₁ ν β : ℝ) :
    ∃ CF Kw δw : ℝ, 0 < CF ∧ 0 < Kw ∧ 0 < δw ∧
      ∀ {ι : Type*} [DecidableEq ι] [Fintype ι]
        (c : ι → ℕ × CTorus S.d S.L N₁ m₁ (k + 1)) {r δ1 ε1 δ0 ε0 δb εb κ₁ : ℝ}
        (𝒬 : Finset (CTorus S.d S.L N₁ m₁ (k + 1)))
        (y0 : CTorus S.d S.L N₁ m₁ (k + 1) → Torus S.d (n (k + 1)))
        (Sdom : Set (StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N)), IsOpen Sdom →
        0 < a₁ →
        BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν →
        2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1) → 0 ≤ r →
        (∀ b ∈ 𝒬, y0 b ∈ (Zc : Set (Torus S.d (n (k + 1))))) →
        (∀ b ∈ 𝒬, nbhd 4 {y0 b} ⊆ (Hl.step k).Omega) →
        0 < δ1 → δ1 ≤ ε1 → ε1 ≤ bgC0 S.d S.L N → δ1 ≤ thm73C1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε1 ^ 2 ≤ δ1 ^ 2 →
        0 < δ0 → δ0 ≤ ε0 → ε0 ≤ bgC0 S.d S.L N → δ0 ≤ bgC1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε0 ^ 2 ≤ δ0 ^ 2 →
        0 < δb → δb ≤ εb → εb ≤ bgC0 S.d S.L N → δb ≤ thm73C1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * εb ^ 2 ≤ δb ^ 2 →
        (∀ u ∈ Sdom,
          InDomainC (locGen g Hl k Zc hZc hk) ν δ1 ε1 (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2) ∧
          InDomainC (bdGen g Hl k hk) ν δb εb (bdDataC g Hl k hk u.1 u.2.1 u.2.2)) →
        (∀ u ∈ Sdom, ∀ b ∈ 𝒬,
          u.2.1 ∈ DeltaC (q := k + 1) (M1 := g.M1) (N₁ := g.c * n (k + 1))
            (L := S.L) (compWeight S.L a₁) ν r u.2.2 g.c (n (k + 1)) (y0 b) ∧
          InDomainC (genCubeLoc g k (y0 b)) ν δ0 ε0
            (liftSingle (genCubeLoc g k (y0 b)) u.2.1 u.2.2)) →
        bgK1 S.d S.L N * δ0 ≤ deltaStar S.d S.L N → bgK1 S.d S.L N * δ0 ≤ δw →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δ1) ≤ deltaStar S.d S.L N →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δ1) ≤ δw →
        bgK1 S.d S.L N * δ1 ≤ deltaStar S.d S.L N → bgK1 S.d S.L N * δ1 ≤ δw →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δb) ≤ deltaStar S.d S.L N →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δb) ≤ δw →
        (∀ b ∈ 𝒬, ∀ x ∈ boxSites hN b (S.L * cellSide S.L m₀ m₁ j),
          blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x = y0 b) →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δb) ≤ Cδ * (r + transferShift S.d S.L N (k + 1) ν Kw δ1
          (stepDist S.L g.M1 g.c k 1 (minSep S.L g.M1))) →
        0 ≤ β →
        Nonempty (DecoupledCubeResponse (realGenC g Hl k Zc hZc hk hN) m₀ j c 𝒬 Sdom κ₁
          (realCubeCb (N := N) (m₁ := m₁) g k m₀ j CF Kw ν r δ1 β)
          (fun _ u u' => ∀ b ∈ 𝒬, realCubeAct g Hl k Zc hZc hk hN m₀ j a₁ ν β b u =
            realCubeAct g Hl k Zc hZc hk hN m₀ j a₁ ν β b u')
          (realCubeAct g Hl k Zc hZc hk hN m₀ j a₁ ν β)
          (fun b u _ => realCubeAct g Hl k Zc hZc hk hN m₀ j a₁ ν β b u)) := by
  obtain ⟨CF, Kw, δw, hCF, hKw, hδw, hmain⟩ := realStepAct_bound_agg g Hl k Zc hZc hk hd hL hCδ
  refine ⟨CF, Kw, δw, hCF, hKw, hδw, ?_⟩
  intro ι _ _ c r δ1 ε1 δ0 ε0 δb εb κ₁ 𝒬 y0 Sdom hopen ha₁ H hsep hr hy0 hΩ hδ10 hδε1 hε1 hδ1c hνε1
    hδ00 hδε0 hε0 hδ0c hνε0 hδb0 hδεb hεb hδbc hνεb hDom hDelta hK0 hKw0 hK1 hKw1 hK11 hKw11 hKb
    hKwb hQ hCr hβ
  have hbd := hmain 𝒬 y0 (fun b => boxSites hN b (S.L * cellSide S.L m₀ m₁ j))
    (Qmax := ((S.L * cellSide S.L m₀ m₁ j) ^ S.d : ℕ)) Sdom ha₁ H hsep hr hy0 hΩ hδ10 hδε1 hε1
    hδ1c hνε1 hδ00 hδε0 hε0 hδ0c hνε0 hδb0 hδεb hεb hδbc hνεb hDom hDelta hK0 hKw0 hK1 hKw1 hK11
    hKw11 hKb hKwb hQ (fun b _ => by exact_mod_cast card_boxSites_le hN b _) hCr hβ
  have hδ1b : δ1 ≤ bgC1 S.d S.L N := (thm73_small (L := S.L) (N := N) (by omega) hδ10 hδ1c).1
  have hδbb : δb ≤ bgC1 S.d S.L N := (thm73_small (L := S.L) (N := N) (by omega) hδb0 hδbc).1
  have han := realStepAct_analytic_agg g Hl k Zc hZc hk H 𝒬
    (fun b => boxSites hN b (S.L * cellSide S.L m₀ m₁ j)) hopen (β := β)
    (fun u hu => ⟨δ1, ε1, hδ10, hδε1, hε1, hδ1b, hνε1, (hDom u hu).1⟩)
    (fun u hu => ⟨δb, εb, hδb0, hδεb, hεb, hδbb, hνεb, (hDom u hu).2⟩)
  exact DecoupledCubeResponse.nonempty_of_undecoupled (G := realGenC g Hl k Zc hZc hk hN)
    (m₀ := m₀) (j := j) (c := c) 𝒬 κ₁ _ (realCubeAct g Hl k Zc hZc hk hN m₀ j a₁ ν β)
    han (fun b hb u hu => by
      unfold realCubeAct realCubeCb
      exact hbd b hb u hu)

include Hl hZc hk in
/-- **Theorem 4.2 for the real step, `s`-independent family** (the decoupling vector is ignored and
the agreement relation is "equal cube action differences"): the expansion (4.2), the bound (4.3),
holomorphy and locality of the traces `Δ(T)`, for the bulk cubes, with NO decoupled premise.  The
locality is the trivial one; the genuine statement is `realStep_theorem42_of_input`. -/
theorem realStep_theorem42_undecoupled (hd : 3 ≤ S.d) (hL : 3 ≤ S.L) {Cδ : ℝ} (hCδ : 0 ≤ Cδ)
    (a₁ ν β : ℝ) :
    ∃ CF Kw δw : ℝ, 0 < CF ∧ 0 < Kw ∧ 0 < δw ∧
      ∀ {ι : Type*} [DecidableEq ι] [Fintype ι]
        (c : ι → ℕ × CTorus S.d S.L N₁ m₁ (k + 1)) {r δ1 ε1 δ0 ε0 δb εb κ₁ : ℝ}
        (𝒬 : Finset (CTorus S.d S.L N₁ m₁ (k + 1)))
        (y0 : CTorus S.d S.L N₁ m₁ (k + 1) → Torus S.d (n (k + 1)))
        (Sdom : Set (StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N)),
        IsOpen Sdom →
        0 < a₁ →
        BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν →
        2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1) → 0 ≤ r →
        (∀ b ∈ 𝒬, y0 b ∈ (Zc : Set (Torus S.d (n (k + 1))))) →
        (∀ b ∈ 𝒬, nbhd 4 {y0 b} ⊆ (Hl.step k).Omega) →
        0 < δ1 → δ1 ≤ ε1 → ε1 ≤ bgC0 S.d S.L N → δ1 ≤ thm73C1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε1 ^ 2 ≤ δ1 ^ 2 →
        0 < δ0 → δ0 ≤ ε0 → ε0 ≤ bgC0 S.d S.L N → δ0 ≤ bgC1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε0 ^ 2 ≤ δ0 ^ 2 →
        0 < δb → δb ≤ εb → εb ≤ bgC0 S.d S.L N → δb ≤ thm73C1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * εb ^ 2 ≤ δb ^ 2 →
        (∀ u ∈ Sdom,
          InDomainC (locGen g Hl k Zc hZc hk) ν δ1 ε1 (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2) ∧
          InDomainC (bdGen g Hl k hk) ν δb εb (bdDataC g Hl k hk u.1 u.2.1 u.2.2)) →
        (∀ u ∈ Sdom, ∀ b ∈ 𝒬,
          u.2.1 ∈ DeltaC (q := k + 1) (M1 := g.M1) (N₁ := g.c * n (k + 1))
            (L := S.L) (compWeight S.L a₁) ν r u.2.2 g.c (n (k + 1)) (y0 b) ∧
          InDomainC (genCubeLoc g k (y0 b)) ν δ0 ε0
            (liftSingle (genCubeLoc g k (y0 b)) u.2.1 u.2.2)) →
        bgK1 S.d S.L N * δ0 ≤ deltaStar S.d S.L N → bgK1 S.d S.L N * δ0 ≤ δw →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δ1) ≤ deltaStar S.d S.L N →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δ1) ≤ δw →
        bgK1 S.d S.L N * δ1 ≤ deltaStar S.d S.L N → bgK1 S.d S.L N * δ1 ≤ δw →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δb) ≤ deltaStar S.d S.L N →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δb) ≤ δw →
        (∀ b ∈ 𝒬, ∀ x ∈ boxSites hN b (S.L * cellSide S.L m₀ m₁ j),
          blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x = y0 b) →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δb) ≤ Cδ * (r + transferShift S.d S.L N (k + 1) ν Kw δ1
          (stepDist S.L g.M1 g.c k 1 (minSep S.L g.M1))) →
        0 ≤ β →
        ∀ (Ω : Set (CTorus S.d S.L N₁ m₁ (k + 1))) {κ κ' : ℝ},
          Ω ⊆ ((realGenC g Hl k Zc hZc hk hN).layer (k + 1) :
            Set (CTorus S.d S.L N₁ m₁ (k + 1))) →
          (4 * S.d * S.L * (S.L : ℝ) ^ (m₀ + m₁) : ℝ) ≤ minSep S.L g.M1 →
          (∀ b ∈ 𝒬, CovSetup (realGenC g Hl k Zc hZc hk hN) m₀ j
            (Localization.box b (S.L * cellSide S.L m₀ m₁ j)) {b}) →
          (∀ i, c i ∈ cubeIdx (realGenC g Hl k Zc hZc hk hN)) →
          Function.Injective c →
          (∀ b ∈ 𝒬, ∀ i, Disjoint (Pset m₁ (c i))
            (X1 (realGenC g Hl k Zc hZc hk hN) m₀ j ({b} : Set (CTorus S.d S.L N₁ m₁ (k + 1))))) →
          3 ≤ κ → 4 * S.d * (((2 * S.L + 1) ^ S.d : ℕ) : ℝ) * κ ≤ κ₁ →
          1 ≤ (κ₁ / 2 - 1) / 2 →
          Real.log ((((2 * S.L + 1) ^ S.d : ℕ) : ℝ) * (((S.L ^ m₀) ^ S.d : ℕ) : ℝ)) ≤
            (κ₁ / 2 - 1) / 2 →
          0 ≤ κ' → aMulti S.d S.L + 2 ≤ 2 * κ - κ' →
          Expansion42 (realGenC g Hl k Zc hZc hk hN) m₀ j c 𝒬 Ω κ'
            (realCubeCb (N := N) (m₁ := m₁) g k m₀ j CF Kw ν r δ1 β * cubeCount S.d S.L (k + 1) j *
              K0Multi S.d S.L) Sdom
            (realCubeAct g Hl k Zc hZc hk hN m₀ j a₁ ν β)
            (fun b u _ => realCubeAct g Hl k Zc hZc hk hN m₀ j a₁ ν β b u)
            (fun _ u u' => ∀ b ∈ 𝒬, realCubeAct g Hl k Zc hZc hk hN m₀ j a₁ ν β b u =
              realCubeAct g Hl k Zc hZc hk hN m₀ j a₁ ν β b u') := by
  obtain ⟨CF, Kw, δw, hCF, hKw, hδw, hnon⟩ :=
    realStep_response_nonempty g Hl k Zc hZc hk hN m₀ j hd hL hCδ a₁ ν β
  refine ⟨CF, Kw, δw, hCF, hKw, hδw, ?_⟩
  intro ι _ _ c r δ1 ε1 δ0 ε0 δb εb κ₁ 𝒬 y0 Sdom hopen ha₁ H hsep hr hy0 hΩ' hδ10 hδε1 hε1 hδ1c hνε1
    hδ00 hδε0 hε0 hδ0c hνε0 hδb0 hδεb hεb hδbc hνεb hDom hDelta hK0 hKw0 hK1 hKw1 hK11 hKw11 hKb
    hKwb hQ hCr hβ Ω κ κ' hΩ hϱ hS hc hcinj hdisj hκ hκ₁ h1 hlog hκ'0 hκm
  obtain ⟨Rr⟩ := hnon c 𝒬 y0 Sdom hopen ha₁ H hsep hr hy0 hΩ' hδ10 hδε1 hε1 hδ1c hνε1
    hδ00 hδε0 hε0 hδ0c hνε0 hδb0 hδεb hεb hδbc hνεb hDom hDelta hK0 hKw0 hK1 hKw1 hK11 hKw11 hKb
    hKwb hQ hCr hβ
  have hCb : 0 ≤ realCubeCb (N := N) (m₁ := m₁) g k m₀ j CF Kw ν r δ1 β := by
    unfold realCubeCb; have := hCF.le; positivity
  exact theorem42_of_input 𝒬 Ω hΩ hϱ hd hL hS hc hcinj hdisj hκ hκ₁ h1 hlog hCb hκ'0 hκm
    (Ag := fun _ u u' => ∀ b ∈ 𝒬, realCubeAct g Hl k Zc hZc hk hN m₀ j a₁ ν β b u =
      realCubeAct g Hl k Zc hZc hk hN m₀ j a₁ ν β b u')
    (AgY := fun _ u u' => ∀ b ∈ 𝒬, realCubeAct g Hl k Zc hZc hk hN m₀ j a₁ ν β b u =
      realCubeAct g Hl k Zc hZc hk hN m₀ j a₁ ν β b u')
    (fun C u _ b _ => rfl) (fun b _ C u u' h => h) Rr

include Hl hZc hk in
/-- **Theorem 4.2 for the real step, conditional on the decoupled weighted response**
(OPEN-NC-MIXED): `theorem42_of_input` with `act = realCubeAct`.  The remaining premise `R` is
exactly the `s`-dependent extension `F b u s` of `act b u = F b u 1` (holomorphic in `(u, s)`,
bounded by `C_b` on the polydisc, local for a genuine agreement relation); its `s = 1` slice is
`realStep_response_nonempty`. -/
theorem realStep_theorem42_of_input {ι : Type*} [DecidableEq ι] [Fintype ι]
    (c : ι → ℕ × CTorus S.d S.L N₁ m₁ (k + 1))
    (𝒬 : Finset (CTorus S.d S.L N₁ m₁ (k + 1)))
    (Ω : Set (CTorus S.d S.L N₁ m₁ (k + 1)))
    (hΩ : Ω ⊆ ((realGenC g Hl k Zc hZc hk hN).layer (k + 1) :
      Set (CTorus S.d S.L N₁ m₁ (k + 1))))
    (hϱ : (4 * S.d * S.L * (S.L : ℝ) ^ (m₀ + m₁) : ℝ) ≤ minSep S.L g.M1)
    (hd : 3 ≤ S.d) (hL : 3 ≤ S.L)
    (hS : ∀ b ∈ 𝒬, CovSetup (realGenC g Hl k Zc hZc hk hN) m₀ j
      (Localization.box b (S.L * cellSide S.L m₀ m₁ j)) {b})
    (hc : ∀ i, c i ∈ cubeIdx (realGenC g Hl k Zc hZc hk hN))
    (hcinj : Function.Injective c)
    (hdisj : ∀ b ∈ 𝒬, ∀ i, Disjoint (Pset m₁ (c i))
      (X1 (realGenC g Hl k Zc hZc hk hN) m₀ j ({b} : Set (CTorus S.d S.L N₁ m₁ (k + 1)))))
    {κ κ₁ Cb κ' : ℝ} (hκ : 3 ≤ κ)
    (hκ₁ : 4 * S.d * (((2 * S.L + 1) ^ S.d : ℕ) : ℝ) * κ ≤ κ₁)
    (h1 : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * S.L + 1) ^ S.d : ℕ) : ℝ) * (((S.L ^ m₀) ^ S.d : ℕ) : ℝ)) ≤
      (κ₁ / 2 - 1) / 2)
    (hCb : 0 ≤ Cb) (hκ'0 : 0 ≤ κ') (hκm : aMulti S.d S.L + 2 ≤ 2 * κ - κ')
    {Sdom : Set (StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N)} {a₁ ν β : ℝ}
    {F : CTorus S.d S.L N₁ m₁ (k + 1) →
      StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N → (ι → ℂ) → ℂ}
    {Ag : Finset ι → StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N →
      StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N → Prop}
    {AgY : Set (CTorus S.d S.L N₁ m₁ (k + 1)) →
      StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N →
      StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N → Prop}
    (hrefl : ∀ C u, u ∈ Sdom → Ag C u u)
    (hlink : ∀ b ∈ 𝒬, ∀ C u u',
      AgY (Ysites (realGenC g Hl k Zc hZc hk hN) m₀ c (X1 (realGenC g Hl k Zc hZc hk hN) m₀ j
        ({b} : Set (CTorus S.d S.L N₁ m₁ (k + 1)))) C) u u' → Ag C u u')
    (R : DecoupledCubeResponse (realGenC g Hl k Zc hZc hk hN) m₀ j c 𝒬 Sdom κ₁ Cb Ag
      (realCubeAct g Hl k Zc hZc hk hN m₀ j a₁ ν β) F) :
    Expansion42 (realGenC g Hl k Zc hZc hk hN) m₀ j c 𝒬 Ω κ'
      (Cb * cubeCount S.d S.L (k + 1) j * K0Multi S.d S.L) Sdom
      (realCubeAct g Hl k Zc hZc hk hN m₀ j a₁ ν β) F AgY :=
  theorem42_of_input 𝒬 Ω hΩ hϱ hd hL hS hc hcinj hdisj hκ hκ₁ h1 hlog hCb hκ'0 hκm hrefl hlink R

end Real

end Balaban.Fluctuation
