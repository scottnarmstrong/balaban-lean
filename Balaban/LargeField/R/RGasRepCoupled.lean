/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RopRestricted
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The output of `R` for several components coupled through the internal variables (W968)

`notes/phase1/LF4R-PLAN.md`, status W968 (blocker 4, the representation of the output of `R`).  The term
`ρ(𝔸, σ)` of a history is an integral over internal variables `ξ` of the product of the kernels of the components
sent to `R` and of a coupling `f` (the boundary terms, the other components and the small-field factor of the term,
P7 (3.6)), which does not read `ψ_k` on the boxes `Z₀(c)` integrated by `R` (Lemma III.8.4 (i)).  `R` then acts on
each kernel separately, inside the integral over `ξ`:

* `Rop_integral_coupling`: for any `RDecomp`, `R[∫ ρ_ξ g_ξ] = ∫ R[ρ_ξ] g_ξ` when the coupling `g_ξ` reads only the
  variables `ψ_k↾𝒵^c_{σ,0}` that `R` does not integrate (Fubini);
* `Rop_famDecompRestricted_coupled`: with `Rop_famDecompRestricted_factor`, the restricted `R` of a coupled term is
  `∫ dξ ∏_c R_c[K_c(·, ξ)](ψ↾V_c) · f(ψ, ξ)`;
* `mul_Rop_remDecomp_eq_removedK`: the part `u = χ_{Z''}` of the one-component `R` of a kernel at fixed internal
  variables is `ρ_{k,0}(Z) e^{-EZ} K^rem`;
* `prod_mul_Rop_famDecompRestricted_coupled`: **the per-history identity for several components with couplings**,
  `∏_c u_c · R[ρ(𝔸, σ)](ψ) = ∏_c ρ_{k,0}(Z_c) e^{-EZ_c} · ∫ dξ ∏_c K^rem_c(ψ↾V_c, ξ) · f(ψ, ξ)`
  (P7 (3.6)-(3.7) and the bracket of (3.26), before the recombination (3.21)-(3.25)).

The output `ψ` is not integrated: in the output of `R` the removed weights are functions of the outputs and of the
internal variables, and the coupling `f` reads the internal variables of several components at once.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory

section Coupling

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- The formula (1.6) of `Rop` (P7 (1.6)), unfolded at `ψ`. -/
theorem Rop_eq_prod (D : RDecomp ν) (ρ : Ω → ℝ) (ψ : Ω) :
    Rop D ρ ψ = (∏ c, D.r c ((D.e ψ).1 c) (D.e ψ).2) *
      ((∫ x, ρ (D.e.symm (x, (D.e ψ).2)) ∂(Measure.pi D.μ)) /
        ∏ c, ∫ w, D.r c w (D.e ψ).2 ∂(D.μ c)) := rfl

/-- **`R` commutes with the integral over internal variables of a coupling that `R` does not integrate**
(Definition III.8.3, Fubini): if `ρ(ψ) = ∫ dξ ρ_ξ(ψ) g_ξ(ψ↾𝒵^c_{σ,0})` with the integrand integrable on the product of
the variables of `𝒵_{σ,0}` and of `ξ` (at the outside variables of `ψ`), then
`R[ρ](ψ) = ∫ dξ R[ρ_ξ](ψ) g_ξ(ψ↾𝒵^c_{σ,0})`. -/
theorem Rop_integral_coupling (D : RDecomp ν) {Ξ : Type*} [MeasurableSpace Ξ] (μΞ : Measure Ξ)
    [SFinite μΞ] (ρξ : Ξ → Ω → ℝ) (g : Ξ → D.Y → ℝ) (ρ : Ω → ℝ)
    (hρ : ∀ ψ, ρ ψ = ∫ ξ, ρξ ξ ψ * g ξ (D.e ψ).2 ∂μΞ) (ψ : Ω)
    (hint : Integrable (fun q : (∀ c, D.W c) × Ξ =>
        ρξ q.2 (D.e.symm (q.1, (D.e ψ).2)) * g q.2 (D.e ψ).2) ((Measure.pi D.μ).prod μΞ)) :
    Rop D ρ ψ = ∫ ξ, Rop D (ρξ ξ) ψ * g ξ (D.e ψ).2 ∂μΞ := by
  set y := (D.e ψ).2 with hy
  set P := ∏ c, D.r c ((D.e ψ).1 c) y with hP
  set Q := ∏ c, ∫ w, D.r c w y ∂(D.μ c) with hQ
  have h1 : ∀ x : ∀ c, D.W c, ρ (D.e.symm (x, y)) = ∫ ξ, ρξ ξ (D.e.symm (x, y)) * g ξ y ∂μΞ := by
    intro x
    rw [hρ, D.e.apply_symm_apply]
  have h2 : ∫ x, ρ (D.e.symm (x, y)) ∂(Measure.pi D.μ) =
      ∫ ξ, (∫ x, ρξ ξ (D.e.symm (x, y)) ∂(Measure.pi D.μ)) * g ξ y ∂μΞ := by
    simp_rw [h1]
    rw [integral_integral_swap (f := fun x ξ => ρξ ξ (D.e.symm (x, y)) * g ξ y) hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    exact integral_mul_const _ _
  have h3 : ∫ ξ, Rop D (ρξ ξ) ψ * g ξ y ∂μΞ =
      P / Q * ∫ ξ, (∫ x, ρξ ξ (D.e.symm (x, y)) ∂(Measure.pi D.μ)) * g ξ y ∂μΞ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [Rop_eq_prod]
    ring
  rw [h3, Rop_eq_prod, h2]
  ring

end Coupling

section Pointwise

open Balaban RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (k : ℕ) (Z0 : Set (BlockAt S n M K k))

/-- **The removed part of the one-component `R` of a kernel at fixed internal variables** (P7 (3.7), (3.10)): for
the kernel `Kf(·, x)` at the internal configuration `x`, the reference density `r` vanishing where `c₀ = χ_{Z₀}`
vanishes, and the front `u` (`χ_{Z''}`, or `1 - χ_{Z''}` for `ϰ₅`),
`u(o) · R[Kf(·, x)](o) = ρ_{k,0}(Z)(o) · e^{-EZ} · K^rem(o, x)`. -/
theorem mul_Rop_remDecomp_eq_removedK {X H : Type*} (Kf : OutT N R a k → X → H → ℝ)
    (u c0 : OutT N R a k → ℝ) (r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ) (EZ : ℝ)
    (hrc : ∀ q : OutZero N R a k Z0 × OutRest N R a k Z0,
      r q.1 q.2 = c0 (remZeroMerge a k Z0 q) * r q.1 q.2)
    (o : OutT N R a k) (x : X) (hv : H) :
    u o * Rop (remDecomp a k Z0 r) (fun o' => Kf o' x hv) o =
      r (remZeroSplit a k Z0 o).1 (remZeroSplit a k Z0 o).2 * Real.exp (-EZ) *
        removedK a k Z0 Kf u c0 r EZ o x hv := by
  rw [Rop_remDecomp_apply]
  set R0 := r (remZeroSplit a k Z0 o).1 (remZeroSplit a k Z0 o).2 with hR0
  set D := remDen a k Z0 r o with hD
  set I := remNum a k Z0 Kf o x hv with hI
  have hrc' : R0 = c0 o * R0 := by
    have := hrc (remZeroSplit a k Z0 o)
    rwa [remZeroMerge_split] at this
  have hexp : Real.exp (-EZ) * Real.exp EZ = 1 := by
    rw [← Real.exp_add]; simp
  have hnum : ∫ w, Kf (remZeroMerge a k Z0 (w, (remZeroSplit a k Z0 o).2)) x hv
      ∂(outPartMeasure N (Vblk R a k) (· ∈ Z0)) = I := rfl
  rw [hnum]
  simp only [removedK, ← hI, ← hD]
  linear_combination (u o * I / D) * hrc' - (u o * I / D * R0 * c0 o) * hexp

end Pointwise

section Factor

open Balaban Balaban.Multiscale Balaban.Background ActionConv RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] (N : ℕ) {k N₀ : ℕ} [NeZero N₀] [NeZero N]
  (hN : N₀ * S.L ^ (k - k) = M * n K * S.L ^ (K - k)) {ι : Type} [Fintype ι]
  (a : ι → LocalHistory S n M K) {ϱ : ℝ} (G : ι → GeneratingSet S.d S.L N₀ k ϱ) (aw : ℕ → ℝ) {D : ℕ}
  (hd : 2 ≤ S.d) (hk : 1 ≤ k)
  (b0 : ι → Torus S.d (N₀ * S.L ^ (k - k))) (w : ι → Fin S.d → ℕ)
  (hw1 : ∀ c i, 1 ≤ w c i) (hwD : ∀ c i, w c i ≤ D) (hm : D + 2 ≤ N₀ * S.L ^ (k - k))
  (X : ι → Set (Torus S.d (N₀ * S.L ^ (k - k))))
  (hXreg : ∀ c, box (b0 c) (w c) ∪ shellOut (box (b0 c) (w c)) ⊆ X c)
  (hsep : ∀ c c', c ≠ c' → Disjoint (X c) (box (b0 c') (w c')))
  (hΩ : ∀ c, OverTop (G c) (box (b0 c) (w c) ∪ shellOut (box (b0 c) (w c))))
  (hdata : ∀ c, ∀ x ∈ dataSites (G c), jBlock S.d S.L N₀ k k x ∈ X c) (H : BgHyp S.d S.L k ϱ aw 0)
  (δ : ι → ℝ) (hδ : ∀ c, 0 < δ c)
  (hδc : ∀ c, δ c ≤ psiZeroC11 N (G c) aw hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c) (hdata c) H)
  (Zr : ∀ c, Region (G c)) (σ : Finset ι) (Z0 : ι → Set (BlockAt S n M K k))
  (hZ0 : ∀ (c : ι) (y : BlockAt S n M K k), (y ∈ Vblk R (a c) k ∧ y ∈ Z0 c) ↔
    torusCast hN.symm y ∈ zb b0 w c)
  (hsepV : ∀ c c' : σ, c ≠ c' → ∀ y ∈ Vblk R (a c.1) k, torusCast hN.symm y ∉ zb b0 w c'.1)

set_option hygiene false in
/-- The restriction of a block field to the blocks of `V_c`. -/
local notation "rs[" c "," ψ "]" =>
  (fun ybk : Vblk R (a c) k =>
    (WithLp.toLp 2 (fun ii => ψ (torusCast hN.symm ybk.1) ii) : EuclideanSpace ℝ (Fin N)))

set_option hygiene false in
/-- The extension (zero off `V_c`) of the output equal to `0` on `Z₀(c)` and to `y` on `V_c ∖ Z₀(c)`. -/
local notation "ψo[" c "," y "]" =>
  (fun (z : Torus S.d (N₀ * S.L ^ (k - k))) (i : Fin N) =>
    outField N (remZeroMerge (a c) k (Z0 c) (0, y)) (torusCast hN z) i)

set_option hygiene false in
/-- The variable `u ∈ SuppSpace (zb c)` of `Z₀(c)` carrying the output `wv : OutZero`. -/
local notation "uo[" c "," wv "]" =>
  (WithLp.toLp 2 (fun p : ↥(zb b0 w c) × Fin N =>
    wv ⟨torusCast hN p.1.1, (hZ0 c _).2 (by rw [torusCast_symm_cast]; exact p.1.2)⟩ p.2) :
    SuppSpace (zb b0 w c) N)

include hZ0 hsepV in
open Classical in
/-- **The restricted `R` of a term coupled through the internal variables** (P7 (3.6), Definition III.8.3,
`LF4R-PLAN` status W968): if `ρ(ψ) = ∫ dξ ∏_{c∈σ} K_c(ψ↾V_c, ξ) · f(ψ, ξ)`, where the coupling `f` (boundary terms,
small-field factor, other components) does not read `ψ` on the boxes `Z₀(c)` (`hf`), the components are separated as
in `Rop_famDecompRestricted_factor`, and the integrand is integrable on the product of the box variables and `ξ`
(`hint`), then `R[ρ](ψ) = ∫ dξ ∏_c R_c[K_c(·, ξ)](ψ↾V_c) · f(ψ, ξ)`: `R` acts on each kernel at fixed internal
variables, and the coupling is untouched. -/
theorem Rop_famDecompRestricted_coupled (ν : ℝ) (h : Fin N → ℝ) (β0 p0 : ℝ)
    (r : ∀ c : ι, OutZero N R (a c) k (Z0 c) → OutRest N R (a c) k (Z0 c) → ℝ)
    (hr : ∀ (c : σ) (wv : OutZero N R (a c.1) k (Z0 c.1)) (y : OutRest N R (a c.1) k (Z0 c.1)),
      r c.1 wv y =
        if hψ : TubeOn (G c.1) (X c.1 \ box (b0 c.1) (w c.1)) (δ c.1) ψo[c.1, y] then
          rhoZeroRestricted (G c.1) aw hd hk (b0 c.1) (w c.1) (hw1 c.1) (hwD c.1) hm (hXreg c.1) (hΩ c.1)
            (hdata c.1) H (hδ c.1) (hδc c.1) hψ (Zr c.1) ν h β0 p0 uo[c.1, wv]
        else 0)
    (hXV : ∀ c : σ, ∀ z ∈ X c.1, torusCast hN z ∈ Vblk R (a c.1) k)
    {Ξ : Type*} [MeasurableSpace Ξ] (μΞ : Measure Ξ) [SFinite μΞ]
    (Kc : ∀ c : ι, OutT N R (a c) k → Ξ → ℝ) (f : BlockField S.d S.L N₀ k N → Ξ → ℝ)
    (hf : ∀ ψ ψ' ξ, (∀ z, (∀ c : σ, z ∉ zb b0 w c.1) → ψ z = ψ' z) → f ψ ξ = f ψ' ξ)
    (ρ : BlockField S.d S.L N₀ k N → ℝ)
    (hρ : ∀ ψ, ρ ψ = ∫ ξ, (∏ c : σ, Kc c.1 rs[c.1, ψ] ξ) * f ψ ξ ∂μΞ)
    (ψ : BlockField S.d S.L N₀ k N)
    (hint : Integrable (fun q : ((c : σ) → SuppSpace (zb b0 w c.1) N) × Ξ =>
        (∏ c : σ, Kc c.1 rs[c.1, (famEquiv N b0 w X hXreg hsep σ).symm
          (q.1, (famEquiv N b0 w X hXreg hsep σ ψ).2)] q.2) * f ψ q.2)
      ((Measure.pi fun c : σ => (volume : Measure (SuppSpace (zb b0 w c.1) N))).prod μΞ)) :
    Rop (famDecompRestricted N G aw hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h β0 p0) ρ ψ =
      ∫ ξ, (∏ c : σ, Rop (remDecomp (a c.1) k (Z0 c.1) (r c.1)) (fun o => Kc c.1 o ξ) rs[c.1, ψ]) *
        f ψ ξ ∂μΞ := by
  have hfo : ∀ ψ' ξ, f (famOut N b0 w X hXreg hsep σ (famEquiv N b0 w X hXreg hsep σ ψ').2) ξ = f ψ' ξ :=
    fun ψ' ξ => hf _ _ ξ (fun z hz => famOut_eq N b0 w X hXreg hsep σ ψ' z hz)
  have key := Rop_integral_coupling
    (famDecompRestricted N G aw hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h β0 p0) μΞ
    (fun ξ ψ' => ∏ c : σ, Kc c.1 rs[c.1, ψ'] ξ)
    (fun ξ y => f (famOut N b0 w X hXreg hsep σ y) ξ) ρ
    (fun ψ' => by
      rw [hρ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      exact congrArg _ (hfo ψ' ξ).symm) ψ
    (hint.congr (Filter.Eventually.of_forall fun q => congrArg _ (hfo ψ q.2).symm))
  refine key.trans (integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_))
  have hfac := Rop_famDecompRestricted_factor N hN a G aw hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc
    Zr σ Z0 hZ0 hsepV ν h β0 p0 r hr hXV (fun c o => Kc c o ξ) (fun ψ' => ∏ c : σ, Kc c.1 rs[c.1, ψ'] ξ)
    (fun _ => rfl) ψ
  exact congrArg₂ (· * ·) hfac (hfo ψ ξ)

include hZ0 hsepV in
open Classical in
/-- **The per-history identity of `R` for several components with couplings** (P7 (3.6)-(3.7), the bracket of
P7 (3.26) before the recombination (3.21)-(3.25); `LF4R-PLAN` status W968).  For a term
`ρ(ψ) = ∫ dξ ∏_{c∈σ} K_c(ψ↾V_c, ξ) · f(ψ, ξ)` as in `Rop_famDecompRestricted_coupled`, fronts `u_c` (`χ_{Z''_c}` for
the removed outcome, `1 - χ_{Z''_c}` for `ϰ₅`), and reference densities `r_c` vanishing where `c₀,c = χ_{Z₀(c)}`
vanishes (`hrc`):
`∏_c u_c(ψ↾V_c) · R[ρ](ψ) = ∏_c ρ_{k,0}(Z_c)(ψ↾V_c) e^{-EZ_c} · ∫ dξ ∏_c K^rem_c(ψ↾V_c, ξ) · f(ψ, ξ)`,
with `K^rem_c = removedK … (EZ c)` (the kernel of `removedKernel`).  The outputs `ψ` are not integrated, and `f`
couples the internal variables of all the components. -/
theorem prod_mul_Rop_famDecompRestricted_coupled (ν : ℝ) (h : Fin N → ℝ) (β0 p0 : ℝ)
    (r : ∀ c : ι, OutZero N R (a c) k (Z0 c) → OutRest N R (a c) k (Z0 c) → ℝ)
    (hr : ∀ (c : σ) (wv : OutZero N R (a c.1) k (Z0 c.1)) (y : OutRest N R (a c.1) k (Z0 c.1)),
      r c.1 wv y =
        if hψ : TubeOn (G c.1) (X c.1 \ box (b0 c.1) (w c.1)) (δ c.1) ψo[c.1, y] then
          rhoZeroRestricted (G c.1) aw hd hk (b0 c.1) (w c.1) (hw1 c.1) (hwD c.1) hm (hXreg c.1) (hΩ c.1)
            (hdata c.1) H (hδ c.1) (hδc c.1) hψ (Zr c.1) ν h β0 p0 uo[c.1, wv]
        else 0)
    (hXV : ∀ c : σ, ∀ z ∈ X c.1, torusCast hN z ∈ Vblk R (a c.1) k)
    {Ξ Hh : Type*} [MeasurableSpace Ξ] (μΞ : Measure Ξ) [SFinite μΞ]
    (Kf : ∀ c : ι, OutT N R (a c) k → Ξ → Hh → ℝ) (hv : Hh)
    (u c0 : ∀ c : ι, OutT N R (a c) k → ℝ) (EZ : ι → ℝ)
    (hrc : ∀ (c : σ) (q : OutZero N R (a c.1) k (Z0 c.1) × OutRest N R (a c.1) k (Z0 c.1)),
      r c.1 q.1 q.2 = c0 c.1 (remZeroMerge (a c.1) k (Z0 c.1) q) * r c.1 q.1 q.2)
    (f : BlockField S.d S.L N₀ k N → Ξ → ℝ)
    (hf : ∀ ψ ψ' ξ, (∀ z, (∀ c : σ, z ∉ zb b0 w c.1) → ψ z = ψ' z) → f ψ ξ = f ψ' ξ)
    (ρ : BlockField S.d S.L N₀ k N → ℝ)
    (hρ : ∀ ψ, ρ ψ = ∫ ξ, (∏ c : σ, Kf c.1 rs[c.1, ψ] ξ hv) * f ψ ξ ∂μΞ)
    (ψ : BlockField S.d S.L N₀ k N)
    (hint : Integrable (fun q : ((c : σ) → SuppSpace (zb b0 w c.1) N) × Ξ =>
        (∏ c : σ, Kf c.1 rs[c.1, (famEquiv N b0 w X hXreg hsep σ).symm
          (q.1, (famEquiv N b0 w X hXreg hsep σ ψ).2)] q.2 hv) * f ψ q.2)
      ((Measure.pi fun c : σ => (volume : Measure (SuppSpace (zb b0 w c.1) N))).prod μΞ)) :
    (∏ c : σ, u c.1 rs[c.1, ψ]) *
        Rop (famDecompRestricted N G aw hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ ν h β0 p0)
          ρ ψ =
      (∏ c : σ, r c.1 (remZeroSplit (a c.1) k (Z0 c.1) rs[c.1, ψ]).1
          (remZeroSplit (a c.1) k (Z0 c.1) rs[c.1, ψ]).2 * Real.exp (-EZ c.1)) *
        ∫ ξ, (∏ c : σ, removedK (a c.1) k (Z0 c.1) (Kf c.1) (u c.1) (c0 c.1) (r c.1) (EZ c.1)
          rs[c.1, ψ] ξ hv) * f ψ ξ ∂μΞ := by
  rw [Rop_famDecompRestricted_coupled N hN a G aw hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc Zr σ
    Z0 hZ0 hsepV ν h β0 p0 r hr hXV μΞ (fun c o ξ => Kf c o ξ hv) f hf ρ hρ ψ hint,
    ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  have hc : ∀ c : σ, u c.1 rs[c.1, ψ] *
      Rop (remDecomp (a c.1) k (Z0 c.1) (r c.1)) (fun o => Kf c.1 o ξ hv) rs[c.1, ψ] =
      r c.1 (remZeroSplit (a c.1) k (Z0 c.1) rs[c.1, ψ]).1
          (remZeroSplit (a c.1) k (Z0 c.1) rs[c.1, ψ]).2 * Real.exp (-EZ c.1) *
        removedK (a c.1) k (Z0 c.1) (Kf c.1) (u c.1) (c0 c.1) (r c.1) (EZ c.1) rs[c.1, ψ] ξ hv :=
    fun c => mul_Rop_remDecomp_eq_removedK (a c.1) k (Z0 c.1) (Kf c.1) (u c.1) (c0 c.1) (r c.1) (EZ c.1)
      (hrc c) rs[c.1, ψ] ξ hv
  calc (∏ c : σ, u c.1 rs[c.1, ψ]) *
        ((∏ c : σ, Rop (remDecomp (a c.1) k (Z0 c.1) (r c.1)) (fun o => Kf c.1 o ξ hv) rs[c.1, ψ]) * f ψ ξ)
      = (∏ c : σ, u c.1 rs[c.1, ψ] *
          Rop (remDecomp (a c.1) k (Z0 c.1) (r c.1)) (fun o => Kf c.1 o ξ hv) rs[c.1, ψ]) * f ψ ξ := by
        rw [Finset.prod_mul_distrib]; ring
    _ = _ := by
        rw [Finset.prod_congr rfl fun c _ => hc c, Finset.prod_mul_distrib]
        ring

end Factor

end Balaban.LargeField
