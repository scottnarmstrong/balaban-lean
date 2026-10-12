module

public import Balaban.LargeField.Operators.MainAction
public import Balaban.LargeField.Characteristic.Functions

/-!
# Quiet steps and the quiet step kernel (Part II, Definitions II.5.5-II.5.6, block J4)

* `IsQuiet`: the step `k → k + 1` is quiet in `Z'` if `𝒩_{k+1} ∩ Z' = ∅` (no new large-field cube);
* `ChiNewProp`, `chiNew`: the conditions of Definition II.3.4 that are new at level `k + 1`
  (`χ^new_k(Z')`): (1.24) for `j = k` and for the `π_k`- and `π_{k+1}`-cubes of the second family,
  (1.25) for `j = k`;
* `quietKernel`: the quiet step kernel
  `K^q_k(Z') = ∏_y z^N t_k(θ(y), (Qψ_k)(y)) · χ_k(⋯) χ'_{k+1}(⋯) χ'_{k+1}(⋯) χ_{k+1}(⋯) · χ^new_k(Z')
   · 1[φ^loc-data ∈ 𝒟_ℝ] · e^{-𝒜_{k+1}(Z';ψ)}`
  as a function of the output `ψ_{k+1}|_V`, the new internal variables `I^new_k`, and `h`.
  Here `θ = z_{k+1} ψ_{k+1}`, `t_k(ϑ, w) = (β_k a L^{d-2}/2π)^{N/2} exp(-β_k a L^{d-2}|ϑ-w|²/2)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory

/-- The Gaussian `t_k(ϑ, w) = (c/2π)^{N/2} exp(-c|ϑ - w|²/2)` of the kernel of `T^{(k)}`
(`c = β_k a L^{d-2}`). -/
noncomputable def gaussT (N : ℕ) (c : ℝ) (ϑ w : EuclideanSpace ℝ (Fin N)) : ℝ :=
  (c / (2 * Real.pi)) ^ ((N : ℝ) / 2) * Real.exp (-(c / 2) * ‖ϑ - w‖ ^ 2)

theorem gaussT_nonneg (N : ℕ) (c : ℝ) (hc : 0 ≤ c) (ϑ w : EuclideanSpace ℝ (Fin N)) :
    0 ≤ gaussT N c ϑ w := by
  unfold gaussT
  have : 0 ≤ c / (2 * Real.pi) := div_nonneg hc (by positivity)
  positivity

section Quiet

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- The step `k → k + 1` is *quiet in* `Z'` if `𝒩_{k+1} ∩ Z' = ∅` (Definition II.5.5). -/
def IsQuiet (Hl : RegionHistory S n R k0 K) (k : ℕ) (Zc : Finset (Torus S.d (n (k + 1)))) : Prop :=
  Zc ∩ Hl.newCubes (k + 1) = ∅

/-- The `(k+1)`-blocks of `Ω^c_{k+1} ∩ Z'`: the blocks carrying the Gaussian factors. -/
def gaussBlocks (a : LocalHistory S n M K) (k : ℕ) : Set (BlockAt S n M K (k + 1)) :=
  {y | BlockSub (S := S) (n := n) (M := M) (K := K) (k + 1) y (a.Z (k + 1) \ a.Omega k)}

open Classical in
/-- The coarsened large-field field `(Qψ_k)(y) = L^{-d} ∑_{y' ∈ T_k(B_{k+1}(y))} ψ_k(y')`. -/
noncomputable def qCoarseK (N : ℕ) {a : LocalHistory S n M K} {k : ℕ}
    {A : Set (InternalVars a (k + 1))} (x : SubCfg N a (k + 1) A) (y : BlockAt S n M K (k + 1)) :
    EuclideanSpace ℝ (Fin N) :=
  ((S.L : ℝ) ^ S.d)⁻¹ •
    ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K k =>
      blockMap S.L (M * n K * S.L ^ (K - (k + 1))) y' = y), subVarField N x k y'

/-- The Gaussian argument `u_y = z_{k+1} ψ_{k+1}(y) - (Qψ_k)(y)`, `y ∈ Ω^c_{k+1} ∩ Z'`. -/
noncomputable def gaussArg (N : ℕ) (z : ℝ) {a : LocalHistory S n M K} {k : ℕ} {V : Set (BlockAt S n M K (k + 1))}
    (o : OutConfig N V) {A : Set (InternalVars a (k + 1))} (x : SubCfg N a (k + 1) A)
    (y : BlockAt S n M K (k + 1)) : EuclideanSpace ℝ (Fin N) :=
  z • outField N o y - qCoarseK N x y

open Classical in
/-- The product over the Gaussian blocks of `z^N t_k(z ψ_{k+1}(y), (Qψ_k)(y))`. -/
noncomputable def gaussProd (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) (cs : OpConsts)
    {V : Set (BlockAt S n M K (k + 1))} (o : OutConfig N V)
    (x : NewCfg N a k) : ℝ :=
  ∏ y : gaussBlocks a k, cs.z (k + 1) ^ N *
    gaussT N (cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (cs.z (k + 1) • outField N o y)
      (qCoarseK N x y)

theorem gaussProd_nonneg (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) (cs : OpConsts)
    (hz : 0 ≤ cs.z (k + 1)) (hc : 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    {V : Set (BlockAt S n M K (k + 1))} (o : OutConfig N V) (x : NewCfg N a k) :
    0 ≤ gaussProd N a k cs o x :=
  Finset.prod_nonneg fun _ _ => mul_nonneg (pow_nonneg hz _) (gaussT_nonneg N _ hc _ _)

/-! ### The conditions of the domain that are new at level `k + 1` -/

variable {ϱ : ℝ}

/-- The conditions of Definition II.3.4 at level `k + 1` that involve scales `k` or `k + 1`
(Lemma II.5.13): (1.24) for `j = k` (the `π_{k+1}`-cubes of `Ω^∼_{k+1} ∩ Z'`) and for the
`π_k`- and `π_{k+1}`-cubes of the second family (`1 ≤ j`, as in Definition II.3.4: the second
family is indexed by `1 ≤ j ≤ k`), (1.25) for `j = k`. -/
def ChiNewProp (a : LocalHistory S n M K) (k : ℕ) (B : GeneratingSet S.d S.L (M * n K) K ϱ)
    (Zc : Set (Torus S.d (M * n K * S.L ^ K))) (δ p0 : ℕ → ℝ) (Cpsi : ℝ)
    (ψ ψ' : MultiField S n M K N) : Prop :=
  (∀ y : Torus S.d (n (k + 1)), CubeSub (S := S) (n := n) M K (k + 1) y (a.Z (k + 1)) →
      y ∈ lhOmegaSim a (k + 1) (k + 1) →
        PsiTildeMulti ψ (genBlocksIn B (k + 1) (nbhd 1 {y})) (3 * S.d * S.L * δ k)) ∧
  (∀ j, 1 ≤ j → (j = k ∨ j = k + 1) → ∀ y : Torus S.d (n j), CubeSub (S := S) (n := n) M K j y Zc →
      (∀ x, cubeMap n S.L M K j x = y → x ∉ a.Z j) →
      (∀ x, cubeMap n S.L M K j x = y → cubeMap n S.L M K (j + 1) x ∉ lhOmegaSim a (k + 1) (j + 1)) →
        PsiTildeMulti ψ (scaleBlocksIn j (nbhd 1 {y})) (3 * δ j)) ∧
  (∀ y : BlockAt S n M K k,
      BlockSub (S := S) (n := n) (M := M) (K := K) k y (a.Omega k \ a.OmegaDD k) →
        ‖ψ' k y‖ < Cpsi * p0 k)

/-- `χ^new_k(Z')`: the indicator of `ChiNewProp`. -/
noncomputable def chiNew (a : LocalHistory S n M K) (k : ℕ) (B : GeneratingSet S.d S.L (M * n K) K ϱ)
    (Zc : Set (Torus S.d (M * n K * S.L ^ K))) (δ p0 : ℕ → ℝ) (Cpsi : ℝ) :
    MultiField S n M K N × MultiField S n M K N → ℝ :=
  charFn fun p => ChiNewProp a k B Zc δ p0 Cpsi p.1 p.2

/-! ### The quiet step kernel -/

open Classical in
/-- A finite set of cubes of `𝕋_j`. -/
noncomputable def cubeFin {m : ℕ} [NeZero m] (A : Set (Torus S.d m)) : Finset (Torus S.d m) :=
  Finset.univ.filter fun y => y ∈ A

/-- The `π_k`-cubes of `Z^c_k ∩ Z' ∩ (Ω^{∼3}_{k+1})^c` (the argument of the first `χ_k`). -/
def quietA1 (a : LocalHistory S n M K) (k : ℕ) : Set (Torus S.d (n k)) :=
  {y | CubeSub (S := S) (n := n) M K k y (a.Z (k + 1) \ a.Z k) ∧
    blockMap S.L (n (k + 1)) y ∉ omegaNb a (k + 1) 3 (k + 1)}

/-- The `π_{k+1}`-cubes of `Ω^{∼3}_{k+1} ∩ Ω^c_{k+1} ∩ Z'`. -/
def quietA2 (a : LocalHistory S n M K) (k : ℕ) : Set (Torus S.d (n (k + 1))) :=
  {y | CubeSub (S := S) (n := n) M K (k + 1) y (a.Z (k + 1) \ a.Omega k) ∧
    y ∈ omegaNb a (k + 1) 3 (k + 1)}

/-- The `π_{k+1}`-cubes of `Ω_{k+1} ∩ (Ω^c_{k+1})^{∼3} ∩ Z'`. -/
def quietA3 (a : LocalHistory S n M K) (k : ℕ) : Set (Torus S.d (n (k + 1))) :=
  {y | CubeSub (S := S) (n := n) M K (k + 1) y (a.Omega k) ∧ y ∈ omegaCNb a 3 (k + 1)}

/-- The `π_{k+1}`-cubes of `Ω^{∼-3}_{k+1} ∩ Z'`, `Ω^{∼-3} = ((Ω^c)^{∼3})^c`. -/
def quietA4 (a : LocalHistory S n M K) (k : ℕ) : Set (Torus S.d (n (k + 1))) :=
  {y | CubeSub (S := S) (n := n) M K (k + 1) y (a.Z (k + 1)) ∧ y ∉ omegaCNb a 3 (k + 1)}

theorem charFn_nonneg' {X : Type*} (P : X → Prop) (x : X) : 0 ≤ charFn P x := by
  classical
  rw [charFn_apply]
  split_ifs <;> norm_num

theorem cubeProd_charFn_nonneg {m : ℕ} {X : Type*} (P : Torus S.d m → X → Prop)
    (A : Finset (Torus S.d m)) (x : X) : 0 ≤ cubeProd (fun y => charFn (P y)) A x :=
  Finset.prod_nonneg fun y _ => charFn_nonneg' (P y) x

variable (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ) (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1))) (hk : k + 1 ≤ K)
  (cs : OpConsts) (hrem : ∀ j, Hl.rem j = ∅)

open Classical in
/-- **Definition II.5.6 (quiet step kernel)** at the configuration `(o, x) = (ψ_{k+1}|_V, I^new_k)`
and the external direction `h`.  The factors are, in the order of the source: the Gaussians of
`T^{(k)}`; `χ_k(Z^c_k ∩ Z' ∩ (Ω^{∼3})^c)`; `χ'_{k+1}(Ω^{∼3} ∩ Ω^c ∩ Z')`;
`χ'_{k+1}(Ω ∩ (Ω^c)^{∼3} ∩ Z')`; `χ_{k+1}(Ω^{∼-3} ∩ Z')`; `χ^new_k(Z')`; the indicator that the
data of the local background lie in `𝒟_ℝ`; and `e^{-𝒜_{k+1}(Z';ψ)}`. -/
noncomputable def quietKernel (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) : ℝ :=
  gaussProd N (locHist Hl M K (k + 1) Zc) k cs o x *
  cubeProd (fun y0 => chiK (M1 := g.M1) (N₁ := g.c * n k) (L := S.L) (q := k) (N := N) cs.aw
      (cs.mu k) (cs.delta k) (fun i => hv i) g.c (n k) y0)
    (cubeFin (quietA1 (locHist Hl M K (k + 1) Zc) k))
    (blockCfgOf g Hl.F.hnn (le_refl k) ((Nat.le_succ k).trans hk) (subVarField N x k)) *
  cubeProd (fun y0 => chiPrimeNew (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L) (N := N)
      (k := k) cs.aw (cs.mu (k + 1)) (cs.delta k) (cs.nu k) (fun i => hv i)
      (c := g.c) (n := n (k + 1)) (by simp) y0
      (omegaLevel (S := S) (n := n) g.M1 g.c (k + 1)
        {z | CubeSub (S := S) (n := n) M K (k + 1) z
          ((locHist Hl M K (k + 1) Zc).Omega k)})
      (omegaLevel_blockUnion (S := S) (n := n) g.M1 g.c (k + 1) _))
    (cubeFin (quietA2 (locHist Hl M K (k + 1) Zc) k))
    (blockCfgOf g Hl.F.hnn (Nat.le_succ k) hk (subVarField N x k),
      blockCfgOf g Hl.F.hnn le_rfl hk (fun y => cs.z (k + 1) • outField N o y)) *
  cubeProd (fun y0 => chiPrimeNew (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L) (N := N)
      (k := k) cs.aw (cs.mu (k + 1)) (cs.delta k) (cs.nu k) (fun i => hv i)
      (c := g.c) (n := n (k + 1)) (by simp) y0
      (omegaLevel (S := S) (n := n) g.M1 g.c (k + 1)
        {z | CubeSub (S := S) (n := n) M K (k + 1) z
          ((locHist Hl M K (k + 1) Zc).Omega k)})
      (omegaLevel_blockUnion (S := S) (n := n) g.M1 g.c (k + 1) _))
    (cubeFin (quietA3 (locHist Hl M K (k + 1) Zc) k))
    (blockCfgOf g Hl.F.hnn (Nat.le_succ k) hk (subVarField N x k),
      blockCfgOf g Hl.F.hnn le_rfl hk (fun y => cs.z (k + 1) • outField N o y)) *
  cubeProd (fun y0 => chiNext (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L) (N := N) cs.aw
      (cs.mu (k + 1)) (cs.delta (k + 1)) (fun i => hv i) g.c (n (k + 1)) k y0)
    (cubeFin (quietA4 (locHist Hl M K (k + 1) Zc) k))
    (blockCfgOf g Hl.F.hnn le_rfl hk (outField N o)) *
  chiNew (locHist Hl M K (k + 1) Zc) k
    (Hl.histGen (M := M) (K' := K) le_rfl hrem Hl.F.ok.two_le_L (fun j _ _ => g.hRlow j))
    (fineSet (S := S) (n := n) M K (k + 1) (Zc : Set (Torus S.d (n (k + 1))))) cs.delta cs.p0
    cs.Cpsi
    (subMultiscaleField N (locHist Hl M K (k + 1) Zc) (k + 1)
        (Vblk R (locHist Hl M K (k + 1) Zc) (k + 1)) x o,
      subFluctField N (locHist Hl M K (k + 1) Zc) (k + 1) x) *
  (if InUnionDomainR (locGen g Hl k Zc hZc hk) (bgC1 S.d S.L N) (cs.mu (k + 1))
      (locData g Hl k Zc hZc hk o x hv) then 1 else 0) *
  Real.exp (-mainActionLoc g Hl k Zc hZc hk cs hrem o x hv)

theorem cubeProd_nonneg_of_nonneg {m : ℕ} {X : Type*} {χ : Torus S.d m → X → ℝ}
    (h : ∀ y x, 0 ≤ χ y x) (A : Finset (Torus S.d m)) (x : X) : 0 ≤ cubeProd χ A x :=
  Finset.prod_nonneg fun y _ => h y x

/-- The quiet kernel is non-negative (for non-negative running constants). -/
theorem quietKernel_nonneg (hz : 0 ≤ cs.z (k + 1))
    (hc : 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    0 ≤ quietKernel g Hl k Zc hZc hk cs hrem o x hv := by
  classical
  unfold quietKernel
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (gaussProd_nonneg N _ k cs hz hc o x) ?_) ?_) ?_) ?_) ?_) ?_) (Real.exp_pos _).le
  · exact cubeProd_nonneg_of_nonneg (fun y x => by unfold chiK; exact charFn_nonneg' _ _) _ _
  · exact cubeProd_nonneg_of_nonneg (fun y x => by unfold chiPrimeNew; exact charFn_nonneg' _ _) _ _
  · exact cubeProd_nonneg_of_nonneg (fun y x => by unfold chiPrimeNew; exact charFn_nonneg' _ _) _ _
  · exact cubeProd_nonneg_of_nonneg
      (fun y x => by unfold chiNext chiK; exact charFn_nonneg' _ _) _ _
  · unfold chiNew; exact charFn_nonneg' _ _
  · split_ifs <;> norm_num

end Quiet

end Balaban.LargeField
