module

public import Balaban.LargeField.Operators.CompBound
public import Balaban.LargeField.Operators.ShellVolume
public import Balaban.LargeField.Characteristic.Stencil

/-!
# The quiet kernel factorizes and its remainder does not read the Gaussian variables
(Part II, Lemma II.5.14, first half)

* `quietKernel_eq`: `K^q_k = gaussProd * quietRest`;
* `quietRest_congr`: `quietRest` does not depend on `ψ_{k+1}` on the Gaussian blocks
  `Ω^c_{k+1} ∩ Z'`.  Every factor reads `ψ_{k+1}` only through the mixed lifts, which read `θ`
  only on `Ω_{k+1}` (`liftMixed_congr_Om`), through the stencils of the characteristic functions
  (cubes at distance `> 3` from `Ω^c`), and through the multiscale field (supported in `Ω_{k+1}`);
  the bridge between the level-`q` torus and the fine torus is `blockCube_torusCast`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory ENNReal

section Bridge

theorem torusCast_val {d m m' : ℕ} (h : m = m') (y : Torus d m) (i : Fin d) :
    ((torusCast h y) i).val = (y i).val := by
  subst h
  rfl

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L]

/-- The `π_{q}`-cube of the fine-torus block corresponding to a site of the level-`q` torus is the
cube of that site. -/
theorem blockCube_torusCast (g : Geo S n R M) (hnn : ∀ i, n i = S.L * n (i + 1)) {q : ℕ}
    (hqK : q ≤ K)
    (x : Torus S.d (g.M1 * (g.c * n q) * S.L ^ q)) :
    blockCube S n M K q (torusCast (histScale_eq g.hM hnn (le_refl q) hqK)
        (jBlock S.d S.L (g.M1 * (g.c * n q)) q q x)) =
      blockMap (S.L ^ q * (g.c * g.M1)) (n q) x := by
  funext i
  unfold blockCube blockMap blockCoord
  congr 1
  rw [torusCast_val]
  have hℓ : g.M1 * (g.c * n q) * S.L ^ q = S.L ^ q * (g.M1 * (g.c * n q) * S.L ^ (q - q)) := by
    simp [mul_comm]
  have h1 : (jBlock S.d S.L (g.M1 * (g.c * n q)) q q x i).val = (x i).val / S.L ^ q := by
    unfold jBlock
    exact blockCoord_val hℓ (x i)
  rw [h1, Nat.div_div_eq_div_mul]
  exact congrArg (fun m => (x i).val / (S.L ^ q * m)) g.hM

end Bridge

section Congr

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The refinement of `liftMixed_congr`: the mixed lift reads `ϑ` only at the sites of `Ω`. -/
theorem liftMixed_congr_Om (G : GeneratingSet d L N₀ (k + 1) ϱ)
    {Ω : Finset (Torus d (N₀ * L ^ (k + 1)))} (hΩ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω)
    (hG : G.Ω (k + 1) ⊆ Ω) {ψ : Torus d (N₀ * L ^ (k + 1 - k)) → Fin N → ℂ}
    {ϑ ϑ' : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ} {h : Fin N → ℂ}
    (hϑ : ∀ x ∈ dataSites G, x ∈ Ω →
      ϑ (jBlock d L N₀ (k + 1) (k + 1) x) = ϑ' (jBlock d L N₀ (k + 1) (k + 1) x)) :
    liftMixed G hΩ hG ψ ϑ h = liftMixed G hΩ hG ψ ϑ' h := by
  classical
  refine BgData.ext' (funext fun x => ?_) rfl
  by_cases hx : x ∈ dataSites G
  · simp only [liftMixed, BgData.clip, hx, ↓reduceIte, mixedLift, blockLift]
    split_ifs with hxΩ
    · exact hϑ x hx hxΩ
    · rfl
  · simp [liftMixed, BgData.clip, hx]


variable {M1 N₁ : ℕ} [NeZero M1] [NeZero N₁] {c n : ℕ} [NeZero n]

/-- `χ'_{k+1}(□')` depends on `θ` only at the blocks of the cubes of `□'^{∼3}` that lie in `Ω`. -/
theorem chiPrimeNew_congr_Om (a : ℕ → ℝ) (μ δ νk : ℝ) (h : Fin N → ℝ) (hL : 2 ≤ L)
    (hc : 12 ≤ c) (hm : N₁ * L ^ (k + 1 - (k + 1)) = c * n) (y0 : Torus d n)
    (Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1))))
    (hOm : IsBlockUnion L (M1 * N₁) (k + 1) (k + 1) Om)
    (ψ : BlockCfg d (M1 * N₁) L (k + 1) k N) {θ θ' : BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N}
    (hθ : ∀ x : Torus d (M1 * N₁ * L ^ (k + 1)),
      blockMap (L ^ (k + 1) * (c * M1)) n x ∈ nbhd 3 {y0} → x ∈ Om →
      θ (jBlock d L (M1 * N₁) (k + 1) (k + 1) x) = θ' (jBlock d L (M1 * N₁) (k + 1) (k + 1) x)) :
    chiPrimeNew a μ δ νk h hm y0 Om hOm (ψ, θ) = chiPrimeNew a μ δ νk h hm y0 Om hOm (ψ, θ') := by
  have hD : mixedData h hm y0 Om hOm ψ θ = mixedData h hm y0 Om hOm ψ θ' := by
    refine liftMixed_congr_Om _ _ _ (fun x hx hxΩ => ?_)
    have := hθ x (dataSites_genCubeMixed_near hL hc hm y0 Om hOm hx) hxΩ
    exact funext fun i => by simp only [BlockCfg.toC, this]
  exact charFn_congr (by simp only [ChiPrimeNewProp, hD])

end Congr

section QuietRest

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}
  (g : Geo S n R M) (Hl : RegionHistory S n R k0) (k : ℕ) (Zc : Finset (Torus S.d (n (k + 1))))
  (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1))) (cs : OpConsts) (hk : k + 1 ≤ K)
  (hrem : ∀ j, Hl.rem j = ∅)

open Classical in
/-- The quiet kernel without its Gaussian factor: the product of the characteristic functions,
the indicator of `𝒟_ℝ` and `e^{-𝒜}`. -/
noncomputable def quietRest (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) : ℝ :=
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
    (Hl.histGen (M := M) hrem Hl.F.ok.two_le_L K (fun j _ _ => g.hRlow j))
    (fineSet (S := S) (n := n) M K (k + 1) (Zc : Set (Torus S.d (n (k + 1))))) cs.delta cs.p0
    cs.Cpsi
    (subMultiscaleField N (locHist Hl M K (k + 1) Zc) (k + 1)
        (Vblk R (locHist Hl M K (k + 1) Zc) (k + 1)) x o,
      subFluctField N (locHist Hl M K (k + 1) Zc) (k + 1) x) *
  (if InUnionDomainR (locGen g Hl k Zc hZc) (bgC1 S.d S.L N) (cs.mu (k + 1))
      (locData g Hl k Zc hZc hk o x hv) then 1 else 0) *
  Real.exp (-mainActionLoc g Hl k Zc hZc cs hk hrem o x hv)

open Classical in
theorem quietKernel_eq (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    quietKernel g Hl k Zc hZc cs hk hrem o x hv =
      gaussProd N (locHist Hl M K (k + 1) Zc) k cs o x * quietRest g Hl k Zc hZc cs hk hrem o x hv := by
  unfold quietKernel quietRest
  ring

end QuietRest

section Indep

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0} {k : ℕ}
  (g : Geo S n R M) (cs : OpConsts) (hk : k + 1 ≤ K)

theorem cubeSub_omega_mem (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) {w : Torus S.d (n (k + 1))}
    (hw : CubeSub (S := S) (n := n) M K (k + 1) w ((H.localHistory M K (k + 1) Z').Omega k)) :
    w ∈ ((H.locRH (k + 1) Z').step k).Omega := by
  obtain ⟨x, hx⟩ := exists_site_of_cube (M := M) (K := K) H.F.hnn hK w
  have := (hw x hx).1
  exact hx ▸ this

theorem outField_agree (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (o o' : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (hoo : ∀ y : Vblk R (H.localHistory M K (k + 1) Z') (k + 1),
      y.1 ∉ gaussBlocks (H.localHistory M K (k + 1) Z') k → o y = o' y)
    (y : BlockAt S n M K (k + 1))
    (hy : blockCube S n M K (k + 1) y ∈ ((H.locRH (k + 1) Z').step k).Omega ∨
      blockCube S n M K (k + 1) y ∉ (Z'.1 : Set (Torus S.d (n (k + 1))))) :
    outField N o y = outField N o' y := by
  classical
  have hng : y ∉ gaussBlocks (H.localHistory M K (k + 1) Z') k := by
    rw [gaussBlocks_iff hK Z']
    rintro ⟨h1, h2⟩
    rcases hy with h | h
    · exact h2 h
    · exact h h1
  unfold outField
  by_cases h : y ∈ Vblk R (H.localHistory M K (k + 1) Z') (k + 1)
  · simp only [h, ↓reduceDIte]
    exact hoo ⟨y, h⟩ hng
  · simp only [h, ↓reduceDIte]

theorem blockCfgOf_agree (g : Geo S n R M) {q : ℕ} (hqK : q ≤ K)
    (f f' : BlockAt S n M K q → EuclideanSpace ℝ (Fin N)) (W : Set (Torus S.d (n q)))
    (hf : ∀ y, blockCube S n M K q y ∈ W → f y = f' y)
    (z : Torus S.d (g.M1 * (g.c * n q) * S.L ^ q))
    (hz : blockMap (S.L ^ q * (g.c * g.M1)) (n q) z ∈ W) :
    blockCfgOf g H.F.hnn (le_refl q) hqK f (jBlock S.d S.L (g.M1 * (g.c * n q)) q q z) =
      blockCfgOf g H.F.hnn (le_refl q) hqK f' (jBlock S.d S.L (g.M1 * (g.c * n q)) q q z) := by
  unfold blockCfgOf
  funext j
  rw [hf _ (by rw [blockCube_torusCast g H.F.hnn hqK z]; exact hz)]

theorem theta_congr (g : Geo S n R M) (cs : OpConsts) (hk : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (o o' : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (hoo : ∀ y : Vblk R (H.localHistory M K (k + 1) Z') (k + 1),
      y.1 ∉ gaussBlocks (H.localHistory M K (k + 1) Z') k → o y = o' y)
    (z : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)))
    (hz : blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) z ∈
      ((H.locRH (k + 1) Z').step k).Omega) :
    blockCfgOf g H.F.hnn (le_refl (k + 1)) hk (fun y => cs.z (k + 1) • outField N o y)
        (jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (k + 1) z) =
      blockCfgOf g H.F.hnn (le_refl (k + 1)) hk (fun y => cs.z (k + 1) • outField N o' y)
        (jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (k + 1) z) :=
  blockCfgOf_agree (H := H) g hk _ _ _
    (fun y hy => by simp only [outField_agree hk Z' o o' hoo y (Or.inl hy)]) z hz

theorem subMultiscaleField_agree (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k)
    (o o' : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (hoo : ∀ y : Vblk R (H.localHistory M K (k + 1) Z') (k + 1),
      y.1 ∉ gaussBlocks (H.localHistory M K (k + 1) Z') k → o y = o' y) :
    subMultiscaleField N (H.localHistory M K (k + 1) Z') (k + 1)
        (Vblk R (H.localHistory M K (k + 1) Z') (k + 1)) x o =
      subMultiscaleField N (H.localHistory M K (k + 1) Z') (k + 1)
        (Vblk R (H.localHistory M K (k + 1) Z') (k + 1)) x o' := by
  classical
  funext j y
  unfold subMultiscaleField
  by_cases hj : j < k + 1
  · simp only [hj, ↓reduceIte]
  · by_cases hjk : j = k + 1
    · subst hjk
      simp only [lt_irrefl, ↓reduceIte, ↓reduceDIte]
      by_cases hb : (k + 1 = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) (k + 1) y
          ((H.localHistory M K (k + 1) Z').Omega (k + 1 - 1)))
      · simp only [hb, ↓reduceIte]
        refine outField_agree hK Z' o o' hoo y (Or.inl ?_)
        rcases hb with hb | hb
        · omega
        · obtain ⟨x0, hx0⟩ := exists_site_in_block (S := S) (n := n) (M := M) hK y
          have h1 := (hb x0 hx0).1
          have h2 : cubeMap n S.L M K (k + 1) x0 ∈ ((H.locRH (k + 1) Z').step k).Omega := h1
          rwa [← blockCube_eq_cubeMap H.F.hnn hK hx0] at h2
      · simp only [hb, ↓reduceIte]
    · simp only [hj, hjk, ↓reduceIte, ↓reduceDIte]

theorem theta_congr0 (g : Geo S n R M) (hk : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (o o' : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (hoo : ∀ y : Vblk R (H.localHistory M K (k + 1) Z') (k + 1),
      y.1 ∉ gaussBlocks (H.localHistory M K (k + 1) Z') k → o y = o' y)
    (z : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)))
    (hz : blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) z ∈
      ((H.locRH (k + 1) Z').step k).Omega) :
    (locLiftTheta g (H.locRH (k + 1) Z') k Z'.1 hk o).toC
        (jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (k + 1) z) =
      (locLiftTheta g (H.locRH (k + 1) Z') k Z'.1 hk o').toC
        (jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (k + 1) z) := by
  have h := blockCfgOf_agree (H := H) g hk (outField N o) (outField N o')
    ((H.locRH (k + 1) Z').step k).Omega
    (fun y hy => outField_agree hk Z' o o' hoo y (Or.inl hy)) z hz
  funext i
  simp only [BlockCfg.toC]
  exact congrArg (fun r : ℝ => (r : ℂ)) (congrFun h i)

theorem locData_congr (g : Geo S n R M) (hk : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (o o' : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (hoo : ∀ y : Vblk R (H.localHistory M K (k + 1) Z') (k + 1),
      y.1 ∉ gaussBlocks (H.localHistory M K (k + 1) Z') k → o y = o' y)
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hv : EuclideanSpace ℝ (Fin N)) :
    locData g (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H Z') hk o x hv =
      locData g (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H Z') hk o' x hv := by
  unfold locData
  exact liftMixed_congr_Om _ _ _ (fun x' _ hx' =>
    theta_congr0 g hk Z' o o' hoo x' (mem_fineK1.mp hx'))

theorem locBg_congr (g : Geo S n R M) (cs : OpConsts) (hk : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (o o' : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (hoo : ∀ y : Vblk R (H.localHistory M K (k + 1) Z') (k + 1),
      y.1 ∉ gaussBlocks (H.localHistory M K (k + 1) Z') k → o y = o' y)
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hv : EuclideanSpace ℝ (Fin N)) :
    locBg g (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H Z') cs hk o x hv =
      locBg g (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H Z') cs hk o' x hv := by
  unfold locBg bgLocPiece
  congr 1
  exact liftMixed_congr_Om _ _ _ (fun x' _ hx' =>
    theta_congr0 g hk Z' o o' hoo x' (mem_fineK1.mp hx'))

theorem locPhi_congr (g : Geo S n R M) (cs : OpConsts) (hk : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (o o' : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (hoo : ∀ y : Vblk R (H.localHistory M K (k + 1) Z') (k + 1),
      y.1 ∉ gaussBlocks (H.localHistory M K (k + 1) Z') k → o y = o' y)
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hv : EuclideanSpace ℝ (Fin N)) :
    locPhi g (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H Z') cs hk o x hv =
      locPhi g (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H Z') cs hk o' x hv := by
  unfold locPhi
  rw [locData_congr g hk Z' o o' hoo x hv, locBg_congr g cs hk Z' o o' hoo x hv]

theorem mainActionLoc_congr (g : Geo S n R M) (cs : OpConsts) (hk : k + 1 ≤ K)
    (Z' : H.Comp (k + 1))
    (o o' : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (hoo : ∀ y : Vblk R (H.localHistory M K (k + 1) Z') (k + 1),
      y.1 ∉ gaussBlocks (H.localHistory M K (k + 1) Z') k → o y = o' y)
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hv : EuclideanSpace ℝ (Fin N)) :
    mainActionLoc g (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H Z') cs hk (locRH_rem (k + 1) Z') o x hv =
      mainActionLoc g (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H Z') cs hk (locRH_rem (k + 1) Z') o' x hv := by
  have e2 : subMultiscaleField N (locHist (H.locRH (k + 1) Z') M K (k + 1) Z'.1) (k + 1)
      (Vblk R (locHist (H.locRH (k + 1) Z') M K (k + 1) Z'.1) (k + 1)) x o =
      subMultiscaleField N (locHist (H.locRH (k + 1) Z') M K (k + 1) Z'.1) (k + 1)
      (Vblk R (locHist (H.locRH (k + 1) Z') M K (k + 1) Z'.1) (k + 1)) x o' :=
    subMultiscaleField_agree hk Z' x o o' hoo
  unfold mainActionLoc
  rw [locPhi_congr g cs hk Z' o o' hoo x hv]
  erw [e2]
  rfl

open Classical in
theorem quietRest_congr (Z' : H.Comp (k + 1))
    (o o' : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hv : EuclideanSpace ℝ (Fin N))
    (hoo : ∀ y : Vblk R (H.localHistory M K (k + 1) Z') (k + 1),
      y.1 ∉ gaussBlocks (H.localHistory M K (k + 1) Z') k → o y = o' y) :
    quietRest g (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H Z') cs hk (locRH_rem (k + 1) Z') o x hv =
      quietRest g (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H Z') cs hk (locRH_rem (k + 1) Z') o' x hv := by
  unfold quietRest
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_) ?_) ?_) ?_) ?_
  · rfl
  · unfold cubeProd
    refine Finset.prod_congr rfl fun y0 _ => ?_
    refine chiPrimeNew_congr_Om _ _ _ _ _ H.F.ok.two_le_L (by have := g.hc; omega) _ _ _ _ _ ?_
    intro z _ hzOm
    exact theta_congr g cs hk Z' o o' hoo z
      (cubeSub_omega_mem hk Z' (mem_cubePre.mp hzOm))
  · unfold cubeProd
    refine Finset.prod_congr rfl fun y0 _ => ?_
    refine chiPrimeNew_congr_Om _ _ _ _ _ H.F.ok.two_le_L (by have := g.hc; omega) _ _ _ _ _ ?_
    intro z _ hzOm
    exact theta_congr g cs hk Z' o o' hoo z
      (cubeSub_omega_mem hk Z' (mem_cubePre.mp hzOm))
  · unfold cubeProd
    refine Finset.prod_congr rfl fun y0 hy0 => ?_
    have hy0' : y0 ∈ quietA4 (H.localHistory M K (k + 1) Z') k :=
      (Finset.mem_filter.mp hy0).2
    refine chiNext_stencil _ _ _ _ H.F.ok.two_le_L (by have := g.hc; omega) (by simp) _ ?_
    intro z hz
    refine blockCfgOf_agree (H := H) g hk _ _ {c | c ∈ ((H.locRH (k + 1) Z').step k).Omega ∨
      c ∉ (Z'.1 : Set (Torus S.d (n (k + 1))))} (fun y hy => ?_) z ?_
    · exact outField_agree hk Z' o o' hoo y hy
    · by_contra hcon
      simp only [Set.mem_ofPred_eq, not_or, not_not] at hcon
      obtain ⟨hnO, hZ⟩ := hcon
      apply hy0'.2
      show y0 ∈ nbhd 3 {w | CubeSub (S := S) (n := n) M K (k + 1) w
        ((H.localHistory M K (k + 1) Z').Z (k + 1) \ (H.localHistory M K (k + 1) Z').Omega k)}
      refine mem_nbhd.mpr ⟨blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) z, ?_, ?_⟩
      · intro x' hx'
        refine ⟨⟨?_, ?_⟩, fun hh => hnO ?_⟩
        · show cubeMap n S.L M K (k + 1) x' ∈ ((H.locRH (k + 1) Z').step (k + 1)).Z
          rw [locRH_Z Z' le_rfl, lin_self, hx']; exact hZ
        · show cubeMap n S.L M K (k + 1) x' ∈ (Z'.1 : Set (Torus S.d (n (k + 1))))
          rw [hx']; exact hZ
        · have := hh.1
          have h2 : cubeMap n S.L M K (k + 1) x' ∈ ((H.locRH (k + 1) Z').step k).Omega := this
          rwa [hx'] at h2
      · obtain ⟨w, hw, hd⟩ := mem_nbhd.mp hz
        rw [Set.mem_singleton_iff] at hw
        subst hw
        rwa [supDist_comm]
  · exact congrArg (fun m => chiNew (locHist (H.locRH (k + 1) Z') M K (k + 1) Z'.1) k
      ((H.locRH (k + 1) Z').histGen (M := M) (locRH_rem (k + 1) Z') H.F.ok.two_le_L K
        (fun j _ _ => g.hRlow j))
      (fineSet (S := S) (n := n) M K (k + 1) (Z'.1 : Set (Torus S.d (n (k + 1))))) cs.delta cs.p0
      cs.Cpsi (m, subFluctField N (locHist (H.locRH (k + 1) Z') M K (k + 1) Z'.1) (k + 1) x))
      (subMultiscaleField_agree hk Z' x o o' hoo)
  · rw [locData_congr g hk Z' o o' hoo x hv]
  · rw [mainActionLoc_congr g cs hk Z' o o' hoo x hv]

end Indep

end Balaban.LargeField

