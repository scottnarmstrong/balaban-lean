module

public import Balaban.LargeField.Characteristic.Functions
import Mathlib.Tactic.Linarith

/-!
# Stencils of the characteristic functions (Part II, Lemma II.3.3, second half)

The data of the generating sets `G_k(□) = 𝔹_k(□^{∼2})` and `G_{k+1}(□')` live on
`Ω₁ ∪ C(Ω₁) ⊂ □^{∼3}` (Lemma II.2.3 (c)), so `χ_k(□)` depends only on `ψ_k` on the blocks of the
cubes of `□^{∼3}`, `χ'_{k+1}(□')` only on `(ψ_k, θ)` there, `χ'^{(k)}(□')` and `χ^{(k)}(□')` only
on the blocks of `□'`, and `χ_{k+1}(□')` only on `ψ_{k+1}` on `□'^{∼3}`.  "`ψ` and `ψ'` agree on
`E`" is stated on fine sites: for every fine site `x` whose `π_q`-cube lies in `E`, the values at
the block of `x` agree.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

set_option linter.unusedSectionVars false

/-! ### The lifted data depends only on the blocks of the data sites -/

section LiftCongr

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem liftSingle_congr (G : GeneratingSet d L N₀ k ϱ) {ψ ψ' : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ}
    {h : Fin N → ℂ} (hψ : ∀ x ∈ dataSites G, ψ (jBlock d L N₀ k k x) = ψ' (jBlock d L N₀ k k x)) :
    liftSingle G ψ h = liftSingle G ψ' h := by
  classical
  refine BgData.ext' (funext fun x => ?_) rfl
  by_cases hx : x ∈ dataSites G
  · simp only [liftSingle, BgData.clip, hx, ↓reduceIte, blockLift]
    exact hψ x hx
  · simp [liftSingle, BgData.clip, hx]

theorem liftMixed_congr (G : GeneratingSet d L N₀ (k + 1) ϱ)
    {Ω : Finset (Torus d (N₀ * L ^ (k + 1)))} (hΩ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω)
    (hG : G.Ω (k + 1) ⊆ Ω) {ψ ψ' : Torus d (N₀ * L ^ (k + 1 - k)) → Fin N → ℂ}
    {ϑ ϑ' : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ} {h : Fin N → ℂ}
    (hψ : ∀ x ∈ dataSites G, ψ (jBlock d L N₀ (k + 1) k x) = ψ' (jBlock d L N₀ (k + 1) k x))
    (hϑ : ∀ x ∈ dataSites G,
      ϑ (jBlock d L N₀ (k + 1) (k + 1) x) = ϑ' (jBlock d L N₀ (k + 1) (k + 1) x)) :
    liftMixed G hΩ hG ψ ϑ h = liftMixed G hΩ hG ψ' ϑ' h := by
  classical
  refine BgData.ext' (funext fun x => ?_) rfl
  by_cases hx : x ∈ dataSites G
  · simp only [liftMixed, BgData.clip, hx, ↓reduceIte, mixedLift, blockLift]
    split_ifs
    · exact hϑ x hx
    · exact hψ x hx
  · simp [liftMixed, BgData.clip, hx]

end LiftCongr

/-! ### The range of the data sites -/

section Range

variable {d M1 N₁ L q : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

/-- **Lemma II.2.3 (c)** for every generating set `G'` whose first layer lies in that of `𝔹_j(X)`:
the data sites of `G'` lie in the `π_j`-cubes of, or adjacent to, a site of `X`. -/
theorem dataSites_cube_near {j : ℕ} (hL : 2 ≤ L) (hj : j ≤ q)
    (X : Finset (Torus d (M1 * N₁ * L ^ q)))
    {G' : GeneratingSet d L (M1 * N₁) q (minSep L M1)}
    (hG' : G'.Ω 1 ⊆ (minimalGenSet hj X).Ω 1) {M : ℕ} (hM : 12 * M1 ≤ M) {m' : ℕ}
    [NeZero m'] (hP : M1 * N₁ * L ^ q = (L ^ j * M) * m') {x : Torus d (M1 * N₁ * L ^ q)}
    (hx : x ∈ dataSites G') :
    ∃ y ∈ X, supDist (blockMap (L ^ j * M) m' x) (blockMap (L ^ j * M) m' y) ≤ 1 := by
  have hΩ : ∀ z ∈ G'.Ω 1, ∃ y ∈ X, supDist z y ≤ 11 * M1 * L ^ j := by
    intro z hz
    have hz' := hG' hz
    rw [minimalGenSet_Ω] at hz'
    by_cases h1 : 1 ≤ j
    · exact exists_near_of_mem_minLayer' X hL hj h1 hz'
    · rw [minLayer_of_gt X (by omega)] at hz'
      exact absurd hz' (Finset.notMem_empty _)
  have hnear : ∃ y ∈ X, supDist x y ≤ 11 * M1 * L ^ j + 1 := by
    rcases (mem_dataSites _).1 hx with h | h
    · obtain ⟨y, hy, hd⟩ := hΩ x h
      exact ⟨y, hy, by omega⟩
    · obtain ⟨-, x', hx', hadj⟩ := (mem_collar _).1 h
      obtain ⟨y, hy, hd⟩ := hΩ x' hx'
      have h1 : supDist x x' ≤ 1 := by
        have h2 := supDist_le_torusDist x x'
        have h3 := Multiscale.Adj.torusDist_le hadj.symm
        have : (supDist x x' : ℝ) ≤ 1 := h2.trans h3
        exact_mod_cast this
      exact ⟨y, hy, (supDist_triangle x x' y).trans (by omega)⟩
  obtain ⟨y, hy, hd⟩ := hnear
  refine ⟨y, hy, supDist_blockMap_le_one hP (D := 11 * M1 * L ^ j + 1) ?_ x y hd⟩
  have hB : 1 ≤ M1 * L ^ j := Nat.one_le_iff_ne_zero.2 (by
    have := NeZero.ne L; have := NeZero.ne M1; positivity)
  have h1 : L ^ j * (12 * M1) ≤ L ^ j * M := Nat.mul_le_mul_left _ hM
  have h2 : L ^ j * (12 * M1) = 12 * (M1 * L ^ j) := by ring
  have h3 : 11 * M1 * L ^ j = 11 * (M1 * L ^ j) := by ring
  omega

variable {c n : ℕ} [NeZero n]

theorem cube_fine_eq (hm : N₁ * L ^ (q - q) = c * n) :
    M1 * N₁ * L ^ q = (L ^ q * (c * M1)) * n := by
  have h : N₁ = c * n := by simpa using hm
  rw [h]; ring

/-- The data sites of `G_q(□) = 𝔹_q(□^{∼2})` lie in the cubes of `□^{∼3}`. -/
theorem dataSites_genCube_near (hL : 2 ≤ L) (hc : 12 ≤ c) (hm : N₁ * L ^ (q - q) = c * n)
    (y0 : Torus d n) {x : Torus d (M1 * N₁ * L ^ q)}
    (hx : x ∈ dataSites (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0)) :
    blockMap (L ^ q * (c * M1)) n x ∈ nbhd 3 {y0} := by
  obtain ⟨y, hy, hd⟩ := dataSites_cube_near (j := q) hL (le_refl q)
    (cubePre M1 N₁ L q (L ^ q * (c * M1)) n (nbhd 2 {y0}))
    (G' := genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) (fun z hz => hz)
    (M := c * M1) (by nlinarith [Nat.zero_le M1]) (cube_fine_eq hm) hx
  rw [mem_cubePre] at hy
  have h1 : blockMap (L ^ q * (c * M1)) n x ∈ nbhd 1 (nbhd 2 {y0}) :=
    mem_nbhd.2 ⟨_, hy, hd⟩
  rwa [nbhd_nbhd] at h1

/-- The data sites of `G_{k+1}(□')` lie in the cubes of `□'^{∼3}`. -/
theorem dataSites_genCubeMixed_near (hL : 2 ≤ L) (hc : 12 ≤ c) (hm : N₁ * L ^ (q - q) = c * n)
    (y0 : Torus d n) (Om : Finset (Torus d (M1 * N₁ * L ^ q)))
    (hOm : IsBlockUnion L (M1 * N₁) q q Om) {x : Torus d (M1 * N₁ * L ^ q)}
    (hx : x ∈ dataSites (genCubeMixed hm y0 Om hOm)) :
    blockMap (L ^ q * (c * M1)) n x ∈ nbhd 3 {y0} := by
  have hsub : (genCubeMixed hm y0 Om hOm).Ω 1 ⊆
      (minimalGenSet (le_refl q) (cubePre M1 N₁ L q (L ^ q * (c * M1)) n (nbhd 2 {y0}))).Ω 1 := by
    intro z hz
    have hz' : z ∈ (if 1 = q then
        Om ∩ cubePre M1 N₁ L q (L ^ q * (c * M1)) n (nbhd 2 {y0}) else
        (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0).Ω 1) := hz
    split_ifs at hz' with h1
    · obtain rfl := h1
      rw [minimalGenSet_Ω, minLayer_self,
        (isCubeUnion_cubePre (M1 := M1) (N₁ := N₁) (L := L) (q := 1) (le_refl 1) hm
          (nbhd 2 {y0})).cubeInterior_eq]
      exact (Finset.mem_inter.1 hz').2
    · exact hz'
  obtain ⟨y, hy, hd⟩ := dataSites_cube_near (j := q) hL (le_refl q)
    (cubePre M1 N₁ L q (L ^ q * (c * M1)) n (nbhd 2 {y0})) hsub
    (M := c * M1) (by nlinarith [Nat.zero_le M1]) (cube_fine_eq hm) hx
  rw [mem_cubePre] at hy
  have h1 : blockMap (L ^ q * (c * M1)) n x ∈ nbhd 1 (nbhd 2 {y0}) :=
    mem_nbhd.2 ⟨_, hy, hd⟩
  rwa [nbhd_nbhd] at h1

end Range


/-! ### The stencils of the characteristic functions -/

section Stencils

variable {d M1 N₁ L N : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] {c n : ℕ} [NeZero n]

theorem charFn_congr {X : Type*} {P : X → Prop} {x y : X} (h : P x ↔ P y) :
    charFn P x = charFn P y := by
  by_cases hx : P x
  · rw [charFn_eq_one hx, charFn_eq_one (h.1 hx)]
  · rw [charFn_eq_zero hx, charFn_eq_zero (fun hy => hx (h.2 hy))]

theorem mem_nbhd_zero {y y0 : Torus d n} : y ∈ nbhd 0 ({y0} : Set (Torus d n)) ↔ y = y0 := by
  rw [mem_nbhd]
  constructor
  · rintro ⟨x, hx, hd⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact supDist_eq_zero.1 (Nat.le_zero.1 hd)
  · rintro rfl
    exact ⟨y, rfl, by simp [supDist_self]⟩

/-- `χ_q(□)` depends only on `ψ_q` on the blocks of the cubes of `□^{∼3}` (Lemma II.3.3). -/
theorem chiK_stencil {q : ℕ} (a : ℕ → ℝ) (μ δ : ℝ) (h : Fin N → ℝ) (hL : 2 ≤ L) (hc : 12 ≤ c)
    (hm : N₁ * L ^ (q - q) = c * n) (y0 : Torus d n)
    {ψ ψ' : BlockCfg d (M1 * N₁) L q q N}
    (hψ : ∀ x : Torus d (M1 * N₁ * L ^ q), blockMap (L ^ q * (c * M1)) n x ∈ nbhd 3 {y0} →
      ψ (jBlock d L (M1 * N₁) q q x) = ψ' (jBlock d L (M1 * N₁) q q x)) :
    chiK a μ δ h c n y0 ψ = chiK a μ δ h c n y0 ψ' := by
  have hD : cubeData (M1 := M1) (N₁ := N₁) (L := L) (q := q) h c n y0 ψ =
      cubeData h c n y0 ψ' := by
    refine liftSingle_congr _ fun x hx => ?_
    have := hψ x (dataSites_genCube_near hL hc hm y0 hx)
    exact funext fun i => by simp only [BlockCfg.toC, this]
  exact charFn_congr (by simp only [ChiKProp, hD])

/-- `χ_{k+1}(□')` depends only on `ψ_{k+1}` on the blocks of the cubes of `□'^{∼3}`. -/
theorem chiNext_stencil {k : ℕ} (a : ℕ → ℝ) (μ δ : ℝ) (h : Fin N → ℝ) (hL : 2 ≤ L) (hc : 12 ≤ c)
    (hm : N₁ * L ^ (k + 1 - (k + 1)) = c * n) (y0 : Torus d n)
    {ψ ψ' : BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N}
    (hψ : ∀ x : Torus d (M1 * N₁ * L ^ (k + 1)),
      blockMap (L ^ (k + 1) * (c * M1)) n x ∈ nbhd 3 {y0} →
      ψ (jBlock d L (M1 * N₁) (k + 1) (k + 1) x) = ψ' (jBlock d L (M1 * N₁) (k + 1) (k + 1) x)) :
    chiNext a μ δ h c n k y0 ψ = chiNext a μ δ h c n k y0 ψ' :=
  chiK_stencil a μ δ h hL hc hm y0 hψ

/-- `χ'_{k+1}(□')` depends only on `(ψ_k, θ)` on the blocks of the cubes of `□'^{∼3}`. -/
theorem chiPrimeNew_stencil {k : ℕ} (a : ℕ → ℝ) (μ δ νk : ℝ) (h : Fin N → ℝ) (hL : 2 ≤ L)
    (hc : 12 ≤ c) (hm : N₁ * L ^ (k + 1 - (k + 1)) = c * n) (y0 : Torus d n)
    (Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1))))
    (hOm : IsBlockUnion L (M1 * N₁) (k + 1) (k + 1) Om)
    {p p' : BlockCfg d (M1 * N₁) L (k + 1) k N × BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N}
    (hψ : ∀ x : Torus d (M1 * N₁ * L ^ (k + 1)),
      blockMap (L ^ (k + 1) * (c * M1)) n x ∈ nbhd 3 {y0} →
      p.1 (jBlock d L (M1 * N₁) (k + 1) k x) = p'.1 (jBlock d L (M1 * N₁) (k + 1) k x))
    (hθ : ∀ x : Torus d (M1 * N₁ * L ^ (k + 1)),
      blockMap (L ^ (k + 1) * (c * M1)) n x ∈ nbhd 3 {y0} →
      p.2 (jBlock d L (M1 * N₁) (k + 1) (k + 1) x) =
        p'.2 (jBlock d L (M1 * N₁) (k + 1) (k + 1) x)) :
    chiPrimeNew a μ δ νk h hm y0 Om hOm p = chiPrimeNew a μ δ νk h hm y0 Om hOm p' := by
  have hD : mixedData h hm y0 Om hOm p.1 p.2 = mixedData h hm y0 Om hOm p'.1 p'.2 := by
    refine liftMixed_congr _ _ _ (fun x hx => ?_) (fun x hx => ?_)
    · have := hψ x (dataSites_genCubeMixed_near hL hc hm y0 Om hOm hx)
      exact funext fun i => by simp only [BlockCfg.toC, this]
    · have := hθ x (dataSites_genCubeMixed_near hL hc hm y0 Om hOm hx)
      exact funext fun i => by simp only [BlockCfg.toC, this]
  exact charFn_congr (by simp only [ChiPrimeNewProp, hD])

/-- Blocks of the same `(q)`-block lie in the same `π_q`-cube. -/
theorem cube_eq_of_jBlock_eq {q : ℕ} (hm : N₁ * L ^ (q - q) = c * n)
    {x x' : Torus d (M1 * N₁ * L ^ q)}
    (h : jBlock d L (M1 * N₁) q q x = jBlock d L (M1 * N₁) q q x') :
    blockMap (L ^ q * (c * M1)) n x = blockMap (L ^ q * (c * M1)) n x' := by
  have hℓ : M1 * N₁ * L ^ q = L ^ q * (M1 * N₁ * L ^ (q - q)) := by
    simp
    ring
  have hm' : M1 * N₁ * L ^ (q - q) = (c * M1) * n := by
    have : N₁ = c * n := by simpa using hm
    simp [this]; ring
  have hx : ∀ z : Torus d (M1 * N₁ * L ^ q), blockMap (L ^ q * (c * M1)) n z =
      blockMap (c * M1) n (jBlock d L (M1 * N₁) q q z) := by
    intro z
    unfold jBlock
    rw [blockMap_comp hℓ hm']
  rw [hx x, hx x', h]

/-- `χ'^{(k)}(□')` depends only on `θ` and `ψ_k` on the blocks of the cube `□'`. -/
theorem chiPrimeOld_stencil {k : ℕ} (δ : ℝ) (hm : N₁ * L ^ (k + 1 - (k + 1)) = c * n)
    (y0 : Torus d n)
    {p p' : BlockCfg d (M1 * N₁) L (k + 1) k N × BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N}
    (hψ : ∀ x : Torus d (M1 * N₁ * L ^ (k + 1)), blockMap (L ^ (k + 1) * (c * M1)) n x = y0 →
      p.1 (jBlock d L (M1 * N₁) (k + 1) k x) = p'.1 (jBlock d L (M1 * N₁) (k + 1) k x))
    (hθ : ∀ x : Torus d (M1 * N₁ * L ^ (k + 1)), blockMap (L ^ (k + 1) * (c * M1)) n x = y0 →
      p.2 (jBlock d L (M1 * N₁) (k + 1) (k + 1) x) =
        p'.2 (jBlock d L (M1 * N₁) (k + 1) (k + 1) x)) :
    chiPrimeOld (M1 := M1) (N₁ := N₁) (L := L) δ c n y0 p =
      chiPrimeOld (M1 := M1) (N₁ := N₁) (L := L) δ c n y0 p' := by
  classical
  refine charFn_congr ?_
  have hQ : ∀ x : Torus d (M1 * N₁ * L ^ (k + 1)),
      blockMap (L ^ (k + 1) * (c * M1)) n x = y0 → blockSumQ p.1 x = blockSumQ p'.1 x := by
    intro x hx
    funext i
    unfold blockSumQ
    congr 1
    refine Finset.sum_congr rfl fun y' hy' => ?_
    obtain ⟨x', rfl, hx'⟩ := (Finset.mem_filter.1 hy').2
    rw [hψ x' ((cube_eq_of_jBlock_eq hm hx').trans hx)]
  have hmem : ∀ x : Torus d (M1 * N₁ * L ^ (k + 1)),
      x ∈ cubeNbhd M1 N₁ L (k + 1) c n 0 y0 ↔ blockMap (L ^ (k + 1) * (c * M1)) n x = y0 := by
    intro x
    unfold cubeNbhd
    rw [mem_cubePre, mem_nbhd_zero]
  unfold ChiPrimeOldProp
  refine forall_congr' fun x => imp_congr_right fun hx => ?_
  have hx' := (hmem x).1 hx
  rw [hQ x hx', hθ x hx']

/-- `χ^{(k)}(□')` depends only on `ψ'_k` on the blocks of the cube `□'`. -/
theorem chiFluct_stencil {k : ℕ} (p1 : ℝ) (y0 : Torus d n)
    {ψ ψ' : BlockCfg d (M1 * N₁) L (k + 1) k N}
    (hψ : ∀ x : Torus d (M1 * N₁ * L ^ (k + 1)), blockMap (L ^ (k + 1) * (c * M1)) n x = y0 →
      ψ (jBlock d L (M1 * N₁) (k + 1) k x) = ψ' (jBlock d L (M1 * N₁) (k + 1) k x)) :
    chiFluct (M1 := M1) (N₁ := N₁) (L := L) c n y0 p1 ψ =
      chiFluct (M1 := M1) (N₁ := N₁) (L := L) c n y0 p1 ψ' := by
  refine charFn_congr ?_
  have hmem : ∀ x : Torus d (M1 * N₁ * L ^ (k + 1)),
      x ∈ cubeNbhd M1 N₁ L (k + 1) c n 0 y0 ↔ blockMap (L ^ (k + 1) * (c * M1)) n x = y0 := by
    intro x
    unfold cubeNbhd
    rw [mem_cubePre, mem_nbhd_zero]
  unfold ChiFluctProp
  refine forall_congr' fun x => imp_congr_right fun hx => ?_
  rw [hψ x ((hmem x).1 hx)]

end Stencils

end Balaban.LargeField
