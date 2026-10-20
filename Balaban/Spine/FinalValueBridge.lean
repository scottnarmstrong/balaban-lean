/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfConst
public import Balaban.Spine.FinalValue
public import Balaban.Fluctuation.CubeActionReal

/-!
# The single-scale action on the whole torus is the Background-theory action

A6-3 (a), step (P1c). For the cut `Y = univ` the generating set `𝔹_k(W_k)` has the single layer
`Ω_1 = … = Ω_k = univ`, so the multiscale action `actionG` of `actStar2` (with the level generating
set) is the Background-theory action `actionC` of the lifted datum at the real background field:
`actStar2_univ_eq_actionC`.
-/

@[expose] public section

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7
  Balaban.LargeField.Def7v2

namespace Balaban.RootFSpine

section Generic

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- `actionG` depends on the generating set only through the sets `lam G n`, `1 ≤ n ≤ q`. -/
theorem actionG_congr_lam {G₁ : GeneratingSet d L N₀ q ϱ} {G₂ : GeneratingSet d L N₀ q ϱ'}
    (h : ∀ n, 1 ≤ n → n ≤ q → lam G₁ n = lam G₂ n) (a : ℕ → ℝ) (μ : ℝ) (v : E)
    (X : Finset (Site d L N₀ q)) (ψ : (m : ℕ) → Blk d L N₀ q m → E) (φ : Site d L N₀ q → E) :
    actionG G₁ a μ v X ψ φ = actionG G₂ a μ v X ψ φ := by
  unfold actionG
  have e : ∀ n ∈ Finset.Icc 1 q,
      ∑ y ∈ tBlocks d L N₀ q n (lam G₁ n ∩ X),
        a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ q n φ y‖ ^ 2 =
      ∑ y ∈ tBlocks d L N₀ q n (lam G₂ n ∩ X),
        a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ q n φ y‖ ^ 2 := fun n hn => by
    obtain ⟨hn1, hnq⟩ := Finset.mem_Icc.1 hn
    rw [h n hn1 hnq]
  rw [Finset.sum_congr rfl e]

/-- A generating set with `Ω_n = univ` for `1 ≤ n ≤ q` has the single layer `q`. -/
theorem lam_of_Ω_univ {G : GeneratingSet d L N₀ q ϱ} (hΩ : ∀ n, 1 ≤ n → n ≤ q → G.Ω n = Finset.univ)
    {n : ℕ} (hn1 : 1 ≤ n) (hnq : n ≤ q) :
    lam G n = if n = q then Finset.univ else ∅ := by
  unfold lam
  simp only [show n ≠ 0 from by omega, ↓reduceIte]
  ext x
  by_cases hnq' : n = q
  · subst hnq'
    simp [GeneratingSet.layer, hΩ n hn1 le_rfl, G.top]
  · have : n + 1 ≤ q := by omega
    simp [GeneratingSet.layer, hΩ n hn1 hnq, hΩ (n + 1) (by omega) this, hnq']

end Generic

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))

/-- **`A*_k` on the whole torus is the Background-theory action** (`k ≥ 1`, `d ≥ 2`): the value
`actStar2 C univ` is the real action of the lifted datum at the real background `φ̄_k`. -/
theorem actStar2_univ_eq_actionC (hk : 1 ≤ k) (hd2 : 2 ≤ S.d) :
    ((actStar2 C Set.univ ψk hv : ℝ) : ℂ) =
      actionC (C.genW Set.univ) C.weights (sfActMass2 C.cs k)
        (liftSingle (C.genW Set.univ) (C.liftData ψk) (hC hv))
        (Fluctuation.toFieldC (C.genW Set.univ) (C.phiBar Set.univ ψk hv)) := by
  classical
  have hb : C.bgSet (Set.univ : Set (Torus S.d (n k))) = Finset.univ := by
    ext x; simp [SFCtx.bgSet]
  have hΩ : ∀ m, 1 ≤ m → m ≤ k → (C.genW (Set.univ : Set (Torus S.d (n k)))).Ω m = Finset.univ :=
    fun m _ hmk => genW_Ω_univ_of_le C hmk
  have hlam : ∀ m, 1 ≤ m → m ≤ k → lam (C.genW (Set.univ : Set (Torus S.d (n k)))) m =
      lam (levelGen (d := S.d) (L := S.L) (N₀ := C.geo.M1 * (C.geo.c * n k)) (ϱ := (1 : ℝ)) k) m := by
    intro m hm1 hmk
    rw [lam_of_Ω_univ hΩ hm1 hmk]
    unfold lam
    simp only [show m ≠ 0 from by omega, ↓reduceIte]
    ext x
    by_cases h : m = k
    · subst h; simp [GeneratingSet.layer, levelGen]
    · have : m + 1 ≤ k := by omega
      simp [GeneratingSet.layer, levelGen, hmk, this, h]
  rw [← Fluctuation.cubeActionStar_univ]
  have hmem : ∀ x : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ k),
      x ∈ (C.genW (Set.univ : Set (Torus S.d (n k)))).Ω 1 := fun x => by
    rw [genW_Ω_univ C hk]; exact Finset.mem_univ x
  rw [Fluctuation.cubeActionStar_eq_actionG (G := C.genW Set.univ) hd2 Finset.univ
    (fun x _ => hmem x) (fun _ _ _ x _ _ y _ => Finset.mem_univ y) _ _ _ (C.psiLevelK ψk) hv
    (fun x hx => absurd (hmem x) hx) ?_ ?_]
  · unfold actStar2
    rw [hb]
    have e := actionG_congr_lam (G₁ := levelGen (d := S.d) (L := S.L)
      (N₀ := C.geo.M1 * (C.geo.c * n k)) (ϱ := (1 : ℝ)) k) (G₂ := C.genW Set.univ)
      (fun m h1 h2 => (hlam m h1 h2).symm) C.weights (sfActMass2 C.cs k) hv Finset.univ
      (C.psiLevelK ψk) (C.phiBar Set.univ ψk hv)
    rw [e]
  · intro m hm1 hmk x hx i
    have hxd : x ∈ dataSites (C.genW (Set.univ : Set (Torus S.d (n k)))) :=
      (mem_dataSites _).2 (Or.inl (hmem x))
    have hmk' : m = k := by
      by_contra hne
      have h1 : x ∈ (C.genW (Set.univ : Set (Torus S.d (n k)))).Ω m := ((C.genW (Set.univ : Set (Torus S.d (n k)))).mem_layer.1 hx).1
      have h2 := ((C.genW (Set.univ : Set (Torus S.d (n k)))).mem_layer.1 hx).2
      rw [hΩ (m + 1) (by omega) (by omega)] at h2
      exact h2 (Finset.mem_univ x)
    subst hmk'
    rw [liftSingle_Ψ _ _ _ hxd]
    simp [SFCtx.liftData, SFCtx.psiLevelK, singleScale, BlockCfg.toC, blockCfgOf, blkMap, jBlock]
  · intro x _ i
    rw [liftSingle_h _ _ _ (hmem x)]
    rfl

end Ctx

end Balaban.RootFSpine
