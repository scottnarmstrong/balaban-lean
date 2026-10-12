module

public import Balaban.LargeField.Region.SymmLevel
public import Balaban.LargeField.Characteristic.RegSymm
public import Balaban.LargeField.Background.LiftSymm
public import Balaban.LargeField.Operators.QuietSymm
import Mathlib.Tactic.Ring

/-!
# Lattice covariance of the characteristic functions `χ_q`, `χ'_{q}`

Let `A` be an affine lattice isometry of the level-`q` torus aligned to the cubes of side `c M1 L^q`.
It acts on the cubes of `𝕋_q` by `e = A.coarse (L^q c M1) n` and on the `q`-blocks by
`A.coarse (L^q)`.  The characteristic functions of the cube `□` at the configuration `ψ` are those of
`e □` at the transported configuration (`chiK_euclid`, `chiPrimeNew_euclid`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Chi

variable {d M1 N₁ L N q c n : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] [NeZero n]
  {A : AffIso d (M1 * N₁ * L ^ q)} (hal : A.Aligned (c * M1 * L ^ q)) (hm : N₁ = c * n)
include hal hm

theorem cubeNbhd_map (r : ℕ) (y0 : Torus d n) :
    (cubeNbhd M1 N₁ L q c n r y0).map A.toEquiv.toEmbedding =
      cubeNbhd M1 N₁ L q c n r ((A.coarse (L ^ q * (c * M1)) n).toFun y0) := by
  have hpos : 0 < L ^ q * (c * M1) := by
    have := NeZero.pos L; have := NeZero.pos M1
    have hc : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · exact absurd (by simpa [h] using hm) (NeZero.ne N₁)
      · exact h
    positivity
  unfold cubeNbhd
  rw [cubePre_map hal (by rw [hm]; ring) hpos ⟨1, by ring⟩, AffIso.image_nbhd, Set.image_singleton]

theorem aligned_pow : A.Aligned (L ^ q) :=
  AffIso.Aligned.mono A hal ⟨c * M1, by ring⟩

/-- **Covariance of `χ_q(□)`.** -/
theorem chiK_euclid (a : ℕ → ℝ) (μ δ : ℝ) (h : Fin N → ℝ) (y0 : Torus d n)
    (ψ ψ' : BlockCfg d (M1 * N₁) L q q N)
    (hψ : ∀ y, ψ' ((A.coarse (L ^ q) (M1 * N₁ * L ^ (q - q))).toFun y) = ψ y) :
    chiK (M1 := M1) (N₁ := N₁) (L := L) (q := q) (N := N) a μ δ h c n
        ((A.coarse (L ^ q * (c * M1)) n).toFun y0) ψ' =
      chiK (M1 := M1) (N₁ := N₁) (L := L) (q := q) (N := N) a μ δ h c n y0 ψ := by
  unfold chiK
  refine charFn_congr_apply ?_
  have hq := aligned_pow hal hm
  let S := genCube_latSymm hal hm y0 hq
  have hsym : S.sym (cubeData (M1 := M1) (N₁ := N₁) (L := L) (q := q) h c n y0 ψ) =
      cubeData (M1 := M1) (N₁ := N₁) (L := L) (q := q) h c n
        ((A.coarse (L ^ q * (c * M1)) n).toFun y0) ψ' := by
    unfold cubeData
    refine S.liftSingle_sym (A.coarse (L ^ q) (M1 * N₁ * L ^ (q - q))).toEquiv
      (fun x => jBlock_aff0 A hq le_rfl x) _ _ (fun y => ?_) _
    funext i
    simp only [BlockCfg.toC]
    exact congrArg (fun r => (r i : ℂ)) (hψ y)
  unfold ChiKProp
  rw [← hsym, ← cubeNbhd_map hal hm]
  exact S.reg_sym_iff a μ _ δ _ _

end Chi


section ChiMixed

variable {d M1 N₁ L N k c n : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] [NeZero n]
  {A : AffIso d (M1 * N₁ * L ^ (k + 1))} (hal : A.Aligned (c * M1 * L ^ (k + 1)))
  (hm1 : N₁ * L ^ (k + 1 - (k + 1)) = c * n)
include hal hm1

/-- **Covariance of `χ'_{k+1}(□')`.** -/
theorem chiPrimeNew_euclid (a : ℕ → ℝ) (μ δ νk : ℝ) (h : Fin N → ℝ) (y0 : Torus d n)
    (Om Om' : Finset (Torus d (M1 * N₁ * L ^ (k + 1))))
    (hOm : IsBlockUnion L (M1 * N₁) (k + 1) (k + 1) Om)
    (hOm' : IsBlockUnion L (M1 * N₁) (k + 1) (k + 1) Om')
    (hOO : Om' = Om.map A.toEquiv.toEmbedding)
    (p p' : BlockCfg d (M1 * N₁) L (k + 1) k N × BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N)
    (hψ : ∀ y, p'.1 ((A.coarse (L ^ k) (M1 * N₁ * L ^ (k + 1 - k))).toFun y) = p.1 y)
    (hθ : ∀ y, p'.2 ((A.coarse (L ^ (k + 1)) (M1 * N₁ * L ^ (k + 1 - (k + 1)))).toFun y) = p.2 y) :
    chiPrimeNew (M1 := M1) (N₁ := N₁) (L := L) (N := N) (k := k) a μ δ νk h (c := c) (n := n)
        hm1 ((A.coarse (L ^ (k + 1) * (c * M1)) n).toFun y0) Om' hOm' p' =
      chiPrimeNew (M1 := M1) (N₁ := N₁) (L := L) (N := N) (k := k) a μ δ νk h (c := c) (n := n)
        hm1 y0 Om hOm p := by
  have hm : N₁ = c * n := by simpa using hm1
  unfold chiPrimeNew
  refine charFn_congr_apply ?_
  have hq := aligned_pow hal hm
  let S := A.latSymm hq (genCubeMixed_map hal hm hm1 y0 Om Om' hOm hOm' hOO)
  have hΩΩ : ∀ x, A.toEquiv x ∈ Om' ↔ x ∈ Om := fun x => by
    rw [hOO, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  have hsym : S.sym (mixedData (M1 := M1) (N₁ := N₁) (L := L) (k := k) h hm1 y0 Om hOm p.1 p.2) =
      mixedData (M1 := M1) (N₁ := N₁) (L := L) (k := k) h hm1
        ((A.coarse (L ^ (k + 1) * (c * M1)) n).toFun y0) Om' hOm' p'.1 p'.2 := by
    unfold mixedData
    refine S.liftMixed_sym hOm (genCubeMixed_top_subset hm1 y0 Om hOm) hOm'
      (genCubeMixed_top_subset hm1 _ Om' hOm') hΩΩ
      (A.coarse (L ^ k) (M1 * N₁ * L ^ (k + 1 - k))).toEquiv
      (A.coarse (L ^ (k + 1)) (M1 * N₁ * L ^ (k + 1 - (k + 1)))).toEquiv
      (fun x => jBlock_aff0 A hq (Nat.le_succ k) x) (fun x => jBlock_aff0 A hq le_rfl x)
      _ _ (fun y => ?_) _ _ (fun y => ?_) _
    · funext i; simp only [BlockCfg.toC]; exact congrArg (fun r => (r i : ℂ)) (hψ y)
    · funext i; simp only [BlockCfg.toC]; exact congrArg (fun r => (r i : ℂ)) (hθ y)
  have hnb := cubeNbhd_map hal hm (L := L) (M1 := M1) 1 y0
  unfold ChiPrimeNewProp
  rw [← hsym]
  refine and_congr (S.inUnionDomainR_sym_iff _) ?_
  have := S.regMixedIneq_sym a μ
    (mixedData (M1 := M1) (N₁ := N₁) (L := L) (k := k) h hm1 y0 Om hOm p.1 p.2) ((L : ℝ) ^ k) νk δ
    (cubeNbhd M1 N₁ L (k + 1) c n 1 y0 \ Om) (cubeNbhd M1 N₁ L (k + 1) c n 1 y0 ∩ Om)
    (cubeNbhd M1 N₁ L (k + 1) c n 1 y0)
  rw [Finset.map_sdiff, Finset.map_inter, hnb, ← hOO] at this
  exact this

end ChiMixed

end Balaban.LargeField
