/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalDomCore
public import Balaban.Spine.FinalDomLevel
public import Balaban.Spine.FinalDomCompose
public import Balaban.Spine.FinalSfConst
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The inherited fields `ψ^{(j)}_k` on the whole torus: bounds at every site

A6-3 (a), item 1. -/

@[expose] public section

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7
  Balaban.SmallField.Def6v2 Balaban.Localization

namespace Balaban.RootFSpine

open Balaban.SmallField

section Generic

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The bounds at every site from the real domain of a generating set with a single layer**:
if every site lies in the layer `jj` of `G` (that is `Ω_jj = univ` and `Ω_{jj+1} = ∅`), the real
domain `Ψ̃(G; m, η)` gives the bounds at every site. -/
theorem allSitesBounds_of_inPsiTilde {G : GeneratingSet d L N₀ q ϱ} {jj : ℕ} (hjj : 1 ≤ jj)
    (hjq : jj ≤ q) (hall : ∀ x, x ∈ G.Ω jj) (htop : G.Ω (jj + 1) = ∅) {m η : ℝ}
    {f : Torus d (N₀ * L ^ q) → Fin N → ℝ} {h₀ : Fin N → ℝ} (hP : InPsiTilde G m η f h₀) :
    AllSitesBounds jj m η f h₀ := by
  have hl : ∀ x, x ∈ G.layer jj := fun x => G.mem_layer.2 ⟨hall x, by rw [htop]; simp⟩
  have hidx : ∀ x, G.layerIndex x = jj := fun x => G.layerIndex_eq hjj hjq (hl x)
  have h1 : ∀ x, x ∈ G.Ω 1 := fun x => G.Ω_antitone le_rfl hjj (by omega) (hall x)
  have hd : ∀ x, x ∈ dataSites G := fun x => (mem_dataSites G).2 (Or.inl (h1 x))
  refine ⟨fun x x' hb => ?_, fun x x' hadj => hP.r1 x x' ?_, fun x => hP.r2 x (hd x),
    fun x => ?_⟩
  · exact (hP.layerConst jj hjj hjq x (hl x) x' (G.mem_blk.2 hb.symm)).symm
  · refine ⟨hd x, hd x', Or.inl (by rw [hidx, hidx]), x, ?_, x', ?_, hadj⟩
    · unfold blockSet; simp only [h1 x, ↓reduceIte, hidx]; exact G.mem_blk.2 rfl
    · unfold blockSet; simp only [h1 x', ↓reduceIte, hidx]; exact G.mem_blk.2 rfl
  · have := hP.r3 x (hd x)
    rwa [hidx] at this

omit [NeZero N₀] [NeZero L] in
/-- **The bounds at every site are invariant under the identification of tori of equal side.** -/
theorem AllSitesBounds.cast {N₀' : ℕ} (hN : N₀ = N₀') (e : N₀ * L ^ q = N₀' * L ^ q) {jj : ℕ}
    {m η : ℝ} {f : Torus d (N₀' * L ^ q) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    (hf : AllSitesBounds jj m η f h₀) :
    AllSitesBounds (N₀ := N₀) jj m η (fun x => f (torusCast e x)) h₀ := by
  subst hN
  exact hf

omit [NeZero N₀] [NeZero L] in
/-- Weaker bounds at every site: a larger radius `2 η` and a mass `m'` with
`m' L^{2j} ≤ 4 m L^{2j}`. -/
theorem AllSitesBounds.weaken {jj : ℕ} {m m' η : ℝ} {f : Torus d (N₀ * L ^ q) → Fin N → ℝ}
    {h₀ : Fin N → ℝ} (hf : AllSitesBounds jj m η f h₀) (hη : 0 < η)
    (hmm : m' * ((L : ℝ) ^ jj) ^ 2 ≤ 4 * (m * ((L : ℝ) ^ jj) ^ 2)) :
    AllSitesBounds jj m' (2 * η) f h₀ where
  block := hf.block
  adj x x' h := (hf.adj x x' h).trans (by linarith)
  sphere x := (hf.sphere x).trans (by linarith)
  dir x := by
    have h0 : 0 ≤ |1 - (∑ i, f x i * h₀ i) / rn (f x)| := abs_nonneg _
    calc m' * ((L : ℝ) ^ jj) ^ 2 * |1 - (∑ i, f x i * h₀ i) / rn (f x)|
        ≤ 4 * (m * ((L : ℝ) ^ jj) ^ 2) * |1 - (∑ i, f x i * h₀ i) / rn (f x)| :=
          mul_le_mul_of_nonneg_right hmm h0
      _ = 4 * (m * ((L : ℝ) ^ jj) ^ 2 * |1 - (∑ i, f x i * h₀ i) / rn (f x)|) := by ring
      _ < 4 * η ^ 2 := by have := hf.dir x; linarith
      _ = (2 * η) ^ 2 := by ring

end Generic

section Weights

variable {L : ℕ}

/-- The weights `a_n = a_k (1 - L^{-2k})/(1 - L^{-2n})` of the ideal flow are the weights
`compWeight L a₁` of the composition theorem with `a₁ = a_1`. -/
theorem aIdeal_eq_compWeight (hL : 2 ≤ L) (k : ℕ) (ak : ℝ) (r : ℕ) :
    Def6.aIdeal L k ak r = compWeight L (Def6.aIdeal L k ak 1) r := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have h4 : (4 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hne : (1 - (((L : ℝ)) ^ 2)⁻¹) ≠ 0 := by
    have : (((L : ℝ)) ^ 2)⁻¹ ≤ 1 / 4 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hQ : (1 - ((L : ℝ) ^ 1)⁻¹ ^ 2) = 1 - (((L : ℝ)) ^ 2)⁻¹ := by rw [pow_one, inv_pow]
  have e : ∀ n : ℕ, (((L : ℝ) ^ n) ^ 2)⁻¹ = ((L : ℝ) ^ n)⁻¹ ^ 2 := fun n => (inv_pow _ _).symm
  unfold Def6.aIdeal compWeight
  rw [hQ, e r, div_mul_cancel₀ _ hne]

end Weights

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N (j + 1) m₁ ϱ)
  (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))

/-- **The inherited field `ψ^{(j')}_k` of a cut `Y`, real part**, on the background torus. -/
noncomputable def psiJReY (Y : Set (Torus S.d (n (j + 1)))) {jj : ℕ} (hj : jj ≤ j + 1) :
    BgT C.geo (j + 1) → Fin N → ℝ :=
  fun x i => (psiSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
    (n := n (j + 1)) C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N) hj
    (W2 R Y) (C.liftData ψk) (hC hv) x i).re

/-- **The inherited field `ψ^{(j')}_k` of the whole torus, real part**, on the background torus. -/
noncomputable def psiJRe {jj : ℕ} (hj : jj ≤ j + 1) : BgT C.geo (j + 1) → Fin N → ℝ :=
  psiJReY C ψk hv Set.univ hj

/-- **The inherited fields on the `χ`-support, at every site.** On the support of the small-field
characteristic function of the whole torus (late scale `j + 1`, cube mass equal to the background
mass `ν L^{-2(j+1)}`), the inherited field `ψ^{(j')}_k`, `1 ≤ j' ≤ j + 1`, is real and satisfies the
bounds of the real data domain at every site, with radius `C₄ K₁ · 4 (d+1) δ_k`. -/
theorem psiJ_allSites {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) (hL : 3 ≤ S.L) {ν : ℝ}
    (hν : 0 < ν) (hunit : ‖hv‖ = 1) (hδ : 0 < C.cs.delta (j + 1))
    (hδ1 : (S.d + 1) * C.cs.delta (j + 1) ≤ 1)
    (hμ : C.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (hμBg : C.cs.muBg (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (hχ : C.chiY (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv ≠ 0)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    (hη : 4 * (S.d + 1) * C.cs.delta (j + 1) ≤ thm73C1 S.d S.L N) :
    (∀ x i, psiSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
      (n := n (j + 1)) C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N) hj
      (W2 R (Set.univ : Set (Torus S.d (n (j + 1))))) (C.liftData ψk) (hC hv) x i =
        ((psiJRe C ψk hv hj x i : ℝ) : ℂ)) ∧
    AllSitesBounds (N₀ := C.geo.M1 * (C.geo.c * n (j + 1))) (q := j + 1) jj
      (sfBgMassAt S.L (j + 1) ν)
      (compC4 S.d * (bgK1 S.d S.L N * (4 * (S.d + 1) * C.cs.delta (j + 1))))
      (psiJRe C ψk hv hj) (fun i => hv i) := by
  classical
  have hL2 : 2 ≤ S.L := by omega
  have hHBmu : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.mu (j + 1)) := by
    rw [hμ, ← hμBg]; exact HB
  have hP := inPsiTilde_genW_univ_late C ψk hv hL2 hν hunit hδ hδ1 hμ hχ hHBmu
  have ha₁ : 0 < Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)) 1 := by
    have := (HB.weights 1 le_rfl (by omega)).1
    exact lt_of_lt_of_le (by norm_num) this
  have hw : C.weights = compWeight S.L (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)) 1) :=
    funext fun r => aIdeal_eq_compWeight hL2 (j + 1) (C.sf.a (j + 1)) r
  have HBc : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1)
      (compWeight S.L (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)) 1)) (sfBgMassAt S.L (j + 1) ν) := by
    rw [← hw, ← hμBg]; exact HB
  have hm : C.geo.c * n (j + 1) * S.L ^ (j + 1 - (j + 1)) = C.geo.c * n (j + 1) := by simp
  have hprec := genSF_precedes (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L)
    (c := C.geo.c) (n := n (j + 1)) hj hm (W2 R (Set.univ : Set (Torus S.d (n (j + 1)))))
  have hδ0 : 0 < 4 * ((S.d : ℝ) + 1) * C.cs.delta (j + 1) := by positivity
  obtain ⟨hreal, hchild⟩ := inPsiTilde_composeField_bgFieldC ha₁ HBc HBc hprec
    (D' := liftSingle (C.genW (Set.univ : Set (Torus S.d (n (j + 1)))))
      (C.liftData ψk) (hC hv)) hδ0 hη hP
    (fun x hx i => liftSingle_Ψ_eq_parentPsi C _ ψk hv hx i)
    (fun x hx i => by rw [liftSingle_h _ _ _ hx]; rfl)
  have hpsi : ∀ x i, psiSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L)
      (c := C.geo.c) (n := n (j + 1)) C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N) hj
      (W2 R (Set.univ : Set (Torus S.d (n (j + 1))))) (C.liftData ψk) (hC hv) x i =
      composeField (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L)
        (c := C.geo.c) (n := n (j + 1)) hj (W2 R (Set.univ : Set (Torus S.d (n (j + 1))))))
        (C.genW (Set.univ : Set (Torus S.d (n (j + 1)))))
        (compWeight S.L (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)) 1))
        (bgFieldC (C.genW (Set.univ : Set (Torus S.d (n (j + 1)))))
          (compWeight S.L (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)) 1))
          (sfBgMassAt S.L (j + 1) ν) (bgC0 S.d S.L N)
          (liftSingle (C.genW (Set.univ : Set (Torus S.d (n (j + 1)))))
            (C.liftData ψk) (hC hv)))
        (liftSingle (C.genW (Set.univ : Set (Torus S.d (n (j + 1)))))
          (C.liftData ψk) (hC hv)).Ψ x i := by
    intro x i
    unfold psiSF bgSF
    rw [hw, hμBg]
  refine ⟨fun x i => ?_, ?_⟩
  · have h3 : psiJRe C ψk hv hj x i = (psiSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1))
        (L := S.L) (c := C.geo.c) (n := n (j + 1)) C.weights (C.cs.muBg (j + 1))
        (bgC0 S.d S.L N) hj (W2 R (Set.univ : Set (Torus S.d (n (j + 1)))))
        (C.liftData ψk) (hC hv) x i).re := rfl
    rw [h3, hpsi x i]
    exact hreal x i
  · refine allSitesBounds_of_inPsiTilde
      (G := genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
        (n := n (j + 1)) hj (W2 R (Set.univ : Set (Torus S.d (n (j + 1))))))
      hj1 hj (fun x => ?_) ?_ ?_
    · rw [genSF_Ω_univ_of_le C hj le_rfl]; exact Finset.mem_univ _
    · exact minLayer_of_gt _ (Nat.lt_succ_self _)
    · convert hchild using 2
      rename_i x
      funext i
      unfold psiJRe psiJReY
      rw [hpsi x i]

/-- The inherited field of a cut on the Def-6 torus is the real part of the composed field, when
the composed field is real. -/
theorem psiJ_eq_ofRealY (Y : Set (Torus S.d (n (j + 1)))) {jj : ℕ}
    (ψk' : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hj : jj ≤ j + 1)
    (hreal : ∀ x i, psiSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
      (n := n (j + 1)) C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N) hj
      (W2 R Y) (C.liftData ψk') (hC hv) x i =
        ((psiJReY C ψk' hv Y hj x i : ℝ) : ℂ)) (x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1))
    (i : Fin N) :
    C.psiJ Y ψk' hv jj x i = ((psiJReY C ψk' hv Y hj (torusCast C.hT x) i : ℝ) : ℂ) := by
  unfold SFCtx.psiJ
  simp only [hj, ↓reduceDIte]
  exact hreal _ i

/-- The inherited field of the Def-6 torus is the real part of the composed field, when the
composed field is real. -/
theorem psiJ_eq_ofReal {jj : ℕ} (ψk' : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))
    (hj : jj ≤ j + 1)
    (hreal : ∀ x i, psiSF (M1 := C.geo.M1) (N₁ := C.geo.c * n (j + 1)) (L := S.L) (c := C.geo.c)
      (n := n (j + 1)) C.weights (C.cs.muBg (j + 1)) (bgC0 S.d S.L N) hj
      (W2 R (Set.univ : Set (Torus S.d (n (j + 1))))) (C.liftData ψk') (hC hv) x i =
        ((psiJRe C ψk' hv hj x i : ℝ) : ℂ)) (x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1))
    (i : Fin N) :
    C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk' hv jj x i =
      ((psiJRe C ψk' hv hj (torusCast C.hT x) i : ℝ) : ℂ) :=
  psiJ_eq_ofRealY C hv Set.univ ψk' hj hreal x i

/-- **A field of the background torus, read on the Def-6 torus, in the analyticity domain of the
terms, from bounds at every site.** For a real field `f` with the bounds of the data domain at every
site (level `j'`, mass `m`, radius `η`), a generating set `𝔹` of the Def-6 torus with empty layers
above `j'`, the standing hypotheses `BgHyp` at a mass `ν_b` with `ν_b L^{2j'} ≤ 4 m L^{2j'}`, and
radii `2 η ≤ min (c₀, c₁)`, `(2 K₁ + 2) · 2 η ≤ ε`: the field `f` read on the Def-6 torus lies in
`Ξ^c_{j'}(𝔹; 1, ε)` at the constant field `h`. -/
theorem xiDom_pull_of_allSites {jj : ℕ} (hjk : jj ≤ j + 1) (hunit : ‖hv‖ = 1) {m η : ℝ}
    (hη : 0 < η) {f : BgT C.geo (j + 1) → Fin N → ℝ}
    (hA : AllSitesBounds (N₀ := C.geo.M1 * (C.geo.c * n (j + 1))) (q := j + 1) jj m η f
      (fun i => hv i))
    {a : ℕ → ℝ} {νb : ℝ} (Hb : BgHyp S.d S.L (j + 1) ϱ a νb)
    (gs : GeneratingSet S.d S.L (C.N₁ * S.L ^ m₁) (j + 1) ϱ) (hΩ : ∀ i, jj < i → gs.Ω i = ∅)
    (hmm : νb * ((S.L : ℝ) ^ jj) ^ 2 ≤ 4 * (m * ((S.L : ℝ) ^ jj) ^ 2)) {ε : ℝ}
    (hc0 : 2 * η ≤ bgC0 S.d S.L N) (hc1 : 2 * η ≤ bgC1 S.d S.L N)
    (hε : (2 * bgK1 S.d S.L N + 2) * (2 * η) ≤ ε) :
    Def6.XiDom gs a νb jj ε (fun x i => ((f (torusCast C.hT x) i : ℝ) : ℂ))
      (Def6.constFld (hC hv)) := by
  have hA2 := hA.weaken hη hmm
  have hNN : C.N₁ * S.L ^ m₁ = C.geo.M1 * (C.geo.c * n (j + 1)) := by
    have hpos : 0 < S.L ^ (j + 1) := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne S.L))
    exact Nat.eq_of_mul_eq_mul_right hpos C.hT
  have hA3 := AllSitesBounds.cast (N₀ := C.N₁ * S.L ^ m₁) hNN C.hT hA2
  exact xiDom_of_allSites (G := gs) Hb hΩ hjk (by linarith) hc0 hc1 hε
    (fun x => f (torusCast C.hT x)) (fun i => hv i)
    ((parent_sum_sq_eq_norm_sq hv).trans (by rw [hunit]; norm_num)) hA3

/-- **The inherited field in the analyticity domain of the terms, on the `χ`-support.** For a
generating set `𝔹` of the Def-6 torus with empty layers above `j'` (the `𝔹_{j'}(X)` of a polymer),
the standing hypotheses `BgHyp` at the birth mass `ν_b` (with `ν_b L^{2j'} ≤ 4 ν L^{-2k} L^{2j'}`)
and radii `2 C₄ K₁ · 4 (d+1) δ_k ≤ min (c₀, c₁)`, `(2 K₁ + 2) · 2 C₄ K₁ · 4 (d+1) δ_k ≤ ε_{j'}`: the
inherited field `ψ^{(j')}_k` of the whole torus lies in `Ξ^c_{j'}(𝔹; 1, ε)`. -/
theorem psiJ_xiDom {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) (hL : 3 ≤ S.L) {ν : ℝ}
    (hν : 0 < ν) (hunit : ‖hv‖ = 1) (hδ : 0 < C.cs.delta (j + 1))
    (hδ1 : (S.d + 1) * C.cs.delta (j + 1) ≤ 1)
    (hμ : C.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (hμBg : C.cs.muBg (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (hχ : C.chiY (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv ≠ 0)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    (hη : 4 * (S.d + 1) * C.cs.delta (j + 1) ≤ thm73C1 S.d S.L N)
    {a : ℕ → ℝ} {νb : ℝ} (Hb : BgHyp S.d S.L (j + 1) ϱ a νb)
    (gs : GeneratingSet S.d S.L (C.N₁ * S.L ^ m₁) (j + 1) ϱ)
    (hΩ : ∀ i, jj < i → gs.Ω i = ∅)
    (hmm : νb * ((S.L : ℝ) ^ jj) ^ 2 ≤ 4 * (sfBgMassAt S.L (j + 1) ν * ((S.L : ℝ) ^ jj) ^ 2))
    {ε : ℝ}
    (hc0 : 2 * (compC4 S.d * (bgK1 S.d S.L N * (4 * (S.d + 1) * C.cs.delta (j + 1)))) ≤
      bgC0 S.d S.L N)
    (hc1 : 2 * (compC4 S.d * (bgK1 S.d S.L N * (4 * (S.d + 1) * C.cs.delta (j + 1)))) ≤
      bgC1 S.d S.L N)
    (hε : (2 * bgK1 S.d S.L N + 2) *
      (2 * (compC4 S.d * (bgK1 S.d S.L N * (4 * (S.d + 1) * C.cs.delta (j + 1))))) ≤ ε) :
    Def6.XiDom gs a νb jj ε (C.psiJ Set.univ ψk hv jj) (Def6.constFld (hC hv)) := by
  obtain ⟨hreal, hA⟩ := psiJ_allSites C ψk hv hj1 hj hL hν hunit hδ hδ1 hμ hμBg hχ HB hη
  have hd : 0 < S.d := by have := Hb.hd; omega
  have hK1 := bgK1_ge_one S.d S.L N
  have hC4 := compC4_ge S.d
  have hηc : 0 < compC4 S.d * (bgK1 S.d S.L N * (4 * (S.d + 1) * C.cs.delta (j + 1))) := by
    have : (0 : ℝ) < S.d := by exact_mod_cast hd
    positivity
  have hxi := xiDom_pull_of_allSites C hv hj hunit hηc hA Hb gs hΩ hmm hc0 hc1 hε
  have hpsi : C.psiJ Set.univ ψk hv jj = fun x i => ((psiJRe C ψk hv hj (torusCast C.hT x) i : ℝ) : ℂ) := by
    funext x i
    exact psiJ_eq_ofReal C hv ψk hj hreal x i
  rw [hpsi]
  exact hxi

/-- **The level-`k` lift of `ψ_k` in the analyticity domain of the terms `ℛ^{(k)}_n`, on the
`χ`-support.** For a generating set with empty layers above `j + 1`, standing hypotheses `BgHyp` at a
mass `ν_R` with `ν_R L^{2(j+1)} ≤ 4 ν L^{-2(j+1)} L^{2(j+1)}`, and radius `2 · 4 (d+1) δ_k` below
`min (c₀, c₁)` and `(2 K₁ + 2)` times it at most `ε`: the lift `sfLiftK ψ_k` of the block field to the
Def-6 torus lies in `Ξ^c_{j+1}(𝔹; 1, ε)`. -/
theorem sfLiftK_xiDom (hL : 3 ≤ S.L) {ν : ℝ}
    (hν : 0 < ν) (hunit : ‖hv‖ = 1) (hδ : 0 < C.cs.delta (j + 1))
    (hδ1 : (S.d + 1) * C.cs.delta (j + 1) ≤ 1)
    (hμ : C.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (hμBg : C.cs.muBg (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (hχ : C.chiY (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv ≠ 0)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    {a : ℕ → ℝ} {νR : ℝ} (Hb : BgHyp S.d S.L (j + 1) ϱ a νR)
    (gs : GeneratingSet S.d S.L (C.N₁ * S.L ^ m₁) (j + 1) ϱ)
    (hΩ : ∀ i, j + 1 < i → gs.Ω i = ∅)
    (hmm : νR * ((S.L : ℝ) ^ (j + 1)) ^ 2 ≤
      4 * (sfBgMassAt S.L (j + 1) ν * ((S.L : ℝ) ^ (j + 1)) ^ 2))
    {ε : ℝ}
    (hc0 : 2 * (4 * (S.d + 1) * C.cs.delta (j + 1)) ≤ bgC0 S.d S.L N)
    (hc1 : 2 * (4 * (S.d + 1) * C.cs.delta (j + 1)) ≤ bgC1 S.d S.L N)
    (hε : (2 * bgK1 S.d S.L N + 2) * (2 * (4 * (S.d + 1) * C.cs.delta (j + 1))) ≤ ε) :
    Def6.XiDom gs a νR (j + 1) ε (sfLiftK C.geo C.hnn C.hkK C.hT ψk) (Def6.constFld (hC hv)) := by
  have hL2 : 2 ≤ S.L := by omega
  have hHBmu : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.mu (j + 1)) := by
    rw [hμ, ← hμBg]; exact HB
  have hP := inPsiTilde_genW_univ_late C ψk hv hL2 hν hunit hδ hδ1 hμ hχ hHBmu
  have hA := allSitesBounds_of_inPsiTilde (G := C.genW (Set.univ : Set (Torus S.d (n (j + 1)))))
    (jj := j + 1) (by omega) le_rfl (fun x => by
      rw [genW_Ω_univ_of_le C le_rfl]; exact Finset.mem_univ _)
    (C.genW (Set.univ : Set (Torus S.d (n (j + 1))))).top hP
  have hηpos : 0 < 4 * ((S.d : ℝ) + 1) * C.cs.delta (j + 1) := by positivity
  have hxi := xiDom_pull_of_allSites C hv le_rfl hunit hηpos hA Hb gs hΩ hmm hc0 hc1 hε
  have hlift : sfLiftK C.geo C.hnn C.hkK C.hT ψk =
      fun x i => ((parentPsi C ψk (torusCast C.hT x) i : ℝ) : ℂ) := by
    funext x i
    unfold sfLiftK parentPsi sfToBg
    rw [jBlock_bgToFine C]
  rw [hlift]
  exact hxi

end Ctx

end Balaban.RootFSpine
