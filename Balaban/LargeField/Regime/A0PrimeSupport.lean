module

public import Balaban.LargeField.Operators.QuietSymm
public import Balaban.LargeField.Def7SmallField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The massless sharp supports do not see the source (route R-YM, leaf `support_h_free_below_k0`)

In the hybrid convention A0' the sharp large-field indicators of scales `j ≤ k₀` are massless
(`μ = 0`, and `νk = 0` in the mixed test), so the field `h` enters neither the regularity
predicate nor the characteristic functions, provided the datum `h` is a constant real vector on
`Ω₁` (the typing data of `InDomainR`).

* `reg_zero_mass_h_free`: `Reg G a 0 D δ T S ↔ Reg G a 0 D' δ T S` when `D.Ψ = D'.Ψ` and both
  `h`-fields are constant real vectors on `Ω₁`.
* `chiK_zero_mass_h_free`, `chiPrimeNew_zero_mass_h_free`, `chiY_zero_mass_h_free`: the
  characteristic functions `χ_k(□)`, `χ'_{k+1}(□')`, `χ_k(Y)` at mass zero do not depend on `h`.
* `chiK_zero_mass_rot_fixed_h`, `chiPrimeNew_zero_mass_rot_fixed_h`: the symmetry S5(i):
  invariance under `Ψ ↦ RΨ` with `h` fixed (the landed joint covariance `chiK_rot` combined
  with `h`-freedom).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Matrix

section Reg0

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ q ϱ)
  (a : ℕ → ℝ)

theorem source_zero_congr {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ) :
    source G a 0 D = source G a 0 D' := by
  funext p
  simp [source, hΨ]

theorem isSmallSolution_zero_congr {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ) (c₀ : ℝ) :
    IsSmallSolution G a 0 c₀ D = IsSmallSolution G a 0 c₀ D' := by
  funext φ α
  simp only [IsSmallSolution, IsEL, source_zero_congr G a hΨ]

/-- Both background objects of `Def5` depend on `D` only through the small-solution predicate. -/
theorem bgPair_zero_congr {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ) (c₀ : ℝ) :
    bgFieldC G a 0 c₀ D = bgFieldC G a 0 c₀ D' ∧ bgMultC G a 0 c₀ D = bgMultC G a 0 c₀ D' := by
  classical
  have hp := isSmallSolution_zero_congr G a hΨ c₀
  have hiff : (∃! s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsSmallSolution G a 0 c₀ D s.1 s.2) ↔
      (∃! s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsSmallSolution G a 0 c₀ D' s.1 s.2) := by
    rw [hp]
  unfold bgFieldC bgMultC
  by_cases H : ∃! s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsSmallSolution G a 0 c₀ D s.1 s.2
  · have H' := hiff.1 H
    have hs : H.exists.choose = H'.exists.choose := by
      refine H'.unique ?_ H'.exists.choose_spec
      have h2 : IsSmallSolution G a 0 c₀ D H.exists.choose.1 H.exists.choose.2 :=
        H.exists.choose_spec
      exact (congrFun (congrFun hp _) _).mp h2
    simp only [H, H', dite_true, hs, and_self]
  · have H' : ¬ (∃! s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
        IsSmallSolution G a 0 c₀ D' s.1 s.2) := fun h => H (hiff.2 h)
    simp only [H, H', dite_false, and_self]

theorem bgFieldC_zero_congr {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ) (c₀ : ℝ) :
    bgFieldC G a 0 c₀ D = bgFieldC G a 0 c₀ D' := (bgPair_zero_congr G a hΨ c₀).1

theorem bgMultC_zero_congr {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ) (c₀ : ℝ) :
    bgMultC G a 0 c₀ D = bgMultC G a 0 c₀ D' := (bgPair_zero_congr G a hΨ c₀).2

theorem inUnionDomainR_zero_h_free {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ) (c₁ : ℝ)
    (hD' : ∃ h : Fin N → ℝ, ∀ x ∈ G.Ω 1, ∀ i, D'.h x i = (h i : ℂ)) :
    InUnionDomainR G c₁ 0 D → InUnionDomainR G c₁ 0 D' := by
  rintro ⟨δ, hδ, hc, Ψ, h, hpsi, hΨx, _⟩
  obtain ⟨h', hh'⟩ := hD'
  refine ⟨δ, hδ, hc, Ψ, h', ⟨hpsi.layerConst, hpsi.r1, hpsi.r2, ?_, ?_⟩, ?_, hh'⟩
  · intro x _; simp only [zero_mul]; positivity
  · simp only [zero_mul]; positivity
  · intro x hx i; rw [← hΨ]; exact hΨx x hx i

theorem inUnionDomainR_zero_h_free_iff {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ) (c₁ : ℝ)
    (hD : ∃ h : Fin N → ℝ, ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h i : ℂ))
    (hD' : ∃ h : Fin N → ℝ, ∀ x ∈ G.Ω 1, ∀ i, D'.h x i = (h i : ℂ)) :
    InUnionDomainR G c₁ 0 D ↔ InUnionDomainR G c₁ 0 D' :=
  ⟨inUnionDomainR_zero_h_free G hΨ c₁ hD', inUnionDomainR_zero_h_free G hΨ.symm c₁ hD⟩

theorem blockClose_h_free {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ) (φ : G.Ω 1 × Fin N → ℂ)
    (T : Finset (Torus d (N₀ * L ^ q))) (δ : ℝ) :
    BlockClose G D φ T δ ↔ BlockClose G D' φ T δ := by
  simp only [BlockClose, blockDev, hΨ]

theorem barVec_h_free {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ) (φ : G.Ω 1 × Fin N → ℂ) :
    barVec G D φ = barVec G D' φ := by
  funext x; unfold barVec; rw [hΨ]

theorem gradClose_h_free {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ) (φ : G.Ω 1 × Fin N → ℂ)
    (α : G.Ω 1 → ℂ) (ℓ : ℝ) (S : Finset (Torus d (N₀ * L ^ q))) (δ : ℝ) :
    GradClose G D φ α ℓ S δ ↔ GradClose G D' φ α ℓ S δ := by
  simp only [GradClose, barLap, barVec_h_free G hΨ]

theorem fieldClose_zero (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (ν : ℝ) (hν : ¬ 0 < ν)
    (S : Finset (Torus d (N₀ * L ^ q))) (δ : ℝ) : FieldClose G D φ ν S δ :=
  fun h => absurd h hν

/-- At mass zero the regularity predicate does not depend on `h`. -/
theorem reg_zero_mass_h_free {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ)
    (hD : ∃ h : Fin N → ℝ, ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h i : ℂ))
    (hD' : ∃ h : Fin N → ℝ, ∀ x ∈ G.Ω 1, ∀ i, D'.h x i = (h i : ℂ)) (δ : ℝ)
    (T S : Finset (Torus d (N₀ * L ^ q))) :
    Reg G a 0 D δ T S ↔ Reg G a 0 D' δ T S := by
  unfold Reg RegIneq
  rw [bgFieldC_zero_congr G a hΨ, bgMultC_zero_congr G a hΨ,
    inUnionDomainR_zero_h_free_iff G hΨ _ hD hD', blockClose_h_free G hΨ,
    gradClose_h_free G hΨ]
  have hF : ∀ (D : BgData G N) φ S δ, FieldClose G D φ 0 S δ :=
    fun D φ S δ => fieldClose_zero G D φ 0 (lt_irrefl 0) S δ
  simp only [zero_mul, hF, and_true]

/-- The mixed predicate at mass zero and `νk = 0`. -/
theorem regMixedIneq_zero_mass_h_free {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ) (ℓ δ : ℝ)
    (Tfar Tnear S : Finset (Torus d (N₀ * L ^ q))) :
    RegMixedIneq G a 0 D ℓ 0 δ Tfar Tnear S ↔ RegMixedIneq G a 0 D' ℓ 0 δ Tfar Tnear S := by
  unfold RegMixedIneq
  rw [bgFieldC_zero_congr G a hΨ, bgMultC_zero_congr G a hΨ, blockClose_h_free G hΨ,
    blockClose_h_free G hΨ, gradClose_h_free G hΨ]
  have hF : ∀ (D : BgData G N) φ S δ, FieldClose G D φ 0 S δ :=
    fun D φ S δ => fieldClose_zero G D φ 0 (lt_irrefl 0) S δ
  simp only [hF, and_true]

end Reg0

section Chi0

variable {d M1 N₁ L N : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

/-- `χ_q(□)` at mass zero does not depend on `h`. -/
theorem chiK_zero_mass_h_free {q : ℕ} (a : ℕ → ℝ) (δ : ℝ) (c n : ℕ) (y0 : Torus d n)
    (h h' : Fin N → ℝ) :
    chiK (M1 := M1) (N₁ := N₁) (L := L) (q := q) a 0 δ h c n y0 =
      chiK (M1 := M1) (N₁ := N₁) (L := L) (q := q) a 0 δ h' c n y0 := by
  funext ψ
  unfold chiK
  refine charFn_congr_apply ?_
  unfold ChiKProp
  have hΨ : (cubeData (M1 := M1) (N₁ := N₁) (L := L) (q := q) h c n y0 ψ).Ψ =
      (cubeData (M1 := M1) (N₁ := N₁) (L := L) (q := q) h' c n y0 ψ).Ψ := rfl
  exact reg_zero_mass_h_free _ a hΨ
    ⟨h, fun x hx i => by unfold cubeData; rw [liftSingle_h _ _ _ hx]⟩
    ⟨h', fun x hx i => by unfold cubeData; rw [liftSingle_h _ _ _ hx]⟩ _ _ _

/-- `χ'_{k+1}(□')` at mass zero and `νk = 0` does not depend on `h`. -/
theorem chiPrimeNew_zero_mass_h_free {k : ℕ} (a : ℕ → ℝ) (δ : ℝ) {c n : ℕ}
    (hm : N₁ * L ^ (k + 1 - (k + 1)) = c * n) (y0 : Torus d n)
    (Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1))))
    (hOm : IsBlockUnion L (M1 * N₁) (k + 1) (k + 1) Om) (h h' : Fin N → ℝ) :
    chiPrimeNew a 0 δ 0 h hm y0 Om hOm = chiPrimeNew a 0 δ 0 h' hm y0 Om hOm := by
  funext p
  unfold chiPrimeNew
  refine charFn_congr_apply ?_
  have hΨ : (mixedData h hm y0 Om hOm p.1 p.2).Ψ = (mixedData h' hm y0 Om hOm p.1 p.2).Ψ := rfl
  have key := inUnionDomainR_zero_h_free_iff (genCubeMixed hm y0 Om hOm) hΨ (bgC1 d L N)
    ⟨h, fun x hx i => by unfold mixedData; rw [liftMixed_h _ _ _ _ _ _ hx]⟩
    ⟨h', fun x hx i => by unfold mixedData; rw [liftMixed_h _ _ _ _ _ _ hx]⟩
  have key2 := regMixedIneq_zero_mass_h_free (genCubeMixed hm y0 Om hOm) a hΨ ((L : ℝ) ^ k) δ
    (cubeNbhd M1 N₁ L (k + 1) c n 1 y0 \ Om) (cubeNbhd M1 N₁ L (k + 1) c n 1 y0 ∩ Om)
    (cubeNbhd M1 N₁ L (k + 1) c n 1 y0)
  unfold ChiPrimeNewProp
  rw [key, key2]

/-- **S5(i) for `χ_q(□)`** at mass zero: invariance under `ψ ↦ Q ψ` with `h` fixed. -/
theorem chiK_zero_mass_rot_fixed_h {q : ℕ} (a : ℕ → ℝ) (δ : ℝ) (c n : ℕ) (y0 : Torus d n)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (h : Fin N → ℝ)
    (ψ : BlockCfg d (M1 * N₁) L q q N) :
    chiK (M1 := M1) (N₁ := N₁) (L := L) a 0 δ h c n y0 (rotBC Q ψ) =
      chiK (M1 := M1) (N₁ := N₁) (L := L) a 0 δ h c n y0 ψ := by
  exact (congrFun (chiK_zero_mass_h_free a δ c n y0 h (Q *ᵥ h)) _).trans
    (chiK_rot a 0 δ c n y0 hQ h ψ)

/-- **S5(i) for `χ'_{k+1}(□')`** at mass zero and `νk = 0`. -/
theorem chiPrimeNew_zero_mass_rot_fixed_h {k : ℕ} (a : ℕ → ℝ) (δ : ℝ) {c n : ℕ}
    (hm : N₁ * L ^ (k + 1 - (k + 1)) = c * n) (y0 : Torus d n)
    (Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1))))
    (hOm : IsBlockUnion L (M1 * N₁) (k + 1) (k + 1) Om)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (h : Fin N → ℝ)
    (ψ : BlockCfg d (M1 * N₁) L (k + 1) k N) (θ : BlockCfg d (M1 * N₁) L (k + 1) (k + 1) N) :
    chiPrimeNew a 0 δ 0 h hm y0 Om hOm (rotBC Q ψ, rotBC Q θ) =
      chiPrimeNew a 0 δ 0 h hm y0 Om hOm (ψ, θ) := by
  exact (congrFun (chiPrimeNew_zero_mass_h_free a δ hm y0 Om hOm h (Q *ᵥ h)) _).trans
    (chiPrimeNew_rot a 0 δ 0 hm y0 Om hOm hQ h ψ θ)

end Chi0

end Balaban.LargeField

namespace Balaban.LargeField.Def7.SFCtx

open Balaban Balaban.Multiscale Balaban.Background

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (Y : Set (Torus S.d (n k))) (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))

/-- **`χ_k(Y)` at mass zero does not depend on the source `h`** (scales `j ≤ k₀`, A0'). -/
theorem chiY_zero_mass_h_free (hmu : C.cs.mu k = 0) (hv hv' : EuclideanSpace ℝ (Fin N)) :
    C.chiY Y ψk hv = C.chiY Y ψk hv' := by
  unfold chiY
  rw [hmu]
  refine Finset.prod_congr rfl fun y _ => ?_
  exact congrFun (chiK_zero_mass_h_free (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L)
    (q := k) C.weights (C.cs.delta k) C.geo.c (n k) y (fun i => hv i) (fun i => hv' i)) _

end Balaban.LargeField.Def7.SFCtx
