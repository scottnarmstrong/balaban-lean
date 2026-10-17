/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftDomOp

/-!
# The background fields on a transported generating set

The real background field `bgField`, its multiplier, and the complex small-solution field and
multiplier are defined by unique existence of a minimizer, respectively of a small solution.  Both
problems on `liftOldGS G` are in bijection with those on `G`, so the fields agree under the
relabeling `oldTorusEquiv`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Matrix Balaban Balaban.Localization Balaban.Multiscale Balaban.Background

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem existsUnique_congr_equiv {X Y : Type*} (Φ : X ≃ Y) {P : X → Prop} {Q : Y → Prop}
    (h : ∀ x, Q (Φ x) ↔ P x) : (∃! y, Q y) ↔ ∃! x, P x := by
  constructor
  · rintro ⟨y, hy, huniq⟩
    refine ⟨Φ.symm y, (h _).1 (by simpa using hy), fun x hx => ?_⟩
    have := huniq (Φ x) ((h x).2 hx)
    simp [← this]
  · rintro ⟨x, hx, huniq⟩
    refine ⟨Φ x, (h x).2 hx, fun y hy => ?_⟩
    have := huniq (Φ.symm y) ((h _).1 (by simpa using hy))
    simp [← this]

theorem choose_eq_equiv {X Y : Type*} (Φ : X ≃ Y) {P : X → Prop} {Q : Y → Prop}
    (h : ∀ x, Q (Φ x) ↔ P x) (H : ∃! x, P x) (H' : ∃! y, Q y) :
    H'.exists.choose = Φ H.exists.choose :=
  H'.unique H'.exists.choose_spec ((h _).2 H.exists.choose_spec)

section
variable {G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ}
  (e : G.Ω 1 ≃ (liftOldGS G).Ω 1)
  (he : ∀ x, (e x : CTorus d L N₁ m₁ (k + 1)) = oldTorusEquiv x)

include he

theorem liftOldGS_bgField (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (D' : BgData (liftOldGS G) N)
    (hΨ : ∀ x, D'.Ψ (oldTorusEquiv x) = D.Ψ x) (hh : ∀ x, D'.h (oldTorusEquiv x) = D.h x)
    (x : G.Ω 1) (i : Fin N) :
    bgField (liftOldGS G) a ν D' (e x, i) = bgField G a ν D (x, i) := by
  classical
  let Φ : (G.Ω 1 × Fin N → ℂ) ≃ ((liftOldGS G).Ω 1 × Fin N → ℂ) :=
    Equiv.arrowCongr (e.prodCongr (Equiv.refl (Fin N))) (Equiv.refl ℂ)
  have hΦ : ∀ φ x i, Φ φ (e x, i) = φ (x, i) := by intro φ x i; simp [Φ]
  have h : ∀ φ, IsMinimizer (liftOldGS G) a ν D' (Φ φ) ↔ IsMinimizer G a ν D φ :=
    fun φ => liftOldGS_isMinimizer_iff e he a ν D D' hΨ hh (hΦ φ)
  by_cases H : ∃! φ, IsMinimizer G a ν D φ
  · have H' := (existsUnique_congr_equiv Φ h).2 H
    simp only [bgField, H, H', dite_true]
    rw [choose_eq_equiv Φ h H H', hΦ]
  · have H' : ¬ ∃! φ, IsMinimizer (liftOldGS G) a ν D' φ := fun H'' =>
      H ((existsUnique_congr_equiv Φ h).1 H'')
    simp [bgField, H, H']

theorem liftOldGS_bgMult (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (D' : BgData (liftOldGS G) N)
    (hΨ : ∀ x, D'.Ψ (oldTorusEquiv x) = D.Ψ x) (hh : ∀ x, D'.h (oldTorusEquiv x) = D.h x)
    (x : G.Ω 1) :
    bgMult (liftOldGS G) a ν D' (e x) = bgMult G a ν D x := by
  have hφ := liftOldGS_bgField e he a ν D D' hΨ hh
  unfold bgMult
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hφ, Pi.sub_apply, Pi.sub_apply,
    liftOldGS_liftOp_mulVec e he a ν (α := 0) (α' := 0) (fun _ => rfl) hφ,
    liftOldGS_source e he a ν D D' hΨ hh]

theorem liftOldGS_bgFieldC (a : ℕ → ℝ) (ν c₀ : ℝ) (D : BgData G N) (D' : BgData (liftOldGS G) N)
    (hΨ : ∀ x, D'.Ψ (oldTorusEquiv x) = D.Ψ x) (hh : ∀ x, D'.h (oldTorusEquiv x) = D.h x)
    (x : G.Ω 1) (i : Fin N) :
    bgFieldC (liftOldGS G) a ν c₀ D' (e x, i) = bgFieldC G a ν c₀ D (x, i) := by
  classical
  let Φ : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) ≃
      ((liftOldGS G).Ω 1 × Fin N → ℂ) × ((liftOldGS G).Ω 1 → ℂ) :=
    Equiv.prodCongr (Equiv.arrowCongr (e.prodCongr (Equiv.refl (Fin N))) (Equiv.refl ℂ))
      (Equiv.arrowCongr e (Equiv.refl ℂ))
  have hΦ : ∀ s x i, (Φ s).1 (e x, i) = s.1 (x, i) := by intro s x i; simp [Φ]
  have hΦ' : ∀ s x, (Φ s).2 (e x) = s.2 x := by intro s x; simp [Φ]
  have h : ∀ s, IsSmallSolution (liftOldGS G) a ν c₀ D' (Φ s).1 (Φ s).2 ↔
      IsSmallSolution G a ν c₀ D s.1 s.2 :=
    fun s => liftOldGS_isSmallSolution_iff e he a ν c₀ D D' hΨ hh (hΦ s) (hΦ' s)
  by_cases H : ∃! s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsSmallSolution G a ν c₀ D s.1 s.2
  · have H' := (existsUnique_congr_equiv Φ (Q := fun s => IsSmallSolution (liftOldGS G) a ν c₀ D' s.1 s.2) h).2 H
    simp only [bgFieldC, H, H', dite_true]
    rw [choose_eq_equiv Φ h H H', hΦ]
  · have H' : ¬ ∃! s : ((liftOldGS G).Ω 1 × Fin N → ℂ) × ((liftOldGS G).Ω 1 → ℂ),
        IsSmallSolution (liftOldGS G) a ν c₀ D' s.1 s.2 := fun H'' =>
      H ((existsUnique_congr_equiv Φ (Q := fun s => IsSmallSolution (liftOldGS G) a ν c₀ D' s.1 s.2) h).1 H'')
    simp [bgFieldC, H, H']

theorem liftOldGS_bgMultC (a : ℕ → ℝ) (ν c₀ : ℝ) (D : BgData G N) (D' : BgData (liftOldGS G) N)
    (hΨ : ∀ x, D'.Ψ (oldTorusEquiv x) = D.Ψ x) (hh : ∀ x, D'.h (oldTorusEquiv x) = D.h x)
    (x : G.Ω 1) :
    bgMultC (liftOldGS G) a ν c₀ D' (e x) = bgMultC G a ν c₀ D x := by
  classical
  let Φ : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) ≃
      ((liftOldGS G).Ω 1 × Fin N → ℂ) × ((liftOldGS G).Ω 1 → ℂ) :=
    Equiv.prodCongr (Equiv.arrowCongr (e.prodCongr (Equiv.refl (Fin N))) (Equiv.refl ℂ))
      (Equiv.arrowCongr e (Equiv.refl ℂ))
  have hΦ : ∀ s x i, (Φ s).1 (e x, i) = s.1 (x, i) := by intro s x i; simp [Φ]
  have hΦ' : ∀ s x, (Φ s).2 (e x) = s.2 x := by intro s x; simp [Φ]
  have h : ∀ s, IsSmallSolution (liftOldGS G) a ν c₀ D' (Φ s).1 (Φ s).2 ↔
      IsSmallSolution G a ν c₀ D s.1 s.2 :=
    fun s => liftOldGS_isSmallSolution_iff e he a ν c₀ D D' hΨ hh (hΦ s) (hΦ' s)
  by_cases H : ∃! s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsSmallSolution G a ν c₀ D s.1 s.2
  · have H' := (existsUnique_congr_equiv Φ (Q := fun s => IsSmallSolution (liftOldGS G) a ν c₀ D' s.1 s.2) h).2 H
    simp only [bgMultC, H, H', dite_true]
    rw [choose_eq_equiv Φ h H H', hΦ']
  · have H' : ¬ ∃! s : ((liftOldGS G).Ω 1 × Fin N → ℂ) × ((liftOldGS G).Ω 1 → ℂ),
        IsSmallSolution (liftOldGS G) a ν c₀ D' s.1 s.2 := fun H'' =>
      H ((existsUnique_congr_equiv Φ (Q := fun s => IsSmallSolution (liftOldGS G) a ν c₀ D' s.1 s.2) h).1 H'')
    simp [bgMultC, H, H']

end

end Balaban.Fluctuation
