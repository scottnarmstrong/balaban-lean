module

public import Balaban.Fluctuation.ExpansionQuad
public import Balaban.Fluctuation.ExpansionNuFree
import Mathlib.Tactic.Linarith

/-!
# Lemma 2.3 (a) for real data

The identities of `Expansion*` use the bilinear product `u * v` (complex data, as in the proof of
FLUCTUATION Lemma 2.3 (a)); for real data they are identities of real numbers:
`couplingC_ofReal`, `Jbg_eq_bilinear` (`J_k` of `CriticalPoint` with the real action is the value of
the bilinear `J_k`), `expansion_chord_real`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Finset Matrix

section Real

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'} {a₁ ν : ℝ} {n : ℕ}

/-- For real fields the bilinear coupling is the real coupling. -/
theorem couplingC_ofReal (G' : GeneratingSet d L N₀ K ϱ') (a₁ : ℝ) (p : ℕ)
    (θ Ψ : Torus d (N₀ * L ^ K) → Fin N → ℂ) (hθ : ∀ x i, (θ x i).im = 0)
    (hΨ : ∀ x i, (Ψ x i).im = 0) :
    couplingC G' a₁ p θ Ψ = ((coupling G' a₁ p θ Ψ : ℝ) : ℂ) := by
  unfold couplingC coupling
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  have him : (θ x i - blockMean G' p (fun y => Ψ y i) x).im = 0 := by
    rw [Complex.sub_im, hθ x i, blockMean_im_zero (fun y => Ψ y i) x (fun y => hΨ y i)]
    simp
  have := Complex.mul_conj (θ x i - blockMean G' p (fun y => Ψ y i) x)
  rw [Complex.conj_eq_iff_im.2 him, Complex.normSq_eq_norm_sq] at this
  push_cast at this
  exact this

/-- `J_k` with the background field is the real part (the value) of the bilinear `J_k`. -/
theorem Jbg_eq_bilinear (H : BgHyp d L K ϱ (compWeight L a₁) ν) (D : BgData G N)
    (hD : InUnionDomainR G (bgC1 d L N) ν D) (θ : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (hθ : ∀ x i, (θ x i).im = 0) :
    ((Jbg G G' (compWeight L a₁) a₁ ν n θ D : ℝ) : ℂ) =
      couplingC G' a₁ (n + 1) θ D.Ψ +
        actionC G (compWeight L a₁) ν D (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D) := by
  obtain ⟨-, hunit, -, -⟩ := theorem71 H hD
  have hreal := isReal_of_inDomainR hD.choose_spec.2.2
  rw [(theorem72_real H hD).1]
  unfold Jbg
  push_cast
  rw [couplingC_ofReal G' a₁ (n + 1) θ D.Ψ hθ (fun x i => (hreal x i).1),
    action_cast D hreal (fun x i => (hunit x).1 i)]

/-- **The chord identity (2.3) for real data**: `J_k(θ, ψ)` of the real action equals the bilinear
right-hand side (all quantities real for real data). -/
theorem expansion_chord_real (ha₁ : 0 < a₁) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (H : BgHyp d L K ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L K ϱ' (compWeight L a₁) ν) (D' : BgData G' N)
    (hD' : InUnionDomainC G' (bgC0 d L N) (thm73C1 d L N) ν D') (hD'R : D'.IsReal)
    (D : BgData G N) (hh : ∀ x i, D.h x i = D'.h x i)
    (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D)
    (hDR : InUnionDomainR G (bgC1 d L N) ν D) :
    ((Jbg G G' (compWeight L a₁) a₁ ν n D'.Ψ D : ℝ) : ℂ) =
      actionC G' (compWeight L a₁) ν D' (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') +
        couplingC G' a₁ (n + 1) (fun _ _ => 0) (compTangent hG hG' hp (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D) +
        levelEnergyC G (compWeight L a₁) n (compTangent hG hG' hp (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D)
          (svec G (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D -
            (hG.precedes hG' hp).restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D'))) +
        (1 / 2) * hessForm G' ν (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (svec G (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D -
            (hG.precedes hG' hp).restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D'))) := by
  rw [Jbg_eq_bilinear (G' := G') (n := n) H D hDR D'.Ψ (fun x i => (hD'R x i).1)]
  exact expansion_chord ha₁ hG hG' hp H H' D' hD' D hh hD

end Real

end Balaban.Fluctuation
