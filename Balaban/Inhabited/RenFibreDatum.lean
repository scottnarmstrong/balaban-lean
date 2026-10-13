/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.XiCDomains
public import Balaban.Inhabited.StepTowerScale
public import Balaban.Fluctuation.RenormExpInputOn

/-!
# A datum in the fibre domain of the renormalization record

The fibre domain `{D ∈ Ξ^c_{k+1}(1, ε) real part | h ≡ h₀}` of `RenormExpInputOn` contains the
constant unit datum, so `nonempty_renormExpInputOn_fibre` is not a statement about an empty domain.

* `exists_xiCOneReal_fibre`: the datum of `exists_xiCOneReal` has external field the unit vector;
* `nonempty_renormExpInputOn_fibre_datum`: the record on the fibre domain together with a datum in it;
* `exists_xiCOneReal_fibre_step`: at every scale of the tower, for every radius `e > 0`, the step's
  own datum `D'` lies in the fibre domain of the step.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.I5Inhabited Balaban.Inhabited.LevelStep

/-- **The constant unit datum lies in the fibre over the unit vector.**  Here `G.Ω 1` is the whole
torus, so that the field of the datum is the unit vector at every site. -/
theorem exists_xiCOneReal_fibre {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {a : ℕ → ℝ}
    {ν : ℝ} (H : BgHyp d L k ϱ a ν) (G : GeneratingSet d L N₀ k ϱ) (hN : 0 < N)
    (hν : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) (hΩ : ∀ x, x ∈ G.Ω 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : BgData G N, XiCOneReal G a ν ε D ∧ ∀ x i, D.h x i = ((unitVec hN i : ℝ) : ℂ) := by
  refine ⟨complexData G (fun _ => unitVec hN) (unitVec hN) 0 0 (fun _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl), ?_, ?_⟩
  · exact ⟨_, _, 0, exists_xiC H G hN hν hε,
      complexData_realizes (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)
        (fun _ _ _ _ _ _ _ => rfl)⟩
  · intro x i
    simp [complexData, BgData.clip, hΩ x]

/-- **Hard rule 10 for the fibre record, with a datum.**  The record of
`nonempty_renormExpInputOn_fibre` at `h₀ = e₀`, together with a datum of its fibre domain. -/
theorem nonempty_renormExpInputOn_fibre_datum {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    {a : ℕ → ℝ} {G : GeneratingSet d L N₀ k ϱ} {ν : ℝ} (H : BgHyp d L k ϱ a ν) {ι : Type*}
    (blk : ι → Finset (Torus d (N₀ * L ^ k))) (κa κb : ℝ) (hN : 0 < N)
    (hν : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) (hΩ : ∀ x, x ∈ G.Ω 1) :
    ∃ ε r₀ : ℝ, 0 < ε ∧ 0 < r₀ ∧ ∃ F, IsRenSol (N := N) G a ν ε ε r₀ (8 * ε) F ∧
      RenormExpInputOn G a ν ε r₀ 2 (8 * ε) F blk (fun _ => {Finset.univ})
        (fun _ => {Finset.univ}) (fun _ => 0) κa κb 1 0 0 0 0 (fun _ _ _ => 0) (fun _ _ _ => 0)
        (fun _ _ _ => 0) (fun _ _ _ => 0)
        (fun D => XiCOneReal G a ν ε D ∧ ∀ x i, D.h x i = ((unitVec hN i : ℝ) : ℂ)) ∧
      ∃ D : BgData G N, XiCOneReal G a ν ε D ∧ ∀ x i, D.h x i = ((unitVec hN i : ℝ) : ℂ) := by
  obtain ⟨ε, r₀, hε, hr, F, hF, I⟩ :=
    nonempty_renormExpInputOn_fibre (N := N) (G := G) H blk κa κb (unitVec hN)
  exact ⟨ε, r₀, hε, hr, F, hF, I, exists_xiCOneReal_fibre H G hN hν hΩ hε⟩

/-- **The step's own datum lies in the fibre domain, at every radius `e > 0`.** -/
theorem exists_xiCOneReal_fibre_step {κmin : ℝ} (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (ν β p₁ : ℝ) (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ}
    (he : 0 < e) :
    XiCOneReal (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν e
        (T.step k hk N₁ ν β p₁).D' ∧
      ∀ x i, (T.step k hk N₁ ν β p₁).D'.h x i = (((T.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ) := by
  refine ⟨?_, (T.step k hk N₁ ν β p₁).hh₀⟩
  have hHB := bgHyp_lv (k := k) T.m₁ hν0 hν
  refine ⟨fun _ => unitVec hN2, unitVec hN2, 0,
    exists_xiC hHB (lvTop N₁ T.m₁ k (rhoSep T.m₁)) hN2 (massLe_lv hν) he, ?_, ?_⟩
  · intro x hx i
    have := unitBg_Ψ_of_mem (lvTop N₁ T.m₁ k (rhoSep T.m₁)) hN2 (unitVec hN2) hx i
    show (unitBg (lvTop N₁ T.m₁ k (rhoSep T.m₁)) hN2 (unitVec hN2)).Ψ x i = _
    rw [this]; simp
  · intro x hx i
    have := unitBg_h_of_mem (lvTop N₁ T.m₁ k (rhoSep T.m₁)) hN2 (unitVec hN2) hx i
    show (unitBg (lvTop N₁ T.m₁ k (rhoSep T.m₁)) hN2 (unitVec hN2)).h x i = _
    rw [this]; simp

end Balaban.Inhabited
