/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RenFibreDatum

/-!
# The fibre domain of the renormalization record, restated on the first domain

Every datum `D : BgData G N` has external field zero off `G.Ω 1`.  The predicate
`∀ x i, D.h x i = h₀ i` is therefore empty when `G.Ω 1` is a proper subset and `h₀ ≠ 0`.  The
corrected fibre domain asks `D.h = h₀` on `G.Ω 1` only.

* `RenDom`: the class `XiCOneReal` together with `D.h x = h₀` on `G.Ω 1`;
* `renDom_iff_clip`, `renDom_iff_of_forall_mem`: the clipped equality, and the old predicate when
  `G.Ω 1` is the whole torus;
* `renormExpInputOn_renDom`: the restriction of the renormalization record to `RenDom`;
* `exists_renDom`: a datum in `RenDom` without the hypothesis that `G.Ω 1` is everything;
* `nonempty_renormExpInputOn_renDom_datum`: the record on `RenDom` together with a datum in it;
* `renDom_step`: `RenDom` at every step of the tower.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Inhabited
  Balaban.Localization Balaban.Localization.I5Inhabited Balaban.Inhabited.LevelStep

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The fibre domain over a constant field `h₀`**: the data of the class `Ξ^c_{k+1}(1, e)`
(real part) whose external field equals `h₀` on the first domain `G.Ω 1` (off `G.Ω 1` the field
of a datum is zero). -/
def RenDom (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν e : ℝ) (h₀ : Fin N → ℝ)
    (D : BgData G N) : Prop :=
  XiCOneReal G a ν e D ∧ ∀ x, x ∈ G.Ω 1 → ∀ i, D.h x i = (h₀ i : ℂ)

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν e : ℝ} {h₀ : Fin N → ℝ}
  {D : BgData G N}

theorem RenDom.xi (h : RenDom G a ν e h₀ D) : XiCOneReal G a ν e D := h.1

theorem RenDom.h_eq (h : RenDom G a ν e h₀ D) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (i : Fin N) : D.h x i = (h₀ i : ℂ) := h.2 x hx i

/-- `RenDom` is the class together with the clipped equality `h = 1_{Ω₁} h₀`. -/
theorem renDom_iff_clip :
    RenDom G a ν e h₀ D ↔ XiCOneReal G a ν e D ∧
      ∀ x i, D.h x i = if x ∈ G.Ω 1 then (h₀ i : ℂ) else 0 := by
  refine and_congr_right fun _ => ⟨fun h x i => ?_, fun h x hx i => ?_⟩
  · by_cases hx : x ∈ G.Ω 1
    · simp [hx, h x hx i]
    · simp [hx, congrFun (D.h_zero x hx) i]
  · simpa [hx] using h x i

/-- When `G.Ω 1` is the whole torus, `RenDom` is the old global predicate. -/
theorem renDom_iff_of_forall_mem (hΩ : ∀ x, x ∈ G.Ω 1) :
    RenDom G a ν e h₀ D ↔ XiCOneReal G a ν e D ∧ ∀ x i, D.h x i = (h₀ i : ℂ) :=
  and_congr_right fun _ => ⟨fun h x i => h x (hΩ x) i, fun h x _ i => h x i⟩

/-- **The renormalization record restricts to `RenDom`**, for every real `h₀`. -/
theorem renormExpInputOn_renDom {r₀ cK B : ℝ}
    {F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    {ι : Type*} {blk : ι → Finset (Torus d (N₀ * L ^ k))}
    {Ys : ι → Finset (Finset (Torus d (N₀ * L ^ k)))}
    {YsM : G.Ω 1 × Fin N → Finset (Finset (Torus d (N₀ * L ^ k)))}
    {dY : Finset (Torus d (N₀ * L ^ k)) → ℝ} {κa κb Kloc BE0 Bold BM0 BoldM : ℝ}
    {E0θ oldE : ι → BgData G N → (Fin 3 → ℂ) → ℂ}
    {M0θ oldM : G.Ω 1 × Fin N → BgData G N → (Fin 3 → ℂ) → ℂ}
    (I : RenormExpInput G a ν e r₀ cK B F blk Ys YsM dY κa κb Kloc BE0 Bold BM0 BoldM E0θ oldE
      M0θ oldM) (h₀ : Fin N → ℝ) :
    RenormExpInputOn G a ν e r₀ cK B F blk Ys YsM dY κa κb Kloc BE0 Bold BM0 BoldM E0θ oldE
      M0θ oldM (RenDom G a ν e h₀) :=
  I.toOn fun _ h => h.1

/-- **A datum in `RenDom`, without assuming `G.Ω 1` is the whole torus**: the witness of
`exists_xiCOneReal` (unit field clipped to `G.Ω 1`). -/
theorem exists_renDom {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν)
    (G : GeneratingSet d L N₀ k ϱ) (hN : 0 < N) (hν : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) {ε : ℝ}
    (hε : 0 < ε) : ∃ D : BgData G N, RenDom G a ν ε (unitVec hN) D := by
  refine ⟨complexData G (fun _ => unitVec hN) (unitVec hN) 0 0 (fun _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl), ?_, ?_⟩
  · exact ⟨_, _, 0, exists_xiC H G hN hν hε,
      complexData_realizes (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)
        (fun _ _ _ _ _ _ _ => rfl)⟩
  · intro x hx i
    simp [complexData, BgData.clip, hx]

/-- **The record on `RenDom` together with a datum in it**, without assuming `G.Ω 1` is the whole
torus (hard rule 10 for the corrected fibre domain). -/
theorem nonempty_renormExpInputOn_renDom_datum {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν)
    {ι : Type*} (blk : ι → Finset (Torus d (N₀ * L ^ k))) (κa κb : ℝ) (hN : 0 < N)
    (hν : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) :
    ∃ ε r₀ : ℝ, 0 < ε ∧ 0 < r₀ ∧ ∃ F, IsRenSol (N := N) G a ν ε ε r₀ (8 * ε) F ∧
      RenormExpInputOn G a ν ε r₀ 2 (8 * ε) F blk (fun _ => {Finset.univ})
        (fun _ => {Finset.univ}) (fun _ => 0) κa κb 1 0 0 0 0 (fun _ _ _ => 0) (fun _ _ _ => 0)
        (fun _ _ _ => 0) (fun _ _ _ => 0) (RenDom G a ν ε (unitVec hN)) ∧
      ∃ D : BgData G N, RenDom G a ν ε (unitVec hN) D := by
  obtain ⟨ε, r₀, hε, hr, F, hF, I⟩ := nonempty_renormExpInput (N := N) (G := G) a H blk κa κb
  exact ⟨ε, r₀, hε, hr, F, hF, renormExpInputOn_renDom I (unitVec hN),
    exists_renDom H G hN hν hε⟩

/-- **`RenDom` at every step of the tower**: the step's datum `D'` lies in the fibre domain over
the step's field `h₀`, at every radius `e > 0`. -/
theorem renDom_step {κmin : ℝ} (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (ν β p₁ : ℝ) (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e : ℝ}
    (he : 0 < e) :
    RenDom (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν e
      (T.step k hk N₁ ν β p₁).h₀ (T.step k hk N₁ ν β p₁).D' := by
  obtain ⟨h1, h2⟩ := exists_xiCOneReal_fibre_step T k hk N₁ ν β p₁ hν0 hν he
  exact ⟨h1, fun x _ i => h2 x i⟩

end Balaban.Fluctuation
