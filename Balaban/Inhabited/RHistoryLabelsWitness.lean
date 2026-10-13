/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RipeHistory
public import Balaban.LargeField.R.RHistoryLabels

/-!
# A non-trivial fibre of the `R`-enumeration (VMOD-37 package 5, T6)

On the landed history `RipeHist.histT` (one large-field cube, one ripe component of `Z^pre_T` at
the scale `k = T = k₀`, nothing removed) the five kept labels give five distinct scale-`T`
outcome assignments with the `(T,T)`-record of the history, so the fibre of the forgetful map
`(T,T+1)`-records `→` `(T,T)`-records over it has at least five elements
(`ripe_fibre_card_ge`).  The removed outcome is not realized by a landed history here (the
landed witnesses all have `Rem = ∅`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RipeHist

variable {S : Setting} [NeZero S.L] (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
  (hRb : (4 * S.L + 20 : ℝ) ≤ S.Rb) (N : ℕ) [NeZero N]

/-- The labelled history over `histT` (all labels `0`). -/
noncomputable def ripeLab : LabHist S (side S N (Tstar S)) JointWitness.radii (Tstar S) (Tstar S)
    where
  H := histT ok h4 h5 hRb N
  adm := fun k c hc => by
    exact absurd hc (by simp [histT, hist])
  lab := fun _ _ => 0

include ok h4 h5 hRb in
open Classical in
/-- **A non-trivial instance**: there are a history `A` with a ripe scale-`T` component `c`, sets
`𝔄` complete at `(T,T)` and `𝔄'` complete at `(T,T+1)` with the projection `projTo`, such that
the representative of `A` has at least five preimages in `𝔄'`. -/
theorem ripe_fibre_card_ge :
    ∃ (A : LabHist S (side S N (Tstar S)) JointWitness.radii (Tstar S) (Tstar S))
      (𝔄 𝔄' : Finset (LabHist S (side S N (Tstar S)) JointWitness.radii (Tstar S) (Tstar S))),
      IsComplete (Tstar S) (Tstar S) 𝔄 ∧ IsComplete (Tstar S) (Tstar S + 1) 𝔄' ∧
      (∃ c : A.H.Comp (Tstar S), IsKept A.H (Tstar S) c) ∧
      ∃ A₀ ∈ 𝔄, A.Agree (Tstar S) (Tstar S) A₀ ∧
        5 ≤ (𝔄'.filter fun B => projTo (Tstar S) 𝔄 B = A₀).card := by
  classical
  set A := ripeLab ok h4 h5 hRb N with hA
  obtain ⟨c, -, hrip⟩ := exists_ripe ok h4 h5 hRb N
  have hkept : IsKept A.H (Tstar S) c := ⟨one_le_Tstar S, le_rfl, hrip⟩
  obtain ⟨𝔄, h𝔄⟩ := exists_isComplete (S := S) (n := side S N (Tstar S))
    (R := JointWitness.radii) (k0 := Tstar S) (K := Tstar S) (Tstar S) (Tstar S)
  obtain ⟨𝔄', h𝔄', -, -, hbij⟩ := exists_enum h𝔄
  obtain ⟨A₀, ⟨hA₀, hAA₀⟩, -⟩ := h𝔄 A
  -- the outcome of `A` at `c` is a kept one
  have hout : A.outcomeAt (Tstar S) c.1 = some (Outcome.kept 0) := by
    have hnr : c.1 ∉ A.H.rem (Tstar S) := by simp [A, ripeLab, histT, hist]
    simp only [LabHist.outcomeAt, hnr, ite_false]
    have hkn : IsKept (histT ok h4 h5 hRb N) (Tstar S) c ∧
        c.1 ∉ (histT ok h4 h5 hRb N).rem (Tstar S) := ⟨hkept, hnr⟩
    simp [LabHist.keptLab, c.2, hkn, A, ripeLab]
  have hreal : ∀ i : Fin 5, ∃ f ∈ Realized (Tstar S) A₀, f c.1 = some (Outcome.kept i) := by
    intro i
    refine ⟨fun c' => (A.outcomeAt (Tstar S) c').map (Outcome.relabel i), ?_, ?_⟩
    · exact (realized_congr hAA₀) ▸ realized_of_relabel A (Tstar S) (fun _ => i)
    · simp [hout, Outcome.relabel]
  refine ⟨A, 𝔄, 𝔄', h𝔄, h𝔄', ⟨c, hkept⟩, A₀, hA₀, hAA₀, ?_⟩
  choose f hf hfc using hreal
  have hsurj := (hbij A₀ hA₀).2.2
  choose B hB using fun i => hsurj (hf i)
  have : (Finset.univ : Finset (Fin 5)).card ≤
      (𝔄'.filter fun B => projTo (Tstar S) 𝔄 B = A₀).card := by
    refine Finset.card_le_card_of_injOn B (fun i _ => ?_) (fun i _ j _ hij => ?_)
    · have := (hB i).1
      simpa using this
    · have h1 := (hB i).2
      have h2 := (hB j).2
      simp only at h1 h2
      have : f i c.1 = f j c.1 := by rw [← h1, ← h2, hij]
      rw [hfc, hfc] at this
      exact Outcome.kept.inj (Option.some.inj this)
  simpa using this

end Balaban.Inhabited
