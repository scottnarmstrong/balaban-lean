/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.PairedReadLocality
public import Balaban.Inhabited.P6PairGraphWitness

/-!
# Non-vacuity of the graph side of the restricted-read locality

Combinatorics only.  On the slab pair of `P6PairGraphWitness`, the joint closure with the one-site
seed `{ustar}` (a one-site read set) contains the seed, and `seed_graph_hyps` supplies the graph
hypotheses of `paired_locality_on` for it.  The analytic hypotheses of `paired_locality_on`
(selectors, data domains) have no landed instance for the P6 pair, so no instance of the full
theorem is given.
-/

@[expose] public section

namespace Balaban.Inhabited

namespace PairedReadLocalityWitness

open Balaban Balaban.LargeField Balaban.Localization Balaban.Multiscale Balaban.Localization.Dec2
open Slab P6PairGraphWitness

/-- The graph hypotheses with a one-site seed that need not contain `X₁ = ∅`. -/
theorem seed_instance (n1 : ℕ) [NeZero n1] (a : ℕ → ℝ) (ν : ℝ) :
    ustar n1 ∈ jointSites (coverOf (P6FsharpRootedWitness.Fs n1)) (Hbd n1) (Hold n1) a ν
        (∅ : Finset (CTorus 3 3 (15 * n1) 2 (1 + 1)))
        ({((1 + 1, ustar n1) : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1))} : Finset _)
        (({ustar n1} : Set _)) ∧
    ∀ J : Finset (Fin 1), ∃ Ab Am : Finset (ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1)),
      IsIncUnion (coverOf (P6FsharpRootedWitness.Fs n1)) (Hbd n1) a ν (∅ : Finset _)
        (J.image fun _ => ((1 + 1, ustar n1) : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1)))
        (jointSites (coverOf (P6FsharpRootedWitness.Fs n1)) (Hbd n1) (Hold n1) a ν (∅ : Finset _)
          (J.image fun _ => ((1 + 1, ustar n1) : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1)))
          (({ustar n1} : Set _))) Ab ∧
      IsIncUnion (coverOf (P6FsharpRootedWitness.Fs n1)) (Hold n1) a ν (∅ : Finset _)
        (J.image fun _ => ((1 + 1, ustar n1) : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1)))
        (jointSites (coverOf (P6FsharpRootedWitness.Fs n1)) (Hbd n1) (Hold n1) a ν (∅ : Finset _)
          (J.image fun _ => ((1 + 1, ustar n1) : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1)))
          (({ustar n1} : Set _))) Am := by
  refine ⟨seed_mem_jointSites rfl, fun J => ?_⟩
  obtain ⟨Ab, Am, h1, h2, -, -⟩ := seed_graph_hyps (C := coverOf (P6FsharpRootedWitness.Fs n1))
    (Hb := Hbd n1) (Hm := Hold n1) (a := a) (ν := ν) (X₁ := (∅ : Finset _))
    (U := (({ustar n1} : Set _))) (fun _ : Fin 1 => ((1 + 1, ustar n1) : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1))) J
  exact ⟨Ab, Am, h1, h2⟩

end PairedReadLocalityWitness

end Balaban.Inhabited
