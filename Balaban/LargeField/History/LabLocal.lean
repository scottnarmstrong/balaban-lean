/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.LocalRegion
public import Balaban.LargeField.History.Descent

/-!
# The kept labels of a localized history (ruling R28; LFR Definition II.5.7 (S3), Part I §I.4)

The localized prefix `𝔞 = 𝔸 ∩ Z` of a component `Z` carries the `R`-records of its lineage, in
particular the labels `ϰ` of the kept components of the lineage (LFR line "including the kept labels
of the ripe lineage components").  The landed `LocalHistory` records the regions only; the labels
are the **kept-label record** `LabRec`: the triples `(j, 𝔥_j(Y), ϰ)` of the kept lineage components
`Y` of `Z` at the scales `j < k`, with their localized histories and labels.

* `LabRec`, `RegionHistory.locLab`: the record of `Z` in `(H, lab)`;
* `RegionHistory.mem_locLab`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban RegionHistory

/-- **The kept-label record of a localized history**: triples `(j, a, ϰ)` (scale, localized history
of a kept lineage component, its label). -/
abbrev LabRec (S : Setting) (n : ℕ → ℕ) (M K : ℕ) : Type :=
  Set (ℕ × LocalHistory S n M K × Fin 5)

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K)

/-- **The kept-label record of `Z` in the labelled history `(H, lab)`**: the kept components `Y`
(ripe at a scale `1 ≤ j ≤ k₀`) of the lineage of `Z` at the scales `j < k`, with their localized
histories and their labels `lab j Y`. -/
def locLab (M : ℕ) (lab : ∀ j, H.Comp j → Fin 5) (k : ℕ) (Z : H.Comp k) : LabRec S n M K :=
  {t | ∃ Y : H.Comp t.1, t.1 < k ∧ H.Desc t.1 k Y Z ∧
    (1 ≤ t.1 ∧ t.1 ≤ k0 ∧ S.Ripe t.1 (H.bk t.1 Y)) ∧ H.localHistory M K t.1 Y = t.2.1 ∧
    lab t.1 Y = t.2.2}

theorem mem_locLab {M : ℕ} {lab : ∀ j, H.Comp j → Fin 5} {k : ℕ} {Z : H.Comp k} {j : ℕ}
    {a : LocalHistory S n M K} {ϰ : Fin 5} :
    (j, a, ϰ) ∈ H.locLab M lab k Z ↔ ∃ Y : H.Comp j, j < k ∧ H.Desc j k Y Z ∧
      (1 ≤ j ∧ j ≤ k0 ∧ S.Ripe j (H.bk j Y)) ∧ H.localHistory M K j Y = a ∧ lab j Y = ϰ :=
  Iff.rfl

end RegionHistory

end Balaban.LargeField
