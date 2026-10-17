/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedLres
public import Balaban.LargeField.R.RRemovedFinalRip

/-!
# `hCR0` of `lf4R_removed` from the Setting (W947)

`notes/phase1/LF4R-PLAN.md`, item 7.  `CR_le_A2_pow_of_lam0`: `C_R ≤ A₂ λ_k^{p₂-2d-1}` for every scale `k` as soon as
`λ₀ ≥ C_R / A₂` (`λ_k ≥ λ₀ ≥ 1`).  The condition `λ₀ ≥ C_R/A₂` is not among (Λ0)–(Λ11) (`(Λ10)` only gives
`C_R λ^{2d+1} ≤ A₃' λ^{p_R}`, `p_R > p₂ + 2d`), so it is a named condition on `λ₀` (an eventual one).
-/

@[expose] public section

namespace Balaban.LargeField

theorem CR_le_A2_pow_of_lam0 {S : Setting} (ok : S.Ok) (h0 : S.CR / S.A2 ≤ S.lam 0) (k : ℕ) :
    S.CR ≤ S.A2 * S.lam k ^ (S.p2 - (2 * S.d + 1)) :=
  CR_le_A2_pow_of_large ok (ok.one_le_lam0.trans (ok.lam_mono (Nat.zero_le k)))
    (h0.trans (ok.lam_mono (Nat.zero_le k)))

end Balaban.LargeField
