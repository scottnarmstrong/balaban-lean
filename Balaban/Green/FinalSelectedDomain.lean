/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalSelectedDatum
public import Balaban.LargeField.History.D1ParentDomain

/-!
# The selected datum lies in the real P2 domain

P7 p. 530 (4.3)--(4.6) solves the massive variational problem for the datum
`Q*ψ_k` on `𝔹_k(W_k)`, `W_k = (Z_kᶜ)^{≈2}`. For the old large-field region
`Z_k = Z_k(A)` of a history `A` the selected datum `finalSelectedDatum` is the landed datum of the
small-field solver, so the P2 real-domain clause `InDomainR` (P2 (R1)--(R4)) holds wherever the
weighted integrand of (D1) is nonzero. This is the clause of the P2 hypotheses that is already
proved; it is available for `k = j + 1 ≤ k₀` only.
-/

@[expose] public section

namespace Balaban.Green

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7
  Balaban.LargeField.Def7v2 RegionHistory Balaban.SmallField.Def6v2

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
  {d : ℕ} {β ν0 a ε : ℝ} {b nr : ℕ → ℝ} {A0 : ℝ} {p0 : ℕ}

/-- **The selected datum of P7 (4.3)--(4.6) is in the real domain `Ψ̃(𝔹_k(W_k); ν, η)`** of P2
for the old large-field region `Z_k(A)`, wherever the weighted integrand of (D1) does not
vanish (scales `k = j + 1 ≤ k₀`). Wrapper of `inDomainR_of_postWeighted_ne_zero` through
`finalSelectedDatum_eq`. -/
theorem finalSelectedDatum_inDomainR (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)
    (rep : Rep S n R k0 K M N geo cs P (j + 1)) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (hgeo : Cx.geo = geo) (hcs : Cx.cs = cs)
    (hreg : RunningHyp d S.L β ν0 a ε b nr) (hg' : KZeroGenuine β ν0)
    (hk : j + 1 ≤ kZero d S.L β ν0) (hA0 : 0 ≤ A0) (hl0 : 0 ≤ runLam a b (j + 1))
    (hlam : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * runLam a b (j + 1) ^ (2 * p0))
    (hδrun : Cx.cs.delta = deltaRun A0 p0 a b) (hunit : ‖hv‖ = 1)
    (hδ : 0 < Cx.cs.delta (j + 1)) (hδ1 : (S.d + 1) * Cx.cs.delta (j + 1) ≤ 1)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    (x : GCfg (fun c : PostComp A (j + 1) => A.H.localHistory M K (j + 1) c.1) (j + 1)
      (postOp geo cs rep.SD rep.KD A Cx.hkK))
    (hW : postWeighted Cx rep A ψk hv g x ≠ 0) :
    InDomainR (finalSelectedGenSet Cx (A.H.step (j + 1)).Z) (sfBgMassAt S.L (j + 1) (nr (j + 1)))
      (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
      (finalSelectedDatum Cx (A.H.step (j + 1)).Z ψk hv) :=
  inDomainR_of_postWeighted_ne_zero Cx rep A ψk hv g hgeo hcs hreg hg' hk hA0 hl0 hlam hδrun
    hunit hδ hδ1 HB x hW

end Balaban.Green
