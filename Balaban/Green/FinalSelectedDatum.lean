/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol (astra)
-/
module

public import Balaban.LargeField.Def7SmallField

/-!
# Selected-set generating geometry and retained datum

P7, printed p. 530 (4.3)--(4.6), uses `𝔹_k(W_k)` and
`ψ̃_k = Q*(𝔹_k(W_k)) ψ_k` in its variational problem. P5, printed p. 493 (1.4),
specifies `W_k = (Z_kᶜ)^{≈2}`. The landed `W2`, `SFCtx.genW` and `liftSingle` implement
these operations, including clipping the datum to `dataSites` and the direction to `Ω₁`.
The `Zk` below is the selected *old* large-field region of (4.3), not the new cutoff set
`Z_{k+1}` produced later in (4.9). The proof that a particular last-integral term carries
this `SFCtx` is separate.
-/

@[expose] public section

noncomputable section

open Balaban.Background Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale

namespace Balaban.Green

/-- P7 p. 530 (4.3)--(4.6): the selected `𝔹_k(W_k)` for the P5 p. 493 (1.4)
good set `W_k = (Z_kᶜ)^{≈2}`. The source construction is the landed `SFCtx.genW`. -/
def finalSelectedGenSet {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    {R : ℕ → ℝ} {M K N k m₁ : ℕ} [NeZero M] [NeZero S.L] {ϱ : ℝ}
    (C : SFCtx S n R M K N k m₁ ϱ)
    (Zk : Set (Torus S.d (n k))) :
    GeneratingSet S.d S.L (C.geo.M1 * (C.geo.c * n k)) k
      (minSep S.L C.geo.M1) :=
  C.genW Zkᶜ

/-- P7 p. 530 (4.4)--(4.6): the selected retained datum `Q*ψ_k`, clipped to the
generating set's data collar, with constant external direction `h`. The source operation
is the landed `liftSingle`; its argument `C.liftData ψk` is the level-`k` field lift. -/
def finalSelectedDatum {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    {R : ℕ → ℝ} {M K N k m₁ : ℕ} [NeZero M] [NeZero S.L] {ϱ : ℝ}
    (C : SFCtx S n R M K N k m₁ ϱ)
    (Zk : Set (Torus S.d (n k)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) : BgData (finalSelectedGenSet C Zk) N :=
  liftSingle (finalSelectedGenSet C Zk) (C.liftData ψk) (hC hv)

/-- Unfold the selected set to the already landed P5/P3 `𝔹_k(W_k)`. -/
theorem finalSelectedGenSet_eq {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    {R : ℕ → ℝ} {M K N k m₁ : ℕ} [NeZero M] [NeZero S.L] {ϱ : ℝ}
    (C : SFCtx S n R M K N k m₁ ϱ)
    (Zk : Set (Torus S.d (n k))) : finalSelectedGenSet C Zk = C.genW Zkᶜ := rfl

/-- Unfold the selected datum to the landed `liftSingle` of `Q*ψ_k`. -/
theorem finalSelectedDatum_eq {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    {R : ℕ → ℝ} {M K N k m₁ : ℕ} [NeZero M] [NeZero S.L] {ϱ : ℝ}
    (C : SFCtx S n R M K N k m₁ ϱ)
    (Zk : Set (Torus S.d (n k)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) :
    finalSelectedDatum C Zk ψk hv =
      liftSingle (C.genW Zkᶜ) (C.liftData ψk) (hC hv) := rfl

/-- On the selected P2 data collar, the datum is the lifted retained field. -/
theorem finalSelectedDatum_Ψ {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    {R : ℕ → ℝ} {M K N k m₁ : ℕ} [NeZero M] [NeZero S.L] {ϱ : ℝ}
    (C : SFCtx S n R M K N k m₁ ϱ)
    (Zk : Set (Torus S.d (n k)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N))
    {x : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ k)}
    (hx : x ∈ dataSites (finalSelectedGenSet C Zk)) :
    (finalSelectedDatum C Zk ψk hv).Ψ x = blockLift k (C.liftData ψk) x := by
  exact liftSingle_Ψ (finalSelectedGenSet C Zk) (C.liftData ψk) (hC hv) hx

/-- On `Ω₁`, the selected datum carries the fixed external direction. -/
theorem finalSelectedDatum_h {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    {R : ℕ → ℝ} {M K N k m₁ : ℕ} [NeZero M] [NeZero S.L] {ϱ : ℝ}
    (C : SFCtx S n R M K N k m₁ ϱ)
    (Zk : Set (Torus S.d (n k)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N))
    {x : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ k)}
    (hx : x ∈ (finalSelectedGenSet C Zk).Ω 1) :
    (finalSelectedDatum C Zk ψk hv).h x = hC hv := by
  exact liftSingle_h (finalSelectedGenSet C Zk) (C.liftData ψk) (hC hv) hx

end Balaban.Green
