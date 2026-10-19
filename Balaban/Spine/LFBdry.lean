/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFStep
public import Balaban.Spine.LFBdryHole
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The boundary terms of the large-field step (row (g2) of A4-1h; LFR Lemma IV.1.5)

`LFBdryInput` (`Spine/LFStep.lean`) asks (D7) of the pre-`R` class for the boundary terms
`ℬ^{(k+1)}` of the step map `Λ` at the physical field: locality in the fields and in the history,
reality, analyticity and the bound `B_st e^{-(3κ/2) d^cov}` on the H7 domain, covariance and the
vanishing off the valid labels.  LFR Lemma IV.1.5 (P5 p. 512, P6 pp. 14–15) sorts these terms into
three kinds, each with a constant of rows 0–11; `B_st` is their sum.  This file splits the part
accordingly.

* `D7Bdry.add_B`, `D7Bdry.mono_fac`: (D7) is additive in the boundary terms (the constants add) and
  monotone in the constant.
* `LFBdryPieces`, `LFBdrySplit`: the three kinds of the boundary terms of the step map (a parameter,
  like `Λ`: the provider defines each kind by its formula, and their sum is `Λ.B`).
* `LFBdryPart` and the three parts: `LFBdryNewInput` (kind (i): the new terms of the fluctuation
  integral, of the renormalization and of the surface terms), `LFBdryDeltaInput` (kind (ii): the
  terms `Δ(Y)` of LFR Lemma IV.1.3 meeting `Z^c_{k+1}`), `LFBdryOldInput` (kind (iii): the old
  terms whose domains meet `Ω_{k+1}`, re-expanded).
* `lfBdryInput_of_parts` (**proved**): `LFBdryInput` from the three parts and `Bn + Bd + Bo ≤ B_st`.
* `norm_sum_le_of_transfer` (**proved**): the bound of kind (iii) at an output label from the
  re-expansion bound of each assignment, the lower bound that frees the constant from `B₀`, the size
  transfer of the labels and the entropy of the assignments, every constant shown.

**Kind (iii) and blocker 3.**  The size transfer (`hsize` of `norm_sum_le_of_transfer`) is
geometric.  It is proved in `Spine/LFBdryHole.lean` for the valid labels `Def7.FineValidAt`, which
(ruling R11) require the `π'`-cubes only at the small-field sites
(`Balaban.LargeField.Def7.exists_transfer_fineValidAt`, with mark patches
`Balaban.Fluctuation.transfer_patches`), whatever the shape of the new holes.  For the former
labels (`Fluctuation.DjMod`, `π'`-cubes at every site) it holds only when the new holes are unions
of `π'_{k+1}`-cubes (`Balaban.LargeField.Def7.exists_transfer_djMod_of_open`); at a defect of a new
hole it fails (`Balaban.Fluctuation.spill_of_defect`; the seam of
`notes/phase1/astra/ALIGNED.md` (23)–(26)), which is why R11 was needed.  The labels `Ŷ(S)` of
kinds (i) and (ii) are labels of R11 (`Balaban.Fluctuation.djModFin_Yhat`).  The ruling is R11 in
`notes/phase1/PLAN-B.md`; the named leaves of the three parts are listed in `notes/phase1/SPINE.md`,
row (g2).

Rule 10: `LFBdryPieces` is inhabited; the parts and `LFBdrySplit` need the exemption of the spine
inputs, as the parts of `Spine/LFStep.lean`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Multiscale
  Balaban.Background RegionHistory

namespace Balaban.RootFSpine

/-!
### (D7) of a sum of boundary terms
-/

section Sum

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {m₀ m₁ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {hnn : ∀ i, i < K → n i = S.L * n (i + 1)}
  {hkK : k ≤ K} {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))} {aw μs ε ε1 νs : ℕ → ℝ}
  {rate : ℝ} {hv : EuclideanSpace ℝ (Fin N)}

/-- **(D7) of the pre-`R` class is additive in the boundary terms.**  If the boundary terms `B₁`
and `B₂`, with the histories of `rep`, satisfy (D7) with the constants `fac₁` and `fac₂` (and the
same rate), then their sum satisfies (D7) with `fac₁ + fac₂`: locality, reality, analyticity,
covariance and support are linear, and the bound is the triangle inequality. -/
theorem _root_.Balaban.LargeField.Def7.D7Bdry.add_B (rep : Rep S n R k0 K M N geo cs P k)
    {B₁ B₂ : BTerms S n R k0 K M N k} {fac₁ fac₂ : ℝ}
    (h₁ : D7Bdry Fr hnn hkK { rep with B := B₁ } Zof aw μs ε ε1 νs fac₁ rate hv)
    (h₂ : D7Bdry Fr hnn hkK { rep with B := B₂ } Zof aw μs ε ε1 νs fac₂ rate hv)
    (hB : rep.B = B₁ + B₂) :
    D7Bdry Fr hnn hkK rep Zof aw μs ε ε1 νs (fac₁ + fac₂) rate hv where
  loc_field A hA X hX ψ₁ ψ₂ ψ'₁ ψ'₂ h g₁ g₂ hψ hg := by
    rw [hB]
    simp only [Pi.add_apply]
    exact congrArg₂ (· + ·) (h₁.loc_field A hA X hX ψ₁ ψ₂ ψ'₁ ψ'₂ h g₁ g₂ hψ hg)
      (h₂.loc_field A hA X hX ψ₁ ψ₂ ψ'₁ ψ'₂ h g₁ g₂ hψ hg)
  loc_hist A hA A' hA' X hX hX' hreg hc hc' ψ ψ' h g := by
    rw [hB]
    simp only [Pi.add_apply]
    exact congrArg₂ (· + ·) (h₁.loc_hist A hA A' hA' X hX hX' hreg hc hc' ψ ψ' h g)
      (h₂.loc_hist A hA A' hA' X hX hX' hreg hc hc' ψ ψ' h g)
  real A hA X hX ψ ψ' h g hψ hh hg := by
    rw [hB]
    simp only [Pi.add_apply, Complex.add_im]
    have e1 := h₁.real A hA X hX ψ ψ' h g hψ hh hg
    have e2 := h₂.real A hA X hX ψ ψ' h g hψ hh hg
    simp only at e1 e2
    rw [e1, e2, add_zero]
  analytic A hA X hX h hh := by
    rw [hB]
    exact (h₁.analytic A hA X hX h hh).add (h₂.analytic A hA X hX h hh)
  bound A hA X hX h hh p hp := by
    rw [hB]
    simp only [Pi.add_apply]
    calc _ ≤ ‖B₁ A X (extK p.1) (extK p.2.1) h p.2.2‖ + ‖B₂ A X (extK p.1) (extK p.2.1) h p.2.2‖ :=
          norm_add_le _ _
      _ < _ := by
          rw [add_mul]
          exact add_lt_add (h₁.bound A hA X hX h hh p hp) (h₂.bound A hA X hX h hh p hp)
  rot A hA X hX ρ ψ ψ' h g := by
    rw [hB]
    simp only [Pi.add_apply]
    exact congrArg₂ (· + ·) (h₁.rot A hA X hX ρ ψ ψ' h g) (h₂.rot A hA X hX ρ ψ ψ' h g)
  euclid A hA A' hA' σ hσ hlab X hX ψ ψ' h g := by
    rw [hB]
    simp only [Pi.add_apply]
    exact congrArg₂ (· + ·) (h₁.euclid A hA A' hA' σ hσ hlab X hX ψ ψ' h g)
      (h₂.euclid A hA A' hA' σ hσ hlab X hX ψ ψ' h g)
  support A hA X hX hv' ψ ψ' h g := by
    rw [hB]
    simp only [Pi.add_apply]
    have e1 := h₁.support A hA X hX hv' ψ ψ' h g
    have e2 := h₂.support A hA X hX hv' ψ ψ' h g
    simp only at e1 e2
    rw [e1, e2, add_zero]

/-- **(D7) with a larger constant.** -/
theorem _root_.Balaban.LargeField.Def7.D7Bdry.mono_fac {rep : Rep S n R k0 K M N geo cs P k}
    {fac fac' : ℝ} (h : D7Bdry Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv) (hle : fac ≤ fac') :
    D7Bdry Fr hnn hkK rep Zof aw μs ε ε1 νs fac' rate hv where
  loc_field := h.loc_field
  loc_hist := h.loc_hist
  real := h.real
  analytic := h.analytic
  bound A hA X hX h' hh p hp :=
    (h.bound A hA X hX h' hh p hp).trans_le
      (mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le)
  rot := h.rot
  euclid := h.euclid
  support := h.support

end Sum

/-!
### The three kinds of boundary terms created by a step
-/

section Pieces

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N k : ℕ}

/-- **The boundary terms of a step, by kind** (LFR Lemma IV.1.5; P5 p. 512, P6 pp. 14–15): on every
torus, the boundary terms `ℬ^{(k)}` of the step data `D` are the sum of
* `new`: the new terms of the fluctuation integral, of the renormalization and of the surface terms
  (P5 Propositions 3.1–3.4, P6 Propositions 2.1–2.3), the clusters with no old boundary term;
* `delta`: the terms `Δ(Y)` of LFR Lemma IV.1.3 (FLUCTUATION Theorem 4.2) with `Y` meeting
  `Z^c_{k+1}`;
* `old`: the old boundary terms `ℬ^{(k)}(X')` whose domains meet `Ω_{k+1}` (the part `ℬ''^{(k)}` of
  P5 p. 512), re-expanded in the fluctuation integral (P6 (4.32)–(4.34), P3 (4.41)–(4.48)), the
  clusters with at least one old boundary term. -/
structure LFBdryPieces (D : LFStepRaw S R k0 K M N k) where
  /-- the new terms of the fluctuation integral, the renormalization and the surface terms -/
  new : ∀ (nK : ℕ) [NeZero nK], BTerms S (sides S.L K nK) R k0 K M N k
  /-- the terms `Δ(Y)` of the change of background (LFR Lemma IV.1.3) meeting `Z^c_{k+1}` -/
  delta : ∀ (nK : ℕ) [NeZero nK], BTerms S (sides S.L K nK) R k0 K M N k
  /-- the old boundary terms meeting `Ω_{k+1}`, re-expanded -/
  old : ∀ (nK : ℕ) [NeZero nK], BTerms S (sides S.L K nK) R k0 K M N k
  /-- the boundary terms of `D` are the sum of the three kinds -/
  sum_eq : ∀ (nK : ℕ) [NeZero nK], D.B nK = new nK + delta nK + old nK

/-- `LFBdryPieces` is inhabited (rule 10): all the terms in `new`. -/
instance (D : LFStepRaw S R k0 K M N k) : Nonempty (LFBdryPieces D) :=
  ⟨⟨D.B, fun _ _ => 0, fun _ _ => 0, fun _ _ => by simp⟩⟩

end Pieces

section Inputs

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)
  (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉))

/-- **The split of the boundary terms of a step map by kind** (a parameter of the sub-spine, like
`Λ`): for every record, the three kinds of the boundary terms of `Λ rec` (`LFBdryPieces`). -/
abbrev LFBdrySplit (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ) :=
  ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
    [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
    (rec : RepRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk),
    LFBdryPieces (Λ κ c₉ β ν h kf k ρ νk rec)

/-- **(D7) of one kind of the boundary terms** at the physical field, with the constant `fac κ c₉`
and the rate `3κ/2` of the pre-`R` class: as `LFBdryInput`, for the family whose boundary terms are
those of the kind `B'` (the other data of the successor unchanged). -/
def LFBdryPart (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (B' : ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
      [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
      (rec : RepRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk) (nK : ℕ) [NeZero nK],
      BTerms 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) rec.R
        (kZero d (T κ c₉).L β ν) (kf + 1) (T κ c₉).M N (k + 1))
    (fac : ℝ → ℝ → ℝ) : Prop :=
  LFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ fun κ c₉ β ν h kf _ _ k ρ νk rec hkK' =>
    rec.SuccFams (Φ κ c₉ β ν k rec.F.sf) (Λ κ c₉ β ν h kf k ρ νk rec) fun F' =>
      ∀ (nK : ℕ) [NeZero nK], D7Bdry (fineFrame 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
          (sides (T κ c₉).L (kf + 1) nK) (kf + 1) rec.hM6) (sides_hnn (T κ c₉).L (kf + 1) nK)
        hkK' { F'.lf nK with B := B' κ c₉ β ν h kf k ρ νk rec nK } (fun A => A.H.F.Zpre (k + 1))
        F'.weights (rec.succCs (Φ κ c₉ β ν k rec.F.sf)).mu ((P6 κ c₉).eps d (T κ c₉).L)
        (epsOne 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (P6 κ c₉) (C7 κ c₉))
        (rec.succCs (Φ κ c₉ β ν k rec.F.sf)).nu (fac κ c₉) (3 / 2 * (P6 κ c₉).κ) h

/-- **The new terms (row (g2), kind (i); LFR Lemma IV.1.5 (i)).** The new boundary terms of the
fluctuation integral, of the renormalization and of the surface terms (P5 Propositions 3.1–3.4,
P6 Propositions 2.1–2.3, the clusters of the fluctuation integral with no old boundary term) satisfy
(D7) of the pre-`R` class with the constant `Bn κ c₉` (constants of rows 0–11, P6 p. 15). -/
def LFBdryNewInput (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (Sb : LFBdrySplit d N T P6 C7 PB cs₀ M1 c rH ϱ Λ) (Bn : ℝ → ℝ → ℝ) : Prop :=
  LFBdryPart d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ
    (fun κ c₉ β ν h kf _ _ k ρ νk rec => (Sb κ c₉ β ν h kf k ρ νk rec).new) Bn

/-- **The terms of the change of background (row (g2), kind (ii); LFR Lemma IV.1.5 (ii), Lemma
IV.1.3, FLUCTUATION Theorem 4.2).** The terms `Δ(Y)` of the expansion (IV.1.1) of the main action at
the complete background with `Y` meeting `Z^c_{k+1}` satisfy (D7) of the pre-`R` class with the
constant `Bd κ c₉` (Lemma IV.1.3: `|Δ(Y)| ≤ e^{-R̂_k/2} e^{-κ_+ d^cov}`). -/
def LFBdryDeltaInput (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (Sb : LFBdrySplit d N T P6 C7 PB cs₀ M1 c rH ϱ Λ) (Bd : ℝ → ℝ → ℝ) : Prop :=
  LFBdryPart d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ
    (fun κ c₉ β ν h kf _ _ k ρ νk rec => (Sb κ c₉ β ν h kf k ρ νk rec).delta) Bd

/-- **The old terms re-expanded (row (g2), kind (iii); LFR Lemma IV.1.5 (iii); P5 p. 512, P6 p. 34,
(4.32)–(4.34); blocker 3).** The old boundary terms `ℬ^{(k)}(X')` of the record whose domains meet
`Ω_{k+1}`, re-expanded in the fluctuation integral, satisfy (D7) of the pre-`R` class with the
constant `Bo κ c₉`.  The bound is the transfer of the bound of the record's terms
(`norm_sum_le_of_transfer`) along the transfer of their labels to the scale `k + 1`
(`Balaban.Fluctuation.exists_transfer_djModFin`); the transfer of a label across a new hole that is
not a union of `π'_{k+1}`-cubes is blocker 3 (`notes/phase1/PLAN-B.md`, ruling request R11). -/
def LFBdryOldInput (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (Sb : LFBdrySplit d N T P6 C7 PB cs₀ M1 c rH ϱ Λ) (Bo : ℝ → ℝ → ℝ) : Prop :=
  LFBdryPart d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ
    (fun κ c₉ β ν h kf _ _ k ρ νk rec => (Sb κ c₉ β ν h kf k ρ νk rec).old) Bo

end Inputs

/-!
### The assembly
-/

section Assembly

variable {d N : ℕ} {T : ℝ → ℝ → Typing} {P6 : ℝ → ℝ → Def6.Consts}
  {C7 : ℝ → ℝ → Consts7} {PB : ℝ → ℝ → BudgetConsts} {cs₀ : ℝ → ℝ → OpConsts}
  {M1 c : ℝ → ℝ → ℕ} {rH ϱ : ℝ → ℝ → ℝ}
  {Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉)}

/-- **(D7) of the boundary terms of the step from its three kinds** (LFR Lemma IV.1.5: `B_st` is the
sum of the constants of the three kinds).  Given the split `Sb` of the boundary terms of the map
`Λ` into the new terms, the terms `Δ(Y)` and the re-expanded old terms, (D7) of each kind with the
constants `Bn`, `Bd`, `Bo` and `Bn + Bd + Bo ≤ B_st` give `LFBdryInput` (row (g2)). -/
theorem lfBdryInput_of_parts (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (Sb : LFBdrySplit d N T P6 C7 PB cs₀ M1 c rH ϱ Λ) {Bn Bd Bo : ℝ → ℝ → ℝ}
    (hBst : ∀ κ c₉, Bn κ c₉ + Bd κ c₉ + Bo κ c₉ ≤ (C7 κ c₉).Bst)
    (hN : LFBdryNewInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ Sb Bn)
    (hD : LFBdryDeltaInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ Sb Bd)
    (hO : LFBdryOldInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ Sb Bo) :
    LFBdryInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ := by
  intro κ hκ c₉ hc₉
  obtain ⟨b₁, h₁⟩ := hN κ hκ c₉ hc₉
  obtain ⟨b₂, h₂⟩ := hD κ hκ c₉ hc₉
  obtain ⟨b₃, h₃⟩ := hO κ hκ c₉ hc₉
  refine ⟨max b₁ (max b₂ b₃), ?_⟩
  intro β hβ ν hν hνL h hh kf hkf _ _ k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK' SD hM nK _
  simp only [max_le_iff] at hβ
  obtain ⟨hb₁, hb₂, hb₃⟩ := hβ
  have e1 := h₁ β hb₁ ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK' SD hM nK
  have e2 := h₂ β hb₂ ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK' SD hM nK
  have e3 := h₃ β hb₃ ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK' SD hM nK
  have h12 := D7Bdry.add_B { ((Λ κ c₉ β ν h kf k ρ νk rec).fam (Φ κ c₉ β ν k rec.F.sf)
      (fun nK _ => (rec.F.lf nK).κK) SD (rec.succKD (Φ κ c₉ β ν k rec.F.sf))).lf nK with
      B := (Sb κ c₉ β ν h kf k ρ νk rec).new nK + (Sb κ c₉ β ν h kf k ρ νk rec).delta nK } e1 e2 rfl
  exact (D7Bdry.add_B _ h12 e3 ((Sb κ c₉ β ν h kf k ρ νk rec).sum_eq nK)).mono_fac (hBst κ c₉)

end Assembly

/-!
### The bound of the re-expanded old terms (LFR Lemma IV.1.5 (iii), P6 (4.34))
-/

section Ledger

/-- **The transfer of the bound of the old boundary terms to an output label** (LFR Lemma IV.1.5
(iii); P6 (4.32)–(4.34); P3 (4.48)–(4.49)).  The old part of the coefficient at an output label of
size `Dp` is a finite sum over the assignments `a` (an old label `X'` and the marks of its
re-expansion) of coefficients `T a`, with
* `hT`: the re-expansion bound `‖T a‖ ≤ C_re B₀ e^{-κ D(X')} e^{-κ_m m(a)}` (the bound (D7) of the
  record's term, `κ` its rate, times the factor of the `m(a)` marks);
* `hmin`, `hB₀min`: the old label meets the collar of the old holes and `Ω_{k+1}`, so
  `D(X') ≥ D_min` with `B₀ e^{-(κ/2) D_min} ≤ 1` (the constant of the step is free of `B₀`;
  `Balaban.Fluctuation.dcovMod_ge_supDist`);
* `hsize`: the size of the output label is at most `D(X')/L + C_d m(a)` (the transfer of the label;
  across a new hole this is blocker 3, `Balaban.Fluctuation.exists_transfer_djModFin`,
  `Balaban.Fluctuation.transfer_patches`);
* `hent`: the entropy of the assignments at one output label,
  `∑_a e^{-(κ/2 - κ_o/L) D(X') - (κ_m - κ_o C_d) m(a)} ≤ K_ent`.
Then `‖∑_a T a‖ ≤ C_re K_ent e^{-κ_o Dp}`, with every constant shown. -/
theorem norm_sum_le_of_transfer {ι : Type*} (I : Finset ι) (T : ι → ℂ) (Dm mk : ι → ℝ)
    {Dp B₀ Cre κ κm κo L Cd Dmin Kent : ℝ} (hCre : 0 ≤ Cre) (hB₀ : 0 ≤ B₀) (hκ : 0 ≤ κ)
    (hκo : 0 ≤ κo)
    (hT : ∀ a ∈ I, ‖T a‖ ≤ Cre * B₀ * Real.exp (-κ * Dm a) * Real.exp (-κm * mk a))
    (hmin : ∀ a ∈ I, Dmin ≤ Dm a) (hB₀min : B₀ * Real.exp (-(κ / 2) * Dmin) ≤ 1)
    (hsize : ∀ a ∈ I, Dp ≤ Dm a / L + Cd * mk a)
    (hent : ∑ a ∈ I, Real.exp (-(κ / 2 - κo / L) * Dm a - (κm - κo * Cd) * mk a) ≤ Kent) :
    ‖∑ a ∈ I, T a‖ ≤ Cre * Kent * Real.exp (-κo * Dp) := by
  have hterm : ∀ a ∈ I, ‖T a‖ ≤ Cre * Real.exp (-κo * Dp) *
      Real.exp (-(κ / 2 - κo / L) * Dm a - (κm - κo * Cd) * mk a) := by
    intro a ha
    have hsplit :
        Real.exp (-κ * Dm a) = Real.exp (-(κ / 2) * Dm a) * Real.exp (-(κ / 2) * Dm a) := by
      rw [← Real.exp_add]; congr 1; ring
    have hmono : Real.exp (-(κ / 2) * Dm a) ≤ Real.exp (-(κ / 2) * Dmin) :=
      Real.exp_le_exp.2 (by nlinarith [hmin a ha])
    have h1 : B₀ * Real.exp (-κ * Dm a) ≤ Real.exp (-(κ / 2) * Dm a) := by
      rw [hsplit, ← mul_assoc]
      calc B₀ * Real.exp (-(κ / 2) * Dm a) * Real.exp (-(κ / 2) * Dm a)
          ≤ B₀ * Real.exp (-(κ / 2) * Dmin) * Real.exp (-(κ / 2) * Dm a) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hB₀) (Real.exp_pos _).le
        _ ≤ 1 * Real.exp (-(κ / 2) * Dm a) :=
            mul_le_mul_of_nonneg_right hB₀min (Real.exp_pos _).le
        _ = Real.exp (-(κ / 2) * Dm a) := one_mul _
    have h3 : -(κ / 2) * Dm a + -κm * mk a ≤
        -κo * Dp + (-(κ / 2 - κo / L) * Dm a - (κm - κo * Cd) * mk a) := by
      have h4 : κo * Dp ≤ κo * (Dm a / L + Cd * mk a) := mul_le_mul_of_nonneg_left (hsize a ha) hκo
      have e : κo * (Dm a / L + Cd * mk a) = κo / L * Dm a + κo * Cd * mk a := by ring
      linarith
    calc ‖T a‖ ≤ Cre * B₀ * Real.exp (-κ * Dm a) * Real.exp (-κm * mk a) := hT a ha
      _ = Cre * (B₀ * Real.exp (-κ * Dm a)) * Real.exp (-κm * mk a) := by ring
      _ ≤ Cre * Real.exp (-(κ / 2) * Dm a) * Real.exp (-κm * mk a) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCre) (Real.exp_pos _).le
      _ = Cre * Real.exp (-(κ / 2) * Dm a + -κm * mk a) := by rw [Real.exp_add]; ring
      _ ≤ Cre * Real.exp (-κo * Dp + (-(κ / 2 - κo / L) * Dm a - (κm - κo * Cd) * mk a)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h3) hCre
      _ = _ := by rw [Real.exp_add]; ring
  calc ‖∑ a ∈ I, T a‖ ≤ ∑ a ∈ I, ‖T a‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ I, Cre * Real.exp (-κo * Dp) *
          Real.exp (-(κ / 2 - κo / L) * Dm a - (κm - κo * Cd) * mk a) :=
        Finset.sum_le_sum hterm
    _ = Cre * Real.exp (-κo * Dp) *
          ∑ a ∈ I, Real.exp (-(κ / 2 - κo / L) * Dm a - (κm - κo * Cd) * mk a) := by
        rw [Finset.mul_sum]
    _ ≤ Cre * Real.exp (-κo * Dp) * Kent :=
        mul_le_mul_of_nonneg_left hent (mul_nonneg hCre (Real.exp_pos _).le)
    _ = Cre * Kent * Real.exp (-κo * Dp) := by ring

end Ledger

end Balaban.RootFSpine
