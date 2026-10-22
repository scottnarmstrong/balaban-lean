/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RKeptGasParts
public import Balaban.LargeField.R.G0Gas

/-!
# G0: `ℬ′` and `ℛ″` of the output of `R`, for every record

The parameters `B : BdryFam` and `Rpp : RemFam` of A4's assembly `rKeptGasInput_of_parts`
(`Spine/RKeptGasParts.lean`), constructed by the cluster expansion of the decorated gas of the
removed clusters (P7 (3.26)–(3.29); LFR Definition III.10.6; rulings R4, R12):

* `bPrimeFam pres`: on the torus `nK` of a record, `bPrimeTorus` of the pre-`R` representation
  `rec.F.lf nK` and its small-field context `rec.F.ctx … nK`:
  `ℬ′(𝔸′, X) = ℬ̂(X; 𝔸′) + P^{(k)}(X; 𝔸′)`
  for a removal-free history `𝔸′` and `X` meeting `Y_k`;
* `remFam pres`: on the Def-6 torus `N₁ = L^{m₀} n_k` of the torus `nK` of a record, `remTorus`:
  `ℛ″_m(X) = P^{(k)}_∅(X)` (the gas with no kept region) at `m = m₀ + m₁`; `0` on the Def-6 tori
  that are not of this form.

`pres` is the family of the (H-op) presentations of the removed members (`RemPres`: internal
variables, reference measure, removed weights in operator form, fields of the pre-`R` histories,
the constants of `ℬ′`), W2's export.

**The identity they must satisfy** (G3/E1): with the output family `outFam Ks (bPrimeFam pres)
(remFam pres) rec`, the post-`R` density `outDens` (the sum over the output histories of
`postTerm2`, `0` for the histories with a removal record, R12) is `R ρ`; in particular
`∫ outDens = ∫ ρ` (`RIntegral`).  For a removal-free `𝔸′` the gas of its kept configuration is
`Ξ(𝔸′) = exp Σ_X P^{(k)}(X; 𝔸′)`, the terms with `X ⊂ Y_k^c` are `P^{(k)}_∅(X)` (LFR Lemma
III.10.5, last clause) and are the terms of `ℛ″` inside `sfFactor2` on `Y_k^c` (`sfAddRem`), the
terms with `X ∩ Y_k ≠ ∅` are in `ℬ′` (`bdrySum` over `bdryDoms (Ω_k(𝔸′)) Y_k`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6v2 Balaban.LargeField.G0

section G0

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **The (H-op) presentations of the removed members** for every record and torus (W2's export). -/
abbrev RemPresFam :=
  ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
    [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
    (rec : PreRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k k ρ νk) (nK : ℕ) [NeZero nK],
    RemPres (rec.F.lf nK)

variable {d N T P6 C7 PB cs₀ M1 c rH ϱ}

/-- **`ℬ′` of the output of `R`** (P7 (3.26)–(3.28); LFR Definition III.10.6): `bPrimeTorus` on
every torus of every record. -/
def bPrimeFam (pres : RemPresFam d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    BdryFam d N T P6 C7 PB cs₀ M1 c rH ϱ :=
  fun κ c₉ β ν h kf _ _ k ρ νk rec nK _ =>
    bPrimeTorus (rec.F.lf nK) (rec.F.ctx rec.hM6 rec.hkK nK) h rec.vc
      (pres κ c₉ β ν h kf k ρ νk rec nK)

/-- **`ℛ″` of the output of `R`** (P7 (3.28)–(3.29); LFR Definition III.10.6): on the Def-6 torus
`N₁ = L^{m₀} n_k` of the torus `nK`, `remTorus` of that torus; `0` on the other Def-6 tori. -/
def remFam (pres : RemPresFam d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    RemFam d N T P6 C7 PB cs₀ M1 c rH ϱ :=
  fun κ c₉ β ν h kf _ _ k ρ νk rec N₁ _ =>
    if hN : ∃ nK, 0 < nK ∧
        sfIdx (T κ c₉).L (P6 κ c₉).m₀ (sides (T κ c₉).L (kf + 1) nK) k = N₁ then
      haveI : NeZero hN.choose := ⟨hN.choose_spec.1.ne'⟩
      hN.choose_spec.2 ▸
        remTorus (rec.F.lf hN.choose) (rec.F.ctx rec.hM6 rec.hkK hN.choose) h rec.vc
          (pres κ c₉ β ν h kf k ρ νk rec hN.choose)
    else fun _ _ _ _ _ => 0

end G0

end Balaban.RootFSpine
