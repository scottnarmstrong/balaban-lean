/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusDefectFinTail
public import Balaban.SmallField.IrrelTorusDefectInfTail
public import Balaban.SmallField.Def6v2Renorm

/-!
# Matched shapes and the infinite shapes for the second version

* `filed_fin_eq_inf`: on a shape that is a polymer of the torus and of `T∞`, the filed terms of the
  torus and of the infinite volume are equal (the two terms are the same function);
* `IsSFFamily2.tsum_filed_inf`, `IsSFFamily2.norm_filed_inf_le`: the two infinite-volume facts for
  a member of the second version (through the reduction to the landed class).
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}

open Classical in
/-- The pulled-back finite term at the origin is the term `termLA` of the lifted family. -/
theorem trickFnA_origin_eq_termLA (i₀ : Fin N) (ν r : ℝ) (X' : Finset (Site d)) :
    (fun c : Cfg d N X' => trickFnA i₀ ν r (fun c' : Cfg d N X' =>
      Tm.E j 0 (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')
        (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' c' (z - 0))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν X' c')) c) =
      termLA Tm j i₀ ν r X' := by
  funext c
  have hG : (fun c' : Cfg d N X' =>
      Tm.E j 0 (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')
        (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' c' (z - 0))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν X' c')) = Eaux Tm j i₀ ν X' := by
    funext c'
    unfold Eaux
    simp only [sub_zero]
  rw [hG]
  rfl


end Balaban.SmallField.Def6v2

namespace Balaban.SmallField

variable {d N : ℕ} {T T' : TermFamily d N} {i₀ i₁ : Fin N} {ν : ℝ} {X : Finset (Site d)}
  {ψ : Site d → Spin N} {b : Spin N}

/-- The first order part of the filed term depends on the family through the term of the polymer
only. -/
theorem Ttw_congr_term (h : T.term X = T'.term X) :
    Ttw T i₀ ν X ψ b = Ttw T' i₀ ν X ψ b := by
  unfold Ttw
  rw [h]

/-- The second order part of the filed term depends on the family through the term of the polymer
only. -/
theorem Phitw_congr_term (h : T.term X = T'.term X) :
    Phitw T i₀ i₁ ν X ψ = Phitw T' i₀ i₁ ν X ψ := by
  unfold Phitw Sx tensB
  rw [h]

end Balaban.SmallField

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts}
  {TmF : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ} {j : ℕ}

/-- **On a shape common to the torus and to `T∞` the filed terms agree**: the terms of the two
one-polymer families are the same function. -/
theorem filed_fin_eq_inf {N₁ : ℕ} [NeZero N₁] (hT : TorusIndep P.m₀ TmF) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX' : X' ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j)
    (hInf : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') (i₀ i₁ : Fin N) (ν r : ℝ)
    (ψ : Site d → Spin N) (b : Spin N) :
    Ttw (⟨{X'}, fun _ => sizeJ P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'),
        fun S' c => trickFnA i₀ ν r (fun c' : Cfg d N S' =>
          (TmF N₁).E j 0 (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')
            (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S' c' (z - 0))
            (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S' c')) c⟩ : TermFamily d N)
        i₀ ν X' ψ b +
      Phitw (⟨{X'}, fun _ => sizeJ P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'),
        fun S' c => trickFnA i₀ ν r (fun c' : Cfg d N S' =>
          (TmF N₁).E j 0 (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')
            (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S' c' (z - 0))
            (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S' c')) c⟩ : TermFamily d N)
        i₀ i₁ ν X' ψ =
    Ttw (liftInfA (L := L) (m₁ := m₁) (k := k) P TmF j i₀ ν r) i₀ ν X' ψ b +
      Phitw (liftInfA (L := L) (m₁ := m₁) (k := k) P TmF j i₀ ν r) i₀ i₁ ν X' ψ := by
  obtain ⟨h0, hnw, hpd⟩ := hX'
  have hterm : (liftInfA (L := L) (m₁ := m₁) (k := k) P TmF j i₀ ν r).term X' =
      (⟨{X'}, fun _ => sizeJ P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'),
        fun S' c => trickFnA i₀ ν r (fun c' : Cfg d N S' =>
          (TmF N₁).E j 0 (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')
            (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S' c' (z - 0))
            (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S' c')) c⟩ : TermFamily d N).term X' := by
    funext c
    show termLInfA TmF P.m₀ j i₀ ν r X' c = _
    rw [termLInfA_eq hT hj1 hjk i₀ ν r h0 hInf N₁ hnw hpd c]
    exact (congrFun (trickFnA_origin_eq_termLA (Tm := TmF N₁) (j := j) i₀ ν r X') c).symm
  rw [Ttw_congr_term hterm.symm, Phitw_congr_term hterm.symm]

end Balaban.SmallField.Def6v2

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ}
  {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

section Inf

variable (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
  (hCR : ∀ (N₁ : ℕ) [NeZero N₁], CRotE P (completeXiDom P Rg a N₁) (Tm N₁))
  (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
include hF hCR hn hne

open Classical in
/-- **The sum over the infinite shapes of the filed term vanishes**, second version. -/
theorem IsSFFamily2.tsum_filed_inf (ψ : Site d → Spin N) (b : Spin N) :
    Summable (fun X : (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀
        (nuIdeal L k (Rg.ν k) j) (anisoRadius d L N P j)).polys =>
      Ttw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (Rg.ν k) j)
        (anisoRadius d L N P j)) i₀ (nuIdeal L k (Rg.ν k) j) X.1 ψ b +
      Phitw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (Rg.ν k) j)
        (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) X.1 ψ) ∧
    ∑' X : (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (Rg.ν k) j)
        (anisoRadius d L N P j)).polys,
      (Ttw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (Rg.ν k) j)
        (anisoRadius d L N P j)) i₀ (nuIdeal L k (Rg.ν k) j) X.1 ψ b +
      Phitw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (Rg.ν k) j)
        (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) X.1 ψ) = 0 := by
  obtain ⟨β', ν', hν, -, hF'⟩ := hF.toLanded hCR
  rw [← hν]
  exact hF'.tsum_filed_inf hn.noChi hne ψ b

/-- **The filed term of one infinite shape in the Cauchy form**, second version. -/
theorem IsSFFamily2.norm_filed_inf_le {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {ψ : Site d → Spin N} {b : Spin N} {σ ε K₂ Λ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)}
    (dat : DataHypAniso Dom (nuIdeal L k (Rg.ν k) j) σ ε K₂ ψ b) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hε : 0 < ε) (hεΛ : ε ≤ Λ * anisoRadius d L N P j) (hτ : σ ^ 2 * ε ≤ 1 / 4) :
    ‖Ttw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (Rg.ν k) j)
        (anisoRadius d L N P j)) i₀ (nuIdeal L k (Rg.ν k) j) X' ψ b +
      Phitw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (Rg.ν k) j)
        (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (Rg.ν k) j) X' ψ‖ ≤
      (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 +
          (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 *
            (N * (N * 40 * Λ) ^ 2)) *
        (P.E₀ * Real.exp (-P.κ * dInf L m₁ k P.m₀ j X') * (1 + dInf L m₁ k P.m₀ j X') ^ 4) := by
  obtain ⟨β', ν', hν, -, hF'⟩ := hF.toLanded hCR
  rw [← hν] at dat ⊢
  exact hF'.norm_filed_inf_le hn.noChi hne h0 hX dat hσ hσ1 hε hεΛ hτ

end Inf

end Balaban.SmallField.Def6v2
