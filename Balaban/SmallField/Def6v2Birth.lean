/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2Bridge

/-!
# The birth-mass domains of Def-6 v2

The level-`j` terms keep the fine mass `μ_j = ν_j L⁻²ʲ` of the scale at which they were born.
Their wide complex chart is `Ξᶜ_j(G; aIdeal L k (a k), μ_j, 1, ε_j)`, with the same physical
carrier and ideal kernel sequence as `completeXiDom`. This is the birth-frozen interpretation of
P4 p. 704 (4.19) and the inherited term domains in P1 (H.4)–(H.7), under author ruling R6.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The wide level-`j` field domain with its background mass fixed at the birth scale `j`:
`Ξᶜ_j(G; aIdeal L k (a k), ν_j L⁻²ʲ, 1, ε_j)`. The real carrier is all external fields, as in
`completeXiDom`. See P4 p. 704 (4.19), P1 (H.4)–(H.7), and ruling R6. -/
noncomputable def birthXiDom (P : Consts) (Rg : Regime L) (a : ℕ → ℝ) :
    ∀ (N₁ : ℕ) [NeZero N₁], FieldDom d L N₁ m₁ k N ϱ :=
  fun _ _ =>
    { phys := Set.univ
      dom := fun j G Ψ h =>
        XiDom G (aIdeal L k (a k)) (physMass L j (Rg.ν j)) j (P.eps d L j) Ψ h }

theorem birthXiDom_phys (P : Consts) (Rg : Regime L) (a : ℕ → ℝ) :
    (birthXiDom (d := d) (m₁ := m₁) (k := k) (N := N) (ϱ := ϱ) P Rg a N₁).phys =
      Set.univ := rfl

theorem birthXiDom_dom_iff (P : Consts) (Rg : Regime L) (a : ℕ → ℝ) (j : ℕ)
    (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) (Ψ h : Fld d L N₁ m₁ k N) :
    (birthXiDom P Rg a N₁).dom j G Ψ h ↔
      XiDom G (aIdeal L k (a k)) (physMass L j (Rg.ν j)) j (P.eps d L j) Ψ h :=
  Iff.rfl

theorem birthXiDom_dom_self (P : Consts) (Rg : Regime L) (a : ℕ → ℝ)
    (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) (Ψ h : Fld d L N₁ m₁ k N) :
    (birthXiDom P Rg a N₁).dom k G Ψ h ↔ (completeXiDom P Rg a N₁).dom k G Ψ h :=
  Iff.rfl

/-- On a fixed fine torus, an old level has the same chart whenever its birth mass and its
ideal kernel sequence agree. This isolates the two coefficient identities needed when old terms
are transported to the next scale. -/
theorem birthXiDom_dom_congr (P : Consts) {Rg Rg' : Regime L} {a a' : ℕ → ℝ}
    (ha : aIdeal L k (a k) = aIdeal L k (a' k)) {j : ℕ} (hν : Rg.ν j = Rg'.ν j)
    (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) (Ψ h : Fld d L N₁ m₁ k N) :
    (birthXiDom P Rg a N₁).dom j G Ψ h ↔ (birthXiDom P Rg' a' N₁).dom j G Ψ h := by
  rw [birthXiDom_dom_iff, birthXiDom_dom_iff, ha, hν]

section Bridge

variable {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρ : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}

/-- The shared radius inclusion for the birth domain at a level where its fine mass satisfies
the background hypothesis and the source-mass comparison. -/
theorem polyAniso_subset_birthXiDom_of_mass
    (hF : IsSFFamily2 P Rg β a (birthXiDom P Rg a) Tm ρ Ek) {j : ℕ}
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (physMass L j (Rg.ν j)))
    (hνj : 0 < nuIdeal L k (Rg.ν k) j)
    (hm : physMass L j (Rg.ν j) * ((L : ℝ) ^ j) ^ 2 ≤ nuIdeal L k (Rg.ν k) j)
    (hj1 : 1 ≤ j) (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (i₀ : Fin N) {r : ℝ} (hr : AnisoRadiusOK d L N P j r) {c : Cfg d N X'}
    (hc : c ∈ polyAniso i₀ (nuIdeal L k (Rg.ν k) j) r X') :
    (birthXiDom P Rg a N₁).dom j ((Tm N₁).gs j (Ypoly j X'))
      (fieldOf j i₀ X' c) (hOf (nuIdeal L k (Rg.ν k) j) X' c) := by
  rw [birthXiDom_dom_iff]
  exact polyAniso_subset_xiDom_of_radius hBg
    ((hF.torus N₁).terms.gs_spec j hj1 hjk _ hX).2 hjk hνj hm i₀ hr hc

/-- At the newly born level, the birth-domain radius inclusion has the same mass hypotheses as
the complete-domain bridge. -/
theorem polyAniso_subset_birthXiDom_top
    (hF : IsSFFamily2 P Rg β a (birthXiDom P Rg a) Tm ρ Ek)
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ) (hk1 : 1 ≤ k)
    {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ k (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) k X'))
    (i₀ : Fin N) {r : ℝ} (hr : AnisoRadiusOK d L N P k r) {c : Cfg d N X'}
    (hc : c ∈ polyAniso i₀ (nuIdeal L k (Rg.ν k) k) r X') :
    (birthXiDom P Rg a N₁).dom k ((Tm N₁).gs k (Ypoly k X'))
      (fieldOf k i₀ X' c) (hOf (nuIdeal L k (Rg.ν k) k) X' c) := by
  apply polyAniso_subset_birthXiDom_of_mass hF
    (show BgHyp d L k ϱ (aIdeal L k (a k)) (physMass L k (Rg.ν k)) by
      exact bgHyp_of_class2 hF.admissible hF.coeff hd hL hϱ)
    (by simpa only [nuIdeal, Nat.sub_self, pow_zero, inv_one, one_pow, mul_one] using hF.coeff.nu_pos)
    (by rw [physMass_mul_sq]; simp only [nuIdeal, Nat.sub_self, pow_zero, inv_one, one_pow, mul_one]; exact le_rfl)
    hk1 le_rfl hX i₀ hr hc

end Bridge

end Balaban.SmallField.Def6v2
