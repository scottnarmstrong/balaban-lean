/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.InheritedBound
public import Balaban.Spine.InheritedAgreeGeom
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The two-torus agreement of the inherited observable activities

`inheritedAgreeInput` proves the spine sub-input `InheritedAgreeInput`
(`Spine/LastIntegral.lean`): the increments of the inherited observable activities `inhObs` on two
admissible tori agree on the images of a finite set `A ⊂ ℤ^d` in the common quarter box
(LFR Theorem IV.5.3 item 7 for `j ≤ k_f`; the clause `ActAgree`).

The argument follows the small-field half of (D8) of the class (`D8SF.M_eq`). On the torus
`𝕋_ℓ`, `ℓ = N₁ L^{m₁} L^k`, the set `A` of the quarter box is a polymer of `𝒟_j` iff it is a polymer
of `ℤ^d` (`isPolyDom_toTorus_iff`), a condition that does not mention the torus; then it is the lift
`Ypoly j X'` of the set `X'` of its `j`-blocks, which does not wind around either torus
(`Ypoly_eq_toTorus_image`, `nonWind_blocks`). By locality of the terms the source `g` may be replaced
by its pullback `pullFld j g` (`inhObs_image_eq`), and `D8SF.M_eq` identifies the terms of the two
tori one by one; the sum over the sites of the polymer is reindexed by the injective map
`toTorus` on the quarter box.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2

section Torus

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

open Classical in
/-- **The inherited activities on the image of a set of the quarter box**, with a source of the form
`z ↦ G(centred representative of z)`: zero unless `A` is a polymer of `ℤ^d`, and then the sum over
`A` of the terms `ℳ^{(j)}(a, Ypoly j X'; h, h, pullFld j G)` of the lift of the set `X'` of blocks of
`A`. The torus enters through the index `N₁` of the terms only. -/
theorem inhObs_image_eq {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ}
    (hsf : SFFlat2 P6 k0 sf) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N)) {N₁ : ℕ} [NeZero N₁]
    (hN : L ^ m₀ ∣ N₁) (hM8 : 8 ≤ L ^ (m₀ + m₁)) (j : ℕ) {A : Finset (Fin d → ℤ)}
    (hA : ∀ y ∈ A, QBox d (N₁ * L ^ m₁ * L ^ k) y) (G : (Fin d → ℤ) → Fin N → ℂ) :
    inhObs sf m₀ hv (N₁ * L ^ m₁ * L ^ k) j (A.image (toTorus L N₁ m₁ k))
        (fun z => G fun μ => ZMod.valMinAbs (z μ)) =
      if 1 ≤ j ∧ j ≤ k ∧ PolyZ L m₀ m₁ j (A : Set (Fin d → ℤ)) then
        ∑ a ∈ A, ∑ i, G a i * (sf.Tm N₁).M j (toTorus L N₁ m₁ k a)
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (A.image (blockOf L j)))
          (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) (pullFld j G) i
      else 0 := by
  obtain ⟨_, hρsf⟩ := hsf.torus
  have hloc := (hρsf N₁).terms.localM
  rw [inhObs_eq_explicit, Finset.coe_image]
  by_cases hc : 1 ≤ j ∧ j ≤ k ∧ PolyZ L m₀ m₁ j (A : Set (Fin d → ℤ))
  · have hpd : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
        (toTorus L N₁ m₁ k '' (A : Set (Fin d → ℤ))) :=
      (isPolyDom_toTorus_iff hc.2.1 hN hM8 hA).2 hc.2.2
    rw [ite_eq_left ⟨hc.1, hc.2.1, hpd⟩, ite_eq_left hc]
    have hjk := hc.2.1
    have hR := eight_le_R (k := k) (j := j) hN hM8
    have hℓ : 2 ≤ N₁ * L ^ m₁ * L ^ k := by
      rw [ell_eq hjk]
      have := Nat.one_le_pow j L (NeZero.pos L)
      nlinarith
    have hY := Ypoly_eq_toTorus_image hjk hA hR hc.2.2
    rw [Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_image (fun x hx y hy hxy => toTorus_inj_of_qbox hℓ (hA x hx) (hA y hy) hxy)]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun i _ => ?_
    have hga : (G fun μ => ZMod.valMinAbs (toTorus L N₁ m₁ k a μ)) = G a :=
      congrArg G (funext fun μ => valMinAbs_toTorus hℓ (hA a ha) μ)
    rw [hga, ← hY]
    congr 1
    refine congrFun (hloc j (toTorus L N₁ m₁ k a) _ _ _ _ _ _ _ fun z hz => ⟨rfl, rfl, ?_⟩) i
    have hz' : z ∈ toTorus L N₁ m₁ k '' (A : Set (Fin d → ℤ)) := hY ▸ hz
    obtain ⟨a', ha', rfl⟩ := hz'
    have hfl := fineLift_toTorus (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) hjk a' (fun μ => by
      have := zSmall_blocks hjk hA hR (blockOf L j a') (Finset.mem_image.2 ⟨a', ha', rfl⟩) μ
      simp only [blockOf] at this ⊢
      push_cast at this ⊢
      omega)
    have hg : (G fun μ => ZMod.valMinAbs (toTorus L N₁ m₁ k a' μ)) = G a' :=
      congrArg G (funext fun μ => valMinAbs_toTorus hℓ (hA a' ha') μ)
    simp only [pullFld, hfl, hg]
  · have : ¬ (1 ≤ j ∧ j ≤ k ∧ IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
        (toTorus L N₁ m₁ k '' (A : Set (Fin d → ℤ)))) := fun h =>
      hc ⟨h.1, h.2.1, (isPolyDom_toTorus_iff h.2.1 hN hM8 hA).1 h.2.2⟩
    rw [ite_eq_right this, ite_eq_right hc]

/-- **The inherited activities agree on the images of a set of the quarter box of two tori** with a
source of the form `z ↦ G(centred representative of z)`: the small-field half of (D8) of the class
(`D8SF.M_eq`) for the terms `ℳ^{(j)}`. -/
theorem inhObs_image_agree {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ}
    (hsf : SFFlat2 P6 k0 sf) (m₀ : ℕ) (hd8 : D8SF m₀ sf) (hv : EuclideanSpace ℝ (Fin N))
    {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (hN₁ : L ^ m₀ ∣ N₁) (hN₂ : L ^ m₀ ∣ N₂)
    (hM8 : 8 ≤ L ^ (m₀ + m₁)) (j : ℕ) {A : Finset (Fin d → ℤ)}
    (hA₁ : ∀ y ∈ A, QBox d (N₁ * L ^ m₁ * L ^ k) y)
    (hA₂ : ∀ y ∈ A, QBox d (N₂ * L ^ m₁ * L ^ k) y) (G : (Fin d → ℤ) → Fin N → ℂ) :
    inhObs sf m₀ hv (N₁ * L ^ m₁ * L ^ k) j (A.image (toTorus L N₁ m₁ k))
        (fun z => G fun μ => ZMod.valMinAbs (z μ)) =
      inhObs sf m₀ hv (N₂ * L ^ m₁ * L ^ k) j (A.image (toTorus L N₂ m₁ k))
        (fun z => G fun μ => ZMod.valMinAbs (z μ)) := by
  rw [inhObs_image_eq hsf m₀ hv hN₁ hM8 j hA₁ G, inhObs_image_eq hsf m₀ hv hN₂ hM8 j hA₂ G]
  by_cases hc : 1 ≤ j ∧ j ≤ k ∧ PolyZ L m₀ m₁ j (A : Set (Fin d → ℤ))
  · rw [ite_eq_left hc, ite_eq_left hc]
    have hjk := hc.2.1
    have hR₁ := eight_le_R (k := k) (j := j) hN₁ hM8
    have hR₂ := eight_le_R (k := k) (j := j) hN₂ hM8
    have hp₁ := (isPolyDom_toTorus_iff hjk hN₁ hM8 hA₁).2 hc.2.2
    have hp₂ := (isPolyDom_toTorus_iff hjk hN₂ hM8 hA₂).2 hc.2.2
    rw [← Ypoly_eq_toTorus_image hjk hA₁ hR₁ hc.2.2] at hp₁
    rw [← Ypoly_eq_toTorus_image hjk hA₂ hR₂ hc.2.2] at hp₂
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    have := congrFun (hd8.M_eq j hc.1 hjk a (A.image (blockOf L j)) (fun _ => hC hv)
      (fun _ => hC hv) G N₁ N₂ (nonWind_blocks hjk hA₁ hR₁) (nonWind_blocks hjk hA₂ hR₂)
      hp₁ hp₂) i
    exact congrArg (fun t => G a i * t) this
  · rw [ite_eq_right hc, ite_eq_right hc]

end Torus

section Assembly

/-- An admissible torus `M L^{k_f+1} ∣ ℓ` has the form `ℓ = N₁ L^{m₁} L^k` with `L^{m₀} ∣ N₁` (the
Def-6 torus index of the context of the representation), for `M = L^{m₀+m₁}` and `k ≤ k_f`. -/
theorem exists_sfIdx {L m₀ m₁ k kf M ℓ : ℕ} (hM : M = L ^ (m₀ + m₁)) (hk : k ≤ kf)
    (hd : M * L ^ (kf + 1) ∣ ℓ) : ∃ N₁ : ℕ, ℓ = N₁ * L ^ m₁ * L ^ k ∧ L ^ m₀ ∣ N₁ := by
  obtain ⟨c, hc⟩ := hd
  have e1 : L ^ (kf + 1) = L ^ (kf + 1 - k) * L ^ k := by
    rw [← pow_add]
    congr 1
    omega
  refine ⟨c * L ^ m₀ * L ^ (kf + 1 - k), ?_, ⟨c * L ^ (kf + 1 - k), by ring⟩⟩
  rw [hc, hM, pow_add, e1]
  ring

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The two-torus agreement of the inherited activities** (`ActAgree`) from the small-field half
of (D8) of the class: for `M = L^{m₀+m₁}`, `8 ≤ M` and `k ≤ k_f`. -/
theorem inhObs_actAgree {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ}
    (hsf : SFFlat2 P6 k0 sf) (m₀ : ℕ) (hd8 : D8SF m₀ sf) (hv : EuclideanSpace ℝ (Fin N))
    {M kf : ℕ} (hM : M = L ^ (m₀ + m₁)) (hM8 : 8 ≤ M) (hk : k ≤ kf) :
    ActAgree d N L M kf (inhObs sf m₀ hv) := by
  intro ℓ ℓ' hnℓ hnℓ' hℓ hℓ' j a A g _ hbox
  obtain ⟨N₁, rfl, hN₁⟩ := exists_sfIdx hM hk hℓ
  obtain ⟨N₂, rfl, hN₂⟩ := exists_sfIdx hM hk hℓ'
  have : NeZero N₁ := ⟨left_ne_zero_of_mul (left_ne_zero_of_mul hnℓ.out)⟩
  have : NeZero N₂ := ⟨left_ne_zero_of_mul (left_ne_zero_of_mul hnℓ'.out)⟩
  rw [inhObs_zero, inhObs_zero, sub_zero, sub_zero]
  exact inhObs_image_agree hsf m₀ hd8 hv hN₁ hN₂ (hM ▸ hM8) j (fun y hy μ => (hbox y hy μ).1)
    (fun y hy μ => (hbox y hy μ).2) g

/-- The small-field half of (D8) of a member of `FlatRep`. -/
theorem FlatRep.d8 {d N : ℕ} {T : Typing} {P6 : Def6.Consts} {C7 : Consts7}
    {PB : BudgetConsts} {cs₀ : OpConsts} {M1 c : ℕ} {rH ϱ β ν : ℝ}
    {h : EuclideanSpace ℝ (Fin N)} {kf k : ℕ} [NeZero T.M] [NeZero T.L]
    {hM6 : T.M = T.L ^ (P6.m₀ + C7.m₁)} {hkK : k ≤ kf + 1} {R : ℕ → ℝ}
    {geo : ∀ (nK : ℕ) [NeZero nK], Geo 𝒮[d, T, β, cs₀.aKer] (sides T.L (kf + 1) nK) R T.M}
    {cs : OpConsts} {P : BudgetConsts}
    {F : RepFam 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N geo cs P k C7.m₁ ϱ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d T.L N₁ C7.m₁ k N} {vc : CorrCoef d}
    {ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]} {νk : ℝ}
    (hF : FlatRep d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k hM6 hkK R geo cs P F St vc ρ νk) :
    D8SF P6.m₀ F.sf :=
  hF.2.2.2.2.2.2.2.2.1.coherent

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **A6-2, the exact two-torus agreement of the inherited observable terms** (LFR Theorem IV.5.3
item 7 for `j ≤ k_f`; P4 (H.4); (D8), D-IV.9): `InheritedAgreeInput`. For a member of `ℛ♭_k` with a
representation `F`, `ActAgree` of `inhObs F.sf` follows from the small-field half of (D8) of the
class (`D8SF.M_eq`) and the locality of the terms (`SFFlat2`), through the quarter-box transport of
`isPolyDom_toTorus_iff`; the size `M ≥ 14` of the cubes comes from the clause `Geo` of the family. No
premise beyond `FlatRep` is needed. -/
theorem inheritedAgreeInput : InheritedAgreeInput d N T P6 C7 PB cs₀ M1 c rH ϱ := by
  intro κ _ c₉ _
  refine ⟨0, fun β _ ν _ _ h _ kf _ _ _ k _ hk ρ νk hM6 hkK R geo cs P F St vc hrep _ => ?_⟩
  have hM : 14 ≤ (T κ c₉).M := by
    have h1 := (geo 1).hc
    have h2 := (geo 1).hM
    have h3 : 1 ≤ (geo 1).M1 := Nat.pos_of_ne_zero (NeZero.ne _)
    nlinarith
  exact inhObs_actAgree hrep.sfFlat (P6 κ c₉).m₀ hrep.d8 h hM6 (by omega) hk

end Assembly

end Balaban.RootFSpine
