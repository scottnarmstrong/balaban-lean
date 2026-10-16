/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GasCoreSize
public import Balaban.LargeField.Def7FineSize
public import Balaban.LargeField.R.RExtraSize

/-!
# The core gas against the modular size of the large-field class (blocker 4)

`notes/phase1/VMOD-43.md` §5b.  The gas of `Polymer/GasCoreSize.lean` is a gas on sets of active
`π_k`-cells of the region `Ω_f = d7Pull F k Ω` (`CubeB m₀ k Ω_f`), with the size `dExt`.  The
large-field class bounds its boundary terms in the fine modular size `d7SizeAt F k Ω X`
(`Def7FineSize.lean`), the real value of `dcovModE m₀ k Ω_f X_f`.

* `dExt_core_eq_d7SizeAt`: if the fine set `X_f` of a domain `X` is `Ŷ(S)` for the set `S` of
  cells of a core `T` (that is, `X_f` is `sitesOf T` together with the components of `Ω_f^c` it
  touches), `X_f` is site-connected and `d7SizeAtE ≠ ⊤`, then `dExt T = d7SizeAt F k Ω X`:
  equality, so a bound with decay in the modular size is a bound with the same decay in `dExt` of
  the core.  When `d7SizeAtE = ⊤` the real value `d7SizeAt` is `0` while `dExt` is `Mbig`, so no
  inequality holds there; the bounds of (D7) are stated only for `FineValid` domains.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Polymer Balaban.LargeField.Def7

variable {S : Setting} {n : ℕ → ℕ} {M K m₀ m₁ : ℕ} [NeZero S.L]

/-- **The size of a core is the modular size of its domain.**  The core `T` is a set of active
`π_k`-cells of the fine region `d7Pull F k Om`; if the fine set of `X` is `Ŷ(sitesOf T)`, is
site-connected and has finite modular size, then `dExt T = d7SizeAt F k Om X`. -/
theorem dExt_core_eq_d7SizeAt (F : FineSizeFrame S n M K m₀ m₁) (k : ℕ)
    (Om : Set (Torus S.d (n k)))
    (T : Finset (CubeB (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ k (d7Pull F k Om)))
    (X : Finset (Torus S.d (n k)))
    (hX : d7Pull F k (X : Set (Torus S.d (n k))) = Yhat (d7Pull F k Om) (sitesOf T))
    (hcon : SiteConnected (d7Pull F k (X : Set (Torus S.d (n k)))))
    (hfin : d7SizeAtE F k Om X ≠ ⊤) :
    dExt (d := S.d) T = d7SizeAt F k Om X := by
  have h1 : dOmega m₀ k (d7Pull F k Om) (sitesOf T) = d7SizeAtE F k Om X := by
    unfold dOmega d7SizeAtE
    rw [← hX]
    simp [hcon]
  rw [dExt_eq_toReal (by rw [h1]; exact hfin), h1]
  rfl

/-- The same for the size `d7Size` after `R`: the region is `Ω_k^post(𝔸)`. -/
theorem dExt_core_eq_d7Size {R : ℕ → ℝ} {k0 : ℕ} [∀ k, NeZero (n k)]
    (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (k : ℕ)
    (T : Finset (CubeB (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull F k (A.H.omegaPost k))))
    (X : Finset (Torus S.d (n k)))
    (hX : d7Pull F k (X : Set (Torus S.d (n k))) =
      Yhat (d7Pull F k (A.H.omegaPost k)) (sitesOf T))
    (hcon : SiteConnected (d7Pull F k (X : Set (Torus S.d (n k)))))
    (hfin : d7SizeE F A k X ≠ ⊤) :
    dExt (d := S.d) T = d7Size F A k X :=
  dExt_core_eq_d7SizeAt F k _ T X hX hcon hfin

/-- **The size of a core of a domain, after `R`, against the size before `R`.**  For a domain `X`
with `X_f = Ŷ(sitesOf T)` in `𝒟_k` of finite size, `1 ≤ k ≤ K`, the size `dExt T` of its core is
at most `d7SizePre` plus `(d L + d + 3)` per cube of the removed components meeting `X`, each
removed component having at most `(2ρ_k + 10)^d` cubes (`d7Size_le_d7SizePre_add_removed`). -/
theorem dExt_core_le_d7SizePre_add_removed {R : ℕ → ℝ} {k0 : ℕ} [∀ k, NeZero (n k)]
    (F : FineSizeFrame S n M K m₀ m₁) (A : LabHist S n R k0 K) (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) {k : ℕ} (hk : 1 ≤ k) (hkK : k ≤ K)
    (T : Finset (CubeB (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull F k (A.H.omegaPost k))))
    (X : Finset (Torus S.d (n k)))
    (hX : d7Pull F k (X : Set (Torus S.d (n k))) =
      Yhat (d7Pull F k (A.H.omegaPost k)) (sitesOf T))
    (hDj : IsDj m₀ k (d7Pull F k (X : Set (Torus S.d (n k)))))
    (hfin : d7SizeE F A k X ≠ ⊤) :
    dExt (d := S.d) T ≤ d7SizePre F A k X +
      ((S.d : ℝ) * S.L + S.d + 3) *
        (((A.H.remMeeting X).card : ℝ) * ((2 * S.rho k + 10 : ℕ) ^ S.d : ℕ)) := by
  rw [dExt_core_eq_d7Size F A k T X hX hDj.2.2 hfin]
  exact d7Size_le_d7SizePre_add_removed F A G hT hk hkK hDj

section Fibre

variable [∀ k, NeZero (n k)]

/-- Every cube of `𝕋_k` is the cube index of an aligned fine site. -/
theorem exists_cubeIdx_eq (F : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K) (q : Torus S.d (n k)) :
    ∃ b : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K, cubeIdx F k b = q := by
  have hside := fine_side_eq F hnn hkK
  have hcs : cellSide S.L m₀ m₁ k = S.L ^ k * M := by
    unfold cellSide; rw [F.hM, ← pow_add]; congr 1; ring
  have hpos : 0 < cellSide S.L m₀ m₁ k := cellSide_pos m₀ m₁ k
  have hlt : ∀ μ, (q μ).val * cellSide S.L m₀ m₁ k <
      F.N₁ * S.L ^ m₁ * S.L ^ K := by
    intro μ
    rw [hside, Nat.mul_comm (cellSide S.L m₀ m₁ k)]
    exact Nat.mul_lt_mul_of_pos_right (ZMod.val_lt (q μ)) hpos
  refine ⟨fun μ => (((q μ).val * cellSide S.L m₀ m₁ k : ℕ) : ZMod _), ?_⟩
  funext μ
  rw [cubeIdx_apply, ← hcs, ZMod.val_natCast, Nat.mod_eq_of_lt (hlt μ),
    Nat.mul_div_cancel _ hpos, ZMod.natCast_zmod_val]

/-- The fine lift of a set of cubes determines the set. -/
theorem d7Pull_injective (F : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K) :
    Function.Injective (d7Pull F (m₀ := m₀) k) := by
  intro Y Y' h
  ext q
  obtain ⟨b, rfl⟩ := exists_cubeIdx_eq F hnn hkK q
  have := congrArg (fun s => b ∈ s) h
  simpa [d7Pull_iff] using this

/-- **Fibre bound: a core determines its domain.**  Two domains whose fine sets are `Ŷ` of the
cells of the same core are equal; hence at most one label has a given core, `m_Y = m_Z = 1`
in `gas_activity_bound_core_dExt_count`. -/
theorem card_fibre_le_one {ι : Type*} [Fintype ι] (F : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
    (Om : Set (Torus S.d (n k)))
    (lab : ι → Finset (Torus S.d (n k))) (hlab : Function.Injective lab)
    (core : ι → Finset (CubeB (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ k (d7Pull F k Om)))
    (hX : ∀ i, d7Pull F k (lab i : Set (Torus S.d (n k))) =
      Yhat (d7Pull F k Om) (sitesOf (core i)))
    (T : Finset (CubeB (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ k (d7Pull F k Om))) :
    ((Finset.univ.filter (fun i => core i = T)).card : ℝ) ≤ 1 := by
  classical
  have h1 : (Finset.univ.filter (fun i => core i = T)).card ≤ 1 := by
    refine Finset.card_le_one.2 fun i hi i' hi' => ?_
    have e : core i = core i' := by
      rw [(Finset.mem_filter.1 hi).2, (Finset.mem_filter.1 hi').2]
    have : d7Pull F k (lab i : Set (Torus S.d (n k))) = d7Pull F k (lab i' : Set _) := by
      rw [hX, hX, e]
    exact hlab (Finset.coe_injective (d7Pull_injective F hnn hkK this))
  exact_mod_cast h1

end Fibre

section Instance

variable [∀ k, NeZero (n k)] {Yt Zt : Type*} [Fintype Yt] [Fintype Zt] {β : Yt → ℂ} {τ : Zt → ℂ}

open Classical in
/-- **The activity bound of the physical large-field gas, with the fibre bounds discharged.**
The instance of `gas_activity_bound_core_dExt_count` at the cells of the fine region
`d7Pull F k Om`, with `core := id`, for old terms labelled by distinct domains `labY y` and heavy
objects labelled by distinct domains `labZ z`, whose fine sets are `Ŷ` of their cores: the fibre
bounds are `m_Y = m_Z = 1` (`card_fibre_le_one`), `hN` is `F.divN₁`.  The remaining inputs are
`hB` (bound (1.35) with `3κ/2` decay in `dExt` of the core, `κ'' = 3κ/2`, `κ'' - κ' ≥ a_ent + 1`),
`hτ` (the factor (3.10) of the removed components), `hzd` (a removed core has size at most `c2`
times its number of cells; see `dExt_core_le_d7SizePre_add_removed`), and `hh`. -/
theorem gas_activity_bound_physical (F : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
    (Om : Set (Torus S.d (n k)))
    (labY : Yt → Finset (Torus S.d (n k))) (hlabY : Function.Injective labY)
    (labZ : Zt → Finset (Torus S.d (n k))) (hlabZ : Function.Injective labZ)
    {cy zs cr : _ → Finset (CubeB (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ k (d7Pull F k Om))}
    (hXY : ∀ y, d7Pull F k (labY y : Set (Torus S.d (n k))) =
      Yhat (d7Pull F k Om) (sitesOf (cy y)))
    (hXZ : ∀ z, d7Pull F k (labZ z : Set (Torus S.d (n k))) =
      Yhat (d7Pull F k Om) (sitesOf (zs z)))
    {B0 κ' κ'' c2 p h : ℝ}
    (hc2 : 0 ≤ c2) (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hp : 0 ≤ p)
    (hκ : aEnt S.d S.L + 1 ≤ κ'' - κ')
    (hz : ∀ z, (zs z).Nonempty) (hcr : ∀ z, cr z ⊆ zs z)
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * dExt (d := S.d) (cy y)))
    (hτ : ∀ z, ‖τ z‖ ≤ Real.exp (-p - h * (zs z).card))
    (hzd : ∀ z, dExt (d := S.d) (zs z) ≤ c2 * (zs z).card)
    (hh : B0 * Real.exp B0 * Real.exp (κ' * cG S.d S.L) *
        (1 * (K0 S.d S.L (aEnt S.d S.L + 1) + 1)) +
      κ' * (c2 + cG S.d S.L) + c1 S.d S.L + 3 +
      Real.log (1 * (K0 S.d S.L (aEnt S.d S.L + 1) + 1) *
        Real.exp ((aEnt S.d S.L + 1) * c2)) ≤ h)
    (X : NePoly (CubeB (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ k (d7Pull F k Om))) :
    ‖gasK cy zs cr β τ X‖ ≤
      3 * c1 S.d S.L * Real.exp (-p) * Real.exp (-(κ' - 2) * dExt (d := S.d) X.1) := by
  have := gas_activity_bound_core_dExt_count (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁)
    (K := K) (m₀ := m₀) (j := k) (Ω := d7Pull F k Om) (β := β) (τ := τ) F.divN₁ hkK id
    (cy := cy) (zs := zs) (cr := cr) (mY := 1) (mZ := 1) hc2 hB0 hκ' hκ'' hp hκ hz hcr
    (fun T => by convert card_fibre_le_one F hnn hkK Om labY hlabY cy hXY T using 3; simp)
    (fun T => by convert card_fibre_le_one F hnn hkK Om labZ hlabZ zs hXZ T using 3; simp) le_rfl hB hτ hzd hh X
  simpa using this

end Instance

end Balaban.LargeField
