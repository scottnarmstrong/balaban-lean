/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapIdentPair

/-!
# The gap-scale torus clause for the block-energy terms (item 24, blocker 7)

The new terms `Tnew ℓ g X` of the gap-scale step on the torus `ℓ` are the terms `evDec` of the block
energy at the sites `{x | cell x ∈ X}` of the polymer `X` of cells.

* `evDec_eq_zero_of_not_subset`: `evDec` vanishes at a set of sites that does not contain the read
  region;
* `boxMap_injective_of_le`: the box map from the smaller torus is injective;
* `hnew_of_blockEnergy`: the exact torus clause `Tnew ℓ g X = Tnew (can X) g X` (`hnew` of
  `hFclose_of_split`) for the compact supports of the quarter box, from the pair theorem
  `evDec_cellSites_blockEnergy`;
* `resum_gapScale_torus_blockEnergy`: the gap-scale torus clause (`resum_gapScale_torus_inherited`) with
  the closeness of the new terms proved, and only the closeness of the inherited terms (`hinh`) as an
  input about the terms.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background

section Zero

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}

/-- **`evDec` vanishes off the supports containing the read region.**  The families `𝒞` with
`Y[𝒞] = Y` have `Y[𝒞] ⊇ X₁`; if `X₁ ⊄ Y` there are none. -/
theorem evDec_eq_zero_of_not_subset {a₁ ν : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (Zm : Finset (unitPts Gp)) (um tm : ℂ) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ))
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (h : ¬ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ Y) :
    evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol Φ Zm um tm Y u = 0 := by
  unfold evDec evTerm
  refine Finset.sum_eq_zero fun C hC => ?_
  exfalso
  refine h ?_
  rw [hX₁]
  have h1 := (Finset.mem_filter.1 hC).2
  rw [← h1]
  exact subset_Ysites _ _

end Zero

section Inj

variable {d : ℕ}

/-- The box map from the torus of side `n` to a torus of side `n' ≥ n` is injective. -/
theorem boxMap_injective_of_le {n n' : ℕ} [NeZero n] [NeZero n'] (h : n ≤ n') :
    Function.Injective (boxMap (d := d) n n') := by
  intro x y hxy
  funext μ
  have h1 := congrFun hxy μ
  simp only [boxMap] at h1
  have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n').1 h1
  have hx := ZMod.valMinAbs_mem_Ioc (x μ)
  have hy := ZMod.valMinAbs_mem_Ioc (y μ)
  have h3 : (y μ).valMinAbs - (x μ).valMinAbs = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd h2 ?_
    rw [abs_lt]
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    have : (n : ℤ) ≤ n' := by exact_mod_cast h
    constructor <;> omega
  have : (x μ).valMinAbs = (y μ).valMinAbs := by omega
  exact ZMod.valMinAbs_inj.1 this

end Inj

section Family

open Balaban.Localization.DetUnitIncidence Balaban.Localization.DecEquiv

variable {ι G : Type*} {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {N₁ : ι → ℕ} [∀ ℓ, NeZero (N₁ ℓ)]
  {K : ι → ℕ} [∀ ℓ, NeZero (K ℓ)]

set_option hygiene false in
local notation "bm[" ℓ "," ℓ' "]" =>
  boxMap ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)) ((N₁ ℓ' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA[" ℓ "]" => levelGS (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := m₁) (k := k + 1)
  (ϱ := ϱ) (k + 1) le_rfl
set_option hygiene false in
local notation "HA[" ℓ "]" => levelGS (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := m₁) (k := k + 1)
  (ϱ := ϱ) k (Nat.le_succ k)
set_option hygiene false in
local notation "cellsOf[" ℓ "," X "]" => {x : CTorus d L (N₁ ℓ) m₁ (k + 1) |
  (fun μ => (((((x μ).val / cellSide L m₀ m₁ (k + 1) : ℕ)) : ZMod (K ℓ))).valMinAbs) ∈
    (↑X : Set (Fin d → ℤ))}

variable
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : ∀ ℓ, FlCore N (GA[ℓ]) (HA[ℓ]) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG : ∀ ℓ, IsLevel (GA[ℓ]) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : ∀ ℓ, DecParams (GA[ℓ]) × RawData d L (N₁ ℓ * L ^ m₁) (k + 1) N →
      ((GA[ℓ]).Ω 1 × Fin N → ℂ) × ((GA[ℓ]).Ω 1 → ℂ)}
    {Sol : ∀ ℓ, Dec2.DecParams (coverOf (GA[ℓ])) × Edat (HA[ℓ]) N →
      ((HA[ℓ]).Ω 1 × Fin N → ℂ) × ((HA[ℓ]).Ω 1 → ℂ)}
    (hF₁ : ∀ ℓ, ∀ (s : DecParams (GA[ℓ])) (D : BgData (GA[ℓ]) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA[ℓ]) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA[ℓ]).Ω 1 × Fin N → ℂ)
        (α : (GA[ℓ]).Ω 1 → ℂ), IsDecBg (GA[ℓ]) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ ℓ (s, rawOf D) = (φ, α))
    (hSol : ∀ ℓ, ∀ p : Dec2.DecParams (coverOf (GA[ℓ])) × Edat (HA[ℓ]) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA[ℓ]) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol ℓ p).1 = dphi (HA[ℓ]) (Dec2.decG (coverOf (GA[ℓ])) (HA[ℓ]) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA[ℓ]) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol ℓ p).2 ∧
        Dec2.DecFixed (coverOf (GA[ℓ])) (HA[ℓ]) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA[ℓ]) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol ℓ p).2 ∧
        Small (HA[ℓ]) (Sol ℓ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA[ℓ]) (Sol ℓ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA[ℓ]) (Sol ℓ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA[ℓ]).Ω 1 → ℂ, Small (HA[ℓ]) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA[ℓ])) (HA[ℓ]) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA[ℓ]) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol ℓ p).2))

variable
    {m₀ j : ℕ} (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : ∀ ℓ, L ^ m₀ ∣ N₁ ℓ)
    {Xc 𝒦X : ∀ ℓ, Set (CTorus d L (N₁ ℓ) m₁ (k + 1))}
    {X₁f : ∀ ℓ, Finset (CTorus d L (N₁ ℓ) m₁ (k + 1))}
    (hcov : ∀ ℓ, CovSetup (GA[ℓ]) m₀ j (Xc ℓ) (𝒦X ℓ))
    (hX₁ : ∀ ℓ, (↑(X₁f ℓ) : Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) = X1 (GA[ℓ]) m₀ j (𝒦X ℓ))
    (h𝒦 : ∀ ℓ, (𝒦X ℓ).Nonempty)
    {Dset : Set G} {Dat : ∀ ℓ, G → BgData (GA[ℓ]) N}
    (hD : ∀ ℓ, ∀ g ∈ Dset, XiCData (GA[ℓ]) (compWeight L a₁) ν (k + 1) 1 eps (Dat ℓ g))
    {ψh : ∀ ℓ, G → unitPts (GA[ℓ]) × Fin N → ℂ}
    (hψh : ∀ ℓ, ∀ g ∈ Dset, ∀ p, ‖ψh ℓ g p‖ ≤ cψ)
    {Zm : ∀ ℓ, Finset (unitPts (GA[ℓ]))} {um tm : ℂ}
    (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {x₀ : ∀ ℓ, CTorus d L (N₁ ℓ) m₁ (k + 1)}
    (hZ : ∀ ℓ, readSites (HA[ℓ]) k (jBlock d L (N₁ ℓ * L ^ m₁) (k + 1) (k + 1) (x₀ ℓ)) ⊆
      ↑(X₁f ℓ))
    (hBM : ∀ ℓ, BlockMargin (GA[ℓ]) (X₁f ℓ)
      (↑(blockSites d L (N₁ ℓ) m₁ (k + 1) k
        (jBlock d L (N₁ ℓ * L ^ m₁) (k + 1) (k + 1) (x₀ ℓ))) :
        Set (CTorus d L (N₁ ℓ) m₁ (k + 1))))

variable
    (hK26 : ∀ ℓ, 26 ≤ K ℓ)
    (hside : ∀ ℓ, (N₁ ℓ * L ^ m₁) * L ^ (k + 1) = cellSide L m₀ m₁ (k + 1) * K ℓ)
    (P : ι → Finset (Finset (Fin d → ℤ))) (Q : ι → Finset (Fin d → ℤ) → Prop)
    (can : Finset (Fin d → ℤ) → ι) (Wd : ι → Finset (Fin d → ℤ) → Prop)
    (hP : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs))
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
    (hcanK : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → K ℓ ≤ K (can X))
    (hcompact : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → ∀ c ∈ X, ∀ c' ∈ X, ∀ μ,
      |c μ - c' μ| ≤ (((K ℓ - 26) / 25 : ℕ) : ℤ))
    (hcoverX : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → X₁f (can X) = (X₁f ℓ).image bm[ℓ, can X])
    (hx₀c : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → x₀ (can X) = bm[ℓ, can X] (x₀ ℓ))
    (hfamD : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset →
      ∀ Ds : ℕ, Ds = cellSide L m₀ m₁ (k + 1) * ((K ℓ - 26) / 25 + 1) - 1 →
      ∀ z : Fin d → ℤ, (∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ (↑(X₁f ℓ) : Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) ∪ cellsOf[ℓ, X], ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      RawBoxAgree {w | InBox d (Ds + (Ds + 1) / 4 + 3 * L ^ (k + 1))
          ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)) w}
        (symRaw (Equiv.addRight
          (fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ m₁) * L ^ (k + 1))))) (rawOf (Dat ℓ g)))
        (symRaw (Equiv.addRight
          (fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ m₁) * L ^ (k + 1)))))
          (rawOf (Dat (can X) g))) ∧
      (∀ y, InBox d (Ds + (Ds + 1) / 4) ((N₁ ℓ * L ^ m₁) * L ^ (k + 1))
          (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)))) →
        ∀ i, ψh (can X) g (unitPt (hG (can X)) (bm[ℓ, can X]
          (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)))) -
          fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ m₁) * L ^ (k + 1)))), i) =
          ψh ℓ g (unitPt (hG ℓ) y, i)) ∧
      (∀ y, InBox d (Ds + (Ds + 1) / 4) ((N₁ ℓ * L ^ m₁) * L ^ (k + 1))
          (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)))) →
        (unitPt (hG (can X)) (bm[ℓ, can X]
          (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)))) -
          fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ m₁) * L ^ (k + 1)))) ∈ Zm (can X) ↔
          unitPt (hG ℓ) y ∈ Zm ℓ)))
    (Tnew : ι → G → Finset (Fin d → ℤ) → ℂ)
    (hTnew : ∀ ℓ g X, X ∈ P ℓ → g ∈ Dset →
      Tnew ℓ g X = evDec (X₁f ℓ) m₀ j (𝒦X ℓ) a₁ ν (hG ℓ) cc (F₁ ℓ) (Sol ℓ)
        (blockEnergyFun (GA[ℓ]) (HA[ℓ]) (compWeight L a₁) ν k
          (jBlock d L (N₁ ℓ * L ^ m₁) (k + 1) (k + 1) (x₀ ℓ))) (Zm ℓ) um tm
        cellsOf[ℓ, X] (rawOf (Dat ℓ g), ψh ℓ g))

include hC hk hG cc hcψ hMX hmar hαK hsm hF₁ hSol hd hL hm₀ hm₁ hN hcov hX₁ h𝒦 hD hψh hum hZ hBM
  hK26 hside hP hQ hcanK hcompact hcoverX hx₀c hfamD hTnew

/-- **The exact torus clause of the new terms at the gap scale** (item 24, part 1: `hnew` of
`hFclose_of_split`).  Let the new terms `Tnew ℓ g X` on the torus `ℓ` be the terms `evDec` of the
block energy of the block `x₀ ℓ` at the sites `{x | cell x ∈ X}` of the polymer `X` of cells
(`hTnew`), and let the covers, the blocks and the data of the tori `ℓ` and `can X` correspond under
the box map (`hcoverX`, `hx₀c`, `hfamD`).  For a support `X` of the quarter box of `ℓ` that is not
wide (`hcompact`: its cyclic spread is at most `(K ℓ - 26) / 25`), the terms on `ℓ` and on `can X`
are equal. -/
theorem hnew_of_blockEnergy :
    ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → ∀ g ∈ Dset, Tnew ℓ g X = Tnew (can X) g X := by
  intro ℓ X hX hQX hW g hg
  have hXc : X ∈ P (can X) := by
    obtain ⟨Y, hY, rfl⟩ := (hP ℓ _).1 hX
    have hbox : ∀ b ∈ Y, ∀ μ, (b μ).valMinAbs.natAbs ≤ K ℓ / 4 := fun b hb μ =>
      (hQ ℓ _).1 hQX _ (Finset.mem_image_of_mem _ hb) μ
    obtain ⟨Y', hY', h⟩ := quarterBox_polymer_larger (by have := hK26 ℓ; omega)
      (hcanK ℓ _ hX hQX) hY hbox
    exact (hP _ _).2 ⟨Y', hY', h.symm⟩
  have hKK : K ℓ ≤ K (can X) := hcanK ℓ X hX hQX
  have : NeZero (cellSide L m₀ m₁ (k + 1)) := ⟨(cellSide_pos (L := L) m₀ m₁ (k + 1)).ne'⟩
  have hXq : ∀ c ∈ (↑X : Set (Fin d → ℤ)), ∀ μ, (c μ).natAbs ≤ K ℓ / 4 := fun c hc μ =>
    (hQ ℓ X).1 hQX c hc μ
  have hXs := hcompact ℓ X hX hQX hW
  have hbm := boxMap_image_cellSites (d := d) (n := (N₁ ℓ * L ^ m₁) * L ^ (k + 1))
    (n' := (N₁ (can X) * L ^ m₁) * L ^ (k + 1)) (hside ℓ) (hside (can X)) (hK26 ℓ) hKK
    (↑X : Set (Fin d → ℤ)) hXq
  rw [hTnew ℓ g X hX hg, hTnew (can X) g X hXc hg]
  by_cases hsub : (↑(X₁f ℓ) : Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) ⊆ cellsOf[ℓ, X]
  · have := evDec_cellSites_blockEnergy (N₁ := N₁ ℓ) (N₁' := N₁ (can X)) (hC := hC ℓ)
      (hC' := hC (can X)) (hk := hk) (hGA := hG ℓ) (hGB := hG (can X)) (cc := cc) (hcψ := hcψ)
      (hMX := hMX) (hmar := hmar) (hαK := hαK) (hsm := hsm) (hF₁ := hF₁ ℓ) (hF₁' := hF₁ (can X))
      (hSol := hSol ℓ) (hSol' := hSol (can X)) (hd := hd) (hL := hL) (hm₀ := hm₀) (hm₁ := hm₁)
      (hN := hN ℓ) (hN' := hN (can X)) (hX' := hcoverX ℓ X hX hQX) (hcov := hcov ℓ)
      (hX₁ := hX₁ ℓ) (hcov' := hcov (can X)) (hX₁' := hX₁ (can X)) (h𝒦 := h𝒦 ℓ)
      (hD := hD ℓ g hg) (hD' := hD (can X) g hg) (hψh := hψh ℓ g hg)
      (hψh' := hψh (can X) g hg) (hum := hum)
      (hfamD := hfamD ℓ X g hX hQX hW hg _ rfl) (hZ := hZ ℓ) (hBM := hBM ℓ) (hK := hK26 ℓ)
      (hKK' := hKK) (hm := hside ℓ) (hm' := hside (can X)) (hDsdef := rfl) (hXq := hXq)
      (hXs := hXs) (hY := rfl) (hXc := hsub)
    rw [← hx₀c ℓ X hX hQX] at this
    exact this.symm
  · rw [evDec_eq_zero_of_not_subset (hG ℓ) cc (F₁ ℓ) (Sol ℓ) _ (Zm ℓ) um tm _ _ (hX₁ ℓ) hsub]
    symm
    refine evDec_eq_zero_of_not_subset (hG (can X)) cc (F₁ (can X)) (Sol (can X)) _ (Zm (can X))
      um tm _ _ (hX₁ (can X)) ?_
    intro hsub'
    refine hsub fun x hx => ?_
    have h1 : bm[ℓ, can X] x ∈ (↑(X₁f (can X)) : Set (CTorus d L (N₁ (can X)) m₁ (k + 1))) := by
      rw [hcoverX ℓ X hX hQX]
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hx))
    have h2 := hsub' h1
    rw [← hbm] at h2
    obtain ⟨y, hy, hyx⟩ := h2
    have hn : (N₁ ℓ * L ^ m₁) * L ^ (k + 1) ≤ (N₁ (can X) * L ^ m₁) * L ^ (k + 1) := by
      rw [hside ℓ, hside (can X)]; exact Nat.mul_le_mul_left _ hKK
    rw [← boxMap_injective_of_le hn hyx]
    exact hy

end Family

end Balaban.Polymer.TwoTorusStep
