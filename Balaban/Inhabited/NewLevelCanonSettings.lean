/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCanonProducer
public import Balaban.Inhabited.NewLevelCanonLocal
public import Balaban.Fluctuation.HatSetGeom
public import Balaban.Fluctuation.OldTermsLiftHat
public import Balaban.Fluctuation.LocalClassDensityIrrelSuppSpec
public import Balaban.Fluctuation.LocalClassDensityIrrelAux
public import Balaban.Fluctuation.LocalClassDensityIrrelSupport
public import Balaban.SmallField.IrrelTorusSum

/-!
# The canonically indexed inherited levels with their settings

`exists_canonOldTermData`: in the regime of ruling R13 (`ClassHatCond`), from one reference
`BgSetting`/`FlSetting` (the typing data and numerics of the step) there are a system `O` of
inherited levels indexed by `AdmPairs`, the settings `OS` of its terms (`OldTermSettings`: the
`BgSetting`, `FlSetting`, the covering setups of the polymers `X ∪ □(y)`, the frozen regions, the
optimal trees, the analyticity of the background fields) and a canonical cover `F` with
`OldTermsCanonPinsAt` and `OldTermsAreIrrel`.  The generating sets are those of
`settings_family_castLocalB_hat` (`Gj = C.Tm.gs j X`, `Gk` the cast local set on the cube-index
neighbourhood of the polymer).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec
  Balaban.LargeField

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The canonically indexed inherited levels with their settings.** -/
theorem exists_canonOldTermData (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    (t : ℝ) (i₀ i₁ : Fin N) {s : ℕ} {r₀ : ℝ} (hH : ClassHatCond C s r₀)
    (hN : L ^ C.m₀ ∣ N₁) (hL : 2 ≤ L)
    {ϱ₀ ϱ₁ : ℝ} {Gk0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₀}
    {Gj0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    {cB BG κ δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    {X₀' X₁f' : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB0 : BgSetting N S.G' Gk0 Gj0 S.a₁ S.ν cB BG κ r₀ t δ₃ X₀' X₁f' j₁)
    (hF0 : FlSetting N S.G' Gk0 (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG t δ₃ Kc Cx c₂ BG₂ δ₁ δfl
      X₁f')
    (hϱ₁ : bgR0 d L ≤ ϱ₁) (hϱ₂ : bgR0 d L ≤ ϱ)
    (hs₁ : ϱ₁ ≤ Balaban.LargeField.minSep L (L ^ (m₁ + s)))
    (hs₂ : ϱ ≤ Balaban.LargeField.minSep L (L ^ (m₁ + s))) (ρ : ℝ) :
    ∃ (O : OldTermSystem S t) (OS : OldTermSettings S t O) (F : CanonCover d L N₁ m₁ k ϱ O.ϱ₁),
      OldTermsCanonPinsAt S C O F i₀ i₁ ∧ OldTermsAreIrrel S C O ∧ O.BG = BG ∧ O.κ = κ ∧
        O.BG₂ = BG₂ ∧ O.δ₁ = δ₁ ∧ O.ϱ₁ = ϱ₁ ∧ OS.cB = cB ∧ OS.r₀ = r₀ ∧ OS.δ₃ = δ₃ ∧ OS.Kc = Kc ∧
          OS.Cx = Cx ∧ OS.c₂ = c₂ ∧ OS.δfl = δfl := by
  classical
  obtain ⟨hidx', hsc, hslt, hHatC⟩ := hH
  -- the admissible pairs
  have : Fintype (AdmPairs L N₁ m₁ k d C.m₀ k) := (admPairs_finite C.m₀ k).fintype
  let ι := AdmPairs L N₁ m₁ k d C.m₀ k
  have hj1 : ∀ τ : ι, 1 ≤ τ.1.1 := fun τ => τ.2.1
  have hjk : ∀ τ : ι, τ.1.1 ≤ k := fun τ => τ.2.2.1
  have hXp : ∀ τ : ι, IsPolyDom C.m₀ τ.1.1 τ.1.2.2 := fun τ => τ.2.2.2.2.1
  have hy : ∀ τ : ι, τ.1.2.1 ∈ τ.1.2.2 := fun τ => τ.2.2.2.2.2
  have hal : ∀ τ : ι, Aligned (L ^ τ.1.1) τ.1.2.1 := fun τ => τ.2.2.2.1
  let XL : ι → Set (CTorus d L N₁ m₁ (k + 1)) := fun τ => polySet C.m₀ τ.1.1 τ.1.2.1 τ.1.2.2
  have hXLpoly : ∀ τ : ι, IsPolyDom C.m₀ τ.1.1 (XL τ) := fun τ =>
    isPolyDom_union (hXp τ) (isPolyDom_cubeAt hN ((hjk τ).trans (Nat.le_succ k)) τ.1.2.1)
      (hy τ) (mem_cubeAt τ.1.2.1)
  have hopt' := fun τ : ι => exists_optimal_chosen (hXLpoly τ)
  choose 𝒦X Wo Eo hch hconn hWo hmeet hbond using hopt'
  have hcov : ∀ τ : ι, CovSetup S.G' C.m₀ τ.1.1 (XL τ) (𝒦X τ) := fun τ =>
    covSetup_of_chosen S.hG' hN (Nat.succ_le_succ (hjk τ)) hL (hch τ)
  -- the settings of the family
  obtain ⟨N₁', hN1', hc⟩ := exists_finer_torusG (L := L) m₁ s (by
    exact (pow_dvd_pow L hslt.le).trans hN)
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, hSg, hGjeq⟩ := settings_family_castLocalB_hat
    (N₁' := N₁') (m₁' := m₁ + s) hc S.hG' hB0 hF0 S.hG hL hN (by omega)
    (fun τ : ι => τ.1.1) XL 𝒦X (fun τ => τ.1.2.2) hj1 hjk hXp
    (fun τ => Set.subset_union_left) (fun τ => union_cubeAt_subset_hatSet (hy τ)) hcov hϱ₁ hϱ₂
    hs₁ hs₂ (c₁ := L ^ s) (le_of_eq (pow_add L m₁ s)) hidx'
  have hGj : ∀ τ : ι, Gj τ = C.Tm.gs τ.1.1 τ.1.2.2 := fun τ => by
    rw [hGjeq τ]
    subst hsc
    exact (HatSpec.eq_castLocalB
      (hHatC τ.1.1 (hj1 τ) (hjk τ) τ.1.2.2 (hXp τ)) hslt hs₂ (Nat.le_succ_of_le (hjk τ)) hc).symm
  -- the decoupled fields
  have hC := flCore_of hB0 hF0
  obtain ⟨F₁, hF₁⟩ := exists_decFieldPin S hC
  obtain ⟨Sol, hSol⟩ := exists_decSolPin S hC
  have hFk := fun τ : ι => theorem72_analytic (G := Gk τ) (N := N) (a := compWeight L S.a₁)
    (ν := S.ν) (hBs τ).HBk
  choose FkL hFkan hFkeq using hFk
  -- the canonical cover
  let F : CanonCover d L N₁ m₁ k ϱ ϱ₁ :=
    { X₁fC := fun j y X => if h : (j, y, X) ∈ AdmPairs L N₁ m₁ k d C.m₀ k then X₁f ⟨_, h⟩ else ∅
      𝒦XC := fun j y X => if h : (j, y, X) ∈ AdmPairs L N₁ m₁ k d C.m₀ k then 𝒦X ⟨_, h⟩ else ∅
      GkC := fun j y X => if h : (j, y, X) ∈ AdmPairs L N₁ m₁ k d C.m₀ k then Gk ⟨_, h⟩
        else castG hc (localB 0 (Nat.zero_le _) ∅ hs₁)
      GjC := fun j y X => if h : (j, y, X) ∈ AdmPairs L N₁ m₁ k d C.m₀ k then Gj ⟨_, h⟩
        else castG hc (localB 0 (Nat.zero_le _) ∅ hs₂)
      ρC := ρ }
  let O : OldTermSystem S t :=
    { ι := ι
      fin := inferInstance
      m₀ := C.m₀
      jL := fun τ => τ.1.1
      X₁f := X₁f
      𝒦X := 𝒦X
      XL := XL
      ϱ₁ := ϱ₁
      Gk := Gk
      Gj := Gj
      Eτ := fun τ r => irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2
      F₁L := fun _ => F₁
      SolL := fun _ => Sol
      FkL := FkL
      ρ := ρ
      κ := κ
      BG := BG
      BG₂ := BG₂
      δ₁ := δ₁
      hF₁L := fun _ => hF₁
      hSolL := fun _ => hSol
      hFkL := fun τ => fun D hD => hFkeq τ D hD }
  have hdp : ∀ τ : ι, (τ.1.1, τ.1.2.1, τ.1.2.2) ∈ AdmPairs L N₁ m₁ k d C.m₀ k := fun τ => τ.2
  have hinj : ∀ τ τ' : ι, τ.1.1 = τ'.1.1 → τ.1.2.1 = τ'.1.2.1 → τ.1.2.2 = τ'.1.2.2 → τ = τ' :=
    fun τ τ' h1 h2 h3 => Subtype.ext (Prod.ext h1 (Prod.ext h2 h3))
  have hXFe : ∀ τ : ι, F.X₁fC τ.1.1 τ.1.2.1 τ.1.2.2 = X₁f τ := fun τ => by simp only [F, hdp τ, dite_true]
  have hKe : ∀ τ : ι, F.𝒦XC τ.1.1 τ.1.2.1 τ.1.2.2 = 𝒦X τ := fun τ => by simp only [F, hdp τ, dite_true]
  have hGke : ∀ τ : ι, F.GkC τ.1.1 τ.1.2.1 τ.1.2.2 = Gk τ := fun τ => by simp only [F, hdp τ, dite_true]
  have hGje : ∀ τ : ι, F.GjC τ.1.1 τ.1.2.1 τ.1.2.2 = Gj τ := fun τ => by simp only [F, hdp τ, dite_true]
  let OS : OldTermSettings S t O :=
    { cB := cB, r₀ := r₀, δ₃ := δ₃, Kc := Kc, Cx := Cx, c₂ := c₂, δfl := δfl, X₀ := X₀
      hB := hBs, hF := hFs, hcov := hcov, hX₁ := hX₁
      hopt := fun τ => ⟨Wo τ, Eo τ, hconn τ, hWo τ, hmeet τ, hbond τ⟩
      hFkan := fun τ => hFkan τ, hN := hN }
  refine ⟨O, OS, F, ⟨rfl, fun τ => τ.1.2.1, fun τ => τ.1.2.2, fun _ _ => rfl,
    ⟨fun τ _ => τ.2, fun a _ b _ h => ?_, fun p hp => ⟨⟨p, hp⟩, Set.mem_univ _, rfl⟩⟩,
    fun τ => ⟨(hXFe τ).symm, (hKe τ).symm, (hGke τ).symm, (hGje τ).symm, rfl⟩⟩, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [Prod.mk.injEq] at h
    exact hinj a b h.1 h.2.1 h.2.2
  · exact ⟨rfl, i₀, i₁, fun τ => τ.1.2.1, fun τ => τ.1.2.2, fun _ _ => rfl,
      fun τ => ⟨hGj τ, hj1 τ, hjk τ, hal τ, hXp τ, hy τ, rfl⟩, hinj⟩

end Balaban.Inhabited
