/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.GsSpecStrong
public import Balaban.Fluctuation.StepObjects
public import Balaban.Background.Theorem73

/-!
# LOCAL-PAIR-AGREEMENT under `GsSpecStrong` (RAY-DOMAIN §3)

* `localPairAt_agree`: on `X` the local composed spin/source pair of `G_{j,X}` over `levelGS k`
  (`localPairAt`, `localComposedData`) is the whole-level pair `composedDataAt`;
* `localPair_bg_agree`: the two background solutions (field and multiplier) restrict to the same
  local solution on `X` (`theorem73_real` restriction identities);
* `Eloc_eq_local`, `Mloc_eq_local`, `EcompAt_eq_local`, `McompAt_eq_local`: through the locality
  clauses `LocalE`, `LocalM`, `EcompAt` and `McompAt` are the terms evaluated at the local pairs;
* `levelTerms_localE_localM_strongGS`: the hypothesis predicates are inhabited.
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Finset

variable {d L N₁ m₁ K k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The local composed datum on `G = G_{j,X}` (I-2 (6.2)): `composeData` of `G` over the top
level-`k` set `levelGS k`, the field being the background of the top datum `D`. -/
noncomputable def localComposedData (a : ℕ → ℝ) (ν : ℝ) (hk : k ≤ K)
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (hG : Precedes G (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk))
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N) :
    BgData G N :=
  composeData hG a
    (bgField (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν D) D

/-- The local composed spin/source pair on `G`, as fields on the whole torus (the fields
`Ψ`, `h̃` of `localComposedData`; defined without the `Precedes` proof). -/
noncomputable def localPairAt (a : ℕ → ℝ) (ν : ℝ) (hk : k ≤ K)
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N) :
    Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N :=
  (fun x i => composeField G
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a
      (bgField (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν D)
      D.Ψ x i,
   fun x i => by classical exact if x ∈ G.Ω 1 then D.h x i else 0)

theorem localPairAt_eq (a : ℕ → ℝ) (ν : ℝ) (hk : k ≤ K)
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (hG : Precedes G (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk))
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N) :
    localPairAt a ν hk G D = ((localComposedData a ν hk G hG D).Ψ,
      (localComposedData a ν hk G hG D).h) := rfl

/-- **Agreement of the composed pairs on `X` (local pair versus whole-level pair).**  If `G` has
the strong specification for the level-`j` polymer `X`, the local composed pair of `G` over
`levelGS k` agrees on `X` with the whole-level composite `composedDataAt` of `levelGS j`, for
every top datum `D` and every coefficient sequence. -/
theorem localPairAt_agree {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hk : k ≤ K) (a : ℕ → ℝ) (ν : ℝ)
    {X : Set (CTorus d L N₁ m₁ K)} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    (hS : GsSpecStrong j (hjk.trans hk) X G)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N)
    {z : CTorus d L N₁ m₁ K} (hz : z ∈ X) (i : Fin N) :
    (localPairAt a ν hk G D).1 z i = (composedDataAt a ν hjk hk D).Ψ z i ∧
      (localPairAt a ν hk G D).2 z i = (composedDataAt a ν hjk hk D).h z i := by
  have hzG : z ∈ G.Ω 1 := hS.subset hz
  have hzL : z ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j
      (hjk.trans hk)).Ω 1 := by simp [levelGS, hj1]
  refine ⟨?_, ?_⟩
  · show composeField G _ a _ D.Ψ z i = composeField _ _ _ _ D.Ψ z i
    rw [composeField_of_mem _ _ _ hzG, composeField_of_mem _ _ _ hzL, hS.layerEq z hz]
    rfl
  · show (if z ∈ G.Ω 1 then D.h z i else 0) = _
    simp [composedDataAt, composeData, hzG, hzL]

/-- **The two background solutions restrict to the same local solution on `X`** (Theorem 7.3,
restriction identities): for the datum `D` of `Ξ_k` in the union domain, the field `φ` and the
multiplier `α` of the composed data of `G` and of `levelGS j` agree at the sites of `X`
(both are the restrictions of the top background to `Ω₁`). -/
theorem localPair_bg_agree {j : ℕ} (hjk : j ≤ k) (hk : k ≤ K) {a₁ ν : ℝ} (ha₁ : 0 < a₁)
    (H : BgHyp d L K ϱ (compWeight L a₁) ν)
    {X : Set (CTorus d L N₁ m₁ K)} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    (hS : GsSpecStrong j (hjk.trans hk) X G) (hj1 : 1 ≤ j)
    {D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N}
    (hD : InUnionDomainR (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
      (thm73C1 d L N) ν D) {z : CTorus d L N₁ m₁ K} (hz : z ∈ X) (i : Fin N) :
    bgField G (compWeight L a₁) ν
        (localComposedData (compWeight L a₁) ν hk G (precedes_levelGS hS hjk hk) D)
        (⟨z, hS.subset hz⟩, i) =
      bgField (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j (hjk.trans hk))
        (compWeight L a₁) ν (composedDataAt (compWeight L a₁) ν hjk hk D)
        (⟨z, by simp [levelGS, hj1]⟩, i) ∧
    bgMult G (compWeight L a₁) ν
        (localComposedData (compWeight L a₁) ν hk G (precedes_levelGS hS hjk hk) D)
        ⟨z, hS.subset hz⟩ =
      bgMult (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j (hjk.trans hk))
        (compWeight L a₁) ν (composedDataAt (compWeight L a₁) ν hjk hk D)
        ⟨z, by simp [levelGS, hj1]⟩ := by
  obtain ⟨-, -, hf1, hm1⟩ := theorem73_real ha₁ H H (precedes_levelGS hS hjk hk) hD
  obtain ⟨-, -, hf2, hm2⟩ := theorem73_real ha₁ H H (levelGS_precedes_at hjk hk) hD
  refine ⟨?_, ?_⟩
  · have e1 := congrFun hf1 (⟨z, hS.subset hz⟩, i)
    have e2 := congrFun hf2 (⟨z, by simp [levelGS, hj1]⟩, i)
    exact e1.trans e2.symm
  · have e1 := congrFun hm1 ⟨z, hS.subset hz⟩
    have e2 := congrFun hm2 ⟨z, by simp [levelGS, hj1]⟩
    exact e1.trans e2.symm


section Terms

variable (m₀ : ℕ) (Tm : Terms d L N₁ m₁ K N ϱ)

/-- The locality clause `localE` of `Def6.IsSF` (H.4) [P1 (H.5)]. -/
def LocalE : Prop :=
  ∀ j y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) → Tm.E j y X Ψ h = Tm.E j y X Ψ' h'

/-- The locality clause `localM` of `Def6.IsSF` (H.4). -/
def LocalM : Prop :=
  ∀ j x X Ψ Ψ' h h' g g', (∀ z ∈ X, Ψ z = Ψ' z ∧ h z = h' z ∧ g z = g' z) →
    Tm.M j x X Ψ h g = Tm.M j x X Ψ' h' g'

/-- The strong specification for every polymer of the levels `1 ≤ j ≤ k`. -/
def StrongGS (hk : k ≤ K) : Prop :=
  ∀ j, 1 ≤ j → ∀ hjk : j ≤ k, ∀ X, IsPolyDom m₀ j X → GsSpecStrong j (hjk.trans hk) X (Tm.gs j X)

variable {m₀ Tm}

theorem Eloc_eq_local (hE : LocalE Tm) {hk : k ≤ K} (hS : StrongGS m₀ Tm hk) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (a : ℕ → ℝ) (ν : ℝ)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N)
    (y : CTorus d L N₁ m₁ K) :
    Eloc m₀ Tm j y (composedPairAt a ν hk j D).1 (composedPairAt a ν hk j D).2 =
      ∑ᶠ X ∈ polysAt m₀ j y,
        Tm.E j y X (localPairAt a ν hk (Tm.gs j X) D).1 (localPairAt a ν hk (Tm.gs j X) D).2 := by
  unfold Eloc
  refine finsum_mem_congr rfl fun X hX => hE j y X _ _ _ _ fun z hz => ?_
  have hag := fun i => localPairAt_agree hj1 hjk hk a ν (hS j hj1 hjk X hX.1) D hz i
  simp only [composedPairAt, hjk, dite_true]
  exact ⟨(funext fun i => (hag i).1).symm, (funext fun i => (hag i).2).symm⟩

theorem Mloc_eq_local (hM : LocalM Tm) {hk : k ≤ K} (hS : StrongGS m₀ Tm hk) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (a : ℕ → ℝ) (ν : ℝ)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N)
    (x : CTorus d L N₁ m₁ K) (g : Fld d L N₁ m₁ K N) :
    Mloc m₀ Tm j x (composedPairAt a ν hk j D).1 (composedPairAt a ν hk j D).2 g =
      ∑ᶠ X ∈ polysAt m₀ j x,
        Tm.M j x X (localPairAt a ν hk (Tm.gs j X) D).1 (localPairAt a ν hk (Tm.gs j X) D).2 g := by
  unfold Mloc
  refine finsum_mem_congr rfl fun X hX => hM j x X _ _ _ _ g g fun z hz => ?_
  have hag := fun i => localPairAt_agree hj1 hjk hk a ν (hS j hj1 hjk X hX.1) D hz i
  simp only [composedPairAt, hjk, dite_true]
  exact ⟨(funext fun i => (hag i).1).symm, (funext fun i => (hag i).2).symm, trivial⟩

open Classical in
/-- **`ℰ_k` is the sum of the terms evaluated at the local composed pairs**: `EcompAt` (whole-level
composite) equals the sum, over `j ≤ k`, `y` and the polymers `X ∋ y`, of `ℰ^{(j)}(y, X)` evaluated
at the local composed data of `G_{j,X}`. -/
theorem EcompAt_eq_local (hE : LocalE Tm) {hk : k ≤ K} (hS : StrongGS m₀ Tm hk) (a : ℕ → ℝ)
    (ν : ℝ)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N) :
    EcompAt m₀ Tm a ν hk D =
      ∑ j ∈ Finset.Icc 1 k,
        ∑ y ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter (Aligned (L ^ j)),
          ∑ᶠ X ∈ polysAt m₀ j y,
            Tm.E j y X (localPairAt a ν hk (Tm.gs j X) D).1
              (localPairAt a ν hk (Tm.gs j X) D).2 := by
  unfold EcompAt Edens
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mem_Icc] at hj
  exact Eloc_eq_local hE hS hj.1 hj.2 a ν D y

/-- **`ℳ_k` is the field term plus the terms evaluated at the local composed pairs.** -/
theorem McompAt_eq_local (hM : LocalM Tm) {hk : k ≤ K} (hS : StrongGS m₀ Tm hk) (a : ℕ → ℝ)
    (ν : ℝ)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N)
    (g : Fld d L N₁ m₁ K N) (x : CTorus d L N₁ m₁ K) (i : Fin N) :
    McompAt m₀ Tm a ν hk D g x i =
      svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
        (bgField (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) a ν D)
        x i +
      ∑ j ∈ Finset.Icc 1 k,
        (∑ᶠ X ∈ polysAt m₀ j x,
          Tm.M j x X (localPairAt a ν hk (Tm.gs j X) D).1 (localPairAt a ν hk (Tm.gs j X) D).2 g) i := by
  unfold McompAt
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  rw [Mloc_eq_local hM hS hj.1 hj.2 a ν D x g]


/-- The terms with `E = M = 0` and the whole-level generating sets `gs j X = levelGS j`. -/
noncomputable def levelTerms (d L N₁ m₁ K N : ℕ) [NeZero L] [NeZero N₁] (ϱ : ℝ) :
    Terms d L N₁ m₁ K N ϱ where
  E := fun _ _ _ _ _ => 0
  M := fun _ _ _ _ _ _ => 0
  gs := fun j _ => if h : j ≤ K then levelGS j h else levelGS K le_rfl

/-- **`LocalE`, `LocalM` and `StrongGS` are inhabited** (hard rule 10), for every `m₀` and every
top level `k ≤ K`. -/
theorem levelTerms_localE_localM_strongGS (m₀ : ℕ) (hk : k ≤ K) :
    LocalE (levelTerms d L N₁ m₁ K N ϱ) ∧ LocalM (levelTerms d L N₁ m₁ K N ϱ) ∧
      StrongGS m₀ (levelTerms d L N₁ m₁ K N ϱ) hk := by
  refine ⟨fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ => rfl, ?_⟩
  intro j hj1 hjk X _
  have hjK : j ≤ K := hjk.trans hk
  have : (levelTerms d L N₁ m₁ K N ϱ).gs j X = levelGS j hjK := by simp [levelTerms, hjK]
  rw [this]
  exact levelGS_strong hj1 hjK X

end Terms

end Balaban.SmallField.GsSpec
