module

public import Balaban.LargeField.Operators.StepData
public import Balaban.LargeField.Operators.DomainGeom
public import Balaban.LargeField.Operators.AncVars
public import Balaban.Background.BlockGeometry

/-!
# The domain identity (Part II, first step of the proof of Lemma II.5.13)

`χ^dom_{k+1}(Z') = χ^new_k(Z') ∏_{Y ∈ Anc_k(Z')} χ^dom_k(Y)` (`chiDomAt_succ_iff`), with the
output of the old part `Y` the large-field variable `ψ_k` of `Z'` on `V_Y` (`ancOut`) and its
variables the restriction of those of `Z'` (`ancRestrict`).

*Source fidelity (fix of the formalization).*  The localized history of a component is the lineage
localization of the region history (Definition I.4.4, Lemma I.3.9): its domains `Ω_j` contain the
complement of the component.  The multiscale field of Definition II.3.4 and the sets `Ω^∼_j` of
(1.24) are read with these domains (`lhOmega`, `lhOmegaSim`; Variables.lean for the field), so the
output variables `ψ_k` on `V_Y ∖ Y` (parameters of the operator of `Y`, proof of Lemma II.5.13 (3))
enter the conditions at the boundary cubes of `Y`.  Second-family conditions are indexed by
`1 ≤ j` (Definition II.3.4), which also makes the identity true at `k = 0`.

*Proof.*  Near an old part `Y` (cubes of `𝕋_k` within `1` of `Y`) the two localized region
histories (`Y`, `Z'`) have the same `Ω_i`, `i ≤ k` inside `Y`; outside `Y` both contain the cube
(it is not in `Z_k`, components being `ω_k`-separated, `near_cases`), and neither has `Ω_i`, `i > k`
(`fine_far`, Lemma I.3.5 (f)): so the layers of the generating sets coincide (`near_layer_iff`,
`genBlocksIn_eq`) and the multiscale fields coincide (`msField_anc`), as do the sets `Ω^∼_i`
(`sim_iff`).  Cubes of the lineage of `Z'` belong to a unique old part, and cubes outside
`Z_k` are in `Ω^∼` (`mem_sim_of_not_lin`), which gives `dom1_iff`, `dom2_iff`, `dom3_iff`
(the conditions at scales `j < k`).  The scales `k`, `k+1` are `χ^new_k`: its blocks have layers
`≥ k` (`genBlocks_scale_ge`, `fibre_far`), where the field depends on the new variables only
(`msField_new`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section Identity

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- The generating set `𝔹_K` of the localized history of a component (the one in `ChiDomAt`). -/
noncomputable abbrev genOf (geo : Geo S n R M) {H : RegionHistory S n R k0 K} {k : ℕ}
    (Z : H.Comp k) : GeneratingSet S.d S.L (M * n K) K ((S.L : ℝ) * M * S.Rb) :=
  (H.locRH k Z).histGen (M := M) (K' := K) le_rfl (locRH_rem k Z) H.F.ok.two_le_L (fun j _ _ => geo.hRlow j)

theorem mem_genOf_succ (geo : Geo S n R M) {H : RegionHistory S n R k0 K} {k : ℕ} (Z : H.Comp k)
    (i : ℕ) (x : Torus S.d (M * n K * S.L ^ K)) :
    x ∈ (genOf (K := K) geo Z).Ω (i + 1) ↔
      i + 1 ≤ K ∧ cubeMap n S.L M K (i + 1) x ∈ ((H.locRH k Z).step i).Omega :=
  (H.locRH k Z).mem_histGen (M := M) (K' := K) le_rfl (locRH_rem k Z) H.F.ok.two_le_L
    (fun j _ _ => geo.hRlow j) (i + 1) x

theorem le_of_mem_genOf (geo : Geo S n R M) {H : RegionHistory S n R k0 K} {k : ℕ} (Z : H.Comp k)
    {i : ℕ} {x : Torus S.d (M * n K * S.L ^ K)} (h : x ∈ (genOf (K := K) geo Z).Ω i) : i ≤ K :=
  ((H.locRH k Z).mem_histGen (M := M) (K' := K) le_rfl (locRH_rem k Z) H.F.ok.two_le_L
    (fun j _ _ => geo.hRlow j) i x |>.mp h).1

section Layers

variable (geo : Geo S n R M) {H : RegionHistory S n R k0 K} {k : ℕ} (hK : k + 1 ≤ K)
  {Y : H.Comp k} {Z' : H.Comp (k + 1)} (hY : Y ∈ H.parts k Z')

include hK hY in
/-- Near an old part `Y`, no site lies in `Ω_i` for `i ≥ k + 1`, for either generating set. -/
theorem near_not_mem_Omega {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : NearPart Y (cubeMap n S.L M K k x)) {i : ℕ} (hi : k + 1 ≤ i) :
    x ∉ (genOf (K := K) geo Y).Ω i ∧ x ∉ (genOf (K := K) geo Z').Ω i := by
  have hL : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne _)
  have hnn := H.F.hnn
  obtain ⟨z, hz, hd⟩ := hx
  have hsucc : blockMap S.L (n (k + 1)) (cubeMap n S.L M K k x) = cubeMap n S.L M K (k + 1) x :=
    cubeMap_succ hnn (by omega) x
  have h1 : x ∉ (genOf (K := K) geo Y).Ω (k + 1) := by
    rw [mem_genOf_succ]
    rintro ⟨-, hO⟩
    rw [← hsucc] at hO
    have hzZ : z ∈ ((H.locRH k Y).step k).Z := by
      rw [locRH_Z Y le_rfl (by omega), lin_self]; exact hz
    have := ((H.locRH k Y).step k).fine_far hL (hnn k (by omega)) hO hzZ
    omega
  have h2 : x ∉ (genOf (K := K) geo Z').Ω (k + 1) := by
    rw [mem_genOf_succ]
    rintro ⟨-, hO⟩
    rw [← hsucc] at hO
    have hzZ : z ∈ ((H.locRH (k + 1) Z').step k).Z := by
      rw [locRH_Z Z' (by omega) (by omega)]; exact part_sub_lin hY hz
    have := ((H.locRH (k + 1) Z').step k).fine_far hL (hnn k (by omega)) hO hzZ
    omega
  constructor
  · intro hx'
    exact h1 ((genOf (K := K) geo Y).Ω_antitone (by omega) hi
      (by have := le_of_mem_genOf geo Y hx'; omega) hx')
  · intro hx'
    exact h2 ((genOf (K := K) geo Z').Ω_antitone (by omega) hi
      (by have := le_of_mem_genOf geo Z' hx'; omega) hx')

include hK hY in
/-- Near an old part `Y`, the sites of `Ω_i` (`1 ≤ i ≤ k`) are the same for the two generating
sets; outside `Y` every such `Ω_i` contains the site. -/
theorem near_mem_Omega {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : NearPart Y (cubeMap n S.L M K k x)) {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) :
    (x ∈ (genOf (K := K) geo Y).Ω i ↔ x ∈ (genOf (K := K) geo Z').Ω i) ∧
      (cubeMap n S.L M K k x ∉ Y.1 →
        x ∈ (genOf (K := K) geo Y).Ω i ∧ x ∈ (genOf (K := K) geo Z').Ω i) := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hi'k : i' < k := by omega
  rw [mem_genOf_succ, mem_genOf_succ, mem_locOmega_iff' (by omega) Y hi'k, mem_locOmega_iff' (by omega) Z' (by omega)]
  by_cases hxY : cubeMap n S.L M K k x ∈ Y.1
  · rw [mem_lin_part_iff hK hY hik hxY]
    exact ⟨Iff.rfl, fun h => absurd hxY h⟩
  · have h1 : cubeMap n S.L M K (i' + 1) x ∉
        ((H.lin (i' + 1) k Y : Finset (Torus S.d (n (i' + 1)))) : Set _) := fun h =>
      hxY (cubeMap_mem_of_lin (by omega) h)
    have h2 : cubeMap n S.L M K (i' + 1) x ∉
        ((H.lin (i' + 1) (k + 1) Z' : Finset (Torus S.d (n (i' + 1)))) : Set _) := by
      intro h
      have h3 := cubeMap_lin_coarsen hik (Nat.le_succ k) hK h
      rcases near_cases hK hY hx with h4 | h4
      · exact hxY h4
      · exact h4 h3
    exact ⟨by simp [h1, h2, show i' + 1 ≤ K by omega], fun _ =>
      ⟨⟨by omega, Or.inr h1⟩, ⟨by omega, Or.inr h2⟩⟩⟩


include hK hY in
theorem near_Omega_iff {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : NearPart Y (cubeMap n S.L M K k x)) {i : ℕ} (hi1 : 1 ≤ i) :
    x ∈ (genOf (K := K) geo Y).Ω i ↔ x ∈ (genOf (K := K) geo Z').Ω i := by
  by_cases hik : i ≤ k
  · exact (near_mem_Omega geo hK hY hx hi1 hik).1
  · have := near_not_mem_Omega geo hK hY hx (show k + 1 ≤ i by omega)
    exact ⟨fun h => absurd h this.1, fun h => absurd h this.2⟩

include hK hY in
theorem near_layer_iff {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : NearPart Y (cubeMap n S.L M K k x)) {i : ℕ} (hi1 : 1 ≤ i) :
    x ∈ (genOf (K := K) geo Y).layer i ↔ x ∈ (genOf (K := K) geo Z').layer i := by
  rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer, near_Omega_iff geo hK hY hx hi1,
    near_Omega_iff geo hK hY hx (show 1 ≤ i + 1 by omega)]

include hK hY in
theorem near_layer_le {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : NearPart Y (cubeMap n S.L M K k x)) {i : ℕ}
    (h : x ∈ (genOf (K := K) geo Y).layer i) : i ≤ k := by
  by_contra hik
  exact (near_not_mem_Omega geo hK hY hx (show k + 1 ≤ i by omega)).1
    ((genOf (K := K) geo Y).mem_layer.mp h).1

include hK hY in
/-- The block sets `𝔹_K ∩ W` of the two generating sets agree over a set of cubes `W` of `𝕋_{j'}`
all of whose sites are near `Y`. -/
theorem genBlocksIn_eq {j' : ℕ} (W : Set (Torus S.d (n j')))
    (hW : ∀ x : Torus S.d (M * n K * S.L ^ K), cubeMap n S.L M K j' x ∈ W →
      NearPart Y (cubeMap n S.L M K k x)) :
    genBlocksIn (genOf (K := K) geo Y) j' W = genBlocksIn (genOf (K := K) geo Z') j' W := by
  ext b
  constructor
  · rintro ⟨h1, h2, x, hxl, hxb, hxW⟩
    exact ⟨h1, h2, x, (near_layer_iff geo hK hY (hW x hxW) h1).mp hxl, hxb, hxW⟩
  · rintro ⟨h1, h2, x, hxl, hxb, hxW⟩
    exact ⟨h1, h2, x, (near_layer_iff geo hK hY (hW x hxW) h1).mpr hxl, hxb, hxW⟩


end Layers

/-! ### Variables of the old parts inside those of the component -/

section Fields

variable {H : RegionHistory S n R k0 K} {k : ℕ}

/-- Typing data of the variable sets: the integrated variables `A'` of `Z'` are the new variables
and the images of the integrated variables `A_Y` of the old parts (`preVars`). -/
structure AncCover (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (AY : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → Set (InternalVars (H.localHistory M K k Y) k))
    (A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))) : Prop where
  new : newVars (H.localHistory M K (k + 1) Z') k ⊆ A'
  anc : ∀ (Y : H.Comp k) (hY : Y ∈ H.parts k Z'), ∀ q ∈ AY Y hY, ancInc hK hY q ∈ A'
  cov : ∀ p ∈ A', p ∉ newVars (H.localHistory M K (k + 1) Z') k →
    ∃ (Y : H.Comp k) (hY : Y ∈ H.parts k Z') (q : InternalVars (H.localHistory M K k Y) k),
      q ∈ AY Y hY ∧ ancInc hK hY q = p

variable (hK : k + 1 ≤ K) {Z' : H.Comp (k + 1)}
  {AY : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → Set (InternalVars (H.localHistory M K k Y) k)}
  {A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
  (cov : AncCover hK Z' AY A') {Y : H.Comp k} (hY : Y ∈ H.parts k Z')

include cov in
theorem read_exists_iff (κ : VarKind) {j : ℕ} (hj : j < k) {z : BlockAt S n M K j}
    (hz : BlockSub (S := S) (n := n) (M := M) (K := K) j z
      (fineSet (S := S) (n := n) M K k (Y.1 : Set (Torus S.d (n k))))) :
    (∃ (hj : j < k) (hb : BlockSub (S := S) (n := n) (M := M) (K := K) j z
        (varSet (H.localHistory M K k Y) j κ)),
      mkVar (H.localHistory M K k Y) k j κ z hj hb ∈ AY Y hY) ↔
    (∃ (hj' : j < k + 1) (hb' : BlockSub (S := S) (n := n) (M := M) (K := K) j z
        (varSet (H.localHistory M K (k + 1) Z') j κ)),
      mkVar (H.localHistory M K (k + 1) Z') (k + 1) j κ z hj' hb' ∈ A') := by
  constructor
  · rintro ⟨hj0, hb, hm⟩
    exact ⟨Nat.lt_succ_of_lt hj0, ancInc_mem hK hY (mkVar (H.localHistory M K k Y) k j κ z hj0 hb),
      cov.anc Y hY _ hm⟩
  · rintro ⟨hj', hb', hm⟩
    have hnn : mkVar (H.localHistory M K (k + 1) Z') (k + 1) j κ z hj' hb' ∉
        newVars (H.localHistory M K (k + 1) Z') k := fun h => by
      have : j = k := h
      omega
    obtain ⟨Y', hY', q, hq, hqp⟩ := cov.cov _ hm hnn
    obtain ⟨⟨⟨jq, hjq⟩, κq, zq⟩, hbq⟩ := q
    have h1 : (⟨Fin.castSucc ⟨jq, hjq⟩, κq, zq⟩ :
        Σ i : Fin (k + 1), VarKind × BlockAt S n M K i) = ⟨⟨j, hj'⟩, κ, z⟩ :=
      congrArg Subtype.val hqp
    obtain ⟨he1, he2⟩ := Sigma.mk.inj_iff.mp h1
    have e1 : jq = j := congrArg Fin.val he1
    subst e1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq he2)
    have hYY : Y' = Y := by
      refine RegionHistory.comp_eq_of_block_sub (M := M) (K := K) hj.le (by omega) ?_ hz
      intro x0 hx0
      exact varSet_sub_fineSet Y' jq κq (hbq x0 hx0)
    subst hYY
    exact ⟨hjq, hbq, hq⟩


theorem toEuc_eq_of_val_eq {a : LocalHistory S n M K} {m : ℕ} {A : Set (InternalVars a m)}
    (x : SubCfg N a m A) (p1 p2 : A) (h : p1.1 = p2.1) :
    VarVal.toEuc (x p1) = VarVal.toEuc (x p2) := by
  obtain rfl : p1 = p2 := Subtype.ext h
  rfl

include cov in
theorem subVarField_anc (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A') {j : ℕ}
    (hj : j < k) {z : BlockAt S n M K j}
    (hz : BlockSub (S := S) (n := n) (M := M) (K := K) j z
      (fineSet (S := S) (n := n) M K k (Y.1 : Set (Torus S.d (n k))))) :
    subVarField N (ancRestrict hK hY (cov.anc Y hY) x) j z = subVarField N x j z := by
  classical
  unfold subVarField
  by_cases hP : ∃ (hj : j < k) (hb : BlockSub (S := S) (n := n) (M := M) (K := K) j z
        (varSet (H.localHistory M K k Y) j .large)),
      mkVar (H.localHistory M K k Y) k j .large z hj hb ∈ AY Y hY
  · have hP' := (read_exists_iff hK cov hY .large hj hz).mp hP
    simp only [hP, hP', ↓reduceDIte]
    exact toEuc_eq_of_val_eq x ⟨ancInc hK hY _, _⟩ ⟨_, _⟩ rfl
  · have hP' : ¬ ∃ (hj' : j < k + 1) (hb' : BlockSub (S := S) (n := n) (M := M) (K := K) j z
        (varSet (H.localHistory M K (k + 1) Z') j .large)),
      mkVar (H.localHistory M K (k + 1) Z') (k + 1) j .large z hj' hb' ∈ A' := fun h =>
      hP ((read_exists_iff hK cov hY .large hj hz).mpr h)
    simp only [hP, hP', ↓reduceDIte]

include cov in
theorem subFluctVarField_anc (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A') {j : ℕ}
    (hj : j < k) {z : BlockAt S n M K j}
    (hz : BlockSub (S := S) (n := n) (M := M) (K := K) j z
      (fineSet (S := S) (n := n) M K k (Y.1 : Set (Torus S.d (n k))))) :
    subFluctVarField N (ancRestrict hK hY (cov.anc Y hY) x) j z = subFluctVarField N x j z := by
  classical
  unfold subFluctVarField
  by_cases hP : ∃ (hj : j < k) (hb : BlockSub (S := S) (n := n) (M := M) (K := K) j z
        (varSet (H.localHistory M K k Y) j .fluct)),
      mkVar (H.localHistory M K k Y) k j .fluct z hj hb ∈ AY Y hY
  · have hP' := (read_exists_iff hK cov hY .fluct hj hz).mp hP
    simp only [hP, hP', ↓reduceDIte]
    exact toEuc_eq_of_val_eq x ⟨ancInc hK hY _, _⟩ ⟨_, _⟩ rfl
  · have hP' : ¬ ∃ (hj' : j < k + 1) (hb' : BlockSub (S := S) (n := n) (M := M) (K := K) j z
        (varSet (H.localHistory M K (k + 1) Z') j .fluct)),
      mkVar (H.localHistory M K (k + 1) Z') (k + 1) j .fluct z hj' hb' ∈ A' := fun h =>
      hP ((read_exists_iff hK cov hY .fluct hj hz).mpr h)
    simp only [hP, hP', ↓reduceDIte]


end Fields

/-- The cube of `𝕋_{j'}` containing a site determines its cube in every coarser `𝕋_k`. -/
theorem cubeMap_eq_of_cubeMap_eq {j k : ℕ} (hjk : j ≤ k) (hkK : k ≤ K)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {x x' : Torus S.d (M * n K * S.L ^ K)}
    (h : cubeMap n S.L M K j x = cubeMap n S.L M K j x') :
    cubeMap n S.L M K k x = cubeMap n S.L M K k x' := by
  induction k, hjk using Nat.le_induction with
  | base => exact h
  | succ k hjk ih =>
    rw [← cubeMap_succ hnn (by omega) x, ← cubeMap_succ hnn (by omega) x', ih (by omega)]

/-- Adjacent cubes stay adjacent under coarsening. -/
theorem supDist_cubeMap_le_one {j k : ℕ} (hjk : j ≤ k) (hkK : k ≤ K)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {x x' : Torus S.d (M * n K * S.L ^ K)}
    (h : supDist (cubeMap n S.L M K j x) (cubeMap n S.L M K j x') ≤ 1) :
    supDist (cubeMap n S.L M K k x) (cubeMap n S.L M K k x') ≤ 1 := by
  induction k, hjk using Nat.le_induction with
  | base => exact h
  | succ k hjk ih =>
    have h1 := ih (by omega)
    rw [← cubeMap_succ hnn (by omega) x, ← cubeMap_succ hnn (by omega) x']
    refine (supDist_blockMap_le (hnn k (by omega)) _ _).trans ?_
    have hL : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne _)
    calc (supDist (cubeMap n S.L M K k x) (cubeMap n S.L M K k x') + S.L - 1) / S.L
        ≤ (1 + S.L - 1) / S.L := Nat.div_le_div_right (by omega)
      _ = 1 := by rw [show 1 + S.L - 1 = S.L by omega, Nat.div_self hL]


/-! ### The multiscale field of an old part and of the component agree near the part -/

section FieldAgree

variable {H : RegionHistory S n R k0 K} {k : ℕ} (geo : Geo S n R M) (hK : k + 1 ≤ K)
  {Z' : H.Comp (k + 1)}
  {AY : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → Set (InternalVars (H.localHistory M K k Y) k)}
  {A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
  (cov : AncCover hK Z' AY A') {Y : H.Comp k} (hY : Y ∈ H.parts k Z')

/-- Two sites of the same `j`-block (`j ≤ k ≤ K`) have the same cube of `𝕋_k`. -/
theorem cubeMap_eq_of_jBlock_eq {j k : ℕ} (hjk : j ≤ k) (hkK : k ≤ K)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {x x' : Torus S.d (M * n K * S.L ^ K)}
    (h : jBlock S.d S.L (M * n K) K j x = jBlock S.d S.L (M * n K) K j x') :
    cubeMap n S.L M K k x = cubeMap n S.L M K k x' := by
  have h' := Balaban.Background.jBlock_mono hjk hkK h
  rw [← cubeMap_eq_comp hnn hkK x, ← cubeMap_eq_comp hnn hkK x', h']

include hK hY in
theorem gate_iff {j : ℕ} (hjk : j ≤ k) {z : BlockAt S n M K j}
    (hin : ∀ x, jBlock S.d S.L (M * n K) K j x = z → cubeMap n S.L M K k x ∈ Y.1) :
    (j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j z
        (lhOmega (H.localHistory M K k Y) k j)) ↔
      (j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j z
        (lhOmega (H.localHistory M K (k + 1) Z') (k + 1) j)) := by
  by_cases hj0 : j = 0
  · simp [hj0]
  · simp only [hj0, false_or]
    exact ⟨fun h x hx => (agree_lhOmega hK hY (by omega) hjk (hin x hx)).mp (h x hx),
      fun h x hx => (agree_lhOmega hK hY (by omega) hjk (hin x hx)).mpr (h x hx)⟩

include hK hY in
/-- Outside the fine set of `Y` but near it, `lhOmega` holds at every site of a block of scale
`k` (for both localized histories). -/
theorem gate_outside {z : BlockAt S n M K k}
    (hout : ∀ x, jBlock S.d S.L (M * n K) K k x = z → cubeMap n S.L M K k x ∉ Y.1)
    (hnear : ∀ x, jBlock S.d S.L (M * n K) K k x = z → NearPart Y (cubeMap n S.L M K k x)) :
    (k = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) k z
        (lhOmega (H.localHistory M K k Y) k k)) ∧
      (k = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) k z
        (lhOmega (H.localHistory M K (k + 1) Z') (k + 1) k)) := by
  by_cases hk0 : k = 0
  · simp [hk0]
  refine ⟨Or.inr fun x hx => Or.inr fun h => hout x hx
      ((mem_localHistory_Z_top (M := M) (K := K) (by omega) Y x).mp h), Or.inr fun x hx => ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  by_cases hxZ : x ∈ (H.localHistory M K (k' + 1 + 1) Z').Z (k' + 1 + 1)
  · left
    have hnl : cubeMap n S.L M K (k' + 1) x ∉
        ((H.lin (k' + 1) (k' + 1 + 1) Z' : Finset (Torus S.d (n (k' + 1)))) : Set _) := by
      rcases near_cases hK hY (hnear x hx) with h | h
      · exact absurd h (hout x hx)
      · exact h
    refine ⟨?_, (mem_localHistory_Z_top (M := M) (K := K) (by omega) Z' x).mp hxZ⟩
    show cubeMap n S.L M K (k' + 1) x ∈ ((H.locRH (k' + 1 + 1) Z').step k').Omega
    exact (mem_locOmega_iff' (by omega) Z' (by omega) _).mpr (Or.inr hnl)
  · exact Or.inr hxZ


include hK hY in
/-- A block of scale `j ≤ k` near `Y` but outside its fine set carries no large-field variable of
`Z'`. -/
theorem subVarField_outside (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A') {j : ℕ}
    (hjk : j < k) {z : BlockAt S n M K j} {x0 : Torus S.d (M * n K * S.L ^ K)}
    (hx0 : jBlock S.d S.L (M * n K) K j x0 = z) (hnear : NearPart Y (cubeMap n S.L M K k x0))
    (hout : cubeMap n S.L M K k x0 ∉ Y.1) : subVarField N x j z = 0 := by
  classical
  unfold subVarField
  split_ifs with hex
  swap
  · rfl
  exfalso
  obtain ⟨hj', hb', -⟩ := hex
  have h1 : x0 ∈ (H.localHistory M K (k + 1) Z').Z (j + 1) := (hb' x0 hx0).1
  have h2 : cubeMap n S.L M K (j + 1) x0 ∈
      ((H.lin (j + 1) (k + 1) Z' : Finset (Torus S.d (n (j + 1)))) : Set _) := by
    have := h1.1
    rwa [show ((H.locRH (k + 1) Z').step (j + 1)).Z = _ from locRH_Z Z' (by omega) (by omega)] at this
  have h3 := cubeMap_lin_coarsen (show j + 1 ≤ k by omega) (Nat.le_succ k) hK h2
  rcases near_cases hK hY hnear with h | h
  · exact hout h
  · exact h h3

include hK hY in
theorem subVarField_outside_Y (x : SubCfg N (H.localHistory M K k Y) k (AY Y hY)) {j : ℕ}
    {z : BlockAt S n M K j} {x0 : Torus S.d (M * n K * S.L ^ K)}
    (hx0 : jBlock S.d S.L (M * n K) K j x0 = z) (hout : cubeMap n S.L M K k x0 ∉ Y.1) :
    subVarField N x j z = 0 := by
  classical
  unfold subVarField
  split_ifs with hex
  swap
  · rfl
  exfalso
  obtain ⟨hj', hb', -⟩ := hex
  exact hout (varSet_sub_fineSet Y j .large (hb' x0 hx0))


include cov hY in
/-- **The multiscale fields agree near an old part.**  At a block of scale `j ≤ k` near `Y`, the
multiscale field of the component `Z'` (at the configuration `x` of its variables, output `o`)
equals that of the old part `Y` at the restricted configuration and the output
`ψ_k|_{V_Y}` read from `x`. -/
theorem msField_anc (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A')
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1)) {j : ℕ} (hjk : j ≤ k)
    {z : BlockAt S n M K j} {x0 : Torus S.d (M * n K * S.L ^ K)}
    (hx0 : jBlock S.d S.L (M * n K) K j x0 = z) (hnear : NearPart Y (cubeMap n S.L M K k x0)) :
    subMultiscaleField N (H.localHistory M K k Y) k (Vblk R (H.localHistory M K k Y) k)
        (ancRestrict hK hY (cov.anc Y hY) x) (ancOut Y Z' x) j z =
      subMultiscaleField N (H.localHistory M K (k + 1) Z') (k + 1)
        (Vblk R (H.localHistory M K (k + 1) Z') (k + 1)) x o j z := by
  classical
  have hnnK := H.F.hnn
  have hsame : ∀ x1, jBlock S.d S.L (M * n K) K j x1 = z →
      cubeMap n S.L M K k x1 = cubeMap n S.L M K k x0 := fun x1 hx1 =>
    cubeMap_eq_of_jBlock_eq hjk (by omega) hnnK (hx1.trans hx0.symm)
  unfold subMultiscaleField
  rcases Nat.lt_or_ge j k with hj | hj
  · -- scale `j < k`
    simp only [hj, Nat.lt_succ_of_lt hj, ↓reduceIte]
    by_cases hin : cubeMap n S.L M K k x0 ∈ Y.1
    · have hz : BlockSub (S := S) (n := n) (M := M) (K := K) j z
          (fineSet (S := S) (n := n) M K k (Y.1 : Set (Torus S.d (n k)))) := fun x1 hx1 => by
        show cubeMap n S.L M K k x1 ∈ Y.1
        rw [hsame x1 hx1]; exact hin
      have hg := gate_iff hK hY hjk (z := z) (fun x1 hx1 => by
        rw [hsame x1 hx1]; exact hin)
      by_cases hc : j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j z
          (lhOmega (H.localHistory M K k Y) k j)
      · simp only [hc, hg.mp hc, ↓reduceIte]
        exact subVarField_anc hK cov hY x hj hz
      · simp only [hc, (not_congr hg).mp hc, ↓reduceIte]
    · have h1 : subVarField N (ancRestrict hK hY (cov.anc Y hY) x) j z = 0 :=
        subVarField_outside_Y hK hY _ hx0 hin
      have h2 : subVarField N x j z = 0 := subVarField_outside hK hY x hj hx0 hnear hin
      rw [h1, h2]
      simp
  · -- scale `j = k`
    obtain rfl : j = k := le_antisymm hjk hj
    simp only [lt_irrefl, Nat.lt_succ_self, ↓reduceIte, ↓reduceDIte]
    have hbc : blockCube S n M K j z = cubeMap n S.L M K j x0 := by
      rw [← hx0]; exact cubeMap_jBlock hnnK (by omega) x0
    have hV : z ∈ Vblk R (H.localHistory M K j Y) j := by
      show blockCube S n M K j z ∈ Vcubes R (H.localHistory M K j Y) j
      rw [hbc]
      obtain ⟨z0, hz0, hd⟩ := hnear
      exact mem_nbhd.mpr ⟨z0, subset_nbhd _ _ (Zcubes_loc_top (by omega) Y hz0), hd⟩
    have hval : outField N (ancOut Y Z' x) z = subVarField N x j z := by
      unfold outField
      simp only [hV, ↓reduceDIte]
      rfl
    have hnear' : ∀ x1, jBlock S.d S.L (M * n K) K j x1 = z →
        NearPart Y (cubeMap n S.L M K j x1) := fun x1 hx1 => by
      rw [hsame x1 hx1]; exact hnear
    by_cases hin : cubeMap n S.L M K j x0 ∈ Y.1
    · have hg := gate_iff hK hY (le_refl j) (z := z) (fun x1 hx1 => by
        rw [hsame x1 hx1]; exact hin)
      by_cases hc : j = 0 ∨ BlockSub (S := S) (n := n) (M := M) (K := K) j z
          (lhOmega (H.localHistory M K j Y) j j)
      · simp only [hc, hg.mp hc, ↓reduceIte]
        exact hval
      · simp only [hc, (not_congr hg).mp hc, ↓reduceIte]
    · have hg := gate_outside hK hY (z := z) (fun x1 hx1 => by
        rw [hsame x1 hx1]; exact hin) hnear'
      simp only [hg.1, hg.2, ↓reduceIte]
      exact hval

include hK hY in
/-- Near an old part but outside its fine set, every site lies in `lhOmega` (`1 ≤ i ≤ k`), for the
localized histories of `Y` and of `Z'`. -/
theorem lhOmega_outside {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) {w : Torus S.d (M * n K * S.L ^ K)}
    (hw : NearPart Y (cubeMap n S.L M K k w)) (hout : cubeMap n S.L M K k w ∉ Y.1) :
    w ∈ lhOmega (H.localHistory M K k Y) k i ∧
      w ∈ lhOmega (H.localHistory M K (k + 1) Z') (k + 1) i := by
  refine ⟨Or.inr fun h => hout ((mem_localHistory_Z_top (M := M) (K := K) (by omega) Y w).mp h), ?_⟩
  by_cases hZ : w ∈ (H.localHistory M K (k + 1) Z').Z (k + 1)
  · left
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hnl : cubeMap n S.L M K (i' + 1) w ∉
        ((H.lin (i' + 1) (k + 1) Z' : Finset (Torus S.d (n (i' + 1)))) : Set _) := by
      intro h
      have h3 := cubeMap_lin_coarsen hik (Nat.le_succ k) hK h
      rcases near_cases hK hY hw with h4 | h4
      · exact hout h4
      · exact h4 h3
    refine ⟨?_, (mem_localHistory_Z_top (M := M) (K := K) (by omega) Z' w).mp hZ⟩
    show cubeMap n S.L M K (i' + 1) w ∈ ((H.locRH (k + 1) Z').step i').Omega
    exact (mem_locOmega_iff' (by omega) Z' (by omega) _).mpr (Or.inr hnl)
  · exact Or.inr hZ

include hK hY in
/-- `CubeSub` in `lhOmega` is the same for a cube near `Y`, for the two localized histories. -/
theorem cubeSub_lhOmega_iff {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) {c : Torus S.d (n i)}
    (hc : ∀ w, cubeMap n S.L M K i w = c → NearPart Y (cubeMap n S.L M K k w)) :
    CubeSub (S := S) (n := n) M K i c (lhOmega (H.localHistory M K k Y) k i) ↔
      CubeSub (S := S) (n := n) M K i c (lhOmega (H.localHistory M K (k + 1) Z') (k + 1) i) := by
  constructor
  · intro h w hw
    by_cases hin : cubeMap n S.L M K k w ∈ Y.1
    · exact (agree_lhOmega hK hY hi1 hik hin).mp (h w hw)
    · exact (lhOmega_outside hK hY hi1 hik (hc w hw) hin).2
  · intro h w hw
    by_cases hin : cubeMap n S.L M K k w ∈ Y.1
    · exact (agree_lhOmega hK hY hi1 hik hin).mpr (h w hw)
    · exact (lhOmega_outside hK hY hi1 hik (hc w hw) hin).1

include hK hY in
/-- **The neighbourhood `Ω^∼_i` of the localized region histories agree on cubes of `Y`.** -/
theorem sim_iff {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) {e : Torus S.d (n i)}
    (he : ∀ w, cubeMap n S.L M K i w = e → cubeMap n S.L M K k w ∈ Y.1) :
    e ∈ lhOmegaSim (H.localHistory M K k Y) k i ↔
      e ∈ lhOmegaSim (H.localHistory M K (k + 1) Z') (k + 1) i := by
  have hnn := H.F.hnn
  obtain ⟨we, hwe⟩ := exists_site_of_cube (M := M) (K := K) hnn (hik.trans (by omega)) e
  have hnear : ∀ c : Torus S.d (n i), supDist e c ≤ 1 → ∀ w, cubeMap n S.L M K i w = c →
      NearPart Y (cubeMap n S.L M K k w) := by
    intro c hc w hw
    refine ⟨cubeMap n S.L M K k we, he we hwe, ?_⟩
    refine supDist_cubeMap_le_one hik (by omega) hnn ?_
    rw [hw, hwe, supDist_comm]; exact hc
  have hk1 : i ≠ k + 1 := by omega
  have hk2 : i ≠ k + 1 + 1 := by omega
  unfold lhOmegaSim lhOmegaNb
  simp only [hk1, hk2, ↓reduceIte, mem_nbhd]
  constructor
  · rintro ⟨c, hc, hd⟩
    exact ⟨c, (cubeSub_lhOmega_iff hK hY hi1 hik (hnear c hd)).mp hc, hd⟩
  · rintro ⟨c, hc, hd⟩
    exact ⟨c, (cubeSub_lhOmega_iff hK hY hi1 hik (hnear c hd)).mpr hc, hd⟩


include hK hY in
/-- A site over a cube `y` near `Y` has its cube near `Y` (coarsening). -/
theorem near_nbhd {j' : ℕ} (hj' : j' ≤ k) (y : Torus S.d (n j'))
    (hy : ∀ w, cubeMap n S.L M K j' w = y → cubeMap n S.L M K k w ∈ Y.1)
    {x : Torus S.d (M * n K * S.L ^ K)} (hx : cubeMap n S.L M K j' x ∈ nbhd 1 {y}) :
    NearPart Y (cubeMap n S.L M K k x) := by
  have hnn := H.F.hnn
  obtain ⟨wy, hwy⟩ := exists_site_of_cube (M := M) (K := K) hnn (hj'.trans (by omega)) y
  obtain ⟨y0, hy0, hd⟩ := mem_nbhd.mp hx
  rw [Set.mem_singleton_iff] at hy0
  subst hy0
  exact ⟨cubeMap n S.L M K k wy, hy wy hwy,
    supDist_cubeMap_le_one hj' (by omega) hnn (by rw [hwy]; exact hd)⟩

theorem psiTildeMulti_congr {ψ1 ψ2 : MultiField S n M K N} {Yb : Set (BlockPt S n M K)} {δ : ℝ}
    (h : ∀ b ∈ Yb, ψ1 b.1 b.2 = ψ2 b.1 b.2) :
    PsiTildeMulti ψ1 Yb δ ↔ PsiTildeMulti ψ2 Yb δ := by
  unfold PsiTildeMulti
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb b' hb' hl ha => ?_, fun b hb => ?_⟩
    · rw [← h b hb, ← h b' hb']; exact h1 b hb b' hb' hl ha
    · rw [← h b hb]; exact h2 b hb
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb b' hb' hl ha => ?_, fun b hb => ?_⟩
    · rw [h b hb, h b' hb']; exact h1 b hb b' hb' hl ha
    · rw [h b hb]; exact h2 b hb

/-- The multiscale field of the old part `Y`, read from a configuration of `Z'`. -/
noncomputable def msY (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A') : MultiField S n M K N :=
  subMultiscaleField N (H.localHistory M K k Y) k (Vblk R (H.localHistory M K k Y) k)
    (ancRestrict hK hY (cov.anc Y hY) x) (ancOut Y Z' x)

/-- The fluctuation field of the old part `Y`, read from a configuration of `Z'`. -/
noncomputable def flY (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A') :
    MultiField S n M K N :=
  subFluctField N (H.localHistory M K k Y) k (ancRestrict hK hY (cov.anc Y hY) x)

include hK hY cov in
theorem psiTilde_gen_iff (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A')
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1)) {j' : ℕ}
    (W : Set (Torus S.d (n j')))
    (hW : ∀ x1 : Torus S.d (M * n K * S.L ^ K), cubeMap n S.L M K j' x1 ∈ W →
      NearPart Y (cubeMap n S.L M K k x1)) (δ : ℝ) :
    PsiTildeMulti (msY hK cov hY x) (genBlocksIn (genOf (K := K) geo Y) j' W) δ ↔
      PsiTildeMulti (subMultiscaleField N (H.localHistory M K (k + 1) Z') (k + 1)
        (Vblk R (H.localHistory M K (k + 1) Z') (k + 1)) x o)
        (genBlocksIn (genOf (K := K) geo Z') j' W) δ := by
  rw [genBlocksIn_eq geo hK hY W hW]
  refine psiTildeMulti_congr fun b hb => ?_
  obtain ⟨h1, h2, x0, hxl, hxb, hxW⟩ := hb
  have hxl' := (near_layer_iff geo hK hY (hW x0 hxW) h1).mpr hxl
  have hbk := near_layer_le geo hK hY (hW x0 hxW) hxl'
  exact msField_anc hK cov hY x o hbk hxb (hW x0 hxW)

include hK hY cov in
theorem psiTilde_scale_iff (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A')
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1)) {j : ℕ} (hj : j ≤ k)
    (W : Set (Torus S.d (n j)))
    (hW : ∀ x1 : Torus S.d (M * n K * S.L ^ K), cubeMap n S.L M K j x1 ∈ W →
      NearPart Y (cubeMap n S.L M K k x1)) (δ : ℝ) :
    PsiTildeMulti (msY hK cov hY x) (scaleBlocksIn j W) δ ↔
      PsiTildeMulti (subMultiscaleField N (H.localHistory M K (k + 1) Z') (k + 1)
        (Vblk R (H.localHistory M K (k + 1) Z') (k + 1)) x o) (scaleBlocksIn j W) δ := by
  refine psiTildeMulti_congr fun b hb => ?_
  obtain ⟨y, rfl, x0, hx0, hW0⟩ := hb
  exact msField_anc hK cov hY x o hj hx0 (hW x0 hW0)


include hK hY cov in
/-- The conditions (1.24), first family, for `Z'` at scale `j < k` that concern cubes of the lineage
of `Y` are those of `Y`. -/
theorem dom1_part_iff (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A')
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1)) {j : ℕ} (hj : j < k) (δ : ℝ)
    (y : Torus S.d (n (j + 1)))
    (hfine : ∀ w, cubeMap n S.L M K (j + 1) w = y → cubeMap n S.L M K k w ∈ Y.1) :
    (CubeSub (S := S) (n := n) M K (j + 1) y ((H.localHistory M K k Y).Z (j + 1)) →
      y ∈ lhOmegaSim (H.localHistory M K k Y) k (j + 1) →
        PsiTildeMulti (msY hK cov hY x) (genBlocksIn (genOf (K := K) geo Y) (j + 1) (nbhd 1 {y})) δ) ↔
    (CubeSub (S := S) (n := n) M K (j + 1) y ((H.localHistory M K (k + 1) Z').Z (j + 1)) →
      y ∈ lhOmegaSim (H.localHistory M K (k + 1) Z') (k + 1) (j + 1) →
        PsiTildeMulti (subMultiscaleField N (H.localHistory M K (k + 1) Z') (k + 1)
          (Vblk R (H.localHistory M K (k + 1) Z') (k + 1)) x o)
          (genBlocksIn (genOf (K := K) geo Z') (j + 1) (nbhd 1 {y})) δ) := by
  have hW : ∀ x1 : Torus S.d (M * n K * S.L ^ K), cubeMap n S.L M K (j + 1) x1 ∈ nbhd 1 {y} →
      NearPart Y (cubeMap n S.L M K k x1) := fun x1 hx1 => near_nbhd hK hY (by omega) y hfine hx1
  have hiff := psiTilde_gen_iff geo hK cov hY x o (nbhd 1 {y}) hW δ
  have hz : CubeSub (S := S) (n := n) M K (j + 1) y ((H.localHistory M K k Y).Z (j + 1)) ↔
      CubeSub (S := S) (n := n) M K (j + 1) y ((H.localHistory M K (k + 1) Z').Z (j + 1)) :=
    ⟨fun h w hw => (agree_Z hK hY (show j + 1 ≤ k by omega) (hfine w hw)).mp (h w hw),
      fun h w hw => (agree_Z hK hY (show j + 1 ≤ k by omega) (hfine w hw)).mpr (h w hw)⟩
  have hs := sim_iff hK hY (show 1 ≤ j + 1 by omega) (show j + 1 ≤ k by omega) hfine
  rw [hz, hs, hiff]


include hK hY cov in
/-- The conditions (1.24), second family, for `Z'` at scale `j < k` that concern cubes of `Y`
are those of `Y`. -/
theorem dom2_part_iff (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A')
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1)) {j : ℕ} (hj : j < k) (δ : ℝ)
    (y : Torus S.d (n j))
    (hfine : ∀ w, cubeMap n S.L M K j w = y → cubeMap n S.L M K k w ∈ Y.1) :
    (CubeSub (S := S) (n := n) M K j y (fineSet (S := S) (n := n) M K k (Y.1 : Set _)) →
      (∀ x1, cubeMap n S.L M K j x1 = y → x1 ∉ (H.localHistory M K k Y).Z j) →
      (∀ x1, cubeMap n S.L M K j x1 = y → cubeMap n S.L M K (j + 1) x1 ∉
        lhOmegaSim (H.localHistory M K k Y) k (j + 1)) →
        PsiTildeMulti (msY hK cov hY x) (scaleBlocksIn j (nbhd 1 {y})) δ) ↔
    (CubeSub (S := S) (n := n) M K j y (fineSet (S := S) (n := n) M K (k + 1) (Z'.1 : Set _)) →
      (∀ x1, cubeMap n S.L M K j x1 = y → x1 ∉ (H.localHistory M K (k + 1) Z').Z j) →
      (∀ x1, cubeMap n S.L M K j x1 = y → cubeMap n S.L M K (j + 1) x1 ∉
        lhOmegaSim (H.localHistory M K (k + 1) Z') (k + 1) (j + 1)) →
        PsiTildeMulti (subMultiscaleField N (H.localHistory M K (k + 1) Z') (k + 1)
          (Vblk R (H.localHistory M K (k + 1) Z') (k + 1)) x o) (scaleBlocksIn j (nbhd 1 {y})) δ) := by
  have hnn := H.F.hnn
  have hW : ∀ x1 : Torus S.d (M * n K * S.L ^ K), cubeMap n S.L M K j x1 ∈ nbhd 1 {y} →
      NearPart Y (cubeMap n S.L M K k x1) := fun x1 hx1 =>
    near_nbhd hK hY hj.le y hfine hx1
  have hiff := psiTilde_scale_iff hK cov hY x o hj.le (nbhd 1 {y}) hW δ
  have h1 : CubeSub (S := S) (n := n) M K j y (fineSet (S := S) (n := n) M K k (Y.1 : Set _)) :=
    fun w hw => hfine w hw
  have h1' : CubeSub (S := S) (n := n) M K j y
      (fineSet (S := S) (n := n) M K (k + 1) (Z'.1 : Set _)) :=
    fun w hw => part_fine_sub hK hY (hfine w hw)
  have h2 : (∀ x1, cubeMap n S.L M K j x1 = y → x1 ∉ (H.localHistory M K k Y).Z j) ↔
      (∀ x1, cubeMap n S.L M K j x1 = y → x1 ∉ (H.localHistory M K (k + 1) Z').Z j) :=
    forall_congr' fun x1 => imp_congr_right fun hx1 =>
      not_congr (agree_Z hK hY hj.le (hfine x1 hx1))
  have h3 : (∀ x1, cubeMap n S.L M K j x1 = y → cubeMap n S.L M K (j + 1) x1 ∉
        lhOmegaSim (H.localHistory M K k Y) k (j + 1)) ↔
      (∀ x1, cubeMap n S.L M K j x1 = y → cubeMap n S.L M K (j + 1) x1 ∉
        lhOmegaSim (H.localHistory M K (k + 1) Z') (k + 1) (j + 1)) :=
    forall_congr' fun x1 => imp_congr_right fun hx1 =>
      not_congr (sim_iff hK hY (show 1 ≤ j + 1 by omega) (show j + 1 ≤ k by omega) (fun w hw => by
        rw [cubeMap_eq_of_cubeMap_eq (show j + 1 ≤ k by omega) (by omega) hnn hw]
        exact hfine x1 hx1))
  rw [h2, h3, hiff]
  exact ⟨fun h _ hb hc => h h1 hb hc, fun h _ hb hc => h h1' hb hc⟩


include hK hY cov in
/-- The condition (1.25) for `Z'` at scale `j < k` on a block of the fine set of `Y` is that of
`Y`. -/
theorem dom3_part_iff (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A') {j : ℕ} (hj : j < k)
    (C : ℝ) (y : BlockAt S n M K j)
    (hfine : BlockSub (S := S) (n := n) (M := M) (K := K) j y
      (fineSet (S := S) (n := n) M K k (Y.1 : Set (Torus S.d (n k))))) :
    (BlockSub (S := S) (n := n) (M := M) (K := K) j y
        ((H.localHistory M K k Y).Omega j \ (H.localHistory M K k Y).OmegaDD j) →
      ‖flY hK cov hY x j y‖ < C) ↔
    (BlockSub (S := S) (n := n) (M := M) (K := K) j y
        ((H.localHistory M K (k + 1) Z').Omega j \ (H.localHistory M K (k + 1) Z').OmegaDD j) →
      ‖subFluctField N (H.localHistory M K (k + 1) Z') (k + 1) x j y‖ < C) := by
  have hf : flY hK cov hY x j y = subFluctField N (H.localHistory M K (k + 1) Z') (k + 1) x j y :=
    subFluctVarField_anc hK cov hY x hj hfine
  have hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y
        ((H.localHistory M K k Y).Omega j \ (H.localHistory M K k Y).OmegaDD j) ↔
      BlockSub (S := S) (n := n) (M := M) (K := K) j y
        ((H.localHistory M K (k + 1) Z').Omega j \ (H.localHistory M K (k + 1) Z').OmegaDD j) :=
    ⟨fun h w hw => ⟨(agree_Omega hK hY hj (hfine w hw)).mp (h w hw).1,
        fun h' => (h w hw).2 ((agree_OmegaDD hK hY hj (hfine w hw)).mpr h')⟩,
      fun h w hw => ⟨(agree_Omega hK hY hj (hfine w hw)).mpr (h w hw).1,
        fun h' => (h w hw).2 ((agree_OmegaDD hK hY hj (hfine w hw)).mp h')⟩⟩
  rw [hb]
  show (_ → ‖flY hK cov hY x j y‖ < C) ↔ _
  rw [hf]


end FieldAgree

section Outside

variable {H : RegionHistory S n R k0 K} {k : ℕ} (hK : k + 1 ≤ K) {Z' : H.Comp (k + 1)}

include hK in
/-- A cube of `𝕋_i` (`1 ≤ i ≤ k`) lying over a cube of `𝕋_k` outside the lineage of `Z'` is in
`Ω^∼_i` of the localized history of `Z'`. -/
theorem mem_sim_of_not_lin {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k)
    {w0 : Torus S.d (M * n K * S.L ^ K)}
    (hw0 : cubeMap n S.L M K k w0 ∉
      ((H.lin k (k + 1) Z' : Finset (Torus S.d (n k))) : Set _)) :
    cubeMap n S.L M K i w0 ∈ lhOmegaSim (H.localHistory M K (k + 1) Z') (k + 1) i := by
  have hnn := H.F.hnn
  unfold lhOmegaSim lhOmegaNb
  simp only [show ¬ (i = k + 1 + 1) by omega, ↓reduceIte]
  refine subset_nbhd 1 _ ?_
  intro w hw
  by_cases hZ : w ∈ (H.localHistory M K (k + 1) Z').Z (k + 1)
  · left
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hnl : cubeMap n S.L M K (i' + 1) w ∉
        ((H.lin (i' + 1) (k + 1) Z' : Finset (Torus S.d (n (i' + 1)))) : Set _) := by
      intro h
      have h3 := cubeMap_lin_coarsen hik (Nat.le_succ k) hK h
      rw [cubeMap_eq_of_cubeMap_eq hik (by omega) hnn hw] at h3
      exact hw0 h3
    refine ⟨?_, (mem_localHistory_Z_top (M := M) (K := K) (by omega) Z' w).mp hZ⟩
    show cubeMap n S.L M K (i' + 1) w ∈ ((H.locRH (k + 1) Z').step i').Omega
    exact (mem_locOmega_iff' (by omega) Z' (by omega) _).mpr (Or.inr hnl)
  · exact Or.inr hZ

end Outside

section NewPart

variable {H : RegionHistory S n R k0 K} {k : ℕ} (hK : k + 1 ≤ K) {Z' : H.Comp (k + 1)}
  {A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
  (hnew : newVars (H.localHistory M K (k + 1) Z') k ⊆ A')

include hnew in
theorem subVarField_new (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A')
    (z : BlockAt S n M K k) :
    subVarField N (newRestrict (H.localHistory M K (k + 1) Z') hnew x) k z =
      subVarField N x k z := by
  classical
  unfold subVarField
  by_cases hP : ∃ (hj : k < k + 1) (hb : BlockSub (S := S) (n := n) (M := M) (K := K) k z
        (varSet (H.localHistory M K (k + 1) Z') k .large)),
      mkVar (H.localHistory M K (k + 1) Z') (k + 1) k .large z hj hb ∈
        newVars (H.localHistory M K (k + 1) Z') k
  · have hP' : ∃ (hj : k < k + 1) (hb : BlockSub (S := S) (n := n) (M := M) (K := K) k z
        (varSet (H.localHistory M K (k + 1) Z') k .large)),
      mkVar (H.localHistory M K (k + 1) Z') (k + 1) k .large z hj hb ∈ A' :=
      ⟨hP.1, hP.2.1, hnew rfl⟩
    simp only [hP, hP', ↓reduceDIte]
    exact toEuc_eq_of_val_eq _ ⟨_, _⟩ ⟨_, _⟩ rfl
  · have hP' : ¬ ∃ (hj : k < k + 1) (hb : BlockSub (S := S) (n := n) (M := M) (K := K) k z
        (varSet (H.localHistory M K (k + 1) Z') k .large)),
      mkVar (H.localHistory M K (k + 1) Z') (k + 1) k .large z hj hb ∈ A' :=
      fun h => hP ⟨h.1, h.2.1, rfl⟩
    simp only [hP, hP', ↓reduceDIte]

include hnew in
theorem subFluctVarField_new (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A')
    (z : BlockAt S n M K k) :
    subFluctVarField N (newRestrict (H.localHistory M K (k + 1) Z') hnew x) k z =
      subFluctVarField N x k z := by
  classical
  unfold subFluctVarField
  by_cases hP : ∃ (hj : k < k + 1) (hb : BlockSub (S := S) (n := n) (M := M) (K := K) k z
        (varSet (H.localHistory M K (k + 1) Z') k .fluct)),
      mkVar (H.localHistory M K (k + 1) Z') (k + 1) k .fluct z hj hb ∈
        newVars (H.localHistory M K (k + 1) Z') k
  · have hP' : ∃ (hj : k < k + 1) (hb : BlockSub (S := S) (n := n) (M := M) (K := K) k z
        (varSet (H.localHistory M K (k + 1) Z') k .fluct)),
      mkVar (H.localHistory M K (k + 1) Z') (k + 1) k .fluct z hj hb ∈ A' :=
      ⟨hP.1, hP.2.1, hnew rfl⟩
    simp only [hP, hP', ↓reduceDIte]
    exact toEuc_eq_of_val_eq _ ⟨_, _⟩ ⟨_, _⟩ rfl
  · have hP' : ¬ ∃ (hj : k < k + 1) (hb : BlockSub (S := S) (n := n) (M := M) (K := K) k z
        (varSet (H.localHistory M K (k + 1) Z') k .fluct)),
      mkVar (H.localHistory M K (k + 1) Z') (k + 1) k .fluct z hj hb ∈ A' :=
      fun h => hP ⟨h.1, h.2.1, rfl⟩
    simp only [hP, hP', ↓reduceDIte]

include hnew in
/-- The multiscale field of the new variables agrees with the full field at scales `≥ k`. -/
theorem msField_new (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A')
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1)) {j : ℕ} (hj : k ≤ j)
    (z : BlockAt S n M K j) :
    subMultiscaleField N (H.localHistory M K (k + 1) Z') (k + 1)
        (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (newRestrict (H.localHistory M K (k + 1) Z') hnew x) o j z =
      subMultiscaleField N (H.localHistory M K (k + 1) Z') (k + 1)
        (Vblk R (H.localHistory M K (k + 1) Z') (k + 1)) x o j z := by
  classical
  unfold subMultiscaleField
  by_cases hjk : j = k
  · subst hjk
    simp only [Nat.lt_succ_self, ↓reduceIte]
    rw [subVarField_new hnew x z]
  · have hn1 : ¬ j < k + 1 := by omega
    simp only [hn1, ↓reduceIte]
    by_cases h1 : j = k + 1
    · subst h1
      rfl
    · simp only [h1, ↓reduceDIte]

end NewPart

section NewBlocks

variable {H : RegionHistory S n R k0 K} {k : ℕ} (geo : Geo S n R M) (hK : k + 1 ≤ K)
  (Z' : H.Comp (k + 1))

include hK in
/-- **Blocks of the new conditions have scale `≥ k`.**  A block of the generating set over the
neighbourhood of a cube of `Ω^∼_{k+1}` has layer `≥ k`: the layers `< k` stay at index distance
`≥ L(⌊R_k⌋ + 4)` from `Ω_{k+1}` (Lemma I.3.5 (f)). -/
theorem genBlocks_scale_ge {y : Torus S.d (n (k + 1))}
    (hy : y ∈ lhOmegaSim (H.localHistory M K (k + 1) Z') (k + 1) (k + 1))
    {b : BlockPt S n M K}
    (hb : b ∈ genBlocksIn (genOf (K := K) geo Z') (k + 1) (nbhd 1 {y})) : k ≤ b.1 := by
  by_contra hlt
  push Not at hlt
  have hnn := H.F.hnn
  obtain ⟨h1, h2, x, hxl, hxb, hxW⟩ := hb
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hxl' := (genOf (K := K) geo Z').mem_layer.mp hxl
  have hnk : x ∉ (genOf (K := K) geo Z').Ω (k' + 1) := fun hx =>
    hxl'.2 ((genOf (K := K) geo Z').Ω_antitone (by omega) (by omega) (by omega) hx)
  rw [mem_genOf_succ] at hnk
  have hO : cubeMap n S.L M K (k' + 1) x ∉ ((H.locRH (k' + 1 + 1) Z').step k').Omega :=
    fun h => hnk ⟨by omega, h⟩
  have hZ := ((H.locRH (k' + 1 + 1) Z').toSeq (K' := K) le_rfl (locRH_rem (k' + 1 + 1) Z')).OmegaAt_compl_subset_Z
    k' hO
  have hz0 : cubeMap n S.L M K (k' + 1) x ∈
      ((H.lin (k' + 1) (k' + 1 + 1) Z' : Finset (Torus S.d (n (k' + 1)))) : Set _) := by
    have : cubeMap n S.L M K (k' + 1) x ∈ ((H.locRH (k' + 1 + 1) Z').step (k' + 1)).Z := hZ
    rwa [locRH_Z Z' (by omega) (by omega)] at this
  unfold lhOmegaSim lhOmegaNb at hy
  simp only [show ¬ (k' + 1 + 1 = k' + 1 + 1 + 1) by omega, ↓reduceIte, mem_nbhd] at hy
  obtain ⟨c, hc, hyc⟩ := hy
  obtain ⟨y0, hy0, hd⟩ := mem_nbhd.mp hxW
  rw [Set.mem_singleton_iff] at hy0
  subst hy0
  have hbm : blockMap S.L (n (k' + 1 + 1)) (cubeMap n S.L M K (k' + 1) x) =
      cubeMap n S.L M K (k' + 1 + 1) x := cubeMap_succ hnn (by omega) x
  have hdc : supDist (blockMap S.L (n (k' + 1 + 1)) (cubeMap n S.L M K (k' + 1) x)) c ≤ 2 := by
    rw [hbm]
    have := supDist_triangle (cubeMap n S.L M K (k' + 1 + 1) x) y0 c
    omega
  obtain ⟨hcZ, hcO⟩ := fibre_far (M := M) hK Z' hz0 hdc
  obtain ⟨w, hw⟩ := exists_site_of_cube (M := M) (K := K) hnn hK c
  rcases hc w hw with h | h
  · have h' : cubeMap n S.L M K (k' + 1 + 1) w ∈ ((H.locRH (k' + 1 + 1) Z').step (k' + 1)).Omega :=
      h.1
    exact hcO (by rwa [hw] at h')
  · exact h ((mem_localHistory_Z_top (M := M) (K := K) (by omega) Z' w).mpr (by rw [hw]; exact hcZ))

end NewBlocks

section Aggregate

variable {H : RegionHistory S n R k0 K} {k : ℕ} (geo : Geo S n R M) (hK : k + 1 ≤ K)
  {Z' : H.Comp (k + 1)}
  {AY : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → Set (InternalVars (H.localHistory M K k Y) k)}
  {A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
  (cov : AncCover hK Z' AY A')

include cov in
/-- (1.24), first family, at scales `j < k`: the conditions of `Z'` are those of its old parts. -/
theorem dom1_iff (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A')
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1)) (δ : ℕ → ℝ) :
    (∀ j, j < k → ∀ y : Torus S.d (n (j + 1)),
      CubeSub (S := S) (n := n) M K (j + 1) y ((H.localHistory M K (k + 1) Z').Z (j + 1)) →
      y ∈ lhOmegaSim (H.localHistory M K (k + 1) Z') (k + 1) (j + 1) →
        PsiTildeMulti (subMultiscaleField N (H.localHistory M K (k + 1) Z') (k + 1)
          (Vblk R (H.localHistory M K (k + 1) Z') (k + 1)) x o)
          (genBlocksIn (genOf (K := K) geo Z') (j + 1) (nbhd 1 {y})) (3 * S.d * S.L * δ j)) ↔
    (∀ (Y : H.Comp k) (hY : Y ∈ H.parts k Z'), ∀ j, j < k → ∀ y : Torus S.d (n (j + 1)),
      CubeSub (S := S) (n := n) M K (j + 1) y ((H.localHistory M K k Y).Z (j + 1)) →
      y ∈ lhOmegaSim (H.localHistory M K k Y) k (j + 1) →
        PsiTildeMulti (msY hK cov hY x) (genBlocksIn (genOf (K := K) geo Y) (j + 1) (nbhd 1 {y}))
          (3 * S.d * S.L * δ j)) := by
  have hnn := H.F.hnn
  constructor
  · intro h Y hY j hj y hz hs
    have hfine : ∀ w, cubeMap n S.L M K (j + 1) w = y → cubeMap n S.L M K k w ∈ Y.1 :=
      fun w hw => (hz w hw).2
    exact (dom1_part_iff geo hK cov hY x o hj _ y hfine).mpr (h j hj y) hz hs
  · intro h j hj y hz hs
    obtain ⟨w0, hw0⟩ := exists_site_of_cube (M := M) (K := K) hnn (show j + 1 ≤ K by omega) y
    have h1 := cubeMap_mem_lin_of_mem_Z (show j + 1 ≤ k + 1 by omega) (by omega) (hz w0 hw0)
    have h2 := cubeMap_lin_coarsen (show j + 1 ≤ k by omega) (Nat.le_succ k) hK h1
    obtain ⟨Y, hY, hwY⟩ := exists_part_of_mem_lin h2
    have hfine : ∀ w, cubeMap n S.L M K (j + 1) w = y → cubeMap n S.L M K k w ∈ Y.1 := by
      intro w hw
      rw [cubeMap_eq_of_cubeMap_eq (show j + 1 ≤ k by omega) (by omega) hnn (hw.trans hw0.symm)]
      exact hwY
    exact (dom1_part_iff geo hK cov hY x o hj _ y hfine).mp (h Y hY j hj y) hz hs

include cov in
/-- (1.24), second family, at scales `1 ≤ j < k`: the conditions of `Z'` are those of its old
parts (the scale `j = k` of an old part is void: its cubes lie in `Z_k`). -/
theorem dom2_iff (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A')
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1)) (δ : ℕ → ℝ) :
    (∀ j, 1 ≤ j → j < k → ∀ y : Torus S.d (n j),
      CubeSub (S := S) (n := n) M K j y (fineSet (S := S) (n := n) M K (k + 1) (Z'.1 : Set _)) →
      (∀ x1, cubeMap n S.L M K j x1 = y → x1 ∉ (H.localHistory M K (k + 1) Z').Z j) →
      (∀ x1, cubeMap n S.L M K j x1 = y → cubeMap n S.L M K (j + 1) x1 ∉
        lhOmegaSim (H.localHistory M K (k + 1) Z') (k + 1) (j + 1)) →
        PsiTildeMulti (subMultiscaleField N (H.localHistory M K (k + 1) Z') (k + 1)
          (Vblk R (H.localHistory M K (k + 1) Z') (k + 1)) x o) (scaleBlocksIn j (nbhd 1 {y}))
          (3 * δ j)) ↔
    (∀ (Y : H.Comp k) (hY : Y ∈ H.parts k Z'), ∀ j, 1 ≤ j → j ≤ k → ∀ y : Torus S.d (n j),
      CubeSub (S := S) (n := n) M K j y (fineSet (S := S) (n := n) M K k (Y.1 : Set _)) →
      (∀ x1, cubeMap n S.L M K j x1 = y → x1 ∉ (H.localHistory M K k Y).Z j) →
      (∀ x1, cubeMap n S.L M K j x1 = y → cubeMap n S.L M K (j + 1) x1 ∉
        lhOmegaSim (H.localHistory M K k Y) k (j + 1)) →
        PsiTildeMulti (msY hK cov hY x) (scaleBlocksIn j (nbhd 1 {y})) (3 * δ j)) := by
  have hnn := H.F.hnn
  constructor
  · intro h Y hY j hj1 hjk y hy1 hy2 hy3
    rcases Nat.lt_or_ge j k with hlt | hge
    · have hfine : ∀ w, cubeMap n S.L M K j w = y → cubeMap n S.L M K k w ∈ Y.1 :=
        fun w hw => hy1 w hw
      exact (dom2_part_iff hK cov hY x o hlt _ y hfine).mpr (h j hj1 hlt y) hy1 hy2 hy3
    · exfalso
      obtain rfl : j = k := le_antisymm hjk hge
      obtain ⟨w0, hw0⟩ := exists_site_of_cube (M := M) (K := K) hnn (show j ≤ K by omega) y
      exact hy2 w0 hw0 ((mem_localHistory_Z_top (M := M) (K := K) (by omega) Y w0).mpr (by
        have := hy1 w0 hw0
        exact this))
  · intro h j hj1 hjk y hy1 hy2 hy3
    obtain ⟨w0, hw0⟩ := exists_site_of_cube (M := M) (K := K) hnn (show j ≤ K by omega) y
    by_cases hlin : cubeMap n S.L M K k w0 ∈
        ((H.lin k (k + 1) Z' : Finset (Torus S.d (n k))) : Set _)
    · obtain ⟨Y, hY, hwY⟩ := exists_part_of_mem_lin hlin
      have hfine : ∀ w, cubeMap n S.L M K j w = y → cubeMap n S.L M K k w ∈ Y.1 := by
        intro w hw
        rw [cubeMap_eq_of_cubeMap_eq hjk.le (by omega) hnn (hw.trans hw0.symm)]
        exact hwY
      exact (dom2_part_iff hK cov hY x o hjk _ y hfine).mp (h Y hY j hj1 hjk.le y) hy1 hy2 hy3
    · exfalso
      exact hy3 w0 hw0 (mem_sim_of_not_lin hK (i := j + 1) (by omega) (by omega) hlin)

include cov in
/-- (1.25) at scales `j < k`: the conditions of `Z'` are those of its old parts. -/
theorem dom3_iff (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A') (C : ℕ → ℝ) :
    (∀ j, j < k → ∀ y : BlockAt S n M K j,
      BlockSub (S := S) (n := n) (M := M) (K := K) j y
        ((H.localHistory M K (k + 1) Z').Omega j \ (H.localHistory M K (k + 1) Z').OmegaDD j) →
        ‖subFluctField N (H.localHistory M K (k + 1) Z') (k + 1) x j y‖ < C j) ↔
    (∀ (Y : H.Comp k) (hY : Y ∈ H.parts k Z'), ∀ j, j < k → ∀ y : BlockAt S n M K j,
      BlockSub (S := S) (n := n) (M := M) (K := K) j y
        ((H.localHistory M K k Y).Omega j \ (H.localHistory M K k Y).OmegaDD j) →
        ‖flY hK cov hY x j y‖ < C j) := by
  have hnn := H.F.hnn
  constructor
  · intro h Y hY j hj y hb
    have hfine : BlockSub (S := S) (n := n) (M := M) (K := K) j y
        (fineSet (S := S) (n := n) M K k (Y.1 : Set (Torus S.d (n k)))) :=
      fun w hw => (hb w hw).1.2
    exact (dom3_part_iff hK cov hY x hj (C j) y hfine).mpr (h j hj y) hb
  · intro h j hj y hb
    obtain ⟨w0, hw0⟩ := exists_site_in_block (S := S) (n := n) (M := M) (K := K)
      (show j ≤ K by omega) y
    have hb0 := hb w0 hw0
    have hnD : cubeMap n S.L M K (j + 1) w0 ∉ ((H.locRH (k + 1) Z').step j).OmegaDD := fun hD =>
      hb0.2 ⟨hD, hb0.1.2⟩
    have h1 := mem_lin_of_not_mem_locOmegaDD Z' (show j < k + 1 by omega) (by omega) hnD
    have h2 := cubeMap_lin_coarsen (show j + 1 ≤ k by omega) (Nat.le_succ k) hK h1
    obtain ⟨Y, hY, hwY⟩ := exists_part_of_mem_lin h2
    have hfine : BlockSub (S := S) (n := n) (M := M) (K := K) j y
        (fineSet (S := S) (n := n) M K k (Y.1 : Set (Torus S.d (n k)))) := by
      intro w hw
      show cubeMap n S.L M K k w ∈ Y.1
      rw [cubeMap_eq_of_jBlock_eq hj.le (by omega) hnn (hw.trans hw0.symm)]
      exact hwY
    exact (dom3_part_iff hK cov hY x hj (C j) y hfine).mp (h Y hY j hj y) hb


end Aggregate

section Main

variable {H : RegionHistory S n R k0 K} {k : ℕ} (geo : Geo S n R M) (cs : OpConsts)
  (hK : k + 1 ≤ K) {Z' : H.Comp (k + 1)}
  {AY : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → Set (InternalVars (H.localHistory M K k Y) k)}
  {A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))}
  (cov : AncCover hK Z' AY A')

include cov in
/-- **The domain identity, `⇐`** (first step of the proof of Lemma II.5.13):
`χ^new_k(Z') ∏_Y χ^dom_k(Y) ≤ χ^dom_{k+1}(Z')`.  The output of the old part `Y` is the
large-field variable `ψ_k` of `Z'` on `V_Y` (`ancOut`). -/
theorem chiDomAt_succ_of (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A')
    (hnew : ChiNewAt geo cs H k Z' o (newRestrict (H.localHistory M K (k + 1) Z') cov.new x))
    (hanc : ∀ (Y : H.Comp k) (hY : Y ∈ H.parts k Z'),
      ChiDomAt geo cs H k Y (ancOut Y Z' x) (ancRestrict hK hY (cov.anc Y hY) x)) :
    ChiDomAt geo cs H (k + 1) Z' o x := by
  obtain ⟨N1, N2, N3⟩ := hnew
  refine ⟨?_, ?_, ?_⟩
  · intro j hj y hz hs
    rcases Nat.lt_or_ge j k with hlt | hge
    · exact (dom1_iff geo hK cov x o cs.delta).mpr
        (fun Y hY => (hanc Y hY).1) j hlt y hz hs
    · obtain rfl : j = k := by omega
      exact (psiTildeMulti_congr fun b hb =>
        (msField_new cov.new x o (genBlocks_scale_ge geo hK Z' hs hb) b.2)).mp (N1 y hz hs)
  · intro j hj1 hj2 y h1 h2 h3
    rcases Nat.lt_or_ge j k with hlt | hge
    · exact (dom2_iff hK cov x o cs.delta).mpr (fun Y hY => (hanc Y hY).2.1) j hj1 hlt y h1 h2 h3
    · have hjk : j = k ∨ j = k + 1 := by omega
      exact (psiTildeMulti_congr fun b hb => by
        obtain ⟨z, rfl, -⟩ := hb
        exact msField_new cov.new x o (show k ≤ j by omega) z).mp (N2 j hj1 hjk y h1 h2 h3)
  · intro j hj y hb
    rcases Nat.lt_or_ge j k with hlt | hge
    · exact (dom3_iff hK cov x (fun j => cs.Cpsi * cs.p0 j)).mpr
        (fun Y hY => (hanc Y hY).2.2) j hlt y hb
    · obtain rfl : j = k := by omega
      have := N3 y hb
      show ‖subFluctVarField N x j y‖ < _
      rw [← subFluctVarField_new cov.new x y]
      exact this

include cov in
/-- **The domain identity, `⇒`**: the domain of `Z'` contains the new conditions and the
domains of the old parts. -/
theorem chiDomAt_succ_imp (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A')
    (hdom : ChiDomAt geo cs H (k + 1) Z' o x) :
    ChiNewAt geo cs H k Z' o (newRestrict (H.localHistory M K (k + 1) Z') cov.new x) ∧
      ∀ (Y : H.Comp k) (hY : Y ∈ H.parts k Z'),
        ChiDomAt geo cs H k Y (ancOut Y Z' x) (ancRestrict hK hY (cov.anc Y hY) x) := by
  obtain ⟨P1, P2, P3⟩ := hdom
  refine ⟨⟨?_, ?_, ?_⟩, fun Y hY => ⟨?_, ?_, ?_⟩⟩
  · intro y hz hs
    exact (psiTildeMulti_congr fun b hb =>
      (msField_new cov.new x o (genBlocks_scale_ge geo hK Z' hs hb) b.2)).mpr
      (P1 k (Nat.lt_succ_self k) y hz hs)
  · intro j hj1 hjk y h1 h2 h3
    exact (psiTildeMulti_congr fun b hb => by
      obtain ⟨z, rfl, -⟩ := hb
      exact msField_new cov.new x o (show k ≤ j by omega) z).mpr
      (P2 j hj1 (by omega) y h1 h2 h3)
  · intro y hb
    have := P3 k (Nat.lt_succ_self k) y hb
    show ‖subFluctVarField N (newRestrict (H.localHistory M K (k + 1) Z') cov.new x) k y‖ < _
    rw [subFluctVarField_new cov.new x y]
    exact this
  · exact (dom1_iff geo hK cov x o cs.delta).mp
      (fun j hj y hz hs => P1 j (Nat.lt_succ_of_lt hj) y hz hs) Y hY
  · exact (dom2_iff hK cov x o cs.delta).mp
      (fun j hj1 hjk y h1 h2 h3 => P2 j hj1 (by omega) y h1 h2 h3) Y hY
  · exact (dom3_iff hK cov x (fun j => cs.Cpsi * cs.p0 j)).mp
      (fun j hj y hb => P3 j (Nat.lt_succ_of_lt hj) y hb) Y hY

include cov in
/-- **The domain identity** (first step of the proof of Lemma II.5.13):
`χ^dom_{k+1}(Z') = χ^new_k(Z') ∏_{Y ∈ Anc_k(Z')} χ^dom_k(Y)`. -/
theorem chiDomAt_succ_iff (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) A') :
    ChiDomAt geo cs H (k + 1) Z' o x ↔
      ChiNewAt geo cs H k Z' o (newRestrict (H.localHistory M K (k + 1) Z') cov.new x) ∧
        ∀ (Y : H.Comp k) (hY : Y ∈ H.parts k Z'),
          ChiDomAt geo cs H k Y (ancOut Y Z' x) (ancRestrict hK hY (cov.anc Y hY) x) :=
  ⟨chiDomAt_succ_imp geo cs hK cov o x, fun h => chiDomAt_succ_of geo cs hK cov o x h.1 h.2⟩

end Main

end Identity

end Balaban.LargeField
