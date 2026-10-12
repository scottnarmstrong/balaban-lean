/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgGroup
public import Balaban.SmallField.XiLatSymm

/-!
# Reynolds averaging: invariance of the cut-off term of `T∞` under the paving symmetries

CLASS-RULINGS Q-A.  The terms of `T∞` (`Einf`) are covariant under the paving group `H`, the
fine-lattice maps `symZ (L^j L^{m₀+m₁})`, by the termwise (H.4-E) `eucE`, passed to the limit.
Everything is stated on block states `BSt` (a polymer of `j`-blocks, a centre block, fine fields)
on which the fine lattice group acts through the induced block map `blkZ` and `ψ ↦ ψ ∘ γ⁻¹`:

* `xiDom_image_pavingSymGroup'`: **`XiDom` equivariance**, with the generating set transported
  along the paving symmetry (`Ω_i(𝔹_j(γY)) = γ Ω_i(𝔹_j(Y))`, `pavingGS`);
* `ExtN`, `ExtEv`, `Supp`: the data extend, eventually along the tori of the sequence, into the
  analyticity domain of the lift of the polymer;
* `FB`: the cut-off term of `T∞` (zero outside `Supp`);
* `Einf_act`, `Supp_act`, `FB_act`: for `γ ∈ symZ (L^j L^{m₀+m₁})`, `FB (γ·s) = FB s`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

instance torusSeq_neZero (m₀ n : ℕ) : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩

/-- A finite shape is eventually small on the tori of the sequence. -/
theorem eventually_zsmall (m₀ j : ℕ) (X' : Finset (Fin d → ℤ)) :
    ∀ᶠ n in atTop, ZSmall (torusSeq L m₀ n * L ^ m₁ * L ^ (k - j)) 0 X' := by
  unfold ZSmall
  rw [Filter.eventually_all_finset]
  intro z _
  rw [Filter.eventually_all]
  intro μ
  filter_upwards [Filter.eventually_ge_atTop ((z μ).natAbs * 2 + 2)] with n hn
  have hR := (succ_le_torusSeq (L := L) m₀ n).trans (torusSeq_le_side (L := L) (m₁ := m₁) (k := k) m₀ n j)
  have : ((z μ).natAbs : ℤ) * 2 + 2 ≤ n := by exact_mod_cast hn
  have h3 : (n : ℤ) + 1 ≤ ((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by exact_mod_cast hR
  have h4 : |z μ| = ((z μ).natAbs : ℤ) := Int.abs_eq_natAbs _
  simp only [Nat.cast_zero, add_zero]
  omega


omit [NeZero L] in
theorem blockOf_eq_bW (j : ℕ) (x : Fin d → ℤ) : blockOf L j x = bW (L ^ j) x := rfl

section TorusDict
variable {N₁ : ℕ} [NeZero N₁]

theorem cbase_toTorus {W : ℕ} (hW : W ∣ N₁ * L ^ m₁ * L ^ k) (x : Fin d → ℤ) :
    cbase W (toTorus L N₁ m₁ k x) = toTorus L N₁ m₁ k (ibZ W (bW W x)) := by
  have hn : NeZero (N₁ * L ^ m₁ * L ^ k) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  rw [cbase_eq_sub]
  funext μ
  simp only [Pi.sub_apply, natT, toTorus, ibZ, bW]
  have h1 := ZMod.val_intCast (n := N₁ * L ^ m₁ * L ^ k) (x μ)
  have h2 : ((((x μ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ k)).val % W : ℕ) : ℤ) = x μ % (W : ℤ) := by
    rw [Int.natCast_mod, h1]
    exact Int.emod_emod_of_dvd _ (by exact_mod_cast hW)
  rw [← Int.cast_natCast, h2, ← Int.cast_sub]
  congr 1
  rw [Int.emod_def]; ring

omit [NeZero L] [NeZero N₁] in
theorem blockPt_eq_toTorus (j : ℕ) (y : Fin d → ℤ) :
    blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y = toTorus L N₁ m₁ k (ibZ (L ^ j) y) := by
  funext μ; simp [blockPt, toTorus, ibZ, mul_comm]

end TorusDict

omit [NeZero L] in
theorem image_yhat {s j : ℕ} (hW : 0 < L ^ j) (hs : L ^ j ∣ s) {g : Equiv.Perm (Fin d → ℤ)}
    (hg : g ∈ symZ (d := d) s) (X' : Finset (Fin d → ℤ)) :
    g '' yhat L j X' = yhat L j (X'.image (blkZ (L ^ j) g)) := by
  ext x
  constructor
  · rintro ⟨x', hx', rfl⟩
    simp only [yhat, Set.mem_ofPred_eq, Finset.mem_image] at hx' ⊢
    refine ⟨_, hx', ?_⟩
    rw [blockOf_eq_bW (L := L) j (g x'), blkZ_spec hW hs hg]
    rfl
  · intro hx
    simp only [yhat, Set.mem_ofPred_eq, Finset.mem_image] at hx
    obtain ⟨b, hb, hbx⟩ := hx
    refine ⟨g.symm x, ?_, by simp⟩
    simp only [yhat, Set.mem_ofPred_eq]
    have hg' : g⁻¹ ∈ symZ (d := d) s := (symZ (d := d) s).inv_mem hg
    have h1 := blkZ_spec hW hs hg' x
    have e : (g⁻¹ : Equiv.Perm (Fin d → ℤ)) x = g.symm x := rfl
    rw [e] at h1
    rw [blockOf_eq_bW, h1, ← blockOf_eq_bW (L := L) j x, ← hbx, blkZ_inv_blkZ hW hs hg]
    exact hb

section Dict

variable [NeZero N₁]

theorem ypoly_image_torus {s j : ℕ} (hjk : j ≤ k) (hs : L ^ j ∣ s) {γ : Equiv.Perm (Fin d → ℤ)}
    (hγ : γ ∈ symZ (d := d) s) {γb : Equiv.Perm (CTorus d L N₁ m₁ k)}
    (hlift : ∀ x, γb (toTorus L N₁ m₁ k x) = toTorus L N₁ m₁ k (γ x))
    {X' : Finset (Fin d → ℤ)}
    (h1 : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) 0 X')
    (h2 : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) 0 (X'.image (blkZ (L ^ j) γ))) :
    Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (X'.image (blkZ (L ^ j) γ)) =
      γb '' Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' := by
  have hW : 0 < L ^ j := pow_pos (NeZero.pos L) j
  rw [Ypoly_eq_image hjk h1, Ypoly_eq_image hjk h2, Set.image_image, ← image_yhat hW hs hγ X',
    Set.image_image]
  congr 1
  funext x
  exact (hlift x).symm

theorem fineLift_image {s j : ℕ} (hjk : j ≤ k) (hs : L ^ j ∣ s) {γ : Equiv.Perm (Fin d → ℤ)}
    (hγ : γ ∈ symZ (d := d) s) {γb : Equiv.Perm (CTorus d L N₁ m₁ k)}
    (hlift : ∀ x, γb (toTorus L N₁ m₁ k x) = toTorus L N₁ m₁ k (γ x))
    {X' : Finset (Fin d → ℤ)}
    (h1 : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) 0 X')
    (h2 : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) 0 (X'.image (blkZ (L ^ j) γ)))
    {z : CTorus d L N₁ m₁ k}
    (hz : z ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') :
    fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (γb z) =
      γ (fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z) := by
  have hW : 0 < L ^ j := pow_pos (NeZero.pos L) j
  rw [Ypoly_eq_image hjk h1] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hx' : γ x ∈ yhat L j (X'.image (blkZ (L ^ j) γ)) := by
    rw [← image_yhat hW hs hγ X']; exact ⟨x, hx, rfl⟩
  have hs1 : ∀ μ, 2 * |x μ / ((L ^ j : ℕ) : ℤ)| < ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
    intro μ
    have : 2 * (|x μ / ((L ^ j : ℕ) : ℤ)| + ((0 : ℕ) : ℤ) + 1) <
        ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := h1 _ hx μ
    simp only [Nat.cast_zero, add_zero] at this
    omega
  have hs2 : ∀ μ, 2 * |γ x μ / ((L ^ j : ℕ) : ℤ)| < ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
    intro μ
    have : 2 * (|γ x μ / ((L ^ j : ℕ) : ℤ)| + ((0 : ℕ) : ℤ) + 1) <
        ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := h2 _ hx' μ
    simp only [Nat.cast_zero, add_zero] at this
    omega
  rw [hlift, fineLift_toTorus hjk x hs1, fineLift_toTorus hjk (γ x) hs2]

theorem pullFld_image {s j : ℕ} (hjk : j ≤ k) (hs : L ^ j ∣ s) {γ : Equiv.Perm (Fin d → ℤ)}
    (hγ : γ ∈ symZ (d := d) s) {γb : Equiv.Perm (CTorus d L N₁ m₁ k)}
    (hlift : ∀ x, γb (toTorus L N₁ m₁ k x) = toTorus L N₁ m₁ k (γ x))
    {X' : Finset (Fin d → ℤ)}
    (h1 : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) 0 X')
    (h2 : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) 0 (X'.image (blkZ (L ^ j) γ)))
    (ψ : InfFld d N) {z : CTorus d L N₁ m₁ k}
    (hz : z ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') :
    pullFld (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (fun x => ψ (γ.symm x)) (γb z) =
      pullFld (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j ψ z := by
  unfold pullFld
  rw [fineLift_image hjk hs hγ hlift h1 h2 hz]
  simp

end Dict


/-- `XiDom` transported along a paving symmetry (the data-level form used for the polymer lifts). -/
theorem xiDom_image_pavingSymGroup' {m₀ j : ℕ} {N₁ : ℕ} [NeZero N₁] (hjk : j ≤ k)
    {G G' : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} (hG : ∀ i, j < i → G.Ω i = ∅)
    {r : Equiv.Perm (CTorus d L N₁ m₁ k)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L m₀ j)
    (hΩ : ∀ i, ((G'.Ω i : Finset (CTorus d L N₁ m₁ k)) : Set (CTorus d L N₁ m₁ k)) =
      r '' ((G.Ω i : Finset (CTorus d L N₁ m₁ k)) : Set (CTorus d L N₁ m₁ k)))
    {a : ℕ → ℝ} {ν ε : ℝ} {Ψ h : Fld d L N₁ m₁ k N}
    (hX : XiDom G a ν j ε Ψ h) : XiDom G' a ν j ε (actField r Ψ) (actField r h) := by
  obtain ⟨T⟩ := nonempty_torusSymm_of_mem_pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) m₀ hjk hr
  have hΩ' : ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ x, r x ∈ G'.Ω i ↔ x ∈ G.Ω i := by
    intro i _ _ x
    have h1 : r x ∈ (G'.Ω i : Set (CTorus d L N₁ m₁ k)) ↔ r x ∈ r '' (G.Ω i : Set (CTorus d L N₁ m₁ k)) := by
      rw [hΩ i]
    simpa using h1
  have hj : ∀ n, 1 ≤ n → n ≤ k → (G.layer n).Nonempty → n ≤ j := by
    intro n _ _ hne
    obtain ⟨x, hx⟩ := hne
    rw [GeneratingSet.mem_layer] at hx
    by_contra hnj
    have := hG n (by omega)
    rw [this] at hx
    simp at hx
  have S := LatSymm.ofTorusSymm T hΩ' hj
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hΨ, hh, hXi⟩ := hX
  refine ⟨fun y => Ψ₀ (r.symm y), h₀, fun y => Ψ'' (r.symm y), fun y => h'' (r.symm y),
    fun x i => ?_, fun x i => ?_, xiC_sym S a ν hXi⟩
  · exact hΨ _ i
  · exact hh _ i


/-! ### States and the action -/

/-- A block state: a polymer of `ℤ^d` (set of `j`-blocks), a centre block and the fine fields
`(ψ, h)`. -/
structure BSt (d N : ℕ) where
  X : Finset (Fin d → ℤ)
  y : Fin d → ℤ
  ψ : InfFld d N
  h : InfFld d N

/-- The action of a permutation of the fine lattice on block states. -/
def BSt.act (W : ℕ) (g : Equiv.Perm (Fin d → ℤ)) (s : BSt d N) : BSt d N :=
  ⟨s.X.image (blkZ W g), blkZ W g s.y, fun x => s.ψ (g.symm x), fun x => s.h (g.symm x)⟩

theorem BSt.act_mul {W s : ℕ} (hW : 0 < W) (hs : W ∣ s) {g : Equiv.Perm (Fin d → ℤ)}
    (hg : g ∈ symZ (d := d) s) (g' : Equiv.Perm (Fin d → ℤ)) (st : BSt d N) :
    BSt.act W (g * g') st = BSt.act W g (BSt.act W g' st) := by
  unfold BSt.act
  have hb : ∀ b, blkZ W (g * g') b = blkZ W g (blkZ W g' b) := blkZ_mul hW hs hg
  have hI : Finset.image (blkZ W (g * g')) st.X =
      Finset.image (blkZ W g) (Finset.image (blkZ W g') st.X) := by
    rw [Finset.image_image]; exact Finset.image_congr (fun b _ => hb b)
  rw [hI, hb]
  rfl

theorem BSt.act_one {W : ℕ} (hW : 0 < W) (st : BSt d N) : BSt.act W 1 st = st := by
  cases st with
  | mk X y ψ h =>
    have : blkZ W (1 : Equiv.Perm (Fin d → ℤ)) = id := funext (blkZ_one hW)
    simp only [BSt.act, this, Finset.image_id, id]
    rfl

/-! ### The cutoff of the terms of `T∞` and the invariant function -/

section Cut

variable (P : Consts) (β ν a : ℕ → ℝ) (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (j : ℕ)

/-- `ψ, h` extend, on the torus `n` of the sequence, to a datum of `Ξ^c_j(𝔹_j(Y); 1, ε_j)` which
agrees with them on the lift `Y` of the polymer `X'`. -/
def ExtN (n : ℕ) (X' : Finset (Fin d → ℤ)) (ψ h : InfFld d N) : Prop :=
  ∃ (Ψ h' : Fld d L (torusSeq L P.m₀ n) m₁ k N),
    (∀ x ∈ Ypoly (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j X',
      Ψ x = pullFld j ψ x ∧ h' x = pullFld j h x) ∧
    XiDom ((Tm (torusSeq L P.m₀ n)).gs j (Ypoly j X')) (aIdeal L k (a k))
      (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h'

/-- Eventually along the tori of the sequence the data extend into the analyticity domain. -/
def ExtEv (X' : Finset (Fin d → ℤ)) (ψ h : InfFld d N) : Prop :=
  ∀ᶠ n in atTop, ExtN P β ν a Tm j n X' ψ h

/-- The support of the cut-off term: the polymer is a polymer of `T∞` containing the centre, and
the data extend eventually into the analyticity domain. -/
def Supp (s : BSt d N) : Prop :=
  InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j s.X ∧ s.y ∈ s.X ∧ ExtEv P β ν a Tm j s.X s.ψ s.h

open Classical in
/-- **The cut-off term of `T∞` on block states**: `ℰ_∞(y, X'; ψ, h)` for a polymer of `T∞`
containing the centre `y`, on data that extend eventually into the analyticity domain; `0` otherwise. -/
noncomputable def FB (s : BSt d N) : ℂ :=
  if Supp P β ν a Tm j s then Einf P.m₀ Tm j s.y s.X s.ψ s.h else 0

end Cut

section Inv

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

omit [NeZero L] in
theorem pavingSymGroup_eq {N₁ : ℕ} [NeZero N₁] (m₀ : ℕ) :
    pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L m₀ j =
      symGroupBy (cellSide L m₀ m₁ j) := rfl

omit [NeZero L] in
theorem torus_lift_paving {N₁ : ℕ} [NeZero N₁] (m₀ : ℕ) {γ : Equiv.Perm (Fin d → ℤ)}
    (hγ : γ ∈ symZ (d := d) (L ^ j * L ^ (m₀ + m₁))) :
    ∃ γb ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L m₀ j,
      ∀ x, γb (toTorus L N₁ m₁ k x) = toTorus L N₁ m₁ k (γ x) := by
  rw [pavingSymGroup_eq, cellSide_eq_mul]
  exact exists_torus_lift hγ

omit [NeZero L] in
theorem dvd_paving_cell (m₀ : ℕ) : L ^ j ∣ L ^ j * L ^ (m₀ + m₁) := dvd_mul_right _ _

/-- **`ExtN` is equivariant under the paving symmetries** (`XiDom` equivariance with the generating
set transported, `pavingGS`). -/
theorem ExtN_act (hF : IsSFFamily P β ν a Tm ρd Ek) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {γ : Equiv.Perm (Fin d → ℤ)} (hγ : γ ∈ symZ (d := d) (L ^ j * L ^ (P.m₀ + m₁))) {n : ℕ}
    {X' : Finset (Fin d → ℤ)}
    (hpd : IsPolyDom (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) P.m₀ j
      (Ypoly j X'))
    (h1 : ZSmall (torusSeq L P.m₀ n * L ^ m₁ * L ^ (k - j)) 0 X')
    (h2 : ZSmall (torusSeq L P.m₀ n * L ^ m₁ * L ^ (k - j)) 0 (X'.image (blkZ (L ^ j) γ)))
    {ψ h : InfFld d N} (hE : ExtN P β ν a Tm j n X' ψ h) :
    ExtN P β ν a Tm j n (X'.image (blkZ (L ^ j) γ)) (fun x => ψ (γ.symm x))
      (fun x => h (γ.symm x)) := by
  obtain ⟨γb, hγb, hlift⟩ := torus_lift_paving (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁)
    (k := k) P.m₀ hγ
  have hY := ypoly_image_torus (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) hjk
    (dvd_paving_cell (L := L) (m₁ := m₁) (j := j) P.m₀) hγ hlift h1 h2
  obtain ⟨Ψ, h', hag, hxi⟩ := hE
  refine ⟨actField γb Ψ, actField γb h', fun x hx => ?_, ?_⟩
  · rw [hY] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨?_, ?_⟩
    · show Ψ (γb.symm (γb z)) = _
      rw [Equiv.symm_apply_apply, (hag z hz).1,
        pullFld_image hjk (dvd_paving_cell (L := L) (m₁ := m₁) (j := j) P.m₀) hγ hlift h1 h2 ψ hz]
    · show h' (γb.symm (γb z)) = _
      rw [Equiv.symm_apply_apply, (hag z hz).2,
        pullFld_image hjk (dvd_paving_cell (L := L) (m₁ := m₁) (j := j) P.m₀) hγ hlift h1 h2 h hz]
  · rw [hY]
    have hsf := hF.torus (torusSeq L P.m₀ n)
    exact xiDom_image_pavingSymGroup' hjk (hsf.gs_spec j hj1 hjk _ hpd).2 hγb
      (hsf.pavingGS j hj1 hjk _ hpd γb hγb) hxi

/-- `XiDom` for the image polymer under a paving symmetry. -/
theorem xiDom_paving_image (hF : IsSFFamily P β ν a Tm ρd Ek) (hj1 : 1 ≤ j) (hjk : j ≤ k) {n : ℕ}
    {Y : Set (CTorus d L (torusSeq L P.m₀ n) m₁ k)}
    (hpd : IsPolyDom (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) P.m₀ j Y)
    {γb : Equiv.Perm (CTorus d L (torusSeq L P.m₀ n) m₁ k)}
    (hγb : γb ∈ pavingSymGroup (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) (d := d) L P.m₀ j)
    {Ψ h : Fld d L (torusSeq L P.m₀ n) m₁ k N}
    (hxi : XiDom ((Tm (torusSeq L P.m₀ n)).gs j Y) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j
      (P.eps d L j) Ψ h) :
    XiDom ((Tm (torusSeq L P.m₀ n)).gs j (γb '' Y)) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j
      (P.eps d L j) (actField γb Ψ) (actField γb h) := by
  have hsf := hF.torus (torusSeq L P.m₀ n)
  exact xiDom_image_pavingSymGroup' hjk (hsf.gs_spec j hj1 hjk _ hpd).2 hγb
    (hsf.pavingGS j hj1 hjk _ hpd γb hγb) hxi

theorem blockPt_mem_Ypoly {N₁ : ℕ} [NeZero N₁] (hjk : j ≤ k) {X' : Finset (Fin d → ℤ)}
    (hnw : NonWind L N₁ m₁ k j X') {y : Fin d → ℤ} (hy : y ∈ X') :
    blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y ∈
      Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' := by
  have : blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y = ibase j y := by
    funext μ; simp only [blockPt, ibase]; congr 1; ring
  rw [this]
  show unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (ibase j y) ∈ X'
  rw [unlift_ibase hjk (hnw y hy)]; exact hy

theorem blockBase_image {N₁ : ℕ} [NeZero N₁] (hjk : j ≤ k) {γ : Equiv.Perm (Fin d → ℤ)}
    {γb : Equiv.Perm (CTorus d L N₁ m₁ k)}
    (hlift : ∀ x, γb (toTorus L N₁ m₁ k x) = toTorus L N₁ m₁ k (γ x)) (y : Fin d → ℤ) :
    blockBase (d := d) (N₁ := N₁) (m₁ := m₁) (k := k) L j
        (γb (blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y)) =
      blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (blkZ (L ^ j) γ y) := by
  have hdvd : L ^ j ∣ N₁ * L ^ m₁ * L ^ k :=
    Dvd.dvd.mul_left (pow_dvd_pow L hjk) _
  rw [blockPt_eq_toTorus, hlift, blockBase, cbase_toTorus hdvd, blockPt_eq_toTorus]
  rfl

theorem Supp_act (hF : IsSFFamily P β ν a Tm ρd Ek) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {γ : Equiv.Perm (Fin d → ℤ)} (hγ : γ ∈ symZ (d := d) (L ^ j * L ^ (P.m₀ + m₁)))
    {s : BSt d N} (hΦ : Supp P β ν a Tm j s) :
    Supp P β ν a Tm j (BSt.act (L ^ j) γ s) := by
  obtain ⟨hX, hy, hE⟩ := hΦ
  refine ⟨?_, Finset.mem_image_of_mem _ hy, ?_⟩
  · show ∀ᶠ n in atTop, _
    filter_upwards [hX, eventually_zsmall (L := L) (m₁ := m₁) (k := k) P.m₀ j s.X,
      eventually_zsmall (L := L) (m₁ := m₁) (k := k) P.m₀ j (s.X.image (blkZ (L ^ j) γ)),
      eventually_nonWind (L := L) (m₁ := m₁) (k := k) P.m₀ j (s.X.image (blkZ (L ^ j) γ))]
      with n hn h1 h2 hnw
    obtain ⟨γb, hγb, hlift⟩ := torus_lift_paving (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁)
      (k := k) P.m₀ hγ
    refine ⟨hnw, ?_⟩
    show IsPolyDom (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) P.m₀ j
      (Ypoly j (s.X.image (blkZ (L ^ j) γ)))
    rw [ypoly_image_torus hjk (dvd_paving_cell (L := L) (m₁ := m₁) (j := j) P.m₀) hγ hlift h1 h2]
    exact isPolyDom_image_of_mem_pavingSymGroup (torusSeq_dvd P.m₀ n) hjk hn.2 hγb
  · show ∀ᶠ n in atTop, _
    filter_upwards [hX, hE, eventually_zsmall (L := L) (m₁ := m₁) (k := k) P.m₀ j s.X,
      eventually_zsmall (L := L) (m₁ := m₁) (k := k) P.m₀ j (s.X.image (blkZ (L ^ j) γ))]
      with n hn hEn h1 h2
    exact ExtN_act hF hj1 hjk hγ hn.2 h1 h2 hEn

/-- **Covariance of the term of `T∞` under the paving symmetries** (the termwise (H.4-E), passed to
the limit): for a state in the support, `ℰ_∞(γ y, γ X'; ψ∘γ⁻¹, h∘γ⁻¹) = ℰ_∞(y, X'; ψ, h)`. -/
theorem Einf_act (hF : IsSFFamily P β ν a Tm ρd Ek) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {γ : Equiv.Perm (Fin d → ℤ)} (hγ : γ ∈ symZ (d := d) (L ^ j * L ^ (P.m₀ + m₁)))
    {s : BSt d N} (hΦ : Supp P β ν a Tm j s) :
    Einf P.m₀ Tm j (BSt.act (L ^ j) γ s).y (BSt.act (L ^ j) γ s).X (BSt.act (L ^ j) γ s).ψ
      (BSt.act (L ^ j) γ s).h = Einf P.m₀ Tm j s.y s.X s.ψ s.h := by
  have hΦ' := Supp_act hF hj1 hjk hγ hΦ
  obtain ⟨hX, hy, hE⟩ := hΦ
  obtain ⟨hX', hy', -⟩ := hΦ'
  obtain ⟨n, ⟨hn, hEn⟩, h1, h2, hn'⟩ := ((hX.and hE).and
    ((eventually_zsmall (L := L) (m₁ := m₁) (k := k) P.m₀ j s.X).and
    ((eventually_zsmall (L := L) (m₁ := m₁) (k := k) P.m₀ j (s.X.image (blkZ (L ^ j) γ))).and
    hX'))).exists
  obtain ⟨γb, hγb, hlift⟩ := torus_lift_paving (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁)
    (k := k) P.m₀ hγ
  have hsf := hF.torus (torusSeq L P.m₀ n)
  have hdvd := dvd_paving_cell (L := L) (m₁ := m₁) (j := j) P.m₀
  have hY := ypoly_image_torus hjk hdvd hγ hlift h1 h2
  rw [Einf_eq_torus hF.torusIndep hj1 hjk hy hX s.ψ s.h (torusSeq L P.m₀ n) hn.1 hn.2]
  change Einf P.m₀ Tm j (blkZ (L ^ j) γ s.y) (s.X.image (blkZ (L ^ j) γ))
    (fun x => s.ψ (γ.symm x)) (fun x => s.h (γ.symm x)) = _
  have hy'' : blkZ (L ^ j) γ s.y ∈ s.X.image (blkZ (L ^ j) γ) := hy'
  have hX'' : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j (s.X.image (blkZ (L ^ j) γ)) := hX'
  have hn'' : NonWind L (torusSeq L P.m₀ n) m₁ k j (s.X.image (blkZ (L ^ j) γ)) ∧
      IsPolyDom (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly j (s.X.image (blkZ (L ^ j) γ))) := hn'
  rw [Einf_eq_torus hF.torusIndep hj1 hjk hy'' hX'' _ _ (torusSeq L P.m₀ n) hn''.1 hn''.2]
  obtain ⟨Ψ, h', hag, hxi⟩ := hEn
  have hxi2 := xiDom_paving_image hF hj1 hjk hn.2 hγb hxi
  have hmem := blockPt_mem_Ypoly (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) hjk hn.1 hy
  have hc := (blockBase_image (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) hjk hlift s.y).symm
  rw [hY]
  calc (Tm (torusSeq L P.m₀ n)).E j (blockPt j (blkZ (L ^ j) γ s.y)) (γb '' Ypoly j s.X)
        (pullFld j fun x => s.ψ (γ.symm x)) (pullFld j fun x => s.h (γ.symm x))
      = (Tm (torusSeq L P.m₀ n)).E j (blockPt j (blkZ (L ^ j) γ s.y)) (γb '' Ypoly j s.X)
          (actField γb Ψ) (actField γb h') := by
        refine hsf.localE j _ _ _ _ _ _ (fun x hx => ?_)
        obtain ⟨z, hz, rfl⟩ := hx
        refine ⟨?_, ?_⟩
        · rw [pullFld_image hjk hdvd hγ hlift h1 h2 s.ψ hz]
          show _ = Ψ (γb.symm (γb z))
          rw [Equiv.symm_apply_apply, (hag z hz).1]
        · rw [pullFld_image hjk hdvd hγ hlift h1 h2 s.h hz]
          show _ = h' (γb.symm (γb z))
          rw [Equiv.symm_apply_apply, (hag z hz).2]
    _ = (Tm (torusSeq L P.m₀ n)).E j (blockBase L j (γb (blockPt j s.y))) (γb '' Ypoly j s.X)
          (actField γb Ψ) (actField γb h') := by rw [hc]
    _ = (Tm (torusSeq L P.m₀ n)).E j (blockPt j s.y) (Ypoly j s.X) Ψ h' :=
        hsf.eucE j hj1 hjk _ _ hn.2 hmem γb hγb Ψ h' hxi hxi2
    _ = _ := hsf.localE j _ _ _ _ _ _ (fun x hx => ⟨(hag x hx).1, (hag x hx).2⟩)

theorem Supp_act_iff (hF : IsSFFamily P β ν a Tm ρd Ek) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {γ : Equiv.Perm (Fin d → ℤ)} (hγ : γ ∈ symZ (d := d) (L ^ j * L ^ (P.m₀ + m₁)))
    (s : BSt d N) : Supp P β ν a Tm j (BSt.act (L ^ j) γ s) ↔ Supp P β ν a Tm j s := by
  have hW : 0 < L ^ j := pow_pos (NeZero.pos L) j
  have hdvd := dvd_paving_cell (L := L) (m₁ := m₁) (j := j) P.m₀
  refine ⟨fun h => ?_, fun h => Supp_act hF hj1 hjk hγ h⟩
  have h' := Supp_act hF hj1 hjk ((symZ (d := d) _).inv_mem hγ) h
  rwa [← BSt.act_mul hW hdvd ((symZ (d := d) _).inv_mem hγ), inv_mul_cancel, BSt.act_one hW] at h'

/-- **The cut-off term of `T∞` is invariant under the paving symmetries**, acting on block states. -/
theorem FB_act (hF : IsSFFamily P β ν a Tm ρd Ek) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {γ : Equiv.Perm (Fin d → ℤ)} (hγ : γ ∈ symZ (d := d) (L ^ j * L ^ (P.m₀ + m₁)))
    (s : BSt d N) : FB P β ν a Tm j (BSt.act (L ^ j) γ s) = FB P β ν a Tm j s := by
  by_cases h : Supp P β ν a Tm j s
  · unfold FB
    rw [ite_eq_left h, ite_eq_left (Supp_act hF hj1 hjk hγ h)]
    exact Einf_act hF hj1 hjk hγ h
  · unfold FB
    rw [ite_eq_right h, ite_eq_right (fun h' => h ((Supp_act_iff hF hj1 hjk hγ s).1 h'))]

end Inv

end Balaban.SmallField.Def6