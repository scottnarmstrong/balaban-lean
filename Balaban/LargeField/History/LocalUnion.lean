module

public import Balaban.LargeField.Region.Locality

/-!
# Lemma I.3.9 for unions of components

`Region/Locality.lean` proves Lemma I.3.9 for a single component `Z'` of `Z^pre_{k+1}`.  The
localized history of a component of scale `k` has, at each earlier scale, a *union* of components
(the lineage), so we need the same statements for a *link-closed* set `W`: a set such that every
point of the ambient set linked to a point of `W` lies in `W` (`LinkClosed`).  The proofs are those
of `Region/Locality.lean` and `Region/Hull.lean`, with `W` in place of a component.

* `hullClosure_inter_closed`: `Hull_b(X ∩ W) = W` for a link-closed `W ⊆ Hull_b(X)`;
* `Z0_inter_closed`, `restrict_Zpre_closed` (Lemma I.3.9 (b), (c)): for `W ⊆ Z^pre_{k+1}` link-closed
  in `Z^pre_{k+1}`, the local step `restrict W` has `Z^{(0)}(loc) = Z^{(0)} ∩ W` and
  `Z^pre(loc) = W`; likewise for `Ω'ᶜ`, `Ωᶜ`, `Ω''ᶜ`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section Closed

variable {d n : ℕ} [NeZero n] {ω b : ℕ}

/-- `W` is closed under `ω`-links inside `Xc`. -/
def LinkClosed (ω : ℕ) (Xc W : Set (Torus d n)) : Prop :=
  ∀ x ∈ W, ∀ y ∈ Xc, supDist x y < ω → y ∈ W

theorem LinkClosed.linked {Xc W A : Set (Torus d n)} (hW : LinkClosed ω Xc W) (hA : A ⊆ Xc)
    {x y : Torus d n} (hx : x ∈ W) (h : Linked ω A x y) : y ∈ W ∧ Linked ω (A ∩ W) x y := by
  induction h with
  | refl => exact ⟨hx, Linked.refl _⟩
  | tail _ hbc ih =>
    obtain ⟨hb, hl⟩ := ih
    have hc := hW _ hb _ (hA hbc.2.1) hbc.2.2
    exact ⟨hc, hl.trans (Linked.single ⟨hbc.1, hb⟩ ⟨hbc.2.1, hc⟩ hbc.2.2)⟩

/-- A component of a set in a link-closed `W` is link-closed. -/
theorem linkClosed_of_comp {Xc : Set (Torus d n)} {Y : Finset (Torus d n)}
    (hY : Y ∈ comps ω (finOf Xc)) : LinkClosed ω Xc (Y : Set (Torus d n)) :=
  fun _ hx _ hy h => mem_comp_of_close hY hx (mem_finOf.mpr hy) h

theorem linkClosed_iUnion {ι : Type*} {Xc : Set (Torus d n)} {W : ι → Set (Torus d n)}
    (h : ∀ i, LinkClosed ω Xc (W i)) : LinkClosed ω Xc (⋃ i, W i) := by
  intro x hx y hy hxy
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨i, h i x hi y hy hxy⟩

/-- One hull round commutes with intersection with a link-closed set. -/
theorem hullRound_inter_closed (hω : 2 ≤ ω) {A Xc W : Set (Torus d n)} (hA : A ⊆ Xc)
    (hHA : hullRound ω b A ⊆ Xc) (hW : LinkClosed ω Xc W) :
    hullRound ω b (A ∩ W) = hullRound ω b A ∩ W := by
  have hcls : ∀ c ∈ W, c ∈ A →
      linkClass ω (finOf A) c = linkClass ω (finOf (A ∩ W)) c := by
    intro c hc hcA
    ext y
    rw [mem_linkClass, mem_linkClass]
    constructor
    · rintro ⟨hy, hl⟩
      rw [coe_finOf] at hl
      obtain ⟨hyZ, hl'⟩ := hW.linked hA hc hl
      exact ⟨mem_finOf.mpr ⟨mem_finOf.mp hy, hyZ⟩, by rw [coe_finOf]; exact hl'⟩
    · rintro ⟨hy, hl⟩
      rw [coe_finOf] at hl
      exact ⟨mem_finOf.mpr (mem_finOf.mp hy).1, by
        rw [coe_finOf]; exact hl.mono Set.inter_subset_left⟩
  ext y
  constructor
  · rintro (hy | ⟨Y', hY', hs, hb, hyY'⟩)
    · exact ⟨subset_hullRound _ hy.1, hy.2⟩
    · obtain ⟨c, hc⟩ := comp_nonempty hY'
      have hcA : c ∈ A ∩ W := mem_finOf.mp (comp_subset hY' hc)
      obtain ⟨Y, hY, hcY⟩ := mem_comp_self (ω := ω) (mem_finOf.mpr hcA.1)
      have hYeq : Y = Y' := by
        obtain ⟨z, hz, rfl⟩ := mem_comps_iff.mp hY'
        have hzc : c ∈ linkClass ω (finOf (A ∩ W)) z := hc
        have : linkClass ω (finOf (A ∩ W)) z = linkClass ω (finOf (A ∩ W)) c := by
          ext w
          rw [mem_linkClass, mem_linkClass]
          have hl := (mem_linkClass.mp hzc).2
          constructor
          · rintro ⟨hw, hl2⟩; exact ⟨hw, hl.symm.trans hl2⟩
          · rintro ⟨hw, hl2⟩; exact ⟨hw, hl.trans hl2⟩
        rw [this, ← hcls c hcA.2 hcA.1]
        obtain ⟨z', hz', rfl⟩ := mem_comps_iff.mp hY
        have : linkClass ω (finOf A) z' = linkClass ω (finOf A) c := by
          ext w
          rw [mem_linkClass, mem_linkClass]
          have hl := (mem_linkClass.mp hcY).2
          constructor
          · rintro ⟨hw, hl2⟩; exact ⟨hw, hl.symm.trans hl2⟩
          · rintro ⟨hw, hl2⟩; exact ⟨hw, hl.trans hl2⟩
        exact this
      subst hYeq
      have hyH : y ∈ hullRound ω b A := hull_subset_hullRound hY hs hb hyY'
      refine ⟨hyH, ?_⟩
      have hsubA : hull (Y : Set (Torus d n)) ⊆ Xc :=
        fun z hz => hHA (hull_subset_hullRound hY hs hb hz)
      have hl := hull_linked hω ⟨c, hc⟩ hs (subset_hull _ hc) hyY'
      exact (hW.linked subset_rfl hcA.2 (hl.mono hsubA)).1
  · rintro ⟨hy | ⟨Y, hY, hs, hb, hyY⟩, hyZ⟩
    · exact Or.inl ⟨hy, hyZ⟩
    · right
      obtain ⟨c, hc⟩ := comp_nonempty hY
      have hcA : c ∈ A := mem_finOf.mp (comp_subset hY hc)
      have hsubA : hull (Y : Set (Torus d n)) ⊆ Xc :=
        fun z hz => hHA (hull_subset_hullRound hY hs hb hz)
      have hl := hull_linked hω ⟨c, hc⟩ hs (subset_hull _ hc) hyY
      have hcZ : c ∈ W := (hW.linked subset_rfl hyZ (hl.symm.mono hsubA)).1
      have hY2 : Y ∈ comps ω (finOf (A ∩ W)) := by
        obtain ⟨z, hz, rfl⟩ := mem_comps_iff.mp hY
        have hzY : c ∈ linkClass ω (finOf A) z := hc
        have e1 : linkClass ω (finOf A) z = linkClass ω (finOf A) c := by
          ext w
          rw [mem_linkClass, mem_linkClass]
          have hl := (mem_linkClass.mp hzY).2
          constructor
          · rintro ⟨hw, hl2⟩; exact ⟨hw, hl.symm.trans hl2⟩
          · rintro ⟨hw, hl2⟩; exact ⟨hw, hl.trans hl2⟩
        rw [e1, hcls c hcZ hcA]
        exact mem_comps_iff.mpr ⟨c, mem_finOf.mpr ⟨hcA, hcZ⟩, rfl⟩
      exact ⟨Y, hY2, hs, hb, hyY⟩

/-- **Locality of the closure for a link-closed set**: if `W ⊆ Hull_b(X)` is link-closed in
`Hull_b(X)`, then the closure of `X ∩ W` is `W`. -/
theorem hullClosure_inter_closed (hω : 2 ≤ ω) (X : Set (Torus d n)) {W : Set (Torus d n)}
    (hW : LinkClosed ω (hullClosure ω b X) W) (hWsub : W ⊆ hullClosure ω b X) :
    hullClosure ω b (X ∩ W) = W := by
  set N := Fintype.card (Torus d n) with hN
  have key : ∀ t ≤ N, (hullRound ω b)^[t] (X ∩ W) = (hullRound ω b)^[t] X ∩ W := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
      exact hullRound_inter_closed hω (iter_subset_hullClosure X (by omega))
        (by rw [← Function.iterate_succ_apply' (hullRound ω b) t X]
            exact iter_subset_hullClosure X ht) hW
  show (hullRound ω b)^[N] (X ∩ W) = _
  rw [key N le_rfl]
  exact Set.inter_eq_right.mpr hWsub

end Closed

namespace RegionStep

section Local

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rprev Rk : ℝ}
  (st : RegionStep d L n0 n1 Rprev Rk) {ω r : ℕ} (crit : Option ℕ) {W : Set (Torus d n1)}
  (hn : n0 = L * n1) (rad : StepRadii L ω r Rprev Rk)
  (hcl : LinkClosed ω (st.Zpre ω crit) W)

include hcl in
theorem hW_of_closed : ∀ x ∈ W, ∀ y ∈ st.Z0, supDist x y < ω → y ∈ W :=
  fun _ hx _ hy h => hcl _ hx _ (st.Z0_subset_Zpre ω crit hy) h

include hn rad hcl

/-- The local sets lie in the link-closed set `W` (Lemma I.3.9). -/
theorem restrict_Z0_subset_closed : (st.restrict W).Z0 ⊆ W := by
  intro x hx
  have key : ∀ y ∈ W, Linked ω (st.restrict W).Z0 x y → x ∈ W := by
    intro y hy hl
    have hl' : Linked ω (st.Zpre ω crit) y x :=
      hl.symm.mono ((st.restrict_Z0_subset _).trans (st.Z0_subset_Zpre ω crit))
    exact (hcl.linked subset_rfl hy hl').1
  rcases (st.restrict W).attribution (ωk := 0) rad hn hx with
    ⟨Y, hY, _, ⟨z, hz, rfl⟩, -, hl⟩ | ⟨q, hq, -, hl⟩
  · have hzY : z ∈ (st.restrict W).Z := mem_finOf.mp (comp_subset hY hz)
    exact key _ hzY.2 hl
  · exact key q (st.restrict_newCubes_subset _ hq) hl

/-- **Lemma I.3.9 (b)**, `Ω'`, for a link-closed `W`: `Ω'ᶜ ∩ W = Ω'ᶜ(loc)`. -/
theorem OmegaPrime_compl_inter_closed :
    st.OmegaPrimeᶜ ∩ W = (st.restrict W).OmegaPrimeᶜ := by
  have hW := st.hW_of_closed crit hcl
  ext x
  constructor
  · rintro ⟨hxO, hxZ⟩
    exact st.not_mem_OmegaPrime_restrict hn rad hW hxZ hxO
  · intro hx
    exact ⟨fun h => hx (st.restrict_OmegaPrime_supset _ h),
      st.restrict_Z0_subset_closed crit hn rad hcl (RegionStep.OmegaPrime_compl_subset_Z0 _ hx)⟩

/-- **Lemma I.3.9 (b)**, `Ω`, for a link-closed `W`. -/
theorem Omega_compl_inter_closed : st.Omegaᶜ ∩ W = (st.restrict W).Omegaᶜ := by
  have hW := st.hW_of_closed crit hcl
  ext x
  constructor
  · rintro ⟨hxO, hxZ⟩
    exact st.not_mem_Omega_restrict hn rad hW hxZ hxO
  · intro hx
    exact ⟨fun h => hx (st.restrict_Omega_supset _ h),
      st.restrict_Z0_subset_closed crit hn rad hcl (RegionStep.Omega_compl_subset_Z0 _ hx)⟩

/-- **Lemma I.3.9 (b)**, `Ω''`, for a link-closed `W`. -/
theorem OmegaDD_compl_inter_closed : st.OmegaDDᶜ ∩ W = (st.restrict W).OmegaDDᶜ := by
  have hW := st.hW_of_closed crit hcl
  ext x
  constructor
  · rintro ⟨hxO, hxZ⟩
    exact st.not_mem_OmegaDD_restrict hn rad hW hxZ hxO
  · intro hx
    exact ⟨fun h => hx (st.restrict_OmegaDD_supset _ h),
      st.restrict_Z0_subset_closed crit hn rad hcl (RegionStep.OmegaDD_compl_subset_Z0 _ hx)⟩

/-- **Lemma I.3.9 (b)**, `Z^{(0)}`, for a link-closed `W`. -/
theorem Z0_inter_closed : st.Z0 ∩ W = (st.restrict W).Z0 := by
  have hW := st.hW_of_closed crit hcl
  ext x
  constructor
  · rintro ⟨hxO, hxZ⟩
    exact st.mem_restrict_Z0 hn rad hW hxZ hxO
  · intro hx
    exact ⟨st.restrict_Z0_subset _ hx, st.restrict_Z0_subset_closed crit hn rad hcl hx⟩

/-- **Lemma I.3.9 (c)** for a link-closed `W ⊆ Z^pre`: `Z^pre(loc) = W`. -/
theorem restrict_Zpre_closed (hω2 : 2 ≤ ω) (hWsub : W ⊆ st.Zpre ω crit) :
    (st.restrict W).Zpre ω crit = W := by
  have hZ0 := st.Z0_inter_closed crit hn rad hcl
  cases crit with
  | none =>
    show (st.restrict W).Z0 = _
    rw [← hZ0]
    exact Set.inter_eq_right.mpr hWsub
  | some b =>
    show hullClosure ω b (st.restrict W).Z0 = _
    rw [← hZ0]
    exact hullClosure_inter_closed hω2 st.Z0 hcl hWsub

end Local

end RegionStep

end Balaban.LargeField
