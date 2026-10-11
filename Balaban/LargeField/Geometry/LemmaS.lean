module

public import Balaban.LargeField.Geometry.Timar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lemma S (Lemma I.3.13): lattice separation and enclosure

Let `A₁, …, A_n ⊂ ℤ^d` be finite and pairwise `*`-separated, `A = ⋃ A_i`. A site `x ∉ A` is
*enclosed* by `A` if every infinite nn path from `x` that leaves every finite set meets `A`.

* `enclosed_by_single_component` (a): an enclosed point is enclosed by one `*`-component of one
  `A_{i₀}`;
* `enclosed_component_diam` (b): if moreover a box `Q = [u, v] ⊂ ℤ^d ∖ A` contains `x`, that
  `*`-component has extent `≥ (v_j - u_j) + 2` in every coordinate `j` (that is, sup-diameter
  `≥ side(Q) + 1`);
* `not_enclosed_boxes` (c): a union of pairwise `*`-separated boxes encloses no point.

All three are deduced from Timár's lemma (`exteriorBoundary_starConn`). Also
`exists_shell_path_iff_not_enclosed`, the lifting statement used for the torus version: for `A ∪ {x}`
in the interior of a box `Q`, `x` is joined to the shell of `Q` by an nn path in `Q ∖ A` iff `x` is
not enclosed by `A`.
-/

@[expose] public section

namespace Balaban.LatticeGeom

open Function Filter

variable {d : ℕ}

/-- `x ∉ A` is enclosed by `A`: every infinite nn path from `x` leaving every finite set meets `A`. -/
def Enclosed (A : Set (Pt d)) (x : Pt d) : Prop :=
  x ∉ A ∧ ∀ p, IsEscPath x p → ∃ n, p n ∈ A

/-- The `*`-component of `a` in `T`. -/
def starComp (T : Set (Pt d)) (a : Pt d) : Set (Pt d) := {y | StarConn T a y}

/-- Pairwise `*`-separation of a family of sets. -/
def StarSeparated {ι : Type*} (A : ι → Set (Pt d)) : Prop :=
  ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, ¬ StarNear a b

theorem Enclosed.mono {A B : Set (Pt d)} {x : Pt d} (hAB : A ⊆ B) (h : Enclosed A x)
    (hx : x ∉ B) : Enclosed B x :=
  ⟨hx, fun p hp => let ⟨n, hn⟩ := h.2 p hp; ⟨n, hAB hn⟩⟩

theorem enclosed_iff {A : Set (Pt d)} (hA : A.Finite) {x : Pt d} :
    Enclosed A x ↔ x ∉ A ∧ {z | Conn Aᶜ x z}.Finite := by
  constructor
  · intro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    by_contra hinf
    obtain ⟨p, hp, hpA⟩ := (joinedToInf_iff_infinite hA).mpr hinf
    obtain ⟨n, hn⟩ := h p hp
    exact hpA n hn
  · intro ⟨hx, hfin⟩
    refine ⟨hx, fun p hp => ?_⟩
    by_contra hno
    push Not at hno
    have : JoinedToInf A x := ⟨p, hp, hno⟩
    rw [joinedToInf_iff_infinite hA] at this
    exact this hfin

theorem StarConn.mono {T U : Set (Pt d)} (h : T ⊆ U) {a b : Pt d} (hab : StarConn T a b) :
    StarConn U a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨h hbc.1, h hbc.2.1, hbc.2.2⟩

theorem mem_of_starConn {T : Set (Pt d)} {a b : Pt d} (ha : a ∈ T) (h : StarConn T a b) :
    b ∈ T := by
  induction h with
  | refl => exact ha
  | tail _ hbc _ => exact hbc.2.1

theorem starConn_sep {ι : Type*} {A : ι → Set (Pt d)} (hsep : StarSeparated A) {i : ι}
    {a b : Pt d} (ha : a ∈ A i) (h : StarConn (⋃ j, A j) a b) : StarConn (A i) a b := by
  have : b ∈ A i ∧ StarConn (A i) a b := by
    induction h with
    | refl => exact ⟨ha, Relation.ReflTransGen.refl⟩
    | tail _ hbc ih =>
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hbc.2.1
      have hji : j = i := by
        by_contra hne
        exact hsep j i hne _ hj _ ih.1 hbc.2.2.symm
      subst hji
      exact ⟨hj, ih.2.tail ⟨ih.1, hj, hbc.2.2⟩⟩
  exact this.2

section Component

variable {A : Set (Pt d)} {x : Pt d}

theorem comp_not_mem (hx : x ∉ A) {c : Pt d} (hc : Conn Aᶜ x c) : c ∉ A := by
  by_cases h : x = c
  · subst h; exact hx
  · exact Conn.mem_right hc h

theorem conn_comp {c : Pt d} (hc : Conn Aᶜ x c) : Conn {z | Conn Aᶜ x z} x c := by
  induction hc with
  | refl => exact Conn.refl _
  | tail hxb hbc ih =>
    exact ih.tail (Conn.tail hxb hbc.2.1 hbc.1 hbc.2.2) hxb hbc.2.2

theorem comp_conn (a b : Pt d) (ha : Conn Aᶜ x a) (hb : Conn Aᶜ x b) :
    Conn {z | Conn Aᶜ x z} a b :=
  (conn_comp ha).symm.trans (conn_comp hb)

theorem comp_boundary_subset (hx : x ∉ A) :
    exteriorBoundary {z | Conn Aᶜ x z} ⊆ A := by
  rintro y ⟨hyC, ⟨c, hc, hn⟩, _⟩
  by_contra hyA
  exact hyC (hc.tail hyA (comp_not_mem hx hc) hn)

/-- An escaping path from a point of a finite set `C` meets the exterior boundary of `C`. -/
theorem path_meets_boundary {C : Set (Pt d)} (hC : C.Finite) {p : ℕ → Pt d}
    (hp : IsEscPath x p) (hxC : x ∈ C) : ∃ n, p n ∈ exteriorBoundary C := by
  classical
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hp.esc C hC)
  set N := Nat.findGreatest (fun n => p n ∈ C) M with hN
  have h0 : p 0 ∈ C := hp.zero ▸ hxC
  have hNC : p N ∈ C := Nat.findGreatest_spec (P := fun n => p n ∈ C) (Nat.zero_le M) h0
  have hgt : ∀ n, N < n → p n ∉ C := by
    intro n hn
    by_cases hnM : n ≤ M
    · exact Nat.findGreatest_is_greatest hn hnM
    · exact hM n (by omega)
  refine ⟨N + 1, hgt _ (Nat.lt_succ_self N), ⟨p N, hNC, hp.step N⟩, ?_⟩
  exact ⟨fun k => p (N + 1 + k), hp.tail (N + 1), fun k => hgt _ (by omega)⟩

/-- Maximal point in a coordinate direction and the exterior boundary point beyond it. -/
theorem exists_extreme {C : Set (Pt d)} (hC : C.Finite) (hne : C.Nonempty) (j : Fin d) {s : ℤ}
    (hs : s = 1 ∨ s = -1) :
    ∃ c ∈ C, (∀ c' ∈ C, s * c' j ≤ s * c j) ∧ c + Pi.single j s ∈ exteriorBoundary C := by
  obtain ⟨c, hc', hmax'⟩ := Finset.exists_max_image hC.toFinset (fun w : Pt d => s * w j)
    (by obtain ⟨c, hc⟩ := hne; exact ⟨c, hC.mem_toFinset.mpr hc⟩)
  have hc : c ∈ C := hC.mem_toFinset.mp hc'
  have hmax : ∀ b ∈ C, s * b j ≤ s * c j := fun b hb => hmax' b (hC.mem_toFinset.mpr hb)
  have hy : s * (c + (Pi.single j s : Pt d)) j = s * c j + 1 := by
    simp only [Pi.add_apply, Pi.single_eq_same]
    rcases hs with rfl | rfl <;> ring
  have hlt : ∀ w ∈ C, s * w j < s * (c + (Pi.single j s : Pt d)) j := fun w hw => by
    have := hmax w hw; rw [hy]; omega
  refine ⟨c, hc, hmax, fun hmem => absurd (hlt _ hmem) (lt_irrefl _), ⟨c, hc, ?_⟩, ?_⟩
  · rcases hs with rfl | rfl
    · exact ⟨j, Or.inl rfl⟩
    · refine ⟨j, Or.inr ?_⟩
      ext l
      by_cases hl : l = j
      · subst hl; simp
      · simp [hl]
  · exact ⟨ray _ j s, ray_isEscPath _ j hs, ray_not_mem _ j hs hlt⟩

end Component


theorem Icc_finite (u v : Pt d) : (Set.Icc u v : Set (Pt d)).Finite := by
  rw [← Set.pi_univ_Icc]
  exact Set.Finite.pi (fun _ => Set.finite_Icc _ _)

/-- A box is nn-connected. -/
theorem conn_Icc (u v : Pt d) {a b : Pt d} (ha : a ∈ Set.Icc u v) (hb : b ∈ Set.Icc u v) :
    Conn (Set.Icc u v) a b := by
  classical
  have key : ∀ J : Finset (Fin d), Conn (Set.Icc u v) a (fun k => if k ∈ J then b k else a k) := by
    intro J
    induction J using Finset.induction_on with
    | empty => simpa using Conn.refl a
    | insert j J hj ih =>
      refine ih.trans ?_
      have hw : ∀ k, u k ≤ (fun k => if k ∈ J then b k else a k) k ∧
          (fun k => if k ∈ J then b k else a k) k ≤ v k := by
        intro k
        by_cases hk : k ∈ J
        · simpa [hk] using ⟨hb.1 k, hb.2 k⟩
        · simpa [hk] using ⟨ha.1 k, ha.2 k⟩
      have := Conn.update (S := Set.Icc u v) j (b j) (fun k => if k ∈ J then b k else a k)
        (fun t ht => by
          have ht' : u j ≤ t ∧ t ≤ v j := by
            rw [Set.mem_uIcc] at ht
            simp only [hj, ite_false] at ht
            have hb1 : u j ≤ b j := hb.1 j
            have hb2 : b j ≤ v j := hb.2 j
            have ha1 : u j ≤ a j := ha.1 j
            have ha2 : a j ≤ v j := ha.2 j
            rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> omega
          refine ⟨fun k => ?_, fun k => ?_⟩
          · by_cases hk : k = j
            · subst hk; simp only [Function.update_self]; exact ht'.1
            · simp only [Function.update_of_ne hk]; exact (hw k).1
          · by_cases hk : k = j
            · subst hk; simp only [Function.update_self]; exact ht'.2
            · simp only [Function.update_of_ne hk]; exact (hw k).2)
      convert this using 1
      ext k
      by_cases hk : k = j
      · subst hk; simp
      · simp [Function.update, hk]
  simpa using key Finset.univ

section Main

variable {ι : Type*} [Finite ι] {A : ι → Set (Pt d)}

/-- Common core of Lemma S (a) and (b): an enclosed point has a finite nn-component `C` of the
complement, whose exterior boundary lies in one `*`-component `K` of one `A_i`, and `K` encloses
`x`. -/
theorem exists_component (hd : 2 ≤ d) (hfin : ∀ i, (A i).Finite) (hsep : StarSeparated A)
    {x : Pt d} (hx : Enclosed (⋃ i, A i) x) :
    ∃ i a, a ∈ A i ∧
      exteriorBoundary {z | Conn (⋃ j, A j)ᶜ x z} ⊆ starComp (A i) a ∧
      Enclosed (starComp (A i) a) x := by
  have hUfin : (⋃ i, A i).Finite := Set.finite_iUnion hfin
  obtain ⟨hxU, hCfin⟩ := (enclosed_iff hUfin).mp hx
  set C : Set (Pt d) := {z | Conn (⋃ j, A j)ᶜ x z} with hC
  have hxC : x ∈ C := Conn.refl _
  have hCconn : ∀ a ∈ C, ∀ b ∈ C, Conn C a b := fun a ha b hb => comp_conn a b ha hb
  have hCsub : exteriorBoundary C ⊆ ⋃ j, A j := comp_boundary_subset hxU
  let j0 : Fin d := ⟨0, by omega⟩
  obtain ⟨c, _, _, hy0⟩ := exists_extreme hCfin ⟨x, hxC⟩ j0 (s := 1) (Or.inl rfl)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hCsub hy0)
  have hsub : exteriorBoundary C ⊆ starComp (A i) (c + Pi.single j0 1) := by
    intro y hy
    have h1 := exteriorBoundary_starConn hd hCfin hCconn hy0 hy
    exact starConn_sep hsep hi (h1.mono hCsub)
  have hKsub : starComp (A i) (c + Pi.single j0 1) ⊆ A i := fun y hy =>
    mem_of_starConn hi hy
  refine ⟨i, _, hi, hsub, ?_, fun p hp => ?_⟩
  · intro hxK
    exact hxU (Set.mem_iUnion.mpr ⟨i, hKsub hxK⟩)
  · obtain ⟨n, hn⟩ := path_meets_boundary hCfin hp hxC
    exact ⟨n, hsub hn⟩

/-- **Lemma S (a)** (Lemma I.3.13 (a)): a point enclosed by a union of pairwise `*`-separated
finite sets is enclosed by a single `*`-component of a single set. -/
theorem enclosed_by_single_component (hd : 2 ≤ d) (hfin : ∀ i, (A i).Finite)
    (hsep : StarSeparated A) {x : Pt d} (hx : Enclosed (⋃ i, A i) x) :
    ∃ i a, a ∈ A i ∧ Enclosed (starComp (A i) a) x :=
  let ⟨i, a, ha, _, h⟩ := exists_component hd hfin hsep hx
  ⟨i, a, ha, h⟩

/-- **Lemma S (b)** (Lemma I.3.13 (b)): if moreover a box `Q = [u, v]` in the complement contains
`x`, that `*`-component has two points whose `j`-th coordinates differ by at least
`(v j - u j) + 2` for every `j` (sup-diameter `≥ side(Q) + 1`). -/
theorem enclosed_component_diam (hd : 2 ≤ d) (hfin : ∀ i, (A i).Finite) (hsep : StarSeparated A)
    {x : Pt d} (hx : Enclosed (⋃ i, A i) x) (u v : Pt d)
    (hQ : Set.Icc u v ⊆ (⋃ i, A i)ᶜ) (hxQ : x ∈ Set.Icc u v) :
    ∃ i a, a ∈ A i ∧ Enclosed (starComp (A i) a) x ∧
      ∀ j, ∃ y ∈ starComp (A i) a, ∃ z ∈ starComp (A i) a, v j - u j + 2 ≤ z j - y j := by
  obtain ⟨i, a, ha, hsub, hEnc⟩ := exists_component hd hfin hsep hx
  have hUfin : (⋃ i, A i).Finite := Set.finite_iUnion hfin
  obtain ⟨_, hCfin⟩ := (enclosed_iff hUfin).mp hx
  set C : Set (Pt d) := {z | Conn (⋃ j, A j)ᶜ x z} with hC
  have hQC : ∀ q ∈ Set.Icc u v, q ∈ C := fun q hq =>
    (conn_Icc u v hxQ hq).mono hQ
  have huv : u ≤ v := hxQ.1.trans hxQ.2
  refine ⟨i, a, ha, hEnc, fun j => ?_⟩
  obtain ⟨c', hc'C, hc'max, hz⟩ := exists_extreme hCfin ⟨x, hQC x hxQ⟩ j (s := 1) (Or.inl rfl)
  obtain ⟨c, hcC, hcmax, hy⟩ := exists_extreme hCfin ⟨x, hQC x hxQ⟩ j (s := -1) (Or.inr rfl)
  refine ⟨c + Pi.single j (-1), hsub hy, c' + Pi.single j 1, hsub hz, ?_⟩
  have h1 := hc'max v (hQC v ⟨huv, le_rfl⟩)
  have h2 := hcmax u (hQC u ⟨le_rfl, huv⟩)
  simp only [Pi.add_apply, Pi.single_eq_same]
  omega

/-- **Lemma S (c)** (Lemma I.3.13 (c)): a union of pairwise `*`-separated boxes encloses no
point. -/
theorem not_enclosed_boxes (hd : 2 ≤ d) (u v : ι → Pt d)
    (hsep : StarSeparated (fun i => (Set.Icc (u i) (v i) : Set (Pt d)))) (x : Pt d) :
    ¬ Enclosed (⋃ i, (Set.Icc (u i) (v i) : Set (Pt d))) x := by
  intro hx
  obtain ⟨i, a, ha, hK⟩ := enclosed_by_single_component hd (fun i => Icc_finite (u i) (v i)) hsep hx
  have hKsub : starComp (Set.Icc (u i) (v i)) a ⊆ Set.Icc (u i) (v i) := fun y hy =>
    mem_of_starConn ha hy
  have hxi : x ∉ Set.Icc (u i) (v i) := fun h => hx.1 (Set.mem_iUnion.mpr ⟨i, h⟩)
  have hE := hK.mono hKsub hxi
  obtain ⟨j, hj⟩ : ∃ j, x j < u i j ∨ v i j < x j := by
    by_contra h
    push Not at h
    exact hxi ⟨fun j => (h j).1, fun j => (h j).2⟩
  obtain ⟨s, hs, hT⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ∀ w ∈ Set.Icc (u i) (v i), s * w j < s * x j := by
    rcases hj with h | h
    · exact ⟨-1, Or.inr rfl, fun w hw => by have := hw.1 j; linarith⟩
    · exact ⟨1, Or.inl rfl, fun w hw => by have := hw.2 j; linarith⟩
  obtain ⟨n, hn⟩ := hE.2 (ray x j s) (ray_isEscPath x j hs)
  exact ray_not_mem x j hs hT n hn

end Main


section Shell

/-- The interior `Q^{∼-1}` of the box `[u, v]`. -/
def boxInterior (u v : Pt d) : Set (Pt d) := Set.Icc (fun j => u j + 1) (fun j => v j - 1)

theorem boxInterior_subset (u v : Pt d) : boxInterior u v ⊆ Set.Icc u v :=
  fun w hw => ⟨fun j => by have : u j + 1 ≤ w j := hw.1 j; show u j ≤ w j; omega,
    fun j => by have : w j ≤ v j - 1 := hw.2 j; show w j ≤ v j; omega⟩

theorem boxInterior_nn {u v a b : Pt d} (ha : a ∈ boxInterior u v) (h : NN a b) :
    b ∈ Set.Icc u v := by
  have hs := h.starNear
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have h1 : u j + 1 ≤ a j := ha.1 j
    have h2 := abs_le.mp (hs j)
    show u j ≤ b j
    omega
  · have h1 : a j ≤ v j - 1 := ha.2 j
    have h2 := abs_le.mp (hs j)
    show b j ≤ v j
    omega

/-- Lifting statement for the torus version of Lemma S: if `A ∪ {x}` lies in the interior of the
box `Q = [u, v]`, then `x` is joined to the shell `Q ∖ Q^{∼-1}` by an nn path in `Q ∖ A` if and only
if `x` is not enclosed by `A` (outside `Q` one can go to infinity freely). -/
theorem exists_shell_path_iff_not_enclosed {A : Set (Pt d)} (u v : Pt d)
    (hA : A ⊆ boxInterior u v) {x : Pt d} (hx : x ∈ boxInterior u v) (hxA : x ∉ A) :
    (∃ z ∈ Set.Icc u v, z ∉ boxInterior u v ∧ Conn (Set.Icc u v \ A) x z) ↔
      ¬ Enclosed A x := by
  constructor
  · rintro ⟨z, hzQ, hzI, hc⟩ ⟨_, hE⟩
    have hzA : z ∉ A := fun h => hzI (hA h)
    obtain ⟨j, hj⟩ : ∃ j, z j = u j ∨ z j = v j := by
      by_contra h
      push Not at h
      refine hzI ⟨fun j => ?_, fun j => ?_⟩
      · have h1 : u j ≤ z j := hzQ.1 j
        have h2 := h j
        show u j + 1 ≤ z j
        omega
      · have h1 : z j ≤ v j := hzQ.2 j
        have h2 := h j
        show z j ≤ v j - 1
        omega
    obtain ⟨s, hs, hT⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ w ∈ A, s * w j < s * z j := by
      rcases hj with h | h
      · exact ⟨-1, Or.inr rfl, fun w hw => by have : u j + 1 ≤ w j := (hA hw).1 j; rw [h]; linarith⟩
      · exact ⟨1, Or.inl rfl, fun w hw => by have : w j ≤ v j - 1 := (hA hw).2 j; rw [h]; linarith⟩
    have hJ : JoinedToInf A z := ⟨ray z j s, ray_isEscPath z j hs, ray_not_mem z j hs hT⟩
    have hc' : Conn Aᶜ x z := hc.mono fun w hw => hw.2
    obtain ⟨p, hp, hpA⟩ := JoinedToInf.of_conn hc' hJ
    obtain ⟨n, hn⟩ := hE p hp
    exact hpA n hn
  · intro hne
    have : ∃ p, IsEscPath x p ∧ ∀ n, p n ∉ A := by
      by_contra h
      apply hne
      refine ⟨hxA, fun p hp => ?_⟩
      by_contra hno
      push Not at hno
      exact h ⟨p, hp, hno⟩
    obtain ⟨p, hp, hpA⟩ := this
    classical
    have hex : ∃ n, p n ∉ boxInterior u v := by
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hp.esc _ (Icc_finite (fun j => u j + 1) (fun j => v j - 1)))
      exact ⟨N, hN N le_rfl⟩
    set n := Nat.find hex with hn
    have hnot : p n ∉ boxInterior u v := Nat.find_spec hex
    have hin : ∀ k < n, p k ∈ boxInterior u v := fun k hk => by
      by_contra h; exact Nat.find_min hex hk h
    have hnQ : ∀ k < n, p (k + 1) ∈ Set.Icc u v := fun k hk => boxInterior_nn (hin k hk) (hp.step k)
    refine ⟨p n, ?_, hnot, ?_⟩
    · rcases Nat.eq_zero_or_pos n with h0 | h0
      · exfalso; apply hnot; rw [h0, hp.zero]; exact hx
      · have := hnQ (n - 1) (by omega)
        rwa [Nat.sub_add_cancel h0] at this
    · have hc : ∀ k ≤ n, Conn (Set.Icc u v \ A) x (p k) := by
        intro k
        induction k with
        | zero => intro _; rw [hp.zero]; exact Conn.refl _
        | succ k ih =>
          intro hk
          exact (ih (by omega)).tail ⟨hnQ k (by omega), hpA _⟩
            ⟨boxInterior_subset u v (hin k (by omega)), hpA _⟩ (hp.step k)
      exact hc n le_rfl

end Shell

end Balaban.LatticeGeom
