module

public import Balaban.Polymer.Animals

/-!
# Weighted count of vertex sets all of whose components touch a root

Pure finite graph theory.  `V` is a finite type with a graph `G` of degrees at most `b`.  A *root*
is given by its set `N` of neighbours in `V` (the root itself is not a vertex of `G`).  A finite
set `C ⊆ V` is *rooted at `N`* if every vertex of `C` is joined, by a walk of `G` all of whose
vertices lie in `C`, to a vertex of `N` (equivalently: every connected component of the induced
graph on `C` meets `N`); the empty set is rooted.

With `Δ = max (b + 1) b_root` (the degree of the root is at most `b_root`; a vertex has at most
`b + 1` neighbours once the root is adjoined to the graph):

* `card_rooted_le`: the number of sets rooted at one root `N` with `|N| ≤ b_root` and of
  cardinality `n` is at most `Δ ^ (2 * n)`, by the animal bound `card_animals_le` in the graph
  with the root adjoined;
* `sum_rooted_le_one`: for `z = Δ² t < 1`, `Σ t ^ |C| ≤ 1 / (1 - z)` over sets rooted at one root;
* `sum_rooted_le`: for `r` roots, `Σ t ^ |C| ≤ (1 / (1 - z)) ^ r` over sets rooted at the family,
  by splitting a set into the part joined to the first root and the rest;
* `sum_rooted_family_le_exp`: with `t = exp (-κ₂)` the bound `exp (h r)`, `h = -log (1 - z)`,
  and `h ≤ 2 z` for `z ≤ 1/2`.

The intended use is VMOD-24 (3.3): the roots are the active top cells and the vertices are
the cover indices under Moore adjacency.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset SimpleGraph

namespace Balaban.Polymer

variable {V : Type*} (G : SimpleGraph V)

/-- The vertex `v` is joined to `w` by a walk of `G` all of whose vertices lie in `C`. -/
def WalkIn (C : Finset V) (v w : V) : Prop :=
  ∃ p : G.Walk v w, ∀ x ∈ p.support, x ∈ C

/-- `C` is rooted at `N`: every vertex of `C` is joined, by a walk inside `C`, to a vertex of `N`.
Equivalently every connected component of the graph induced on `C` meets `N`. -/
def Rooted (N : Set V) (C : Finset V) : Prop :=
  ∀ v ∈ C, ∃ w ∈ N, WalkIn G C v w

variable {G}

theorem WalkIn.trans {C : Finset V} {u v w : V} (h₁ : WalkIn G C u v) (h₂ : WalkIn G C v w) :
    WalkIn G C u w := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  refine ⟨p.append q, fun x hx => ?_⟩
  rw [Walk.mem_support_append_iff] at hx
  exact hx.elim (hp x) (hq x)

theorem WalkIn.refl {C : Finset V} {v : V} (hv : v ∈ C) : WalkIn G C v v :=
  ⟨Walk.nil, by simpa using hv⟩

/-- Along a walk inside `C` every visited vertex is reached from the start. -/
theorem WalkIn.of_mem_support {C : Finset V} {v w x : V} (p : G.Walk v w)
    (hp : ∀ y ∈ p.support, y ∈ C) (hx : x ∈ p.support) : WalkIn G C v x :=
  ⟨p.takeUntil x hx, fun y hy => hp y (p.support_takeUntil_subset_support hx hy)⟩

/-- Along a walk inside `C` the end is reached from every visited vertex. -/
theorem WalkIn.of_mem_support' {C : Finset V} {v w x : V} (p : G.Walk v w)
    (hp : ∀ y ∈ p.support, y ∈ C) (hx : x ∈ p.support) : WalkIn G C x w :=
  ⟨p.dropUntil x hx, fun y hy => hp y (p.support_dropUntil_subset_support hx hy)⟩

theorem WalkIn.mem_right {C : Finset V} {v w : V} (h : WalkIn G C v w) : w ∈ C := by
  obtain ⟨p, hp⟩ := h
  exact hp w p.end_mem_support

theorem WalkIn.mem_left {C : Finset V} {v w : V} (h : WalkIn G C v w) : v ∈ C := by
  obtain ⟨p, hp⟩ := h
  exact hp v p.start_mem_support

/-- The empty set is rooted. -/
theorem rooted_empty (N : Set V) : Rooted G N (∅ : Finset V) := by
  intro v hv; simp at hv

/-- Rootedness is monotone in the root set. -/
theorem Rooted.mono {N N' : Set V} (h : N ⊆ N') {C : Finset V} (hC : Rooted G N C) :
    Rooted G N' C := fun v hv => by
  obtain ⟨w, hw, hvw⟩ := hC v hv
  exact ⟨w, h hw, hvw⟩

/-- The only set rooted at the empty root set is the empty set. -/
theorem Rooted.eq_empty_of_empty {C : Finset V} (hC : Rooted G (∅ : Set V) C) : C = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
  obtain ⟨w, hw, -⟩ := hC v hv
  exact hw

/-- The part of `C` joined inside `C` to a vertex of `N₁`. -/
def splitOff (N₁ : Set V) (C : Finset V) : Finset V :=
  C.filter fun v => ∃ w ∈ N₁, WalkIn G C v w

theorem splitOff_subset (N₁ : Set V) (C : Finset V) : splitOff (G := G) N₁ C ⊆ C :=
  Finset.filter_subset _ _

/-- The part of a set rooted at `N₁ ∪ N'` that is joined to `N₁` is rooted at `N₁`. -/
theorem rooted_splitOff {N₁ N' : Set V} {C : Finset V} (_hC : Rooted G (N₁ ∪ N') C) :
    Rooted G N₁ (splitOff (G := G) N₁ C) := by
  intro v hv
  simp only [splitOff, Finset.mem_filter] at hv
  obtain ⟨hvC, w, hw, p, hp⟩ := hv
  refine ⟨w, hw, p, fun x hx => ?_⟩
  simp only [splitOff, Finset.mem_filter]
  exact ⟨hp x hx, w, hw, WalkIn.of_mem_support' p hp hx⟩

/-- The rest of a set rooted at `N₁ ∪ N'` is rooted at `N'`: a walk inside `C` starting there
cannot enter the part joined to `N₁`. -/
theorem rooted_sdiff_splitOff {N₁ N' : Set V} {C : Finset V} (hC : Rooted G (N₁ ∪ N') C) :
    Rooted G N' (C \ splitOff (G := G) N₁ C) := by
  intro v hv
  rw [Finset.mem_sdiff] at hv
  obtain ⟨hvC, hvs⟩ := hv
  obtain ⟨w, hw, p, hp⟩ := hC v hvC
  have hnot : ∀ x ∈ p.support, x ∉ splitOff (G := G) N₁ C := by
    intro x hx hxs
    simp only [splitOff, Finset.mem_filter] at hxs
    obtain ⟨-, w', hw', hxw'⟩ := hxs
    apply hvs
    simp only [splitOff, Finset.mem_filter]
    exact ⟨hvC, w', hw', (WalkIn.of_mem_support p hp hx).trans hxw'⟩
  have hwN' : w ∈ N' := by
    rcases hw with hw | hw
    · exact absurd (by
        simp only [splitOff, Finset.mem_filter]
        exact ⟨hvC, w, hw, p, hp⟩) hvs
    · exact hw
  exact ⟨w, hwN', p, fun x hx => Finset.mem_sdiff.2 ⟨hp x hx, hnot x hx⟩⟩

/-- The splitting map is injective: `C = C₁ ∪ C'`. -/
theorem splitOff_union_sdiff (N₁ : Set V) (C : Finset V) :
    splitOff (G := G) N₁ C ∪ (C \ splitOff (G := G) N₁ C) = C :=
  Finset.union_sdiff_of_subset (splitOff_subset N₁ C)

theorem card_splitOff_add (N₁ : Set V) (C : Finset V) :
    (splitOff (G := G) N₁ C).card + (C \ splitOff (G := G) N₁ C).card = C.card := by
  rw [add_comm]
  exact Finset.card_sdiff_add_card_eq_card (splitOff_subset N₁ C)

/-! ### Adjoining the root -/

variable (G)

/-- The graph `G` with a root vertex `none` adjoined, joined to the vertices of `N`. -/
def rootGraph (N : Finset V) : SimpleGraph (Option V) where
  Adj a b :=
    match a, b with
    | some v, some w => G.Adj v w
    | none, some w => w ∈ N
    | some v, none => v ∈ N
    | none, none => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by
    intro a h
    cases a <;> simp_all⟩

variable {G}

theorem rootGraph_adj_some {N : Finset V} {v w : V} :
    (rootGraph G N).Adj (some v) (some w) ↔ G.Adj v w := Iff.rfl

theorem rootGraph_adj_none {N : Finset V} {w : V} :
    (rootGraph G N).Adj none (some w) ↔ w ∈ N := Iff.rfl

variable [Fintype V]

instance (N : Finset V) : (rootGraph G N).LocallyFinite := fun _ => inferInstance

/-- The finite family of sets rooted at `N`. -/
def rootedSets (N : Set V) : Finset (Finset V) :=
  Finset.univ.filter (Rooted G N)

theorem mem_rootedSets {N : Set V} {C : Finset V} : C ∈ rootedSets (G := G) N ↔ Rooted G N C := by
  simp [rootedSets]

variable [G.LocallyFinite]

/-- Degrees in the graph with the root adjoined are at most `max (b + 1) b_root`. -/
theorem degree_rootGraph_le {b b_root : ℕ} (hb : ∀ v, G.degree v ≤ b) (N : Finset V)
    (hN : N.card ≤ b_root) (a : Option V) :
    (rootGraph G N).degree a ≤ max (b + 1) b_root := by
  cases a with
  | none =>
    rw [← card_neighborFinset_eq_degree]
    refine le_trans ?_ (hN.trans (le_max_right _ _))
    calc _ ≤ (N.image some).card := by
          apply Finset.card_le_card
          intro x hx
          rw [mem_neighborFinset] at hx
          cases x with
          | none => exact absurd hx (by simp [rootGraph])
          | some w => exact Finset.mem_image.2 ⟨w, hx, rfl⟩
      _ ≤ N.card := Finset.card_image_le
  | some v =>
    rw [← card_neighborFinset_eq_degree]
    refine le_trans ?_ ((Nat.add_le_add_right (hb v) 1).trans (le_max_left _ _))
    calc _ ≤ (insert none ((G.neighborFinset v).image some)).card := by
          apply Finset.card_le_card
          intro x hx
          rw [mem_neighborFinset] at hx
          cases x with
          | none => simp
          | some w => exact Finset.mem_insert_of_mem (Finset.mem_image.2
              ⟨w, (mem_neighborFinset _ _ _).2 hx, rfl⟩)
      _ ≤ ((G.neighborFinset v).image some).card + 1 := Finset.card_insert_le _ _
      _ ≤ _ := by
          exact Nat.add_le_add_right
            (Finset.card_image_le.trans (card_neighborFinset_eq_degree G v).le) 1

omit [Fintype V] [G.LocallyFinite] in
/-- The image of a rooted set, with the root `none` adjoined, is connected in `rootGraph`. -/
private theorem connected_insert_none (N : Finset V) {C : Finset V} (hC : Rooted G (N : Set V) C) :
    ((rootGraph G N).induce ((insert none (C.image some) : Finset (Option V)) : Set (Option V))).Connected := by
  set S : Finset (Option V) := insert none (C.image some) with hS
  have hnone : (none : Option V) ∈ S := by simp [hS]
  have hsome : ∀ {v}, v ∈ C → (some v : Option V) ∈ S := by intro v hv; simp [hS, hv]
  have lift : ∀ {v w : V} (p : G.Walk v w) (hp : ∀ x ∈ p.support, x ∈ C)
      (hv : (some v : Option V) ∈ (S : Set (Option V))) (hw : (some w : Option V) ∈ (S : Set (Option V))),
      ((rootGraph G N).induce (S : Set (Option V))).Reachable ⟨some v, hv⟩ ⟨some w, hw⟩ := by
    intro v w p
    induction p with
    | nil => intro _ hv hw; exact SimpleGraph.Reachable.refl _
    | @cons a b c h q ih =>
      intro hp hv hw
      have hb : b ∈ C := hp b (by simp)
      have hbS : (some b : Option V) ∈ (S : Set (Option V)) := hsome hb
      refine SimpleGraph.Adj.reachable (G := (rootGraph G N).induce (S : Set (Option V)))
        (u := ⟨some a, hv⟩) (v := ⟨some b, hbS⟩) h |>.trans (ih (fun x hx => hp x (by simp [hx])) hbS hw)
  have hreach : ∀ x : (S : Set (Option V)),
      ((rootGraph G N).induce (S : Set (Option V))).Reachable x ⟨none, hnone⟩ := by
    rintro ⟨x, hx⟩
    cases x with
    | none => exact SimpleGraph.Reachable.refl _
    | some v =>
      have hvC : v ∈ C := by simpa [hS] using hx
      obtain ⟨w, hw, p, hp⟩ := hC v hvC
      have hwC : w ∈ C := hp w p.end_mem_support
      have hwS := hsome hwC
      refine (lift p hp hx hwS).trans ?_
      exact SimpleGraph.Adj.reachable (G := (rootGraph G N).induce (S : Set (Option V)))
        (u := ⟨some w, hwS⟩) (v := ⟨none, hnone⟩) (by exact hw)
  have : Nonempty (S : Set (Option V)) := ⟨⟨none, hnone⟩⟩
  exact ⟨fun x y => (hreach x).trans (hreach y).symm⟩

/-- The count of sets rooted at one root `N` of cardinality `n` is at most
`max (b + 1) b_root ^ (2 * n)`. -/
theorem card_rooted_le {b b_root : ℕ} (hb : ∀ v, G.degree v ≤ b) (N : Finset V)
    (hN : N.card ≤ b_root) (n : ℕ) :
    ((rootedSets (G := G) (N : Set V)).filter fun C => C.card = n).card
      ≤ (max (b + 1) b_root) ^ (2 * n) := by
  have hA := card_animals_le (rootGraph G N) (degree_rootGraph_le hb N hN) none (n + 1)
  rw [Nat.add_sub_cancel] at hA
  refine le_trans ?_ hA
  refine Finset.card_le_card_of_injOn (fun C => insert none (C.image some)) (fun C hC => ?_)
    (fun C _ D _ h => ?_)
  · simp only [Finset.mem_coe, Finset.mem_filter, mem_rootedSets] at hC
    rw [Finset.mem_coe, mem_animals]
    refine ⟨by simp, ?_, connected_insert_none N hC.1⟩
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective _ (Option.some_injective _),
      hC.2]
  · simp only at h
    ext v
    have := congrArg (fun S : Finset (Option V) => some v ∈ S) h
    simpa using this

/-- Weighted bound for sets rooted at one root: `Σ t ^ |C| ≤ 1 / (1 - z)`, `z = Δ² t`. -/
theorem sum_rooted_le_one {b b_root : ℕ} (hb : ∀ v, G.degree v ≤ b) (N : Finset V)
    (hN : N.card ≤ b_root) {t : ℝ} (ht : 0 ≤ t)
    (hz : ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t < 1) :
    ∑ C ∈ rootedSets (G := G) (N : Set V), t ^ C.card
      ≤ 1 / (1 - ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t) := by
  set Δ : ℕ := max (b + 1) b_root with hΔ
  set z : ℝ := (Δ : ℝ) ^ 2 * t with hzdef
  have hz0 : 0 ≤ z := by positivity
  have hmaps : ∀ C ∈ rootedSets (G := G) (N : Set V), C.card ∈ range (Fintype.card V + 1) := by
    intro C _; rw [Finset.mem_range]; exact Nat.lt_succ_of_le (Finset.card_le_univ _)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ n ∈ range (Fintype.card V + 1),
      ∑ C ∈ (rootedSets (G := G) (N : Set V)).filter (fun C => C.card = n), t ^ C.card ≤ z ^ n := by
    intro n _
    rw [Finset.sum_congr rfl (g := fun _ => t ^ n) (fun C hC => by
      rw [(Finset.mem_filter.1 hC).2]), Finset.sum_const, nsmul_eq_mul]
    calc _ ≤ ((Δ ^ (2 * n) : ℕ) : ℝ) * t ^ n := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast card_rooted_le hb N hN n
      _ = z ^ n := by rw [hzdef, mul_pow, ← pow_mul]; push_cast; ring
  calc _ ≤ ∑ n ∈ range (Fintype.card V + 1), z ^ n := Finset.sum_le_sum hfib
    _ ≤ (1 - z)⁻¹ := sum_le_hasSum _ (fun i _ => by positivity) (hasSum_geometric_of_lt_one hz0 hz)
    _ = 1 / (1 - z) := (one_div _).symm

/-- Weighted bound for sets rooted at the union of the roots `N i`, `i ∈ s`:
`Σ t ^ |C| ≤ (1 / (1 - z)) ^ |s|`. -/
theorem sum_rooted_le {ι : Type*} [DecidableEq ι] {b b_root : ℕ} (hb : ∀ v, G.degree v ≤ b)
    (N : ι → Finset V) (hN : ∀ i, (N i).card ≤ b_root) {t : ℝ} (ht : 0 ≤ t)
    (hz : ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t < 1) (s : Finset ι) :
    ∑ C ∈ rootedSets (G := G) (⋃ i ∈ s, (N i : Set V)), t ^ C.card
      ≤ (1 / (1 - ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t)) ^ s.card := by
  set A : ℝ := 1 / (1 - ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t) with hA
  have hA0 : 0 ≤ A := by
    have : 0 < 1 - ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t := by linarith
    positivity
  induction s using Finset.induction_on with
  | empty =>
    have hU : (⋃ i ∈ (∅ : Finset ι), (N i : Set V)) = ∅ := by simp
    rw [hU, Finset.card_empty, pow_zero]
    calc _ ≤ ∑ C ∈ ({∅} : Finset (Finset V)), t ^ C.card := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro C hC
            rw [mem_rootedSets] at hC
            simpa using hC.eq_empty_of_empty
          · intros; positivity
      _ = 1 := by simp
  | insert a s ha ih =>
    rw [Finset.card_insert_of_notMem ha, pow_succ']
    have hU : (⋃ i ∈ insert a s, (N i : Set V)) = (N a : Set V) ∪ ⋃ i ∈ s, (N i : Set V) := by
      rw [Finset.set_biUnion_insert]
    rw [hU]
    set R1 := rootedSets (G := G) (N a : Set V)
    set R' := rootedSets (G := G) (⋃ i ∈ s, (N i : Set V))
    set R := rootedSets (G := G) ((N a : Set V) ∪ ⋃ i ∈ s, (N i : Set V))
    let φ : Finset V → Finset V × Finset V := fun C =>
      (splitOff (G := G) (N a : Set V) C, C \ splitOff (G := G) (N a : Set V) C)
    let g : Finset V × Finset V → ℝ := fun p => t ^ p.1.card * t ^ p.2.card
    have hinj : Set.InjOn φ R := by
      intro C _ D _ h
      simp only [φ, Prod.mk.injEq] at h
      calc C = splitOff (G := G) (N a : Set V) C ∪ (C \ splitOff (G := G) (N a : Set V) C) :=
            (splitOff_union_sdiff _ _).symm
        _ = splitOff (G := G) (N a : Set V) D ∪ (D \ splitOff (G := G) (N a : Set V) D) := by
            rw [h.2, h.1]
        _ = D := splitOff_union_sdiff _ _
    have h1 : ∑ C ∈ R, t ^ C.card = ∑ C ∈ R, g (φ C) := by
      refine Finset.sum_congr rfl fun C _ => ?_
      simp only [g, φ]
      rw [← pow_add, card_splitOff_add]
    rw [h1, ← Finset.sum_image hinj]
    have hsub : R.image φ ⊆ R1 ×ˢ R' := by
      intro p hp
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hp
      rw [mem_rootedSets] at hC
      exact Finset.mem_product.2 ⟨mem_rootedSets.2 (rooted_splitOff hC),
        mem_rootedSets.2 (rooted_sdiff_splitOff hC)⟩
    calc _ ≤ ∑ p ∈ R1 ×ˢ R', g p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by simp only [g]; positivity)
      _ = (∑ C ∈ R1, t ^ C.card) * ∑ C ∈ R', t ^ C.card := by
          rw [Finset.sum_product, Finset.sum_mul_sum]
      _ ≤ A * A ^ s.card :=
          mul_le_mul (sum_rooted_le_one hb (N a) (hN a) ht hz) ih
            (Finset.sum_nonneg fun _ _ => by positivity) hA0

/-- The exponential form: for `r` roots, a finite family `𝔉` of sets rooted at the family, and
`Δ² e^{-κ₂} < 1`, `Σ_{C ∈ 𝔉} e^{-κ₂ |C|} ≤ e^{h r}` with `h = -log (1 - Δ² e^{-κ₂})`. -/
theorem sum_rooted_family_le_exp {b b_root r : ℕ} (hb : ∀ v, G.degree v ≤ b)
    (N : Fin r → Finset V) (hN : ∀ i, (N i).card ≤ b_root) {κ₂ : ℝ}
    (hz : ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) < 1)
    (𝔉 : Finset (Finset V)) (h𝔉 : ∀ C ∈ 𝔉, Rooted G (⋃ i, (N i : Set V)) C) :
    ∑ C ∈ 𝔉, Real.exp (-κ₂ * C.card)
      ≤ Real.exp (-Real.log (1 - ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) * r) := by
  set z : ℝ := ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) with hzdef
  have hpos : 0 < 1 - z := by linarith
  have h1 : ∑ C ∈ 𝔉, Real.exp (-κ₂ * C.card) = ∑ C ∈ 𝔉, Real.exp (-κ₂) ^ C.card := by
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← Real.exp_nat_mul]; ring_nf
  have h2 : ∑ C ∈ 𝔉, Real.exp (-κ₂) ^ C.card
      ≤ ∑ C ∈ rootedSets (G := G) (⋃ i ∈ (Finset.univ : Finset (Fin r)), (N i : Set V)),
          Real.exp (-κ₂) ^ C.card := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro C hC
      rw [mem_rootedSets]
      simpa using h𝔉 C hC
    · intros; positivity
  have h3 : ∑ C ∈ rootedSets (G := G) (⋃ i ∈ (Finset.univ : Finset (Fin r)), (N i : Set V)),
      Real.exp (-κ₂) ^ C.card ≤ (1 / (1 - z)) ^ r := by
    have := sum_rooted_le hb N hN (Real.exp_pos (-κ₂)).le hz Finset.univ
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have h4 : Real.exp (-Real.log (1 - z) * r) = (1 / (1 - z)) ^ r := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_neg, Real.exp_log hpos, one_div]
  rw [h1, h4]
  exact h2.trans h3

/-- If `z ≤ 1/2` then `-log (1 - z) ≤ 2 z`. -/
theorem neg_log_one_sub_le {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 2) : -Real.log (1 - z) ≤ 2 * z := by
  have hpos : 0 < 1 - z := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have h2 : (1 - z)⁻¹ - 1 ≤ 2 * z := by
    rw [inv_eq_one_div, div_sub_one hpos.ne', div_le_iff₀ hpos]
    nlinarith
  linarith

/-- The corollary with `2 z r` in the exponent when `z = Δ² e^{-κ₂} ≤ 1/2`. -/
theorem sum_rooted_family_le_exp_two {b b_root r : ℕ} (hb : ∀ v, G.degree v ≤ b)
    (N : Fin r → Finset V) (hN : ∀ i, (N i).card ≤ b_root) {κ₂ : ℝ}
    (hz : ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) ≤ 1 / 2)
    (𝔉 : Finset (Finset V)) (h𝔉 : ∀ C ∈ 𝔉, Rooted G (⋃ i, (N i : Set V)) C) :
    ∑ C ∈ 𝔉, Real.exp (-κ₂ * C.card)
      ≤ Real.exp (2 * (((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) * r) := by
  have hz1 : ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) < 1 := by linarith
  refine (sum_rooted_family_le_exp hb N hN hz1 𝔉 h𝔉).trans (Real.exp_le_exp.2 ?_)
  exact mul_le_mul_of_nonneg_right (neg_log_one_sub_le (by positivity) hz) (Nat.cast_nonneg r)

/-! ### Non-vacuity: the path on three vertices with a root adjacent to the first vertex -/

omit [Fintype V] [G.LocallyFinite] in
/-- A vertex of a rooted set that is adjacent to the root has a neighbour in the set. -/
theorem Rooted.exists_adj {N : Set V} {C : Finset V} (hC : Rooted G N C) {v : V} (hv : v ∈ C)
    (hvN : v ∉ N) : ∃ u ∈ C, G.Adj v u := by
  obtain ⟨w, hw, p, hp⟩ := hC v hv
  cases p with
  | nil => exact absurd hw hvN
  | cons h q => exact ⟨_, hp _ (by simp), h⟩

omit [Fintype V] [G.LocallyFinite] in
/-- A nonempty set rooted at `N` meets `N`. -/
theorem Rooted.exists_mem {N : Set V} {C : Finset V} (hC : Rooted G N C) {v : V} (hv : v ∈ C) :
    ∃ w ∈ N, w ∈ C := by
  obtain ⟨w, hw, hvw⟩ := hC v hv
  exact ⟨w, hw, hvw.mem_right⟩

/-- On the path `0 - 1 - 2` with a root adjacent to `0` alone, the rooted sets are exactly
`∅`, `{0}`, `{0, 1}`, `{0, 1, 2}`: one of each cardinality `0, …, 3`, against the bound
`Δ ^ (2 n)` with `Δ = max (2 + 1) 1 = 3`. -/
theorem rootedSets_pathGraph_three :
    rootedSets (G := pathGraph 3) (({0} : Finset (Fin 3)) : Set (Fin 3)) =
      {∅, {0}, {0, 1}, {0, 1, 2}} := by
  have adj : ∀ {u v : Fin 3}, (pathGraph 3).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val :=
    pathGraph_adj
  ext C
  rw [mem_rootedSets]
  constructor
  · intro hC
    by_cases hne : C = ∅
    · simp [hne]
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.2 hne
    obtain ⟨w, hw, hwC⟩ := hC.exists_mem hv
    have hw0 : w = 0 := by simpa using hw
    subst hw0
    have h21 : (2 : Fin 3) ∈ C → (1 : Fin 3) ∈ C := by
      intro h2
      obtain ⟨u, hu, hadj⟩ := hC.exists_adj h2 (by simp)
      have key2 : ∀ u : Fin 3, ((2 : Fin 3).val + 1 = u.val ∨ u.val + 1 = (2 : Fin 3).val) →
          u = 1 := by decide
      exact (key2 u (adj.1 hadj)) ▸ hu
    have key : ∀ C : Finset (Fin 3), (0 : Fin 3) ∈ C → ((2 : Fin 3) ∈ C → (1 : Fin 3) ∈ C) →
        C = {0} ∨ C = {0, 1} ∨ C = {0, 1, 2} := by decide
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (key C hwC h21)
  · intro hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    have h10 : (pathGraph 3).Adj 1 0 := by rw [adj]; decide
    have h21 : (pathGraph 3).Adj 2 1 := by rw [adj]; decide
    rcases hC with rfl | rfl | rfl | rfl
    · exact rooted_empty _
    · intro v hv
      simp only [Finset.mem_singleton] at hv
      subst hv
      exact ⟨0, by simp, WalkIn.refl (by simp)⟩
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact ⟨0, by simp, WalkIn.refl (by simp)⟩
      · exact ⟨0, by simp, Walk.cons h10 Walk.nil, by simp⟩
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨0, by simp, WalkIn.refl (by simp)⟩
      · exact ⟨0, by simp, Walk.cons h10 Walk.nil, by simp⟩
      · exact ⟨0, by simp, Walk.cons h21 (Walk.cons h10 Walk.nil), by simp⟩

/-- A set with a component not touching the root is not rooted: `{1, 2}` has the component
`{1, 2}`, which does not contain `0`. -/
theorem not_rooted_pair :
    ¬ Rooted (pathGraph 3) (({0} : Finset (Fin 3)) : Set (Fin 3)) ({1, 2} : Finset (Fin 3)) := by
  intro h
  rw [← mem_rootedSets, rootedSets_pathGraph_three] at h
  revert h; decide

/-- Also `{0, 2}` is not rooted: the vertex `2` is cut off from the root. -/
theorem not_rooted_zero_two :
    ¬ Rooted (pathGraph 3) (({0} : Finset (Fin 3)) : Set (Fin 3)) ({0, 2} : Finset (Fin 3)) := by
  intro h
  rw [← mem_rootedSets, rootedSets_pathGraph_three] at h
  revert h; decide

/-- The bound of `card_rooted_le` on the example: at most `3 ^ (2 n)` sets of cardinality `n`
(the true numbers are `1, 1, 1, 1, 0, …`). -/
theorem card_rooted_pathGraph_three (n : ℕ) :
    ((rootedSets (G := pathGraph 3) (({0} : Finset (Fin 3)) : Set (Fin 3))).filter
      fun C => C.card = n).card ≤ 3 ^ (2 * n) := by
  have hb : ∀ v, (pathGraph 3).degree v ≤ 2 := fun v => by
    have := degree_lt_card_verts (G := pathGraph 3) v
    simp at this; omega
  have := card_rooted_le hb ({0} : Finset (Fin 3)) (b_root := 1) (by simp) n
  simpa using this

end Balaban.Polymer
