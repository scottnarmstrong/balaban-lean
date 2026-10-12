module

public import Balaban.Polymer.GasOperator
public import Balaban.Polymer.Hole
public import Balaban.Polymer.Support

/-!
# GAS and the polymer expansion with a hole, for weights acting on disjoint sets of variables

Lemma III.10.5 of `notes/phase1/LF-RECONSTRUCTION.md` (Lean item P10), the hole part.  The hole
`S₀` is the fixed part of the block set, carrying no integration variable: the weights `τ Z` and the
couplings `β Y` depend on the configuration through the *charged* supports `Z \ S₀`, `Y \ S₀`
only, and two elementary objects are in contact when their charged supports meet.  The polymer
of a connected family is the union of the *full* supports; it is a hole polymer of `Hole.lean`
(connected, containing every component of `S₀` that it meets, not inside `S₀`) because each
elementary object is.

* `xi_fiber`: grouping the polymers of a gas by their charged support.
* `holeKOp`: the expected activity of a hole polymer `X`: the expectation of the sum over the
  connected admissible families whose union of full supports is `X`.
* `gasOp_pe_hole`: `E Ξ = Ξ_hole(holeKOp)` and `pe_hole` for these activities, under the bounds of
  `gasOp_activity_bound` (with the Steiner size).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory

namespace Balaban.Polymer

section Fiber

variable {P : Type*} [Fintype P] {B : Type*} [Fintype B] (g : P → Finset B)
  (hne : ∀ x, (g x).Nonempty)

/-- The charged support as a polymer of the gas without a hole. -/
def chargedPoly (x : P) : NePoly B := ⟨g x, hne x⟩

/-- Families of pairwise compatible polymers with the given image. -/
def fiberFam (Γ : Finset (NePoly B)) : Finset (Finset P) :=
  Finset.univ.filter (fun Γ' => Compat (shareBlock g) Γ' ∧ Γ'.image (chargedPoly g hne) = Γ)

omit [Fintype P] [Fintype B] in
theorem chargedPoly_inj {Γ' : Finset P} (hc : Compat (shareBlock g) Γ') {x x' : P}
    (hx : x ∈ Γ') (hx' : x' ∈ Γ') (h : chargedPoly g hne x = chargedPoly g hne x') : x = x' := by
  by_contra hxx
  apply hc x hx x' hx' hxx
  rw [lnk_shareBlock]
  have : g x = g x' := congrArg Subtype.val h
  intro hd
  rw [this] at hd
  obtain ⟨b, hb⟩ := hne x'
  exact Finset.disjoint_left.mp hd hb hb

omit [Fintype P] [Fintype B] in
theorem compat_image {Γ' : Finset P} (hc : Compat (shareBlock g) Γ') :
    Compat (shareBlock (Subtype.val : NePoly B → Finset B)) (Γ'.image (chargedPoly g hne)) := by
  intro Y hY Y' hY' hYY
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hY
  obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hY'
  have hxx : x ≠ x' := fun h => hYY (by rw [h])
  have := hc x hx x' hx' hxx
  rw [lnk_shareBlock] at this ⊢
  exact this

omit [Fintype P] [Fintype B] in
theorem compat_insert {Y : NePoly B} {Γ0 : Finset (NePoly B)} (hY : Y ∉ Γ0)
    (hΓ : Compat (shareBlock (Subtype.val : NePoly B → Finset B)) (insert Y Γ0))
    {x : P} (hx : chargedPoly g hne x = Y) {Γ0' : Finset P} (hc : Compat (shareBlock g) Γ0')
    (him : Γ0'.image (chargedPoly g hne) = Γ0) : Compat (shareBlock g) (insert x Γ0') := by
  subst hx
  have key : ∀ b ∈ Γ0', ¬ lnk (shareBlock g) x b := by
    intro b hb
    have hfb : chargedPoly g hne b ∈ Γ0 := by
      rw [← him]; exact Finset.mem_image_of_mem _ hb
    have hne' : chargedPoly g hne x ≠ chargedPoly g hne b := fun h => hY (h ▸ hfb)
    have := hΓ _ (Finset.mem_insert_self _ _) _ (Finset.mem_insert_of_mem hfb) hne'
    rw [lnk_shareBlock] at this ⊢
    exact this
  intro a ha b hb hab
  rw [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact absurd rfl hab
  · exact key b hb
  · intro h
    exact key a ha ((lnk_symm _ _ _).mp h)
  · exact hc a ha b hb hab

omit [Fintype P] [Fintype B] in
theorem not_mem_of_image {Y : NePoly B} {Γ0 : Finset (NePoly B)} (hY : Y ∉ Γ0) {x : P}
    (hx : chargedPoly g hne x = Y) {Γ0' : Finset P} (him : Γ0'.image (chargedPoly g hne) = Γ0) :
    x ∉ Γ0' := fun hmem => hY (by rw [← him, ← hx]; exact Finset.mem_image_of_mem _ hmem)

omit [Fintype B] in
theorem sum_fiberFam (K : P → ℂ) (Γ : Finset (NePoly B))
    (hΓ : Compat (shareBlock (Subtype.val : NePoly B → Finset B)) Γ) :
    ∑ Γ' ∈ fiberFam g hne Γ, ∏ x ∈ Γ', K x =
      ∏ Y ∈ Γ, ∑ x ∈ Finset.univ.filter (fun x => chargedPoly g hne x = Y), K x := by
  induction Γ using Finset.induction_on with
  | empty =>
    have : fiberFam g hne (∅ : Finset (NePoly B)) = {∅} := by
      ext Γ'
      simp only [fiberFam, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        Finset.image_eq_empty]
      constructor
      · exact fun h => h.2
      · rintro rfl
        exact ⟨fun x hx => by simp at hx, rfl⟩
    rw [this]; simp
  | insert Y Γ0 hY ih =>
    have hΓ0 : Compat (shareBlock (Subtype.val : NePoly B → Finset B)) Γ0 :=
      fun a ha b hb hab => hΓ a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    rw [Finset.prod_insert hY, ← ih hΓ0, Finset.sum_mul_sum, ← Finset.sum_product']
    symm
    refine Finset.sum_bij (fun p _ => insert p.1 p.2) ?_ ?_ ?_ ?_
    · rintro ⟨x, Γ0'⟩ hp
      rw [Finset.mem_product, Finset.mem_filter] at hp
      obtain ⟨⟨_, hxY⟩, hΓ0'⟩ := hp
      simp only [fiberFam, Finset.mem_filter, Finset.mem_univ, true_and] at hΓ0' ⊢
      exact ⟨compat_insert g hne hY hΓ hxY hΓ0'.1 hΓ0'.2, by
        rw [Finset.image_insert, hxY, hΓ0'.2]⟩
    · rintro ⟨x, Γ0'⟩ hp ⟨x2, Γ0'2⟩ hp2 heq
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, fiberFam] at hp hp2
      simp only at heq
      have hx2 : x = x2 := by
        have hmem : x ∈ insert x2 Γ0'2 := heq ▸ Finset.mem_insert_self x Γ0'
        rcases Finset.mem_insert.mp hmem with h | h
        · exact h
        · exact absurd h (not_mem_of_image g hne hY hp.1 hp2.2.2)
      subst hx2
      have : Γ0' = Γ0'2 := by
        ext a
        constructor
        · intro ha
          have : a ∈ insert x Γ0'2 := heq ▸ Finset.mem_insert_of_mem ha
          rcases Finset.mem_insert.mp this with h | h
          · exact absurd (h ▸ ha) (not_mem_of_image g hne hY hp.1 hp.2.2)
          · exact h
        · intro ha
          have : a ∈ insert x Γ0' := heq ▸ Finset.mem_insert_of_mem ha
          rcases Finset.mem_insert.mp this with h | h
          · exact absurd (h ▸ ha) (not_mem_of_image g hne hY hp2.1 hp2.2.2)
          · exact h
      rw [this]
    · intro Γ' hΓ'
      simp only [fiberFam, Finset.mem_filter, Finset.mem_univ, true_and] at hΓ'
      obtain ⟨hc, himg⟩ := hΓ'
      have hYm : Y ∈ Γ'.image (chargedPoly g hne) := by rw [himg]; exact Finset.mem_insert_self _ _
      obtain ⟨x, hx, hxY⟩ := Finset.mem_image.mp hYm
      refine ⟨(x, Γ'.erase x), ?_, ?_⟩
      · rw [Finset.mem_product, Finset.mem_filter]
        refine ⟨⟨Finset.mem_univ _, hxY⟩, ?_⟩
        simp only [fiberFam, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun a ha b hb hab => hc a (Finset.mem_of_mem_erase ha) b
          (Finset.mem_of_mem_erase hb) hab, ?_⟩
        ext Y'
        simp only [Finset.mem_image, Finset.mem_erase]
        constructor
        · rintro ⟨a, ⟨hax, ha⟩, rfl⟩
          have : chargedPoly g hne a ∈ insert Y Γ0 := by
            rw [← himg]; exact Finset.mem_image_of_mem _ ha
          rcases Finset.mem_insert.mp this with h | h
          · exact absurd (chargedPoly_inj g hne hc ha hx (h.trans hxY.symm)) hax
          · exact h
        · intro hY'
          have : Y' ∈ Γ'.image (chargedPoly g hne) := by
            rw [himg]; exact Finset.mem_insert_of_mem hY'
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp this
          refine ⟨a, ⟨fun h => hY (by have := hY'; rw [h, hxY] at this; exact this), ha⟩, rfl⟩
      · simp [Finset.insert_erase hx]
    · intro p hp
      rw [Finset.mem_product, Finset.mem_filter] at hp
      rw [Finset.prod_insert (not_mem_of_image g hne hY hp.1.2 (by
        have := hp.2
        simp only [fiberFam, Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this.2))]


/-- Grouping the polymers of a gas by their charged support. -/
theorem xi_fiber (K : P → ℂ) (K' : NePoly B → ℂ)
    (hK' : ∀ Y, K' Y = ∑ x ∈ Finset.univ.filter (fun x => chargedPoly g hne x = Y), K x) :
    Xi (shareBlock g) K = Xi (shareBlock (Subtype.val : NePoly B → Finset B)) K' := by
  unfold Xi
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (Compat (shareBlock g)))
    (t := Finset.univ.filter (Compat (shareBlock (Subtype.val : NePoly B → Finset B))))
    (g := fun Γ' => Γ'.image (chargedPoly g hne))
    (fun Γ' hΓ' => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hΓ' ⊢
      exact compat_image g hne hΓ')]
  refine Finset.sum_congr rfl (fun Γ hΓ => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hΓ
  have : (Finset.univ.filter (Compat (shareBlock g))).filter
      (fun Γ' => Γ'.image (chargedPoly g hne) = Γ) = fiberFam g hne Γ := by
    ext Γ'
    simp [fiberFam]
  rw [this, sum_fiberFam g hne K Γ hΓ]
  exact Finset.prod_congr rfl (fun Y _ => (hK' Y).symm)

end Fiber

section Geometry

variable {B Yt Zt : Type*} [Fintype Yt] [Fintype Zt] (H : SimpleGraph B) (S₀ : Finset B)
  {cyF : Yt → Finset B} {zsF : Zt → Finset B} {cy : Yt → Finset B} {zs : Zt → Finset B}

omit [Fintype Yt] [Fintype Zt] in
theorem gasCs_charged (hcy : ∀ y, cy y = cyF y \ S₀) (hzs : ∀ z, zs z = zsF z \ S₀)
    (t : Yt ⊕ Zt) : gasCs cy zs t = gasCs cyF zsF t \ S₀ := by
  rcases t with y | z
  · simp [hcy]
  · simp [hzs]

omit [Fintype Yt] [Fintype Zt] in
theorem unionCs_charged (hcy : ∀ y, cy y = cyF y \ S₀) (hzs : ∀ z, zs z = zsF z \ S₀)
    (D : Finset (Yt ⊕ Zt)) :
    unionCs (gasCs cy zs) D = unionCs (gasCs cyF zsF) D \ S₀ := by
  ext b
  simp only [mem_unionCs, Finset.mem_sdiff, gasCs_charged S₀ hcy hzs]
  constructor
  · rintro ⟨t, ht, hb, hb0⟩
    exact ⟨⟨t, ht, hb⟩, hb0⟩
  · rintro ⟨⟨t, ht, hb⟩, hb0⟩
    exact ⟨t, ht, hb, hb0⟩

omit [Fintype Yt] [Fintype Zt] in
theorem holeClosed_union (D : Finset (Yt ⊕ Zt))
    (hcl : ∀ t ∈ D, HoleClosed H S₀ (gasCs cyF zsF t)) :
    HoleClosed H S₀ (unionCs (gasCs cyF zsF) D) := by
  intro a b ha hb hab haU
  obtain ⟨t, ht, hat⟩ := mem_unionCs.mp haU
  exact mem_unionCs.mpr ⟨t, ht, hcl t ht a b ha hb hab hat⟩

omit [Fintype Yt] [Fintype Zt] in
/-- A family connected through charged contacts, of connected full supports, has a connected
union. -/
theorem isAnimal_unionCs (hcy : ∀ y, cy y = cyF y \ S₀) (hzs : ∀ z, zs z = zsF z \ S₀)
    {D : Finset (Yt ⊕ Zt)} (hconn : ConnSet (gasCs cy zs) D)
    (hS : ∀ t ∈ D, IsAnimal H (gasCs cyF zsF t)) :
    IsAnimal H (unionCs (gasCs cyF zsF) D) := by
  set U := unionCs (gasCs cyF zsF) D with hU
  have hmem : ∀ t ∈ D, ∀ p ∈ gasCs cyF zsF t, p ∈ U := fun t ht p hp =>
    mem_unionCs.mpr ⟨t, ht, hp⟩
  have hin : ∀ t ∈ D, ∀ p ∈ gasCs cyF zsF t, ∀ q ∈ gasCs cyF zsF t,
      Relation.ReflTransGen (fun a b => a ∈ U ∧ b ∈ U ∧ H.Adj a b) p q := by
    intro t ht p hp q hq
    have := ((isAnimal_iff H _).mp (hS t ht)).2 p hp q hq
    exact Relation.ReflTransGen.mono
      (fun a b hab => ⟨hmem t ht a hab.1, hmem t ht b hab.2.1, hab.2.2⟩) _ _ this
  have hreach : ∀ t s, Reach (gasCs cy zs) D t s → t ∈ D →
      ∀ p ∈ gasCs cyF zsF t, ∀ q ∈ gasCs cyF zsF s,
        Relation.ReflTransGen (fun a b => a ∈ U ∧ b ∈ U ∧ H.Adj a b) p q := by
    intro t s h htD
    induction h with
    | refl => exact hin t htD
    | @tail b c _ hbc ih =>
      intro p hp q hq
      obtain ⟨_, hcD, hcont⟩ := hbc
      obtain ⟨r, hr1, hr2⟩ := Finset.not_disjoint_iff.mp hcont
      rw [gasCs_charged S₀ hcy hzs] at hr1 hr2
      exact (ih p hp r (Finset.mem_sdiff.mp hr1).1).trans (hin c hcD r (Finset.mem_sdiff.mp hr2).1 q hq)
  rw [isAnimal_iff]
  obtain ⟨t0, ht0⟩ := hconn.1
  refine ⟨?_, fun p hp q hq => ?_⟩
  · obtain ⟨b, hb⟩ := ((isAnimal_iff H _).mp (hS t0 ht0)).1
    exact ⟨b, hmem t0 ht0 b hb⟩
  · obtain ⟨t, ht, hpt⟩ := mem_unionCs.mp hp
    obtain ⟨s, hs, hqs⟩ := mem_unionCs.mp hq
    exact hreach t s (hconn.2 t ht s hs) ht p hpt q hqs

/-- The union of full supports of a connected admissible family with charged union `Y` is a hole
polymer with charged support `Y`. -/
theorem holePoly_of_cfam (hcy : ∀ y, cy y = cyF y \ S₀) (hzs : ∀ z, zs z = zsF z \ S₀)
    (hS : ∀ t, IsAnimal H (gasCs cyF zsF t)) (hcl : ∀ t, HoleClosed H S₀ (gasCs cyF zsF t))
    {cr : Zt → Finset B} {Y : Finset B} (hY : Y.Nonempty) {D : Finset (Yt ⊕ Zt)}
    (hD : D ∈ Cfam (gasCs cy zs) (gasA cy zs cr) Y) :
    IsAnimal H (unionCs (gasCs cyF zsF) D) ∧ ¬ unionCs (gasCs cyF zsF) D ⊆ S₀ ∧
      HoleClosed H S₀ (unionCs (gasCs cyF zsF) D) ∧ unionCs (gasCs cyF zsF) D \ S₀ = Y := by
  obtain ⟨hconn, _, hU⟩ := mem_Cfam.mp hD
  have hsd : unionCs (gasCs cyF zsF) D \ S₀ = Y := by
    rw [← unionCs_charged S₀ hcy hzs, hU]
  refine ⟨isAnimal_unionCs H S₀ hcy hzs hconn (fun t _ => hS t), ?_,
    holeClosed_union H S₀ D (fun t _ => hcl t), hsd⟩
  intro hsub
  obtain ⟨b, hb⟩ := hY
  rw [← hsd] at hb
  exact (Finset.mem_sdiff.mp hb).2 (hsub (Finset.mem_sdiff.mp hb).1)

end Geometry

section Activity

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (H : SimpleGraph B) (S₀ : Finset B)
  (cyF : Yt → Finset B) (zsF : Zt → Finset B)
  (cy : Yt → Finset B) (zs cr : Zt → Finset B)
  (β : Yt → (∀ b, Ω b) → ℂ) (τ : Zt → (∀ b, Ω b) → ℂ) (μ : ∀ b, Measure (Ω b))

/-- The activity integrand of a hole polymer `X`: the sum over the connected admissible families
(connected through charged contacts) whose union of full supports is `X`. -/
def holeActOp (X : HolePolymer H S₀) (Φ : ∀ b, Ω b) : ℂ :=
  ∑ C ∈ Cfam (gasCs cy zs) (gasA cy zs cr) (holeSupp H S₀ X),
    if unionCs (gasCs cyF zsF) C = X.1 then
      ∏ t ∈ C, gasW (fun y => β y Φ) (fun z => τ z Φ) t else 0

/-- The expected activity of a hole polymer. -/
def holeKOp (X : HolePolymer H S₀) : ℂ :=
  ∫ Φ, holeActOp H S₀ cyF zsF cy zs cr β τ X Φ ∂(Measure.pi μ)

variable {H S₀ cyF zsF cy zs cr β τ μ}

theorem integrable_holeActOp [∀ b, IsProbabilityMeasure (μ b)]
    (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hβb : ∀ y, Bdd (β y)) (hτb : ∀ z, Bdd (τ z)) (X : HolePolymer H S₀) :
    Integrable (holeActOp H S₀ cyF zsF cy zs cr β τ X) (Measure.pi μ) := by
  unfold holeActOp
  refine integrable_finsetSum _ (fun C _ => ?_)
  by_cases hc : unionCs (gasCs cyF zsF) C = X.1
  · simp only [hc, ite_true]; exact integrable_prod_gasW hβm hτm hβb hτb C
  · simp only [hc, ite_false]; exact integrable_zero _ _ _

/-- The activities of the gas of charged supports are the sums of the activities of the hole
polymers with that charged support. -/
theorem gasKOp_eq_sum_holeKOp [∀ b, IsProbabilityMeasure (μ b)]
    (hcy : ∀ y, cy y = cyF y \ S₀) (hzs : ∀ z, zs z = zsF z \ S₀)
    (hS : ∀ t, IsAnimal H (gasCs cyF zsF t)) (hcl : ∀ t, HoleClosed H S₀ (gasCs cyF zsF t))
    (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hβb : ∀ y, Bdd (β y)) (hτb : ∀ z, Bdd (τ z)) (Y : NePoly B) :
    gasKOp cy zs cr β τ μ Y = ∑ X ∈ Finset.univ.filter (fun X : HolePolymer H S₀ =>
        chargedPoly (holeSupp H S₀) holeSupp_nonempty X = Y), holeKOp H S₀ cyF zsF cy zs cr β τ μ X := by
  set F := Finset.univ.filter (fun X : HolePolymer H S₀ =>
        chargedPoly (holeSupp H S₀) holeSupp_nonempty X = Y) with hF
  have hmemF : ∀ X : HolePolymer H S₀, X ∈ F ↔ holeSupp H S₀ X = Y.1 := by
    intro X
    constructor
    · intro h
      exact congrArg Subtype.val (Finset.mem_filter.mp h).2
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext h⟩
  have hpt : ∀ Φ : ∀ b, Ω b,
      ∑ X ∈ F, holeActOp H S₀ cyF zsF cy zs cr β τ X Φ = gasActOp cy zs cr β τ Y Φ := by
    intro Φ
    unfold gasActOp gasK polyAct
    have h1 : ∀ X ∈ F, holeActOp H S₀ cyF zsF cy zs cr β τ X Φ =
        ∑ C ∈ Cfam (gasCs cy zs) (gasA cy zs cr) Y.1,
          if unionCs (gasCs cyF zsF) C = X.1 then
            ∏ t ∈ C, gasW (fun y => β y Φ) (fun z => τ z Φ) t else 0 := by
      intro X hX
      unfold holeActOp
      rw [(hmemF X).mp hX]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun C hC => ?_)
    obtain ⟨h1, h2, h3, h4⟩ := holePoly_of_cfam H S₀ hcy hzs hS hcl Y.2 hC
    set X0 : HolePolymer H S₀ := ⟨unionCs (gasCs cyF zsF) C, h1, h2, h3⟩ with hX0
    rw [Finset.sum_eq_single X0]
    · simp [hX0]
    · intro X _ hne
      have hneq : ¬ unionCs (gasCs cyF zsF) C = X.1 := fun h => hne (Subtype.ext h.symm)
      simp [hneq]
    · intro hX0F
      exfalso
      apply hX0F
      rw [hmemF]
      exact h4
  unfold gasKOp holeKOp
  rw [← integral_finsetSum _ (fun X _ => integrable_holeActOp hβm hτm hβb hτb X)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun Φ => (hpt Φ).symm))

section Bound

variable {d : Finset B → ℝ} {B0 κ' κ'' c c1 c2 p h : ℝ} [∀ b, IsProbabilityMeasure (μ b)]

/-- The expected activity of a hole polymer obeys the bound of `gas_activity_bound` for its charged
support (the activity of the gas of charged supports, restricted to the families with the given
union of full supports). -/
theorem norm_holeKOp_le (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c)
    (hc1 : 0 ≤ c1) (hp : 0 ≤ p) (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (zs z).Nonempty)
    (hcr : ∀ z, cr z ⊆ zs z)
    (hτd : ∀ z, DepOn (zs z) (τ z))
    (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hβb : ∀ y, Bdd (β y)) (hτb : ∀ z, Bdd (τ z))
    (hB : ∀ y Φ, ‖β y Φ‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hτ : ∀ z, ∫ Φ, ‖τ z Φ‖ ∂(Measure.pi μ) ≤ Real.exp (-p - h * (zs z).card))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → gasA cy zs cr C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    {K0' K0'' : ℝ} (hK0' : 0 ≤ K0')
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y),
      Real.exp (-(κ'' - κ') * d (cy y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤ K0'' ^ v)
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' + κ' * (c2 + c) + c1 + 3 + Real.log K0'' ≤ h)
    (X : HolePolymer H S₀)
    (hG1 : ((holeSupp H S₀ X).card : ℝ) ≤ c1 * (1 + d (holeSupp H S₀ X))) :
    ‖holeKOp H S₀ cyF zsF cy zs cr β τ μ X‖ ≤
      3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d (holeSupp H S₀ X)) := by
  have hscal := gasBound_norm_le (cy := cy) (zs := zs) (cr := cr) (d := d) hB0 hκ' hκ'' hc hc1 hp hd hz
    hcr hzd hG3 hK0' hent hK1 hcount hh ⟨holeSupp H S₀ X, holeSupp_nonempty X⟩ hG1
  refine le_trans ?_ hscal
  rw [norm_gasK_bound (cy := cy) (zs := zs) (cr := cr) (d := d) (κ'' := κ'') (p := p) (h := h) hB0]
  unfold holeKOp holeActOp
  rw [integral_finsetSum _ (fun C _ => by
    by_cases hc : unionCs (gasCs cyF zsF) C = X.1
    · simp only [hc, ite_true]; exact integrable_prod_gasW hβm hτm hβb hτb C
    · simp only [hc, ite_false]; exact integrable_zero _ _ _)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C hC => ?_))
  by_cases hU : unionCs (gasCs cyF zsF) C = X.1
  · simp only [hU, ite_true]
    exact norm_integral_family_le hB0 hβm hτm hτd hβb hτb hB hτ hC
  · simp only [hU, ite_false, integral_zero, norm_zero]
    refine mul_nonneg (Finset.prod_nonneg (fun y _ => ?_))
      (Finset.prod_nonneg (fun z _ => (Real.exp_pos _).le))
    simp only [sub_nonneg]; exact Real.one_le_exp (by positivity)

end Bound

section Main

variable {B0 κ'' c c2 p h : ℝ} [∀ b, IsProbabilityMeasure (μ b)]

/-- **GAS + PE with a hole for functions of the configuration.**  Let the couplings `β Y` and the
heavy weights `τ Z` depend on the configuration through the charged supports `Y \ S₀`, `Z \ S₀`
(full supports connected and closed under the components of the hole `S₀`), and obey the sup and
integral bounds (the operator norms of (3.10″)).  Then the expected partition function is the
partition function of the gas of hole polymers with the activities `holeKOp`, and these obey
`pe_hole` with the Steiner size: `E Ξ = exp L`, `L = ∑_Y P(Y)`, `∑_{Y ∋ b} |P(Y)| e^{κ' steiner(Y)}
≤ α`, and the bounds on `L` and `Ξ`.  The activity bound is that of `gas_activity_bound` with
`c₁ = 1`, `d = steiner`, rate `κg - 2`, prefactor `3 e^{-p}`. -/
theorem gasOp_pe_hole {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ) {κg κp α : ℝ}
    (hB0 : 0 ≤ B0) (hκg : 0 ≤ κg) (hκ'' : κg ≤ κ'') (hc : 0 ≤ c) (hp : 0 ≤ p) (hκp : 0 ≤ κp)
    (hz : ∀ z, (zs z).Nonempty) (hcr : ∀ z, cr z ⊆ zs z)
    (hcy : ∀ y, cy y = cyF y \ S₀) (hzs : ∀ z, zs z = zsF z \ S₀)
    (hS : ∀ t, IsAnimal H (gasCs cyF zsF t)) (hcl : ∀ t, HoleClosed H S₀ (gasCs cyF zsF t))
    (hβd : ∀ y, DepOn (cy y) (β y)) (hτd : ∀ z, DepOn (zs z) (τ z))
    (hβm : ∀ y, Measurable (β y)) (hτm : ∀ z, Measurable (τ z))
    (hβb : ∀ y, Bdd (β y)) (hτb : ∀ z, Bdd (τ z))
    (hB : ∀ y Φ, ‖β y Φ‖ ≤ B0 * Real.exp (-κ'' * (steiner H (cy y) : ℝ)))
    (hτ : ∀ z, ∫ Φ, ‖τ z Φ‖ ∂(Measure.pi μ) ≤ Real.exp (-p - h * (zs z).card))
    (hzd : ∀ z, (steiner H (zs z) : ℝ) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → gasA cy zs cr C →
      (steiner H (unionCs (gasCs cy zs) C) : ℝ) ≤
        ∑ t ∈ C, (steiner H (gasCs cy zs t) : ℝ) + c * ((C.card : ℝ) - 1))
    {K0g K0h : ℝ} (hK0g : 0 ≤ K0g)
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y),
      Real.exp (-(κ'' - κg) * (steiner H (cy y) : ℝ)) ≤ K0g)
    (hK1 : 1 ≤ K0h)
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤ K0h ^ v)
    (hh : B0 * Real.exp B0 * Real.exp (κg * c) * K0g + κg * (c2 + c) + 1 + 3 + Real.log K0h ≤ h)
    (hq : (Δ : ℝ) ^ 2 * 2 ^ (Δ + 1) * Real.exp (-((κg - 2) - κp - α)) < 1)
    (hcond : 3 * Real.exp (-p) * 2 ^ (Δ + 1) * Real.exp (-((κg - 2) - κp - α)) /
      (1 - (Δ : ℝ) ^ 2 * 2 ^ (Δ + 1) * Real.exp (-((κg - 2) - κp - α))) ≤ α) :
    gasXiOp cy zs cr β τ μ =
      Xi (shareBlock (holeSupp H S₀)) (holeKOp H S₀ cyF zsF cy zs cr β τ μ) ∧
    Xi (shareBlock (holeSupp H S₀)) (holeKOp H S₀ cyF zsF cy zs cr β τ μ) =
      Complex.exp (logSeries (shareBlock (holeSupp H S₀)) (holeKOp H S₀ cyF zsF cy zs cr β τ μ)) ∧
    logSeries (shareBlock (holeSupp H S₀)) (holeKOp H S₀ cyF zsF cy zs cr β τ μ) =
      ∑ Y : Finset B, PY (shareBlock (holeSupp H S₀)) (holeSupp H S₀)
        (holeKOp H S₀ cyF zsF cy zs cr β τ μ) Y ∧
    (∀ b : B, ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ‖PY (shareBlock (holeSupp H S₀)) (holeSupp H S₀)
          (holeKOp H S₀ cyF zsF cy zs cr β τ μ) Y‖ * Real.exp (κp * (steiner H Y : ℝ)) ≤ α) ∧
    ‖logSeries (shareBlock (holeSupp H S₀)) (holeKOp H S₀ cyF zsF cy zs cr β τ μ)‖ ≤
      ((Finset.univ \ S₀).card : ℝ) * α ∧
    Real.exp (-(((Finset.univ \ S₀).card : ℝ) * α)) ≤
      ‖Xi (shareBlock (holeSupp H S₀)) (holeKOp H S₀ cyF zsF cy zs cr β τ μ)‖ ∧
    ‖Xi (shareBlock (holeSupp H S₀)) (holeKOp H S₀ cyF zsF cy zs cr β τ μ)‖ ≤
      Real.exp (((Finset.univ \ S₀).card : ℝ) * α) := by
  have hd : ∀ Y : Finset B, 0 ≤ (steiner H Y : ℝ) := fun Y => Nat.cast_nonneg _
  have hK : ∀ X : HolePolymer H S₀, ‖holeKOp H S₀ cyF zsF cy zs cr β τ μ X‖ ≤
      3 * Real.exp (-p) * Real.exp (-(κg - 2) * (steiner H (holeSupp H S₀ X) : ℝ)) := by
    intro X
    have := norm_holeKOp_le (cyF := cyF) (zsF := zsF) (d := fun Y : Finset B => (steiner H Y : ℝ)) (c1 := 1) hB0 hκg hκ''
      hc zero_le_one hp hd hz hcr hτd hβm hτm hβb hτb hB hτ hzd hG3 hK0g hent hK1 hcount hh X
      (by
        have h1 := card_le_steiner (exists_animal_of_holePolymer X)
        have h2 : ((holeSupp H S₀ X).card : ℝ) ≤ (steiner H (holeSupp H S₀ X) : ℝ) := by
          exact_mod_cast h1
        simp only [one_mul]; linarith)
    simpa [mul_assoc] using this
  have hε : 0 ≤ 3 * Real.exp (-p) := by positivity
  have hpe := pe_hole (S₀ := S₀) hdeg hε hκp hq hcond
    (holeKOp H S₀ cyF zsF cy zs cr β τ μ) hK
  refine ⟨?_, hpe⟩
  rw [gasOp_eq hz hcr hβd hτd hβm hτm hβb hτb]
  exact (xi_fiber (holeSupp H S₀) holeSupp_nonempty _ _
    (fun Y => (gasKOp_eq_sum_holeKOp hcy hzs hS hcl hβm hτm hβb hτb Y))).symm

end Main

end Activity

end Balaban.Polymer
