module

public import Balaban.LargeField.Geometry.DomainsMod
public import Balaban.Localization.PolymerGeometry
public import Balaban.Fluctuation.SizeModDefs

/-!
# Bridge between `DmodOmega` and `DjMod`

`Balaban.LargeField.DmodOmega` (cube level, `Torus d n`) and `Balaban.Fluctuation.DjMod` (site
level, `CTorus`) are two forms of `𝒟_j(mod Ω^c)` of P5 (1.33), both with nearest-neighbour
components of `Ω^c`. The common identification: the fine torus has side `a * n` and the cube
`c ∈ Torus d n` is the block of `a × ⋯ × a` fine sites `{z | siteCube a n z = c}`; a set of cubes
`S` becomes the set of sites `siteCube a n ⁻¹' S`.

* `siteCube`: the cube of a fine site;
* `omegaComp_preimage`: the site component of `Ω^c` through `z` is the preimage of the nn component
  of the cube of `z` (the central lemma, from `nbr_siteCube`: a site step stays in a cube or moves to
  an nn-adjacent cube, and conversely adjacent cubes contain adjacent sites);
* `isDomain_iff_siteConnected`: `X ∈ 𝒟_k` iff the union of its cubes is nonempty and connected;
* `djMod_preimage_iff`: `DjMod` of the unions of cubes iff `DmodOmega` and `π'_j`-union.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Localization Balaban.Fluctuation

variable {d : ℕ}

/-- coordinate cube index -/
def cubeQ (a n : ℕ) {N : ℕ} (x : ZMod N) : ZMod n := (((x.val / a : ℕ)) : ZMod n)

/-- cube index of a fine site -/
def siteCube (a n : ℕ) {N : ℕ} (z : Torus d N) : Torus d n := fun μ => cubeQ a n (z μ)

theorem cubeQ_succ {a n : ℕ} [NeZero a] [NeZero n] (x : ZMod (a * n)) :
    cubeQ a n (x + 1) = cubeQ a n x ∨ cubeQ a n (x + 1) = cubeQ a n x + 1 := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hv := ZMod.val_lt x
  have h1 : (x + 1).val = (x.val + 1) % (a * n) := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
  unfold cubeQ
  rw [h1]
  by_cases hlt : x.val + 1 < a * n
  · rw [Nat.mod_eq_of_lt hlt]
    rw [Nat.succ_div]
    split_ifs
    · right; push_cast; rfl
    · left; simp
  · have heq : x.val + 1 = a * n := by omega
    rw [heq, Nat.mod_self, Nat.zero_div]
    right
    have hdiv : x.val / a = n - 1 := by
      have : x.val = a * (n - 1) + (a - 1) := by
        have : a * n = a * (n - 1) + a := by
          rw [← Nat.mul_succ]; congr 1; omega
        omega
      rw [this, Nat.mul_add_div ha, Nat.div_eq_of_lt (by omega)]
      simp
    rw [hdiv]
    have : ((n - 1 : ℕ) : ZMod n) + 1 = ((n - 1 + 1 : ℕ) : ZMod n) := by push_cast; rfl
    rw [this, Nat.sub_add_cancel hn]; simp


theorem siteCube_step {a n : ℕ} [NeZero a] [NeZero n] (z : Torus d (a * n)) (μ : Fin d) :
    siteCube a n (z + Pi.single μ 1) = siteCube a n z ∨
      siteCube a n (z + Pi.single μ 1) = siteCube a n z + Pi.single μ 1 := by
  rcases cubeQ_succ (a := a) (n := n) (z μ) with h | h
  · left
    funext ν
    by_cases hν : ν = μ
    · subst hν; simpa [siteCube] using h
    · simp [siteCube, Pi.single_eq_of_ne hν]
  · right
    funext ν
    by_cases hν : ν = μ
    · subst hν; simpa [siteCube] using h
    · simp [siteCube, Pi.single_eq_of_ne hν]

theorem nbr_siteCube {a n : ℕ} [NeZero a] [NeZero n] {z z' : Torus d (a * n)} (h : Nbr z z') :
    siteCube a n z' = siteCube a n z ∨ NNAdj (siteCube a n z) (siteCube a n z') := by
  obtain ⟨μ, h | h⟩ := h
  · subst h
    rcases siteCube_step z μ with h | h
    · exact Or.inl h
    · exact Or.inr ⟨μ, Or.inl h⟩
  · subst h
    rcases siteCube_step z' μ with h | h
    · exact Or.inl h.symm
    · exact Or.inr ⟨μ, Or.inr h⟩

theorem nat_pred_div_mod {v a : ℕ} (ha : 0 < a) (hr : 0 < v % a) :
    (v - 1) / a = v / a ∧ (v - 1) % a = v % a - 1 := by
  have h1 := Nat.div_add_mod v a
  have h2 := Nat.mod_lt v ha
  have h3 : v - 1 = a * (v / a) + (v % a - 1) := by omega
  have h4 : (a * (v / a) + (v % a - 1)) / a = v / a := by
    have h6 : (v % a - 1) / a = 0 := Nat.div_eq_of_lt (by omega)
    rw [Nat.mul_add_div ha, h6]; simp
  have h5 : (a * (v / a) + (v % a - 1)) % a = v % a - 1 := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  rw [h3]; exact ⟨h4, h5⟩

theorem rtgMono {α : Type*} {r p : α → α → Prop} (h : ∀ x y, r x y → p x y) {x y : α}
    (hxy : Relation.ReflTransGen r x y) : Relation.ReflTransGen p x y := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

theorem rtgSymmetric {α : Type*} {r : α → α → Prop} (hs : ∀ {x y}, r x y → r y x) {x y : α}
    (h : Relation.ReflTransGen r x y) : Relation.ReflTransGen r y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hs hbc) ih

theorem fibre_reach_aux {a n : ℕ} [NeZero a] [NeZero n] :
    ∀ (m : ℕ) (c : Torus d n) (z : Torus d (a * n)), siteCube a n z = c →
      ∑ μ, (z μ).val % a = m →
      Relation.ReflTransGen (fun u v => siteCube a n u = c ∧ siteCube a n v = c ∧ Nbr u v)
        z (cbase a z) := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro c z hc hm
  by_cases hall : ∀ μ, (z μ).val % a = 0
  · have : cbase a z = z := by
      rw [cbase_eq_sub]
      have : (fun μ => (z μ).val % a) = 0 := funext hall
      rw [this]
      rw [natT_zero, sub_zero]
    rw [this]
  · push Not at hall
    obtain ⟨μ, hμ⟩ := hall
    have hr : 0 < (z μ).val % a := Nat.pos_of_ne_zero hμ
    have hv := ZMod.val_lt (z μ)
    have hvpos : 1 ≤ (z μ).val := by
      by_contra h; push Not at h; have : (z μ).val = 0 := by omega
      rw [this] at hr; simp at hr
    obtain ⟨hd, hm'⟩ := nat_pred_div_mod ha hr
    set z1 : Torus d (a * n) := Function.update z μ (((z μ).val - 1 : ℕ) : ZMod (a * n)) with hz1
    have hz1μ : z1 μ = (((z μ).val - 1 : ℕ) : ZMod (a * n)) := by simp [hz1]
    have hz1ν : ∀ ν, ν ≠ μ → z1 ν = z ν := fun ν hν => by simp [hz1, hν]
    have hval1 : (z1 μ).val = (z μ).val - 1 := by
      rw [hz1μ, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hcub : siteCube a n z1 = siteCube a n z := by
      funext ν
      by_cases hν : ν = μ
      · subst hν; simp only [siteCube, cubeQ, hval1, hd]
      · simp [siteCube, hz1ν ν hν]
    have hzeq : z = z1 + Pi.single μ 1 := by
      funext ν
      by_cases hν : ν = μ
      · subst hν
        simp only [Pi.add_apply, Pi.single_eq_same, hz1μ]
        have : (((z ν).val - 1 : ℕ) : ZMod (a * n)) + 1 = (((z ν).val - 1 + 1 : ℕ) : ZMod (a * n)) := by
          push_cast; rfl
        rw [this, Nat.sub_add_cancel hvpos, ZMod.natCast_zmod_val]
      · simp [hz1ν ν hν, Pi.single_eq_of_ne hν]
    have hcb : cbase a z1 = cbase a z := by
      funext ν
      by_cases hν : ν = μ
      · subst hν; simp only [cbase, hval1, hd]
      · simp only [cbase, hz1ν ν hν]
    have hlt : ∑ ν, (z1 ν).val % a < m := by
      rw [← hm]
      apply Finset.sum_lt_sum
      · intro ν _
        by_cases hν : ν = μ
        · subst hν; rw [hval1, hm']; omega
        · rw [hz1ν ν hν]
      · exact ⟨μ, Finset.mem_univ _, by rw [hval1, hm']; omega⟩
    have step : siteCube a n z = c ∧ siteCube a n z1 = c ∧ Nbr z z1 :=
      ⟨hc, hcub.trans hc, μ, Or.inr hzeq⟩
    have := ih _ hlt c z1 (hcub.trans hc) rfl
    rw [hcb] at this
    exact Relation.ReflTransGen.head step this


theorem siteCube_eq_cbase {a n : ℕ} [NeZero a] [NeZero n] {z z' : Torus d (a * n)}
    (h : siteCube a n z = siteCube a n z') : cbase a z = cbase a z' := by
  funext μ
  have h1 := congrFun h μ
  have hz : (z μ).val / a < n :=
    (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne a))).mpr (lt_of_lt_of_eq (ZMod.val_lt (z μ)) (mul_comm a n))
  have hz' : (z' μ).val / a < n :=
    (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne a))).mpr (lt_of_lt_of_eq (ZMod.val_lt (z' μ)) (mul_comm a n))
  have h2 : (z μ).val / a = (z' μ).val / a := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
    rwa [Nat.mod_eq_of_lt hz, Nat.mod_eq_of_lt hz'] at this
  simp only [cbase, h2]

theorem fibre_reach {a n : ℕ} [NeZero a] [NeZero n] {z z' : Torus d (a * n)}
    (h : siteCube a n z = siteCube a n z') :
    Relation.ReflTransGen
      (fun u v => siteCube a n u = siteCube a n z ∧ siteCube a n v = siteCube a n z ∧ Nbr u v) z z' := by
  have h1 := fibre_reach_aux (a := a) (n := n) _ (siteCube a n z) z rfl rfl
  have h2 := fibre_reach_aux (a := a) (n := n) _ (siteCube a n z) z' h.symm rfl
  rw [← siteCube_eq_cbase h] at h2
  refine h1.trans (rtgSymmetric ?_ h2)
  rintro x y ⟨hx, hy, hn⟩
  exact ⟨hy, hx, hn.symm⟩

theorem cubeQ_nat_lt {a n cv k : ℕ} [NeZero a] [NeZero n] (hcv : cv < n) (hk : k < a) :
    cubeQ a n (((a * cv + k : ℕ)) : ZMod (a * n)) = (cv : ZMod n) := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have hlt : a * cv + k < a * n := by
    calc a * cv + k < a * cv + a := by omega
      _ = a * (cv + 1) := by ring
      _ ≤ a * n := Nat.mul_le_mul_left _ hcv
  unfold cubeQ
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.mul_add_div ha, Nat.div_eq_of_lt hk]
  simp

theorem cubeQ_nat_top {a n cv : ℕ} [NeZero a] [NeZero n] :
    cubeQ a n (((a * cv + a : ℕ)) : ZMod (a * n)) = ((cv + 1 : ℕ) : ZMod n) := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  unfold cubeQ
  have : a * cv + a = a * (cv + 1) := by ring
  rw [ZMod.val_natCast, this, Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ ha, ZMod.natCast_mod]

theorem exists_adj_fibres {a n : ℕ} [NeZero a] [NeZero n] {c c' : Torus d n} (h : NNAdj c c') :
    ∃ z z' : Torus d (a * n), siteCube a n z = c ∧ siteCube a n z' = c' ∧ Nbr z z' := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have key : ∀ (c : Torus d n) (μ : Fin d), ∃ z z' : Torus d (a * n), siteCube a n z = c ∧
      siteCube a n z' = c + Pi.single μ 1 ∧ Nbr z z' := by
    intro c μ
    let z : Torus d (a * n) := fun ν =>
      ((a * (c ν).val + (if ν = μ then a - 1 else 0) : ℕ) : ZMod (a * n))
    refine ⟨z, z + Pi.single μ 1, ?_, ?_, μ, Or.inl rfl⟩
    · funext ν
      by_cases hν : ν = μ
      · subst hν
        have := cubeQ_nat_lt (a := a) (n := n) (cv := (c ν).val) (k := a - 1) (ZMod.val_lt _) (by omega)
        simpa [siteCube, z] using this
      · have := cubeQ_nat_lt (a := a) (n := n) (cv := (c ν).val) (k := 0) (ZMod.val_lt _) ha
        simpa [siteCube, z, hν] using this
    · funext ν
      by_cases hν : ν = μ
      · subst hν
        have := cubeQ_nat_top (a := a) (n := n) (cv := (c ν).val)
        have e : z ν + 1 = ((a * (c ν).val + a : ℕ) : ZMod (a * n)) := by
          simp only [z, ite_true]
          have : a * (c ν).val + a = (a * (c ν).val + (a - 1)) + 1 := by omega
          rw [this]; push_cast; rfl
        simp only [siteCube, Pi.add_apply, Pi.single_eq_same, e, this]
        push_cast; rw [ZMod.natCast_zmod_val]
      · have := cubeQ_nat_lt (a := a) (n := n) (cv := (c ν).val) (k := 0) (ZMod.val_lt _) ha
        simpa [siteCube, z, hν, Pi.single_eq_of_ne hν] using this
  obtain ⟨μ, h | h⟩ := h
  · obtain ⟨z, z', h1, h2, h3⟩ := key c μ
    exact ⟨z, z', h1, h2.trans h.symm, h3⟩
  · obtain ⟨z, z', h1, h2, h3⟩ := key c' μ
    exact ⟨z', z, h2.trans h.symm, h1, h3.symm⟩


theorem siteCube_surj {a n : ℕ} [NeZero a] [NeZero n] (c : Torus d n) :
    ∃ z : Torus d (a * n), siteCube a n z = c := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  refine ⟨fun ν => ((a * (c ν).val + 0 : ℕ) : ZMod (a * n)), ?_⟩
  funext ν
  have := cubeQ_nat_lt (a := a) (n := n) (cv := (c ν).val) (k := 0) (ZMod.val_lt _) ha
  simpa [siteCube] using this

theorem reach_down {a n N : ℕ} [NeZero a] [NeZero n] (hN : N = a * n) (T : Set (Torus d n))
    {z z' : Torus d N}
    (h : Relation.ReflTransGen (fun u v => u ∈ siteCube a n ⁻¹' T ∧ v ∈ siteCube a n ⁻¹' T ∧ Nbr u v) z z') :
    Relation.ReflTransGen (fun u v => u ∈ T ∧ v ∈ T ∧ NNAdj u v) (siteCube a n z) (siteCube a n z') := by
  subst hN
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    obtain ⟨hb, hc, hn⟩ := hbc
    rcases nbr_siteCube hn with h' | h'
    · rw [h']; exact ih
    · exact ih.tail ⟨hb, hc, h'⟩

theorem reach_up {a n N : ℕ} [NeZero a] [NeZero n] (hN : N = a * n) (T : Set (Torus d n))
    {c c' : Torus d n}
    (h : Relation.ReflTransGen (fun u v => u ∈ T ∧ v ∈ T ∧ NNAdj u v) c c') (hc : c ∈ T)
    {z z' : Torus d N} (hz : siteCube a n z = c) (hz' : siteCube a n z' = c') :
    Relation.ReflTransGen (fun u v => u ∈ siteCube a n ⁻¹' T ∧ v ∈ siteCube a n ⁻¹' T ∧ Nbr u v) z z' := by
  subst hN
  induction h generalizing z' with
  | refl =>
    subst hz
    refine rtgMono ?_ (fibre_reach (a := a) (n := n) (z := z) (z' := z') hz'.symm)
    rintro u v ⟨hu, hv, hn⟩
    exact ⟨by simp only [Set.mem_preimage, hu]; exact hc, by simp only [Set.mem_preimage, hv]; exact hc, hn⟩
  | @tail b e _ hbe ih =>
    obtain ⟨hb, he, hadj⟩ := hbe
    obtain ⟨w0, w1, h0, h1, hn⟩ := exists_adj_fibres (a := a) (n := n) hadj
    have r0 := ih h0
    have r1 := fibre_reach (a := a) (n := n) (z := w1) (z' := z') (h1.trans hz'.symm)
    refine (r0.tail ⟨by simpa [h0] using hb, by simpa [h1] using he, hn⟩).trans
      (rtgMono ?_ r1)
    rintro u v ⟨hu, hv, hn⟩
    exact ⟨by simp only [Set.mem_preimage, hu, h1]; exact he,
      by simp only [Set.mem_preimage, hv, h1]; exact he, hn⟩


theorem siteCube_surj' {a n N : ℕ} [NeZero a] [NeZero n] (hN : N = a * n) (c : Torus d n) :
    ∃ z : Torus d N, siteCube a n z = c := by
  subst hN; exact siteCube_surj c

theorem preimage_subset_iff {a n N : ℕ} [NeZero a] [NeZero n] (hN : N = a * n)
    (S X : Set (Torus d n)) : siteCube a n ⁻¹' S ⊆ (siteCube a n ⁻¹' X : Set (Torus d N)) ↔ S ⊆ X := by
  constructor
  · intro h c hc
    obtain ⟨z, rfl⟩ := siteCube_surj' hN c
    exact h hc
  · intro h z hz
    exact h hz

theorem preimage_disjoint_iff {a n N : ℕ} [NeZero a] [NeZero n] (hN : N = a * n)
    (S X : Set (Torus d n)) :
    Disjoint (siteCube a n ⁻¹' S : Set (Torus d N)) (siteCube a n ⁻¹' X) ↔ Disjoint S X := by
  simp only [Set.disjoint_left]
  constructor
  · intro h c hc hX
    obtain ⟨z, rfl⟩ := siteCube_surj' hN c
    exact h hc hX
  · intro h z hz hX
    exact h hz hX

section Bridge

variable {L N₁ m₁ K : ℕ}

/-- The fine-site components of the preimage of `Ω` are the preimages of the nn components of
`Ω^c` of the cubes. -/
theorem omegaComp_preimage {a n : ℕ} [NeZero a] [NeZero n]
    (hN : (N₁ * L ^ m₁) * L ^ K = a * n) (Ω : Set (Torus d n))
    (z : Balaban.Localization.CTorus d L N₁ m₁ K) (hz : siteCube a n z ∈ Ωᶜ) :
    OmegaComp (siteCube a n ⁻¹' Ω : Set (Balaban.Localization.CTorus d L N₁ m₁ K)) z =
      siteCube a n ⁻¹' nnComp Ωᶜ (siteCube a n z) := by
  have e : (siteCube a n ⁻¹' Ω : Set (Balaban.Localization.CTorus d L N₁ m₁ K))ᶜ =
      siteCube a n ⁻¹' Ωᶜ := (Set.preimage_compl).symm
  ext y
  constructor
  · rintro ⟨hy, hr⟩
    rw [e] at hy hr
    exact ⟨hy, reach_down hN Ωᶜ hr⟩
  · rintro ⟨hy, hr⟩
    refine ⟨by rw [e]; exact hy, ?_⟩
    rw [e]
    exact reach_up hN Ωᶜ hr hz rfl rfl

/-- `X ∈ 𝒟_k` at cube level iff the union of its cubes is a nonempty `Nbr`-connected set of
sites. -/
theorem isDomain_iff_siteConnected {a n : ℕ} [NeZero a] [NeZero n]
    (hN : (N₁ * L ^ m₁) * L ^ K = a * n) (X : Finset (Torus d n)) :
    IsDomain X ↔ ((siteCube a n ⁻¹' (X : Set (Torus d n)) :
        Set (Balaban.Localization.CTorus d L N₁ m₁ K)).Nonempty ∧
      SiteConnected (siteCube a n ⁻¹' (X : Set (Torus d n)) :
        Set (Balaban.Localization.CTorus d L N₁ m₁ K))) := by
  constructor
  · rintro ⟨⟨c, hc⟩, hconn⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨z, rfl⟩ := siteCube_surj' hN c
      exact ⟨z, hc⟩
    · intro x hx y hy
      exact reach_up hN (X : Set (Torus d n)) (hconn _ hx _ hy) hx rfl rfl
  · rintro ⟨⟨z, hz⟩, hconn⟩
    refine ⟨⟨_, hz⟩, ?_⟩
    intro c hc c' hc'
    obtain ⟨x, rfl⟩ := siteCube_surj' hN c
    obtain ⟨y, rfl⟩ := siteCube_surj' hN c'
    exact reach_down hN (X : Set (Torus d n)) (hconn x hc y hc')

/-- **Bridge** between the large-field predicate `DmodOmega` (cube level) and the fluctuation
predicate `DjMod` (site level): under the identification of a cube `c` with its `a × ⋯ × a` block of
fine sites, `X ∈ 𝒟_k(mod Ω^c)` iff the union of its cubes is in `𝒟_j(mod (Ω-sites)^c)` and is a union of `π'_j`-cubes. -/
theorem djMod_preimage_iff {a n : ℕ} [NeZero a] [NeZero n] (m₀ j : ℕ)
    (hN : (N₁ * L ^ m₁) * L ^ K = a * n) (Ω : Set (Torus d n)) (X : Finset (Torus d n)) :
    DjMod (m₀ := m₀) (j := j) (siteCube a n ⁻¹' Ω : Set (Balaban.Localization.CTorus d L N₁ m₁ K))
        (siteCube a n ⁻¹' (X : Set (Torus d n))) ↔
      DmodOmega Ω X ∧ IsPiPrimeUnion m₀ j
        (siteCube a n ⁻¹' (X : Set (Torus d n)) : Set (Balaban.Localization.CTorus d L N₁ m₁ K)) := by
  have hdom := isDomain_iff_siteConnected (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) hN X
  have hcomp : (∀ z ∈ (siteCube a n ⁻¹' Ω : Set (Balaban.Localization.CTorus d L N₁ m₁ K))ᶜ,
      OmegaComp (siteCube a n ⁻¹' Ω : Set (Balaban.Localization.CTorus d L N₁ m₁ K)) z ⊆
          siteCube a n ⁻¹' (X : Set (Torus d n)) ∨
        Disjoint (OmegaComp (siteCube a n ⁻¹' Ω : Set (Balaban.Localization.CTorus d L N₁ m₁ K)) z)
          (siteCube a n ⁻¹' (X : Set (Torus d n)))) ↔
      ∀ c ∈ Ωᶜ, nnComp Ωᶜ c ⊆ (X : Set (Torus d n)) ∨ Disjoint (nnComp Ωᶜ c) (X : Set (Torus d n)) := by
    constructor
    · intro h c hc
      obtain ⟨z, rfl⟩ := siteCube_surj' (N := (N₁ * L ^ m₁) * L ^ K) hN c
      have := h z hc
      rw [omegaComp_preimage hN Ω z hc, preimage_subset_iff hN, preimage_disjoint_iff hN] at this
      exact this
    · intro h z hz
      have := h _ hz
      rw [omegaComp_preimage hN Ω z hz, preimage_subset_iff hN, preimage_disjoint_iff hN]
      exact this
  constructor
  · rintro ⟨⟨hne, hpi, hsc⟩, hc⟩
    exact ⟨⟨hdom.mpr ⟨hne, hsc⟩, hcomp.mp hc⟩, hpi⟩
  · rintro ⟨⟨hd, hc⟩, hpi⟩
    obtain ⟨hne, hsc⟩ := hdom.mp hd
    exact ⟨⟨hne, hpi, hsc⟩, hcomp.mpr hc⟩

end Bridge

end Balaban.LargeField
