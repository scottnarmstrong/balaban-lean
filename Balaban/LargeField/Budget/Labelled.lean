module

public import Balaban.LargeField.Budget.Summability
public import Balaban.LargeField.Budget.Exponents

/-!
# Kept labels in the summability (Part II, Lemma II.5.15)

* `logC_eq_record`: the recursive `log C_k` of Definition II.5.11 (`RegionHistory.logC`) is the
  value `LocalHistory.logC` read off the localized history, plus the label costs of the kept ripe
  ancestors (`keptSum`).
* `sum_inv_logC_labelled`: the summability (1.27) for localized histories *with kept labels*.
  A labelled localized history is a record `a` together with the labels `ϰ` of the kept ripe
  lineage components (`T`, a set of pairs `(position, label)`, a position being a scale and a
  component); its combinatoric factor is `C_k(a) ∏ C_dec(ϰ)`.  The labels satisfy
  `∑_ϰ C_dec(ϰ)^{-1} ≤ 1` (S3).  As in the paper, the positions of the kept components are
  a function of the localized history (deterministic bookkeeping, Definition I.4.7); this is the
  hypothesis `hpos` on the family.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) {M : ℕ} [NeZero M]

open Classical in
/-- The label costs `δ` of the kept ripe ancestors of a component (itself included). -/
noncomputable def keptSum (δ : ∀ k, H.Comp k → ℝ) : ∀ k, H.Comp k → ℝ
  | 0, _ => 0
  | k + 1, Z' =>
      ∑ c ∈ H.parts k Z', keptSum δ k c + if H.IsKeptEvent (k + 1) Z' then δ (k + 1) Z' else 0

/-- Definition II.5.11 against the localized history: `log C_k(Z, 𝔞) = (the value read off the
localized history) + (the label costs of the kept ripe ancestors)`. -/
theorem logC_eq_record (δ : ∀ k, H.Comp k → ℝ) :
    ∀ (k : ℕ), k ≤ K → ∀ c : H.Comp k,
      H.logC δ k c = (localHistory H M K k c).logC k + H.keptSum δ k c := by
  intro k
  induction k with
  | zero => intro _ c; exact (H.F.isEmpty_comp_zero.false c).elim
  | succ k ih =>
    intro hkK Z'
    have hcnt := H.card_oldCubes_add_outCubes (by omega) Z'
    have hcnt' : ((H.oldCubes k Z').card : ℝ) + (H.outCubes k Z').card =
        (S.L : ℝ) ^ S.d * Z'.1.card := by exact_mod_cast hcnt
    rw [H.logC_succ hkK Z']
    simp only [logC, keptSum, logCPre]
    have hsum : ∑ c ∈ H.parts k Z', H.logC δ k c =
        ∑ c ∈ H.parts k Z', (localHistory H M K k c).logC k +
          ∑ c ∈ H.parts k Z', H.keptSum δ k c := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => ih (by omega) c
    rw [hsum]
    have : (5 * ((S.L : ℝ) ^ S.d * Z'.1.card) - (H.oldCubes k Z').card) / 4 =
        (H.oldCubes k Z').card + 5 / 4 * (H.outCubes k Z').card := by
      rw [← hcnt']; ring
    rw [this]
    ring

end RegionHistory

/-- A position of a kept ripe component: the scale `j` and the component (a set of
`π_j`-cubes). -/
abbrev KeptPos (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] : Type :=
  Σ j : ℕ, Finset (Torus S.d (n j))

section Labelled

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  {Lab : Type*} [Nonempty Lab]

open RegionHistory in
/-- **Lemma II.5.15 with kept labels**: for `L^d ≥ 8`, `k ≤ K`, `∑_ϰ C_dec(ϰ)^{-1} ≤ 1` (S3), and
a finite family `𝒜` of labelled localized histories `(a, T)` of the component `Y` (`a ∈ 𝔥_k(Y)`,
`T` the labels of the kept ripe lineage components, at most one label per position, the positions
determined by `a`),
`∑_{(a,T) ∈ 𝒜} C_k(a)^{-1} ∏_{(p,ϰ) ∈ T} C_dec(ϰ)^{-1} ≤ 1`. -/
theorem sum_inv_logC_labelled (hLd : 8 ≤ S.L ^ S.d) {k : ℕ} (hkK : k ≤ K)
    (Y : Finset (Torus S.d (n k))) (cdec : Lab → ℝ)
    (hlab : ∀ F : Finset Lab, ∑ ϰ ∈ F, Real.exp (-cdec ϰ) ≤ 1)
    (𝒜 : Finset (LocalHistory S n M K × Finset (KeptPos S n × Lab)))
    (hhist : ∀ x ∈ 𝒜, x.1 ∈ histSet S n R k0 M K k Y)
    (hfun : ∀ x ∈ 𝒜, ∀ p ϰ ϰ', (p, ϰ) ∈ x.2 → (p, ϰ') ∈ x.2 → ϰ = ϰ')
    (hpos : ∀ x ∈ 𝒜, ∀ x' ∈ 𝒜, x.1 = x'.1 → x.2.image Prod.fst = x'.2.image Prod.fst) :
    ∑ x ∈ 𝒜, Real.exp (-(x.1.logC k + ∑ t ∈ x.2, cdec t.2)) ≤ 1 := by
  classical
  -- the label of a position
  let lab : (LocalHistory S n M K × Finset (KeptPos S n × Lab)) → KeptPos S n → Lab :=
    fun x p => if h : ∃ ϰ, (p, ϰ) ∈ x.2 then h.choose else Classical.arbitrary Lab
  have hlab_spec : ∀ x ∈ 𝒜, ∀ p ϰ, (p, ϰ) ∈ x.2 → lab x p = ϰ := by
    intro x hx p ϰ hp
    have h : ∃ ϰ, (p, ϰ) ∈ x.2 := ⟨ϰ, hp⟩
    simp only [lab, h, dite_true]
    exact hfun x hx p _ _ h.choose_spec hp
  have hlab_mem : ∀ x : (LocalHistory S n M K × Finset (KeptPos S n × Lab)), ∀ p,
      p ∈ x.2.image Prod.fst → (p, lab x p) ∈ x.2 := by
    intro x p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    have h : ∃ ϰ, (t.1, ϰ) ∈ x.2 := ⟨t.2, ht⟩
    simp only [lab, h, dite_true]
    exact h.choose_spec
  -- the cost of the labels
  have hcost : ∀ x ∈ 𝒜, ∑ t ∈ x.2, cdec t.2 = ∑ p ∈ x.2.image Prod.fst, cdec (lab x p) := by
    intro x hx
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun t ht => ?_
      rw [hlab_spec x hx t.1 t.2 ht]
    · intro t ht t' ht' h
      have h1 : (t.1, t.2) ∈ x.2 := ht
      have h2 : (t'.1, t'.2) ∈ x.2 := ht'
      rw [h] at h1
      exact Prod.ext h (hfun x hx t'.1 _ _ h1 h2)
  -- group by the record
  have hA : ∀ x ∈ 𝒜, x.1 ∈ 𝒜.image Prod.fst := fun x hx => Finset.mem_image_of_mem _ hx
  have hsumA : ∑ a ∈ 𝒜.image Prod.fst, Real.exp (-(a.logC k)) ≤ 1 :=
    sum_inv_logC_le_one hLd k hkK Y _ (by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      exact hhist x hx)
  have hfibre : ∀ a ∈ 𝒜.image Prod.fst,
      ∑ x ∈ 𝒜.filter (fun x => x.1 = a), Real.exp (-(x.1.logC k + ∑ t ∈ x.2, cdec t.2)) ≤
        Real.exp (-(a.logC k)) := by
    intro a ha
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp ha
    set Φ := 𝒜.filter (fun x => x.1 = x0.1) with hΦ
    set P := x0.2.image Prod.fst with hP
    have hΦmem : ∀ x ∈ Φ, x ∈ 𝒜 ∧ x.1 = x0.1 := fun x hx => Finset.mem_filter.mp hx
    have hPx : ∀ x ∈ Φ, x.2.image Prod.fst = P := fun x hx =>
      hpos x (hΦmem x hx).1 x0 hx0 (hΦmem x hx).2
    let Ψ : (LocalHistory S n M K × Finset (KeptPos S n × Lab)) → ∀ p ∈ P, Lab :=
      fun x p _ => lab x p
    let B : KeptPos S n → Finset Lab := fun p => Φ.image fun x => lab x p
    have hinj : Set.InjOn Ψ Φ := by
      intro x hx x' hx' h
      have hxs : x.1 = x'.1 := (hΦmem x hx).2.trans (hΦmem x' hx').2.symm
      have hl : ∀ p ∈ P, lab x p = lab x' p := fun p hp => congrFun (congrFun h p) hp
      refine Prod.ext hxs ?_
      ext ⟨p, ϰ⟩
      constructor
      · intro hm
        have hp : p ∈ P := by rw [← hPx x hx]; exact Finset.mem_image_of_mem _ hm
        have := hlab_mem x' p (by rw [hPx x' hx']; exact hp)
        rw [← hl p hp, hlab_spec x (hΦmem x hx).1 p ϰ hm] at this
        exact this
      · intro hm
        have hp : p ∈ P := by rw [← hPx x' hx']; exact Finset.mem_image_of_mem _ hm
        have := hlab_mem x p (by rw [hPx x hx]; exact hp)
        rw [hl p hp, hlab_spec x' (hΦmem x' hx').1 p ϰ hm] at this
        exact this
    have hsub : Φ.image Ψ ⊆ P.pi B := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_pi.mpr fun q _ => Finset.mem_image.mpr ⟨x, hx, rfl⟩
    calc ∑ x ∈ Φ, Real.exp (-(x.1.logC k + ∑ t ∈ x.2, cdec t.2))
        = Real.exp (-(x0.1.logC k)) *
            ∑ x ∈ Φ, ∏ p ∈ P.attach, Real.exp (-cdec (Ψ x p.1 p.2)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x hx => ?_
          obtain ⟨hxA, hx1⟩ := hΦmem x hx
          rw [hcost x hxA, hPx x hx, hx1, neg_add, Real.exp_add, ← Finset.sum_neg_distrib,
            Real.exp_sum]
          rw [Finset.prod_attach P (fun p => Real.exp (-cdec (lab x p)))]
        _ = Real.exp (-(x0.1.logC k)) *
            ∑ p ∈ Φ.image Ψ, ∏ q ∈ P.attach, Real.exp (-cdec (p q.1 q.2)) := by
          rw [Finset.sum_image hinj]
        _ ≤ Real.exp (-(x0.1.logC k)) *
            ∑ p ∈ P.pi B, ∏ q ∈ P.attach, Real.exp (-cdec (p q.1 q.2)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)) (Real.exp_pos _).le
        _ = Real.exp (-(x0.1.logC k)) * ∏ p ∈ P, ∑ ϰ ∈ B p, Real.exp (-cdec ϰ) := by
          rw [Finset.prod_sum]
        _ ≤ Real.exp (-(x0.1.logC k)) * 1 :=
          mul_le_mul_of_nonneg_left (Finset.prod_le_one₀
            (fun _ _ => Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
            (fun p _ => hlab (B p))) (Real.exp_pos _).le
        _ = Real.exp (-(x0.1.logC k)) := mul_one _
  calc ∑ x ∈ 𝒜, Real.exp (-(x.1.logC k + ∑ t ∈ x.2, cdec t.2))
      = ∑ a ∈ 𝒜.image Prod.fst, ∑ x ∈ 𝒜.filter (fun x => x.1 = a),
          Real.exp (-(x.1.logC k + ∑ t ∈ x.2, cdec t.2)) :=
        (Finset.sum_fiberwise_of_maps_to hA _).symm
    _ ≤ ∑ a ∈ 𝒜.image Prod.fst, Real.exp (-(a.logC k)) := Finset.sum_le_sum hfibre
    _ ≤ 1 := hsumA

end Labelled

end Balaban.LargeField
