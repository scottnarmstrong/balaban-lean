module

public import Balaban.LargeField.Counter.Main
public import Balaban.LargeField.Counter.LemmaV
public import Balaban.LargeField.Geometry.Components
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# LF-2 (Part I, Theorem I.5.4): the abstract region history and the theorem

`LF2Hyp` is the abstract history of §I.5.2 on cube tori `𝕋_k = Torus d (n k)`: the sets `Z^pre_k`,
the new cubes, the components (for the width `ω_k`) with their spines and bookkeeping, the sets
of removed components, the reals `G^pre_k`, `G_k`, and the hypotheses (B), (Rg) and the
bookkeeping rules.  The counts `|Z'|_#` and `|𝒩_k ∩ Z'|_#` are cardinalities of the actual sets.

The geometric input of Lemma I.4.8 enters through `spine_contains`, the containment (3.1)
`Z ⊂ N_{ρ_k+4}(Γ(Z))`; Lemma V then gives the volume bound, and (4.1) is the field `len_gen`
of `book_rule`.  (G1), (G2) and (H-T) are used only to prove Lemma I.4.8 (spine consistency) and
do not occur in the counting; they are not fields.
-/

@[expose] public section

namespace Balaban.LargeField

theorem Setting.Ok.two_le_c0 {S : Setting} (ok : S.Ok) : 2 ≤ S.c0 := by
  have h := ok.c0_sS
  have hL := ok.cast_L_ge
  have hs : (0 : ℝ) ≤ S.sS := Nat.cast_nonneg _
  have h1 := ok.one_le_c0
  by_contra hc
  have : S.c0 = 1 := by omega
  rw [this] at h
  have : (0 : ℝ) < (S.L : ℝ)⁻¹ := by positivity
  simp at h
  linarith

theorem Setting.Ok.two_le_rho {S : Setting} (ok : S.Ok) (j : ℕ) : (2 : ℝ) ≤ S.rho j := by
  have h1 : 2 ≤ S.c0 := ok.two_le_c0
  have h2 := ok.one_le_r j
  unfold Setting.rho
  have : 2 ≤ S.c0 * S.r j := by nlinarith
  exact_mod_cast this

/-- The components of `Z^pre_k` for the width `ω_k`. -/
abbrev LF2Comp (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (Zp : ∀ k, Finset (Torus S.d (n k)))
    (k : ℕ) : Type :=
  ↥(comps (S.omega k) (Zp k))

/-- The abstract history of LF-2 (§I.5.2) on the cube tori `Torus d (n k)`. -/
structure LF2Hyp (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (k0 K : ℕ) where
  /-- `n_k = L n_{k+1}` -/
  n_succ : ∀ k, k < K → n k = S.L * n (k + 1)
  /-- `Z^pre_k ⊂ 𝕋_k` -/
  Zp : ∀ k, Finset (Torus S.d (n k))
  /-- `Z_0 = ∅` -/
  Zp_zero : Zp 0 = ∅
  /-- the new large-field cubes `𝒩_k` -/
  newCubes : ∀ k, Finset (Torus S.d (n k))
  /-- components removed by `R^{(k)}` -/
  rem : ∀ k, Finset (LF2Comp S n Zp k)
  rem_empty : ∀ k, (k = 0 ∨ k0 < k) → rem k = ∅
  /-- the spine `Γ(Z)` of a component -/
  spine : ∀ k, LF2Comp S n Zp k → Spine S.d
  /-- the bookkeeping data of a component -/
  bk : ∀ k, LF2Comp S n Zp k → Book
  bk_len : ∀ k c, (bk k c).len = (spine k c).length
  rem_ripe : ∀ k, ∀ c ∈ rem k, S.Ripe k (bk k c)
  /-- the component of `Z^pre_{k+1}` containing `c^↑` -/
  succ : ∀ k, LF2Comp S n Zp k → LF2Comp S n Zp (k + 1)
  /-- the old parts of a component of `Z^pre_{k+1}` -/
  parts : ∀ k, LF2Comp S n Zp (k + 1) → Finset (LF2Comp S n Zp k)
  mem_parts : ∀ k (c : LF2Comp S n Zp k) (Z' : LF2Comp S n Zp (k + 1)),
    c ∈ parts k Z' ↔ c ∉ rem k ∧ succ k c = Z'
  /-- `G^pre_k(Z)` -/
  Gp : ∀ k, LF2Comp S n Zp k → ℝ
  /-- `G_k(Z)` -/
  G : ∀ k, LF2Comp S n Zp k → ℝ
  /-- (3.1), the output of Lemma I.4.8: `Z ⊂ N_{ρ_k+4}(Γ(Z))` -/
  spine_contains : ∀ k, 1 ≤ k → k ≤ K → ∀ c : LF2Comp S n Zp k,
    ((c.1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k))) ⊆
      NR ((S.rho k : ℝ) + 4) ((spine k c).proj (n k))
  /-- every component contains a seed -/
  seed_pos : ∀ k, k < K → ∀ Z' : LF2Comp S n Zp (k + 1),
    1 ≤ (parts k Z').card + (Z'.1 ∩ newCubes (k + 1)).card
  /-- the bookkeeping rules (Definition I.4.7, (T1)–(T5)) -/
  book_rule : ∀ k, k < K → ∀ Z' : LF2Comp S n Zp (k + 1),
    S.BookRule (k + 1) (k + 1 ≤ k0) (parts k Z') (fun c => S.postBook k0 k (bk k c))
      (Z'.1 ∩ newCubes (k + 1)).card (bk (k + 1) Z')
  /-- (B) -/
  budget : ∀ k, k < K → ∀ Z' : LF2Comp S n Zp (k + 1),
    ∑ c ∈ parts k Z', G k c + S.g k * (Z'.1 ∩ newCubes (k + 1)).card -
        S.cv * S.lam (k + 1) * Z'.1.card ≤ Gp (k + 1) Z'
  /-- (Rg), kept ripe components -/
  rg_ripe : ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : LF2Comp S n Zp k, c ∉ rem k → S.Ripe k (bk k c) →
    Gp k c - S.CR * S.lam k ^ (2 * S.d + 1) + S.A3' * S.lam k ^ S.pR ≤ G k c
  /-- (Rg), non-ripe components -/
  rg_nonripe : ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : LF2Comp S n Zp k, c ∉ rem k → ¬ S.Ripe k (bk k c) →
    G k c = Gp k c
  /-- (Rg), `k > k₀` -/
  rg_frozen : ∀ k, k0 < k → ∀ c : LF2Comp S n Zp k, G k c = Gp k c

namespace LF2Hyp

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {k0 K : ℕ}

/-- The numerical history underlying an `LF2Hyp`. -/
noncomputable def toCounterHist (ok : S.Ok) (H : LF2Hyp S n k0 K) :
    CounterHist S k0 K (LF2Comp S n H.Zp) where
  isEmpty0 := ⟨fun c => by
    obtain ⟨x, hx⟩ := comp_nonempty c.2
    have h := comp_subset c.2 hx
    have h' : x ∈ (∅ : Finset (Torus S.d (n 0))) := by rw [← H.Zp_zero]; exact h
    simp at h'⟩
  bk := H.bk
  rem := H.rem
  rem_empty := H.rem_empty
  rem_ripe := H.rem_ripe
  succ := H.succ
  parts := H.parts
  mem_parts := H.mem_parts
  newc := fun k Z' => (Z'.1 ∩ H.newCubes k).card
  vol := fun k Z' => (Z'.1.card : ℝ)
  Gp := H.Gp
  G := H.G
  seed_pos := H.seed_pos
  book_rule := H.book_rule
  vol_bound := fun k hk Z' => by
    have h := lemmaV (H.spine (k + 1) Z') (by have := ok.three_le_d; omega) (ok.two_le_rho (k + 1))
      Z'.1 (H.spine_contains (k + 1) (by omega) (by omega) Z')
    rw [H.bk_len]
    unfold Typing.CV
    calc (Z'.1.card : ℝ) ≤ _ := h
      _ = _ := by ring
  budget := fun k hk Z' => by
    have := H.budget k hk Z'
    simpa using this
  rg_ripe := H.rg_ripe
  rg_nonripe := H.rg_nonripe
  rg_frozen := H.rg_frozen

end LF2Hyp

/-- **LF-2** (Theorem I.5.4; an internal lemma, never frozen).  Assume the typing data and the
conditions `(K)`, (H-λ), and `λ₀ ≥ λ_*` (`S.Good`), the abstract history `H`, and `k₀ ≤ K ≤ k̂_f`
with `k̂_f - k₀ < λ_{k₀}` and `λ_{k̂_f} ≤ (d/2) λ_{k₀} + c_H`.  Then (i) (H6′)^pre and (H6′) for
`1 ≤ k ≤ min {k₀, K}`; (ii) (H6♭) for `k₀ ≤ k ≤ K`, `k ≥ 1`; (iii) the shape statements, a ripe
component is `Active` with core `k₁(k)`; (iv) the lower bounds for `G`. -/
theorem LF2 {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {k0 K khat : ℕ} (G : S.Good)
    (H : LF2Hyp S n k0 K) (hk0K : k0 ≤ K) (hKk : K ≤ khat)
    (hH1 : (khat : ℝ) - k0 < S.lam k0) (hH2 : S.lam khat ≤ S.d / 2 * S.lam k0 + S.cH) :
    CounterConclusion (H.toCounterHist G.ok) khat :=
  G.counter_main (H.toCounterHist G.ok) hk0K hKk hH1 hH2

end Balaban.LargeField
