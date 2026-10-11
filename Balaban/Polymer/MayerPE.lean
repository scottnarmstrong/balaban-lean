module

public import Balaban.Polymer.Mayer
public import Balaban.Polymer.GasBound
public import Balaban.Polymer.Size

/-!
# The combined statements MY + PE-L and GAS + PE-L

`mayer_pe`: the integral `∫ exp(∑ H) dν` of a product measure against local terms obeying the
bounds of MY is `exp(L)` for an absolutely convergent cluster sum `L = ∑_Y P(Y)` with
`∑_{Y ∋ □} |P(Y)| e^{κ' d(Y)} ≤ α e^{-κ' c}`.  The entropy bound (G2) is needed twice, once for the
terms (`hG2T`, in MY (iii)) and once for the unions (`hG2P`, in PE-L); (G1) and (G3) are needed
for both (`hG3T`, `hG3P`) (POLYMER.md §2.4, review R7).

`gas_pe`: the same for the partition function of GAS (POLYMER.md §2.6).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory

namespace Balaban.Polymer

section MayerPE

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
  {T : Type*} [Fintype T] {sup : T → Finset B} {H : T → (∀ b, Ω b) → ℂ}
  {d : Finset B → ℝ} {H0 κ0 κ1 c K0 c1 κ' κ0P K0P cP : ℝ}

/-- **MY + PE-L**. -/
theorem mayer_pe (hne : ∀ t, (sup t).Nonempty) (hloc : ∀ t, DepOn (sup t) (H t))
    (hmeas : ∀ t, Measurable (H t))
    (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2) (hκ0 : 0 ≤ κ0) (hκ1 : 0 ≤ κ1) (hc : 0 ≤ c)
    (hd : ∀ Y, 0 ≤ d Y)
    (hH : ∀ t Φ, ‖H t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d (sup t)))
    (hK0 : 0 ≤ K0)
    (hG2T : ∀ b : B, ∑ t ∈ Finset.univ.filter (fun t => b ∈ sup t),
      Real.exp (-κ0 * d (sup t)) ≤ K0)
    (hG3T : ∀ C : Finset T, ConnSet sup C →
      d (unionCs sup C) ≤ ∑ t ∈ C, d (sup t) + c * ((C.card : ℝ) - 1))
    (hc1 : 0 ≤ c1) (hq : 2 * H0 * K0 * Real.exp (κ1 * c) * c1 ≤ 1 / 2)
    (hG1 : ∀ Y : NePoly B, (Y.1.card : ℝ) ≤ c1 * (1 + d Y.1))
    (hK0P : 0 ≤ K0P) (hκ' : 0 ≤ κ') (hcP : 0 ≤ cP)
    (hG2P : ∀ b : B, ∑ Y : NePoly B, (if b ∈ Y.1 then Real.exp (-κ0P * d Y.1) else 0) ≤ K0P)
    (hG3P : ∀ (n : ℕ) (X : Fin (n + 1) → NePoly B),
      (clusterGraph (shareBlock (Subtype.val : NePoly B → Finset B)) X).Connected →
        d (unionOf (Subtype.val : NePoly B → Finset B) X) ≤ ∑ i, d (X i).1 + cP * n)
    (hκ : κ' + κ0P + c1 ≤ κ1 - 3 / 2)
    (hα : 2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 * K0P * Real.exp (c1 + κ' * cP) ≤ 1) :
    ∫ Φ, Complex.exp (∑ t, H t Φ) ∂(Measure.pi μ) =
      Complex.exp (logSeries (shareBlock (Subtype.val : NePoly B → Finset B)) (mayerK μ sup H)) ∧
    (∀ b : B, ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ‖PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val (mayerK μ sup H) Y‖ *
          Real.exp (κ' * d Y) ≤
        2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 * K0P * Real.exp (c1 + κ' * cP) *
          Real.exp (-(κ' * cP))) ∧
    ‖logSeries (shareBlock (Subtype.val : NePoly B → Finset B)) (mayerK μ sup H)‖ ≤
      Fintype.card B * (2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 * K0P * Real.exp (c1 + κ' * cP)) := by
  have hbdd : ∀ t, Bdd (H t) := fun t => ⟨_, hH t⟩
  have hMY := mayer_integral_eq μ hne hloc hmeas hbdd
  have hK : ∀ Y : NePoly B, ‖mayerK μ sup H Y‖ ≤
      (2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1) * Real.exp (-(κ1 - 3 / 2) * d Y.1) := by
    intro Y
    have := mayer_activity_bound μ hH0 hH0' hκ0 hκ1 hc hd hne hH hG2T hG3T hc1 hq Y (hG1 Y)
    calc _ ≤ _ := this
      _ = _ := by ring
  have hε : 0 ≤ 2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 := by positivity
  have hpe := pe_size (Subtype.val : NePoly B → Finset B) d (ε := 2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1)
    (κ := κ1 - 3 / 2) (κ' := κ') (κ0 := κ0P) (K0 := K0P) (c := cP) (c1 := c1)
    hε hK0P hκ' hcP hd (fun Y => Y.2) hG1 hG2P hG3P hκ
    (by simpa [mul_assoc] using hα) Finset.univ (fun Y => by obtain ⟨b, hb⟩ := Y.2; exact ⟨b, Finset.mem_univ _, hb⟩)
    (mayerK μ sup H) hK
  obtain ⟨h1, _, h3, h4, _⟩ := hpe
  rw [← hMY] at h1
  refine ⟨h1, ?_, ?_⟩
  · intro b
    simpa [mul_assoc] using h3 b
  · simpa [mul_assoc] using h4

end MayerPE

section GasPE

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {cy : Yt → Finset B} {zs cr : Zt → Finset B} {β : Yt → ℂ} {τ : Zt → ℂ}
  {d : Finset B → ℝ} {B0 κg κ'' c c1 c2 p h K0g K0h κ' κ0P K0P cP : ℝ}

/-- **GAS + PE-L**: the partition function with non-small boundary terms is `exp(L)` for an
absolutely convergent cluster sum, with local terms decaying at the rate `κg - 2` of GAS. -/
theorem gas_pe (hB0 : 0 ≤ B0) (hκg : 0 ≤ κg) (hκ'' : κg ≤ κ'') (hc : 0 ≤ c)
    (hc1 : 0 ≤ c1) (hp : 0 ≤ p) (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (zs z).Nonempty)
    (hcr : ∀ z, cr z ⊆ zs z)
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hτ : ∀ z, ‖τ z‖ ≤ Real.exp (-p - h * (zs z).card))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → gasA cy zs cr C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    (hK0g : 0 ≤ K0g)
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y),
      Real.exp (-(κ'' - κg) * d (cy y)) ≤ K0g)
    (hK1 : 1 ≤ K0h)
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤ K0h ^ v)
    (hh : B0 * Real.exp B0 * Real.exp (κg * c) * K0g + κg * (c2 + c) + c1 + 3 +
      Real.log K0h ≤ h)
    (hG1 : ∀ X : NePoly B, (X.1.card : ℝ) ≤ c1 * (1 + d X.1))
    (hK0P : 0 ≤ K0P) (hκ' : 0 ≤ κ') (hcP : 0 ≤ cP)
    (hG2P : ∀ b : B, ∑ Y : NePoly B, (if b ∈ Y.1 then Real.exp (-κ0P * d Y.1) else 0) ≤ K0P)
    (hG3P : ∀ (n : ℕ) (X : Fin (n + 1) → NePoly B),
      (clusterGraph (shareBlock (Subtype.val : NePoly B → Finset B)) X).Connected →
        d (unionOf (Subtype.val : NePoly B → Finset B) X) ≤ ∑ i, d (X i).1 + cP * n)
    (hκ : κ' + κ0P + c1 ≤ κg - 2)
    (hα : 3 * c1 * Real.exp (-p) * K0P * Real.exp (c1 + κ' * cP) ≤ 1) :
    gasXi cy zs cr β τ = Complex.exp (logSeries (shareBlock (Subtype.val : NePoly B → Finset B))
      (gasK cy zs cr β τ)) ∧
    (∀ b : B, ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ‖PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
          (gasK cy zs cr β τ) Y‖ * Real.exp (κ' * d Y) ≤
        3 * c1 * Real.exp (-p) * K0P * Real.exp (c1 + κ' * cP) * Real.exp (-(κ' * cP))) ∧
    ‖logSeries (shareBlock (Subtype.val : NePoly B → Finset B)) (gasK cy zs cr β τ)‖ ≤
      Fintype.card B * (3 * c1 * Real.exp (-p) * K0P * Real.exp (c1 + κ' * cP)) := by
  have hK : ∀ X : NePoly B, ‖gasK cy zs cr β τ X‖ ≤
      (3 * c1 * Real.exp (-p)) * Real.exp (-(κg - 2) * d X.1) := fun X =>
    gas_activity_bound hB0 hκg hκ'' hc hc1 hp hd hz hcr hB hτ hzd hG3 hK0g hent hK1 hcount hh X
      (hG1 X)
  have hε : 0 ≤ 3 * c1 * Real.exp (-p) := by positivity
  have hpe := pe_size (Subtype.val : NePoly B → Finset B) d (ε := 3 * c1 * Real.exp (-p))
    (κ := κg - 2) (κ' := κ') (κ0 := κ0P) (K0 := K0P) (c := cP) (c1 := c1)
    hε hK0P hκ' hcP hd (fun Y => Y.2) hG1 hG2P hG3P hκ
    (by simpa [mul_assoc] using hα) Finset.univ
    (fun Y => by obtain ⟨b, hb⟩ := Y.2; exact ⟨b, Finset.mem_univ _, hb⟩)
    (gasK cy zs cr β τ) hK
  obtain ⟨h1, _, h3, h4, _⟩ := hpe
  refine ⟨(gas_eq β τ hz hcr).trans h1, ?_, ?_⟩
  · intro b
    simpa [mul_assoc] using h3 b
  · simpa [mul_assoc] using h4

end GasPE

end Balaban.Polymer
