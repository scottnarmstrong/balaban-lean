module

public import Balaban.Correlations.KernelLargeAssembly
public import Balaban.Correlations.Assembly

/-!
# Root-C from the joint flow statement

`rootC_of_rootFAndC1Star`: Root-C (`RootCStatement`, definitionally the type of the frozen
`Balaban.lowTemperature_correlations`) follows from the single joint hypothesis
`RootFAndC1Star` (Root-F's clauses at `κ = kappaStar d`, `c₉ = 1` together with the interface
C-1* for the same `L, M`).  The Gaussian kernel hypotheses are discharged by
`Balaban.kernelHyp_and_large_holds`.
-/

@[expose] public section

namespace Balaban.Correlations

/-- Root-C from the joint Root-F / C-1* statement; no other hypothesis. -/
theorem rootC_of_rootFAndC1Star (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N)
    (h : RootFAndC1Star d N hN) : RootCStatement d N :=
  rootC_of_rootF_c1Star_kernelLarge d N hd hN h
    (fun L _ a hL ha1 ha2 => kernelHyp_and_large_holds d hd L a hL ha1 ha2)

end Balaban.Correlations
