import LatticeProb.Prob.AkcogluKrengelAE.AnchoredBoxMean

/-!
# The anchored-box maximal inequality: one declaration, one owner

The missing anchored-box maximal inequality `LatticeProb.AnchoredBoxMaximal` is declared in
exactly one module — `LatticeProb/Prob/AkcogluKrengelAE/AnchoredBoxMean.lean`, with its average
`anchoredBoxAvgMean` — together with its formalised refutation.

This module previously restated the definition with a second, identical average
`anchoredBoxAvg`; the duplicate made the two modules impossible to co-import
(`environment already contains 'LatticeProb.AnchoredBoxMaximal'`).  The duplicate has been
removed and this module now imports the owner.

The statement is **false as stated**: the box cardinality `∏ᵢ ⌈N cᵢ⌉` equals `N^d ∏ᵢ cᵢ` only
asymptotically, so the box average of a constant is not `∏ᵢ cᵢ`.  See the erratum in
`AnchoredBoxMean.lean` and the counterexamples `LatticeProb.not_anchoredBoxMaximal`,
`LatticeProb.not_anchoredBoxMaximal_ge_one` and `LatticeProb.not_anchoredBoxLimsupBound`; the
conditional results that assume `AnchoredBoxMaximal` are therefore vacuous.
-/
