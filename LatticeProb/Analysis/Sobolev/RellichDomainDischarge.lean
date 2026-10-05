/-
# Discharging the Rellich–Kondrachov external from the domain-restricted support repair

`rkLowFreqNet_of_domainSupportRepair` (`SupportRepair.lean`) reduces `rkLowFreqNet` to the single
domain-restricted input `BandLimitedTestFnApproxOnDomain`, and
`rellichKondrachovNegSobolev_of_lowfreqNet` (`RellichLowFreqNet.lean`) turns `rkLowFreqNet` into the
external `LatticeProb.External.RellichKondrachovNegSobolev`.  Composing the two names the discharge:

* `rellichKondrachovNegSobolev_of_domainSupportRepair` — the external from
  `BandLimitedTestFnApproxOnDomain`.

The external therefore remains conditional on `BandLimitedTestFnApproxOnDomain`, stated exactly.
-/
import LatticeProb.Analysis.Sobolev.RellichLowFreqNet
import LatticeProb.Analysis.Sobolev.SupportRepair

namespace LatticeProb.Sobolev

/-- **The external, from the domain-restricted support repair.**  Composing the sound composition
`rkLowFreqNet_of_domainSupportRepair` with `rellichKondrachovNegSobolev_of_lowfreqNet` discharges
`RellichKondrachovNegSobolev`.  The external stays conditional on
`BandLimitedTestFnApproxOnDomain`. -/
theorem rellichKondrachovNegSobolev_of_domainSupportRepair
    (hrep : BandLimitedTestFnApproxOnDomain) :
    LatticeProb.External.RellichKondrachovNegSobolev :=
  rellichKondrachovNegSobolev_of_lowfreqNet (rkLowFreqNet_of_domainSupportRepair hrep)

end LatticeProb.Sobolev
