import LatticeProb

/-!
# Axioms audit

Building this module prints the axiom dependencies of the principal theorems of
the library, the ones listed under "Contents" in `README.md`.  Each must report
exactly the three standard foundational axioms of Mathlib: `propext`,
`Classical.choice`, `Quot.sound`.

The results the library cites without proof are not axioms here: each is a
`Prop` in `LatticeProb/External/` taken as an explicit hypothesis of the
theorems that use it (`LatticeProb.gaussian_lipschitz_concentration` takes
`GaussianHerbstBound n`), so it appears in the statement, not in this list.

This file is not imported by the library root; the report runs when it is built,
as part of `lake build` or explicitly with `lake build LatticeProb.Meta.AxiomsAudit`.
`python3 tools/check_axioms.py` runs the same check on every declaration of the
library.
-/

/-! ### Walks and Green functions on `ℤ^d` and on graphs -/

#print axioms LatticeProb.srwHeat_gaussian
#print axioms LatticeProb.sqrt_le_gR_one_dim
#print axioms LatticeProb.gR_one_dim_le
#print axioms LatticeProb.log_le_gR_two_dim
#print axioms LatticeProb.gR_two_dim_le
#print axioms LatticeProb.gR_high_dim_le
#print axioms LatticeProb.tsum_iterate_delta0_eq
#print axioms LatticeProb.exists_srwGreen_gradient
#print axioms LatticeProb.exists_srwGreenInf_gradient
#print axioms LatticeProb.exists_srwGreenInf_le
#print axioms LatticeProb.exists_tsum_srwGreenInf_sq_tail_le
#print axioms LatticeProb.srwHitProb_eq_green_ratio
#print axioms LatticeProb.markov_stopping
#print axioms LatticeProb.exists_maxDisp_bound
#print axioms LatticeProb.srwTail_le
#print axioms LatticeProb.integral_rangeCard_sq_le
#print axioms LatticeProb.T_originBox_le
#print axioms LatticeProb.Graph.nash_ineq
#print axioms LatticeProb.Graph.heat_diag_le
#print axioms LatticeProb.Graph.spectralDimensionBound_of_boundedDegree
#print axioms LatticeProb.Graph.markov_exitTime
#print axioms LatticeProb.Graph.integrable_exitNat

/-! ### Local central limit theorems -/

#print axioms LatticeProb.BinomialLCLT.exists_binomPMF_localCLT
#print axioms LatticeProb.exists_srwHeat_one_sub_gauss_le_int
#print axioms LatticeProb.LocalCLT.srwHeat_eq_fourier

/-! ### Electrical networks and the killed Green function -/

#print axioms LatticeProb.Network.dirichlet_principle
#print axioms LatticeProb.Network.rayleigh_monotone
#print axioms LatticeProb.Network.thomson_principle
#print axioms LatticeProb.Network.nashWilliams_le_effRes
#print axioms LatticeProb.Network.nashWilliams_nested
#print axioms LatticeProb.Network.one_sub_returnProb
#print axioms LatticeProb.Network.escape_eq_inv
#print axioms LatticeProb.Network.le_of_harmonicOn
#print axioms LatticeProb.Network.exists_voltage
#print axioms LatticeProb.Network.laplacian_killedGreenReal
#print axioms LatticeProb.Network.killedGreenReal_symm
#print axioms LatticeProb.Network.energyOn_killedGreenReal

/-! ### The discrete Gaussian free field -/

#print axioms LatticeProb.Network.killedGreenMatrix_posSemidef
#print axioms LatticeProb.Network.integral_gff
#print axioms LatticeProb.Network.covariance_gff

/-! ### Ergodic theory and zero-one laws -/

#print axioms LatticeProb.maximal_ergodic
#print axioms LatticeProb.ae_tendsto_bAvg
#print axioms LatticeProb.tendsto_integral_div
#print axioms LatticeProb.ae_tendsto_gLow
#print axioms LatticeProb.ae_tendsto_div
#print axioms LatticeProb.ergodic_decomposition
#print axioms LatticeProb.ergodic_coordShift_infinitePi
#print axioms LatticeProb.measure_zero_or_one_of_exchangeable
#print axioms LatticeProb.measure_zero_or_one_of_allTranslationInvariant

/-! ### Correlation inequalities -/

#print axioms LatticeProb.infinitePi_harris
#print axioms LatticeProb.infinitePi_locallyMonotone_fkg
#print axioms LatticeProb.measure_pi_disjointOccSet_le

/-! ### Concentration and moment inequalities -/

#print axioms LatticeProb.bernstein
#print axioms LatticeProb.freedman
#print axioms LatticeProb.fukNagaev_bound
#print axioms LatticeProb.vonBahrEsseen
#print axioms LatticeProb.poisson_tail
#print axioms LatticeProb.evariance_le_half_tsum_siteEnergy
#print axioms LatticeProb.gaussian_lipschitz_concentration
#print axioms LatticeProb.paley_zygmund_of_second_moment
#print axioms LatticeProb.ottaviani
#print axioms LatticeProb.DoobMaximal.measureReal_sup_partialSum_sq_le
#print axioms LatticeProb.pinsker

/-! ### Gaussian processes and Brownian motion -/

#print axioms LatticeProb.exists_continuous_modification
#print axioms LatticeProb.exists_isBrownian
#print axioms LatticeProb.IsBrownianSpace.hasStrongMarkovRestart
#print axioms LatticeProb.brownian_exit_tail
#print axioms LatticeProb.Isonormal.ae_tendsto_partialSum
#print axioms LatticeProb.GaussTail.gaussianReal_real_Ioi_le
#print axioms LatticeProb.klDiv_gaussianReal_shift
#print axioms LatticeProb.CramerWold.tendstoInDistribution_of_forall_inner
#print axioms LatticeProb.ExtendedMapping.extended_continuous_mapping

/-! ### Regular variation -/

#print axioms LatticeProb.potter_bounds
#print axioms LatticeProb.karamata_integrated_tail
#print axioms LatticeProb.karamata_origin_integral

/-! ### Planar lattice topology -/

#print axioms LatticeProb.Lattice.Planar.separation

/-! ### Recurrence of the two-dimensional simple random walk on `ℤ²` -/

#print axioms LatticeProb.simpleRandomWalkRecurrent

/-! ### Dissipative-skew generators and their resolvents -/

#print axioms LatticeProb.Analysis.DissipativeSkewPair.variational_bound
#print axioms LatticeProb.Analysis.integral_inner_operatorSemigroup_eq_resolvent

/-! ### The Nash inequality on `ℤ²`, and the rate-two Poisson clock -/

#print axioms LatticeProb.NashZ2.nash
#print axioms LatticeProb.hasSum_poissonWeight
#print axioms LatticeProb.hasDerivAt_poissonWeight
#print axioms LatticeProb.tsum_abs_dPoissonWeight_le
