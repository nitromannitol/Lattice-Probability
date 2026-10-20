import LatticeProb.Meta.LyonsAxioms
import LatticeProb.Meta.AllMinorsAxioms
import LatticeProb
import LatticeProb.Meta.CopiedGraphAxioms
import LatticeProb.Meta.DiskAlternationAxioms
import LatticeProb.Meta.PairingMinorAxioms
import LatticeProb.Meta.WilsonGenericAxioms
import LatticeProb.Meta.PlaneIncidenceAxioms
import LatticeProb.Walk.KilledGreenPlanarLower
import LatticeProb.Topology.CurveSpace
import LatticeProb.Prob.BoundedStopping
import LatticeProb.Network.Dirichlet
import LatticeProb.Network.FiniteCalculus
import LatticeProb.Prob.SupportedLaw
import LatticeProb.Prob.LevyProkhorovMaps
import LatticeProb.Prob.DependentKernelMap
import LatticeProb.Prob.SubcouplingCompletion
import LatticeProb.Prob.MatchedCellCoupling
import LatticeProb.Prob.FinitePartitionCoupling
import LatticeProb.Prob.FinitePartitionCouplingKernel
import LatticeProb.Prob.CameronMartin
import LatticeProb.Prob.McLeish.ExpRemainder
import LatticeProb.Prob.McLeish.Truncation
import LatticeProb.Prob.McLeish.ProductLimit
import LatticeProb.Prob.McLeish.ProductMoment
import LatticeProb.Prob.McLeish.Remainder
import LatticeProb.Prob.McLeish.CharFunLimit
import LatticeProb.Prob.McLeish.TruncProduct
import LatticeProb.Prob.McLeish.RatioLimit
import LatticeProb.Prob.McLeish.MartingaleCLT
import LatticeProb.Prob.McLeish.Example
import LatticeProb.Prob.GaussProductRotation
import LatticeProb.Prob.GaussSteinIBP
import LatticeProb.Prob.GaussEuclideanPushforward
import LatticeProb.Prob.GaussSmoothBdd
import LatticeProb.Prob.GaussSmoothMGF
import LatticeProb.Prob.GaussMollify
import LatticeProb.Prob.BrownianOpenExit
import LatticeProb.Prob.BrownianOpenExitStopping
import LatticeProb.Prob.BrownianOpenExitFinite
import LatticeProb.Analysis.HarmonicBridge
import LatticeProb.Prob.GaussianHerbstDischarge
import LatticeProb.Topology.ContinuousMapBorel
import LatticeProb.Prob.BrownianPathMap
import LatticeProb.Prob.GaussLipConcentration
import LatticeProb.Prob.BrownianMomentsCore
import LatticeProb.Analysis.HessianTaylorRemainder
import LatticeProb.Prob.DyadicExitApprox
import LatticeProb.Prob.BrownianPathSpace
import LatticeProb.Prob.BrownianPredictableTaylor
import LatticeProb.Prob.BrownianStoppedSum
import LatticeProb.Prob.BrownianStoppedLimit
import LatticeProb.Prob.BrownianPathHarmonicExit
import LatticeProb.Prob.BrownianOpenHarmonicExit
import LatticeProb.Prob.Quantile
import LatticeProb.Prob.BinomialTail
import LatticeProb.Prob.SkorokhodPartition
import LatticeProb.Prob.SkorokhodMix
import LatticeProb.Prob.TrivialSigma
import LatticeProb.Prob.QuantileMap
import LatticeProb.Prob.QuantileLimit
import LatticeProb.Prob.BinomialDomination
import LatticeProb.Prob.SkorokhodSpace
import LatticeProb.Prob.TrivialSigmaJoin
import LatticeProb.Prob.GaussPittCore
import LatticeProb.Prob.GaussPittVector
import LatticeProb.Prob.GaussAssociationSets
import LatticeProb.Prob.BrownianAbsMoments
import LatticeProb.Topology.Length.VariationCompat
import LatticeProb.Prob.SkorokhodLaw
import LatticeProb.Prob.BrownianGermZeroOne
import LatticeProb.Prob.BrownianAbsMomentsFubini
import LatticeProb.Prob.GaussPittSmooth
import LatticeProb.Topology.Length.CurveLength
import LatticeProb.Prob.GaussBorellFinite
import LatticeProb.Prob.GaussKahaneStein
import LatticeProb.Prob.GaussKahaneCore
import LatticeProb.Topology.PolishContinuousMap
import LatticeProb.Prob.BrownianTailZeroOne
import LatticeProb.Prob.GaussPittLipschitz
import LatticeProb.Prob.GaussBorellVector
import LatticeProb.Prob.GaussKahaneBound
import LatticeProb.Topology.Length.LengthSpace
import LatticeProb.Prob.Skorokhod
import LatticeProb.Prob.GaussKahaneInterp
import LatticeProb.Prob.GaussSupTailBorell
import LatticeProb.Topology.Length.CurveNatural
import LatticeProb.Topology.Length.Midpoint
import LatticeProb.Topology.Length.Internal
import LatticeProb.Prob.GaussAssociationEvents
import LatticeProb.Prob.GaussBorellSeq
import LatticeProb.Prob.GaussKahaneVector
import LatticeProb.Topology.Length.LengthGeodesic
import LatticeProb.Topology.Length.Menger
import LatticeProb.Prob.GaussAssociationFun
import LatticeProb.Prob.GaussKahaneRpow
import LatticeProb.Topology.Length.Geodesic
import LatticeProb.Topology.Length.LengthLimit
import LatticeProb.Prob.SkorokhodRepresentation
import LatticeProb.Prob.CondIndepEv
import LatticeProb.Analysis.ReciprocalPowerDecay
import LatticeProb.Analysis.MatrixHeat
import LatticeProb.Network.Conductance
import LatticeProb.Analysis.Polynomial.Degree
import LatticeProb.Prob.EfronSteinSigma
import LatticeProb.Network.HeatGenerator
import LatticeProb.Network.DirichletForm
import LatticeProb.Analysis.Polynomial.Laplacian
import LatticeProb.Prob.GaussKahane2Const
import LatticeProb.Network.HeatUniformization
import LatticeProb.Network.KilledHeat
import LatticeProb.Network.DirichletSpace
import LatticeProb.Network.WeightedGradient
import LatticeProb.Network.AnchoredEnergy
import LatticeProb.Analysis.Polynomial.BallVanishing
import LatticeProb.Analysis.Polynomial.Analytic
import LatticeProb.Prob.CondIndepDetermined
import LatticeProb.Network.ConductanceHarmonic
import LatticeProb.Network.EnergyENN
import LatticeProb.Network.HeatPositivity
import LatticeProb.Network.DirichletSpaceComplete
import LatticeProb.Network.AnchoredTraceMinimizer
import LatticeProb.Topology.Length.SetDist
import LatticeProb.Prob.GaussSupTailField
import LatticeProb.Network.ConductanceBridge
import LatticeProb.Analysis.Polynomial.BoundaryApproximation
import LatticeProb.Analysis.Polynomial.Dirichlet
import LatticeProb.Prob.AEDetermined
import LatticeProb.Prob.CondIndepEvJoin
import LatticeProb.Network.HeatKernel
import LatticeProb.Network.AnchoredMinimizer
import LatticeProb.Topology.Length.InternalOps
import LatticeProb.Prob.EfronSteinSigmaResample
import LatticeProb.Prob.CondCopies
import LatticeProb.Topology.Length.InternalLimit
import LatticeProb.Prob.FiniteChainPairTV
import LatticeProb.Prob.SubGaussianMaximal
import LatticeProb.Prob.BrownianPathCoords
import LatticeProb.Prob.BrownianExitPosition
import LatticeProb.Analysis.HarmonicScaling
import LatticeProb.Prob.BrownianIncrementMoments
import LatticeProb.Prob.BrownianWeakMarkovPath
import LatticeProb.Prob.BrownianFiniteStopping
import LatticeProb.Prob.BrownianHessianTaylor

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
#print axioms LatticeProb.greenNorms
#print axioms LatticeProb.BallGreen.ballGreenBounds
#print axioms LatticeProb.exists_srwGreen_gradient
#print axioms LatticeProb.exists_srwGreenInf_gradient
#print axioms LatticeProb.exists_srwGreenInf_le
#print axioms LatticeProb.exists_tsum_srwGreenInf_sq_tail_le
#print axioms LatticeProb.Intersection.exists_lintegral_interCount_sq_le
#print axioms LatticeProb.srwHitProb_eq_green_ratio
#print axioms LatticeProb.DrivenWalk.position
#print axioms LatticeProb.DrivenWalk.position_zero
#print axioms LatticeProb.DrivenWalk.position_succ
#print axioms LatticeProb.DrivenWalk.position_consNat_succ
#print axioms LatticeProb.DrivenWalk.hitBefore
#print axioms LatticeProb.DrivenWalk.hitBefore_eq_empty
#print axioms LatticeProb.DrivenWalk.hitBefore_eq_univ
#print axioms LatticeProb.DrivenWalk.consNat_mem_hitBefore_iff
#print axioms LatticeProb.DrivenWalk.measurable_position
#print axioms LatticeProb.DrivenWalk.measurableSet_hitBefore
#print axioms LatticeProb.DrivenWalk.measure_hitBefore_eq_lintegral
#print axioms LatticeProb.DrivenWalk.measure_hitBefore_eq_sum
#print axioms LatticeProb.stepLaw_map_dirVec
#print axioms LatticeProb.pathLaw_map_dirVec
#print axioms LatticeProb.pathLaw_map_sitePath
#print axioms LatticeProb.srwGreen_eq_sum_srwFirstHit
#print axioms LatticeProb.srwGreen_mono
#print axioms LatticeProb.srwGreen_le_srwHitProb_mul
#print axioms LatticeProb.tendsto_srwGreen_two_dim_origin
#print axioms LatticeProb.srwHitProb_two_dim_eq_one
#print axioms LatticeProb.siteWalkLaw_two_dim_hitOrigin
#print axioms LatticeProb.measurableSet_hit_site
#print axioms LatticeProb.siteWalkLaw_hit_site
#print axioms LatticeProb.siteWalkLaw_two_dim_hit_site
#print axioms LatticeProb.pathLaw_two_dim_hit_site
#print axioms LatticeProb.exists_abs_srwGreenInf_sub_le
#print axioms LatticeProb.tendsto_potentialKernel
#print axioms LatticeProb.potentialKernel_zero
#print axioms LatticeProb.walkOp_potentialKernel_sub
#print axioms LatticeProb.exists_abs_potentialKernel_sub_log_le
#print axioms LatticeProb.External.potentialKernelAsymptotics_holds
#print axioms LatticeProb.External.feyMeesterRedigLeastAction_holds
#print axioms LatticeProb.External.carneVaropoulos_holds
#print axioms LatticeProb.External.greenNorms_holds
#print axioms LatticeProb.External.ballGreenBounds_holds
#print axioms LatticeProb.markov_stopping
#print axioms LatticeProb.exists_maxDisp_bound
#print axioms LatticeProb.srwTail_le
#print axioms LatticeProb.integral_rangeCard_sq_le
#print axioms LatticeProb.T_originBox_le
#print axioms LatticeProb.resistance_packing
#print axioms LatticeProb.insertion_inequality
#print axioms LatticeProb.Graph.nash_ineq
#print axioms LatticeProb.Graph.heat_diag_le
#print axioms LatticeProb.Graph.spectralDimensionBound_of_boundedDegree
#print axioms LatticeProb.Graph.walkLaw_eval_le_carneVaropoulos
#print axioms LatticeProb.Graph.heat_le_carneVaropoulos
#print axioms LatticeProb.Graph.markov_exitTime
#print axioms LatticeProb.Graph.integrable_exitNat

/-! ### Local central limit theorems -/

#print axioms LatticeProb.BinomialLCLT.exists_binomPMF_localCLT
#print axioms LatticeProb.exists_srwHeat_one_sub_gauss_le_int
#print axioms LatticeProb.LocalCLT.srwHeat_eq_fourier
#print axioms LatticeProb.ContinuousTime.exists_abs_lineKernel_sub_lineGauss_le
#print axioms LatticeProb.ContinuousTime.exists_abs_ctHeat_sub_ctGauss_le
#print axioms LatticeProb.LocalCLT.exists_abs_srwHeat_add_succ_sub_le
#print axioms LatticeProb.LocalCLT.exists_abs_srwHeat_sub_le
#print axioms LatticeProb.LocalCLT.exists_abs_heatKernel_four_add_succ_sub_le
#print axioms LatticeProb.LocalCLT.exists_window_abs_heatKernel_sub_heatKernelBM_le
#print axioms LatticeProb.LocalCLT.exists_window_abs_srwHeat_sub_gauss_lt

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
#print axioms LatticeProb.Network.maximum_neighbors
#print axioms LatticeProb.Network.caccioppoli
#print axioms LatticeProb.Network.moser_estimate
#print axioms LatticeProb.Network.moser_l2_step

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
#print axioms LatticeProb.akcoglu_krengel_mean
#print axioms LatticeProb.ergodic_decomposition
#print axioms LatticeProb.ergodic_coordShift_infinitePi
#print axioms LatticeProb.measure_zero_or_one_of_exchangeable
#print axioms LatticeProb.measure_zero_or_one_of_allTranslationInvariant

/-! ### Sub-invariant functions and Kac's lemma -/

#print axioms LatticeProb.ae_eq_comp_of_ae_le_comp
#print axioms LatticeProb.ae_eq_comp_of_ae_le_comp_real
#print axioms LatticeProb.ae_eq_const_of_ae_le_comp_real
#print axioms LatticeProb.lintegral_retTime_eq_measure_hit
#print axioms LatticeProb.kac_le
#print axioms LatticeProb.kac_integrable
#print axioms LatticeProb.kac

/-! ### Correlation inequalities -/

#print axioms LatticeProb.infinitePi_harris
#print axioms LatticeProb.infinitePi_locallyMonotone_fkg
#print axioms LatticeProb.measure_pi_disjointOccSet_le

/-! ### Negative-order Sobolev norms and the Rellich–Kondrachov reduction -/

#print axioms LatticeProb.Sobolev.exists_sobolevNormSqHigh_le
#print axioms LatticeProb.Sobolev.isBandLimited_mono
#print axioms LatticeProb.Sobolev.rellichKondrachov_iff_rkLowFrequencyStatement
#print axioms LatticeProb.Sobolev.rellichKondrachov_of_rkBandLimitedCmNet
#print axioms LatticeProb.Sobolev.rellichKondrachov_of_rkLowFrequencyStatement
#print axioms LatticeProb.Sobolev.rk_finite_net_of_Cm_net
#print axioms LatticeProb.Sobolev.rkLowFrequencyStatement_of_rkBandLimitedCmNet
#print axioms LatticeProb.Sobolev.rkResidual_diff_bound
#print axioms LatticeProb.Sobolev.rkResidual_holds
#print axioms LatticeProb.Sobolev.sobolevNormSqHigh_eq_zero_of_isBandLimited
#print axioms LatticeProb.Sobolev.sobolevNormSqHigh_le
#print axioms LatticeProb.Sobolev.sobolevNormSqLow_add_high
#print axioms LatticeProb.Sobolev.sobolevNormSq_add_le
#print axioms LatticeProb.Sobolev.sobolevNormSq_eq_low_of_isBandLimited
#print axioms LatticeProb.Sobolev.sobolevNormSq_sub_le
#print axioms LatticeProb.Sobolev.tendsto_weight_atTop_zero

/-! ### Concentration and moment inequalities -/

#print axioms LatticeProb.bernstein
#print axioms LatticeProb.mcdiarmid
#print axioms LatticeProb.freedman
#print axioms LatticeProb.fukNagaev_bound
#print axioms LatticeProb.vonBahrEsseen
#print axioms LatticeProb.poisson_tail
#print axioms LatticeProb.evariance_le_half_tsum_siteEnergy
#print axioms LatticeProb.gaussian_lipschitz_concentration
#print axioms LatticeProb.gaussianHerbstBound_of_logSobolev
#print axioms LatticeProb.hasDerivAt_mgf_centred
#print axioms LatticeProb.herbstTilt_entropy_le
#print axioms LatticeProb.herbstTilt_integral
#print axioms LatticeProb.herbstTilt_log_lipschitz
#print axioms LatticeProb.herbstTilt_pos
#print axioms LatticeProb.herbst_entropy_le
#print axioms LatticeProb.integrable_exp_sub_integral
#print axioms LatticeProb.integrable_mul_exp_sub_integral
#print axioms LatticeProb.integral_sub_integral_eq_zero
#print axioms LatticeProb.lipschitzWith_sub_integral
#print axioms LatticeProb.mgf_centred_pos
#print axioms LatticeProb.sqrt_sum_sq_le_sqrt_card_mul_dist
#print axioms LatticeProb.lipschitzWith_pi_of_hasSum_sq
#print axioms LatticeProb.gaussian_lipschitz_concentration_l2_fin
#print axioms LatticeProb.gaussianLogSobolev_succ_of_one
#print axioms LatticeProb.gaussianLogSobolev_of_one_of_tensorStep
#print axioms LatticeProb.gaussianHerbstBound_of_one_of_tensorStep
#print axioms LatticeProb.gaussianLogSobolevGrad_of_one_of_tensorStep
#print axioms LatticeProb.gaussianLogSobolev_of_grad_smooth
#print axioms LatticeProb.entropy_prod_split
#print axioms LatticeProb.norm_sq_integral_le_integral_norm_sq
#print axioms LatticeProb.fderiv_slice
#print axioms LatticeProb.hasFDerivAt_integral_marginal
#print axioms LatticeProb.fderiv_log
#print axioms LatticeProb.gaussianLogSobolevGradTensorStep_of_prodStep
#print axioms LatticeProb.gaussianLogSobolevGrad_zero
#print axioms LatticeProb.gaussianLogSobolevGradProdStep_of_tensorStep
#print axioms LatticeProb.gaussianLogSobolevGradProdStep_iff_tensorStep
#print axioms LatticeProb.sqrt_sum_sq_le_sqrt_card_mul_dist
#print axioms LatticeProb.lipschitzWith_pi_of_hasSum_sq
#print axioms LatticeProb.gaussian_lipschitz_concentration_l2_fin
#print axioms LatticeProb.paley_zygmund_of_second_moment
#print axioms LatticeProb.ottaviani
#print axioms LatticeProb.DoobMaximal.measureReal_sup_partialSum_sq_le
#print axioms LatticeProb.pinsker
#print axioms LatticeProb.efron_stein
#print axioms LatticeProb.exists_mgf_neg_bounds
#print axioms LatticeProb.small_ball_of_exp
#print axioms LatticeProb.integral_comparison_third_order
#print axioms LatticeProb.tendsto_measureReal_weighted
#print axioms LatticeProb.weighted_iid_central_limit
#print axioms LatticeProb.weighted_iid_central_limit_pick

/-! ### The bracket process and the Dambis–Dubins–Schwarz representation -/

#print axioms LatticeProb.condExp_cross_eq_zero
#print axioms LatticeProb.condExp_dyadic_cross_eq_zero
#print axioms LatticeProb.crossTerm_eq_sum
#print axioms LatticeProb.dyadicPoint_le_mid
#print axioms LatticeProb.dyadicPoint_mid_le
#print axioms LatticeProb.dyadicPoint_nonneg
#print axioms LatticeProb.dyadicPoint_two_mul
#print axioms LatticeProb.dyadicPoint_two_mul_add_two
#print axioms LatticeProb.dyadicPoint_zero_time
#print axioms LatticeProb.integral_crossTerm_eq_zero
#print axioms LatticeProb.integral_realizedQVar_succ_eq
#print axioms LatticeProb.measurable_crossTerm
#print axioms LatticeProb.measurable_realizedQVar
#print axioms LatticeProb.realizedQVar_eq_succ_add_cross
#print axioms LatticeProb.realizedQVar_nonneg
#print axioms LatticeProb.realizedQVar_refine
#print axioms LatticeProb.realizedQVar_zero_grid
#print axioms LatticeProb.realizedQVar_zero_time
#print axioms LatticeProb.sq_sub_sq_decomp
#print axioms LatticeProb.sum_range_two_mul'

/-! ### Smooth maxima and softmax stability -/

#print axioms LatticeProb.softMaximum_derivative_bound
#print axioms LatticeProb.softMinimum_derivative_bound
#print axioms LatticeProb.SmoothBottleneckBound.softMaximum
#print axioms LatticeProb.expStable_softWeightComposition

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
#print axioms LatticeProb.mehler_pushforward_general
#print axioms LatticeProb.mehler_pushforward_one
#print axioms LatticeProb.mehler_double_integral_shift
#print axioms LatticeProb.gaussianReal_affine
#print axioms LatticeProb.integrable_comp_affine
#print axioms LatticeProb.ouSemigroup_sq_le
#print axioms LatticeProb.ouSemigroup_zero
#print axioms LatticeProb.ouSemigroup_const
#print axioms LatticeProb.ouSemigroup_one
#print axioms LatticeProb.ouSemigroup_const_mul
#print axioms LatticeProb.integral_ouSemigroup
#print axioms LatticeProb.ouSemigroup_add

/-! ### Regular variation -/

#print axioms LatticeProb.potter_bounds
#print axioms LatticeProb.karamata_integrated_tail
#print axioms LatticeProb.karamata_origin_integral

/-! ### Planar lattice topology -/

#print axioms LatticeProb.Lattice.Planar.separation

/-! ### The classical (integer, Abelian) sandpile on `ℤ^d` -/

#print axioms LatticeProb.Sandpile.lap_eq_sum_second_diff
#print axioms LatticeProb.Sandpile.podo_mono_step
#print axioms LatticeProb.Sandpile.fodo_topple_of_ge
#print axioms LatticeProb.Sandpile.wave_mono_time
#print axioms LatticeProb.Sandpile.exists_adj_pos_of_nbrSumZ_pos
#print axioms LatticeProb.Sandpile.lap_le_of_fixed
#print axioms LatticeProb.Sandpile.recurrent_const
#print axioms LatticeProb.Sandpile.le_of_isLegalToppling
#print axioms LatticeProb.eventually_constant_of_monotone_bounded
#print axioms LatticeProb.finset_common_stable
#print axioms LatticeProb.sInf_coe_attained
#print axioms LatticeProb.sInf_coe_top
#print axioms LatticeProb.exists_nat_bound_of_isCompact
#print axioms LatticeProb.nearestSite_smul_mem_box
/-! ### Scaling-limit infrastructure -/

#print axioms LatticeProb.Scaling.RunningMax.continuous_runningMax
#print axioms LatticeProb.Scaling.RunningMax.measurable_runningMax
#print axioms LatticeProb.Scaling.BoundedFunctionalLift.abs_liftPhiOn_sub_le
#print axioms LatticeProb.Scaling.BoundedFunctionalLift.liftPhiOn_eq_of_nice
#print axioms LatticeProb.Scaling.CramerWold.tendstoInDistribution_of_tendsto_charFun_linearCombination_filter
#print axioms LatticeProb.Scaling.Slutsky.tendsto_add_of_tendsto_zero
#print axioms LatticeProb.Scaling.LipschitzLimit.lipschitzWith_one_of_tendsto
#print axioms LatticeProb.Scaling.LocallyUniformLimit.continuous_and_monotone_of_tendstoLocallyUniformly
#print axioms LatticeProb.Scaling.PositiveCutoff.exists_cutoff_eq_one

/-! ### Convex order and the exponential reference law -/

#print axioms LatticeProb.ConvexOrder.convex_integral_le_refLaw
#print axioms LatticeProb.ConvexOrder.convex_lipschitz_integral_le_finite_pi
#print axioms LatticeProb.ConvexOrder.twoPointLaw_convex_le
#print axioms LatticeProb.ConvexOrder.exists_twoPoint_comparison

/-! ### The binomial law and its shift correlation -/

#print axioms LatticeProb.Walk.shift_energy

/-! ### Lattice kernels and Riemann sums -/

#print axioms LatticeProb.Walk.tendsto_latticeSum_mul_rpow
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

/-! ### Percolation -/

#print axioms LatticeProb.Percolation.fpr_piv
#print axioms LatticeProb.Percolation.fpr_change
#print axioms LatticeProb.Percolation.fpr_le_of_map
#print axioms LatticeProb.Percolation.fpw_le_of_agree
#print axioms LatticeProb.Percolation.fpw_le_of_par
#print axioms LatticeProb.Percolation.bondLaw_half_le_of_flip
#print axioms LatticeProb.Percolation.bondLaw_toReal_eq_fpr
#print axioms LatticeProb.Percolation.walk_prefix_hit_integer
#print axioms LatticeProb.Percolation.walk_mem_support_of_induce
#print axioms LatticeProb.Percolation.card_planeRectangle_aspect_le_cube
#print axioms LatticeProb.Percolation.measure_boxPathEvent_le
#print axioms LatticeProb.Percolation.card_double_square_le_cube
#print axioms LatticeProb.Percolation.walkBottleneck_append
#print axioms LatticeProb.Percolation.finiteMaximum_mem

/-! ### Total variation distance -/

#print axioms LatticeProb.pi_one_coord_le
#print axioms LatticeProb.pi_tv_le
#print axioms LatticeProb.infinitePi_restrict_tv_le

/-! ### Graph combinatorics -/

#print axioms LatticeProb.Graph.exists_epath
#print axioms LatticeProb.Graph.konig
#print axioms LatticeProb.Graph.two_mul_sum_card_filter_lt

/-! ### Rellich–Kondrachov -/

#print axioms LatticeProb.Sobolev.rkLowFrequencyStatement_of_rkLowFreqNet
#print axioms LatticeProb.Sobolev.rellichKondrachovNegSobolev_of_lowfreqNet
#print axioms LatticeProb.Sobolev.fourier_bandTrunc
#print axioms LatticeProb.Sobolev.fourier_bandTrunc_eq_zero
#print axioms LatticeProb.Sobolev.fourier_realToComplexSchwartz
#print axioms LatticeProb.Sobolev.fourier_bandTrunc_real
#print axioms LatticeProb.Sobolev.fourier_bandTrunc_real_eq_zero
#print axioms LatticeProb.Sobolev.mul_fourier_eq_fourier_convolution
#print axioms LatticeProb.Sobolev.integrable_fourier_mul
#print axioms LatticeProb.Sobolev.fourier_smul
#print axioms LatticeProb.Sobolev.fourier_convolution_fourierInv_mul
#print axioms LatticeProb.Sobolev.integrable_convolution_fourierInv_mul
#print axioms LatticeProb.Sobolev.integrable_fourier_mul_conv
#print axioms LatticeProb.Sobolev.fejer_integrable_side_condition

/-! ### The Fejér limit and the real projection -/

#print axioms LatticeProb.Sobolev.bandCut_neg
#print axioms LatticeProb.Sobolev.bandTrunc_im_eq_zero
#print axioms LatticeProb.Sobolev.fourier_bandProj
#print axioms LatticeProb.Sobolev.isBandLimited_bandProj
#print axioms LatticeProb.Sobolev.sobolevNormSqHigh_bandProj_eq_zero

/-! ### The sharp band projection and its consumption -/


/-! ### Band-limited Bernstein bound -/

#print axioms LatticeProb.Sobolev.fourierInv_eq_setIntegral
#print axioms LatticeProb.Sobolev.norm_iteratedFDeriv_fourierInv_le_setIntegral
#print axioms LatticeProb.Sobolev.exists_iteratedFDeriv_bandTrunc_le

/-! ### Band-limited C^m bound -/

#print axioms LatticeProb.Sobolev.exists_iteratedFDeriv_bandTrunc_le_L2
#print axioms LatticeProb.Sobolev.exists_iteratedFDeriv_bandTrunc_le_Hs
#print axioms LatticeProb.Sobolev.bandLimitedCmBound_holds

/-! ### Rellich C^m net supply -/

#print axioms LatticeProb.Sobolev.exists_bandTrunc_Cm_jet_bound

/-! ### Band-limited C^m and Lipschitz bounds -/

#print axioms LatticeProb.Sobolev.exists_uniform_iteratedFDeriv_le
#print axioms LatticeProb.Sobolev.exists_uniform_iteratedFDeriv_apply_le

/-! ### The sound low-frequency glue (domain-restricted) -/

#print axioms LatticeProb.Sobolev.rkLowFreqNet_of_truncation_and_supportRepair
#print axioms LatticeProb.Sobolev.rellichKondrachovNegSobolev_of_truncation_and_supportRepair
#print axioms LatticeProb.Sobolev.lipschitz_of_norm_iteratedFDeriv_one_le
#print axioms LatticeProb.Sobolev.exists_finite_supNet_of_uniformLip_of_proper
#print axioms LatticeProb.Sobolev.exists_uniform_lipschitz_bandTrunc

/-! ### The mollifier Fourier normalisation (density repair) -/

#print axioms LatticeProb.Sobolev.fourier_comp_smul
#print axioms LatticeProb.Sobolev.fourier_normalized_dilation
#print axioms LatticeProb.Sobolev.tendsto_fourier_mollifierDil
#print axioms LatticeProb.Sobolev.mollifierFourierTendsto

/-! ### Fourier convolution, averaging and test-function Sobolev duality -/

#print axioms LatticeProb.Sobolev.fourier_toLp_ae_eq
#print axioms LatticeProb.Sobolev.abs_integral_mul_le_lintegral_fourier
#print axioms LatticeProb.Sobolev.sub_convReal_eq_integral_translate
#print axioms LatticeProb.Sobolev.ae_sub_convReal_eq_integral_translate
#print axioms LatticeProb.Sobolev.sobolevNormSq_congr_ae
#print axioms LatticeProb.Sobolev.sobolevNormSq_sub_convReal_le
#print axioms LatticeProb.Sobolev.sobolevNormSq_toReal_eq_integral
#print axioms LatticeProb.Sobolev.sobolevWeight
#print axioms LatticeProb.Sobolev.sobolevWeight_nonneg
#print axioms LatticeProb.Sobolev.sobolevNormSq_eq_lintegral_weight
#print axioms LatticeProb.Sobolev.norm_fourier_lift_convReal_le
#print axioms LatticeProb.Sobolev.sobolevNormSq_convReal_le
#print axioms LatticeProb.Sobolev.convReal
#print axioms LatticeProb.Sobolev.fourier_convolution_lift
#print axioms LatticeProb.Sobolev.lift_convReal
#print axioms LatticeProb.Sobolev.fourier_lift_convReal
#print axioms LatticeProb.Sobolev.continuous_sobolevWeight
#print axioms LatticeProb.Sobolev.continuous_fourier_lift
#print axioms LatticeProb.Sobolev.lintegral_fourier_pairing_le
#print axioms LatticeProb.Sobolev.sobolevDualityBound_of_memLp
#print axioms LatticeProb.Sobolev.integrable_sobolevWeight_mul_norm_sq
#print axioms LatticeProb.Sobolev.sq_abs_integral_mul_le_integral_weight
#print axioms LatticeProb.Sobolev.IsTestFn.integrable
#print axioms LatticeProb.Sobolev.IsTestFn.memLp_two
#print axioms LatticeProb.Sobolev.IsTestFn.comp_sub_left
#print axioms LatticeProb.Sobolev.IsTestFn.fderiv_apply
#print axioms LatticeProb.Sobolev.sobolevDualityBound_of_isTestFn
#print axioms LatticeProb.Sobolev.sq_abs_integral_mul_le_integral_weight_of_isTestFn
#print axioms LatticeProb.Sobolev.sobolevDualityBound_convReal
#print axioms LatticeProb.Sobolev.sobolevDualityBound_fderiv
#print axioms LatticeProb.Sobolev.isTestFn_contDiffBump
#print axioms LatticeProb.Sobolev.sobolevNormSq_mul_pos_bump
#print axioms LatticeProb.Sobolev.exists_fderiv_contDiffBump_ne_zero
#print axioms LatticeProb.Sobolev.sobolevDualityBound_fderiv_bump
/-! ### Euclidean lattice sums: the critical asymptotic and its estimates -/

#print axioms LatticeProb.Euclidean.Asymptotic.shell_sum_asymp
#print axioms LatticeProb.Euclidean.Integral.disjoint_cube_integral_inequality
#print axioms LatticeProb.Euclidean.Integral.annulus_rpow_integral
#print axioms LatticeProb.Euclidean.Shell.volume_unit_ball
#print axioms LatticeProb.Euclidean.Shell.unitBallVolume_eq_pi_div_gamma
#print axioms LatticeProb.Euclidean.Summability.nonzero_radial_error_summable_real
#print axioms LatticeProb.Euclidean.Estimates.rpow_sum_upper_bound
#print axioms LatticeProb.Euclidean.Estimates.exterior_rpow_sum_bound
#print axioms LatticeProb.Euclidean.Examples.critical_sum_asymp_dim_one
#print axioms LatticeProb.Euclidean.Examples.critical_sum_asymp_dim_two
#print axioms LatticeProb.Euclidean.Examples.exterior_summable_dim_one
#print axioms LatticeProb.Euclidean.Examples.upper_bound_dim_two

/-! ### Stretched-exponential summability -/

#print axioms LatticeProb.pow_mul_exp_neg_mul_le_factorial_div
#print axioms LatticeProb.pow_mul_exp_neg_sqrt_le_factorial_div_mul_inv_sq
#print axioms LatticeProb.summable_pow_mul_exp_neg_sqrt

/-! ### Long lattice detours -/

#print axioms LatticeProb.exists_five_log_rpow_le
#print axioms LatticeProb.detour_ne
#print axioms LatticeProb.exists_long_lattice_path_avoiding_site
#print axioms LatticeProb.abs_sub_coord_le_one_of_adj
#print axioms LatticeProb.abs_sub_coord_le_of_walk
#print axioms LatticeProb.sum_abs_sub_le_of_walk_box
#print axioms LatticeProb.lattice_adj_add_right_iff
#print axioms LatticeProb.External.FeyDenBoerRedigCubicalCluster
#print axioms LatticeProb.External.FeyLevinePeresRadius
#print axioms LatticeProb.GreenTwoSided.killedGreen_diag_two_le_log
#print axioms LatticeProb.GreenTwoSided.killedGreen_row_sum_le_sq
#print axioms LatticeProb.GreenTwoSided.killedGreen_diag_le_const_of_three_le
#print axioms LatticeProb.GreenTwoSided.killedGreen_diag_pos_control
#print axioms LatticeProb.Network.sum_mul_laplacian_comm
#print axioms LatticeProb.Sandpile.fdbr_parallel_terminal
#print axioms LatticeProb.Sandpile.flp_specialization
#print axioms LatticeProb.Sandpile.pconf_zero
#print axioms LatticeProb.Sandpile.pconf_nonneg
#print axioms LatticeProb.le_sandpile_scale_root
#print axioms LatticeProb.exists_sandpile_scale_bound
#print axioms LatticeProb.Sandpile.dirac_nonneg
#print axioms LatticeProb.Sandpile.podo_succ_eq_min_floor
#print axioms LatticeProb.Sandpile.podo_succ_le_floor
#print axioms LatticeProb.Sandpile.podo_mono
#print axioms LatticeProb.Sandpile.podo_eq_zero

#print axioms LatticeProb.planar_killedGreen_zero_zero_log_lower

#print axioms LatticeProb.curveSpace_project_comp_monotone
#print axioms LatticeProb.curveSpace_project_terminalPause
#print axioms LatticeProb.finite_stopping_integral_eq_terminal
#print axioms LatticeProb.finite_stopping_second_moment_le
#print axioms LatticeProb.bounded_stopping_integrable_and_integral_eq_terminal

#print axioms LatticeProb.Network.subharmonic_maximum_principle
#print axioms LatticeProb.Network.existsUnique_dirichlet
#print axioms LatticeProb.Network.dirichlet_stability
#print axioms LatticeProb.Network.boundaryAccessible_of_strict_subharmonic
#print axioms LatticeProb.Network.green_netLaplacian
#print axioms LatticeProb.Network.discrete_integration_by_parts

#print axioms LatticeProb.ae_iff_exists_measurable_null_set
#print axioms LatticeProb.map_supportedLaw
#print axioms LatticeProb.supportedLaw_unique
#print axioms LatticeProb.levyProkhorovEDist_map_le_of_lipschitz_one
#print axioms LatticeProb.levyProkhorovEDist_map_endPoint_le
#print axioms LatticeProb.levyProkhorovEDist_le_of_coupling
#print axioms LatticeProb.compProd_map_dependent_of_kernel_map
#print axioms LatticeProb.compProd_map_dependent_of_kernel_map_ae
#print axioms LatticeProb.completeSubcoupling_fst
#print axioms LatticeProb.completeSubcoupling_snd
#print axioms LatticeProb.completeSubcoupling_bad_event_le
#print axioms LatticeProb.matchedCellCoupling_fst
#print axioms LatticeProb.matchedCellCoupling_snd
#print axioms LatticeProb.matchedCellCoupling_univ
#print axioms LatticeProb.matchedCellCoupling_compl_prod_eq_zero
#print axioms LatticeProb.finitePartitionCoupling_spec
#print axioms LatticeProb.levyProkhorovEDist_le_of_finite_cells
#print axioms LatticeProb.finitePartitionCouplingKernel_spec
#print axioms LatticeProb.CameronMartin.map_tiltMeasure_path
#print axioms LatticeProb.CameronMartin.integral_mul_tiltDensity
#print axioms LatticeProb.CameronMartin.abs_measureReal_shift_sub_le
#print axioms LatticeProb.McLeish.tendstoInDistribution_martingale_clt
#print axioms LatticeProb.GaussConc.measurePreserving_rotPair
#print axioms LatticeProb.GaussConc.integral_inner_mul_stdGaussian
#print axioms LatticeProb.GaussConc.gaussEuclid_map_ofLp
#print axioms LatticeProb.GaussConc.integral_mul_sub_eq_cov
#print axioms LatticeProb.GaussConc.mgf_le_of_smoothBdd
#print axioms LatticeProb.GaussConc.mgf_le_of_lipschitz_bdd
#print axioms LatticeProb.openExitTime_mem_frontier
#print axioms LatticeProb.isStoppingTime_openExitTime
#print axioms LatticeProb.measurable_openExitTime
#print axioms LatticeProb.ae_openExitTime_ne_top
#print axioms LatticeProb.openExitTime_uniform_tail
#print axioms LatticeProb.isHarmonicOn_iff_harmonicOnNhd
#print axioms LatticeProb.harmonicNearClosure_iff
#print axioms LatticeProb.IsHarmonicOn.exists_compactSupport_eq_near_compact
#print axioms LatticeProb.gaussianHerbstBound_all
#print axioms LatticeProb.gaussian_lipschitz_concentration_unconditional
#print axioms LatticeProb.ContinuousMapBorel.ContinuousMap.borel_eq_iSup_comap_eval
#print axioms LatticeProb.measurable_pathMap
#print axioms LatticeProb.GaussConc.mgf_le_of_lipschitz
#print axioms LatticeProb.GaussConc.tail_le_of_lipschitz
#print axioms LatticeProb.preBrownian_increment_fourth_moment
#print axioms LatticeProb.uniform_taylor_remainder_of_contDiff_compactSupport
#print axioms LatticeProb.nnrealApproxSeq_isStoppingTime
#print axioms LatticeProb.isStoppingTime_continuousExitTime
#print axioms LatticeProb.standardBrownianLaw_ae_finiteExit
#print axioms LatticeProb.FiniteChain.pairTV_add_le
#print axioms LatticeProb.FiniteChain.pairTV_mul_le
#print axioms LatticeProb.measure_exists_partialSum_ge_le
#print axioms LatticeProb.measure_sum_bernoulli_le
#print axioms LatticeProb.IsBrownianSpace.exists_continuousVersion
#print axioms LatticeProb.isStandardBrownianLaw_map_pathMap
#print axioms LatticeProb.integral_exitPosition_eq_pathMap
#print axioms LatticeProb.laplacian_affine_comp
#print axioms LatticeProb.IsHarmonicOn.comp_affine
#print axioms LatticeProb.standardBrownianLaw_integral_quadratic
#print axioms LatticeProb.standardBrownianLaw_unique
#print axioms LatticeProb.standardBrownianLaw_map_shift
#print axioms LatticeProb.standardBrownianLaw_finiteStopping_inter
#print axioms LatticeProb.standardBrownianLaw_taylor_expectation_bound
#print axioms LatticeProb.standardBrownianLaw_predictable_taylor_bound
#print axioms LatticeProb.standardBrownianLaw_dyadic_stopped_harmonic_bound
#print axioms LatticeProb.standardBrownianLaw_bounded_stopped_harmonic_difference
#print axioms LatticeProb.standardBrownianLaw_integral_exit_harmonic_compactSupport
#print axioms LatticeProb.standardBrownianLaw_integral_exit_harmonicNearClosure
#print axioms LatticeProb.McLeish.Example.rademacherRows_clt
#print axioms LatticeProb.integral_openExit_harmonic_compactSupport
#print axioms LatticeProb.integral_openExit_harmonicNearClosure
#print axioms LatticeProb.isQuantile_iff_mem_Icc
#print axioms LatticeProb.isQuantile_lowerQuantile
#print axioms LatticeProb.bernoulli_hoeffding
#print axioms LatticeProb.Skorokhod.exists_skorokhodPartition
#print axioms LatticeProb.Skorokhod.skMix_key
#print axioms LatticeProb.Skorokhod.skMix_isProbabilityMeasure
#print axioms LatticeProb.isTrivialSigma_of_indep_self
#print axioms LatticeProb.tendsto_integral_abs_condExp_sub
#print axioms LatticeProb.isQuantile_map_affine_iff
#print axioms LatticeProb.isQuantile_iff_eq_lowerQuantile
#print axioms LatticeProb.IsQuantile.of_tendsto
#print axioms LatticeProb.IsQuantile.of_tendstoInDistribution
#print axioms LatticeProb.measureReal_binomDom_hoeffding
#print axioms LatticeProb.Skorokhod.exists_skData
#print axioms LatticeProb.isTrivialSigma_iInf_sup
#print axioms LatticeProb.Pitt.integral_mul_le_integral_mul_stdGaussian
#print axioms LatticeProb.Pitt.exists_gram_map_eq
#print axioms LatticeProb.Pitt.tendsto_closedApprox
#print axioms LatticeProb.brownian_integral_abs_pow_eq
#print axioms LatticeProb.eVariationOn_image_range_of_monotone
#print axioms LatticeProb.eVariationOn_id_Icc
#print axioms LatticeProb.Skorokhod.SkData.map_X'
#print axioms LatticeProb.isTrivialSigma_iInf_bmPast
#print axioms LatticeProb.isTrivialSigma_iInf_bmPast_of
#print axioms LatticeProb.brownian_integral_integral_abs_pow_le
#print axioms LatticeProb.Pitt.integral_mul_le_of_contDiff
#print axioms LatticeProb.MetricGeometry.curveLength_eq_partitionLengthSup
#print axioms LatticeProb.MetricGeometry.curveLength_add
#print axioms LatticeProb.GaussConc.borellTIS_finiteMax
#print axioms LatticeProb.Kahane.integral_inner_mul_stdGaussian_of_le
#print axioms LatticeProb.polishSpace_continuousMap
#print axioms LatticeProb.isTrivialSigma_tailFar
#print axioms LatticeProb.isTrivialSigma_tailFar_drift
#print axioms LatticeProb.Pitt.integral_mul_le_of_lipschitz
#print axioms LatticeProb.GaussConc.borellTIS_gaussianVector
#print axioms LatticeProb.Kahane.norm_kGrad_le
#print axioms LatticeProb.MetricGeometry.isLengthSpace_iff_curves
#print axioms LatticeProb.Skorokhod.SkData.prob_good_compl
#print axioms LatticeProb.Skorokhod.SkData.prob_bad
#print axioms LatticeProb.Skorokhod.SkData.tendsto_X'
#print axioms LatticeProb.Pitt.measureReal_mul_le_inter_of_isClosed
#print axioms LatticeProb.Kahane.integral_kW_zero_le
#print axioms LatticeProb.GaussConc.SupTail.tendsto_seqMax
#print axioms LatticeProb.MetricGeometry.hasUnitSpeedOn_lengthParam
#print axioms LatticeProb.MetricGeometry.exists_lipschitz_path
#print axioms LatticeProb.MetricGeometry.hasApproxMidpoints_of_isLengthSpace
#print axioms LatticeProb.MetricGeometry.curveLength_eq_iSup_internalEDist
#print axioms LatticeProb.MetricGeometry.internalEDist_eq_edist_of_ball_subset
#print axioms LatticeProb.Pitt.measureReal_mul_le_inter
#print axioms LatticeProb.Pitt.prod_prob_le_biInter
#print axioms LatticeProb.Pitt.exists_measure_compl_ge_of_prod_le
#print axioms LatticeProb.GaussConc.SupTail.borellTIS_iSup_seq
#print axioms LatticeProb.Kahane.kahane_convexity
#print axioms LatticeProb.MetricGeometry.exists_shortest_path
#print axioms LatticeProb.MetricGeometry.isLengthSpace_of_hasApproxMidpoints
#print axioms LatticeProb.Pitt.integral_mul_le_of_monotone
#print axioms LatticeProb.Kahane.kahane_convexity_rpow
#print axioms LatticeProb.MetricGeometry.compactSpace_metricFunSpace
#print axioms LatticeProb.Skorokhod.exists_skorokhod_representation
#print axioms LatticeProb.condIndep_iff_condIndepEv
#print axioms LatticeProb.reciprocal_power_bound_of_power_decay
#print axioms LatticeProb.Network.ConductanceGraph.tsum_gradSq_eq
#print axioms LatticeProb.efronStein_sigma
#print axioms LatticeProb.condExp_sup_indep_eq
#print axioms LatticeProb.Network.killedMassGenerator_energy
#print axioms LatticeProb.Network.hasDerivAt_weighted_sq_of_killed_heat
#print axioms LatticeProb.Network.ConductanceGraph.dirichletForm_add_left
#print axioms LatticeProb.Network.ConductanceGraph.dirichletForm_self
#print axioms LatticeProb.polynomialLaplacian_squaredNorm_mul
#print axioms LatticeProb.Kahane.kahane_rpow_le_add_const
#print axioms LatticeProb.Network.uniformizedTransition_generator
#print axioms LatticeProb.Network.sum_uniformizedTransition
#print axioms LatticeProb.Network.killedHeatMatrix_add
#print axioms LatticeProb.Network.hasDerivAt_killedHeatFlow
#print axioms LatticeProb.Network.ConductanceGraph.DirichletSpace.norm_sq_eq_energy
#print axioms LatticeProb.Network.ConductanceGraph.weightedGradient_norm_sq
#print axioms LatticeProb.Network.ConductanceGraph.weightedGradientCoord_mem_iff
#print axioms LatticeProb.Network.ConductanceGraph.eq_of_eqOn_energy_sub_zero
#print axioms LatticeProb.polynomial_eq_zero_of_eval_zero_on_ball
#print axioms LatticeProb.laplacian_polynomialEval
#print axioms LatticeProb.isHarmonicOn_polynomialEval_of_laplacian_eq_zero
#print axioms LatticeProb.aeDeterminedSigma_of_condIndepEv_of_ae_eq
#print axioms LatticeProb.Network.ConductanceGraph.IsHarmonicAt.tsum_eq_zero
#print axioms LatticeProb.Network.ConductanceGraph.energyENN_eq_top_iff_not_hasFiniteEnergy
#print axioms LatticeProb.Network.ConductanceGraph.energyENN_eq_ofReal_Energy
#print axioms LatticeProb.Network.killedHeatMatrix_isSubstochastic
#print axioms LatticeProb.Network.killedHeatMatrix_diagonal_pos
#print axioms LatticeProb.Network.ConductanceGraph.DirichletSpace.instCompleteSpace
#print axioms LatticeProb.Network.ConductanceGraph.isClosed_zeroOn
#print axioms LatticeProb.Network.ConductanceGraph.isClosed_zeroTraceGradient
#print axioms LatticeProb.MetricGeometry.IsCompact.exists_setEDist_eq_edist
#print axioms LatticeProb.MetricGeometry.IsGeodesicCurveBetween.isGeodesicCurve
#print axioms LatticeProb.GaussConc.SupTail.borellTIS_iSup_continuous
#print axioms LatticeProb.GaussConc.SupTail.tail_iSup_abs_le_gaussian
#print axioms LatticeProb.Network.ConductanceGraph.isCond_toSimpleGraph
#print axioms LatticeProb.Network.ConductanceGraph.isHarmonicAt_iff_netLaplacian
#print axioms LatticeProb.Network.ConductanceGraph.energy_eq_energyOn_half
#print axioms LatticeProb.exists_polynomial_near_continuous_on_compact
#print axioms LatticeProb.ballDirichletOperator_injective
#print axioms LatticeProb.exists_harmonic_polynomial_on_sphere_of_brownianLaw
#print axioms LatticeProb.aeDeterminedBy_of_condIndepEv_of_ae_eq
#print axioms LatticeProb.condIndepEv_sup_of_condIndepEv
#print axioms LatticeProb.Network.killedHeatDensity_symmetric
#print axioms LatticeProb.Network.killedHeatDensity_weighted_L1_le_one
#print axioms LatticeProb.Network.killedHeatDensity_weighted_sq_eq_double
#print axioms LatticeProb.Network.ConductanceGraph.existsUnique_anchored_trace_minimizer
#print axioms LatticeProb.MetricGeometry.infEDist_compl_eq_infEDist_frontier
#print axioms LatticeProb.MetricGeometry.internalEDist_eq_edist_of_le_infEDist
#print axioms LatticeProb.es_resample_identity
#print axioms LatticeProb.es_half_sq_eq_posPart_sq
#print axioms LatticeProb.condIndepEv_condCopy
#print axioms LatticeProb.aeDeterminedBy_of_condCopy_ae_eq
#print axioms LatticeProb.MetricGeometry.internalEDist_eq_of_isLocalIsometryOn
