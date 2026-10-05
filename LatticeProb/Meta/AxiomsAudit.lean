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
#print axioms LatticeProb.greenNorms
#print axioms LatticeProb.exists_srwGreen_gradient
#print axioms LatticeProb.exists_srwGreenInf_gradient
#print axioms LatticeProb.exists_srwGreenInf_le
#print axioms LatticeProb.exists_tsum_srwGreenInf_sq_tail_le
#print axioms LatticeProb.Intersection.exists_lintegral_interCount_sq_le
#print axioms LatticeProb.srwHitProb_eq_green_ratio
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
