import Erdos374Research
import Lean

/- Generated source-named inventory; all imported own kernel constants, including private and generated auxiliaries, are separately enumerated by the compiled environment below. -/

#print axioms Erdos374Research.rough_small_factorial_component
#print axioms Erdos374Research.admissibleCofactorsUpTo
#print axioms Erdos374Research.excludedRoughCofactors
#print axioms Erdos374Research.excludedRoughCofactor_has_witness
#print axioms Erdos374Research.card_excludedRoughCofactors_le
#print axioms Erdos374Research.rough_card_le_admissible_add_excluded
#print axioms Erdos374Research.admissibleCofactors_positive_lower_density
#print axioms Erdos374Research.firstHalf
#print axioms Erdos374Research.firstHalf_pairwiseDisjoint
#print axioms Erdos374Research.firstHalf_volume
#print axioms Erdos374Research.bad_blocks_mass_le_exceptional_measure
#print axioms Erdos374Research.sum_increments
#print axioms Erdos374Research.mass_lower_of_good_blocks
#print axioms Erdos374Research.block_mass_ge_local_mass
#print axioms Erdos374Research.shiftedPlateau_ne_zero_offset
#print axioms Erdos374Research.not_dvd_of_integerAvoidingWeight
#print axioms Erdos374Research.exists_dvd_falling_of_small_fract
#print axioms Erdos374Research.exists_dvd_block_of_centered_integer
#print axioms Erdos374Research.factorization_eq_one_of_prime_dvd_not_sq
#print axioms Erdos374Research.not_square_of_selected_block_prime
#print axioms Erdos374Research.block_term_close_to_shift
#print axioms Erdos374Research.longBlockSquareWeight_not_sq_dvd
#print axioms Erdos374Research.blockSeparator_nonzero_selects_odd_prime
#print axioms Erdos374Research.hasRepresentation_five_of_even
#print axioms Erdos374Research.hasRepresentation_six_of_separated_factors
#print axioms Erdos374Research.eventually_lift_through_half
#print axioms Erdos374Research.eventually_window_power_transfer
#print axioms Erdos374Research.eventually_candidate_factor_geometry
#print axioms Erdos374Research.squarefree_prime_cofactor_product
#print axioms Erdos374Research.AdmissibleCofactor
#print axioms Erdos374Research.AdmissibleCofactor.not_small_factorial_square
#print axioms Erdos374Research.not_isSquare_mul_of_squarefree_left
#print axioms Erdos374Research.squarefreeComponent_mul_factorial
#print axioms Erdos374Research.bad_cofactor_has_large_common_divisor
#print axioms Erdos374Research.badCofactorsFor
#print axioms Erdos374Research.badFactorialWeight
#print axioms Erdos374Research.badFactorialWeight_nonneg
#print axioms Erdos374Research.card_badCofactorsFor_le
#print axioms Erdos374Research.eventually_badFactorialWeight_le_exp
#print axioms Erdos374Research.summable_badFactorialWeight
#print axioms Erdos374Research.sum_exp_large_indices_le
#print axioms Erdos374Research.tendsto_nat_mul_exp_sixteenth
#print axioms Erdos374Research.exists_badFactorialWeight_tail_small
#print axioms Erdos374Research.factorialRootWeight
#print axioms Erdos374Research.factorialRootWeight_nonneg
#print axioms Erdos374Research.factorialComponent_pos
#print axioms Erdos374Research.eventually_factorialRootWeight_le_exp
#print axioms Erdos374Research.summable_factorialRootWeight
#print axioms Erdos374Research.factorialRootWeightSum
#print axioms Erdos374Research.factorialRootWeightSum_nonneg
#print axioms Erdos374Research.oneTermFamily
#print axioms Erdos374Research.card_oneTermFamily_le
#print axioms Erdos374Research.oneTermNumbers_subset_families
#print axioms Erdos374Research.factorialThreeOneTermCount_le_sqrt
#print axioms Erdos374Research.consecutiveProduct_eq_prod_offsets
#print axioms Erdos374Research.injectiveOn_negative_natCast_Icc
#print axioms Erdos374Research.card_factorialAllowedStartResidues_eq
#print axioms Erdos374Research.cast_consecutiveProduct_eq_rootProduct
#print axioms Erdos374Research.factorial_cast_ne_zero_of_lt
#print axioms Erdos374Research.factorialSquareStartResidues
#print axioms Erdos374Research.factorial_start_mem_squareResidues
#print axioms Erdos374Research.card_factorialSquareStartResidues_le
#print axioms Erdos374Research.card_natMod_image_le_zmod_set
#print axioms Erdos374Research.crtNonzeroClasses
#print axioms Erdos374Research.card_crtNonzeroClasses
#print axioms Erdos374Research.mem_crtNonzeroClasses_natCast
#print axioms Erdos374Research.crtNatResidues
#print axioms Erdos374Research.crtNatResidues_subset_range
#print axioms Erdos374Research.card_crtNatResidues
#print axioms Erdos374Research.mod_mem_crtNatResidues
#print axioms Erdos374Research.crt_avoidance_prefix_lower
#print axioms Erdos374Research.HasRepresentation
#print axioms Erdos374Research.IsInD
#print axioms Erdos374Research.numbersInDUpTo
#print axioms Erdos374Research.countD
#print axioms Erdos374Research.mem_numbersInDUpTo
#print axioms Erdos374Research.representation_card_le
#print axioms Erdos374Research.IsInD.two_le_endpoint
#print axioms Erdos374Research.isInD_unique
#print axioms Erdos374Research.isInD_iff_minimal
#print axioms Erdos374Research.exists_isInD_of_representation
#print axioms Erdos374Research.countD_le
#print axioms Erdos374Research.countD_mono
#print axioms Erdos374Research.HasOrder
#print axioms Erdos374Research.OriginalGrowthConclusion
#print axioms Erdos374Research.hasOrder_linear_of_lower
#print axioms Erdos374Research.prod_le_prod_subset_unit
#print axioms Erdos374Research.prod_one_sub_reciprocal
#print axioms Erdos374Research.prod_one_sub_reciprocal_square
#print axioms Erdos374Research.prime_product_lower
#print axioms Erdos374Research.prime_square_product_lower
#print axioms Erdos374Research.EvenSquarefreeCofactor
#print axioms Erdos374Research.rough_two_mul_evenSquarefree
#print axioms Erdos374Research.card_evenSquarefree_lower
#print axioms Erdos374Research.evenSquarefree_positive_lower_density
#print axioms Erdos374Research.admissible_prime_candidates_linear
#print axioms Erdos374Research.evenSquarefree_prime_candidates_linear
#print axioms Erdos374Research.factorial_eq_mul_pred
#print axioms Erdos374Research.paired_factorials
#print axioms Erdos374Research.four_factorial_identity
#print axioms Erdos374Research.six_factorial_identity
#print axioms Erdos374Research.five_factorial_identity
#print axioms Erdos374Research.straus_identity
#print axioms Erdos374Research.straus_even_seed
#print axioms Erdos374Research.straus_odd_seed
#print axioms Erdos374Research.falling
#print axioms Erdos374Research.falling_pos
#print axioms Erdos374Research.factorial_mul_falling
#print axioms Erdos374Research.paired_block_factorials
#print axioms Erdos374Research.square_mul_iff
#print axioms Erdos374Research.two_blocks_square_iff
#print axioms Erdos374Research.eventually_blocksAreShort
#print axioms Erdos374Research.growth_five_and_six
#print axioms Erdos374Research.growth_five
#print axioms Erdos374Research.growth_six
#print axioms Erdos374Research.erdos_374_original_growth
#print axioms Erdos374Research.BlocksAreShort
#print axioms Erdos374Research.squarefree_not_isSquare
#print axioms Erdos374Research.no_four_representation_of_short_good_candidate
#print axioms Erdos374Research.no_five_representation_of_short_admissible_candidate
#print axioms Erdos374Research.even_good_candidate_in_D5
#print axioms Erdos374Research.admissible_good_candidate_in_D6
#print axioms Erdos374Research.eventually_countD_three_le_linear
#print axioms Erdos374Research.count_of_cover_le
#print axioms Erdos374Research.growth_five_and_six_of_short_blocks
#print axioms Erdos374Research.hasRepresentation_four_of_four_mul
#print axioms Erdos374Research.fourMultipleFamily
#print axioms Erdos374Research.card_fourMultipleFamily
#print axioms Erdos374Research.fourMultipleFamily_subset
#print axioms Erdos374Research.floor_quarter_le_sum_counts
#print axioms Erdos374Research.growth_four_of_three_upper
#print axioms Erdos374Research.HasLargeSquarefreePrime
#print axioms Erdos374Research.goodPrimeCofactorProducts
#print axioms Erdos374Research.badPrimeCofactorProducts
#print axioms Erdos374Research.card_badPrimeCofactors_le_smooth
#print axioms Erdos374Research.card_candidates_le_good_add_bad
#print axioms Erdos374Research.eventually_goodCandidate_count_lower
#print axioms Erdos374Research.exists_small_candidate_exponent
#print axioms Erdos374Research.eventually_two_rpow_three_quarters_le
#print axioms Erdos374Research.good_candidates_linear_for_small_exponent
#print axioms Erdos374Research.two_candidate_families_positive_density
#print axioms Erdos374Research.realPeriodCell
#print axioms Erdos374Research.realPeriodCells_disjoint
#print axioms Erdos374Research.realPeriodCell_measure
#print axioms Erdos374Research.mem_realPeriodCell_floor
#print axioms Erdos374Research.periodic_weight_integral_lower_from_band
#print axioms Erdos374Research.hardFactorialFibre
#print axioms Erdos374Research.mem_hardFactorialFibre
#print axioms Erdos374Research.hardFactorialFibre_subset
#print axioms Erdos374Research.hardFactorialFibre_upperHalf_residues
#print axioms Erdos374Research.hardFactorialFibre_square_residues
#print axioms Erdos374Research.weil_residue_bound_le_kappa
#print axioms Erdos374Research.gallagherPrimeBand
#print axioms Erdos374Research.mem_gallagherPrimeBand
#print axioms Erdos374Research.gallagherPrimeBand_disjoint_upperHalf
#print axioms Erdos374Research.hardFactorialFibre_band_residues
#print axioms Erdos374Research.gallagherPrimeBand_weighted_sum
#print axioms Erdos374Research.gallagherFactorialResidueBudget
#print axioms Erdos374Research.gallagherFactorialDenominator
#print axioms Erdos374Research.gallagherFactorial_denominator_identity
#print axioms Erdos374Research.primeRange_log_sum_eq_theta
#print axioms Erdos374Research.gallagherPrimeBand_log_sum_le_theta
#print axioms Erdos374Research.gallagher_log_numerator_le
#print axioms Erdos374Research.hardFactorialFibre_card_le
#print axioms Erdos374Research.d3Eta
#print axioms Erdos374Research.d3PrimeLowerExponent
#print axioms Erdos374Research.d3PrimeUpperExponent
#print axioms Erdos374Research.d3HardExponent
#print axioms Erdos374Research.rpowCeil
#print axioms Erdos374Research.rpowCeil_lower
#print axioms Erdos374Research.rpowCeil_upper
#print axioms Erdos374Research.rpowCeil_mono_exponent
#print axioms Erdos374Research.d3SieveCoefficient
#print axioms Erdos374Research.d3SieveCoefficient_lower
#print axioms Erdos374Research.log_four_le_two
#print axioms Erdos374Research.eventually_hardFactorial_denominator
#print axioms Erdos374Research.eventually_hardFactorialFibre_card
#print axioms Erdos374Research.prefixMass
#print axioms Erdos374Research.reciprocalWindow
#print axioms Erdos374Research.prefixMass_succ
#print axioms Erdos374Research.reciprocal_prefix_abel
#print axioms Erdos374Research.sum_Ioc_window
#print axioms Erdos374Research.reciprocal_window_abel
#print axioms Erdos374Research.shifted_harmonic_sum
#print axioms Erdos374Research.reciprocal_window_lower
#print axioms Erdos374Research.predicateIndicator
#print axioms Erdos374Research.predicatePrefix
#print axioms Erdos374Research.prefixMass_indicator
#print axioms Erdos374Research.reciprocalWindow_indicator
#print axioms Erdos374Research.positive_density_power_window
#print axioms Erdos374Research.plateauWidth
#print axioms Erdos374Research.integerAvoidingWeight
#print axioms Erdos374Research.plateauWidth_pos
#print axioms Erdos374Research.plateauWidth_lt_tenth
#print axioms Erdos374Research.integerAvoidingWeight_contDiff
#print axioms Erdos374Research.integerAvoidingWeight_periodic
#print axioms Erdos374Research.integerAvoidingWeight_nonneg
#print axioms Erdos374Research.integerAvoidingWeight_le_one
#print axioms Erdos374Research.integerAvoidingWeight_zero_near_integer
#print axioms Erdos374Research.integerAvoidingWeight_eq_one_far
#print axioms Erdos374Research.integerAvoidingWeight_ne_zero_imp_far
#print axioms Erdos374Research.not_sq_dvd_of_integerAvoidingWeight
#print axioms Erdos374Research.residueFibreMass
#print axioms Erdos374Research.residueCollisionMass
#print axioms Erdos374Research.residueFibreMass_nonneg
#print axioms Erdos374Research.residueFibreMass_sum
#print axioms Erdos374Research.residueCollisionMass_nonneg
#print axioms Erdos374Research.residueCollisionMass_eq_sum
#print axioms Erdos374Research.residueFibreMass_eq_sum
#print axioms Erdos374Research.residueCollisionMass_lower
#print axioms Erdos374Research.residuePairWeight
#print axioms Erdos374Research.weighted_collision_identity
#print axioms Erdos374Research.weighted_collision_upper
#print axioms Erdos374Research.largerSieve_weighted
#print axioms Erdos374Research.largerSieve_card_bound
#print axioms Erdos374Research.sum_log_prime_divisors_le
#print axioms Erdos374Research.prime_dvd_dist_of_mod_eq
#print axioms Erdos374Research.residuePairWeight_log_le
#print axioms Erdos374Research.largerSieve_nat_card_bound
#print axioms Erdos374Research.blockDetectingWeight
#print axioms Erdos374Research.blockDetectingReal
#print axioms Erdos374Research.selectedBlockCenter_pos_le
#print axioms Erdos374Research.blockDetectingReal_continuous
#print axioms Erdos374Research.blockDetectingReal_nonneg
#print axioms Erdos374Research.blockDetectingWeight_eval
#print axioms Erdos374Research.blockDetectingWeight_primeSum_zero
#print axioms Erdos374Research.blockDetectingWeight_integral_lower
#print axioms Erdos374Research.exists_fixed_integerAvoidingWeight
#print axioms Erdos374Research.exists_longBlockSquareWeight_C3_bound
#print axioms Erdos374Research.eventually_longBlockScale_ranges
#print axioms Erdos374Research.eventually_no_long_two_blocks_with_relation
#print axioms Erdos374Research.longBlockSigma
#print axioms Erdos374Research.longBlockPrimeScale
#print axioms Erdos374Research.longBlockPrimeScale_bounds
#print axioms Erdos374Research.longBlockPrimeScale_pos
#print axioms Erdos374Research.longBlock_ratio_bounds
#print axioms Erdos374Research.plateauWidth_natPower
#print axioms Erdos374Research.lower_dominant_avoided_width
#print axioms Erdos374Research.upperBlockSeparator
#print axioms Erdos374Research.lowerBlockSeparator
#print axioms Erdos374Research.blockSeparator
#print axioms Erdos374Research.blockSeparatorReal
#print axioms Erdos374Research.selectedBlockCenter
#print axioms Erdos374Research.blockSeparatorReal_eval
#print axioms Erdos374Research.blockSeparator_contDiff
#print axioms Erdos374Research.blockSeparator_periodic
#print axioms Erdos374Research.blockSeparator_norm_le_one
#print axioms Erdos374Research.blockSeparatorReal_continuous
#print axioms Erdos374Research.blockSeparatorReal_nonneg
#print axioms Erdos374Research.blockSeparatorReal_periodic
#print axioms Erdos374Research.blockSeparatorReal_period_mass
#print axioms Erdos374Research.exists_blockSeparator_C3_bound
#print axioms Erdos374Research.largeIndexSourceIntervals
#print axioms Erdos374Research.largeIndexSourceEndpoints
#print axioms Erdos374Research.mem_largeIndexSourceIntervals
#print axioms Erdos374Research.nontrivialFactorialThreeCount_le_small_large
#print axioms Erdos374Research.hardParameterPairs
#print axioms Erdos374Research.hardEndpointEnvelope
#print axioms Erdos374Research.largeIndexSourceEndpoints_subset_envelope
#print axioms Erdos374Research.hardEndpointEnvelope_card_bound
#print axioms Erdos374Research.eventually_le_rpow_of_powerUpperBound_zero
#print axioms Erdos374Research.eventually_largeIndexSourceEndpoints_card
#print axioms Erdos374Research.eventually_nontrivialFactorialThreeCount_le
#print axioms Erdos374Research.nontrivialFactorialThreeCount_isBigO_rpow
#print axioms Erdos374Research.d3HardExponent_lt_half
#print axioms Erdos374Research.eventually_orderedTwoBlocks_short
#print axioms Erdos374Research.eventually_orderedTwoBlocks_small_parameters
#print axioms Erdos374Research.hasRepresentation_succ_iff
#print axioms Erdos374Research.hasRepresentation_two_iff
#print axioms Erdos374Research.hasRepresentation_three_iff
#print axioms Erdos374Research.hasRepresentation_three_iff_upstream
#print axioms Erdos374Research.hasRepresentation_four
#print axioms Erdos374Research.hasRepresentation_five
#print axioms Erdos374Research.hasRepresentation_six
#print axioms Erdos374Research.pairedWeight
#print axioms Erdos374Research.continuous_pairedWeight
#print axioms Erdos374Research.pairedLinear
#print axioms Erdos374Research.pairedQuadratic
#print axioms Erdos374Research.pairedMode_eval
#print axioms Erdos374Research.pairedPolynomial_eval
#print axioms Erdos374Research.pairedPolynomial_primeSum
#print axioms Erdos374Research.pairedPolynomial_integral
#print axioms Erdos374Research.pairedPolynomial_discrepancy
#print axioms Erdos374Research.norm_product_sub_product_le
#print axioms Erdos374Research.fourierTailConstant
#print axioms Erdos374Research.fourierMassConstant
#print axioms Erdos374Research.smoothTruncationError
#print axioms Erdos374Research.smoothCoefficientMass
#print axioms Erdos374Research.smoothTruncationError_nonneg
#print axioms Erdos374Research.smoothCoefficientMass_nonneg
#print axioms Erdos374Research.smoothTruncation_bound
#print axioms Erdos374Research.pairedSmooth_discrepancy
#print axioms Erdos374Research.residuePrefix
#print axioms Erdos374Research.residue_block_injective
#print axioms Erdos374Research.residuePrefix_card_ge_blocks
#print axioms Erdos374Research.residuePrefix_card_lower_real
#print axioms Erdos374Research.normalizedPlateau_unit_mass_upper
#print axioms Erdos374Research.shiftedPlateau_period_mass_upper
#print axioms Erdos374Research.integerAvoidingWeight_period_defect
#print axioms Erdos374Research.primeCofactorPairs
#print axioms Erdos374Research.primeCofactorProducts
#print axioms Erdos374Research.mem_primeCofactorPairs
#print axioms Erdos374Research.primeCofactorProducts_le
#print axioms Erdos374Research.primeCofactorProducts_gt_half
#print axioms Erdos374Research.card_primeCofactorProducts
#print axioms Erdos374Research.upperHalfPrime_card_lower
#print axioms Erdos374Research.nat_div_ge_half_real_ratio
#print axioms Erdos374Research.primeCofactor_card_finite_lower
#print axioms Erdos374Research.cofactorPowerWindow
#print axioms Erdos374Research.eventually_primeCofactor_window_parameters
#print axioms Erdos374Research.positive_density_primeCofactorProducts
#print axioms Erdos374Research.eventually_rational_product_prime_comparison
#print axioms Erdos374Research.logarithmic_radiusFactor
#print axioms Erdos374Research.smoothTruncationError_logarithmicRadius
#print axioms Erdos374Research.eventually_rational_product_logarithmic_comparison
#print axioms Erdos374Research.eventually_yudin_dyadic_comparison
#print axioms Erdos374Research.eventually_yudin_prime_comparison_fourteen
#print axioms Erdos374Research.eventually_yudin_prime_comparison
#print axioms Erdos374Research.primeComparisonConstant
#print axioms Erdos374Research.primeComparisonConstant_nonneg
#print axioms Erdos374Research.primeComparison_scalar_budget
#print axioms Erdos374Research.eventually_rationalMode_highLow
#print axioms Erdos374Research.eventually_primeMode_comparison
#print axioms Erdos374Research.eventually_logPow_le_small_rpow
#print axioms Erdos374Research.logarithmicRadius_le_twice_logPow
#print axioms Erdos374Research.eventually_square_le_stretchedExp
#print axioms Erdos374Research.eventually_rationalParameterRanges
#print axioms Erdos374Research.reciprocal_weight_log_integral_lower
#print axioms Erdos374Research.prime_integral_norm_lower_of_real_reciprocal_mass
#print axioms Erdos374Research.rationalQuadraticBand
#print axioms Erdos374Research.measurableSet_rationalQuadraticBand
#print axioms Erdos374Research.mem_rationalQuadraticBand
#print axioms Erdos374Research.rationalQuadraticBand_measure_lower
#print axioms Erdos374Research.quadratic_phase_variation
#print axioms Erdos374Research.one_hundredth_le_dist_integer_of_innerBand
#print axioms Erdos374Research.integerAvoidingWeight_eq_one_of_innerBand
#print axioms Erdos374Research.quadratic_period_integral_lower
#print axioms Erdos374Research.full_period_integral_lower
#print axioms Erdos374Research.longBlockSquareWeight
#print axioms Erdos374Research.longBlockSquareWeight_contDiff
#print axioms Erdos374Research.longBlockSquareWeight_nonneg
#print axioms Erdos374Research.longBlockSquareWeight_le_one
#print axioms Erdos374Research.longBlockSquareWeight_periodic
#print axioms Erdos374Research.longBlockSquareWeight_reciprocal_mass
#print axioms Erdos374Research.pairedLinear_integer_identity
#print axioms Erdos374Research.pairedLinear_separation
#print axioms Erdos374Research.pairedLinear_box_bound
#print axioms Erdos374Research.pairedQuadratic_box_bound
#print axioms Erdos374Research.paired_stationaryPoint_le
#print axioms Erdos374Research.eventually_rational_modes
#print axioms Erdos374Research.additiveCharacter_nat_mul
#print axioms Erdos374Research.additiveCharacter_ne_one_of_between
#print axioms Erdos374Research.geometric_sum_mul_sub_one
#print axioms Erdos374Research.rational_character_sum_zero
#print axioms Erdos374Research.integerAvoidingWeight_character_minorant
#print axioms Erdos374Research.rational_orbit_avoiding_weight_sum
#print axioms Erdos374Research.integral_sum_range_continuous
#print axioms Erdos374Research.integral_nat_interval_eq_unit_translates
#print axioms Erdos374Research.upper_weight_rational_period_mass
#print axioms Erdos374Research.rational_product_periodic
#print axioms Erdos374Research.integral_periodic_rational_nat_interval
#print axioms Erdos374Research.integral_periodic_nat_interval
#print axioms Erdos374Research.lower_weight_rational_period_mass
#print axioms Erdos374Research.OrderedTwoBlocks
#print axioms Erdos374Research.four_representation_has_blocks
#print axioms Erdos374Research.five_representation_has_blocks
#print axioms Erdos374Research.falling_eq_prod_range
#print axioms Erdos374Research.puncturedFalling
#print axioms Erdos374Research.falling_eq_term_mul_punctured
#print axioms Erdos374Research.puncturedFalling_pos
#print axioms Erdos374Research.first_singleton_punctured_square
#print axioms Erdos374Research.roughPrimeSet
#print axioms Erdos374Research.roughModulus
#print axioms Erdos374Research.roughModulus_pos
#print axioms Erdos374Research.roughModulus_neZero
#print axioms Erdos374Research.roughModulus_pairwise
#print axioms Erdos374Research.roughPeriod
#print axioms Erdos374Research.roughPeriod_pos
#print axioms Erdos374Research.rough_modulus_ratio
#print axioms Erdos374Research.rough_modulus_density_lower
#print axioms Erdos374Research.IsRoughSquarefree
#print axioms Erdos374Research.roughSquarefreeUpTo
#print axioms Erdos374Research.finiteRoughSieve
#print axioms Erdos374Research.finiteRoughSieve_subset_union
#print axioms Erdos374Research.roughSquarefree_count_lower
#print axioms Erdos374Research.eventually_roughSquarefree_positive_density
#print axioms Erdos374Research.shortBlockCutoff
#print axioms Erdos374Research.half_rpow_le_nat_sqrt
#print axioms Erdos374Research.eventually_shortBlock_sieve_parameters
#print axioms Erdos374Research.eventually_shortBlockExceptional_power_bound
#print axioms Erdos374Research.eventually_shortBlockExceptional_le_linear
#print axioms Erdos374Research.puncturedSolutionsUpTo
#print axioms Erdos374Research.upperHalfPrime_large_for_short_block
#print axioms Erdos374Research.puncturedSolutions_card_finite_bound
#print axioms Erdos374Research.ShortBlockKey
#print axioms Erdos374Research.shortBlockSlice
#print axioms Erdos374Research.shortBlockExceptional
#print axioms Erdos374Research.mem_shortBlockExceptional
#print axioms Erdos374Research.shortBlockExceptional_card_finite_bound
#print axioms Erdos374Research.puncturedRoots
#print axioms Erdos374Research.puncturedSquareResidues
#print axioms Erdos374Research.puncturedRoots_nonempty
#print axioms Erdos374Research.puncturedSquareResidues_nonempty
#print axioms Erdos374Research.natCast_injective_on_short_range
#print axioms Erdos374Research.puncturedRoots_card_le
#print axioms Erdos374Research.puncturedSquareResidues_mem
#print axioms Erdos374Research.puncturedScalar_ne_zero
#print axioms Erdos374Research.puncturedSquareResidues_card_le_three_quarters
#print axioms Erdos374Research.allowedRestrictions
#print axioms Erdos374Research.allowedRestrictions_proper
#print axioms Erdos374Research.allowedRestrictions_avoids
#print axioms Erdos374Research.primeSieveModulus
#print axioms Erdos374Research.restrictionRatio_ge_third
#print axioms Erdos374Research.shortBlock_largeSieve_card_mul_prime_count
#print axioms Erdos374Research.primeMangoldtIntervalSum_eq_theta_sub
#print axioms Erdos374Research.eventually_primePowerTail_le_quarter
#print axioms Erdos374Research.eventually_theta_forward_three_fifths
#print axioms Erdos374Research.rpow_half_ge_half
#print axioms Erdos374Research.uniform_backward_mass_of_forward
#print axioms Erdos374Research.eventually_theta_backward_three_fifths
#print axioms Erdos374Research.cofactor_prime_gt_power
#print axioms Erdos374Research.first_block_singleton_of_large_squarefree_prime
#print axioms Erdos374Research.short_blocks_singletons_of_not_exceptional
#print axioms Erdos374Research.singleton_blocks_not_square_for_admissible
#print axioms Erdos374Research.singleton_blocks_not_square_for_squarefree
#print axioms Erdos374Research.prod_primes_dvd_iff
#print axioms Erdos374Research.divisor_product_expansion
#print axioms Erdos374Research.sum_divisor_products_le
#print axioms Erdos374Research.exp_sub_one_le_exp_one_mul
#print axioms Erdos374Research.smallPrimeSet
#print axioms Erdos374Research.smallPrimeMoment
#print axioms Erdos374Research.smallPrimeMomentConstant
#print axioms Erdos374Research.smallPrimeMomentConstant_pos
#print axioms Erdos374Research.sum_smallPrimeMoment_le
#print axioms Erdos374Research.SmoothSquarefreeComponent
#print axioms Erdos374Research.squarefreeComponent_rpow_le_moment
#print axioms Erdos374Research.largeSmoothComponents
#print axioms Erdos374Research.card_largeSmoothComponents_le
#print axioms Erdos374Research.smoothComponentsInUpperRange
#print axioms Erdos374Research.small_square_part_large_component
#print axioms Erdos374Research.eventually_smoothComponent_density_bound
#print axioms Erdos374Research.sum_reciprocal_differences
#print axioms Erdos374Research.inverse_square_le_reciprocal_difference
#print axioms Erdos374Research.sum_inverse_squares_tail_le
#print axioms Erdos374Research.largeSquareMultiples
#print axioms Erdos374Research.card_largeSquareMultiples_le
#print axioms Erdos374Research.countD_three_le_factorialThreeCount
#print axioms Erdos374Research.eventually_countD_three_upper
#print axioms Erdos374Research.growth_three
#print axioms Erdos374Research.growth_four
#print axioms Erdos374Research.growth_three_and_four
#print axioms Erdos374Research.not_isSquare_two
#print axioms Erdos374Research.two_mul_square_mem_D3
#print axioms Erdos374Research.twiceSquareFamily
#print axioms Erdos374Research.card_twiceSquareFamily
#print axioms Erdos374Research.twiceSquareFamily_subset
#print axioms Erdos374Research.sqrt_half_sub_one_le_countD_three
#print axioms Erdos374Research.eventually_countD_three_lower
#print axioms Erdos374Research.shiftedPlateau
#print axioms Erdos374Research.shiftedPlateau_contDiff
#print axioms Erdos374Research.shiftedPlateau_periodic
#print axioms Erdos374Research.shiftedPlateau_nonneg
#print axioms Erdos374Research.shiftedPlateau_le_one
#print axioms Erdos374Research.shiftedPlateau_supported
#print axioms Erdos374Research.shiftedPlateau_eq_one
#print axioms Erdos374Research.shiftedPlateau_period_mass
#print axioms Erdos374Research.norm_iteratedFDeriv_shiftedPlateau_le
#print axioms Erdos374Research.shiftedPlateau_lift_periodic
#print axioms Erdos374Research.shiftedPlateau_lift_contDiff
#print axioms Erdos374Research.shiftedPlateau_lift_norm_le_one
#print axioms Erdos374Research.exists_shiftedPlateau_lift_C3_bound
#print axioms Erdos374Research.exists_shiftedPlateau_power_lift_C3_bound
#print axioms Erdos374Research.falling_eq_prod_Ioc
#print axioms Erdos374Research.prime_factorization_zero
#print axioms Erdos374Research.even_factorization_of_isSquare
#print axioms Erdos374Research.eq_of_prime_dvd_block_terms
#print axioms Erdos374Research.factorization_falling_eq_unique
#print axioms Erdos374Research.factorization_eq_one_of_prime_dvd_of_lt_sq
#print axioms Erdos374Research.prime_dvd_lower_block
#print axioms Erdos374Research.exists_lower_block_rational_relation
#print axioms Erdos374Research.not_dvd_lower_term_of_dvd_n_sub_one
#print axioms Erdos374Research.odd_factorization_pred_imp_le
#print axioms Erdos374Research.eventually_three_fifths_le_half
#print axioms Erdos374Research.eventually_two_block_lengths_le_two_thirds
#print axioms Erdos374Research.eventually_large_prime_dominates_blocks
#print axioms Erdos374Research.log_falling_le
#print axioms Erdos374Research.prime_dvd_eq_self_below_twice
#print axioms Erdos374Research.upperHalfPrime_factorization_falling
#print axioms Erdos374Research.prime_factorization_falling_zero_of_end_lt
#print axioms Erdos374Research.upperHalfPrime_not_in_upper_block
#print axioms Erdos374Research.upperHalfPrime_in_lower_dvd_upper
#print axioms Erdos374Research.factorial_upperHalfPrime_dvd_two_blocks
#print axioms Erdos374Research.two_block_cofactor_theta_le
#print axioms Erdos374Research.exists_two_block_cofactor_bound
#print axioms Erdos374Research.shortIntervalPrimes
#print axioms Erdos374Research.mem_shortIntervalPrimes
#print axioms Erdos374Research.sum_log_shortIntervalPrimes
#print axioms Erdos374Research.upper_block_theta_difference_eq_zero
#print axioms Erdos374Research.lower_block_theta_difference_le
#print axioms Erdos374Research.hasRepresentation_two_iff_square
#print axioms Erdos374Research.isInD_two_iff_square
#print axioms Erdos374Research.numbersInD_two_eq_squares
#print axioms Erdos374Research.countD_two
#print axioms Erdos374Research.isInD_three_of_representation_of_not_square
#print axioms Erdos374Research.secondWeightLift
#print axioms Erdos374Research.secondWeightLift_contDiff
#print axioms Erdos374Research.secondWeightLift_periodic
#print axioms Erdos374Research.secondWeightLift_norm_le_one
#print axioms Erdos374Research.norm_iteratedFDeriv_secondWeightLift_le
#print axioms Erdos374Research.norm_iteratedFDeriv_le_C3
#print axioms Erdos374Research.taoC3Norm_mul_le
#print axioms Erdos374Research.taoC3Norm_one_sub_le
#print axioms Erdos374Research.exists_shiftedPlateau_power_second_C3_bound
#print axioms Erdos374Research.integerAvoidingWeight_first_lift_contDiff
#print axioms Erdos374Research.integerAvoidingWeight_first_lift_periodic
#print axioms Erdos374Research.exists_integerAvoidingWeight_power_lift_C3_bound
#print axioms Erdos374Research.exists_integerAvoidingWeight_power_second_C3_bound
#print axioms Erdos374Research.abel_linear_model
#print axioms Erdos374Research.weightedPrimeLogSum_ge_of_theta_lower
#print axioms Erdos374Research.exists_chebyshev_theta_uniform_lower
#print axioms Erdos374Research.exists_weightedPrimeLogSum_lower
#print axioms Erdos374Research.exists_weightedPrimeLogSum_difference_lower
#print axioms Erdos374Research.complexQuadraticChar
#print axioms Erdos374Research.complexQuadraticChar_apply
#print axioms Erdos374Research.complexQuadraticChar_ne_one
#print axioms Erdos374Research.norm_complexQuadraticChar_of_ne_zero
#print axioms Erdos374Research.splitValue
#print axioms Erdos374Research.splitSquareResidues
#print axioms Erdos374Research.splitValue_eq_zero_iff
#print axioms Erdos374Research.eval_finsetRootPolynomial
#print axioms Erdos374Research.norm_sum_complexQuadraticChar_splitValue_le
#print axioms Erdos374Research.quadratic_square_indicator
#print axioms Erdos374Research.sum_indicator_eq_card
#print axioms Erdos374Research.splitSquareResidues_card_identity
#print axioms Erdos374Research.card_splitSquareResidues_le

open Lean

run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let ownRoot : Name := `Erdos374Research
  let isOwnModule := fun (m : Name) => ownRoot.isPrefixOf m
  let ownModules := (moduleNames.filter isOwnModule).qsort Name.lt
  if ownModules.size != 66 then
    throwError "Expected 66 imported own modules, found {ownModules.size}"

  -- Constructor-preserving encoding. Ordinary ToJson Name is insufficient.
  let rec nameJson : Name → Json
    | .anonymous => Json.null
    | .str p s => Json.mkObj [
        ("str", Json.arr #[nameJson p, Json.str s])]
    | .num p n => Json.mkObj [
        ("num", Json.arr #[nameJson p, toJson n])]

  let declKind : ConstantInfo → String
    | .axiomInfo _ => "axiom"
    | .defnInfo _ => "definition"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .inductInfo _ => "inductive"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"

  let mut entries : Array (Name × Json) := #[]
  for (name, ci) in env.constants do
    match env.getModuleIdxFor? name with
    | none => pure ()  -- Current audit-file declarations have no import index.
    | some modIdx =>
      let some owner := moduleNames[modIdx.toNat]? |
        throwError "Invalid imported module index for {name}"
      if isOwnModule owner then
        if ci.name != name then
          throwError "Environment key/ConstantInfo.name mismatch for {name}"
        -- This actual Name exists in the kernel map; never collect an unknown
        -- name reconstructed from text (unknown names can yield empty arrays).
        let axioms ← collectAxioms name
        let row := Json.mkObj [
          ("name_ast", nameJson name),
          ("name_text", Json.str name.toString),
          ("module", Json.str owner.toString),
          ("module_index", toJson modIdx.toNat),
          ("kind", Json.str (declKind ci)),
          ("is_private_name", toJson (isPrivateName name)),
          ("is_internal_name", toJson name.isInternal),
          ("is_internal_detail_name", toJson name.isInternalDetail),
          ("has_numeric_name_part", toJson name.hasNum),
          ("is_unsafe", toJson ci.isUnsafe),
          ("is_partial", toJson ci.isPartial),
          ("axioms", Json.arr (axioms.map fun ax => Json.str ax.toString)),
          ("axiom_name_asts", Json.arr (axioms.map nameJson))]
        entries := entries.push (name, row)

  let rows := (entries.qsort fun a b => Name.lt a.1 b.1).map Prod.snd
  let payload := Json.mkObj [
    ("schema", Json.str "jsp309.own-declarations.v1"),
    ("scope", Json.str "Imported own kernel declarations, all kinds and names"),
    ("own_modules", Json.arr (ownModules.map fun m => Json.str m.toString)),
    ("own_module_count", toJson ownModules.size),
    ("declaration_count", toJson rows.size),
    ("generated_auxiliary_identification", Json.str
      "Name flags are descriptive; no complete author/generated classifier"),
    ("declarations", Json.arr rows)]
  logInfo ("JSP309_OWN_DECLARATIONS_JSON=" ++ payload.compress)
