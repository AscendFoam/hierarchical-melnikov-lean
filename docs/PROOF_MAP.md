# Hilbert 16 Lean proof map

Last updated: 2026-10-07

This file maps the companion manuscript *Hierarchical Melnikov Realization: Logarithmic Factor Improvement
to Hilbert Number Lower Bounds* to Lean declarations.
The `arxiv-v1` release freezes the manuscript-facing version of this map.
The only allowed status values are `planned`, `proving`, `proved`, and `blocked`.

## Status convention

- `planned`: the final declaration and its dependencies have been identified, but no source file is
  being developed yet.
- `proving`: a zero-`sorry` slice or a proper subset of the required statement is compiling.
- `proved`: the full paper-level statement compiles, is imported by `Hilbert16.lean`, and has passed
  the axiom audit.
- `blocked`: a named missing mathematical or Mathlib interface prevents further progress. A
  `blocked` item must name that interface explicitly.

## Public theorem chain

| Paper location | Lean target | Module | Status | Current evidence / next obligation |
|---|---|---|---|---|
| Theorem 1.1, `thm:main` | `Hilbert16.exists_threeAdicPolynomialVectorField_with_hyperbolicLimitCycles` | `Hilbert16/Dynamics/ThreeAdicSeparatedPeriodicOrbits.lean` | proved | For every `r≥1`, the theorem returns `lambda>1`, one concrete degree-`≤4*3^r-5` polynomial field, and an injective `Fin (cycleLowerBound r)` family of actual standard hyperbolic limit cycles. Each proposition-valued certificate is anchored at the genuine energy Poincaré section; its local-return predicate supplies an open coordinate neighborhood, a `C¹` injective section chart, a differentiable transverse section equation, positive return times, and actual ODE curves ending at the stated return-map values. The stored derivative `rho` satisfies `0<rho`, `rho≠1`, and therefore `|rho|≠1`; distinct indices have disjoint carriers. The previous non-hyperbolic theorem is retained as a forgetful corollary. Root build and axiom audit pass. |
| Theorem 1.1, exact subsequence bound | `Hilbert16.threeAdic_subsequence_hyperbolicLimitCycle_lower_bound` | `Hilbert16/Main.lean` | proved | `DegreeNAdmitsAtLeastHyperbolic (4*3^r-5) (cycleLowerBound r)` is proved for every `r≥2`, using the exact natural-number count, the final degree audit, and the compiled finite injective hyperbolic family. The legacy `DegreeNAdmitsAtLeast` statement follows by forgetting the Poincaré certificate. |
| Corollary 1.2, revised explicit all-degree bound | `Hilbert16.polynomial_hyperbolicLimitCycle_lower_bound_explicit` | `Hilbert16/Main.lean` | proved | For every `d≥31`, this endpoint returns a degree-`≤d` polynomial field and an injective family of `L` standard hyperbolic limit cycles with `B(d)<L`, where `B(d)=(d+5)^2/324*(log((d+5)/12)/log 3)^2-(d+1)^2/16`. It uses the actual subsequence construction and the revised estimate of both terms of its exact count. Full macOS build, axiom audit, and boundary checks passed on 2026-10-07. |
| Additional asymptotic consequence | `Hilbert16.polynomial_hyperbolicLimitCycle_lower_bound_asymptotic` | `Hilbert16/Main.lean` | proved | For `N≥144`, this endpoint returns a degree-`≤N` field and `L` standard hyperbolic limit cycles with `N²(log N)²/(5184*(log 3)^2)≤L`. This positive coarse estimate remains available alongside the revised explicit corollary. |
| Lemma 2.1, `lem:rank-to-roots` | `Hilbert16.rankToSimplePositiveRoots` | `Hilbert16/Analytic/ValuationBasis.lean`, `Hilbert16/Analytic/RankToRoots.lean` | proved | Separating Taylor coefficient functionals recursively give a basis with strictly increasing valuations. Descartes' rule bounds positive roots with multiplicity, the scaled factored equation is jointly `C¹`, and the scalar IFT gives positive simple roots at `τρ_s+o(τ)`. The theorem expands the constructed member back into the original analytic family and includes the `m=1`/zero-root case. Root build and axiom audit pass. |
| Theorem 2.2, `thm:hierarchical` | `Hilbert16.hierarchicalRealization`, `Hilbert16.hierarchicalRealizationOn`, `Hilbert16.threeAdicHierarchicalKernelRealization` | `Hilbert16/Hierarchy.lean`, `Hilbert16/Hierarchy/Realization.lean`, `Hilbert16/Hierarchy/LocalRealization.lean`, `Hilbert16/Hierarchy/ThreeAdicRealization.lean` | proved and concretely instantiated | The scalar IFT and finite intersection give one common positive `zeta` threshold. The local form selects every diagonal root inside an arbitrary `(0,R)` and needs only `C¹` there. The concrete theorem instantiates this with the genuine three-adic row/frequency types, common anisotropy, triangular invisibility, and nonzero mod-twelve diagonal characters, producing simultaneous simple roots with `0<h<1/4`. Root build and axiom audit pass. |
| Corollary 2.3, `cor:tensor` | `Hilbert16.tensorLayer_counting_identity` | `Hilbert16/Counting.lean` | proved | Full commutative-ring identity; axiom audit contains only standard logical axioms. |
| Section 3, Hamiltonian and cells | `Hilbert16.Spikes.chebyshevCellPeriodAnnulus` | `Hilbert16/Spikes/ChebyshevPeriodAnnulus.lean` | proved | The indexed Chebyshev roots give exactly `n²` centers with zero gradient and positive Hessian. The fixed ceiling `chebyshevCommonEnergyUpper = 1/4 < 1/2` works in every legal cell and for every `lambda ≥ 1`; the resulting annulus is a union of explicit regular closed energy curves contained in the cell rectangle. Distinct energies and distinct cells are disjoint, and compact closed subannuli are compiled for the W9 return-map argument. Actual Hamiltonian-time flow and Poincaré return maps remain W9 obligations, not Section 3 geometry. |
| Eq. (3.4)--(3.7), inverse branches | `Hilbert16.Spikes.chebyshevInverseBranch_mem_cellInterval` | `Hilbert16/Spikes/ChebyshevPeriodAnnulus.lean` | proved | The explicit branch is a right inverse on `[-1,1]`; its derivative is nonzero with constant sign, its angle lies in the exact monotonicity interval, and every `|u|<1` point lies in the corresponding open physical cell. These statements feed the uniform period-annulus containment theorem. |
| Lemma 3.2 / Eq. (3.8)--(3.12), exact kernel | `Hilbert16.Spikes.chebyshevFirstMelnikovDisplacement_finiteDensity_eq_kernel_sum`, `Hilbert16.chebyshevFirstMelnikovDisplacement_threeAdicPolynomial_eq` | `Hilbert16/Spikes/ChebyshevMelnikov.lean`, `Hilbert16/Spikes/HamiltonianAngularTrace.lean`, `Hilbert16/Spikes/HamiltonianTimeClock.lean`, `Hilbert16/Spikes/HamiltonianSectionClock.lean`, `Hilbert16/Dynamics/PolynomialPrimitive.lean`, `Hilbert16/Dynamics/ThreeAdicMelnikov.lean`, `Hilbert16/Dynamics/ThreeAdicPolynomialBridge.lean` | proved and connected to the actual polynomial field | The parameterized physical `P dy` orbit is split into the two ellipse graphs and identified with `verticalBoundaryPdy`; vertical Fubini, inverse-branch substitution, and signed derivative cancellation identify it with the finite analytic-kernel sum and independent original-cell Jacobian integral. The integrated positive Hamiltonian clock gives the genuine-time trace. The algebraic bridge proves that `MvPolynomial.integrateAt 0` evaluates to the same canonical primitive and that the actual three-adic degree-audited polynomial density evaluates to the finite density, so all simultaneous simple roots transfer to the real polynomial first Melnikov displacement. Root build and axiom audit pass. |
| Lemma 4.1, `lem:visibility` | `Hilbert16.threeAdic_tensor_invisible`, `Hilbert16.threeAdic_tensor_diagonal_factor` | `Hilbert16/Chebyshev/ThreeAdicVisibility.lean` | proved | Zero-based finite row/frequency parametrizations realize the exact `Y_(k+1)` valuations and primitive `W_(k+1)` numerators. Their maps are injective, their images are pairwise disjoint, every `p<k` cosine vanishes, and the four unit classes modulo `12` give the exact multiplicative nonzero diagonal character. The two-coordinate invisibility and row/frequency sign separation are compiled and audited. |
| Eq. (4.4), balanced rows | `Hilbert16.threeAdic_layer_card_product` | `Hilbert16/Chebyshev/ThreeAdicVisibility.lean` | proved | The actual finite image sets have cardinalities `2*3^(r-k-1)` and `3^k`, hence product `2*3^(r-1)` for every `k<r`. |
| Eq. (4.5), row sum | `Hilbert16.threeAdicRowSet_card_sum` | `Hilbert16/Chebyshev/ThreeAdicVisibility.lean` | proved | The actual row-layer cardinalities sum in `ℕ` to `3^r-1`; `threeAdicCentralRow_numerator` identifies the omitted terminal row. |
| Lemma 5.1, `lem:borel-gauss` | `Hilbert16.borelGaussShiftIndependent` | `Hilbert16/Hypergeometric/ShiftIndependence.lean` | proved | The theorem covers arbitrary finite strictly ordered parameter families in `0<alpha<1` and every finite shift range. It uses the compiled Euler--Borel germ bridge, real-analytic continuation, arbitrary differentiated negative-axis asymptotics, and pairwise-distinct exponents; the root import and axiom audit pass. |
| Proposition 5.2, `prop:block-rank` | `Hilbert16.anisotropicAnalyticKernelRank` | `Hilbert16/Hypergeometric/AnalyticKernel.lean` | proved | The formal Cartesian-rank chain compiles in `CartesianRank.lean`. `AnalyticKernel.lean` proves absolute convergence at radius `1/4`, constructs the actual analytic germs with exactly Eq. (3.12)'s Taylor coefficients, lifts coefficient rank by power-series uniqueness, and proves a common threshold for every finite block family. Root import and axiom audit pass. W4 separately remains responsible for identifying the Chebyshev cell integral with this kernel. |
| Eq. (6.4), hierarchical weight | `Hilbert16.visible_weight_gap` | `Hilbert16/Hierarchy.lean` | proved | Coordinatewise visibility has a unique minimum and a one-power gap. |
| Eq. (6.7), exact cycle count | `Hilbert16.card_threeAdicCycleIndex` | `Hilbert16/Counting.lean`, `Hilbert16/Counting/ThreeAdicCycles.lean` | proved | `ThreeAdicCycleIndex r` is the actual dependent finite type of two layers, two genuine three-adic row parameters, and one of the block's `d_k d_l - 1` marked roots. Its cardinality is proved equal in `ℕ` to `(2*3^(r-1)*r)^2-(3^r-1)^2`; `threeAdic_count_sub_le` proves the subtraction is nontruncated. Root build and axiom audit pass. |
| Eq. (6.8), degree audit | `Hilbert16.threeAdicHierarchicalFinalVectorField_degree_le` | `Hilbert16/Degree.lean`, `Hilbert16/Degree/ThreeAdicDensity.lean` | proved | `ThreeAdicMode r` is the actual dependent family of all band pairs and frequencies. Every frequency is proved odd and at most `3^r-2`, hence every mode has `a+b≤2*3^r-4`. `threeAdicHierarchicalDensityPolynomial` inserts the paper's one-based `zeta^(k+l)` weights and arbitrary block coefficients; its total degree is at most `2*3^r-4`, so the concrete final polynomial vector field has degree at most `4*3^r-5`. Root build and axiom audit pass. |
| Lemma 6.1/6.3, `lem:finite-PP` | `Hilbert16.threeAdicPolynomialCommonSeparatedPeriodicOrbits` | `Hilbert16/Dynamics/AngularSection.lean`, `Hilbert16/Dynamics/ChebyshevAngularSection.lean`, `Hilbert16/Dynamics/ReturnTubeSection.lean`, `Hilbert16/Dynamics/MonotoneReturn.lean`, `Hilbert16/Dynamics/ReturnTubeIsolation.lean`, `Hilbert16/Dynamics/ThreeAdicSeparatedPeriodicOrbits.lean` | proved | The forward Chebyshev coordinates give a nonvanishing oriented angular tube, and a stereographic branch-cut argument forces every periodic carrier inside it to hit the positive ray. A local inverse theorem identifies that ray with the energy-parametrized Poincare section. Repeated local returns stay on the carrier by ODE uniqueness and inside a compact energy interval by the localized ray tube. The order-preserving return iterates converge to the uniform unique fixed point, so carrier uniqueness proves isolation. Independently, the explicit derivative `1+mu*partial₂D` tends to `1`, proving positivity of every selected planar multiplier and upgrading `rho≠1` to `|rho|≠1`. A finite filter intersection selects one common `mu>0` at which all actual carriers are isolated and pairwise disjoint. Root build and axiom audit pass. |
| Revised Section 6.4, explicit all-degree estimate | `Hilbert16.allDegreeLowerBound_lt_cycleLowerBound`, `Hilbert16.subsequenceToAllDegrees_explicit` | `Hilbert16/Asymptotics.lean` | proved | The lower scale and logarithm estimates bound the positive term, while `allDegreeIndex_scale_upper` bounds the square being subtracted. Together with `cycleLowerBound_eq_paper_formula`, this proves `B(d)<cycleLowerBound(allDegreeIndex d)` for `d≥31`. The transfer theorem assumes only monotonicity and the exact subsequence estimate. Full macOS build, axiom audit, and boundary checks passed on 2026-10-07. |
| Coarse positive all-degree estimate | `Hilbert16.subsequenceToAllDegrees` | `Hilbert16/Asymptotics.lean` | proved | The existing `1/1296` shifted-log estimate and `cycleLowerBound_gt_leading` remain the numerical inputs of the positive `Omega` theorem. |

## Existing audited declarations

The following declarations compile on Windows x86_64 with Lean/Mathlib `v4.33.1` and are audited in
`Hilbert16/AxiomAudit.lean`:

- `Hilbert16.tensorLayer_counting_identity`
- `Hilbert16.balanced_layer`
- `Hilbert16.rowMultiplicity_sum`
- `Hilbert16.balancedWeighted_sum`
- `Hilbert16.threeAdic_exact_count`
- `Hilbert16.threeAdic_exact_count_scaled`
- `Hilbert16.card_threeAdicCycleIndex_sum`
- `Hilbert16.threeAdic_count_sub_le`
- `Hilbert16.card_threeAdicCycleIndex`
- W11's all-degree chain: `cycleLowerBound_gt_leading`, `allDegreeIndex_bracket`,
  `allDegreeIndex_scale_lower`, `allDegreeIndex_log_lower`, `subsequenceToAllDegrees`,
  `half_log_le_shifted_log`, and `hilbert_lower_bound_asymptotic`
- Revised Corollary 1.2: `allDegreeIndex_scale_upper`,
  `allDegreeLowerBound_eq_four_mul_explicit`, `allDegreeLowerBound_lt_cycleLowerBound`,
  `subsequenceToAllDegrees_explicit`, `polynomial_hyperbolicLimitCycle_lower_bound_explicit`,
  and `polynomial_limitCycle_lower_bound_explicit` (macOS verification, 2026-10-07)
- W8's actual global-density chain: `threeAdicFrequencyValue_le_pow_sub_two`,
  `threeAdicModeFrequencyPair_sum_le`,
  `threeAdicHierarchicalDensityPolynomial_totalDegree_le`, and
  `threeAdicHierarchicalFinalVectorField_degree_le`
- `Hilbert16.visible_weight_mono`
- `Hilbert16.visible_equal_weight_iff`
- `Hilbert16.visible_weight_gap`
- W1's complete rank-to-roots chain: `exists_valuationBasis_of_separating_coefficients`,
  `exists_factored_valuationBasis_of_linearlyIndependent_series`,
  `exists_sparsePolynomial_simpleRoots`, `scaledSimpleRootFamily_of_simpleRoots`,
  `rankToRootsCombination_eq_valuationOriginalCombination`, and
  `rankToSimplePositiveRoots`
- W2's finite-poset realization chain: `hierarchicalNormalizedResponse_zero`,
  `hierarchyWeight_mul_normalized_eq_weighted`,
  `HierarchicalSimpleRootFamily.eventually_weighted_positive_simpleZeros`,
  `exists_simpleRootCombination_of_rank`, and `hierarchicalRealization`
- W5's actual finite-layer and visibility chain: `card_threeAdicRowSet`,
  `card_threeAdicFrequencySet`, `threeAdicRowIndex_exact_layer`,
  `threeAdicFrequencyValue_exact_band`, both finite-set disjointness theorems,
  `threeAdic_layer_card_product`, `threeAdicRowSet_card_sum`,
  `threeAdic_lower_band_invisible`, `modTwelveCharacter_mul`,
  `threeAdic_diagonal_cosine_factor`, `threeAdic_tensor_invisible`, and
  `threeAdic_tensor_diagonal_factor`
- B1 coefficientwise Borel identities, the Euler--Borel germ bridge, the specialized real
  hypergeometric ODE, both infinity coefficients, and the exact theorem
  `Hilbert16.Spikes.negativeAxisConnectionFormula`, as listed in `docs/B1_NEGATIVE_AXIS.md`
- B1 arbitrary differentiated asymptotics and Paper Lemma 5.1,
  `Hilbert16.formalTwoFZeroShift_linearIndependent` and
  `Hilbert16.borelGaussShiftIndependent`
- W7's formal-series part of Proposition 5.2: `formalTwoFZeroCoefficient_eq_squarePolynomial`,
  `borelCoefficientMatrix_det_ne_zero`, `transformedProductCoefficient_tendsto`,
  `anisotropicCartesianRank`, and `anisotropicAnalyticKernelTaylorRank`
- W7's convergent-germ conclusion: `analyticKernelSeries_radius_pos`,
  `analyticKernel_hasFPowerSeriesAt`, `anisotropicAnalyticKernelRank`, and
  `finiteBlockCommonAnisotropicKernelRank`
- W2/W7's concrete local hierarchy: `analyticKernel_contDiffOn_Ioo_quarter`,
  `exists_boundedSimpleRootCombination_of_rank`, `hierarchicalRealizationOn`,
  `finiteThreeAdicCommonDiagonalKernelSeriesRank`,
  `threeAdicHierarchicalBasisResponse_invisible`,
  `threeAdicHierarchicalBasisResponse_diagonal`, and
  `threeAdicHierarchicalKernelRealization`
- W4's geometric disk-moment chain: `radialEvenMoment`, `quarterEvenAngularMoment_eq`,
  `fullEvenAngularMoment_eq`, `polarEvenMonomialMoment`, and
  `cartesianEvenMonomialMoment_eq`
- W4's convergent mode-integral chain: `cos_mul_arcsin_eq_gauss`,
  `cos_mul_arcsin_hasSum`, `modeTaylorAntidiagonal_hasSum_on_disk`,
  `normalizedModeAntidiagonalIntegral`, and
  `normalizedModeDiskIntegral_eq_analyticKernel`
- W4's ellipse/cell chain: `ellipticModeIntegral_eq_inv_sqrt_mul_disk`,
  `ellipticModeIntegral_eq_area_mul_analyticKernel`, `eval_chebyshevInverseBranch`,
  `chebyshevInverseBranch_orientation_mul_deriv_pos`,
  `chebyshevCellJacobianOrientation_mul_deriv_product_pos`, and
  `integral_chebyshevCellMode_eq_weight_mul_area_mul_analyticKernel`
- W4's genuine original-cell change of variables:
  `chebyshevForwardDerivative_mul_inverseDeriv_eq_one`,
  `integral_chebyshevDensityMode_cell_eq_orientation_mul_pulledBack`, and
  `integral_chebyshevDensityMode_cell_eq_orientation_mul_weight_mul_kernel`
- W4's finite density and Green/FTC layer:
  `integral_finiteChebyshevDensity_cell_eq_kernel_sum`,
  `verticalBoundaryPdy_firstCoordinatePrimitive_eq_iteratedIntegral`, and
  `verticalBoundaryPdy_add_snd`
- W3/W4's Hamiltonian-orbit layer: `chebyshevRoot_isRoot`,
  `eval_derivative_chebyshev_at_root_ne_zero`, `chebyshevCenterHessianQuadratic_pos`,
  `chebyshevCellOrbit_energy_eq`, `chebyshevCellOrbit_add_two_pi`,
  `chebyshevCellOrbitVelocity_mul_derivatives_eq_neg_vector`, and
  `chebyshevCellOrbit_timeFactor_orientation_pos`
- W3's common period-annulus layer: `chebyshevInverseBranch_mem_cellInterval`,
  `chebyshevCellOrbit_mem_cellRectangle`, `chebyshevCellOrbitVelocity_ne_zero`,
  `chebyshevCellOrbit_range_disjoint_of_ne`, `chebyshevCellPeriodAnnulus_subset_rectangle`,
  `chebyshevCellPeriodAnnulus_disjoint_of_cell`,
  `isCompact_chebyshevCellCompactSubannulus`,
  `chebyshevCellCompactSubannulus_disjoint_of_energy`, and
  `chebyshevCellCompactSubannulus_disjoint_of_cell`
- W4's completed Green/orbit/Melnikov layer: `graphParameterizedPdy_add_eq_verticalBoundaryPdy`,
  `chebyshevCellAngularPdy_eq_verticalBoundaryPdy`,
  `integral_ellipticEnergyDisk_eq_verticalSlices`,
  `chebyshevCellAngularPdy_firstCoordinatePrimitive_finiteDensity_eq_integral`,
  `chebyshevFirstMelnikovDisplacement_finiteDensity_eq_kernel_sum`, and
  `chebyshevFirstMelnikovDisplacement_finiteDensity_eq_cellIntegral`
- W0's public carrier and coordinate layer: `phaseSpaceProdEquiv`, `PolyVectorField.eval`,
  `PolyVectorField.coordinate_totalDegree_le_degree`, `PeriodicOrbit.ext`,
  `PeriodicOrbit.carrier_nontrivial`, and `LimitCycle.ext`
- W9's simple-zero analytic closure: `ContDiffAt.localZeroContinuation_of_hasDerivAt`,
  `LocalZeroContinuation.eventually_hasDerivAt_slice_ne_zero`,
  `normalizedReturnMap_fixed_and_hyperbolic`, and
  `eventually_normalizedReturnMap_fixed_and_hyperbolic`
- W9's conditional genuine-flow return chain: `localReturnTime_of_transverseSection`,
  `chebyshevSectionFDeriv_phaseHamiltonianVector_ne_zero`,
  `C1LocalFlow.chebyshevByEnergy_hasDerivAt`,
  `ChebyshevReturnSetup.section_hasDerivAt_return`,
  `ChebyshevReturnSetup.contDiffAt_energyDisplacement`,
  `chebyshevPhaseEnergyNumerator_comp_hasDerivAt_zero`,
  `ChebyshevReturnSetup.energyDisplacement_zero_at_base`, and
  `ChebyshevReturnSetup.eventually_energyDisplacement_zero_unperturbed`
- W9's exact perturbed-energy/Melnikov chain:
  `chebyshevHamiltonianNumerator_comp_hasDerivAt_perturbed`,
  `chebyshevPhaseEnergy_comp_hasDerivAt_perturbed`,
  `ChebyshevReturnSetup.energyDisplacement_eq_mu_mul_melnikovIntegral`,
  `ChebyshevReturnSetup.energyDisplacement_eq_mu_mul_actualMelnikov`,
  `ChebyshevReturnSetup.melnikovIntegral_zero_eq_neg_unperturbedTimePdy`, and
  `ChebyshevReturnSetup.unperturbedTimeCurve_hasDerivAt`
- W9's local parameter-integral and actual-return persistence closure:
  `contDiff_parametricIntervalIntegral_const`,
  `contDiffAt_parametricIntervalIntegral_const_of_contDiffOn`,
  `contDiff_parametricIntervalIntegral`,
  `contDiffAt_parametricIntervalIntegral_of_contDiffOn`,
  `ChebyshevReturnSetup.contDiffAt_melnikovIntegral`,
  `contDiff_chebyshevEnergyProduction`,
  `ChebyshevReturnSetup.contDiffAt_actualMelnikov`,
  `ChebyshevReturnSetup.exists_admissibleReturnNeighborhood`,
  `ChebyshevReturnSetup.exists_actualMelnikovFactorizationNeighborhood`, and
  `ChebyshevReturnSetup.eventually_energyReturnMap_fixed_and_hyperbolic`
- W9's actual polynomial-field and local-existence chain:
  `phaseSpaceProdEquiv_polyVectorField_eval`,
  `finalPolyVectorField_eval_eq_perturbedPhaseVector`,
  `contDiff_mvPolynomialProdEval`, `contDiff_chebyshevPerturbedParameter`, and
  `chebyshevPolynomialPerturbation_exists_local_integralCurve`
- W9's jointly smooth local-flow constructor:
  `contDiff_chebyshevLiftedODECurveField`, `localPicardCurveBranch`,
  `chebyshevPicardResidual_eq_zero_rescale_hasDerivAt`,
  `chebyshevLifted_integralCurve_unique_on_Icc`,
  `chebyshevPicardResidual_endpoint_unique`, `contDiffOn_smoothPicardLiftedFlow`,
  `smoothPicardLiftedFlow_time_hasDerivAt`, `smoothPicardDomain_time_segment_mem`,
  `chebyshevPicardResidual_eq_zero_endpoint_fst`, and
  `chebyshevPolynomialC1LocalFlow`
- W9's finite compact-period continuation:
  `smoothPicardStepChartDomain_time_segment_mem`,
  `smoothPicardStepChart_eq_next_of_mem`,
  `smoothPicardStepIterate_sectionOrbit`,
  `exists_smoothPicard_sectionOrbit_period_chain`,
  `smoothPicardFiniteChart_eq_of_mem`,
  `contDiffOn_smoothPicardFiniteLiftedFlow`,
  `smoothPicardFiniteContinuationDomain_time_segment_mem`,
  `chebyshevPolynomialFiniteC1LocalFlow`, and
  `exists_chebyshevPolynomialFiniteC1LocalFlow_sectionPeriod`
- W4/W8/W9's actual finite-density and polynomial-primitive bridge:
  `mvPolynomialProdEval_integrateAt_eq_firstCoordinatePrimitive`,
  `chebyshevFirstMelnikovDisplacement_threeAdic_eq_modeKernelResponse`,
  `threeAdicMelnikovSimpleRootRealization`,
  `threeAdicHierarchicalDensityPolynomial_eq_chebyshevDensityPolynomial`,
  `mvPolynomialProdEval_chebyshevQPolynomial_eq_finiteChebyshevDensity`,
  `chebyshevFirstMelnikovDisplacement_threeAdicPolynomial_eq`, and
  `threeAdicPolynomialMelnikovSimpleRootRealization`
- W9's Melnikov-germ and finite-common-parameter closure:
  `contDiffOn_chebyshevHamiltonianAngularTimeDensity_joint`,
  `contDiffAt_chebyshevHamiltonianSectionPeriod`,
  `C1LocalFlow.eventually_chebyshevReturnSetupOfSectionPeriod_melnikov_eq_first`,
  `exists_chebyshevPolynomialReturnPersistence`,
  `threeAdicPolynomialReturnCertificateRealization`,
  `exists_commonPositiveParameter_of_returnCertificates`, and
  `threeAdicPolynomialCommonReturnParameter`
- W9's global periodic-carrier and finite separation closure:
  `range_periodicExtension_subset_of_scaled_Icc`,
  `ChebyshevReturnSetup.eventually_exists_periodicOrbit_of_energy_fixed`,
  `ChebyshevPolynomialReturnCertificate.eventually_periodicOrbitAt`,
  `threeAdicPolynomialCommonPeriodicOrbits`,
  `threeAdicUnperturbedCarrier_pairwise_disjoint`,
  `ChebyshevReturnSetup.eventually_normalizedReturnCurve_mem_of_open`,
  `ChebyshevPolynomialReturnCertificate.eventually_periodicOrbitAt_carrier_subset`,
  `exists_pairwiseDisjoint_open_supersets`, and
  `threeAdicPolynomialCommonSeparatedPeriodicOrbits`
- W9's carrier-uniqueness and isolation reduction:
  `isIntegralCurve_eq_of_contDiff_of_eq_zero`,
  `PeriodicOrbit.carrier_eq_of_mem_of_mem`,
  `exists_open_fixedPointNeighborhood_of_hasDerivAt_ne_one`, and
  `PeriodicOrbit.isIsolated_of_returnSection`
- W4/W9's explicit Hamiltonian-oriented one-turn bridge:
  `parameterizedPdy_comp_affine`,
  `chebyshevHamiltonianAngularOrbit_fst_hasDerivAt`,
  `chebyshevHamiltonianAngularOrbit_snd_hasDerivAt`,
  `chebyshevHamiltonianAngularVelocity_timeFactor_eq_vector`,
  `chebyshevHamiltonianAngular_timeFactor_pos`,
  `chebyshevHamiltonianAngularOrbit_two_pi_eq_zero`,
  `chebyshevHamiltonianAngularOrbit_energy_eq`,
  `chebyshevHamiltonianAngularVelocity_ne_zero`, and
  `chebyshevHamiltonianAngularPdy_eq_hamiltonianOrientedPdy`
- W4/W9's integrated Hamiltonian-time bridge:
  `chebyshevHamiltonianAngularTimeFactor_pos`,
  `strictMono_chebyshevHamiltonianAngularTime`,
  `chebyshevHamiltonianAngularTimeOrderIso`,
  `chebyshevHamiltonianPhysicalAngle_hasDerivAt`,
  `chebyshevHamiltonianPhysicalAngle_zero`,
  `chebyshevHamiltonianPhysicalAngle_period`,
  `chebyshevHamiltonianPhysicalAngle_angularTime_eq_of_mem`,
  `chebyshevHamiltonianTimeOrbit_sectionPoint`,
  both coordinate theorems for `chebyshevHamiltonianTimeOrbit`,
  `chebyshevHamiltonianTimePdy_eq_angularPdy`, and
  `chebyshevFirstMelnikovDisplacement_eq_neg_hamiltonianTimePdy`
- W9's section-based positive-return bridge:
  `chebyshevHamiltonianAngularOrbit_add_two_pi`,
  `chebyshevHamiltonianSectionPeriod_pos`,
  `chebyshevHamiltonianSectionTimeOrderIso`,
  `chebyshevHamiltonianSectionPhysicalOffset_hasDerivAt`,
  `chebyshevHamiltonianSectionTimeOrbit_zero`,
  `chebyshevHamiltonianSectionTimeOrbit_period`,
  both coordinate Hamilton-equation theorems for `chebyshevHamiltonianSectionTimeOrbit`,
  `chebyshevHamiltonianSectionPhaseOrbit_zero`,
  `chebyshevHamiltonianSectionPhaseOrbit_period`, and both transported coordinate
  Hamilton-equation theorems
- W4/W9's section-trace and ODE-uniqueness closure:
  `chebyshevHamiltonianSectionPaddedTimeOrderIso`,
  both padded-interval coordinate Hamilton-equation theorems,
  `chebyshevHamiltonianAngularVelocity_add_two_pi`,
  `chebyshevHamiltonianSectionTimePdy_eq_angularPdy`,
  `C1LocalFlow.chebyshevUnperturbed_eq_sectionTimeOrbit_on_Icc`,
  `C1LocalFlow.chebyshevUnperturbed_returns_after_sectionPeriod`,
  `C1LocalFlow.chebyshevReturnSetupOfSectionPeriod`, and
  `C1LocalFlow.chebyshevReturnSetupOfSectionPeriod_melnikovIntegral_zero_eq_neg_angularPdy`
- W8's polynomial degree core: `eval_univariateAt`,
  `MvPolynomial.pderiv_integrateAt`, `MvPolynomial.totalDegree_integrateAt_le`,
  `chebyshevDensityPolynomial_totalDegree_le`, `chebyshevQPolynomial_totalDegree_le`,
  `chebyshevPPolynomial_pderiv`, `chebyshevPPolynomial_totalDegree_le`,
  `chebyshevHamiltonianPolyVectorField_degree_le`, and `finalVectorField_degree_le`

## Current high-risk slices

| Slice | Compile target | Go criterion |
|---|---|---|
| B1 | `Hilbert16/Hypergeometric/ShiftIndependence.lean` | **Go passed:** the full arbitrary finite shifted-independence theorem is proved with no project axiom; Proposition 5.2 / W7 is also complete. |
| B2 | `Hilbert16/Spikes/ChebyshevMelnikov.lean` | **Go passed and W4 closed:** an arbitrary finite polynomial density is connected both through the explicit Hamiltonian-oriented `P dy` orbit and through a genuine original-cell two-dimensional set integral to the same convergent analytic-kernel sum, with exact DCT weights, area factor, and proved cell orientation. |
| B3 | `Hilbert16/Dynamics/ReturnTubeIsolation.lean`, `Hilbert16/Dynamics/ThreeAdicSeparatedPeriodicOrbits.lean` | **Go passed and W9 closed:** the angular positive-ray theorem, localized section tube, compact monotone-return interval, repeated-return convergence, ODE carrier uniqueness, finite common-parameter isolation, pairwise disjointness, and final `Fin (cycleLowerBound r)` limit-cycle injection all compile and pass the axiom audit. |
| W7 | `Hilbert16/Hypergeometric/AnalyticKernel.lean` | **Go passed:** Proposition 5.2 is proved for actual positive-radius analytic germs, including one common anisotropy threshold for finitely many blocks. |

These spike files may be imported by `Hilbert16.lean` only while they remain zero-`sorry` and expose
mathematically correct declarations. Passing the Go criterion moves the declarations into their
final responsibility-based modules.
