# Lemmas 2.1--8.1: formalization map

`SevenPrime.lean` contains theorem declarations corresponding to every numbered
lemma from 2.1 through 8.1 in the manuscript.  It deliberately formalizes the
analytic reductions, not Proposition 9.1's exhaustive certificate.

`SevenPrime/ConcreteCovering.lean` defines concrete residue classes by equality
in `ZMod`, records the actual finite LCM, implements divisor completion, proves
the exact cardinality `p^(e-f)` of a level-`f` slice in `ZMod (p^e)`, and uses
`ZMod.prodEquivPi` for the finite CRT survivor coordinates.

`SevenPrime/AxisResidual.lean` represents every axis class `3^g p^f` by its
two CRT residues, groups its concrete `p`-slices by 3-adic node, performs
ancestor disjointization by set difference, and defines the rooted-tree
quantities `R_T`, `L₀`, `L₁`, `L₂`, `L₃`, and `H`.

`SevenPrime/RootedSymmetry.lean` explicitly represents rooted-tree
automorphisms by compatible permutations of leaves, nodes, and branches.  It
proves preservation of the relaxation domain and invariance of the complete
Stage-I/Stage-II functional under their action.

The paper uses several domain-specific constructions (covering systems, CRT
coordinates, disjointized axis masses, and the corrected relaxation).  They are
represented by explicit predicates and real-valued finite families.  In
particular, assumptions named `hdisjointize` and `hclip` are the
precise interfaces where the paper supplies the corresponding measure
argument.  No theorem assumes its own conclusion, and the file contains no
`axiom`, `sorry`, or `admit`.

## Coverage

| Paper item | Lean declaration | Status |
|---|---|---|
| Lemma 2.1 | `lemma_2_1_concrete_divisor_completion` | concrete `ZMod` classes; completion preserves coverage, distinctness and LCM and supplies every nontrivial divisor |
| Lemmas 3.1--3.2 | `lemma_3_1_pure_tower_survivor_size`, `primePowerSlice_ncard`, `lemma_3_1_concrete_pure_tower_survivor`, `lemma_3_2_concrete_crt_survivor` | geometric sum/budget, exact concrete slice cardinalities and union-bound survivor count, and the exact survivor under `ZMod.prodEquivPi` CRT coordinates |
| Lemmas 4.1--4.2 | `threePow_dvd_paddedThreePow`, `concreteLeafMass_le_two_div_twentySeven`, `lemma_4_1_concrete_padded_leaf_bound`, `lemma_4_1_profile_polytope`, `lemma_4_2_vertices_of_K3` | concrete exponent padding by `max e 3`, the exact mod-27 slice bound for a 3-adic survivor, profile inequalities, and the full extreme-point multiset `0^4, 1^1, 2^13`, proved by balanced perturbation and finite coordinate counting |
| Lemmas 5.1--5.2 | `lemma_5_1_concrete_levelwise_axis_budget`, `lemma_5_1_concrete_axis_budget_beta`, `finite_crt_product_fraction`, `lemma_5_2_finite_crt_skeleton_complement` | concrete axis classes, node unions and ancestor disjointization; exact finite budget `< β_p`; and an exact finite CRT-cardinality proof of the product formula |
| Lemma 6.1 | `exponentVectorCapacity_sum_le_supportBudget`, `threeTailCapacity_lt_one_div_twentySeven`, `lemma_6_1_fully_concrete_capacity_bounds` | dependent exponent-vector factorization, the concrete finite `g ≥ 4` tail, and all five rooted-tree clipped bounds without external total-budget hypotheses |
| Lemmas 7.1--7.4 | `lemma_7_1_concrete_profile_convexity`, `lemma_7_1_concrete_axis_block_convexity`, `lemma_7_2_vertex_reduction_two_blocks`, `lemma_7_3_concrete_rooted_tree_invariance`, `lemma_7_3_rooted_tree_orbit_count`, `lemma_7_4_concrete_singleton_promotion_cost` | separate convexity of the complete clipped functional in the profile and every concrete prime-axis block; blockwise vertex replacement; preservation of the feasible domain and complete objective under explicit rooted-tree automorphisms; exactly 28 canonical orbit keys; and the concrete singleton promotion-cost inequality |
| Lemma 8.1 | `clippedStageFunctional`, `concreteRelaxationDomain`, `lemma_8_1_concrete_budget_monotonicity` | the complete Stage-I/Stage-II finite sums and supremum monotonicity on their concrete profile/axis domain |

This completes the analytic formalization of the manuscript's numbered Lemmas
2.1--8.1, including the two previously open connections: convexity in each
concrete axis block and rooted-tree invariance of both the feasible domain and
the complete functional.  Proposition 9.1's exhaustive finite certificate
remains deliberately outside this scope, as stated above.

Build with:

```powershell
$env:GIT_CONFIG_COUNT='1'
$env:GIT_CONFIG_KEY_0='safe.directory'
$env:GIT_CONFIG_VALUE_0='*'
lake build
```
