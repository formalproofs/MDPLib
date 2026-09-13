# Formalizing Markov Decision Processes in Lean

[![CI](https://github.com/formalproofs/MDPLib/actions/workflows/ci.yml/badge.svg)](https://github.com/formalproofs/MDPLib/actions/workflows/ci.yml)
[![Documentation](https://img.shields.io/badge/docs-online-blue)](https://formalproofs.github.io/MDPLib/docs/)

**Documentation:** the [API documentation](https://formalproofs.github.io/MDPLib/docs/)
and the [companion paper](https://formalproofs.github.io/MDPLib/main.pdf) are built by CI and
published to [GitHub Pages](https://formalproofs.github.io/MDPLib/) on every push to `main`.

Verified Lean algorithms for solving tabular MDPs and proving their properties. The focus of this project is on two main goals:

1. Basic algorithms that can solve robust and risk-averse MDPs of moderate size. 

2. Proofs of correctness of algorithms and fundamental MDP properties which can be used independently to prove structural results, such as the optimality of certain policy class.


## Library Contents

The main results formalized so far. Everything is developed for *finite* sample spaces
(`[FinEnum Ω]`) over an arbitrary linear ordered field `R`
(`[Field R] [LinearOrder R] [IsStrictOrderedRing R] [CharZero R] [Archimedean R]`), so the
statements are free of measurability side conditions. Instantiate at `ℚ` — as
[`MDPLibTest.lean`](MDPLibTest.lean) does — and every definition is computable and executable;
instantiate at `ℝ` for the standard theory, where the definitions remain well-formed but
`noncomputable` (`Real.instField` and the classical `DecidableLE ℝ` are noncomputable, so
`VaR[X // P, α]` cannot be `#eval`'d over `ℝ`).


### Relationship to Mathlib's measure theory-based probability

Mathlib's measure-theoretic probability (`Measure`, `PMF`, `∫`, `∫⁻`) is **not** used, and
cannot be: it is uniformly `noncomputable` and valued in `ℝ≥0∞` or an `ℝ`-normed space, so it
neither evaluates at `ℚ` nor says anything about a general scalar `R`. Mathlib also has no
quantiles, VaR or CVaR at all. What *is* reused is the scalar-generic algebraic API —
`Finset.centerMass`, which is weighted expectation over exactly this library's class stack, and
the order/convexity results built on it. See the audit note at the top of
[`MDPLib/Probability/Defs.lean`](MDPLib/Probability/Defs.lean) for the details and citations.


Legend: ✅ proof complete &nbsp;·&nbsp; 🚧 statement final, proof still depends on a `sorry`
(check with `#print axioms`).

### Probability foundations

[`MDPLib/Probability/Defs.lean`](MDPLib/Probability/Defs.lean),
[`MDPLib/Probability/Prelude.lean`](MDPLib/Probability/Prelude.lean)

| | Result | Lean name |
|---|---|---|
| ✅ | Finite distribution on `Ω` (nonneg weights summing to one), Dirac distribution | [`Findist`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#Findist), [`Findist.Δ`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#Findist.Δ), [`Findist.dirac`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#Findist.dirac) |
| ✅ | A distribution forces its sample space to be nonempty | [`Findist.nonempty`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#Findist.nonempty) |
| ✅ | Random variables as bare functions `Ω → ρ`; events as `Ω → Bool` with a Boolean semiring structure | [`FinRV`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#FinRV), [`FinRV.instMulBool`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#FinRV.instMulBool), [`FinRV.instAddBool`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#FinRV.instAddBool) |
| ✅ | Comparison events `X ≤ᵣ t`, `X <ᵣ t`, `X ≥ᵣ t`, `X >ᵣ t`, `X =ᵣ y` and the indicator `𝕀` | [`FinRV.leq`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#FinRV.leq), [`FinRV.lt`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#FinRV.lt), [`FinRV.geq`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#FinRV.geq), [`FinRV.gt`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#FinRV.gt), [`FinRV.eq`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#FinRV.eq), [`FinRV.indicator`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#FinRV.indicator) |
| ✅ | Probability `ℙ[B // P]`, conditional probability `ℙ[B \| C // P]` | [`Findist.probability`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#Findist.probability), [`Findist.probabilityCond`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#Findist.probabilityCond) |
| ✅ | Expectation `𝔼[X // P]`, conditional expectation `𝔼[X \| B // P]` and the conditional-expectation random variable `𝔼[X \|ᵣ L // P]` | [`Findist.expect`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#Findist.expect), [`Findist.expectCond`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#Findist.expectCond), [`Findist.expectCondRV`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#Findist.expectCondRV) |
| ✅ | Probability as the expectation of an indicator | [`Findist.probability_eq_expect_indicator`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#Findist.probability_eq_expect_indicator) |
| ✅ | Decomposition of a random variable along a discrete label `X = ∑ᵢ X · 𝕀[L = i]` | [`FinRV.eq_sum_mul_indicatorEq`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#FinRV.eq_sum_mul_indicatorEq), [`Findist.expect_eq_sum_mul_indicatorEq`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#Findist.expect_eq_sum_mul_indicatorEq) |
| ✅ | Convexity bounds for two-point mixtures; Jensen's inequality for `\|·\|` on the uniform distribution | [`IsProb.self_le_combo_of_le`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Prelude.html#IsProb.self_le_combo_of_le), [`IsProb.combo_le_self_of_ge`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Prelude.html#IsProb.combo_le_self_of_ge), [`Matrix.abs_dotProduct_le_dotProduct_abs_uniform`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Prelude.html#Matrix.abs_dotProduct_le_dotProduct_abs_uniform) |

### Expectation as a convex combination

[`MDPLib/Probability/Convexity.lean`](MDPLib/Probability/Convexity.lean)

| | Result | Lean name |
|---|---|---|
| ✅ | `𝔼[X // P]` is Mathlib's `Finset.centerMass` at weights summing to one | [`Findist.expect_eq_centerMass`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Convexity.html#Findist.expect_eq_centerMass) |
| ✅ | `min X ≤ 𝔼[X] ≤ max X` | [`Findist.expect_ge_min`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Convexity.html#Findist.expect_ge_min), [`Findist.expect_le_max`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Convexity.html#Findist.expect_le_max) |
| ✅ | Jensen's inequality for an arbitrary convex / concave function | [`Findist.expect_convexOn_le`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Convexity.html#Findist.expect_convexOn_le), [`Findist.expect_concaveOn_ge`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Convexity.html#Findist.expect_concaveOn_ge) |

### Bridge to Mathlib's standard simplex

[`MDPLib/Probability/StdSimplex.lean`](MDPLib/Probability/StdSimplex.lean)

| | Result | Lean name |
|---|---|---|
| ✅ | A `Findist` as a point of `Convexity.StdSimplex` (`noncomputable`; proof-layer only) | [`Findist.toStdSimplex`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/StdSimplex.html#Findist.toStdSimplex) |
| ✅ | Mathlib's indexed convex combination is this library's expectation | [`Findist.toStdSimplex_iConvexComb`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/StdSimplex.html#Findist.toStdSimplex_iConvexComb) |
| ✅ | `Findist.dirac` is `StdSimplex.single`; the bridge is injective | [`Findist.toStdSimplex_dirac`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/StdSimplex.html#Findist.toStdSimplex_dirac), [`Findist.toStdSimplex_injective`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/StdSimplex.html#Findist.toStdSimplex_injective) |

### Probability: basic properties

[`MDPLib/Probability/Basic.lean`](MDPLib/Probability/Basic.lean)

| | Result | Lean name |
|---|---|---|
| ✅ | `ℙ` takes values in `[0,1]` | [`Findist.probability_nonneg`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.probability_nonneg), [`Findist.probability_le_one`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.probability_le_one), [`Findist.isProb_probability`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.isProb_probability) |
| ✅ | Linearity, homogeneity and monotonicity of expectation | [`Findist.expect_sum`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#Findist.expect_sum), [`Findist.expect_smul`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#Findist.expect_smul), [`Findist.expect_mono`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#Findist.expect_mono) |
| ✅ | Complement rules `ℙ[B] + ℙ[¬B] = 1`, and the `≤`/`>` and `<`/`≥` pairs | [`Findist.probability_add_probability_not`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.probability_add_probability_not), [`Findist.probability_leq_add_probability_gt`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.probability_leq_add_probability_gt), [`Findist.probability_lt_add_probability_geq`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.probability_lt_add_probability_geq) |
| ✅ | Monotonicity of `ℙ[X ≤ t]` in both `X` and `t` (and the antitone versions) | [`Findist.probability_leq_mono`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.probability_leq_mono), [`Findist.probability_lt_mono`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.probability_lt_mono), [`Findist.probability_geq_anti`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.probability_geq_anti), [`Findist.probability_gt_anti`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.probability_gt_anti) |
| ✅ | Behaviour of events and probabilities under monotone / strictly monotone / antitone transformations of `X` | [`FinRV.leq_eq_comp_leq_of_strictMono`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#FinRV.leq_eq_comp_leq_of_strictMono), [`Findist.probability_leq_eq_probability_comp_leq_of_strictMono`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.probability_leq_eq_probability_comp_leq_of_strictMono), [`Findist.probability_geq_eq_probability_comp_geq_of_strictMono`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.probability_geq_eq_probability_comp_geq_of_strictMono), … |
| ✅ | Cash (translation) invariance and negation duality of the comparison events | [`Findist.probability_leq_add_const`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.probability_leq_add_const), [`Findist.probability_leq_eq_neg_geq_neg`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.probability_leq_eq_neg_geq_neg) |
| ✅ | CDF `cdf P X t = ℙ[X ≤ t]`; it is nondecreasing in `t` and antitone in `X` | [`Findist.cdf`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Defs.html#Findist.cdf), [`Findist.cdf_mono`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.cdf_mono), [`Findist.cdf_anti_of_le`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.cdf_anti_of_le) |
| ✅ | Law of the unconscious statistician | [`Findist.expect_comp_eq_sum`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.expect_comp_eq_sum) |
| ✅ | Tower property (law of total expectation) | [`Findist.expect_expectCondRV`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.expect_expectCondRV) |
| ✅ | Law of total probability | [`Findist.probability_eq_sum`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.probability_eq_sum) |
| ✅ | Expectation equals the sum over the (finite) image of `X` | [`Findist.expect_eq_sum_probability_mul`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.expect_eq_sum_probability_mul), [`FinRV.sum_image_univ_eq_sum_fin`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#FinRV.sum_image_univ_eq_sum_fin) |
| ✅ | Duplicate-free list of the values of a random variable, with index/value inverses | [`FinRV.imageList`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#FinRV.imageList), [`FinRV.imageIdxOf`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#FinRV.imageIdxOf), [`FinRV.getElem_imageIdxOf`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#FinRV.getElem_imageIdxOf), [`FinRV.imageList_nodup`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#FinRV.imageList_nodup) |
| ✅ | Invariance of probability and expectation under a permutation of the sample space | [`Findist.comp`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.comp), [`Findist.probability_comp_perm`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.probability_comp_perm), [`Findist.expect_comp_perm`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.expect_comp_perm) |
| 🚧 | A `≤` event can be replaced by a strict `<` event at a larger threshold | [`Findist.exists_probability_leq_eq_probability_lt_of_lt_max`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Basic.html#Findist.exists_probability_leq_eq_probability_lt_of_lt_max) |

### Probability: matrices and Markov reward processes

[`MDPLib/Probability/Matrix.lean`](MDPLib/Probability/Matrix.lean)

| | Result | Lean name |
|---|---|---|
| ✅ | Row-stochastic transition matrix | [`Matrix.ProbabilityMatrix`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Matrix.html#Matrix.ProbabilityMatrix) |
| ✅ | A distribution pushed through a transition matrix is again a distribution | [`Matrix.nonneg_vecMul`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Matrix.html#Matrix.nonneg_vecMul), [`Matrix.vecMul_dotProduct_one`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Matrix.html#Matrix.vecMul_dotProduct_one) |
| ✅ | Discounted Markov reward process and its Bellman backup `𝔹[v // Proc] = r + γ · P v` | [`Matrix.DiscountedMRP`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Matrix.html#Matrix.DiscountedMRP), [`Matrix.bellmanBackup`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Matrix.html#Matrix.bellmanBackup) |

### Quantiles

[`MDPLib/Probability/Quantile.lean`](MDPLib/Probability/Quantile.lean)

| | Result | Lean name |
|---|---|---|
| ✅ | Quantile set `{q \| ℙ[X ≤ q] ≥ α ∧ ℙ[X ≥ q] ≥ 1-α}` and its one-sided (lower) relaxation | [`Statistic.quantile`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Quantile.html#Statistic.quantile), [`Statistic.quantileLower`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Quantile.html#Statistic.quantileLower), [`Statistic.IsQuantile`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Quantile.html#Statistic.IsQuantile), [`Statistic.IsQuantileLower`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Quantile.html#Statistic.IsQuantileLower) |
| ✅ | Equivalent characterizations of membership, including the strict form `ℙ[X < q] ≤ α` | [`Statistic.mem_quantile_iff`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Quantile.html#Statistic.mem_quantile_iff), [`Statistic.mem_quantileLower_iff_probability_lt`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Quantile.html#Statistic.mem_quantileLower_iff_probability_lt), [`Statistic.mem_quantile_of_probability_lt`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Quantile.html#Statistic.mem_quantile_of_probability_lt) |
| ✅ | Every quantile is a lower quantile | [`Statistic.quantile_subset_quantileLower`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Quantile.html#Statistic.quantile_subset_quantileLower) |
| ✅ | Reflection: `q` is an `α`-quantile of `X` iff `-q` is a `(1-α)`-quantile of `-X` | [`Statistic.mem_quantile_neg_iff`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Quantile.html#Statistic.mem_quantile_neg_iff) |
| ✅ | Quantiles under monotone maps; equivalence for strictly monotone maps | [`Statistic.mem_quantile_comp_of_monotone`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Quantile.html#Statistic.mem_quantile_comp_of_monotone), [`Statistic.mem_quantile_comp_iff_of_strictMono`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Quantile.html#Statistic.mem_quantile_comp_iff_of_strictMono), [`Statistic.mem_quantileLower_comp_iff_of_strictMono`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Quantile.html#Statistic.mem_quantileLower_comp_iff_of_strictMono) |
| ✅ | Lower quantiles of `X ≤ Y` are cofinal — the basis for monotonicity of VaR | [`Statistic.isCofinalFor_quantileLower_of_le`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Quantile.html#Statistic.isCofinalFor_quantileLower_of_le) |
| ✅ | Cash invariance of the lower-quantile set: `QuantileLower(X + c) = QuantileLower(X) + c` | [`Statistic.quantileLower_add_const_eq_image`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Quantile.html#Statistic.quantileLower_add_const_eq_image) |
| 🚧 | The image `f '' quantile(X)` is cofinal/coinitial in `quantile(f∘X)` for monotone `f` | [`Statistic.isCofinalFor_quantile_comp_image_of_monotone`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Quantile.html#Statistic.isCofinalFor_quantile_comp_image_of_monotone), [`Statistic.isCoinitialFor_quantile_comp_image_of_monotone`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Probability/Quantile.html#Statistic.isCoinitialFor_quantile_comp_image_of_monotone) |

### Value at Risk

[`MDPLib/Risk/VaR.lean`](MDPLib/Risk/VaR.lean)

| | Result | Lean name |
|---|---|---|
| ✅ | Risk level `0 ≤ α < 1` | [`Risk.IsRiskLevel`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.IsRiskLevel), [`Risk.RiskLevel`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.RiskLevel) |
| ✅ | Non-constructive VaR: the greatest lower quantile (equivalently, the greatest quantile) | [`Risk.IsVaR`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.IsVaR), [`Risk.IsVaRQuantile`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.IsVaRQuantile) |
| ✅ | Characterization `IsVaR v ↔ ℙ[X < v] ≤ α < ℙ[X ≤ v]` | [`Risk.isVaR_iff`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.isVaR_iff) |
| ✅ | Computable VaR `VaR[X // P, α]` as a max over the finite candidate set, which is nonempty | [`Risk.finVaR`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.finVaR), [`Risk.finVaRSet`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.finVaRSet), [`Risk.finVaRSet_nonempty`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.finVaRSet_nonempty) |
| ✅ | VaR is monotone: `X ≤ Y` implies `VaR[X] ≤ VaR[Y]` | [`Risk.IsVaR.le_of_le`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.IsVaR.le_of_le) |
| 🚧 | **Correctness of the computable VaR:** `IsVaR P X α (VaR[X // P, α])` | [`Risk.isVaR_finVaR`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.isVaR_finVaR) |
| 🚧 | The two definitions (greatest quantile / greatest lower quantile) agree | [`Risk.isVaRQuantile_iff_isVaR`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.isVaRQuantile_iff_isVaR) |
| 🚧 | The quantile set is nonempty | [`Risk.quantile_nonempty`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.quantile_nonempty) |
| ✅ | Translation (cash) invariance for the `Risk.IsVaR` predicate | [`Risk.IsVaR.add_const`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.IsVaR.add_const) |
| 🚧 | … and for the computable VaR: `VaR[X + c] = VaR[X] + c` | [`Risk.finVaR_add_const`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.finVaR_add_const) |
| ✅ | Strictly monotone transformations for the `Risk.IsVaR` predicate | [`Risk.IsVaR.comp_of_strictMono`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.IsVaR.comp_of_strictMono) |
| 🚧 | … and for the computable VaR: `VaR[f∘X] = f(VaR[X])` | [`Risk.finVaR_comp_of_strictMono`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.finVaR_comp_of_strictMono) |
| 🚧 | Positive homogeneity: `VaR[c·X] = c·VaR[X]` for `c > 0` | [`Risk.finVaR_const_mul`](https://formalproofs.github.io/MDPLib/docs/MDPLib/Risk/VaR.html#Risk.finVaR_const_mul) |

The 🚧 entries above are all complete modulo the single missing lemma
`Findist.exists_probability_leq_eq_probability_lt_of_lt_max`.

[`Main.lean`](Main.lean) contains an executable that reads distributions from a JSON
file, computes VaR with `computeVaR`, and checks it against reference values
(see [`test_var.json`](test_var.json)). `computeVaR` is standalone IO glue over
`Array ℚ` rather than the verified `Risk.finVaR`; it is
[`MDPLibTest.lean`](MDPLibTest.lean) that instantiates the library itself at `ℚ`.

### MDPs and histories

[`MDPLib/MDP/Histories.lean`](MDPLib/MDP/Histories.lean)

|    | Result                                                                                      | Lean name                                                          |
|----|---------------------------------------------------------------------------------------------|--------------------------------------------------------------------|
| ✅ | Tabular MDP with finite states, actions, transitions and rewards                            | [`MDP`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#MDP)                                                              |
| ✅ | Histories `s₀ a₀ s₁ …`, their length, last state, prefixes, and the length-indexed subtype  | [`Hist`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#Hist), [`Hist.length`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#Hist.length), [`Hist.last`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#Hist.last), [`Hist.prefix`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#Hist.prefix), [`MDP.HistOfLength`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#MDP.HistOfLength)     |
| ✅ | The count `S · (S·A)^t` and the explicit index maps `Fin (numHist t) ↔ HistOfLength t`             | [`MDP.numHist`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#MDP.numHist), [`MDP.idxToHist`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#MDP.idxToHist), [`MDP.histToIdx`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#MDP.histToIdx)                |
| 🚧 | … that those maps are mutually inverse, i.e. that the count is the cardinality              | [`leftInverse_idxToHist_histToIdx`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#leftInverse_idxToHist_histToIdx), [`rightInverse_idxToHist_histToIdx`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#rightInverse_idxToHist_histToIdx), [`exists_init_of_length_eq_zero`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#exists_init_of_length_eq_zero), [`exists_foll_of_length_eq_succ`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#exists_foll_of_length_eq_succ) |
| ✅ | Embeddings `Hist × A × S ↪ Hist` and `S ↪ Hist`                                             | [`tupleToHistEmbedding`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#tupleToHistEmbedding), [`stateToHistEmbedding`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#stateToHistEmbedding)                                 |
| ✅ | The horizon-`t` history sets are exactly the histories of length `t`; `Fintype (M.HistOfLength t)` | [`mem_historiesHorizon`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#mem_historiesHorizon), [`length_eq_of_mem_historiesHorizon`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#length_eq_of_mem_historiesHorizon), [`MDP.historiesHorizonT`](https://formalproofs.github.io/MDPLib/docs/MDPLib/MDP/Histories.html#MDP.historiesHorizonT) |

The `ℋ h t` family (histories extending `h` by `t` steps) is defined but its length
lemma `length_of_mem_histories` is still 🚧.

[`MDPLib/Risk/CVaR.lean`](MDPLib/Risk/CVaR.lean) is an empty stub; it carries notes on which
Mathlib pieces are and are not available for Conditional Value at Risk.


## Building and testing

```bash
lake build MDPLib            # the library
lake -R build MDPLib:docs    # the API documentation
lake build mdplib            # the binary file
lake build MDPLibTest        # tests the elaborationa dn 
```


On linux, you can use build and test the binary file as follows:
```bash
./test.sh                    # computability + regression tests, interpreted and compiled
```

CI (`.github/workflows/ci.yml`) runs the library build, that script, the docs and the paper on
every pull request, and deploys to GitHub Pages on `main`.

## Lean Resources


### Most useful

* Overview of tactics: <https://github.com/madvorak/lean4-tactics>
* Comprehensive list of tactics: <https://seasawher.github.io/mathlib4-help/tactics/>
* Loogle: <https://loogle.lean-lang.org/>
* Moogle: <https://www.moogle.ai/> 

### Others

* Blueprint: <https://github.com/PatrickMassot/leanblueprint>
* Lean packages and extensions: <https://reservoir.lean-lang.org/>
* Notations: <https://github.com/leanprover-community/lean4-mode/blob/master/data/abbreviations.json>
* Resource for Probability: <https://korivernon.com/documents/MathematicalStatisticsandDataAnalysis3ed.pdf>



