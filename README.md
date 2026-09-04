# Formalizing Markov Decision Processes in Lean

[![CI](https://github.com/formalproofs/MDPLib/actions/workflows/ci.yml/badge.svg)](https://github.com/formalproofs/MDPLib/actions/workflows/ci.yml)
[![Documentation](https://img.shields.io/badge/docs-online-blue)](https://formalproofs.github.io/MDPLib/)

**Documentation:** the [API documentation](https://formalproofs.github.io/MDPLib/docs/)
and the [companion paper](https://formalproofs.github.io/MDPLib/main.pdf) are built by CI and
published to [GitHub Pages](https://formalproofs.github.io/MDPLib/) on every push to `main`.

Verified Lean algorithms for solving tabular MDPs and proving their properties. The focus of this project is on two main goals:

1. Basic algorithms that can solve robust and risk-averse MDPs of moderate size. 

2. Proofs of correctness of algorithms and fundamental MDP properties which can be used independently to prove structural results, such as the optimality of certain policy class.


## Library Contents

The main results formalized so far. Everything is developed for *finite* sample spaces
(`[FinEnum Ω]`) over the rationals `ℚ`, so all definitions are computable and the
statements are free of measurability side conditions.

Legend: ✅ proof complete &nbsp;·&nbsp; 🚧 statement final, proof still depends on a `sorry`
(check with `#print axioms`).

### Probability foundations

[`MDPLib/Probability/Defs.lean`](MDPLib/Probability/Defs.lean),
[`MDPLib/Probability/Prelude.lean`](MDPLib/Probability/Prelude.lean)

| | Result | Lean name |
|---|---|---|
| ✅ | Finite distribution on `Ω` (nonneg weights summing to one), Dirac distribution | `Findist`, `Δ`, `dirac` |
| ✅ | A distribution forces its sample space to be nonempty | `Findist.nonempty` |
| ✅ | Random variables as bare functions `Ω → ρ`; events as `Ω → Bool` with a Boolean semiring structure | `FinRV`, `instBoolMul`, `instBoolAdd` |
| ✅ | Comparison events `X ≤ᵣ t`, `X <ᵣ t`, `X ≥ᵣ t`, `X >ᵣ t`, `X =ᵣ y` and the indicator `𝕀` | `FinRV.leq`, `FinRV.lt`, `FinRV.geq`, `FinRV.gt`, `FinRV.eq`, `indicator` |
| ✅ | Probability `ℙ[B // P]`, conditional probability `ℙ[B \| C // P]` | `probability`, `probability_cnd` |
| ✅ | Expectation `𝔼[X // P]`, conditional expectation `𝔼[X \| B // P]` and the conditional-expectation random variable `𝔼[X \|ᵣ L // P]` | `expect`, `expect_cnd`, `expect_cnd_rv` |
| ✅ | Probability as the expectation of an indicator | `prob_eq_exp_ind` |
| ✅ | Decomposition of a random variable along a discrete label `X = ∑ᵢ X · 𝕀[L = i]` | `rv_decompose`, `exp_decompose` |
| ✅ | Convexity bounds for two-point mixtures; Jensen's inequality for `\|·\|` on the uniform distribution | `lower_bound_fst`, `upper_bound_fst`, `jensen_abs_uniform` |

### Probability: basic properties

[`MDPLib/Probability/Basic.lean`](MDPLib/Probability/Basic.lean)

| | Result | Lean name |
|---|---|---|
| ✅ | `ℙ` takes values in `[0,1]` | `Findist.ge_zero`, `Findist.le_one`, `Findist.in_prob` |
| ✅ | Linearity, homogeneity and monotonicity of expectation | `exp_additive`, `exp_homogenous`, `exp_monotone` |
| ✅ | Complement rules `ℙ[B] + ℙ[¬B] = 1`, and the `≤`/`>` and `<`/`≥` pairs | `prob_compl_sums_to_one`, `prob_le_compl_gt`, `prob_lt_compl_ge` |
| ✅ | Monotonicity of `ℙ[X ≤ t]` in both `X` and `t` (and the antitone versions) | `prob_le_monotone`, `prob_lt_monotone`, `prob_ge_antitone`, `prob_gt_antitone` |
| ✅ | Behaviour of events and probabilities under monotone / strictly monotone / antitone transformations of `X` | `rv_f_le_strictmono`, `prob_f_le_strictmono`, `prob_f_ge_strictmono`, … |
| ✅ | Cash (translation) invariance and negation duality of the comparison events | `prob_le_cashinvar`, `prob_le_neg_ge` |
| ✅ | CDF `cdf P X t = ℙ[X ≤ t]`; it is nondecreasing in `t` and antitone in `X` | `cdf`, `cdf_nondecreasing`, `cdf_monotone_xy` |
| ✅ | Law of the unconscious statistician | `LOTUS` |
| ✅ | Tower property (law of total expectation) | `law_total_exp` |
| ✅ | Law of total probability | `law_of_total_probs` |
| ✅ | Expectation equals the sum over the (finite) image of `X` | `expect_def_correct`, `sum_eq_sum_image` |
| ✅ | Duplicate-free list of the values of a random variable, with index/value inverses | `FinRV.imageList`, `FinRV.imageIdxOf`, `finrv_image_inverse`, `finrv_image_nodup` |
| ✅ | Invariance of probability and expectation under a permutation of the sample space | `Findist.perm`, `prob_eq_perm`, `exp_eq_perm` |
| 🚧 | A `≤` event can be replaced by a strict `<` event at a larger threshold | `prob_le_step_lt_max` |

### Probability: matrices and Markov reward processes

[`MDPLib/Probability/Matrix.lean`](MDPLib/Probability/Matrix.lean)

| | Result | Lean name |
|---|---|---|
| ✅ | Row-stochastic transition matrix | `ProbabilityMatrix` |
| ✅ | A distribution pushed through a transition matrix is again a distribution | `dist_prob_product_nneg`, `dist_prob_product_sum` |
| ✅ | Discounted Markov reward process and its Bellman backup `𝔹[v // Proc] = r + γ · P v` | `DMRP`, `bellman_backup` |

### Quantiles

[`MDPLib/Probability/Quantile.lean`](MDPLib/Probability/Quantile.lean)

| | Result | Lean name |
|---|---|---|
| ✅ | Quantile set `{q \| ℙ[X ≤ q] ≥ α ∧ ℙ[X ≥ q] ≥ 1-α}` and its one-sided (lower) relaxation | `Quantile`, `QuantileLower`, `IsQuantile`, `IsQuantileLower` |
| ✅ | Equivalent characterizations of membership, including the strict form `ℙ[X < q] ≤ α` | `qset_def`, `qsetlower_def_lt`, `qset_of_cond_lt` |
| ✅ | Every quantile is a lower quantile | `quantile_subset_quantilelower` |
| ✅ | Reflection: `q` is an `α`-quantile of `X` iff `-q` is a `(1-α)`-quantile of `-X` | `quantile_neg` |
| ✅ | Quantiles under monotone maps; equivalence for strictly monotone maps | `quantile_f_monotone`, `quantile_f_strictmono`, `quantilelower_f_strictmono` |
| ✅ | Lower quantiles of `X ≤ Y` are cofinal — the basis for monotonicity of VaR | `quantile_le_monotone` |
| ✅ | Cash invariance of the lower-quantile set: `QuantileLower(X + c) = QuantileLower(X) + c` | `quantilelower_cash_image` |
| 🚧 | The image `f '' Quantile(X)` is cofinal/coinitial in `Quantile(f∘X)` for monotone `f` | `quantile_f_cofinal`, `quantile_f_coinitial` |

### Value at Risk

[`MDPLib/Risk/VaR.lean`](MDPLib/Risk/VaR.lean)

| | Result | Lean name |
|---|---|---|
| ✅ | Risk level `0 ≤ α < 1` | `IsRiskLevel`, `RiskLevel` |
| ✅ | Non-constructive VaR: the greatest lower quantile (equivalently, the greatest quantile) | `IsVaR`, `IsVaR_Q` |
| ✅ | Characterization `IsVaR v ↔ ℙ[X < v] ≤ α < ℙ[X ≤ v]` | `var_prob_cond` |
| ✅ | Computable VaR `VaR[X // P, α]` as a max over the finite candidate set, which is nonempty | `FinVaR`, `FinVaRSet`, `FinVarSet_nonempty` |
| ✅ | VaR is monotone: `X ≤ Y` implies `VaR[X] ≤ VaR[Y]` | `var_monotone` |
| 🚧 | **Correctness of the computable VaR:** `IsVaR P X α (VaR[X // P, α])` | `finvar_correct` |
| 🚧 | The two definitions (greatest quantile / greatest lower quantile) agree | `varq_eq_var` |
| 🚧 | The quantile set is nonempty | `quantile_nonempty` |
| 🚧 | Translation (cash) invariance: `VaR[X + c] = VaR[X] + c` | `var_translation_invariant`, `isvar_translation_invariant` |
| 🚧 | Strictly monotone transformations: `VaR[f∘X] = f(VaR[X])` | `var_f_strictmono`, `isvar_f_strictmono` |
| 🚧 | Positive homogeneity: `VaR[c·X] = c·VaR[X]` for `c > 0` | `var_positive_homog` |

The 🚧 entries above are all complete modulo the single missing lemma
`prob_le_step_lt_max`.

[`Main.lean`](Main.lean) contains an executable that reads distributions from a JSON
file, computes VaR with `computeVaR`, and checks it against reference values
(see [`test_var.json`](test_var.json)).

### MDPs and histories

[`MDPLib/MDP/Histories.lean`](MDPLib/MDP/Histories.lean)

| | Result | Lean name |
|---|---|---|
| ✅ | Tabular MDP with finite states, actions, transitions and rewards | `MDP` |
| ✅ | Histories `s₀ a₀ s₁ …`, their length, last state, prefixes, and the length-indexed subtype | `Hist`, `Hist.length`, `Hist.last`, `Hist.prefix`, `MDP.HistT` |
| ✅ | Counting histories: `\|H_t\| = S · (S·A)^t` | `MDP.numhist` |
| ✅ | Embeddings `Hist × A × S ↪ Hist` and `S ↪ Hist` | `emb_tuple2hist`, `state2hist_emb` |
| ✅ | The horizon-`t` history sets are exactly the histories of length `t`; `Fintype (M.HistT t)` | `hist_horiz_complete`, `hist_horiz_exact`, `MDP.HistoriesHorizonT` |
| 🚧 | Explicit bijection between histories of length `t` and `Fin (numhist t)` | `MDP.hist_to_idx`, `MDP.idx_to_hist`, `hist_idx_LeftInverse`, `hist_idx_RightInverse` |


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



