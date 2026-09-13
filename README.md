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

Because the library is finite throughout — every sum is a `Finset.sum`/`⬝ᵥ` and every
supremum a `Finset.max'`/`IsGreatest` — nothing here depends on completeness, so `ℚ` is a
genuine instance rather than an approximation. Future results that *do* need completeness
(Banach fixed points for `bellman_backup`, suprema over infinite action sets) should live in
separate files carrying their own stronger assumptions, so that they do not silently make
the whole development `ℝ`-only.

### Relationship to Mathlib

Mathlib's measure-theoretic probability (`Measure`, `PMF`, `∫`, `∫⁻`) is **not** used, and
cannot be: it is uniformly `noncomputable` and valued in `ℝ≥0∞` or an `ℝ`-normed space, so it
neither evaluates at `ℚ` nor says anything about a general scalar `R`. Mathlib also has no
quantiles, VaR or CVaR at all. What *is* reused is the scalar-generic algebraic API —
`Finset.centerMass`, which is weighted expectation over exactly this library's class stack, and
the order/convexity results built on it. See the audit note at the top of
[`MDPLib/Probability/Defs.lean`](MDPLib/Probability/Defs.lean) for the details and citations.

Mathlib's `Convexity.StdSimplex` is the same object as `Findist`, but `Finsupp`-backed and
therefore noncomputable as well (`Finsupp` is declared "a `noncomputable theory` … uses
classical logic throughout"), so it is not adopted either. Instead
[`MDPLib/Probability/StdSimplex.lean`](MDPLib/Probability/StdSimplex.lean) provides a one-way,
proof-layer bridge, which makes Mathlib's convexity machinery available while the computable
core is untouched.


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
| ✅ | Convexity bounds for two-point mixtures; Jensen's inequality for `\|·\|` on the uniform distribution | `Prob.lower_bound_fst`, `Prob.upper_bound_fst`, `jensen_abs_uniform` |

### Expectation as a convex combination

[`MDPLib/Probability/Convexity.lean`](MDPLib/Probability/Convexity.lean)

| | Result | Lean name |
|---|---|---|
| ✅ | `𝔼[X // P]` is Mathlib's `Finset.centerMass` at weights summing to one | `Findist.exp_eq_centerMass` |
| ✅ | `min X ≤ 𝔼[X] ≤ max X` | `Findist.exp_ge_min`, `Findist.exp_le_max` |
| ✅ | Jensen's inequality for an arbitrary convex / concave function | `Findist.exp_convexOn_le`, `Findist.exp_concaveOn_ge` |

### Bridge to Mathlib's standard simplex

[`MDPLib/Probability/StdSimplex.lean`](MDPLib/Probability/StdSimplex.lean)

| | Result | Lean name |
|---|---|---|
| ✅ | A `Findist` as a point of `Convexity.StdSimplex` (`noncomputable`; proof-layer only) | `Findist.toStdSimplex` |
| ✅ | Mathlib's indexed convex combination is this library's expectation | `Findist.toStdSimplex_iConvexComb` |
| ✅ | `dirac` is `StdSimplex.single`; the bridge is injective | `Findist.toStdSimplex_dirac`, `Findist.toStdSimplex_injective` |

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
| ✅ | Translation (cash) invariance for the `IsVaR` predicate | `isvar_translation_invariant` |
| 🚧 | … and for the computable VaR: `VaR[X + c] = VaR[X] + c` | `var_translation_invariant` |
| ✅ | Strictly monotone transformations for the `IsVaR` predicate | `isvar_f_strictmono` |
| 🚧 | … and for the computable VaR: `VaR[f∘X] = f(VaR[X])` | `var_f_strictmono` |
| 🚧 | Positive homogeneity: `VaR[c·X] = c·VaR[X]` for `c > 0` | `var_positive_homog` |

The 🚧 entries above are all complete modulo the single missing lemma
`prob_le_step_lt_max`.

[`Main.lean`](Main.lean) contains an executable that reads distributions from a JSON
file, computes VaR with `computeVaR`, and checks it against reference values
(see [`test_var.json`](test_var.json)). `computeVaR` is standalone IO glue over
`Array ℚ` rather than the verified `FinVaR`; it is
[`MDPLibTest.lean`](MDPLibTest.lean) that instantiates the library itself at `ℚ`.

### MDPs and histories

[`MDPLib/MDP/Histories.lean`](MDPLib/MDP/Histories.lean)

|    | Result                                                                                      | Lean name                                                          |
|----|---------------------------------------------------------------------------------------------|--------------------------------------------------------------------|
| ✅ | Tabular MDP with finite states, actions, transitions and rewards                            | `MDP`                                                              |
| ✅ | Histories `s₀ a₀ s₁ …`, their length, last state, prefixes, and the length-indexed subtype  | `Hist`, `Hist.length`, `Hist.last`, `Hist.prefix`, `MDP.HistT`     |
| ✅ | The count `S · (S·A)^t` and the explicit index maps `Fin (numhist t) ↔ HistT t`             | `MDP.numhist`, `MDP.idx_to_hist`, `MDP.hist_to_idx`                |
| 🚧 | … that those maps are mutually inverse, i.e. that the count is the cardinality              | `hist_idx_LeftInverse`, `hist_idx_RightInverse`, `state_of_hist_len0`, `state_of_hist_len_t` |
| ✅ | Embeddings `Hist × A × S ↪ Hist` and `S ↪ Hist`                                             | `emb_tuple2hist`, `state2hist_emb`                                 |
| ✅ | The horizon-`t` history sets are exactly the histories of length `t`; `Fintype (M.HistT t)` | `hist_horiz_complete`, `hist_horiz_exact`, `MDP.HistoriesHorizonT` |

The `ℋ h t` family (histories extending `h` by `t` steps) is defined but its length
lemma `hist_lenth_eq_horizon` is still 🚧.

`Hist M` is infinite — only the length-`t` slice `MDP.HistT t` is a `Fintype` — so a
distribution over whole histories cannot be a `Findist`, which requires `[FinEnum Ω]`. See
the note on `Hist` in the source for what that means for trajectory distributions.

[`MDPLib/Risk/CVaR.lean`](MDPLib/Risk/CVaR.lean) is an empty stub; it carries notes on which
Mathlib pieces are and are not available for Conditional Value at Risk.


## Building and testing

```bash
lake build MDPLib            # the library
./test.sh                    # computability + regression tests, interpreted and compiled
lake -R build MDPLib:docs    # the API documentation
```

Do **not** run a bare `lake build`: the default target is the `mdplib` executable, which
native-compiles every transitively-imported Mathlib module. Build a target by name.

Building the executable or the docs needs memory headroom. On a machine with little or no swap
those builds fail with `resource exhausted (error code: 12, not enough memory)` — note this is
a refused `fork()`, not a job that needs a lot of RAM (a single `clang -O3` on Mathlib's largest
generated C file peaks at ~250 MB). Cap the concurrency with `LEAN_NUM_THREADS` (this version of
Lake has no `-j` option):

```bash
LEAN_NUM_THREADS=2 lake build mdplib       # ~5 min, produces .lake/build/bin/mdplib
./.lake/build/bin/mdplib < test_var.json
```

The documentation build is heavier still — each page forks a `doc-gen4` that loads the module
environment — and may need real swap rather than just fewer threads.

[`test.sh`](test.sh) checks the computability claim above at four increasing levels of
strength, all of them unconditionally:

1. **Elaboration.** [`MDPLibTest.lean`](MDPLibTest.lean) states every definition under test as
   a plain `def`, so elaboration fails if anything it touches becomes `noncomputable`, and
   every `#guard` pins the resulting value. This runs via `lake env lean` rather than
   `lake build` on purpose — the build caches its result, so on a warm cache `lake build
   MDPLibTest` would report success without re-running the guards.
2. **Interpreted execution.** The [`test_var.json`](test_var.json) regression suite is run
   through `lake env lean --run Main.lean`, which takes about ten seconds.
3. **Native compilation.** `lake build mdplib` compiles the whole import closure to machine
   code, exercising the compiler backend rather than just the elaborator's check.
4. **Compiled execution.** The compiled binary is run against the same suite, so the numbers
   come from compiled code rather than the interpreter.

Note that `Main.main` has type `IO Unit` and never sets a non-zero exit code, so the script
greps the harness's `--- N passed, M failed` summary text for both execution steps.

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



