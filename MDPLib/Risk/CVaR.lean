import MDPLib.Probability.Basic
import MDPLib.Risk.VaR

namespace Risk

/-
NOTE(mathlib): groundwork notes for CVaR, from the 2026-09-13 Mathlib audit (see the block at
the top of `MDPLib/Probability/Defs.lean` for why measure theory is not usable here).

* There is **no discrete Markov inequality in Mathlib**. `mul_meas_ge_le_lintegral`
  (`MeasureTheory/Integral/Lebesgue/Markov.lean:52`) is `ℝ≥0∞`/measure-valued and noncomputable.
  A `Finset` version over `R` must be hand-rolled; the ingredients are
  `Finset.sum_le_sum_of_subset_of_nonneg` and `Finset.card_nsmul_le_sum`
  (`Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:169,291`) applied over a
  `Finset.filter`.
* Both standard definitions of CVaR stay inside this library's finite, computable setting:
  `𝔼[X | X ≤ᵣ VaR]` is `expect_cnd`, and the optimisation form
  `min over t of  t + (1-α)⁻¹ * 𝔼[(X - t)⁺]` attains at a point of `X`'s finite image, so it is
  a `Finset.min'` over `FinVaRSet`-style candidates -- no infimum over `ℝ` is needed.
  The `(1-α)⁻¹` factor is already available as `Prob.complement_inv_nneg`
  (`MDPLib/Probability/Prelude.lean`).
* Convexity/coherence arguments should go through `Finset.centerMass`; `exp_convexOn_le` in
  `MDPLib/Probability/Convexity.lean` is the entry point.
-/

end Risk

