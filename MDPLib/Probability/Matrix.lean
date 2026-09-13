import MDPLib.Probability.Prelude
import MDPLib.Probability.Defs

import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct

set_option linter.unusedSectionVars false

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
         [CharZero R] [Archimedean R]


namespace Matrix

section ProbabilityMatrix

variable {Ω : Type} [FinEnum Ω]

-- TODO(mathlib): this is `Matrix.rowStochastic ℚ Ω`
-- (`Mathlib/LinearAlgebra/Matrix/Stochastic.lean:46`), whose carrier is
-- `{M | (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1}` -- field-for-field this structure.
-- It needs `[DecidableEq Ω]`, which `FinEnum Ω` supplies.
-- Switching would additionally give `le_one_of_mem_rowStochastic`,
-- `nonneg_mulVec_of_mem_rowStochastic` and `convex_rowStochastic` for free.
-- TODO(naming): field `row_sum : P *ᵥ 1 = 1` → `mulVec_one`. Mathlib names a field after the
-- statement it proves, spelled with the operation that appears in it (`*ᵥ` is `mulVec`);
-- `row_sum` describes the intuition and, read as a name, sounds like a function returning
-- the row sums. Field `nneg` → `nonneg` (see `Findist` in `Probability/Defs.lean`).
-- TODO(naming): field `P` shadows the local `variable (Prob : ProbabilityMatrix Ω)` naming
-- and forces the awkward `Prob.P`; `toMatrix` (or `val`) is the Mathlib spelling for the
-- carrier of a bundled structure.
structure ProbabilityMatrix (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] (Ω : Type) [FinEnum Ω] : Type where
    -- Square matrix over `Ω` where each row is a probability distribution
    P : (Matrix Ω Ω R)
    row_sum : P *ᵥ 1 = 1
    nneg : ∀ i j : Ω, P i j ≥ 0

variable (Prob : ProbabilityMatrix R Ω) (μ : Findist R Ω) (r : Ω → R) (γ : R)


-- TODO(mathlib): = `Matrix.nonneg_vecMul_of_mem_rowStochastic`
-- (`Mathlib/LinearAlgebra/Matrix/Stochastic.lean:84`).
-- TODO(naming): `dist_prob_product_nneg` → `Matrix.nonneg_vecMul` and
-- `dist_prob_product_sum` → `Matrix.vecMul_dotProduct_one`. `dist` reads as `Dist`/distance
-- in Mathlib, `prob` and `nneg` are contractions, and "product" does not say which product
-- (`ᵥ*`, i.e. `vecMul`). These names should in any case disappear with the `TODO(mathlib)`
-- replacements noted above.
theorem dist_prob_product_nneg : μ.p ᵥ* (Prob.P) ≥ 0 := by
    unfold vecMul
    intro j
    apply dotProduct_nonneg_of_nonneg
    exact μ.nneg
    exact fun i => Prob.nneg i j

-- TODO(mathlib): = `Matrix.vecMul_dotProduct_one_eq_one_rowStochastic`
-- (`Mathlib/LinearAlgebra/Matrix/Stochastic.lean:105`) -- same statement *and* same proof
-- (`rw [← dotProduct_mulVec, hM.2, hx]`).
theorem dist_prob_product_sum : μ.p ᵥ* (Prob.P) ⬝ᵥ 1 = 1 := by
    rw [← dotProduct_mulVec]
    calc μ.p ⬝ᵥ Prob.P *ᵥ 1 = μ.p ⬝ᵥ 1 := by rw[Prob.row_sum]
        _ = 1 ⬝ᵥ μ.p := by rw[dotProduct_comm]
        _ = 1 := by rw[μ.prob]

end ProbabilityMatrix

section RewardProcess

variable {Ω : Type} [FinEnum Ω]

--Discounted Markov Reward Process Definition
-- TODO(naming): `DMRP` → `DiscountedMRP` or `MRP` with a discount field. Mathlib expands
-- acronyms in type names unless they are universally standard (`PMF`, `ENNReal`); a
-- four-letter one is not discoverable by search.
-- TODO(naming): field `discount_in_range` → split into `γ_nonneg : 0 ≤ γ` and
-- `γ_lt_one : γ < 1`. Mathlib does not bundle a conjunction behind a vague name like
-- "in_range"; two fields named after their statements give usable dot notation.
-- TODO(naming): field `Prob : ProbabilityMatrix Ω` → `P` or `transition`. A field whose name
-- is a truncation of its type carries no information.
structure DMRP (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] (Ω : Type) [FinEnum Ω] : Type where
    r : Ω → R --rewards
    Prob : ProbabilityMatrix R Ω --transitions
    γ : R --discount
    discount_in_range : 0 ≤ γ ∧ γ < 1

variable (Proc : DMRP R Ω) (u : Ω → R) (v : Ω → R)

-- TODO(naming): `bellman_backup` → `bellmanBackup`. It is a data-valued `def`, so Mathlib
-- requires `lowerCamelCase` with no underscores.
def bellman_backup (v : Ω → R) : Ω → R := Proc.r + Proc.γ • Proc.Prob.P *ᵥ v

notation "𝔹["v "//" Proc "]" => bellman_backup Proc v

end RewardProcess
