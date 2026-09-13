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
structure ProbabilityMatrix (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] (Ω : Type) [FinEnum Ω] : Type where
    -- Square matrix over `Ω` where each row is a probability distribution
    toMatrix : (Matrix Ω Ω R)
    mulVec_one : toMatrix *ᵥ 1 = 1
    nonneg : ∀ i j : Ω, toMatrix i j ≥ 0

variable (Prob : ProbabilityMatrix R Ω) (μ : Findist R Ω) (r : Ω → R) (γ : R)


-- TODO(mathlib): = `Matrix.nonneg_vecMul_of_mem_rowStochastic`
-- (`Mathlib/LinearAlgebra/Matrix/Stochastic.lean:84`).
-- (`ᵥ*`, i.e. `vecMul`). These names should in any case disappear with the `TODO(mathlib)`
-- replacements noted above.
theorem nonneg_vecMul : μ.p ᵥ* (Prob.toMatrix) ≥ 0 := by
    unfold vecMul
    intro j
    apply dotProduct_nonneg_of_nonneg
    exact μ.nonneg
    exact fun i => Prob.nonneg i j

-- TODO(mathlib): = `Matrix.vecMul_dotProduct_one_eq_one_rowStochastic`
-- (`Mathlib/LinearAlgebra/Matrix/Stochastic.lean:105`) -- same statement *and* same proof
-- (`rw [← dotProduct_mulVec, hM.2, hx]`).
theorem vecMul_dotProduct_one : μ.p ᵥ* (Prob.toMatrix) ⬝ᵥ 1 = 1 := by
    rw [← dotProduct_mulVec]
    calc μ.p ⬝ᵥ Prob.toMatrix *ᵥ 1 = μ.p ⬝ᵥ 1 := by rw[Prob.mulVec_one]
        _ = 1 ⬝ᵥ μ.p := by rw[dotProduct_comm]
        _ = 1 := by rw[μ.sum_eq_one]

end ProbabilityMatrix

section RewardProcess

variable {Ω : Type} [FinEnum Ω]

--Discounted Markov Reward Process Definition
-- TODO(naming): field `discount_in_range` → split into `γ_nonneg : 0 ≤ γ` and
-- `γ_lt_one : γ < 1`. Mathlib does not bundle a conjunction behind a vague name like
-- "in_range"; two fields named after their statements give usable dot notation.
structure DiscountedMRP (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] (Ω : Type) [FinEnum Ω] : Type where
    r : Ω → R --rewards
    transition : ProbabilityMatrix R Ω --transitions
    γ : R --discount
    discount_in_range : 0 ≤ γ ∧ γ < 1

variable (Proc : DiscountedMRP R Ω) (u : Ω → R) (v : Ω → R)

def bellmanBackup (v : Ω → R) : Ω → R := Proc.r + Proc.γ • Proc.transition.toMatrix *ᵥ v

notation "𝔹["v "//" Proc "]" => bellmanBackup Proc v

end RewardProcess
