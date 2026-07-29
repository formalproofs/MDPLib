import MDPLib.Probability.Prelude
import MDPLib.Probability.Defs

import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace Matrix

section ProbabilityMatrix

variable {Ω : Type} [FinEnum Ω]

structure ProbabilityMatrix (Ω : Type) [FinEnum Ω] : Type where
    -- Square matrix over `Ω` where each row is a probability distribution
    P : (Matrix Ω Ω ℚ)
    row_sum : P *ᵥ 1 = 1
    nneg : ∀ i j : Ω, P i j ≥ 0

variable (Prob : ProbabilityMatrix Ω) (μ : Findist Ω) (r : Ω → ℚ) (γ : ℚ)


theorem dist_prob_product_nneg : μ.p ᵥ* (Prob.P) ≥ 0 := by
    unfold vecMul
    intro j
    apply dotProduct_nonneg_of_nonneg
    exact μ.nneg
    exact fun i => Prob.nneg i j

theorem dist_prob_product_sum : μ.p ᵥ* (Prob.P) ⬝ᵥ 1 = 1 := by
    rw [← dotProduct_mulVec]
    calc μ.p ⬝ᵥ Prob.P *ᵥ 1 = μ.p ⬝ᵥ 1 := by rw[Prob.row_sum]
        _ = 1 ⬝ᵥ μ.p := by rw[dotProduct_comm]
        _ = 1 := by rw[μ.prob]

end ProbabilityMatrix

section RewardProcess

variable {Ω : Type} [FinEnum Ω]

--Discounted Markov Reward Process Definition
structure DMRP (Ω : Type) [FinEnum Ω] : Type where
    r : Ω → ℚ --rewards
    Prob : ProbabilityMatrix Ω --transitions
    γ : ℚ --discount
    discount_in_range : 0 ≤ γ ∧ γ < 1

variable (Proc : DMRP Ω) (u : Ω → ℚ) (v : Ω → ℚ)

def bellman_backup (v : Ω → ℚ) : Ω → ℚ := Proc.r + Proc.γ • Proc.Prob.P *ᵥ v

notation "𝔹["v "//" Proc "]" => bellman_backup Proc v

-- Looking for norm in mathlib
theorem bellman_backup_contraction : 1 = 1 := by sorry

end RewardProcess
