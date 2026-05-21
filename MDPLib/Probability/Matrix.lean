import MDPLib.Probability.Prelude

import Probability.Probability.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace Matrix

section ProbabilityMatrix

structure ProbabilityMatrix (n : ℕ) : Type where
    --(n x n) Matrix where each row is a probability distribution
    P : (Matrix (Fin n) (Fin n) ℚ)
    row_sum : P *ᵥ 1 = 1
    nneg : ∀ i j : Fin n, P i j ≥ 0

variable (n : ℕ) (Prob : ProbabilityMatrix n) (μ : Findist n) (r : Fin n → ℚ) (γ : ℚ)


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

--Discounted Markov Reward Process Definition
structure DMRP (n : ℕ) : Type where
    r : Fin n → ℚ --rewards
    Prob : ProbabilityMatrix n --transitions
    γ : ℚ --discount
    discount_in_range : 0 ≤ γ ∧ γ < 1

variable (n : ℕ) (Proc : DMRP n) (u : (Fin n) → ℚ) (v : (Fin n) → ℚ)

def bellman_backup (v : Fin n → ℚ) : Fin n → ℚ := Proc.r + Proc.γ • Proc.Prob.P *ᵥ v

notation "𝔹["v "//" Proc "]" => bellman_backup Proc v

-- Looking for norm in mathlib
theorem bellman_backup_contraction : 1 = 1 := by sorry

end RewardProcess
