import MDPLib.Probability.Basic
import MDPLib.Risk.VaR

namespace Risk

/-- Tail indicator: 1 if X(ω) > t, else 0. -/
def tailInd (X : FinRV n ℚ) (t : ℚ) : FinRV n ℚ :=
  fun ω => if X ω > t then 1 else 0

variable {n : ℕ}

/-- Conditional Value-at-Risk (CVaR) of X at level α under P.
CVaR_α(X) =  E[X * I[X > VaR] ] / P[X > VaR]
If the tail probability is zero, CVaR is defined to be 0.
-/
def CVaR (P : Findist n) (X : FinRV n ℚ) (α : RiskLevel) : ℚ :=
  -- TODO: This CVaR computation is incorrect
  -- we could use the implementation from here: https://arxiv.org/abs/2607.05078
  let v := Risk.FinVaR P X α
  let B : FinRV n ℚ := tailInd X v
  let num := 𝔼[X * B // P]
  let den := ℙ[X >ᵣ v // P]
  if _ : den = 0 then
     0
  else
     num / den

-- NOTE (Marek): The CVaR, as defined above is not convex/concave.
-- See Page 14 at https://www.cs.unh.edu/~mpetrik/pub/tutorials/risk2/dlrl2023.pdf
-- NOTE (Marek): The CVaR above is defined for costs and not rewards

notation "CVaR[" X "//" P ", " α "]" => CVaR P X α

--TODO: prove...
-- monotonicity: (∀ ω, X ω ≤ Y ω) → CVaR[α, X // P] ≤ CVaR[α, Y // P]
-- translation: CVaR[α, (fun ω => X ω + c) // P] = CVaR[α, X // P] + c
-- positive homogeneity: c > 0 → CVaR[α, (fun ω => c * X ω) // P] = c * CVaR[α, X // P]
-- convexity
-- CVaR ≥ VaR: CVaR[α, X // P] ≥ VaR[α, X // P]

end Risk

