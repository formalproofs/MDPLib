import MDPLib
import MDPLib.Risk.VaR

theorem fancy : True := True.intro

def main : IO Unit := -- main
  let x : Fin 3 → ℚ := ![1,2,3]
  let p : Fin 3 → ℚ := ![0.1, 0.5, 0.4]
  let P : Findist 3 := 
    {p := p, prob := by  simp [dotProduct, p]; sorry; , nneg := by sorry }     
  let α : Risk.RiskLevel := ⟨0.5, by unfold Risk.IsRiskLevel; constructor; linarith; linarith  ⟩

  let v := Risk.FinVaR P x α

  IO.println s!"VaR value: {v}" 


