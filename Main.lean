import MDPLib
import MDPLib.Risk.VaR

theorem fancy : True := True.intro

example : 0 ≤ (0.5 : ℚ) := by norm_num

def main : IO Unit := -- main
  let x : Fin 6 → ℚ := ![4.0,5.0,1.0,2.0,-1.0,-2.0]
  let p : Fin 6 → ℚ := ![0.1,0.2,0.3,0.1, 0.3, 0.0]
  let P : Findist 6 := 
    { p := p, 
      prob := by simp [dotProduct, p]; decide_cbv, 
      nneg := (fun ω => by fin_cases ω; repeat (simp [p]; norm_num))}     
  let α : Risk.RiskLevel := ⟨0.7, by constructor; linarith; linarith⟩

  let v := Risk.FinVaR P x α

  IO.println s!"VaR value: {v}" 


