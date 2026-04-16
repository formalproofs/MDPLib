import MDPLib
import MDPLib.Risk.VaR

theorem fancy : True := True.intro

example : 0 ≤ (0.5 : ℚ) := by norm_num

def main : IO Unit := -- main
  let x : Fin 3 → ℚ := ![1,2,3]
  let p : Fin 3 → ℚ := ![0.1, 0.5, 0.4]
  set_option diagnostics true in 
  let P : Findist 3 := 
    { p := p, 
      prob := by simp [dotProduct, p]; decide_cbv, 
      nneg := (fun ω => by fin_cases ω; repeat (simp [p]; norm_num))}     
  let α : Risk.RiskLevel := ⟨0.5, by constructor; linarith; linarith⟩

  let v := Risk.FinVaR P x α

  IO.println s!"VaR value: {v}" 


