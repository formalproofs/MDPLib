import MDPLib
import MDPLib.Risk.VaR

theorem fancy : True := True.intro

example : 0 ≤ (0.5 : ℚ) := by norm_num

-- ── Parsing ──────────────────────────────────────────────────────────────────

/-- Parse a rational from "a/b" or bare-integer format. -/
private def strTrim (s : String) : String := s.trimAscii.toString

/-- Parse a rational from "a/b", decimal "1.5"/"-0.5", or bare-integer format. -/
def parseRat? (s : String) : Option ℚ :=
  let s := strTrim s
  if s.contains '/' then
    match s.splitOn "/" with
    | [n, d] => do
        let num ← (strTrim n).toInt?
        let den ← (strTrim d).toInt?
        if den = 0 then none else some ((num : ℚ) / (den : ℚ))
    | _ => none
  else if s.contains '.' then
    let (neg, s') := if s.startsWith "-" then (true, s.drop 1 |>.toString) else (false, s)
    match s'.splitOn "." with
    | [intPart, fracPart] => do
        let whole ← (strTrim intPart).toNat?
        let frac  ← (strTrim fracPart).toNat?
        let denom := (10 : ℚ) ^ fracPart.length
        let r : ℚ := (whole : ℚ) + (frac : ℚ) / denom
        some (if neg then -r else r)
    | _ => none
  else
    s.toInt?.map (fun n => (n : ℚ))

-- ── Core computation ─────────────────────────────────────────────────────────

/-- VaR_α(X) from parallel probability and value arrays.
    VaR = max { t ∈ range(X) | P[X < t] ≤ α }.
    Returns none when the arrays are empty or have different sizes. -/
def computeVaR (probs vals : Array ℚ) (α : ℚ) : Option ℚ :=
  if probs.size != vals.size || probs.size == 0 then none
  else
    let pv := probs.toList.zip vals.toList
    -- P[X < t] = sum of p_i over outcomes where x_i < t
    let probLt (t : ℚ) : ℚ :=
      pv.foldl (fun acc px => if px.2 < t then acc + px.1 else acc) 0
    -- keep every value in range(X) that satisfies the VaR condition
    let valid := vals.toList.filter (fun t => probLt t ≤ α)
    match valid with
    | []      => none
    | v :: vs => some (vs.foldl max v)

-- ── Console I/O ──────────────────────────────────────────────────────────────

/-- Read a probability distribution and random variable from stdin, then print
    the Value-at-Risk at the requested level.

    Expected input (four lines):
      n               — number of outcomes (positive integer)
      p₁ p₂ … pₙ     — probabilities, space-separated rationals "a/b", decimals, or integers
      x₁ x₂ … xₙ     — outcome values, same format
      α               — risk level in [0, 1) -/
def parseAndPrintVaR : IO Unit := do
  let stdin ← IO.getStdin
  let l1 ← stdin.getLine
  let l2 ← stdin.getLine
  let l3 ← stdin.getLine
  let l4 ← stdin.getLine
  let tok (l : String) := (strTrim l).splitOn " " |>.filter (· ≠ "")
  let result : Option ℚ := do
    let n     ← (strTrim l1).toNat?
    let probs ← (tok l2).mapM parseRat? |>.map (·.toArray)
    let vals  ← (tok l3).mapM parseRat? |>.map (·.toArray)
    let α     ← parseRat? l4
    if probs.size != n || vals.size != n then none
    else computeVaR probs vals α
  match result with
  | none   => IO.println "Error: invalid input or computation failed"
  | some v => IO.println s!"VaR = {v}"

-- ── Demo ─────────────────────────────────────────────────────────────────────

def main : IO Unit :=
  parseAndPrintVaR
