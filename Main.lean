import MDPLib
import MDPLib.Risk.VaR
import Lean.Data.Json

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

-- ── JSON test-case checker ───────────────────────────────────────────────────

/-- Coerce a JSON value to a rational, accepting both string and numeric forms. -/
private def jsonToRat? (j : Lean.Json) : Option ℚ :=
  match j with
  | .str s => parseRat? s
  | .num n => parseRat? n.toString
  | _ => none

/-- Coerce a JSON array to an Array ℚ, using jsonToRat? on each element. -/
private def jsonToRats? (j : Lean.Json) : Option (Array ℚ) :=
  match j with
  | .arr a => a.mapM jsonToRat?
  | _ => none

/-- Read a JSON array of test cases from stdin and verify each VaR value.

    Expected JSON format (array of objects):
    ```json
    [
      { "probs": ["1/3","1/3","1/3"], "vals": ["1","2","3"],
        "alpha": "0.5", "expected": "2" }
    ]
    ```
    Values may be strings ("a/b", decimal, integer) or JSON numbers.
    Prints PASS / FAIL for each case and a summary at the end. -/
def checkVaRTestCases : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  match Lean.Json.parse input with
  | .error e => IO.println s!"JSON parse error: {e}"
  | .ok json =>
    match json with
    | .arr cases =>
      let mut passed := 0
      let mut failed := 0
      let mut i := 0
      for c in cases do
        let field (key : String) : Option Lean.Json := c.getObjVal? key |>.toOption
        let result : Option (ℚ × ℚ) := do
          let probs    ← jsonToRats? (← field "probs")
          let vals     ← jsonToRats? (← field "vals")
          let α        ← jsonToRat?  (← field "alpha")
          let expected ← jsonToRat?  (← field "expected")
          let var      ← computeVaR probs vals α
          some (var, expected)
        match result with
        | none =>
          IO.println s!"Case {i}: ERROR (parse or computation failed)"
        | some (var, expected) =>
          if var == expected then
            IO.println s!"Case {i}: PASS  (VaR = {var})"
            passed := passed + 1
          else
            IO.println s!"Case {i}: FAIL  (expected {expected}, got {var})"
            failed := failed + 1
        i := i + 1
      IO.println s!"--- {passed} passed, {failed} failed out of {i} cases ---"
    | _ => IO.println "Error: expected a JSON array of test cases"

-- ── Demo ─────────────────────────────────────────────────────────────────────

def main : IO Unit :=
  checkVaRTestCases
