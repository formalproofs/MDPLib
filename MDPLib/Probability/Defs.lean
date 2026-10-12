import MDPLib.Probability.Prelude

import Mathlib.Data.FinEnum -- finitely-enumerable sample spaces
import Mathlib.Data.Matrix.Mul  -- dot product definitions and results
import Mathlib.Algebra.Notation.Pi.Defs -- operations on functions
import Mathlib.Algebra.Module.PointwisePi -- for smul_pi
import Mathlib.LinearAlgebra.Matrix.DotProduct -- for monotonicity
import Mathlib.Data.Finset.Image -- for Finset.universal.image
import Mathlib.Algebra.Ring.BooleanRing -- `0`, `1` on Bool

set_option linter.unusedSectionVars false

-- Two types, by role:
-- * `W` (weights): probabilities, and the values of random variables that are combined with
--   them arithmetically (expectation, CVaR). Any linear ordered field (see
--   `MDPLib/Probability/Prelude.lean`); the targets are ℚ for computability and ℝ for proofs.
-- * `V` (values): the values of random variables whose results only need the order on them
--   (events, `ℙ`, the CDF, quantiles, VaR). Any linear order, e.g. `W` itself, ℕ, or ℤ.
--   Keeping `V` separate from `W` lets `@[to_dual (dont_translate := W)]` reverse the order on
--   values without also reversing it on probabilities.
variable {W : Type} [Field W] [LinearOrder W] [IsStrictOrderedRing W] [CharZero W] [Archimedean W]


--------------------------- Findist ---------------------------------------------------------------

structure Findist (W : Type) [Field W] [LinearOrder W] [IsStrictOrderedRing W] (Ω : Type) [FinEnum Ω] : Type where
    /-- Probability measure -/
    p : Ω → W
    sum_eq_one : 1 ⬝ᵥ p = 1
    nonneg : 0 ≤ p

namespace Findist


/-- Finite probability distribution  -/
abbrev Delta (W : Type) [Field W] [LinearOrder W] [IsStrictOrderedRing W] (Ω : Type) [FinEnum Ω] : Type := Findist W Ω

/-- Finite probability distribution  -/
abbrev Δ (W : Type) [Field W] [LinearOrder W] [IsStrictOrderedRing W] (Ω : Type) [FinEnum Ω] : Type := Delta W Ω

/-- Dirac (point mass) distribution concentrated at `ω₀`. -/
-- NOTE(mathlib): `p` here is `Pi.single ω₀ 1`; cf. `StdSimplex.single` / `single_mem_stdSimplex`.
def dirac {Ω : Type} [FinEnum Ω] (ω₀ : Ω) : Findist W Ω where
    p    := fun ω => if ω = ω₀ then 1 else 0
    sum_eq_one := by simp [dotProduct]
    nonneg := by intro ω; by_cases h : ω = ω₀ <;> simp [h]

variable {Ω : Type} [FinEnum Ω]


/-- The sample space of a probability distribution is nonempty. -/
theorem nonempty (P : Findist W Ω) : Nonempty Ω := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := P.sum_eq_one
  simp_all only [Matrix.dotProduct_of_isEmpty, zero_ne_one]

/-- A distribution over an empty sample space is impossible. -/
theorem isEmpty_elim [IsEmpty Ω] (P : Findist W Ω) : False :=
  (not_nonempty_iff.mpr ‹_›) P.nonempty


end Findist

------------------------ Random Variable --------------------------------------------------

/-!
Random variables are defined as functions. The operations on random variables can be performed
using the standard notation:

- X + Y is elementwise addition
- X * Y is elementwise product (Hadamard product)
- f ∘ X is composition
- c • X is scalar multiplication


- L =ᵣ i is a boolean indicator random variable
- L =ᵢ i is a `W`-valued indicator random variable
- L ≤ᵣ i is a bool indicator random variable

Main results

- Hadamard product is linear:  Y * (∑ i, Xs i) = ∑ i, Y * (Xs i)
-/


section RandomVariable

/-- A finite random variable: a bare function from the sample space `Ω` to `V`.
    The `FinEnum` instance lives on `Ω` and is shared with the distribution function. -/
abbrev FinRV (Ω : Type) [Nonempty Ω] (V : Type) := Ω → V

variable {Ω : Type} [Nonempty Ω] {V : Type}

namespace FinRV

-- Boolean random variables use Mathlib's lattice operations: `B ⊔ C` is the union (`or`),
-- `B ⊓ C` the intersection (`and`), and `¬ᵣ B` the complement. `0`/`1` are `false`/`true`
-- from Mathlib's `BooleanRing Bool`; do not use its `+`, which is `xor`.
variable {A B : Bool}

@[simp] theorem one_eq_true : (1:Bool) = true := rfl
@[simp] theorem zero_eq_false : (0:Bool) = false := rfl
@[simp] theorem sup_eq_or : A ⊔ B = (A || B) := rfl
@[simp] theorem inf_eq_and : A ⊓ B = (A && B) := rfl


-- NOTE: the following definitions of inequalities and operations
-- are neccessary because the standard operators generate Prop whereas
-- we need to generate random variables.

/-- Negates a random variable -/
@[simp] def not (B : FinRV Ω Bool) : FinRV Ω Bool :=
  fun ω ↦ (B ω).not

/-- Negates a random variable -/
prefix:40 "¬ᵣ" => FinRV.not

/-- Boolean random variable representing an quality condition -/
@[simp] def eq [DecidableEq V] (Y : FinRV Ω V) (y : V) : FinRV Ω Bool :=
  (fun ω ↦ decide (Y ω = y))

/-- Boolean random variable representing an quality condition -/
infix:50 "=ᵣ" => FinRV.eq

/-- 0/1 random variable representing an quality condition -/
@[simp] def indicatorEq {W : Type} [Zero W] [One W] [DecidableEq V] (Y : FinRV Ω V) (y : V) :
    FinRV Ω W :=
  (fun ω ↦ if Y ω = y then 1 else 0)

/-- 0/1 random variable representing an quality condition -/
infix:50 "=ᵢ" => FinRV.indicatorEq

/-- Boolean random variable represening Y ≤ y inequality -/
@[simp] def leq [LE V] [DecidableLE V] (Y : FinRV Ω V) (y : V) : FinRV Ω Bool :=
  (fun ω ↦ Y ω ≤ y)

/-- Boolean random variable represening Y ≤ y inequality -/
infix:50 "≤ᵣ" => FinRV.leq

/-- Boolean random variable represening Y ≤ y inequality -/
@[simp] 
def lt [LT V] [DecidableLT V] (Y : FinRV Ω V) (y : V) : FinRV Ω Bool :=
  (fun ω ↦ Y ω < y)

/-- Boolean random variable represening Y ≤ y inequality -/
infix:50 "<ᵣ" => FinRV.lt

/-- Boolean random variable represening Y ≤ y inequality -/
@[simp, to_dual existing leq] 
def geq [LE V] [DecidableLE V] (Y : FinRV Ω V) (y : V) : FinRV Ω Bool :=
  (fun ω ↦ Y ω ≥ y)

/-- Boolean random variable represening Y ≤ y inequality -/
infix:50 "≥ᵣ" => FinRV.geq

/-- Boolean random variable represening Y > y inequality -/
@[simp, to_dual existing lt] def gt [LT V] [DecidableLT V] (Y : FinRV Ω V) (y : V) : FinRV Ω Bool :=
  fun ω ↦ Y ω > y

/-- Boolean random variable represening Y > y inequality -/
infix:50 ">ᵣ" => FinRV.gt

--instance instCoeFinRV_Fun : Coe (FinRV Ω V) (Ω → V) where 
--  coe a := a

/-- Equivalence when adding an element to integer comparison. -/
theorem leq_sup_eq_succ (D : FinRV Ω ℕ) (m : ℕ) : ((D ≤ᵣ m) ⊔ (D =ᵣ m.succ)) = (D ≤ᵣ m.succ) := by
  funext x
  simp only [Pi.sup_apply, FinRV.leq, FinRV.eq, sup_eq_or]
  by_cases h₁ : D x ≤ m <;> by_cases h₂ : D x = m + 1 <;> simp [h₁, h₂] <;> omega

/-- Defines a preimage of an RV. This is a set with a decidable membership. -/
def preimage (f : FinRV Ω V) : V → Set Ω :=
  fun t => { m : Ω | f m  = t}

variable [DecidableEq V] [FinEnum Ω]
/-! Finite set of potential atoms of X (probability may be zero) -/
abbrev quarks  (X : FinRV Ω V) := Finset.univ.image X

theorem mem_quarks {X : FinRV Ω V} (ω) : X ω ∈ X.quarks := Finset.mem_image_of_mem X (Finset.mem_univ ω)

theorem quarks_nonempty {X : FinRV Ω V} : X.quarks.Nonempty := Finset.univ_nonempty.image X

end FinRV

namespace FinRV

/-- Boolean indicator function -/
def indicator {W : Type} [Zero W] [One W] (cond : Bool) : W := cond.rec 0 1

/-- Boolean indicator function -/
abbrev 𝕀 {W : Type} [Zero W] [One W] : Bool → W := indicator


variable {k : ℕ} {L : FinRV Ω (Fin k)}

theorem indicator_comp_eq_indicatorEq : ∀i : Fin k, (𝕀 ∘ (L =ᵣ i) : FinRV Ω W) = (L =ᵢ i) := by
  intro i; unfold FinRV.eq FinRV.indicatorEq 𝕀 indicator; ext ω; by_cases h: L ω = i; repeat simp [h]

variable {B : FinRV Ω Bool}

theorem indicator_eq_one_or_eq_zero {ω : Ω} : (𝕀∘B : FinRV Ω W) ω = 1 ∨ (𝕀∘B : FinRV Ω W) ω = 0 := by
    by_cases h : B ω
    · left; simp only [Function.comp_apply, h, indicator]
    · right; simp only [Function.comp_apply, h, indicator]

/-- Indicator is 0 or 1 -/
theorem indicator_nonneg : (0 : FinRV Ω W) ≤ 𝕀∘B := by
    intro ω; unfold 𝕀 indicator; by_cases h : B ω; repeat simp [h]

theorem indicator_le_one : (𝕀∘B : FinRV Ω W) ≤ 1 :=
    by unfold 𝕀 indicator; intro ω; by_cases h : B ω; repeat simp [h]

variable {c : W} {X : FinRV Ω W}

omit [Nonempty Ω] in
theorem const_eq_smul_one : (fun _ ↦ c : FinRV Ω W)  = c • 1 := by ext; simp;

theorem eq_sum_mul_indicatorEq (X : FinRV Ω W) (L : FinRV Ω (Fin k)) : X = ∑ i, X * (L =ᵢ i) := by ext ω; simp

omit [Nonempty Ω] in
theorem indicator_one : 𝕀 ∘ (1 : Ω → Bool) = (1 : Ω → W) := by ext; simp [𝕀, indicator]

theorem sup_not_eq_one : B ⊔ (¬ᵣ B) = (1 : FinRV Ω Bool) := by ext ω; unfold FinRV.not; simp

theorem indicator_add_indicator_not_eq_one : (𝕀∘B) + (𝕀∘(¬ᵣ B)) = (1 : FinRV Ω W) :=
    by ext ω; unfold FinRV.not 𝕀 indicator Bool.not
       by_cases h : B ω <;> simp [h]

variable {X Y: FinRV Ω W} {Xs : Fin k → FinRV Ω W}

theorem rv_le_abs : X ≤ abs ∘ X := le_abs_self X

theorem rv_prod_sum_additive  : ∑ i, Y * (Xs i) = Y * (∑ i, Xs i) := Eq.symm (Finset.mul_sum Finset.univ Xs Y)

variable {g : Fin k → W}

theorem comp_mul_indicatorEq (i) : (g ∘ L) * (L =ᵢ i) = (g i) • (L =ᵢ i) := 
    by ext ω; by_cases h : L ω = i <;> simp [h] 

-- assume enumerability of Ω from here because we need a probability space
variable [FinEnum Ω] [LinearOrder V]

@[to_dual] -- minQuark
def maxQuark (X : FinRV Ω V) : V := X.quarks.max' quarks_nonempty

variable {X : FinRV Ω V}

@[to_dual]
theorem maxQuark_mem_quarks : X.maxQuark ∈ X.quarks := Finset.max'_mem _ quarks_nonempty

@[to_dual minQuark_le]
theorem le_maxQuark (ω) : X ω ≤ X.maxQuark := Finset.le_max' (X.quarks) (X ω) (mem_quarks ω)

end FinRV

end RandomVariable

------------------------------ Probability ---------------------------

namespace Findist
open FinRV

section Probability 

variable {Ω : Type} [Nonempty Ω] [FinEnum Ω] (P : Findist W Ω) (B C : FinRV Ω Bool)

/-- Probability of B -/
def probability : W :=  P.p ⬝ᵥ (𝕀 ∘ B)

/-- Probability of B -/
notation "ℙ[" B "//" P "]" => probability P B

/-- Conditional probability of B on C -/
def probabilityCond : W := ℙ[B ⊓ C // P] / ℙ[ C // P ]

/-- Conditional probability of B on C -/
notation "ℙ[" B "|" C "//" P "]" => probabilityCond P B C

/-- Elements of Ω with positive probability  -/
def support (P : Findist W Ω) : Finset Ω := Finset.univ.filter (fun ω => P.p ω > 0)

/-- Values of X with positive probability -/
def atoms {V : Type} [DecidableEq V] (P : Findist W Ω) (X : FinRV Ω V) : Finset V := P.support.image X

theorem probability_one : ℙ[1 // P] = 1 :=
    by rewrite [probability, indicator_one, dotProduct_comm]
       exact P.sum_eq_one

example {a b : W} (h : 0 ≤ a) (h2 : 0 ≤ b) : 0 ≤ a * b :=  mul_nonneg h h2

variable {P : Findist W Ω} {B : FinRV Ω Bool}

theorem probability_congr {A : FinRV Ω Bool} (h : A = B) : ℙ[A // P] = ℙ[B // P] := congrArg (probability P) h

theorem mul_eq_zero_of_probability_eq_zero (h : ℙ[B // P] = 0) : (P.p * (𝕀∘B) = 0) := by
    exact Matrix.mul_eq_zero_of_dotProduct_eq_zero P.nonneg indicator_nonneg h

------------------------------ IsPMF ---------------------------

/-- Proof that p is a the IsPMF of X on probability space P -/
def IsPMF {K : ℕ} (pmf : Fin K → W) (P : Findist W Ω) (L : FinRV Ω (Fin K)) :=
    ∀ k : Fin K, pmf k = ℙ[ L =ᵣ k // P]

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] {k : ℕ}  {L : FinRV Ω (Fin k)}
variable {pmf : Fin k → W} {P : Findist W Ω}

theorem IsPMF.pos (h : IsPMF pmf P L)  : 0 < k :=
  match k with  
  | Nat.zero => Fin.pos <| L P.nonempty.some
  | Nat.succ k₂ => Nat.zero_lt_succ k₂

end Probability

------------------------------ CDF ----------------------

section CDF

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] {V : Type} [LinearOrder V]

def cdf (P : Findist W Ω) (X : FinRV Ω V) (t : V) : W := ℙ[X ≤ᵣ t // P]

end CDF

------------------------------ Expectation ----------------------

/-!

## Expectation operator

Definitions and main properties of the expectation operator

Main results
  - Monotonicity of expectations 
  - Correspondence between expectations and probabilities (indicator functions)
  - Decomposition with a discrete random variables, used in the proofs of LOTUS and TLE
-/

section Expectation_properties

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] (P : Findist W Ω) (X Y Z: FinRV Ω W) (B : FinRV Ω Bool)

/-- Standard expectation operator -/
def expect : W := P.p ⬝ᵥ X

/-- Default expectation operator -/
notation "𝔼[" X "//" P "]" => expect P X


theorem probability_eq_expect_indicator : ℙ[B // P] = 𝔼[(𝕀 ∘ B : FinRV Ω W) // P] := by simp only [expect, probability]

/-- Conditional expectation operator -/
def expectCond : W := 𝔼[ X * (𝕀 ∘ B) // P] / ℙ[ B // P]

/-- Conditional expectation operator -/
notation "𝔼[" X "|" B "//" P "]" => expectCond P X B

variable {k : ℕ} (L : FinRV Ω (Fin k))

/-- Expectation conditioned on a random variable. It creates a random variable -/
def expectCondRV : Ω → W := fun i ↦ 𝔼[ X | L =ᵣ (L i) // P ]

/-- Expectation conditioned on a random variable. It creates a random variable -/
notation "𝔼[" X "|ᵣ" L "//" P "]" => expectCondRV P X L

--- some basic properties

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] {P : Findist W Ω} {X Y Z: FinRV Ω W} {B : FinRV Ω Bool}

theorem expect_congr (h : X = Y) : 𝔼[X // P] = 𝔼[Y // P] := congrArg (expect P) h

theorem expect_mul_comm : 𝔼[X * Y // P] = 𝔼[Y * X // P] := expect_congr (mul_comm X Y)

variable {c : W} {p : Ω → W}

theorem expect_const : 𝔼[(fun _ ↦ c) // P] = c := by 
  rw [const_eq_smul_one,expect, dotProduct_smul,smul_eq_mul,dotProduct_comm,P.sum_eq_one,mul_one]

theorem expect_one : 𝔼[ 1 // P] = 1 := expect_const
       
/-- Expectation is homogeneous under product -/
theorem expect_smul : 𝔼[c • X // P] = c * 𝔼[X // P] := by rw [expect, expect, Matrix.dotProduct_smul']

theorem expect_const_mul : 𝔼[(fun _ ↦ c) * X // P] = c * 𝔼[X // P] := by rw [const_mul_eq_smul, expect_smul]

variable {k : ℕ} {g : Fin k → W}  {L : FinRV Ω (Fin k)}

theorem expect_indicatorEq (i) : 𝔼[(L =ᵢ i : FinRV Ω W) // P] = 𝔼[(𝕀 ∘ (L =ᵣ i) : FinRV Ω W) // P] := by rw [indicator_comp_eq_indicatorEq]

/-- Additivity of expectation --/
theorem expect_sum {m : ℕ} (Xs : Fin m → FinRV Ω W) : 
    𝔼[∑ i : Fin m, Xs i // P] = ∑ i : Fin m, 𝔼[Xs i // P] := dotProduct_sum P.p Finset.univ Xs
     
theorem expect_add : 𝔼[X + Y // P] = 𝔼[X // P] + 𝔼[Y // P] := dotProduct_add P.p X Y

/-- Expectation is monotone  -/
theorem expect_mono (h: X ≤ Y)  : 𝔼[X // P] ≤ 𝔼[Y // P] := dotProduct_le_dotProduct_of_nonneg_left h P.nonneg

---- ** conditional expectation -----


theorem expect_eq_sum_mul_indicatorEq : 𝔼[X // P] = ∑ i, 𝔼[X * (L =ᵢ i) // P] := by 
    nth_rewrite 1 [eq_sum_mul_indicatorEq X L]
    rw [expect_sum]

/-- Expectation of a conditional constant. Only when probability is positive.  -/
theorem expectCond_comp (i) (h : ℙ[L =ᵣ i //   P] ≠ 0) : 𝔼[g ∘ L | L =ᵣ i // P] = g i := by 
    unfold expectCond
    rw [indicator_comp_eq_indicatorEq, comp_mul_indicatorEq i, expect_smul, ←indicator_comp_eq_indicatorEq, ←probability_eq_expect_indicator]
    simp [h, ne_eq, not_false_eq_true]

theorem expectCond_mul_probability  : 𝔼[X | B // P] * ℙ[B // P] = 𝔼[X * (𝕀 ∘ B) // P] :=
  by unfold expectCond 
     by_cases h: ℙ[B//P] = 0
     · rw [h, mul_zero, expect,Matrix.dotProduct_mul_comm, Matrix.dotProduct_mul_rotate, mul_eq_zero_of_probability_eq_zero h]
       exact (dotProduct_zero X).symm 
     · simp_all 

end Expectation_properties

end Findist

-- Derived properties from the properties of expectation
section Probability_properties

namespace FinRV

theorem indicator_mono {Ω : Type} [Nonempty Ω] {A B : FinRV Ω Bool}
    (h : ∀ ω, A ω → B ω) : (𝕀∘A : FinRV Ω W) ≤ (𝕀∘B) := by
  intro ω
  specialize h ω
  by_cases h1 : A ω
  · simp_all [indicator] 
  · by_cases h2 : B ω
    repeat simp_all [indicator]

end FinRV

end Probability_properties 
