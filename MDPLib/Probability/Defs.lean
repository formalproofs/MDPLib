import MDPLib.Probability.Prelude

import Mathlib.Data.FinEnum -- finitely-enumerable sample spaces
import Mathlib.Data.Matrix.Mul  -- dot product definitions and results
import Mathlib.Algebra.Notation.Pi.Defs -- operations on functions
import Mathlib.Algebra.Module.PointwisePi -- for smul_pi
import Mathlib.LinearAlgebra.Matrix.DotProduct -- for monotonicity
import Mathlib.Data.Finset.Image -- for Finset.universal.image

set_option linter.unusedSectionVars false

-- The scalar type: any linear ordered field (see `MDPLib/Probability/Prelude.lean`).
-- the particular targets are: ℚ for computability and ℝ for proofs
variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [CharZero R] [Archimedean R]


--------------------------- Findist ---------------------------------------------------------------

structure Findist (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] (Ω : Type) [FinEnum Ω] : Type where
    /-- Probability measure -/
    p : Ω → R
    sum_eq_one : 1 ⬝ᵥ p = 1
    nonneg : 0 ≤ p

namespace Findist


/-- Finite probability distribution  -/
abbrev Delta (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] (Ω : Type) [FinEnum Ω] : Type := Findist R Ω

/-- Finite probability distribution  -/
abbrev Δ (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] (Ω : Type) [FinEnum Ω] : Type := Delta R Ω

/-- Dirac (point mass) distribution concentrated at `ω₀`. -/
-- NOTE(mathlib): `p` here is `Pi.single ω₀ 1`; cf. `StdSimplex.single` / `single_mem_stdSimplex`.
def dirac {Ω : Type} [FinEnum Ω] (ω₀ : Ω) : Findist R Ω where
    p    := fun ω => if ω = ω₀ then 1 else 0
    sum_eq_one := by simp [dotProduct]
    nonneg := by intro ω; by_cases h : ω = ω₀ <;> simp [h]

variable {Ω : Type} [FinEnum Ω]


/-- The sample space of a probability distribution is nonempty. -/
theorem nonempty (P : Findist R Ω) : Nonempty Ω := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := P.sum_eq_one
  simp_all only [Matrix.dotProduct_of_isEmpty, zero_ne_one]

/-- A distribution over an empty sample space is impossible. -/
theorem isEmpty_elim [IsEmpty Ω] (P : Findist R Ω) : False :=
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
- L =ᵢ i is an `R`-valued indicator random variable
- L ≤ᵣ i is a bool indicator random variable

Main results

- Hadamard product is linear:  Y * (∑ i, Xs i) = ∑ i, Y * (Xs i)
-/


section RandomVariable

/-- A finite random variable: a bare function from the sample space `Ω` to `ρ`.
    The `FinEnum` instance lives on `Ω` and is shared with the distribution function. -/
abbrev FinRV (Ω : Type) [Nonempty Ω] (ρ : Type) := Ω → ρ

variable {Ω : Type} [Nonempty Ω] {ρ : Type}

namespace FinRV

-- WARNING: these four instances shadow Mathlib's global `Bool` algebra.
-- in `Mathlib/Algebra/Ring/BooleanRing.lean. These operations are defined differntly
instance instMulBool : Mul Bool where mul a b := Bool.and a b
instance instAddBool: Add Bool  where add a b := Bool.or a b
instance instZeroBool : Zero Bool where zero := false
instance instOneBool : One Bool where one := true

variable {A B : Bool}


@[simp] theorem one_eq_true : (1:Bool) = true := rfl
@[simp] theorem zero_eq_false : (0:Bool) = false := rfl
@[simp] theorem add_eq_or : A + B = Bool.or A B := rfl
@[simp] theorem mul_eq_and : A * B = Bool.and A B := rfl


-- NOTE: the following definitions of inequalities and operations
-- are neccessary because the standard operators generate Prop whereas
-- we need to generate random variables.

/-- Negates a random variable -/
@[simp] def not (B : FinRV Ω Bool) : FinRV Ω Bool :=
  fun ω ↦ (B ω).not

/-- Negates a random variable -/
prefix:40 "¬ᵣ" => FinRV.not

/-- Boolean random variable representing an quality condition -/
@[simp] def eq [DecidableEq ρ] (Y : FinRV Ω ρ) (y : ρ) : FinRV Ω Bool :=
  (fun ω ↦ decide (Y ω = y))

/-- Boolean random variable representing an quality condition -/
infix:50 "=ᵣ" => FinRV.eq

/-- 0/1 random variable representing an quality condition -/
@[simp] def indicatorEq {R : Type} [Zero R] [One R] [DecidableEq ρ] (Y : FinRV Ω ρ) (y : ρ) :
    FinRV Ω R :=
  (fun ω ↦ if Y ω = y then 1 else 0)

/-- 0/1 random variable representing an quality condition -/
infix:50 "=ᵢ" => FinRV.indicatorEq

/-- Boolean random variable represening Y ≤ y inequality -/
@[simp] def leq [LE ρ] [DecidableLE ρ] (Y : FinRV Ω ρ) (y : ρ) : FinRV Ω Bool :=
  (fun ω ↦ Y ω ≤ y)

/-- Boolean random variable represening Y ≤ y inequality -/
infix:50 "≤ᵣ" => FinRV.leq

/-- Boolean random variable represening Y ≤ y inequality -/
@[simp] 
def lt [LT ρ] [DecidableLT ρ] (Y : FinRV Ω ρ) (y : ρ) : FinRV Ω Bool :=
  (fun ω ↦ Y ω < y)

/-- Boolean random variable represening Y ≤ y inequality -/
infix:50 "<ᵣ" => FinRV.lt

/-- Boolean random variable represening Y ≤ y inequality -/
@[simp, to_dual existing leq] 
def geq [LE ρ] [DecidableLE ρ] (Y : FinRV Ω ρ) (y : ρ) : FinRV Ω Bool :=
  (fun ω ↦ Y ω ≥ y)

/-- Boolean random variable represening Y ≤ y inequality -/
infix:50 "≥ᵣ" => FinRV.geq

/-- Boolean random variable represening Y > y inequality -/
@[simp, to_dual existing lt] def gt [LT ρ] [DecidableLT ρ] (Y : FinRV Ω ρ) (y : ρ) : FinRV Ω Bool :=
  fun ω ↦ Y ω > y

/-- Boolean random variable represening Y > y inequality -/
infix:50 ">ᵣ" => FinRV.gt

--instance instCoeFinRV_Fun : Coe (FinRV Ω ρ) (Ω → ρ) where 
--  coe a := a

/-- Equivalence when adding an element to integer comparison. -/
theorem leq_add_eq_succ (D : FinRV Ω ℕ) (m : ℕ) : ((D ≤ᵣ m) + (D =ᵣ m.succ)) = (D ≤ᵣ m.succ) := by 
  have exclusion {a b : ℕ} (h : a > b + 1) : (a > b) ∧ ¬(a = b + 1) := 
  ⟨ Nat.lt_of_succ_lt h, Ne.symm (Nat.ne_of_lt h) ⟩
  funext x 
  rw [FinRV.leq, instHAdd, Add.add, Pi.instAdd, Pi.add_apply, add_eq_or]
  by_cases h : D x ≤ m.succ
  · simp [h, Nat.le_or_eq_of_le_succ]
  · simp [h, exclusion (Nat.not_le.mp h)] 

/-- Defines a preimage of an RV. This is a set with a decidable membership. -/
def preimage (f : FinRV Ω ρ) : ρ → Set Ω :=
  fun t => { m : Ω | f m  = t}

variable {β : Type} [DecidableEq β] [FinEnum Ω]
/-! Finite set of potential atoms of X (probability may be zero) -/
abbrev quarks  (X : FinRV Ω β) := Finset.univ.image X

theorem mem_quarks {X : FinRV Ω β} (ω) : X ω ∈ X.quarks := Finset.mem_image_of_mem X (Finset.mem_univ ω)

theorem quarks_nonempty {X : FinRV Ω β} : X.quarks.Nonempty := Finset.univ_nonempty.image X

end FinRV

namespace FinRV

/-- Boolean indicator function -/
def indicator {R : Type} [Zero R] [One R] (cond : Bool) : R := cond.rec 0 1

/-- Boolean indicator function -/
abbrev 𝕀 {R : Type} [Zero R] [One R] : Bool → R := indicator


variable {k : ℕ} {L : FinRV Ω (Fin k)}

theorem indicator_comp_eq_indicatorEq : ∀i : Fin k, (𝕀 ∘ (L =ᵣ i) : FinRV Ω R) = (L =ᵢ i) := by
  intro i; unfold FinRV.eq FinRV.indicatorEq 𝕀 indicator; ext ω; by_cases h: L ω = i; repeat simp [h]

variable {B : FinRV Ω Bool}

theorem indicator_eq_one_or_eq_zero {ω : Ω} : (𝕀∘B : FinRV Ω R) ω = 1 ∨ (𝕀∘B : FinRV Ω R) ω = 0 := by
    by_cases h : B ω
    · left; simp only [Function.comp_apply, h, indicator]
    · right; simp only [Function.comp_apply, h, indicator]

/-- Indicator is 0 or 1 -/
theorem indicator_nonneg : (0 : FinRV Ω R) ≤ 𝕀∘B := by
    intro ω; unfold 𝕀 indicator; by_cases h : B ω; repeat simp [h]

theorem indicator_le_one : (𝕀∘B : FinRV Ω R) ≤ 1 :=
    by unfold 𝕀 indicator; intro ω; by_cases h : B ω; repeat simp [h]

variable {c : R} {X : FinRV Ω R}

omit [Nonempty Ω] in
theorem const_eq_smul_one : (fun _ ↦ c : FinRV Ω R)  = c • 1 := by ext; simp;

theorem eq_sum_mul_indicatorEq (X : FinRV Ω R) (L : FinRV Ω (Fin k)) : X = ∑ i, X * (L =ᵢ i) := by ext ω; simp

omit [Nonempty Ω] in
theorem indicator_one : 𝕀 ∘ (1 : Ω → Bool) = (1 : Ω → R) := by ext; simp [𝕀, indicator]

theorem add_not_eq_one : B + (¬ᵣ B) = (1 : FinRV Ω Bool) := by ext ω; unfold FinRV.not; simp

theorem indicator_add_indicator_not_eq_one : (𝕀∘B) + (𝕀∘(¬ᵣ B)) = (1 : FinRV Ω R) :=
    by ext ω; unfold FinRV.not 𝕀 indicator Bool.not
       by_cases h : B ω <;> simp [h]

variable {X Y: FinRV Ω R} {Xs : Fin k → FinRV Ω R}

theorem rv_le_abs : X ≤ abs ∘ X := le_abs_self X

theorem rv_prod_sum_additive  : ∑ i, Y * (Xs i) = Y * (∑ i, Xs i) := Eq.symm (Finset.mul_sum Finset.univ Xs Y)

variable {g : Fin k → R}

theorem comp_mul_indicatorEq (i) : (g ∘ L) * (L =ᵢ i) = (g i) • (L =ᵢ i) := 
    by ext ω; by_cases h : L ω = i <;> simp [h] 

variable {β : Type}  -- general type, but different from the scalar type; could be an integer or categorical

-- assume enumerability of Ω from here because we need a probability space
variable [FinEnum Ω] [LinearOrder β]

@[to_dual] -- minQuark
def maxQuark (X : FinRV Ω β) : β := X.quarks.max' quarks_nonempty

variable {X : FinRV Ω β}

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

variable {Ω : Type} [Nonempty Ω] [FinEnum Ω] (P : Findist R Ω) (B C : FinRV Ω Bool)

/-- Probability of B -/
def probability : R :=  P.p ⬝ᵥ (𝕀 ∘ B)

/-- Probability of B -/
notation "ℙ[" B "//" P "]" => probability P B

/-- Conditional probability of B on C -/
def probabilityCond : R := ℙ[B * C // P] / ℙ[ C // P ]

/-- Conditional probability of B on C -/
notation "ℙ[" B "|" C "//" P "]" => probabilityCond P B C

/-- Elements of Ω with positive probability  -/
def support (P : Findist R Ω) : Finset Ω := Finset.univ.filter (fun ω => P.p ω > 0)

/-- Values of X with positive probability -/
def atoms (P : Findist R Ω) (X : FinRV Ω R) : Finset R := P.support.image X

theorem probability_one : ℙ[1 // P] = 1 :=
    by rewrite [probability, indicator_one, dotProduct_comm]
       exact P.sum_eq_one

example {a b : R} (h : 0 ≤ a) (h2 : 0 ≤ b) : 0 ≤ a * b :=  mul_nonneg h h2

variable {P : Findist R Ω} {B : FinRV Ω Bool}

theorem probability_congr {A : FinRV Ω Bool} (h : A = B) : ℙ[A // P] = ℙ[B // P] := congrArg (probability P) h

theorem mul_eq_zero_of_probability_eq_zero (h : ℙ[B // P] = 0) : (P.p * (𝕀∘B) = 0) := by
    exact Matrix.mul_eq_zero_of_dotProduct_eq_zero P.nonneg indicator_nonneg h

------------------------------ IsPMF ---------------------------

/-- Proof that p is a the IsPMF of X on probability space P -/
def IsPMF {K : ℕ} (pmf : Fin K → R) (P : Findist R Ω) (L : FinRV Ω (Fin K)) :=
    ∀ k : Fin K, pmf k = ℙ[ L =ᵣ k // P]

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] {k : ℕ}  {L : FinRV Ω (Fin k)}
variable {pmf : Fin k → R} {P : Findist R Ω}

theorem IsPMF.pos (h : IsPMF pmf P L)  : 0 < k :=
  match k with  
  | Nat.zero => Fin.pos <| L P.nonempty.some
  | Nat.succ k₂ => Nat.zero_lt_succ k₂

end Probability

------------------------------ CDF ----------------------

section CDF

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω]

def cdf (P : Findist R Ω) (X : FinRV Ω R) (t : R) : R := ℙ[X ≤ᵣ t // P]

variable {P : Findist R Ω} {X Y : FinRV Ω R} {t t₁ t₂ : R}


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

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] (P : Findist R Ω) (X Y Z: FinRV Ω R) (B : FinRV Ω Bool)

/-- Standard expectation operator -/
def expect : R := P.p ⬝ᵥ X

/-- Default expectation operator -/
notation "𝔼[" X "//" P "]" => expect P X


theorem probability_eq_expect_indicator : ℙ[B // P] = 𝔼[(𝕀 ∘ B : FinRV Ω R) // P] := by simp only [expect, probability]

/-- Conditional expectation operator -/
def expectCond : R := 𝔼[ X * (𝕀 ∘ B) // P] / ℙ[ B // P]

/-- Conditional expectation operator -/
notation "𝔼[" X "|" B "//" P "]" => expectCond P X B

variable {k : ℕ} (L : FinRV Ω (Fin k))

/-- Expectation conditioned on a random variable. It creates a random variable -/
def expectCondRV : Ω → R := fun i ↦ 𝔼[ X | L =ᵣ (L i) // P ]

/-- Expectation conditioned on a random variable. It creates a random variable -/
notation "𝔼[" X "|ᵣ" L "//" P "]" => expectCondRV P X L

--- some basic properties

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] {P : Findist R Ω} {X Y Z: FinRV Ω R} {B : FinRV Ω Bool}

theorem expect_congr (h : X = Y) : 𝔼[X // P] = 𝔼[Y // P] := congrArg (expect P) h

theorem expect_mul_comm : 𝔼[X * Y // P] = 𝔼[Y * X // P] := expect_congr (mul_comm X Y)

variable {c : R} {p : Ω → R}

theorem expect_const : 𝔼[(fun _ ↦ c) // P] = c := by 
  rw [const_eq_smul_one,expect, dotProduct_smul,smul_eq_mul,dotProduct_comm,P.sum_eq_one,mul_one]

theorem expect_one : 𝔼[ 1 // P] = 1 := expect_const
       
/-- Expectation is homogeneous under product -/
theorem expect_smul : 𝔼[c • X // P] = c * 𝔼[X // P] := by rw [expect, expect, Matrix.dotProduct_smul']

theorem expect_const_mul : 𝔼[(fun _ ↦ c) * X // P] = c * 𝔼[X // P] := by rw [const_mul_eq_smul, expect_smul]

variable {k : ℕ} {g : Fin k → R}  {L : FinRV Ω (Fin k)}

theorem expect_indicatorEq (i) : 𝔼[(L =ᵢ i : FinRV Ω R) // P] = 𝔼[(𝕀 ∘ (L =ᵣ i) : FinRV Ω R) // P] := by rw [indicator_comp_eq_indicatorEq]

/-- Additivity of expectation --/
theorem expect_sum {m : ℕ} (Xs : Fin m → FinRV Ω R) : 
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
    (h : ∀ ω, A ω → B ω) : (𝕀∘A : FinRV Ω R) ≤ (𝕀∘B) := by
  intro ω
  specialize h ω
  by_cases h1 : A ω
  · simp_all [indicator] 
  · by_cases h2 : B ω
    repeat simp_all [indicator]

end FinRV

end Probability_properties 
