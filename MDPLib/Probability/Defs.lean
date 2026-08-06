import MDPLib.Probability.Prelude

import Mathlib.Data.FinEnum -- finitely-enumerable sample spaces
import Mathlib.Data.Matrix.Mul  -- dot product definitions and results
import Mathlib.Algebra.Notation.Pi.Defs -- operations on functions
import Mathlib.Algebra.Module.PointwisePi -- for smul_pi
import Mathlib.LinearAlgebra.Matrix.DotProduct -- for monotonicity


----------- Generic results -----------------

theorem bool_ineq {a b : Bool} (h : a → b) : (a ≤ b) := h

theorem bool_eq {a b : Bool} (h1 : a → b) (h2 : b → a) : a = b := Bool.le_antisymm h1 h2

--------------------------- Findist ---------------------------------------------------------------


variable {Ω : Type} [FinEnum Ω]


-- TODO: do we even need to assume that Ω is finitely enumerable when defining the probability space?

/-- Finite probability distribution over a finitely-enumerable sample space `Ω`. -/
structure Findist (Ω : Type) [FinEnum Ω] : Type where
    /-- Probability measure -/
    p : Ω → ℚ
    prob : 1 ⬝ᵥ p = 1
    nneg : 0 ≤ p


namespace Findist

/-- Finite probability distribution  -/
abbrev Delta (Ω : Type) [FinEnum Ω] : Type := Findist Ω

/-- Finite probability distribution  -/
abbrev Δ (Ω : Type) [FinEnum Ω] : Type := Delta Ω

/-- Dirac (point mass) distribution concentrated at `ω₀`. -/
def dirac (ω₀ : Ω) : Findist Ω where
    p    := fun ω => if ω = ω₀ then 1 else 0
    prob := by simp [dotProduct]
    nneg := by intro ω; by_cases h : ω = ω₀ <;> simp [h]

/-- The sample space of a probability distribution is nonempty. -/
theorem nonempty (P : Findist Ω) : Nonempty Ω := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := P.prob
  simp_all only [Matrix.dotProduct_of_isEmpty, zero_ne_one]

/-- A distribution over an empty sample space is impossible. -/
theorem nonempty' [IsEmpty Ω] (P : Findist Ω) : False :=
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
- L =ᵢ i is a ℚ indicator random variable
- L ≤ᵣ i is a bool indicator random variable

Main results

- Hadamard product is linear:  Y * (∑ i, Xs i) = ∑ i, Y * (Xs i)
-/


section RandomVariable

/-- A finite random variable: a bare function from the sample space `Ω` to `ρ`.
    The `FinEnum` instance lives on `Ω` and is shared with the distribution function, so
    a random variable never carries its own enumeration. -/
abbrev FinRV (Ω : Type) (ρ : Type) := Ω → ρ


variable {Ω : Type}  {ρ : Type}

namespace FinRV

-- for convenience define operations on bools
instance instBoolMul : Mul Bool where mul a b := Bool.and a b
instance instBoolAdd: Add Bool  where add a b := Bool.or a b
instance instBoolZero : Zero Bool where zero := false
instance instBoolOne : One Bool where one := true

variable {A B : Bool}

@[simp] theorem one_eq_true : (1:Bool) = true := rfl
@[simp] theorem zero_eq_false : (0:Bool) = false := rfl
@[simp] theorem bool_sum_or : A + B = Bool.or A B := rfl
@[simp] theorem bool_prod_and : A * B = Bool.and A B := rfl


/-- Negates a random variable -/
@[simp] def not (B : FinRV Ω Bool) : FinRV Ω Bool :=
  fun ω ↦ (B ω).not

/-- Negates a random variable -/
prefix:40 "¬ᵣ" => FinRV.not

/-- Boolean random variable representing an quality condition -/
@[simp] def eq [DecidableEq ρ] (Y : FinRV Ω ρ) (y : ρ) : FinRV Ω Bool :=
  (fun ω ↦ decide (Y ω = y) )

/-- Boolean random variable representing an quality condition -/
infix:50 "=ᵣ" => FinRV.eq

/-- 0/1 random variable representing an quality condition -/
@[simp] def eqi [DecidableEq ρ] (Y : FinRV Ω ρ) (y : ρ) : FinRV Ω ℚ :=
  (fun ω ↦ if Y ω = y then 1 else 0)

/-- 0/1 random variable representing an quality condition -/
infix:50 "=ᵢ" => FinRV.eqi

/-- Boolean random variable represening Y ≤ y inequality -/
@[simp] def leq [LE ρ] [DecidableLE ρ] (Y : FinRV Ω ρ) (y : ρ) : FinRV Ω Bool :=
  (fun ω ↦ Y ω ≤ y)

/-- Boolean random variable represening Y ≤ y inequality -/
infix:50 "≤ᵣ" => FinRV.leq


/-- Boolean random variable represening Y ≤ y inequality -/
@[simp] def lt [LT ρ] [DecidableLT ρ] (Y : FinRV Ω ρ) (y : ρ) : FinRV Ω Bool :=
  (fun ω ↦ Y ω < y)

/-- Boolean random variable represening Y ≤ y inequality -/
infix:50 "<ᵣ" => FinRV.lt

/-- Boolean random variable represening Y ≤ y inequality -/
@[simp] def geq [LE ρ] [DecidableLE ρ] (Y : FinRV Ω ρ) (y : ρ) : FinRV Ω Bool :=
  (fun ω ↦ Y ω ≥ y)

/-- Boolean random variable represening Y ≤ y inequality -/
infix:50 "≥ᵣ" => FinRV.geq

/-- Boolean random variable represening Y > y inequality -/
@[simp] def gt [LT ρ] [DecidableLT ρ] (Y : FinRV Ω ρ) (y : ρ) : FinRV Ω Bool :=
  fun ω ↦ Y ω > y

/-- Boolean random variable represening Y > y inequality -/
infix:50 ">ᵣ" => FinRV.gt


/-- Equivalence when adding an element to integer comparison. -/
theorem le_of_le_eq (D : FinRV Ω ℕ) (m : ℕ) : ((D ≤ᵣ m) + (D =ᵣ m.succ)) = (D ≤ᵣ m.succ) := by
  have exclusion {a b : ℕ} (h : a > b + 1) : (a > b) ∧ ¬(a = b + 1) := 
  ⟨ Nat.lt_of_succ_lt h, Ne.symm (Nat.ne_of_lt h) ⟩
  funext x 
  unfold FinRV.leq FinRV.eq instHAdd Add.add Pi.instAdd
  rw [Pi.add_apply, bool_sum_or]
  by_cases h : D x ≤ m.succ
  · simp [h, Nat.le_or_eq_of_le_succ]
  · simp [h, exclusion (Nat.not_le.mp h) ] 

/-- Defines a preimage of an RV. This is a set with a decidable membership. -/
def preimage (f : FinRV Ω ρ) : ρ → Set Ω :=
  fun t => { m : Ω | f m  = t}

end FinRV

/-- Boolean indicator function -/
def indicator  [OfNat ℚ 0] [OfNat ℚ 1] (cond : Bool) : ℚ := cond.rec 0 1

/-- Boolean indicator function -/
abbrev 𝕀 [OfNat ℚ 0] [OfNat ℚ 1] : Bool → ℚ := indicator


variable {k : ℕ} {L : FinRV Ω (Fin k)}

theorem indi_eq_indr : ∀i : Fin k, (𝕀 ∘ (L =ᵣ i)) = (L =ᵢ i) := by
  intro i; unfold FinRV.eq FinRV.eqi 𝕀 indicator; ext ω; by_cases h: L ω = i; repeat simp [h]

variable {B : FinRV Ω Bool}
/-- Indicator is 0 or 1 -/
theorem ind_zero_one : ∀ ω, (𝕀∘B) ω = 1 ∨ (𝕀∘B) ω = 0 := by
    intro ω
    by_cases h : B ω
    · left; simp only [Function.comp_apply, h, indicator]
    · right; simp only [Function.comp_apply, h, indicator]

/-- Indicator is 0 or 1 -/
theorem ind_nneg : (0 : FinRV Ω ℚ) ≤ 𝕀∘B := by
    intro ω; unfold 𝕀 indicator; by_cases h : B ω; repeat simp [h]

theorem ind_le_one : 𝕀∘B ≤ (1 : FinRV Ω ℚ) :=
    by unfold 𝕀 indicator; intro ω; by_cases h : B ω; repeat simp [h]

variable {c : ℚ} {X : FinRV Ω ℚ}

theorem rv_const_fun_to_one : (fun _ ↦ c : FinRV Ω ℚ)  = c • 1 := by ext; simp;

theorem rv_decompose (X : FinRV Ω ℚ) (L : FinRV Ω (Fin k)) : X = ∑ i, X * (L =ᵢ i) := by ext ω; simp

theorem one_of_true : 𝕀 ∘ (1 : Ω → Bool) = (1 : Ω → ℚ) := by ext; simp [𝕀, indicator]

theorem one_of_bool_or_not : B + (¬ᵣ B) = (1 : FinRV Ω Bool) := by ext ω; unfold FinRV.not; simp

theorem one_of_ind_bool_or_not : (𝕀∘B) + (𝕀∘(¬ᵣ B)) = (1 : FinRV Ω ℚ) :=
    by ext ω; unfold FinRV.not 𝕀 indicator not
       by_cases h : B ω <;> simp [h]

variable {X Y: FinRV Ω ℚ} {Xs : Fin k → FinRV Ω ℚ}

theorem rv_le_abs : X ≤ abs ∘ X := by intro i; simp [le_abs_self (X i)]

theorem rv_prod_sum_additive  : ∑ i, Y * (Xs i) = Y * (∑ i, Xs i) :=
    by ext ω; simp [Finset.mul_sum]

variable {g : Fin k → ℚ}

theorem rv_prod_const : ∀i, (g ∘ L) * (L =ᵢ i) = (g i) • (L =ᵢ i) := 
    by intro i; ext ω; by_cases h : L ω = i <;> simp [h] 

variable {β : Type}


-- assume enumerability of Ω from here because we need a probability space
variable [FinEnum Ω]

theorem rv_image_nonempty  [DecidableEq β] [LinearOrder β] (P : Findist Ω) (X : FinRV Ω β)  :
    (Finset.univ.image X).Nonempty :=
  have : Nonempty Ω := P.nonempty
  Finset.image_nonempty.mpr Finset.univ_nonempty

def FinRV.min [DecidableEq β] [LinearOrder β] (P : Findist Ω) (X : FinRV Ω β) : β :=
  (Finset.univ.image X).min' (rv_image_nonempty P X)

def FinRV.max [DecidableEq β] [LinearOrder β] (P : Findist Ω) (X : FinRV Ω β) : β :=
  (Finset.univ.image X).max' (rv_image_nonempty P X)

variable {X : FinRV Ω ℚ}


theorem rv_omega_le_max (P : Findist Ω) : ∀ω, X ω ≤ (FinRV.max P X) := by 
       intro ω
       have h : X ω ∈ (Finset.image X Finset.univ) := Finset.mem_image_of_mem X (Finset.mem_univ ω)
       exact Finset.le_max' (Finset.image X Finset.univ) (X ω) h


end RandomVariable

------------------------------ Probability ---------------------------
section Probability 

variable {Ω : Type} [FinEnum Ω] (P : Findist Ω) (B C : FinRV Ω Bool)

/-- Probability of B -/
def probability : ℚ :=  P.p ⬝ᵥ (𝕀 ∘ B)

/-- Probability of B -/
notation "ℙ[" B "//" P "]" => probability P B

/-- Conditional probability of B on C -/
def probability_cnd : ℚ := ℙ[B * C // P] / ℙ[ C // P ]

/-- Conditional probability of B on C -/
notation "ℙ[" B "|" C "//" P "]" => probability_cnd P B C


theorem prob_one_of_true : ℙ[1 // P] = 1 :=
    by rewrite [probability, one_of_true, dotProduct_comm]
       exact P.prob

example {a b : ℚ} (h : 0 ≤ a) (h2 : 0 ≤ b) : 0 ≤ a * b :=  Rat.mul_nonneg h h2

variable {P : Findist Ω} {B : FinRV Ω Bool}

theorem prod_zero_of_prob_zero : ℙ[B // P] = 0 → (P.p * (𝕀∘B) = 0) := by
    intro h; exact prod_eq_zero_of_nneg_dp_zero P.nneg ind_nneg h

------------------------------ PMF ---------------------------

/-- Proof that p is a the PMF of X on probability space P -/
def PMF {K : ℕ} (pmf : Fin K → ℚ) (P : Findist Ω) (L : FinRV Ω (Fin K)) :=
    ∀ k : Fin K, pmf k = ℙ[ L =ᵣ k // P]


variable {Ω : Type} [FinEnum Ω] {k : ℕ}  {L : FinRV Ω (Fin k)}
variable {pmf : Fin k → ℚ} {P : Findist Ω}

theorem pmf_rv_k_ge_1 (h : PMF pmf P L)  : 0 < k :=
  match k with  
  | Nat.zero => Fin.pos <| L P.nonempty.some
  | Nat.succ k₂ => Nat.zero_lt_succ k₂

end Probability

------------------------------ CDF ----------------------

section CDF

variable {Ω : Type} [FinEnum Ω]

def cdf (P : Findist Ω) (X : FinRV Ω ℚ) (t : ℚ) : ℚ := ℙ[X ≤ᵣ t // P]

variable {P : Findist Ω} {X Y : FinRV Ω ℚ} {t t₁ t₂ : ℚ}


end CDF

------------------------------ Expectation ----------------------

/-!
Definitions and main properties of the expectation operator

Main results
  - Monotonicity of expectations 
  - Correspondence between expectations and probabilities (indicator functions)
  - Decomposition with a discrete random variables, used in the proofs of LOTUS and TLE
-/

variable {Ω : Type} [FinEnum Ω] (P : Findist Ω) (X Y Z: FinRV Ω ℚ) (B : FinRV Ω Bool)

/-- Standard expectation operator -/
def expect : ℚ := P.p ⬝ᵥ X

/-- Standard expectation operator -/
notation "𝔼[" X "//" P "]" => expect P X

--theorem exp_eq_correct : 𝔼[X // P] = ∑ v ∈ ((List.finRange P.length).map X).toFinset, v * ℙ[ X =ᵣ v // P]

theorem prob_eq_exp_ind : ℙ[B // P] = 𝔼[𝕀 ∘ B // P] := by simp only [expect, probability]

/-- Conditional expectation operator -/
def expect_cnd : ℚ := 𝔼[ X * (𝕀 ∘ B) // P] / ℙ[ B // P]

/-- Conditional expectation operator -/
notation "𝔼[" X "|" B "//" P "]" => expect_cnd P X B

variable {k : ℕ} (L : FinRV Ω (Fin k))

/-- Expectation conditioned on a random variable. It creates a random variable -/
def expect_cnd_rv : Ω → ℚ := fun i ↦ 𝔼[ X | L =ᵣ (L i) // P ]

/-- Expectation conditioned on a random variable. It creates a random variable -/
notation "𝔼[" X "|ᵣ" L "//" P "]" => expect_cnd_rv P X L

--- some basic properties

section Expectation_properties
variable {P : Findist Ω} {X Y Z: FinRV Ω ℚ} {B : FinRV Ω Bool}

theorem exp_congr : (X = Y) → 𝔼[X // P] = 𝔼[Y // P] :=
  by intro h
     unfold expect dotProduct
     apply Fintype.sum_congr
     simp_all


theorem exp_mul_comm : 𝔼[X * Y // P] = 𝔼[Y * X // P] := exp_congr (CommMonoid.mul_comm X Y)

variable {c : ℚ} {p : Ω → ℚ}

theorem exp_const : 𝔼[(fun _ ↦ c) // P] = c :=
  by unfold expect
     rw [rv_const_fun_to_one]
     simp only [dotProduct_smul, smul_eq_mul]
     rw [dotProduct_comm, P.prob]
     simp

theorem exp_one : 𝔼[ 1 // P] = 1  := exp_const

theorem exp_cond_eq_def  : 𝔼[X | B // P] * ℙ[B // P] = 𝔼[X * (𝕀 ∘ B) // P] :=
  by unfold expect_cnd 
     by_cases h: ℙ[B//P] = 0
     · rw [h, Rat.mul_zero, expect,dotProd_hadProd_comm, dotProd_hadProd_rotate, prod_zero_of_prob_zero h]
       exact (dotProduct_zero X).symm 
     · simp_all 

theorem exp_prod_const_fun : 𝔼[(λ _ ↦ c) * X // P] = c * 𝔼[X // P] := by 
  have constant_mul_eq_smul : (fun ω ↦ c * X ω) = c • X := rfl 
  simp only [expect, Pi.mul_def, constant_mul_eq_smul, dotProduct_smul, smul_eq_mul]

theorem exp_indi_eq_exp_indr : ∀i : Fin k, 𝔼[L =ᵢ i // P] = 𝔼[𝕀 ∘ (L =ᵣ i) // P] := by
  intro i; rw [indi_eq_indr]

/-- Expectation is homogeneous under product -/
theorem exp_homogenous : 𝔼[c • X // P] = c * 𝔼[X // P] := by simp only [expect, dotProduct_smul, smul_eq_mul]

/-- Additivity of expectation --/
theorem exp_additive {m : ℕ} (Xs : Fin m → FinRV Ω ℚ) : 𝔼[∑ i : Fin m, Xs i // P] = ∑ i : Fin m, 𝔼[Xs i // P] := 
  by unfold expect; exact dotProduct_sum P.p Finset.univ Xs
     
theorem exp_additive_two : 𝔼[X + Y // P] = 𝔼[X // P] + 𝔼[Y // P] := by simp [expect]

/-- Expectation is monotone  -/
theorem exp_monotone (h: X ≤ Y)  : 𝔼[X // P] ≤ 𝔼[Y // P] := dotProduct_le_dotProduct_of_nonneg_left h P.nneg

---- ** conditional expectation -----

variable {k : ℕ} {g : Fin k → ℚ} {L : FinRV Ω (Fin k)} 

theorem exp_decompose : 𝔼[X // P] = ∑ i, 𝔼[X * (L =ᵢ i) // P] := 
  by nth_rewrite 1 [rv_decompose X L]
     rw [exp_additive]

/-- Expectation of a conditional constant. Only when probability is positive.  -/
theorem exp_cond_const : ∀ i, ℙ[L =ᵣ i //   P] ≠ 0 → 𝔼[g ∘ L | L =ᵣ i // P] = g i := 
    by intro i h 
       unfold expect_cnd
       rw [indi_eq_indr, rv_prod_const i, exp_homogenous]
       rw [←indi_eq_indr, ←prob_eq_exp_ind]
       simp only [h, ne_eq, isUnit_iff_ne_zero, not_false_eq_true, IsUnit.mul_div_cancel_right]

end Expectation_properties

-- Derived properties from the properties of expectation
section Probability_properties

variable {n : ℕ} {P : Findist Ω} {A B : FinRV Ω Bool}

theorem ind_monotone : (∀ ω, A ω → B ω) → (𝕀∘A) ≤ (𝕀∘B) := by
  intro h ω
  specialize h ω
  by_cases h1 : A ω
  · simp_all [indicator] 
  · by_cases h2 : B ω
    repeat simp_all [indicator]

end Probability_properties 
