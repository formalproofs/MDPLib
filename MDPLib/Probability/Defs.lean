import MDPLib.Probability.Prelude

import Mathlib.Data.FinEnum -- finitely-enumerable sample spaces
import Mathlib.Data.Matrix.Mul  -- dot product definitions and results
import Mathlib.Algebra.Notation.Pi.Defs -- operations on functions
import Mathlib.Algebra.Module.PointwisePi -- for smul_pi
import Mathlib.LinearAlgebra.Matrix.DotProduct -- for monotonicity

set_option linter.unusedSectionVars false

-- The scalar type: any linear ordered field (see `MDPLib/Probability/Prelude.lean`).
-- the particular targets are: ℚ for computability and ℝ for proofs
variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [CharZero R] [Archimedean R]


--------------------------- Findist ---------------------------------------------------------------

/-
NOTE(mathlib): **Mathlib's measure theory is not a source of proofs for this library.**
Audited 2026-09-13; recording the result so the question is not re-opened.

Three independent obstructions, any one of which is fatal:

1. Nothing in that stack is computable, so routing a definition through it would lose `#eval`
   at `ℚ` -- the property this library exists to have.
     `Measure`      -- `MeasureTheory/Measure/MeasureSpaceDef.lean:77`, in `noncomputable section`
     `IsPMF`          -- `Probability/ProbabilityMassFunction/Basic.lean:44`,
                       `{f : α → ℝ≥0∞ // HasSum f 1}` (so `tsum`, even on a `Fintype`)
     `lintegral`    -- `MeasureTheory/Integral/Lebesgue/Basic.lean:48`, a
                       `noncomputable irreducible_def`
     `integral` (∫) -- `MeasureTheory/Integral/Bochner/Basic.lean:158`, `open scoped Classical in`
   The root cause is `Real` itself (`noncomputable` `linearOrder` / `instField` / `decidableLT`,
   `Basic/Real/Basic.lean:491,501,521`), inherited by `ℝ≥0` and then `ℝ≥0∞` -- whose
   *multiplication* is noncomputable (`Basic/ENNReal/Basic.lean:141`). Every `Repr` in the
   chain is `unsafe`.

2. Nothing in it is generic in the scalar. Measures are `ℝ≥0∞`-valued; Bochner `∫` requires
   `[NormedAddCommGroup E] [NormedSpace ℝ E]` and every usable lemma adds `[CompleteSpace E]`.
   `ℚ` is none of those. There is no integral in Mathlib over an arbitrary ordered field: the
   most general object, `setToSimpleFunc` (`MeasureTheory/Integral/FinMeasAdditive.lean:295`),
   still works with `F →L[ℝ] F'`. So a measure-theoretic proof yields a theorem *about `ℝ`*,
   and there is no transfer to the `R` this library is stated over.

3. The statements largely are not there. `quantile`, `VaR`, `CVaR`, `valueAtRisk` and
   `expectedShortfall` have **zero** occurrences in Mathlib, so `Probability/Quantile.lean` and
   `Risk/VaR.lean` have no counterpart at all. Of this library's ~198 theorems only ~8
   (`expect_sum`, `expect_mono`, `expect_smul`, `prob_compl_sums_to_one`, `LOTUS`,
   `law_total_exp`, `law_of_total_probs`, `in_prob`) have a measure-theoretic analogue -- and
   each is already a one- to three-line proof here. The rest are comparison-event lemmas
   (`prob_f_*`, `prob_*_cashinvar`, `rv_f_*`) and finite image/list machinery, which measure
   theory does not develop even for `ℝ`.

What measure theory *is* good for, if ever wanted: as a **target** at `R = ℝ`. A bridge
`Findist ℝ Ω → IsPMF Ω` (`IsPMF.ofFintype`, `Constructions.lean:204`) plus
`IsPMF.integral_eq_sum` (`ProbabilityMassFunction/Integrals.lean:47`) would identify `𝔼` with `∫`
and make Mathlib's deep results (`condExp`, martingales, CLT, concentration) importable. That
belongs in its own file; it derives nothing that is already proved here.

The reusable Mathlib API for finite probability is *algebraic*, not measure-theoretic, and is
harvested in `MDPLib/Probability/Convexity.lean` via `Finset.centerMass`.
-/


/-- Finite probability distribution over a finitely-enumerable sample space `Ω`. -/
-- NOTE(mathlib): Mathlib's `StdSimplex R Ω` (`Mathlib/Geometry/Convex/ConvexSpace/Defs.lean:56`)
-- is the same object (`weights` / `nonneg` / `total`), and `StdSimplex.nonempty` duplicates
-- `Findist.nonempty` below. We deliberately do NOT switch: `StdSimplex` is `Finsupp`-backed,
-- whereas this library is built throughout on plain functions and `⬝ᵥ`.
-- Re-audited 2026-09-13, decision unchanged, with these additions:
--  * confirmed `Finsupp`-backed -- the field is literally `weights : X →₀ R` (`Defs.lean:58`).
--  * `StdSimplex.range_toFun_comp_weights` (`Defs.lean:101`) states
--    `Set.range (·.weights) = (⋂ i, {s | 0 ≤ s i}) ∩ {s | ∑ i, s i = 1}` -- i.e. exactly this
--    structure's carrier. That is the bridge to use if we ever do want to interoperate.
--  * the *plain-function* simplex `stdSimplex : Set (ι → 𝕜)`
--    (`Mathlib/Analysis/Convex/StdSimplex.lean:39`) would have matched `Findist` directly, but
--    is DEPRECATED since 2026-08-29 in favour of the `Finsupp` one. Worth knowing before any
--    future migration: plain functions are the representation Mathlib is moving away from.
--
-- The decision is not merely a preference -- **switching is not possible without giving up
-- computability at `ℚ`**, which is this library's reason for existing. Evidence:
--
--  1. `Finsupp` is a noncomputable theory BY DECLARATION. `Mathlib/Data/Finsupp/Defs.lean:68`:
--     "This file is a `noncomputable theory` and uses classical logic throughout", with
--     `noncomputable section` at `:80`. The classical choice is welded into the *bodies*, not
--     exposed as instance arguments -- `onFinsetSupport` (`Defs.lean:231`) is
--     `haveI := Classical.decEq M; {a ∈ s | f a ≠ 0}` -- so no instance you supply can recover
--     it. Verified at `ℚ` over `Fin 3`: `Finsupp.mk`, `.support` and `Finsupp.sum` evaluate,
--     but `f + f` ("`Finsupp.instAdd` is noncomputable"), `(2:ℚ) • f`
--     ("`Finsupp.smulZeroClass`"), `Finsupp.single`, `Finsupp.onFinset` and
--     `Finsupp.equivFunOnFinite` all fail to compile. `#synth DecidableLE (Fin 3 →₀ ℚ)` also
--     fails: `Finsupp.decidableLE` (`Order.lean:245`) is gated on `[CanonicallyOrderedAdd α]`
--     (`:224`), which `ℚ` is not.
--  2. `StdSimplex` inherits this. `Mathlib/Geometry/Convex/ConvexSpace/Defs.lean:38` is
--     `@[expose] public noncomputable section`, covering `single`, `map`, `join`, `restrict`,
--     `iConvexComb`, `convexCombPair`. Even reading one coordinate,
--     `(s : StdSimplex ℚ (Fin 3)).weights 0`, is noncomputable -- `Finsupp.instFunLike` is.
--     This is the same test `IsPMF`/`Measure`/`ENNReal` failed in the block above, for the same
--     structural reason.
--  3. It would buy almost nothing anyway. `StdSimplex` is convex geometry, not probability:
--     no expectation monotonicity, no probability of an event, no indicators, no CDF, no
--     comparison events, no conditional expectation, no law of total probability, no products
--     or independence. ~190 of this library's ~198 theorems get no help. There is no `bind`
--     and no `Monad` instance either -- the module docstring calls `StdSimplex` a monad, but
--     `join`'s laws (`Defs.lean:307,311,315`) are `private`. Switching would additionally
--     *lose* the `Finset.centerMass` connection harvested in `Probability/Convexity.lean`:
--     that bridge was deprecated with "no replacement"
--     (`Mathlib/Analysis/Convex/StdSimplex.lean:458`).
--
-- Note also that "switch to `Finsupp` throughout" is the wrong granularity: only the
-- *distribution* is a candidate. `FinRV`, `MDP.r`, `DMRP.r`, value vectors and
-- `ProbabilityMatrix.P` are plain functions whose zero values carry no special meaning, and
-- over a `FinEnum Ω` we have `Ω →₀ R ≃ (Ω → R)`, so the `support` field is pure overhead --
-- zero-probability outcomes are ordinary and need no tracking. `Finsupp` earns its keep only
-- when the index is infinite; see the note on `Hist` in `MDPLib/MDP/Histories.lean`.
--
-- Maturity caveat, if this is ever revisited: `Convexity.StdSimplex` is four months old
-- (first commit 2026-05-11), still churning (18 commits since June, latest 2026-09-04 -- nine
-- days before our pin), with in-file renames already deprecated
-- (`convexCombination -> sConvexComb`, `convexComboPair -> convexCombPair`) and an open

-- `FIXME` at `Defs.lean:379`. Outside its own directory it has about five real dependents.
--
-- What we do instead: a one-way, proof-layer bridge in `MDPLib/Probability/StdSimplex.lean`
-- (`Findist.toStdSimplex`), which makes Mathlib's convexity/affine/compactness machinery
-- available without touching the computable core.


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

section General

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

end General

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

-- for convenience define operations on bools
-- WARNING: these four instances shadow Mathlib's global `Bool` algebra.
-- `Mathlib/Algebra/Ring/BooleanRing.lean:515,521` declares `Add Bool := xor` and
-- `Mul Bool := and` as part of `instance : BooleanRing Bool`, and :540 declares
-- `Bool.zero_eq_false`, which would collide by name with `zero_eq_false` below.
-- That file is NOT currently reachable from this import graph (checked: `BooleanRing` and
-- `Bool.zero_eq_false` are unknown constants here, and `#synth Add Bool` returns
-- `instAddBool`), so there is no ambiguity today -- but the moment anything pulls
-- `Mathlib.Algebra.Ring.BooleanRing` in, `+` on `Bool` becomes ambiguous between `or` and
-- `xor`, and `add_not_eq_one` / `leq_add_eq_succ` could change meaning.
-- If that happens: make these `scoped instance`s in the `FinRV` namespace, or drop them and
-- write `||` / `&&` explicitly.
instance instMulBool : Mul Bool where mul a b := Bool.and a b
instance instAddBool: Add Bool  where add a b := Bool.or a b
instance instZeroBool : Zero Bool where zero := false
instance instOneBool : One Bool where one := true

variable {A B : Bool}

@[simp] theorem one_eq_true : (1:Bool) = true := rfl
-- NOTE: name-clashes with Mathlib's `Bool.zero_eq_false` -- see the WARNING above.
@[simp] theorem zero_eq_false : (0:Bool) = false := rfl
@[simp] theorem add_eq_or : A + B = Bool.or A B := rfl
@[simp] theorem mul_eq_and : A * B = Bool.and A B := rfl


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
theorem leq_add_eq_succ (D : FinRV Ω ℕ) (m : ℕ) : ((D ≤ᵣ m) + (D =ᵣ m.succ)) = (D ≤ᵣ m.succ) := by
  have exclusion {a b : ℕ} (h : a > b + 1) : (a > b) ∧ ¬(a = b + 1) := 
  ⟨ Nat.lt_of_succ_lt h, Ne.symm (Nat.ne_of_lt h) ⟩
  funext x 
  unfold FinRV.leq FinRV.eq instHAdd Add.add Pi.instAdd
  rw [Pi.add_apply, add_eq_or]
  by_cases h : D x ≤ m.succ
  · simp [h, Nat.le_or_eq_of_le_succ]
  · simp [h, exclusion (Nat.not_le.mp h) ] 

/-- Defines a preimage of an RV. This is a set with a decidable membership. -/
def preimage (f : FinRV Ω ρ) : ρ → Set Ω :=
  fun t => { m : Ω | f m  = t}

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

theorem indicator_eq_one_or_eq_zero : (𝕀∘B : FinRV Ω R) ω = 1 ∨ (𝕀∘B : FinRV Ω R) ω = 0 := by
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

-- TODO(mathlib): = `le_abs_self X`. `Ω → ℚ` is a Pi lattice ordered group, so `|X|` is
-- pointwise and defeq to `abs ∘ X`. Verified: `le_abs_self X` closes this goal as stated.
theorem rv_le_abs : X ≤ abs ∘ X := by intro i; simp [le_abs_self (X i)]

-- TODO(mathlib): = `(Finset.mul_sum _ _ _).symm`
-- (`Mathlib/Algebra/BigOperators/Ring/Finset.lean:59`) applied directly in the Pi semiring
-- `Ω → ℚ` -- no pointwise `ext` needed.
theorem rv_prod_sum_additive  : ∑ i, Y * (Xs i) = Y * (∑ i, Xs i) :=
    by ext ω; simp [Finset.mul_sum]

variable {g : Fin k → R}

theorem comp_mul_indicatorEq (i) : (g ∘ L) * (L =ᵢ i) = (g i) • (L =ᵢ i) := 
    by ext ω; by_cases h : L ω = i <;> simp [h] 

variable {β : Type}


-- assume enumerability of Ω from here because we need a probability space
variable [FinEnum Ω] [DecidableEq β]

-- TODO(mathlib): = `Finset.univ_nonempty.image X` (`Mathlib/Data/Finset/BooleanAlgebra.lean:50`).
theorem image_univ_nonempty (X : FinRV Ω β) : (Finset.univ.image X).Nonempty :=
  Finset.image_nonempty.mpr Finset.univ_nonempty

-- NOTE(mathlib): already Mathlib-based (`Finset.min'`/`max'` on the image). An alternative
-- spelling is `Finset.univ.sup' Finset.univ_nonempty X`, which would make `le_max`
-- literally `Finset.le_sup' X (Finset.mem_univ ω)`
-- (`Mathlib/Data/Finset/Lattice/Fold.lean:564`), dually `Finset.inf'_le`. Cosmetic only.
protected def min [LinearOrder β] (X : FinRV Ω β) : β :=
  (Finset.univ.image X).min' (image_univ_nonempty X)

protected def max [LinearOrder β] (X : FinRV Ω β) : β :=
  (Finset.univ.image X).max' (image_univ_nonempty X)

variable {X : FinRV Ω R}

theorem le_max  (ω) : X ω ≤ (FinRV.max X) := by 
       have h : X ω ∈ (Finset.image X Finset.univ) := Finset.mem_image_of_mem X (Finset.mem_univ ω)
       exact Finset.le_max' (Finset.image X Finset.univ) (X ω) h

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


theorem probability_one : ℙ[1 // P] = 1 :=
    by rewrite [probability, indicator_one, dotProduct_comm]
       exact P.sum_eq_one

example {a b : R} (h : 0 ≤ a) (h2 : 0 ≤ b) : 0 ≤ a * b :=  mul_nonneg h h2

variable {P : Findist R Ω} {B : FinRV Ω Bool}

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

/-- Standard expectation operator -/
notation "𝔼[" X "//" P "]" => expect P X

--theorem exp_eq_correct : 𝔼[X // P] = ∑ v ∈ ((List.finRange P.length).map X).toFinset, v * ℙ[ X =ᵣ v // P]

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

-- TODO(mathlib): = `congrArg (expect P) h`. This is `congrArg`, nothing more.
theorem expect_congr (h : X = Y) : 𝔼[X // P] = 𝔼[Y // P] := by 
     unfold expect dotProduct
     apply Fintype.sum_congr
     simp_all


-- TODO(mathlib): `CommMonoid.mul_comm` is the unbundled field accessor; use `mul_comm X Y`.
theorem expect_mul_comm : 𝔼[X * Y // P] = 𝔼[Y * X // P] := expect_congr (CommMonoid.mul_comm X Y)

variable {c : R} {p : Ω → R}

theorem expect_const : 𝔼[(fun _ ↦ c) // P] = c := by 
  rw [const_eq_smul_one,expect, dotProduct_smul,smul_eq_mul,dotProduct_comm,P.sum_eq_one,mul_one]

theorem expect_one : 𝔼[ 1 // P] = 1 := expect_const
       
/-- Expectation is homogeneous under product -/
theorem expect_smul : 𝔼[c • X // P] = c * 𝔼[X // P] := by rw [expect, expect, Matrix.dotProduct_smul']

-- TODO: rename to exp_homogenous'
theorem expect_const_mul : 𝔼[(fun _ ↦ c) * X // P] = c * 𝔼[X // P] := by rw [const_mul_eq_smul,expect_smul]

variable {k : ℕ} {g : Fin k → R}  {L : FinRV Ω (Fin k)}

theorem expect_indicatorEq (i) : 𝔼[(L =ᵢ i : FinRV Ω R) // P] = 𝔼[(𝕀 ∘ (L =ᵣ i) : FinRV Ω R) // P] := by rw [indicator_comp_eq_indicatorEq]

/-- Additivity of expectation --/
theorem expect_sum {m : ℕ} (Xs : Fin m → FinRV Ω R) : 
    𝔼[∑ i : Fin m, Xs i // P] = ∑ i : Fin m, 𝔼[Xs i // P] := dotProduct_sum P.p Finset.univ Xs
     
-- TODO(mathlib): = `dotProduct_add P.p X Y` (`Mathlib/Data/Matrix/Mul.lean:124`).
theorem expect_add : 𝔼[X + Y // P] = 𝔼[X // P] + 𝔼[Y // P] := by simp [expect]

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

-- TODO(naming): `A` and `B` here are auto-bound implicits rather than section variables,
-- so the lemma is stated at a more general type than intended. Bind them explicitly.
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
