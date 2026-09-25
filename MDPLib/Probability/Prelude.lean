import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Tactic

import Mathlib.Logic.Function.Defs

-- The scalar type used throughout the library: any linear ordered field.
-- Instantiate at `ℚ` for computable results and at `ℝ` for the standard theory.
-- The whole class stack is carried uniformly; Lean auto-includes every instance binder
-- whenever `R` appears, so the `unusedSectionVars` linter is off in the numeric files.
set_option linter.unusedSectionVars false

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
         [CharZero R] [Archimedean R]


/-- states that p is a valid probability value -/
@[simp]
abbrev IsProb (p : R) : Prop := 0 ≤ p ∧ p ≤ 1

----------------- Section: Basic Probability -----------------------------------------------


namespace IsProb

variable {p x y : R}

@[simp]
theorem one_sub ( hp : IsProb p) : IsProb (1-p) := by
        simp_all only [ IsProb, sub_nonneg, tsub_le_iff_right, le_add_iff_nonneg_right, and_self]

@[simp]
theorem inv_one_sub_nonneg (hp : IsProb p) : 0 ≤ (1-p)⁻¹ := by
        simp_all only [IsProb, inv_nonneg, sub_nonneg]


-- NOTE: could use Convex.min_le_combo, ..., but that just comlicates the argument

theorem self_le_combo_of_le (hp : IsProb p) (h : x ≤ y) : x ≤ p * x + (1-p) * y := by
        have h2 := mul_le_mul_of_nonneg_left h hp.one_sub.1
        linarith

theorem self_le_combo_of_ge (hp : IsProb p) (h : y ≤ x) : y ≤ p * x + (1-p) * y := by
        have h2 := mul_le_mul_of_nonneg_left h hp.1
        linarith

theorem combo_le_self_of_ge (hp : IsProb p) (h : y ≤ x) : p * x + (1-p) * y ≤ x := by
        have h2 := mul_le_mul_of_nonneg_left h hp.one_sub.1
        linarith

theorem combo_le_self_of_le (hp : IsProb p) (h : x ≤ y) : p * x + (1-p) * y ≤ y := by
        have h2 : p * x ≤ p * y := mul_le_mul_of_nonneg_left h hp.1
        linarith

end IsProb


section FunctionalAnalysis


end FunctionalAnalysis

section dotProduct
namespace Matrix

variable {Ω : Type*} [Fintype Ω]
variable {x y z : Ω → R} {c : R}


theorem dotProduct_mul_rotate : x ⬝ᵥ (y * z) = z ⬝ᵥ (x * y) := by
  apply Fintype.sum_congr
  intro i
  rewrite [Pi.mul_apply y z i, Pi.mul_apply]
  ring

theorem dotProduct_mul_comm : x ⬝ᵥ (y * z) = x ⬝ᵥ (z * y) := congrArg (x ⬝ᵥ ·) (mul_comm y z)

#check smul_eq_mul
#check List.map_inj.mp rfl

theorem _root_.const_mul_eq_smul {X : Ω → R} : (fun _ ↦ c) * X = c • X := rfl

-- TODO(mathlib): a literal alias of Mathlib's `dotProduct_smul`; consider dropping it
-- and using the Mathlib name at call sites.
theorem dotProduct_smul' : x ⬝ᵥ (c • y) = c * x ⬝ᵥ y := dotProduct_smul c x y

theorem dotProduct_eq_one_dotProduct_mul : x ⬝ᵥ y = 1 ⬝ᵥ (x * y) := by simp [dotProduct]

theorem mul_eq_zero_of_dotProduct_eq_zero (hx : 0 ≤ x) (hy : 0 ≤ y) : x ⬝ᵥ y = 0 → x * y = 0 := by
  intro h
  rw [dotProduct_eq_one_dotProduct_mul] at h
  have := Left.mul_nonneg hx hy
  simp_all [dotProduct]
  exact (Fintype.sum_eq_zero_iff_of_nonneg this).mp h

theorem _root_.abs_mul_of_nonneg {a b : R} (h : 0 ≤ a) : |a * b| = a * |b| := by 
  rw [abs_mul, abs_of_nonneg h]

theorem abs_dotProduct_le_dotProduct_abs (p x : Ω → R) (hp : ∀ i, 0 ≤ p i) : |p ⬝ᵥ x| ≤ p ⬝ᵥ fun i => |x i| := by
  calc
    |∑ i : Ω, p i * x i| ≤ ∑ i, |p i * x i| := Finset.abs_sum_le_sum_abs (fun i ↦ p i * x i) Finset.univ
    _ = ∑ i, p i * |x i| := Finset.sum_congr rfl (fun i _ => abs_mul_of_nonneg (hp i))
    _ = p ⬝ᵥ fun i => |x i| := rfl

-- NOTE(mathlib): general Jensen is now available as `Findist.exp_convexOn_le`
-- (`MDPLib/Probability/Convexity.lean`), for any convex `f` and any distribution. This lemma
-- does NOT follow from it directly: Mathlib has no `convexOn_abs` (zero occurrences repo-wide),
-- so folding it in would first require proving `ConvexOn R Set.univ abs`. Keep it as is.
theorem abs_dotProduct_le_dotProduct_abs_uniform (x : Fin n → R) (hn : 0 < n) :
    |(fun _ : Fin n => (1 : R) / n) ⬝ᵥ x| ≤ (fun _ : Fin n => (1 : R) / n) ⬝ᵥ fun i => |x i| := by
  have hpos : 0 < (n : R) := by exact_mod_cast hn
  have hnonneg : 0 ≤ (1 : R) / n := by
    have := inv_pos.mpr hpos
    simp
  have hp : ∀ i : Fin n, 0 ≤ (1 : R) / n := fun _ => hnonneg
  simpa using
    abs_dotProduct_le_dotProduct_abs
      (p := fun _ : Fin n => (1 : R) / n)
      (x := x)
      (hp := hp)

end Matrix
end dotProduct
