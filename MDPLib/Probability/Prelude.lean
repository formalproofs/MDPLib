import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Tactic

import Mathlib.Logic.Function.Defs


/-- states that p is a valid probability value -/
@[simp]
abbrev Prob (p : ℚ) : Prop := 0 ≤ p ∧ p ≤ 1

----------------- Section: Basic Probability -----------------------------------------------


namespace Prob

variable {p x y : ℚ}

@[simp]
theorem of_complement ( hp : Prob p) : Prob (1-p) := by
        simp_all only [ Prob, sub_nonneg, tsub_le_iff_right, le_add_iff_nonneg_right, and_self]

@[simp]
theorem complement_inv_nneg (hp : Prob p) : 0 ≤ (1-p)⁻¹ := by
        simp_all only [Prob, inv_nonneg, sub_nonneg]

theorem lower_bound_fst (hp : Prob p) (h : x ≤ y) : x ≤ p * x + (1-p) * y := by
        have h2 : (1-p) * x ≤ (1-p) * y := mul_le_mul_of_nonneg_left h hp.of_complement.1
        linarith

theorem lower_bound_snd (hp : Prob p) (h : y ≤ x) : y ≤ p * x + (1-p) * y := by
        have h2 : p * y ≤ p * x := mul_le_mul_of_nonneg_left h hp.1
        linarith

theorem upper_bound_fst (hp : Prob p) (h : y ≤ x) : p * x + (1-p) * y ≤ x := by
        have h2 : (1-p) * y ≤ (1-p) * x := mul_le_mul_of_nonneg_left h hp.of_complement.1
        linarith

theorem upper_bound_snd (hp : Prob p) (h : x ≤ y) : p * x + (1-p) * y ≤ y := by
        have h2 : p * x ≤ p * y := mul_le_mul_of_nonneg_left h hp.1
        linarith

end Prob


section FunctionalAnalysis


end FunctionalAnalysis

section dotProduct

variable {x y z : Fin n → ℚ}

theorem dotProd_hadProd_rotate : x ⬝ᵥ (y * z) = z ⬝ᵥ (x * y) := by
  unfold dotProduct
  apply Fintype.sum_congr
  intro i
  simp
  ring

theorem dotProd_hadProd_comm : x ⬝ᵥ (y * z) = x ⬝ᵥ (z * y) := by
  unfold dotProduct
  apply Fintype.sum_congr
  intro i
  simp
  left
  ring

theorem dotProduct_eq_one_had : x ⬝ᵥ y = 1 ⬝ᵥ (x * y) := by simp [dotProduct]

example (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := Left.mul_nonneg hx hy

theorem prod_eq_zero_of_nneg_dp_zero (hx : 0 ≤ x) (hy : 0 ≤ y) : x ⬝ᵥ y = 0 → x * y = 0 := by
  intro h
  rw [dotProduct_eq_one_had] at h
  have := Left.mul_nonneg hx hy
  simp_all [dotProduct]
  exact (Fintype.sum_eq_zero_iff_of_nonneg this).mp h

theorem abs_pos_hom {a b : ℚ} (h : 0 ≤ a) : |a * b| = a * |b| := by 
  rw [abs_mul, abs_of_nonneg h]

theorem abs_dotProd_le_dotProd_abs(p x : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i) : |p ⬝ᵥ x| ≤ p ⬝ᵥ fun i => |x i| := by
  calc
    |∑ i : Fin n, p i * x i| ≤ ∑ i, |p i * x i| := Finset.abs_sum_le_sum_abs (fun i ↦ p i * x i) Finset.univ
    _ = ∑ i, p i * |x i| := Finset.sum_congr rfl (fun i _ => abs_pos_hom (hp i))
    _ = p ⬝ᵥ fun i => |x i| := rfl

theorem jensen_abs_uniform (x : Fin n → ℚ) (hn : 0 < n) :
    |(fun _ : Fin n => (1 : ℚ) / n) ⬝ᵥ x| ≤ (fun _ : Fin n => (1 : ℚ) / n) ⬝ᵥ fun i => |x i| := by
  have hpos : 0 < (n : ℚ) := by exact_mod_cast hn
  have hnonneg : 0 ≤ (1 : ℚ) / n := by
    have := inv_pos.mpr hpos
    simp
  have hp : ∀ i : Fin n, 0 ≤ (1 : ℚ) / n := fun _ => hnonneg
  simpa using
    abs_dotProd_le_dotProd_abs
      (p := fun _ : Fin n => (1 : ℚ) / n)
      (x := x)
      (hp := hp)

end dotProduct
