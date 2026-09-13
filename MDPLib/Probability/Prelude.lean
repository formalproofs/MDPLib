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
-- TODO(naming): `Prob` → `IsProb`. Mathlib prefixes a predicate (a `Prop`-valued def) with
-- `Is` (`IsGreatest`, `IsQuantile` below); a bare noun reads as a type of probabilities.
-- Note also that this is literally `p ∈ Set.Icc (0:ℚ) 1`, which Mathlib would spell directly.
abbrev Prob (p : R) : Prop := 0 ≤ p ∧ p ≤ 1

----------------- Section: Basic Probability -----------------------------------------------


namespace Prob

variable {p x y : R}

@[simp]
-- TODO(naming): `Prob.of_complement` → `Prob.one_sub`. `_of_` in Mathlib introduces the
-- hypothesis (`le_of_lt`), but here `Prob p` is the dot-notation receiver, not an `of_`
-- argument; the name should describe the conclusion's head term, `1 - p`.
theorem of_complement ( hp : Prob p) : Prob (1-p) := by
        simp_all only [ Prob, sub_nonneg, tsub_le_iff_right, le_add_iff_nonneg_right, and_self]

@[simp]
-- TODO(naming): `Prob.complement_inv_nneg` → `Prob.inv_one_sub_nonneg`. Two fixes: `nneg`
-- is not a Mathlib abbreviation (always `nonneg`), and the name should follow the term
-- structure outside-in, `(1 - p)⁻¹` = `inv_one_sub`.
theorem complement_inv_nneg (hp : Prob p) : 0 ≤ (1-p)⁻¹ := by
        simp_all only [Prob, inv_nonneg, sub_nonneg]

-- See also `Convex.min_le_combo` / `Convex.combo_le_max` and `min_eq_left h` / `max_eq_left h` and `smul_eq_mul`
-- TODO(mathlib): confirmed 2026-09-13 -- `Convex.min_le_combo` and `Convex.combo_le_max`
-- (`Mathlib/Analysis/Convex/Segment.lean:502,506`) assume only `[Semiring 𝕜] [PartialOrder 𝕜]`,
-- strictly weaker than this library's stack, so the replacement is unconditionally available
-- (with `•` = `*` via `smul_eq_mul`). The `n`-ary versions are `Finset.inf_le_centerMass` /
-- `Finset.centerMass_le_sup`, already harvested as `exp_ge_min` / `exp_le_max` in
-- `MDPLib/Probability/Convexity.lean`.
-- TODO(naming): the four `lower_bound_*`/`upper_bound_*` lemmas below. `fst`/`snd` describe
-- an argument position rather than the statement, and "bound" does not say which side.
-- Mathlib names these after the convex combination they bound:
--   `lower_bound_fst` → `Prob.self_le_combo_of_le`   (x ≤ p*x + (1-p)*y  given  x ≤ y)
--   `lower_bound_snd` → `Prob.self_le_combo_of_ge`
--   `upper_bound_fst` → `Prob.combo_le_self_of_ge`
--   `upper_bound_snd` → `Prob.combo_le_self_of_le`
-- cf. the `Convex.min_le_combo` / `Convex.combo_le_max` naming already cited above.
theorem lower_bound_fst (hp : Prob p) (h : x ≤ y) : x ≤ p * x + (1-p) * y := by
        have h2 := mul_le_mul_of_nonneg_left h hp.of_complement.1
        linarith

theorem lower_bound_snd (hp : Prob p) (h : y ≤ x) : y ≤ p * x + (1-p) * y := by
        have h2 := mul_le_mul_of_nonneg_left h hp.1
        linarith

theorem upper_bound_fst (hp : Prob p) (h : y ≤ x) : p * x + (1-p) * y ≤ x := by
        have h2 := mul_le_mul_of_nonneg_left h hp.of_complement.1
        linarith

theorem upper_bound_snd (hp : Prob p) (h : x ≤ y) : p * x + (1-p) * y ≤ y := by
        have h2 : p * x ≤ p * y := mul_le_mul_of_nonneg_left h hp.1
        linarith

end Prob


section FunctionalAnalysis


end FunctionalAnalysis

section dotProduct

variable {Ω : Type*} [Fintype Ω]
variable {x y z : Ω → R} {c : R}


-- TODO(naming): this whole `dotProduct` section lives in the root namespace; Mathlib keeps
-- every `⬝ᵥ` lemma in the `Matrix` namespace. Suggest wrapping the section in
-- `namespace Matrix ... end Matrix` so these become `Matrix.dotProduct_*`.
-- TODO(naming): `dotProd_hadProd_rotate` → `Matrix.dotProduct_mul_rotate`. `dotProd` and
-- `hadProd` are ad-hoc contractions: Mathlib spells the operation `dotProduct`, and the
-- Hadamard product here is just `*` on the Pi type, so it is named `mul`.
theorem dotProd_hadProd_rotate : x ⬝ᵥ (y * z) = z ⬝ᵥ (x * y) := by
  apply Fintype.sum_congr
  intro i
  rewrite [Pi.mul_apply y z i, Pi.mul_apply]
  ring

-- TODO(naming): `dotProd_hadProd_comm` → `Matrix.dotProduct_mul_comm` (same reasons).
theorem dotProd_hadProd_comm : x ⬝ᵥ (y * z) = x ⬝ᵥ (z * y) := congrArg (x ⬝ᵥ ·) (mul_comm y z)

example : (c • x) i = c * x i := by rw [Pi.smul_apply, smul_eq_mul] 

-- TODO(naming): `funmul_eq_smul` → `const_mul_eq_smul`. `funmul` is not a Mathlib word; the
-- left-hand side is a *constant* function times `X`, and Mathlib names that piece `const`.
-- TODO(naming): `X` here is an auto-bound implicit (it is not in the `variable` block), so
-- its type is inferred as a fresh universe-polymorphic Pi type. Bind it explicitly.
theorem funmul_eq_smul : (fun _ ↦ c) * X = c • X := rfl 

-- TODO(naming): `dotProd_smul_homogeneous` → drop it; it is a literal alias of Mathlib's
-- `dotProduct_smul`. If kept, `Matrix.dotProduct_smul'`, never `dotProd`/`homogeneous`
-- (Mathlib names the property by its statement shape, not by the word "homogeneous").
theorem dotProd_smul_homogeneous : x ⬝ᵥ (c • y) = c * x ⬝ᵥ y := dotProduct_smul c x y

-- TODO(naming): `dotProduct_eq_one_had` → `Matrix.dotProduct_eq_one_dotProduct_mul`.
-- `had` (Hadamard) is opaque, and the current name reads as "the dot product equals one".
theorem dotProduct_eq_one_had : x ⬝ᵥ y = 1 ⬝ᵥ (x * y) := by simp [dotProduct]

-- TODO(naming): `prod_eq_zero_of_nneg_dp_zero` →
-- `Matrix.mul_eq_zero_of_dotProduct_eq_zero`. Three fixes: `prod` → `mul` (Mathlib reserves
-- `prod` for `∏`), `dp` is not an abbreviation Mathlib uses, and `nneg` → `nonneg`
-- (the nonnegativity hypotheses can stay unnamed in the conclusion-driven name).
theorem prod_eq_zero_of_nneg_dp_zero (hx : 0 ≤ x) (hy : 0 ≤ y) : x ⬝ᵥ y = 0 → x * y = 0 := by
  intro h
  rw [dotProduct_eq_one_had] at h
  have := Left.mul_nonneg hx hy
  simp_all [dotProduct]
  exact (Fintype.sum_eq_zero_iff_of_nonneg this).mp h

-- TODO(naming): `abs_pos_hom` → `abs_mul_of_nonneg`. The statement is `|a * b| = a * |b|`
-- under `0 ≤ a`; "pos_hom" describes a motivation, not the statement, and the hypothesis
-- is nonnegativity rather than positivity.
theorem abs_pos_hom {a b : R} (h : 0 ≤ a) : |a * b| = a * |b| := by 
  rw [abs_mul, abs_of_nonneg h]

-- TODO(naming): `abs_dotProd_le_dotProd_abs` → `Matrix.abs_dotProduct_le_dotProduct_abs`.
-- Correct structure already; only `dotProd` → `dotProduct` and the namespace.
theorem abs_dotProd_le_dotProd_abs (p x : Ω → R) (hp : ∀ i, 0 ≤ p i) : |p ⬝ᵥ x| ≤ p ⬝ᵥ fun i => |x i| := by
  calc
    |∑ i : Ω, p i * x i| ≤ ∑ i, |p i * x i| := Finset.abs_sum_le_sum_abs (fun i ↦ p i * x i) Finset.univ
    _ = ∑ i, p i * |x i| := Finset.sum_congr rfl (fun i _ => abs_pos_hom (hp i))
    _ = p ⬝ᵥ fun i => |x i| := rfl

-- NOTE(mathlib): general Jensen is now available as `Findist.exp_convexOn_le`
-- (`MDPLib/Probability/Convexity.lean`), for any convex `f` and any distribution. This lemma
-- does NOT follow from it directly: Mathlib has no `convexOn_abs` (zero occurrences repo-wide),
-- so folding it in would first require proving `ConvexOn R Set.univ abs`. Keep it as is.
-- TODO(naming): `jensen_abs_uniform` → `Matrix.abs_dotProduct_le_dotProduct_abs_uniform`.
-- This is the triangle inequality specialised to the uniform weights, not Jensen's
-- inequality; Mathlib names a specialisation after the general lemma it instantiates.
theorem jensen_abs_uniform (x : Fin n → R) (hn : 0 < n) :
    |(fun _ : Fin n => (1 : R) / n) ⬝ᵥ x| ≤ (fun _ : Fin n => (1 : R) / n) ⬝ᵥ fun i => |x i| := by
  have hpos : 0 < (n : R) := by exact_mod_cast hn
  have hnonneg : 0 ≤ (1 : R) / n := by
    have := inv_pos.mpr hpos
    simp
  have hp : ∀ i : Fin n, 0 ≤ (1 : R) / n := fun _ => hnonneg
  simpa using
    abs_dotProd_le_dotProd_abs
      (p := fun _ : Fin n => (1 : R) / n)
      (x := x)
      (hp := hp)

end dotProduct
