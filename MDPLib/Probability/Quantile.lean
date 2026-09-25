import MDPLib.Probability.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Data.Fin.VecNotation

set_option linter.unusedSectionVars false

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
         [CharZero R] [Archimedean R]





-- TODO(naming): Mathlib states order lemmas in the `≤` / `<` direction and derives the `≥`
-- / `>` forms via `ge_iff_le`. Most statements in this file (`IsQuantile`, `probability_geq_of_mem_quantile`,
-- `mem_quantileLower_iff`, ...) are written with `≥`, which keeps them from matching Mathlib's
-- order lemmas by `rw`/`simp` and forces the `suffices ... from this` workarounds below.
-- Flagged once here rather than per declaration.
namespace Statistic
open Findist FinRV


section Definition 

--def UnitI := {α : ℚ // 0 ≤ α ∧ α ≤ 1}

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] (P : Findist R Ω) (X Y : FinRV Ω R) (α : R) (q v : R)

/-- Proof the `q` is an `α`-quantile of `X` --/
def IsQuantile  : Prop := ℙ[X ≤ᵣ q // P ] ≥ α ∧ ℙ[X ≥ᵣ q // P] ≥ 1 - α

/-- Proof that `q` is a lower bound on the `α`-quantile of `X` --/
def IsQuantileLower : Prop := ℙ[X ≥ᵣ q // P] ≥ 1 - α

/-- Set of quantiles at a level `α`  --/
def quantile : Set R := {q | IsQuantile P X α q}

/-- Set of lower bounds on a quantile at `α` -/
def quantileLower : Set R := {q | IsQuantileLower P X α q}

/-- Value `q` is maximum quantile at `α` of `X` and probability `P`  -/
def IsGreatestQuantile : Prop := IsGreatest (quantile P X α) q

/-- Value `q` is minimum quantile at `α` of `X` and probability `P`  -/
def IsLeastQuantile : Prop := IsLeast (quantile P X α) q

end Definition

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] {P : Findist R Ω} {X Y : FinRV Ω R} {α : R} {q v : R}

theorem le_probability_leq_of_mem_quantile : q ∈ quantile P X α → ℙ[X ≤ᵣ q // P ] ≥ α := by simp_all [quantile, IsQuantile]

theorem probability_geq_of_mem_quantile : q ∈ quantile P X α → ℙ[X ≥ᵣ q // P] ≥ 1 - α := by simp_all [quantile, IsQuantile]

theorem mem_quantile_iff : q ∈ quantile P X α ↔ ℙ[X ≤ᵣ q // P] ≥ α ∧ ℙ[X ≥ᵣ q // P] ≥ 1 - α := by simp_all [quantile, IsQuantile]

theorem notMem_quantile_iff : q ∉ quantile P X α ↔ ℙ[ X ≤ᵣ q // P ] < α ∨ ℙ[ X ≥ᵣ q // P] < 1 - α := by
    constructor; repeat intro h2; grind [mem_quantile_iff]

theorem mem_quantileLower_iff : q ∈ quantileLower P X α ↔ ℙ[X ≥ᵣ q // P] ≥ 1 - α := by simp_all [quantileLower, IsQuantileLower]

theorem mem_quantileLower_iff_probability_lt : q ∈ quantileLower P X α ↔ ℙ[X <ᵣ q // P] ≤ α :=
    by constructor
       · intro h; have := mem_quantileLower_iff.mp h; rw [probability_lt_eq_one_sub]; linarith
       · intro h; rw [probability_lt_eq_one_sub] at h;
         suffices  ℙ[X≥ᵣq // P] ≥ 1-α from this
         linarith

theorem probability_lt_of_mem_quantile : q ∈ quantile P X α → ℙ[ X <ᵣ q // P] ≤ α :=
  by intro h
     have := probability_geq_of_mem_quantile h
     rewrite [probability_geq_eq_one_sub] at this
     linarith

-- TODO(mathlib): this is `mem_quantile_iff.mpr`; consider dropping it.
theorem mem_quantile_of_probability_geq : ℙ[ X ≤ᵣ q // P ] ≥ α ∧ ℙ[ X ≥ᵣ q // P] ≥ 1 - α → q ∈ quantile P X α :=
    by intro h; simp_all [quantile, IsQuantile]

theorem mem_quantile_of_probability_lt : ℙ[X ≤ᵣ q // P] ≥ α ∧ ℙ[ X <ᵣ q // P] ≤ α → q ∈ quantile P X α :=
    by intro h1
       have h2 : ℙ[ X ≥ᵣ q // P] ≥ 1 - α := by rw [probability_geq_eq_one_sub]; linarith
       exact mem_quantile_of_probability_geq ⟨h1.1, h2⟩

-- TODO(mathlib): this is `mem_quantileLower_iff.mpr`; consider dropping it.
theorem mem_quantileLower_of_probability_geq : ℙ[ X ≥ᵣ q // P] ≥ 1 - α → q ∈ quantileLower P X α :=
    by intro h; simp_all [quantileLower, IsQuantileLower]

theorem mem_quantileLower_of_probability_lt : ℙ[ X <ᵣ q // P] ≤ α → q ∈ quantileLower P X α :=
    by intro h1
       have h2 : ℙ[X ≥ᵣ q // P] ≥ 1 - α := by rw [probability_geq_eq_one_sub]; linarith
       exact mem_quantileLower_of_probability_geq  h2

theorem IsQuantile.isQuantileLower : IsQuantile P X α v → IsQuantileLower P X α v :=
    by simp[IsQuantile, IsQuantileLower]

theorem quantile_subset_quantileLower : quantile P X α ⊆ quantileLower P X α := fun _ => IsQuantile.isQuantileLower

theorem isCofinalFor_quantileLower_of_le : X ≤ Y → IsCofinalFor (quantileLower P X α) (IsQuantileLower P Y α) := by
  intro hle q₁ hvar₁
  have hq₁ := le_refl q₁
  exact ⟨q₁, ⟨le_trans hvar₁ (probability_geq_anti hle hq₁), hq₁⟩⟩

section Negation 

theorem isQuantile_neg_iff : (IsQuantile P X α q) ↔ (IsQuantile P (-X) (1-α) (-q)) := by 
  rw [IsQuantile, IsQuantile, probability_geq_eq_neg_leq_neg,probability_leq_eq_neg_geq_neg]
  have hα : 1-(1-α) = α := by ring 
  rewrite [hα]
  constructor <;> exact fun a => a.symm
  
theorem mem_quantile_neg_iff : q ∈ quantile P X α ↔ (-q) ∈ quantile P (-X) (1-α) := isQuantile_neg_iff




end Negation 

section Bounds 


end Bounds 


section UpperLowerBounds

end UpperLowerBounds


section Transformations

variable {f : R → R}

-- the reverse implications of the following results do not hold
theorem mem_quantile_comp_of_monotone (hm : Monotone f) : q ∈ quantile P X α → (f q) ∈ quantile P (f ∘ X) α := by
    intro h; grw [mem_quantile_iff, hm.probability_leq_le, hm.probability_geq_le] at h; exact h

theorem mem_quantile_comp_iff_of_strictMono (hm : StrictMono f) : q ∈ quantile P X α ↔ (f q) ∈ quantile P (f ∘ X) α := by 
    rw [mem_quantile_iff, mem_quantile_iff, hm.probability_leq_eq, hm.probability_geq_eq]

theorem mem_quantileLower_comp_of_monotone (hm : Monotone f) : q ∈ quantileLower P X α → (f q) ∈ quantileLower P (f ∘ X) α := by
    intro h; grw [mem_quantileLower_iff, hm.probability_geq_le] at h; exact h

theorem mem_quantileLower_comp_iff_of_strictMono (hm : StrictMono f) : q ∈ quantileLower P X α ↔ (f q) ∈ quantileLower P (f ∘ X) α := by 
    rw [mem_quantileLower_iff, mem_quantileLower_iff, hm.probability_geq_eq]

-- set transformations
theorem image_quantile_subset_quantile_comp_of_monotone (hm : Monotone f) : f '' quantile P X α ⊆  quantile P (f∘X) α := by
    intro q ⟨x, hx⟩ 
    rw [←hx.2] 
    exact mem_quantile_comp_of_monotone hm hx.1 

theorem image_quantileLower_subset_quantileLower_comp_of_monotone (hm : Monotone f) : f '' quantileLower P X α ⊆  quantileLower P (f∘X) α := by
    intro q ⟨x, hx⟩ 
    rw [←hx.2] 
    exact mem_quantileLower_comp_of_monotone hm hx.1 

-- this property only holds for a discrete random variable 
theorem isCofinalFor_quantile_comp_image_of_monotone (hm : Monotone f) : IsCofinalFor (quantile P (f∘X) α) (f '' quantile P X α) := by 
    unfold IsCofinalFor
    intro a ha 
    use a 
    rewrite [mem_quantile_iff] at ha 
    constructor
    swap; exact le_rfl
    refine (Set.mem_image f (quantile P X α) a).mpr ?_
    sorry 

-- this property only holds for a discrete random variable 
theorem isCoinitialFor_quantile_comp_image_of_monotone (hm : Monotone f) : IsCoinitialFor (quantile P (f∘X) α) (f '' quantile P X α) := by 
    sorry 

end Transformations

variable {c : R}

theorem mem_quantileLower_add_const_iff : q ∈ quantileLower P X α ↔ (q+c) ∈ quantileLower P (X+c•1) α := by
  constructor
  · intro h; rw [mem_quantileLower_iff, probability_geq_add_const c] at h; exact h
  · intro h; rw [mem_quantileLower_iff, probability_geq_add_const c]; exact h

/-- Adding a constant to a random variable shifts the quantile -/
theorem quantileLower_add_const_eq_image : quantileLower P (X+c•1) α = (fun x ↦ x+c) '' quantileLower P X α := by
  apply Set.eq_of_subset_of_subset
  · unfold Set.image
    intro qc hqc
    use qc-c
    constructor
    · generalize hqcq : qc - c = q
      rw [mem_quantileLower_add_const_iff (c:=c)]
      have hqcq2 : qc = q + c := by rw[←hqcq]; ring
      rw [hqcq2] at hqc
      exact hqc
    · simp
  · unfold Set.image
    intro q hq
    obtain ⟨a, ha⟩ := hq
    rw [mem_quantileLower_add_const_iff (c:=c)] at ha
    rw [←ha.2]
    exact ha.1


    

end Statistic  

