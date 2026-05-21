import MDPLib.Probability.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Data.Fin.VecNotation




namespace Statistic 

section Definition 

--def UnitI := {α : ℚ // 0 ≤ α ∧ α ≤ 1}

variable {n : ℕ} (P : Findist n) (X Y : FinRV n ℚ) (α : ℚ) (q v : ℚ)

/-- Proof the `q` is an `α`-quantile of `X` --/
def IsQuantile  : Prop := ℙ[X ≤ᵣ q // P ] ≥ α ∧ ℙ[X ≥ᵣ q // P] ≥ 1 - α

/-- Proof that `q` is a lower bound on the `α`-quantile of `X` --/
def IsQuantileLower : Prop := ℙ[X ≥ᵣ q // P] ≥ 1 - α

/-- Set of quantiles at a level `α`  --/
def Quantile : Set ℚ := {q | IsQuantile P X α q}

/-- Set of lower bounds on a quantile at `α` -/
def QuantileLower : Set ℚ := {q | IsQuantileLower P X α q}

/-- Value `q` is maximum quantile at `α` of `X` and probability `P`  -/
def IsQuantMax : Prop := IsGreatest (Quantile P X α) q

/-- Value `q` is minimum quantile at `α` of `X` and probability `P`  -/
def IsQuantMin : Prop := IsLeast (Quantile P X α) q

end Definition

variable {n : ℕ} {P : Findist n} {X Y : FinRV n ℚ} {α : ℚ} {q v : ℚ}

theorem qset_lb : q ∈ Quantile P X α → ℙ[X ≤ᵣ q // P ] ≥ α := by simp_all [Quantile, IsQuantile]

theorem qset_ub : q ∈ Quantile P X α → ℙ[X ≥ᵣ q // P] ≥ 1 - α := by simp_all [Quantile, IsQuantile]

theorem qset_def : q ∈ Quantile P X α ↔ ℙ[X ≤ᵣ q // P] ≥ α ∧ ℙ[X ≥ᵣ q // P] ≥ 1 - α := by simp_all [Quantile, IsQuantile]

theorem qset_not_def : q ∉ Quantile P X α ↔ ℙ[ X ≤ᵣ q // P ] < α ∨ ℙ[ X ≥ᵣ q // P] < 1 - α := by
    constructor; repeat intro h2; grind [qset_def]

theorem qsetlower_def : q ∈ QuantileLower P X α ↔ ℙ[X ≥ᵣ q // P] ≥ 1 - α := by simp_all [QuantileLower, IsQuantileLower]

theorem qsetlower_def_lt : q ∈ QuantileLower P X α ↔ ℙ[X <ᵣ q // P] ≤ α :=
    by constructor
       · intro h; have := qsetlower_def.mp h; rw [prob_lt_of_ge]; linarith
       · intro h; rw [prob_lt_of_ge] at h;
         suffices  ℙ[X≥ᵣq // P] ≥ 1-α from this
         linarith

theorem qset_ub_lt : q ∈ Quantile P X α → ℙ[ X <ᵣ q // P] ≤ α :=
  by intro h
     have := qset_ub h
     rewrite [prob_ge_of_lt] at this
     linarith

theorem qset_of_cond : ℙ[ X ≤ᵣ q // P ] ≥ α ∧ ℙ[ X ≥ᵣ q // P] ≥ 1 - α → q ∈ Quantile P X α :=
    by intro h; simp_all [Quantile, IsQuantile]

theorem qset_of_cond_lt : ℙ[X ≤ᵣ q // P] ≥ α ∧ ℙ[ X <ᵣ q // P] ≤ α → q ∈ Quantile P X α :=
    by intro h1
       have h2 : ℙ[ X ≥ᵣ q // P] ≥ 1 - α := by rw [prob_ge_of_lt]; linarith
       exact qset_of_cond ⟨h1.1, h2⟩

theorem qsetlower_of_cond : ℙ[ X ≥ᵣ q // P] ≥ 1 - α → q ∈ QuantileLower P X α :=
    by intro h; simp_all [QuantileLower, IsQuantileLower]

theorem qsetlower_of_cond_lt : ℙ[ X <ᵣ q // P] ≤ α → q ∈ QuantileLower P X α :=
    by intro h1
       have h2 : ℙ[X ≥ᵣ q // P] ≥ 1 - α := by rw [prob_ge_of_lt]; linarith
       exact qsetlower_of_cond  h2

theorem quantile_implies_quantilelower : IsQuantile P X α v → IsQuantileLower P X α v :=
    by simp[IsQuantile, IsQuantileLower]

theorem quantile_subset_quantilelower : Quantile P X α ⊆ QuantileLower P X α := fun _ => quantile_implies_quantilelower

theorem quantile_le_monotone : X ≤ Y → IsCofinalFor (QuantileLower P X α) (IsQuantileLower P Y α) := by
  intro hle q₁ hvar₁
  have hq₁ := le_refl q₁
  exact ⟨q₁, ⟨le_trans hvar₁ (prob_ge_antitone hle hq₁), hq₁⟩⟩

section Negation 

theorem isquant_neg : (IsQuantile P X α q) ↔ (IsQuantile P (-X) (1-α) (-q)) := by 
  rw [IsQuantile, IsQuantile, prob_ge_neg_le,prob_le_neg_ge]
  have hα : 1-(1-α) = α := by ring 
  rewrite [hα]
  constructor <;> exact fun a => a.symm
  
theorem quantile_neg : q ∈ Quantile P X α ↔ (-q) ∈ Quantile P (-X) (1-α) := isquant_neg




end Negation 

section Bounds 


end Bounds 


section UpperLowerBounds

end UpperLowerBounds


section Transformations

variable {f : ℚ → ℚ}

-- the reverse implications of the following results do not hold
theorem quantile_f_monotone (hm : Monotone f) : q ∈ Quantile P X α → (f q) ∈ Quantile P (f ∘ X) α := by
    intro h; grw [qset_def, prob_f_le_monotone hm, prob_f_ge_monotone hm] at h; exact h

theorem quantile_f_strictmono (hm : StrictMono f) : q ∈ Quantile P X α ↔ (f q) ∈ Quantile P (f ∘ X) α := by 
    rw [qset_def, qset_def, prob_f_le_strictmono hm, prob_f_ge_strictmono hm]

theorem quantilelower_f_monotone (hm : Monotone f) : q ∈ QuantileLower P X α → (f q) ∈ QuantileLower P (f ∘ X) α := by
    intro h; grw [qsetlower_def, prob_f_ge_monotone hm] at h; exact h

theorem quantilelower_f_strictmono (hm : StrictMono f) : q ∈ QuantileLower P X α ↔ (f q) ∈ QuantileLower P (f ∘ X) α := by 
    rw [qsetlower_def, qsetlower_def, prob_f_ge_strictmono hm]

-- set transformations
theorem quantile_f_monotone_set (hm : Monotone f) : f '' Quantile P X α ⊆  Quantile P (f∘X) α := by
    intro q ⟨x, hx⟩ 
    rw [←hx.2] 
    exact quantile_f_monotone hm hx.1 

theorem quantilelower_f_monotone_set (hm : Monotone f) : f '' QuantileLower P X α ⊆  QuantileLower P (f∘X) α := by
    intro q ⟨x, hx⟩ 
    rw [←hx.2] 
    exact quantilelower_f_monotone hm hx.1 

-- this property only holds for a discrete random variable 
theorem quantile_f_cofinal (hm : Monotone f) : IsCofinalFor (Quantile P (f∘X) α) (f '' Quantile P X α) := by 
    unfold IsCofinalFor
    intro a ha 
    use a 
    rewrite [qset_def] at ha 
    constructor
    swap; exact Rat.le_refl
    refine (Set.mem_image f (Quantile P X α) a).mpr ?_
    sorry 

-- this property only holds for a discrete random variable 
theorem quantile_f_coinitial (hm : Monotone f) : IsCoinitialFor (Quantile P (f∘X) α) (f '' Quantile P X α) := by 
    sorry 

end Transformations

variable {c : ℚ}

theorem quantilelower_cashinv : q ∈ QuantileLower P X α ↔ (q+c) ∈ QuantileLower P (X+c•1) α := by
  constructor
  · intro h; rw [qsetlower_def, prob_ge_cashinvar c] at h; exact h
  · intro h; rw [qsetlower_def, prob_ge_cashinvar c]; exact h

/-- Adding a constant to a random variable shifts the quantile -/
theorem quantilelower_cash_image : QuantileLower P (X+c•1) α = (fun x ↦ x+c) '' QuantileLower P X α := by
  apply Set.eq_of_subset_of_subset
  · unfold Set.image
    intro qc hqc
    use qc-c
    constructor
    · generalize hqcq : qc - c = q
      rw [quantilelower_cashinv (c:=c)]
      have hqcq2 : qc = q + c := by rw[←hqcq]; ring
      rw [hqcq2] at hqc
      exact hqc
    · simp
  · unfold Set.image
    intro q hq
    obtain ⟨a, ha⟩ := hq
    rw [quantilelower_cashinv (c:=c)] at ha
    rw [←ha.2]
    exact ha.1


    

end Statistic  

