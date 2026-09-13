import MDPLib.Probability.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Data.Fin.VecNotation

set_option linter.unusedSectionVars false

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
         [CharZero R] [Archimedean R]





-- TODO(naming): namespace `Statistic` → `Findist` (or `Quantile`). Mathlib namespaces are
-- named after the object the declarations are about, and everything here is about a
-- `Findist`/`FinRV` pair; "Statistic" names neither, and the singular reads oddly for a
-- namespace holding many statistics.
-- TODO(naming): Mathlib states order lemmas in the `≤` / `<` direction and derives the `≥`
-- / `>` forms via `ge_iff_le`. Most statements in this file (`IsQuantile`, `qset_ub`,
-- `qsetlower_def`, ...) are written with `≥`, which keeps them from matching Mathlib's
-- order lemmas by `rw`/`simp` and forces the `suffices ... from this` workarounds below.
-- Flagged once here rather than per declaration.
namespace Statistic 

section Definition 

--def UnitI := {α : ℚ // 0 ≤ α ∧ α ≤ 1}

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] (P : Findist R Ω) (X Y : FinRV Ω R) (α : R) (q v : R)

/-- Proof the `q` is an `α`-quantile of `X` --/
def IsQuantile  : Prop := ℙ[X ≤ᵣ q // P ] ≥ α ∧ ℙ[X ≥ᵣ q // P] ≥ 1 - α

/-- Proof that `q` is a lower bound on the `α`-quantile of `X` --/
def IsQuantileLower : Prop := ℙ[X ≥ᵣ q // P] ≥ 1 - α

/-- Set of quantiles at a level `α`  --/
-- TODO(naming): `Quantile` → `quantile` and `QuantileLower` → `quantileLower`. These are
-- data (a `Set ℚ`), not `Prop`s or types, so Mathlib requires `lowerCamelCase`; the
-- `UpperCamelCase` spelling makes them look like predicates alongside `IsQuantile`.
def Quantile : Set R := {q | IsQuantile P X α q}

/-- Set of lower bounds on a quantile at `α` -/
def QuantileLower : Set R := {q | IsQuantileLower P X α q}

/-- Value `q` is maximum quantile at `α` of `X` and probability `P`  -/
-- TODO(naming): `IsQuantMax` → `IsGreatestQuantile`, `IsQuantMin` → `IsLeastQuantile`.
-- `Quant` is a truncation Mathlib would not use, and the underlying predicates are
-- `IsGreatest`/`IsLeast`, so the names should echo them rather than `Max`/`Min`.
def IsQuantMax : Prop := IsGreatest (Quantile P X α) q

/-- Value `q` is minimum quantile at `α` of `X` and probability `P`  -/
def IsQuantMin : Prop := IsLeast (Quantile P X α) q

end Definition

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] {P : Findist R Ω} {X Y : FinRV Ω R} {α : R} {q v : R}

-- TODO(naming): the whole `qset_*` / `qsetlower_*` family. `qset` is an unguessable
-- contraction and every one of these lemmas is really about `∈`, which Mathlib names `mem_`:
--   `qset_lb`            → `mem_quantile.le` / `le_probability_leq_of_mem_quantile`
--   `qset_ub`            → `probability_geq_of_mem_quantile`
--   `qset_def`           → `mem_quantile_iff`        (an `↔` takes `_iff_`, not `_def`)
--   `qset_not_def`       → `notMem_quantile_iff`     (Mathlib now spells `∉` as `notMem`)
--   `qsetlower_def`      → `mem_quantileLower_iff`
--   `qsetlower_def_lt`   → `mem_quantileLower_iff_probability_lt`
--   `qset_ub_lt`         → `probability_lt_of_mem_quantile`
--   `qset_of_cond`       → drop; it is `mem_quantile_iff.mpr` (and `_of_cond` says nothing)
--   `qset_of_cond_lt`    → `mem_quantile_of_probability_lt`
--   `qsetlower_of_cond`  → drop; it is `mem_quantileLower_iff.mpr`
--   `qsetlower_of_cond_lt` → `mem_quantileLower_of_probability_lt`
-- Note `lb`/`ub` are also not Mathlib abbreviations (it writes `lowerBounds`/`upperBounds`).
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

-- TODO(naming): `quantile_implies_quantilelower` → `IsQuantile.isQuantileLower`. Mathlib
-- never writes `implies`: an implication from `IsQuantile` is a dot-notation lemma on it.
-- Likewise `quantile_subset_quantilelower` → `quantile_subset_quantileLower` — the
-- name is right, but the `lower` must be camel-cased to match the renamed definition.
theorem quantile_implies_quantilelower : IsQuantile P X α v → IsQuantileLower P X α v :=
    by simp[IsQuantile, IsQuantileLower]

theorem quantile_subset_quantilelower : Quantile P X α ⊆ QuantileLower P X α := fun _ => quantile_implies_quantilelower

-- TODO(naming): `quantile_le_monotone` → `isCofinalFor_quantileLower_of_le`. The conclusion
-- is `IsCofinalFor ...`, not a monotonicity statement, and the `X ≤ Y` hypothesis belongs
-- after `_of_`.
theorem quantile_le_monotone : X ≤ Y → IsCofinalFor (QuantileLower P X α) (IsQuantileLower P Y α) := by
  intro hle q₁ hvar₁
  have hq₁ := le_refl q₁
  exact ⟨q₁, ⟨le_trans hvar₁ (prob_ge_antitone hle hq₁), hq₁⟩⟩

section Negation 

-- TODO(naming): `isquant_neg` → `isQuantile_neg_iff` and `quantile_neg` →
-- `mem_quantile_neg_iff`. Mathlib camel-cases an embedded predicate name inside snake_case
-- (`isQuantile`, cf. `isCompact_iff`), truncating it to `isquant` loses that, and both
-- statements are `↔`, which takes `_iff`.
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

variable {f : R → R}

-- the reverse implications of the following results do not hold
-- TODO(naming): the six `quantile_f_*` / `quantilelower_f_*` lemmas. `f` names a variable;
-- the statement's operation is composition, which Mathlib calls `comp`. Also
-- `strictmono` → `strictMono`, and a hypothesis goes after `_of_`:
--   `quantile_f_monotone`        → `mem_quantile_comp_of_monotone`
--   `quantile_f_strictmono`      → `mem_quantile_comp_iff_of_strictMono`
--   `quantilelower_f_monotone`   → `mem_quantileLower_comp_of_monotone`
--   `quantilelower_f_strictmono` → `mem_quantileLower_comp_iff_of_strictMono`
--   `quantile_f_monotone_set`    → `image_quantile_subset_quantile_comp_of_monotone`
--   `quantilelower_f_monotone_set` → `image_quantileLower_subset_quantileLower_comp_of_monotone`
-- (`_set` says nothing; the distinguishing content is `f '' _ ⊆ _`.)
-- Same for `quantile_f_cofinal` / `quantile_f_coinitial` →
-- `isCofinalFor_quantile_comp_image_of_monotone` / `isCoinitialFor_...`.
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
    swap; exact le_rfl
    refine (Set.mem_image f (Quantile P X α) a).mpr ?_
    sorry 

-- this property only holds for a discrete random variable 
theorem quantile_f_coinitial (hm : Monotone f) : IsCoinitialFor (Quantile P (f∘X) α) (f '' Quantile P X α) := by 
    sorry 

end Transformations

variable {c : R}

-- TODO(naming): `quantilelower_cashinv` → `mem_quantileLower_add_const_iff`, and
-- `quantilelower_cash_image` → `quantileLower_add_const_eq_image`. "cash invariance" is
-- risk jargon for what the statement plainly is — adding a constant — and `cashinv` is a
-- further contraction of it; see the `rv_le_cashinvar` note in `Probability/Basic.lean`.
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

