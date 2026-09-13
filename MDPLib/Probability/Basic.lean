import MDPLib.Probability.Defs

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

import Mathlib.Data.Fin.Tuple.Sort -- for Equiv.Perm and permutation operations

set_option linter.unusedSectionVars false

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
         [CharZero R] [Archimedean R]



/-!
  # Basic properties for probability spaces and expectations

  The main results:
  - LOTUS: The law of the unconscious statistician 
  - The law of total expectations
  - The law of total probabilities
  - Relationship between X < x and X ≤ x for discrete random variables
-/


section General
open Matrix

variable {Ω : Type} [Fintype Ω] {p x : Ω → R}

/-- If a dot product with a nonnegative vector is positive, some coordinate of the
    vector is positive. -/
-- TODO(naming): `nneg_dotProd_pos_ex_pos` → `Matrix.exists_pos_of_dotProduct_pos`. Mathlib
-- names an existential conclusion `exists_*` and puts it first, with the hypotheses after
-- `_of_`; `nneg` → `nonneg`, `dotProd` → `dotProduct`, and `ex` is not an abbreviation
-- Mathlib uses. The nonnegativity side condition need not appear in the name.
theorem nneg_dotProd_pos_ex_pos (h1 : p ≥ 0) (h : p ⬝ᵥ x > 0) : ∃ ω, x ω > 0 := by
    by_contra! hcon
    have h2 := dotProduct_le_dotProduct_of_nonneg_left hcon h1   
    rw [dotProduct_zero'] at h2
    order 
                          

end General

namespace Findist

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] {P : Findist R Ω} {B : FinRV Ω Bool}

-- TODO(naming): `Findist.ge_zero` → `Findist.probability_nonneg`, `Findist.le_one` →
-- `Findist.probability_le_one`, `Findist.in_prob` → `Findist.isProb_probability`.
-- The current names describe neither the subject (`ℙ[B // P]`, not `P`) nor, in the first
-- case, the Mathlib spelling of `0 ≤ _` (always `nonneg`, and stated as `0 ≤ x` not `x ≥ 0`).
theorem ge_zero : 0 ≤ ℙ[B // P] := 
    by rw [prob_eq_exp_ind]
       calc 0 = 𝔼[0 //P] := exp_const.symm 
            _ ≤ 𝔼[𝕀 ∘ B//P] := exp_monotone ind_nneg
       

theorem le_one : ℙ[B // P] ≤ 1 := 
    by rw [prob_eq_exp_ind]
       calc 𝔼[𝕀 ∘ B//P] ≤ 𝔼[1 // P] := exp_monotone ind_le_one 
            _ = 1 := exp_const 

theorem in_prob (P : Findist R Ω) : Prob ℙ[B // P] := ⟨ge_zero, le_one⟩

end Findist


-------- Random variables --------------------------------------------

section RandomVariables

variable {Ω : Type} [Nonempty Ω] {X Y : FinRV Ω R} {t t₁ t₂ : R}

-- TODO(naming): `rvle_monotone` → `FinRV.indicator_leq_mono` and `rvlt_monotone` →
-- `FinRV.indicator_lt_mono`. `rvle`/`rvlt` jam two namespaces together; the statements are
-- about `𝕀 ∘ (X ≤ᵣ t)`, so `indicator` belongs in the name, and `_monotone` → `_mono`.
theorem rvle_monotone (h1 : X ≤ Y) (h2: t₁ ≤ t₂) : (𝕀 ∘ (Y ≤ᵣ t₁) : FinRV Ω R) ≤ 𝕀 ∘ (X ≤ᵣ t₂) := by 
    intro ω   
    by_cases h3 : Y ω ≤ t₁
    · simp [FinRV.leq, 𝕀, indicator, h3, (le_trans (le_trans (h1 ω) h3) h2)] 
    · by_cases h5 : X ω ≤ t₂
      repeat simp [h3, h5, 𝕀, indicator] 

theorem rvlt_monotone (h1 : X ≤ Y) (h2: t₁ ≤ t₂) : (𝕀 ∘ (Y <ᵣ t₁) : FinRV Ω R) ≤ 𝕀 ∘ (X <ᵣ t₂) := by 
    intro ω   
    by_cases h3 : Y ω < t₁
    · have h4 : X ω < t₂ := 
        calc X ω ≤ Y ω := h1 ω
             _ < t₁ := h3
             _ ≤ t₂ := h2 
      simp [FinRV.lt, 𝕀, indicator, h3, h4] 
    · by_cases h5 : X ω < t₂
      repeat simp [h3, h5, 𝕀, indicator] 

-- TODO(naming): `rv_monotone_sharp` → `FinRV.gt_of_geq_of_lt`. This is not a monotonicity
-- statement at all: from `t₁ < t₂` and `(X ≥ᵣ t₂) ω` it concludes `(X >ᵣ t₁) ω`, which is
-- exactly the `_of_`-chained shape Mathlib names `lt_of_le_of_lt`.
theorem rv_monotone_sharp {t₁ t₂ : R} (h : t₁ < t₂) (ω) (hω : (X ≥ᵣ t₂) ω ) : (X >ᵣ t₁) ω :=
    by simp [FinRV.gt, FinRV.geq] at hω ⊢
       order

variable [FinEnum Ω] {P : Findist R Ω} {A B : FinRV Ω Bool}

-- TODO(naming): `rv_le_max_one` → `FinRV.leq_max`, `rv_max_in_image` →
-- `FinRV.max_mem_image`, `rv_omega_ge_min` → `FinRV.min_le`, `rv_ge_min_one` →
-- `FinRV.geq_min`. `in` → `mem` (Mathlib's word for `∈`), the `_one` suffix is implied by
-- the equation, and `omega` is a bound-variable name.
theorem rv_le_max_one : (X ≤ᵣ (FinRV.max X)) = 1 :=
    by ext ω; simpa using rv_omega_le_max ω

theorem rv_max_in_image : (FinRV.max X) ∈ Finset.univ.image X :=
     Finset.max'_mem (Finset.image X Finset.univ) (rv_image_nonempty X)

theorem rv_omega_ge_min  (ω) : X ω ≥ (FinRV.min X) :=
   Finset.min'_le (Finset.image X Finset.univ) (X ω) (Finset.mem_image_of_mem X (Finset.mem_univ ω))

theorem rv_ge_min_one : (X ≥ᵣ (FinRV.min X)) = 1 :=
    by ext ω; simpa using rv_omega_ge_min ω

-- results for discrete probability distributions
section Atomic 

variable (P : Findist R Ω) (X : FinRV Ω R) (t : R)

-- TODO(naming): `prob_atomic_omega` → `Findist.exists_eq_of_probability_pos`. The conclusion
-- is an existential, which Mathlib puts first as `exists_`; "atomic" describes the setting
-- and `omega` the bound variable, neither of which belongs in the name.
theorem prob_atomic_omega {b : R} (h : ℙ[X =ᵣ b // P] > 0) : ∃ω, X ω = b := by 
    obtain ⟨ω, hω⟩ : ∃ω, (𝕀 ∘ (X=ᵣb)) ω > 0 := nneg_dotProd_pos_ex_pos (P.nneg) h 
    use ω
    by_contra!
    simp_all [𝕀, indicator]


-- TODO(naming): `rv_le_step_lt_max` → `FinRV.exists_leq_eq_lt_of_lt_max`,
-- `rv_le_step_lt` → `FinRV.exists_leq_eq_lt`, `rv_ge_step_lt_min` →
-- `FinRV.exists_geq_eq_gt_of_min_lt`. "step" names the intuition rather than the statement;
-- each of these produces a `q` with `(X ≤ᵣ t) = (X <ᵣ q)`, so `exists_..._eq_...` is the
-- Mathlib shape, with the side condition after `_of_`.
theorem rv_le_step_lt_max (h0 : t < (FinRV.max  X)) : ∃q > t, (X ≤ᵣ t) = (X <ᵣ q) ∧ q ∈ (Finset.univ.image X) := by
     let 𝓧 := Finset.univ.image X
     let 𝓨 := 𝓧.filter (fun x ↦ x > t)
     have hnonempty : 𝓨.Nonempty := Finset.filter_nonempty_iff.mpr ⟨FinRV.max X, ⟨rv_max_in_image, h0⟩⟩
     let q := 𝓨.min' hnonempty
     have q_ge_t : q > t := (Finset.mem_filter.mp (Finset.min'_mem 𝓨 hnonempty)).right 
     use q
     constructor
     · exact q_ge_t
     · constructor
       · ext ω
         rw [FinRV.leq,FinRV.lt,decide_eq_decide]
         constructor
         · exact fun h2 => lt_of_le_of_lt h2 q_ge_t
         · intro h2
           have hxω : X ω ∉ 𝓨 := by
              by_contra! inY; exact not_lt_of_ge (Finset.min'_le 𝓨 (X ω) inY) h2
           rw [Finset.mem_filter] at hxω
           push Not at hxω
           exact hxω (Finset.mem_image_of_mem X (Finset.mem_univ ω))
       · exact Finset.mem_of_mem_filter q (Finset.min'_mem 𝓨 hnonempty)

theorem rv_le_step_lt (P : Findist R Ω) : ∃q > t,  (X ≤ᵣ t) = (X <ᵣ q) :=
       by cases' lt_or_ge t (FinRV.max X) with hlt hge
          · obtain ⟨q, h⟩ := rv_le_step_lt_max  X t hlt
            exact ⟨q, ⟨h.1, h.2.1⟩⟩
          · have h := rv_omega_le_max (X:=X)
            grw [hge] at h
            let q := t + 1
            have b : ∀ω, X ω < q := fun ω => lt_add_of_le_of_pos (h ω) zero_lt_one
            have ab : (X ≤ᵣ t) = (X <ᵣ q) := by ext ω; simp_all [FinRV.leq, FinRV.lt]
            exact ⟨q, ⟨lt_add_one t, ab⟩⟩

theorem rv_ge_step_lt_min (h0 : t > (FinRV.min X)) : ∃q < t, (X ≥ᵣ t) = (X >ᵣ q) ∧ q ∈ (Finset.univ.image X) := by
    sorry

end Atomic

section Transformations

-- Monotone transformation of the random variable 

section Monotone
-- TODO: The proofs below are quite repetitive; may be worth it to simplify them

open Function 

variable {f : R → R} {x : R}  

--- LE

omit [FinEnum Ω] in 
-- TODO(naming): the twelve `rv_f_*` lemmas below. Fixes, applied uniformly:
--   * drop the `rv_` prefix in favour of `namespace FinRV`;
--   * `f` names a variable, not a statement — Mathlib says `comp` for `f ∘ X`;
--   * `strictmono`/`strictanti` → `strictMono`/`strictAnti` (Mathlib camel-cases the
--     `StrictMono`/`StrictAnti` roots inside snake_case names, e.g. `StrictMono.injective`);
--   * `monotone`/`antitone` as a *hypothesis* goes after `_of_`.
-- So `rv_f_le_monotone` → `FinRV.leq_le_comp_leq_of_monotone`,
--    `rv_f_le_strictmono` → `FinRV.leq_eq_comp_leq_of_strictMono`,
--    `rv_f_le_antitone`   → `FinRV.leq_le_comp_geq_of_antitone`,  and so on.
-- Alternatively make them dot-notation lemmas on the hypothesis: `Monotone.leq_comp`,
-- `StrictMono.leq_comp`, which is how Mathlib usually states this family.
theorem rv_f_le_monotone (hm : Monotone f) : (X ≤ᵣ x) ≤ (f ∘ X ≤ᵣ f x) := 
    by intro ω; rw [Bool.le_iff_imp]; simpa using fun a ↦ hm a


omit [FinEnum Ω] in 
theorem rv_f_le_antitone (hm : Antitone f) : (X ≤ᵣ x) ≤ (f ∘ X ≥ᵣ f x) := 
    by intro ω; rw [Bool.le_iff_imp]; simpa using fun a ↦ hm a

omit [FinEnum Ω] in 
theorem rv_f_le_strictmono (hm : StrictMono f) : (X ≤ᵣ x) = (f ∘ X ≤ᵣ f x) := 
    by ext ω; rw [Bool.eq_iff_iff]; simpa using hm.le_iff_le.symm

omit [FinEnum Ω] in 
theorem rv_f_le_strictanti (hm : StrictAnti f) : (X ≤ᵣ x) = (f ∘ X ≥ᵣ f x) := 
    by ext ω; rw [Bool.eq_iff_iff]; simpa using hm.le_iff_ge.symm

--- LT

omit [FinEnum Ω] in 
theorem rv_f_lt_strictmono (hm : StrictMono f) : (X <ᵣ x) = (f ∘ X <ᵣ f x) := 
    by ext ω; rw [Bool.eq_iff_iff]; simpa using hm.lt_iff_lt.symm

omit [FinEnum Ω] in 
theorem rv_f_lt_strictanti (hm : StrictAnti f) : (X <ᵣ x) = (f ∘ X >ᵣ f x) := 
    by ext ω; rw [Bool.eq_iff_iff]; simpa using hm.lt_iff_gt.symm

--- GE

omit [FinEnum Ω] in 
theorem rv_f_ge_monotone (hm : Monotone f) : (X ≥ᵣ x) ≤ (f ∘ X ≥ᵣ f x) := 
    by intro ω; rw [Bool.le_iff_imp]; simpa using fun a ↦ hm a

omit [FinEnum Ω] in 
theorem rv_f_ge_antitone (hm : Antitone  f) : (X ≥ᵣ x) ≤ (f ∘ X ≤ᵣ f x) := 
    by intro ω; rw [Bool.le_iff_imp]; simpa using fun a ↦ hm a


omit [FinEnum Ω] in 
theorem rv_f_ge_strictmono (hm : StrictMono f) : (X ≥ᵣ x) = (f ∘ X ≥ᵣ f x) := 
    by ext ω; rw [Bool.eq_iff_iff]; simpa using hm.le_iff_le.symm

omit [FinEnum Ω] in 
theorem rv_f_ge_strictanti (hm : StrictAnti f) : (X ≥ᵣ x) = (f ∘ X ≤ᵣ f x) := 
    by ext ω; rw [Bool.eq_iff_iff]; simpa using hm.le_iff_ge.symm

--- GT

omit [FinEnum Ω] in 
theorem rv_f_gt_strictmono (hm : StrictMono f) : (X >ᵣ x) = (f ∘ X >ᵣ f x) := 
    by ext ω;  rw [Bool.eq_iff_iff]; simpa using hm.lt_iff_lt.symm


omit [FinEnum Ω] in 
theorem rv_f_gt_strictanti (hm : StrictAnti f) : (X >ᵣ x) = (f ∘ X <ᵣ f x) := 
    by ext ω; rw [Bool.eq_iff_iff]; simpa using hm.lt_iff_gt.symm


end Monotone

-- TODO: Add similar results for anti-tone functions

section CashInvariance 

variable (c : R) {x : R}

omit [FinEnum Ω] in 
-- TODO(naming): the four `rv_*_cashinvar` lemmas → `FinRV.leq_add_const`,
-- `FinRV.lt_add_const`, `FinRV.geq_add_const`, `FinRV.gt_add_const`. "cash invariance" is
-- risk-measure jargon for the statement's actual content, adding a constant; Mathlib names
-- the operation (`add_const`), not the property it witnesses. Same for `prob_*_cashinvar`
-- below and `quantilelower_cashinv` / `*_translation_invariant` in the Risk files.
theorem rv_le_cashinvar : (X ≤ᵣ x) = (X + c•1 ≤ᵣ x + c) := by ext ω; simp

omit [FinEnum Ω] in 
theorem rv_lt_cashinvar : (X <ᵣ x) = (X + c•1 <ᵣ x + c) := by ext ω; simp

omit [FinEnum Ω] in 
theorem rv_ge_cashinvar : (X ≥ᵣ x) = (X + c•1 ≥ᵣ x + c) := by ext ω; simp

omit [FinEnum Ω] in 
theorem rv_gt_cashinvar : (X >ᵣ x) = (X + c•1 >ᵣ x + c) := by ext ω; simp

end CashInvariance

section Negation 


variable {x : R}

-- TODO(naming): the four `rv_*_neg_*` lemmas → `FinRV.leq_eq_neg_geq_neg`,
-- `FinRV.geq_eq_neg_leq_neg`, `FinRV.lt_eq_neg_gt_neg`, `FinRV.gt_eq_neg_lt_neg`.
-- These are equalities, so they need `_eq_` between the two sides; the current names read
-- as a relation between `≤` and `≥`.
theorem rv_le_neg_ge : (X ≤ᵣ x) = (-X ≥ᵣ -x) := by ext ω; simp

theorem rv_ge_neg_le : (X ≥ᵣ x) = (-X ≤ᵣ -x) := by ext ω; simp

theorem rv_lt_neg_gt : (X <ᵣ x) = (-X >ᵣ -x) := by ext ω; simp

theorem rv_gt_neg_lt : (X >ᵣ x) = (-X <ᵣ -x) := by ext ω; simp

end Negation 


end Transformations

end RandomVariables

------------------------------ Probability ---------------------------

section Probability 

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] {P : Findist R Ω} {A B C : FinRV Ω Bool} {X Y : FinRV Ω R} {t t₁ t₂ : R}


-- TODO(naming): `prob_compl_sums_to_one` → `Findist.probability_add_probability_not`, and
-- `prob_compl_one_minus` → `Findist.probability_not`. `compl` is Mathlib's word for set/order
-- complement, whereas the operation here is `FinRV.not`; `sums_to` → `add` (a verb phrase is
-- never a Mathlib name part); and `one_minus` → simply naming the subject, as in
-- `Finset.card_compl` / `prob_compl` style.
theorem prob_compl_sums_to_one : ℙ[B // P] + ℙ[¬ᵣB // P] = 1 := 
    by rw [prob_eq_exp_ind, prob_eq_exp_ind, ←exp_additive_two, one_of_ind_bool_or_not]
       exact exp_one 

theorem prob_compl_one_minus : ℙ[¬ᵣB // P] = 1 - ℙ[B // P] :=
    by rw [←prob_compl_sums_to_one (P:=P) (B:=B)]; ring 

-- TODO(naming): `rv_le_compl_gt` → `FinRV.leq_add_gt` (the statement is
-- `(X ≤ᵣ t) + (X >ᵣ t) = 1`, an addition, not a complement).
theorem rv_le_compl_gt : (X ≤ᵣ t) + (X >ᵣ t) = 1 := by
  ext ω
  unfold FinRV.leq FinRV.gt
  simp
  exact le_or_gt (X ω) t

-- TODO(naming): `prob_le_compl_gt` → `Findist.probability_leq_add_probability_gt`, and
-- likewise `prob_lt_compl_ge` → `Findist.probability_lt_add_probability_geq`.
theorem prob_le_compl_gt : ℙ[X ≤ᵣ t // P] + ℙ[X >ᵣ t // P] = 1 := by
  rw [prob_eq_exp_ind, prob_eq_exp_ind, ← exp_additive_two]
  have h : (𝕀 ∘ (X ≤ᵣ t)) + (𝕀 ∘ (X >ᵣ t)) = (1 : FinRV Ω R) := by
    ext ω
    unfold FinRV.leq FinRV.gt
    simp [𝕀, indicator]
    by_cases h1 : X ω ≤ t
    · have h2 : ¬ (X ω > t) := not_lt_of_ge h1
      simp [h1, h2]
    · have h3 : X ω > t := lt_of_not_ge h1
      simp [h1, h3]
  rw [h]
  exact exp_one

-- TODO(naming): `prob_gt_of_le`, `prob_le_of_gt`, `prob_ge_of_lt`, `prob_lt_of_ge` are
-- equalities (`ℙ[X >ᵣ t] = 1 - ℙ[X ≤ᵣ t]`), so `_of_` — which introduces a hypothesis —
-- is wrong. Mathlib would write `Findist.probability_gt_eq_one_sub` etc., or state the pair
-- once as `probability_gt` / `probability_leq` with the `one_sub` form as the `simp` normal
-- form.
theorem prob_gt_of_le : ℙ[X >ᵣ t // P] = 1 -  ℙ[X ≤ᵣ t // P] := by
  rw [←prob_le_compl_gt (P := P) (X := X) (t := t)]
  ring

theorem prob_le_of_gt :  ℙ[X ≤ᵣ t // P] = 1 - ℙ[X >ᵣ t // P] := by
  rw [←prob_le_compl_gt (P := P) (X := X) (t := t)]
  ring

theorem prob_lt_compl_ge : ℙ[X <ᵣ t // P] + ℙ[X ≥ᵣ t // P] = 1 := by
  rw [prob_eq_exp_ind, prob_eq_exp_ind, ← exp_additive_two]
  have h : (𝕀 ∘ (X <ᵣ t)) + (𝕀 ∘ (X ≥ᵣ t)) = (1 : FinRV Ω R) := by
    ext ω
    unfold FinRV.lt FinRV.geq
    simp [𝕀, indicator]
    by_cases h1 : X ω < t
    · have h2 : ¬ (X ω ≥ t) := not_le_of_gt h1
      simp [h1, h2]
    · have h3 : X ω ≥ t := le_of_not_gt h1
      simp [h1, h3]
  rw [h]
  exact exp_one

theorem prob_ge_of_lt : ℙ[X ≥ᵣ t // P] = 1 -  ℙ[X <ᵣ t // P] := by
  rw [← prob_lt_compl_ge (P := P) (X := X) (t := t)]; ring

theorem prob_lt_of_ge :  ℙ[X <ᵣ t // P] = 1 - ℙ[X ≥ᵣ t // P] := by
  rw [← prob_lt_compl_ge (P := P) (X := X) (t := t)]; ring

-- TODO(naming): `prob_bool_monotone` → `Findist.probability_mono`. The `bool_` qualifier is
-- redundant (the argument type already says it), and `_monotone` → `_mono`.
theorem prob_bool_monotone : A ≤ B → ℙ[A // P] ≤ ℙ[B // P] := fun h => exp_monotone (ind_monotone h)

-- TODO(naming): the four order-comparison lemmas `prob_le_monotone`, `prob_lt_monotone`,
-- `prob_ge_antitone`, `prob_gt_antitone` → `Findist.probability_leq_mono`,
-- `probability_lt_mono`, `probability_geq_anti`, `probability_gt_anti`
-- (`_monotone`/`_antitone` → `_mono`/`_anti`). Note also that the last two are stated with
-- `≥`; Mathlib states order lemmas in the `≤`/`<` direction and lets `ge_iff_le` do the rest.
theorem prob_le_monotone : X ≤ Y → t₁ ≤ t₂ → ℙ[Y ≤ᵣ t₁ // P] ≤ ℙ[X ≤ᵣ t₂ // P] := by 
  intro hxy ht 
  exact exp_monotone (rvle_monotone hxy ht)

theorem prob_lt_monotone : X ≤ Y → t₁ ≤ t₂ → ℙ[Y <ᵣ t₁ // P] ≤ ℙ[X <ᵣ t₂ // P] := by 
  intro hxy ht
  exact exp_monotone (rvlt_monotone hxy ht)

theorem prob_ge_antitone : X ≤ Y → t₁ ≤ t₂ → ℙ[Y ≥ᵣ t₁ // P] ≥ ℙ[X ≥ᵣ t₂ // P] := by 
  intro hxy ht 
  rewrite [prob_ge_of_lt,prob_ge_of_lt] 
  have := prob_lt_monotone (P := P) hxy ht 
  linarith 

theorem prob_gt_antitone : X ≤ Y → t₁ ≤ t₂ → ℙ[Y >ᵣ t₁ // P] ≥ ℙ[X >ᵣ t₂ // P] := by 
  intro hxy ht 
  rewrite [prob_gt_of_le,prob_gt_of_le] 
  have := prob_le_monotone (P := P) hxy ht 
  linarith 

-- TODO(naming): `prob_lt_le_monotone` → `Findist.probability_leq_le_probability_lt`. It is
-- not a monotonicity statement in either argument; it compares two different events under
-- `t < q`, so the name should list both sides in the order they appear.
theorem prob_lt_le_monotone {q : R} (h : q > t) : ℙ[X <ᵣ q // P] ≥ ℙ[X ≤ᵣ t // P] := by 
     unfold probability 
     apply Finset.sum_le_sum
     intro ω hω
     have h2 : (𝕀 ∘ (X ≤ᵣ t) : FinRV Ω R) ω ≤ (𝕀 ∘ (X <ᵣ q) : FinRV Ω R) ω :=
       by by_cases h3 : X ω ≤ t
          · have h4 : X ω < q := lt_of_le_of_lt h3 h
            simp [FinRV.leq, FinRV.lt, 𝕀, indicator, Function.comp, h3, h4]
          · simp [𝕀, indicator, FinRV.leq, FinRV.lt, Function.comp, h3]
            by_cases h5 : X ω < q <;> simp [h5] 
     exact mul_le_mul_of_nonneg_left h2 (P.nneg ω)

-- TODO(naming): `prob_le_eq_one` → `Findist.probability_leq_max`, `prob_ge_eq_one` →
-- `Findist.probability_geq_min`, `prob_lt_min_eq_zero` → `Findist.probability_lt_min`.
-- The distinguishing content is *which threshold* (`FinRV.max` / `FinRV.min`) is used; the
-- value `1` or `0` is what the lemma proves and, per Mathlib style, can be dropped once the
-- threshold is in the name.
theorem prob_le_eq_one : ℙ[X ≤ᵣ (FinRV.max X) // P] = 1 := by rw [rv_le_max_one]; exact prob_one_of_true P

theorem prob_ge_eq_one : ℙ[X ≥ᵣ (FinRV.min X) // P] = 1 := by rw [rv_ge_min_one]; exact prob_one_of_true P

theorem prob_lt_min_eq_zero : ℙ[X <ᵣ (FinRV.min X) // P] = 0 := by
    rw [prob_lt_of_ge, prob_ge_eq_one]; exact sub_self 1

-- TODO(naming): `prob_le_max_of_le_1` → `Findist.lt_max_of_probability_leq_lt_one`. Digits
-- do not appear in Mathlib names (`le_1` → `lt_one`), the conclusion (`t < FinRV.max X`)
-- should come first, and the hypothesis after `_of_`.
theorem prob_le_max_of_le_1 {t : R} (h : ℙ[X ≤ᵣ t // P] < 1) : t < FinRV.max X := by 
       by_contra! hcontra
       have h1 := prob_le_monotone (P := P) (le_refl X) hcontra
       rw [prob_le_eq_one] at h1
       exact not_le_of_gt h h1

section Rounding ---results for discrete probability distributions

variable (P : Findist R Ω) (X : FinRV Ω R) (t : R)

-- TODO(naming): `prob_le_step_lt_max` → `Findist.exists_probability_leq_eq_probability_lt_of_lt_max`
-- and `prob_le_step_lt` → `Findist.exists_probability_leq_eq_probability_lt` (see the
-- `rv_le_step_lt*` note above; "step" is intuition, and the conclusion is an existential).
theorem prob_le_step_lt_max (h: t < (FinRV.max X)) : 
    ∃q > t, ℙ[X ≤ᵣ t // P] = ℙ[X <ᵣ q // P] ∧ q ∈ (Finset.univ.image X) := sorry
          --let ⟨q, hq⟩ := rv_le_step_lt_max P t h
          --Exists.intro q ⟨hq.1, ⟨congrArg (probability P) hq.2.1, hq.2.2 ⟩⟩

/-- similar to `prob_le_step_lt_max` but no precondition -/
theorem prob_le_step_lt : ∃q > t,  ℙ[X ≤ᵣ t // P] = ℙ[X <ᵣ q // P] :=
      let ⟨q, hq⟩ := rv_le_step_lt X t P
      Exists.intro q ⟨hq.1, congrArg (probability P) hq.2⟩


end Rounding 

section Transformations

section Monotone

-- TODO: The proofs below are quite repetitive; may be worth it to simplify them

open Function 

variable {f : R → R} {x : R}  

--- LE

-- TODO(naming): the six `prob_f_*` lemmas mirror the `rv_f_*` family and take the same fixes:
-- drop `f`, use `comp`, camel-case `strictMono`, put the hypothesis after `_of_`, and move
-- into `namespace Findist`. E.g. `prob_f_le_strictmono` →
-- `Findist.probability_leq_eq_probability_comp_leq_of_strictMono`, or as dot notation
-- `StrictMono.probability_leq_comp`.
theorem prob_f_le_monotone (hm : Monotone f) : ℙ[X ≤ᵣ x // P] ≤ ℙ[f ∘ X ≤ᵣ f x // P] := 
   prob_bool_monotone (rv_f_le_monotone hm)

theorem prob_f_le_strictmono (hm : StrictMono f) : ℙ[X ≤ᵣ x // P] = ℙ[f ∘ X ≤ᵣ f x // P] := 
  congrArg (probability P) (rv_f_le_strictmono hm) 
--- LT

theorem prob_f_lt_strictmono (hm : StrictMono f) : ℙ[X <ᵣ x // P] = ℙ[f ∘ X <ᵣ f x // P] := 
  congrArg (probability P) (rv_f_lt_strictmono hm) 

--- GE

theorem prob_f_ge_monotone (hm : Monotone f) : ℙ[X ≥ᵣ x // P] ≤ ℙ[f ∘ X ≥ᵣ f x // P] := 
   prob_bool_monotone (rv_f_ge_monotone hm)

theorem prob_f_ge_strictmono (hm : StrictMono f) : ℙ[X ≥ᵣ x // P] = ℙ[f ∘ X ≥ᵣ f x // P] := 
  congrArg (probability P) (rv_f_ge_strictmono hm) 

--- GT

theorem prob_f_gt_strictmono (hm : StrictMono f) : ℙ[X >ᵣ x // P] = ℙ[f ∘ X >ᵣ f x // P] := 
  congrArg (probability P) (rv_f_gt_strictmono hm) 

end Monotone 

section CashInvariance 

variable (c : R) {x : R}

-- TODO(naming): the four `prob_*_cashinvar` lemmas → `Findist.probability_leq_add_const`
-- etc.; see the `rv_le_cashinvar` note above for why "cash invariance" is not a name part.
theorem prob_le_cashinvar : ℙ[X ≤ᵣ x // P] = ℙ[X + c•1 ≤ᵣ x + c // P] := congrArg (probability P) (rv_le_cashinvar c)

theorem prob_lt_cashinvar : ℙ[X <ᵣ x // P] = ℙ[X + c•1 <ᵣ x + c // P] := congrArg (probability P) (rv_lt_cashinvar c)

theorem prob_ge_cashinvar : ℙ[X ≥ᵣ x // P] = ℙ[X + c•1 ≥ᵣ x + c // P] := congrArg (probability P) (rv_ge_cashinvar c)

theorem prob_gt_cashinvar : ℙ[X >ᵣ x // P] = ℙ[X + c•1 >ᵣ x + c // P] := congrArg (probability P) (rv_gt_cashinvar c)

end CashInvariance

section Negation 

variable {x : R}

-- TODO(naming): the four `prob_*_neg_*` lemmas → `Findist.probability_leq_eq_neg_geq_neg`
-- etc.; these are equalities and need `_eq_`, as with the `rv_*_neg_*` family above.
theorem prob_le_neg_ge :  ℙ[X ≤ᵣ x // P] = ℙ[-X ≥ᵣ -x // P] := by rw [rv_le_neg_ge]

theorem prob_ge_neg_le :  ℙ[X ≥ᵣ x // P] = ℙ[-X ≤ᵣ -x // P] := by rw [rv_ge_neg_le]

theorem prob_lt_neg_gt : ℙ[X <ᵣ x //P] = ℙ[-X >ᵣ -x // P] := by rw [rv_lt_neg_gt]

theorem prob_gt_neg_lt : ℙ[X >ᵣ x //P] = ℙ[-X <ᵣ -x // P] := by rw [rv_gt_neg_lt]

end Negation 

end Transformations

end Probability 

------------------------------ CDF ---------------------------

section CDF

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] {P : Findist R Ω} {X Y : FinRV Ω R} {t t₁ t₂ : R}

/-- shows CDF is non-decreasing -/
-- TODO(naming): `cdf_nondecreasing` → `Findist.cdf_mono`. Mathlib says `mono`, never
-- `nondecreasing` (`Monotone` *is* "nondecreasing" for it).
theorem cdf_nondecreasing : t₁ ≤ t₂ → cdf P X t₁ ≤ cdf P X t₂ := by
  intro ht; unfold cdf
  apply prob_le_monotone (le_refl X) ht

/-- Shows CDF is monotone in random variable  -/
-- TODO(naming): `cdf_monotone_xy` → `Findist.cdf_anti_of_le`. Two problems: `xy` names the
-- variables it varies rather than the statement, and the conclusion is
-- `cdf P X t ≥ cdf P Y t` from `X ≤ Y`, i.e. *anti*tone in the random variable.
theorem cdf_monotone_xy : X ≤ Y → cdf P X t ≥ cdf P Y t := by
  intro h; unfold cdf
  apply prob_le_monotone h (le_refl t)

end CDF

------------------------------ Expectation ---------------------------

section Expectation 

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] {P : Findist R Ω}
variable {k : ℕ} {X : FinRV Ω R} {B : FinRV Ω Bool} {L : FinRV Ω (Fin k)}
variable (g : Fin k → R)

/-- LOTUS: The law of the unconscious statistician (or similar) -/
-- TODO(naming): `LOTUS` → `Findist.expect_comp_eq_sum`, keeping "law of the unconscious
-- statistician" in the docstring. Mathlib has no all-caps lemma names; a lemma is named by
-- its statement so it can be found by `exact?`, with the folklore name in the doc comment
-- (cf. `MeasureTheory.integral_map`).
theorem LOTUS : 𝔼[g ∘ L // P ] = ∑ i, ℙ[L =ᵣ i // P] * (g i) :=
  by rewrite [exp_decompose (X := g ∘ L) (L := L) ]
     apply Fintype.sum_congr
     intro i
     rewrite [←indi_eq_indr, ←exp_cond_eq_def (X := g ∘ L) ]
     by_cases! h : ℙ[L =ᵣ i // P] = 0 
     · rw [h];  simp 
     · rw [exp_cond_const i h ]
       ring

-- TODO(naming): `law_total_exp` → `Findist.expect_expectCondRV` (or `expect_condExp` to echo
-- Mathlib's `MeasureTheory.integral_condExp`), with "law of total expectation" left to the
-- docstring; same reasoning as `LOTUS`. `exp` here also reads as `Real.exp`.
theorem law_total_exp : 𝔼[𝔼[X |ᵣ L // P] // P] = 𝔼[X // P] :=
  let g i := 𝔼[X | L =ᵣ i // P]
  calc
    𝔼[𝔼[X |ᵣ L // P] // P ] = ∑ i , ℙ[ L =ᵣ i // P] * 𝔼[ X | L =ᵣ i // P ] := LOTUS g
    _ =  ∑ i , 𝔼[ X | L =ᵣ i // P ] * ℙ[ L =ᵣ i // P] := by apply Fintype.sum_congr; intro i; ring 
    _ =  ∑ i : Fin k, 𝔼[X * (𝕀 ∘ (L =ᵣ i)) // P] := by apply Fintype.sum_congr; exact fun a  ↦ exp_cond_eq_def
    _ =  ∑ i : Fin k, 𝔼[X * (L =ᵢ i) // P] := by apply Fintype.sum_congr; intro i; apply exp_congr; rw[indi_eq_indr] 
    _ = 𝔼[X // P]  := by rw [←exp_decompose]


section RV_Unique_Values

variable  {τ:Type} [DecidableEq τ] 

/-- The distinct values of a random variable, as a deduplicated list built from the
    enumeration of the sample space. -/
def FinRV.imageList (X : FinRV Ω τ) : List τ := List.dedup ((FinEnum.toList Ω).map X)

/-- The image finset of `X` equals the `toFinset` of its `imageList`. -/
-- TODO(naming): `univ_image_eq_imageList_toFinset` → `FinRV.image_univ_eq_imageList_toFinset`.
-- Mathlib writes the operation first and its argument second (`Finset.image_univ`), and the
-- lemma belongs in the `FinRV` namespace with the `imageList` it is about.
theorem univ_image_eq_imageList_toFinset (X : FinRV Ω τ) : Finset.univ.image X = X.imageList.toFinset := by
    ext y
    simp [FinRV.imageList]

-- TODO(naming): `sum_finset_eq_sum_image` → `FinRV.sum_image_univ_eq_sum_imageList`. The
-- current name says "finset" (uninformative — both sides are finite sums) and "image" for
-- the side that is actually the `imageList`.
theorem sum_finset_eq_sum_image (f : R → R) :
    (∑ y ∈ (Finset.univ.image X), f y) = ((X.imageList).map f).sum := by
      rw [univ_image_eq_imageList_toFinset]
      exact List.sum_toFinset f (List.nodup_dedup _)


section Generic 

variable {X : FinRV Ω τ}

-- TODO(naming): `finrv_image_superset` → `FinRV.apply_mem_imageList`. The statement is a
-- membership, `X ω ∈ X.imageList`, not a superset relation; `finrv_` duplicates the
-- namespace. Likewise `finrv_image_superset_exists` → `FinRV.exists_getElem_imageList`
-- (Mathlib puts `exists` first, not last).
theorem finrv_image_superset (ω : Ω) : X ω ∈ X.imageList := by
    simp only [FinRV.imageList, List.mem_dedup, List.mem_map]
    exact ⟨ω, FinEnum.mem_toList ω, rfl⟩

theorem finrv_image_superset_exists (ω) : ∃ i : Fin X.imageList.length, X ω = X.imageList[i] := 
  List.exists_mem_iff_get.mp ⟨X ω, ⟨finrv_image_superset ω, rfl⟩⟩
  
-- TODO(naming): `finrv_image_nodup` → `FinRV.imageList_nodup` (subject first, property last).
theorem finrv_image_nodup : X.imageList.Nodup := List.nodup_dedup _

-- TODO(naming): `List.finIdxOf` and `List.getElem_finIdxOf` are declared *into Mathlib's and
-- core's `List` namespace* from a project file. That is name squatting: core Lean already
-- ships `List.finIdxOf` (`List.finIdxOf : α → List α → Fin _`), so this shadows or clashes
-- with it depending on import order, and the `getElem_` lemma would silently compete with
-- core's. Move both under a project namespace, e.g. `MDPLib.List.finIdxOf`, or use core's
-- `List.finIdxOf` directly. Same issue as `Nat.sum_one_prod_cancel` in `MDP/Histories.lean`.
def List.finIdxOf (L : List τ) (a : τ) (h : a ∈ L) : Fin L.length := 
    ⟨L.idxOf a, List.idxOf_lt_length_of_mem h⟩

@[simp]
theorem List.getElem_finIdxOf (L : List τ) (a : τ) (h : a ∈ L) : L[L.finIdxOf a h] = a := 
    getElem_idxOf (idxOf_lt_length_of_mem h) 

def FinRV.imageIdxOf (X : FinRV Ω τ) (ω : Ω) : Fin (X.imageList.length) := 
    X.imageList.finIdxOf (X ω) (finrv_image_superset ω)

@[simp]
-- TODO(naming): `finrv_image_inverse` → `FinRV.getElem_imageIdxOf` (name the left-hand side,
-- `X.imageList[X.imageIdxOf ω]`; "inverse" describes the role, not the statement).
theorem finrv_image_inverse (ω : Ω) : X.imageList[X.imageIdxOf ω] = X ω := 
  List.getElem_finIdxOf X.imageList (X ω) (finrv_image_superset ω)

-- TODO(naming): `finrv_image_unique` → `FinRV.imageIdxOf_eq_of_eq_getElem`, and
-- `finrv_image_exact` → `FinRV.eq_getElem_iff_imageIdxOf_eq` (Mathlib marks an `↔` with
-- `_iff_`; "unique"/"exact" say nothing about either side).
theorem finrv_image_unique {ω i} (h: X ω = X.imageList[i]) : X.imageIdxOf ω = i := by 
  have h1 : X.imageList.Nodup := finrv_image_nodup 
  rewrite [← finrv_image_inverse ω (X := X)] at h 
  exact (List.Nodup.get_inj_iff h1).mp h
  
theorem finrv_image_exact {ω i} : X ω = X.imageList[i] ↔ X.imageIdxOf ω = i := 
  ⟨finrv_image_unique, fun h => by rw[←h]; exact Eq.symm (finrv_image_inverse ω)⟩


end Generic    

-- TODO(naming): `sum_eq_sum_image` → `FinRV.sum_image_univ_eq_sum_fin`. As written the name
-- is nearly identical to `sum_finset_eq_sum_image` above while stating something different
-- (indexing by `Fin X.imageList.length`).
theorem sum_eq_sum_image (f : R → R) : 
    ∑ y ∈ (Finset.univ.image X), f y = ∑ i : Fin X.imageList.length, f (X.imageList[i]) := by 
      rw [sum_finset_eq_sum_image, ← List.ofFn_getElem_eq_map, List.sum_ofFn]; rfl
      

/-- Shows that our definition of expectation is correct -/ 
-- TODO(naming): `expect_def_correct` → `Findist.expect_eq_sum_probability_mul`. Mathlib never
-- names a lemma "correct" (every lemma is); and `_def` is reserved for a definitional
-- unfolding, which this is not.
theorem expect_def_correct : 𝔼[ X // P] = ∑ y ∈ (Finset.univ.image X), (ℙ[ X =ᵣ y // P] * y) := by
    -- Reduce to LOTUS: L ω is the index of X ω in X.imageList and g maps an
    -- index back to its value, so that g ∘ L = X.
    let L ω := X.imageIdxOf ω
    have hgL : (fun i => X.imageList[i]) ∘ L = X := funext finrv_image_inverse
    conv_lhs => rw [← hgL, LOTUS (P := P) (L := L)]
    rw [sum_eq_sum_image]
    refine Fintype.sum_congr _ _ fun i => ?_
    rw [show (X =ᵣ X.imageList[i]) = (L =ᵣ i) by ext ω; simpa [L, FinRV.eq] using finrv_image_exact]


-- theorem expect_def_correct2 : 𝔼[ X // P] = ∑ y ∈ X.imageList, ℙ[ X =ᵣ y // P] * y := by  sorry
  

end RV_Unique_Values 

end Expectation 

section Probability 

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] {k : ℕ}  {L : FinRV Ω (Fin k)}
variable {P : Findist R Ω} {B : FinRV Ω Bool}

/-- The law of total probabilities -/
-- TODO(naming): `law_of_total_probs` → `Findist.probability_eq_sum`, with "law of total
-- probability" in the docstring (see `LOTUS` above). `probs` is also a contraction Mathlib
-- avoids.
theorem law_of_total_probs : ℙ[B // P] =  ∑ i, ℙ[B * (L =ᵣ i) // P]  := by 
    rewrite [prob_eq_exp_ind, rv_decompose (𝕀∘B : FinRV Ω R) L, exp_additive]
    apply Fintype.sum_congr
    intro i 
    rewrite [prob_eq_exp_ind] 
    apply exp_congr
    ext ω
    by_cases h1 : L ω = i 
    repeat by_cases h2 : B ω; repeat simp [h1, h2, 𝕀, indicator ]

end Probability 

---- Prababilities and permutations 

section Probability_Permutation

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] {P : Findist R Ω} {A B : FinRV Ω Bool} {X Y : FinRV Ω R} {t : R}

-- TODO(naming): `Findist.perm` → `Findist.comp` (or `Findist.map`). The distribution is
-- literally `P.p ∘ σ`; Mathlib names such a def after the operation, reserving `perm` for
-- `Equiv.Perm` itself.
def Findist.perm (P : Findist R Ω) (σ : Equiv.Perm (Ω)) : Findist R Ω where 
  p :=  P.p ∘ σ
  prob := by 
    have h1 : 1 = (1 : Ω → R) ∘ σ := rfl 
    rw [h1, comp_equiv_dotProduct_comp_equiv 1 P.p σ]
    exact P.prob
  nneg := fun ω => P.nneg (σ ω)

variable (σ : Equiv.Perm (Ω))

-- TODO(naming): the permutation block: `exp_eq_perm` → `Findist.expect_comp_perm`,
-- `prob_eq_perm` → `Findist.probability_comp_perm`, `rv_le_perm` → `FinRV.leq_comp_perm`
-- (and the `lt`/`ge`/`gt` variants), `prob_le_eq_perm` → `Findist.probability_leq_comp_perm`.
-- `exp` → `expect`, `prob` → `probability`, and `_eq_perm` hides that the operation being
-- commuted past is composition with `σ`.
theorem exp_eq_perm : 𝔼[X ∘ σ // P.perm σ] = 𝔼[X // P] := by
  unfold expect Findist.perm 
  exact (comp_equiv_dotProduct_comp_equiv P.1 X σ)

theorem prob_eq_perm : ℙ[A ∘ σ // P.perm σ] = ℙ[A // P] := by 
  have h1 : (𝕀 ∘ A ∘ σ : FinRV Ω R) = (𝕀 ∘ A) ∘ σ := by rfl 
  rw [prob_eq_exp_ind, h1, exp_eq_perm, ←prob_eq_exp_ind] 
  
theorem rv_le_perm : (X ∘ σ ≤ᵣ t) = (X ≤ᵣ t) ∘ σ := by unfold FinRV.leq; grind only 

theorem rv_lt_perm : (X ∘ σ <ᵣ t) = (X <ᵣ t) ∘ σ := by unfold FinRV.lt; grind only 

theorem rv_ge_perm : (X ∘ σ ≥ᵣ t) = (X ≥ᵣ t) ∘ σ := by unfold FinRV.geq; grind only 

theorem rv_gt_perm : (X ∘ σ >ᵣ t) = (X >ᵣ t) ∘ σ := by unfold FinRV.gt; grind only 

theorem prob_le_eq_perm : ℙ[X ∘ σ ≤ᵣ t // P.perm σ] = ℙ[X ≤ᵣ t // P] := by rw [rv_le_perm, prob_eq_perm]

theorem prob_lt_eq_perm : ℙ[X ∘ σ <ᵣ t // P.perm σ] = ℙ[X <ᵣ t // P] := by rw [rv_lt_perm, prob_eq_perm]

theorem prob_ge_eq_perm : ℙ[X ∘ σ ≥ᵣ t // P.perm σ] = ℙ[X ≥ᵣ t // P] := by rw [rv_ge_perm, prob_eq_perm]

theorem prob_gt_eq_perm : ℙ[X ∘ σ >ᵣ t // P.perm σ] = ℙ[X >ᵣ t // P] := by rw [rv_gt_perm, prob_eq_perm]

end Probability_Permutation 
