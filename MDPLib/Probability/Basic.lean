import MDPLib.Probability.Defs

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

import Mathlib.Data.Fin.Tuple.Sort -- for Equiv.Perm and permutation operations


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

variable {Ω : Type} [Fintype Ω] {p x : Ω → ℚ}

/-- If a dot product of nonnegative vectors is positive, some coordinate of the
    second vector is positive. Proved over an arbitrary finite index. -/
theorem nneg_dotProd_pos_ex_pos (h1 : ∀ ω, p ω ≥ 0) (h2 : ∀ ω, x ω ≥ 0) (h : p ⬝ᵥ x > 0) : ∃ ω, x ω > 0 := by
  by_contra hcon
  push Not at hcon
  have hle : p ⬝ᵥ x ≤ 0 := by
    unfold dotProduct
    apply Finset.sum_nonpos
    intro ω _
    nlinarith [h1 ω, hcon ω]
  linarith

end General

namespace Findist

variable {Ω : Type} [FinEnum Ω] {P : Findist Ω} {B : FinRV Ω Bool}

theorem ge_zero : 0 ≤ ℙ[B // P] := 
    by rw [prob_eq_exp_ind]
       calc 0 = 𝔼[0 //P] := exp_const.symm 
            _ ≤ 𝔼[𝕀 ∘ B//P] := exp_monotone ind_nneg
       

theorem le_one : ℙ[B // P] ≤ 1 := 
    by rw [prob_eq_exp_ind]
       calc 𝔼[𝕀 ∘ B//P] ≤ 𝔼[1 // P] := exp_monotone ind_le_one 
            _ = 1 := exp_const 

theorem in_prob (P : Findist Ω) : Prob ℙ[B // P] := ⟨ge_zero, le_one⟩

end Findist


-------- Random variables --------------------------------------------

section RandomVariables

variable {Ω : Type} [FinEnum Ω] {P : Findist Ω} {A B : FinRV Ω Bool} {X Y : FinRV Ω ℚ} {t t₁ t₂ : ℚ}

theorem rvle_monotone (h1 : X ≤ Y) (h2: t₁ ≤ t₂) : 𝕀 ∘ (Y ≤ᵣ t₁) ≤ 𝕀 ∘ (X ≤ᵣ t₂) := by 
    intro ω   
    by_cases h3 : Y ω ≤ t₁
    · have h4 : X ω ≤ t₂ := le_trans (le_trans (h1 ω) h3) h2
      simp [FinRV.leq, 𝕀, indicator, h3, h4] 
    · by_cases h5 : X ω ≤ t₂
      repeat simp [h3, h5, 𝕀, indicator] 

theorem rvlt_monotone (h1 : X ≤ Y) (h2: t₁ ≤ t₂) : 𝕀 ∘ (Y <ᵣ t₁) ≤ 𝕀 ∘ (X <ᵣ t₂) := by 
    intro ω   
    by_cases h3 : Y ω < t₁
    · have h4 : X ω < t₂ := 
        calc X ω ≤ Y ω := h1 ω
             _ < t₁ := h3
             _ ≤ t₂ := h2 
      simp [FinRV.lt, 𝕀, indicator, h3, h4] 
    · by_cases h5 : X ω < t₂
      repeat simp [h3, h5, 𝕀, indicator] 

theorem rv_le_max_one : (X ≤ᵣ (FinRV.max P X)) = 1 :=
    by ext ω
       unfold FinRV.leq
       simpa using rv_omega_le_max P ω

theorem rv_max_in_image : (FinRV.max P X) ∈ Finset.univ.image X :=
     Finset.max'_mem (Finset.image X Finset.univ) (rv_image_nonempty P X)

theorem rv_omega_ge_min (P : Findist Ω) : ∀ω, X ω ≥ (FinRV.min P X) :=
    by intro ω
       have h : X ω ∈ (Finset.image X Finset.univ) := Finset.mem_image_of_mem X (Finset.mem_univ ω)
       exact Finset.min'_le (Finset.image X Finset.univ) (X ω) h

theorem rv_ge_min_one : (X ≥ᵣ (FinRV.min P X)) = 1 :=
    by ext ω
       unfold FinRV.geq
       simpa using rv_omega_ge_min P ω

theorem rv_monotone_sharp {t₁ t₂ : ℚ} : t₁ < t₂ → ∀ ω, (X ≥ᵣ t₂) ω → (X >ᵣ t₁) ω   :=
    by intro h ω pre
       simp [FinRV.gt, FinRV.geq] at pre ⊢
       linarith

-- results for discrete probability distributions
section Atomic 

variable (P : Findist Ω) (X : FinRV Ω ℚ) (t : ℚ)


theorem prob_atomic_omega {b : ℚ} (h : ℙ[X =ᵣ b // P] > 0) : ∃ω, X ω = b := by 
    obtain ⟨ω, hω⟩ : ∃ω, (𝕀 ∘ (X=ᵣb)) ω > 0 := nneg_dotProd_pos_ex_pos (P.nneg) (ind_nneg) h 
    use ω
    by_contra!
    simp_all [𝕀, indicator]

theorem rv_le_step_lt_max (h0 : t < (FinRV.max P X)) : ∃q > t, (X ≤ᵣ t) = (X <ᵣ q) ∧ q ∈ (Finset.univ.image X) := by
     let 𝓧 := Finset.univ.image X
     let 𝓨 := 𝓧.filter (fun x ↦ x > t)
     have hnonempty : 𝓨.Nonempty := Finset.filter_nonempty_iff.mpr ⟨FinRV.max P X, ⟨rv_max_in_image, h0⟩⟩
     let q := 𝓨.min' hnonempty
     have hq_Y : q > t := (Finset.mem_filter.mp (Finset.min'_mem 𝓨 hnonempty)).right 
     use q
     constructor
     · exact hq_Y
     · constructor; swap
       · exact Finset.mem_of_mem_filter q (Finset.min'_mem 𝓨 hnonempty)
       · ext ω
         rw [FinRV.leq,FinRV.lt,decide_eq_decide]
         constructor
         · exact fun h2 => lt_of_le_of_lt h2 hq_Y
         · intro h2
           have hxω : X ω ∉ 𝓨 := by
              by_contra! inY; exact not_lt_of_ge (Finset.min'_le 𝓨 (X ω) inY) h2
           rw [Finset.mem_filter] at hxω
           push Not at hxω
           exact hxω (Finset.mem_image_of_mem X (Finset.mem_univ ω))

theorem rv_le_step_lt (P : Findist Ω) : ∃q > t,  (X ≤ᵣ t) = (X <ᵣ q) :=
       by cases' lt_or_ge t (FinRV.max P X) with hlt hge
          · obtain ⟨q, h⟩ := rv_le_step_lt_max P X t hlt
            exact ⟨q, ⟨h.1, h.2.1⟩⟩
          · have h := rv_omega_le_max P (X:=X)
            grw [hge] at h
            let q := t + 1
            have b : ∀ω, X ω < q := fun ω => lt_add_of_le_of_pos (h ω) rfl
            have ab : (X ≤ᵣ t) = (X <ᵣ q) := by ext ω; simp_all [FinRV.leq, FinRV.lt]
            exact ⟨q, ⟨lt_add_one t, ab⟩⟩


theorem rv_ge_step_lt_min (h0 : t > (FinRV.min P X)) : ∃q < t, (X ≥ᵣ t) = (X >ᵣ q) ∧ q ∈ (Finset.univ.image X) := by
    sorry 

end Atomic


section Transformations

-- Monotone transformation of the random variable 

section Monotone
-- TODO: The proofs below are quite repetitive; may be worth it to simplify them

open Function 

variable {f : ℚ → ℚ} {x : ℚ}  

--- LE

theorem rv_f_le_monotone (hm : Monotone f) : (X ≤ᵣ x) ≤ (f ∘ X ≤ᵣ f x) := 
    by intro ω; apply bool_ineq; simpa using fun a ↦ hm a


theorem rv_f_le_antitone (hm : Antitone f) : (X ≤ᵣ x) ≤ (f ∘ X ≥ᵣ f x) := 
    by intro ω; apply bool_ineq; simpa using fun a ↦ hm a


theorem rv_f_le_strictmono (hm : StrictMono f) : (X ≤ᵣ x) = (f ∘ X ≤ᵣ f x) := 
    by ext ω; apply bool_eq; simpa using fun a ↦ hm.monotone a; simpa using hm.le_iff_le.mp

theorem rv_f_le_strictanti (hm : StrictAnti f) : (X ≤ᵣ x) = (f ∘ X ≥ᵣ f x) := 
    by ext ω; apply bool_eq; simpa using fun a ↦ hm.antitone a; simpa using hm.le_iff_ge.mp

--- LT

theorem rv_f_lt_strictmono (hm : StrictMono f) : (X <ᵣ x) = (f ∘ X <ᵣ f x) := 
    by ext ω; apply bool_eq; simpa using fun a => hm a; simpa using hm.lt_iff_lt.mp 

theorem rv_f_lt_strictanti (hm : StrictAnti f) : (X <ᵣ x) = (f ∘ X >ᵣ f x) := 
    by ext ω; apply bool_eq; simpa using fun a => hm a; simpa using hm.lt_iff_gt.mp 

--- GE

theorem rv_f_ge_monotone (hm : Monotone f) : (X ≥ᵣ x) ≤ (f ∘ X ≥ᵣ f x) := 
    by intro ω; apply bool_ineq; simpa using fun a ↦ hm a

theorem rv_f_ge_antitone (hm : Antitone  f) : (X ≥ᵣ x) ≤ (f ∘ X ≤ᵣ f x) := 
    by intro ω; apply bool_ineq; simpa using fun a ↦ hm a


theorem rv_f_ge_strictmono (hm : StrictMono f) : (X ≥ᵣ x) = (f ∘ X ≥ᵣ f x) := 
    by ext ω; apply bool_eq; simpa using fun a ↦ hm.monotone a; simpa using hm.le_iff_le.mp

theorem rv_f_ge_strictanti (hm : StrictAnti f) : (X ≥ᵣ x) = (f ∘ X ≤ᵣ f x) := 
    by ext ω; apply bool_eq; simpa using fun a ↦ hm.antitone a; simpa using hm.le_iff_ge.mp

--- GT

theorem rv_f_gt_strictmono (hm : StrictMono f) : (X >ᵣ x) = (f ∘ X >ᵣ f x) := 
    by ext ω; apply bool_eq; simpa using fun a => hm a; simpa using hm.lt_iff_lt.mp 


theorem rv_f_gt_strictanti (hm : StrictAnti f) : (X >ᵣ x) = (f ∘ X <ᵣ f x) := 
    by ext ω; apply bool_eq; simpa using fun a => hm a; simpa using hm.lt_iff_gt.mp


end Monotone

-- TODO: Add similar results for anti-tone functions

section CashInvariance 

variable (c : ℚ) {x : ℚ}

theorem rv_le_cashinvar : (X ≤ᵣ x) = (X + c•1 ≤ᵣ x + c) := by ext ω; simp

theorem rv_lt_cashinvar : (X <ᵣ x) = (X + c•1 <ᵣ x + c) := by ext ω; simp

theorem rv_ge_cashinvar : (X ≥ᵣ x) = (X + c•1 ≥ᵣ x + c) := by ext ω; simp

theorem rv_gt_cashinvar : (X >ᵣ x) = (X + c•1 >ᵣ x + c) := by ext ω; simp

end CashInvariance

section Negation 


variable {x : ℚ}

theorem rv_le_neg_ge : (X ≤ᵣ x) = (-X ≥ᵣ -x) := by ext ω; simp

theorem rv_ge_neg_le : (X ≥ᵣ x) = (-X ≤ᵣ -x) := by ext ω; simp

theorem rv_lt_neg_gt : (X <ᵣ x) = (-X >ᵣ -x) := by ext ω; simp

theorem rv_gt_neg_lt : (X >ᵣ x) = (-X <ᵣ -x) := by ext ω; simp

end Negation 


end Transformations

end RandomVariables

------------------------------ Probability ---------------------------

section Probability 

variable {Ω : Type} [FinEnum Ω] {P : Findist Ω} {A B C : FinRV Ω Bool} {X Y : FinRV Ω ℚ} {t t₁ t₂ : ℚ}


theorem prob_compl_sums_to_one : ℙ[B // P] + ℙ[¬ᵣB // P] = 1 := 
    by rw [prob_eq_exp_ind, prob_eq_exp_ind, ←exp_additive_two, one_of_ind_bool_or_not]
       exact exp_one 

theorem prob_compl_one_minus : ℙ[¬ᵣB // P] = 1 - ℙ[B // P] :=
    by rw [←prob_compl_sums_to_one (P:=P) (B:=B)]; ring 

theorem rv_le_compl_gt : (X ≤ᵣ t) + (X >ᵣ t) = 1 := by
  ext ω
  unfold FinRV.leq FinRV.gt
  simp
  exact le_or_gt (X ω) t

theorem prob_le_compl_gt : ℙ[X ≤ᵣ t // P] + ℙ[X >ᵣ t // P] = 1 := by
  rw [prob_eq_exp_ind, prob_eq_exp_ind, ← exp_additive_two]
  have h : (𝕀 ∘ (X ≤ᵣ t)) + (𝕀 ∘ (X >ᵣ t)) = (1 : FinRV Ω ℚ) := by
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

theorem prob_gt_of_le : ℙ[X >ᵣ t // P] = 1 -  ℙ[X ≤ᵣ t // P] := by
  rw [←prob_le_compl_gt (P := P) (X := X) (t := t)]
  ring

theorem prob_le_of_gt :  ℙ[X ≤ᵣ t // P] = 1 - ℙ[X >ᵣ t // P] := by
  rw [←prob_le_compl_gt (P := P) (X := X) (t := t)]
  ring

theorem prob_lt_compl_ge : ℙ[X <ᵣ t // P] + ℙ[X ≥ᵣ t // P] = 1 := by
  rw [prob_eq_exp_ind, prob_eq_exp_ind, ← exp_additive_two]
  have h : (𝕀 ∘ (X <ᵣ t)) + (𝕀 ∘ (X ≥ᵣ t)) = (1 : FinRV Ω ℚ) := by
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

theorem prob_bool_monotone : A ≤ B → ℙ[A // P] ≤ ℙ[B // P] := fun h => exp_monotone (ind_monotone h)

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

theorem prob_lt_le_monotone {q : ℚ} (h : q > t) : ℙ[X <ᵣ q // P] ≥ ℙ[X ≤ᵣ t // P] := by 
     unfold probability 
     apply Finset.sum_le_sum
     intro ω hω
     have h2 : (𝕀 ∘ (X ≤ᵣ t)) ω ≤ (𝕀 ∘ (X <ᵣ q)) ω :=
       by by_cases h3 : X ω ≤ t
          · have h4 : X ω < q := lt_of_le_of_lt h3 h
            simp [FinRV.leq, FinRV.lt, 𝕀, indicator, Function.comp, h3, h4]
          · simp [𝕀, indicator, FinRV.leq, FinRV.lt, Function.comp, h3]
            by_cases h5 : X ω < q <;> simp [h5] 
     exact mul_le_mul_of_nonneg_left h2 (P.nneg ω)

theorem prob_le_eq_one : ℙ[X ≤ᵣ (FinRV.max P X) // P] = 1 := by rw [rv_le_max_one]; exact prob_one_of_true P

theorem prob_ge_eq_one : ℙ[X ≥ᵣ (FinRV.min P X) // P] = 1 := by rw [rv_ge_min_one]; exact prob_one_of_true P

theorem prob_lt_min_eq_zero : ℙ[X <ᵣ (FinRV.min P X) // P] = 0 := by
    rw [prob_lt_of_ge, prob_ge_eq_one]; exact sub_self 1

theorem prob_le_max_of_le_1 {t : ℚ} (h : ℙ[X ≤ᵣ t // P] < 1) : t < FinRV.max P X := by 
       by_contra! hcontra
       have h1 := prob_le_monotone (P := P) (le_refl X) hcontra
       rw [prob_le_eq_one] at h1
       exact not_le_of_gt h h1

section Rounding ---results for discrete probability distributions

variable (P : Findist Ω) (X : FinRV Ω ℚ) (t : ℚ)

theorem prob_le_step_lt_max (h: t < (FinRV.max P X)) : 
    ∃q > t, ℙ[X ≤ᵣ t // P] = ℙ[X <ᵣ q // P] ∧ q ∈ (Finset.univ.image X) :=
          let ⟨q, hq⟩ := rv_le_step_lt_max P X t h
          Exists.intro q ⟨hq.1, ⟨congrArg (probability P) hq.2.1, hq.2.2 ⟩⟩

/-- similar to `prob_le_step_lt_max` but no precondition -/
theorem prob_le_step_lt : ∃q > t,  ℙ[X ≤ᵣ t // P] = ℙ[X <ᵣ q // P] :=
      let ⟨q, hq⟩ := rv_le_step_lt X t P
      Exists.intro q ⟨hq.1, congrArg (probability P) hq.2⟩


end Rounding 

section Transformations

section Monotone

-- TODO: The proofs below are quite repetitive; may be worth it to simplify them

open Function 

variable {f : ℚ → ℚ} {x : ℚ}  

--- LE

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

variable (c : ℚ) {x : ℚ}

theorem prob_le_cashinvar : ℙ[X ≤ᵣ x // P] = ℙ[X + c•1 ≤ᵣ x + c // P] := congrArg (probability P) (rv_le_cashinvar c)

theorem prob_lt_cashinvar : ℙ[X <ᵣ x // P] = ℙ[X + c•1 <ᵣ x + c // P] := congrArg (probability P) (rv_lt_cashinvar c)

theorem prob_ge_cashinvar : ℙ[X ≥ᵣ x // P] = ℙ[X + c•1 ≥ᵣ x + c // P] := congrArg (probability P) (rv_ge_cashinvar c)

theorem prob_gt_cashinvar : ℙ[X >ᵣ x // P] = ℙ[X + c•1 >ᵣ x + c // P] := congrArg (probability P) (rv_gt_cashinvar c)

end CashInvariance

section Negation 

variable {x : ℚ}

theorem prob_le_neg_ge :  ℙ[X ≤ᵣ x // P] = ℙ[-X ≥ᵣ -x // P] := by rw [rv_le_neg_ge]

theorem prob_ge_neg_le :  ℙ[X ≥ᵣ x // P] = ℙ[-X ≤ᵣ -x // P] := by rw [rv_ge_neg_le]

theorem prob_lt_neg_gt : ℙ[X <ᵣ x //P] = ℙ[-X >ᵣ -x // P] := by rw [rv_lt_neg_gt]

theorem prob_gt_neg_lt : ℙ[X >ᵣ x //P] = ℙ[-X <ᵣ -x // P] := by rw [rv_gt_neg_lt]

end Negation 

end Transformations

end Probability 

------------------------------ CDF ---------------------------

section CDF

variable {Ω : Type} [FinEnum Ω] {P : Findist Ω} {X Y : FinRV Ω ℚ} {t t₁ t₂ : ℚ}

/-- shows CDF is non-decreasing -/
theorem cdf_nondecreasing : t₁ ≤ t₂ → cdf P X t₁ ≤ cdf P X t₂ := by
  intro ht; unfold cdf
  apply prob_le_monotone (le_refl X) ht

/-- Shows CDF is monotone in random variable  -/
theorem cdf_monotone_xy : X ≤ Y → cdf P X t ≥ cdf P Y t := by
  intro h; unfold cdf
  apply prob_le_monotone h (le_refl t)

end CDF

------------------------------ Expectation ---------------------------

section Expectation 

variable {Ω : Type} [FinEnum Ω] {P : Findist Ω}
variable {k : ℕ} {X : FinRV Ω ℚ} {B : FinRV Ω Bool} {L : FinRV Ω (Fin k)}
variable (g : Fin k → ℚ)

/-- LOTUS: The law of the unconscious statistician (or similar) -/
theorem LOTUS : 𝔼[g ∘ L // P ] = ∑ i, ℙ[L =ᵣ i // P] * (g i) :=
  by rewrite [exp_decompose (X := g ∘ L) (L := L) ]
     apply Fintype.sum_congr
     intro i
     rewrite [←indi_eq_indr, ←exp_cond_eq_def (X := g ∘ L) ]
     by_cases! h : ℙ[L =ᵣ i // P] = 0 
     · rw [h];  simp 
     · rw [exp_cond_const i h ]
       ring

theorem law_total_exp : 𝔼[𝔼[X |ᵣ L // P] // P] = 𝔼[X // P] :=
  let g i := 𝔼[X | L =ᵣ i // P]
  calc
    𝔼[𝔼[X |ᵣ L // P] // P ] = ∑ i , ℙ[ L =ᵣ i // P] * 𝔼[ X | L =ᵣ i // P ] := LOTUS g
    _ =  ∑ i , 𝔼[ X | L =ᵣ i // P ] * ℙ[ L =ᵣ i // P] := by apply Fintype.sum_congr; intro i; ring 
    _ =  ∑ i : Fin k, 𝔼[X * (𝕀 ∘ (L =ᵣ i)) // P] := by apply Fintype.sum_congr; exact fun a  ↦ exp_cond_eq_def
    _ =  ∑ i : Fin k, 𝔼[X * (L =ᵢ i) // P] := by apply Fintype.sum_congr; intro i; apply exp_congr; rw[indi_eq_indr] 
    _ = 𝔼[X // P]  := by rw [←exp_decompose]

--- shows that using a set and list is the same
lemma finset_image_eq_list_map_dedup : ∀x, x ∈ Finset.univ.image X ↔ x ∈ (((FinEnum.toList Ω).map X) |> List.dedup) :=  by
    intro x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_dedup, List.mem_map,
               FinEnum.mem_toList, true_and]


lemma finset_list_eq_list_dedup (l : List ℚ) : l.toFinset = l.dedup.toFinset := 
    List.toFinset.ext (fun _ => List.mem_dedup.symm)


example (f : ℚ → ℚ) (l : List ℚ) (h : l.Nodup) : ∑ y ∈ l.toFinset, f y = (l.map f).sum :=  
    List.sum_toFinset (fun y => f y) h

section RV_Unique_Values

variable  {τ:Type} [DecidableEq τ] 

/-- The distinct values of a random variable, as a deduplicated list built from the
    enumeration of the sample space. -/
def FinRV.imageList (X : FinRV Ω τ) : List τ := List.dedup ((FinEnum.toList Ω).map X)

/-- The image finset of `X` equals the `toFinset` of its `imageList`. -/
theorem univ_image_eq_imageList_toFinset (X : FinRV Ω τ) :
    Finset.univ.image X = X.imageList.toFinset := by
    ext y
    simp only [FinRV.imageList, Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset,
               List.mem_dedup, List.mem_map, FinEnum.mem_toList, true_and]

theorem sum_finset_eq_sum_image (f : ℚ → ℚ) :
    (∑ y ∈ (Finset.univ.image X), f y) = ((X.imageList).map f).sum := by
      rw [univ_image_eq_imageList_toFinset]
      exact List.sum_toFinset f (List.nodup_dedup _)




section generic 

variable {X : FinRV Ω τ}

theorem finrv_image_superset (ω : Ω) : X ω ∈ X.imageList := by
    simp only [FinRV.imageList, List.mem_dedup, List.mem_map]
    exact ⟨ω, FinEnum.mem_toList ω, rfl⟩

theorem finrv_image_superset_exists (ω) : ∃ i : Fin X.imageList.length, X ω = X.imageList[i] := 
  List.exists_mem_iff_get.mp ⟨X ω, ⟨finrv_image_superset ω, rfl⟩⟩
  
theorem finrv_image_nodup : X.imageList.Nodup := List.nodup_dedup _

-- Mathlib seems to be missing this function
def List.finIdxOf (L : List τ) (a : τ) (h : a ∈ L) : Fin L.length := 
    ⟨L.idxOf a, List.idxOf_lt_length_of_mem h⟩

@[simp]
theorem List.getElem_finIdxOf (L : List τ) (a : τ) (h : a ∈ L) : L[L.finIdxOf a h] = a := 
    getElem_idxOf (idxOf_lt_length_of_mem h) 

def FinRV.imageIdxOf (X : FinRV Ω τ) (ω : Ω) : Fin (X.imageList.length) := 
    X.imageList.finIdxOf (X ω) (finrv_image_superset ω)

@[simp]
theorem finrv_image_inverse (ω : Ω) : X.imageList[X.imageIdxOf ω] = X ω := 
  List.getElem_finIdxOf X.imageList (X ω) (finrv_image_superset ω)

theorem finrv_image_unique {ω i} (h: X ω = X.imageList[i]) : X.imageIdxOf ω = i := by 
  have h1 : X.imageList.Nodup := finrv_image_nodup 
  rewrite [← finrv_image_inverse ω (X := X)] at h 
  exact (List.Nodup.get_inj_iff h1).mp h
  
theorem finrv_image_exact {ω i} : X ω = X.imageList[i] ↔ X.imageIdxOf ω = i := 
  ⟨finrv_image_unique, fun h => by rw[←h]; exact Eq.symm (finrv_image_inverse ω)⟩




end generic    

theorem sum_eq_sum_image (f : ℚ → ℚ) : 
    ∑ y ∈ (Finset.univ.image X), f y = ∑ i : Fin X.imageList.length, f (X.imageList[i]) := by 
      rw [sum_finset_eq_sum_image, ← List.ofFn_getElem_eq_map, List.sum_ofFn]; rfl
      

/-- Shows that our definition of expectation is correct -/ 
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

variable {Ω : Type} [FinEnum Ω] {k : ℕ}  {L : FinRV Ω (Fin k)}

/-- The law of total probabilities -/
theorem law_of_total_probs : ℙ[B // P] =  ∑ i, ℙ[B * (L =ᵣ i) // P]  := by 
    rewrite [prob_eq_exp_ind, rv_decompose (𝕀∘B) L, exp_additive]
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

variable {Ω : Type} [FinEnum Ω] {P : Findist Ω} {A B : FinRV Ω Bool} {X Y : FinRV Ω ℚ} {t : ℚ}

example (σ : Equiv.Perm (Ω)) (f g : Ω → ℚ) : f ⬝ᵥ g = (f ∘ σ) ⬝ᵥ (g ∘ σ) := 
  by exact Eq.symm (comp_equiv_dotProduct_comp_equiv f g σ)

example (σ : Equiv.Perm (Ω)) : (1 : Ω → ℚ) = (1 : Ω → ℚ) ∘ σ := rfl

def Findist.perm (P : Findist Ω) (σ : Equiv.Perm (Ω)) : Findist Ω where 
  p :=  P.p ∘ σ
  prob := by 
    have h1 : 1 = (1 : Ω → ℚ) ∘ σ := rfl 
    rw [h1, comp_equiv_dotProduct_comp_equiv 1 P.p σ]
    exact P.prob
  nneg := fun ω => P.nneg (σ ω)

variable (σ : Equiv.Perm (Ω))

theorem exp_eq_perm : 𝔼[X ∘ σ // P.perm σ] = 𝔼[X // P] := by
  unfold expect Findist.perm 
  exact (comp_equiv_dotProduct_comp_equiv P.1 X σ)

theorem prob_eq_perm : ℙ[A ∘ σ // P.perm σ] = ℙ[A // P] := by 
  have h1 : (𝕀 ∘ A ∘ σ) = (𝕀 ∘ A) ∘ σ := by rfl 
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
