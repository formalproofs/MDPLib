import MDPLib.Probability.Basic
import MDPLib.Probability.Quantile
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Set.Operations

namespace Risk

open Findist FinRV Statistic

variable {n : ℕ}
variable {P : Findist n} {X Y : FinRV n ℚ} {t t₁ t₂ : ℚ}

def IsRiskLevel (α : ℚ) : Prop := 0 ≤ α ∧ α < 1

def RiskLevel := { α : ℚ // IsRiskLevel α}

--instance instCoeRiskUnit : Coe RiskLevel UnitI where
--  coe := fun ⟨v,c⟩ => ⟨v, ⟨c.1, le_of_lt c.2⟩ ⟩

def FinVaRSet (P : Findist n) (X : FinRV n ℚ) (α : RiskLevel) : Finset ℚ :=
  let 𝓧 := Finset.univ.image X
  𝓧.filter (fun t ↦ ℙ[X <ᵣ t // P] ≤ α.val)

theorem FinVarSet_nonempty (P : Findist n) (X : FinRV n ℚ) (α : RiskLevel) : (FinVaRSet (n := n) P X α).Nonempty := by
    apply Finset.filter_nonempty_iff.mpr
    let xmin := (Finset.univ.image X).min' (rv_image_nonempty P X)
    use xmin
    constructor
    · exact Finset.min'_mem (Finset.univ.image X) (rv_image_nonempty P X)
    · have h : ℙ[X <ᵣ xmin // P] = 0 := prob_lt_min_eq_zero
      rewrite [h]
      exact α.2.1 

/-- Value-at-Risk of X at level α: VaR_α(X) = min { t ∈ X(Ω) | P[X ≤ t] ≥ α }.
    If we assume 0 ≤ α < 1, then the "else 0" branch is never used. -/
def FinVaR (P : Findist n) (X : FinRV n ℚ) (α : RiskLevel) : ℚ :=
   let 𝓧 := Finset.univ.image X
   let 𝓢 := 𝓧.filter (fun t ↦ ℙ[X <ᵣ t // P] ≤ α.val)
   have h : 𝓢.Nonempty := FinVarSet_nonempty P X α
   𝓢.max' h

variable {α : RiskLevel}


theorem finvar_prob_cond : ℙ[X <ᵣ (FinVaR P X α) // P] ≤ α.val ∧ α.val < ℙ[X ≤ᵣ (FinVaR P X α) // P]  := by
    constructor
    · unfold FinVaR; extract_lets 𝓧 𝓢 ne𝓢 
      exact (Finset.mem_filter.mp  (Finset.max'_mem 𝓢 ne𝓢)).right
    · generalize h : (FinVaR P X α) = t
      by_contra! hg
      have hlt : t < (FinRV.max P X) := prob_le_max_of_le_1 (lt_of_le_of_lt hg (Set.Ico.coe_lt_one α)) 
      obtain ⟨q, ⟨hqgt, hqp, hqin⟩⟩ := prob_le_step_lt_max P X t hlt
      have hqt : t ≥ q  := by 
        unfold FinVaR at h; extract_lets 𝓧 𝓢 ne𝓢 at h;
        subst t 
        rw [hqp] at hg 
        have h2: q ∈ 𝓢 := Finset.mem_filter.mpr ⟨hqin, hg⟩
        exact Finset.le_max' 𝓢 q h2 
      exact false_of_lt_ge hqgt hqt 

notation "VaR[" X "//" P ", " α "]" => FinVaR P X α

variable {n : ℕ} (P : Findist n) (X Y : FinRV n ℚ) (α : RiskLevel) (q v : ℚ)

/-- Value `v` is the Value at Risk at `α` of `X` and probability `P`  -/
def IsVaR_Q : Prop := IsGreatest (Quantile P X α.val) v

/-- A simpler, equivalent definition of Value at Risk  -/
def IsVaR : Prop := IsGreatest (QuantileLower P X α.val) v

variable {n : ℕ} {P : Findist n} {X Y : FinRV n ℚ} {α : RiskLevel} {q v q₁ q₂ : ℚ}

theorem var_prob_cond : IsVaR P X α v ↔ (ℙ[X <ᵣ v // P] ≤ α.val ∧ α.val < ℙ[X ≤ᵣ v // P]) :=
  by constructor
     · intro h
       constructor
       · have h1 : 1 - ℙ[X<ᵣv//P] ≥ 1 - α.val := by 
            simp_all [IsVaR,IsGreatest,QuantileLower,IsQuantileLower,prob_ge_of_lt]
         linarith
       · by_contra! hc
         obtain ⟨q,hq⟩ := prob_le_step_lt P X v
         have h3 : q ∈ QuantileLower P X α.val := by
            rw [hq.2,prob_lt_of_ge] at hc
            suffices ℙ[X≥ᵣq//P] ≥ 1 - α.val from this 
            linarith
         exact false_of_le_gt (h.2 h3) hq.1
     · intro h
       constructor
       · exact qsetlower_of_cond_lt h.1
       · by_contra! hc
         simp [upperBounds] at hc
         obtain ⟨q, hq⟩ := hc
         have hu : ℙ[X ≤ᵣ v // P] ≤ α.val :=
            calc ℙ[X ≤ᵣ v // P] ≤  ℙ[X <ᵣ q // P] := prob_lt_le_monotone hq.2
                 _ ≤ α.val := qsetlower_def_lt.mp hq.1
         exact false_of_lt_ge h.2 hu

-- This is the main correctness proof
theorem finvar_correct : IsVaR P X α (FinVaR P X α) := var_prob_cond.mpr finvar_prob_cond

theorem varq_is_quantile : IsVaR_Q P X α v → IsQuantile P X α.val v :=
    fun h => by simp_all only [Set.mem_setOf_eq,IsVaR_Q,Quantile,IsGreatest]

theorem varq_is_quantilelower : IsVaR_Q P X α v → IsQuantileLower P X α.val v :=
    fun h => by simp_all only [Set.mem_setOf_eq,IsVaR_Q,Quantile,IsGreatest,IsQuantileLower,IsQuantile]

theorem var_is_quantilelower : IsVaR P X α v → IsQuantileLower P X α.val v :=
    fun h => by simp_all only [Set.mem_setOf_eq,IsVaR,QuantileLower,IsGreatest,Set.mem_setOf_eq]

theorem var_is_quantile : IsVaR P X α v → IsQuantile P X α.val v := by
    intro h
    constructor
    · suffices ℙ[X≤ᵣv//P] > α.val by linarith
      exact (var_prob_cond.mp h).2
    · exact var_is_quantilelower h

-- TODO: this should be in Quantile.lean but it depends on VaR
theorem quantile_nonempty : (Quantile P X α.val).Nonempty :=
  Set.nonempty_def.mpr ⟨ VaR[X// P,α], finvar_correct  |> var_is_quantile ⟩

theorem isquantilelower_le_isquantile : IsCofinalFor (QuantileLower P X α.val) (Quantile P X α.val) := by
    intro q₁ h
    by_cases h2 : q₁ ∈ Quantile P X α.val
    · exact ⟨q₁, h2, le_refl q₁⟩
    · rewrite [qset_not_def] at h2
      rewrite [qsetlower_def] at h
      cases' h2 with h2l h2r
      · obtain ⟨q₂, hq₂⟩ : (Quantile P X α.val).Nonempty := quantile_nonempty
        use q₂
        constructor
        · exact hq₂
        · by_contra! ine
          exact ge_trans (prob_le_monotone (le_refl X) (le_of_lt ine)) (qset_lb hq₂) |> false_of_lt_ge h2l
      · exfalso; exact false_of_lt_ge h2r h

theorem isquantile_le_isquantilelower : IsCofinalFor (Quantile P X α.val) (QuantileLower P X α.val) :=
    HasSubset.Subset.isCofinalFor quantile_subset_quantilelower

theorem varq_eq_var : IsVaR_Q P X α v ↔ IsVaR P X α v := 
    ⟨fun h => ⟨varq_is_quantilelower h, (upperBounds_mono_of_isCofinalFor isquantilelower_le_isquantile) h.2⟩,
     fun h => ⟨var_is_quantile h, (upperBounds_mono_of_isCofinalFor isquantile_le_isquantilelower) h.2⟩⟩

theorem varq_prob_cond : IsVaR_Q P X α v ↔ (ℙ[X <ᵣ v // P] ≤ α.val ∧ α.val < ℙ[ X ≤ᵣ v // P]) :=
  by rewrite[varq_eq_var]; exact var_prob_cond

-------------------- VaR Properties -----------------------------------------------------------------------------

section VaR_properties

variable {P : Findist n} {X Y : FinRV n ℚ} {q q₁ v₁ v₂ c : ℚ} {α : RiskLevel}

theorem var_monotone : X ≤ Y → IsVaR P X α v₁ → IsVaR P Y α v₂ → v₁ ≤ v₂ :=
  fun hle hv1 hv2 => upperBounds_mono_of_isCofinalFor (quantile_le_monotone hle) hv2.2 hv1.1

theorem const_monotone_univ : StrictMono (fun x ↦ x + c)  := add_left_strictMono

theorem isvar_translation_invariant : IsVaR P X α v → IsVaR P (X+c•1) α (v+c) := by
    intro h
    rw [IsVaR,quantilelower_cash_image]
    exact MonotoneOn.map_isGreatest (Monotone.monotoneOn add_left_mono
                                    (QuantileLower P X α.val)) h

theorem var_translation_invariant : VaR[X + c•1 // P, α] = VaR[X + c•1 // P, α] + c := sorry

theorem var_positive_homog (hc : c > 0) : FinVaR P (fun ω => c * X ω) α = c * FinVaR P X α := sorry

end VaR_properties

end Risk


