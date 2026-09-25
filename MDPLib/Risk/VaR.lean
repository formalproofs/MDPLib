import MDPLib.Probability.Basic
import MDPLib.Probability.Quantile
import Mathlib.Data.Set.Operations

set_option linter.unusedSectionVars false

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
         [CharZero R] [Archimedean R]


namespace Risk

open Findist FinRV Statistic

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω]
variable {P : Findist R Ω} {X Y : FinRV Ω R} {t t₁ t₂ : R}

def IsRiskLevel (α : R) : Prop := 0 ≤ α ∧ α < 1

def RiskLevel (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] := { α : R // IsRiskLevel α}

--instance instCoeRiskUnit : Coe RiskLevel UnitI where
--  coe := fun ⟨v,c⟩ => ⟨v, ⟨c.1, le_of_lt c.2⟩ ⟩

def finVaRSet (P : Findist R Ω) (X : FinRV Ω R) (α : RiskLevel R) : Finset R :=
  let 𝓧 := X.quarks
  𝓧.filter (fun t ↦ ℙ[X <ᵣ t // P] ≤ α.val)

theorem finVaRSet_nonempty (P : Findist R Ω) (X : FinRV Ω R) (α : RiskLevel R) : (finVaRSet (Ω := Ω) P X α).Nonempty := by
    apply Finset.filter_nonempty_iff.mpr
    use X.minQuark
    constructor
    · exact minQuark_mem_quarks
    · have h : ℙ[X <ᵣ X.minQuark // P] = 0 := probability_lt_minQuark
      rewrite [h]
      exact α.2.1 

/-- Value-at-Risk of X at level α: VaR_α(X) = min { t ∈ X(Ω) | P[X ≤ t] ≥ α }.
    If we assume 0 ≤ α < 1, then the "else 0" branch is never used. -/
def finVaR (P : Findist R Ω) (X : FinRV Ω R) (α : RiskLevel R) : R :=
   let 𝓧 := X.quarks
   let 𝓢 := 𝓧.filter (fun t ↦ ℙ[X <ᵣ t // P] ≤ α.val)
   have h : 𝓢.Nonempty := finVaRSet_nonempty P X α
   𝓢.max' h

variable {α : RiskLevel R}


theorem finVaR_spec : ℙ[X <ᵣ (finVaR P X α) // P] ≤ α.val ∧ α.val < ℙ[X ≤ᵣ (finVaR P X α) // P]  := by
    constructor
    · unfold finVaR; extract_lets 𝓧 𝓢 ne𝓢 
      exact (Finset.mem_filter.mp  (Finset.max'_mem 𝓢 ne𝓢)).right
    · generalize h : (finVaR P X α) = t
      by_contra! hg
      have hlt : t < (FinRV.maxQuark X) := lt_maxQuark_of_probability_leq_lt_one (lt_of_le_of_lt hg (Set.Ico.coe_lt_one α)) 
      obtain ⟨q, ⟨hqgt, hqp, hqin⟩⟩ := exists_probability_leq_eq_probability_lt_of_lt_maxQuark P X t hlt
      have hqt : t ≥ q  := by 
        unfold finVaR at h; extract_lets 𝓧 𝓢 ne𝓢 at h;
        subst t 
        rw [hqp] at hg 
        have h2: q ∈ 𝓢 := Finset.mem_filter.mpr ⟨hqin, hg⟩
        exact Finset.le_max' 𝓢 q h2 
      exact not_le_of_gt hqgt hqt 

notation "VaR[" X "//" P ", " α "]" => finVaR P X α

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] (P : Findist R Ω) (X Y : FinRV Ω R) (α : RiskLevel R) (q v : R)

/-- Value `v` is the Value at Risk at `α` of `X` and probability `P`  -/
def IsVaRQuantile : Prop := IsGreatest (quantile P X α.val) v

/-- A simpler, equivalent definition of Value at Risk  -/
def IsVaR : Prop := IsGreatest (quantileLower P X α.val) v

variable {Ω : Type} [FinEnum Ω] [Nonempty Ω] {P : Findist R Ω} {X Y : FinRV Ω R} {α : RiskLevel R} {q v q₁ q₂ : R}

theorem isVaR_iff : IsVaR P X α v ↔ (ℙ[X <ᵣ v // P] ≤ α.val ∧ α.val < ℙ[X ≤ᵣ v // P]) :=
  by constructor
     · intro h
       constructor
       · have h1 : 1 - ℙ[X<ᵣv//P] ≥ 1 - α.val := by 
            simp_all [IsVaR,IsGreatest,quantileLower,IsQuantileLower,probability_geq_eq_one_sub]
         linarith
       · by_contra! hc
         obtain ⟨q,hq⟩ := exists_probability_leq_eq_probability_lt P X v
         have h3 : q ∈ quantileLower P X α.val := by
            rw [hq.2,probability_lt_eq_one_sub] at hc
            suffices ℙ[X≥ᵣq//P] ≥ 1 - α.val from this 
            linarith
         exact not_lt_of_ge (h.2 h3) hq.1
     · intro h
       constructor
       · exact mem_quantileLower_of_probability_lt h.1
       · by_contra! hc
         simp [upperBounds] at hc
         obtain ⟨q, hq⟩ := hc
         have hu : ℙ[X ≤ᵣ v // P] ≤ α.val :=
            calc ℙ[X ≤ᵣ v // P] ≤  ℙ[X <ᵣ q // P] := probability_leq_le_probability_lt hq.2
                 _ ≤ α.val := mem_quantileLower_iff_probability_lt.mp hq.1
         exact not_le_of_gt h.2 hu

-- This is the main correctness proof
theorem isVaR_finVaR : IsVaR P X α (finVaR P X α) := isVaR_iff.mpr finVaR_spec

theorem IsVaRQuantile.isQuantile : IsVaRQuantile P X α v → IsQuantile P X α.val v :=
    fun h => by simp_all only [Set.mem_ofPred_eq,IsVaRQuantile,quantile,IsGreatest]

theorem IsVaRQuantile.isQuantileLower : IsVaRQuantile P X α v → IsQuantileLower P X α.val v :=
    fun h => by simp_all only [Set.mem_ofPred_eq,IsVaRQuantile,quantile,IsGreatest,IsQuantileLower,IsQuantile]

theorem IsVaR.isQuantileLower : IsVaR P X α v → IsQuantileLower P X α.val v :=
    fun h => by simp_all only [Set.mem_ofPred_eq,IsVaR,quantileLower,IsGreatest]

theorem IsVaR.isQuantile : IsVaR P X α v → IsQuantile P X α.val v := by
    intro h
    constructor
    · suffices ℙ[X≤ᵣv//P] > α.val by linarith
      exact (isVaR_iff.mp h).2
    · exact IsVaR.isQuantileLower h

-- TODO: this should be in quantile.lean but it depends on VaR
theorem quantile_nonempty : (quantile P X α.val).Nonempty :=
  Set.nonempty_def.mpr ⟨ VaR[X// P,α], isVaR_finVaR  |> IsVaR.isQuantile ⟩

theorem isCofinalFor_quantileLower_quantile : IsCofinalFor (quantileLower P X α.val) (quantile P X α.val) := by
    intro q₁ h
    by_cases h2 : q₁ ∈ quantile P X α.val
    · exact ⟨q₁, h2, le_refl q₁⟩
    · rewrite [notMem_quantile_iff] at h2
      rewrite [mem_quantileLower_iff] at h
      cases' h2 with h2l h2r
      · obtain ⟨q₂, hq₂⟩ : (quantile P X α.val).Nonempty := quantile_nonempty
        use q₂
        constructor
        · exact hq₂
        · by_contra! ine
          exact ge_trans (probability_leq_mono (le_refl X) (le_of_lt ine)) (le_probability_leq_of_mem_quantile hq₂) |> not_le_of_gt h2l
      · exfalso; exact not_le_of_gt h2r h

theorem isCofinalFor_quantile_quantileLower : IsCofinalFor (quantile P X α.val) (quantileLower P X α.val) :=
    LE.le.isCofinalFor quantile_subset_quantileLower

theorem isVaRQuantile_iff_isVaR : IsVaRQuantile P X α v ↔ IsVaR P X α v := 
    ⟨fun h => ⟨IsVaRQuantile.isQuantileLower h, (upperBounds_mono_of_isCofinalFor isCofinalFor_quantileLower_quantile) h.2⟩,
     fun h => ⟨IsVaR.isQuantile h, (upperBounds_mono_of_isCofinalFor isCofinalFor_quantile_quantileLower) h.2⟩⟩

theorem isVaRQuantile_iff : IsVaRQuantile P X α v ↔ (ℙ[X <ᵣ v // P] ≤ α.val ∧ α.val < ℙ[ X ≤ᵣ v // P]) :=
  by rewrite[isVaRQuantile_iff_isVaR]; exact isVaR_iff

-------------------- VaR Properties ------------------------------------------------------

section VaR_properties

variable {P : Findist R Ω} {X Y : FinRV Ω R} {q q₁ v₁ v₂ c : R} {α : RiskLevel R} {f : R → R}

theorem IsVaR.le_of_le : X ≤ Y → IsVaR P X α v₁ → IsVaR P Y α v₂ → v₁ ≤ v₂ :=
  fun hle hv1 hv2 => upperBounds_mono_of_isCofinalFor (isCofinalFor_quantileLower_of_le hle) hv2.2 hv1.1

-- TODO(mathlib): literal alias of `add_left_strictMono` -- use the Mathlib name at call sites.
theorem const_monotone_univ : StrictMono (fun x ↦ x + c)  := add_left_strictMono

theorem IsVaR.add_const : IsVaR P X α v → IsVaR P (X+c•1) α (v+c) := by
    intro h
    rw [IsVaR,quantileLower_add_const_eq_image]
    exact MonotoneOn.map_isGreatest (Monotone.monotoneOn add_left_mono
                                    (quantileLower P X α.val)) h

theorem finVaR_add_const : VaR[X + c•1 // P, α] = VaR[X // P, α] + c := by
  have h1 : IsVaR P (X + c•1) α (VaR[X + c•1 // P, α]) := isVaR_finVaR
  have h2 : IsVaR P (X + c•1) α (VaR[X // P, α] + c) := IsVaR.add_const isVaR_finVaR
  exact le_antisymm (h2.2 h1.1) (h1.2 h2.1)

/-- If `f` is strictly monotone then `f(VaR[X])` is the VaR of `f∘X`. -/
theorem IsVaR.comp_of_strictMono (hm : StrictMono f) (hv : IsVaR P X α v) : IsVaR P (f ∘ X) α (f v) := by
  rw [isVaR_iff]
  rw [isVaR_iff] at hv
  rw [← hm.probability_lt_eq, ← hm.probability_leq_eq]
  exact hv


/-- Monotone transformation of VaR: for strictly monotone `f`, `VaR[f∘X] = f(VaR[X])`. -/
theorem finVaR_comp_of_strictMono (hm : StrictMono f) : VaR[f ∘ X // P, α] = f (VaR[X // P, α]) := by
  have h1 : IsVaR P (f ∘ X) α (VaR[f ∘ X // P, α]) := isVaR_finVaR
  have h2 : IsVaR P (f ∘ X) α (f (VaR[X // P, α])) := IsVaR.comp_of_strictMono hm isVaR_finVaR
  exact le_antisymm (h2.2 h1.1) (h1.2 h2.1)

-- TODO(naming): the statement writes `finVaR P (fun ω => c * X ω)` where the surrounding
-- lemmas use the `c • X` / notation form; `finVaR_const_mul` should be stated the same way
-- as its siblings so the names line up with the statements.
theorem finVaR_const_mul (hc : c > 0) : finVaR P (fun ω => c * X ω) α = c * finVaR P X α :=
  finVaR_comp_of_strictMono (fun _ _ hab => mul_lt_mul_of_pos_left hab hc)

end VaR_properties

end Risk


