/-
In this file we define histories and operations that are related to them. 

* Defines an MDP
* Defines a history, which is a sequence of states and actions
* Defines a histories consistent with a partial sequence of states and actions
* A general randomized history-dependent policy
* The reward and probability of the history, which is used to compute the value function
* Value function for a history as the expected reward
-/

import Mathlib.Data.Nat.Defs

import Mathlib.Data.Real.Basic 
import Mathlib.Data.NNReal.Basic

--import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Defs -- Injective

import Mathlib.Probability.ProbabilityMassFunction.Basic
--variable (α σ : Type)

import LeanMDPs.Finprob

namespace MDPs

variable {σ α : Type}
--variable [Inhabited σ] [Inhabited α] -- used to construct policies

open NNReal -- for ℝ≥0 notation
open Finprob

section Definitions

/-- Markov decision process -/
structure MDP (σ α : Type) : Type where
  /-- states -/
  S : Finset σ
  S_ne : S.Nonempty
  /-- actions  -/
  A : Finset α
  A_ne : A.Nonempty
  /-- transition probability s, a, s' -/
  P : σ → α → Δ S  -- TODO : change to S → A → Δ S
  /-- reward function s, a, s' -/
  r : σ → α → σ → ℝ -- TODO: change to S → A → S → ℝ
  
end Definitions

variable {M : MDP σ α}

section Histories

/-- Represents a history. The state is type σ and action is type α. -/
inductive Hist {σ α : Type} (M : MDP σ α)  : Type where
  | init : σ → Hist M
  | foll : Hist M → α → σ → Hist M

/-- Coerces a state to a history -/
instance : Coe σ (Hist M) where
  coe s := Hist.init s

/-- The length of the history corresponds to the zero-based step of the decision -/
@[reducible] def Hist.length : Hist M → ℕ
  | init _ => 0
  | Hist.foll h _ _ => 1 + length h 

/-- Nonempty histories -/
abbrev HistNE {σ α : Type} (m : MDP σ α) : Type := {h : Hist m // h.length ≥ 1}

/-- Returns the last state of the history -/
def Hist.last : Hist M → σ
  | init s => s
  | Hist.foll _ _ s => s

/-- Appends the state and action to the history --/
def Hist.append (h : Hist M) (as : α × σ) : Hist M := h.foll as.1 as.2
-- TODO: remove?

def Hist.one (s₀ : σ) (a : α) (s : σ) : Hist M := (Hist.init s₀).foll a s

/-- Return the prefix of hist of length k -/
def Hist.prefix (k : ℕ)  (h : Hist M) : Hist M :=
    match h with
      | Hist.init s => Hist.init s
      | Hist.foll hp a s =>      
        if hp.length + 1 ≤ k then hp.foll a s
        else hp.prefix k
  
def tuple2hist : Hist M × α × σ → HistNE M
  | ⟨h, as⟩ => ⟨h.append as, Nat.le.intro rfl⟩
def hist2tuple : HistNE M → Hist M × α × σ
  | ⟨Hist.foll h a s, _ ⟩ => ⟨h, a, s⟩
  
open Function 

lemma linv_hist2tuple_tuple2hist : 
      LeftInverse (hist2tuple (M := M)) tuple2hist := fun _ => rfl
lemma inj_tuple2hist_l1 : Injective (tuple2hist (M:=M)) :=
        LeftInverse.injective linv_hist2tuple_tuple2hist
lemma inj_tuple2hist : Injective ((Subtype.val) ∘ (tuple2hist (M:=M))) := 
    Injective.comp (Subtype.val_injective) inj_tuple2hist_l1

def emb_tuple2hist_l1 : Hist M × α × σ ↪ HistNE M := ⟨tuple2hist, inj_tuple2hist_l1⟩
def emb_tuple2hist : Hist M × α × σ ↪ Hist M  := ⟨λ x ↦ tuple2hist x, inj_tuple2hist⟩

--- state
def state2hist (s : σ) : Hist M := Hist.init s
def hist2state : Hist M → σ | Hist.init s => s | Hist.foll _ _ s => s
    
lemma linv_hist2state_state2hist : LeftInverse (hist2state (M:=M)) state2hist := fun _ => rfl
lemma inj_state2hist : Injective (state2hist (M:=M)) := 
                     LeftInverse.injective linv_hist2state_state2hist
                     
def state2hist_emb : σ ↪ Hist M := ⟨state2hist, inj_state2hist⟩

/-- Checks if the first hist is the prefix of the second hist. -/
def isprefix : Hist M → Hist M → Prop 
    | Hist.init s₁, Hist.init s₂ => s₁ = s₂
    | Hist.init s₁, Hist.foll hp _ _ => isprefix (Hist.init s₁) hp 
    | Hist.foll _ _ _, Hist.init _ => False
    | Hist.foll h₁ a₁ s₁', Hist.foll  h₂ a₂ s₂' => 
        if h₁.length > h₂.length then
            False
        else if h₁.length < h₂.length then
            let pre := Hist.foll h₁ a₁ s₁' 
            isprefix pre h₂
        else
            (a₁ = a₂) ∧ (s₁' = s₂') ∧ (isprefix h₁ h₂)

/-- All histories of additional length t that follow history h -/
def Histories (h : Hist M) : ℕ → Finset (Hist M) 
    | Nat.zero => {h}
    | Nat.succ t => ((Histories h t) ×ˢ M.A ×ˢ M.S).map emb_tuple2hist

abbrev ℋ : Hist M → ℕ → Finset (Hist M) := Histories

theorem hist_lenth_eq_horizon (h : Hist M) (t : ℕ): ∀ h' ∈ (ℋ h t), h'.length = h.length + t := sorry

/-- All histories of a given length  -/
def HistoriesHorizon : ℕ → Finset (Hist M)
  | Nat.zero => M.S.map state2hist_emb 
  | Nat.succ t => ((HistoriesHorizon t) ×ˢ M.A ×ˢ M.S).map emb_tuple2hist


abbrev ℋₜ : ℕ → Finset (Hist M) := HistoriesHorizon

--theorem Histories

end Histories

section Policies

/-- A randomized history-dependent policy -/
def PolicyHR (M : MDP σ α) : Type := Hist M → Δ M.A

instance [DecidableEq α] : Coe M.A (PolicyHR M) where
  coe a := fun _ ↦ dirac_dist M.A a

/-- Decision rule -/
def DecisionRule (M : MDP σ α) := σ → M.A

instance [DecidableEq α] : Coe M.A (DecisionRule M) where
  coe a := fun _ ↦ a

/-- A deterministic stationary policy -/
def PolicySD (M : MDP σ α) : Type := DecisionRule M

instance [DecidableEq α] : Coe (PolicySD M) (PolicyHR M) where
  coe d := fun h ↦ dirac_dist M.A (d h.last)


end Policies

section Distribution

/-- Probability distribution over histories induced by the policy and 
    transition probabilities -/
def HistDist (h : Hist M) (π : PolicyHR M) (T : ℕ) : Δ (ℋ h T) :=
  match T with 
    | Nat.zero => dirac_ofsingleton h
    | Nat.succ t => 
      let prev := HistDist h π t 
      let update h' (as : α × σ) := ((π h').p as.1 * (M.P h'.last as.1).p as.2)
      let probability : Hist M → ℝ≥0 
        | Hist.init _ => 0 --ignored
        | Hist.foll h' a s => prev.p h' * update h' ⟨a,s⟩
      -- proof of probability
      let sumsto_as (h' : Hist M) _ : ∑ as ∈ M.A ×ˢ M.S, update h' as = 1 :=
          prob_prod_prob (π h').p (fun a =>(M.P h'.last a).p ) 
                         (π h').sumsto (fun a _ => (M.P h'.last a).sumsto)
      let sumsto : ∑ ⟨h',as⟩ ∈ ((ℋ h t) ×ˢ M.A ×ˢ M.S), prev.p h' * update h' as = 1 := 
          prob_prod_prob prev.p update prev.sumsto sumsto_as 
      let HAS := ((ℋ h t) ×ˢ M.A ×ˢ M.S).map emb_tuple2hist
      have sumsto_fin : ∑ h' ∈ HAS, probability h'  = 1 := 
          (Finset.sum_map ((ℋ h t) ×ˢ M.A ×ˢ M.S) emb_tuple2hist probability) ▸ sumsto
      ⟨probability, sumsto_fin⟩

abbrev Δℋ (h : Hist M) (π : PolicyHR M) (T : ℕ) : Finprob (Hist M) := 
          ⟨ℋ h T, HistDist h π T⟩

--theorem 

/- Computes the probability of a history -/
/-def probability  (π : PolicyHR m) : Hist m → ℝ≥0 
      | Hist.init s => m.μ.p s
      | Hist.prev hp a s' => probability π hp * ((π hp).p a * (m.P hp.last a).p s')  
-/

/-- Reward of a history -/
def reward : Hist M → ℝ 
    | Hist.init _ => 0
    | Hist.foll hp a s' => (M.r hp.last a s') + (reward hp)  

/-- Reward at a specific position; 0-based -/    
def reward_at (i : ℕ) : Hist M → ℝ 
    | Hist.init _ => 0
    | Hist.foll hp a s' => 
      if hp.length = i then (M.r hp.last a s')
      else reward_at i hp
      
/-- Sum of rewards from a specific position to the end -/
def reward_to (j : ℕ) : Hist M → ℝ
    | Hist.init _ => 0
    | Hist.foll hp a s' =>
      if hp.length ≤ j then (M.r hp.last a s') + (reward hp)
      else reward_to j hp

/-- Sum of rewards from a specific position to the end -/
def reward_from (j : ℕ) : Hist M → ℝ
    | Hist.init _ => 0
    | Hist.foll hp a s' =>
      if hp.length ≥ j  then (M.r hp.last a s') + (reward_from j hp)
      else 0
      

/-- The probability of a history -/
def prob_h (h : Hist M) (π : PolicyHR M) (T : ℕ) (h' : ℋ h T) : ℝ≥0 := (Δℋ h π T).2.p h'

/-- Probability of a boolean event -/
def probability_h (h : Hist M) (π : PolicyHR M) (T : ℕ) (B : Hist M → Bool) : ℝ≥0 := 
        let P := Δℋ h π T
        probability (⟨B⟩ : Finrv P Bool)

scoped[MDPs] notation "ℙₕ[" B "//" h "," π "," t "]" => probability_h h π t B

/- ----------- Expectations ---------------- -/

--variable {ρ : Type} [HMulZero ρ] [HMul ℕ ρ ρ] [AddCommMonoid ρ]

/-- Expectation over histories for a r.v. X for horizon T and policy π -/
def expect_h (h : Hist M) (π : PolicyHR M) (T : ℕ) (X : Hist M → ℝ) : ℝ := 
        let P := Δℋ h π T
        expect (⟨X⟩ : Finrv P ℝ)

scoped[MDPs] notation "𝔼ₕ[" X "//" h "," π "," t "]" => expect_h h π t X

/-- Condtional expectation over histories for a r.v. X for horizon T and policy π -/
noncomputable
def expect_h_cnd (h : Hist M) (π : PolicyHR M) (T : ℕ) (X : Hist M → ℝ)  (B : Hist M → Bool): ℝ := 
    have P := Δℋ h π T
    expect_cnd (⟨X⟩ : Finrv P ℝ) (⟨B⟩ : Finrv P Bool)
    
scoped[MDPs] notation "𝔼ₕ[" X "|" B "//" h "," π "," t "]" => expect_h_cnd h π t X B

noncomputable
def expect_h_cnd_rv (h : Hist M) (π : PolicyHR M) (T : ℕ) (X : Hist M → ℝ) 
                    {ν : Type} [DecidableEq ν] (Y : Hist M → ν): Hist M → ℝ := 
    have P := Δℋ h π T
    fun h ↦ expect_cnd (⟨X⟩ : Finrv P ℝ) ((⟨Y⟩ : Finrv P ν) ᵣ== Y h)

scoped[MDPs] notation "𝔼ₕ[" X "|ᵥ" Y "//" h "," π "," t "]" => expect_h_cnd_rv h π t X Y

/-- The k-th state of a history. The initial state is state 0. -/
def state  (k : ℕ) (h : Hist M) : σ := 
    match h with
    | Hist.init s => s
    | Hist.foll h' a s => if (h'.foll a s).length = k then s else (state k h') 
    
   
/-- The k-th action of a history. The first action is action 0.  -/
def action  [Inhabited α] (k : ℕ) (h : Hist M) : α := 
    match h with
    | Hist.init _ => Inhabited.default -- no valid action
    | Hist.foll h' a _ => if h.length = k then a else action k h'
    
/-- Random variable on histories sans distribution (policy dependent) -/
def Histrv (M : MDP σ α) := Hist M → ℝ

instance instCoeRtoRV: Coe ℝ (Histrv M) where
  coe c := fun _ ↦ c

instance instHAddHRV : HAdd (Histrv M) (Histrv M) (Histrv M) where
  hAdd a b := fun h ↦ a h + b h
  
instance instHAddRVRV : HAdd ℝ (Histrv M) (Histrv M) where
  hAdd a b := fun h ↦ a + b h

end Distribution

section BasicProperties

variable {h : Hist M} {π : PolicyHR M} {t : ℕ} 

theorem exph_add_rv (X : Histrv M) (Y : Histrv M) :
        𝔼ₕ[ X+Y // h,π,t] = 𝔼ₕ[ X // h,π,t] + 𝔼ₕ[ Y // h,π,t] := sorry
  
theorem exph_const (X : Histrv M) (c : ℝ) :
  𝔼ₕ[ (c : Histrv M) // h, π, t] = c := sorry

theorem exph_add_const (X : Hist M → ℝ) (c : ℝ) : 
        𝔼ₕ[ (c + X : Histrv M) // h, π, t]  = c + 𝔼ₕ[ X // h, π, t] := sorry
       
-- TODO: add the supported condition
/-- Expected return can be expressed as a sum of expected rewards -/
theorem exph_congr (X : Hist M → ℝ) (Y : Hist M → ℝ)
                   (rv_eq : ∀ h' ∈ ℋ h t, X h' = Y h') : 
        𝔼ₕ[ X // h, π, t]  = 𝔼ₕ[ Y // h, π, t] := 
          let P := Δℋ h π t
          --let Peq : P.Ω = ℋ h T := rfl
          let X' : Finrv P ℝ := ⟨X⟩
          let Y' : Finrv P ℝ := ⟨Y⟩
          let rv_eq': ∀h'∈ P.Ω, P.supp h' → X'.val h' = Y'.val h' := fun h'' a _ => rv_eq h'' a
          exp_congr rv_eq'     
          

def rew_sum [Inhabited α] (h : Hist M) := 
    ∑ k ∈ Finset.range h.length, M.r (state k h) (action k h) (state (k+1) h)
    
/-- Sum of rewards with start (b) and end (e) (is exclusive) -/
def rew_sum_rg [Inhabited α] (b : ℕ) (e : ℕ) (h : Hist M) := 
    ∑ k ∈ Finset.range (e-b), M.r (state (b+k) h) (action (b+k) h) (state (b+k+1) h)
    
-- Examples of proving with if then else, see also if_pos and if_neg for proofs and use
example (t : ℕ) [d: DecidableEq ℕ] : (if t+1 = t then 1 else 0) = 0 := 
  match d (t+1) t with
  | isTrue h => (Nat.add_one_ne t h).rec  -- or by cases
  | isFalse _ => rfl
example (t : ℕ) [d: DecidableEq ℕ] : (if t+1 = t then 1 else 0) = 0 := 
  if h : t+1 = t then 
    (Nat.add_one_ne t h).rec  -- or by cases h
  else
    by simp  only [add_right_eq_self, one_ne_zero, ↓reduceIte]

example (t : ℕ) : t ≠ t + 1 := Nat.ne_add_one t
-- see: https://proofassistants.stackexchange.com/questions/1565/how-to-prove-a-property-of-a-conditional-statement-without-using-tactics-in-lean

lemma state_last  {k : ℕ} (keq : k = h.length): state k h = h.last :=  
        by rw[keq]; cases h; simp!; simp!       

lemma state_foll_last {s : σ} {a : α} {k : ℕ} (keq : k = h.length): 
        state k (h.foll a s) = h.last :=
      by rw[keq]; cases h; simp!; simp!

lemma action_last {s : σ} {a : α} [Inhabited α] {h : Hist M} {k : ℕ} (keq : k = h.length + 1): 
        action (h.foll a s).length (h.foll a s) = a := by cases h; simp!; simp!

lemma state_foll_eq {s : σ} {a : α} {k : ℕ} (kleq : k ≤ h.length) : 
  state k h = state k (h.foll a s) :=  
        match h with
        | Hist.init s' => if 1 = k then by simp_all! else by simp_all!
        | Hist.foll h' a' s' =>
            let hh := h'.foll a' s' --weird; cannot use h
            if p: hh.length = k then calc
              state k hh = hh.last := state_last p.symm
              _ = state k (hh.foll a s) := (state_foll_last p.symm).symm                
            else
              have pse : k < hh.length := Nat.lt_of_le_of_ne kleq (fun a ↦ p a.symm)
              have pneq_foll : (hh.foll a s).length ≠ k := by simp_all!; linarith
              (if_neg pneq_foll).symm
        
variable [Inhabited σ] [Inhabited α]

lemma ret_eq_sum_rew (h : Hist M) : reward h = rew_sum h := 
  match h with 
  | Hist.init s => rfl
  | Hist.foll h' a s => 
    let t := h'.length  --last step
    let hh := Hist.foll h' a s
    let tp1 : hh.length = t + 1 := Nat.add_comm 1 t
    let fr h k := M.r (state k h) (action k h) (state (k+1) h)
    let rew_eq : fr hh t = (M.r h'.last a s) := sorry
    let fr_eq k (kl : k < t) : fr h' k = fr hh k := sorry  
    let sum_fr_eq : 
        ∑ k ∈ Finset.range t, fr h' k = ∑ k ∈ Finset.range t, fr hh k := 
          Finset.sum_congr rfl (fun k a => fr_eq k (Finset.mem_range.mp a))
    calc
      reward hh  = (M.r h'.last a s) + (reward h') := rfl
      _ = fr hh t + (rew_sum h') := by rw[ret_eq_sum_rew h', rew_eq]
      _ = fr hh t + ∑ k ∈ Finset.range t, fr h' k := rfl
      _ = fr hh t + ∑ k ∈ Finset.range t, fr hh k := by rw[sum_fr_eq]
      _ = ∑ k ∈ Finset.range (t+1), fr hh k := 
          by simp [Finset.sum_insert, Finset.range_succ]
      _ = ∑ k ∈ Finset.range hh.length, fr hh k := by simp[tp1]
      _ = rew_sum hh := rfl


/-- Expected return can be expressed as a sum of expected rewards -/
theorem expret_eq_sum_rew : 𝔼ₕ[ reward // h, π, t]  = 𝔼ₕ[ rew_sum // h, π, t ] := 
        exph_congr reward rew_sum (fun h' _ ↦ ret_eq_sum_rew h') 
        

theorem sum_rew_eq_sum_rew_rg  : 
    𝔼ₕ[ rew_sum // h, π, t ] = rew_sum h + 𝔼ₕ[ rew_sum_rg (h.length) t  // h, π, t ] := sorry

theorem exph_zero_horizon_eq_zero  (hzero : h.length = 0) :
    𝔼ₕ[ reward // h, π, 0] = 0 := by 
    cases h
    sorry -- the interesting case
    simp_all! only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, false_and]

theorem exph_zero_horizon_eq_zero_f (hzero : h.length = 0) :
    𝔼ₕ[ reward_from 0 // h, π, 0] = 0 := by 
    cases h
    sorry -- the interesting case
    simp_all! only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, false_and]

/-- When the random variable beyond a point does not matter, cut the horizon's expectation -/
theorem exph_horizon_cut {X : Histrv M} (k : ℕ) (kle : k ≤ t) 
        (eqpastk : ∀h : Hist M, X h = X (h.prefix k)) :
        𝔼ₕ[ X // h,π,t ] = 𝔼ₕ[ X // h,π,k ] := sorry

theorem exph_horizon_trim {X : Histrv M} {h : Hist M} :
    ∀ (s : M.S) (a : M.A), X (h.foll a s) = X (Hist.one h.last a s) → 
      𝔼ₕ[ X // h,π,1 ] = 𝔼ₕ[ X // h.last,π,1 ] := 
    sorry



end BasicProperties

/- ------------ Law of total expectation ----------/

section TotalExpectation

--variable {ρ : Type} [HMulZero ρ] [AddCommMonoid ρ] 
variable {ν : Type} [DecidableEq ν] {V : Finset ν}
variable { h : Hist M } { π : PolicyHR M } { t : ℕ }
variable { X : Hist M → ℝ } { Y : Hist M → ν }

theorem total_expectation_h : 𝔼ₕ[ (𝔼ₕ[ X |ᵥ Y // h, π, t]) // h, π, t ] = 𝔼ₕ[ X // h, π, t ] := sorry

end TotalExpectation
 
section ConditionalProperties

variable {ν : Type} [DecidableEq ν] {V : Finset ν}
variable { h : Hist M } { π : PolicyHR M } { t : ℕ }
variable { X : Hist M → ℝ } { Y : Hist M → ν }

theorem exph_cond_eq_hist (s : M.S) (a : M.A) [Inhabited α] [Inhabited σ] [BEq α] [BEq σ]: 
  𝔼ₕ[ reward | (fun h' ↦ (action h.length h' == a) ∧ (state (h.length+1) h' == s)) // h, π, (t+1)  ] =
  𝔼ₕ[ reward // (h.foll a s), π, t] := sorry

end ConditionalProperties

end MDPs

/- Conditional expectation with future singletons -/
/-theorem hist_tower_property {hₖ : Hist m} {π : PolicyHR m} {t : ℕ} {f : Hist m → ℝ}
  (valid : hₖ ∈ ℋ hₖ t) 
  : 𝔼ₕ hₖ π 1 f = (∑ a ∈ m.A, ∑ s ∈ m.S, f (Hist.prev hₖ a s)) := sorry
-/
-- TODO: write a general tower property result first, and then derive a version of this
-- result, which needs to apply over multiple time steps. 

/-
TODO:
2. Show that is the policy is Markov then also the value function is Markov
-/
