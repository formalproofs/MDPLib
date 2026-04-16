import LeanMDPs.Histories

--set_option diagnostics true
--set_option diagnostics.threshold 3

open NNReal
open Finprob
--open MDPs


section ArgMax

variable {τ : Type*} {a m : τ} {S : Finset τ} {f : S → ℝ}

noncomputable 
def Finset.argmax' (I: Finset τ) (H : I.Nonempty) (f : I → ℝ)  : I :=
  -- TODO: make it implemtable by directly applying fold as in Finset.sum
  let M := List.argmax f I.attach.toList
  let H1 : I.attach.toList ≠ [] := Finset.Nonempty.toList_ne_nil (Finset.attach_nonempty_iff.mpr H)
  let H2 : M ≠ none := fun eq ↦ H1 (List.argmax_eq_none.mp eq)
  match M, H2 with 
  | (x:I),_ => x

#check List.argmax

theorem le_of_mem_argmax'  
  (h : a ∈ S) (NE : S.Nonempty) : f ⟨a, h⟩ ≤ f (S.argmax' NE f)  := 
     let m := S.argmax' NE f
     sorry

theorem argmax_eq_sup (NE : S.Nonempty) : 
    S.attach.sup' (Finset.attach_nonempty_iff.mpr NE) f = f (S.argmax' NE f) := sorry

example : a ∈ S.toList ↔ a ∈ S := Finset.mem_toList
example (h : a ∈ S) : ⟨a,h⟩ ∈ S.attach  := Finset.mem_attach S ⟨a, h⟩

end ArgMax

namespace MDPs

/- state -/
variable {σ : Type} [Inhabited σ] [DecidableEq σ] 
/- action -/
variable {α : Type} [Inhabited α] [DecidableEq α]
variable {M : MDP σ α}

section Objectives

/-- Finite horizon objective parameters -/
structure ObjectiveFH (M : MDP σ α) : Type where
  s₀ : M.S -- initial state
  T : ℕ -- horizon

/-- Objective function -/
def objective_fh (O : ObjectiveFH M) (π : PolicyHR M) := 𝔼ₕ[ reward // O.s₀, π, O.T]

/-- An optimal policy πopt -/
def Optimal_fh (O : ObjectiveFH M) (πopt : PolicyHR M) := ∀ π : PolicyHR M, objective_fh O πopt ≥ objective_fh O π

/-- Value function type for history-dependent value functions -/
def ValuesH (M : MDP σ α) : Type := Hist M → ℝ

/-- History-dependent value function -/
def hvalue_π (π : PolicyHR M) : ℕ → ValuesH M
  | Nat.zero => fun _ ↦ 0
  | Nat.succ t => fun h ↦ 𝔼ₕ[ reward_from h.length // h,π,t.succ ] 
  
-- TODO: This needs some thought to be defined properly
--def hvalue_opt : ℕ → ValuesH M
--    | Nat.zero => fun _ ↦ 0
--    | Nat.succ t => fun h => fun π ↦ hvalue_π π  

/-- A value-optimal policy πopt -/
def OptimalVF_fh (t : ℕ) (πopt : PolicyHR M) := ∀ π : PolicyHR M, ∀ h : Hist M, hvalue_π πopt t h ≥ hvalue_π π t h

omit [Inhabited σ] [DecidableEq σ] [Inhabited α] [DecidableEq α] 
lemma reward_eq_reward_from_0 : ∀h : Hist M, reward h = reward_from 0 h :=      
           fun h => by induction h; simp! only []; simp_all!

theorem optimalvf_imp_optimal {O : ObjectiveFH M} 
  (πopt : PolicyHR M) (opt : OptimalVF_fh O.T πopt) : (Optimal_fh O πopt) :=  
        fun π => calc
            objective_fh O πopt = 𝔼ₕ[ reward // O.s₀, πopt, O.T] := rfl
            _ = 𝔼ₕ[ reward_from 0 // O.s₀, πopt, O.T] := 
                    exph_congr reward (reward_from 0) (fun h' a ↦ reward_eq_reward_from_0 h')
            _ = hvalue_π πopt O.T O.s₀ := 
                sorry -- by cases O.T; simp![exph_zero_horizon_eq_zero_f]; simp_all!
            _ ≥ hvalue_π π O.T O.s₀ := opt π (Hist.init ↑O.s₀)
            _ =  𝔼ₕ[ reward_from 0 // O.s₀, π, O.T] := 
                    sorry --by cases O.T; simp![exph_zero_horizon_eq_zero_f]; dsimp!
            _ = 𝔼ₕ[ reward // O.s₀, π, O.T] := 
                exph_congr (reward_from 0) reward (fun h' a ↦ (reward_eq_reward_from_0 h').symm)
            _ = objective_fh O π := rfl
                
end Objectives

section HistoryDP

/-- Bellman operator on history-dependent value functions -/
def DPhπ (π : PolicyHR M) (v : ValuesH M) : ValuesH M 
  | h => 𝔼ₕ[ fun h' ↦ reward h' + v h' // h, π, 1 ]
  
/-- Bellman operator on history-dependent value functions -/
def DPhopt (u : ValuesH M) : ValuesH M 
  | h => let q (a : M.A) :=  𝔼ₕ[fun h' ↦ reward_at h.length h' + u h' // h, a, 1]
         M.A.attach.sup' (Finset.attach_nonempty_iff.mpr M.A_ne) q

--let q a :=  ∑ s' ∈ M.S, (M.P h.last a).p s' * (M.r h.last a s' + vₜ (h.foll a s'))

/-- Dynamic program value function, finite-horizon history dependent -/
def u_dp_π (π : PolicyHR M) : ℕ → ValuesH M 
  | Nat.zero => fun _ ↦ 0
  | Nat.succ t => DPhπ π (u_dp_π π t)


/-- Dynamic program value function, finite-horizon history dependent -/
def u_dp_opt  : ℕ → ValuesH M 
  | Nat.zero => fun _ ↦ 0
  | Nat.succ t => DPhopt (u_dp_opt t)
  
theorem dp_opt_ge_dp_pi (h : Hist M) (u₁ u₂ : ValuesH M) (uge : ∀h : Hist M, u₁ h ≥ u₂ h) :
        ∀h : Hist M, ∀π : PolicyHR M, DPhopt u₁ h ≥ DPhπ π u₂ h := sorry


theorem dph_correct_vf (π : PolicyHR M) (t : ℕ) (h : Hist M) : hvalue_π π t h = u_dp_π π t h := 
   match t with
     | Nat.zero => rfl
     | Nat.succ t => 
       let hp h' := dph_correct_vf π t h'
       sorry

theorem dph_opt_vf_opt (t : ℕ) : 
        ∀π : PolicyHR M, ∀ h : Hist M, u_dp_opt t h ≥ u_dp_π π t h := sorry 

end HistoryDP


section MarkovOptimality -- Markov policies and value functions as a dynamic program

/-- A deterministic Markov policy. Depends on the time step, 
and does not depend on the horizon. -/
def PolicyMD (M : MDP σ α) : Type := ℕ → DecisionRule M

instance [DecidableEq α] : Coe (PolicyMD M) (PolicyHR M) where
  coe d := fun h ↦ dirac_dist M.A (d h.length h.last)

/-- History-independent value function. Note that the optimal
value function is history-independent, while the 
value function of a Markov policy depends on the time step. -/
def Values (_ : MDP σ α) := σ → ℝ

/-- Markov q function -/
def q_of_v (s : σ) (a : M.A) (v : Values M) : ℝ :=
 𝔼ₕ[ fun h ↦ reward h + v h.last // (s:Hist M), (a:PolicyHR M), 1 ]

/-- Bellman operator on history-dependent value functions -/
def DPMopt (v : Values M) : Values M
  | s => M.A.attach.sup' (Finset.attach_nonempty_iff.mpr M.A_ne) (fun a ↦ q_of_v s a v)


/-- Optimal value function -/
def v_dp_opt : ℕ → Values M
  | Nat.zero => fun _ ↦ 0
  | Nat.succ t => DPMopt (v_dp_opt t)


variable {t : ℕ}

/-- The Markov DP is optimal -/
theorem v_dp_opt_eq_u_opt : ∀h : Hist M, v_dp_opt (M:=M) t h.last = u_dp_opt t h := 
  sorry


/-- Optimal policy for horizon t -/
noncomputable
def πopt (t : ℕ) : PolicyMD M 
  | k, s => 
    if t ≥ k then 
       M.A.argmax' M.A_ne (fun a ↦ q_of_v s a (v_dp_opt (t-k)) )
    else
      -- just return some action
      Classical.indefiniteDescription (fun a ↦ a ∈ M.A) M.A_ne

/-- Greedy to v_opt is optimal policy -/
theorem v_dp_opt_eq_v_dp_π {T : ℕ} : ∀h : Hist M, h.length ≤ T → 
           v_dp_opt (M:=M) (T - h.length) h.last = u_dp_π (πopt (M:=M) T) (T - h.length) h := 
        sorry

end MarkovOptimality

section MarkovEvaluation


def ValuesM (_ : MDP σ α) := ℕ → σ → ℝ

/-- Optimal Bellman operator on state-dependent value functions. Also includes
the prior history's reward. -/
def DPMπ (π : PolicyMD M) (v : ValuesM M) : ValuesM M 
  | k,s => 𝔼ₕ[ fun h ↦ reward h + v (k+1) h.last // s, (π : PolicyHR M), 1 ]

/-- Value function of a Markov policy. Horizon to value function. -/
def v_dp_π (π:PolicyMD M) : ℕ → ValuesM M
  | Nat.zero => fun _ ↦ 0
  | Nat.succ t => DPMπ π (v_dp_π π t)

variable {t : ℕ} {π : PolicyMD M}

theorem v_eq_u_π : ∀ h : Hist M, u_dp_π π t h = v_dp_π π t h.length h.last := sorry

theorem markov_u_quot : 
  ∀ h₁ h₂ : Hist M, h₁.length = h₂.length ∧ h₁.last = h₂.last → u_dp_π π t h₁ = u_dp_π π t h₂ := 
        fun h₁ h₂ => fun a => by simp_all [v_eq_u_π]

end MarkovEvaluation


end MDPs

