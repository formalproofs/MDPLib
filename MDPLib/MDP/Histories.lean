/-
In this file we define histories and operations that are related to them.

* Defines an MDP
* Defines a history, which is a sequence of states and actions
* Defines a histories consistent with a partial sequence of states and actions
* A general randomized history-dependent policy
* The reward and probability of the history, which is used to compute the value function
* Value function for a history as the expected reward
-/
import Mathlib.Data.Nat.Basic

import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import MDPLib.Probability.Basic

namespace MDPs

section Definitions

open Findist

/-- Markov decision process -/
structure MDP : Type where
  /-- states -/
  S : ℕ
  S_ne : 0 < S
  /-- actions  -/
  A : ℕ
  A_ne : 0 < A
  /-- transition probability s, a, s' -/
  P : Fin S → Fin A → Δ (Fin S)
  /-- reward function s, a, s' -/
  r : Fin S → Fin A → Fin S → ℝ

variable (M : MDP)

def MDP.maxS : Fin M.S := ⟨M.S-1, by simp [M.S_ne]⟩
def MDP.maxA : Fin M.A := ⟨M.A-1, by simp [M.A_ne]⟩

-- here, we use the fintype property to show that the state and action
-- sets are complete 

abbrev MDP.St := Fin M.S 
abbrev MDP.At := Fin M.A

/-- Set of all states -/
def MDP.setS : Finset M.St := Fintype.elems 
/-- Set of all actions -/
def MDP.setA : Finset M.At := Fintype.elems

theorem MDP.inS : ∀s : M.St, s ∈ M.setS := Fintype.complete
theorem MDP.inA : ∀a : M.At, a ∈ M.setA := Fintype.complete

def MDP.SA := M.S * M.A

theorem MDP.SA_ne : 0 < M.SA := Nat.mul_pos M.S_ne M.A_ne

end Definitions

variable {M : MDP}

section Histories

/-- Represents a history. The state is type ℕ and action is type ℕ. -/
inductive Hist (M : MDP)  : Type where
  | init : Fin M.S → Hist M
  | foll : Hist M → Fin M.A → Fin M.S → Hist M

instance : Coe (Fin M.S) (Hist M) where
  coe s := Hist.init s

/-- History's length = the number of actions taken -/
@[simp]
def Hist.length : Hist M → ℕ
  | init _ => 0
  | Hist.foll h _ _ => 1 + length h

def MDP.HistT (M : MDP) (t : ℕ) := {h : Hist M // h.length = t}

-- TODO: We should prove that HistT is a Fintype in order to be able to perform operations on it

/-- Nonempty histories -/
abbrev HistNE (M : MDP) := {m : Hist M // m.length ≥ 1}

/-- Returns the last state of the history -/
def Hist.last : Hist M → Fin M.S
  | init s => s
  | Hist.foll _ _ s => s

/-- Number of histories of length t. -/
@[simp]
def MDP.numhist (M : MDP) (t : ℕ) : ℕ := M.S * M.SA^t

theorem hist_len_zero : M.numhist 0 = M.S := by simp [MDP.numhist]

--------------------------- START: Explicit index for hist -------------------------------------------------------------------
section ExplicitHistIndex

/-- Construct i-th history of length t -/
def MDP.idx_to_hist (M : MDP) (t : ℕ) (i : Fin (M.numhist t)) : M.HistT t := 
  match t with
  | Nat.zero => 
      let ii : Fin M.S := ⟨i.1, by have h := i.2; simp_all [MDP.numhist] ⟩
      ⟨Hist.init ii,  rfl⟩
  | Nat.succ t' =>
      let sa : ℕ := i % M.SA 
      let s : Fin M.S := ⟨sa  % M.S,  Nat.mod_lt sa M.S_ne ⟩
      let a : Fin M.A := ⟨(sa / M.S) % M.A, Nat.mod_lt (sa/M.S) M.A_ne⟩
      let ni : ℕ := (i - sa) / M.SA
      let h1 : M.SA ∣ (i - sa) := Nat.dvd_sub_mod ↑i
      let h2 : ni < M.numhist t' :=  
        by have h := i.2
           unfold MDP.numhist at h ⊢
           have h6 : M.SA ∣ M.S*M.SA^t'.succ := 
                  by apply Nat.dvd_mul_left_of_dvd ?_ M.S; exact Dvd.intro_left (M.SA.pow t') rfl
           have h7 : M.S*M.SA^t' = M.S*M.SA^t'.succ / M.SA :=
              by calc M.S*M.SA^t' = M.S*M.SA^t'* M.SA / M.SA := Eq.symm (Nat.mul_div_left (M.S*M.SA^t') M.SA_ne)
                      _ = M.S*M.SA^t'.succ / M.SA :=  by rw [Nat.mul_assoc,←Nat.pow_succ]
           subst ni 
           rw [h7]
           exact Nat.div_lt_div_of_lt_of_dvd h6 (Nat.sub_lt_of_lt h)
      let h' := M.idx_to_hist t' ⟨ni, h2⟩
      ⟨ h'.1.foll a s , 
        by simp only [Hist.length, h'.2, Nat.succ_eq_add_one]; exact Nat.add_comm 1 t'⟩ 

lemma Nat.sum_one_prod_cancel (n : ℕ) {m : ℕ} (h : 0 < m) : (m-1) * n + n = m*n := 
  by rw [Nat.sub_one_mul]
     apply Nat.sub_add_cancel
     exact Nat.le_mul_of_pos_left n h 

/-- Compute the index of a history  -/
def MDP.hist_to_idx (M : MDP) (h : Hist M) : Fin (M.numhist h.length) := 
    match h with 
    | Hist.init s => ⟨s, by simp only [numhist, Hist.length, pow_zero, mul_one, Fin.is_lt]⟩
    | Hist.foll h' a s => 
        let n' := M.hist_to_idx h'
        let n := M.SA * ↑n' + (a * M.S + s)
        have h : a * M.S + s < M.SA := 
            by unfold MDP.SA
               calc a * M.S + s < a * M.S + M.S := 
                        by grw [Nat.le_sub_one_of_lt s.2]
                           exact Nat.add_lt_add_iff_left.mpr (Nat.sub_one_lt_of_lt  M.S_ne)
                    _ ≤ (M.A-1) * M.S + M.S := by grw [Nat.le_sub_one_of_lt a.2]
                    _ ≤ M.SA := 
                        by unfold MDP.SA
                           rw [Nat.sum_one_prod_cancel]
                           · rw [Nat.mul_comm]
                           · exact M.A_ne 
        ⟨n, 
         by have h1 : ↑n' ≤ M.numhist h'.length - 1 := Nat.le_sub_one_of_lt n'.2
            have h2 : a * M.S + s ≤ M.SA - 1 := Nat.le_sub_one_of_lt h 
            unfold numhist at h1 ⊢
            unfold Hist.length
            subst n
            rw [Nat.pow_add,←Nat.mul_assoc,Nat.mul_comm,Nat.mul_assoc]
            nth_rw 3 [Nat.mul_comm]
            have h4 : M.SA ≤ M.SA * M.SA ^ h'.length * M.S := by 
                rw [Nat.mul_assoc]
                apply Nat.le_mul_of_pos_right M.SA (Nat.mul_pos (Nat.pow_pos M.SA_ne) M.S_ne)
            have h5 : 0 < M.SA * M.SA ^ h'.length * M.S  := 
              calc 0 < M.SA := M.SA_ne
                   _ ≤  M.SA * M.SA ^ h'.length * M.S := h4  
            calc ↑n' * M.SA + (↑a * M.S + ↑s) ≤ (M.S * M.SA ^ h'.length - 1) * M.SA + (↑a * M.S + ↑s) := by grw [h1]
                 _ ≤ (M.S * M.SA ^ h'.length - 1) * M.SA + (M.SA - 1) := by grw [h2]
                 _ = M.S * M.SA ^ h'.length * M.SA - M.SA + (M.SA - 1) := by rw [Nat.sub_one_mul]
                 _ = M.SA * M.SA ^ h'.length * M.S - M.SA + (M.SA - 1) := by qify; ring_nf -- commutativity?
                 _ = M.SA * M.SA ^ h'.length * M.S - M.SA + M.SA - 1 := by 
                        rw [Nat.add_sub_assoc M.SA_ne (M.SA * M.SA ^ h'.length * M.S - M.SA)]
                 _ = M.SA * M.SA ^ h'.length * M.S + M.SA - M.SA - 1 := by rw [← Nat.sub_add_comm h4]
                 _ = M.SA * M.SA ^ h'.length * M.S - 1 := by rw [Nat.add_sub_cancel_right]
                 _ < M.SA * M.SA ^ h'.length * M.S := by exact Nat.sub_one_lt_of_lt h5
                 _ = M.SA^1 * M.SA ^ h'.length * M.S := by simp 
            ⟩

open Function 


/-- A more convenient definition for constructing inverses  -/
def MDP.hist_to_idx' (M : MDP) (t : ℕ) (h : HistT M t) : Fin (M.numhist t) := 
    h.property ▸ M.hist_to_idx h.val

/-- A more convenient definition for constructing inverses  -/
def MDP.idx_to_hist' (M : MDP) (t : ℕ) (i : Fin (M.numhist t)) : HistT M t := 
    M.idx_to_hist t i

def MDP.hist_idx_valid (M : MDP) := {ti : ℕ × ℕ | ti.2 < M.numhist ti.1}

variable (M : MDP) (t : ℕ) 


theorem state_of_hist_len0 (h : M.HistT 0) : ∃s, h.val = Hist.init s := sorry 

theorem state_of_hist_len_t (h : M.HistT t.succ) : ∃h',∃a,∃s, h.val = Hist.foll h' a s := sorry 

theorem hist_idx_LeftInverse (M : MDP) : LeftInverse (M.idx_to_hist' t) (M.hist_to_idx' t)  := by
  intro h
  unfold MDP.idx_to_hist' MDP.hist_to_idx'
  --simp only
  -- Show that the index is valid
  have h_valid : ⟨h.1.length, (M.hist_to_idx h.1).val⟩ ∈ M.hist_idx_valid := by
    unfold MDP.hist_idx_valid
    simp only [Set.mem_setOf_eq]
    exact (M.hist_to_idx h.1).2
  simp -- TODO: remove non-terminal simps
  -- Prove by induction on the history
  induction t with --TODO: 
    | zero => 
        sorry 
        /- unfold MDP.hist_to_idx MDP.idx_to_hist
        simp 
        have h : s.val < M.S * 1 := by simp; exact s.2
        simp
        sorry -/
    | succ t' => sorry 
  /-| init s =>
    unfold hist_to_idx idx_to_hist
    simp only [Hist.length, numhist, pow_zero, mul_one]
    have h : s.val < M.S * 1 := by simp; exact s.2
    simp [h]
  | foll h' a s ih =>
    unfold hist_to_idx
    simp only [Hist.length]
    -- The encoded index for foll h' a s
    let n' := M.hist_to_idx h'
    let n := M.SA * ↑n' + (a.val * M.S + s.val)
    -- Need to show idx_to_hist decodes this correctly
    have h_lt : n < M.numhist (h'.length + 1) := (M.hist_to_idx (Hist.foll h' a s)).2
    unfold idx_to_hist
    simp only [Hist.length]
    -- Show that modular arithmetic recovers a and s
    have h_sa_mod : n % M.SA = a.val * M.S + s.val := by
      unfold n
      rw [Nat.add_mod, Nat.mul_mod_right]
      simp
      have : a.val * M.S + s.val < M.SA := by
        unfold MDP.SA
        calc a.val * M.S + s.val < a.val * M.S + M.S := by omega
             _ ≤ (M.A - 1) * M.S + M.S := by omega
             _ = M.A * M.S := by omega
      exact Nat.mod_eq_of_lt this
    -- Show that division recovers n'
    have h_div : (n - n % M.SA) / M.SA = ↑n' := by
      rw [h_sa_mod]
      exact hist_to_idx_foll_decompose M h' a s
    -- Now combine to show the full result
    simp only [n, h_sa_mod, h_div]
    congr 1
    · -- Show the recursive history is recovered
      have : (M.idx_to_hist h'.length ⟨↑n', n'.2⟩).val = h' := by
        have ih' := ih
        unfold idx_to_hist' hist_to_idx' at ih'
        simp only at ih'
        have h_valid' : (h'.length, n'.val) ∈ M.hist_idx_valid := by
          unfold hist_idx_valid
          simp only [Set.mem_setOf_eq]
          exact n'.2
        simp [h_valid'] at ih'
        exact ih'
      exact this
    · -- States match (trivial from definition)
      rfl  
-/
-- this is a RightInvOn because we can possibly feed an incorrect index to the history 
theorem hist_idx_RightInverse : RightInverse (M.idx_to_hist' t) (M.hist_to_idx' t) := sorry 


end ExplicitHistIndex
------------------------------ END: Explicit index for history --------------------------------------------

------------------------------ An implicit index construction through a finset --------------------------------------------
-- this is a less practical construction, but probably will be easier to deal with ---

/-- Return the prefix of hist of length k -/
def Hist.prefix (k : ℕ) (h : Hist M) : Hist M :=
    match h with
      | Hist.init s => Hist.init s
      | Hist.foll hp a s =>
        if hp.length + 1 ≤ k then hp.foll a s
        else hp.prefix k

def MDP.tuple2hist : Hist M × (Fin M.A) × (Fin M.S) → HistNE M
  | ⟨h, as⟩ => ⟨h.foll as.1 as.2, Nat.le.intro rfl⟩

def MDP.hist2tuple : HistNE M → Hist M × (Fin M.A) × (Fin M.S) 
  | ⟨Hist.foll h a s, _ ⟩ => ⟨h, a, s⟩

open Function 

variable {M : MDP}

-- mapping between tuples and histories are injective
lemma linv_hist2tuple_tuple2hist : LeftInverse M.hist2tuple M.tuple2hist := fun _ ↦ rfl
lemma inj_tuple2hist_l1 : Injective M.tuple2hist  := LeftInverse.injective linv_hist2tuple_tuple2hist
lemma inj_tuple2hist : Injective (Subtype.val ∘ M.tuple2hist)  := Injective.comp (Subtype.val_injective) inj_tuple2hist_l1

def emb_tuple2hist_l1 : Hist M × (Fin M.A) × (Fin M.S) ↪ HistNE M := ⟨M.tuple2hist, inj_tuple2hist_l1⟩
def emb_tuple2hist : Hist M × (Fin M.A) × (Fin M.S) ↪ Hist M  := ⟨λ x ↦  M.tuple2hist x, inj_tuple2hist⟩

--- state
def MDP.state2hist (M : MDP) (s : Fin M.S) : Hist M := Hist.init s
def MDP.hist2state (M : MDP) : Hist M → (Fin M.S) 
    | Hist.init s => s 
    | Hist.foll _ _ s => s
    
lemma linv_hist2state_state2hist : LeftInverse M.hist2state M.state2hist := fun _ => rfl
lemma inj_state2hist : Injective (M.state2hist) := LeftInverse.injective linv_hist2state_state2hist
                     
def state2hist_emb : (Fin M.S) ↪ Hist M := ⟨M.state2hist, inj_state2hist⟩

/-- Checks if the first hist is the prefix of the second hist. -/
def isprefix : Hist M → Hist M → Bool 
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

/-- All histories that follow h for t decisions -/
def Histories (h : Hist M) : ℕ → Finset (Hist M) 
    | Nat.zero => {h}
    | Nat.succ t => ((Histories h t) ×ˢ M.setA ×ˢ M.setS).map emb_tuple2hist

abbrev ℋ : Hist M → ℕ → Finset (Hist M) := Histories

theorem hist_lenth_eq_horizon (h : Hist M) (t : ℕ): ∀ h' ∈ (ℋ h t), h'.length = h.length + t := sorry

@[simp]
theorem hist_foll_nonempty (h : Hist M) (a : M.At) (s : M.St) : (h.foll a s).length > 0 := by simp 

theorem hist_foll_len (h : Hist M) (a : M.At) (s : M.St) : (h.foll a s).length = h.length + 1 := 
    by rewrite [Hist.length.eq_def]; exact Nat.add_comm 1 h.length

/-- All histories of a given length  -/
def MDP.HistoriesHorizon (M : MDP) (t : ℕ) : Finset (Hist M) := 
  match t with
  | Nat.zero => M.setS.map state2hist_emb 
  | Nat.succ t => ((M.HistoriesHorizon t) ×ˢ M.setA ×ˢ M.setS).map emb_tuple2hist

section Fintype_props 

theorem hist_horiz_complete (t : ℕ) (h : M.HistT t) : h.val ∈ M.HistoriesHorizon t := by
    induction t 
    case zero =>
      obtain ⟨h, ht⟩ := h
      cases h with
        | init s => simpa [MDP.HistoriesHorizon] using ⟨s, ⟨M.inS s, rfl⟩⟩
        | foll h s a => exfalso; simp_all 
    case succ t' ih =>
      obtain ⟨h, ht⟩ := h
      unfold MDP.HistoriesHorizon at ⊢ 
      cases h with 
        | init s => exfalso; simp_all
        | foll h s a =>
          rewrite [hist_foll_len] at ht 
          have ih1 := ih ⟨h, Nat.succ_inj.mp ht⟩ 
          simp_all [emb_tuple2hist, MDP.tuple2hist, M.inS, M.inA] 

/-- Shows that there are no extra histories in the finset -/
theorem hist_horiz_exact (t : ℕ) (h : Hist M) (hh : h ∈ M.HistoriesHorizon t) : h.length = t := by 
  induction t generalizing h 
  case zero => 
    unfold MDP.HistoriesHorizon state2hist_emb MDP.state2hist at hh 
    rewrite [Finset.mem_map] at hh
    obtain ⟨s, sin, sf⟩ := hh
    subst sf 
    simp only [Hist.length]
  case succ t' ih => 
    unfold MDP.HistoriesHorizon emb_tuple2hist MDP.tuple2hist at hh 
    rw [Finset.mem_map] at hh
    obtain ⟨has, hasi, em⟩ := hh 
    subst em 
    unfold Hist.length
    rewrite [Finset.mem_product] at hasi
    rewrite [ih has.1 hasi.1]
    exact Nat.add_comm 1 t'

def MDP.HistoriesHorizonT (M : MDP) (t : ℕ) : Finset (M.HistT t) := 
    let H := M.HistoriesHorizon t 
    let f : {h : Hist M // h ∈ H} → M.HistT t := fun hh => ⟨hh.1, hist_horiz_exact t hh.1 hh.2⟩
    have finj : Injective f := by unfold Injective f;  intro h₁ h₂ steq; grind only 
        -- TODO: this used to work instead of grind: rw [Subtype.ext_iff] at steq; simpa using steq 
    H.attach.map ⟨f, finj⟩

theorem hist_horiz_complete_t (t : ℕ) (h : M.HistT t) : h ∈ M.HistoriesHorizonT t := by 
    unfold MDP.HistoriesHorizonT
    extract_lets H f finj 
    apply Finset.mem_map.mpr 
    use ⟨h.1, hist_horiz_complete t h⟩
    simp [f]
    
instance (M : MDP) (t : ℕ) : Fintype (M.HistT t) where 
    elems := M.HistoriesHorizonT t  
    complete := fun h => hist_horiz_complete_t t h 

end Fintype_props

abbrev ℋₜ : ℕ → Finset (Hist M) := M.HistoriesHorizon

end Histories

end MDPs
