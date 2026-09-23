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


import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import MDPLib.Probability.Basic

set_option linter.unusedSectionVars false

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
         [CharZero R] [Archimedean R]



section Definitions

open Findist

/-- Markov decision process -/
structure MDP (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] : Type where
  /-- states -/
  S : ℕ
  S_pos : 0 < S
  /-- actions  -/
  A : ℕ
  A_pos : 0 < A
  /-- transition probability s, a, s' -/
  P : Fin S → Fin A → Δ R (Fin S)
  /-- reward function s, a, s' -/
  r : Fin S → Fin A → Fin S → R

variable (M : MDP R)

def MDP.maxS : Fin M.S := ⟨M.S-1, by simp [M.S_pos]⟩
def MDP.maxA : Fin M.A := ⟨M.A-1, by simp [M.A_pos]⟩

-- here, we use the fintype property to show that the state and action
-- sets are complete 

abbrev MDP.State := Fin M.S 
abbrev MDP.Action := Fin M.A

/-- Set of all states -/
-- TODO(mathlib): `Fintype.elems` is `Finset.univ` and `Fintype.complete` is `Finset.mem_univ`,
-- so `setS`/`setA`/`inS`/`inA` are four aliases -- use the Mathlib names directly.
def MDP.setS : Finset M.State := Fintype.elems 
/-- Set of all actions -/
def MDP.setA : Finset M.Action := Fintype.elems

theorem MDP.inS : ∀s : M.State, s ∈ M.setS := Fintype.complete
theorem MDP.inA : ∀a : M.Action, a ∈ M.setA := Fintype.complete

def MDP.numStateActions := M.S * M.A

theorem MDP.numStateActions_pos : 0 < M.numStateActions := Nat.mul_pos M.S_pos M.A_pos

end Definitions

variable {M : MDP R}

section Histories

/-- Represents a history. The state is type ℕ and action is type ℕ. -/
-- NOTE(mathlib): `Hist M` is INFINITE -- histories have unbounded length, and there is no
-- `Fintype`/`FinEnum` instance for it (only `MDP.HistOfLength M t`, the length-`t` slice, has one;
-- see the `Fintype (M.HistOfLength t)` instance below). Consequently `Δ R (Hist M)` is currently
-- inexpressible: `Findist` requires `[FinEnum Ω]`.
--
-- That matters for the roadmap. Randomized history-dependent policies `Π_HR` and the
-- trajectory expectations `𝔼^{h,π,T}` (`latex/main.tex:977-1000,1317`) are exactly
-- distributions over `Hist M`. This file already works with `Finset (Hist M)` in four places
-- (`histories`, `MDP.historiesHorizon`), so a *finitely supported* distribution is the
-- natural shape for them.
--
-- This is the one place where Mathlib's `Finsupp` would genuinely be the right model -- but it
-- is noncomputable (see the long NOTE at the top of `MDPLib/Probability/Defs.lean`). Three
-- options when the time comes, deliberately not decided here:
--   (a) a library-local `support : Finset Ω` + `toFun` structure. `Finsupp.mk`, `.support` and
--       `Finsupp.sum` ARE computable -- it is `onFinset`/`single`/`+`/`•` that are not -- so a
--       hand-rolled version keeps `#eval` and handles infinite `Ω`.
--   (b) Mathlib's `Finsupp`, accepting noncomputability for history distributions only.
--   (c) keep indexing by `MDP.HistOfLength M t`, which is finite for each `t`, and never form a
--       distribution over all of `Hist M`.
inductive Hist (M : MDP R)  : Type where
  | init : Fin M.S → Hist M
  | foll : Hist M → Fin M.A → Fin M.S → Hist M

instance : Coe (Fin M.S) (Hist M) where
  coe s := Hist.init s

/-- History's length = the number of actions taken -/
@[simp]
def Hist.length : Hist M → ℕ
  | init _ => 0
  | Hist.foll h _ _ => 1 + length h

def MDP.HistOfLength (M : MDP R) (t : ℕ) := {h : Hist M // h.length = t}

-- TODO: We should prove that HistOfLength is a Fintype in order to be able to perform operations on it

/-- Nonempty histories -/
abbrev HistNonempty (M : MDP R) := {m : Hist M // m.length ≥ 1}

/-- Returns the last state of the history -/
def Hist.last : Hist M → Fin M.S
  | init s => s
  | Hist.foll _ _ s => s

/-- Number of histories of length t. -/
@[simp]
def MDP.numHist (M : MDP R) (t : ℕ) : ℕ := M.S * M.numStateActions^t

theorem numHist_zero : M.numHist 0 = M.S := by simp [MDP.numHist]

--------------------------- START: Explicit index for hist -------------------------------------------------------------------
section ExplicitHistIndex

/-- Construct i-th history of length t -/
def MDP.idxToHist (M : MDP R) (t : ℕ) (i : Fin (M.numHist t)) : M.HistOfLength t := 
  match t with
  | Nat.zero => 
      let ii : Fin M.S := ⟨i.1, by have h := i.2; simp_all [MDP.numHist] ⟩
      ⟨Hist.init ii,  rfl⟩
  | Nat.succ t' =>
      let sa : ℕ := i % M.numStateActions 
      let s : Fin M.S := ⟨sa  % M.S,  Nat.mod_lt sa M.S_pos ⟩
      let a : Fin M.A := ⟨(sa / M.S) % M.A, Nat.mod_lt (sa/M.S) M.A_pos⟩
      let ni : ℕ := (i - sa) / M.numStateActions
      let h1 : M.numStateActions ∣ (i - sa) := Nat.dvd_sub_mod ↑i
      let h2 : ni < M.numHist t' :=  
        by have h := i.2
           unfold MDP.numHist at h ⊢
           have h6 : M.numStateActions ∣ M.S*M.numStateActions^t'.succ := 
                  by apply Nat.dvd_mul_left_of_dvd ?_ M.S; exact Dvd.intro_left (M.numStateActions.pow t') rfl
           have h7 : M.S*M.numStateActions^t' = M.S*M.numStateActions^t'.succ / M.numStateActions :=
              by calc M.S*M.numStateActions^t' = M.S*M.numStateActions^t'* M.numStateActions / M.numStateActions := Eq.symm (Nat.mul_div_left (M.S*M.numStateActions^t') M.numStateActions_pos)
                      _ = M.S*M.numStateActions^t'.succ / M.numStateActions :=  by rw [Nat.mul_assoc,←Nat.pow_succ]
           subst ni 
           rw [h7]
           exact Nat.div_lt_div_of_lt_of_dvd h6 (Nat.sub_lt_of_lt h)
      let h' := M.idxToHist t' ⟨ni, h2⟩
      ⟨ h'.1.foll a s , 
        by simp only [Hist.length, h'.2, Nat.succ_eq_add_one]; exact Nat.add_comm 1 t'⟩ 

-- TODO(mathlib): = `by rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n h)]`
-- (`Nat.sub_one_mul` is core `Init/Data/Nat/Basic.lean:1189`). Verified.
-- Also note this declares into the root `Nat` namespace from a project file.
-- prefix suffices), or drop it in favour of the core one-liner in the `TODO(mathlib)` above.
-- Same issue as `List.finIdxOf` in `Probability/Basic.lean`.
lemma MDPLib.Nat.sub_one_mul_add_self (n : ℕ) {m : ℕ} (h : 0 < m) : (m-1) * n + n = m*n := 
  by rw [Nat.sub_one_mul]
     apply Nat.sub_add_cancel
     exact Nat.le_mul_of_pos_left n h 

/-- Compute the index of a history  -/
def MDP.histToIdx (M : MDP R) (h : Hist M) : Fin (M.numHist h.length) := 
    match h with 
    | Hist.init s => ⟨s, by simp only [numHist, Hist.length, pow_zero, mul_one, Fin.is_lt]⟩
    | Hist.foll h' a s => 
        let n' := M.histToIdx h'
        let n := M.numStateActions * ↑n' + (a * M.S + s)
        have h : a * M.S + s < M.numStateActions := 
            by unfold MDP.numStateActions
               calc a * M.S + s < a * M.S + M.S := 
                        by grw [Nat.le_sub_one_of_lt s.2]
                           exact Nat.add_lt_add_iff_left.mpr (Nat.sub_one_lt_of_lt  M.S_pos)
                    _ ≤ (M.A-1) * M.S + M.S := by grw [Nat.le_sub_one_of_lt a.2]
                    _ ≤ M.numStateActions := 
                        by unfold MDP.numStateActions
                           rw [MDPLib.Nat.sub_one_mul_add_self]
                           · rw [Nat.mul_comm]
                           · exact M.A_pos 
        ⟨n, 
         by have h1 : ↑n' ≤ M.numHist h'.length - 1 := Nat.le_sub_one_of_lt n'.2
            have h2 : a * M.S + s ≤ M.numStateActions - 1 := Nat.le_sub_one_of_lt h 
            unfold numHist at h1 ⊢
            unfold Hist.length
            subst n
            rw [Nat.pow_add,←Nat.mul_assoc,Nat.mul_comm,Nat.mul_assoc]
            nth_rw 3 [Nat.mul_comm]
            have h4 : M.numStateActions ≤ M.numStateActions * M.numStateActions ^ h'.length * M.S := by 
                rw [Nat.mul_assoc]
                apply Nat.le_mul_of_pos_right M.numStateActions (Nat.mul_pos (Nat.pow_pos M.numStateActions_pos) M.S_pos)
            have h5 : 0 < M.numStateActions * M.numStateActions ^ h'.length * M.S  := 
              calc 0 < M.numStateActions := M.numStateActions_pos
                   _ ≤  M.numStateActions * M.numStateActions ^ h'.length * M.S := h4  
            calc ↑n' * M.numStateActions + (↑a * M.S + ↑s) ≤ (M.S * M.numStateActions ^ h'.length - 1) * M.numStateActions + (↑a * M.S + ↑s) := by grw [h1]
                 _ ≤ (M.S * M.numStateActions ^ h'.length - 1) * M.numStateActions + (M.numStateActions - 1) := by grw [h2]
                 _ = M.S * M.numStateActions ^ h'.length * M.numStateActions - M.numStateActions + (M.numStateActions - 1) := by rw [Nat.sub_one_mul]
                 _ = M.numStateActions * M.numStateActions ^ h'.length * M.S - M.numStateActions + (M.numStateActions - 1) := by qify; ring_nf -- commutativity?
                 _ = M.numStateActions * M.numStateActions ^ h'.length * M.S - M.numStateActions + M.numStateActions - 1 := by 
                        rw [Nat.add_sub_assoc M.numStateActions_pos (M.numStateActions * M.numStateActions ^ h'.length * M.S - M.numStateActions)]
                 _ = M.numStateActions * M.numStateActions ^ h'.length * M.S + M.numStateActions - M.numStateActions - 1 := by rw [← Nat.sub_add_comm h4]
                 _ = M.numStateActions * M.numStateActions ^ h'.length * M.S - 1 := by rw [Nat.add_sub_cancel_right]
                 _ < M.numStateActions * M.numStateActions ^ h'.length * M.S := by exact Nat.sub_one_lt_of_lt h5
                 _ = M.numStateActions^1 * M.numStateActions ^ h'.length * M.S := by simp 
            ⟩

open Function 


/-- A more convenient definition for constructing inverses  -/
def MDP.histToIdx' (M : MDP R) (t : ℕ) (h : HistOfLength M t) : Fin (M.numHist t) := 
    h.property ▸ M.histToIdx h.val

/-- A more convenient definition for constructing inverses  -/
def MDP.idxToHist' (M : MDP R) (t : ℕ) (i : Fin (M.numHist t)) : HistOfLength M t := 
    M.idxToHist t i

def MDP.histIdxValid (M : MDP R) := {ti : ℕ × ℕ | ti.2 < M.numHist ti.1}

variable (M : MDP R) (t : ℕ) 


theorem exists_init_of_length_eq_zero (h : M.HistOfLength 0) : ∃s, h.val = Hist.init s := sorry 

theorem exists_foll_of_length_eq_succ (h : M.HistOfLength t.succ) : ∃h',∃a,∃s, h.val = Hist.foll h' a s := sorry 

theorem leftInverse_idxToHist_histToIdx (M : MDP R) : LeftInverse (M.idxToHist' t) (M.histToIdx' t)  := by
  intro h
  unfold MDP.idxToHist' MDP.histToIdx'
  --simp only
  -- Show that the index is valid
  have h_valid : ⟨h.1.length, (M.histToIdx h.1).val⟩ ∈ M.histIdxValid := by
    unfold MDP.histIdxValid
    rw [Set.mem_ofPred_eq]
    exact (M.histToIdx h.1).2
  simp 
  -- Prove by induction on the history
  induction t with --TODO: 
    | zero => 
        sorry 
        /- unfold MDP.histToIdx MDP.idxToHist
        simp 
        have h : s.val < M.S * 1 := by simp; exact s.2
        simp
        sorry -/
    | succ t' => sorry 
  /-| init s =>
    unfold histToIdx idxToHist
    simp only [Hist.length, numHist, pow_zero, mul_one]
    have h : s.val < M.S * 1 := by simp; exact s.2
    simp [h]
  | foll h' a s ih =>
    unfold histToIdx
    simp only [Hist.length]
    -- The encoded index for foll h' a s
    let n' := M.histToIdx h'
    let n := M.numStateActions * ↑n' + (a.val * M.S + s.val)
    -- Need to show idxToHist decodes this correctly
    have h_lt : n < M.numHist (h'.length + 1) := (M.histToIdx (Hist.foll h' a s)).2
    unfold idxToHist
    simp only [Hist.length]
    -- Show that modular arithmetic recovers a and s
    have h_sa_mod : n % M.numStateActions = a.val * M.S + s.val := by
      unfold n
      rw [Nat.add_mod, Nat.mul_mod_right]
      simp
      have : a.val * M.S + s.val < M.numStateActions := by
        unfold MDP.numStateActions
        calc a.val * M.S + s.val < a.val * M.S + M.S := by omega
             _ ≤ (M.A - 1) * M.S + M.S := by omega
             _ = M.A * M.S := by omega
      exact Nat.mod_eq_of_lt this
    -- Show that division recovers n'
    have h_div : (n - n % M.numStateActions) / M.numStateActions = ↑n' := by
      rw [h_sa_mod]
      exact hist_to_idx_foll_decompose M h' a s
    -- Now combine to show the full result
    simp only [n, h_sa_mod, h_div]
    congr 1
    · -- Show the recursive history is recovered
      have : (M.idxToHist h'.length ⟨↑n', n'.2⟩).val = h' := by
        have ih' := ih
        unfold idxToHist' histToIdx' at ih'
        simp only at ih'
        have h_valid' : (h'.length, n'.val) ∈ M.histIdxValid := by
          unfold histIdxValid
          simp only [Set.mem_setOf_eq]
          exact n'.2
        simp [h_valid'] at ih'
        exact ih'
      exact this
    · -- States match (trivial from definition)
      rfl  
-/
-- this is a RightInvOn because we can possibly feed an incorrect index to the history 
theorem rightInverse_idxToHist_histToIdx : RightInverse (M.idxToHist' t) (M.histToIdx' t) := sorry 


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

def MDP.tupleToHist : Hist M × (Fin M.A) × (Fin M.S) → HistNonempty M
  | ⟨h, as⟩ => ⟨h.foll as.1 as.2, Nat.le.intro rfl⟩

def MDP.histToTuple : HistNonempty M → Hist M × (Fin M.A) × (Fin M.S) 
  | ⟨Hist.foll h a s, _ ⟩ => ⟨h, a, s⟩

open Function 

variable {M : MDP R}

-- mapping between tuples and histories are injective
lemma leftInverse_histToTuple_tupleToHist : LeftInverse M.histToTuple M.tupleToHist := fun _ ↦ rfl
lemma tupleToHist_injective : Injective M.tupleToHist  := LeftInverse.injective leftInverse_histToTuple_tupleToHist
lemma val_comp_tupleToHist_injective : Injective (Subtype.val ∘ M.tupleToHist)  := Injective.comp (Subtype.val_injective) tupleToHist_injective

def tupleToHistNEEmbedding : Hist M × (Fin M.A) × (Fin M.S) ↪ HistNonempty M := ⟨M.tupleToHist, tupleToHist_injective⟩
def tupleToHistEmbedding : Hist M × (Fin M.A) × (Fin M.S) ↪ Hist M  := ⟨λ x ↦  M.tupleToHist x, val_comp_tupleToHist_injective⟩

--- state
def MDP.stateToHist (M : MDP R) (s : Fin M.S) : Hist M := Hist.init s
def MDP.histToState (M : MDP R) : Hist M → (Fin M.S) 
    | Hist.init s => s 
    | Hist.foll _ _ s => s
    
lemma leftInverse_histToState_stateToHist : LeftInverse M.histToState M.stateToHist := fun _ => rfl
lemma stateToHist_injective : Injective (M.stateToHist) := LeftInverse.injective leftInverse_histToState_stateToHist
                     
def stateToHistEmbedding : (Fin M.S) ↪ Hist M := ⟨M.stateToHist, stateToHist_injective⟩

/-- Checks if the first hist is the prefix of the second hist. -/
def isPrefix : Hist M → Hist M → Bool 
    | Hist.init s₁, Hist.init s₂ => s₁ = s₂
    | Hist.init s₁, Hist.foll hp _ _ => isPrefix (Hist.init s₁) hp 
    | Hist.foll _ _ _, Hist.init _ => False
    | Hist.foll h₁ a₁ s₁', Hist.foll  h₂ a₂ s₂' => 
        if h₁.length > h₂.length then
            False
        else if h₁.length < h₂.length then
            let pre := Hist.foll h₁ a₁ s₁' 
            isPrefix pre h₂
        else
            (a₁ = a₂) ∧ (s₁' = s₂') ∧ (isPrefix h₁ h₂)

/-- All histories that follow h for t decisions -/
def histories (h : Hist M) : ℕ → Finset (Hist M) 
    | Nat.zero => {h}
    | Nat.succ t => ((histories h t) ×ˢ M.setA ×ˢ M.setS).map tupleToHistEmbedding

abbrev ℋ : Hist M → ℕ → Finset (Hist M) := histories

theorem length_of_mem_histories (h : Hist M) (t : ℕ): ∀ h' ∈ (ℋ h t), h'.length = h.length + t := sorry

@[simp]
theorem length_foll_pos (h : Hist M) (a : M.Action) (s : M.State) : (h.foll a s).length > 0 := by simp 

theorem length_foll (h : Hist M) (a : M.Action) (s : M.State) : (h.foll a s).length = h.length + 1 := 
    by rewrite [Hist.length.eq_def]; exact Nat.add_comm 1 h.length

/-- All histories of a given length  -/
def MDP.historiesHorizon (M : MDP R) (t : ℕ) : Finset (Hist M) := 
  match t with
  | Nat.zero => M.setS.map stateToHistEmbedding 
  | Nat.succ t => ((M.historiesHorizon t) ×ˢ M.setA ×ˢ M.setS).map tupleToHistEmbedding

section Fintype_props 

theorem mem_historiesHorizon (t : ℕ) (h : M.HistOfLength t) : h.val ∈ M.historiesHorizon t := by
    induction t 
    case zero =>
      obtain ⟨h, ht⟩ := h
      cases h with
        | init s => simpa [MDP.historiesHorizon] using ⟨s, ⟨M.inS s, rfl⟩⟩
        | foll h s a => exfalso; simp_all 
    case succ t' ih =>
      obtain ⟨h, ht⟩ := h
      unfold MDP.historiesHorizon at ⊢ 
      cases h with 
        | init s => exfalso; simp_all
        | foll h s a =>
          rewrite [length_foll] at ht 
          have ih1 := ih ⟨h, Nat.succ_inj.mp ht⟩ 
          simp_all [tupleToHistEmbedding, MDP.tupleToHist, M.inS, M.inA] 

/-- Shows that there are no extra histories in the finset -/
theorem length_eq_of_mem_historiesHorizon (t : ℕ) (h : Hist M) (hh : h ∈ M.historiesHorizon t) : h.length = t := by 
  induction t generalizing h 
  case zero => 
    unfold MDP.historiesHorizon stateToHistEmbedding MDP.stateToHist at hh 
    rewrite [Finset.mem_map] at hh
    obtain ⟨s, sin, sf⟩ := hh
    subst sf
    rfl
  case succ t' ih => 
    unfold MDP.historiesHorizon tupleToHistEmbedding MDP.tupleToHist at hh 
    rw [Finset.mem_map] at hh
    obtain ⟨has, hasi, em⟩ := hh
    subst em
    obtain ⟨h', a, s⟩ := has
    rewrite [Finset.mem_product] at hasi
    show 1 + h'.length = t' + 1
    rw [ih h' hasi.1]
    exact Nat.add_comm 1 t'

def MDP.historiesHorizonT (M : MDP R) (t : ℕ) : Finset (M.HistOfLength t) := 
    let H := M.historiesHorizon t 
    let f : {h : Hist M // h ∈ H} → M.HistOfLength t := fun hh => ⟨hh.1, length_eq_of_mem_historiesHorizon t hh.1 hh.2⟩
    have finj : Injective f := by unfold Injective f;  intro h₁ h₂ steq; grind only 
        -- TODO: this used to work instead of grind: rw [Subtype.ext_iff] at steq; simpa using steq 
    H.attach.map ⟨f, finj⟩

theorem mem_historiesHorizonT (t : ℕ) (h : M.HistOfLength t) : h ∈ M.historiesHorizonT t := by 
    unfold MDP.historiesHorizonT
    extract_lets H f finj 
    apply Finset.mem_map.mpr 
    use ⟨h.1, mem_historiesHorizon t h⟩
    exact ⟨Finset.mem_attach _ _, rfl⟩
    
instance (M : MDP R) (t : ℕ) : Fintype (M.HistOfLength t) where 
    elems := M.historiesHorizonT t  
    complete := fun h => mem_historiesHorizonT t h 

end Fintype_props

abbrev ℋₜ : ℕ → Finset (Hist M) := M.historiesHorizon

end Histories

