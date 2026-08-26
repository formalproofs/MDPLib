import MDPLib.Probability.Basic
import MDPLib.Risk.VaR

namespace Risk

open Findist FinRV

variable {n : ℕ}

section QMax

def qmax (a b : ℚ) : ℚ := if a ≤ b then b else a

theorem qmax_ge_left (a b : ℚ) : qmax a b ≥ a := by
  unfold qmax
  by_cases h : a ≤ b
  · simp only [h, if_true]
  · simp only [h, if_false]; linarith

theorem qmax_ge_right (a b : ℚ) : qmax a b ≥ b := by
  unfold qmax
  by_cases h : a ≤ b
  · simp only [h, if_true]; linarith
  · simp only [h, if_false]; linarith

theorem qmax_eq_left {a b : ℚ} (h : b ≤ a) : qmax a b = a := by
  unfold qmax
  by_cases hab : a ≤ b
  · simp only [hab, if_true]; linarith
  · simp only [hab, if_false]

theorem qmax_eq_right {a b : ℚ} (h : a ≤ b) : qmax a b = b := by
  unfold qmax
  simp only [h, if_true]

theorem qmax_le {a b c : ℚ} (ha : a ≤ c) (hb : b ≤ c) : qmax a b ≤ c := by
  unfold qmax
  by_cases h : a ≤ b
  · simp only [h, if_true]; exact hb
  · simp only [h, if_false]; exact ha

theorem qmax_le_qmax {a b c d : ℚ} (h1 : a ≤ b) (h2 : c ≤ d) : qmax a c ≤ qmax b d := by
  unfold qmax
  by_cases hac : a ≤ c <;> by_cases hbd : b ≤ d <;>
    simp only [hac, hbd, if_true, if_false] <;> linarith

end QMax

def posPart (X : FinRV n ℚ) (t : ℚ) : FinRV n ℚ :=
  fun ω => qmax (X ω - t) 0

@[simp] theorem posPart_nonneg (X : FinRV n ℚ) (t : ℚ) (ω : Fin n) : 0 ≤ posPart X t ω :=
  qmax_ge_right _ _

def CVaRFun {n : ℕ} (P : Findist n) (X : FinRV n ℚ) (α : RiskLevel) (t : ℚ) : ℚ :=
  t + (𝔼[posPart X t // P]) / (1 - α.val)

def CVaR {n : ℕ} (P : Findist n) (X : FinRV n ℚ) (α : RiskLevel) : ℚ :=
  CVaRFun P X α (FinVaR P X α)

notation "CVaR[" X "//" P ", " α "]" => CVaR P X α

section Subgradient

theorem posPart_ge_posPart_add (x t v : ℚ) :
    qmax (x - t) 0 ≥ qmax (x - v) 0 + (v - t) * (if v < x then (1 : ℚ) else 0) := by
  by_cases hxv : v < x
  · have hmv : qmax (x - v) 0 = x - v := qmax_eq_left (by linarith)
    simp only [hxv, if_true, mul_one, hmv]
    have h1 : qmax (x - t) 0 ≥ x - t := qmax_ge_left _ _
    linarith
  · simp only [hxv, if_false, mul_zero, add_zero]
    push_neg at hxv
    have h0 : qmax (x - v) 0 = 0 := qmax_eq_right (by linarith)
    rw [h0]
    exact qmax_ge_right _ _

theorem posPart_ge_posPart_add' (x t v : ℚ) :
    qmax (x - t) 0 ≥ qmax (x - v) 0 + (v - t) * (if v ≤ x then (1 : ℚ) else 0) := by
  by_cases hxv : v ≤ x
  · have hmv : qmax (x - v) 0 = x - v := qmax_eq_left (by linarith)
    simp only [hxv, if_true, mul_one, hmv]
    have h1 : qmax (x - t) 0 ≥ x - t := qmax_ge_left _ _
    linarith
  · simp only [hxv, if_false, mul_zero, add_zero]
    push_neg at hxv
    have h0 : qmax (x - v) 0 = 0 := qmax_eq_right (by linarith)
    rw [h0]
    exact qmax_ge_right _ _

end Subgradient

section Min

variable {P : Findist n} {X Y : FinRV n ℚ} {α : RiskLevel} {c : ℚ}

theorem one_sub_alpha_pos (α : RiskLevel) : (0 : ℚ) < 1 - α.val := sub_pos.mpr α.2.2

theorem cvarFun_min (P : Findist n) (X : FinRV n ℚ) (α : RiskLevel) (t : ℚ) :
    CVaRFun P X α (FinVaR P X α) ≤ CVaRFun P X α t := by
  obtain ⟨hlt, hle⟩ := finvar_prob_cond (P := P) (X := X) (α := α)
  set v := FinVaR P X α with hv
  have hκ : (0 : ℚ) < 1 - α.val := one_sub_alpha_pos α
  have hκne : (1 - α.val) ≠ 0 := ne_of_gt hκ
  suffices h : (1 - α.val) * (t - v) + (𝔼[posPart X t // P] - 𝔼[posPart X v // P]) ≥ 0 by
    unfold CVaRFun
    have heq : (t + 𝔼[posPart X t // P] / (1 - α.val)) - (v + 𝔼[posPart X v // P] / (1 - α.val))
        = ((1 - α.val) * (t - v) + (𝔼[posPart X t // P] - 𝔼[posPart X v // P])) / (1 - α.val) := by
      field_simp [hκne]
      ring
    have hnn : (t + 𝔼[posPart X t // P] / (1 - α.val))
        - (v + 𝔼[posPart X v // P] / (1 - α.val)) ≥ 0 := by
      rw [heq]; exact div_nonneg h (le_of_lt hκ)
    linarith [hnn]
  by_cases htv : v ≤ t
  · have hgt : ℙ[X >ᵣ v // P] ≤ 1 - α.val := by
      have hcompl := prob_gt_of_le (P := P) (X := X) (t := v)
      linarith [hcompl, hle]
    have hind_eq : (fun ω => (if v < X ω then (1 : ℚ) else 0)) = (𝕀 ∘ (X >ᵣ v)) := by
      funext ω
      simp only [Function.comp_apply, FinRV.gt, indicator]
      by_cases h : X ω > v <;> simp [h]
    have hstep : 𝔼[posPart X t // P]
        ≥ 𝔼[posPart X v // P] + (v - t) * ℙ[X >ᵣ v // P] := by
      have hpt : (fun ω => posPart X v ω + (v - t) * (if v < X ω then (1 : ℚ) else 0))
          ≤ posPart X t := by
        intro ω
        exact posPart_ge_posPart_add (X ω) t v
      have hmono := exp_monotone (P := P) hpt
      have hexpand : (fun ω => posPart X v ω + (v - t) * (if v < X ω then (1 : ℚ) else 0))
          = posPart X v + (v - t) • (fun ω => (if v < X ω then (1 : ℚ) else 0)) := by
        funext ω; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hexpand, exp_additive_two, exp_homogenous, hind_eq, ← prob_eq_exp_ind] at hmono
      linarith [hmono]
    have hprod : (t - v) * ((1 - α.val) - ℙ[X >ᵣ v // P]) ≥ 0 :=
      mul_nonneg (by linarith) (by linarith [hgt])
    nlinarith [hstep, hprod]
  · push_neg at htv
    have hge : ℙ[X ≥ᵣ v // P] ≥ 1 - α.val := by
      have hcompl := prob_ge_of_lt (P := P) (X := X) (t := v)
      linarith [hcompl, hlt]
    have hind_eq : (fun ω => (if v ≤ X ω then (1 : ℚ) else 0)) = (𝕀 ∘ (X ≥ᵣ v)) := by
      funext ω
      simp only [Function.comp_apply, FinRV.geq, indicator]
      by_cases h : X ω ≥ v <;> simp [h]
    have hstep : 𝔼[posPart X t // P]
        ≥ 𝔼[posPart X v // P] + (v - t) * ℙ[X ≥ᵣ v // P] := by
      have hpt : (fun ω => posPart X v ω + (v - t) * (if v ≤ X ω then (1 : ℚ) else 0))
          ≤ posPart X t := by
        intro ω
        exact posPart_ge_posPart_add' (X ω) t v
      have hmono := exp_monotone (P := P) hpt
      have hexpand : (fun ω => posPart X v ω + (v - t) * (if v ≤ X ω then (1 : ℚ) else 0))
          = posPart X v + (v - t) • (fun ω => (if v ≤ X ω then (1 : ℚ) else 0)) := by
        funext ω; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hexpand, exp_additive_two, exp_homogenous, hind_eq, ← prob_eq_exp_ind] at hmono
      linarith [hmono]
    have hprod : (v - t) * (ℙ[X ≥ᵣ v // P] - (1 - α.val)) ≥ 0 :=
      mul_nonneg (by linarith) (by linarith [hge])
    nlinarith [hstep, hprod]

end Min

section Properties

variable {P : Findist n} {X Y : FinRV n ℚ} {α : RiskLevel} {c : ℚ}

theorem cvar_ge_var : CVaR[X // P, α] ≥ VaR[X // P, α] := by
  unfold CVaR CVaRFun
  have hκ : (0 : ℚ) < 1 - α.val := one_sub_alpha_pos α
  have hnn : 𝔼[posPart X (FinVaR P X α) // P] ≥ 0 := by
    have h0 : (0 : FinRV n ℚ) ≤ posPart X (FinVaR P X α) := fun ω => posPart_nonneg X _ ω
    calc 𝔼[posPart X (FinVaR P X α) // P] ≥ 𝔼[(0 : FinRV n ℚ) // P] := exp_monotone (P := P) h0
      _ = 0 := by unfold expect; exact dotProduct_zero P.p
  have : 𝔼[posPart X (FinVaR P X α) // P] / (1 - α.val) ≥ 0 := div_nonneg hnn (le_of_lt hκ)
  linarith [this]

theorem cvar_translation_invariant :
    CVaR[X + c • 1 // P, α] = CVaR[X // P, α] + c := by
  unfold CVaR CVaRFun
  have hv' : FinVaR P (X + c • 1) α = FinVaR P X α + c := var_translation_invariant
  rw [hv']
  have hpp : posPart (X + c • 1) (FinVaR P X α + c) = posPart X (FinVaR P X α) := by
    funext ω
    unfold posPart
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    have harg : (X ω + c) - (FinVaR P X α + c) = X ω - FinVaR P X α := by ring
    rw [harg]
  rw [hpp]
  ring

theorem cvar_positive_homog (hc : c > 0) :
    CVaR[(fun ω => c * X ω) // P, α] = c * CVaR[X // P, α] := by
  unfold CVaR CVaRFun
  have hv' : FinVaR P (fun ω => c * X ω) α = c * FinVaR P X α := var_positive_homog hc
  rw [hv']
  have hpp : posPart (fun ω => c * X ω) (c * FinVaR P X α) = c • posPart X (FinVaR P X α) := by
    funext ω
    unfold posPart
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases h : X ω ≤ FinVaR P X α
    · have h1 : c * X ω - c * FinVaR P X α ≤ 0 := by nlinarith
      have h2 : X ω - FinVaR P X α ≤ 0 := by linarith
      rw [qmax_eq_right h1, qmax_eq_right h2, mul_zero]
    · push_neg at h
      have h1 : c * X ω - c * FinVaR P X α ≥ 0 := by nlinarith
      have h2 : X ω - FinVaR P X α ≥ 0 := by linarith
      rw [qmax_eq_left h1, qmax_eq_left h2]
      ring
  rw [hpp, exp_homogenous]
  ring

theorem cvar_monotone (hxy : X ≤ Y) : CVaR[X // P, α] ≤ CVaR[Y // P, α] := by
  have h1 : CVaR[X // P, α] ≤ CVaRFun P X α (FinVaR P Y α) := by
    unfold CVaR
    exact cvarFun_min P X α (FinVaR P Y α)
  have h2 : CVaRFun P X α (FinVaR P Y α) ≤ CVaRFun P Y α (FinVaR P Y α) := by
    unfold CVaRFun
    have hpp : posPart X (FinVaR P Y α) ≤ posPart Y (FinVaR P Y α) := by
      intro ω
      exact qmax_le_qmax (by linarith [hxy ω]) (le_refl 0)
    have hmono := exp_monotone (P := P) hpp
    have hκ : (0 : ℚ) < 1 - α.val := one_sub_alpha_pos α
    have hdiv : 𝔼[posPart X (FinVaR P Y α) // P] / (1 - α.val)
        ≤ 𝔼[posPart Y (FinVaR P Y α) // P] / (1 - α.val) := by
      gcongr
    linarith [hdiv]
  have h3 : CVaRFun P Y α (FinVaR P Y α) = CVaR[Y // P, α] := rfl
  calc CVaR[X // P, α] ≤ CVaRFun P X α (FinVaR P Y α) := h1
    _ ≤ CVaRFun P Y α (FinVaR P Y α) := h2
    _ = CVaR[Y // P, α] := h3

end Properties

section Convexity

variable {P : Findist n} {α : RiskLevel}

theorem qmax_nonneg_sublinear {a b lam mu : ℚ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    qmax (lam * a + mu * b) 0 ≤ lam * qmax a 0 + mu * qmax b 0 := by
  have h1 : lam * a ≤ lam * qmax a 0 := mul_le_mul_of_nonneg_left (qmax_ge_left a 0) hlam
  have h2 : mu * b ≤ mu * qmax b 0 := mul_le_mul_of_nonneg_left (qmax_ge_left b 0) hmu
  have h3 : (0 : ℚ) ≤ lam * qmax a 0 := mul_nonneg hlam (qmax_ge_right a 0)
  have h4 : (0 : ℚ) ≤ mu * qmax b 0 := mul_nonneg hmu (qmax_ge_right b 0)
  exact qmax_le (by linarith) (by linarith)

theorem cvar_convex (X Y : FinRV n ℚ) (lam : ℚ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    CVaR[(fun ω => lam * X ω + (1 - lam) * Y ω) // P, α]
      ≤ lam * CVaR[X // P, α] + (1 - lam) * CVaR[Y // P, α] := by
  have hκ : (0 : ℚ) < 1 - α.val := one_sub_alpha_pos α
  have hmu : (0 : ℚ) ≤ 1 - lam := by linarith
  set mu : ℚ := 1 - lam with hmuDef
  set vX := FinVaR P X α with hvX
  set vY := FinVaR P Y α with hvY
  set Z : FinRV n ℚ := (fun ω => lam * X ω + mu * Y ω) with hZ
  set tmix : ℚ := lam * vX + mu * vY with htmix
  have hmin : CVaR[Z // P, α] ≤ CVaRFun P Z α tmix := by
    unfold CVaR
    exact cvarFun_min P Z α tmix
  have hpt : posPart Z tmix ≤ lam • posPart X vX + mu • posPart Y vY := by
    intro ω
    have harg : Z ω - tmix = lam * (X ω - vX) + mu * (Y ω - vY) := by
      simp only [hZ, htmix]; ring
    simp only [posPart, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [harg]
    exact qmax_nonneg_sublinear hlam0 hmu
  have hexp : 𝔼[posPart Z tmix // P] ≤ lam * 𝔼[posPart X vX // P] + mu * 𝔼[posPart Y vY // P] := by
    have hmono := exp_monotone (P := P) hpt
    rwa [exp_additive_two, exp_homogenous, exp_homogenous] at hmono
  have hg : CVaRFun P Z α tmix ≤ lam * CVaR[X // P, α] + mu * CVaR[Y // P, α] := by
    unfold CVaRFun CVaR
    rw [← hvX, ← hvY]
    calc tmix + 𝔼[posPart Z tmix // P] / (1 - α.val)
        ≤ tmix + (lam * 𝔼[posPart X vX // P] + mu * 𝔼[posPart Y vY // P]) / (1 - α.val) := by
          gcongr
      _ = lam * (vX + 𝔼[posPart X vX // P] / (1 - α.val))
          + mu * (vY + 𝔼[posPart Y vY // P] / (1 - α.val)) := by
          rw [htmix]; ring
  calc CVaR[Z // P, α] ≤ CVaRFun P Z α tmix := hmin
    _ ≤ lam * CVaR[X // P, α] + mu * CVaR[Y // P, α] := hg

end Convexity

end Risk
