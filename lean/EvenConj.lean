import P699.VRatio
import P699.ConjB

/-!
# Even `n = 2m`: Conjecture B, even steps `k ≥ 1` (Bali lab, 2026-11-02)
-/

open Finset Polynomial Matrix

namespace Bali.VE
open Bali.EvenPsi Bali.Chr Bali.Skew Bali.VG Bali.PfP Bali.VB Bali.GA

variable {K : ℕ}

/-- `Rc` in closed form. -/
lemma Rc_closed (a : ℕ) (ha : a < K + 1) :
    Rc K a * ((2 * ((K + 1 : ℕ) : ℚ) - 2 * a) * ((2 * (K + 1)).choose a : ℚ)) = (-1) ^ a * (2 * ((K + 1 : ℕ) : ℚ)) := by
  unfold Rc; rw [Bali.RE.RE_centre _ _ ha]; exact Bali.RC.F_closed _ a ha

/-- one step of `Rc`. -/
lemma Rc_succ (a : ℕ) (ha : a + 1 < K + 1) :
    Rc K (a + 1) * ((2 * ((K + 1 : ℕ) : ℚ) - 2 * a - 2) * (2 * ((K + 1 : ℕ) : ℚ) - a))
      = -Rc K a * ((2 * ((K + 1 : ℕ) : ℚ) - 2 * a) * ((a : ℚ) + 1)) := by
  have h0 := Rc_closed (K := K) a (by omega)
  have h1 := Rc_closed (K := K) (a + 1) ha
  have key : (((2 * (K + 1)).choose (a + 1) : ℕ) : ℚ) * ((a : ℚ) + 1)
      = ((2 * (K + 1)).choose a : ℚ) * (2 * ((K + 1 : ℕ) : ℚ) - a) := by
    have := Nat.choose_succ_right_eq (2 * (K + 1)) a
    have hc : ((2 * (K + 1) - a : ℕ) : ℚ) = 2 * ((K + 1 : ℕ) : ℚ) - a := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← hc]; exact_mod_cast this
  have hC : ((2 * (K + 1)).choose a : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  apply mul_left_cancel₀ hC
  push_cast at h0 h1 key ⊢
  rw [pow_succ] at h1
  linear_combination (-(2 * ((K : ℚ) + 1) - 2 * a - 2) * Rc K (a + 1)) * key + ((a : ℚ) + 1) * h1 + ((a : ℚ) + 1) * h0

/-- `T(p_a)` through `Rc` and `Scl`. -/
lemma TT_formula (a : ℕ) (ha : a + 2 < K + 1) :
    TT K a = 4 * 2 ^ (2 * (K + 1)) * (Rc K a * Bali.RS.Scl (K + 1) (a + 1) - Rc K (a + 1) * Bali.RS.Scl (K + 1) a) := by
  obtain ⟨s0, s1⟩ := Bali.RS.Sx_closed (K + 1) a ha
  unfold TT
  rw [TB_pK, Bali.RE.RE_total _ _ (by omega), Bali.RE.RE_total _ _ (by omega), s0, s1]
  unfold Rc
  ring

/-! ## up to the boundary -/

lemma bracket_ne' (m a : ℕ) (ha : a + 2 ≤ m) :
    Bali.RS.rho m a * (((a : ℚ) - 2 * m) * ((a : ℚ) + 1 - m)) - ((a : ℚ) + 1) * ((a : ℚ) - m) ≠ 0 := by
  have ham : (a : ℚ) + 2 ≤ m := by exact_mod_cast ha
  have h0 : (0 : ℚ) ≤ a := by positivity
  have dA : 2 * (m : ℚ) - a ≠ 0 := by intro h; linarith
  have dM : (m : ℚ) - a ≠ 0 := by intro h; linarith
  have d1 : (a : ℚ) + 1 ≠ 0 := by positivity
  have dO : 2 * (m : ℚ) - 2 * a - 1 ≠ 0 := by intro h; linarith
  have d2 : (m : ℚ) - a - 1 ≠ 0 := by intro h; linarith
  unfold Bali.RS.rho
  split_ifs
  · have e : -((a : ℚ) + 1) ^ 2 * (2 * (m : ℚ) - 2 * a) / ((2 * (m : ℚ) - a) ^ 2 * (2 * (m : ℚ) - 2 * a - 2))
          * (((a : ℚ) - 2 * m) * ((a : ℚ) + 1 - m)) - ((a : ℚ) + 1) * ((a : ℚ) - m)
        = ((a : ℚ) + 1) * ((m : ℚ) - a) * (2 * (m : ℚ) - 2 * a - 1) / (2 * (m : ℚ) - a) := by
      rw [show 2 * (m : ℚ) - 2 * a - 2 = 2 * ((m : ℚ) - a - 1) by ring]
      field_simp
      ring
    rw [e]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero d1 dM) dO) dA
  · have e : -(2 * (m : ℚ) - 2 * a) / (2 * (m : ℚ) - 2 * a - 2)
          * (((a : ℚ) - 2 * m) * ((a : ℚ) + 1 - m)) - ((a : ℚ) + 1) * ((a : ℚ) - m)
        = -((m : ℚ) - a) * (2 * (m : ℚ) - 2 * a - 1) := by
      rw [show 2 * (m : ℚ) - 2 * a - 2 = 2 * ((m : ℚ) - a - 1) by ring]
      field_simp
      ring
    rw [e]
    exact mul_ne_zero (neg_ne_zero.2 dM) dO

/-- `T(p_a) ≠ 0` up to the boundary `a = m - 2`. -/
theorem TB_ne' (hK : 2 ≤ K) (a : ℕ) (ha : a + 2 ≤ K + 1) : TB K (pK (K + 1) a) ≠ 0 := by
  have s0 := Bali.RS.Sx_ext (K + 1) a (by omega) (by omega)
  have s1 := Bali.RS.Sx_ext (K + 1) (a + 1) (by omega) (by omega)
  have hF := Bali.RC.F_rec (K + 1) a (by omega)
  rw [TB_pK, Bali.RE.RE_total _ _ (by omega), Bali.RE.RE_total _ _ (by omega), Bali.RE.RE_centre _ _ (by omega),
    Bali.RE.RE_centre _ _ (by omega), s0, s1, Bali.RS.Scl]
  set F0 := Bali.RC.F (K + 1) a
  set F1 := Bali.RC.F (K + 1) (a + 1)
  set S := Bali.RS.Scl (K + 1) a
  set r := Bali.RS.rho (K + 1) a
  have hS : S ≠ 0 := Bali.TN.Scl_ne _ a (by omega)
  have hF0 : F0 ≠ 0 := Bali.TN.F_ne _ a (by omega)
  have hb := bracket_ne' (K + 1) a ha
  intro h
  apply hb
  have h' : (2 : ℚ) ^ (2 * (K + 1)) ≠ 0 := by positivity
  have h2 : F0 * (S * r) - F1 * S = 0 := by
    have : (4 : ℚ) * (2 ^ (2 * (K + 1))) * (F0 * (S * r) - F1 * S) = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero (by norm_num) h')
  apply mul_left_cancel₀ (mul_ne_zero hF0 hS)
  rw [mul_zero]
  linear_combination ((a : ℚ) - 2 * ((K + 1 : ℕ) : ℚ)) * ((a : ℚ) + 1 - ((K + 1 : ℕ) : ℚ)) * h2 + S * hF

lemma TT_formula' (hK : 2 ≤ K) (a : ℕ) (ha : a + 2 ≤ K + 1) :
    TT K a = 4 * 2 ^ (2 * (K + 1)) * (Rc K a * Bali.RS.Scl (K + 1) (a + 1) - Rc K (a + 1) * Bali.RS.Scl (K + 1) a) := by
  have s0 := Bali.RS.Sx_ext (K + 1) a (by omega) (by omega)
  have s1 := Bali.RS.Sx_ext (K + 1) (a + 1) (by omega) (by omega)
  unfold TT
  rw [TB_pK, Bali.RE.RE_total _ _ (by omega), Bali.RE.RE_total _ _ (by omega), s0, s1]
  unfold Rc
  ring

lemma tau_even_ne' (hK : 2 ≤ K) (j : ℕ) (hj : 2 * j ≤ K) : τ K (2 * j) ≠ 0 := by
  rcases j with _ | j
  · exact tau_even_ne hK 0 (by omega)
  · rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring]
    simp only [τ, pF]
    rw [if_pos (by omega)]
    exact TB_ne' hK _ (by omega)
set_option maxRecDepth 100000 in
/-- **the ratio of `T`.** `k = j+1`. -/
lemma TT_ratio (j : ℕ) (hj : 2 * j + 4 ≤ K + 1) :
    TT K (2 * j + 2) * (2 * ((j : ℚ) + 1 - ((K + 1 : ℕ) : ℚ)) ^ 2 * (2 * ((j : ℚ) + 1) - ((K + 1 : ℕ) : ℚ) + 1)
        * (4 * ((j : ℚ) + 1) - 2 * ((K + 1 : ℕ) : ℚ) - 1))
      = TT K (2 * j + 1) * (-((j : ℚ) + 1) * (2 * ((j : ℚ) + 1) + 1) * (2 * ((j : ℚ) + 1) - ((K + 1 : ℕ) : ℚ) - 1)
        * (4 * ((j : ℚ) + 1) - 2 * ((K + 1 : ℕ) : ℚ) + 1)) := by
  rw [TT_formula' (by omega) _ (by omega), TT_formula' (by omega) _ (by omega)]
  have hS2 : Bali.RS.Scl (K + 1) (2 * j + 2) = Bali.RS.Scl (K + 1) (2 * j + 1) * Bali.RS.rho (K + 1) (2 * j + 1) := rfl
  have hS3 : Bali.RS.Scl (K + 1) (2 * j + 2 + 1) = Bali.RS.Scl (K + 1) (2 * j + 2) * Bali.RS.rho (K + 1) (2 * j + 2) := rfl
  rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring, hS3, hS2]
  have r1 : Bali.RS.rho (K + 1) (2 * j + 1) = -(2 * ((K + 1 : ℕ) : ℚ) - 2 * (2 * j + 1 : ℕ)) / (2 * ((K + 1 : ℕ) : ℚ) - 2 * (2 * j + 1 : ℕ) - 2) := by
    unfold Bali.RS.rho; rw [if_neg (by omega)]
  have r2 : Bali.RS.rho (K + 1) (2 * j + 2) = -(((2 * j + 2 : ℕ) : ℚ) + 1) ^ 2 * (2 * ((K + 1 : ℕ) : ℚ) - 2 * (2 * j + 2 : ℕ))
      / ((2 * ((K + 1 : ℕ) : ℚ) - (2 * j + 2 : ℕ)) ^ 2 * (2 * ((K + 1 : ℕ) : ℚ) - 2 * (2 * j + 2 : ℕ) - 2)) := by
    unfold Bali.RS.rho; rw [if_pos (by omega)]
  have q1 := Rc_succ (K := K) (2 * j + 1) (by omega)
  have q2 := Rc_succ (K := K) (2 * j + 2) (by omega)
  rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring] at q1
  rw [show 2 * j + 2 + 1 = 2 * j + 3 by ring] at q2 ⊢
  have hjm : (2 * (j : ℚ)) + 4 ≤ (K : ℚ) + 1 := by exact_mod_cast (by omega : 2 * j + 4 ≤ K + 1)
  have h0 : (0 : ℚ) ≤ j := by positivity
  push_cast at q1 q2 r1 r2 ⊢
  set xx : ℚ := (K : ℚ)
  set yy : ℚ := (j : ℚ)
  set ρ1 := Bali.RS.rho (K + 1) (2 * j + 1)
  set ρ2 := Bali.RS.rho (K + 1) (2 * j + 2)
  set SS := Bali.RS.Scl (K + 1) (2 * j + 1)
  set PP : ℚ := 4 * 2 ^ (2 * (K + 1))
  have d1 : 2 * (xx + 1) - 2 * (2 * yy + 1) - 2 ≠ 0 := by intro h; linarith
  have d2a : 2 * (xx + 1) - (2 * yy + 2) ≠ 0 := by intro h; linarith
  have d2b : 2 * (xx + 1) - 2 * (2 * yy + 2) - 2 ≠ 0 := by intro h; linarith
  have d4 : 2 * (xx + 1) - (2 * yy + 1) ≠ 0 := by intro h; linarith
  have hp1 : ρ1 * (2 * (xx + 1) - 2 * (2 * yy + 1) - 2) - -(2 * (xx + 1) - 2 * (2 * yy + 1)) = 0 := by
    rw [r1, div_mul_cancel₀ _ d1]; ring
  have hp2 : ρ2 * ((2 * (xx + 1) - (2 * yy + 2)) ^ 2 * (2 * (xx + 1) - 2 * (2 * yy + 2) - 2))
      - -((2 * yy + 2) + 1) ^ 2 * (2 * (xx + 1) - 2 * (2 * yy + 2)) = 0 := by
    rw [r2, div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero _ d2a) d2b)]; ring
  have hq1 : Rc K (2 * j + 2) * ((2 * (xx + 1) - 2 * (2 * yy + 1) - 2) * (2 * (xx + 1) - (2 * yy + 1)))
      - (-(2 * (xx + 1) - 2 * (2 * yy + 1)) * ((2 * yy + 1) + 1)) * Rc K (2 * j + 1) = 0 := by
    linear_combination q1
  have hq2 : Rc K (2 * j + 3) * ((2 * (xx + 1) - 2 * (2 * yy + 2) - 2) * (2 * (xx + 1) - (2 * yy + 2)))
      - (-(2 * (xx + 1) - 2 * (2 * yy + 2)) * ((2 * yy + 2) + 1)) * Rc K (2 * j + 2) = 0 := by
    linear_combination q2
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero d1 (mul_ne_zero (pow_ne_zero 2 d2a) d2b))
    (mul_ne_zero d1 d4)) (mul_ne_zero d2b d2a))
  linear_combination (-64*PP*SS*ρ1*(xx - yy)^4*(xx - 2*yy - 2)^2*(xx - 2*yy - 1)^2*(2*xx - 4*yy - 1)*(2*xx - 2*yy + 1)) * hq2 + (64*PP*SS*(xx - yy)^3*(xx - 2*yy - 2)^2*(xx - 2*yy - 1)*(4*ρ1*ρ2*xx^4 - 24*ρ1*ρ2*xx^3*yy - 10*ρ1*ρ2*xx^3 + 52*ρ1*ρ2*xx^2*yy^2 + 40*ρ1*ρ2*xx^2*yy + 4*ρ1*ρ2*xx^2 - 48*ρ1*ρ2*xx*yy^3 - 50*ρ1*ρ2*xx*yy^2 - 8*ρ1*ρ2*xx*yy + 16*ρ1*ρ2*yy^4 + 20*ρ1*ρ2*yy^3 + 4*ρ1*ρ2*yy^2 + 4*ρ1*xx^3*yy + 6*ρ1*xx^3 - 20*ρ1*xx^2*yy^2 - 36*ρ1*xx^2*yy - 9*ρ1*xx^2 + 32*ρ1*xx*yy^3 + 66*ρ1*xx*yy^2 + 29*ρ1*xx*yy + 3*ρ1*xx - 16*ρ1*yy^4 - 36*ρ1*yy^3 - 20*ρ1*yy^2 - 3*ρ1*yy - 4*xx^2*yy^2 - 10*xx^2*yy - 6*xx^2 + 16*xx*yy^3 + 46*xx*yy^2 + 39*xx*yy + 9*xx - 16*yy^4 - 52*yy^3 - 54*yy^2 - 18*yy)) * hq1 + (-64*PP*Rc K (2 * j + 1)*SS*ρ1*(xx - 2*yy)*(xx - yy)^3*(yy + 1)*(xx - 2*yy - 2)^2*(xx - 2*yy - 1)*(2*xx - 4*yy - 1)) * hp2 + (128*PP*Rc K (2 * j + 1)*SS*(xx - 2*yy)*(xx - yy)^3*(yy + 1)^2*(2*yy + 3)*(xx - 2*yy - 2)^2*(xx - 2*yy - 1)*(2*xx - 4*yy - 3)) * hp1
set_option maxRecDepth 100000 in
/-- **the reduced even step**, k = j+1: `(2m-2k+1) ℓ_{2k}² V_{2k+2} = 4^{4k+1} 2(m-k)(2m-4k+1) h_{2k} V_{2k}`. -/
theorem V_ratio2 (hK : 2 ≤ K) (j : ℕ) (hj : 2 * j + 4 ≤ K + 1) :
    (2 * ((K : ℚ) + 1) - 2 * ((j : ℚ) + 1) + 1) * ll K (2 * j + 2) ^ 2 * VE K (j + 2)
      = (4 : ℚ) ^ (4 * (j + 1) + 1) * (2 * (((K : ℚ) + 1) - ((j : ℚ) + 1)) * (2 * ((K : ℚ) + 1) - 4 * ((j : ℚ) + 1) + 1))
          * Bali.REO.hE (K + 1) (2 * j + 2) * VE K (j + 1) := by
  have hV0 := V_ratio hK (j + 1) (by omega) (by omega)
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show 2 * (j + 1) = 2 * j + 2 by ring,
    show 2 * j + 2 + 1 = 2 * j + 3 by ring, show j + 1 + 1 = j + 2 by ring] at hV0
  have hT0 := TT_ratio (K := K) j (by omega)
  have q1 := Rc_succ (K := K) (2 * j + 1) (by omega)
  have q2 := Rc_succ (K := K) (2 * j + 2) (by omega)
  rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring] at q1
  rw [show 2 * j + 2 + 1 = 2 * j + 3 by ring] at q2
  have hjm : (2 * (j : ℚ)) + 4 ≤ (K : ℚ) + 1 := by exact_mod_cast hj
  have h0 : (0 : ℚ) ≤ j := by positivity
  simp only [nQ] at hV0
  push_cast at hV0 hT0 q1 q2 ⊢
  set xx : ℚ := (K : ℚ)
  set yy : ℚ := (j : ℚ)
  set hE2 := Bali.REO.hE (K + 1) (2 * j + 2)
  set EE : ℚ := (4 : ℚ) ^ (4 * (j + 1) + 1)
  have hV : ll K (2 * j + 2) ^ 2 * Rc K (2 * j + 1) * TT K (2 * j + 2) * VE K (j + 2)
      - (-EE * (2 * (xx + 1) - 1 - 2 * (2 * (yy + 1))) * TT K (2 * j + 1) * Rc K (2 * j + 3) * hE2 * VE K (j + 1)) = 0 := by
    linear_combination hV0
  have hT : TT K (2 * j + 2) * (2 * ((yy + 1) - (xx + 1)) ^ 2 * (2 * (yy + 1) - (xx + 1) + 1) * (4 * (yy + 1) - 2 * (xx + 1) - 1))
      - TT K (2 * j + 1) * (-(yy + 1) * (2 * (yy + 1) + 1) * (2 * (yy + 1) - (xx + 1) - 1) * (4 * (yy + 1) - 2 * (xx + 1) + 1)) = 0 := by
    linear_combination hT0
  have hq1 : Rc K (2 * j + 2) * ((2 * (xx + 1) - 2 * (2 * yy + 1) - 2) * (2 * (xx + 1) - (2 * yy + 1)))
      - (-(2 * (xx + 1) - 2 * (2 * yy + 1)) * ((2 * yy + 1) + 1)) * Rc K (2 * j + 1) = 0 := by
    linear_combination q1
  have hq2 : Rc K (2 * j + 3) * ((2 * (xx + 1) - 2 * (2 * yy + 2) - 2) * (2 * (xx + 1) - (2 * yy + 2)))
      - (-(2 * (xx + 1) - 2 * (2 * yy + 2)) * ((2 * yy + 2) + 1)) * Rc K (2 * j + 2) = 0 := by
    linear_combination q2
  have nR : Rc K (2 * j + 1) ≠ 0 := by
    unfold Rc; rw [Bali.RE.RE_centre _ _ (by omega)]; exact Bali.TN.F_ne _ _ (by omega)
  have nT : TT K (2 * j + 2) ≠ 0 := TB_ne' hK _ (by omega)
  have nL : 2 * ((yy + 1) - (xx + 1)) ^ 2 * (2 * (yy + 1) - (xx + 1) + 1) * (4 * (yy + 1) - 2 * (xx + 1) - 1) ≠ 0 := by
    have a1 : (yy + 1) - (xx + 1) ≠ 0 := by intro h; linarith
    have a2 : 2 * (yy + 1) - (xx + 1) + 1 ≠ 0 := by intro h; linarith
    have a3 : 4 * (yy + 1) - 2 * (xx + 1) - 1 ≠ 0 := by intro h; linarith
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 a1)) a2) a3
  have nA1 : (2 * (xx + 1) - 2 * (2 * yy + 1) - 2) * (2 * (xx + 1) - (2 * yy + 1)) ≠ 0 := by
    have a1 : 2 * (xx + 1) - 2 * (2 * yy + 1) - 2 ≠ 0 := by intro h; linarith
    have a2 : 2 * (xx + 1) - (2 * yy + 1) ≠ 0 := by intro h; linarith
    exact mul_ne_zero a1 a2
  have nA2 : (2 * (xx + 1) - 2 * (2 * yy + 2) - 2) * (2 * (xx + 1) - (2 * yy + 2)) ≠ 0 := by
    have a1 : 2 * (xx + 1) - 2 * (2 * yy + 2) - 2 ≠ 0 := by intro h; linarith
    have a2 : 2 * (xx + 1) - (2 * yy + 2) ≠ 0 := by intro h; linarith
    exact mul_ne_zero a1 a2
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero nR nT) nL) nA1) nA2)
  linear_combination (16*(xx - yy)^3*(xx - 2*yy - 2)^2*(xx - 2*yy - 1)*(2*xx - 4*yy - 1)*(2*xx - 2*yy + 1)^2) * hV + (-16*EE*Rc K (2 * j + 1)*VE K (j + 1)*hE2*(xx - yy)^2*(xx - 2*yy - 2)*(xx - 2*yy - 1)*(2*xx - 4*yy - 1)*(2*xx - 2*yy + 1)) * hT + (-4*EE*TT K (2 * j + 1)*VE K (j + 1)*hE2*(xx - yy)^2*(xx - 2*yy - 2)*(xx - 2*yy - 1)*(2*xx - 4*yy - 3)*(2*xx - 4*yy - 1)*(2*xx - 2*yy + 1)^2) * hq2 + (4*EE*TT K (2 * j + 1)*VE K (j + 1)*hE2*(xx - yy)^2*(2*yy + 3)*(xx - 2*yy - 2)*(xx - 2*yy - 1)*(2*xx - 4*yy - 3)*(2*xx - 4*yy - 1)*(2*xx - 2*yy + 1)) * hq1
/-! ## the Γ form (even `n`) -/

/-- Conjecture B's ratio for even `n = 2m`. -/
noncomputable def crE (m d : ℕ) (Kc : ℝ) : ℝ :=
  Kc * ((2 * m).factorial : ℝ) * Real.Gamma ((m : ℝ) - d + 3 / 2)
    / (Real.Gamma ((m : ℝ) - d + 1) * Real.Gamma ((2 * (m : ℝ) - d + 1) / 2) * Real.Gamma ((2 * (m : ℝ) - d + 3) / 2))

set_option maxHeartbeats 1000000 in
/-- **Conjecture B, even `n`, even steps `k = j+1 ≥ 1`**, for `m = 2j+5+r`. -/
theorem conjBE_step (j r : ℕ) :
    (VE (2 * j + 4 + r) (j + 2) : ℝ)
      = VE (2 * j + 4 + r) (j + 1) * (crE (2 * j + 5 + r) (2 * j + 2) (Bali.ConjB.Ke (j + 1))
          * crE (2 * j + 5 + r) (2 * j + 3) (Bali.ConjB.Ko (j + 1))) := by
  have hv := V_ratio2 (K := 2 * j + 4 + r) (by omega) j (by omega)
  have hl := Bali.Chr.ell_closedE (2 * j + 4 + r) (2 * j + 2) (by omega)
  have hh := Bali.REO.hE_closed (2 * j + 4 + r) (2 * j + 2) (by omega)
  unfold ll at hv
  rw [hl] at hv
  rw [show 2 * (2 * j + 4 + r + 1) - (2 * j + 2) = 2 * j + 8 + 2 * r by omega,
    show 2 * j + 4 + r - (2 * j + 2) = r + 2 by omega,
    show 2 * j + 4 + r + 1 - (2 * j + 2) = r + 3 by omega,
    show 2 * (2 * j + 4 + r + 1) - 2 * (2 * j + 2) = 2 * r + 6 by omega,
    show 2 * (2 * j + 4 + r + 1) = 4 * j + 10 + 2 * r by ring] at hv
  rw [show 2 * (2 * j + 4 + r + 1) = 4 * j + 10 + 2 * r by ring, show 2 * (2 * j + 4 + r) + 1 = 4 * j + 9 + 2 * r by ring,
    Nat.cast_choose ℚ (show 2 * j + 2 ≤ 4 * j + 10 + 2 * r by omega),
    Nat.cast_choose ℚ (show 2 * j + 4 + r ≤ 4 * j + 9 + 2 * r by omega),
    show 4 * j + 10 + 2 * r - (2 * j + 2) = 2 * j + 8 + 2 * r by omega,
    show 4 * j + 9 + 2 * r - (2 * j + 4 + r) = 2 * j + 5 + r by omega] at hh
  have hs : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have G1 : Real.Gamma (((2 * j + 5 + r : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 3 / 2)
      = ((2 * r + 8).factorial : ℝ) * √Real.pi / (4 ^ (r + 4) * (r + 4).factorial) := by
    rw [show ((2 * j + 5 + r : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 3 / 2 = ((r + 4 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (r + 4) = 2 * r + 8 by ring]
  have G2 : Real.Gamma (((2 * j + 5 + r : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 1) = ((r + 3).factorial : ℝ) := by
    rw [show ((2 * j + 5 + r : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 1 = ((r + 3 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  have G3 : Real.Gamma ((2 * ((2 * j + 5 + r : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 1) / 2)
      = ((2 * j + 8 + 2 * r).factorial : ℝ) * √Real.pi / (4 ^ (j + 4 + r) * (j + 4 + r).factorial) := by
    rw [show (2 * ((2 * j + 5 + r : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 1) / 2 = ((j + 4 + r : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (j + 4 + r) = 2 * j + 8 + 2 * r by ring]
  have G4 : Real.Gamma ((2 * ((2 * j + 5 + r : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 3) / 2)
      = ((2 * j + 10 + 2 * r).factorial : ℝ) * √Real.pi / (4 ^ (j + 5 + r) * (j + 5 + r).factorial) := by
    rw [show (2 * ((2 * j + 5 + r : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 3) / 2 = ((j + 5 + r : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (j + 5 + r) = 2 * j + 10 + 2 * r by ring]
  have G5 : Real.Gamma (((2 * j + 5 + r : ℕ) : ℝ) - ((2 * j + 3 : ℕ) : ℝ) + 3 / 2)
      = ((2 * r + 6).factorial : ℝ) * √Real.pi / (4 ^ (r + 3) * (r + 3).factorial) := by
    rw [show ((2 * j + 5 + r : ℕ) : ℝ) - ((2 * j + 3 : ℕ) : ℝ) + 3 / 2 = ((r + 3 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (r + 3) = 2 * r + 6 by ring]
  have G6 : Real.Gamma (((2 * j + 5 + r : ℕ) : ℝ) - ((2 * j + 3 : ℕ) : ℝ) + 1) = ((r + 2).factorial : ℝ) := by
    rw [show ((2 * j + 5 + r : ℕ) : ℝ) - ((2 * j + 3 : ℕ) : ℝ) + 1 = ((r + 2 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  have G7 : Real.Gamma ((2 * ((2 * j + 5 + r : ℕ) : ℝ) - ((2 * j + 3 : ℕ) : ℝ) + 1) / 2) = ((j + 3 + r).factorial : ℝ) := by
    rw [show (2 * ((2 * j + 5 + r : ℕ) : ℝ) - ((2 * j + 3 : ℕ) : ℝ) + 1) / 2 = ((j + 3 + r : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  have G8 : Real.Gamma ((2 * ((2 * j + 5 + r : ℕ) : ℝ) - ((2 * j + 3 : ℕ) : ℝ) + 3) / 2) = ((j + 4 + r).factorial : ℝ) := by
    rw [show (2 * ((2 * j + 5 + r : ℕ) : ℝ) - ((2 * j + 3 : ℕ) : ℝ) + 3) / 2 = ((j + 4 + r : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  unfold crE Bali.ConjB.Ke Bali.ConjB.Ko
  rw [G1, G2, G3, G4, G5, G6, G7, G8, show 2 * (2 * j + 5 + r) = 4 * j + 10 + 2 * r by ring,
    show 2 * (j + 1) = 2 * j + 2 by ring]
  -- factorial bases
  rw [show 2 * r + 8 = (2 * r + 7) + 1 by ring, Nat.factorial_succ (2 * r + 7),
    show 2 * r + 7 = (2 * r + 6) + 1 by ring, Nat.factorial_succ (2 * r + 6),
    show r + 4 = (r + 3) + 1 by ring, Nat.factorial_succ (r + 3),
    show r + 3 = (r + 2) + 1 by ring, Nat.factorial_succ (r + 2),
    show 2 * j + 10 + 2 * r = (2 * j + 9 + 2 * r) + 1 by ring, Nat.factorial_succ (2 * j + 9 + 2 * r),
    show 2 * j + 9 + 2 * r = (2 * j + 8 + 2 * r) + 1 by ring, Nat.factorial_succ (2 * j + 8 + 2 * r),
    show j + 5 + r = (j + 4 + r) + 1 by ring, Nat.factorial_succ (j + 4 + r),
    show j + 4 + r = (j + 3 + r) + 1 by ring, Nat.factorial_succ (j + 3 + r),
    show 4 * j + 10 + 2 * r = (4 * j + 9 + 2 * r) + 1 by ring, Nat.factorial_succ (4 * j + 9 + 2 * r)] at *
  rw [show 2 * j + 5 + r = (2 * j + 4 + r) + 1 by ring, Nat.factorial_succ (2 * j + 4 + r)] at hh
  rw [Nat.factorial_succ (2 * j + 4 + r)] at hv
  have hE0 : Bali.REO.hE (2 * j + 4 + r + 1) (2 * j + 2) = Bali.REO.hE (2 * j + 4 + r + 1) (2 * j + 2) := rfl
  set H := Bali.REO.hE (2 * j + 4 + r + 1) (2 * j + 2)
  set V1 := VE (2 * j + 4 + r) (j + 2)
  set V0 := VE (2 * j + 4 + r) (j + 1)
  push_cast at hv hh ⊢
  have := hs.ne'
  have hHv : H = ((2 * ((2 * j + 4 + r : ℕ) : ℚ) + 2) ^ 2 * 0 + 0) + H := by ring
  -- solve h and V1 rationally, then cast
  have f1 : ((2 * j + 2).factorial : ℚ) ≠ 0 := by positivity
  have f2 : ((2 * j + 8 + 2 * r).factorial : ℚ) ≠ 0 := by positivity
  have f3 : ((4 * j + 9 + 2 * r).factorial : ℚ) ≠ 0 := by positivity
  have f4 : ((2 * j + 4 + r).factorial : ℚ) ≠ 0 := by positivity
  have f5 : ((r + 2).factorial : ℚ) ≠ 0 := by positivity
  have f6 : ((2 * r + 6).factorial : ℚ) ≠ 0 := by positivity
  have hHs : H = (2 * ((2 * j + 4 + r : ℚ) + 1)) ^ 2 * (((4 * j + 9 + 2 * r).factorial : ℚ) /
        (((2 * j + 4 + r).factorial : ℚ) * (((2 * j + 4 + r : ℚ) + 1) * ((2 * j + 4 + r).factorial : ℚ)))) ^ 2
      / ((2 * (r : ℚ) + 6) * ((((4 * j + 9 + 2 * r : ℚ) + 1) * ((4 * j + 9 + 2 * r).factorial : ℚ)) /
        (((2 * j + 2).factorial : ℚ) * ((2 * j + 8 + 2 * r).factorial : ℚ))) ^ 2) := by
    have d1 : (2 * (r : ℚ) + 6) ≠ 0 := by positivity
    rw [eq_div_iff (mul_ne_zero d1 (by positivity))]
    linear_combination hh
  have hV1 : V1 = V0 * ((4 : ℚ) ^ (4 * (j + 1) + 1) * (2 * (((2 * j + 4 + r : ℚ) + 1) - ((j : ℚ) + 1)) *
        (2 * ((2 * j + 4 + r : ℚ) + 1) - 4 * ((j : ℚ) + 1) + 1)) * H)
      / ((2 * (j : ℚ) + 2 * (r : ℚ) + 9) *
        (((2 * j + 8 + 2 * r).factorial : ℚ) ^ 2 * ((r + 2).factorial : ℚ) * (((r : ℚ) + 2 + 1) * ((r + 2).factorial : ℚ))
          / (((2 * r + 6).factorial : ℚ) * (((4 * j + 9 + 2 * r : ℚ) + 1) * ((4 * j + 9 + 2 * r).factorial : ℚ)) *
            ((2 * j + 4 + r).factorial : ℚ) * (((2 * j + 4 + r : ℚ) + 1) * ((2 * j + 4 + r).factorial : ℚ)))) ^ 2) := by
    have d1 : (2 * (j : ℚ) + 2 * (r : ℚ) + 9) ≠ 0 := by positivity
    rw [eq_div_iff (mul_ne_zero d1 (by positivity))]
    linear_combination hv
  rw [hV1, hHs]
  push_cast
  have jr0 : (0 : ℝ) ≤ j := by positivity
  have rr0 : (0 : ℝ) ≤ r := by positivity
  have n1 : (2 * (2 * (j : ℝ) + 4 + (r : ℝ) + 1) - 2 * ((j : ℝ) + 1) + 1) ≠ 0 := by intro h; linarith
  have n2 : (2 * (2 * (j : ℝ) + 4 + (r : ℝ) + 1) - 2 * (2 * (j : ℝ) + 2)) ≠ 0 := by intro h; linarith
  field_simp
  ring
end Bali.VE

#print axioms Bali.VE.TT_ratio
#print axioms Bali.VE.V_ratio2
#print axioms Bali.VE.conjBE_step
