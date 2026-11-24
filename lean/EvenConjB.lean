import P699.EvenConj

/-!
# Even `n = 2m`: the base step and Conjecture B for all even `d ≤ m - 1` (Bali lab, 2026-11-02)
-/

open Finset Polynomial Matrix

namespace Bali.VE
open Bali.EvenPsi Bali.Chr Bali.Skew Bali.VG Bali.PfP Bali.VB Bali.GA

variable {K : ℕ}

lemma VE_zero (K : ℕ) : VE K 0 = 1 := by simp [VE, VBvol]

lemma co_zero : co K 0 = 1 := by simp [co, Hc]

lemma Rc_zero : Rc K 0 = 1 := by
  have h := Rc_closed (K := K) 0 (by omega)
  have hm : (2 * ((K + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  simp at h
  push_cast at h hm
  exact (mul_left_inj' hm).1 (by linarith)

lemma ll_zero : ll K 0 = 1 := by simp [ll, RPE_coeff, Bali.RE.ce]

/-- **the base step.** `V_2 = -16 ((n-1)/n) Rc_1 h_0 / ℓ_1`. -/
theorem V_base (hK : 2 ≤ K) :
    ll K 1 * VE K 1 = -16 * ((((2 * K + 1 + 1 : ℕ) : ℚ) - 1) / ((2 * K + 1 + 1 : ℕ) : ℚ)) * Rc K 1 * Bali.REO.hE (K + 1) 0 := by
  have hs := V_step hK 0 (by omega)
  simp only [mul_zero, zero_add, VE_zero, mul_one, co_zero, one_mul] at hs
  have c1 := co_succ (K := K) 0
  simp only [zero_add, pow_one] at c1
  rw [c1, Rc_zero] at hs
  have hb := border K (pF K 0)
  have hr : rowB K (pF K 0) = fun k => c0 K * rowB K 1 k := by rw [pF0, rowB_C]
  have hS : skew (rowB K 1) (rowB K (pF K 0)) = 0 := by rw [hr, skew_smul2, skew_self, mul_zero]
  rw [hS, zero_div, zero_sub] at hb
  have he : e K 0 = nuV K := rfl
  have he1 : e K 1 = rowE K (pF K 0) := rfl
  rw [he, he1, hb] at hs
  have hN := ipW_pK K 0 (by omega)
  have hlc0 : (pK (K + 1) 0).coeff 0 = c0 K := by unfold c0 pF; rw [if_pos (by omega)]
  have hc0 : c0 K = ll K 1 := by
    rw [← hlc0, pK_coeff]; unfold ll; rw [Bali.RE.RE_centre _ _ (by omega)]
    have := Rc_zero (K := K); unfold Rc at this; rw [Bali.RE.RE_centre _ _ (by omega)] at this
    rw [this, one_mul]
  have hpF : pF K 0 = pK (K + 1) 0 := pF_eq 0 (by omega)
  have hlin : ipW K (pF K 0) (pF K 0) = c0 K * ipW K (pF K 0) 1 := by
    rw [show ipW K (pF K 0) (pF K 0) = ipW K (pF K 0) (C (c0 K) * 1 + 0) by rw [add_zero, ← pF0], ipW_lin]
    simp [ipW]
  have hll0 : (RPE (K + 1) 0).coeff 0 = 1 := ll_zero
  rw [hll0, one_mul, hlc0, ← hpF, hlin] at hN
  have hcne := c0_ne (K := K) (by omega)
  have hI : ipW K (pF K 0) 1 = -4 * Rc K 1 * Bali.REO.hE (K + 1) 0 := by
    apply mul_left_cancel₀ hcne
    unfold Rc
    linear_combination hN
  rw [hI] at hs
  have hn : ((2 * K + 1 + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  linear_combination (-4 : ℚ) * hs

/-- **base step in the Γ form**, `m = s+3`. -/
theorem conjBE_base (s : ℕ) :
    (VE (s + 2) 1 : ℝ) = VE (s + 2) 0 * (crE (s + 3) 0 (Bali.ConjB.Ke 0) * crE (s + 3) 1 (Bali.ConjB.Ko 0)) := by
  have hv := V_base (K := s + 2) (by omega)
  have hl := Bali.Chr.ell_closedE (s + 2) 1 (by omega)
  have hh := Bali.REO.hE_closed (s + 2) 0 (by omega)
  have hr := Rc_closed (K := s + 2) 1 (by omega)
  have hlv : ll (s + 2) 1 = (2 * (s : ℚ) + 5) / ((2 * (s : ℚ) + 6) * ((s : ℚ) + 3) * ((s : ℚ) + 2)) := by
    unfold ll; rw [hl]
    rw [show 2 * (s + 2 + 1) - 1 = (2 * s + 4) + 1 by omega, show s + 2 - 1 = s + 1 by omega,
      show s + 2 + 1 - 1 = (s + 1) + 1 by omega, show 2 * (s + 2 + 1) - 2 * 1 = 2 * s + 4 by omega,
      show 2 * (s + 2 + 1) = (2 * s + 4) + 1 + 1 by ring, show s + 2 + 1 = (s + 1) + 1 + 1 by ring,
      show s + 2 = (s + 1) + 1 by ring]
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [hlv] at hv
  rw [show 2 * (s + 2) + 1 = 2 * s + 5 by ring, Nat.cast_choose ℚ (show s + 2 ≤ 2 * s + 5 by omega),
    show 2 * s + 5 - (s + 2) = s + 3 by omega] at hh
  rw [show 2 * (s + 2 + 1) = 2 * s + 6 by ring, Nat.choose_one_right] at hr
  rw [VE_zero]
  have hs : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have G1 : Real.Gamma (((s + 3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 3 / 2)
      = ((2 * s + 8).factorial : ℝ) * √Real.pi / (4 ^ (s + 4) * (s + 4).factorial) := by
    rw [show ((s + 3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 3 / 2 = ((s + 4 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (s + 4) = 2 * s + 8 by ring]
  have G2 : Real.Gamma (((s + 3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 1) = ((s + 3).factorial : ℝ) := by
    rw [show ((s + 3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 1 = ((s + 3 : ℕ) : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
  have G3 : Real.Gamma ((2 * ((s + 3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 1) / 2)
      = ((2 * s + 6).factorial : ℝ) * √Real.pi / (4 ^ (s + 3) * (s + 3).factorial) := by
    rw [show (2 * ((s + 3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 1) / 2 = ((s + 3 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (s + 3) = 2 * s + 6 by ring]
  have G4 : Real.Gamma ((2 * ((s + 3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 3) / 2)
      = ((2 * s + 8).factorial : ℝ) * √Real.pi / (4 ^ (s + 4) * (s + 4).factorial) := by
    rw [show (2 * ((s + 3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 3) / 2 = ((s + 4 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (s + 4) = 2 * s + 8 by ring]
  have G5 : Real.Gamma (((s + 3 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) + 3 / 2)
      = ((2 * s + 6).factorial : ℝ) * √Real.pi / (4 ^ (s + 3) * (s + 3).factorial) := by
    rw [show ((s + 3 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) + 3 / 2 = ((s + 3 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (s + 3) = 2 * s + 6 by ring]
  have G6 : Real.Gamma (((s + 3 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) + 1) = ((s + 2).factorial : ℝ) := by
    rw [show ((s + 3 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) + 1 = ((s + 2 : ℕ) : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
  have G7 : Real.Gamma ((2 * ((s + 3 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) + 1) / 2) = ((s + 2).factorial : ℝ) := by
    rw [show (2 * ((s + 3 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) + 1) / 2 = ((s + 2 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  have G8 : Real.Gamma ((2 * ((s + 3 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) + 3) / 2) = ((s + 3).factorial : ℝ) := by
    rw [show (2 * ((s + 3 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) + 3) / 2 = ((s + 3 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  unfold crE Bali.ConjB.Ke Bali.ConjB.Ko
  rw [show (2 * 0 : ℕ) = 0 by ring, G1, G2, G3, G4, G5, G6, G7, G8, show 2 * (s + 3) = 2 * s + 6 by ring]
  rw [show 2 * s + 8 = (2 * s + 7) + 1 by ring, Nat.factorial_succ (2 * s + 7),
    show 2 * s + 7 = (2 * s + 6) + 1 by ring, Nat.factorial_succ (2 * s + 6),
    show s + 4 = (s + 3) + 1 by ring, Nat.factorial_succ (s + 3)]
  rw [show 2 * s + 6 = (2 * s + 5) + 1 by ring, Nat.factorial_succ (2 * s + 5),
    show 2 * s + 5 = (2 * s + 4) + 1 by ring, Nat.factorial_succ (2 * s + 4)]
  rw [show s + 3 = (s + 2) + 1 by ring, Nat.factorial_succ (s + 2), show s + 2 = (s + 1) + 1 by ring,
    Nat.factorial_succ (s + 1)] at hh ⊢
  rw [show 2 * s + 5 = (2 * s + 4) + 1 by ring, Nat.factorial_succ (2 * s + 4)] at hh
  set H := Bali.REO.hE (s + 2 + 1) 0
  set V1 := VE (s + 2) 1
  set R1 := Rc (s + 2) 1
  simp only [Nat.choose_zero_right, Nat.cast_one, one_pow, mul_one, Nat.cast_zero, mul_zero, sub_zero] at hh
  push_cast at hv hh hr ⊢
  have f1 : ((2 * s + 4).factorial : ℚ) ≠ 0 := by positivity
  have f2 : ((s + 1).factorial : ℚ) ≠ 0 := by positivity
  have s0 : (0 : ℚ) ≤ s := by positivity
  have hR : R1 = -1 / (2 * (s : ℚ) + 4) := by
    rw [eq_div_iff (by positivity)]
    have : R1 * ((2 * (s : ℚ) + 4) * (2 * (s : ℚ) + 6)) = -(2 * (s : ℚ) + 6) := by linear_combination hr
    have h6 : (2 * (s : ℚ) + 6) ≠ 0 := by positivity
    apply mul_left_cancel₀ h6
    linear_combination this
  set CC : ℚ := ((2 * (s : ℚ) + 4 + 1) * ((2 * s + 4).factorial : ℚ)) /
      ((((s : ℚ) + 1 + 1) * ((s + 1).factorial : ℚ)) * (((s : ℚ) + 1 + 1 + 1) * (((s : ℚ) + 1 + 1) * ((s + 1).factorial : ℚ)))) with hCC
  have hH : H = (2 * (s : ℚ) + 6) * CC ^ 2 := by
    have h6 : (2 * (s : ℚ) + 6) ≠ 0 := by positivity
    apply mul_left_cancel₀ h6
    rw [hCC]
    linear_combination hh
  have hV : V1 = (-16 * ((2 * ((s : ℚ) + 2) + 1 + 1 - 1) / (2 * ((s : ℚ) + 2) + 1 + 1)) * R1 * H)
      / ((2 * (s : ℚ) + 5) / ((2 * (s : ℚ) + 6) * ((s : ℚ) + 3) * ((s : ℚ) + 2))) := by
    rw [eq_div_iff (by positivity)]
    linear_combination hv
  rw [hV, hR, hH, hCC]
  push_cast
  have := hs.ne'
  field_simp
  ring
/-- **Conjecture B for even `n = 2m` and even `d ≤ m - 1`**, `m ≥ 3`. -/
theorem conjBE (s : ℕ) : ∀ k, 2 * k ≤ s + 2 →
    (VE (s + 2) k : ℝ) = ∏ i ∈ range k, (crE (s + 3) (2 * i) (Bali.ConjB.Ke i) * crE (s + 3) (2 * i + 1) (Bali.ConjB.Ko i))
  | 0, _ => by simp [VE_zero]
  | 1, _ => by rw [conjBE_base, VE_zero]; simp
  | k + 2, hk => by
    obtain ⟨r, hr⟩ : ∃ r, s = 2 * k + 2 + r := ⟨s - (2 * k + 2), by omega⟩
    subst hr
    have h := conjBE_step k r
    rw [show 2 * k + 4 + r = 2 * k + 2 + r + 2 by ring, show 2 * k + 5 + r = 2 * k + 2 + r + 3 by ring] at h
    rw [h, conjBE (2 * k + 2 + r) (k + 1) (by omega), prod_range_succ (f := fun i =>
      crE (2 * k + 2 + r + 3) (2 * i) (Bali.ConjB.Ke i) * crE (2 * k + 2 + r + 3) (2 * i + 1) (Bali.ConjB.Ko i)) (k + 1)]
    rw [show 2 * (k + 1) = 2 * k + 2 by ring]
end Bali.VE

#print axioms Bali.VE.V_base
#print axioms Bali.VE.conjBE_base
#print axioms Bali.VE.conjBE
