import P699.ShellXE

/-!
# Even `n = 2m`: the boundary `d = m`, and Conjecture B for every `d ≤ m` (Bali lab, 2026-11-02)
-/

open Finset Polynomial Matrix

namespace Bali.VE
open Bali.EvenPsi Bali.Chr Bali.Skew Bali.VG Bali.PfP Bali.VB Bali.GA Bali.OddB Bali.OG

set_option maxHeartbeats 2000000 in
/-- **even boundary step**, `m = 2j+4`, `d: 2j+2 → 2j+4 = m`. -/
theorem conjBE_edge (j : ℕ) :
    (VE (2 * j + 3) (j + 2) : ℝ)
      = VE (2 * j + 3) (j + 1) * (crE (2 * j + 4) (2 * j + 2) (Bali.ConjB.Ke (j + 1))
          * crE (2 * j + 4) (2 * j + 3) (Bali.ConjB.Ko (j + 1))) := by
  have hv := V_ratio2 (K := 2 * j + 3) (by omega) j (by omega)
  have hl := Bali.Chr.ell_closedE (2 * j + 3) (2 * j + 2) (by omega)
  have hh := Bali.REO.hE_closed (2 * j + 3) (2 * j + 2) (by omega)
  unfold ll at hv
  rw [hl] at hv
  rw [show 2 * (2 * j + 3 + 1) - (2 * j + 2) = 2 * j + 6 by omega, show 2 * j + 3 - (2 * j + 2) = 1 by omega,
    show 2 * j + 3 + 1 - (2 * j + 2) = 2 by omega, show 2 * (2 * j + 3 + 1) - 2 * (2 * j + 2) = 4 by omega,
    show 2 * (2 * j + 3 + 1) = 4 * j + 8 by ring] at hv
  rw [show 2 * (2 * j + 3 + 1) = 4 * j + 8 by ring, show 2 * (2 * j + 3) + 1 = 4 * j + 7 by ring,
    Nat.cast_choose ℚ (show 2 * j + 2 ≤ 4 * j + 8 by omega), Nat.cast_choose ℚ (show 2 * j + 3 ≤ 4 * j + 7 by omega),
    show 4 * j + 8 - (2 * j + 2) = 2 * j + 6 by omega, show 4 * j + 7 - (2 * j + 3) = 2 * j + 4 by omega] at hh
  have hs : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have G1 : Real.Gamma (((2 * j + 4 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 3 / 2) = 720 * √Real.pi / (4 ^ 3 * 6) := by
    rw [show ((2 * j + 4 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 3 / 2 = ((3 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half]; norm_num [Nat.factorial]
  have G2 : Real.Gamma (((2 * j + 4 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 1) = 2 := by
    rw [show ((2 * j + 4 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 1 = ((2 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]; norm_num [Nat.factorial]
  have G3 : Real.Gamma ((2 * ((2 * j + 4 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 1) / 2)
      = ((2 * j + 6).factorial : ℝ) * √Real.pi / (4 ^ (j + 3) * (j + 3).factorial) := by
    rw [show (2 * ((2 * j + 4 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 1) / 2 = ((j + 3 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (j + 3) = 2 * j + 6 by ring]
  have G4 : Real.Gamma ((2 * ((2 * j + 4 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 3) / 2)
      = ((2 * j + 8).factorial : ℝ) * √Real.pi / (4 ^ (j + 4) * (j + 4).factorial) := by
    rw [show (2 * ((2 * j + 4 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 3) / 2 = ((j + 4 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (j + 4) = 2 * j + 8 by ring]
  have G5 : Real.Gamma (((2 * j + 4 : ℕ) : ℝ) - ((2 * j + 3 : ℕ) : ℝ) + 3 / 2) = 24 * √Real.pi / (4 ^ 2 * 2) := by
    rw [show ((2 * j + 4 : ℕ) : ℝ) - ((2 * j + 3 : ℕ) : ℝ) + 3 / 2 = ((2 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half]; norm_num [Nat.factorial]
  have G6 : Real.Gamma (((2 * j + 4 : ℕ) : ℝ) - ((2 * j + 3 : ℕ) : ℝ) + 1) = 1 := by
    rw [show ((2 * j + 4 : ℕ) : ℝ) - ((2 * j + 3 : ℕ) : ℝ) + 1 = ((1 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]; norm_num
  have G7 : Real.Gamma ((2 * ((2 * j + 4 : ℕ) : ℝ) - ((2 * j + 3 : ℕ) : ℝ) + 1) / 2) = ((j + 2).factorial : ℝ) := by
    rw [show (2 * ((2 * j + 4 : ℕ) : ℝ) - ((2 * j + 3 : ℕ) : ℝ) + 1) / 2 = ((j + 2 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  have G8 : Real.Gamma ((2 * ((2 * j + 4 : ℕ) : ℝ) - ((2 * j + 3 : ℕ) : ℝ) + 3) / 2) = ((j + 3).factorial : ℝ) := by
    rw [show (2 * ((2 * j + 4 : ℕ) : ℝ) - ((2 * j + 3 : ℕ) : ℝ) + 3) / 2 = ((j + 3 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  unfold crE Bali.ConjB.Ke Bali.ConjB.Ko
  rw [G1, G2, G3, G4, G5, G6, G7, G8, show 2 * (2 * j + 4) = 4 * j + 8 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
  rw [show 2 * j + 8 = (2 * j + 7) + 1 by ring, Nat.factorial_succ (2 * j + 7),
    show 2 * j + 7 = (2 * j + 6) + 1 by ring, Nat.factorial_succ (2 * j + 6),
    show j + 4 = (j + 3) + 1 by ring, Nat.factorial_succ (j + 3),
    show j + 3 = (j + 2) + 1 by ring, Nat.factorial_succ (j + 2)]
  rw [show 4 * j + 8 = (4 * j + 7) + 1 by ring, Nat.factorial_succ (4 * j + 7)] at hv hh ⊢
  rw [show 2 * j + 4 = (2 * j + 3) + 1 by ring, Nat.factorial_succ (2 * j + 3),
    show 2 * j + 3 = (2 * j + 2) + 1 by ring, Nat.factorial_succ (2 * j + 2)] at hh
  rw [Nat.factorial_succ (2 * j + 3), show 2 * j + 3 = (2 * j + 2) + 1 by ring, Nat.factorial_succ (2 * j + 2)] at hv
  simp only [Nat.factorial_one, Nat.factorial_two, show Nat.factorial 4 = 24 from rfl, Nat.cast_one, Nat.cast_ofNat, mul_one] at hv
  set H := Bali.REO.hE (2 * j + 2 + 1 + 1) (2 * j + 2)
  set V1 := VE (2 * j + 2 + 1) (j + 2)
  set V0 := VE (2 * j + 2 + 1) (j + 1)
  push_cast at hv hh ⊢
  have f1 : ((2 * j + 2).factorial : ℚ) ≠ 0 := by positivity
  have f2 : ((2 * j + 6).factorial : ℚ) ≠ 0 := by positivity
  have f3 : ((4 * j + 7).factorial : ℚ) ≠ 0 := by positivity
  have hHs : H = (2 * ((2 * (j : ℚ) + 2 + 1) + 1)) ^ 2 * (((4 * (j : ℚ) + 7 + 1) * 0 + ((4 * j + 7).factorial : ℚ)) /
        (((2 * (j : ℚ) + 2 + 1) * ((2 * j + 2).factorial : ℚ)) * ((2 * (j : ℚ) + 2 + 1 + 1) * ((2 * (j : ℚ) + 2 + 1) * ((2 * j + 2).factorial : ℚ))))) ^ 2
      / (4 * (((4 * (j : ℚ) + 7 + 1) * ((4 * j + 7).factorial : ℚ)) /
        (((2 * j + 2).factorial : ℚ) * ((2 * j + 6).factorial : ℚ))) ^ 2) := by
    rw [eq_div_iff (by positivity)]
    linear_combination hh
  have hV1 : V1 = V0 * ((4 : ℚ) ^ (4 * (j + 1) + 1) * (2 * ((2 * (j : ℚ) + 2 + 1 + 1) - ((j : ℚ) + 1)) *
        (2 * (2 * (j : ℚ) + 2 + 1 + 1) - 4 * ((j : ℚ) + 1) + 1)) * H)
      / ((2 * (j : ℚ) + 7) *
        (((2 * j + 6).factorial : ℚ) ^ 2 * 2
          / (24 * (((4 * (j : ℚ) + 7 + 1) * ((4 * j + 7).factorial : ℚ))) *
            ((2 * (j : ℚ) + 2 + 1) * ((2 * j + 2).factorial : ℚ)) * ((2 * (j : ℚ) + 2 + 1 + 1) * ((2 * (j : ℚ) + 2 + 1) * ((2 * j + 2).factorial : ℚ))))) ^ 2) := by
    rw [eq_div_iff (by positivity)]
    linear_combination hv
  rw [hV1, hHs]
  push_cast
  have := hs.ne'
  field_simp
  ring

set_option maxHeartbeats 2000000 in
/-- **odd boundary step**, `m = 2j+3`, `d: 2j+2 → 2j+3 = m`. -/
theorem conjBO_edge (j : ℕ) :
    ((VBvol (fun h : Fin (2 * j + 2 + 1 + 1) => yv (2 * j + 2) (h : ℕ)) (nuV (2 * j + 2)) (2 * (j + 1) + 1) : ℚ) : ℝ)
      = VE (2 * j + 2) (j + 1) * crE (2 * j + 3) (2 * (j + 1)) (Bali.ConjB.Ke (j + 1)) := by
  have hs0 := V_oddstep (K := 2 * j + 2) (by omega) (j + 1) (by omega)
  rw [show 2 * (j + 1) = 2 * j + 2 by ring] at hs0 ⊢
  have hco := co_succ (K := 2 * j + 2) (2 * j + 1)
  rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring] at hco
  have hτ : τ (2 * j + 2) (2 * j + 2) = TT (2 * j + 2) (2 * j + 1) := by
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring]; simp only [τ, TT]; rw [pF_eq _ (by omega)]
  have hT := TT_formula' (K := 2 * j + 2) (by omega) (2 * j + 1) (by omega)
  rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring] at hT
  have hS2 : Bali.RS.Scl (2 * j + 2 + 1) (2 * j + 2)
      = Bali.RS.Scl (2 * j + 2 + 1) (2 * j + 1) * Bali.RS.rho (2 * j + 2 + 1) (2 * j + 1) := rfl
  have hS1 : Bali.RS.Scl (2 * j + 2 + 1) (2 * j + 1)
      = Bali.RS.Scl (2 * j + 2 + 1) (2 * j) * Bali.RS.rho (2 * j + 2 + 1) (2 * j) := rfl
  have r0 : Bali.RS.rho (2 * j + 2 + 1) (2 * j) = -(2 * (j : ℚ) + 1) ^ 2 * 6 / ((2 * (j : ℚ) + 6) ^ 2 * 4) := by
    unfold Bali.RS.rho; rw [if_pos (by omega)]; push_cast; congr 1 <;> ring
  have r1 : Bali.RS.rho (2 * j + 2 + 1) (2 * j + 1) = -4 / 2 := by
    unfold Bali.RS.rho; rw [if_neg (by omega)]; push_cast; congr 1 <;> ring
  have q := Rc_succ (K := 2 * j + 2) (2 * j + 1) (by omega)
  rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring] at q
  have hq : Rc (2 * j + 2) (2 * j + 2) * (2 * (2 * (j : ℚ) + 5)) + Rc (2 * j + 2) (2 * j + 1) * (4 * (2 * (j : ℚ) + 2)) = 0 := by
    push_cast at q; linear_combination q
  set R1 := Rc (2 * j + 2) (2 * j + 1)
  set R2 := Rc (2 * j + 2) (2 * j + 2)
  set l := ll (2 * j + 2) (2 * j + 2)
  set S0 := Bali.RS.Scl (2 * j + 2 + 1) (2 * j)
  set ρ0 := Bali.RS.rho (2 * j + 2 + 1) (2 * j)
  set ρ1 := Bali.RS.rho (2 * j + 2 + 1) (2 * j + 1)
  set P : ℚ := 2 ^ (2 * (2 * j + 2 + 1))
  set Vp := VBvol (fun h : Fin (2 * j + 2 + 1 + 1) => yv (2 * j + 2) (h : ℕ)) (nuV (2 * j + 2)) (2 * j + 2 + 1)
  set V := VE (2 * j + 2) (j + 1)
  set E : ℚ := (1 / 4 : ℚ) ^ (2 * j + 2)
  set F4 : ℚ := (4 : ℚ) ^ (2 * j + 2)
  have he : E * F4 - 1 = 0 := by
    simp only [E, F4]; rw [← mul_pow]; norm_num
  have hs : R1 * l * E * Vp - P * (R1 * S0 * ρ0 * ρ1 - R2 * S0 * ρ0) * V = 0 := by
    rw [hco, hτ, hT, hS2, hS1] at hs0
    linear_combination hs0
  have hX' : R1 * (2 * (2 * (j : ℚ) + 5)) * l * Vp
      = R1 * V * P * S0 * ρ0 * (ρ1 * (2 * (2 * (j : ℚ) + 5)) + 4 * (2 * (j : ℚ) + 2)) * F4 := by
    have hE : E ≠ 0 := by positivity
    apply mul_left_cancel₀ hE
    linear_combination (2 * (2 * (j : ℚ) + 5)) * hs + (-P * S0 * V * ρ0) * hq
      + (-2 * P * R1 * S0 * V * ρ0 * (2 * (j : ℚ) * ρ1 + 4 * j + 5 * ρ1 + 4)) * he
  have nR : R1 ≠ 0 := by
    simp only [R1]; unfold Rc; rw [Bali.RE.RE_centre _ _ (by omega)]; exact Bali.TN.F_ne _ _ (by omega)
  have nl : l ≠ 0 := by
    simp only [l]; unfold ll; rw [RPE_coeff]
    exact mul_ne_zero (Bali.Chr.ce_ne _ _ (by omega) _ le_rfl) (pow_ne_zero _ (by norm_num))
  have hX : Vp = V * (P * S0 * ρ0 * (ρ1 * (2 * (2 * (j : ℚ) + 5)) + 4 * (2 * (j : ℚ) + 2)) * F4)
      / ((2 * (2 * (j : ℚ) + 5)) * l) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) nl)]
    apply mul_left_cancel₀ nR
    linear_combination hX'
  have hSc := Scl_closed (2 * j + 2 + 1) j (by omega)
  rw [show 2 * j + 2 + 1 - j = j + 3 by omega] at hSc
  have hS0 : S0 = 2 * (2 * (j : ℚ) + 3) * (((2 * j).factorial : ℚ) * ((j + 3).factorial : ℚ)) ^ 2
      / (6 * (4 ^ j * (j.factorial : ℚ) * ((2 * j + 2 + 1).factorial : ℚ)) ^ 2) := by
    rw [eq_div_iff (by positivity)]
    push_cast at hSc ⊢
    linear_combination hSc
  have hl := Bali.Chr.ell_closedE (2 * j + 2) (2 * j + 2) le_rfl
  rw [show 2 * (2 * j + 2 + 1) - (2 * j + 2) = 2 * j + 4 by omega, Nat.sub_self,
    show 2 * j + 2 + 1 - (2 * j + 2) = 1 by omega, show 2 * (2 * j + 2 + 1) - 2 * (2 * j + 2) = 2 by omega,
    show 2 * (2 * j + 2 + 1) = 4 * j + 6 by ring] at hl
  have hlv : l = ((2 * j + 4).factorial : ℚ) ^ 2
      / (2 * ((4 * j + 6).factorial : ℚ) * ((2 * j + 2).factorial : ℚ) * ((2 * j + 2 + 1).factorial : ℚ)) := by
    simp only [l, ll]; rw [hl]; simp only [Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two]; push_cast; ring
  have hs' : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have G1 : Real.Gamma (((2 * j + 3 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 3 / 2) = 24 * √Real.pi / (4 ^ 2 * 2) := by
    rw [show ((2 * j + 3 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 3 / 2 = ((2 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half]; norm_num [Nat.factorial]
  have G2 : Real.Gamma (((2 * j + 3 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 1) = 1 := by
    rw [show ((2 * j + 3 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 1 = ((1 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]; norm_num
  have G3 : Real.Gamma ((2 * ((2 * j + 3 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 1) / 2)
      = ((2 * j + 4).factorial : ℝ) * √Real.pi / (4 ^ (j + 2) * (j + 2).factorial) := by
    rw [show (2 * ((2 * j + 3 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 1) / 2 = ((j + 2 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (j + 2) = 2 * j + 4 by ring]
  have G4 : Real.Gamma ((2 * ((2 * j + 3 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 3) / 2)
      = ((2 * j + 6).factorial : ℝ) * √Real.pi / (4 ^ (j + 3) * (j + 3).factorial) := by
    rw [show (2 * ((2 * j + 3 : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 3) / 2 = ((j + 3 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (j + 3) = 2 * j + 6 by ring]
  unfold crE Bali.ConjB.Ke
  rw [G1, G2, G3, G4, show 2 * (2 * j + 3) = 4 * j + 6 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
  have hP : P = (4 : ℚ) ^ (2 * j + 2 + 1) := by simp only [P]; rw [pow_mul]; norm_num
  have hF : F4 = (4 : ℚ) ^ (2 * j + 2) := rfl
  rw [hX, hS0, r0, r1, hlv, hP, hF]
  push_cast
  have e1 : ((2 * j + 2 + 1).factorial : ℝ) = (2 * (j : ℝ) + 3) * (2 * j + 2) * (2 * j + 1) * ((2 * j).factorial : ℝ) := by
    rw [show 2 * j + 2 + 1 = (2 * j + 1) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have e2 : ((2 * j + 2).factorial : ℝ) = (2 * (j : ℝ) + 2) * (2 * j + 1) * ((2 * j).factorial : ℝ) := by
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have e3 : ((j + 3).factorial : ℝ) = ((j : ℝ) + 3) * ((j + 2).factorial : ℝ) := by
    rw [show j + 3 = (j + 2) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  have e4 : ((2 * j + 6).factorial : ℝ) = (2 * (j : ℝ) + 6) * (2 * j + 5) * ((2 * j + 4).factorial : ℝ) := by
    rw [show 2 * j + 6 = (2 * j + 4) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have e5 : ((j + 1).factorial : ℝ) = ((j : ℝ) + 1) * (j.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [e1, e2, e3, e4, e5]
  have := hs'.ne'
  field_simp
  ring

/-- **Conjecture B for even `n = 2m` (`m ≥ 3`), shell form, every `d ≤ m`.** -/
theorem conjB_evenN_full (s d : ℕ) (hd : d ≤ s + 3) :
    ((VBvol (fun h : Fin (s + 2 + 1 + 1) => yv (s + 2) (h : ℕ)) (nuV (s + 2)) d : ℚ) : ℝ)
      = ∏ j ∈ range d, crE (s + 3) j (Kc j) := by
  rcases Nat.lt_or_ge d (s + 3) with h | h
  · exact conjB_evenN s d (by omega)
  · obtain rfl : d = s + 3 := by omega
    obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' s
    · -- m = 2t+3 odd
      have h1 : ((VBvol (fun h : Fin (2 * t + 2 + 1 + 1) => yv (2 * t + 2) (h : ℕ)) (nuV (2 * t + 2)) (2 * t + 3) : ℚ) : ℝ)
          = VE (2 * t + 2) (t + 1) * crE (2 * t + 3) (2 * t + 2) (Bali.ConjB.Ke (t + 1)) := conjBO_edge t
      have hev := evens (2 * t) (t + 1) (by omega)
      rw [h1, hev, show 2 * t + 3 = (2 * t + 2) + 1 from rfl, prod_range_succ, show 2 * (t + 1) = 2 * t + 2 by ring,
        show 2 * t + 2 = 2 * (t + 1) by ring, Kc_even]
    · -- m = 2t+4 even
      have h1 := conjBE_edge t
      have hev := evens (2 * t + 1) (t + 1) (by omega)
      have hL : ((VBvol (fun h : Fin (2 * t + 1 + 2 + 1 + 1) => yv (2 * t + 1 + 2) (h : ℕ)) (nuV (2 * t + 1 + 2)) (2 * t + 1 + 3) : ℚ) : ℝ)
          = (VE (2 * t + 3) (t + 2) : ℝ) := rfl
      rw [hL, h1, show (2 * t + 1 + 3) = 2 * t + 4 by ring]
      rw [show 2 * t + 1 + 2 = 2 * t + 3 by ring, show 2 * t + 1 + 3 = 2 * t + 4 by ring] at hev
      rw [hev, show 2 * t + 4 = 2 * (t + 1) + 1 + 1 by ring, prod_range_succ, prod_range_succ,
        show 2 * (t + 1) = 2 * t + 2 by ring, show 2 * t + 2 = 2 * (t + 1) by ring, Kc_even, Kc_odd]
      ring
/-- **Conjecture B for even `n = 2m` (`m ≥ 3`), point form, every `d ≤ m`.** -/
theorem conjB_evenN_x_full (s d : ℕ) (hd : d ≤ s + 3) :
    ((Bali.ShellX.VBs (fun x : Fin (2 * (s + 2) + 3) => (2 * (x : ℚ) - (2 * (s + 2) + 2)) ^ 2)
        (fun x => ((2 * (s + 2) + 2).choose (x : ℕ) : ℚ)) d : ℚ) : ℝ)
      = ∏ j ∈ range d, crE (s + 3) j (Kc j) := by
  have h := Bali.ShellXE.VBx_eq_even (s + 2) d
  push_cast at h
  rw [h, conjB_evenN_full s d hd]

/-! ## the small cases `n = 2, 4` -/

lemma Pp_single {n : ℕ} (f : Fin n → ℚ) (a : Fin n) : Bali.ShellX.Pp f {a} = 1 := by
  simp [Bali.ShellX.Pp, Finset.filter_singleton]

lemma Pp_pair {n : ℕ} (f : Fin n → ℚ) (a b : Fin n) (h : a < b) : Bali.ShellX.Pp f {a, b} = |f b - f a| := by
  unfold Bali.ShellX.Pp
  rw [prod_pair (ne_of_lt h)]
  have h1 : ({a, b} : Finset (Fin n)).filter (fun c => a < c) = {b} := by
    ext c; simp only [mem_filter, mem_insert, mem_singleton]; constructor
    · rintro ⟨rfl | rfl, hc⟩
      · exact absurd hc (lt_irrefl _)
      · rfl
    · rintro rfl; exact ⟨Or.inr rfl, h⟩
  have h2 : ({a, b} : Finset (Fin n)).filter (fun c => b < c) = ∅ := by
    ext c; simp only [mem_filter, mem_insert, mem_singleton, Finset.notMem_empty, iff_false, not_and]
    rintro (rfl | rfl)
    · exact fun hc => absurd (h.trans hc) (lt_irrefl _)
    · exact lt_irrefl _
  rw [h1, h2, prod_singleton, prod_empty, mul_one]

theorem small_n2_d1 : Bali.ShellX.VBs (fun x : Fin 3 => (2 * (x : ℚ) - 2) ^ 2) (fun x => ((2 : ℕ).choose (x : ℕ) : ℚ)) 1 = 4 := by
  have hS : (univ : Finset (Fin 3)).powersetCard 1 = {{0}, {1}, {2}} := by decide
  simp only [Bali.ShellX.VBs, hS]
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp only [Pp_single, prod_singleton, mul_one]
  simp [Nat.choose]
  norm_num

theorem small_n4_d1 : Bali.ShellX.VBs (fun x : Fin 5 => (2 * (x : ℚ) - 4) ^ 2) (fun x => ((4 : ℕ).choose (x : ℕ) : ℚ)) 1 = 16 := by
  have hS : (univ : Finset (Fin 5)).powersetCard 1 = {{0}, {1}, {2}, {3}, {4}} := by decide
  simp only [Bali.ShellX.VBs, hS]
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp only [Pp_single, prod_singleton, mul_one]
  simp [Nat.choose]
  norm_num

theorem small_n4_d2 : Bali.ShellX.VBs (fun x : Fin 5 => (2 * (x : ℚ) - 4) ^ 2) (fun x => ((4 : ℕ).choose (x : ℕ) : ℚ)) 2 = 576 := by
  have hS : (univ : Finset (Fin 5)).powersetCard 2 =
      {{0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}} := by decide
  simp only [Bali.ShellX.VBs, hS]
  repeat rw [sum_insert (by decide)]
  rw [sum_singleton]
  rw [Pp_pair _ 0 1 (by decide), Pp_pair _ 0 2 (by decide), Pp_pair _ 0 3 (by decide), Pp_pair _ 0 4 (by decide),
    Pp_pair _ 1 2 (by decide), Pp_pair _ 1 3 (by decide), Pp_pair _ 1 4 (by decide), Pp_pair _ 2 3 (by decide),
    Pp_pair _ 2 4 (by decide), Pp_pair _ 3 4 (by decide)]
  rw [prod_pair (by decide), prod_pair (by decide), prod_pair (by decide), prod_pair (by decide), prod_pair (by decide),
    prod_pair (by decide), prod_pair (by decide), prod_pair (by decide), prod_pair (by decide), prod_pair (by decide)]
  simp [Nat.choose]
  norm_num
lemma VBs_zero {n : ℕ} (f w : Fin n → ℚ) : Bali.ShellX.VBs f w 0 = 1 := by
  simp [Bali.ShellX.VBs, Bali.ShellX.Pp]

lemma G_half (k : ℕ) : Real.Gamma ((k : ℝ) + 1 / 2) = ((2 * k).factorial : ℝ) * √Real.pi / (4 ^ k * k.factorial) :=
  Bali.ConjB.Gamma_half k

/-- **`n = 2`**, every `d ≤ m = 1`. -/
theorem conjB_n2 (d : ℕ) (hd : d ≤ 1) :
    ((Bali.ShellX.VBs (fun x : Fin 3 => (2 * (x : ℚ) - 2) ^ 2) (fun x => ((2 : ℕ).choose (x : ℕ) : ℚ)) d : ℚ) : ℝ)
      = ∏ j ∈ range d, crE 1 j (Kc j) := by
  interval_cases d
  · simp [VBs_zero]
  · rw [small_n2_d1, prod_range_one]
    simp only [Kc, Nat.zero_mod, if_true, Nat.zero_div]
    unfold crE Bali.ConjB.Ke
    have hs : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
    rw [show ((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 3 / 2 = ((2 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      show ((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 1 = ((1 : ℕ) : ℝ) + 1 by push_cast; ring,
      show (2 * ((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 1) / 2 = ((1 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      show (2 * ((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 3) / 2 = ((2 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      G_half, G_half, Real.Gamma_nat_eq_factorial]
    have := hs.ne'
    norm_num [Nat.factorial]
    field_simp

/-- **`n = 4`**, every `d ≤ m = 2`. -/
theorem conjB_n4 (d : ℕ) (hd : d ≤ 2) :
    ((Bali.ShellX.VBs (fun x : Fin 5 => (2 * (x : ℚ) - 4) ^ 2) (fun x => ((4 : ℕ).choose (x : ℕ) : ℚ)) d : ℚ) : ℝ)
      = ∏ j ∈ range d, crE 2 j (Kc j) := by
  have hs : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have c0 : crE 2 0 (Kc 0) = 16 := by
    simp only [Kc, Nat.zero_mod, if_true, Nat.zero_div]
    unfold crE Bali.ConjB.Ke
    rw [show ((2 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 3 / 2 = ((3 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      show ((2 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 1 = ((2 : ℕ) : ℝ) + 1 by push_cast; ring,
      show (2 * ((2 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 1) / 2 = ((2 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      show (2 * ((2 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 3) / 2 = ((3 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      G_half, G_half, Real.Gamma_nat_eq_factorial]
    have := hs.ne'
    norm_num [Nat.factorial]
    field_simp
    ring
  have c1 : crE 2 1 (Kc 1) = 36 := by
    simp only [Kc, show (1 : ℕ) % 2 = 1 from rfl, one_ne_zero, if_false, show (1 : ℕ) / 2 = 0 from rfl]
    unfold crE Bali.ConjB.Ko
    rw [show ((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) + 3 / 2 = ((2 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      show ((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) + 1 = ((1 : ℕ) : ℝ) + 1 by push_cast; ring,
      show (2 * ((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) + 1) / 2 = ((1 : ℕ) : ℝ) + 1 by push_cast; ring,
      show (2 * ((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) + 3) / 2 = ((2 : ℕ) : ℝ) + 1 by push_cast; ring,
      G_half]
    simp only [Real.Gamma_nat_eq_factorial]
    have := hs.ne'
    norm_num [Nat.factorial]
    field_simp
    ring
  interval_cases d
  · simp [VBs_zero]
  · rw [small_n4_d1, prod_range_one, c0]; norm_num
  · rw [small_n4_d2, prod_range_succ, prod_range_one, c0, c1]; norm_num
end Bali.VE

#print axioms Bali.VE.conjB_evenN_x_full
#print axioms Bali.VE.small_n4_d2
#print axioms Bali.VE.conjBO_edge
#print axioms Bali.VE.conjB_evenN_full
#print axioms Bali.VE.conjBE_edge
#print axioms Bali.VE.conjB_n2
#print axioms Bali.VE.conjB_n4
