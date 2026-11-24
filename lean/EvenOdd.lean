import P699.VOdd

/-!
# Even `n = 2m`, odd `d`: the odd step in the Γ form (Bali lab, 2026-11-02)
-/

open Finset Polynomial Matrix

namespace Bali.VE
open Bali.EvenPsi Bali.Chr Bali.Skew Bali.VG Bali.PfP Bali.VB Bali.GA Bali.OddB Bali.OG

variable {K : ℕ}

/-- `Scl` at even indices in closed form. -/
theorem Scl_closed (M : ℕ) : ∀ k, 2 * k < M →
    Bali.RS.Scl M (2 * k) * ((2 * (M : ℚ) - 4 * k) * (4 ^ k * (k.factorial : ℚ) * (M.factorial : ℚ)) ^ 2)
      = 2 * (M : ℚ) * (((2 * k).factorial : ℚ) * ((M - k).factorial : ℚ)) ^ 2
  | 0, h => by simp [Bali.RS.Scl]
  | k + 1, h => by
    have ih := Scl_closed M k (by omega)
    have e : Bali.RS.Scl M (2 * (k + 1)) = Bali.RS.Scl M (2 * k) * Bali.RS.rho M (2 * k) * Bali.RS.rho M (2 * k + 1) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]; rfl
    have r0 : Bali.RS.rho M (2 * k) = -((2 * k : ℕ) + 1 : ℚ) ^ 2 * (2 * (M : ℚ) - 2 * (2 * k : ℕ))
        / ((2 * (M : ℚ) - (2 * k : ℕ)) ^ 2 * (2 * (M : ℚ) - 2 * (2 * k : ℕ) - 2)) := by
      unfold Bali.RS.rho; rw [if_pos (by omega)]
    have r1 : Bali.RS.rho M (2 * k + 1) = -(2 * (M : ℚ) - 2 * (2 * k + 1 : ℕ)) / (2 * (M : ℚ) - 2 * (2 * k + 1 : ℕ) - 2) := by
      unfold Bali.RS.rho; rw [if_neg (by omega)]
    obtain ⟨s, rfl⟩ : ∃ s, M = 2 * k + 3 + s := ⟨M - (2 * k + 3), by omega⟩
    have r0' : Bali.RS.rho (2 * k + 3 + s) (2 * k) = -(2 * (k : ℚ) + 1) ^ 2 * (2 * (s : ℚ) + 6)
        / ((2 * (k : ℚ) + 2 * s + 6) ^ 2 * (2 * (s : ℚ) + 4)) := by
      rw [r0]; push_cast; congr 1 <;> ring
    have r1' : Bali.RS.rho (2 * k + 3 + s) (2 * k + 1) = -(2 * (s : ℚ) + 4) / (2 * (s : ℚ) + 2) := by
      rw [r1]; push_cast; congr 1 <;> ring
    rw [e, r0', r1']
    rw [show 2 * k + 3 + s - (k + 1) = k + 2 + s by omega]
    rw [show 2 * k + 3 + s - k = (k + 2 + s) + 1 by omega, Nat.factorial_succ (k + 2 + s)] at ih
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k),
      Nat.factorial_succ k]
    push_cast at ih ⊢
    have hb : (4 ^ k * (k.factorial : ℚ) * ((2 * k + 3 + s).factorial : ℚ)) ≠ 0 := by positivity
    have hS : Bali.RS.Scl (2 * k + 3 + s) (2 * k) = 2 * (2 * (k : ℚ) + 3 + s) *
        (((2 * k).factorial : ℚ) * ((k + 2 + s + 1) * ((k + 2 + s).factorial : ℚ))) ^ 2
        / ((2 * (s : ℚ) + 6) * (4 ^ k * (k.factorial : ℚ) * ((2 * k + 3 + s).factorial : ℚ)) ^ 2) := by
      rw [eq_div_iff (mul_ne_zero (by positivity) (pow_ne_zero _ hb))]
      linear_combination ih
    rw [hS]
    have e1 : (2 * (2 * (k : ℚ) + 3 + s) - 4 * ((k : ℚ) + 1)) = 2 * (s : ℚ) + 2 := by ring
    rw [e1]
    field_simp
    ring
/-- **the odd step**, raw form. -/
theorem V_oddstep (hK : 2 ≤ K) (k : ℕ) (hk : 2 * k ≤ K) :
    co K (2 * k) * VBvol (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) (2 * k + 1) = τ K (2 * k) / 4 * VE K k := by
  have h1 := V_odd hK k hk
  have h2 := V_even_full hK k (by omega)
  rw [prod_co] at h2
  rw [show (∏ p : Fin (2 * k + 1), co K p) = ∏ p ∈ range (2 * k + 1), co K p from
    Fin.prod_univ_eq_prod_range (co K) (2 * k + 1), prod_range_succ, Bali.ConjB.sgn_range, prod_range_succ,
    ← h2, Bali.ConjB.sgn_range] at h1
  have p0 : (-1 : ℚ) ^ (2 * k) = 1 := by rw [pow_mul]; simp
  rw [p0] at h1
  have hP : ∏ s ∈ range (2 * k), co K s ≠ 0 := prod_ne_zero_iff.2 fun s hs =>
    co_ne (by omega) s (by have := mem_range.1 hs; omega)
  have hS : ∏ x ∈ range (2 * k), (-1 : ℚ) ^ x ≠ 0 := prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ (mul_ne_zero hP hS)
  unfold VE
  linear_combination h1

set_option maxHeartbeats 1000000 in
/-- **Conjecture B, even `n`, odd step `k = j+1 ≥ 1`**, `m = 2j+4+r`. -/
theorem conjBO_step (j r : ℕ) :
    ((VBvol (fun h : Fin (2 * j + 3 + r + 1 + 1) => yv (2 * j + 3 + r) (h : ℕ)) (nuV (2 * j + 3 + r)) (2 * (j + 1) + 1) : ℚ) : ℝ)
      = VE (2 * j + 3 + r) (j + 1) * crE (2 * j + 4 + r) (2 * (j + 1)) (Bali.ConjB.Ke (j + 1)) := by
  have hs0 := V_oddstep (K := 2 * j + 3 + r) (by omega) (j + 1) (by omega)
  rw [show 2 * (j + 1) = 2 * j + 2 by ring] at hs0 ⊢
  have hco := co_succ (K := 2 * j + 3 + r) (2 * j + 1)
  rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring] at hco
  have hτ : τ (2 * j + 3 + r) (2 * j + 2) = TT (2 * j + 3 + r) (2 * j + 1) := by
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring]; simp only [τ, TT]; rw [pF_eq _ (by omega)]
  have hT := TT_formula (K := 2 * j + 3 + r) (2 * j + 1) (by omega)
  rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring] at hT
  have hS2 : Bali.RS.Scl (2 * j + 3 + r + 1) (2 * j + 2)
      = Bali.RS.Scl (2 * j + 3 + r + 1) (2 * j + 1) * Bali.RS.rho (2 * j + 3 + r + 1) (2 * j + 1) := rfl
  have hS1 : Bali.RS.Scl (2 * j + 3 + r + 1) (2 * j + 1)
      = Bali.RS.Scl (2 * j + 3 + r + 1) (2 * j) * Bali.RS.rho (2 * j + 3 + r + 1) (2 * j) := rfl
  have r0 : Bali.RS.rho (2 * j + 3 + r + 1) (2 * j) = -(2 * (j : ℚ) + 1) ^ 2 * (2 * (r : ℚ) + 8)
      / ((2 * (j : ℚ) + 2 * r + 8) ^ 2 * (2 * (r : ℚ) + 6)) := by
    unfold Bali.RS.rho; rw [if_pos (by omega)]; push_cast; congr 1 <;> ring
  have r1 : Bali.RS.rho (2 * j + 3 + r + 1) (2 * j + 1) = -(2 * (r : ℚ) + 6) / (2 * (r : ℚ) + 4) := by
    unfold Bali.RS.rho; rw [if_neg (by omega)]; push_cast; congr 1 <;> ring
  have q := Rc_succ (K := 2 * j + 3 + r) (2 * j + 1) (by omega)
  rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring] at q
  have hq : Rc (2 * j + 3 + r) (2 * j + 2) * ((2 * (r : ℚ) + 4) * (2 * (j : ℚ) + 7 + 2 * r))
      + Rc (2 * j + 3 + r) (2 * j + 1) * ((2 * (r : ℚ) + 6) * (2 * (j : ℚ) + 2)) = 0 := by
    push_cast at q; linear_combination q
  set R1 := Rc (2 * j + 3 + r) (2 * j + 1)
  set R2 := Rc (2 * j + 3 + r) (2 * j + 2)
  set l := ll (2 * j + 3 + r) (2 * j + 2)
  set S0 := Bali.RS.Scl (2 * j + 3 + r + 1) (2 * j)
  set ρ0 := Bali.RS.rho (2 * j + 3 + r + 1) (2 * j)
  set ρ1 := Bali.RS.rho (2 * j + 3 + r + 1) (2 * j + 1)
  set P : ℚ := 2 ^ (2 * (2 * j + 3 + r + 1))
  set Vp := VBvol (fun h : Fin (2 * j + 3 + r + 1 + 1) => yv (2 * j + 3 + r) (h : ℕ)) (nuV (2 * j + 3 + r)) (2 * j + 2 + 1)
  set V := VE (2 * j + 3 + r) (j + 1)
  set E : ℚ := (1 / 4 : ℚ) ^ (2 * j + 2)
  set F4 : ℚ := (4 : ℚ) ^ (2 * j + 2)
  have he : E * F4 - 1 = 0 := by
    simp only [E, F4]; rw [← mul_pow]; norm_num
  have hs : R1 * l * E * Vp - P * (R1 * S0 * ρ0 * ρ1 - R2 * S0 * ρ0) * V = 0 := by
    rw [hco, hτ, hT, hS2, hS1] at hs0
    linear_combination hs0
  have hq' : R2 * ((2 * (r : ℚ) + 4) * (2 * (j : ℚ) + 7 + 2 * r)) + R1 * ((2 * (r : ℚ) + 6) * (2 * (j : ℚ) + 2)) = 0 := hq
  have hX' : R1 * ((2 * (r : ℚ) + 4) * (2 * (j : ℚ) + 7 + 2 * r)) * l * Vp
      = R1 * V * P * S0 * ρ0 * (ρ1 * ((2 * (r : ℚ) + 4) * (2 * (j : ℚ) + 7 + 2 * r)) + (2 * (r : ℚ) + 6) * (2 * (j : ℚ) + 2)) * F4 := by
    have hE : E ≠ 0 := by positivity
    apply mul_left_cancel₀ hE
    linear_combination (2 * ((r : ℚ) + 2) * (2 * (j : ℚ) + 2 * r + 7)) * hs + (-P * S0 * V * ρ0) * hq'
      + (-2 * P * R1 * S0 * V * ρ0 * (2 * (j : ℚ) * ρ1 * r + 4 * j * ρ1 + 2 * j * r + 6 * j + 2 * ρ1 * r ^ 2
        + 11 * ρ1 * r + 14 * ρ1 + 2 * r + 6)) * he
  have nR : R1 ≠ 0 := by
    simp only [R1]; unfold Rc; rw [Bali.RE.RE_centre _ _ (by omega)]; exact Bali.TN.F_ne _ _ (by omega)
  have nl : l ≠ 0 := by
    simp only [l]; unfold ll; rw [RPE_coeff]
    exact mul_ne_zero (Bali.Chr.ce_ne _ _ (by omega) _ le_rfl) (pow_ne_zero _ (by norm_num))
  have hX : Vp = V * (P * S0 * ρ0 * (ρ1 * ((2 * (r : ℚ) + 4) * (2 * (j : ℚ) + 7 + 2 * r)) + (2 * (r : ℚ) + 6) * (2 * (j : ℚ) + 2)) * F4)
      / (((2 * (r : ℚ) + 4) * (2 * (j : ℚ) + 7 + 2 * r)) * l) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) nl)]
    apply mul_left_cancel₀ nR
    linear_combination hX'
  -- closed forms
  have hSc := Scl_closed (2 * j + 3 + r + 1) j (by omega)
  rw [show 2 * j + 3 + r + 1 - j = (j + 3 + r) + 1 by omega, Nat.factorial_succ (j + 3 + r),
    Nat.factorial_succ (2 * j + 3 + r)] at hSc
  have hS0 : S0 = 2 * ((2 * j + 3 + r + 1 : ℕ) : ℚ) * (((2 * j).factorial : ℚ) * (((j + 3 + r + 1 : ℕ) : ℚ) * ((j + 3 + r).factorial : ℚ))) ^ 2
      / ((2 * (r : ℚ) + 8) * (4 ^ j * (j.factorial : ℚ) * (((2 * j + 3 + r + 1 : ℕ) : ℚ) * ((2 * j + 3 + r).factorial : ℚ))) ^ 2) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) (by positivity))]
    push_cast at hSc ⊢
    linear_combination hSc
  have hl := Bali.Chr.ell_closedE (2 * j + 3 + r) (2 * j + 2) (by omega)
  rw [show 2 * (2 * j + 3 + r + 1) - (2 * j + 2) = 2 * j + 6 + 2 * r by omega,
    show 2 * j + 3 + r - (2 * j + 2) = r + 1 by omega, show 2 * j + 3 + r + 1 - (2 * j + 2) = (r + 1) + 1 by omega,
    show 2 * (2 * j + 3 + r + 1) - 2 * (2 * j + 2) = 2 * r + 4 by omega,
    show 2 * (2 * j + 3 + r + 1) = 4 * j + 8 + 2 * r by ring, Nat.factorial_succ (2 * j + 3 + r),
    Nat.factorial_succ (r + 1)] at hl
  have hs' : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have G1 : Real.Gamma (((2 * j + 4 + r : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 3 / 2)
      = ((2 * r + 6).factorial : ℝ) * √Real.pi / (4 ^ (r + 3) * (r + 3).factorial) := by
    rw [show ((2 * j + 4 + r : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 3 / 2 = ((r + 3 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (r + 3) = 2 * r + 6 by ring]
  have G2 : Real.Gamma (((2 * j + 4 + r : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 1) = ((r + 2).factorial : ℝ) := by
    rw [show ((2 * j + 4 + r : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 1 = ((r + 2 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  have G3 : Real.Gamma ((2 * ((2 * j + 4 + r : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 1) / 2)
      = ((2 * j + 6 + 2 * r).factorial : ℝ) * √Real.pi / (4 ^ (j + 3 + r) * (j + 3 + r).factorial) := by
    rw [show (2 * ((2 * j + 4 + r : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 1) / 2 = ((j + 3 + r : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (j + 3 + r) = 2 * j + 6 + 2 * r by ring]
  have G4 : Real.Gamma ((2 * ((2 * j + 4 + r : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 3) / 2)
      = ((2 * j + 8 + 2 * r).factorial : ℝ) * √Real.pi / (4 ^ (j + 4 + r) * (j + 4 + r).factorial) := by
    rw [show (2 * ((2 * j + 4 + r : ℕ) : ℝ) - ((2 * j + 2 : ℕ) : ℝ) + 3) / 2 = ((j + 4 + r : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (j + 4 + r) = 2 * j + 8 + 2 * r by ring]
  unfold crE Bali.ConjB.Ke
  rw [G1, G2, G3, G4, show 2 * (2 * j + 4 + r) = 4 * j + 8 + 2 * r by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
  rw [show 2 * r + 6 = (2 * r + 5) + 1 by ring, Nat.factorial_succ (2 * r + 5),
    show 2 * r + 5 = (2 * r + 4) + 1 by ring, Nat.factorial_succ (2 * r + 4),
    show r + 3 = (r + 2) + 1 by ring, Nat.factorial_succ (r + 2),
    show r + 2 = (r + 1) + 1 by ring, Nat.factorial_succ (r + 1),
    show 2 * j + 8 + 2 * r = (2 * j + 7 + 2 * r) + 1 by ring, Nat.factorial_succ (2 * j + 7 + 2 * r),
    show 2 * j + 7 + 2 * r = (2 * j + 6 + 2 * r) + 1 by ring, Nat.factorial_succ (2 * j + 6 + 2 * r),
    show j + 4 + r = (j + 3 + r) + 1 by ring, Nat.factorial_succ (j + 3 + r),
    show 2 * j + 2 = (2 * j + 1) + 1 by ring, Nat.factorial_succ (2 * j + 1), Nat.factorial_succ (2 * j),
    Nat.factorial_succ j]
  have hlv : l = ((2 * j + 6 + 2 * r).factorial : ℚ) ^ 2 * ((r + 1).factorial : ℚ) * (((r : ℚ) + 1 + 1) * ((r + 1).factorial : ℚ))
      / (((2 * r + 4).factorial : ℚ) * ((4 * j + 8 + 2 * r).factorial : ℚ) * ((2 * j + 3 + r).factorial : ℚ) *
        (((2 * j + 3 + r : ℚ) + 1) * ((2 * j + 3 + r).factorial : ℚ))) := by
    simp only [l, ll]; rw [hl]; push_cast; ring
  have hP : P = (4 : ℚ) ^ (2 * j + 3 + r + 1) := by simp only [P]; rw [pow_mul]; norm_num
  have hF : F4 = (4 : ℚ) ^ (2 * j + 2) := rfl
  rw [hX, hS0, r0, r1, hlv, hP, hF]
  push_cast
  have := hs'.ne'
  field_simp
  ring
end Bali.VE

#print axioms Bali.VE.Scl_closed
#print axioms Bali.VE.V_oddstep
#print axioms Bali.VE.conjBO_step
