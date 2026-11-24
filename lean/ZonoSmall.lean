/-
Zonotope paper, Theorem (the cases d ≤ 5): explicit forms of the right-hand side of `Bali.ZF.main_theorem`.
Stated with the lowest admissible n written as m + d - 1.
-/
import P699.ZonoFinal

open Finset

namespace Bali.ZF

private abbrev C (n : ℕ) : ℚ := ((2 * n).choose n : ℚ)

theorem small_two (m : ℕ) : RHS (m + 1) 2 = (1 / 2) * ((m + 1 : ℕ) : ℚ) * C (m + 1) := by
  simp only [RHS, Kd, Zp, Wn, Tc, C]
  norm_num [Finset.prod_range_succ, Finset.prod_Ico_succ_top, dfk]
  rw [show (2 : ℚ) ^ (2 * (m + 1)) = 4 ^ (m + 1) by rw [pow_mul]; norm_num]
  field_simp

theorem small_three (m : ℕ) :
    RHS (m + 2) 3 = 2 ^ (m + 2) / 4 * ((m + 2 : ℕ) : ℚ) * ((m + 1 : ℕ) : ℚ) * C (m + 1) := by
  simp only [RHS, Kd, Zp, Wn, Tc, C]
  norm_num [Finset.prod_range_succ, Finset.prod_Ico_succ_top, dfk]
  rw [show (2 : ℚ) ^ (3 * (m + 2)) = 2 ^ (m + 2) * (4 * 4 ^ (m + 1)) by
    rw [show (4 : ℚ) * 4 ^ (m + 1) = 2 ^ (2 * (m + 2)) by rw [pow_mul]; norm_num [pow_succ]; ring, ← pow_add]; congr 1; ring]
  field_simp
  ring

theorem small_four (m : ℕ) :
    RHS (m + 3) 4 = (1 / 2) * ((m + 3 : ℕ) : ℚ) ^ 2 * ((m + 2 : ℕ) : ℚ) * ((m + 1 : ℕ) : ℚ) * C (m + 2) * C (m + 1) := by
  simp only [RHS, Kd, Zp, Wn, Tc, C]
  norm_num [Finset.prod_range_succ, Finset.prod_Ico_succ_top, Finset.Icc_self, dfk]
  rw [show (2 : ℚ) ^ (4 * (m + 3)) = 64 * (4 ^ (m + 2) * 4 ^ (m + 1)) by
    rw [show (64 : ℚ) = 2 ^ 6 by norm_num, show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 1; ring]
  field_simp
  ring

theorem small_five (m : ℕ) :
    RHS (m + 4) 5 = 3 * 2 ^ (m + 4) / 8 * ((m + 4 : ℕ) : ℚ) ^ 3 * ((m + 3 : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) * ((m + 1 : ℕ) : ℚ)
      * C (m + 2) * C (m + 1) := by
  simp only [RHS, Kd, Zp, Wn, Tc, C]
  norm_num [Finset.prod_range_succ, Finset.prod_Ico_succ_top, Finset.Icc_self, dfk, Finset.prod_Icc_succ_top]
  rw [show (2 : ℚ) ^ (5 * (m + 4)) = 2 ^ (m + 4) * (1024 * (4 ^ (m + 2) * 4 ^ (m + 1))) by
    rw [show (1024 : ℚ) = 2 ^ 10 by norm_num, show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring]
  field_simp
  ring

end Bali.ZF

#print axioms Bali.ZF.small_two
#print axioms Bali.ZF.small_three
#print axioms Bali.ZF.small_four
#print axioms Bali.ZF.small_five
