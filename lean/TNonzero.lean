import P699.VGram

/-!
# Even `n = 2m`: `T(p_a)` in closed form and nonzero (Bali lab, 2026-11-02)
`T(p_a) = 4·2ⁿ·F(a)·Scl(a)·(ρ(a) - (a+1)(a-m)/((a-n)(a+1-m)))`, and the bracket never vanishes.
-/

open Finset Polynomial

namespace Bali.TN
open Bali.Chr Bali.RE

lemma rho_ne (m a : ℕ) (ha : a + 2 < m) : Bali.RS.rho m a ≠ 0 := by
  have ham : (a : ℚ) + 3 ≤ m := by exact_mod_cast (by omega : a + 3 ≤ m)
  have h0 : (0 : ℚ) ≤ a := by positivity
  have d1 : 2 * (m : ℚ) - 2 * a ≠ 0 := by intro h; linarith
  have d2 : 2 * (m : ℚ) - 2 * a - 2 ≠ 0 := by intro h; linarith
  have d3 : 2 * (m : ℚ) - a ≠ 0 := by intro h; linarith
  have d4 : (a : ℚ) + 1 ≠ 0 := by positivity
  unfold Bali.RS.rho
  split_ifs
  · exact div_ne_zero (mul_ne_zero (neg_ne_zero.2 (pow_ne_zero _ d4)) d1) (mul_ne_zero (pow_ne_zero _ d3) d2)
  · exact div_ne_zero (neg_ne_zero.2 d1) d2

lemma Scl_ne (m : ℕ) : ∀ a, a + 1 < m → Bali.RS.Scl m a ≠ 0
  | 0, _ => by simp [Bali.RS.Scl]
  | a + 1, h => by
    rw [Bali.RS.Scl]
    exact mul_ne_zero (Scl_ne m a (by omega)) (rho_ne m a (by omega))

lemma F_ne (m a : ℕ) (ha : a < m) : Bali.RC.F m a ≠ 0 := by
  intro h
  have := Bali.RC.F_closed m a ha
  rw [h, zero_mul] at this
  have hm : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero two_ne_zero hm) this.symm

/-- the bracket is nonzero. -/
lemma bracket_ne (m a : ℕ) (ha : a + 2 < m) :
    Bali.RS.rho m a * (((a : ℚ) - 2 * m) * ((a : ℚ) + 1 - m)) - ((a : ℚ) + 1) * ((a : ℚ) - m) ≠ 0 := by
  have ham : (a : ℚ) + 3 ≤ m := by exact_mod_cast (by omega : a + 3 ≤ m)
  have h0 : (0 : ℚ) ≤ a := by positivity
  have dA : 2 * (m : ℚ) - a ≠ 0 := by intro h; linarith
  have dE : (m : ℚ) - a - 1 ≠ 0 := by intro h; linarith
  have dM : (m : ℚ) - a ≠ 0 := by intro h; linarith
  have d1 : (a : ℚ) + 1 ≠ 0 := by positivity
  have dO : 2 * (m : ℚ) - 2 * a - 1 ≠ 0 := by intro h; linarith
  have d2 : 2 * (m : ℚ) - 2 * a - 2 ≠ 0 := by intro h; linarith
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

/-- **`T(p_a) ≠ 0`**, for `a + 2 < m`. -/
theorem TB_ne (K a : ℕ) (ha : a + 2 < K + 1) : Bali.EvenPsi.TB K (pK (K + 1) a) ≠ 0 := by
  obtain ⟨s0, s1⟩ := Bali.RS.Sx_closed (K + 1) a ha
  have hF := Bali.RC.F_rec (K + 1) a (by omega)
  rw [TB_pK, RE_total _ _ (by omega), RE_total _ _ (by omega), RE_centre _ _ (by omega), RE_centre _ _ (by omega),
    s0, s1, Bali.RS.Scl]
  set F0 := Bali.RC.F (K + 1) a
  set F1 := Bali.RC.F (K + 1) (a + 1)
  set S := Bali.RS.Scl (K + 1) a
  set r := Bali.RS.rho (K + 1) a
  have hS : S ≠ 0 := Scl_ne _ a (by omega)
  have hF0 : F0 ≠ 0 := F_ne _ a (by omega)
  have hb := bracket_ne (K + 1) a ha
  have ham : (a : ℚ) + 2 ≤ ((K + 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : a + 2 ≤ K + 1)
  have h0 : (0 : ℚ) ≤ a := by positivity
  have d1 : (a : ℚ) - 2 * ((K + 1 : ℕ) : ℚ) ≠ 0 := by intro h; linarith
  have d2 : (a : ℚ) + 1 - ((K + 1 : ℕ) : ℚ) ≠ 0 := by intro h; linarith
  intro h
  apply hb
  have h' : (2 : ℚ) ^ (2 * (K + 1)) ≠ 0 := by positivity
  have h2 : F0 * (S * r) - F1 * S = 0 := by
    have : (4 : ℚ) * (2 ^ (2 * (K + 1))) * (F0 * (S * r) - F1 * S) = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero (by norm_num) h')
  apply mul_left_cancel₀ (mul_ne_zero hF0 hS)
  rw [mul_zero]
  linear_combination ((a : ℚ) - 2 * ((K + 1 : ℕ) : ℚ)) * ((a : ℚ) + 1 - ((K + 1 : ℕ) : ℚ)) * h2 + S * hF

end Bali.TN

#print axioms Bali.TN.TB_ne
