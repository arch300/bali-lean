import Mathlib

/-!
# Even `n = 2m`: the Racah family at the centre `x = m` (Bali lab, 2026-11-02)
At `x = m` the series reduces to `F(a) = Σ_j (-a)_j (a-n)_j / ((-n)_j j!) · m/(m-j)`, and
`F(a) = (-1)^a n / ((n-2a) C(n,a))` for `a < m`, by a telescoping certificate in `j`.
-/

open Finset

namespace Bali.RC

/-- `P a j = (-a)_j (a-n)_j / ((-n)_j j!)`, `n = 2m`. -/
def P (m a : ℕ) : ℕ → ℚ
  | 0 => 1
  | j + 1 => P m a j * (((j : ℚ) - a) * ((a : ℚ) - 2 * m + j) / (((j : ℚ) - 2 * m) * ((j : ℚ) + 1)))

/-- the term with the factor `m/(m-j)`. -/
def t (m a j : ℕ) : ℚ := P m a j * ((m : ℚ) / ((m : ℚ) - j))

def F (m a : ℕ) : ℚ := ∑ j ∈ range (a + 1), t m a j

lemma P_last (m a : ℕ) : P m a (a + 1) = 0 := by
  simp [P]

lemma P_shift (m a : ℕ) : ∀ j, P m (a + 1) j * ((a : ℚ) + 1 - j) * ((a : ℚ) - 2 * m)
    = P m a j * ((a : ℚ) + 1) * ((a : ℚ) - 2 * m + j)
  | 0 => by simp [P]
  | j + 1 => by
    have ih := P_shift m a j
    simp only [P]
    push_cast
    linear_combination (-((a : ℚ) + 1 - 2 * m + j) * ((a : ℚ) - j)
      / (((j : ℚ) - 2 * m) * ((j : ℚ) + 1))) * ih

/-- the telescoping certificate. -/
lemma tele (m a : ℕ) (ha : a + 1 < m) : ∀ J, J ≤ a + 2 →
    ∑ j ∈ range J, (-((a : ℚ) + 1) * ((a : ℚ) - m) * t m a j
        + ((a : ℚ) - 2 * m) * ((a : ℚ) + 1 - m) * t m (a + 1) j)
      = P m (a + 1) J * ((2 * (a : ℚ) + 1 - 2 * m) / (((a : ℚ) + 1) * ((a : ℚ) - 2 * m + J))) *
          ((m : ℚ) * J * ((J : ℚ) - 1 - 2 * m))
  | 0, _ => by simp
  | J + 1, hJ => by
    rw [sum_range_succ, tele m a ha J (by omega)]
    have hJa : (J : ℚ) ≤ (a : ℚ) + 1 := by exact_mod_cast (by omega : J ≤ a + 1)
    have ham : (a : ℚ) + 2 ≤ m := by exact_mod_cast (by omega : a + 2 ≤ m)
    have ha0 : (0 : ℚ) ≤ a := by positivity
    have hJ0 : (0 : ℚ) ≤ J := by positivity
    have d1 : (a : ℚ) + 1 ≠ 0 := by positivity
    have d2 : (a : ℚ) - 2 * m + J ≠ 0 := by intro h; linarith
    have d3 : (a : ℚ) - 2 * m + J + 1 ≠ 0 := by intro h; linarith
    have d4 : (J : ℚ) - 2 * m ≠ 0 := by intro h; linarith
    have d5 : (J : ℚ) + 1 ≠ 0 := by positivity
    have d6 : (m : ℚ) - J ≠ 0 := by intro h; linarith
    have d7 : (a : ℚ) - 2 * m ≠ 0 := by intro h; linarith
    have hP : P m a J = P m (a + 1) J * ((a : ℚ) + 1 - J) * ((a : ℚ) - 2 * m)
        / (((a : ℚ) + 1) * ((a : ℚ) - 2 * m + J)) := by
      rw [P_shift]; field_simp
    have d3' : (a : ℚ) + 1 - 2 * m + J ≠ 0 := by intro h; linarith
    have hG : P m (a + 1) (J + 1) * ((2 * (a : ℚ) + 1 - 2 * m) / (((a : ℚ) + 1) * ((a : ℚ) - 2 * m + ((J + 1 : ℕ) : ℚ)))) *
        ((m : ℚ) * ((J + 1 : ℕ) : ℚ) * (((J + 1 : ℕ) : ℚ) - 1 - 2 * m))
        = P m (a + 1) J * ((J : ℚ) - a - 1) * (2 * (a : ℚ) + 1 - 2 * m) * m / ((a : ℚ) + 1) := by
      simp only [P]
      push_cast
      rw [show (a : ℚ) - 2 * m + (J + 1) = (a : ℚ) + 1 - 2 * m + J by ring,
        show (J : ℚ) + 1 - 1 - 2 * m = (J : ℚ) - 2 * m by ring]
      field_simp
      ring
    rw [hG]
    simp only [t, hP]
    push_cast
    field_simp
    ring

/-- first-order recurrence in `a`. -/
theorem F_rec (m a : ℕ) (ha : a + 1 < m) :
    -((a : ℚ) + 1) * ((a : ℚ) - m) * F m a + ((a : ℚ) - 2 * m) * ((a : ℚ) + 1 - m) * F m (a + 1) = 0 := by
  have h := tele m a ha (a + 2) le_rfl
  rw [show P m (a + 1) (a + 2) = 0 from P_last m (a + 1), zero_mul, zero_mul,
    sum_add_distrib, ← mul_sum, ← mul_sum, sum_range_succ (fun j => t m a j) (a + 1)] at h
  simpa [F, t, P_last] using h

/-- **The centre value.** `F(a) (n-2a) C(n,a) = (-1)^a n`, `n = 2m`, `a < m`. -/
theorem F_closed (m : ℕ) : ∀ a, a < m →
    F m a * ((2 * (m : ℚ) - 2 * a) * ((2 * m).choose a : ℚ)) = (-1) ^ a * (2 * m)
  | 0, h => by
    have : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    simp [F, t, P]; field_simp
  | a + 1, h => by
    have ih := F_closed m a (by omega)
    have hr := F_rec m a (by omega)
    have key : (((2 * m).choose (a + 1) : ℕ) : ℚ) * ((a : ℚ) + 1)
        = ((2 * m).choose a : ℚ) * (2 * (m : ℚ) - a) := by
      have := Nat.choose_succ_right_eq (2 * m) a
      have hc : ((2 * m - a : ℕ) : ℚ) = 2 * (m : ℚ) - a := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [← hc]; exact_mod_cast this
    have ham : (a : ℚ) + 2 ≤ m := by exact_mod_cast (by omega : a + 2 ≤ m)
    have d1 : (a : ℚ) + 1 ≠ 0 := by positivity
    have d2 : (a : ℚ) - m ≠ 0 := by intro h; linarith
    have ha0 : (0 : ℚ) ≤ a := by positivity
    have d3 : (a : ℚ) - 2 * m ≠ 0 := by intro h; linarith
    apply mul_left_cancel₀ d1
    push_cast
    rw [pow_succ]
    linear_combination F m (a + 1) * (2 * (m : ℚ) - 2 * a - 2) * key - ((a : ℚ) + 1) * ih
      + 2 * ((2 * m).choose a : ℚ) * hr
end Bali.RC

#print axioms Bali.RC.F_closed
