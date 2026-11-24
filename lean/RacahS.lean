import Mathlib

/-!
# Even `n = 2m`: the total `S_a / 2ⁿ = 3F2(-a, a-n, 1/2-m; 1-m, -n; 1)` (Bali lab, 2026-11-02)
A three-term recurrence in `a` (telescoping certificate in `j`), then the closed form with two parities.
-/

open Finset

namespace Bali.RS

def s (m a : ℕ) : ℕ → ℚ
  | 0 => 1
  | j + 1 => s m a j * (((j : ℚ) - a) * ((a : ℚ) - 2 * m + j) * (1 / 2 - (m : ℚ) + j)
      / ((1 - (m : ℚ) + j) * ((j : ℚ) - 2 * m) * ((j : ℚ) + 1)))

def Sx (m a : ℕ) : ℚ := ∑ j ∈ range (a + 1), s m a j

lemma s_gt (m a : ℕ) : ∀ i, s m a (a + 1 + i) = 0
  | 0 => by simp [s]
  | i + 1 => by
    rw [show a + 1 + (i + 1) = (a + 1 + i) + 1 by ring, s, s_gt m a i, zero_mul]

lemma s_shift (m a : ℕ) : ∀ j, s m (a + 1) j * ((a : ℚ) + 1 - j) * ((a : ℚ) - 2 * m)
    = s m a j * ((a : ℚ) + 1) * ((a : ℚ) - 2 * m + j)
  | 0 => by simp [s]
  | j + 1 => by
    have ih := s_shift m a j
    simp only [s]
    push_cast
    linear_combination (-((a : ℚ) + 1 - 2 * m + j) * ((a : ℚ) - j) * (1 / 2 - (m : ℚ) + j)
      / ((1 - (m : ℚ) + j) * ((j : ℚ) - 2 * m) * ((j : ℚ) + 1))) * ih

/-- the coefficients of the recurrence. -/
def C0 (m a : ℕ) : ℚ := ((a : ℚ) + 1) ^ 2 * ((a : ℚ) - m) * (2 * (a : ℚ) - 2 * m + 3)
def C1 (m a : ℕ) : ℚ := -((a : ℚ) - m + 1) *
  (2 * (a : ℚ) ^ 2 - 4 * a * m + 4 * a - 6 * m + 1)
def C2 (m a : ℕ) : ℚ := -((a : ℚ) - 2 * m + 1) ^ 2 * ((a : ℚ) - m + 2) * (2 * (a : ℚ) - 2 * m + 1)

lemma tele (m a : ℕ) (ha : a + 3 < m) : ∀ J, J ≤ a + 3 →
    ∑ j ∈ range J, (C0 m a * s m a j + C1 m a * s m (a + 1) j + C2 m a * s m (a + 2) j)
      = s m (a + 2) J * (2 * ((a : ℚ) - m + 1) * (2 * (a : ℚ) - 2 * m + 1) * (2 * (a : ℚ) - 2 * m + 3)
          * ((a : ℚ) + 1 - 2 * m) / (((a : ℚ) + 2) * ((a : ℚ) - 2 * m + J) * ((a : ℚ) + 1 - 2 * m + J))) *
          ((J : ℚ) * ((J : ℚ) - 1 - 2 * m) * ((J : ℚ) - m))
  | 0, _ => by simp
  | J + 1, hJ => by
    rw [sum_range_succ, tele m a ha J (by omega)]
    have hJa : (J : ℚ) ≤ (a : ℚ) + 2 := by exact_mod_cast (by omega : J ≤ a + 2)
    have ham : (a : ℚ) + 4 ≤ m := by exact_mod_cast (by omega : a + 4 ≤ m)
    have ha0 : (0 : ℚ) ≤ a := by positivity
    have hJ0 : (0 : ℚ) ≤ J := by positivity
    have d1 : (a : ℚ) + 1 ≠ 0 := by positivity
    have d2 : (a : ℚ) + 2 ≠ 0 := by positivity
    have d3 : (a : ℚ) - 2 * m + J ≠ 0 := by intro h; linarith
    have d4 : (a : ℚ) + 1 - 2 * m + J ≠ 0 := by intro h; linarith
    have d5 : (J : ℚ) - 2 * m ≠ 0 := by intro h; linarith
    have d6 : (J : ℚ) + 1 ≠ 0 := by positivity
    have d7 : 1 - (m : ℚ) + J ≠ 0 := by intro h; linarith
    have d8 : (a : ℚ) + 2 - 2 * m + J ≠ 0 := by intro h; linarith
    have hs1 : s m (a + 1) J = s m (a + 2) J * ((a : ℚ) + 2 - J) * ((a : ℚ) + 1 - 2 * m)
        / (((a : ℚ) + 2) * ((a : ℚ) + 1 - 2 * m + J)) := by
      have := s_shift m (a + 1) J
      push_cast at this
      rw [show (a : ℚ) + 1 + 1 = (a : ℚ) + 2 by ring] at this
      rw [eq_div_iff (mul_ne_zero d2 d4)]
      linear_combination -this
    have hs0 : s m a J = s m (a + 1) J * ((a : ℚ) + 1 - J) * ((a : ℚ) - 2 * m)
        / (((a : ℚ) + 1) * ((a : ℚ) - 2 * m + J)) := by
      rw [s_shift]; field_simp
    have hG : s m (a + 2) (J + 1) * (2 * ((a : ℚ) - m + 1) * (2 * (a : ℚ) - 2 * m + 1) * (2 * (a : ℚ) - 2 * m + 3)
          * ((a : ℚ) + 1 - 2 * m) / (((a : ℚ) + 2) * ((a : ℚ) - 2 * m + ((J + 1 : ℕ) : ℚ)) * ((a : ℚ) + 1 - 2 * m + ((J + 1 : ℕ) : ℚ)))) *
          (((J + 1 : ℕ) : ℚ) * (((J + 1 : ℕ) : ℚ) - 1 - 2 * m) * (((J + 1 : ℕ) : ℚ) - m))
        = s m (a + 2) J * ((J : ℚ) - a - 2) * (1 / 2 - (m : ℚ) + J) * (2 * ((a : ℚ) - m + 1) * (2 * (a : ℚ) - 2 * m + 1) * (2 * (a : ℚ) - 2 * m + 3)
          * ((a : ℚ) + 1 - 2 * m)) / (((a : ℚ) + 2) * ((a : ℚ) + 1 - 2 * m + J)) := by
      simp only [s]
      push_cast
      rw [show (a : ℚ) - 2 * m + (J + 1) = (a : ℚ) + 1 - 2 * m + J by ring,
        show (a : ℚ) + 1 - 2 * m + (J + 1) = (a : ℚ) + 2 - 2 * m + J by ring,
        show (a : ℚ) + 2 - 2 * m + J = (a : ℚ) + 2 - 2 * m + J from rfl,
        show (J : ℚ) + 1 - 1 - 2 * m = (J : ℚ) - 2 * m by ring,
        show (J : ℚ) + 1 - (m : ℚ) = 1 - (m : ℚ) + J by ring]
      field_simp
      ring
    rw [hG, hs0, hs1]
    simp only [C0, C1, C2]
    field_simp
    ring

/-- **three-term recurrence.** -/
theorem Sx_rec (m a : ℕ) (ha : a + 3 < m) :
    C0 m a * Sx m a + C1 m a * Sx m (a + 1) + C2 m a * Sx m (a + 2) = 0 := by
  have h := tele m a ha (a + 3) le_rfl
  have h3 : s m (a + 2) (a + 3) = 0 := s_gt m (a + 2) 0
  rw [h3, zero_mul, zero_mul, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum] at h
  have e0 : ∑ j ∈ range (a + 3), s m a j = Sx m a := by
    rw [sum_range_succ, sum_range_succ, show s m a (a + 1) = 0 from s_gt m a 0,
      show s m a (a + 2) = 0 from s_gt m a 1]; simp [Sx]
  have e1 : ∑ j ∈ range (a + 3), s m (a + 1) j = Sx m (a + 1) := by
    rw [sum_range_succ, show s m (a + 1) (a + 2) = 0 from s_gt m (a + 1) 0]; simp [Sx]
  have e2 : ∑ j ∈ range (a + 3), s m (a + 2) j = Sx m (a + 2) := rfl
  rw [e0, e1, e2] at h
  exact h

/-- the two-parity ratio `S_{a+1}/S_a`. -/
def rho (m a : ℕ) : ℚ :=
  if a % 2 = 0 then -((a : ℚ) + 1) ^ 2 * (2 * (m : ℚ) - 2 * a) / ((2 * (m : ℚ) - a) ^ 2 * (2 * (m : ℚ) - 2 * a - 2))
  else -(2 * (m : ℚ) - 2 * a) / (2 * (m : ℚ) - 2 * a - 2)

def Scl (m : ℕ) : ℕ → ℚ
  | 0 => 1
  | a + 1 => Scl m a * rho m a

lemma Scl_rec (m a : ℕ) (ha : a + 3 < m) :
    C0 m a * Scl m a + C1 m a * Scl m (a + 1) + C2 m a * Scl m (a + 2) = 0 := by
  have ham : (a : ℚ) + 4 ≤ m := by exact_mod_cast (by omega : a + 4 ≤ m)
  have ha0 : (0 : ℚ) ≤ a := by positivity
  have dA : 2 * (m : ℚ) - a ≠ 0 := by intro h; linarith
  have dB : 2 * (m : ℚ) - a - 1 ≠ 0 := by intro h; linarith
  have dE : (m : ℚ) - a - 1 ≠ 0 := by intro h; linarith
  have dG : (m : ℚ) - a - 2 ≠ 0 := by intro h; linarith
  have d2 : 2 * (m : ℚ) - 2 * a - 2 ≠ 0 := by intro h; linarith
  have d4 : 2 * (m : ℚ) - 2 * ((a : ℚ) + 1) - 2 ≠ 0 := by intro h; linarith
  have dA' : 2 * (m : ℚ) - ((a : ℚ) + 1) ≠ 0 := by intro h; linarith
  simp only [Scl]
  set r0 := rho m a with h0
  set r1 := rho m (a + 1) with h1
  suffices key : C0 m a + C1 m a * r0 + C2 m a * (r0 * r1) = 0 by
    linear_combination Scl m a * key
  rcases Nat.mod_two_eq_zero_or_one a with hp | hp
  · have hr0 : r0 * ((2 * (m : ℚ) - a) ^ 2 * ((m : ℚ) - a - 1)) = -(((a : ℚ) + 1) ^ 2 * ((m : ℚ) - a)) := by
      rw [h0, rho, if_pos hp, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero (pow_ne_zero _ dA) d2)]; ring
    have hr1 : r1 * ((m : ℚ) - a - 2) = -((m : ℚ) - a - 1) := by
      rw [h1, rho, if_neg (by omega)]; push_cast; rw [div_mul_eq_mul_div, div_eq_iff d4]; ring
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 dA) dE) dG)
    simp only [C0, C1, C2] at *
    linear_combination (((a : ℚ) - m + 1) * -(2 * (a : ℚ) ^ 2 - 4 * a * m + 4 * a - 6 * m + 1) * ((m : ℚ) - a - 2)
        + (-((a : ℚ) - 2 * m + 1) ^ 2 * ((a : ℚ) - m + 2) * (2 * (a : ℚ) - 2 * m + 1)) * r1 * ((m : ℚ) - a - 2)) * hr0
      + (-((a : ℚ) - 2 * m + 1) ^ 2 * ((a : ℚ) - m + 2) * (2 * (a : ℚ) - 2 * m + 1)) * (-(((a : ℚ) + 1) ^ 2 * ((m : ℚ) - a))) * hr1
  · have hr0 : r0 * ((m : ℚ) - a - 1) = -((m : ℚ) - a) := by
      rw [h0, rho, if_neg (by omega), div_mul_eq_mul_div, div_eq_iff d2]; ring
    have hr1 : r1 * ((2 * (m : ℚ) - a - 1) ^ 2 * ((m : ℚ) - a - 2)) = -(((a : ℚ) + 2) ^ 2 * ((m : ℚ) - a - 1)) := by
      rw [h1, rho, if_pos (by omega)]; push_cast; rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero (pow_ne_zero _ dA') d4)]; ring
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero dE (pow_ne_zero 2 dB)) dG)
    simp only [C0, C1, C2] at *
    linear_combination (((a : ℚ) - m + 1) * -(2 * (a : ℚ) ^ 2 - 4 * a * m + 4 * a - 6 * m + 1) * ((2 * (m : ℚ) - a - 1) ^ 2 * ((m : ℚ) - a - 2))
        + (-((a : ℚ) - 2 * m + 1) ^ 2 * ((a : ℚ) - m + 2) * (2 * (a : ℚ) - 2 * m + 1)) * r1 * ((2 * (m : ℚ) - a - 1) ^ 2 * ((m : ℚ) - a - 2))) * hr0
      + (-((a : ℚ) - 2 * m + 1) ^ 2 * ((a : ℚ) - m + 2) * (2 * (a : ℚ) - 2 * m + 1)) * (-((m : ℚ) - a)) * hr1
/-- **The closed form of the total**: both `Sx a` and `Sx (a+1)` for `a + 2 < m`, i.e. up to index `m - 2`. -/
theorem Sx_closed (m : ℕ) : ∀ a, a + 2 < m → Sx m a = Scl m a ∧ Sx m (a + 1) = Scl m (a + 1)
  | 0, h => by
    have hm : (2 : ℚ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
    have d1 : (m : ℚ) ≠ 0 := by intro h; linarith
    have d2 : (m : ℚ) - 1 ≠ 0 := by intro h; linarith
    have d3 : 1 - (m : ℚ) ≠ 0 := by intro h; linarith
    constructor
    · simp [Sx, Scl, s]
    · simp [Sx, Scl, s, sum_range_succ, rho]
      field_simp
      ring
  | a + 1, h => by
    obtain ⟨h0, h1⟩ := Sx_closed m a (by omega)
    refine ⟨h1, ?_⟩
    have r1 := Sx_rec m a (by omega)
    have r2 := Scl_rec m a (by omega)
    have ham : (a : ℚ) + 4 ≤ m := by exact_mod_cast (by omega : a + 4 ≤ m)
    have ha0 : (0 : ℚ) ≤ a := by positivity
    have hc : C2 m a ≠ 0 := by
      unfold C2
      have e1 : (a : ℚ) - 2 * m + 1 ≠ 0 := by intro h; linarith
      have e2 : (a : ℚ) - m + 2 ≠ 0 := by intro h; linarith
      have e3 : 2 * (a : ℚ) - 2 * m + 1 ≠ 0 := by intro h; linarith
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 (pow_ne_zero _ e1)) e2) e3
    rw [h0, h1] at r1
    exact mul_left_cancel₀ hc (by linear_combination r1 - r2)

/-! ## the boundary index `m - 1` -/

lemma tele' (m a : ℕ) (ha : a + 3 ≤ m) : ∀ J, J ≤ a + 2 →
    ∑ j ∈ range J, (C0 m a * s m a j + C1 m a * s m (a + 1) j + C2 m a * s m (a + 2) j)
      = s m (a + 2) J * (2 * ((a : ℚ) - m + 1) * (2 * (a : ℚ) - 2 * m + 1) * (2 * (a : ℚ) - 2 * m + 3)
          * ((a : ℚ) + 1 - 2 * m) / (((a : ℚ) + 2) * ((a : ℚ) - 2 * m + J) * ((a : ℚ) + 1 - 2 * m + J))) *
          ((J : ℚ) * ((J : ℚ) - 1 - 2 * m) * ((J : ℚ) - m))
  | 0, _ => by simp
  | J + 1, hJ => by
    rw [sum_range_succ, tele' m a ha J (by omega)]
    have hJa : (J : ℚ) + 1 ≤ (a : ℚ) + 2 := by exact_mod_cast (by omega : J + 1 ≤ a + 2)
    have ham : (a : ℚ) + 3 ≤ m := by exact_mod_cast ha
    have ha0 : (0 : ℚ) ≤ a := by positivity
    have hJ0 : (0 : ℚ) ≤ J := by positivity
    have d1 : (a : ℚ) + 1 ≠ 0 := by positivity
    have d2 : (a : ℚ) + 2 ≠ 0 := by positivity
    have d3 : (a : ℚ) - 2 * m + J ≠ 0 := by intro h; linarith
    have d4 : (a : ℚ) + 1 - 2 * m + J ≠ 0 := by intro h; linarith
    have d5 : (J : ℚ) - 2 * m ≠ 0 := by intro h; linarith
    have d6 : (J : ℚ) + 1 ≠ 0 := by positivity
    have d7 : 1 - (m : ℚ) + J ≠ 0 := by intro h; linarith
    have d8 : (a : ℚ) + 2 - 2 * m + J ≠ 0 := by intro h; linarith
    have hs1 : s m (a + 1) J = s m (a + 2) J * ((a : ℚ) + 2 - J) * ((a : ℚ) + 1 - 2 * m)
        / (((a : ℚ) + 2) * ((a : ℚ) + 1 - 2 * m + J)) := by
      have := s_shift m (a + 1) J
      push_cast at this
      rw [show (a : ℚ) + 1 + 1 = (a : ℚ) + 2 by ring] at this
      rw [eq_div_iff (mul_ne_zero d2 d4)]
      linear_combination -this
    have hs0 : s m a J = s m (a + 1) J * ((a : ℚ) + 1 - J) * ((a : ℚ) - 2 * m)
        / (((a : ℚ) + 1) * ((a : ℚ) - 2 * m + J)) := by
      rw [s_shift]; field_simp
    have hG : s m (a + 2) (J + 1) * (2 * ((a : ℚ) - m + 1) * (2 * (a : ℚ) - 2 * m + 1) * (2 * (a : ℚ) - 2 * m + 3)
          * ((a : ℚ) + 1 - 2 * m) / (((a : ℚ) + 2) * ((a : ℚ) - 2 * m + ((J + 1 : ℕ) : ℚ)) * ((a : ℚ) + 1 - 2 * m + ((J + 1 : ℕ) : ℚ)))) *
          (((J + 1 : ℕ) : ℚ) * (((J + 1 : ℕ) : ℚ) - 1 - 2 * m) * (((J + 1 : ℕ) : ℚ) - m))
        = s m (a + 2) J * ((J : ℚ) - a - 2) * (1 / 2 - (m : ℚ) + J) * (2 * ((a : ℚ) - m + 1) * (2 * (a : ℚ) - 2 * m + 1) * (2 * (a : ℚ) - 2 * m + 3)
          * ((a : ℚ) + 1 - 2 * m)) / (((a : ℚ) + 2) * ((a : ℚ) + 1 - 2 * m + J)) := by
      simp only [s]
      push_cast
      rw [show (a : ℚ) - 2 * m + (J + 1) = (a : ℚ) + 1 - 2 * m + J by ring,
        show (a : ℚ) + 1 - 2 * m + (J + 1) = (a : ℚ) + 2 - 2 * m + J by ring,
        show (J : ℚ) + 1 - 1 - 2 * m = (J : ℚ) - 2 * m by ring,
        show (J : ℚ) + 1 - (m : ℚ) = 1 - (m : ℚ) + J by ring]
      field_simp
      ring
    rw [hG, hs0, hs1]
    simp only [C0, C1, C2]
    field_simp
    ring

/-- the recurrence at `a = m - 3`. -/
theorem Sx_rec_edge (m a : ℕ) (ha : a + 3 = m) :
    C0 m a * Sx m a + C1 m a * Sx m (a + 1) + C2 m a * Sx m (a + 2) = 0 := by
  have h := tele' m a (by omega) (a + 2) le_rfl
  have ham : (a : ℚ) + 3 = m := by exact_mod_cast ha
  have e0 : ∑ j ∈ range (a + 3), s m a j = Sx m a := by
    rw [sum_range_succ, sum_range_succ, show s m a (a + 1) = 0 from s_gt m a 0,
      show s m a (a + 2) = 0 from s_gt m a 1]; simp [Sx]
  have e1 : ∑ j ∈ range (a + 3), s m (a + 1) j = Sx m (a + 1) := by
    rw [sum_range_succ, show s m (a + 1) (a + 2) = 0 from s_gt m (a + 1) 0]; simp [Sx]
  have e2 : ∑ j ∈ range (a + 3), s m (a + 2) j = Sx m (a + 2) := rfl
  rw [← e0, ← e1, ← e2, mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib, sum_range_succ, h,
    show s m a (a + 2) = 0 from s_gt m a 1, show s m (a + 1) (a + 2) = 0 from s_gt m (a + 1) 0]
  have ha0 : (0 : ℚ) ≤ a := by positivity
  have d2 : (a : ℚ) + 2 ≠ 0 := by positivity
  have d3 : (a : ℚ) - 2 * m + ((a + 2 : ℕ) : ℚ) ≠ 0 := by push_cast; intro h; linarith
  have d4 : (a : ℚ) + 1 - 2 * m + ((a + 2 : ℕ) : ℚ) ≠ 0 := by push_cast; intro h; linarith
  simp only [C0, C1, C2]
  rw [← ham] at d3 d4 ⊢
  push_cast at d3 d4 ⊢
  field_simp
  ring

lemma Scl_rec_edge (m a : ℕ) (ha : a + 3 = m) :
    C0 m a * Scl m a + C1 m a * Scl m (a + 1) + C2 m a * Scl m (a + 2) = 0 := by
  subst ha
  have ha0 : (0 : ℚ) ≤ a := by positivity
  have dA : 2 * ((a + 3 : ℕ) : ℚ) - a ≠ 0 := by push_cast; intro h; linarith
  have dB : 2 * ((a + 3 : ℕ) : ℚ) - a - 1 ≠ 0 := by push_cast; intro h; linarith
  have dE : ((a + 3 : ℕ) : ℚ) - a - 1 ≠ 0 := by push_cast; intro h; linarith
  have dG : ((a + 3 : ℕ) : ℚ) - a - 2 ≠ 0 := by push_cast; intro h; linarith
  have d2 : 2 * ((a + 3 : ℕ) : ℚ) - 2 * a - 2 ≠ 0 := by push_cast; intro h; linarith
  have d4 : 2 * ((a + 3 : ℕ) : ℚ) - 2 * ((a : ℚ) + 1) - 2 ≠ 0 := by push_cast; intro h; linarith
  have dA' : 2 * ((a + 3 : ℕ) : ℚ) - ((a : ℚ) + 1) ≠ 0 := by push_cast; intro h; linarith
  simp only [Scl]
  set r0 := rho (a + 3) a with h0
  set r1 := rho (a + 3) (a + 1) with h1
  suffices key : C0 (a + 3) a + C1 (a + 3) a * r0 + C2 (a + 3) a * (r0 * r1) = 0 by
    linear_combination Scl (a + 3) a * key
  rcases Nat.mod_two_eq_zero_or_one a with hp | hp
  · have hr0 : r0 = -((a : ℚ) + 1) ^ 2 * (2 * ((a + 3 : ℕ) : ℚ) - 2 * a) / ((2 * ((a + 3 : ℕ) : ℚ) - a) ^ 2 * (2 * ((a + 3 : ℕ) : ℚ) - 2 * a - 2)) := by
      rw [h0, rho, if_pos hp]
    have hr1 : r1 = -(2 * ((a + 3 : ℕ) : ℚ) - 2 * ((a + 1 : ℕ) : ℚ)) / (2 * ((a + 3 : ℕ) : ℚ) - 2 * ((a + 1 : ℕ) : ℚ) - 2) := by
      rw [h1, rho, if_neg (by omega)]
    rw [hr0, hr1]
    simp only [C0, C1, C2]
    push_cast at dA d2 ⊢
    have e1 : 2 * ((a : ℚ) + 3) - 2 * ((a : ℚ) + 1) - 2 = 2 := by ring
    have e2 : 2 * ((a : ℚ) + 3) - (a : ℚ) = (a : ℚ) + 6 := by ring
    have e3 : 2 * ((a : ℚ) + 3) - 2 * a - 2 = 4 := by ring
    rw [e1, e2, e3]
    have : (a : ℚ) + 6 ≠ 0 := by positivity
    field_simp
    ring
  · have hr0 : r0 = -(2 * ((a + 3 : ℕ) : ℚ) - 2 * a) / (2 * ((a + 3 : ℕ) : ℚ) - 2 * a - 2) := by
      rw [h0, rho, if_neg (by omega)]
    have hr1 : r1 = -(((a + 1 : ℕ) : ℚ) + 1) ^ 2 * (2 * ((a + 3 : ℕ) : ℚ) - 2 * ((a + 1 : ℕ) : ℚ))
        / ((2 * ((a + 3 : ℕ) : ℚ) - ((a + 1 : ℕ) : ℚ)) ^ 2 * (2 * ((a + 3 : ℕ) : ℚ) - 2 * ((a + 1 : ℕ) : ℚ) - 2)) := by
      rw [h1, rho, if_pos (by omega)]
    rw [hr0, hr1]
    simp only [C0, C1, C2]
    push_cast
    have e1 : 2 * ((a : ℚ) + 3) - 2 * ((a : ℚ) + 1) - 2 = 2 := by ring
    have e2 : 2 * ((a : ℚ) + 3) - ((a : ℚ) + 1) = (a : ℚ) + 5 := by ring
    have e3 : 2 * ((a : ℚ) + 3) - 2 * a - 2 = 4 := by ring
    rw [e1, e2, e3]
    have : (a : ℚ) + 5 ≠ 0 := by positivity
    field_simp
    ring

/-- **the boundary value** `Sx(m-1) = Scl(m-1)`, `m ≥ 3`. -/
theorem Sx_last (m : ℕ) (hm : 3 ≤ m) : Sx m (m - 1) = Scl m (m - 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 3 := ⟨m - 3, by omega⟩
  obtain ⟨h0, h1⟩ := Sx_closed (a + 3) a (by omega)
  have r1 := Sx_rec_edge (a + 3) a rfl
  have r2 := Scl_rec_edge (a + 3) a rfl
  have ha0 : (0 : ℚ) ≤ a := by positivity
  have hc : C2 (a + 3) a ≠ 0 := by
    unfold C2
    push_cast
    have e1 : (a : ℚ) - 2 * ((a : ℚ) + 3) + 1 ≠ 0 := by intro h; linarith
    have e2 : (a : ℚ) - ((a : ℚ) + 3) + 2 ≠ 0 := by intro h; linarith
    have e3 : 2 * (a : ℚ) - 2 * ((a : ℚ) + 3) + 1 ≠ 0 := by intro h; linarith
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 (pow_ne_zero _ e1)) e2) e3
  rw [h0, h1] at r1
  rw [show a + 3 - 1 = a + 2 by omega]
  exact mul_left_cancel₀ hc (by linear_combination r1 - r2)

/-- `Sx = Scl` for every index `≤ m - 1`. -/
theorem Sx_ext (m a : ℕ) (hm : 3 ≤ m) (ha : a + 1 ≤ m) : Sx m a = Scl m a := by
  rcases Nat.lt_or_ge (a + 2) m with h | h
  · exact (Sx_closed m a h).1
  · rcases Nat.lt_or_ge (a + 1) m with h' | h'
    · have := (Sx_closed m (a - 1) (by omega)).2
      rwa [show a - 1 + 1 = a by omega] at this
    · have := Sx_last m hm
      rwa [show m - 1 = a by omega] at this
end Bali.RS

#print axioms Bali.RS.Sx_closed
#print axioms Bali.RS.Sx_ext
