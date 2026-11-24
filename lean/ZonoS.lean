import Mathlib

/-!
# Main theorem `V_d(n)`: triangularising the Hankel matrix `μ_{i+j}` (Bali lab, 2026-11-02)
`Σ_l a_{i,l} μ_{l+j} = μ_j ∏_{t<i} ρ(t,j)`: Pfaff–Saalschütz, by a telescoping certificate in `l`.
All the denominators are odd integers, so no hypothesis on the size of `n` is needed.
-/

open Finset

namespace Bali.ZS

lemma oddne (n t : ℕ) : 2 * (n : ℚ) - 2 * t - 1 ≠ 0 := by
  intro h
  have : (2 * (n : ℤ) - 2 * t - 1) = 0 := by exact_mod_cast h
  omega

/-- the moments, normalised by `μ_0 = 1`. -/
def mu (n : ℕ) : ℕ → ℚ
  | 0 => 1
  | r + 1 => mu n r * ((2 * (r : ℚ) + 1) / (2 * (n : ℚ) - 2 * r - 1))

def a (n i : ℕ) : ℕ → ℚ
  | 0 => 1
  | l + 1 => a n i l * (-(((i : ℚ) - l) * (2 * (n : ℚ) - 2 * i + 1 - 2 * l)) / (((l : ℚ) + 1) * (2 * (l : ℚ) + 1)))

def rho (n t j : ℕ) : ℚ :=
  4 * ((t : ℚ) - j) * ((n : ℚ) - t) / ((2 * (t : ℚ) + 1) * (2 * (n : ℚ) - 2 * t - 2 * j - 1))

def Ss (n i j : ℕ) : ℚ := ∑ l ∈ range (i + 1), a n i l * mu n (l + j)

lemma a_gt (n i : ℕ) : ∀ s, a n i (i + 1 + s) = 0
  | 0 => by simp [a]
  | s + 1 => by rw [show i + 1 + (s + 1) = (i + 1 + s) + 1 by ring, a, a_gt n i s, zero_mul]

/-- `2n - 2i + 1 - 2l` is odd. -/
lemma odd1 (n i l : ℕ) : 2 * (n : ℚ) - 2 * i + 1 - 2 * l ≠ 0 := by
  intro h
  have : (2 * (n : ℤ) - 2 * i + 1 - 2 * l) = 0 := by exact_mod_cast h
  omega

lemma a_shift (n i : ℕ) : ∀ l, a n (i + 1) l * ((i : ℚ) + 1 - l) * (2 * (n : ℚ) - 2 * i + 1)
    = a n i l * ((i : ℚ) + 1) * (2 * (n : ℚ) - 2 * i + 1 - 2 * l)
  | 0 => by simp [a]
  | l + 1 => by
    have ih := a_shift n i l
    have d1 : (l : ℚ) + 1 ≠ 0 := by positivity
    have d2 : 2 * (l : ℚ) + 1 ≠ 0 := by positivity
    simp only [a]
    push_cast
    field_simp
    linear_combination (-((i : ℚ) - l) * (2 * (n : ℚ) - 2 * i - 1 - 2 * l)) * ih

lemma odd2 (n i j : ℕ) : 2 * (n : ℚ) - 2 * i - 2 * j - 1 ≠ 0 := by
  intro h
  have : (2 * (n : ℤ) - 2 * i - 2 * j - 1) = 0 := by exact_mod_cast h
  omega

/-- the certificate. -/
lemma tele (n i j : ℕ) : ∀ J, ∑ l ∈ range J, (a n (i + 1) l * mu n (l + j) - rho n i j * (a n i l * mu n (l + j)))
    = (4 * (i : ℚ) - 2 * n + 1) / (((i : ℚ) + 1) * (2 * (i : ℚ) + 1) * (2 * (n : ℚ) - 2 * i - 2 * j - 1))
      * ((J : ℚ) * (2 * (J : ℚ) - 1) * (2 * (n : ℚ) - 2 * J - 2 * j + 1) / (2 * (n : ℚ) - 2 * i + 1 - 2 * J))
      * (a n (i + 1) J * mu n (J + j))
  | 0 => by simp
  | J + 1 => by
    rw [sum_range_succ, tele n i j J]
    have d1 : (i : ℚ) + 1 ≠ 0 := by positivity
    have d2 : 2 * (i : ℚ) + 1 ≠ 0 := by positivity
    have d3 := odd2 n i j
    have d4 := odd1 n i J
    have d4' : 2 * (n : ℚ) - 2 * i + 1 - 2 * ((J : ℚ) + 1) ≠ 0 := by
      have := odd1 n i (J + 1); push_cast at this; exact this
    have d5 : (J : ℚ) + 1 ≠ 0 := by positivity
    have d6 : 2 * (J : ℚ) + 1 ≠ 0 := by positivity
    have d7 : 2 * (n : ℚ) - 2 * ((J : ℚ) + j) - 1 ≠ 0 := by
      have := oddne n (J + j); push_cast at this; exact this
    have d8 : 2 * (n : ℚ) - 2 * i + 1 ≠ 0 := by simpa using odd1 n i 0
    have h0 : a n i J = a n (i + 1) J * ((i : ℚ) + 1 - J) * (2 * (n : ℚ) - 2 * i + 1)
        / (((i : ℚ) + 1) * (2 * (n : ℚ) - 2 * i + 1 - 2 * J)) := by
      rw [eq_div_iff (mul_ne_zero d1 d4)]
      linear_combination -a_shift n i J
    have h1 : a n (i + 1) (J + 1) = a n (i + 1) J * (-(((i : ℚ) + 1 - J) * (2 * (n : ℚ) - 2 * i - 1 - 2 * J))
        / (((J : ℚ) + 1) * (2 * (J : ℚ) + 1))) := by
      simp only [a]; push_cast; ring_nf
    have h2 : mu n (J + 1 + j) = mu n (J + j) * ((2 * ((J : ℚ) + j) + 1) / (2 * (n : ℚ) - 2 * ((J : ℚ) + j) - 1)) := by
      rw [show J + 1 + j = (J + j) + 1 by ring, mu]; push_cast; rfl
    rw [h0, h1, h2]
    simp only [rho]
    push_cast
    rw [show 2 * (n : ℚ) - 2 * ((J : ℚ) + 1) - 2 * j + 1 = 2 * (n : ℚ) - 2 * ((J : ℚ) + j) - 1 by ring]
    generalize hA3 : 2 * (n : ℚ) - 2 * i - 2 * j - 1 = A3 at d3 ⊢
    generalize hA4 : 2 * (n : ℚ) - 2 * i + 1 - 2 * (J : ℚ) = A4 at d4 ⊢
    generalize hA5 : 2 * (n : ℚ) - 2 * i + 1 - 2 * ((J : ℚ) + 1) = A5 at d4' ⊢
    generalize hA7 : 2 * (n : ℚ) - 2 * ((J : ℚ) + j) - 1 = A7 at d7 ⊢
    generalize hA8 : 2 * (n : ℚ) - 2 * i + 1 = A8 at d8 ⊢
    field_simp
    subst hA3 hA4 hA5 hA7 hA8
    ring

theorem Ss_succ (n i j : ℕ) : Ss n (i + 1) j = rho n i j * Ss n i j := by
  have ht := tele n i j (i + 2)
  have hz : a n (i + 1) (i + 2) = 0 := by simpa using a_gt n (i + 1) 0
  have hz' : a n i (i + 1) = 0 := by simpa using a_gt n i 0
  rw [hz, zero_mul, mul_zero, sum_sub_distrib, ← mul_sum, sum_range_succ (fun l => a n i l * mu n (l + j)) (i + 1),
    hz', zero_mul, add_zero] at ht
  unfold Ss
  linarith

theorem Ss_closed (n i j : ℕ) : Ss n i j = mu n j * ∏ t ∈ range i, rho n t j := by
  induction i with
  | zero => simp [Ss, a]
  | succ i ih => rw [Ss_succ, ih, prod_range_succ]; ring

/-- **triangularity.** -/
theorem Ss_zero (n i j : ℕ) (h : j < i) : Ss n i j = 0 := by
  rw [Ss_closed, prod_eq_zero (mem_range.2 h) (by simp [rho]), mul_zero]

end Bali.ZS

#print axioms Bali.ZS.Ss_closed
#print axioms Bali.ZS.Ss_zero
