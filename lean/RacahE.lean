import P699.TWatson
import P699.RacahCentre
import P699.RacahS

/-!
# Even `n = 2m`: the Racah family `R_a` and its links to the two reduced series (Bali lab, 2026-11-02)
`R_a(x) = Σ_j (-a)_j (a-n)_j (-x)_j (x-n)_j / ((1-m)_j (-m)_j (-n)_j j!)`.
`RE_centre`: `R_a(m) = F(a)`;  `RE_total`: `Σ_x C(n,x) R_a(x) = 2ⁿ Sx(a)`.
-/

open Finset

namespace Bali.RE
open Bali.Racah Bali.TW

/-- coefficients of `R_a`. -/
def ce (m a : ℕ) : ℕ → ℚ
  | 0 => 1
  | j + 1 => ce m a j * (((j : ℚ) - a) * ((a : ℚ) - 2 * m + j)
      / ((1 - (m : ℚ) + j) * ((j : ℚ) - m) * ((j : ℚ) - 2 * m) * ((j : ℚ) + 1)))

/-- the Racah family for `n = 2m`. -/
def RE (m a : ℕ) (x : ℚ) : ℚ := ∑ j ∈ range (a + 1), ce m a j * phi (2 * (m : ℚ)) j x

lemma phi_succ (n x : ℚ) (j : ℕ) : phi n (j + 1) x = phi n j x * ((-x + j) * (x - n + j)) := by
  simp only [phi, P]; ring

lemma term_centre (m a : ℕ) : ∀ j, j < m →
    ce m a j * phi (2 * (m : ℚ)) j (m : ℚ) = Bali.RC.t m a j
  | 0, h => by
    have : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    simp [ce, phi, P, Bali.RC.t, Bali.RC.P, this]
  | j + 1, h => by
    have ih := term_centre m a j (by omega)
    have hj : (j : ℚ) + 2 ≤ m := by exact_mod_cast (by omega : j + 2 ≤ m)
    have hj0 : (0 : ℚ) ≤ j := by positivity
    have d1 : 1 - (m : ℚ) + j ≠ 0 := by intro h; linarith
    have d2 : (j : ℚ) - m ≠ 0 := by intro h; linarith
    have d3 : (j : ℚ) - 2 * m ≠ 0 := by intro h; linarith
    have d4 : (j : ℚ) + 1 ≠ 0 := by positivity
    have d5 : (m : ℚ) - j ≠ 0 := by intro h; linarith
    have d6 : (m : ℚ) - (j + 1) ≠ 0 := by intro h; linarith
    have e : ce m a (j + 1) * phi (2 * (m : ℚ)) (j + 1) (m : ℚ)
        = (ce m a j * phi (2 * (m : ℚ)) j (m : ℚ)) * (((j : ℚ) - a) * ((a : ℚ) - 2 * m + j) * ((j : ℚ) - m)
            / ((1 - (m : ℚ) + j) * ((j : ℚ) - 2 * m) * ((j : ℚ) + 1))) := by
      rw [phi_succ, ce]; field_simp; ring
    rw [e, ih]
    simp only [Bali.RC.t, Bali.RC.P]
    push_cast
    field_simp
    ring

/-- `R_a(m) = F(a)`. -/
theorem RE_centre (m a : ℕ) (ha : a < m) : RE m a (m : ℚ) = Bali.RC.F m a :=
  sum_congr rfl fun j hj => term_centre m a j (by have := mem_range.1 hj; omega)

lemma sum_phi (m j : ℕ) (hj : j ≤ m) :
    ∑ x ∈ range (2 * m + 1), ((2 * m).choose x : ℚ) * phi (2 * (m : ℚ)) j (x : ℚ)
      = ((2 * m).descFactorial (2 * j) : ℚ) * 2 ^ (2 * m - 2 * j) := by
  have h := sum_choose_desc (2 * m) j (by omega)
  have hq := congrArg (fun z : ℕ => (z : ℚ)) h
  push_cast at hq
  rw [← hq]
  refine sum_congr rfl fun x hx => ?_
  have hx' : x ≤ 2 * m := by have := mem_range.1 hx; omega
  have := phi_nat (2 * m) x j hx'
  push_cast at this
  rw [this]; ring

lemma ce_desc (m a : ℕ) : ∀ j, j < m →
    ce m a j * ((2 * m).descFactorial (2 * j) : ℚ) = 4 ^ j * Bali.RS.s m a j
  | 0, _ => by simp [ce, Bali.RS.s]
  | j + 1, h => by
    have ih := ce_desc m a j (by omega)
    have hj : (j : ℚ) + 2 ≤ m := by exact_mod_cast (by omega : j + 2 ≤ m)
    have hj0 : (0 : ℚ) ≤ j := by positivity
    have d1 : 1 - (m : ℚ) + j ≠ 0 := by intro h; linarith
    have d2 : (j : ℚ) - m ≠ 0 := by intro h; linarith
    have d3 : (j : ℚ) - 2 * m ≠ 0 := by intro h; linarith
    have d4 : (j : ℚ) + 1 ≠ 0 := by positivity
    have hd : ((2 * m).descFactorial (2 * (j + 1)) : ℚ)
        = (2 * (m : ℚ) - 2 * j - 1) * (2 * (m : ℚ) - 2 * j) * ((2 * m).descFactorial (2 * j) : ℚ) := by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.descFactorial_succ, Nat.descFactorial_succ]
      push_cast [Nat.cast_sub (show 2 * j + 1 ≤ 2 * m by omega), Nat.cast_sub (show 2 * j ≤ 2 * m by omega)]
      ring
    rw [hd]
    simp only [ce, Bali.RS.s]
    have e : ce m a j * (((j : ℚ) - a) * ((a : ℚ) - 2 * m + j) / ((1 - (m : ℚ) + j) * ((j : ℚ) - m) * ((j : ℚ) - 2 * m) * ((j : ℚ) + 1)))
          * ((2 * (m : ℚ) - 2 * j - 1) * (2 * (m : ℚ) - 2 * j) * ((2 * m).descFactorial (2 * j) : ℚ))
        = (ce m a j * ((2 * m).descFactorial (2 * j) : ℚ)) * (4 * (((j : ℚ) - a) * ((a : ℚ) - 2 * m + j) * (1 / 2 - (m : ℚ) + j)
            / ((1 - (m : ℚ) + j) * ((j : ℚ) - 2 * m) * ((j : ℚ) + 1)))) := by
      field_simp
      ring
    rw [e, ih]; ring

/-- `Σ_x C(n,x) R_a(x) = 2ⁿ Sx(a)`. -/
theorem RE_total (m a : ℕ) (ha : a < m) :
    ∑ x ∈ range (2 * m + 1), ((2 * m).choose x : ℚ) * RE m a (x : ℚ) = 2 ^ (2 * m) * Bali.RS.Sx m a := by
  simp only [RE, mul_sum]
  rw [sum_comm, Bali.RS.Sx, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < m := by have := mem_range.1 hj; omega
  have e : ∑ x ∈ range (2 * m + 1), ((2 * m).choose x : ℚ) * (ce m a j * phi (2 * (m : ℚ)) j (x : ℚ))
      = ce m a j * ∑ x ∈ range (2 * m + 1), ((2 * m).choose x : ℚ) * phi (2 * (m : ℚ)) j (x : ℚ) := by
    rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  rw [e, sum_phi m j hj'.le, ← mul_assoc, ce_desc m a j hj']
  have hp : (2 : ℚ) ^ (2 * m) = 4 ^ j * 2 ^ (2 * m - 2 * j) := by
    rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1; omega
  rw [hp]; ring

end Bali.RE

#print axioms Bali.RE.RE_centre
#print axioms Bali.RE.RE_total
