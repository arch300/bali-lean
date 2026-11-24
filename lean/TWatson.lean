import P699.RacahOrth
import P699.Watson

/-!
# Step (d): `T(R_b) = 2^n S(b)`, hence `T(R_odd) = 0` (Bali lab, 2026-11-01)
-/

open Finset

namespace Bali.TW
open Bali.Racah

lemma P_neg_nat (x : ℕ) : ∀ j : ℕ, P (-(x : ℚ)) j = (-1) ^ j * (x.descFactorial j : ℚ)
  | 0 => by simp [P]
  | j + 1 => by
    rw [P, P_neg_nat x j, Nat.descFactorial_succ]
    rcases le_or_gt j x with h | h
    · push_cast [Nat.cast_sub h]; ring
    · rw [Nat.descFactorial_eq_zero_iff_lt.2 h]; simp

/-- `C(n,x) x^{↓j} (n-x)^{↓j} = n^{↓2j} C(n-2j, x-j)` (zero outside `j ≤ x ≤ n-j`). -/
lemma choose_desc (n x j : ℕ) (h1 : j ≤ x) (h2 : x + j ≤ n) :
    n.choose x * x.descFactorial j * (n - x).descFactorial j
      = n.descFactorial (2 * j) * (n - 2 * j).choose (x - j) := by
  have hd : n.descFactorial (2 * j) = (n - j).descFactorial j * n.descFactorial j := by
    have := Nat.descFactorial_mul_descFactorial (n := n) (k := j) (m := 2 * j) (by omega)
    rw [show 2 * j - j = j by omega] at this; exact this.symm
  rw [hd, Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    show 2 * j = j + j by ring]
  have e1 : n.choose x * x.choose j = n.choose j * (n - j).choose (x - j) := Nat.choose_mul h1
  have e2 : (n - j).choose (x - j) * (n - x).choose j = (n - j).choose j * (n - j - j).choose (x - j) := by
    have := Nat.choose_mul (n := n - j) (k := (n - j) - (x - j)) (s := j) (by omega)
    rw [Nat.choose_symm (by omega : x - j ≤ n - j)] at this
    rw [show n - x = n - j - (x - j) by omega, this,
      show n - j - (x - j) - j = (n - j - j) - (x - j) by omega, Nat.choose_symm (by omega)]
  calc n.choose x * (j.factorial * x.choose j) * (j.factorial * (n - x).choose j)
      = j.factorial * j.factorial * ((n.choose x * x.choose j) * (n - x).choose j) := by ring
    _ = j.factorial * j.factorial * (n.choose j * ((n - j).choose (x - j) * (n - x).choose j)) := by rw [e1]; ring
    _ = _ := by rw [e2, show n - j - j = n - (j + j) by omega]; ring


/-- `Σ_x C(n,x) x^{↓j} (n-x)^{↓j} = n^{↓2j} 2^{n-2j}` for `2j ≤ n`. -/
theorem sum_choose_desc (n j : ℕ) (hj : 2 * j ≤ n) :
    ∑ x ∈ range (n + 1), n.choose x * x.descFactorial j * (n - x).descFactorial j
      = n.descFactorial (2 * j) * 2 ^ (n - 2 * j) := by
  set f := fun x => n.choose x * x.descFactorial j * (n - x).descFactorial j with hf
  rw [range_eq_Ico, ← sum_Ico_consecutive f (Nat.zero_le (n - j + 1)) (by omega : n - j + 1 ≤ n + 1),
    ← sum_Ico_consecutive f (Nat.zero_le j) (by omega : j ≤ n - j + 1)]
  have h0 : ∑ x ∈ Ico 0 j, f x = 0 := sum_eq_zero fun x hx => by
    simp only [mem_Ico] at hx; simp [hf, Nat.descFactorial_eq_zero_iff_lt.2 hx.2]
  have h2 : ∑ x ∈ Ico (n - j + 1) (n + 1), f x = 0 := sum_eq_zero fun x hx => by
    simp only [mem_Ico] at hx
    simp [hf, Nat.descFactorial_eq_zero_iff_lt.2 (by omega : n - x < j)]
  rw [h0, h2, zero_add, add_zero, sum_Ico_eq_sum_range]
  rw [show n - j + 1 - j = n - 2 * j + 1 by omega]
  rw [show ∑ y ∈ range (n - 2 * j + 1), f (j + y) = ∑ y ∈ range (n - 2 * j + 1), n.descFactorial (2 * j) * (n - 2 * j).choose y
      from sum_congr rfl fun y hy => by
        have := mem_range.1 hy
        rw [hf]; simp only
        rw [choose_desc n (j + y) j (by omega) (by omega), Nat.add_sub_cancel_left]]
  rw [← mul_sum, Nat.sum_range_choose]


/-- `φ_j(x) = x^{↓j} (n-x)^{↓j}` at integers `x ≤ n`. -/
lemma phi_nat (n x j : ℕ) (hx : x ≤ n) :
    phi (n : ℚ) j (x : ℚ) = (x.descFactorial j : ℚ) * ((n - x).descFactorial j : ℚ) := by
  rw [phi, P_neg_nat, show (x : ℚ) - n = -((n - x : ℕ) : ℚ) by push_cast [Nat.cast_sub hx]; ring, P_neg_nat]
  rw [← mul_assoc, mul_comm ((-1 : ℚ) ^ j), mul_assoc, mul_assoc, ← mul_assoc ((-1 : ℚ) ^ j), ← pow_add,
    ← two_mul, pow_mul]
  norm_num
  try ring

/-- term by term: `c_j n^{↓2j} 2^{n-2j} = 2^n F(b, j)`. -/
lemma coef_eq (H b : ℕ) (hb : b ≤ H) : ∀ j, j ≤ b →
    c ((2 * H + 1 : ℕ) : ℚ) b j * ((2 * H + 1).descFactorial (2 * j) : ℚ) * (2 : ℚ) ^ (2 * H + 1 - 2 * j)
      = (2 : ℚ) ^ (2 * H + 1) * Bali.Watson.F b ((2 * H + 1 : ℕ) : ℚ) j
  | 0, _ => by simp [c, Bali.Watson.F]
  | j + 1, hj => by
    have ih := coef_eq H b hb j (by omega)
    have hjH : (j : ℚ) + 1 ≤ H := by exact_mod_cast (by omega : j + 1 ≤ H)
    simp only [c, Bali.Watson.F, Bali.Watson.num, Bali.Watson.den]
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.descFactorial_succ, Nat.descFactorial_succ,
      show 2 * H + 1 - (2 * j + 1 + 1) = 2 * H + 1 - 2 * j - 2 by omega]
    have hpow : (2 : ℚ) ^ (2 * H + 1 - 2 * j) = 4 * (2 : ℚ) ^ (2 * H + 1 - 2 * j - 2) := by
      have e : 2 * H + 1 - 2 * j = (2 * H + 1 - 2 * j - 2) + 2 := by omega
      conv_lhs => rw [e]
      rw [pow_add]; ring
    rw [hpow] at ih
    push_cast [Nat.cast_sub (by omega : 2 * j + 1 ≤ 2 * H + 1), Nat.cast_sub (by omega : 2 * j ≤ 2 * H + 1),
      Nat.cast_sub (by omega : 2 * j ≤ 2 * H)] at ih ⊢
    have d1 : ((1 - (2 * (H : ℚ) + 1)) / 2 + j) ≠ 0 := by intro h; linarith
    have d2 : (-(2 * (H : ℚ) + 1) + j) ≠ 0 := by intro h; linarith
    have d3 : ((j : ℚ) + 1) ≠ 0 := by positivity
    rw [show ∀ A B : ℚ, (2 : ℚ) ^ (2 * H + 1) * (A * B) = ((2 : ℚ) ^ (2 * H + 1) * A) * B from
      fun A B => by ring, ← ih]
    rw [show ((1 - (2 * (H : ℚ) + 1)) / 2 + j) = (j - H) by ring,
      show (-(2 * (H : ℚ) + 1) + j) = (j - 2 * H - 1) by ring]
    have e1 : (j : ℚ) - H ≠ 0 := by intro h; linarith
    have e2 : (j : ℚ) - 2 * H - 1 ≠ 0 := by intro h; linarith
    field_simp
    ring

/-- **`T(R_b) = 2^n S(b)`** for `n = 2H+1`, `b ≤ H`. -/
theorem T_R (H b : ℕ) (hb : b ≤ H) :
    ∑ x ∈ range (2 * H + 1 + 1), ((2 * H + 1).choose x : ℚ) * Rq ((2 * H + 1 : ℕ) : ℚ) b x
      = (2 : ℚ) ^ (2 * H + 1) * Bali.Watson.S b ((2 * H + 1 : ℕ) : ℚ) := by
  simp only [Rq, mul_sum]
  rw [sum_comm, Bali.Watson.S, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hjb : j ≤ b := by have := mem_range.1 hj; omega
  rw [← coef_eq H b hb j hjb]
  have hsum := sum_choose_desc (2 * H + 1) j (by omega)
  have hcast := congrArg (fun t : ℕ => (t : ℚ)) hsum
  push_cast at hcast
  rw [show ∑ x ∈ range (2 * H + 1 + 1), ((2 * H + 1).choose x : ℚ) * (c ((2 * H + 1 : ℕ) : ℚ) b j * phi ((2 * H + 1 : ℕ) : ℚ) j x)
      = c ((2 * H + 1 : ℕ) : ℚ) b j * ∑ x ∈ range (2 * H + 1 + 1),
          ((2 * H + 1).choose x : ℚ) * (x.descFactorial j : ℚ) * ((2 * H + 1 - x).descFactorial j : ℚ) from by
    rw [mul_sum]; refine sum_congr rfl fun x hx => ?_
    rw [phi_nat (2 * H + 1) x j (by have := mem_range.1 hx; omega)]; ring]
  rw [hcast]; ring


/-- **`T(R_b) = 0` for odd `b ≤ H`.** -/
theorem T_R_odd (H k : ℕ) (hk : 2 * k + 1 ≤ H) :
    ∑ x ∈ range (2 * H + 1 + 1), ((2 * H + 1).choose x : ℚ) * Rq ((2 * H + 1 : ℕ) : ℚ) (2 * k + 1) x = 0 := by
  rw [T_R H (2 * k + 1) hk]
  have := Bali.Watson.S_odd_zero H k hk
  push_cast
  rw [this, mul_zero]

end Bali.TW

#print axioms Bali.TW.choose_desc
#print axioms Bali.TW.sum_choose_desc
#print axioms Bali.TW.T_R
#print axioms Bali.TW.T_R_odd
