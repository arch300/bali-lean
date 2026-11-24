import Mathlib

/-!
# Coefficients of shifted polynomials (Bali lab, 2026-11-01)
Tool for the leading coefficient of `Q` in Lemma ψ.
-/

open Polynomial Finset

namespace Bali.LeadQ

/-- `(q(X + r)).coeff j = Σ_k q_k r^{k-j} C(k,j)`. -/
lemma coeff_comp_X_add_C (q : ℚ[X]) (r : ℚ) (D : ℕ) (hq : q.natDegree < D) (j : ℕ) :
    (q.comp (X + C r)).coeff j = ∑ k ∈ range D, q.coeff k * (r ^ (k - j) * (k.choose j : ℚ)) := by
  conv_lhs => rw [q.as_sum_range' D hq]
  rw [Polynomial.sum_comp, finsetSum_coeff]
  refine sum_congr rfl fun k _ => ?_
  rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, coeff_C_mul, coeff_X_add_C_pow]

/-- top two coefficients of `q(X + r)` for `deg q ≤ D` (`1 ≤ D`):
`coeff D = q_D`, `coeff (D-1) = q_{D-1} + D r q_D`. -/
lemma top_coeffs (q : ℚ[X]) (r : ℚ) (D : ℕ) (hD : 1 ≤ D) (hq : q.natDegree ≤ D) :
    (q.comp (X + C r)).coeff D = q.coeff D ∧
    (q.comp (X + C r)).coeff (D - 1) = q.coeff (D - 1) + D * r * q.coeff D := by
  have hq' : q.natDegree < D + 1 := by omega
  constructor
  · rw [coeff_comp_X_add_C q r (D + 1) hq', sum_range_succ, sum_eq_zero (fun k hk => by
      have := mem_range.1 hk; rw [Nat.choose_eq_zero_of_lt this]; simp)]
    simp
  · obtain ⟨E, rfl⟩ : ∃ E, D = E + 1 := ⟨D - 1, by omega⟩
    rw [coeff_comp_X_add_C q r (E + 1 + 1) hq', sum_range_succ, sum_range_succ,
      sum_eq_zero (fun k hk => by
        have := mem_range.1 hk; rw [Nat.choose_eq_zero_of_lt (by omega : k < E + 1 - 1)]; simp)]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one,
      zero_add, show E + 1 - E = 1 by omega, pow_one, Nat.choose_succ_self_right]
    push_cast; ring


lemma coeff_comp_neg_X (p : ℚ[X]) (k : ℕ) : (p.comp (-X)).coeff k = (-1) ^ k * p.coeff k := by
  conv_lhs => rw [p.as_sum_range' (p.natDegree + 1) (Nat.lt_succ_self _)]
  rw [Polynomial.sum_comp, finsetSum_coeff]
  have hterm : ∀ x : ℕ, (((monomial x) (p.coeff x)).comp (-X)).coeff k
      = if k = x then (-1) ^ k * p.coeff k else 0 := by
    intro x
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, neg_pow,
      show (C (p.coeff x) * ((-1 : ℚ[X]) ^ x * X ^ x)) = C (p.coeff x * (-1) ^ x) * X ^ x by
        rw [C_mul, C_pow, C_neg, C_1]; ring,
      coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; ring
    · rfl
  rw [sum_congr rfl fun x _ => hterm x, sum_ite_eq]
  split_ifs with h
  · rfl
  · simp only [mem_range, not_lt] at h
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]; ring

/-- **second coefficient of an antisymmetric polynomial.**  If `q(m - x) = -q(x)` and `deg q ≤ 2d - 1`, `1 ≤ d`,
then `q_{2d-2} = -(2d-1)(m/2) q_{2d-1}`. -/
lemma second_coeff_antisymm (q : ℚ[X]) (m : ℚ) (d : ℕ) (hd : 1 ≤ d) (hq : q.natDegree ≤ 2 * d - 1)
    (hanti : q.comp (C m - X) = -q) :
    q.coeff (2 * d - 2) = -((2 * d - 1 : ℕ) : ℚ) * (m / 2) * q.coeff (2 * d - 1) := by
  set p := q.comp (X + C (m / 2)) with hp
  have hodd : p.comp (-X) = -p := by
    rw [hp, comp_assoc]
    have : (X + C (m / 2) : ℚ[X]).comp (-X) = (C m - X).comp (X + C (m / 2)) := by
      simp only [add_comp, X_comp, C_comp, sub_comp]
      rw [show (C m : ℚ[X]) = C (m / 2) + C (m / 2) by rw [← C_add]; ring_nf]; ring
    rw [this, ← comp_assoc, hanti, neg_comp]
  have hzero : p.coeff (2 * d - 2) = 0 := by
    have := congrArg (fun r => r.coeff (2 * d - 2)) hodd
    simp only [coeff_comp_neg_X, coeff_neg] at this
    rw [show 2 * d - 2 = 2 * (d - 1) by omega, pow_mul] at this
    norm_num at this
    rw [show 2 * d - 2 = 2 * (d - 1) by omega]
    linarith
  have ht := (top_coeffs q (m / 2) (2 * d - 1) (by omega) hq).2
  rw [show 2 * d - 1 - 1 = 2 * d - 2 by omega, ← hp, hzero] at ht
  linear_combination -ht

end Bali.LeadQ
#print axioms Bali.LeadQ.top_coeffs
#print axioms Bali.LeadQ.second_coeff_antisymm
