import P699.PsiPoly
import P699.LeadQ

/-!
# The leading coefficient of `Q` in Lemma ψ: `Q_{d-1} = γ (n + 1 - 2d) / 4` (Bali lab, 2026-11-01)
-/

open Polynomial Finset

namespace Bali.LeadQ
open Bali Bali.Even Bali.Psi

lemma lam_pow_coeff (n : ℚ) (d : ℕ) (hd : 1 ≤ d) :
    ((lam n) ^ d).coeff (2 * d) = 1 ∧ ((lam n) ^ d).coeff (2 * d - 1) = -n * d := by
  have hl : (lam n) ^ d = X ^ d * (X + C (-n)) ^ d := by
    rw [lam, mul_pow, C_neg, ← sub_eq_add_neg]
  rw [hl, coeff_X_pow_mul', coeff_X_pow_mul', if_pos (by omega), if_pos (by omega),
    coeff_X_add_C_pow, coeff_X_add_C_pow, show 2 * d - d = d by omega, show 2 * d - 1 - d = d - 1 by omega,
    Nat.sub_self, Nat.choose_self, show d - (d - 1) = 1 by omega, Nat.choose_symm hd, Nat.choose_one_right]
  simp

/-- top two coefficients of `G(λ)` for `deg G ≤ d`. -/
lemma comp_lam_coeffs (n : ℚ) (G : ℚ[X]) (d : ℕ) (hd : 1 ≤ d) (hG : G.natDegree ≤ d) :
    (G.comp (lam n)).coeff (2 * d) = G.coeff d ∧
    (G.comp (lam n)).coeff (2 * d - 1) = -n * d * G.coeff d := by
  have hG' : G.natDegree < d + 1 := by omega
  have hexp : G.comp (lam n) = ∑ k ∈ range (d + 1), C (G.coeff k) * (lam n) ^ k := by
    conv_lhs => rw [G.as_sum_range' (d + 1) hG']
    rw [Polynomial.sum_comp]
    exact sum_congr rfl fun k _ => by rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp]
  have hlow : ∀ k ∈ range d, ∀ j, 2 * d - 1 ≤ j → (C (G.coeff k) * (lam n) ^ k).coeff j = 0 := by
    intro k hk j hj
    have := mem_range.1 hk
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (p := lam n ^ k) (by rw [natDegree_pow, lam_natDegree]; omega),
      mul_zero]
  rw [hexp, finsetSum_coeff, finsetSum_coeff, sum_range_succ, sum_range_succ,
    sum_eq_zero (fun k hk => hlow k hk _ (by omega)), sum_eq_zero (fun k hk => hlow k hk _ le_rfl),
    coeff_C_mul, coeff_C_mul, (lam_pow_coeff n d hd).1, (lam_pow_coeff n d hd).2]
  constructor <;> ring

/-- coefficients of `Q(λ)` at the top for `deg Q ≤ e`: `coeff (2e) = Q_e`, `coeff (2e+1) = 0`. -/
lemma comp_lam_top (n : ℚ) (Q : ℚ[X]) (e : ℕ) (hQ : Q.natDegree ≤ e) :
    (Q.comp (lam n)).coeff (2 * e) = Q.coeff e ∧ (Q.comp (lam n)).coeff (2 * e + 1) = 0 := by
  constructor
  · rcases Nat.eq_zero_or_pos e with rfl | he
    · rw [eq_C_of_natDegree_eq_zero (by omega : Q.natDegree = 0)]; simp
    · have := (comp_lam_coeffs n Q e he hQ).1; exact this
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt natDegree_comp_le
    rw [lam_natDegree]; nlinarith


/-- **Leading coefficient in Lemma ψ.**  The `Q` of `psi_poly` has `Q_{d-1} = γ (n + 1 - 2d) / 4`, `γ = G_d`. -/
theorem psi_lead (m d : ℕ) (hd1 : 1 ≤ d) (hdm : 2 * d ≤ m) (G : ℚ[X]) (hG : G.natDegree ≤ d)
    (htot : totL (m + 1) (G.comp (lam ((m : ℚ) + 1))) = 0) :
    ∃ Q : ℚ[X], Q.natDegree ≤ d - 1 ∧
      (∃ q : ℚ[X], phiQ (m + 1) q = G.comp (lam ((m : ℚ) + 1)) ∧
        C 2 * (C ((m : ℚ) + 1) - X) * q - G.comp (lam ((m : ℚ) + 1))
          = (C ((m : ℚ) + 1) - C 2 * X) * Q.comp (lam ((m : ℚ) + 1))) ∧
      Q.coeff (d - 1) = G.coeff d * (((m : ℚ) + 1) + 1 - 2 * d) / 4 := by
  obtain ⟨q, hphi, hqdeg, hanti, Q, hQdeg, hN⟩ := psi_poly m d hd1 hdm G hG htot
  refine ⟨Q, hQdeg, ⟨q, hphi, hN⟩, ?_⟩
  set n : ℚ := (m : ℚ) + 1 with hn
  set γ := G.coeff d
  have hgc := comp_lam_coeffs n G d hd1 hG
  -- (a) q_{2d-1} = -γ/2 from the coefficient 2d of the recurrence
  have hrecP : C n * q - X * q - X * q.comp (X + C (-1)) = G.comp (lam n) := by
    rw [← hphi]; simp [phiQ, hn, sub_mul, C_neg]; ring
  have hq2d : q.coeff (2 * d) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have htopc := (top_coeffs q (-1) (2 * d - 1) (by omega) hqdeg).1
  have ha : q.coeff (2 * d - 1) = -γ / 2 := by
    have := congrArg (fun p => p.coeff (2 * d)) hrecP
    simp only [coeff_sub, coeff_C_mul] at this
    rw [show 2 * d = (2 * d - 1) + 1 by omega, coeff_X_mul, coeff_X_mul] at this
    rw [show 2 * d - 1 + 1 = 2 * d by omega, hq2d, htopc, hgc.1] at this
    linarith
  -- (b) the second coefficient from antisymmetry
  have hb := second_coeff_antisymm q m d hd1 hqdeg hanti
  -- (c) coefficient 2d-1 of the factorisation
  have hQt := comp_lam_top n Q (d - 1) hQdeg
  have hc := congrArg (fun p => p.coeff (2 * d - 1)) hN
  simp only [coeff_sub, mul_sub, sub_mul] at hc
  rw [show C 2 * C n * q = C (2 * n) * q by rw [C_mul], show C 2 * X * q = X * (C 2 * q) by ring,
    show C 2 * X * Q.comp (lam n) = X * (C 2 * Q.comp (lam n)) by ring,
    show 2 * d - 1 = (2 * d - 2) + 1 by omega, coeff_X_mul, coeff_X_mul] at hc
  simp only [coeff_C_mul] at hc
  rw [show 2 * d - 2 + 1 = 2 * (d - 1) + 1 by omega, show 2 * d - 2 = 2 * (d - 1) by omega, hQt.1, hQt.2,
    show 2 * (d - 1) + 1 = 2 * d - 1 by omega, show 2 * (d - 1) = 2 * d - 2 by omega, ha, hb, ha, hgc.2] at hc
  push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * d)] at hc
  have hγ : γ = G.coeff d := rfl
  rw [← hγ] at hc
  rw [hn] at hc ⊢
  linear_combination (1 / 2 : ℚ) * hc

end Bali.LeadQ

#print axioms Bali.LeadQ.comp_lam_coeffs
#print axioms Bali.LeadQ.psi_lead
