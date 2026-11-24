import P699.EvenLead

/-!
# Even `n = 2m`: `ℓ_a` in closed form and the norm of `p_b` in terms of `h_b` (Bali lab, 2026-11-02)
-/

open Finset Polynomial

namespace Bali.Chr
open Bali.Racah Bali.RE Bali.REO

/-! ## the norm -/

/-- pairing with `R_b` sees only the top coefficient. -/
lemma ipR_lead (M b : ℕ) (hb : b < M + 1) (Q : ℚ[X]) (hQ : Q.natDegree ≤ b) :
    (RPE (M + 1) b).coeff b * ∑ x ∈ range (M + 1), wE (M + 1) x * RE (M + 1) b x *
        Q.eval ((x : ℚ) * ((x : ℚ) - 2 * ((M + 1 : ℕ) : ℚ)))
      = Q.coeff b * hE (M + 1) b := by
  set S := RPE (M + 1) b with hS
  have hl : S.coeff b ≠ 0 := by
    rw [hS, RPE_coeff]; exact mul_ne_zero (ce_ne _ b hb b le_rfl) (pow_ne_zero _ (by norm_num))
  set α := Q.coeff b / S.coeff b with hα
  set R := Q - C α * S with hR
  have hRle : R.natDegree ≤ b :=
    (natDegree_sub_le _ _).trans (max_le hQ ((natDegree_C_mul_le _ _).trans (RPE_le _ _)))
  have hRc : R.coeff b = 0 := by
    simp only [hR, coeff_sub, coeff_C_mul, hα]; field_simp; ring
  have hR0 : ∑ x ∈ range (M + 1), wE (M + 1) x * RE (M + 1) b x *
      R.eval ((x : ℚ) * ((x : ℚ) - 2 * ((M + 1 : ℕ) : ℚ))) = 0 := by
    by_cases h0 : R = 0
    · simp [h0]
    · have hlt : R.natDegree < b := by
        rcases Nat.lt_or_ge R.natDegree b with h | h
        · exact h
        · have he : R.natDegree = b := by omega
          rw [← he] at hRc
          exact absurd (leadingCoeff_eq_zero.1 hRc) h0
      exact orth_polyE M b hb _ R rfl hlt
  have hsum : ∑ x ∈ range (M + 1), wE (M + 1) x * RE (M + 1) b x *
      Q.eval ((x : ℚ) * ((x : ℚ) - 2 * ((M + 1 : ℕ) : ℚ))) = α * hE (M + 1) b := by
    have : ∀ x ∈ range (M + 1), wE (M + 1) x * RE (M + 1) b x *
        Q.eval ((x : ℚ) * ((x : ℚ) - 2 * ((M + 1 : ℕ) : ℚ)))
        = wE (M + 1) x * RE (M + 1) b x * R.eval ((x : ℚ) * ((x : ℚ) - 2 * ((M + 1 : ℕ) : ℚ)))
          + α * (wE (M + 1) x * Bali.REO.RR (M + 1) b x * Bali.REO.RR (M + 1) b x) := by
      intro x _
      simp only [hR, eval_sub, eval_mul, eval_C, hS, RPE_eval, Bali.REO.RR]
      ring
    rw [sum_congr rfl this, sum_add_distrib, hR0, zero_add, ← mul_sum]
    rfl
  rw [hsum, hα]; field_simp

/-- **the norm of `p_b`.** `ℓ_b ⟨p_b,p_b⟩_W = -4 R_{b+1}(m) · lc(p_b) · h_b`. -/
theorem ipW_pK (K b : ℕ) (hb : b + 1 < K + 1) :
    (RPE (K + 1) b).coeff b * Bali.EvenPsi.ipW K (pK (K + 1) b) (pK (K + 1) b)
      = -4 * RE (K + 1) (b + 1) ((K + 1 : ℕ) : ℚ) * (pK (K + 1) b).coeff b * hE (K + 1) b := by
  have e1 := orth_polyE K (b + 1) hb _ (pK (K + 1) b) rfl (by have := pK_le (K + 1) b; omega)
  have e2 := ipR_lead K b (by omega) (pK (K + 1) b) (pK_le _ _)
  have key : Bali.EvenPsi.ipW K (pK (K + 1) b) (pK (K + 1) b)
      = 4 * RE (K + 1) b ((K + 1 : ℕ) : ℚ) * ∑ x ∈ range (K + 1), wE (K + 1) x * RE (K + 1) (b + 1) x *
            (pK (K + 1) b).eval ((x : ℚ) * ((x : ℚ) - 2 * ((K + 1 : ℕ) : ℚ)))
        - 4 * RE (K + 1) (b + 1) ((K + 1 : ℕ) : ℚ) * ∑ x ∈ range (K + 1), wE (K + 1) x * RE (K + 1) b x *
            (pK (K + 1) b).eval ((x : ℚ) * ((x : ℚ) - 2 * ((K + 1 : ℕ) : ℚ))) := by
    unfold Bali.EvenPsi.ipW
    rw [Y_pK, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [lam_eval, nQ_eq]
    simp only [Nk, eval_mul, eval_C, eval_sub, RPE_eval, wE]
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring]
    ring
  rw [key, e1]
  linear_combination (-4 * RE (K + 1) (b + 1) ((K + 1 : ℕ) : ℚ)) * e2

/-! ## `ℓ_a` closed -/

lemma fallE (N : ℕ) : ∀ a, a ≤ N →
    ∏ i ∈ range a, ((i : ℚ) - N) = (-1) ^ a * ((N.factorial : ℚ) / (N - a).factorial)
  | 0, _ => by simp [Nat.factorial_ne_zero]
  | a + 1, ha => by
    rw [prod_range_succ, fallE N a (by omega)]
    obtain ⟨r, rfl⟩ : ∃ r, N = a + 1 + r := ⟨N - (a + 1), by omega⟩
    rw [show a + 1 + r - a = r + 1 by omega, show a + 1 + r - (a + 1) = r by omega, Nat.factorial_succ]
    push_cast
    field_simp
    ring

lemma ce_prod (m a : ℕ) : ∀ j, ce m a j = ∏ i ∈ range j, (((i : ℚ) - a) * ((a : ℚ) - 2 * m + i)
      / ((1 - (m : ℚ) + i) * ((i : ℚ) - m) * ((i : ℚ) - 2 * m) * ((i : ℚ) + 1)))
  | 0 => by simp [ce]
  | j + 1 => by rw [prod_range_succ, ← ce_prod m a j]; rfl

/-- **`ℓ_a`**, `n = 2(M+1)`, `a ≤ M`. -/
theorem ell_closedE (M a : ℕ) (ha : a ≤ M) :
    (RPE (M + 1) a).coeff a
      = ((2 * (M + 1) - a).factorial : ℚ) ^ 2 * ((M - a).factorial : ℚ) * ((M + 1 - a).factorial : ℚ)
        / (((2 * (M + 1) - 2 * a).factorial : ℚ) * ((2 * (M + 1)).factorial : ℚ) * (M.factorial : ℚ) * ((M + 1).factorial : ℚ)) := by
  rw [RPE_coeff, ce_prod]
  have e : ∀ i ∈ range a,
      (((i : ℚ) - a) * ((a : ℚ) - 2 * ((M + 1 : ℕ) : ℚ) + i)
        / ((1 - ((M + 1 : ℕ) : ℚ) + i) * ((i : ℚ) - ((M + 1 : ℕ) : ℚ)) * ((i : ℚ) - 2 * ((M + 1 : ℕ) : ℚ)) * ((i : ℚ) + 1)))
      = ((i : ℚ) - (a : ℕ)) * ((i : ℚ) - ((2 * (M + 1) - a : ℕ) : ℚ)) /
        (((i : ℚ) - (M : ℕ)) * ((i : ℚ) - ((M + 1 : ℕ) : ℚ)) * ((i : ℚ) - ((2 * (M + 1) : ℕ) : ℚ)) * (((i + 1 : ℕ) : ℚ))) := by
    intro i _
    rw [Nat.cast_sub (by omega)]
    push_cast
    congr 1 <;> ring
  rw [prod_congr rfl e, prod_div_distrib, prod_mul_distrib, prod_mul_distrib, prod_mul_distrib, prod_mul_distrib,
    fallE a a le_rfl, fallE (2 * (M + 1) - a) a (by omega), fallE M a ha, fallE (M + 1) a (by omega),
    fallE (2 * (M + 1)) a (by omega), ← Nat.cast_prod, prod_range_add_one_eq_factorial, Nat.sub_self, Nat.factorial_zero,
    show 2 * (M + 1) - a - a = 2 * (M + 1) - 2 * a by omega]
  have h1 : ((2 * (M + 1) - 2 * a).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((M - a).factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((M + 1 - a).factorial : ℚ) ≠ 0 := by positivity
  have h4 : ((2 * (M + 1) - a).factorial : ℚ) ≠ 0 := by positivity
  have h5 : (a.factorial : ℚ) ≠ 0 := by positivity
  have h6 : (M.factorial : ℚ) ≠ 0 := by positivity
  have h7 : ((M + 1).factorial : ℚ) ≠ 0 := by positivity
  have h8 : ((2 * (M + 1)).factorial : ℚ) ≠ 0 := by positivity
  have h9 : ((-1 : ℚ) ^ a) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

end Bali.Chr

#print axioms Bali.Chr.ipW_pK
#print axioms Bali.Chr.ell_closedE
