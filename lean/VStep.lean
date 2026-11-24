import P699.VEvenFull
import P699.ConjB

/-!
# Even `n`: the step `V_{2k} → V_{2k+2}` (Bali lab, 2026-11-02)
`-co(2k) co(2k+1) V_{2k+2} = ⟨e_{2k},e_{2k+1}⟩ V_{2k}`, with `co s` the leading coefficient of the slot `s`.
-/

open Finset Polynomial Matrix

namespace Bali.VE
open Bali.EvenPsi Bali.Chr Bali.Skew Bali.VG Bali.PfP Bali.VB Bali.GA

variable {K : ℕ}

lemma coeff_comp_Lt (P : ℚ[X]) (s : ℕ) (hP : P.natDegree ≤ s) :
    (P.comp (Lt K)).coeff s = P.coeff s * (1 / 4 : ℚ) ^ s := by
  have hLd : (Lt K).natDegree = 1 := by
    unfold Lt
    rw [natDegree_C_mul (by norm_num), natDegree_X_sub_C]
  have hLl : (Lt K).leadingCoeff = 1 / 4 := by
    unfold Lt
    rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X_sub_C, mul_one]
  rcases Nat.lt_or_ge P.natDegree s with h | h
  · rw [coeff_eq_zero_of_natDegree_lt h, zero_mul]
    apply coeff_eq_zero_of_natDegree_lt
    calc (P.comp (Lt K)).natDegree ≤ P.natDegree * (Lt K).natDegree := natDegree_comp_le
      _ = P.natDegree := by rw [hLd, mul_one]
      _ < s := h
  · have he : P.natDegree = s := by omega
    have := coeff_comp_degree_mul_degree (p := P) (q := Lt K) (by rw [hLd]; norm_num)
    rw [hLd, mul_one, hLl, he] at this
    rw [this, leadingCoeff, he]

/-- the leading coefficient of the slot `s`. -/
noncomputable def co (K s : ℕ) : ℚ := (Hc K s).coeff s * (1 / 4 : ℚ) ^ s

lemma Gp_coeff (k : ℕ) (a : Fin k × Fin 2) : (Gp K k a).coeff (eι k a : ℕ) = co K (eι k a : ℕ) := by
  obtain ⟨i, x⟩ := a
  rw [eι_val]
  unfold Gp co
  rcases fin2_cases x with rfl | rfl
  · simp only [Fin.val_zero, if_true, add_zero]
    exact coeff_comp_Lt _ _ (Hc_le _)
  · simp only [Fin.val_one, one_ne_zero, if_false]
    rw [coeff_comp_Lt]
    · rw [coeff_sub, coeff_C_mul, coeff_eq_zero_of_natDegree_lt (p := Hc K (2 * (i : ℕ))) (by
        have := Hc_le (K := K) (2 * (i : ℕ)); omega), mul_zero, sub_zero]
    · exact (natDegree_sub_le _ _).trans (max_le (Hc_le _) ((natDegree_C_mul_le _ _).trans ((Hc_le _).trans (by omega))))

lemma prod_co (k : ℕ) : ∏ a, (Gp K k a).coeff (eι k a : ℕ) = ∏ s ∈ range (2 * k), co K s := by
  rw [prod_congr rfl fun a _ => Gp_coeff k a,
    (eι k).prod_comp (fun q : Fin (2 * k) => co K (q : ℕ))]
  exact Fin.prod_univ_eq_prod_range (co K) (2 * k)

lemma co_ne (hK : 1 ≤ K) (s : ℕ) (hs : s < K + 1) : co K s ≠ 0 := by
  unfold co
  refine mul_ne_zero ?_ (by positivity)
  rcases s with _ | s
  · simp [Hc]
  · simp only [Hc, Nk, coeff_sub, coeff_C_mul]
    rw [coeff_eq_zero_of_natDegree_lt (p := RPE (K + 1) s) (by have := RPE_le (K + 1) s; omega), mul_zero, sub_zero,
      Bali.RE.RE_centre _ _ (by omega), RPE_coeff]
    exact mul_ne_zero (Bali.TN.F_ne _ s (by omega))
      (mul_ne_zero (Bali.Chr.ce_ne _ _ (by omega) _ le_rfl) (pow_ne_zero _ (by norm_num)))

/-- `V_{2k}` for even `n`. -/
noncomputable def VE (K k : ℕ) : ℚ := VBvol (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) (2 * k)

/-- **The step.** -/
theorem V_step (hK : 2 ≤ K) (k : ℕ) (hk : 2 * (k + 1) ≤ K + 1) :
    -(co K (2 * k) * co K (2 * k + 1)) * VE K (k + 1)
      = skew (e K (2 * k)) (e K (2 * k + 1)) * VE K k := by
  have h1 := V_even_full hK k (by omega)
  have h2 := V_even_full hK (k + 1) hk
  rw [Fin.prod_univ_castSucc] at h2
  simp only [Fin.val_castSucc, Fin.val_last] at h2
  rw [← h1, prod_co, prod_co, Bali.ConjB.sgn_range, Bali.ConjB.sgn_range,
    show 2 * (k + 1) = 2 * k + 1 + 1 by ring, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ] at h2
  have p0 : (-1 : ℚ) ^ (2 * k) = 1 := by rw [pow_mul]; simp
  have p1 : (-1 : ℚ) ^ (2 * k + 1) = -1 := by rw [pow_succ, p0]; ring
  rw [p0, p1] at h2
  have hP : ∏ s ∈ range (2 * k), co K s ≠ 0 := prod_ne_zero_iff.2 fun s hs =>
    co_ne (by omega) s (by have := mem_range.1 hs; omega)
  have hS : ∏ x ∈ range (2 * k), (-1 : ℚ) ^ x ≠ 0 := prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ (mul_ne_zero hP hS)
  unfold VE
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
  linear_combination h2

end Bali.VE

#print axioms Bali.VE.V_step
