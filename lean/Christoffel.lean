import P699.RacahEOrth
import P699.EvenPsi
import P699.PhiLambda

/-!
# Even `n = 2m`: the Christoffel family at the centre, and (L1) for it (Bali lab, 2026-11-02)
`p_a = (R_a(m) R_{a+1} - R_{a+1}(m) R_a) / (λ - λ₀)`, `λ₀ = -m²`, so `y p_a = 4 (R_a(m) R_{a+1} - R_{a+1}(m) R_a)`.
-/

open Finset Polynomial

namespace Bali.Chr
open Bali.Racah Bali.RE Bali.REO

/-- `R_a` as a polynomial in `λ`. -/
noncomputable def RPE (m a : ℕ) : ℚ[X] := ∑ j ∈ range (a + 1), C (ce m a j) * PhiP (2 * (m : ℚ)) j

lemma RPE_eval (m a : ℕ) (y : ℚ) : (RPE m a).eval (y * (y - 2 * (m : ℚ))) = RE m a y := by
  rw [RPE, eval_finsetSum, RE]
  exact sum_congr rfl fun j _ => by rw [eval_mul, eval_C, PhiP_eval]

lemma ce_ne (m a : ℕ) (ha : a < m) : ∀ j, j ≤ a → ce m a j ≠ 0
  | 0, _ => by simp [ce]
  | j + 1, hj => by
    have ih := ce_ne m a ha j (by omega)
    simp only [ce]
    have hja : (j : ℚ) + 1 ≤ a := by exact_mod_cast hj
    have ham : (a : ℚ) + 1 ≤ m := by exact_mod_cast ha
    have h0 : (0 : ℚ) ≤ j := by positivity
    have h1 : (j : ℚ) - a ≠ 0 := by intro h; linarith
    have h2 : (a : ℚ) - 2 * m + j ≠ 0 := by intro h; linarith
    have h3 : 1 - (m : ℚ) + j ≠ 0 := by intro h; linarith
    have h4 : (j : ℚ) - m ≠ 0 := by intro h; linarith
    have h5 : (j : ℚ) - 2 * m ≠ 0 := by intro h; linarith
    have h6 : (j : ℚ) + 1 ≠ 0 := by positivity
    exact mul_ne_zero ih (div_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero (mul_ne_zero (mul_ne_zero h3 h4) h5) h6))

lemma RPE_le (m a : ℕ) : (RPE m a).natDegree ≤ a := by
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  have := mem_range.1 hj
  calc (C (ce m a j) * PhiP (2 * (m : ℚ)) j).natDegree ≤ (PhiP (2 * (m : ℚ)) j).natDegree := natDegree_C_mul_le _ _
    _ = j := PhiP_natDegree _ _
    _ ≤ a := by omega

/-- `R_a` has exact degree `a`; its coefficient at `λ^a` is `(-1)^a ce a`. -/
lemma RPE_coeff (m a : ℕ) : (RPE m a).coeff a = ce m a a * (-1) ^ a := by
  rw [RPE, sum_range_succ, coeff_add, coeff_C_mul, ← PhiP_leading (2 * (m : ℚ)) a, leadingCoeff, PhiP_natDegree]
  have : (∑ j ∈ range a, C (ce m a j) * PhiP (2 * (m : ℚ)) j).coeff a = 0 := by
    rw [finsetSum_coeff]
    refine sum_eq_zero fun j hj => ?_
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by rw [PhiP_natDegree]; exact mem_range.1 hj), mul_zero]
  rw [this, zero_add]

lemma RPE_natDegree (m a : ℕ) (ha : a < m) : (RPE m a).natDegree = a := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (RPE_le m a)
  rw [RPE_coeff]
  exact mul_ne_zero (ce_ne m a ha a le_rfl) (pow_ne_zero _ (by norm_num))

/-- orthogonality to lower degree. -/
theorem orth_polyE (M a : ℕ) (ha : a < M + 1) :
    ∀ k : ℕ, ∀ Q : ℚ[X], Q.natDegree = k → k < a →
      ∑ x ∈ range (M + 1), wE (M + 1) x * RE (M + 1) a x *
        Q.eval ((x : ℚ) * ((x : ℚ) - 2 * ((M + 1 : ℕ) : ℚ))) = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro Q hQk hka
  by_cases hQ0 : Q = 0
  · simp [hQ0]
  have hk : k < M + 1 := by omega
  set R := RPE (M + 1) k with hR
  have hRdeg : R.natDegree = k := RPE_natDegree _ k hk
  have hRlc : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 (fun h => by
    have hc := RPE_coeff (M + 1) k
    rw [← hR, h, coeff_zero] at hc
    exact mul_ne_zero (ce_ne _ k hk k le_rfl) (pow_ne_zero _ (by norm_num)) hc.symm)
  set α := Q.leadingCoeff / R.leadingCoeff with hα
  set Q' := Q - C α * R with hQ'
  have hsplit : ∀ x : ℚ, Q.eval x = Q'.eval x + α * R.eval x := by
    intro x; simp [hQ']
  have hR0 : ∑ x ∈ range (M + 1), wE (M + 1) x * RE (M + 1) a x *
      R.eval ((x : ℚ) * ((x : ℚ) - 2 * ((M + 1 : ℕ) : ℚ))) = 0 := by
    have := orth M a k ha hk (by omega)
    rw [← this]
    refine sum_congr rfl fun x _ => ?_
    rw [hR, RPE_eval]
  have hQ'0 : Q' = 0 ∨ Q'.natDegree < k := by
    by_cases h : Q' = 0
    · exact Or.inl h
    right
    have hdeg : (C α * R).degree = Q.degree := by
      rw [degree_C_mul (by simp [hα, hRlc, leadingCoeff_ne_zero.2 hQ0]),
        degree_eq_natDegree (fun h0 => hRlc (by rw [h0, leadingCoeff_zero])), degree_eq_natDegree hQ0, hRdeg, hQk]
    have hlc : (C α * R).leadingCoeff = Q.leadingCoeff := by
      rw [leadingCoeff_C_mul_of_isUnit (by simp [hα, hRlc, leadingCoeff_ne_zero.2 hQ0]), hα]
      field_simp
    have hlt := degree_sub_lt hdeg.symm hQ0 hlc.symm
    rw [← hQ', degree_eq_natDegree h, degree_eq_natDegree hQ0, hQk] at hlt
    exact_mod_cast hlt
  have hQ'sum : ∑ x ∈ range (M + 1), wE (M + 1) x * RE (M + 1) a x *
      Q'.eval ((x : ℚ) * ((x : ℚ) - 2 * ((M + 1 : ℕ) : ℚ))) = 0 := by
    rcases hQ'0 with h | h
    · simp [h]
    · exact ih _ h Q' rfl (by omega)
  calc ∑ x ∈ range (M + 1), wE (M + 1) x * RE (M + 1) a x * Q.eval ((x : ℚ) * ((x : ℚ) - 2 * ((M + 1 : ℕ) : ℚ)))
      = ∑ x ∈ range (M + 1), wE (M + 1) x * RE (M + 1) a x * Q'.eval ((x : ℚ) * ((x : ℚ) - 2 * ((M + 1 : ℕ) : ℚ)))
        + α * ∑ x ∈ range (M + 1), wE (M + 1) x * RE (M + 1) a x * R.eval ((x : ℚ) * ((x : ℚ) - 2 * ((M + 1 : ℕ) : ℚ))) := by
        rw [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun x _ => ?_
        rw [hsplit]; ring
    _ = 0 := by rw [hQ'sum, hR0]; ring

/-! the kernel family -/

/-- `λ₀ = λ(m) = -m²`. -/
def l0 (m : ℕ) : ℚ := (m : ℚ) * ((m : ℚ) - 2 * m)

/-- the numerator, vanishing at `λ₀`. -/
noncomputable def Nk (m a : ℕ) : ℚ[X] :=
  C (RE m a (m : ℚ)) * RPE m (a + 1) - C (RE m (a + 1) (m : ℚ)) * RPE m a

lemma Nk_root (m a : ℕ) : (Nk m a).IsRoot (l0 m) := by
  simp only [IsRoot, Nk, eval_sub, eval_mul, eval_C, l0, RPE_eval]; ring

noncomputable def pK (m a : ℕ) : ℚ[X] := Nk m a /ₘ (X - C (l0 m))

lemma mul_pK (m a : ℕ) : (X - C (l0 m)) * pK m a = Nk m a :=
  mul_divByMonic_eq_iff_isRoot.2 (Nk_root m a)

lemma Nk_le (m a : ℕ) : (Nk m a).natDegree ≤ a + 1 := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_C_mul_le _ _).trans (RPE_le _ _)
  · exact (natDegree_C_mul_le _ _).trans ((RPE_le _ _).trans (by omega))

lemma pK_le (m a : ℕ) : (pK m a).natDegree ≤ a := by
  rw [pK, natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
  have := Nk_le m a
  omega

/-- the family used in (L1): `p_a`, truncated to zero outside its range. -/
noncomputable def pF (K a : ℕ) : ℚ[X] := if a + 1 < K + 1 then pK (K + 1) a else 0

lemma nQ_eq (K : ℕ) : Bali.EvenPsi.nQ K = 2 * ((K + 1 : ℕ) : ℚ) := by
  simp only [Bali.EvenPsi.nQ]; push_cast; ring

lemma Ylam_eq (K : ℕ) : Bali.EvenPsi.Ylam K = C 4 * (X - C (l0 (K + 1))) := by
  simp only [Bali.EvenPsi.Ylam, nQ_eq, l0]
  rw [mul_sub, ← C_mul, sub_eq_add_neg, add_comm, ← C_neg]
  congr 2
  push_cast; ring

/-- **`y p_a = 4 Nk`.** -/
lemma Y_pK (K a : ℕ) : Bali.EvenPsi.Ylam K * pK (K + 1) a = C 4 * Nk (K + 1) a := by
  rw [Ylam_eq, mul_assoc, mul_pK]

lemma lam_eval (K : ℕ) (r : ℚ[X]) (x : ℚ) :
    (r.comp (Bali.Even.lam (Bali.EvenPsi.nQ K))).eval x = r.eval (x * (x - 2 * ((K + 1 : ℕ) : ℚ))) := by
  rw [eval_comp, nQ_eq]; simp [Bali.Even.lam]

/-- **`horth`**: `p_a` is orthogonal to lower degree for `W`. -/
theorem pF_orth (K a : ℕ) (Q : ℚ[X]) (hQ : Q.natDegree < a) : Bali.EvenPsi.ipW K (pF K a) Q = 0 := by
  unfold pF
  split_ifs with h
  · unfold Bali.EvenPsi.ipW
    rw [Y_pK]
    have e1 := orth_polyE K (a + 1) h Q.natDegree Q rfl (by omega)
    have e2 := orth_polyE K a (by omega) Q.natDegree Q rfl hQ
    have key : ∀ k ∈ range (K + 1), ((2 * K + 1 + 1).choose k : ℚ) ^ 2 * (Bali.EvenPsi.nQ K - 2 * k) *
          ((C 4 * Nk (K + 1) a).comp (Bali.Even.lam (Bali.EvenPsi.nQ K))).eval (k : ℚ) *
          Q.eval ((k : ℚ) * ((k : ℚ) - Bali.EvenPsi.nQ K))
        = 4 * RE (K + 1) a ((K + 1 : ℕ) : ℚ) * (wE (K + 1) k * RE (K + 1) (a + 1) k *
            Q.eval ((k : ℚ) * ((k : ℚ) - 2 * ((K + 1 : ℕ) : ℚ))))
          - 4 * RE (K + 1) (a + 1) ((K + 1 : ℕ) : ℚ) * (wE (K + 1) k * RE (K + 1) a k *
            Q.eval ((k : ℚ) * ((k : ℚ) - 2 * ((K + 1 : ℕ) : ℚ)))) := by
      intro k _
      rw [lam_eval, nQ_eq]
      simp only [Nk, eval_mul, eval_C, eval_sub, RPE_eval, wE]
      rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring]
      ring
    rw [sum_congr rfl key, sum_sub_distrib, ← mul_sum, ← mul_sum, e1, e2]
    ring
  · simp [Bali.EvenPsi.ipW]

/-- **(L1) for the explicit family.** -/
theorem L1_explicit (K a b : ℕ) (hab : b < a) (hbK : b + 1 ≤ K) :
    Bali.Skew.skew (Bali.EvenPsi.rowB K (pF K a)) (Bali.EvenPsi.rowB K (pF K b)) * Bali.EvenPsi.TB K (pF K 0)
      = Bali.EvenPsi.TB K (pF K b) * Bali.Skew.skew (Bali.EvenPsi.rowB K (pF K a)) (Bali.EvenPsi.rowB K (pF K 0)) :=
  Bali.EvenPsi.L1 K (pF K)
    (fun c => by
      unfold pF; split_ifs
      · exact pK_le _ _
      · simp)
    (fun c Q hQ => pF_orth K c Q hQ) a b hab hbK

end Bali.Chr

#print axioms Bali.Chr.orth_polyE
#print axioms Bali.Chr.L1_explicit
