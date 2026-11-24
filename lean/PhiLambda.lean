import P699.RacahOrth

/-!
# `φ_j` is a polynomial in `λ = y (y - n)` (Bali lab, 2026-11-01)

`φ_j(y) = (-y)_j (y-n)_j = ∏_{i<j} (-λ(y) - i (n - i))`.  Hence `R_a` is a polynomial in `λ` of degree `a`.
-/

namespace Bali.Racah

theorem phi_lambda (n y : ℚ) : ∀ j : ℕ, phi n j y = ∏ i ∈ Finset.range j, (-(y * (y - n)) - (i : ℚ) * (n - i))
  | 0 => by simp [phi, P]
  | j + 1 => by
    rw [Finset.prod_range_succ, ← phi_lambda n y j]
    simp only [phi, P]
    ring

end Bali.Racah

namespace Bali.Racah

open Polynomial Finset

noncomputable def PhiP (n : ℚ) (j : ℕ) : ℚ[X] := ∏ i ∈ range j, (-X - C ((i : ℚ) * (n - i)))

lemma PhiP_eval (n y : ℚ) (j : ℕ) : (PhiP n j).eval (y * (y - n)) = phi n j y := by
  rw [phi_lambda, PhiP, eval_prod]; simp

lemma PhiP_eq (n : ℚ) (j : ℕ) : PhiP n j = C ((-1) ^ j) * ∏ i ∈ range j, (X + C ((i : ℚ) * (n - i))) := by
  induction j with
  | zero => simp [PhiP]
  | succ j ih =>
    rw [PhiP, prod_range_succ, ← PhiP, ih, prod_range_succ]
    simp only [pow_succ, C_mul, C_neg, C_1]; ring

lemma PhiP_natDegree (n : ℚ) (j : ℕ) : (PhiP n j).natDegree = j := by
  rw [PhiP_eq, natDegree_C_mul (pow_ne_zero _ (by norm_num)),
    natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C _)]
  rw [sum_congr rfl fun i _ => natDegree_X_add_C _]; simp

lemma PhiP_leading (n : ℚ) (j : ℕ) : (PhiP n j).leadingCoeff = (-1) ^ j := by
  rw [PhiP_eq, leadingCoeff_mul, leadingCoeff_C,
    (monic_prod_of_monic _ _ (fun i _ => monic_X_add_C _)).leadingCoeff, mul_one]

noncomputable def RP (n : ℚ) (m : ℕ) : ℚ[X] := ∑ j ∈ range (m + 1), C (c n m j) * PhiP n j

lemma RP_eval (n y : ℚ) (m : ℕ) : (RP n m).eval (y * (y - n)) = Rq n m y := by
  rw [RP, eval_finsetSum, Rq]
  exact sum_congr rfl fun j _ => by rw [eval_mul, eval_C, PhiP_eval]

lemma c_ne_zero (H m : ℕ) (hm : m ≤ H) : ∀ j, j ≤ m → c (2 * H + 1 : ℚ) m j ≠ 0
  | 0, _ => by simp [c]
  | j + 1, hj => by
    have ih := c_ne_zero H m hm j (by omega)
    simp only [c]
    have hjm : (j : ℚ) < m := by exact_mod_cast (by omega : j < m)
    have hmH : (m : ℚ) ≤ H := by exact_mod_cast hm
    have h1 : ((j : ℚ) - m) ≠ 0 := by intro h; linarith
    have h2 : ((m : ℚ) - (2 * H + 1) + j) ≠ 0 := by intro h; linarith
    have h3 : ((1 - (2 * (H : ℚ) + 1)) / 2 + j) ≠ 0 := by intro h; linarith
    have h4 : (-(2 * (H : ℚ) + 1) + j) ≠ 0 := by intro h; linarith
    have h5 : ((j : ℚ) + 1) ≠ 0 := by positivity
    exact mul_ne_zero ih (div_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h3) h4) h5))

lemma RP_split (n : ℚ) (m : ℕ) :
    RP n m = C (c n m m) * PhiP n m + ∑ j ∈ range m, C (c n m j) * PhiP n j := by
  rw [RP, sum_range_succ, add_comm]

lemma low_natDegree_lt (n : ℚ) (m : ℕ) (hm : 0 < m) :
    (∑ j ∈ range m, C (c n m j) * PhiP n j).natDegree < m := by
  apply lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := m - 1) fun j hj => ?_) (by omega)
  have := mem_range.1 hj
  calc (C (c n m j) * PhiP n j).natDegree ≤ (PhiP n j).natDegree := natDegree_C_mul_le _ _
    _ = j := PhiP_natDegree n j
    _ ≤ m - 1 := by omega

lemma RP_natDegree (H m : ℕ) (hm : m ≤ H) : (RP (2 * H + 1) m).natDegree = m := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp [RP, PhiP, c]
  rw [RP_split, natDegree_add_eq_left_of_natDegree_lt]
  · rw [natDegree_C_mul (c_ne_zero H m hm m le_rfl), PhiP_natDegree]
  · rw [natDegree_C_mul (c_ne_zero H m hm m le_rfl), PhiP_natDegree]
    exact low_natDegree_lt _ m hpos

lemma RP_leading (H m : ℕ) (hm : m ≤ H) :
    (RP (2 * H + 1) m).leadingCoeff = c (2 * H + 1) m m * (-1) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp [RP, PhiP, c]
  rw [RP_split, leadingCoeff_add_of_degree_lt']
  · rw [leadingCoeff_mul, leadingCoeff_C, PhiP_leading]
  · have hne : C (c (2 * H + 1) m m) * PhiP (2 * H + 1) m ≠ 0 := by
      intro h; have := congrArg natDegree h
      rw [natDegree_C_mul (c_ne_zero H m hm m le_rfl), PhiP_natDegree] at this; simp at this; omega
    rw [degree_eq_natDegree hne, natDegree_C_mul (c_ne_zero H m hm m le_rfl), PhiP_natDegree]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast low_natDegree_lt _ m hpos)


/-- **(c) orthogonality to lower degree.**  `R_a ⟂_w Q(λ)` for every polynomial `Q` of degree `< a`. -/
theorem orth_poly (H a : ℕ) (ha : a ≤ H) :
    ∀ k : ℕ, ∀ Q : ℚ[X], Q.natDegree = k → k < a →
      ∑ x ∈ range (H + 1), w H x * Rq (2 * H + 1) a x * Q.eval ((x : ℚ) * ((x : ℚ) - (2 * H + 1))) = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro Q hQk hka
  by_cases hQ0 : Q = 0
  · simp [hQ0]
  have hk : k ≤ H := by omega
  set R := RP (2 * H + 1) k with hR
  have hRdeg : R.natDegree = k := RP_natDegree H k hk
  have hRlc : R.leadingCoeff ≠ 0 := by
    rw [RP_leading H k hk]; exact mul_ne_zero (c_ne_zero H k hk k le_rfl) (pow_ne_zero _ (by norm_num))
  set α := Q.leadingCoeff / R.leadingCoeff with hα
  set Q' := Q - C α * R with hQ'
  have hsplit : ∀ x : ℚ, Q.eval x = Q'.eval x + α * R.eval x := by
    intro x; simp [hQ']
  -- the R_k part vanishes by orthogonality
  have hR0 : ∑ x ∈ range (H + 1), w H x * Rq (2 * H + 1) a x * R.eval ((x : ℚ) * ((x : ℚ) - (2 * H + 1))) = 0 := by
    have := orth H a k ha hk (by omega)
    rw [← this]
    refine sum_congr rfl fun x _ => ?_
    rw [hR, RP_eval]
  -- the remainder has lower degree
  have hQ'0 : Q' = 0 ∨ Q'.natDegree < k := by
    by_cases h : Q' = 0
    · exact Or.inl h
    right
    have hdeg : (C α * R).degree = Q.degree := by
      rw [degree_C_mul (by simp [hα, hRlc, leadingCoeff_ne_zero.2 hQ0]), degree_eq_natDegree (fun h0 => hRlc (by rw [h0, leadingCoeff_zero])), degree_eq_natDegree hQ0, hRdeg, hQk]
    have hlc : (C α * R).leadingCoeff = Q.leadingCoeff := by
      rw [leadingCoeff_C_mul_of_isUnit (by simp [hα, hRlc, leadingCoeff_ne_zero.2 hQ0]), hα]
      field_simp
    have hlt := degree_sub_lt hdeg.symm hQ0 hlc.symm
    rw [← hQ', degree_eq_natDegree h, degree_eq_natDegree hQ0, hQk] at hlt
    exact_mod_cast hlt
  have hQ'sum : ∑ x ∈ range (H + 1), w H x * Rq (2 * H + 1) a x * Q'.eval ((x : ℚ) * ((x : ℚ) - (2 * H + 1))) = 0 := by
    rcases hQ'0 with h | h
    · simp [h]
    · exact ih _ h Q' rfl (by omega)
  calc ∑ x ∈ range (H + 1), w H x * Rq (2 * H + 1) a x * Q.eval ((x : ℚ) * ((x : ℚ) - (2 * H + 1)))
      = ∑ x ∈ range (H + 1), w H x * Rq (2 * H + 1) a x * Q'.eval ((x : ℚ) * ((x : ℚ) - (2 * H + 1)))
        + α * ∑ x ∈ range (H + 1), w H x * Rq (2 * H + 1) a x * R.eval ((x : ℚ) * ((x : ℚ) - (2 * H + 1))) := by
        rw [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun x _ => ?_
        rw [hsplit]; ring
    _ = 0 := by rw [hQ'sum, hR0]; ring

end Bali.Racah

#print axioms Bali.Racah.phi_lambda
#print axioms Bali.Racah.PhiP_natDegree
#print axioms Bali.Racah.PhiP_leading
#print axioms Bali.Racah.RP_natDegree
#print axioms Bali.Racah.RP_leading
#print axioms Bali.Racah.orth_poly
