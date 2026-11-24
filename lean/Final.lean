import P699.VB
import P699.GramRacah

/-!
# Theorem Bodd in Lean: the final assembly (Bali lab, 2026-11-01)
-/

open Finset Polynomial Matrix

namespace Bali.Final
open Bali Bali.PfP Bali.VB Bali.Racah Bali.GR Bali.Skew

/-- `P_a(t) = R_a((t - n²)/4)`: the Racah polynomial in the variable `t = (n - 2h)²`. -/
noncomputable def Pa (n : ℚ) (a : ℕ) : ℚ[X] := (RP n a).comp (C (1 / 4) * (X - C (n ^ 2)))

lemma Pa_eval_shell (H : ℕ) (a h : ℕ) :
    (Pa (2 * H + 1) a).eval ((2 * (H : ℚ) + 1 - 2 * h) ^ 2) = Rq (2 * H + 1) a h := by
  rw [Pa, eval_comp]
  simp only [eval_mul, eval_C, eval_sub, eval_X]
  rw [show 1 / 4 * ((2 * (H : ℚ) + 1 - 2 * h) ^ 2 - (2 * H + 1) ^ 2) = (h : ℚ) * ((h : ℚ) - (2 * H + 1)) by ring]
  exact RP_eval _ _ _

lemma lin_natDegree (n : ℚ) : (C (1 / 4 : ℚ) * (X - C (n ^ 2))).natDegree = 1 := by
  rw [natDegree_C_mul (by norm_num), natDegree_X_sub_C]

lemma Pa_natDegree (H a : ℕ) (ha : a ≤ H) : (Pa (2 * H + 1) a).natDegree = a := by
  rw [Pa, natDegree_comp, lin_natDegree, mul_one, RP_natDegree H a ha]

lemma Pa_leading (H a : ℕ) (ha : a ≤ H) :
    (Pa (2 * H + 1) a).leadingCoeff = (RP (2 * H + 1) a).leadingCoeff * (1 / 4) ^ a := by
  rw [Pa, leadingCoeff_comp (by rw [lin_natDegree]; norm_num), leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_X_sub_C, mul_one, RP_natDegree H a ha]


/-- shell points and weights. -/
def tS (H : ℕ) : Fin (H + 1) → ℚ := fun h => (2 * (H : ℚ) + 1 - 2 * (h : ℕ)) ^ 2
def nuS (H : ℕ) : Fin (H + 1) → ℚ := fun h => 2 * ((2 * H + 1).choose (h : ℕ) : ℚ)

/-- change of basis from powers of `t` to the Racah polynomials. -/
noncomputable def Brac (H m : ℕ) : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℚ :=
  fun a p => (Pa (2 * H + 1) (eι m a : ℕ)).coeff (eι m p : ℕ)

lemma Brac_mul (H m : ℕ) (hm : 2 * m ≤ H + 1) (a : Fin m × Fin 2) (h : Fin (H + 1)) :
    (Brac H m * Mpow (m := m) (tS H) (nuS H)) a h = row H (eι m a : ℕ) h := by
  have ha : ((eι m a : Fin (2 * m)) : ℕ) ≤ H := by have := (eι m a).isLt; omega
  have hdeg : (Pa (2 * H + 1) (eι m a : ℕ)).natDegree < 2 * m := by
    rw [Pa_natDegree H _ ha]; exact (eι m a).isLt
  simp only [Matrix.mul_apply, Brac, Mpow]
  rw [show ∑ p : Fin m × Fin 2, (Pa (2 * H + 1) (eι m a : ℕ)).coeff (eι m p : ℕ) * (nuS H h * tS H h ^ ((eι m p : Fin (2 * m)) : ℕ))
      = nuS H h * ∑ q : Fin (2 * m), (Pa (2 * H + 1) (eι m a : ℕ)).coeff (q : ℕ) * tS H h ^ (q : ℕ) from by
    rw [mul_sum]
    rw [← Fintype.sum_equiv (eι m) (fun p => (Pa (2 * H + 1) (eι m a : ℕ)).coeff (eι m p : ℕ) * (nuS H h * tS H h ^ ((eι m p : Fin (2 * m)) : ℕ)))
      (fun q => nuS H h * ((Pa (2 * H + 1) (eι m a : ℕ)).coeff (q : ℕ) * tS H h ^ (q : ℕ))) (fun p => by ring)]]
  rw [Fin.sum_univ_eq_sum_range (fun q => (Pa (2 * H + 1) (eι m a : ℕ)).coeff q * tS H h ^ q) (2 * m),
    ← eval_eq_sum_range' hdeg, tS, Pa_eval_shell, GR.row, nuS]


lemma det_Brac (H m : ℕ) (hm : 2 * m ≤ H + 1) :
    det (Brac H m) = ∏ q : Fin (2 * m), (RP (2 * H + 1) (q : ℕ)).leadingCoeff * (1 / 4) ^ (q : ℕ) := by
  rw [← det_reindex_self (eι m), det_of_lowerTriangular]
  · refine prod_congr rfl fun q _ => ?_
    simp only [reindex_apply, submatrix_apply, Brac, Equiv.apply_symm_apply]
    have hq : (q : ℕ) ≤ H := by have := q.isLt; omega
    rw [← Pa_leading H q hq, Polynomial.leadingCoeff, Pa_natDegree H q hq]
  · intro p q hpq
    simp only [reindex_apply, submatrix_apply, Brac, Equiv.apply_symm_apply]
    have hp : (p : ℕ) ≤ H := by have := p.isLt; omega
    apply coeff_eq_zero_of_natDegree_lt
    rw [Pa_natDegree H p hp]
    exact hpq

lemma tS_anti (H : ℕ) : StrictAnti (tS H) := by
  intro a b hab
  simp only [tS]
  have h1 : (a : ℕ) < (b : ℕ) := hab
  have hb : (b : ℕ) ≤ H := Nat.lt_succ_iff.1 b.isLt
  have e1 : (2 * (H : ℚ) + 1 - 2 * (b : ℕ)) > 0 := by
    have : ((b : ℕ) : ℚ) ≤ H := by exact_mod_cast hb
    linarith
  have e2 : ((a : ℕ) : ℚ) < (b : ℕ) := by exact_mod_cast h1
  nlinarith


/-- the diagonal entries `D_i = ⟨R_{2i}, R_{2i+1}⟩`. -/
noncomputable def Dval (H i : ℕ) : ℚ :=
  -4 * ((RP (2 * H + 1) (2 * i + 1)).leadingCoeff * ((2 * (H : ℚ) + 1) + 1 - 2 * (2 * i + 1)) / 4
    / (RP (2 * H + 1) (2 * i)).leadingCoeff) * hN H (2 * i)

lemma Dval_ne (H i : ℕ) (hi : 2 * i + 1 ≤ H) : Dval H i ≠ 0 := by
  have l1 : (RP (2 * H + 1) (2 * i + 1)).leadingCoeff ≠ 0 := by
    rw [RP_leading H _ hi]; exact mul_ne_zero (c_ne_zero H _ hi _ le_rfl) (pow_ne_zero _ (by norm_num))
  have l0 : (RP (2 * H + 1) (2 * i)).leadingCoeff ≠ 0 := by
    rw [RP_leading H _ (by omega)]; exact mul_ne_zero (c_ne_zero H _ (by omega) _ le_rfl) (pow_ne_zero _ (by norm_num))
  have hf : ((2 * (H : ℚ) + 1) + 1 - 2 * (2 * i + 1)) ≠ 0 := by
    have : (2 * (i : ℚ) + 1) ≤ H := by exact_mod_cast hi
    intro h; linarith
  have hn : hN H (2 * i) ≠ 0 := by
    rw [hN_closed H (2 * i) (by omega)]
    have hc1 : ((2 * H).choose H : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have hc2 : ((2 * H + 1).choose (2 * i) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have hd : (2 * (H : ℚ) + 1 - 2 * ((2 * i : ℕ) : ℚ)) ≠ 0 := by
      have : (2 * (i : ℚ) + 1) ≤ H := by exact_mod_cast hi
      push_cast; intro h; linarith
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by positivity)) (pow_ne_zero _ hc1))
      (mul_ne_zero hd (pow_ne_zero _ hc2))
  unfold Dval
  exact mul_ne_zero (mul_ne_zero (by norm_num) (div_ne_zero (div_ne_zero (mul_ne_zero l1 hf) (by norm_num)) l0)) hn

/-- the Racah Gram matrix. -/
noncomputable def Gram (H m : ℕ) : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℚ :=
  (Brac H m * Mpow (m := m) (tS H) (nuS H)) * (signM H : Matrix (Fin (H + 1)) (Fin (H + 1)) ℚ) *
    (Brac H m * Mpow (m := m) (tS H) (nuS H))ᵀ

lemma Gram_entry (H m : ℕ) (hm : 2 * m ≤ H + 1) (a b : Fin m × Fin 2) :
    Gram H m a b = skew (row H (eι m a : ℕ)) (row H (eι m b : ℕ)) := by
  rw [Gram, gram_eq_skew]
  congr 1 <;> funext h <;> exact Brac_mul H m hm _ h

lemma Gram_skew (H m : ℕ) : (Gram H m)ᵀ = -Gram H m := by
  unfold Gram
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, signM_transpose]
  simp [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]

/-- **Theorem Bodd (even `d = 2m`), Lean form.**  `n = 2H+1`, `2m ≤ H+1`:
`det B · sgn · V^B_{2m} = ∏_{i<m} D_i`, with `det B = ∏ ℓ_a/4^a` (`det_Brac`) and `D_i` explicit (`Dval`). -/
theorem theorem_Bodd (H m : ℕ) (hm : 2 * m ≤ H + 1) :
    det (Brac H m) * (sgnPairs (2 * m) * VBvol (tS H) (nuS H) (2 * m)) = ∏ i : Fin m, Dval H i := by
  have hval : ∀ (i : Fin m) (s : Fin 2), ((eι m (i, s) : Fin (2 * m)) : ℕ) = 2 * (i : ℕ) + s := fun i s => eι_val m (i, s)
  have hi : ∀ i : Fin m, 2 * (i : ℕ) + 1 ≤ H := fun i => by have := i.isLt; omega
  have hOO : ∀ i j : Fin m, Gram H m (i, 1) (j, 1) = 0 := by
    intro i j
    rcases le_or_gt (j : ℕ) i with hji | hij
    · rw [Gram_entry H m hm, hval, hval]
      exact skew_rows_zero H _ j (by have := hi i; simp; omega) (by simp; omega)
    · have := congrFun (congrFun (Gram_skew H m) (j, 1)) (i, 1)
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
      rw [this, Gram_entry H m hm, hval, hval, neg_eq_zero]
      exact skew_rows_zero H _ i (by have := hi j; simp; omega) (by simp; omega)
  set Y : Matrix (Fin m) (Fin m) ℚ := fun i j => Gram H m (i, 0) (j, 1) with hY
  have hYtri : Y.BlockTriangular id := by
    intro i j hji
    simp only [hY, id] at hji ⊢
    rw [Gram_entry H m hm, hval, hval]
    exact skew_rows_zero H _ j (by have := hi i; simp; omega) (by simp; omega)
  have hdiag : ∀ i : Fin m, Y i i = Dval H i := by
    intro i
    simp only [hY]
    rw [Gram_entry H m hm, hval, hval]
    simpa [Dval] using skew_rows_diag H i (hi i)
  have hdetY : det Y = ∏ i : Fin m, Dval H i := by
    rw [det_of_upperTriangular hYtri]
    exact prod_congr rfl fun i _ => hdiag i
  have hYunit : IsUnit (det Y) := by
    rw [hdetY]
    exact isUnit_iff_ne_zero.2 (prod_ne_zero_iff.2 fun i _ => Dval_ne H i (hi i))
  have key := VB_eq_detY (K := ℚ) (tS H) (nuS H) (tS_anti H) (Brac H m) hOO hYunit
  rw [key]
  exact hdetY

end Bali.Final
#print axioms Bali.Final.Pa_leading
#print axioms Bali.Final.Pa_eval_shell
#print axioms Bali.Final.Brac_mul
#print axioms Bali.Final.det_Brac
#print axioms Bali.Final.tS_anti
#print axioms Bali.Final.theorem_Bodd
