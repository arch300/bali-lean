import P699.OddGen

/-!
# Even `n`, odd `d = 2k+1` (Bali lab, 2026-11-02)
`co(2k) V_{2k+1} = (τ_{2k}/4) V_{2k}`.
-/

open Finset Polynomial Matrix

namespace Bali.VE
open Bali.EvenPsi Bali.Chr Bali.Skew Bali.VG Bali.PfP Bali.VB Bali.GA Bali.OddB Bali.OG

variable {K : ℕ}

/-! ## totals -/

lemma TB_one (K : ℕ) : TB K 1 = ((2 * K + 1 + 1 : ℕ) : ℚ) * 2 ^ (2 * K + 1 + 1) := by
  have hf := fold_even K (yv K) (by intro x hx; simp only [yv]; rw [Nat.cast_sub hx]; ring)
  rw [show yv K (K + 1) = 0 by simp only [yv]; push_cast; ring, mul_zero, add_zero, tot2] at hf
  unfold TB
  rw [Bali.totL_apply]
  rw [show (∑ x ∈ range (2 * K + 1 + 1 + 1), ((2 * K + 1 + 1).choose x : ℚ) * yv K x) =
      ∑ x ∈ range (2 * K + 1 + 1 + 1), ((2 * K + 1 + 1).choose x : ℚ) * ((Ylam K * 1).comp (Bali.Even.lam (nQ K))).eval (x : ℚ) from
    sum_congr rfl fun x _ => by
      congr 1
      rw [mul_one, lam_eval]
      simp only [Ylam, yv, eval_add, eval_C, eval_mul, eval_X, nQ_eq]
      push_cast; ring] at hf
  exact hf.symm


lemma sum_rowB (p : ℚ[X]) : ∑ k : Fin (K + 1), rowB K p k = TB K p := by
  have hsym : ∀ x, x ≤ 2 * K + 1 + 1 → ((Ylam K * p).comp (Bali.Even.lam (nQ K))).eval (x : ℚ)
      = ((Ylam K * p).comp (Bali.Even.lam (nQ K))).eval ((2 * K + 1 + 1 - x : ℕ) : ℚ) := by
    intro x hx
    rw [lam_eval, lam_eval, Nat.cast_sub hx]
    congr 1; push_cast; ring
  have hc : ((Ylam K * p).comp (Bali.Even.lam (nQ K))).eval ((K + 1 : ℕ) : ℚ) = 0 := by
    rw [mul_comp, eval_mul]
    have := Ylam_centre K
    push_cast; rw [this, zero_mul]
  have hf := fold_even K (fun x => ((Ylam K * p).comp (Bali.Even.lam (nQ K))).eval (x : ℚ)) hsym
  rw [hc, mul_zero, add_zero] at hf
  unfold TB rowB
  rw [Bali.totL_apply, ← hf]
  exact Fin.sum_univ_eq_sum_range (fun x => 2 * ((2 * K + 1 + 1).choose x : ℚ) *
    ((Ylam K * p).comp (Bali.Even.lam (nQ K))).eval (x : ℚ)) (K + 1)

/-- **the totals.** `Σ e_s = τ_s / 4`. -/
lemma sum_e (s : ℕ) : ∑ h, e K s h = τ K s / 4 := by
  rcases s with _ | s
  · simp only [e, τ]
    rw [show (∑ h, nuV K h) = ∑ h : Fin (K + 1 + 1), FV K (h : ℕ) from rfl,
      Fin.sum_univ_eq_sum_range (FV K) (K + 1 + 1), tot1, TB_one]
    have : ((2 * K + 1 + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp
  · simp only [e, τ, rowE]
    rw [Fin.sum_univ_castSucc]
    simp only [extZ_cs, extZ_last, add_zero]
    rw [← sum_div, sum_rowB]

/-! ## the odd rows -/

/-- the row polynomials (in `t`). -/
noncomputable def Go (K : ℕ) (p : ℕ) : ℚ[X] :=
  if p % 2 = 0 then (Hc K p).comp (Lt K)
  else (Hc K p - C (τ K p / τ K (p - 1)) * Hc K (p - 1)).comp (Lt K)

lemma Go_deg (p : ℕ) : (Go K p).natDegree ≤ p := by
  unfold Go
  split_ifs
  · exact comp_le _ _ (Hc_le _)
  · refine comp_le _ _ ((natDegree_sub_le _ _).trans (max_le (Hc_le _) ?_))
    exact (natDegree_C_mul_le _ _).trans ((Hc_le _).trans (by omega))

lemma Go_coeff (p : ℕ) : (Go K p).coeff p = co K p := by
  unfold Go co
  split_ifs
  · exact coeff_comp_Lt _ _ (Hc_le _)
  · rw [coeff_comp_Lt]
    · rw [coeff_sub, coeff_C_mul, coeff_eq_zero_of_natDegree_lt (p := Hc K (p - 1)) (by
        have := Hc_le (K := K) (p - 1); omega), mul_zero, sub_zero]
    · exact (natDegree_sub_le _ _).trans (max_le (Hc_le _) ((natDegree_C_mul_le _ _).trans ((Hc_le _).trans (by omega))))

lemma Go_row_even (i : ℕ) (hi : 2 * i < K + 1) (h : Fin (K + 1 + 1)) :
    nuV K h * (Go K (2 * i)).eval (yv K (h : ℕ)) = e K (2 * i) h := by
  simp only [Go, show (2 * i) % 2 = 0 by omega, if_true, eval_comp, Lt_eval]
  exact rowEq _ hi h

lemma Go_row_odd (i : ℕ) (hi : 2 * i + 1 < K + 1) (h : Fin (K + 1 + 1)) :
    nuV K h * (Go K (2 * i + 1)).eval (yv K (h : ℕ)) = gO (e K) (τ K) i h := by
  simp only [Go, show (2 * i + 1) % 2 = 1 by omega, one_ne_zero, if_false, eval_comp, Lt_eval, eval_sub, eval_mul,
    eval_C, gO, Nat.add_sub_cancel]
  rw [mul_sub, one_mul, ← rowEq _ hi h, ← rowEq (2 * i) (by omega) h]
  ring

lemma sum_gO (hK : 2 ≤ K) (i : ℕ) (hi : 2 * i + 1 < K + 1) : ∑ h, gO (e K) (τ K) i h = 0 := by
  simp only [gO, sum_sub_distrib, ← mul_sum, one_mul, sum_e]
  have := tau_even_ne hK i hi
  field_simp
  ring

/-- **odd `d` for even `n`.** -/
theorem V_odd (hK : 2 ≤ K) (k : ℕ) (hk : 2 * k ≤ K) :
    (∏ p : Fin (2 * k + 1), co K p) *
        (sgnPairs (2 * k + 1) * VBvol (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) (2 * k + 1))
      = (∏ i : Fin k, skew (e K (2 * (i : ℕ))) (e K (2 * (i : ℕ) + 1))) * (τ K (2 * k) / 4) := by
  set r : Fin (2 * k + 1) → Fin (K + 1 + 1) → ℚ := fun p h => nuV K h * (Go K p).eval (yv K (h : ℕ)) with hr
  have hsl : ∀ i : Fin (k + 1), ∀ x : Fin 2, sl (m := k) (i, x) = 2 * (i : ℕ) + x := fun i x => eι_val (k + 1) (i, x)
  have row0 : ∀ i : Fin (k + 1), Ma r (i, 0) = Bali.OddB.ext (e K (2 * (i : ℕ))) := by
    intro i
    have hi := i.isLt
    have h0 : sl (m := k) (i, 0) < 2 * k + 1 := by rw [hsl]; simp; omega
    simp only [Ma, dif_pos h0]
    congr 1; funext h
    simp only [hr]
    rw [hsl]; simp only [Fin.val_zero, add_zero]
    exact Go_row_even _ (by omega) h
  have row1 : ∀ i : Fin (k + 1), (i : ℕ) < k → Ma r (i, 1) = Bali.OddB.ext (gO (e K) (τ K) i) := by
    intro i hik
    have h1 : sl (m := k) (i, 1) < 2 * k + 1 := by rw [hsl]; simp; omega
    simp only [Ma, dif_pos h1]
    congr 1; funext h
    simp only [hr]
    rw [hsl]; simp only [Fin.val_one]
    exact Go_row_odd _ (by omega) h
  have rowL : Ma r (Fin.last k, 1) = dI := by
    have h1 : ¬ sl (m := k) (Fin.last k, 1) < 2 * k + 1 := by rw [hsl]; simp
    simp only [Ma, dif_neg h1]
  have hτ : ∀ i : ℕ, i < k → τ K (2 * i) ≠ 0 := fun i hi => tau_even_ne hK i (by omega)
  have gg : ∀ i j : ℕ, i < k → j < k → skew (gO (e K) (τ K) i) (gO (e K) (τ K) j) = 0 :=
    fun i j hi hj => gO_gO (e K) (τ K) (w K) (hK_V hK) i j (hτ i hi) (hτ j hj)
  have hOO : ∀ i j : Fin (k + 1), (Ma r * (signM (K + 1 + 1) : Matrix _ _ ℚ) * (Ma r)ᵀ :
      Matrix (Fin (k + 1) × Fin 2) (Fin (k + 1) × Fin 2) ℚ) (i, 1) (j, 1) = 0 := by
    intro i j
    rw [gram_eq_skew]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · rw [row1 _ (by simp), row1 _ (by simp), skew_ext_ext]; exact gg _ _ (by simp) (by simp)
    · rw [row1 _ (by simp), rowL, skew_ext_dI]; exact sum_gO hK _ (by have := i'.isLt; simp; omega)
    · rw [rowL, row1 _ (by simp), skew_dI_ext, sum_gO hK _ (by have := j'.isLt; simp; omega), neg_zero]
    · rw [rowL, skew_dI_dI]
  set Y : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ := fun i j => (Ma r * (signM (K + 1 + 1) : Matrix _ _ ℚ) * (Ma r)ᵀ :
      Matrix (Fin (k + 1) × Fin 2) (Fin (k + 1) × Fin 2) ℚ) (i, 0) (j, 1) with hYd
  have hYc : ∀ i j : Fin (k + 1), (j : ℕ) < k → Y i j = skew (e K (2 * (i : ℕ))) (gO (e K) (τ K) j) := by
    intro i j hj
    simp only [hYd]; rw [gram_eq_skew, row0, row1 j hj, skew_ext_ext]
  have hYL : ∀ i : Fin (k + 1), Y i (Fin.last k) = τ K (2 * (i : ℕ)) / 4 := by
    intro i
    simp only [hYd]; rw [gram_eq_skew, row0, rowL, skew_ext_dI, sum_e]
  have hdet : det Y = (∏ i : Fin k, skew (e K (2 * (i : ℕ))) (e K (2 * (i : ℕ) + 1))) * (τ K (2 * k) / 4) := by
    rw [det_of_upperTriangular, Fin.prod_univ_castSucc]
    · congr 1
      · refine prod_congr rfl fun i _ => ?_
        rw [hYc _ _ (by simp), Fin.val_castSucc, Y_diag]
      · rw [hYL, Fin.val_last]
    · intro i j hji
      have hj : (j : ℕ) < k := by have := i.isLt; have : (j : ℕ) < i := hji; omega
      rw [hYc _ _ hj]
      exact Y_low (e K) (τ K) (w K) (hK_V hK) _ _ (hτ _ hj) hji
  have hU : IsUnit (det Y) := by
    rw [isUnit_iff_ne_zero, hdet]
    refine mul_ne_zero (prod_ne_zero_iff.2 fun i _ => hd_ne hK i (by have := i.isLt; omega)) ?_
    exact div_ne_zero (tau_even_ne' hK k (by omega)) (by norm_num)
  have key : (∏ p : Fin (2 * k + 1), (Go K p).coeff p) * (sgnPairs (2 * k + 1) *
      VBvol (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) (2 * k + 1)) = det Y :=
    odd_assemble (k := k) (Go K) Go_deg (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) yv_anti hOO hU
  rw [hdet] at key
  rw [← key]
  congr 1
  exact prod_congr rfl fun p _ => (Go_coeff p).symm

end Bali.VE

#print axioms Bali.VE.V_odd
