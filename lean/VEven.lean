import P699.GenAssemble

/-!
# Even `n`, even `d`: `V^B_{2k}` as a product of skew pairings (Bali lab, 2026-11-02)
`n = 2(K+1)`; shells `h = 0..K+1`, the centre `h = K+1` has weight `C(n,K+1)`.
-/

open Finset Polynomial Matrix

namespace Bali.VE
open Bali.EvenPsi Bali.Chr Bali.Skew Bali.VG Bali.PfP Bali.VB Bali.GA

variable (K : ℕ)

/-! ## linearity -/

lemma rowB_C (c : ℚ) (q : ℚ[X]) : rowB K (C c * q) = fun k => c * rowB K q k := by
  funext k
  simp only [rowB, show Ylam K * (C c * q) = C c * (Ylam K * q) by ring, mul_comp, C_comp, eval_mul, eval_C]
  ring

lemma TB_C (c : ℚ) (q : ℚ[X]) : TB K (C c * q) = c * TB K q := by
  unfold TB
  rw [show Ylam K * (C c * q) = C c * (Ylam K * q) by ring, mul_comp, C_comp, ← smul_eq_C_mul, map_smul, smul_eq_mul]

lemma skew_smul2 {N : ℕ} (f g : Fin (N + 1) → ℚ) (c : ℚ) : skew f (fun k => c * g k) = c * skew f g := by
  unfold skew
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  simp only [← mul_sum]
  ring

lemma skew_smul1 {N : ℕ} (f g : Fin (N + 1) → ℚ) (c : ℚ) : skew (fun k => c * f k) g = c * skew f g := by
  rw [Bali.OddB.skew_anti, skew_smul2, Bali.OddB.skew_anti g f]; ring

lemma rowB_zero : rowB K 0 = fun _ => 0 := by funext k; simp [rowB]
lemma TB_zero : TB K 0 = 0 := by simp [TB]

/-! ## the data -/

/-- the constant `p_0 = c₀`. -/
noncomputable def c0 : ℚ := (pF K 0).coeff 0

lemma pF0 : pF K 0 = C (c0 K) * 1 := by
  rw [mul_one]
  apply eq_C_of_natDegree_le_zero
  unfold pF; split_ifs
  · exact pK_le _ _
  · simp

/-- `V`-rows `e_0 = ν`, `e_{s+1} = (y/4) p_s`. -/
noncomputable def e : ℕ → Fin (K + 1 + 1) → ℚ
  | 0 => nuV K
  | s + 1 => rowE K (pF K s)

noncomputable def τ : ℕ → ℚ
  | 0 => 4 * TB K 1 / ((2 * K + 1 + 1 : ℕ) : ℚ)
  | s + 1 => TB K (pF K s)

noncomputable def w : ℕ → ℚ
  | 0 => 0
  | t + 1 => skew (rowB K (pF K 0)) (rowB K (pF K t)) / (16 * TB K (pF K 0))

variable {K}

lemma lc_ne (hK : 1 ≤ K) (b : ℕ) (hb : b + 1 < K + 1) : (pK (K + 1) b).coeff b ≠ 0 := by
  rw [pK_coeff, Bali.RE.RE_centre _ _ (by omega), RPE_coeff]
  exact mul_ne_zero (Bali.TN.F_ne _ b (by omega))
    (mul_ne_zero (Bali.Chr.ce_ne _ _ (by omega) _ le_rfl) (pow_ne_zero _ (by norm_num)))

lemma c0_ne (hK : 1 ≤ K) : c0 K ≠ 0 := by
  unfold c0 pF
  rw [if_pos (by omega)]
  exact lc_ne hK 0 (by omega)

lemma T0_ne (hK : 2 ≤ K) : TB K (pF K 0) ≠ 0 := by
  unfold pF
  rw [if_pos (by omega)]
  exact Bali.TN.TB_ne K 0 (by omega)

lemma T1_ne (hK : 2 ≤ K) : TB K 1 ≠ 0 := by
  intro h
  apply T0_ne hK
  rw [pF0, TB_C, h, mul_zero]

/-- **The semiseparable structure of `V`.** -/
theorem hK_V (hK : 2 ≤ K) (s t : ℕ) (hst : s < t) (hn : ¬(s = 0 ∧ t = 1)) :
    skew (e K s) (e K t) = τ K s * w K t := by
  have hT0 := T0_ne hK
  have hc := c0_ne (K := K) (by omega)
  have hnn : ((2 * K + 1 + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rcases s with _ | a
  · obtain ⟨j, rfl⟩ : ∃ j, t = j + 1 := ⟨t - 1, by omega⟩
    have hj : 1 ≤ j := by omega
    simp only [e, τ, w]
    rw [border_pF K j hj]
    have hr : rowB K (pF K 0) = fun k => c0 K * rowB K 1 k := by rw [pF0, rowB_C]
    have hT : TB K (pF K 0) = c0 K * TB K 1 := by rw [pF0, TB_C]
    rw [hr, skew_smul1, hT]
    have h1 := T1_ne hK
    field_simp
    ring
  · obtain ⟨b, rfl⟩ : ∃ b, t = b + 1 := ⟨t - 1, by omega⟩
    have hab : a < b := by omega
    simp only [e, τ, w]
    rw [skew_rowE]
    by_cases ha : a + 1 ≤ K
    · have h := L1_explicit K b a hab ha
      rw [Bali.OddB.skew_anti (rowB K (pF K a)), Bali.OddB.skew_anti (rowB K (pF K 0))]
      field_simp
      linear_combination -h
    · have hz : pF K a = 0 := by unfold pF; rw [if_neg (by omega)]
      rw [hz, rowB_zero, TB_zero]
      simp [skew]

lemma tau_even_ne (hK : 2 ≤ K) (j : ℕ) (hj : 2 * j + 1 < K + 1) : τ K (2 * j) ≠ 0 := by
  rcases j with _ | j
  · simp only [mul_zero, τ]
    have hnn : ((2 * K + 1 + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    exact div_ne_zero (mul_ne_zero (by norm_num) (T1_ne hK)) hnn
  · rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring]
    simp only [τ, pF]
    rw [if_pos (by omega)]
    exact Bali.TN.TB_ne K _ (by omega)

/-! ## the polynomials -/

/-- `H_0 = 1`, `H_{s+1} = Nk s`, in `λ`. -/
noncomputable def Hc (K : ℕ) : ℕ → ℚ[X]
  | 0 => 1
  | s + 1 => Nk (K + 1) s

lemma Hc_le (s : ℕ) : (Hc K s).natDegree ≤ s := by
  cases s with
  | zero => simp [Hc]
  | succ s => exact Nk_le _ _

/-- the shell value of `λ`. -/
def lamS (K : ℕ) (h : ℕ) : ℚ := (h : ℚ) * ((h : ℚ) - 2 * ((K + 1 : ℕ) : ℚ))

lemma rowEq (s : ℕ) (hs : s < K + 1) (h : Fin (K + 1 + 1)) :
    nuV K h * (Hc K s).eval (lamS K h) = e K s h := by
  rcases s with _ | s
  · simp [Hc, e]
  · simp only [Hc, e, rowE, pF]
    rw [if_pos (by omega)]
    rcases Fin.eq_castSucc_or_eq_last h with ⟨k, rfl⟩ | rfl
    · rw [extZ_cs]
      have hk := k.isLt
      simp only [nuV, FV, rowB, Fin.val_castSucc]
      rw [if_pos hk, Y_pK, lam_eval]
      simp only [lamS, eval_mul, eval_C]
      ring
    · rw [extZ_last]
      have : lamS K (Fin.last (K + 1) : ℕ) = l0 (K + 1) := by simp [lamS, l0]
      rw [this, (Nk_root (K + 1) s), mul_zero]

/-- `λ = (t - n²)/4` as a polynomial in `t`. -/
noncomputable def Lt (K : ℕ) : ℚ[X] := C (1 / 4) * (X - C (((2 * K + 1 + 1 : ℕ) : ℚ) ^ 2))

lemma Lt_eval (h : ℕ) : (Lt K).eval (yv K h) = lamS K h := by
  simp only [Lt, eval_mul, eval_C, eval_sub, eval_X, yv, lamS]
  push_cast
  ring

lemma Lt_deg : (Lt K).natDegree ≤ 1 := by
  unfold Lt; compute_degree

/-- the basis polynomials in `t`. -/
noncomputable def Gp (K k : ℕ) (a : Fin k × Fin 2) : ℚ[X] :=
  if (a.2 : ℕ) = 0 then (Hc K (2 * (a.1 : ℕ))).comp (Lt K)
  else (Hc K (2 * (a.1 : ℕ) + 1) - C (τ K (2 * (a.1 : ℕ) + 1) / τ K (2 * (a.1 : ℕ))) * Hc K (2 * (a.1 : ℕ))).comp (Lt K)

lemma comp_le (P : ℚ[X]) (s : ℕ) (hP : P.natDegree ≤ s) : (P.comp (Lt K)).natDegree ≤ s := by
  refine natDegree_comp_le.trans ?_
  calc P.natDegree * (Lt K).natDegree ≤ s * 1 := Nat.mul_le_mul hP Lt_deg
    _ = s := mul_one s

lemma Gp_deg (k : ℕ) (a : Fin k × Fin 2) : (Gp K k a).natDegree ≤ (eι k a : ℕ) := by
  obtain ⟨i, x⟩ := a
  rw [eι_val]
  unfold Gp
  rcases fin2_cases x with rfl | rfl
  · simpa using comp_le _ _ (Hc_le _)
  · simp only [Fin.val_one, one_ne_zero, if_false]
    refine comp_le _ _ ((natDegree_sub_le _ _).trans (max_le (Hc_le _) ?_))
    exact (natDegree_C_mul_le _ _).trans ((Hc_le _).trans (by omega))

lemma yv_anti : StrictAnti (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) := by
  intro a b hab
  have hab' : ((a : ℕ) : ℚ) < (b : ℕ) := by exact_mod_cast hab
  have hb : ((b : ℕ) : ℚ) ≤ (K : ℚ) + 1 := by exact_mod_cast (by have := b.isLt; omega : (b : ℕ) ≤ K + 1)
  simp only [yv]
  push_cast
  nlinarith

/-- **`V^B_{2k}` for even `n`**, as a product of skew pairings, assuming they do not vanish. -/
theorem V_even (hK : 2 ≤ K) (k : ℕ) (hk : 2 * k ≤ K + 1)
    (hd : ∀ i : Fin k, skew (e K (2 * (i : ℕ))) (e K (2 * (i : ℕ) + 1)) ≠ 0) :
    (∏ a, (Gp K k a).coeff (eι k a : ℕ)) *
        (sgnPairs (2 * k) * VBvol (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) (2 * k))
      = ∏ i : Fin k, skew (e K (2 * (i : ℕ))) (e K (2 * (i : ℕ) + 1)) := by
  refine assemble (e K) (τ K) (w K) (hK_V hK) _ _ yv_anti (Gp K k) (Gp_deg k) ?_ ?_ ?_ hd
  · intro i h
    have hi := i.isLt
    simp only [Gp, Fin.val_zero, if_true, eval_comp, Lt_eval]
    exact rowEq _ (by omega) h
  · intro i h
    have hi := i.isLt
    simp only [Gp, Fin.val_one, one_ne_zero, if_false, eval_comp, Lt_eval, eval_sub, eval_mul, eval_C, gO]
    rw [mul_sub, one_mul, ← rowEq _ (by omega) h, ← rowEq (2 * (i : ℕ)) (by omega) h]
    ring
  · intro i
    have hi := i.isLt
    exact tau_even_ne hK _ (by omega)

end Bali.VE

#print axioms Bali.VE.hK_V
#print axioms Bali.VE.V_even
