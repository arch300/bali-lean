import P699.PsiLead
import P699.PhiLambda
import P699.TWatson

/-!
# Gram matrix of the Racah basis (Bali lab, 2026-11-01)
`⟨R_a, R_b⟩` (skew product with shell weights) for odd `b`: zero if `b ≤ a`, and `-4 (Q_a / ℓ_a) ‖R_a‖²` if `b = a + 1`.
-/

open Finset Polynomial

namespace Bali.GR
open Bali Bali.Skew Bali.Even Bali.Racah Bali.PsiA

/-- row of the Racah basis on the shells. -/
noncomputable def row (H a : ℕ) : Fin (H + 1) → ℚ :=
  fun k => 2 * ((2 * H + 1).choose (k : ℕ) : ℚ) * Rq (2 * H + 1) a (k : ℕ)

lemma comp_lam_eval (H b : ℕ) (k : ℕ) :
    ((RP (2 * H + 1) b).comp (Even.lam (((2 * H : ℕ) : ℚ) + 1))).eval (k : ℚ) = Rq (2 * H + 1) b k := by
  rw [eval_comp, Even.lam]; simp only [eval_mul, eval_X, eval_sub, eval_C]; push_cast
  exact RP_eval _ _ _

/-- the skew product of two Racah rows, through Lemma ψ, for odd `b`. -/
lemma skew_rows (H a j : ℕ) (hb : 2 * j + 1 ≤ H) :
    ∃ Q : ℚ[X], Q.natDegree ≤ 2 * j ∧
      Q.coeff (2 * j) = (RP (2 * H + 1) (2 * j + 1)).leadingCoeff * ((2 * (H : ℚ) + 1) + 1 - 2 * (2 * j + 1)) / 4 ∧
      skew (row H a) (row H (2 * j + 1))
        = -4 * ∑ k ∈ range (H + 1), w H k * Rq (2 * H + 1) a k * Q.eval ((k : ℚ) * ((k : ℚ) - (2 * H + 1))) := by
  have hdeg := RP_natDegree H (2 * j + 1) hb
  have htot : totL (2 * H + 1) ((RP (2 * H + 1) (2 * j + 1)).comp (Even.lam (((2 * H : ℕ) : ℚ) + 1))) = 0 := by
    rw [totL_apply]
    have := Bali.TW.T_R_odd H j hb
    rw [← this]
    refine sum_congr rfl fun x _ => ?_
    rw [comp_lam_eval]; push_cast; ring_nf
  obtain ⟨Q, hQdeg, hlead, hskew⟩ :=
    psi_skew_lead H (2 * j + 1) (by omega) hb (RP (2 * H + 1) (2 * j + 1)) hdeg.le htot (fun x => Rq (2 * H + 1) a x)
  refine ⟨Q, by simpa using hQdeg, ?_, ?_⟩
  · rw [show 2 * j + 1 - 1 = 2 * j by omega] at hlead
    rw [hlead, Polynomial.leadingCoeff, hdeg]; push_cast; ring
  · have e1 : row H a = fun k : Fin (H + 1) => 2 * ((2 * H + 1).choose (k : ℕ) : ℚ) * Rq (2 * H + 1) a (k : ℕ) := rfl
    have e2 : row H (2 * j + 1) = fun k : Fin (H + 1) => 2 * ((2 * H + 1).choose (k : ℕ) : ℚ) *
        ((RP (2 * H + 1) (2 * j + 1)).comp (Even.lam (((2 * H : ℕ) : ℚ) + 1))).eval ((k : ℕ) : ℚ) := by
      funext k; rw [row, comp_lam_eval]
    rw [e1, e2, hskew]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    simp only [w]; push_cast; ring


/-- **zeros**: `⟨R_a, R_b⟩ = 0` for odd `b ≤ a ≤ H`. -/
theorem skew_rows_zero (H a j : ℕ) (ha : a ≤ H) (hba : 2 * j + 1 ≤ a) :
    skew (row H a) (row H (2 * j + 1)) = 0 := by
  obtain ⟨Q, hQdeg, -, hsk⟩ := skew_rows H a j (by omega)
  rw [hsk, orth_poly H a ha Q.natDegree Q rfl (by omega), mul_zero]

/-- **diagonal**: `⟨R_{2j}, R_{2j+1}⟩ = -4 (Q_{2j} / ℓ_{2j}) ‖R_{2j}‖²`. -/
theorem skew_rows_diag (H j : ℕ) (hb : 2 * j + 1 ≤ H) :
    skew (row H (2 * j)) (row H (2 * j + 1))
      = -4 * ((RP (2 * H + 1) (2 * j + 1)).leadingCoeff * ((2 * (H : ℚ) + 1) + 1 - 2 * (2 * j + 1)) / 4
          / (RP (2 * H + 1) (2 * j)).leadingCoeff) * hN H (2 * j) := by
  obtain ⟨Q, hQdeg, hlead, hsk⟩ := skew_rows H (2 * j) j hb
  rw [hsk, ← hlead]
  set R := RP (2 * H + 1) (2 * j) with hR
  have hRdeg : R.natDegree = 2 * j := RP_natDegree H (2 * j) (by omega)
  have hRlc : R.leadingCoeff ≠ 0 := by
    rw [RP_leading H (2 * j) (by omega)]
    exact mul_ne_zero (c_ne_zero H (2 * j) (by omega) (2 * j) le_rfl) (pow_ne_zero _ (by norm_num))
  set α := Q.coeff (2 * j) / R.leadingCoeff with hα
  set Q' := Q - C α * R with hQ'
  have hQ'coef : ∀ k, 2 * j ≤ k → Q'.coeff k = 0 := by
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · have hRc : R.coeff (2 * j) = R.leadingCoeff := by rw [Polynomial.leadingCoeff, hRdeg]
      rw [hQ', coeff_sub, coeff_C_mul, hRc, hα]; field_simp; ring
    · rw [hQ', coeff_sub, coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by omega),
        coeff_eq_zero_of_natDegree_lt (by omega)]; ring
  have hQ'sum : ∑ k ∈ range (H + 1), w H k * Rq (2 * H + 1) (2 * j) k * Q'.eval ((k : ℚ) * ((k : ℚ) - (2 * H + 1))) = 0 := by
    by_cases h0 : Q' = 0
    · simp [h0]
    · have : Q'.natDegree < 2 * j := by
        by_contra hc; push Not at hc
        exact (leadingCoeff_ne_zero.2 h0) (hQ'coef _ hc)
      exact orth_poly H (2 * j) (by omega) Q'.natDegree Q' rfl this
  have hsplit : ∀ x : ℚ, Q.eval x = Q'.eval x + α * R.eval x := by intro x; simp [hQ']
  have hRR : ∑ k ∈ range (H + 1), w H k * Rq (2 * H + 1) (2 * j) k * R.eval ((k : ℚ) * ((k : ℚ) - (2 * H + 1)))
      = hN H (2 * j) := by
    simp only [hN, ip, RR]
    refine sum_congr rfl fun k _ => ?_
    rw [show R.eval ((k : ℚ) * ((k : ℚ) - (2 * H + 1))) = Rq (2 * H + 1) (2 * j) k from RP_eval _ _ _]
  calc -4 * ∑ k ∈ range (H + 1), w H k * Rq (2 * H + 1) (2 * j) k * Q.eval ((k : ℚ) * ((k : ℚ) - (2 * H + 1)))
      = -4 * (∑ k ∈ range (H + 1), w H k * Rq (2 * H + 1) (2 * j) k * Q'.eval ((k : ℚ) * ((k : ℚ) - (2 * H + 1)))
          + α * ∑ k ∈ range (H + 1), w H k * Rq (2 * H + 1) (2 * j) k * R.eval ((k : ℚ) * ((k : ℚ) - (2 * H + 1)))) := by
        congr 1
        rw [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun k _ => ?_
        rw [hsplit]; ring
    _ = _ := by rw [hQ'sum, hRR, hα]; ring

end Bali.GR

#print axioms Bali.GR.skew_rows
#print axioms Bali.GR.skew_rows_zero
#print axioms Bali.GR.skew_rows_diag
