import P699.Christoffel
import P699.LeadQ2

/-!
# Even `n`: the diagonal of the skew Gram, and the explicit data of `p_a` (Bali lab, 2026-11-02)
-/

open Finset Polynomial

namespace Bali.EvenPsi
open Bali Bali.Skew Bali.Psi Bali.Even Bali.PsiA

/-- **Lemma ψ, even `n = 2K+2`**, for `g = G(λ)` vanishing at the centre. -/
theorem psi_skew_even_lead (K d : ℕ) (hd1 : 1 ≤ d) (hdK : d ≤ K) (G : ℚ[X]) (hG : G.natDegree ≤ d)
    (htot : totL (2 * K + 1 + 1) (G.comp (lam (((2 * K + 1 : ℕ) : ℚ) + 1))) = 0)
    (hc : (G.comp (lam (((2 * K + 1 : ℕ) : ℚ) + 1))).eval ((K : ℚ) + 1) = 0) (f : ℕ → ℚ) :
    ∃ Q : ℚ[X], Q.natDegree ≤ d - 1 ∧
      Q.coeff (d - 1) = G.coeff d * ((((2 * K + 1 : ℕ) : ℚ) + 1) + 1 - 2 * d) / 4 ∧
      skew (fun k : Fin (K + 1) => 2 * ((2 * K + 1 + 1).choose k : ℚ) * f k)
           (fun k : Fin (K + 1) => 2 * ((2 * K + 1 + 1).choose k : ℚ) *
              (G.comp (lam (((2 * K + 1 : ℕ) : ℚ) + 1))).eval (k : ℚ))
        = -4 * ∑ k ∈ range (K + 1), ((2 * K + 1 + 1).choose k : ℚ) ^ 2 *
            ((((2 * K + 1 : ℕ) : ℚ) + 1) - 2 * k) * f k *
            Q.eval ((k : ℚ) * ((k : ℚ) - (((2 * K + 1 : ℕ) : ℚ) + 1))) := by
  set m := 2 * K + 1 with hm
  set g := G.comp (lam ((m : ℚ) + 1)) with hgdef
  obtain ⟨Q, hQdeg, ⟨q, hphi, hN⟩, hlead⟩ := Bali.LeadQ.psi_lead m d hd1 (by omega) G hG htot
  refine ⟨Q, hQdeg, hlead, ?_⟩
  have hgsym : ∀ x, x ≤ m + 1 → g.eval (x : ℚ) = g.eval ((m + 1 - x : ℕ) : ℚ) := by
    intro x hx
    have := congrArg (eval (x : ℚ)) (show g.comp (C ((m : ℚ) + 1) - X) = g by rw [hgdef, comp_assoc, lam_symm])
    rw [eval_comp] at this; simp only [eval_sub, eval_C, eval_X] at this
    rw [Nat.cast_sub hx]; push_cast; rw [← this]
  have htotal : ∑ l : Fin (K + 1), 2 * ((m + 1).choose l : ℚ) * g.eval (l : ℚ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun l => 2 * ((m + 1).choose l : ℚ) * g.eval (l : ℚ)) (K + 1),
      shell_total_even K (fun x => g.eval (x : ℚ)) (by intro x hx; exact hgsym x (by omega))
        (by simpa using hc)]
    rw [totL_apply] at htot
    simpa using htot
  rw [skew_of_total_zero _ _ htotal]
  have hk : ∀ k : Fin (K + 1),
      2 * ((m + 1).choose (k : ℕ) : ℚ) * f k *
        (∑ l ∈ Iic k, 2 * ((m + 1).choose (l : ℕ) : ℚ) * g.eval ((l : ℕ) : ℚ) +
         ∑ l ∈ Iio k, 2 * ((m + 1).choose (l : ℕ) : ℚ) * g.eval ((l : ℕ) : ℚ))
      = 4 * (((m + 1).choose (k : ℕ) : ℚ) ^ 2 * (((m : ℚ) + 1) - 2 * (k : ℕ)) * f k *
          Q.eval (((k : ℕ) : ℚ) * (((k : ℕ) : ℚ) - ((m : ℚ) + 1)))) := by
    intro k
    have hkm : (k : ℕ) ≤ m := by have := k.isLt; omega
    rw [sum_Iic_fin (fun x => 2 * ((m + 1).choose x : ℚ) * g.eval (x : ℚ)) k,
      sum_Iio_fin (fun x => 2 * ((m + 1).choose x : ℚ) * g.eval (x : ℚ)) k]
    have hP : ∑ x ∈ range ((k : ℕ) + 1), 2 * ((m + 1).choose x : ℚ) * g.eval (x : ℚ)
        = 2 * Psum (m + 1) (fun x => g.eval (x : ℚ)) k := by
      rw [Psum, mul_sum]; exact sum_congr rfl fun x _ => by ring
    have hP' : ∑ x ∈ range (k : ℕ), 2 * ((m + 1).choose x : ℚ) * g.eval (x : ℚ)
        = 2 * (if (k : ℕ) = 0 then 0 else Psum (m + 1) (fun x => g.eval (x : ℚ)) ((k : ℕ) - 1)) := by
      split_ifs with h0
      · rw [h0]; simp
      · obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = j + 1 := ⟨(k : ℕ) - 1, by omega⟩
        rw [hj, Nat.add_sub_cancel, Psum, mul_sum]; exact sum_congr rfl fun x _ => by ring
    rw [hP, hP', ← mul_add, bracket_Q m g q Q hphi hN k hkm]
    ring
  rw [sum_congr rfl fun k _ => hk k, ← mul_sum,
    Fin.sum_univ_eq_sum_range (fun k => ((m + 1).choose k : ℚ) ^ 2 * (((m : ℚ) + 1) - 2 * k) * f k *
      Q.eval ((k : ℚ) * ((k : ℚ) - ((m : ℚ) + 1)))) (K + 1)]
  ring


lemma skew_self {N : ℕ} (f : Fin (N + 1) → ℚ) : skew f f = 0 := by
  have h := skew_col f f
  have h2 : skew f f = -∑ l, f l * (∑ k ∈ Iio l, f k - ∑ k ∈ Ioi l, f k) := by
    unfold skew
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun k _ => by ring
  linarith

lemma ipW_lin (K : ℕ) (p R : ℚ[X]) (α : ℚ) (S : ℚ[X]) :
    ipW K p (C α * S + R) = α * ipW K p S + ipW K p R := by
  unfold ipW
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  simp only [eval_add, eval_mul, eval_C]
  ring

/-- `ipW p Q` only sees the coefficient of `p` in `Q`, for `deg Q ≤ b`. -/
lemma ipW_lead (K b : ℕ) (hb1 : 1 ≤ b) (p Q : ℚ[X]) (hp : p.natDegree ≤ b) (hQ : Q.natDegree ≤ b)
    (hlc : p.coeff b ≠ 0) (horth : ∀ R : ℚ[X], R.natDegree < b → ipW K p R = 0) :
    p.coeff b * ipW K p Q = Q.coeff b * ipW K p p := by
  set α := Q.coeff b / p.coeff b with hα
  set R := Q - C α * p with hR
  have hRdeg : R.natDegree < b := by
    have hle : R.natDegree ≤ b :=
      (natDegree_sub_le _ _).trans (max_le hQ ((natDegree_C_mul_le _ _).trans hp))
    have hc : R.coeff b = 0 := by
      simp only [hR, coeff_sub, coeff_C_mul, hα]; field_simp; ring
    rcases Nat.lt_or_ge R.natDegree b with h | h
    · exact h
    · have he : R.natDegree = b := by omega
      by_cases h0 : R = 0
      · rw [h0]; simpa using (by omega : 0 < b)
      · exact absurd (by rw [← he] at hc; exact leadingCoeff_eq_zero.1 hc) h0
  have hsplit : Q = C α * p + R := by simp [hR]
  rw [hsplit, ipW_lin, horth R hRdeg, add_zero]
  have hcq : (C α * p + R).coeff b = α * p.coeff b := by
    rw [coeff_add, coeff_C_mul, coeff_eq_zero_of_natDegree_lt hRdeg, add_zero]
  rw [hcq]; ring

/-- **The diagonal.** `T(p_b) ⟨p_b, p_0⟩_B = 4 T(p_0) (n-1-2b) ⟨p_b,p_b⟩_W`. -/
theorem diag_B (K : ℕ) (p : ℕ → ℚ[X]) (hdeg : ∀ a, (p a).natDegree ≤ a)
    (horth : ∀ a (Q : ℚ[X]), Q.natDegree < a → ipW K (p a) Q = 0)
    (b : ℕ) (hb1 : 1 ≤ b) (hbK : b + 1 ≤ K) (hlc : (p b).coeff b ≠ 0) :
    TB K (p b) * skew (rowB K (p b)) (rowB K (p 0))
      = 4 * TB K (p 0) * (nQ K - 1 - 2 * b) * ipW K (p b) (p b) := by
  set gt : ℚ[X] := C (TB K (p 0)) * p b - C (TB K (p b)) * p 0 with hgt
  have h2 : gt.natDegree ≤ b := by
    rw [hgt]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_C_mul_le _ _).trans (hdeg b)
    · exact (natDegree_C_mul_le _ _).trans ((hdeg 0).trans (Nat.zero_le _))
  have hdeg_gt : (Ylam K * gt).natDegree ≤ b + 1 := by
    have h1 : (Ylam K).natDegree ≤ 1 := by
      unfold Ylam; compute_degree!
    calc (Ylam K * gt).natDegree ≤ (Ylam K).natDegree + gt.natDegree := natDegree_mul_le
      _ ≤ b + 1 := by omega
  have htot : totL (2 * K + 1 + 1) ((Ylam K * gt).comp (lam (((2 * K + 1 : ℕ) : ℚ) + 1))) = 0 := by
    rw [hgt]
    simp only [mul_sub, sub_comp, mul_comp, C_comp, map_sub]
    have e1 : ∀ c (r : ℚ[X]), totL (2 * K + 1 + 1) ((Ylam K).comp (lam (nQ K)) * (C c * r.comp (lam (nQ K))))
        = c * TB K r := by
      intro c r
      rw [TB, mul_comp, show (Ylam K).comp (lam (nQ K)) * (C c * r.comp (lam (nQ K)))
        = C c * ((Ylam K).comp (lam (nQ K)) * r.comp (lam (nQ K))) by ring, ← smul_eq_C_mul, map_smul, smul_eq_mul]
    rw [e1, e1]; ring
  have hc : ((Ylam K * gt).comp (lam (((2 * K + 1 : ℕ) : ℚ) + 1))).eval ((K : ℚ) + 1) = 0 := by
    rw [mul_comp, eval_mul]
    have := Ylam_centre K
    simp only [nQ] at this
    rw [this, zero_mul]
  obtain ⟨Q, hQ, hQlead, hpsi⟩ := psi_skew_even_lead K (b + 1) (by omega) hbK (Ylam K * gt) hdeg_gt htot hc
    (fun k => ((Ylam K * p b).comp (lam (nQ K))).eval (k : ℚ))
  have hlhs : skew (rowB K (p b)) (fun k : Fin (K + 1) => 2 * ((2 * K + 1 + 1).choose k : ℚ) *
      ((Ylam K * gt).comp (lam (((2 * K + 1 : ℕ) : ℚ) + 1))).eval (k : ℚ))
      = TB K (p 0) * skew (rowB K (p b)) (rowB K (p b)) - TB K (p b) * skew (rowB K (p b)) (rowB K (p 0)) := by
    rw [← skew_lin2]
    congr 1
    funext l
    simp only [rowB, hgt, mul_sub, sub_comp, mul_comp, C_comp, eval_sub, eval_mul, eval_C, nQ]
    ring
  have hQb : Q.coeff b = TB K (p 0) * (p b).coeff b * (nQ K - 1 - 2 * b) := by
    have hG : (Ylam K * gt).coeff (b + 1) = 4 * (TB K (p 0) * (p b).coeff b) := by
      have hz : gt.coeff (b + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      have hz0 : (p 0).coeff b = 0 := coeff_eq_zero_of_natDegree_lt (by have := hdeg 0; omega)
      have hgb : gt.coeff b = TB K (p 0) * (p b).coeff b := by
        simp only [hgt, coeff_sub, coeff_C_mul, hz0]; ring
      simp only [Ylam, add_mul, coeff_add, coeff_C_mul, mul_assoc, coeff_X_mul, hz, hgb]
      ring
    simp only [Nat.add_sub_cancel] at hQ hQlead
    rw [hQlead, hG]
    simp only [nQ]; push_cast; ring
  have hpow := ipW_lead K b hb1 (p b) Q (hdeg b) (by simpa using hQ) hlc (fun R hR => horth b R hR)
  have hpsi' := hpsi
  rw [show (fun k : Fin (K + 1) => 2 * ((2 * K + 1 + 1).choose k : ℚ) *
      ((Ylam K * p b).comp (lam (nQ K))).eval (k : ℚ)) = rowB K (p b) from rfl, hlhs, skew_self] at hpsi'
  have hsum : ipW K (p b) Q = TB K (p 0) * (nQ K - 1 - 2 * b) * ipW K (p b) (p b) := by
    apply mul_left_cancel₀ hlc
    rw [hpow, hQb]; ring
  have hp3 : TB K (p 0) * 0 - TB K (p b) * skew (rowB K (p b)) (rowB K (p 0)) = -4 * ipW K (p b) Q := hpsi'
  linear_combination -hp3 + 4 * hsum

end Bali.EvenPsi

namespace Bali.Chr
open Bali.Racah Bali.RE Bali.REO

/-! explicit data of `p_a` -/

/-- leading coefficient of `p_a`: `R_a(m) ℓ_{a+1}`. -/
lemma pK_coeff (m a : ℕ) : (pK m a).coeff a = RE m a (m : ℚ) * (RPE m (a + 1)).coeff (a + 1) := by
  have h := congrArg (fun r : ℚ[X] => r.coeff (a + 1)) (mul_pK m a)
  simp only [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul] at h
  have hz : (pK m a).coeff (a + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by have := pK_le m a; omega)
  have hz2 : (RPE m a).coeff (a + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by have := RPE_le m a; omega)
  simp only [Nk, coeff_sub, coeff_C_mul, hz, hz2] at h
  linarith

/-- `T(p_a) = 4 (R_a(m) S_{a+1} - R_{a+1}(m) S_a)`, `S_a = Σ_x C(n,x) R_a(x)`. -/
lemma TB_pK (K a : ℕ) : Bali.EvenPsi.TB K (pK (K + 1) a)
    = 4 * (RE (K + 1) a ((K + 1 : ℕ) : ℚ) * ∑ x ∈ range (2 * (K + 1) + 1), ((2 * (K + 1)).choose x : ℚ) * RE (K + 1) (a + 1) x
        - RE (K + 1) (a + 1) ((K + 1 : ℕ) : ℚ) * ∑ x ∈ range (2 * (K + 1) + 1), ((2 * (K + 1)).choose x : ℚ) * RE (K + 1) a x) := by
  unfold Bali.EvenPsi.TB
  rw [Y_pK, Bali.totL_apply, show 2 * K + 1 + 1 = 2 * (K + 1) by ring, mul_sum, mul_sum, ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring] at *
  rw [lam_eval]
  simp only [Nk, eval_mul, eval_C, eval_sub, RPE_eval]
  ring

end Bali.Chr

#print axioms Bali.EvenPsi.diag_B
#print axioms Bali.Chr.pK_coeff
#print axioms Bali.Chr.TB_pK
