import P699.PsiAssemble
import P699.LeadQ2

/-! Lemma ψ with the leading coefficient of `Q` (Bali lab, 2026-11-01). -/

open Finset Polynomial

namespace Bali.PsiA
open Bali Bali.Skew Bali.Psi Bali.Even

theorem psi_skew_lead (H d : ℕ) (hd1 : 1 ≤ d) (hdH : d ≤ H) (G : ℚ[X]) (hG : G.natDegree ≤ d)
    (htot : totL (2 * H + 1) (G.comp (lam (((2 * H : ℕ) : ℚ) + 1))) = 0) (f : ℕ → ℚ) :
    ∃ Q : ℚ[X], Q.natDegree ≤ d - 1 ∧
      Q.coeff (d - 1) = G.coeff d * ((((2 * H : ℕ) : ℚ) + 1) + 1 - 2 * d) / 4 ∧
      skew (fun k : Fin (H + 1) => 2 * ((2 * H + 1).choose k : ℚ) * f k)
           (fun k : Fin (H + 1) => 2 * ((2 * H + 1).choose k : ℚ) * (G.comp (lam (((2 * H : ℕ) : ℚ) + 1))).eval (k : ℚ))
        = -4 * ∑ k ∈ range (H + 1), ((2 * H + 1).choose k : ℚ) ^ 2 * ((((2 * H : ℕ) : ℚ) + 1) - 2 * k) * f k *
            Q.eval ((k : ℚ) * ((k : ℚ) - (((2 * H : ℕ) : ℚ) + 1))) := by
  set m := 2 * H with hm
  set g := G.comp (lam ((m : ℚ) + 1)) with hgdef
  obtain ⟨Q, hQdeg, ⟨q, hphi, hN⟩, hlead⟩ := Bali.LeadQ.psi_lead m d hd1 (by omega) G hG htot
  refine ⟨Q, hQdeg, hlead, ?_⟩
  -- symmetry of g about n/2 at the integers
  have hgsym : ∀ x, x ≤ m + 1 → g.eval (x : ℚ) = g.eval ((m + 1 - x : ℕ) : ℚ) := by
    intro x hx
    have := congrArg (eval (x : ℚ)) (show g.comp (C ((m : ℚ) + 1) - X) = g by rw [hgdef, comp_assoc, lam_symm])
    rw [eval_comp] at this; simp only [eval_sub, eval_C, eval_X] at this
    rw [Nat.cast_sub hx]; push_cast; rw [← this]
  -- total over the shells is T g = 0
  have htotal : ∑ l : Fin (H + 1), 2 * ((2 * H + 1).choose l : ℚ) * g.eval (l : ℚ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun l => 2 * ((2 * H + 1).choose l : ℚ) * g.eval (l : ℚ)) (H + 1),
      shell_total H (fun x => g.eval (x : ℚ)) (by intro x hx; exact hgsym x (by omega))]
    rw [totL_apply] at htot
    simpa [hm] using htot
  rw [skew_of_total_zero _ _ htotal]
  have hk : ∀ k : Fin (H + 1),
      2 * ((2 * H + 1).choose (k : ℕ) : ℚ) * f k *
        (∑ l ∈ Iic k, 2 * ((2 * H + 1).choose (l : ℕ) : ℚ) * g.eval ((l : ℕ) : ℚ) +
         ∑ l ∈ Iio k, 2 * ((2 * H + 1).choose (l : ℕ) : ℚ) * g.eval ((l : ℕ) : ℚ))
      = 4 * (((2 * H + 1).choose (k : ℕ) : ℚ) ^ 2 * (((m : ℚ) + 1) - 2 * (k : ℕ)) * f k *
          Q.eval (((k : ℕ) : ℚ) * (((k : ℕ) : ℚ) - ((m : ℚ) + 1)))) := by
    intro k
    have hkm : (k : ℕ) ≤ m := by have := k.isLt; omega
    rw [sum_Iic_fin (fun x => 2 * ((2 * H + 1).choose x : ℚ) * g.eval (x : ℚ)) k,
      sum_Iio_fin (fun x => 2 * ((2 * H + 1).choose x : ℚ) * g.eval (x : ℚ)) k]
    have hP : ∑ x ∈ range ((k : ℕ) + 1), 2 * ((2 * H + 1).choose x : ℚ) * g.eval (x : ℚ)
        = 2 * Psum (m + 1) (fun x => g.eval (x : ℚ)) k := by
      rw [Psum, mul_sum]; exact sum_congr rfl fun x _ => by rw [hm]; ring
    have hP' : ∑ x ∈ range (k : ℕ), 2 * ((2 * H + 1).choose x : ℚ) * g.eval (x : ℚ)
        = 2 * (if (k : ℕ) = 0 then 0 else Psum (m + 1) (fun x => g.eval (x : ℚ)) ((k : ℕ) - 1)) := by
      split_ifs with h0
      · rw [h0]; simp
      · obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = j + 1 := ⟨(k : ℕ) - 1, by omega⟩
        rw [hj, Nat.add_sub_cancel, Psum, mul_sum]; exact sum_congr rfl fun x _ => by rw [hm]; ring
    rw [hP, hP', ← mul_add, bracket_Q m g q Q hphi hN k hkm, hm]
    ring
  rw [sum_congr rfl fun k _ => hk k, ← mul_sum,
    Fin.sum_univ_eq_sum_range (fun k => ((2 * H + 1).choose k : ℚ) ^ 2 * (((m : ℚ) + 1) - 2 * k) * f k *
      Q.eval ((k : ℚ) * ((k : ℚ) - ((m : ℚ) + 1)))) (H + 1)]
  rw [hm]; push_cast; ring

end Bali.PsiA

#print axioms Bali.PsiA.psi_skew_lead
