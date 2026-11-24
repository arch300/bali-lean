import P699.BplusPsi

/-!
# Type B⁺: the skew product is rank one up to an orthogonal correction (Bali lab, 2026-11-02)
`skew(ν' f, ν' G) = T(f) T(G) - 4 Σ_k C(n,k)^2 f_k M(λ_k)` with `deg M ≤ deg G`, `n = m+1`, shells `k ≤ N`, `2N ≤ m`.
-/

open Finset Polynomial

namespace Bali.BP
open Bali Bali.Even Bali.Psi Bali.Skew Bali.PsiA

lemma skew_total {N : ℕ} (f g : Fin (N + 1) → ℚ) :
    skew f g = (∑ k, f k) * (∑ l, g l) - ∑ k, f k * (∑ l ∈ Iic k, g l + ∑ l ∈ Iio k, g l) := by
  classical
  unfold skew
  rw [sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  have hsplit : ∑ l ∈ Ioi k, g l + ∑ l ∈ Iic k, g l = ∑ l, g l := by
    rw [← sum_union (disjoint_left.2 fun l h1 h2 => by
      simp only [mem_Ioi, mem_Iic] at h1 h2; exact absurd h1 (not_lt_of_ge h2))]
    congr 1; ext l
    simp only [mem_union, mem_Ioi, mem_Iic, mem_univ, iff_true]
    exact lt_or_ge k l
  linear_combination f k * hsplit

lemma bracket_M (m : ℕ) (g q M : ℚ[X]) (hphi : phiQ (m + 1) q = g)
    (hN : C 2 * (C ((m : ℚ) + 1) - X) * q - g = M.comp (lam ((m : ℚ) + 1)))
    (k : ℕ) (hk : k ≤ m) :
    Psum (m + 1) (fun x => g.eval (x : ℚ)) k + (if k = 0 then 0 else Psum (m + 1) (fun x => g.eval (x : ℚ)) (k - 1))
      = ((m + 1).choose k : ℚ) * M.eval ((k : ℚ) * ((k : ℚ) - ((m : ℚ) + 1))) := by
  have hNk := congrArg (eval (k : ℚ)) hN
  simp only [eval_sub, eval_mul, eval_C, eval_X, eval_comp, lam] at hNk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · have h0 := congrArg (eval (0 : ℚ)) hphi
    rw [phiQ_eval] at h0
    simp only [Psum, if_true, add_zero, sum_range_one, Nat.choose_zero_right, Nat.cast_one, one_mul]
    push_cast at h0 hNk ⊢
    simp at h0 hNk ⊢
    linarith
  · rw [if_neg (by omega), bracket_eq m _ k hpos hk, qG_eq m g q hphi k hk]
    have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    push_cast at hNk
    linear_combination ((m + 1).choose k : ℚ) * hNk

/-- **rank one + orthogonal correction.** -/
theorem skew_rank1 (m N d : ℕ) (hN : 2 * N ≤ m) (hdm : 2 * d + 1 ≤ m) (G : ℚ[X]) (hG : G.natDegree ≤ d)
    (f : ℕ → ℚ) :
    ∃ M : ℚ[X], M.natDegree ≤ d ∧
      skew (fun k : Fin (N + 1) => 2 * ((m + 1).choose k : ℚ) * f k)
           (fun k : Fin (N + 1) => 2 * ((m + 1).choose k : ℚ) * (phiO ((m : ℚ) + 1) G).eval (k : ℚ))
        = (∑ k ∈ range (N + 1), 2 * ((m + 1).choose k : ℚ) * f k)
            * (∑ k ∈ range (N + 1), 2 * ((m + 1).choose k : ℚ) * (phiO ((m : ℚ) + 1) G).eval (k : ℚ))
          - 4 * ∑ k ∈ range (N + 1), ((m + 1).choose k : ℚ) ^ 2 * f k *
              M.eval ((k : ℚ) * ((k : ℚ) - ((m : ℚ) + 1))) := by
  set g := phiO ((m : ℚ) + 1) G with hgdef
  obtain ⟨q, hphi, M, hMdeg, hNM⟩ := psi_poly_odd m d hdm G hG
  refine ⟨M, hMdeg, ?_⟩
  rw [skew_total]
  have hk : ∀ k : Fin (N + 1),
      2 * ((m + 1).choose (k : ℕ) : ℚ) * f k *
        (∑ l ∈ Iic k, 2 * ((m + 1).choose (l : ℕ) : ℚ) * g.eval ((l : ℕ) : ℚ) +
         ∑ l ∈ Iio k, 2 * ((m + 1).choose (l : ℕ) : ℚ) * g.eval ((l : ℕ) : ℚ))
      = 4 * (((m + 1).choose (k : ℕ) : ℚ) ^ 2 * f k *
          M.eval (((k : ℕ) : ℚ) * (((k : ℕ) : ℚ) - ((m : ℚ) + 1)))) := by
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
    rw [hP, hP', ← mul_add, bracket_M m g q M hphi hNM k hkm]
    ring
  rw [sum_congr rfl fun k _ => hk k, ← mul_sum,
    Fin.sum_univ_eq_sum_range (fun k => 2 * ((m + 1).choose k : ℚ) * f k) (N + 1),
    Fin.sum_univ_eq_sum_range (fun k => 2 * ((m + 1).choose k : ℚ) * g.eval (k : ℚ)) (N + 1),
    Fin.sum_univ_eq_sum_range (fun k => ((m + 1).choose k : ℚ) ^ 2 * f k *
      M.eval ((k : ℚ) * ((k : ℚ) - ((m : ℚ) + 1)))) (N + 1)]

end Bali.BP

#print axioms Bali.BP.skew_rank1
