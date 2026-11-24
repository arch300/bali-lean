import P699.SkewPsi
import P699.PsiPoly

/-!
# Lemma ψ assembled (Bali lab, 2026-11-01)
`skew (ν f) (ν g) = -4 Σ_{k≤H} C(n,k)^2 (n-2k) f_k Q(λ(k))` for `g = G(λ)`, `T g = 0`, `n = 2H+1`.
-/

open Finset Polynomial

namespace Bali.PsiA
open Bali Bali.Skew Bali.Psi Bali.Even

/-- sum over `Iic k` in `Fin (N+1)` is a sum over `range (k+1)`. -/
lemma sum_Iic_fin {N : ℕ} (F : ℕ → ℚ) (k : Fin (N + 1)) :
    ∑ l ∈ Iic k, F (l : ℕ) = ∑ x ∈ range ((k : ℕ) + 1), F x := by
  refine sum_bij (fun l _ => (l : ℕ))
    (fun l hl => mem_range.2 (Nat.lt_succ_of_le (Fin.le_iff_val_le_val.1 (mem_Iic.1 hl))))
    (fun a _ b _ h => Fin.ext h)
    (fun x hx => ⟨⟨x, by have := mem_range.1 hx; omega⟩,
      mem_Iic.2 (Fin.le_iff_val_le_val.2 (by have := mem_range.1 hx; simp; omega)), rfl⟩)
    (fun _ _ => rfl)

lemma sum_Iio_fin {N : ℕ} (F : ℕ → ℚ) (k : Fin (N + 1)) :
    ∑ l ∈ Iio k, F (l : ℕ) = ∑ x ∈ range (k : ℕ), F x := by
  refine sum_bij (fun l _ => (l : ℕ))
    (fun l hl => mem_range.2 (Fin.lt_iff_val_lt_val.1 (mem_Iio.1 hl)))
    (fun a _ b _ h => Fin.ext h)
    (fun x hx => ⟨⟨x, by have := mem_range.1 hx; have := k.isLt; omega⟩,
      mem_Iio.2 (Fin.lt_iff_val_lt_val.2 (by have := mem_range.1 hx; simp; omega)), rfl⟩)
    (fun _ _ => rfl)

/-- shells: `Σ_{h ≤ H} 2 C(n,h) g(h) = Σ_{x ≤ n} C(n,x) g(x)` for `g` symmetric about `n/2`, `n = 2H+1`. -/
lemma shell_total (H : ℕ) (g : ℕ → ℚ) (hsym : ∀ x, x ≤ 2 * H + 1 → g x = g (2 * H + 1 - x)) :
    ∑ h ∈ range (H + 1), 2 * ((2 * H + 1).choose h : ℚ) * g h
      = ∑ x ∈ range (2 * H + 1 + 1), ((2 * H + 1).choose x : ℚ) * g x := by
  rw [show 2 * H + 1 + 1 = (H + 1) + (H + 1) by ring,
    sum_range_add (fun x => ((2 * H + 1).choose x : ℚ) * g x) (H + 1) (H + 1)]
  have hrefl : ∑ x ∈ range (H + 1), ((2 * H + 1).choose (H + 1 + x) : ℚ) * g (H + 1 + x)
      = ∑ x ∈ range (H + 1), ((2 * H + 1).choose x : ℚ) * g x := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun x hx => ?_
    have hx' := mem_range.1 hx
    have e : H + 1 + (H + 1 - 1 - x) = 2 * H + 1 - x := by omega
    rw [e, Nat.choose_symm (by omega), hsym x (by omega)]
  rw [hrefl, ← sum_add_distrib]
  exact sum_congr rfl fun x _ => by ring


/-- `qG = n · q` at the integers, from Gosper's partial-sum identity. -/
lemma qG_eq (m : ℕ) (g q : ℚ[X]) (hphi : phiQ (m + 1) q = g) (h : ℕ) (hh : h ≤ m) :
    qG m (fun x => g.eval (x : ℚ)) h = ((m : ℚ) + 1) * q.eval (h : ℚ) := by
  have hrec : ∀ k : ℕ, ((m : ℚ) + 1 - k) * (((m : ℚ) + 1) * q.eval (k : ℚ)) - k * (((m : ℚ) + 1) * q.eval ((k - 1 : ℕ) : ℚ))
      = ((m : ℚ) + 1) * g.eval (k : ℚ) := by
    intro k
    rw [← hphi, phiQ_eval]
    rcases k with _ | k
    · simp <;> ring
    · push_cast; simp only [add_sub_cancel_right]; ring
  have := gosper_partial_sum m (fun x => g.eval (x : ℚ)) (fun k => ((m : ℚ) + 1) * q.eval (k : ℚ)) hrec h
  have hc : (m.choose h : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hh).ne'
  simp only [qG, Psum]
  rw [this]; field_simp

/-- the bracket in closed form: `P_k + P_{k-1} = C(n,k)(n-2k) Q(λ(k))` (with `P_{-1} = 0`). -/
lemma bracket_Q (m : ℕ) (g q Q : ℚ[X]) (hphi : phiQ (m + 1) q = g)
    (hN : C 2 * (C ((m : ℚ) + 1) - X) * q - g = (C ((m : ℚ) + 1) - C 2 * X) * Q.comp (lam ((m : ℚ) + 1)))
    (k : ℕ) (hk : k ≤ m) :
    Psum (m + 1) (fun x => g.eval (x : ℚ)) k + (if k = 0 then 0 else Psum (m + 1) (fun x => g.eval (x : ℚ)) (k - 1))
      = ((m + 1).choose k : ℚ) * (((m : ℚ) + 1) - 2 * k) * Q.eval ((k : ℚ) * ((k : ℚ) - ((m : ℚ) + 1))) := by
  have hNk := congrArg (eval (k : ℚ)) hN
  simp only [eval_sub, eval_mul, eval_C, eval_X, eval_comp, lam] at hNk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · -- k = 0: q(0) = g(0)/n
    have h0 := congrArg (eval (0 : ℚ)) hphi
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


/-- **Lemma ψ.**  For `g = G(λ)` with `1 ≤ deg-bound d ≤ H` and `T g = 0`, and any `f`,
`⟨ν f, ν g⟩ = -4 Σ_{k ≤ H} C(n,k)^2 (n - 2k) f(k) Q(λ(k))` with `deg Q ≤ d - 1` (`n = 2H + 1`). -/
theorem psi_skew (H d : ℕ) (hd1 : 1 ≤ d) (hdH : d ≤ H) (G : ℚ[X]) (hG : G.natDegree ≤ d)
    (htot : totL (2 * H + 1) (G.comp (lam (((2 * H : ℕ) : ℚ) + 1))) = 0) (f : ℕ → ℚ) :
    ∃ Q : ℚ[X], Q.natDegree ≤ d - 1 ∧
      skew (fun k : Fin (H + 1) => 2 * ((2 * H + 1).choose k : ℚ) * f k)
           (fun k : Fin (H + 1) => 2 * ((2 * H + 1).choose k : ℚ) * (G.comp (lam (((2 * H : ℕ) : ℚ) + 1))).eval (k : ℚ))
        = -4 * ∑ k ∈ range (H + 1), ((2 * H + 1).choose k : ℚ) ^ 2 * ((((2 * H : ℕ) : ℚ) + 1) - 2 * k) * f k *
            Q.eval ((k : ℚ) * ((k : ℚ) - (((2 * H : ℕ) : ℚ) + 1))) := by
  set m := 2 * H with hm
  set g := G.comp (lam ((m : ℚ) + 1)) with hgdef
  obtain ⟨q, hphi, -, -, Q, hQdeg, hN⟩ := psi_poly m d hd1 (by omega) G hG htot
  refine ⟨Q, hQdeg, ?_⟩
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

#print axioms Bali.PsiA.shell_total
#print axioms Bali.PsiA.bracket_Q
#print axioms Bali.PsiA.psi_skew
