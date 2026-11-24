import Mathlib

/-!
# Polynomials symmetric about `n/2` are polynomials in `λ = x (x - n)` (Bali lab, 2026-11-01)
-/

open Polynomial

namespace Bali.Even

noncomputable def lam (n : ℚ) : ℚ[X] := X * (X - C n)

lemma lam_symm (n : ℚ) : (lam n).comp (C n - X) = lam n := by
  simp [lam]; ring

lemma lam_monic (n : ℚ) : (lam n).Monic := by
  unfold lam; exact monic_X.mul (monic_X_sub_C n)

lemma lam_natDegree (n : ℚ) : (lam n).natDegree = 2 := by
  unfold lam; rw [natDegree_mul X_ne_zero (X_sub_C_ne_zero n), natDegree_X, natDegree_X_sub_C]

lemma refl_eq (n : ℚ) : (C n - X : ℚ[X]) = -(X - C n) := by ring

lemma refl_natDegree (n : ℚ) : (C n - X : ℚ[X]).natDegree = 1 := by
  rw [refl_eq, natDegree_neg, natDegree_X_sub_C]

lemma refl_leading (n : ℚ) : (C n - X : ℚ[X]).leadingCoeff = -1 := by
  rw [refl_eq, leadingCoeff_neg, leadingCoeff_X_sub_C]

/-- a symmetric polynomial has even degree (or is zero). -/
lemma symm_not_odd (n : ℚ) (P : ℚ[X]) (hP : P.comp (C n - X) = P) (e : ℕ) (hd : P.natDegree = 2 * e + 1) :
    False := by
  have hlc := congrArg leadingCoeff hP
  rw [leadingCoeff_comp (by rw [refl_natDegree]; norm_num), refl_leading, hd] at hlc
  have hne : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 (by intro h; rw [h] at hd; simp at hd)
  rw [pow_succ, pow_mul] at hlc
  norm_num at hlc
  exact hne (by linarith)

theorem even_center (n : ℚ) : ∀ e : ℕ, ∀ P : ℚ[X], P.natDegree ≤ 2 * e → P.comp (C n - X) = P →
    ∃ Q : ℚ[X], Q.natDegree ≤ e ∧ P = Q.comp (lam n)
  | 0, P, hd, _ => ⟨P, by omega, by
      rw [eq_C_of_natDegree_eq_zero (by omega : P.natDegree = 0)]; simp⟩
  | e + 1, P, hd, hP => by
    set a := P.coeff (2 * e + 2)
    set P' := P - C a * (lam n) ^ (e + 1) with hP'
    have hlp : ((lam n) ^ (e + 1)).natDegree = 2 * e + 2 := by
      rw [natDegree_pow, lam_natDegree]; ring
    have hP'symm : P'.comp (C n - X) = P' := by
      simp only [hP', sub_comp, mul_comp, C_comp, pow_comp, lam_symm, hP]
    have hP'deg1 : P'.natDegree ≤ 2 * e + 1 := by
      have hle : P'.natDegree ≤ 2 * e + 2 := by
        apply (natDegree_sub_le _ _).trans
        apply max_le (by omega)
        exact (natDegree_C_mul_le _ _).trans hlp.le
      have hcoef : P'.coeff (2 * e + 2) = 0 := by
        rw [hP', coeff_sub, coeff_C_mul]
        have : ((lam n) ^ (e + 1)).coeff (2 * e + 2) = 1 := by
          have hm := (lam_monic n).pow (e + 1)
          rw [← hlp]; exact hm
        rw [this]; ring
      by_contra hcon
      push Not at hcon
      have : P'.natDegree = 2 * e + 2 := by omega
      rw [← this] at hcoef
      exact (leadingCoeff_ne_zero.2 (by intro h; rw [h] at this; simp at this)) hcoef
    have hP'deg : P'.natDegree ≤ 2 * e := by
      by_contra hcon; push Not at hcon
      exact symm_not_odd n P' hP'symm e (by omega)
    obtain ⟨Q', hQ'deg, hQ'⟩ := even_center n e P' hP'deg hP'symm
    refine ⟨Q' + C a * X ^ (e + 1), ?_, ?_⟩
    · apply (natDegree_add_le _ _).trans
      apply max_le (by omega)
      exact (natDegree_C_mul_le _ _).trans (by simp)
    · rw [add_comp, ← hQ', mul_comp, C_comp, X_pow_comp, hP']; ring


lemma key1 (n : ℚ) : (C n - C 2 * X : ℚ[X]) * C (-1 / 2) = X - C (n / 2) := by
  ext k
  simp only [coeff_mul_C, coeff_sub, coeff_C, coeff_C_mul, coeff_X]
  split_ifs <;> ring

lemma key2 (n : ℚ) : (C n - C 2 * X : ℚ[X]).comp (C n - X) = -(C n - C 2 * X) := by
  simp only [sub_comp, C_comp, mul_comp, X_comp]
  ext k
  simp only [coeff_sub, coeff_neg, coeff_C, coeff_C_mul, coeff_X]
  split_ifs <;> ring

/-- an antisymmetric polynomial is `(n - 2x)` times a symmetric one. -/
theorem odd_center (n : ℚ) (N : ℚ[X]) (hN : N.comp (C n - X) = -N) (h0 : N ≠ 0) :
    ∃ M : ℚ[X], N = (C n - C 2 * X) * M ∧ M.comp (C n - X) = M ∧ M.natDegree + 1 ≤ N.natDegree := by
  have hroot : N.IsRoot (n / 2) := by
    have := congrArg (eval (n / 2)) hN
    simp only [eval_comp, eval_sub, eval_C, eval_X, eval_neg] at this
    have h2 : n - n / 2 = n / 2 := by ring
    rw [h2] at this
    show N.eval (n / 2) = 0
    linarith
  set D := N /ₘ (X - C (n / 2))
  have hND : (X - C (n / 2)) * D = N := mul_divByMonic_eq_iff_isRoot.2 hroot
  refine ⟨C (-1 / 2) * D, ?_, ?_, ?_⟩
  · rw [← hND]
    have : (C n - C 2 * X : ℚ[X]) * C (-1 / 2) = X - C (n / 2) := key1 n
    rw [← mul_assoc, this]
  · -- symmetry of M by cancelling the nonzero factor (n - 2x)
    have hfac : (C n - C 2 * X : ℚ[X]) ≠ 0 := by
      intro h; have := congrArg natDegree h
      rw [show (C n - C 2 * X : ℚ[X]) = C (-2) * X + C n by rw [C_neg]; ring,
        natDegree_add_C, natDegree_C_mul (by norm_num), natDegree_X] at this; simp at this
    have hNfac : N = (C n - C 2 * X) * (C (-1 / 2) * D) := by
      rw [← hND]
      have : (C n - C 2 * X : ℚ[X]) * C (-1 / 2) = X - C (n / 2) := key1 n
      rw [← mul_assoc, this]
    have := hN
    rw [hNfac, mul_comp] at this
    have hfc : (C n - C 2 * X : ℚ[X]).comp (C n - X) = -(C n - C 2 * X) := key2 n
    rw [hfc, neg_mul, neg_inj] at this
    exact mul_left_cancel₀ hfac this
  · have hD0 : D ≠ 0 := by intro h; rw [h, mul_zero] at hND; exact h0 hND.symm
    rw [← hND, natDegree_mul (X_sub_C_ne_zero _) hD0, natDegree_X_sub_C,
      natDegree_C_mul (by norm_num)]
    omega

end Bali.Even

#print axioms Bali.Even.even_center
#print axioms Bali.Even.odd_center
