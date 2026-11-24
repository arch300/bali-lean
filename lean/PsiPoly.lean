import P699.Gosper
import P699.EvenCenter

/-!
# Lemma ψ, step (b3): `2(n-x) q - g = (n - 2x) · Q(λ)` with `deg Q < d` (Bali lab, 2026-11-01)
-/

open Polynomial Finset

namespace Bali.Psi
open Bali Bali.Even

/-- polynomial antisymmetry of the Gosper solution: `q(m - x) = -q(x)`. -/
theorem q_antisymm_poly (m D : ℕ) (hD : D ≤ m) (g q : ℚ[X]) (hq : q ∈ degreeLT ℚ D)
    (hphi : phiQ (m + 1) q = g) (hgsym : g.comp (C ((m : ℚ) + 1) - X) = g) :
    q.comp (C (m : ℚ) - X) = -q := by
  -- integer antisymmetry from gosper_antisymm
  have hrec : ∀ k : ℕ, ((m : ℚ) + 1 - k) * q.eval (k : ℚ) - k * q.eval ((k - 1 : ℕ) : ℚ)
      = ((m : ℚ) + 1) * (g.eval (k : ℚ) / ((m : ℚ) + 1)) := by
    intro k
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ hm, ← hphi, phiQ_eval]
    rcases k with _ | k
    · simp
    · push_cast; simp only [add_sub_cancel_right]
  have hsym : ∀ k, k ≤ m + 1 → g.eval (k : ℚ) / ((m : ℚ) + 1) = g.eval ((m + 1 - k : ℕ) : ℚ) / ((m : ℚ) + 1) := by
    intro k hk
    have := congrArg (eval (k : ℚ)) hgsym
    rw [eval_comp] at this
    simp only [eval_sub, eval_C, eval_X] at this
    rw [Nat.cast_sub hk]; push_cast
    rw [← this]
  have hint := gosper_antisymm m (fun k => g.eval (k : ℚ) / ((m : ℚ) + 1)) (fun k => q.eval (k : ℚ)) hrec hsym
  -- the difference vanishes at 0..m and has degree < m+1
  set r := q.comp (C (m : ℚ) - X) + q with hr
  have hqdeg : q.natDegree < m + 1 := by
    by_cases h : q = 0
    · simp [h]
    · have := (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hq); omega
  have hrdeg : r.natDegree < m + 1 := by
    apply lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ hqdeg)
    apply lt_of_le_of_lt natDegree_comp_le
    rw [show (C (m : ℚ) - X) = -(X - C (m : ℚ)) by ring, natDegree_neg, natDegree_X_sub_C, mul_one]; exact hqdeg
  have hr0 : r = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero r (f := fun i : Fin (m + 1) => ((i : ℕ) : ℚ))
      (fun a b h => Fin.ext (by exact_mod_cast (show ((a : ℕ) : ℚ) = b from h)))
    · intro i
      have hi := hint i (by omega)
      simp only [hr, eval_add, eval_comp, eval_sub, eval_C, eval_X]
      have : (m : ℚ) - (i : ℕ) = ((m - (i : ℕ) : ℕ) : ℚ) := by rw [Nat.cast_sub (by omega)]
      rw [this]; linarith
    · simpa using hrdeg
  linear_combination hr0


/-- **(b3)**  For `g = G(λ)` with `deg G ≤ d`, `1 ≤ d`, `2d ≤ m`, `T g = 0`: the Gosper solution `q` satisfies
`2(n-x) q(x) - g(x) = (n - 2x) · Q(λ(x))` with `deg Q ≤ d - 1` (`n = m + 1`). -/
theorem psi_poly (m d : ℕ) (hd1 : 1 ≤ d) (hdm : 2 * d ≤ m) (G : ℚ[X]) (hG : G.natDegree ≤ d)
    (htot : totL (m + 1) (G.comp (lam ((m : ℚ) + 1))) = 0) :
    ∃ q : ℚ[X], phiQ (m + 1) q = G.comp (lam ((m : ℚ) + 1)) ∧
      q.natDegree ≤ 2 * d - 1 ∧ q.comp (C (m : ℚ) - X) = -q ∧
      ∃ Q : ℚ[X], Q.natDegree ≤ d - 1 ∧
        C 2 * (C ((m : ℚ) + 1) - X) * q - G.comp (lam ((m : ℚ) + 1))
          = (C ((m : ℚ) + 1) - C 2 * X) * Q.comp (lam ((m : ℚ) + 1)) := by
  set n : ℚ := (m : ℚ) + 1 with hn
  set g := G.comp (lam n) with hgdef
  have hgdeg : g.natDegree ≤ 2 * d := by
    apply natDegree_comp_le.trans; rw [lam_natDegree]; nlinarith
  have hgmem : g ∈ degreeLT ℚ (2 * d + 1) := by
    rw [mem_degreeLT]; exact (degree_le_natDegree).trans_lt (by exact_mod_cast Nat.lt_succ_of_le hgdeg)
  have htot' : totL (m + 1) g = 0 := htot
  obtain ⟨q, hqmem, hphi⟩ := gosper_poly m (2 * d) (by omega) g hgmem htot'
  have hgsym : g.comp (C n - X) = g := by rw [hgdef, comp_assoc, lam_symm]
  have hphi' : phiQ (m + 1) q = g := hphi
  have hanti := q_antisymm_poly m (2 * d) hdm g q hqmem hphi' hgsym
  -- the recurrence as a polynomial identity
  have hrecP : (C n - X) * q - X * q.comp (X - 1) = g := by
    rw [← hphi']; simp [phiQ, hn]
  have hshift : q.comp (C n - X) = -q.comp (X - 1) := by
    have : (C n - X : ℚ[X]) = (C (m : ℚ) - X).comp (X - 1) := by simp [hn]; ring
    rw [this, ← comp_assoc, hanti, neg_comp]
  have hqdeg0 : q.natDegree ≤ 2 * d - 1 := by
    by_cases h : q = 0
    · simp [h]
    · have := (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hqmem); omega
  refine ⟨q, hphi, hqdeg0, hanti, ?_⟩
  set N := C 2 * (C n - X) * q - g with hN
  have hNanti : N.comp (C n - X) = -N := by
    simp only [hN, sub_comp, mul_comp, C_comp, X_comp, hgsym, hshift]
    have : (C n - (C n - X) : ℚ[X]) = X := by ring
    rw [this, show (C (2 : ℚ) : ℚ[X]) = 2 from map_ofNat C 2]
    linear_combination (2 : ℚ[X]) * hrecP
  by_cases hN0 : N = 0
  · exact ⟨0, by simp, by rw [hN0]; simp⟩
  obtain ⟨M, hNM, hMsym, hMdeg⟩ := odd_center n N hNanti hN0
  -- degree of N
  have hqdeg : q.natDegree ≤ 2 * d - 1 := by
    by_cases h : q = 0
    · simp [h]
    · have := (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hqmem); omega
  have hNdeg : N.natDegree ≤ 2 * d := by
    rw [hN]
    apply (natDegree_sub_le _ _).trans (max_le ?_ hgdeg)
    apply (natDegree_mul_le).trans
    have h1 : (C 2 * (C n - X) : ℚ[X]).natDegree ≤ 1 := by
      apply (natDegree_C_mul_le _ _).trans
      rw [show (C n - X : ℚ[X]) = -(X - C n) by ring, natDegree_neg, natDegree_X_sub_C]
    omega
  have hMdeg2 : M.natDegree ≤ 2 * (d - 1) := by
    by_cases hM0 : M = 0
    · simp [hM0]
    by_contra hcon; push Not at hcon
    exact symm_not_odd n M hMsym (d - 1) (by omega)
  obtain ⟨Q, hQdeg, hQ⟩ := even_center n (d - 1) M hMdeg2 hMsym
  exact ⟨Q, hQdeg, by rw [hNM, hQ]⟩

end Bali.Psi

#print axioms Bali.Psi.q_antisymm_poly
#print axioms Bali.Psi.psi_poly
