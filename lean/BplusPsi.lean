import P699.PsiAssemble

/-!
# Type B⁺: Lemma ψ for odd functions `φ = (n - 2x) G(λ)` (Bali lab, 2026-11-02)
For odd `φ` the total vanishes automatically; the Gosper solution is symmetric and
`2(n-x) q - φ = M(λ)` with `deg M ≤ deg G`.
-/

open Finset Polynomial

namespace Bali.BP
open Bali Bali.Even Bali.Psi Bali.Skew Bali.PsiA

theorem gosper_sym (m : ℕ) (g q : ℕ → ℚ)
    (hrec : ∀ k, ((m : ℚ) + 1 - k) * q k - k * q (k - 1) = ((m : ℚ) + 1) * g k)
    (hodd : ∀ k, k ≤ m + 1 → g k = -g (m + 1 - k)) :
    ∀ h, h ≤ m → q h = q (m - h)
  | 0, _ => by
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    have h0 := hrec 0
    have hlast := hrec (m + 1)
    simp only [Nat.cast_zero, sub_zero, zero_mul, Nat.cast_add, Nat.cast_one, sub_self, Nat.add_sub_cancel]
      at h0 hlast
    have hg := hodd 0 (by omega)
    simp only [Nat.sub_zero] at hg
    have hq0 : q 0 = g 0 := mul_left_cancel₀ hm (by linarith)
    have hqm : q m = - g (m + 1) := mul_left_cancel₀ hm (by linarith)
    simp only [Nat.sub_zero]; rw [hq0, hqm, hg]
  | k + 1, hk => by
    have ih := gosper_sym m g q hrec hodd k (by omega)
    have hA := hrec (k + 1)
    have hB := hrec (m - k)
    have hg := hodd (k + 1) (by omega)
    have e1 : m + 1 - (k + 1) = m - k := by omega
    have e2 : m - k - 1 = m - (k + 1) := by omega
    rw [e1] at hg
    simp only [Nat.add_sub_cancel] at hA
    rw [e2] at hB
    have hcast : ((m - k : ℕ) : ℚ) = (m : ℚ) - k := Nat.cast_sub (by omega)
    rw [hcast] at hB
    push_cast at hA
    have hne : ((m : ℚ) - k) ≠ 0 := by
      have : (k : ℚ) < m := by exact_mod_cast (by omega : k < m)
      linarith
    apply mul_left_cancel₀ hne
    rw [hg, ih] at hA
    linear_combination hA + hB

theorem q_sym_poly (m D : ℕ) (hD : D ≤ m) (g q : ℚ[X]) (hq : q ∈ degreeLT ℚ D)
    (hphi : phiQ (m + 1) q = g) (hgodd : g.comp (C ((m : ℚ) + 1) - X) = -g) :
    q.comp (C (m : ℚ) - X) = q := by
  have hrec : ∀ k : ℕ, ((m : ℚ) + 1 - k) * q.eval (k : ℚ) - k * q.eval ((k - 1 : ℕ) : ℚ)
      = ((m : ℚ) + 1) * (g.eval (k : ℚ) / ((m : ℚ) + 1)) := by
    intro k
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ hm, ← hphi, phiQ_eval]
    rcases k with _ | k
    · simp
    · push_cast; simp only [add_sub_cancel_right]
  have hodd : ∀ k, k ≤ m + 1 → g.eval (k : ℚ) / ((m : ℚ) + 1) = -(g.eval ((m + 1 - k : ℕ) : ℚ) / ((m : ℚ) + 1)) := by
    intro k hk
    have := congrArg (eval (k : ℚ)) hgodd
    rw [eval_comp] at this
    simp only [eval_sub, eval_C, eval_X, eval_neg] at this
    rw [Nat.cast_sub hk]; push_cast
    rw [this]; ring
  have hint := gosper_sym m (fun k => g.eval (k : ℚ) / ((m : ℚ) + 1)) (fun k => q.eval (k : ℚ)) hrec hodd
  set r := q.comp (C (m : ℚ) - X) - q with hr
  have hqdeg : q.natDegree < m + 1 := by
    by_cases h : q = 0
    · simp [h]
    · have := (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hq); omega
  have hrdeg : r.natDegree < m + 1 := by
    apply lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt ?_ hqdeg)
    apply lt_of_le_of_lt natDegree_comp_le
    rw [show (C (m : ℚ) - X) = -(X - C (m : ℚ)) by ring, natDegree_neg, natDegree_X_sub_C, mul_one]; exact hqdeg
  have hr0 : r = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero r (f := fun i : Fin (m + 1) => ((i : ℕ) : ℚ))
      (fun a b h => Fin.ext (by exact_mod_cast (show ((a : ℕ) : ℚ) = b from h)))
    · intro i
      have hi := hint i (by omega)
      simp only [hr, eval_sub, eval_comp, eval_C, eval_X]
      have : (m : ℚ) - (i : ℕ) = ((m - (i : ℕ) : ℕ) : ℚ) := by rw [Nat.cast_sub (by omega)]
      rw [this]; linarith
    · simpa using hrdeg
  linear_combination hr0

/-- the odd function `φ = (n - 2X) G(λ)`. -/
noncomputable def phiO (n : ℚ) (G : ℚ[X]) : ℚ[X] := (C n - C 2 * X) * G.comp (lam n)

lemma phiO_odd (n : ℚ) (G : ℚ[X]) : (phiO n G).comp (C n - X) = -phiO n G := by
  unfold phiO
  rw [mul_comp, comp_assoc, lam_symm]
  simp only [sub_comp, C_comp, mul_comp, X_comp]
  rw [show (C (2 : ℚ) : ℚ[X]) = 2 from map_ofNat C 2]
  ring

lemma totL_odd (m : ℕ) (g : ℚ[X]) (hg : g.comp (C ((m : ℚ) + 1) - X) = -g) : totL (m + 1) g = 0 := by
  rw [totL_apply]
  set S := ∑ k ∈ range (m + 1 + 1), ((m + 1).choose k : ℚ) * g.eval (k : ℚ) with hS
  have hrefl : S = -S := by
    conv_lhs => rw [hS, ← sum_range_reflect]
    rw [hS, ← sum_neg_distrib]
    refine sum_congr rfl fun k hk => ?_
    have hk' := mem_range.1 hk
    rw [show m + 1 + 1 - 1 - k = m + 1 - k by omega, Nat.choose_symm (by omega)]
    have := congrArg (eval (k : ℚ)) hg
    rw [eval_comp] at this
    simp only [eval_sub, eval_C, eval_X, eval_neg] at this
    rw [Nat.cast_sub (by omega)]; push_cast
    rw [this]; ring
  linarith

/-- **ψ for odd functions.** -/
theorem psi_poly_odd (m d : ℕ) (hdm : 2 * d + 1 ≤ m) (G : ℚ[X]) (hG : G.natDegree ≤ d) :
    ∃ q : ℚ[X], phiQ (m + 1) q = phiO ((m : ℚ) + 1) G ∧
      ∃ M : ℚ[X], M.natDegree ≤ d ∧
        C 2 * (C ((m : ℚ) + 1) - X) * q - phiO ((m : ℚ) + 1) G = M.comp (lam ((m : ℚ) + 1)) := by
  set n : ℚ := (m : ℚ) + 1 with hn
  set g := phiO n G with hgdef
  have hgdeg : g.natDegree ≤ 2 * d + 1 := by
    rw [hgdef, phiO]
    refine natDegree_mul_le.trans ?_
    have h1 : (C n - C 2 * X : ℚ[X]).natDegree ≤ 1 := by compute_degree!
    have h2 : (G.comp (lam n)).natDegree ≤ 2 * d := by
      apply natDegree_comp_le.trans; rw [lam_natDegree]; nlinarith
    omega
  have hgmem : g ∈ degreeLT ℚ (2 * d + 1 + 1) := by
    rw [mem_degreeLT]; exact (degree_le_natDegree).trans_lt (by exact_mod_cast Nat.lt_succ_of_le hgdeg)
  have hgodd : g.comp (C n - X) = -g := phiO_odd n G
  have htot : totL (m + 1) g = 0 := totL_odd m g hgodd
  obtain ⟨q, hqmem, hphi⟩ := gosper_poly m (2 * d + 1) (by omega) g hgmem htot
  have hsym := q_sym_poly m (2 * d + 1) hdm g q hqmem hphi hgodd
  refine ⟨q, hphi, ?_⟩
  have hrecP : (C n - X) * q - X * q.comp (X - 1) = g := by
    rw [← hphi]; simp [phiQ, hn]
  have hshift : q.comp (C n - X) = q.comp (X - 1) := by
    have : (C n - X : ℚ[X]) = (C (m : ℚ) - X).comp (X - 1) := by simp [hn]; ring
    rw [this, ← comp_assoc, hsym]
  set N := C 2 * (C n - X) * q - g with hN
  have hNsym : N.comp (C n - X) = N := by
    simp only [hN, sub_comp, mul_comp, C_comp, X_comp, hgodd, hshift]
    have : (C n - (C n - X) : ℚ[X]) = X := by ring
    rw [this, show (C (2 : ℚ) : ℚ[X]) = 2 from map_ofNat C 2]
    linear_combination (-2 : ℚ[X]) * hrecP
  have hqdeg : q.natDegree ≤ 2 * d := by
    by_cases h : q = 0
    · simp [h]
    · have := (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hqmem); omega
  have hNdeg : N.natDegree ≤ 2 * d + 1 := by
    rw [hN]
    apply (natDegree_sub_le _ _).trans (max_le ?_ hgdeg)
    apply (natDegree_mul_le).trans
    have h1 : (C 2 * (C n - X) : ℚ[X]).natDegree ≤ 1 := by compute_degree!
    omega
  have hNdeg2 : N.natDegree ≤ 2 * d := by
    by_cases hN0 : N = 0
    · simp [hN0]
    by_contra hcon; push_neg at hcon
    exact symm_not_odd n N hNsym d (by omega)
  obtain ⟨M, hMdeg, hM⟩ := even_center n d N hNdeg2 hNsym
  exact ⟨M, hMdeg, hM⟩

end Bali.BP

#print axioms Bali.BP.psi_poly_odd
