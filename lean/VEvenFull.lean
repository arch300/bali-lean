import P699.VEven

/-!
# Even `n`, even `d`: the pairings do not vanish; `V_even` without hypothesis (Bali lab, 2026-11-02)
-/

open Finset Polynomial Matrix

namespace Bali.VE
open Bali.EvenPsi Bali.Chr Bali.Skew Bali.VG Bali.PfP Bali.VB Bali.GA

variable {K : ℕ}

lemma hE_ne (a : ℕ) (ha : a < K + 1) : Bali.REO.hE (K + 1) a ≠ 0 := by
  intro h
  have := Bali.REO.hE_closed K a ha
  rw [h, zero_mul] at this
  have h1 : (2 * ((K + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  have h2 : ((2 * K + 1).choose K : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  exact mul_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ h2) this.symm

/-- the norm of `p_b` does not vanish. -/
lemma N_ne (hK : 1 ≤ K) (b : ℕ) (hb : b + 1 < K + 1) :
    ipW K (pK (K + 1) b) (pK (K + 1) b) ≠ 0 := by
  intro h
  have key := ipW_pK K b hb
  rw [h, mul_zero] at key
  have hR : Bali.RE.RE (K + 1) (b + 1) ((K + 1 : ℕ) : ℚ) ≠ 0 := by
    rw [Bali.RE.RE_centre _ _ hb]; exact Bali.TN.F_ne _ _ hb
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hR) (lc_ne hK b hb)) (hE_ne b (by omega)) key.symm

lemma pF_eq (b : ℕ) (hb : b + 1 < K + 1) : pF K b = pK (K + 1) b := by
  unfold pF; rw [if_pos hb]

/-- `⟨p_b, p_0⟩_B ≠ 0`. -/
lemma rho_ne (hK : 2 ≤ K) (b : ℕ) (hb1 : 1 ≤ b) (hb : b + 1 ≤ K) :
    skew (rowB K (pF K b)) (rowB K (pF K 0)) ≠ 0 := by
  intro h
  have hlc : (pF K b).coeff b ≠ 0 := by rw [pF_eq b (by omega)]; exact lc_ne (by omega) b (by omega)
  have key := diag_B K (pF K)
    (fun c => by
      unfold pF; split_ifs
      · exact pK_le _ _
      · simp)
    (fun c Q hQ => pF_orth K c Q hQ) b hb1 hb hlc
  rw [h, mul_zero] at key
  have hn : nQ K - 1 - 2 * (b : ℚ) ≠ 0 := by
    rw [nQ_eq]; push_cast
    have : (b : ℚ) + 1 ≤ K := by exact_mod_cast hb
    intro h; linarith
  have hN : ipW K (pF K b) (pF K b) ≠ 0 := by rw [pF_eq b (by omega)]; exact N_ne (by omega) b (by omega)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (T0_ne hK)) hn) hN key.symm

/-- the anomalous pairing `r₀`. -/
lemma r0_ne (hK : 2 ≤ K) : skew (nuV K) (rowE K (pF K 0)) ≠ 0 := by
  have hc := c0_ne (K := K) (by omega)
  have hN : ipW K (pF K 0) (pF K 0) ≠ 0 := by rw [pF_eq 0 (by omega)]; exact N_ne (by omega) 0 (by omega)
  have hS : skew (rowB K 1) (rowB K (pF K 0)) = 0 := by
    have hr : rowB K (pF K 0) = fun k => c0 K * rowB K 1 k := by rw [pF0, rowB_C]
    rw [hr, skew_smul2, skew_self, mul_zero]
  have hI : ipW K (pF K 0) 1 ≠ 0 := by
    intro h
    apply hN
    have e : pF K 0 = C (c0 K) * 1 + 0 := by rw [add_zero]; exact pF0 K
    conv_lhs => rw [e]
    rw [ipW_lin, ← e, h, mul_zero, zero_add]
    simp [ipW]
  rw [border, hS, zero_div, zero_sub]
  have hn0 : ((2 * K + 1 + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hn1 : ((2 * K + 1 + 1 : ℕ) : ℚ) - 1 ≠ 0 := by
    push_cast
    have : (0 : ℚ) ≤ K := by positivity
    intro h; linarith
  exact neg_ne_zero.2 (mul_ne_zero (div_ne_zero hn1 hn0) hI)

/-- all pairings are nonzero. -/
theorem hd_ne (hK : 2 ≤ K) (i : ℕ) (hi : 2 * i + 1 ≤ K) :
    skew (e K (2 * i)) (e K (2 * i + 1)) ≠ 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simpa [e] using r0_ne hK
  · rw [hK_V hK _ _ (by omega) (by omega)]
    refine mul_ne_zero (tau_even_ne hK i (by omega)) ?_
    simp only [w]
    refine div_ne_zero ?_ (mul_ne_zero (by norm_num) (T0_ne hK))
    rw [Bali.OddB.skew_anti]
    exact neg_ne_zero.2 (rho_ne hK (2 * i) (by omega) (by omega))

/-- **`V^B_{2k}`, even `n`, unconditional form.** -/
theorem V_even_full (hK : 2 ≤ K) (k : ℕ) (hk : 2 * k ≤ K + 1) :
    (∏ a, (Gp K k a).coeff (eι k a : ℕ)) *
        (sgnPairs (2 * k) * VBvol (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) (2 * k))
      = ∏ i : Fin k, skew (e K (2 * (i : ℕ))) (e K (2 * (i : ℕ) + 1)) :=
  V_even hK k hk fun i => hd_ne hK i (by have := i.isLt; omega)

end Bali.VE

#print axioms Bali.VE.V_even_full
