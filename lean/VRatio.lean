import P699.VStep

/-!
# Even `n`: the explicit ratio `V_{2k+2}/V_{2k}` for `k ≥ 1` (Bali lab, 2026-11-02)
`ℓ_{2k}² Rc_{2k-1} T_{2k} V_{2k+2} = -4^{4k+1}(n-1-4k) T_{2k-1} Rc_{2k+1} h_{2k} V_{2k}`.
-/

open Finset Polynomial Matrix

namespace Bali.VE
open Bali.EvenPsi Bali.Chr Bali.Skew Bali.VG Bali.PfP Bali.VB Bali.GA

variable {K : ℕ}

/-- shorthand for the explicit data. -/
noncomputable def Rc (K a : ℕ) : ℚ := Bali.RE.RE (K + 1) a ((K + 1 : ℕ) : ℚ)
noncomputable def ll (K a : ℕ) : ℚ := (RPE (K + 1) a).coeff a
noncomputable def TT (K a : ℕ) : ℚ := TB K (pK (K + 1) a)

lemma co_succ (s : ℕ) : co K (s + 1) = Rc K s * ll K (s + 1) * (1 / 4 : ℚ) ^ (s + 1) := by
  unfold co Rc ll
  simp only [Hc, Nk, coeff_sub, coeff_C_mul]
  rw [coeff_eq_zero_of_natDegree_lt (p := RPE (K + 1) s) (by have := RPE_le (K + 1) s; omega), mul_zero, sub_zero]

/-- the pairing in closed terms, `k ≥ 1`. -/
lemma pair_eq (hK : 2 ≤ K) (k : ℕ) (hk1 : 1 ≤ k) (hk : 2 * k + 1 ≤ K) :
    4 * TT K (2 * k) * ll K (2 * k) * skew (e K (2 * k)) (e K (2 * k + 1))
      = 4 * TT K (2 * k - 1) * ((nQ K) - 1 - 2 * (2 * k : ℕ)) * Rc K (2 * k + 1) * Rc K (2 * k) * ll K (2 * k + 1)
          * Bali.REO.hE (K + 1) (2 * k) := by
  have hpos : 2 * k = (2 * k - 1) + 1 := by omega
  have hdiag := diag_B K (pF K)
    (fun c => by
      unfold pF; split_ifs
      · exact pK_le _ _
      · simp)
    (fun c Q hQ => pF_orth K c Q hQ) (2 * k) (by omega) (by omega)
    (by rw [pF_eq _ (by omega)]; exact lc_ne (by omega) _ (by omega))
  have hN := ipW_pK K (2 * k) (by omega)
  have hlc := pK_coeff (K + 1) (2 * k)
  rw [hK_V hK _ _ (by omega) (by omega)]
  have hT0 := T0_ne hK
  have hTe : τ K (2 * k) = TT K (2 * k - 1) := by
    conv_lhs => rw [hpos]
    simp only [τ, TT]; rw [pF_eq _ (by omega)]
  have hw : w K (2 * k + 1) = skew (rowB K (pF K 0)) (rowB K (pF K (2 * k))) / (16 * TB K (pF K 0)) := rfl
  rw [hTe, hw]
  rw [pF_eq (2 * k) (by omega)] at hdiag ⊢
  rw [Bali.OddB.skew_anti (rowB K (pF K 0))]
  simp only [TT, Rc, ll]
  have hinv : TB K (pF K 0) * (TB K (pF K 0))⁻¹ = 1 := mul_inv_cancel₀ hT0
  set X := skew (rowB K (pK (K + 1) (2 * k))) (rowB K (pF K 0))
  set N := ipW K (pK (K + 1) (2 * k)) (pK (K + 1) (2 * k))
  set cc := nQ K - 1 - 2 * ((2 * k : ℕ) : ℚ)
  set T' := TB K (pK (K + 1) (2 * k - 1))
  set l := (RPE (K + 1) (2 * k)).coeff (2 * k)
  rw [div_eq_mul_inv, mul_inv]
  linear_combination (-T' * l * (TB K (pF K 0))⁻¹ / 4) * hdiag + (-T' * l * cc * N) * hinv
    + (-T' * cc) * hN + (4 * T' * cc * Bali.RE.RE (K + 1) (2 * k + 1) ((K + 1 : ℕ) : ℚ) * Bali.REO.hE (K + 1) (2 * k)) * hlc
/-- **the ratio**, `k ≥ 1`. -/
theorem V_ratio (hK : 2 ≤ K) (k : ℕ) (hk1 : 1 ≤ k) (hk : 2 * (k + 1) ≤ K + 1) :
    ll K (2 * k) ^ 2 * Rc K (2 * k - 1) * TT K (2 * k) * VE K (k + 1)
      = -(4 : ℚ) ^ (4 * k + 1) * ((nQ K) - 1 - 2 * (2 * k : ℕ)) * TT K (2 * k - 1) * Rc K (2 * k + 1)
          * Bali.REO.hE (K + 1) (2 * k) * VE K k := by
  have hs := V_step hK k hk
  have hp := pair_eq hK k hk1 (by omega)
  have hpos : 2 * k = (2 * k - 1) + 1 := by omega
  have c1 : co K (2 * k) = Rc K (2 * k - 1) * ll K (2 * k) * (1 / 4 : ℚ) ^ (2 * k) := by
    conv_lhs => rw [hpos]
    rw [co_succ, ← hpos]
  have c2 : co K (2 * k + 1) = Rc K (2 * k) * ll K (2 * k + 1) * (1 / 4 : ℚ) ^ (2 * k + 1) := co_succ _
  rw [c1, c2] at hs
  have hR : Rc K (2 * k) ≠ 0 := by
    unfold Rc; rw [Bali.RE.RE_centre _ _ (by omega)]; exact Bali.TN.F_ne _ _ (by omega)
  have hl : ll K (2 * k + 1) ≠ 0 := by
    unfold ll; rw [RPE_coeff]
    exact mul_ne_zero (Bali.Chr.ce_ne _ _ (by omega) _ le_rfl) (pow_ne_zero _ (by norm_num))
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) hR) hl)
  have e4 : (4 : ℚ) ^ (4 * k + 1) * ((1 / 4 : ℚ) ^ (2 * k) * (1 / 4 : ℚ) ^ (2 * k + 1)) = 1 := by
    rw [← pow_add, show 2 * k + (2 * k + 1) = 4 * k + 1 by ring, ← mul_pow]; norm_num
  linear_combination (-4 * TT K (2 * k) * ll K (2 * k) * (4 : ℚ) ^ (4 * k + 1)) * hs
    - ((4 : ℚ) ^ (4 * k + 1) * VE K k) * hp
    - (4 * TT K (2 * k) * ll K (2 * k) * (Rc K (2 * k - 1) * ll K (2 * k)) * (Rc K (2 * k) * ll K (2 * k + 1)) * VE K (k + 1)) * e4
end Bali.VE

#print axioms Bali.VE.V_ratio
