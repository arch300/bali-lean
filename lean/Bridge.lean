import P699.GaussD4
import P699.ProductC

/-!
# Bridge from the real sums to the closed forms over `ℂ` (Bali lab, 2026-11-05)

`Bsum M t = 4^M · cb M · rr t M` for every real `M > 0`, integer or not.
-/

open Finset

namespace Bali.BR
open GaussTarget Bali.PC Bali.GD4

/-- Integer case: Vandermonde. -/
theorem Bsum_nat (n : ℕ) : Bsum (n : ℝ) 0 = (n.centralBinom : ℝ) := by
  unfold Bsum
  have hz : ∀ a ∉ range (n + 1), gchoose (n : ℝ) a * gchoose (n : ℝ) (a + 0) = 0 := by
    intro a ha
    have : n < a := by simpa using ha
    simp [gchoose_natCast, Nat.choose_eq_zero_of_lt this]
  rw [tsum_eq_sum hz]
  have hV := Nat.add_choose_eq n n n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hV
  rw [Nat.centralBinom_eq_two_mul_choose, two_mul, hV]
  push_cast
  refine sum_congr rfl fun a ha => ?_
  have hle : a ≤ n := by simpa [Nat.lt_succ_iff] using ha
  simp only [add_zero, gchoose_natCast, Nat.choose_symm hle]

/-- The real central ratio. -/
noncomputable def rb (M : ℝ) : ℝ := Real.Gamma (M + 1 / 2) / (Real.Gamma (1 / 2) * Real.Gamma (M + 1))

theorem cb_ofReal (M : ℝ) : cb (M : ℂ) = (rb M : ℂ) := by
  unfold cb rb
  push_cast
  rw [← Complex.ofReal_ofNat, ← Complex.ofReal_one]
  simp only [← Complex.ofReal_div, ← Complex.ofReal_add, Complex.Gamma_ofReal]

theorem four_rpow (M : ℝ) : (2 : ℝ) ^ (2 * M) = (4 : ℝ) ^ M := by
  rw [Real.rpow_mul (by norm_num)]; norm_num

/-- `Γ(2M+1)/Γ(M+1)² = 4^M rb M`, the duplication formula. -/
theorem B0_eq (M : ℝ) (hM : 0 < M) : B0 M = (4 : ℝ) ^ M * rb M := by
  have hd := Real.Gamma_mul_Gamma_add_half (M + 1 / 2)
  rw [show M + 1 / 2 + 1 / 2 = M + 1 by ring, show 2 * (M + 1 / 2) = 2 * M + 1 by ring,
    show (1 : ℝ) - (2 * M + 1) = -(2 * M) by ring, Real.rpow_neg (by norm_num), four_rpow] at hd
  have g1 : Real.Gamma (M + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have g2 : Real.Gamma (1 / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h4 : (4 : ℝ) ^ M ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  unfold B0 rb
  rw [Real.Gamma_one_half_eq] at g2 ⊢
  rw [div_eq_iff (mul_ne_zero g1 g1)]
  have hd2 : Real.Gamma (M + 1 / 2) * Real.Gamma (M + 1) * (4 : ℝ) ^ M = Real.Gamma (2 * M + 1) * √Real.pi := by
    rw [hd]; field_simp
  field_simp
  rw [show (2 * M + 1) / 2 = M + 1 / 2 by ring]
  linarith

theorem Bsum_zero_all (M : ℝ) (hM : 0 < M) : Bsum M 0 = (4 : ℝ) ^ M * rb M := by
  by_cases hni : ∀ n : ℕ, M ≠ n
  · rw [Bsum_zero M hM hni, B0_eq M hM]
  · push_neg at hni
    obtain ⟨n, rfl⟩ := hni
    have hc := cb_natCast n
    rw [← Complex.ofReal_natCast, cb_ofReal] at hc
    have hr : rb (n : ℝ) = (n.centralBinom : ℝ) / 4 ^ n := by
      have : (rb (n : ℝ) : ℂ) = (((n.centralBinom : ℝ) / 4 ^ n : ℝ) : ℂ) := by
        rw [hc]; push_cast; rfl
      exact_mod_cast this
    rw [Bsum_nat, hr, Real.rpow_natCast]
    have : (4 : ℝ) ^ n ≠ 0 := by positivity
    field_simp

/-- Real form of `rr`. -/
noncomputable def rrR (t : ℕ) (M : ℝ) : ℝ := ∏ i ∈ range t, ((M - i) * (M + i + 1)⁻¹)

theorem rr_ofReal (t : ℕ) (M : ℝ) : rr t (M : ℂ) = (rrR t M : ℂ) := by
  simp [rr, rrR]

theorem Bsum_all (M : ℝ) (hM : 0 < M) (t : ℕ) : Bsum M t = (4 : ℝ) ^ M * rb M * rrR t M := by
  induction t with
  | zero => simpa [rrR] using Bsum_zero_all M hM
  | succ t ih =>
    have h := Bsum_recur M hM t
    have hp : M + 1 + (t : ℝ) ≠ 0 := by positivity
    have e : Bsum M (t + 1) = (M - t) * Bsum M t / (M + 1 + t) := by
      rw [eq_div_iff hp]; linarith
    rw [e, ih]
    simp only [rrR, prod_range_succ]
    field_simp
    ring

end Bali.BR

#print axioms Bali.BR.Bsum_all
