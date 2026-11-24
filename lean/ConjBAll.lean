import P699.ConjB
import P699.OddB
import P699.ShellX

/-!
# Conjecture B for all `d` (odd `n`), from Theorem Bodd (even + odd) (Bali lab, 2026-11-02)
-/

open Finset Polynomial Matrix

namespace Bali.ConjBAll
open Bali Bali.PfP Bali.VB Bali.Racah Bali.Final Bali.ConjB Bali.OddB

/-- `T(R_{2m})`. -/
noncomputable def TR (H m : ℕ) : ℚ := 2 ^ (2 * H + 1) * ∏ i ∈ range m, ((2 * (i : ℚ) + 1) / (2 * H - 2 * i)) ^ 2

/-- **odd step from Theorem Bodd:** `V_{2m+1} = V_{2m} · T(R_{2m}) 4^{2m} / ℓ_{2m}`. -/
theorem W_succ (H m : ℕ) (hm : 2 * m ≤ H) :
    VBvol (tS H) (nuS H) (2 * m + 1)
      = V H m * (TR H m * 4 ^ (2 * m) / (RP (2 * H + 1) (2 * m)).leadingCoeff) := by
  have h1 := theorem_Bodd H m (by omega)
  have h2 := theorem_Bodd_odd H m hm
  rw [← h1, det_Bo H m hm, det_Brac H m (by omega), sgn_range (2 * m + 1), sgn_range (2 * m),
    Fin.prod_univ_eq_prod_range (fun q => (RP (2 * H + 1) q).leadingCoeff * (1 / 4 : ℚ) ^ q),
    Fin.prod_univ_eq_prod_range (fun q => (RP (2 * H + 1) q).leadingCoeff * (1 / 4 : ℚ) ^ q),
    prod_range_succ, prod_range_succ (fun i => (-1 : ℚ) ^ i)] at h2
  set B := ∏ x ∈ range (2 * m), (RP (2 * H + 1) x).leadingCoeff * (1 / 4 : ℚ) ^ x
  set s := ∏ x ∈ range (2 * m), (-1 : ℚ) ^ x
  have hB : B ≠ 0 := prod_ne_zero_iff.2 fun q hq =>
    mul_ne_zero (ell_pos H q (by have := mem_range.1 hq; omega)).ne' (by positivity)
  have hs : s ≠ 0 := prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ (by norm_num)
  have l0 := (ell_pos H (2 * m) (by omega)).ne'
  have p0 : (-1 : ℚ) ^ (2 * m) = 1 := by rw [pow_mul]; simp
  rw [p0] at h2
  unfold V TR
  simp only [_root_.one_div_pow] at h2
  field_simp at h2
  field_simp
  linear_combination h2

lemma podd : ∀ m : ℕ, ∏ i ∈ range m, (2 * (i : ℚ) + 1) = (2 * m).factorial / (2 ^ m * m.factorial)
  | 0 => by simp
  | m + 1 => by
    rw [prod_range_succ, podd m, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring

lemma peven (H : ℕ) : ∀ m, m ≤ H →
    ∏ i ∈ range m, (2 * (H : ℚ) - 2 * i) = 2 ^ m * H.factorial / (H - m).factorial
  | 0, _ => by simp [Nat.factorial_ne_zero]
  | m + 1, hm => by
    rw [prod_range_succ, peven H m (by omega)]
    obtain ⟨r, rfl⟩ : ∃ r, H = m + 1 + r := ⟨H - (m + 1), by omega⟩
    rw [show m + 1 + r - m = r + 1 by omega, show m + 1 + r - (m + 1) = r by omega, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- **Theorem Bodd (odd) ⇒ Conjecture B, odd steps:** `V_{2m+1} = V_{2m} · ρ_{2m}`. -/
theorem conjB_odd (H m : ℕ) (hm : 2 * m ≤ H) :
    ((VBvol (tS H) (nuS H) (2 * m + 1) : ℚ) : ℝ) = V H m * crB H (2 * m) (Ke m) := by
  rw [W_succ H m hm]
  push_cast
  congr 1
  obtain ⟨r, rfl⟩ : ∃ r, H = 2 * m + r := ⟨H - 2 * m, by omega⟩
  unfold TR
  rw [ell_closed _ _ (by omega), prod_pow, prod_div_distrib, podd, peven _ m (by omega),
    show 2 * (2 * m + r) + 1 - 2 * m = 2 * m + 2 * r + 1 by omega,
    show 2 * (2 * m + r) + 1 - 2 * (2 * m) = 2 * r + 1 by omega,
    show 2 * m + r - 2 * m = r by omega, show 2 * m + r - m = m + r by omega,
    show 2 * (2 * m + r) + 1 = 4 * m + 2 * r + 1 by ring]
  have G1 : Real.Gamma ((2 * ((2 * m + r : ℕ) : ℝ) + 1) / 2 - ((2 * m : ℕ) : ℝ) + 1)
      = ((2 * r + 2).factorial : ℝ) * √Real.pi / (4 ^ (r + 1) * (r + 1).factorial) := by
    rw [show (2 * ((2 * m + r : ℕ) : ℝ) + 1) / 2 - ((2 * m : ℕ) : ℝ) + 1 = ((r + 1 : ℕ) : ℝ) + 1 / 2 by
      push_cast; ring, Gamma_half, show 2 * (r + 1) = 2 * r + 2 by ring]
  have G2 : Real.Gamma ((2 * ((2 * m + r : ℕ) : ℝ) + 1) / 2 - ((2 * m : ℕ) : ℝ) + 1 / 2)
      = (r.factorial : ℝ) := by
    rw [show (2 * ((2 * m + r : ℕ) : ℝ) + 1) / 2 - ((2 * m : ℕ) : ℝ) + 1 / 2 = (r : ℝ) + 1 by
      push_cast; ring, Real.Gamma_nat_eq_factorial]
  have G3 : Real.Gamma ((2 * ((2 * m + r : ℕ) : ℝ) + 1 - ((2 * m : ℕ) : ℝ) + 2) / 2)
      = ((2 * m + 2 * r + 2).factorial : ℝ) * √Real.pi / (4 ^ (m + r + 1) * (m + r + 1).factorial) := by
    rw [show (2 * ((2 * m + r : ℕ) : ℝ) + 1 - ((2 * m : ℕ) : ℝ) + 2) / 2 = ((m + r + 1 : ℕ) : ℝ) + 1 / 2 by
      push_cast; ring, Gamma_half, show 2 * (m + r + 1) = 2 * m + 2 * r + 2 by ring]
  unfold crB Ke
  rw [G1, G2, G3, show 2 * (2 * m + r) + 1 = 4 * m + 2 * r + 1 by ring]
  rw [show 2 * r + 2 = (2 * r + 1) + 1 by ring, Nat.factorial_succ (2 * r + 1),
    Nat.factorial_succ r,
    show 2 * m + 2 * r + 2 = (2 * m + 2 * r + 1) + 1 by ring, Nat.factorial_succ (2 * m + 2 * r + 1),
    show m + r + 1 = (m + r) + 1 by ring, Nat.factorial_succ (m + r)]
  have hs : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have := hs.ne'
  push_cast
  ring_nf
  simp only [one_div, inv_pow]
  field_simp
  have h4 : (4 : ℝ) ^ r = 2 ^ (r * 2) := by rw [mul_comm, pow_mul]; norm_num
  rw [h4]
  ring

/-- the constant `K_j` of Conjecture B. -/
noncomputable def Kc (j : ℕ) : ℝ := if j % 2 = 0 then Ke (j / 2) else Ko (j / 2)

lemma Kc_even (k : ℕ) : Kc (2 * k) = Ke k := by simp [Kc]
lemma Kc_odd (k : ℕ) : Kc (2 * k + 1) = Ko k := by
  simp [Kc, Nat.add_mod]; congr 1; omega

lemma conjB_evens (H : ℕ) : ∀ m, 2 * m ≤ H + 1 →
    ((VBvol (tS H) (nuS H) (2 * m) : ℚ) : ℝ) = ∏ j ∈ range (2 * m), crB H j (Kc j)
  | 0, _ => by simp [VBvol]
  | m + 1, hm => by
    have := conjB_even H m hm
    unfold V at this
    rw [this, conjB_evens H m (by omega), show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      prod_range_succ, prod_range_succ, Kc_even, Kc_odd]
    ring

/-- **Conjecture B (odd `n = 2H+1`), proved for every `d ≤ H+1`:**
`V^B_d = ∏_{j<d} K_j · n! Γ(n/2-j+1) / (Γ(n/2-j+1/2) Γ((n-j+2)/2)²)`. -/
theorem conjB (H d : ℕ) (hd : d ≤ H + 1) :
    ((VBvol (tS H) (nuS H) d : ℚ) : ℝ) = ∏ j ∈ range d, crB H j (Kc j) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' d
  · exact conjB_evens H m hd
  · rw [conjB_odd H m (by omega), prod_range_succ, Kc_even]
    unfold V
    rw [conjB_evens H m (by omega)]

/-- **the same, in the paper's point form** (`x = 0..n`, `y_x = (2x-n)²`, weights `C(n,x)`). -/
theorem conjB_x (H d : ℕ) (hd : d ≤ H + 1) :
    ((Bali.ShellX.VBs (fun x : Fin (2 * H + 2) => (2 * (x : ℚ) - (2 * H + 1)) ^ 2)
        (fun x => ((2 * H + 1).choose (x : ℕ) : ℚ)) d : ℚ) : ℝ) = ∏ j ∈ range d, crB H j (Kc j) := by
  rw [Bali.ShellX.VBx_eq_VBvol, conjB H d hd]

end Bali.ConjBAll

#print axioms Bali.ConjBAll.conjB
#print axioms Bali.ConjBAll.conjB_x
