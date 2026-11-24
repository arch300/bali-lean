import P699.Final

/-!
# Reservation 3: Theorem Bodd against the Γ form of Conjecture B (Bali lab, 2026-11-02)
(1) `ℓ_a` in closed form; (2) the ratio `V_{2m+2}/V_{2m}` from `theorem_Bodd`.
-/

open Finset Polynomial Matrix

namespace Bali.ConjB
open Bali Bali.PfP Bali.VB Bali.Racah Bali.Final

lemma c_prod (n : ℚ) (m : ℕ) : ∀ j, c n m j = ∏ i ∈ range j,
    (((i : ℚ) - m) * ((m : ℚ) - n + i) / (((1 - n) / 2 + i) ^ 2 * (-n + i) * ((i : ℚ) + 1)))
  | 0 => by simp [c]
  | j + 1 => by rw [prod_range_succ, ← c_prod n m j]; rfl

/-- `∏_{i<a} (i - N) = (-1)^a N!/(N-a)!`. -/
lemma fall (N : ℕ) : ∀ a, a ≤ N →
    ∏ i ∈ range a, ((i : ℚ) - N) = (-1) ^ a * ((N.factorial : ℚ) / (N - a).factorial)
  | 0, _ => by simp [Nat.factorial_ne_zero]
  | a + 1, ha => by
    rw [prod_range_succ, fall N a (by omega)]
    obtain ⟨r, rfl⟩ : ∃ r, N = a + 1 + r := ⟨N - (a + 1), by omega⟩
    rw [show a + 1 + r - a = r + 1 by omega, show a + 1 + r - (a + 1) = r by omega, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- **`ℓ_a` closed form.** -/
theorem ell_closed (H a : ℕ) (ha : a ≤ H) :
    (RP (2 * H + 1) a).leadingCoeff
      = ((2 * H + 1 - a).factorial : ℚ) ^ 2 * ((H - a).factorial : ℚ) ^ 2
        / (((2 * H + 1 - 2 * a).factorial : ℚ) * (2 * H + 1).factorial * (H.factorial : ℚ) ^ 2) := by
  rw [RP_leading H a ha, c_prod]
  have e : ∀ i ∈ range a,
      (((i : ℚ) - a) * ((a : ℚ) - (2 * H + 1 : ℚ) + i) /
          (((1 - (2 * H + 1 : ℚ)) / 2 + i) ^ 2 * (-(2 * H + 1 : ℚ) + i) * ((i : ℚ) + 1)))
        = ((i : ℚ) - (a : ℕ)) * ((i : ℚ) - ((2 * H + 1 - a : ℕ) : ℚ)) /
          (((i : ℚ) - (H : ℕ)) ^ 2 * ((i : ℚ) - ((2 * H + 1 : ℕ) : ℚ)) * (((i + 1 : ℕ) : ℚ))) := by
    intro i _
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [prod_congr rfl e, prod_div_distrib, prod_mul_distrib, prod_mul_distrib, prod_mul_distrib, prod_pow,
    fall a a le_rfl, fall (2 * H + 1 - a) a (by omega), fall H a ha, fall (2 * H + 1) a (by omega),
    ← Nat.cast_prod, prod_range_add_one_eq_factorial, Nat.sub_self, Nat.factorial_zero,
    show 2 * H + 1 - a - a = 2 * H + 1 - 2 * a by omega]
  have h1 : ((2 * H + 1 - 2 * a).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((H - a).factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((2 * H + 1 - a).factorial : ℚ) ≠ 0 := by positivity
  have h4 : (a.factorial : ℚ) ≠ 0 := by positivity
  have h5 : (H.factorial : ℚ) ≠ 0 := by positivity
  have h6 : ((2 * H + 1).factorial : ℚ) ≠ 0 := by positivity
  have h7 : ((-1 : ℚ) ^ a) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

lemma ell_pos (H a : ℕ) (ha : a ≤ H) : 0 < (RP (2 * H + 1) a).leadingCoeff := by
  rw [ell_closed H a ha]; positivity

lemma sgn_range (d : ℕ) : (sgnPairs d : ℚ) = ∏ i ∈ range d, (-1 : ℚ) ^ i := by
  unfold sgnPairs
  simp only [prod_const, Fin.card_Ioi]
  rw [Fin.prod_univ_eq_prod_range (fun i => (-1 : ℚ) ^ (d - 1 - i)) d]
  exact prod_range_reflect (fun i => (-1 : ℚ) ^ i) d

/-- `V_{2m}` (shell form; equal to the point form by `ShellX.VBx_eq_VBvol`). -/
noncomputable def V (H m : ℕ) : ℚ := VBvol (tS H) (nuS H) (2 * m)

/-- **Ratio from Theorem Bodd.** `V_{2m+2} = V_{2m} · 4^{4m+1}(2H-4m)‖R_{2m}‖²/ℓ_{2m}²`. -/
theorem V_succ (H m : ℕ) (hm : 2 * (m + 1) ≤ H + 1) :
    V H (m + 1) = V H m * ((4 : ℚ) ^ (4 * m + 1) * (2 * H - 4 * m) * hN H (2 * m)
      / ((RP (2 * H + 1) (2 * m)).leadingCoeff) ^ 2) := by
  have h1 := theorem_Bodd H m (by omega)
  have h2 := theorem_Bodd H (m + 1) hm
  rw [Fin.prod_univ_castSucc] at h2
  simp only [Fin.coe_castSucc, Fin.val_last] at h2
  rw [← h1, det_Brac H (m + 1) hm, det_Brac H m (by omega), sgn_range, sgn_range,
    Fin.prod_univ_eq_prod_range (fun q => (RP (2 * H + 1) q).leadingCoeff * (1 / 4 : ℚ) ^ q),
    Fin.prod_univ_eq_prod_range (fun q => (RP (2 * H + 1) q).leadingCoeff * (1 / 4 : ℚ) ^ q),
    show 2 * (m + 1) = 2 * m + 1 + 1 by ring, prod_range_succ, prod_range_succ,
    prod_range_succ, prod_range_succ] at h2
  set B := ∏ x ∈ range (2 * m), (RP (2 * H + 1) x).leadingCoeff * (1 / 4 : ℚ) ^ x
  set s := ∏ x ∈ range (2 * m), (-1 : ℚ) ^ x
  have hB : B ≠ 0 := prod_ne_zero_iff.2 fun q hq =>
    mul_ne_zero (ell_pos H q (by have := mem_range.1 hq; omega)).ne' (by positivity)
  have hs : s ≠ 0 := prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ (by norm_num)
  have l0 := (ell_pos H (2 * m) (by omega)).ne'
  have l1 := (ell_pos H (2 * m + 1) (by omega)).ne'
  have p0 : (-1 : ℚ) ^ (2 * m) = 1 := by rw [pow_mul]; simp
  have p1 : (-1 : ℚ) ^ (2 * m + 1) = -1 := by rw [pow_succ, p0]; ring
  rw [p0, p1] at h2
  unfold V
  unfold Dval at h2
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
  simp only [_root_.one_div_pow] at h2
  field_simp at h2
  field_simp
  push_cast at h2 ⊢
  linear_combination (-1 : ℚ) * h2
/-! ## (3) the Γ form of Conjecture B (even steps) -/

open Real in
lemma Gamma_half (j : ℕ) :
    Gamma ((j : ℝ) + 1 / 2) = ((2 * j).factorial : ℝ) * √π / (4 ^ j * j.factorial) := by
  induction j with
  | zero => simpa using Real.Gamma_one_half_eq
  | succ j ih =>
    rw [show ((j + 1 : ℕ) : ℝ) + 1 / 2 = ((j : ℝ) + 1 / 2) + 1 by push_cast; ring,
      Real.Gamma_add_one (by positivity), ih, show 2 * (j + 1) = (2 * j + 1) + 1 by ring,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- Conjecture B's ratio `V_{d+1}/V_d = K · n! Γ(n/2-d+1) / (Γ(n/2-d+1/2) Γ((n-d+2)/2)²)`. -/
noncomputable def crB (H d : ℕ) (K : ℝ) : ℝ :=
  K * ((2 * H + 1).factorial : ℝ) * Real.Gamma ((2 * (H : ℝ) + 1) / 2 - (d : ℝ) + 1)
    / (Real.Gamma ((2 * (H : ℝ) + 1) / 2 - (d : ℝ) + 1 / 2) * Real.Gamma ((2 * (H : ℝ) + 1 - d + 2) / 2) ^ 2)
/-- `K_d` for `d = 2k` and `d = 2k+1`. -/
noncomputable def Ke (k : ℕ) : ℝ := (((2 * k).factorial : ℝ) / k.factorial) ^ 2 * √Real.pi
noncomputable def Ko (k : ℕ) : ℝ := (2 * 4 ^ k * (k.factorial : ℝ)) ^ 2 / √Real.pi

/-- **Theorem Bodd ⇒ Conjecture B (even steps).**  For `n = 2H+1` and `2m+2 ≤ H+1`:
`V_{2m+2} = V_{2m} · ρ_{2m} · ρ_{2m+1}` with Conjecture B's Γ ratios. -/
theorem conjB_even (H m : ℕ) (hm : 2 * (m + 1) ≤ H + 1) :
    (V H (m + 1) : ℝ) = V H m * (crB H (2 * m) (Ke m) * crB H (2 * m + 1) (Ko m)) := by
  rw [V_succ H m hm]
  obtain ⟨r, rfl⟩ : ∃ r, H = 2 * m + 1 + r := ⟨H - (2 * m + 1), by omega⟩
  rw [ell_closed _ _ (by omega), hN_closed _ _ (by omega),
    show 2 * (2 * m + 1 + r) + 1 - 2 * m = 2 * m + 2 * r + 3 by omega,
    show 2 * m + 1 + r - 2 * m = r + 1 by omega,
    show 2 * (2 * m + 1 + r) + 1 - 2 * (2 * m) = 2 * r + 3 by omega,
    show 2 * (2 * m + 1 + r) + 1 = 4 * m + 2 * r + 3 by ring,
    show 2 * (2 * m + 1 + r) = 4 * m + 2 * r + 2 by ring,
    Nat.cast_choose ℚ (show 2 * m + 1 + r ≤ 4 * m + 2 * r + 2 by omega),
    Nat.cast_choose ℚ (show 2 * m ≤ 4 * m + 2 * r + 3 by omega),
    show 4 * m + 2 * r + 2 - (2 * m + 1 + r) = 2 * m + 1 + r by omega,
    show 4 * m + 2 * r + 3 - 2 * m = 2 * m + 2 * r + 3 by omega]
  have hs : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have G1 : Real.Gamma ((2 * ((2 * m + 1 + r : ℕ) : ℝ) + 1) / 2 - ((2 * m : ℕ) : ℝ) + 1)
      = ((2 * r + 4).factorial : ℝ) * √Real.pi / (4 ^ (r + 2) * (r + 2).factorial) := by
    rw [show (2 * ((2 * m + 1 + r : ℕ) : ℝ) + 1) / 2 - ((2 * m : ℕ) : ℝ) + 1 = ((r + 2 : ℕ) : ℝ) + 1 / 2 by
      push_cast; ring, Gamma_half, show 2 * (r + 2) = 2 * r + 4 by ring]
  have G2 : Real.Gamma ((2 * ((2 * m + 1 + r : ℕ) : ℝ) + 1) / 2 - ((2 * m : ℕ) : ℝ) + 1 / 2)
      = ((r + 1).factorial : ℝ) := by
    rw [show (2 * ((2 * m + 1 + r : ℕ) : ℝ) + 1) / 2 - ((2 * m : ℕ) : ℝ) + 1 / 2 = ((r + 1 : ℕ) : ℝ) + 1 by
      push_cast; ring, Real.Gamma_nat_eq_factorial]
  have G3 : Real.Gamma ((2 * ((2 * m + 1 + r : ℕ) : ℝ) + 1 - ((2 * m : ℕ) : ℝ) + 2) / 2)
      = ((2 * m + 2 * r + 4).factorial : ℝ) * √Real.pi / (4 ^ (m + r + 2) * (m + r + 2).factorial) := by
    rw [show (2 * ((2 * m + 1 + r : ℕ) : ℝ) + 1 - ((2 * m : ℕ) : ℝ) + 2) / 2 = ((m + r + 2 : ℕ) : ℝ) + 1 / 2 by
      push_cast; ring, Gamma_half, show 2 * (m + r + 2) = 2 * m + 2 * r + 4 by ring]
  have G4 : Real.Gamma ((2 * ((2 * m + 1 + r : ℕ) : ℝ) + 1) / 2 - ((2 * m + 1 : ℕ) : ℝ) + 1)
      = ((2 * r + 2).factorial : ℝ) * √Real.pi / (4 ^ (r + 1) * (r + 1).factorial) := by
    rw [show (2 * ((2 * m + 1 + r : ℕ) : ℝ) + 1) / 2 - ((2 * m + 1 : ℕ) : ℝ) + 1 = ((r + 1 : ℕ) : ℝ) + 1 / 2 by
      push_cast; ring, Gamma_half, show 2 * (r + 1) = 2 * r + 2 by ring]
  have G5 : Real.Gamma ((2 * ((2 * m + 1 + r : ℕ) : ℝ) + 1) / 2 - ((2 * m + 1 : ℕ) : ℝ) + 1 / 2)
      = (r.factorial : ℝ) := by
    rw [show (2 * ((2 * m + 1 + r : ℕ) : ℝ) + 1) / 2 - ((2 * m + 1 : ℕ) : ℝ) + 1 / 2 = (r : ℝ) + 1 by
      push_cast; ring, Real.Gamma_nat_eq_factorial]
  have G6 : Real.Gamma ((2 * ((2 * m + 1 + r : ℕ) : ℝ) + 1 - ((2 * m + 1 : ℕ) : ℝ) + 2) / 2)
      = ((m + r + 1).factorial : ℝ) := by
    rw [show (2 * ((2 * m + 1 + r : ℕ) : ℝ) + 1 - ((2 * m + 1 : ℕ) : ℝ) + 2) / 2 = ((m + r + 1 : ℕ) : ℝ) + 1 by
      push_cast; ring, Real.Gamma_nat_eq_factorial]
  unfold crB Ke Ko
  rw [G1, G2, G3, G4, G5, G6, show 2 * (2 * m + 1 + r) + 1 = 4 * m + 2 * r + 3 by ring]
  rw [show 2 * r + 4 = (2 * r + 3) + 1 by ring, Nat.factorial_succ (2 * r + 3),
    show 2 * r + 3 = (2 * r + 2) + 1 by ring, Nat.factorial_succ (2 * r + 2),
    show r + 2 = (r + 1) + 1 by ring, Nat.factorial_succ (r + 1), Nat.factorial_succ r,
    show 2 * m + 2 * r + 4 = (2 * m + 2 * r + 3) + 1 by ring, Nat.factorial_succ (2 * m + 2 * r + 3),
    show m + r + 2 = (m + r + 1) + 1 by ring, Nat.factorial_succ (m + r + 1),
    show 4 * m + 2 * r + 3 = (4 * m + 2 * r + 2) + 1 by ring, Nat.factorial_succ (4 * m + 2 * r + 2)]
  push_cast
  have := hs.ne'
  have h3 : (3 + (r : ℝ) * 2) ≠ 0 := by positivity
  ring_nf
  field_simp
  ring
lemma V_zero (H : ℕ) : V H 0 = 1 := by
  simp [V, VBvol]

/-- **Conjecture B (even `d`), proved:** `V^B_{2m} = ∏_{k<m} ρ_{2k} ρ_{2k+1}` with the Γ ratios, `n = 2H+1`, `2m ≤ H+1`. -/
theorem conjB_even_closed (H : ℕ) : ∀ m, 2 * m ≤ H + 1 →
    (V H m : ℝ) = ∏ k ∈ range m, (crB H (2 * k) (Ke k) * crB H (2 * k + 1) (Ko k))
  | 0, _ => by simp [V_zero]
  | m + 1, hm => by
    rw [prod_range_succ, conjB_even H m hm, conjB_even_closed H m (by omega)]
end Bali.ConjB

#print axioms Bali.ConjB.ell_closed
#print axioms Bali.ConjB.V_succ
#print axioms Bali.ConjB.conjB_even
#print axioms Bali.ConjB.conjB_even_closed
