import P699.EvenOdd

/-!
# Conjecture B for even `n = 2m`, every `d ≤ m - 1` (`m ≥ 3`) (Bali lab, 2026-11-02)
-/

open Finset Polynomial Matrix

namespace Bali.VE
open Bali.EvenPsi Bali.Chr Bali.Skew Bali.VG Bali.PfP Bali.VB Bali.GA Bali.OddB Bali.OG

/-- odd base `V_1 = V_0 · ρ_0`. -/
theorem conjBO_base (s : ℕ) :
    ((VBvol (fun h : Fin (s + 2 + 1 + 1) => yv (s + 2) (h : ℕ)) (nuV (s + 2)) 1 : ℚ) : ℝ)
      = VE (s + 2) 0 * crE (s + 3) 0 (Bali.ConjB.Ke 0) := by
  have h := V_oddstep (K := s + 2) (by omega) 0 (by omega)
  simp only [mul_zero, zero_add, co_zero, one_mul] at h
  rw [h, VE_zero]
  simp only [τ, TB_one]
  have hs : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have G1 : Real.Gamma (((s + 3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 3 / 2)
      = ((2 * s + 8).factorial : ℝ) * √Real.pi / (4 ^ (s + 4) * (s + 4).factorial) := by
    rw [show ((s + 3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 3 / 2 = ((s + 4 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (s + 4) = 2 * s + 8 by ring]
  have G2 : Real.Gamma (((s + 3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 1) = ((s + 3).factorial : ℝ) := by
    rw [show ((s + 3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 1 = ((s + 3 : ℕ) : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
  have G3 : Real.Gamma ((2 * ((s + 3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 1) / 2)
      = ((2 * s + 6).factorial : ℝ) * √Real.pi / (4 ^ (s + 3) * (s + 3).factorial) := by
    rw [show (2 * ((s + 3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 1) / 2 = ((s + 3 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (s + 3) = 2 * s + 6 by ring]
  have G4 : Real.Gamma ((2 * ((s + 3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 3) / 2)
      = ((2 * s + 8).factorial : ℝ) * √Real.pi / (4 ^ (s + 4) * (s + 4).factorial) := by
    rw [show (2 * ((s + 3 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) + 3) / 2 = ((s + 4 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half, show 2 * (s + 4) = 2 * s + 8 by ring]
  unfold crE Bali.ConjB.Ke
  rw [show (2 * 0 : ℕ) = 0 by ring, G1, G2, G3, G4, show 2 * (s + 3) = 2 * s + 6 by ring]
  have : ((2 * (s + 2) + 1 + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  push_cast
  have := hs.ne'
  field_simp
  rw [show 2 * (s + 2) + 1 + 1 = 2 * (s + 3) by ring, pow_mul]
  push_cast
  ring

/-- the constant `K_j` of Conjecture B. -/
noncomputable def Kc (j : ℕ) : ℝ := if j % 2 = 0 then Bali.ConjB.Ke (j / 2) else Bali.ConjB.Ko (j / 2)

lemma Kc_even (k : ℕ) : Kc (2 * k) = Bali.ConjB.Ke k := by simp [Kc]
lemma Kc_odd (k : ℕ) : Kc (2 * k + 1) = Bali.ConjB.Ko k := by
  simp [Kc, Nat.add_mod]; congr 1; omega

lemma evens (s k : ℕ) (hk : 2 * k ≤ s + 2) :
    (VE (s + 2) k : ℝ) = ∏ j ∈ range (2 * k), crE (s + 3) j (Kc j) := by
  rw [conjBE s k hk]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ih (by omega), show 2 * (k + 1) = 2 * k + 1 + 1 by ring, prod_range_succ, prod_range_succ,
      Kc_even, Kc_odd]
    ring

/-- **Conjecture B for even `n = 2m`** (`m = s+3 ≥ 3`), every `d ≤ m - 1`, shell form. -/
theorem conjB_evenN (s d : ℕ) (hd : d ≤ s + 2) :
    ((VBvol (fun h : Fin (s + 2 + 1 + 1) => yv (s + 2) (h : ℕ)) (nuV (s + 2)) d : ℚ) : ℝ)
      = ∏ j ∈ range d, crE (s + 3) j (Kc j) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' d
  · exact evens s k hd
  · rw [prod_range_succ, Kc_even, ← evens s k (by omega)]
    rcases k with _ | j
    · simpa using conjBO_base s
    · obtain ⟨r, hr⟩ : ∃ r, s = 2 * j + 1 + r := ⟨s - (2 * j + 1), by omega⟩
      subst hr
      have h := conjBO_step j r
      rw [show 2 * j + 3 + r = 2 * j + 1 + r + 2 by ring, show 2 * j + 4 + r = 2 * j + 1 + r + 3 by ring] at h
      exact h

end Bali.VE

#print axioms Bali.VE.conjB_evenN
