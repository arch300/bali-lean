import P699.EvenFull
import P699.ConjBAll

/-!
# Theorem B (formerly Conjecture B) for every `n ≥ 1` and every `d` (Bali lab, 2026-11-02)
-/

open Finset

namespace Bali.UN
open Bali.EvenPsi Bali.ShellX

/-! ## odd `n`: beyond the shells both sides vanish -/

lemma crB_beyond (H : ℕ) (K : ℝ) : Bali.ConjB.crB H (H + 1) K = 0 := by
  unfold Bali.ConjB.crB
  rw [show (2 * (H : ℝ) + 1) / 2 - ((H + 1 : ℕ) : ℝ) + 1 / 2 = 0 by push_cast; ring, Real.Gamma_zero]
  simp

theorem conjB_odd_all (H d : ℕ) :
    ((VBs (fun x : Fin (2 * H + 2) => (2 * (x : ℚ) - (2 * H + 1)) ^ 2)
        (fun x => ((2 * H + 1).choose (x : ℕ) : ℚ)) d : ℚ) : ℝ)
      = ∏ j ∈ range d, Bali.ConjB.crB H j (Bali.ConjBAll.Kc j) := by
  rcases Nat.lt_or_ge d (H + 2) with h | h
  · exact Bali.ConjBAll.conjB_x H d (by omega)
  · rw [VBx_eq_VBvol]
    have hz : Bali.VB.VBvol (Bali.Final.tS H) (Bali.Final.nuS H) d = 0 := by
      unfold Bali.VB.VBvol
      rw [powersetCard_eq_empty.2 (by rw [card_univ, Fintype.card_fin]; omega), sum_empty]
    rw [hz, Rat.cast_zero, eq_comm]
    exact prod_eq_zero (mem_range.2 (show H + 1 < d by omega)) (crB_beyond H _)

/-! ## even `n`: every `n = 2(K+1)`, every `d` -/

/-- shell form from the point form. -/
lemma shell_of_point (K d : ℕ) :
    Bali.VB.VBvol (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) d
      = VBs (fun x : Fin (2 * K + 3) => (2 * (x : ℚ) - (2 * K + 2)) ^ 2) (fun x => ((2 * K + 2).choose (x : ℕ) : ℚ)) d :=
  (Bali.ShellXE.VBx_eq_even K d).symm

/-- the shell form for every `K`, `d ≤ m = K+1`. -/
lemma shell_le (K d : ℕ) (hd : d ≤ K + 1) :
    ((Bali.VB.VBvol (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) d : ℚ) : ℝ)
      = ∏ j ∈ range d, Bali.VE.crE (K + 1) j (Bali.VE.Kc j) := by
  rcases K with _ | _ | s
  · rw [shell_of_point]; simpa using Bali.VE.conjB_n2 d (by omega)
  · rw [shell_of_point]; have h4 := Bali.VE.conjB_n4 d (by omega); norm_num at h4 ⊢; exact h4
  · exact Bali.VE.conjB_evenN_full s d (by omega)

theorem conjB_even_shell_all (K d : ℕ) :
    ((Bali.VB.VBvol (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) d : ℚ) : ℝ)
      = ∏ j ∈ range d, Bali.VE.crE (K + 1) j (Bali.VE.Kc j) := by
  rcases Nat.lt_or_ge d (K + 2) with h | h
  · exact shell_le K d (by omega)
  · rcases Nat.lt_or_ge d (K + 3) with h' | h'
    · obtain rfl : d = K + 2 := by omega
      have hv := Bali.EF.V_full K
      have hprev := shell_le K (K + 1) le_rfl
      rw [prod_range_succ, ← hprev, Bali.EF.crE_diag]
      have hn : ((K + 1 : ℕ) + 1 : ℚ) ≠ 0 := by positivity
      have hv' : Bali.VB.VBvol (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) (K + 1 + 1)
          = 4 ^ (K + 1) * ((2 * (K + 1)).factorial : ℚ)
            * Bali.VB.VBvol (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) (K + 1) / ((K + 1 : ℕ) + 1 : ℚ) := by
        rw [eq_div_iff hn]; linear_combination hv
      have e : Bali.VB.VBvol (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) (K + 2)
          = Bali.VB.VBvol (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) (K + 1 + 1) := rfl
      rw [e, hv']
      push_cast
      ring
    · have hz : Bali.VB.VBvol (fun h : Fin (K + 1 + 1) => yv K (h : ℕ)) (nuV K) d = 0 := by
        unfold Bali.VB.VBvol
        rw [powersetCard_eq_empty.2 (by rw [card_univ, Fintype.card_fin]; omega), sum_empty]
      rw [hz, Rat.cast_zero, eq_comm]
      exact prod_eq_zero (mem_range.2 (show K + 1 + 1 < d by omega)) (Bali.EF.crE_beyond (K + 1) _)

/-- **even `n = 2m` (`m ≥ 1`), point form, every `d`.** -/
theorem conjB_even_all (K d : ℕ) :
    ((VBs (fun x : Fin (2 * K + 3) => (2 * (x : ℚ) - (2 * K + 2)) ^ 2)
        (fun x => ((2 * K + 2).choose (x : ℕ) : ℚ)) d : ℚ) : ℝ)
      = ∏ j ∈ range d, Bali.VE.crE (K + 1) j (Bali.VE.Kc j) := by
  rw [← shell_of_point]; exact conjB_even_shell_all K d

end Bali.UN

#print axioms Bali.UN.conjB_odd_all
#print axioms Bali.UN.conjB_even_all
