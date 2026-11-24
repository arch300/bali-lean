import P699.Bridge
import P699.GcC
import P699.GaussDeBruijn

/-!
# Lifting the bridge: the Pfaffian over `ℂ` at real points (Bali lab, 2026-11-05)
-/

open Finset

namespace Bali.BR2
open GaussTarget Bali.PC Bali.BR Bali.GC Bali.GDB Bali.PfP

variable {w : ℝ}

lemma cast_sub (w : ℝ) (k : ℕ) : ((w : ℂ) - k) = ((w - k : ℝ) : ℂ) := by push_cast; ring

lemma four_split (w : ℝ) (k : ℕ) : (4 : ℝ) ^ (w - k) = (4 : ℝ) ^ w / 4 ^ k := by
  rw [Real.rpow_sub (by norm_num), Real.rpow_natCast]

lemma two_two (M : ℝ) : (2 : ℝ) ^ M * (2 : ℝ) ^ M = (4 : ℝ) ^ M := by
  rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num

theorem bN_real (k t : ℕ) (h : (k : ℝ) < w) :
    ((Bsum (w - k) t : ℝ) : ℂ) = ((4 : ℝ) ^ w : ℝ) * bN k t (w : ℂ) := by
  rw [Bsum_all (w - k) (by linarith) t, four_split]
  unfold bN
  rw [cast_sub, cb_ofReal, rr_ofReal]
  push_cast
  ring

theorem hP_real (k u : ℕ) (h : (k : ℝ) < w) :
    ((Hz (w - k) (w - k) ((u : ℤ) + 1) : ℝ) : ℂ) = ((4 : ℝ) ^ w : ℝ) * hP k u (w : ℂ) := by
  have hM : 0 < w - k := by linarith
  rw [Hz_closed_pos _ hM, two_two, four_split]
  have hsum : ((∑ t ∈ range u, Bsum (w - k) (t + 1) : ℝ) : ℂ) =
      ((4 : ℝ) ^ w : ℝ) * ∑ t ∈ range u, bN k (t + 1) (w : ℂ) := by
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun t _ => ?_
    have := bN_real (w := w) k (t + 1) h
    push_cast at this ⊢
    exact this
  rw [Complex.ofReal_sub, hsum]
  have h0 := bN_real (w := w) k 0 h
  unfold hP
  rw [Complex.ofReal_div, Complex.ofReal_sub, h0]
  push_cast
  ring

theorem hN_real (k u : ℕ) (h : (k : ℝ) < w) :
    ((Hz (w - k) (w - k) (-(u : ℤ)) : ℝ) : ℂ) = ((4 : ℝ) ^ w : ℝ) * hN k u (w : ℂ) := by
  have hM : 0 < w - k := by linarith
  have hc := Hz_complement (w - k) (w - k) hM hM (-(u : ℤ))
  rw [show (1 : ℤ) - -(u : ℤ) = (u : ℤ) + 1 by ring, two_two, four_split] at hc
  have e : Hz (w - k) (w - k) (-(u : ℤ)) = (4 : ℝ) ^ w / 4 ^ k - Hz (w - k) (w - k) ((u : ℤ) + 1) := by
    linarith
  rw [e, Complex.ofReal_sub, hP_real k u h]
  unfold hN
  push_cast
  ring

theorem Hc_real (k : ℕ) (s : ℤ) (h : (k : ℝ) < w) :
    ((Hz (w - k) (w - k) s : ℝ) : ℂ) = ((4 : ℝ) ^ w : ℝ) * Hc k s (w : ℂ) := by
  unfold Hc
  by_cases hs : 1 ≤ s
  · have e : s = (((s - 1).toNat : ℕ) : ℤ) + 1 := by omega
    simp only [hs, if_true]
    conv_lhs => rw [e]
    exact hP_real k _ h
  · have e : s = -(((-s).toNat : ℕ) : ℤ) := by omega
    simp only [hs, if_false]
    conv_lhs => rw [e]
    exact hN_real k _ h

lemma ffr_ofReal (w : ℝ) (j : ℕ) : ((ffr w j : ℝ) : ℂ) = ffc j (w : ℂ) := by
  simp [ffr, ffc]

theorem FMc_real (j l : ℕ) (hj : (j : ℝ) < w) (hl : (l : ℝ) < w) :
    ((FM w j l : ℝ) : ℂ) = ((4 : ℝ) ^ w : ℝ) * FMc j l (w : ℂ) := by
  unfold FMc
  by_cases h : j ≤ l
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have hM : 0 < w - j - k := by push_cast at hl; linarith
    have ew : w - (j : ℝ) - k = w - ((j + k : ℕ) : ℝ) := by push_cast; ring
    have hs : ∀ s : ℤ, ((Hz (w - j - k) (w - j - k) s : ℝ) : ℂ) =
        ((4 : ℝ) ^ w : ℝ) * Hc (j + k) s (w : ℂ) := fun s => by
      rw [ew]; exact Hc_real (j + k) s hl
    rw [FM_value_le w j k hM]
    simp only [h, ite_true, Nat.add_sub_cancel_left]
    rw [Complex.ofReal_mul, Complex.ofReal_mul, ffr_ofReal, ffr_ofReal, Complex.ofReal_sum]
    have hsum : ∑ x ∈ range (k + 1), (((k.choose x : ℝ) * Hz (w - j - k) (w - j - k) (1 - (k : ℤ) + x) : ℝ) : ℂ) =
        ((4 : ℝ) ^ w : ℝ) * ∑ x ∈ range (k + 1), (k.choose x : ℂ) * Hc (j + k) (1 - (k : ℤ) + x) (w : ℂ) := by
      rw [mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [Complex.ofReal_mul, hs]
      push_cast
      ring
    rw [hsum]
    ring
  · have hle : l ≤ j := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hM : 0 < w - l - k := by push_cast at hj; linarith
    have ew : w - (l : ℝ) - k = w - ((l + k : ℕ) : ℝ) := by push_cast; ring
    have hs : ∀ s : ℤ, ((Hz (w - l - k) (w - l - k) s : ℝ) : ℂ) =
        ((4 : ℝ) ^ w : ℝ) * Hc (l + k) s (w : ℂ) := fun s => by
      rw [ew]; exact Hc_real (l + k) s hj
    have e2 : (2 : ℝ) ^ (w - l - k) * (2 : ℝ) ^ (w - l) = (4 : ℝ) ^ w / 2 ^ (l + k + l) := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_natCast,
        ← two_two w, pow_add, pow_add]
      have : (2 : ℝ) ^ w ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
      field_simp
    rw [FM_value_ge w l k hM]
    simp only [h, ite_false, Nat.add_sub_cancel_left]
    rw [Complex.ofReal_mul, Complex.ofReal_mul, ffr_ofReal, ffr_ofReal, Complex.ofReal_sub, e2, Complex.ofReal_sum]
    have hsum : ∑ x ∈ range (k + 1), (((k.choose x : ℝ) * Hz (w - l - k) (w - l - k) (-(k : ℤ) + x) : ℝ) : ℂ) =
        ((4 : ℝ) ^ w : ℝ) * ∑ x ∈ range (k + 1), (k.choose x : ℂ) * Hc (l + k) (-(k : ℤ) + x) (w : ℂ) := by
      rw [mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [Complex.ofReal_mul, hs]
      push_cast
      ring
    rw [hsum]
    push_cast
    ring

theorem OMc_real (a b : ℕ) (ha : (a : ℝ) < w) (hb : (b : ℝ) < w) :
    ((OM w a b : ℝ) : ℂ) = ((4 : ℝ) ^ w : ℝ) * OMc a b (w : ℂ) := by
  rw [OM_eq_sum_FM w a b ha hb, Complex.ofReal_sum]
  unfold OMc
  rw [mul_sum]
  refine sum_congr rfl ?_
  rintro ⟨j, l⟩ hp
  rw [mem_product, mem_range, mem_range] at hp
  have hj : (j : ℝ) < w := lt_of_le_of_lt (by exact_mod_cast (by omega : j ≤ a)) ha
  have hl : (l : ℝ) < w := lt_of_le_of_lt (by exact_mod_cast (by omega : l ≤ b)) hb
  rw [Complex.ofReal_mul, Complex.ofReal_mul, FMc_real j l hj hl]
  push_cast
  ring

theorem skc_real (e f : ℕ) (he : (e : ℝ) < w) (hf : (f : ℝ) < w) :
    ((skM w e f : ℝ) : ℂ) = ((4 : ℝ) ^ w : ℝ) * skc e f (w : ℂ) := by
  rw [skM_eq_OM w e f he hf]
  unfold skc
  rw [Complex.ofReal_mul, Complex.ofReal_sub, OMc_real e f he hf, OMc_real f e hf he]
  push_cast
  ring

/-- **The bridge for even `d = 2m`.** -/
theorem Gc_real (m : ℕ) (hw : (2 * m : ℝ) - 1 < w) :
    ((pfP (fun a b : Fin m × Fin 2 => skM w (eι m a : ℕ) (eι m b : ℕ)) : ℝ) : ℂ) =
      (((4 : ℝ) ^ w : ℝ) : ℂ) ^ m * Gc m (w : ℂ) := by
  have lt : ∀ c : Fin m × Fin 2, (((eι m c : Fin (2 * m)) : ℕ) : ℝ) < w := by
    intro c
    have h1 : ((eι m c : Fin (2 * m)) : ℕ) + 1 ≤ 2 * m := (eι m c).isLt
    have h2 : (((eι m c : Fin (2 * m)) : ℕ) : ℝ) + 1 ≤ 2 * m := by exact_mod_cast h1
    linarith
  unfold Gc pfP
  rw [Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_prod]
  have : ∏ i : Fin m, ((skM w (eι m (σ (i, 0)) : ℕ) (eι m (σ (i, 1)) : ℕ) : ℝ) : ℂ) =
      (((4 : ℝ) ^ w : ℝ) : ℂ) ^ m * ∏ i : Fin m, skc (eι m (σ (i, 0)) : ℕ) (eι m (σ (i, 1)) : ℕ) (w : ℂ) := by
    rw [prod_congr rfl fun i _ => skc_real _ _ (lt _) (lt _), prod_mul_distrib, prod_const, card_univ,
      Fintype.card_fin]
  rw [this]
  push_cast
  ring

end Bali.BR2

#print axioms Bali.BR2.Gc_real
