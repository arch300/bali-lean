import P699.Bridge2
import P699.GaussAbs
import P699.CarlsonShift
import P699.ZonoFinal

/-!
# The real-`n` continuation for every even `d` (Bali lab, 2026-11-05)
-/

open Finset Filter

namespace Bali.GE
open GaussTarget Bali.PC Bali.GC Bali.GDB Bali.PfP Bali.VB Bali.GAbs Bali.BR2 Bali.ZF Bali.ZV Bali.CS

/-- Past `n` the truncation does not change. -/
theorem VTr_stable (n m N : ℕ) (hN : n ≤ N) : VTr (n : ℝ) m N = VTr (n : ℝ) m n := by
  rw [VTr_eq_sum, VTr_eq_sum]
  symm
  apply sum_subset (powersetCard_mono (range_mono (by omega)))
  intro S hS hS'
  have hc : S.card = 2 * m := (mem_powersetCard.1 hS).2
  have hnot : ¬ S ⊆ range (n + 1) := fun h => hS' (mem_powersetCard.2 ⟨h, hc⟩)
  obtain ⟨x, hx, hxn⟩ := not_subset.mp hnot
  have hlt : n < x := by simpa using hxn
  unfold V
  rw [dif_pos hc, prod_orderEmb S _ hc (gchoose (n : ℝ))]
  rw [prod_eq_zero hx (by rw [gchoose_natCast, Nat.choose_eq_zero_of_lt hlt]; simp), zero_mul]

/-- The value at an integer, from the main theorem over `ℚ`. -/
theorem VTr_int (n m : ℕ) (hm : 1 ≤ m) (hn : 2 * m ≤ n + 1) :
    VTr (n : ℝ) m n = ((RHS n (2 * m) : ℚ) : ℝ) := by
  rw [← main_V n (2 * m) (by omega) hn]
  unfold VTr VBvol
  push_cast
  refine sum_congr rfl fun S _ => ?_
  split_ifs with h
  · push_cast
    simp only [tt, nu, tZ, nuZ, gchoose_natCast]
    push_cast
    rfl
  · simp

/-- The constant linking the Pfaffian to the volume. -/
noncomputable def Pj (m : ℕ) : ℝ :=
  pfP (J0 m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) * sgnPairs (2 * m)

theorem Pj_ne (m : ℕ) : Pj m ≠ 0 := by
  have hJ : pfP (J0 m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) ≠ 0 := by
    rw [pfP_J0]; exact pfP_Om_ne_zero m
  have hS : (sgnPairs (2 * m) : ℝ) ≠ 0 := by
    unfold sgnPairs
    exact prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr fun _ _ => by norm_num
  exact mul_ne_zero hJ hS

/-- At an integer the Pfaffian is `Pj` times the value of the main theorem. -/
theorem pf_int (n m : ℕ) (hm : 1 ≤ m) (hn : 2 * m ≤ n) :
    pfP (fun a b : Fin m × Fin 2 => skM (n : ℝ) (eι m a : ℕ) (eι m b : ℕ)) =
      Pj m * ((RHS n (2 * m) : ℚ) : ℝ) := by
  have hc : ((2 * m : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  push_cast at hc
  have ht := VTr_tendsto (n : ℝ) m (by linarith)
  have hconst : Tendsto (fun N => VTr (n : ℝ) m N) atTop (nhds (VTr (n : ℝ) m n)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n] with N hN
    exact (VTr_stable n m N hN).symm
  have hu := tendsto_nhds_unique ht hconst
  rw [VTr_int n m hm (by omega)] at hu
  have hP := Pj_ne m
  unfold Pj at hP ⊢
  rw [div_eq_iff hP] at hu
  rw [hu]; ring

theorem Zp_cast (n d : ℕ) (hd : 1 ≤ d) :
    ∏ i ∈ range (d - 1), ((n : ℂ) - i) ^ (d - 2 - 2 * i) = ((Zp n d : ℚ) : ℂ) := by
  unfold Zp
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [prod_range_succ, show e + 1 - 1 = e by omega, show e + 1 - 2 - 2 * e = 0 by omega]
  push_cast
  simp

theorem Wn_cast (n d : ℕ) (hn : d ≤ n) :
    ∏ i ∈ Ico (d - 1 - d / 2) (d - 1), (((n : ℂ) - i) * cb ((n : ℂ) - i)) = ((Wn n d : ℚ) : ℂ) := by
  unfold Wn
  rw [Rat.cast_prod]
  refine prod_congr rfl fun i hi => ?_
  have hi2 : i < d - 1 := (mem_Ico.mp hi).2
  have hin : i ≤ n := by omega
  have e : (n : ℂ) - i = ((n - i : ℕ) : ℂ) := by rw [Nat.cast_sub hin]
  rw [e, cb_natCast]
  unfold Tc
  rw [Nat.centralBinom_eq_two_mul_choose]
  push_cast
  ring

theorem Gc_int (n m : ℕ) (hm : 1 ≤ m) (hn : 2 * m ≤ n) :
    Gc m (n : ℂ) = Pc ((Pj m * ((Kd (2 * m) : ℚ) : ℝ) : ℝ) : ℂ) (2 * m) (n : ℂ) := by
  have hc : ((2 * m : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  push_cast at hc
  have hG := Gc_real (w := (n : ℝ)) m (by linarith)
  rw [pf_int n m hm hn, Complex.ofReal_natCast] at hG
  have h4 : (((4 : ℝ) ^ (n : ℝ) : ℝ) : ℂ) ^ m = (2 : ℂ) ^ (2 * m * n) := by
    rw [Real.rpow_natCast]
    push_cast
    rw [← pow_mul, show (4 : ℂ) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1
    ring
  have h2 : (2 : ℂ) ^ (2 * m * n) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [h4] at hG
  unfold Pc
  rw [Zp_cast n (2 * m) (by omega), Wn_cast n (2 * m) hn]
  apply mul_left_cancel₀ h2
  rw [← hG]
  unfold RHS
  push_cast
  ring

theorem Gc_eq (m : ℕ) (hm : 1 ≤ m) : ∀ z : ℂ, (2 * m : ℝ) - 1 < z.re →
    Gc m z = Pc ((Pj m * ((Kd (2 * m) : ℚ) : ℝ) : ℝ) : ℂ) (2 * m) z := by
  set κ : ℂ := ((Pj m * ((Kd (2 * m) : ℚ) : ℝ) : ℝ) : ℂ) with hκ
  have hs : (((2 * m - 1 : ℕ) : ℕ) : ℝ) = (2 * m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hp := diff_poly m κ
  rw [← hs] at hp
  have key := carlson_shift (2 * m - 1) hp (fun n hn => by
    rw [Gc_int n m hm (by omega), sub_self])
  intro z hz
  exact sub_eq_zero.mp (key z (by rw [hs]; exact hz))

/-- **The real-`n` continuation for every even `d = 2m`.** The absolutely convergent sum equals the product
formula, with `2^(dn)` written `(4^w)^m`. -/
theorem even_value (m : ℕ) (hm : 1 ≤ m) (w : ℝ) (hw : (2 * m : ℝ) - 1 < w) :
    ((∑' S : {S : Finset ℕ // S.card = 2 * m}, V w (2 * m) S : ℝ) : ℂ) =
      (((4 : ℝ) ^ w : ℝ) : ℂ) ^ m * Pc (((Kd (2 * m) : ℚ) : ℝ) : ℂ) (2 * m) (w : ℂ) := by
  have hc : ((2 * m : ℕ) : ℝ) - 1 < w := by push_cast; exact hw
  have h1 := tendsto_partial w (2 * m) hc (by omega)
  have h2 := VTr_tendsto w m hw
  simp only [← VTr_eq_sum] at h1
  have hu := tendsto_nhds_unique h1 h2
  rw [hu, show pfP (J0 m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) * sgnPairs (2 * m) = Pj m from rfl]
  have hP := Pj_ne m
  rw [Complex.ofReal_div, Gc_real m hw, Gc_eq m hm (w : ℂ) (by simpa using hw)]
  unfold Pc
  have hPc : ((Pj m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hP
  push_cast
  field_simp

end Bali.GE

#print axioms Bali.GE.Gc_eq
#print axioms Bali.GE.even_value
