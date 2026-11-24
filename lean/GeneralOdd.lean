import P699.GeneralEven
import P699.GaussOdd

/-!
# The real-`n` continuation for every odd `d` (Bali lab, 2026-11-05)
-/

open Finset Filter

namespace Bali.GO
open GaussTarget Bali.PC Bali.GC Bali.GDB Bali.PfP Bali.VB Bali.GAbs Bali.BR2 Bali.ZF Bali.ZV Bali.CS
  Bali.GOdd Bali.GE

theorem hasSum_ff (w : ℝ) (j : ℕ) (hj : (j : ℝ) < w) :
    HasSum (fun x : ℕ => ffr (x : ℝ) j * gchoose w x) (ffr w j * (2 : ℝ) ^ (w - j)) := by
  set f : ℕ → ℝ := fun x => ffr (x : ℝ) j * gchoose w x with hf
  have h1 : HasSum (fun n => f (n + j)) (ffr w j * (2 : ℝ) ^ (w - j) - ∑ i ∈ range j, f i) := by
    have h0 : ∑ i ∈ range j, f i = 0 := sum_eq_zero fun i hi => by
      have : ffr (i : ℝ) j = 0 := falling_eq_zero j i (mem_range.mp hi)
      simp [f, this]
    rw [h0, sub_zero]
    have := (gchoose_hasSum_two (w - j) (by linarith)).mul_left (ffr w j)
    convert this using 1
    funext n
    exact gchoose_absorb j w n
  exact (hasSum_nat_add_iff' j).mp h1

theorem mom_eq (w : ℝ) (e : ℕ) (he : (e : ℝ) < w) :
    mom w e = (-1 : ℝ) ^ e * ∑ j ∈ range (e + 1),
      (e.stirlingSecond j : ℝ) * (ffr w j * (2 : ℝ) ^ (w - j)) := by
  have hs : HasSum (fun x : ℕ => (-1 : ℝ) ^ e * ∑ j ∈ range (e + 1),
      (e.stirlingSecond j : ℝ) * (ffr (x : ℝ) j * gchoose w x))
      ((-1 : ℝ) ^ e * ∑ j ∈ range (e + 1), (e.stirlingSecond j : ℝ) * (ffr w j * (2 : ℝ) ^ (w - j))) := by
    apply HasSum.mul_left
    apply hasSum_sum
    intro j hj
    have hle : (j : ℝ) ≤ e := by exact_mod_cast (by simpa [Nat.lt_succ_iff] using hj : j ≤ e)
    exact (hasSum_ff w j (lt_of_le_of_lt hle he)).mul_left _
  rw [← hs.tsum_eq]
  unfold mom
  refine tsum_congr fun x => ?_
  have hpow : (x : ℝ) ^ e = ∑ i ∈ range (e + 1), (e.stirlingSecond i : ℝ) * ffr (x : ℝ) i := by
    have := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial x e
    have h2 : ((x ^ e : ℕ) : ℝ) =
        ((∑ i ∈ range (e + 1), e.stirlingSecond i * x.descFactorial i : ℕ) : ℝ) := by rw [← this]
    push_cast at h2
    rw [h2]
    exact sum_congr rfl fun i _ => by rw [ffr_natCast]
  rw [neg_pow, hpow]
  simp only [mul_sum, sum_mul]
  exact sum_congr rfl fun j _ => by ring

/-- `mom z e / 2^z`. -/
noncomputable def momc (e : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ e * ∑ j ∈ range (e + 1), (e.stirlingSecond j : ℂ) * (ffc j z * ((2 : ℂ) ^ j)⁻¹)

theorem momc_poly (t : ℝ) (e : ℕ) : PolyH t (momc e) :=
  (PolyH.const t _).mul (PolyH.finset_sum _ fun _ _ =>
    (PolyH.const t _).mul ((ffc_poly t _).mul (PolyH.const t _)))

theorem mom_real {w : ℝ} (e : ℕ) (he : (e : ℝ) < w) :
    ((mom w e : ℝ) : ℂ) = ((2 : ℝ) ^ w : ℝ) * momc e (w : ℂ) := by
  rw [mom_eq w e he]
  unfold momc
  rw [Complex.ofReal_mul, Complex.ofReal_sum]
  have : ∑ j ∈ range (e + 1), (((e.stirlingSecond j : ℝ) * (ffr w j * (2 : ℝ) ^ (w - j)) : ℝ) : ℂ) =
      ((2 : ℝ) ^ w : ℝ) * ∑ j ∈ range (e + 1), (e.stirlingSecond j : ℂ) * (ffc j (w : ℂ) * ((2 : ℂ) ^ j)⁻¹) := by
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Complex.ofReal_mul, Complex.ofReal_mul,
      ffr_ofReal]
    push_cast
    ring
  rw [this]
  push_cast
  ring

/-- The normalized bordered matrix. -/
noncomputable def Ghc (m : ℕ) (a b : Fin (m + 1) × Fin 2) (z : ℂ) : ℂ :=
  if sl a < 2 * m + 1 then
    (if sl b < 2 * m + 1 then skc (sl a) (sl b) z else momc (sl a) z)
  else (if sl b < 2 * m + 1 then -momc (sl b) z else 0)

noncomputable def Goc (m : ℕ) (z : ℂ) : ℂ := pfP (fun a b => Ghc m a b z)

theorem Goc_poly (m : ℕ) : PolyH (2 * m : ℝ) (Goc m) := by
  have le : ∀ c : Fin (m + 1) × Fin 2, sl c < 2 * m + 1 → ((sl c : ℕ) : ℝ) ≤ 2 * m := by
    intro c h
    exact_mod_cast (show sl c ≤ 2 * m by omega)
  refine pfP_poly _ fun a b => ?_
  unfold Ghc
  by_cases ha : sl a < 2 * m + 1 <;> by_cases hb : sl b < 2 * m + 1 <;> simp only [ha, hb, ite_true, ite_false]
  · exact skc_poly _ _ _ (le a ha) (le b hb)
  · exact momc_poly _ _
  · exact (momc_poly _ _).neg_one_mul
  · exact PolyH.const _ 0

/-- The scale of a row. -/
noncomputable def cc (w : ℝ) (m : ℕ) (a : Fin (m + 1) × Fin 2) : ℂ :=
  if sl a < 2 * m + 1 then (((2 : ℝ) ^ w : ℝ) : ℂ) else 1

theorem prod_cc (w : ℝ) (m : ℕ) : ∏ a, cc w m a = (((2 : ℝ) ^ w : ℝ) : ℂ) ^ (2 * m + 1) := by
  have h1 : ∏ a, cc w m a = ∏ i : Fin (2 * (m + 1)),
      (if (i : ℕ) < 2 * m + 1 then (((2 : ℝ) ^ w : ℝ) : ℂ) else 1) :=
    Fintype.prod_equiv (eι (m + 1)) _ _ fun a => rfl
  rw [h1, Fin.prod_univ_eq_prod_range (fun i => if i < 2 * m + 1 then (((2 : ℝ) ^ w : ℝ) : ℂ) else 1),
    show 2 * (m + 1) = (2 * m + 1) + 1 by ring, prod_range_succ]
  simp only [lt_irrefl, ite_false, mul_one]
  rw [prod_congr rfl fun i hi => if_pos (mem_range.mp hi), prod_const, card_range]

theorem Ginf_entry {w : ℝ} (m : ℕ) (hw : (2 * m : ℝ) < w) (a b : Fin (m + 1) × Fin 2) :
    ((Ginf w m a b : ℝ) : ℂ) = cc w m a * cc w m b * Ghc m a b (w : ℂ) := by
  have lt : ∀ c : Fin (m + 1) × Fin 2, sl c < 2 * m + 1 → ((sl c : ℕ) : ℝ) < w := by
    intro c h
    have h2 : ((sl c : ℕ) : ℝ) ≤ 2 * m := by exact_mod_cast (show sl c ≤ 2 * m by omega)
    linarith
  have h4 : (((4 : ℝ) ^ w : ℝ) : ℂ) = (((2 : ℝ) ^ w : ℝ) : ℂ) * (((2 : ℝ) ^ w : ℝ) : ℂ) := by
    rw [← two_two, Complex.ofReal_mul]
  unfold Ginf cc Ghc
  by_cases ha : sl a < 2 * m + 1 <;> by_cases hb : sl b < 2 * m + 1 <;> simp only [ha, hb, ite_true, ite_false]
  · rw [skc_real _ _ (lt a ha) (lt b hb), h4]
  · rw [mom_real _ (lt a ha)]; ring
  · rw [Complex.ofReal_neg, mom_real _ (lt b hb)]; ring
  · simp

theorem Goc_real {w : ℝ} (m : ℕ) (hw : (2 * m : ℝ) < w) :
    ((pfP (Ginf w m) : ℝ) : ℂ) = (((2 : ℝ) ^ w : ℝ) : ℂ) ^ (2 * m + 1) * Goc m (w : ℂ) := by
  rw [← prod_cc]
  unfold Goc pfP
  rw [Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_prod, prod_congr rfl fun i _ => Ginf_entry m hw _ _,
    prod_mul_distrib]
  have hc : ∏ i : Fin (m + 1), (cc w m (σ (i, 0)) * cc w m (σ (i, 1))) = ∏ a, cc w m a := by
    rw [← Equiv.prod_comp σ, Fintype.prod_prod_type]
    exact prod_congr rfl fun i _ => (Fin.prod_univ_two (fun y => cc w m (σ (i, y)))).symm
  rw [hc]
  push_cast
  ring

noncomputable def Pjo (m : ℕ) : ℝ :=
  pfP (J0 (m + 1) : Matrix (Fin (m + 1) × Fin 2) (Fin (m + 1) × Fin 2) ℝ) * sgnPairs (2 * m + 1)

theorem Pjo_ne (m : ℕ) : Pjo m ≠ 0 := by
  have hJ : pfP (J0 (m + 1) : Matrix (Fin (m + 1) × Fin 2) (Fin (m + 1) × Fin 2) ℝ) ≠ 0 := by
    rw [pfP_J0]; exact pfP_Om_ne_zero (m + 1)
  have hS : (sgnPairs (2 * m + 1) : ℝ) ≠ 0 := by
    unfold sgnPairs
    exact prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr fun _ _ => by norm_num
  exact mul_ne_zero hJ hS

theorem VB_stable (n d N : ℕ) (hN : n ≤ N) :
    VBvol (tt N) (nu (n : ℝ) N) d = VBvol (tt n) (nu (n : ℝ) n) d := by
  rw [VB_eq_sum, VB_eq_sum]
  symm
  apply sum_subset (powersetCard_mono (range_mono (by omega)))
  intro S hS hS'
  have hc : S.card = d := (mem_powersetCard.1 hS).2
  have hnot : ¬ S ⊆ range (n + 1) := fun h => hS' (mem_powersetCard.2 ⟨h, hc⟩)
  obtain ⟨x, hx, hxn⟩ := not_subset.mp hnot
  have hlt : n < x := by simpa using hxn
  unfold V
  rw [dif_pos hc, prod_orderEmb S _ hc (gchoose (n : ℝ))]
  rw [prod_eq_zero hx (by rw [gchoose_natCast, Nat.choose_eq_zero_of_lt hlt]; simp), zero_mul]

theorem VB_int (n d : ℕ) (hd : 2 ≤ d) (hn : d ≤ n + 1) :
    VBvol (tt n) (nu (n : ℝ) n) d = ((RHS n d : ℚ) : ℝ) := by
  rw [← main_V n d hd hn]
  unfold VBvol
  push_cast
  refine sum_congr rfl fun S _ => ?_
  split_ifs with h
  · push_cast
    simp only [tt, nu, tZ, nuZ, gchoose_natCast]
    push_cast
    rfl
  · simp

theorem pfo_int (n m : ℕ) (hm : 1 ≤ m) (hn : 2 * m + 1 ≤ n) :
    pfP (Ginf (n : ℝ) m) = Pjo m * ((RHS n (2 * m + 1) : ℚ) : ℝ) := by
  have hc : ((2 * m + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  push_cast at hc
  have ht := VTrO_tendsto (n : ℝ) m (by linarith)
  have hconst : Tendsto (fun N => VBvol (tt N) (nu (n : ℝ) N) (2 * m + 1)) atTop
      (nhds (VBvol (tt n) (nu (n : ℝ) n) (2 * m + 1))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n] with N hN
    exact (VB_stable n _ N hN).symm
  have hu := tendsto_nhds_unique ht hconst
  rw [VB_int n _ (by omega) (by omega)] at hu
  have hP := Pjo_ne m
  unfold Pjo at hP ⊢
  rw [div_eq_iff hP] at hu
  rw [hu]; ring

theorem Goc_int (n m : ℕ) (hm : 1 ≤ m) (hn : 2 * m + 1 ≤ n) :
    Goc m (n : ℂ) = Pc ((Pjo m * ((Kd (2 * m + 1) : ℚ) : ℝ) : ℝ) : ℂ) (2 * m + 1) (n : ℂ) := by
  have hc : ((2 * m + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  push_cast at hc
  have hG := Goc_real (w := (n : ℝ)) m (by linarith)
  rw [pfo_int n m hm hn, Complex.ofReal_natCast] at hG
  have h4 : (((2 : ℝ) ^ (n : ℝ) : ℝ) : ℂ) ^ (2 * m + 1) = (2 : ℂ) ^ ((2 * m + 1) * n) := by
    rw [Real.rpow_natCast]
    push_cast
    rw [← pow_mul, mul_comm]
  have h2 : (2 : ℂ) ^ ((2 * m + 1) * n) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [h4] at hG
  unfold Pc
  rw [Zp_cast n (2 * m + 1) (by omega), Wn_cast n (2 * m + 1) hn]
  apply mul_left_cancel₀ h2
  rw [← hG]
  unfold RHS
  push_cast
  ring

theorem Goc_eq (m : ℕ) (hm : 1 ≤ m) : ∀ z : ℂ, (2 * m : ℝ) < z.re →
    Goc m z = Pc ((Pjo m * ((Kd (2 * m + 1) : ℚ) : ℝ) : ℝ) : ℂ) (2 * m + 1) z := by
  set κ : ℂ := ((Pjo m * ((Kd (2 * m + 1) : ℚ) : ℝ) : ℝ) : ℂ) with hκ
  have hs : (((2 * m : ℕ) : ℕ) : ℝ) = (2 * m : ℝ) := by push_cast; ring
  have hP := Pc_poly κ (2 * m + 1)
  rw [show (((2 * m + 1 : ℕ) : ℝ) - 1) = (2 * m : ℝ) by push_cast; ring] at hP
  have hd := (Goc_poly m).add hP.neg_one_mul
  have hp : PolyH (((2 * m : ℕ) : ℕ) : ℝ) (fun z => Goc m z - Pc κ (2 * m + 1) z) := by
    rw [hs]; simpa only [sub_eq_add_neg] using hd
  have key := carlson_shift (2 * m) hp (fun n hn => by
    rw [Goc_int n m hm (by omega), sub_self])
  intro z hz
  exact sub_eq_zero.mp (key z (by rw [hs]; exact hz))

/-- **The real-`n` continuation for every odd `d = 2m+1 ≥ 3`.** -/
theorem odd_value (m : ℕ) (hm : 1 ≤ m) (w : ℝ) (hw : (2 * m : ℝ) < w) :
    ((∑' S : {S : Finset ℕ // S.card = 2 * m + 1}, V w (2 * m + 1) S : ℝ) : ℂ) =
      (((2 : ℝ) ^ w : ℝ) : ℂ) ^ (2 * m + 1) *
        Pc (((Kd (2 * m + 1) : ℚ) : ℝ) : ℂ) (2 * m + 1) (w : ℂ) := by
  have hc : ((2 * m + 1 : ℕ) : ℝ) - 1 < w := by push_cast; linarith
  have h1 := tendsto_partial w (2 * m + 1) hc (by omega)
  have h2 := VTrO_tendsto w m hw
  simp only [← VB_eq_sum] at h1
  have hu := tendsto_nhds_unique h1 h2
  rw [hu, show pfP (J0 (m + 1) : Matrix (Fin (m + 1) × Fin 2) (Fin (m + 1) × Fin 2) ℝ) * sgnPairs (2 * m + 1) = Pjo m from rfl]
  have hP := Pjo_ne m
  rw [Complex.ofReal_div, Goc_real m hw, Goc_eq m hm (w : ℂ) (by simpa using hw)]
  unfold Pc
  have hPc : ((Pjo m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hP
  push_cast
  field_simp

end Bali.GO

#print axioms Bali.GO.Goc_eq
#print axioms Bali.GO.odd_value
