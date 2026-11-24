import P699.PfaffianPerm
import P699.VB
import P699.GaussTarget

/-!
# de Bruijn's formula for the infinite binomial measure, even `d = 2m` (Bali lab, 2026-11-05)

For real `w > 2m-1`, the truncated sums
`V_N = ∑_{S ⊂ {0..N}, |S| = 2m} ∏_{x∈S} C(w,x) ∏_{x<y∈S} (y-x)`
converge to a Pfaffian of the infinite skew moments. Truncation limit of the finite formula
`Bali.PfP.pfP_deBruijn`.
-/

open Finset Matrix Filter

namespace Bali.GDB
open Bali.PfP Bali.VB GaussTarget

/-- points, strictly decreasing so that the finite theorem applies. -/
noncomputable def tt (N : ℕ) : Fin (N + 1) → ℝ := fun x => -((x : ℕ) : ℝ)

noncomputable def nu (w : ℝ) (N : ℕ) : Fin (N + 1) → ℝ := fun x => gchoose w x

lemma tt_anti (N : ℕ) : StrictAnti (tt N) := by
  intro a b h
  simp only [tt, neg_lt_neg_iff]
  exact_mod_cast h

/-- The truncated volume. `|t y - t x| = y - x`. -/
noncomputable def VTr (w : ℝ) (m N : ℕ) : ℝ := VBvol (tt N) (nu w N) (2 * m)

/-- Summand of the infinite Gram matrix. -/
noncomputable def Fsk (w : ℝ) (e f : ℕ) (r : ℕ × ℕ) : ℝ :=
  gchoose w r.1 * (-(r.1 : ℝ)) ^ e *
    ((if r.1 < r.2 then (1 : ℝ) else if r.2 < r.1 then -1 else 0) * (gchoose w r.2 * (-(r.2 : ℝ)) ^ f))

/-- `x^e |C(w,x)|` is summable for `w > e`. -/
lemma summable_pow_abs (w : ℝ) (e : ℕ) (he : (e : ℝ) < w) :
    Summable (fun x : ℕ => ‖gchoose w x * (-(x : ℝ)) ^ e‖) := by
  have hw : -1 ≤ w := by have := (Nat.cast_nonneg e : (0 : ℝ) ≤ e); linarith
  obtain ⟨C, hC0, hC⟩ := gchoose_bound w hw
  have hs : Summable (fun a : ℕ => C * ((a : ℝ) + 1) ^ (-(w + 1 - e))) := by
    apply Summable.mul_left
    have h1 : Summable (fun a : ℕ => ((a : ℝ)) ^ (-(w + 1 - e))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    simpa using (summable_nat_add_iff 1).mpr h1
  refine Summable.of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_) hs
  have hpos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have e1 : ((a : ℝ) + 1) ^ e * ((a : ℝ) + 1) ^ (-(w + 1)) = ((a : ℝ) + 1) ^ (-(w + 1 - e)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hpos]; ring_nf
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, Nat.abs_cast]
  calc |gchoose w a| * (a : ℝ) ^ e ≤ (C * ((a : ℝ) + 1) ^ (-(w + 1))) * ((a : ℝ) + 1) ^ e :=
        mul_le_mul (hC a) (pow_le_pow_left₀ (by positivity) (by linarith) e) (by positivity)
          (mul_nonneg hC0 (Real.rpow_nonneg hpos.le _))
    _ = _ := by rw [← e1]; ring

lemma summable_Fsk (w : ℝ) (e f : ℕ) (he : (e : ℝ) < w) (hf : (f : ℝ) < w) :
    Summable (Fsk w e f) := by
  have hP : Summable fun r : ℕ × ℕ =>
      ‖gchoose w r.1 * (-(r.1 : ℝ)) ^ e‖ * ‖gchoose w r.2 * (-(r.2 : ℝ)) ^ f‖ :=
    (summable_pow_abs w e he).mul_of_nonneg (summable_pow_abs w f hf)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine Summable.of_norm_bounded hP fun r => ?_
  have hs : ‖(if r.1 < r.2 then (1 : ℝ) else if r.2 < r.1 then -1 else 0)‖ ≤ 1 := by
    split_ifs <;> simp
  simp only [Fsk, norm_mul]
  have n1 := norm_nonneg (gchoose w r.1)
  have a1 : 0 ≤ ‖gchoose w r.1‖ * ‖(-(r.1 : ℝ)) ^ e‖ := by positivity
  have a2 : 0 ≤ ‖gchoose w r.2‖ * ‖(-(r.2 : ℝ)) ^ f‖ := by positivity
  calc ‖gchoose w r.1‖ * ‖(-(r.1 : ℝ)) ^ e‖ *
        (‖(if r.1 < r.2 then (1 : ℝ) else if r.2 < r.1 then -1 else 0)‖ * (‖gchoose w r.2‖ * ‖(-(r.2 : ℝ)) ^ f‖))
      ≤ ‖gchoose w r.1‖ * ‖(-(r.1 : ℝ)) ^ e‖ * (1 * (‖gchoose w r.2‖ * ‖(-(r.2 : ℝ)) ^ f‖)) := by gcongr
    _ = _ := by ring

/-- The infinite skew moment (in the powers of `-x`). -/
noncomputable def skM (w : ℝ) (e f : ℕ) : ℝ := ∑' r, Fsk w e f r

/-- The finite Gram entry is a square partial sum of `Fsk`. -/
lemma gram_entry (w : ℝ) (m N : ℕ) (a b : Fin m × Fin 2) :
    (Mpow (m := m) (tt N) (nu w N) * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) *
        (Mpow (m := m) (tt N) (nu w N))ᵀ) a b =
      ∑ r ∈ range (N + 1) ×ˢ range (N + 1), Fsk w (eι m a : ℕ) (eι m b : ℕ) r := by
  rw [sum_product, ← Fin.sum_univ_eq_sum_range
    (fun k : ℕ => ∑ l ∈ range (N + 1), Fsk w (eι m a : ℕ) (eι m b : ℕ) (k, l)) (N + 1)]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [← Fin.sum_univ_eq_sum_range
    (fun l : ℕ => Fsk w (eι m a : ℕ) (eι m b : ℕ) ((k : ℕ), l)) (N + 1)]
  refine sum_congr rfl fun l _ => ?_
  simp only [Fsk, Mpow, signM, tt, nu, Fin.lt_def]
  ring

lemma tendsto_squares :
    Tendsto (fun N : ℕ => range (N + 1) ×ˢ range (N + 1)) atTop (atTop : Filter (Finset (ℕ × ℕ))) := by
  apply tendsto_atTop_finset_of_monotone
  · intro a b h
    exact product_subset_product (range_mono (by omega)) (range_mono (by omega))
  · rintro ⟨x, y⟩
    refine ⟨x + y, ?_⟩
    simp only [mem_product, mem_range]
    omega

/-- **de Bruijn's formula for the infinite binomial measure.** -/
theorem VTr_tendsto (w : ℝ) (m : ℕ) (hw : (2 * m : ℝ) - 1 < w) :
    Tendsto (fun N => VTr w m N) atTop
      (nhds (pfP (fun a b : Fin m × Fin 2 => skM w (eι m a : ℕ) (eι m b : ℕ)) /
        (pfP (J0 m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) * sgnPairs (2 * m)))) := by
  have hJ : pfP (J0 m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) ≠ 0 := by
    rw [pfP_J0]; exact pfP_Om_ne_zero m
  have hS : (sgnPairs (2 * m) : ℝ) ≠ 0 := by
    unfold sgnPairs
    exact prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr fun _ _ => by norm_num
  have hfin : ∀ N, VTr w m N =
      pfP (Mpow (m := m) (tt N) (nu w N) * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) *
          (Mpow (m := m) (tt N) (nu w N))ᵀ) /
        (pfP (J0 m : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) * sgnPairs (2 * m)) := by
    intro N
    rw [pfP_deBruijn, sum_minors_eq_VB (tt N) (nu w N) (tt_anti N), VTr]
    field_simp
  simp only [hfin]
  apply Tendsto.div_const
  have hent : ∀ a b : Fin m × Fin 2, Tendsto (fun N =>
      (Mpow (m := m) (tt N) (nu w N) * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) *
        (Mpow (m := m) (tt N) (nu w N))ᵀ) a b) atTop (nhds (skM w (eι m a : ℕ) (eι m b : ℕ))) := by
    intro a b
    have lt2 : ∀ c : Fin m × Fin 2, (((eι m c : Fin (2 * m)) : ℕ) : ℝ) < w := by
      intro c
      have h1 : ((eι m c : Fin (2 * m)) : ℕ) + 1 ≤ 2 * m := (eι m c).isLt
      have h2 : (((eι m c : Fin (2 * m)) : ℕ) : ℝ) + 1 ≤ 2 * m := by exact_mod_cast h1
      linarith
    simp only [gram_entry]
    exact (summable_Fsk w _ _ (lt2 a) (lt2 b)).hasSum.comp tendsto_squares
  unfold pfP
  refine tendsto_finsetSum _ fun σ _ => Tendsto.const_mul _ ?_
  exact tendsto_finsetProd _ fun i _ => hent _ _

/-- `skM` in terms of the ordinary moments `OM`: the signed Gram entry is a skew moment. -/
theorem skM_eq_OM (w : ℝ) (e f : ℕ) (he : (e : ℝ) < w) (hf : (f : ℝ) < w) :
    skM w e f = (-1 : ℝ) ^ (e + f) * (OM w e f - OM w f e) := by
  have hP : Summable fun r : ℕ × ℕ =>
      ‖gchoose w r.1 * (-(r.1 : ℝ)) ^ e‖ * ‖gchoose w r.2 * (-(r.2 : ℝ)) ^ f‖ :=
    (summable_pow_abs w e he).mul_of_nonneg (summable_pow_abs w f hf)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  let A : ℕ × ℕ → ℝ := fun r =>
    if r.1 < r.2 then (r.1 : ℝ) ^ e * (r.2 : ℝ) ^ f * (gchoose w r.1 * gchoose w r.2) else 0
  let B : ℕ × ℕ → ℝ := fun r =>
    if r.1 < r.2 then (r.1 : ℝ) ^ f * (r.2 : ℝ) ^ e * (gchoose w r.1 * gchoose w r.2) else 0
  have sA : Summable A := by
    refine Summable.of_norm_bounded hP fun r => ?_
    simp only [A]
    split_ifs
    · simp only [norm_mul, norm_pow, norm_neg]
      exact le_of_eq (by ring)
    · simp only [norm_zero]; positivity
  have sB' : Summable (fun r : ℕ × ℕ => B (r.2, r.1)) := by
    refine Summable.of_norm_bounded hP fun r => ?_
    simp only [B]
    split_ifs
    · simp only [norm_mul, norm_pow, norm_neg]
      exact le_of_eq (by ring)
    · simp only [norm_zero]; positivity
  have eB : ∑' r : ℕ × ℕ, B (r.2, r.1) = OM w f e :=
    (Equiv.prodComm ℕ ℕ).tsum_eq B
  have eA : ∑' r, A r = OM w e f := rfl
  unfold skM
  rw [← eA, ← eB, ← sA.tsum_sub sB', ← tsum_mul_left]
  refine tsum_congr fun r => ?_
  obtain ⟨x, y⟩ := r
  have hx : (-(x : ℝ)) ^ e = (-1) ^ e * (x : ℝ) ^ e := by rw [neg_pow]
  have hy : (-(y : ℝ)) ^ f = (-1) ^ f * (y : ℝ) ^ f := by rw [neg_pow]
  simp only [Fsk, A, B, hx, hy, pow_add]
  rcases lt_trichotomy x y with h | h | h
  · have h' : ¬ y < x := by omega
    simp only [h, h', if_true, if_false]; ring
  · subst h; simp
  · have h' : ¬ x < y := by omega
    simp only [h, h', if_true, if_false]; ring

end Bali.GDB

#print axioms Bali.GDB.VTr_tendsto
#print axioms Bali.GDB.skM_eq_OM
