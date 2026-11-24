import Mathlib

/-!
# Holomorphic functions of polynomial growth on a half-plane, and the product side over `ℂ`
(Bali lab, 2026-11-05)
-/

open Complex MeasureTheory

namespace Bali.PC

/-- `f` is differentiable and of polynomial growth on `Re z > s`. -/
def PolyH (s : ℝ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f {z : ℂ | s < z.re} ∧
    ∃ (A : ℝ) (K : ℕ), 0 ≤ A ∧ ∀ z : ℂ, s < z.re → ‖f z‖ ≤ A * (1 + ‖z‖) ^ K

theorem PolyH.const (s : ℝ) (c : ℂ) : PolyH s (fun _ => c) :=
  ⟨differentiableOn_const c, ‖c‖, 0, norm_nonneg _, fun z _ => by simp⟩

theorem PolyH.sub_const (s : ℝ) (c : ℂ) : PolyH s (fun z => z - c) := by
  refine ⟨by fun_prop, 1 + ‖c‖, 1, by positivity, fun z _ => ?_⟩
  calc ‖z - c‖ ≤ ‖z‖ + ‖c‖ := norm_sub_le _ _
    _ ≤ (1 + ‖c‖) * (1 + ‖z‖) ^ 1 := by nlinarith [norm_nonneg z, norm_nonneg c]

theorem PolyH.mul {s : ℝ} {f g : ℂ → ℂ} (hf : PolyH s f) (hg : PolyH s g) :
    PolyH s (fun z => f z * g z) := by
  obtain ⟨d1, A, K, hA, h1⟩ := hf
  obtain ⟨d2, B, L, hB, h2⟩ := hg
  refine ⟨d1.mul d2, A * B, K + L, mul_nonneg hA hB, fun z hz => ?_⟩
  rw [norm_mul, pow_add]
  calc ‖f z‖ * ‖g z‖ ≤ (A * (1 + ‖z‖) ^ K) * (B * (1 + ‖z‖) ^ L) :=
        mul_le_mul (h1 z hz) (h2 z hz) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem PolyH.add {s : ℝ} {f g : ℂ → ℂ} (hf : PolyH s f) (hg : PolyH s g) :
    PolyH s (fun z => f z + g z) := by
  obtain ⟨d1, A, K, hA, h1⟩ := hf
  obtain ⟨d2, B, L, hB, h2⟩ := hg
  refine ⟨d1.add d2, A + B, K + L, add_nonneg hA hB, fun z hz => ?_⟩
  have hone : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have p1 : (1 + ‖z‖) ^ K ≤ (1 + ‖z‖) ^ (K + L) := pow_le_pow_right₀ hone (by omega)
  have p2 : (1 + ‖z‖) ^ L ≤ (1 + ‖z‖) ^ (K + L) := pow_le_pow_right₀ hone (by omega)
  calc ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ A * (1 + ‖z‖) ^ (K + L) + B * (1 + ‖z‖) ^ (K + L) :=
        add_le_add ((h1 z hz).trans (mul_le_mul_of_nonneg_left p1 hA))
          ((h2 z hz).trans (mul_le_mul_of_nonneg_left p2 hB))
    _ = _ := by ring

theorem PolyH.pow {s : ℝ} {f : ℂ → ℂ} (hf : PolyH s f) (n : ℕ) : PolyH s (fun z => f z ^ n) := by
  induction n with
  | zero => simpa using PolyH.const s 1
  | succ n ih => simpa [pow_succ] using ih.mul hf

theorem PolyH.prod {s : ℝ} {ι : Type*} (t : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ t, PolyH s (f i)) :
    PolyH s (fun z => ∏ i ∈ t, f i z) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using PolyH.const s 1
  | insert a t ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The central binomial ratio over `ℂ`: at a natural `k` it is `C(2k,k)/4^k`. -/
noncomputable def cb (w : ℂ) : ℂ := Gamma (w + 1 / 2) / (Gamma (1 / 2) * Gamma (w + 1))

theorem cb_natCast (k : ℕ) : cb k = ((Nat.centralBinom k : ℚ) / 4 ^ k : ℚ) := by
  have hG : Gamma (1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  induction k with
  | zero =>
    simp [cb]
    simpa using hG
  | succ k ih =>
    have hk : ((k : ℂ) + 1 / 2) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      have hk0 := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      linarith
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hrec : cb ((k + 1 : ℕ) : ℂ) = cb k * ((k : ℂ) + 1 / 2) / ((k : ℂ) + 1) := by
      unfold cb
      push_cast
      rw [show (k : ℂ) + 1 + 1 / 2 = ((k : ℂ) + 1 / 2) + 1 by ring, Gamma_add_one _ hk,
        show (k : ℂ) + 1 + 1 = ((k : ℂ) + 1) + 1 by ring, Gamma_add_one _ hk1]
      have h1 : Gamma ((k : ℂ) + 1) ≠ 0 := by
        rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring]
        exact Gamma_ne_zero_of_re_pos (by simp; positivity)
      field_simp
    rw [hrec, ih]
    have hs := Nat.succ_mul_centralBinom_succ k
    have hq : ((k + 1 : ℕ) : ℚ) * (Nat.centralBinom (k + 1) : ℚ) = 2 * (2 * k + 1) * Nat.centralBinom k := by
      exact_mod_cast hs
    have hk1q : ((k : ℚ) + 1) ≠ 0 := by positivity
    have goalq : ((Nat.centralBinom k : ℚ) / 4 ^ k) * ((k : ℚ) + 1 / 2) / ((k : ℚ) + 1) =
        (Nat.centralBinom (k + 1) : ℚ) / 4 ^ (k + 1) := by
      push_cast at hq
      have : (Nat.centralBinom (k + 1) : ℚ) = 2 * (2 * k + 1) * Nat.centralBinom k / ((k : ℚ) + 1) := by
        rw [eq_div_iff hk1q]; linarith
      rw [this, pow_succ]; field_simp; ring
    have := congrArg (fun q : ℚ => (q : ℂ)) goalq
    push_cast at this ⊢
    exact this

/-- The dominating function. -/
noncomputable def dom (x : ℝ) : ℝ :=
  ‖(x : ℂ) ^ ((1 / 2 : ℂ) - 1) * (1 - (x : ℂ)) ^ ((1 / 2 : ℂ) - 1)‖

theorem dom_integrable : IntervalIntegrable dom volume 0 1 :=
  (Complex.betaIntegral_convergent (u := 1 / 2) (v := 1 / 2) (by norm_num) (by norm_num)).norm

theorem norm_beta_le {z : ℂ} (hz : 0 < z.re) :
    ‖betaIntegral (z + 1 / 2) (1 / 2)‖ ≤ ∫ x in (0 : ℝ)..1, dom x := by
  unfold betaIntegral
  refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ dom_integrable
  refine Filter.Eventually.of_forall fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx.1
  have hx1 : x ≤ 1 := hx.2
  unfold dom
  rw [norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [norm_cpow_eq_rpow_re_of_pos hx0, norm_cpow_eq_rpow_re_of_pos hx0]
  apply Real.rpow_le_rpow_of_exponent_ge hx0 hx1
  simp only [sub_re, add_re, one_re, div_ofNat_re]
  linarith

/-- **`Γ(z+½)/Γ(z+1)` is bounded on `Re z > 0`.** -/
theorem gamma_ratio_bound : ∃ C : ℝ, ∀ z : ℂ, 0 < z.re → ‖Gamma (z + 1 / 2) / Gamma (z + 1)‖ ≤ C := by
  have hG : Gamma (1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  refine ⟨(∫ x in (0 : ℝ)..1, dom x) / ‖Gamma (1 / 2)‖, fun z hz => ?_⟩
  have hs : 0 < (z + 1 / 2).re := by
    simp only [add_re, div_ofNat_re, one_re]; linarith
  have key := Gamma_mul_Gamma_eq_betaIntegral (s := z + 1 / 2) (t := 1 / 2) hs (by norm_num)
  have e : z + 1 / 2 + 1 / 2 = z + 1 := by ring
  rw [e] at key
  have h1 : Gamma (z + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp only [add_re, one_re]; linarith)
  have eq : Gamma (z + 1 / 2) / Gamma (z + 1) = betaIntegral (z + 1 / 2) (1 / 2) / Gamma (1 / 2) := by
    rw [div_eq_div_iff h1 hG, key]
    ring
  rw [eq, norm_div]
  exact div_le_div_of_nonneg_right (norm_beta_le hz) (norm_nonneg _)


theorem cb_poly (s : ℝ) (i : ℕ) (hs : (i : ℝ) ≤ s) : PolyH s (fun z => cb (z - i)) := by
  obtain ⟨C, hC⟩ := gamma_ratio_bound
  have hG : Gamma (1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hre : ∀ z : ℂ, s < z.re → 0 < (z - i).re := fun z hz => by
    simp only [sub_re, natCast_re]; linarith
  have hGne : ∀ w : ℂ, 0 < w.re → ∀ m : ℕ, w ≠ -m := fun w hw m h => by
    have := congrArg Complex.re h
    simp only [neg_re, natCast_re] at this
    have hm := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    linarith
  constructor
  · intro z hz
    have hw : 0 < (z - i).re := hre z hz
    have h1 : 0 < (z - i + 1 / 2).re := by simp only [add_re, div_ofNat_re, one_re]; linarith
    have h2 : 0 < (z - i + 1).re := by simp only [add_re, one_re]; linarith
    have d1 : DifferentiableAt ℂ Gamma (z - i + 1 / 2) := differentiableAt_Gamma _ (hGne _ h1)
    have d2 : DifferentiableAt ℂ Gamma (z - i + 1) := differentiableAt_Gamma _ (hGne _ h2)
    have dd : DifferentiableAt ℂ (fun z : ℂ => Gamma (z - i + 1 / 2) / (Gamma (1 / 2) * Gamma (z - i + 1))) z := by
      refine DifferentiableAt.div ?_ ?_ (mul_ne_zero hG (Gamma_ne_zero_of_re_pos h2))
      · exact DifferentiableAt.comp z d1 (by fun_prop)
      · exact (DifferentiableAt.comp z d2 (by fun_prop)).const_mul _
    exact dd.differentiableWithinAt
  · refine ⟨|C| / ‖Gamma (1 / 2)‖, 0, by positivity, fun z hz => ?_⟩
    have hb := (hC (z - i) (hre z hz)).trans (le_abs_self C)
    have e : cb (z - i) = (Gamma (z - i + 1 / 2) / Gamma (z - i + 1)) / Gamma (1 / 2) := by
      unfold cb; rw [div_div, mul_comm]
    show ‖cb (z - i)‖ ≤ _
    rw [e, norm_div, pow_zero, mul_one]
    exact div_le_div_of_nonneg_right hb (norm_nonneg _)

/-- The product side of the main formula, without the factor `2^(dn)`. -/
noncomputable def Pc (κ : ℂ) (d : ℕ) (z : ℂ) : ℂ :=
  κ * (∏ i ∈ Finset.range (d - 1), (z - i) ^ (d - 2 - 2 * i)) *
    ∏ i ∈ Finset.Ico (d - 1 - d / 2) (d - 1), ((z - i) * cb (z - i))

theorem Pc_poly (κ : ℂ) (d : ℕ) : PolyH ((d : ℝ) - 1) (Pc κ d) := by
  have h1 : PolyH ((d : ℝ) - 1) (fun z => ∏ i ∈ Finset.range (d - 1), (z - i) ^ (d - 2 - 2 * i)) :=
    PolyH.prod _ fun i _ => (PolyH.sub_const _ _).pow _
  have h2 : PolyH ((d : ℝ) - 1) (fun z => ∏ i ∈ Finset.Ico (d - 1 - d / 2) (d - 1), ((z - i) * cb (z - i))) := by
    refine PolyH.prod _ fun i hi => (PolyH.sub_const _ _).mul (cb_poly _ i ?_)
    have hi2 := (Finset.mem_Ico.mp hi).2
    have : (i : ℝ) + 1 ≤ d - 1 + 1 - 1 + 1 := by
      have h3 : i + 1 ≤ d - 1 := hi2
      have h4 : ((i + 1 : ℕ) : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast h3
      have hd : 1 ≤ d := by omega
      rw [Nat.cast_sub hd] at h4
      push_cast at h4
      linarith
    linarith
  exact ((PolyH.const _ κ).mul h1).mul h2


/-! ### Normalized half sums over `ℂ` (everything divided by `4^z`) -/

theorem PolyH.inv_add (s : ℝ) (k i : ℕ) (hs : (k : ℝ) ≤ s) : PolyH s (fun z => (z - k + i + 1)⁻¹) := by
  have hre : ∀ z : ℂ, s < z.re → (1 : ℝ) ≤ (z - k + i + 1).re := fun z hz => by
    simp only [add_re, sub_re, natCast_re, one_re]
    have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i)
    linarith
  have hne : ∀ z : ℂ, s < z.re → z - k + i + 1 ≠ 0 := fun z hz h => by
    have := hre z hz
    rw [h] at this
    simp at this
    linarith
  refine ⟨fun z hz => ?_, 1, 0, zero_le_one, fun z hz => ?_⟩
  · have hd : DifferentiableAt ℂ (fun z : ℂ => (z - k + i + 1)⁻¹) z :=
      DifferentiableAt.inv (by fun_prop) (hne z hz)
    exact hd.differentiableWithinAt
  · rw [pow_zero, mul_one, norm_inv]
    have h1 : 1 ≤ ‖z - k + i + 1‖ := (hre z hz).trans ((Complex.re_le_norm _))
    exact inv_le_one_of_one_le₀ h1

/-- `∏_{i<t} (w-i)/(w+i+1)`: the ratio `B(w,t)/B(w,0)`. -/
noncomputable def rr (t : ℕ) (w : ℂ) : ℂ := ∏ i ∈ Finset.range t, ((w - i) * (w + i + 1)⁻¹)

theorem rr_poly (s : ℝ) (k t : ℕ) (hs : (k : ℝ) ≤ s) : PolyH s (fun z => rr t (z - k)) := by
  unfold rr
  refine PolyH.prod _ fun i _ => ?_
  have h1 : PolyH s (fun z => z - k - i) := by
    have := PolyH.sub_const s ((k : ℂ) + i)
    refine ⟨?_, ?_⟩
    · simpa [sub_sub] using this.1
    · simpa [sub_sub] using this.2
  exact h1.mul (PolyH.inv_add s k i hs)

/-- `B(z-k,t) / 4^z`. -/
noncomputable def bN (k t : ℕ) (z : ℂ) : ℂ := ((4 : ℂ) ^ k)⁻¹ * (cb (z - k) * rr t (z - k))

theorem bN_poly (s : ℝ) (k t : ℕ) (hs : (k : ℝ) ≤ s) : PolyH s (bN k t) :=
  (PolyH.const s _).mul ((cb_poly s k hs).mul (rr_poly s k t hs))

/-- `H(z-k,z-k,u+1) / 4^z`. -/
noncomputable def hP (k u : ℕ) (z : ℂ) : ℂ :=
  (((4 : ℂ) ^ k)⁻¹ - bN k 0 z) * (1 / 2) - ∑ t ∈ Finset.range u, bN k (t + 1) z

/-- `H(z-k,z-k,-u) / 4^z`. -/
noncomputable def hN (k u : ℕ) (z : ℂ) : ℂ := ((4 : ℂ) ^ k)⁻¹ - hP k u z

theorem PolyH.finset_sum {s : ℝ} {ι : Type*} (t : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ t, PolyH s (f i)) :
    PolyH s (fun z => ∑ i ∈ t, f i z) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using PolyH.const s 0
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem PolyH.neg_one_mul {s : ℝ} {f : ℂ → ℂ} (hf : PolyH s f) : PolyH s (fun z => -f z) := by
  simpa using (PolyH.const s (-1)).mul hf

theorem hP_poly (s : ℝ) (k u : ℕ) (hs : (k : ℝ) ≤ s) : PolyH s (hP k u) := by
  have h1 : PolyH s (fun z => (((4 : ℂ) ^ k)⁻¹ - bN k 0 z) * (1 / 2)) := by
    have := ((PolyH.const s ((4 : ℂ) ^ k)⁻¹).add (bN_poly s k 0 hs).neg_one_mul).mul (PolyH.const s (1 / 2))
    simpa [sub_eq_add_neg] using this
  have h2 := (PolyH.finset_sum (Finset.range u) (f := fun t => bN k (t + 1))
    fun t _ => bN_poly s k (t + 1) hs).neg_one_mul
  have e : hP k u = fun z => (((4 : ℂ) ^ k)⁻¹ - bN k 0 z) * (1 / 2) + -∑ i ∈ Finset.range u, bN k (i + 1) z := by
    funext z; simp only [hP, sub_eq_add_neg]
  rw [e]; exact h1.add h2

theorem hN_poly (s : ℝ) (k u : ℕ) (hs : (k : ℝ) ≤ s) : PolyH s (hN k u) := by
  have := (PolyH.const s ((4 : ℂ) ^ k)⁻¹).add (hP_poly s k u hs).neg_one_mul
  have e : hN k u = fun z => ((4 : ℂ) ^ k)⁻¹ + -hP k u z := by
    funext z; simp only [hN, sub_eq_add_neg]
  rw [e]; exact this

end Bali.PC

#print axioms Bali.PC.PolyH.prod
#print axioms Bali.PC.cb_natCast
#print axioms Bali.PC.cb_poly
#print axioms Bali.PC.Pc_poly
#print axioms Bali.PC.hP_poly
#print axioms Bali.PC.hN_poly
