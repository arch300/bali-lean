import Mathlib

/-!
# Carlson's theorem, polynomial-growth version (Bali lab, 2026-11-05)

Route: Jensen's formula in the disc after the Cayley map `φ z = (z - a) / (z + conj a)`.
Step 1: the map and its inverse.
-/

open Complex

namespace Bali.Carlson

/-- `|z - a|² - |z + conj a|² = -4 Re z Re a`. -/
theorem normSq_sub_sub (z a : ℂ) :
    normSq (z - a) - normSq (z + (starRingEnd ℂ) a) = -4 * z.re * a.re := by
  simp only [normSq_apply, sub_re, sub_im, add_re, add_im, conj_re, conj_im]
  ring

theorem add_conj_ne_zero {z a : ℂ} (hz : 0 < z.re) (ha : 0 < a.re) : z + (starRingEnd ℂ) a ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [add_re, conj_re, zero_re] at this
  linarith

/-- The Cayley map sends the right half-plane into the unit disc. -/
theorem cayley_norm_lt_one {z a : ℂ} (hz : 0 < z.re) (ha : 0 < a.re) :
    ‖(z - a) / (z + (starRingEnd ℂ) a)‖ < 1 := by
  have hden := add_conj_ne_zero hz ha
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hden)]
  have h := normSq_sub_sub z a
  have hlt : normSq (z - a) < normSq (z + (starRingEnd ℂ) a) := by nlinarith [mul_pos hz ha]
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at hlt
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt

/-- Inverse of the Cayley map. -/
noncomputable def cayleyInv (a w : ℂ) : ℂ := (a + (starRingEnd ℂ) a * w) / (1 - w)

theorem one_sub_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have : w = 1 := by linear_combination -h
  rw [this, norm_one] at hw
  exact lt_irrefl _ hw

theorem cayleyInv_re {a w : ℂ} (ha : 0 < a.re) (hw : ‖w‖ < 1) : 0 < (cayleyInv a w).re := by
  have hn : 0 < normSq (1 - w) := normSq_pos.mpr (one_sub_ne_zero hw)
  have hw2 : normSq w < 1 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  unfold cayleyInv
  rw [div_re]
  have key : (a + (starRingEnd ℂ) a * w).re * (1 - w).re + (a + (starRingEnd ℂ) a * w).im * (1 - w).im =
      a.re * (1 - normSq w) := by
    simp only [add_re, add_im, mul_re, mul_im, conj_re, conj_im, sub_re, sub_im, one_re, one_im, normSq_apply]
    ring
  rw [← add_div, key]
  exact div_pos (mul_pos ha (by linarith)) hn

theorem cayley_cayleyInv {a w : ℂ} (ha : 0 < a.re) (hw : ‖w‖ < 1) :
    (cayleyInv a w - a) / (cayleyInv a w + (starRingEnd ℂ) a) = w := by
  have h1 := one_sub_ne_zero hw
  have hre : a + (starRingEnd ℂ) a ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, conj_re, zero_re] at this
    linarith
  unfold cayleyInv
  rw [div_eq_iff (by
    rw [div_add' _ _ _ h1]
    exact div_ne_zero (by
      have : a + (starRingEnd ℂ) a * w + (starRingEnd ℂ) a * (1 - w) = a + (starRingEnd ℂ) a := by ring
      rw [this]; exact hre) h1)]
  field_simp
  ring


/-! ### Step 2: Jensen's inequality with prescribed zeros -/

open Metric Filter Topology in
/-- On a connected domain where `H 0 ≠ 0`, every zero of `H` has divisor at least `1`. -/
theorem one_le_divisor {H : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hH : AnalyticOnNhd ℂ H (closedBall 0 R)) (h0 : H 0 ≠ 0) {u : ℂ} (hu : u ∈ closedBall 0 R)
    (hz : H u = 0) : 1 ≤ MeromorphicOn.divisor H (closedBall 0 R) u := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hH hu]
  have hne0 : analyticOrderAt H u ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hH u hu, hz⟩
  have hnetop : analyticOrderAt H u ≠ ⊤ := by
    intro htop
    have hev : H =ᶠ[𝓝 u] 0 := analyticOrderAt_eq_top.mp htop
    have := hH.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_closedBall (0 : ℂ) R).isPreconnected hu hev
    exact h0 (this (mem_closedBall_self hR.le))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  rw [← hn] at hne0 ⊢
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact absurd (by simp [h]) hne0
    · exact h
  simp only [ENat.map_coe, WithTop.untop₀_coe]
  exact_mod_cast hn1

open Metric Real in
/-- **Jensen's inequality with prescribed zeros.** -/
theorem sum_log_le {H : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hH : AnalyticOnNhd ℂ H (closedBall 0 R)) (h0 : H 0 ≠ 0)
    (hb : ∀ z ∈ sphere (0 : ℂ) R, ‖H z‖ ≤ M) (s : Finset ℂ)
    (hs : ∀ u ∈ s, u ∈ closedBall (0 : ℂ) R ∧ H u = 0 ∧ u ≠ 0) :
    ∑ u ∈ s, Real.log (R / ‖u‖) ≤ Real.log M - Real.log ‖H 0‖ := by
  classical
  have hR' : |R| = R := abs_of_pos hR
  have hHa : AnalyticOnNhd ℂ H (closedBall 0 |R|) := by rwa [hR']
  have jensen := hHa.circleAverage_log_norm (c := 0) hR.ne' h0
  rw [hR'] at jensen
  have hbound : circleAverage (fun x => Real.log ‖H x‖) 0 R ≤ Real.log M := by
    apply circleAverage_mono_on_of_le_circle
    · exact (hHa.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    · intro z hz
      rw [hR'] at hz
      rcases eq_zero_or_norm_pos (H z) with h | h
      · rw [h, norm_zero, Real.log_zero]; exact Real.log_nonneg hM
      · exact Real.log_le_log h (hb z hz)
  set D := MeromorphicOn.divisor H (closedBall (0 : ℂ) R) with hD
  set f : ℂ → ℝ := fun u => (D u : ℝ) * Real.log (R * ‖0 - u‖⁻¹) with hf
  have hfin : (Function.support D).Finite := D.finiteSupport (isCompact_closedBall _ _)
  have hsupp : Function.support f ⊆ ↑(hfin.toFinset ∪ s) := by
    intro u hu
    simp only [Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union]
    left
    intro hD0
    exact hu (by simp [hf, hD0])
  have hDnn : ∀ u, 0 ≤ D u := fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hH u
  have hfnn : ∀ u, 0 ≤ f u := by
    intro u
    by_cases hU : u ∈ closedBall (0 : ℂ) R
    · by_cases h0u : u = 0
      · simp [hf, h0u]
      · have hnu : 0 < ‖u‖ := norm_pos_iff.mpr h0u
        have hle : ‖u‖ ≤ R := by simpa using hU
        refine mul_nonneg (by exact_mod_cast hDnn u) (Real.log_nonneg ?_)
        rw [zero_sub, norm_neg, ← div_eq_mul_inv, le_div_iff₀ hnu, one_mul]
        exact hle
    · have : D u = 0 := Function.locallyFinsuppWithin.apply_eq_zero_of_notMem D hU
      simp [hf, this]
  have hterm : ∀ u ∈ s, Real.log (R / ‖u‖) ≤ f u := by
    intro u hu
    obtain ⟨hU, hz, hne⟩ := hs u hu
    have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hne
    have h1 : 1 ≤ D u := one_le_divisor hR hH h0 hU hz
    have hlog : 0 ≤ Real.log (R / ‖u‖) := Real.log_nonneg (by
      rw [le_div_iff₀ hnu, one_mul]; simpa using hU)
    have e : Real.log (R * ‖0 - u‖⁻¹) = Real.log (R / ‖u‖) := by
      rw [zero_sub, norm_neg, div_eq_mul_inv]
    simp only [hf, e]
    have : (1 : ℝ) ≤ (D u : ℝ) := by exact_mod_cast h1
    nlinarith
  have hsum : ∑ u ∈ s, Real.log (R / ‖u‖) ≤ ∑ᶠ u, f u := by
    rw [finsum_eq_sum_of_support_subset f hsupp]
    calc ∑ u ∈ s, Real.log (R / ‖u‖) ≤ ∑ u ∈ s, f u := Finset.sum_le_sum hterm
      _ ≤ ∑ u ∈ hfin.toFinset ∪ s, f u :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right fun u _ _ => hfnn u
  have : circleAverage (fun x => Real.log ‖H x‖) 0 R = ∑ᶠ u, f u + Real.log ‖H 0‖ := by
    rw [jensen]
  linarith


/-! ### Step 3: from the half-plane to the disc, and the contradiction -/

theorem cayleyInv_cayley {a z : ℂ} (hz : 0 < z.re) (ha : 0 < a.re) :
    cayleyInv a ((z - a) / (z + (starRingEnd ℂ) a)) = z := by
  have hd := add_conj_ne_zero hz ha
  have hre : a + (starRingEnd ℂ) a ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, conj_re, zero_re] at this
    linarith
  unfold cayleyInv
  have h1 : 1 - (z - a) / (z + (starRingEnd ℂ) a) = (a + (starRingEnd ℂ) a) / (z + (starRingEnd ℂ) a) := by
    field_simp; ring
  rw [h1, div_eq_iff (div_ne_zero hre hd)]
  field_simp
  ring

theorem norm_cayleyInv_mul {a w : ℂ} (hw : ‖w‖ < 1) :
    ‖cayleyInv a w‖ * ‖1 - w‖ ≤ 2 * ‖a‖ := by
  have h1 := one_sub_ne_zero hw
  have e : cayleyInv a w * (1 - w) = a + (starRingEnd ℂ) a * w := by
    unfold cayleyInv; field_simp
  rw [← norm_mul, e]
  calc ‖a + (starRingEnd ℂ) a * w‖ ≤ ‖a‖ + ‖(starRingEnd ℂ) a * w‖ := norm_add_le _ _
    _ = ‖a‖ + ‖a‖ * ‖w‖ := by rw [norm_mul, Complex.norm_conj]
    _ ≤ 2 * ‖a‖ := by nlinarith [norm_nonneg a, norm_nonneg w]

/-- The disc function. -/
noncomputable def Hd (g : ℂ → ℂ) (a : ℂ) (K : ℕ) (w : ℂ) : ℂ := g (cayleyInv a w) * (1 - w) ^ K

theorem Hd_bound {g : ℂ → ℂ} {a : ℂ} {K : ℕ} {A : ℝ} (hA : 0 ≤ A) (ha : 0 < a.re)
    (hb : ∀ z : ℂ, 0 < z.re → ‖g z‖ ≤ A * (1 + ‖z‖) ^ K) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖Hd g a K w‖ ≤ A * (2 + 2 * ‖a‖) ^ K := by
  unfold Hd
  rw [norm_mul, norm_pow]
  have hz := cayleyInv_re ha hw
  have h1 : ‖1 - w‖ ≤ 2 := by
    calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have h2 : (1 + ‖cayleyInv a w‖) * ‖1 - w‖ ≤ 2 + 2 * ‖a‖ := by
    have := norm_cayleyInv_mul (a := a) hw
    nlinarith
  calc ‖g (cayleyInv a w)‖ * ‖1 - w‖ ^ K ≤ A * (1 + ‖cayleyInv a w‖) ^ K * ‖1 - w‖ ^ K :=
        mul_le_mul_of_nonneg_right (hb _ hz) (by positivity)
    _ = A * ((1 + ‖cayleyInv a w‖) * ‖1 - w‖) ^ K := by rw [mul_pow]; ring
    _ ≤ A * (2 + 2 * ‖a‖) ^ K := by
        apply mul_le_mul_of_nonneg_left _ hA
        exact pow_le_pow_left₀ (by positivity) h2 K

open Metric in
theorem Hd_analytic {g : ℂ → ℂ} {a : ℂ} {K : ℕ} (ha : 0 < a.re)
    (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.re}) {R : ℝ} (hR : R < 1) :
    AnalyticOnNhd ℂ (Hd g a K) (closedBall 0 R) := by
  intro w hw
  have hw1 : ‖w‖ < 1 := by
    have : ‖w‖ ≤ R := by simpa using hw
    linarith
  have hden := one_sub_ne_zero hw1
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hga : AnalyticAt ℂ g (cayleyInv a w) :=
    hg.analyticAt (hopen.mem_nhds (cayleyInv_re ha hw1))
  have hc : AnalyticAt ℂ (cayleyInv a) w := by
    unfold cayleyInv
    exact (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).div
      (analyticAt_const.sub analyticAt_id) hden
  exact (hga.comp hc).mul ((analyticAt_const.sub analyticAt_id).pow K)

/-- `log (1/x) ≥ (1 - x²)/2` on `(0,1]`. -/
theorem log_inv_ge {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : (1 - x ^ 2) / 2 ≤ Real.log (1 / x) := by
  have h := Real.add_one_le_exp (-(1 - x))
  have hl : 1 - x ≤ Real.log (1 / x) := by
    rw [Real.log_div (by norm_num) hx.ne', Real.log_one, zero_sub]
    have := Real.log_le_sub_one_of_pos hx
    linarith
  nlinarith

/-- **Carlson's theorem**, polynomial-growth version: a function of polynomial growth on the right
half-plane that vanishes at every positive integer vanishes identically. -/
theorem carlson {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.re}) {K : ℕ} {A : ℝ}
    (hA : 0 ≤ A) (hb : ∀ z : ℂ, 0 < z.re → ‖g z‖ ≤ A * (1 + ‖z‖) ^ K)
    (hzero : ∀ n : ℕ, 0 < n → g n = 0) : ∀ z : ℂ, 0 < z.re → g z = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, ha, hga⟩ := hcon
  set M : ℝ := max 1 (A * (2 + 2 * ‖a‖) ^ K) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  set φ : ℕ → ℂ := fun n => ((n : ℂ) - a) / ((n : ℂ) + (starRingEnd ℂ) a) with hφ
  have nre : ∀ n : ℕ, 0 < n → 0 < ((n : ℂ)).re := fun n hn => by simpa using (Nat.cast_pos.mpr hn : (0 : ℝ) < n)
  have φlt : ∀ n : ℕ, 0 < n → ‖φ n‖ < 1 := fun n hn => cayley_norm_lt_one (nre n hn) ha
  have φinv : ∀ n : ℕ, 0 < n → cayleyInv a (φ n) = n := fun n hn => cayleyInv_cayley (nre n hn) ha
  have H0 : Hd g a K 0 ≠ 0 := by
    have : cayleyInv a 0 = a := by simp [cayleyInv]
    simp [Hd, this, hga]
  have Hz : ∀ n : ℕ, 0 < n → Hd g a K (φ n) = 0 := fun n hn => by
    simp [Hd, φinv n hn, hzero n hn]
  have φne : ∀ n : ℕ, 0 < n → φ n ≠ 0 := by
    intro n hn h
    have : cayleyInv a (φ n) = cayleyInv a 0 := by rw [h]
    rw [φinv n hn] at this
    have ha' : cayleyInv a 0 = a := by simp [cayleyInv]
    rw [ha'] at this
    exact hga (by rw [← this]; exact hzero n hn)
  have φinj : ∀ n m : ℕ, 0 < n → 0 < m → φ n = φ m → n = m := by
    intro n m hn hm h
    have := congrArg (cayleyInv a) h
    rw [φinv n hn, φinv m hm] at this
    exact_mod_cast this
  set C : ℝ := Real.log M - Real.log ‖Hd g a K 0‖ with hC
  have hMb : ∀ w : ℂ, ‖w‖ < 1 → ‖Hd g a K w‖ ≤ M := fun w hw =>
    (Hd_bound hA ha hb hw).trans (le_max_right _ _)
  -- partial sums are bounded
  have bounded : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.Icc 1 N, Real.log (1 / ‖φ n‖) ≤ C + 1 := by
    intro N hN
    have hne : (Finset.Icc 1 N).Nonempty := ⟨1, by simp [hN]⟩
    set r : ℝ := (Finset.Icc 1 N).sup' hne (fun n => ‖φ n‖) with hr
    have hrlt : r < 1 := by
      rw [hr, Finset.sup'_lt_iff]
      intro n hn
      exact φlt n (by simp at hn; omega)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    set R : ℝ := max r (Real.exp (-(1 / (N : ℝ)))) with hRdef
    have hR1 : R < 1 := max_lt hrlt (by
      have : 0 < 1 / (N : ℝ) := by positivity
      have h := Real.exp_lt_exp.mpr (show -(1 / (N : ℝ)) < 0 by linarith)
      rwa [Real.exp_zero] at h)
    have hRpos : 0 < R := lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
    have hlogR : -(1 / (N : ℝ)) ≤ Real.log R := by
      rw [← Real.log_exp (-(1 / (N : ℝ)))]
      exact Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
    have hmem : ∀ n ∈ Finset.Icc 1 N, ‖φ n‖ ≤ R := fun n hn =>
      (Finset.le_sup' (fun n => ‖φ n‖) hn).trans (le_max_left _ _)
    have key := sum_log_le hRpos hM1 (Hd_analytic (K := K) ha hg hR1) H0
      (fun z hz => hMb z (by rw [mem_sphere_zero_iff_norm] at hz; linarith))
      ((Finset.Icc 1 N).image φ) (by
        intro u hu
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
        have hn0 : 0 < n := by simp at hn; omega
        exact ⟨by simpa using hmem n hn, Hz n hn0, φne n hn0⟩)
    rw [Finset.sum_image (fun n hn m hm h => φinj n m (by simp at hn; omega) (by simp at hm; omega) h)] at key
    have each : ∀ n ∈ Finset.Icc 1 N, Real.log (1 / ‖φ n‖) - 1 / (N : ℝ) ≤ Real.log (R / ‖φ n‖) := by
      intro n hn
      have hn0 : 0 < n := by simp at hn; omega
      have hp : 0 < ‖φ n‖ := norm_pos_iff.mpr (φne n hn0)
      rw [Real.log_div hRpos.ne' hp.ne', Real.log_div one_ne_zero hp.ne', Real.log_one]
      linarith
    have hsum := Finset.sum_le_sum each
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsum
    have : ((N + 1 - 1 : ℕ) : ℝ) * (1 / (N : ℝ)) = 1 := by
      rw [show N + 1 - 1 = N by omega]; field_simp
    linarith
  -- but they diverge
  set c : ℝ := 2 * a.re / (1 + ‖a‖) ^ 2 with hc
  have hcpos : 0 < c := by positivity
  have lower : ∀ n : ℕ, 0 < n → c * (1 / (n : ℝ)) ≤ Real.log (1 / ‖φ n‖) := by
    intro n hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hd := add_conj_ne_zero (nre n hn) ha
    have hq : 0 < normSq ((n : ℂ) + (starRingEnd ℂ) a) := normSq_pos.mpr hd
    have hphi : ‖φ n‖ ^ 2 = normSq ((n : ℂ) - a) / normSq ((n : ℂ) + (starRingEnd ℂ) a) := by
      simp only [hφ]; rw [norm_div, div_pow, ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
    have hdiff := normSq_sub_sub (n : ℂ) a
    have hnre : ((n : ℂ)).re = n := by simp
    rw [hnre] at hdiff
    have hup : normSq ((n : ℂ) + (starRingEnd ℂ) a) ≤ ((n : ℝ) * (1 + ‖a‖)) ^ 2 := by
      rw [normSq_eq_norm_sq]
      have h1 : ‖(n : ℂ) + (starRingEnd ℂ) a‖ ≤ n + ‖a‖ := by
        calc ‖(n : ℂ) + (starRingEnd ℂ) a‖ ≤ ‖(n : ℂ)‖ + ‖(starRingEnd ℂ) a‖ := norm_add_le _ _
          _ = n + ‖a‖ := by rw [Complex.norm_conj, Complex.norm_natCast]
      have h2 : (n : ℝ) + ‖a‖ ≤ n * (1 + ‖a‖) := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith [norm_nonneg a]
      exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
    have hgap : c * (1 / (n : ℝ)) ≤ (1 - ‖φ n‖ ^ 2) / 2 := by
      rw [hphi, hc]
      have e : (1 - normSq ((n : ℂ) - a) / normSq ((n : ℂ) + (starRingEnd ℂ) a)) / 2 =
          2 * n * a.re / normSq ((n : ℂ) + (starRingEnd ℂ) a) := by
        field_simp; linarith
      rw [e]
      have hd2 : 0 < (1 + ‖a‖) ^ 2 := by positivity
      have lhs : 2 * a.re / (1 + ‖a‖) ^ 2 * (1 / (n : ℝ)) = 2 * a.re / ((1 + ‖a‖) ^ 2 * n) := by
        field_simp
      rw [lhs, div_le_div_iff₀ (by positivity) hq]
      have := mul_le_mul_of_nonneg_left hup (by positivity : (0 : ℝ) ≤ 2 * a.re)
      nlinarith [this, ha.le, hnr]
    have hp : 0 < ‖φ n‖ := norm_pos_iff.mpr (φne n hn)
    exact hgap.trans (log_inv_ge hp (φlt n hn).le)
  have harm := Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨N0, hN0⟩ := (harm.eventually (Filter.eventually_gt_atTop ((C + 1) / c))).exists_forall_of_atTop
  have hN := hN0 (N0 + 1) (by omega)
  have hb2 := bounded (N0 + 1) (by omega)
  have hsumlow : c * ∑ i ∈ Finset.range (N0 + 1), (1 / ((i : ℝ) + 1)) ≤
      ∑ n ∈ Finset.Icc 1 (N0 + 1), Real.log (1 / ‖φ n‖) := by
    have hI : Finset.Icc 1 (N0 + 1) = Finset.Ico 1 (N0 + 1 + 1) := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [Finset.mul_sum, hI, Finset.sum_Ico_eq_sum_range]
    simp only [show N0 + 1 + 1 - 1 = N0 + 1 by omega]
    refine Finset.sum_le_sum fun i _ => ?_
    have := lower (1 + i) (by omega)
    push_cast at this ⊢
    rw [show (i : ℝ) + 1 = 1 + i by ring]
    exact this
  have := (div_lt_iff₀ hcpos).mp hN
  linarith

end Bali.Carlson

#print axioms Bali.Carlson.cayley_norm_lt_one
#print axioms Bali.Carlson.cayleyInv_re
#print axioms Bali.Carlson.cayley_cayleyInv
#print axioms Bali.Carlson.one_le_divisor
#print axioms Bali.Carlson.sum_log_le
#print axioms Bali.Carlson.carlson
