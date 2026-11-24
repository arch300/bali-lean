import Mathlib

/-!
# Target statements for the real-n continuation of the zonotope formula

The only analytic input needed (for each fixed `d`, by the Carlson-free route checked in
`tools/zonotope_realn_algebraic.py`) is the evaluation of `B(m,t)` for real `m`, a special case of
Gauss's summation of `₂F₁` at `1`:

  `∑ₐ C(m,a) C(m,a+t) = Γ(2m+1) / (Γ(m+1+t) Γ(m+1-t))`,  `m > 0`, `t : ℕ`.

Lean's `x / 0 = 0` matches the true value `0` when `m+1-t` is a pole of `Γ`.

Milestones (all proved, standard axioms only):
* `choose_abs_le`      : `|C(m,a)| ≤ K (a+1)^(-m-1)` for real `m > -1`.
* `summable_choose_mul`: absolute summability of the product for `m > -1/2`.
* `gauss_binom_real`   : the evaluation above.
-/

open Real

namespace GaussTarget

/-- Generalized binomial coefficient `m (m-1) ⋯ (m-a+1) / a!` for real `m`. -/
noncomputable def gchoose (m : ℝ) (a : ℕ) : ℝ :=
  (∏ i ∈ Finset.range a, (m - i)) / (a.factorial : ℝ)

theorem gchoose_zero (m : ℝ) : gchoose m 0 = 1 := by
  simp [gchoose]

theorem gchoose_succ (m : ℝ) (a : ℕ) :
    gchoose m (a + 1) = gchoose m a * (m - a) / (a + 1 : ℝ) := by
  unfold gchoose
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  field_simp

/-- Agreement with the ordinary binomial coefficient at natural `m`. -/
theorem gchoose_natCast (m a : ℕ) : gchoose (m : ℝ) a = (m.choose a : ℝ) := by
  induction a with
  | zero => simp [gchoose_zero]
  | succ a ih =>
    rw [gchoose_succ, ih]
    rcases Nat.lt_or_ge m (a + 1) with h | h
    · rw [Nat.choose_eq_zero_of_lt h]
      rcases Nat.lt_or_ge m a with h' | h'
      · simp [Nat.choose_eq_zero_of_lt h']
      · have : m = a := by omega
        subst this; simp
    · have key := Nat.choose_succ_right_eq m a
      have hpos : (0 : ℝ) < a + 1 := by positivity
      rw [div_eq_iff hpos.ne']
      have : ((m.choose (a + 1) : ℕ) : ℝ) * ((a : ℝ) + 1) = (m.choose a : ℝ) * ((m : ℝ) - a) := by
        have h2 : ((m.choose (a + 1) * (a + 1) : ℕ) : ℝ) = ((m.choose a * (m - a) : ℕ) : ℝ) := by
          exact_mod_cast key
        push_cast [Nat.cast_sub (by omega : a ≤ m)] at h2
        linarith
      linarith

/-- Splitting off the first `N` factors. -/
theorem gchoose_add (m : ℝ) (N k : ℕ) :
    gchoose m (N + k) = gchoose m N * ∏ j ∈ Finset.range k, (m - (N + j : ℕ)) / ((N + j : ℕ) + 1 : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, gchoose_succ, ih, Finset.prod_range_succ]
    push_cast
    ring

/-- Telescoping lower bound for a piece of the harmonic sum. -/
theorem sum_inv_ge_log (N k : ℕ) :
    Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + 1 : ℕ) : ℝ) ≤
      ∑ j ∈ Finset.range k, (1 : ℝ) / ((N + j : ℕ) + 1 : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hp : (0 : ℝ) < ((N + k : ℕ) : ℝ) + 1 := by positivity
    have step : Real.log ((N + (k + 1) + 1 : ℕ) : ℝ) - Real.log ((N + k + 1 : ℕ) : ℝ) ≤
        1 / (((N + k : ℕ) : ℝ) + 1) := by
      have h1 : ((N + (k + 1) + 1 : ℕ) : ℝ) = ((N + k : ℕ) : ℝ) + 2 := by push_cast; ring
      have h2 : ((N + k + 1 : ℕ) : ℝ) = ((N + k : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [h1, h2, ← Real.log_div (by positivity) hp.ne']
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (((N + k : ℕ) : ℝ) + 2) / (((N + k : ℕ) : ℝ) + 1) by
        positivity)
      have e : (((N + k : ℕ) : ℝ) + 2) / (((N + k : ℕ) : ℝ) + 1) - 1 = 1 / (((N + k : ℕ) : ℝ) + 1) := by
        field_simp; ring
      linarith
    linarith

/-- Decay of the generalized binomial coefficient: past `N ≥ m` it falls like `(a+1)^(-(m+1))`. -/
theorem gchoose_abs_le (m : ℝ) (hm : -1 ≤ m) (N : ℕ) (hN : m ≤ N) (k : ℕ) :
    |gchoose m (N + k)| ≤
      |gchoose m N| * Real.exp (-(m + 1) * (Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + 1 : ℕ) : ℝ))) := by
  rw [gchoose_add, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [Finset.abs_prod]
  have hfac : ∀ j ∈ Finset.range k,
      |(m - (N + j : ℕ)) / ((N + j : ℕ) + 1 : ℝ)| ≤ Real.exp (-(m + 1) * (1 / ((N + j : ℕ) + 1 : ℝ))) := by
    intro j _
    have hp : (0 : ℝ) < ((N + j : ℕ) : ℝ) + 1 := by positivity
    have hle : m ≤ ((N + j : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    rw [abs_div, abs_of_pos hp, abs_of_nonpos (by linarith)]
    have e : -(m - ((N + j : ℕ) : ℝ)) / (((N + j : ℕ) : ℝ) + 1) =
        (-(m + 1) * (1 / (((N + j : ℕ) : ℝ) + 1))) + 1 := by field_simp; ring
    rw [e]
    exact Real.add_one_le_exp _
  calc ∏ j ∈ Finset.range k, |(m - (N + j : ℕ)) / ((N + j : ℕ) + 1 : ℝ)|
      ≤ ∏ j ∈ Finset.range k, Real.exp (-(m + 1) * (1 / ((N + j : ℕ) + 1 : ℝ))) := by
        gcongr with j hj
        exact hfac j hj
    _ = Real.exp (-(m + 1) * ∑ j ∈ Finset.range k, (1 : ℝ) / ((N + j : ℕ) + 1 : ℝ)) := by
        rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ Real.exp (-(m + 1) * (Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + 1 : ℕ) : ℝ))) := by
        apply Real.exp_le_exp.mpr
        have := sum_inv_ge_log N k
        nlinarith

/-- Uniform power bound: `|C(m,a)| ≤ C (a+1)^(-(m+1))` for all `a`. -/
theorem gchoose_bound (m : ℝ) (hm : -1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℕ, |gchoose m a| ≤ C * ((a : ℝ) + 1) ^ (-(m + 1)) := by
  set N := ⌈m⌉₊ with hNdef
  have hN : m ≤ (N : ℝ) := Nat.le_ceil m
  set C := (∑ a ∈ Finset.range N, |gchoose m a| * ((a : ℝ) + 1) ^ (m + 1)) +
    |gchoose m N| * ((N : ℝ) + 1) ^ (m + 1) with hC
  have hterm : ∀ a, 0 ≤ |gchoose m a| * ((a : ℝ) + 1) ^ (m + 1) := fun a =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have hC0 : 0 ≤ C := add_nonneg (Finset.sum_nonneg fun a _ => hterm a) (hterm N)
  refine ⟨C, hC0, fun a => ?_⟩
  have hpos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have split : |gchoose m a| = (|gchoose m a| * ((a : ℝ) + 1) ^ (m + 1)) * ((a : ℝ) + 1) ^ (-(m + 1)) := by
    rw [mul_assoc, ← Real.rpow_add hpos]; simp
  have hneg : 0 ≤ ((a : ℝ) + 1) ^ (-(m + 1)) := Real.rpow_nonneg hpos.le _
  rcases Nat.lt_or_ge a N with h | h
  · rw [split]
    apply mul_le_mul_of_nonneg_right _ hneg
    have : |gchoose m a| * ((a : ℝ) + 1) ^ (m + 1) ≤
        ∑ b ∈ Finset.range N, |gchoose m b| * ((b : ℝ) + 1) ^ (m + 1) :=
      Finset.single_le_sum (f := fun b => |gchoose m b| * ((b : ℝ) + 1) ^ (m + 1))
        (fun b _ => hterm b) (Finset.mem_range.mpr h)
    linarith [hterm N]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have hb := gchoose_abs_le m hm N hN k
    have hN1 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    have hA : (0 : ℝ) < ((N + k + 1 : ℕ) : ℝ) := by positivity
    have e : Real.exp (-(m + 1) * (Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + 1 : ℕ) : ℝ))) =
        ((N : ℝ) + 1) ^ (m + 1) * (((N + k : ℕ) : ℝ) + 1) ^ (-(m + 1)) := by
      have c1 : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      have c2 : ((N + k + 1 : ℕ) : ℝ) = ((N + k : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [c1, c2] at *
      rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
      congr 1; ring
    rw [e] at hb
    calc |gchoose m (N + k)| ≤ |gchoose m N| * (((N : ℝ) + 1) ^ (m + 1) * (((N + k : ℕ) : ℝ) + 1) ^ (-(m + 1))) := hb
      _ = (|gchoose m N| * ((N : ℝ) + 1) ^ (m + 1)) * (((N + k : ℕ) : ℝ) + 1) ^ (-(m + 1)) := by ring
      _ ≤ C * (((N + k : ℕ) : ℝ) + 1) ^ (-(m + 1)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
          have := Finset.sum_nonneg (fun b (_ : b ∈ Finset.range N) => hterm b)
          linarith

/-- Absolute summability of the product of two shifted binomial coefficients, `m > -1/2`. -/
theorem summable_gchoose_mul (m : ℝ) (hm : -1 / 2 < m) (t : ℕ) :
    Summable (fun a : ℕ => |gchoose m a * gchoose m (a + t)|) := by
  obtain ⟨C, hC0, hC⟩ := gchoose_bound m (by linarith)
  have hs : Summable (fun a : ℕ => C * C * ((a : ℝ) + 1) ^ (-(2 * (m + 1)))) := by
    apply Summable.mul_left
    have h1 : Summable (fun a : ℕ => ((a : ℝ)) ^ (-(2 * (m + 1)))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have := (summable_nat_add_iff 1).mpr h1
    simpa using this
  refine Summable.of_nonneg_of_le (fun a => abs_nonneg _) (fun a => ?_) hs
  have hpos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  rw [abs_mul]
  have h2 : |gchoose m (a + t)| ≤ C * ((a : ℝ) + 1) ^ (-(m + 1)) := by
    refine (hC (a + t)).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    apply Real.rpow_le_rpow_of_nonpos hpos (by push_cast; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)])
      (by linarith)
  calc |gchoose m a| * |gchoose m (a + t)|
      ≤ (C * ((a : ℝ) + 1) ^ (-(m + 1))) * (C * ((a : ℝ) + 1) ^ (-(m + 1))) :=
        mul_le_mul (hC a) h2 (abs_nonneg _) (mul_nonneg hC0 (Real.rpow_nonneg hpos.le _))
    _ = C * C * ((a : ℝ) + 1) ^ (-(2 * (m + 1))) := by
        rw [show -(2 * (m + 1)) = -(m + 1) + -(m + 1) by ring, Real.rpow_add hpos]; ring

/-- The sum `B(m,t) = ∑ₐ C(m,a) C(m,a+t)`. -/
noncomputable def Bsum (m : ℝ) (t : ℕ) : ℝ := ∑' a : ℕ, gchoose m a * gchoose m (a + t)

/-- Telescoping certificate (found by a Gosper-type ansatz): with `g a = a C(m,a) C(m,a+t)`. -/
theorem recur_term (m : ℝ) (t a : ℕ) :
    (m + 1 + t) * (gchoose m a * gchoose m (a + (t + 1))) - (m - t) * (gchoose m a * gchoose m (a + t)) =
      ((a + 1 : ℕ) : ℝ) * gchoose m (a + 1) * gchoose m (a + 1 + t) -
        (a : ℝ) * gchoose m a * gchoose m (a + t) := by
  have e1 : a + (t + 1) = (a + t) + 1 := by omega
  have e2 : a + 1 + t = (a + t) + 1 := by omega
  rw [e1, e2, gchoose_succ m (a + t), gchoose_succ m a]
  have h1 : ((a + t : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (a : ℝ) + 1 ≠ 0 := by positivity
  push_cast at *
  field_simp
  ring

/-- `a C(m,a) C(m,a+t) → 0` for `m > 0`. -/
theorem tendsto_g (m : ℝ) (hm : 0 < m) (t : ℕ) :
    Filter.Tendsto (fun a : ℕ => (a : ℝ) * gchoose m a * gchoose m (a + t)) Filter.atTop (nhds 0) := by
  obtain ⟨C, hC0, hC⟩ := gchoose_bound m (by linarith)
  have hlim : Filter.Tendsto (fun a : ℕ => C * C * ((a : ℝ) + 1) ^ (-(2 * m + 1))) Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 2 * m + 1 by linarith)).comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    simpa using h.const_mul (C * C)
  apply squeeze_zero_norm _ hlim
  intro a
  have hpos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_mul, Nat.abs_cast]
  have h2 : |gchoose m (a + t)| ≤ C * ((a : ℝ) + 1) ^ (-(m + 1)) := by
    refine (hC (a + t)).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    apply Real.rpow_le_rpow_of_nonpos hpos (by push_cast; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)])
      (by linarith)
  have hp1 : 0 ≤ ((a : ℝ) + 1) ^ (-(m + 1)) := Real.rpow_nonneg hpos.le _
  calc (a : ℝ) * |gchoose m a| * |gchoose m (a + t)|
      ≤ ((a : ℝ) + 1) * (C * ((a : ℝ) + 1) ^ (-(m + 1))) * (C * ((a : ℝ) + 1) ^ (-(m + 1))) := by
        apply mul_le_mul _ h2 (abs_nonneg _) (by positivity)
        exact mul_le_mul (by linarith) (hC a) (abs_nonneg _) hpos.le
    _ = C * C * ((a : ℝ) + 1) ^ (-(2 * m + 1)) := by
        have : ((a : ℝ) + 1) * ((a : ℝ) + 1) ^ (-(m + 1)) * ((a : ℝ) + 1) ^ (-(m + 1)) =
            ((a : ℝ) + 1) ^ (-(2 * m + 1)) := by
          rw [mul_assoc, ← Real.rpow_add hpos]
          nth_rewrite 1 [← Real.rpow_one ((a : ℝ) + 1)]
          rw [← Real.rpow_add hpos]; ring_nf
        calc ((a : ℝ) + 1) * (C * ((a : ℝ) + 1) ^ (-(m + 1))) * (C * ((a : ℝ) + 1) ^ (-(m + 1)))
            = C * C * (((a : ℝ) + 1) * ((a : ℝ) + 1) ^ (-(m + 1)) * ((a : ℝ) + 1) ^ (-(m + 1))) := by ring
          _ = _ := by rw [this]

/-- The contiguous relation in `t`: `(m+1+t) B(m,t+1) = (m-t) B(m,t)`. -/
theorem Bsum_recur (m : ℝ) (hm : 0 < m) (t : ℕ) :
    (m + 1 + t) * Bsum m (t + 1) = (m - t) * Bsum m t := by
  have s1 : Summable (fun a : ℕ => gchoose m a * gchoose m (a + (t + 1))) :=
    (summable_gchoose_mul m (by linarith) (t + 1)).of_abs
  have s0 : Summable (fun a : ℕ => gchoose m a * gchoose m (a + t)) :=
    (summable_gchoose_mul m (by linarith) t).of_abs
  set g : ℕ → ℝ := fun a => (a : ℝ) * gchoose m a * gchoose m (a + t) with hg
  have hF : Summable (fun a : ℕ => (m + 1 + t) * (gchoose m a * gchoose m (a + (t + 1))) -
      (m - t) * (gchoose m a * gchoose m (a + t))) := (s1.mul_left _).sub (s0.mul_left _)
  have hpart : ∀ N, ∑ a ∈ Finset.range N, ((m + 1 + t) * (gchoose m a * gchoose m (a + (t + 1))) -
      (m - t) * (gchoose m a * gchoose m (a + t))) = g N := by
    intro N
    have : ∀ a ∈ Finset.range N, ((m + 1 + t) * (gchoose m a * gchoose m (a + (t + 1))) -
        (m - t) * (gchoose m a * gchoose m (a + t))) = g (a + 1) - g a := by
      intro a _; rw [recur_term]
    rw [Finset.sum_congr rfl this, Finset.sum_range_sub]
    simp [hg]
  have hlim := hF.hasSum.tendsto_sum_nat
  simp_rw [hpart] at hlim
  have h0 : ∑' a : ℕ, ((m + 1 + t) * (gchoose m a * gchoose m (a + (t + 1))) -
      (m - t) * (gchoose m a * gchoose m (a + t))) = 0 :=
    tendsto_nhds_unique hlim (tendsto_g m hm t)
  rw [s1.mul_left (m + 1 + t) |>.tsum_sub (s0.mul_left (m - t)), tsum_mul_left, tsum_mul_left] at h0
  unfold Bsum
  linarith

/-- Gamma form of the generalized binomial coefficient, for positive non-integer `m`. -/
theorem gchoose_eq_Gamma (m : ℝ) (hm0 : 0 < m) (hm : ∀ n : ℕ, m ≠ n) (t : ℕ) :
    gchoose m t = Gamma (m + 1) / (Gamma (t + 1) * Gamma (m + 1 - t)) := by
  have hne : ∀ s : ℕ, Gamma (m + 1 - s) ≠ 0 := by
    intro s
    apply Real.Gamma_ne_zero
    intro k hk
    exact hm (s - 1 - k + 0) (by
      have : m = (s : ℝ) - 1 - k := by linarith
      rcases Nat.lt_or_ge s (k + 1) with h | h
      · exfalso
        have hs : (s : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp h
        linarith
      · rw [this]; push_cast [Nat.cast_sub h, Nat.cast_sub (by omega : 1 ≤ s - k)]
        rw [Nat.cast_sub (by omega : k ≤ s - 1), Nat.cast_sub (by omega : 1 ≤ s)]; ring)
  induction t with
  | zero =>
    simp only [gchoose_zero, Nat.cast_zero, zero_add, Real.Gamma_one, sub_zero, one_mul]
    rw [div_self (Real.Gamma_pos_of_pos (by linarith)).ne']
  | succ t ih =>
    rw [gchoose_succ, ih]
    have hmt : m - t ≠ 0 := sub_ne_zero.mpr (hm t)
    have g1 : Gamma (m + 1 - t) = (m - t) * Gamma (m - t) := by
      rw [show m + 1 - t = (m - t) + 1 by ring, Real.Gamma_add_one hmt]
    have g2 : Gamma ((t + 1 : ℕ) + 1 : ℝ) = ((t : ℝ) + 1) * Gamma ((t : ℝ) + 1) := by
      push_cast; rw [Real.Gamma_add_one (by positivity)]
    have g3 : m + 1 - ((t + 1 : ℕ) : ℝ) = m - t := by push_cast; ring
    rw [g2, g3, g1]
    have hG : Gamma (m - t) ≠ 0 := by
      have := hne (t + 1); rwa [g3] at this
    have hT : Gamma ((t : ℝ) + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
    have ht1 : (t : ℝ) + 1 ≠ 0 := by positivity
    field_simp

theorem smeval_desc (m : ℝ) (n : ℕ) :
    (descPochhammer ℤ n).smeval m = ∏ i ∈ Finset.range n, (m - i) := by
  rw [← Polynomial.aeval_eq_smeval, Polynomial.aeval_def, ← Polynomial.eval_map, descPochhammer_map,
    descPochhammer_eval_eq_prod_range]

/-- Our coefficient is Mathlib's `Ring.choose`. -/
theorem gchoose_eq_ringChoose (m : ℝ) (n : ℕ) : gchoose m n = Ring.choose m n := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose m n
  rw [smeval_desc, nsmul_eq_mul] at h
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  unfold gchoose; rw [h]; field_simp

/-- The binomial series inside the unit disc, with our coefficients. -/
theorem binom_hasSum (m y : ℝ) (hy : |y| < 1) :
    HasSum (fun a : ℕ => gchoose m a * y ^ a) ((1 + y) ^ m) := by
  have hb := (one_add_rpow_hasFPowerSeriesOnBall_zero (a := m)).hasSum
    (y := y) (by
      rw [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero]
      exact ENNReal.ofReal_lt_one.mpr hy)
  simp only [binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul, zero_add] at hb
  simpa [gchoose_eq_ringChoose] using hb

/-- The real Beta integral. -/
theorem beta_integral (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    ∫ x in (0 : ℝ)..1, x ^ (u - 1) * (1 - x) ^ (v - 1) = ProbabilityTheory.beta u v := by
  rw [ProbabilityTheory.beta_eq_betaIntegralReal u v hu hv, Complex.betaIntegral]
  have hc : (∫ x in (0 : ℝ)..1, (x : ℂ) ^ ((u : ℂ) - 1) * (1 - (x : ℂ)) ^ ((v : ℂ) - 1)) =
      ∫ x in (0 : ℝ)..1, ((x ^ (u - 1) * (1 - x) ^ (v - 1) : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    simp only
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1, Complex.ofReal_cpow (by linarith [hx.2])]
    push_cast; ring_nf
  rw [hc, intervalIntegral.integral_ofReal, Complex.ofReal_re]

theorem summable_abs_gchoose (m : ℝ) (hm : 0 < m) : Summable (fun a : ℕ => |gchoose m a|) := by
  obtain ⟨C, hC0, hC⟩ := gchoose_bound m (by linarith)
  have hs : Summable (fun a : ℕ => C * ((a : ℝ) + 1) ^ (-(m + 1))) := by
    apply Summable.mul_left
    have h1 : Summable (fun a : ℕ => ((a : ℝ)) ^ (-(m + 1))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    simpa using (summable_nat_add_iff 1).mpr h1
  exact Summable.of_nonneg_of_le (fun a => abs_nonneg _) hC hs

theorem beta_intervalIntegrable (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (fun x : ℝ => x ^ (u - 1) * (1 - x) ^ (v - 1)) MeasureTheory.volume 0 1 := by
  have h := Complex.betaIntegral_convergent (u := (u : ℂ)) (v := (v : ℂ)) (by simpa) (by simpa)
  rw [intervalIntegrable_iff] at h ⊢
  refine h.re.congr ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc fun x hx => ?_
  rw [Set.uIoc_of_le zero_le_one] at hx
  have e : (x : ℂ) ^ ((u : ℂ) - 1) * (1 - (x : ℂ)) ^ ((v : ℂ) - 1) =
      ((x ^ (u - 1) * (1 - x) ^ (v - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le, Complex.ofReal_cpow (by linarith [hx.2])]
    push_cast; ring_nf
  simp only [RCLike.re_to_complex]
  rw [e, Complex.ofReal_re]

/-- Termwise integration against the Beta density: the only analytic step. -/
theorem sum_beta (m u : ℝ) (hm : 0 < m) (hu : 0 < u) :
    HasSum (fun a : ℕ => gchoose m a * (-1) ^ a * ProbabilityTheory.beta (u + a) (m + 1))
      (ProbabilityTheory.beta u (2 * m + 1)) := by
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := 1)
    (F := fun (a : ℕ) (x : ℝ) => gchoose m a * (-1) ^ a * (x ^ (u + a - 1) * (1 - x) ^ (m + 1 - 1)))
    (f := fun x : ℝ => x ^ (u - 1) * (1 - x) ^ (2 * m + 1 - 1))
    (fun (a : ℕ) (x : ℝ) => |gchoose m a| * (x ^ (u - 1) * (1 - x) ^ (m + 1 - 1)))
    (fun a => (by fun_prop : Measurable _).aestronglyMeasurable)
    (fun a => Filter.Eventually.of_forall fun x hx => by
      rw [Set.uIoc_of_le zero_le_one] at hx
      have hx0 := hx.1
      have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
      have hp : x ^ (u + a - 1) = x ^ (u - 1) * x ^ a := by
        rw [show u + a - 1 = (u - 1) + a by ring, Real.rpow_add hx0, Real.rpow_natCast]
      have hP : 0 ≤ x ^ (u - 1) := Real.rpow_nonneg hx0.le _
      have hQ : 0 ≤ (1 - x) ^ (m + 1 - 1) := Real.rpow_nonneg hx1 _
      have hxa : x ^ a ≤ 1 := pow_le_one₀ hx0.le hx.2
      have hxa0 : 0 ≤ x ^ a := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, hp]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg hP hxa0) hQ)]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hP hxa) hQ)
    (Filter.Eventually.of_forall fun x _ => (summable_abs_gchoose m hm).mul_right _)
    (by
      have : (fun x : ℝ => ∑' a : ℕ, |gchoose m a| * (x ^ (u - 1) * (1 - x) ^ (m + 1 - 1))) =
          fun x => (∑' a : ℕ, |gchoose m a|) * (x ^ (u - 1) * (1 - x) ^ (m + 1 - 1)) := by
        funext x; exact tsum_mul_right
      rw [this]
      exact (beta_intervalIntegrable u (m + 1) hu (by linarith)).const_mul _)
    (Filter.Eventually.of_forall fun x hx => by
      rw [Set.uIoc_of_le zero_le_one] at hx
      have hx0 := hx.1
      rcases hx.2.lt_or_eq with hlt | heq
      · have hb := (binom_hasSum m (-x) (by rw [abs_neg, abs_of_pos hx0]; exact hlt)).mul_left
          (x ^ (u - 1) * (1 - x) ^ (m + 1 - 1))
        have hq : (0 : ℝ) < 1 - x := by linarith
        have ev : x ^ (u - 1) * (1 - x) ^ (m + 1 - 1) * (1 + -x) ^ m =
            x ^ (u - 1) * (1 - x) ^ (2 * m + 1 - 1) := by
          rw [show (1 : ℝ) + -x = 1 - x by ring, mul_assoc, ← Real.rpow_add hq]
          congr 2; ring
        rw [ev] at hb
        convert hb using 2 with a
        rw [show u + a - 1 = (u - 1) + a by ring, Real.rpow_add hx0, Real.rpow_natCast, neg_pow x a]
        ring
      · subst heq
        have z1 : ((1 : ℝ) - 1) ^ (m + 1 - 1) = 0 := by
          rw [sub_self]; exact Real.zero_rpow (by linarith)
        have z2 : ((1 : ℝ) - 1) ^ (2 * m + 1 - 1) = 0 := by
          rw [sub_self]; exact Real.zero_rpow (by linarith)
        simp only [z1, z2, mul_zero]
        exact hasSum_zero)
  have e1 : ∀ a : ℕ, (∫ x in (0 : ℝ)..1, x ^ (u + a - 1) * (1 - x) ^ (m + 1 - 1)) =
      ProbabilityTheory.beta (u + a) (m + 1) := fun a =>
    beta_integral (u + a) (m + 1) (by have := (Nat.cast_nonneg a : (0 : ℝ) ≤ a); linarith) (by linarith)
  simp only [intervalIntegral.integral_const_mul, e1] at key
  rwa [beta_integral u (2 * m + 1) hu (by linarith)] at key

theorem beta_succ_left (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    ProbabilityTheory.beta (u + 1) v * (u + v) = ProbabilityTheory.beta u v * u := by
  unfold ProbabilityTheory.beta
  rw [Real.Gamma_add_one hu.ne', show u + 1 + v = (u + v) + 1 by ring,
    Real.Gamma_add_one (by linarith : u + v ≠ 0)]
  have h : Gamma (u + v) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have h2 : u + v ≠ 0 := by linarith
  field_simp

theorem gamma_ne (m : ℝ) (hm0 : 0 < m) (hm : ∀ n : ℕ, m ≠ n) (t : ℕ) : Gamma (m + 1 - t) ≠ 0 := by
  apply Real.Gamma_ne_zero
  intro k hk
  have e : m = (t : ℝ) - 1 - k := by linarith
  have hlt : k + 1 ≤ t := by
    by_contra h
    have : (t : ℝ) ≤ k := by exact_mod_cast (by omega : t ≤ k)
    linarith
  apply hm (t - (k + 1))
  rw [e, Nat.cast_sub hlt]
  push_cast; ring

/-- `C(m,a+t)` against the Beta values, for `t > m`. -/
theorem gchoose_shift (m : ℝ) (hm : 0 < m) (t : ℕ) (ht : m < t) (a : ℕ) :
    gchoose m (a + t) * ProbabilityTheory.beta ((t : ℝ) - m) (m + 1) =
      gchoose m t * (-1) ^ a * ProbabilityTheory.beta ((t : ℝ) - m + a) (m + 1) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hu : 0 < (t : ℝ) - m + a := by
      have := (Nat.cast_nonneg a : (0 : ℝ) ≤ a); linarith
    have hb := beta_succ_left ((t : ℝ) - m + a) (m + 1) hu (by linarith)
    have ed : (t : ℝ) - m + a + (m + 1) = ((a + t : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [ed] at hb
    have hd2 : ((a + t : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    have eb : ProbabilityTheory.beta ((t : ℝ) - m + (a + 1 : ℕ)) (m + 1) =
        ProbabilityTheory.beta ((t : ℝ) - m + a) (m + 1) * ((t : ℝ) - m + a) / (((a + t : ℕ) : ℝ) + 1) := by
      rw [eq_div_iff hd2, ← hb]; push_cast; ring_nf
    rw [show a + 1 + t = (a + t) + 1 by omega, gchoose_succ, eb, pow_succ]
    calc gchoose m (a + t) * (m - ((a + t : ℕ) : ℝ)) / (((a + t : ℕ) : ℝ) + 1) * ProbabilityTheory.beta ((t : ℝ) - m) (m + 1)
        = (gchoose m (a + t) * ProbabilityTheory.beta ((t : ℝ) - m) (m + 1)) * (m - ((a + t : ℕ) : ℝ)) / (((a + t : ℕ) : ℝ) + 1) := by ring
      _ = _ := by rw [ih]; push_cast; ring

/-- The target value. -/
noncomputable def Btarget (m : ℝ) (t : ℕ) : ℝ := Gamma (2 * m + 1) / (Gamma (m + 1 + t) * Gamma (m + 1 - t))

theorem Bsum_large (m : ℝ) (hm0 : 0 < m) (hm : ∀ n : ℕ, m ≠ n) (t : ℕ) (ht : m < t) :
    Bsum m t = Btarget m t := by
  have hu : 0 < (t : ℝ) - m := by linarith
  have hb0 : ProbabilityTheory.beta ((t : ℝ) - m) (m + 1) ≠ 0 :=
    (ProbabilityTheory.beta_pos hu (by linarith)).ne'
  have hs := (sum_beta m ((t : ℝ) - m) hm0 hu).mul_left
    (gchoose m t / ProbabilityTheory.beta ((t : ℝ) - m) (m + 1))
  have eT : (fun a : ℕ => gchoose m t / ProbabilityTheory.beta ((t : ℝ) - m) (m + 1) *
      (gchoose m a * (-1) ^ a * ProbabilityTheory.beta ((t : ℝ) - m + a) (m + 1))) =
      fun a => gchoose m a * gchoose m (a + t) := by
    funext a
    have := gchoose_shift m hm0 t ht a
    rw [div_mul_eq_mul_div, div_eq_iff hb0]
    linear_combination (-gchoose m a) * this
  rw [eT] at hs
  unfold Bsum
  rw [hs.tsum_eq, gchoose_eq_Gamma m hm0 hm t]
  unfold Btarget ProbabilityTheory.beta
  rw [show (t : ℝ) - m + (m + 1) = t + 1 by ring, show (t : ℝ) - m + (2 * m + 1) = m + 1 + t by ring]
  have g1 : Gamma (m + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have g2 : Gamma ((t : ℝ) + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have g3 : Gamma ((t : ℝ) - m) ≠ 0 := (Real.Gamma_pos_of_pos hu).ne'
  have g4 : Gamma (m + 1 + t) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have g5 := gamma_ne m hm0 hm t
  field_simp

theorem Btarget_recur (m : ℝ) (hm0 : 0 < m) (hm : ∀ n : ℕ, m ≠ n) (t : ℕ) :
    (m + 1 + t) * Btarget m (t + 1) = (m - t) * Btarget m t := by
  unfold Btarget
  have hmt : m - t ≠ 0 := sub_ne_zero.mpr (hm t)
  have e1 : m + 1 + ((t + 1 : ℕ) : ℝ) = (m + 1 + t) + 1 := by push_cast; ring
  have e2 : m + 1 - ((t + 1 : ℕ) : ℝ) = m - t := by push_cast; ring
  have hp : m + 1 + (t : ℝ) ≠ 0 := by positivity
  have g2 : Gamma (m - t) ≠ 0 := by
    have := gamma_ne m hm0 hm (t + 1); rwa [e2] at this
  rw [e1, e2, Real.Gamma_add_one hp, show m + 1 - (t : ℝ) = (m - t) + 1 by ring, Real.Gamma_add_one hmt]
  have g1 : Gamma (m + 1 + t) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  field_simp

/-- Gauss's `₂F₁(1)` in binomial form, for positive non-integer `m`
(integer `n` is the finite case, already covered by the main theorem). -/
theorem gauss_binom_real (m : ℝ) (hm0 : 0 < m) (hm : ∀ n : ℕ, m ≠ n) (t : ℕ) :
    HasSum (fun a : ℕ => gchoose m a * gchoose m (a + t))
      (Gamma (2 * m + 1) / (Gamma (m + 1 + t) * Gamma (m + 1 - t))) := by
  have all : ∀ k t : ℕ, m < (t : ℝ) + k → Bsum m t = Btarget m t := by
    intro k
    induction k with
    | zero => intro t ht; exact Bsum_large m hm0 hm t (by simpa using ht)
    | succ k ih =>
      intro t ht
      have h1 := ih (t + 1) (by push_cast at ht ⊢; linarith)
      have hmt : m - t ≠ 0 := sub_ne_zero.mpr (hm t)
      apply mul_left_cancel₀ hmt
      rw [← Bsum_recur m hm0 t, ← Btarget_recur m hm0 hm t, h1]
  have hB : Bsum m t = Btarget m t := all ⌈m⌉₊ t (by
    have := Nat.le_ceil m
    have := (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
    by_contra hc
    have h0 : (0 : ℝ) < ⌈m⌉₊ := Nat.cast_pos.mpr (Nat.ceil_pos.mpr hm0)
    have heq : m = (⌈m⌉₊ : ℝ) := by linarith
    exact hm _ heq)
  have hs := ((summable_gchoose_mul m (by linarith) t).of_abs).hasSum
  have e : (∑' a : ℕ, gchoose m a * gchoose m (a + t)) = Btarget m t := hB
  rw [e] at hs
  exact hs

/-- The binomial series at the boundary point `y = 1` (Abel's limit theorem). -/
theorem gchoose_hasSum_two (m : ℝ) (hm : 0 < m) : HasSum (gchoose m) ((2 : ℝ) ^ m) := by
  have hs : Summable (gchoose m) := (summable_abs_gchoose m hm).of_abs
  have hA := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hs.hasSum.tendsto_sum_nat
  have hC : Filter.Tendsto (fun x : ℝ => (1 + x) ^ m) (nhdsWithin 1 (Set.Iio 1)) (nhds ((2 : ℝ) ^ m)) := by
    have hc : ContinuousAt (fun x : ℝ => (1 + x) ^ m) 1 :=
      ContinuousAt.rpow_const (by fun_prop) (Or.inr hm.le)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    norm_num at this ⊢
    exact this
  have hE : (fun x : ℝ => ∑' n, gchoose m n * x ^ n) =ᶠ[nhdsWithin 1 (Set.Iio 1)] fun x => (1 + x) ^ m := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact (binom_hasSum m x (by rw [abs_of_pos hx.1]; exact hx.2)).tsum_eq
  have := tendsto_nhds_unique (hA.congr' hE) hC
  rw [← this]; exact hs.hasSum

/-- Splitting the double series by the sign of `b - a`: `4^m = B(m,0) + 2 ∑ₜ B(m,t+1)`. -/
theorem four_pow_split (m : ℝ) (hm : 0 < m) :
    ((2 : ℝ) ^ m) * ((2 : ℝ) ^ m) = Bsum m 0 + 2 * ∑' t : ℕ, Bsum m (t + 1) := by
  have hn : Summable (fun a => ‖gchoose m a‖) := by
    simpa [Real.norm_eq_abs] using summable_abs_gchoose m hm
  set F : ℕ × ℕ → ℝ := fun p => gchoose m p.1 * gchoose m p.2 with hFdef
  have hF : Summable F := summable_mul_of_summable_norm hn hn
  have hprod : ((2 : ℝ) ^ m) * ((2 : ℝ) ^ m) = ∑' p, F p := by
    rw [← (gchoose_hasSum_two m hm).tsum_eq]
    exact tsum_mul_tsum_of_summable_norm hn hn
  let i1 : ℕ × ℕ → ℕ × ℕ := fun p => (p.2, p.2 + (p.1 + 1))
  let i2 : ℕ × ℕ → ℕ × ℕ := fun p => (p.2 + (p.1 + 1), p.2)
  let i0 : ℕ → ℕ × ℕ := fun a => (a, a)
  have inj1 : Function.Injective i1 := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [i1, Prod.mk.injEq] at h ⊢; omega
  have inj2 : Function.Injective i2 := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [i2, Prod.mk.injEq] at h ⊢; omega
  have inj0 : Function.Injective i0 := by
    intro a b h; simpa [i0] using congrArg Prod.fst h
  have s1 : Summable (F ∘ i1) := hF.comp_injective inj1
  have s2 : Summable (F ∘ i2) := hF.comp_injective inj2
  have s0 : Summable (F ∘ i0) := hF.comp_injective inj0
  have r12 : Disjoint (Set.range i1) (Set.range i2) := by
    rw [Set.disjoint_left]; rintro _ ⟨p, rfl⟩ ⟨q, hq⟩
    simp only [i1, i2, Prod.mk.injEq] at hq; omega
  have r0 : Disjoint (Set.range i1 ∪ Set.range i2) (Set.range i0) := by
    rw [Set.disjoint_left]; rintro _ (⟨p, rfl⟩ | ⟨p, rfl⟩) ⟨a, ha⟩ <;>
      simp only [i0, i1, i2, Prod.mk.injEq] at ha <;> omega
  have cover : (Set.range i1 ∪ Set.range i2) ∪ Set.range i0 = Set.univ := by
    ext ⟨a, b⟩
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    rcases lt_trichotomy a b with h | h | h
    · exact Or.inl (Or.inl ⟨(b - a - 1, a), by show (a, a + (b - a - 1 + 1)) = (a, b); congr 1; omega⟩)
    · exact Or.inr ⟨a, by simp [i0, h]⟩
    · exact Or.inl (Or.inr ⟨(a - b - 1, b), by show (b + (a - b - 1 + 1), b) = (a, b); congr 1; omega⟩)
  have h1 : HasSum (F ∘ i1) (∑' p, (F ∘ i1) p) := s1.hasSum
  have h2 : HasSum (F ∘ i2) (∑' p, (F ∘ i2) p) := s2.hasSum
  have h0 : HasSum (F ∘ i0) (∑' p, (F ∘ i0) p) := s0.hasSum
  have H1 : HasSum (Set.indicator (Set.range i1) F) (∑' p, (F ∘ i1) p) := by
    have := (Function.Injective.hasSum_iff inj1
      (f := Set.indicator (Set.range i1) F) (a := ∑' p, (F ∘ i1) p)
      (fun x hx => Set.indicator_of_notMem hx _)).mp
    apply this; convert h1 using 1; funext p; simp [Set.indicator_of_mem]
  have H2 : HasSum (Set.indicator (Set.range i2) F) (∑' p, (F ∘ i2) p) := by
    have := (Function.Injective.hasSum_iff inj2
      (f := Set.indicator (Set.range i2) F) (a := ∑' p, (F ∘ i2) p)
      (fun x hx => Set.indicator_of_notMem hx _)).mp
    apply this; convert h2 using 1; funext p; simp [Set.indicator_of_mem]
  have H0 : HasSum (Set.indicator (Set.range i0) F) (∑' p, (F ∘ i0) p) := by
    have := (Function.Injective.hasSum_iff inj0
      (f := Set.indicator (Set.range i0) F) (a := ∑' p, (F ∘ i0) p)
      (fun x hx => Set.indicator_of_notMem hx _)).mp
    apply this; convert h0 using 1; funext p; simp [Set.indicator_of_mem]
  have Hall : HasSum F (∑' p, (F ∘ i1) p + ∑' p, (F ∘ i2) p + ∑' p, (F ∘ i0) p) := by
    have := (H1.add H2).add H0
    convert this using 1
    funext p
    have hp : p ∈ (Set.range i1 ∪ Set.range i2) ∪ Set.range i0 := by rw [cover]; trivial
    have d12 := Set.disjoint_left.mp r12
    have d0 := Set.disjoint_left.mp r0
    show F p = Set.indicator (Set.range i1) F p + Set.indicator (Set.range i2) F p +
      Set.indicator (Set.range i0) F p
    rcases hp with (hp | hp) | hp
    · rw [Set.indicator_of_mem hp, Set.indicator_of_notMem (d12 hp),
        Set.indicator_of_notMem (d0 (Or.inl hp))]; ring
    · rw [Set.indicator_of_notMem (fun h => d12 h hp), Set.indicator_of_mem hp,
        Set.indicator_of_notMem (d0 (Or.inr hp))]; ring
    · rw [Set.indicator_of_notMem (fun h => d0 (Or.inl h) hp),
        Set.indicator_of_notMem (fun h => d0 (Or.inr h) hp), Set.indicator_of_mem hp]; ring
  have e1 : ∑' p, (F ∘ i1) p = ∑' t : ℕ, Bsum m (t + 1) := by
    rw [s1.tsum_prod' (fun t => s1.prod_factor t)]
    refine tsum_congr fun t => ?_
    simp [Bsum, hFdef, i1, Function.comp]
  have e2 : ∑' p, (F ∘ i2) p = ∑' t : ℕ, Bsum m (t + 1) := by
    rw [s2.tsum_prod' (fun t => s2.prod_factor t)]
    refine tsum_congr fun t => ?_
    simp only [Bsum, hFdef, i2, Function.comp]
    exact tsum_congr fun a => mul_comm _ _
  have e0 : ∑' p, (F ∘ i0) p = Bsum m 0 := by
    simp [Bsum, hFdef, i0, Function.comp]
  rw [hprod, Hall.tsum_eq, e1, e2, e0]; ring

/-- `y |C(m,y)|` is summable for `m > 1`. -/
theorem summable_mul_abs_gchoose (m : ℝ) (hm : 1 < m) :
    Summable (fun y : ℕ => (y : ℝ) * |gchoose m y|) := by
  obtain ⟨C, hC0, hC⟩ := gchoose_bound m (by linarith)
  have hs : Summable (fun a : ℕ => C * ((a : ℝ) + 1) ^ (-m)) := by
    apply Summable.mul_left
    have h1 : Summable (fun a : ℕ => ((a : ℝ)) ^ (-m)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    simpa using (summable_nat_add_iff 1).mpr h1
  refine Summable.of_nonneg_of_le (fun a => by positivity) (fun a => ?_) hs
  have hpos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have e : ((a : ℝ) + 1) * ((a : ℝ) + 1) ^ (-(m + 1)) = ((a : ℝ) + 1) ^ (-m) := by
    nth_rewrite 1 [← Real.rpow_one ((a : ℝ) + 1)]
    rw [← Real.rpow_add hpos]; ring_nf
  calc (a : ℝ) * |gchoose m a| ≤ ((a : ℝ) + 1) * (C * ((a : ℝ) + 1) ^ (-(m + 1))) :=
        mul_le_mul (by linarith) (hC a) (abs_nonneg _) hpos.le
    _ = C * ((a : ℝ) + 1) ^ (-m) := by rw [← e]; ring

/-- The first skew moment, written with `x = p.2`, `y = x + t + 1`, `t = p.1`:
this is `∑_{x<y} C(m,x) C(m,y) (y-x)`, i.e. the sum `S₂(m)` of the real-`n` theorem. -/
noncomputable def S2term (m : ℝ) (p : ℕ × ℕ) : ℝ :=
  gchoose m p.2 * gchoose m (p.2 + (p.1 + 1)) * ((p.1 : ℝ) + 1)

theorem summable_S2term (m : ℝ) (hm : 1 < m) : Summable (S2term m) := by
  have n1 : Summable (fun a => ‖|gchoose m a|‖) := by
    simpa [Real.norm_eq_abs] using summable_abs_gchoose m (by linarith)
  have n2 : Summable (fun y : ℕ => ‖(y : ℝ) * |gchoose m y|‖) := by
    have := summable_mul_abs_gchoose m hm
    refine this.congr fun y => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_abs, Nat.abs_cast]
  have hP := summable_mul_of_summable_norm n1 n2
  let i : ℕ × ℕ → ℕ × ℕ := fun p => (p.2, p.2 + (p.1 + 1))
  have inj : Function.Injective i := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [i, Prod.mk.injEq] at h ⊢; omega
  have hc := hP.comp_injective inj
  refine Summable.of_norm_bounded hc fun p => ?_
  simp only [S2term, Function.comp, i, Real.norm_eq_abs, abs_mul]
  have h1 : |((p.1 : ℝ) + 1)| ≤ ((p.2 + (p.1 + 1) : ℕ) : ℝ) := by
    rw [abs_of_nonneg (by positivity)]; push_cast
    linarith [(Nat.cast_nonneg p.2 : (0 : ℝ) ≤ p.2)]
  calc |gchoose m p.2| * |gchoose m (p.2 + (p.1 + 1))| * |((p.1 : ℝ) + 1)|
      ≤ |gchoose m p.2| * |gchoose m (p.2 + (p.1 + 1))| * ((p.2 + (p.1 + 1) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

/-- **The case `d = 2` of the real-`n` theorem**:
`∑_{x<y} C(m,x) C(m,y) (y-x) = (m/2) Γ(2m+1)/Γ(m+1)²` for non-integer `m > 1`. -/
theorem S2_value (m : ℝ) (hm : 1 < m) (hni : ∀ n : ℕ, m ≠ n) :
    ∑' p, S2term m p = m / 2 * (Gamma (2 * m + 1) / (Gamma (m + 1) * Gamma (m + 1))) := by
  have hm0 : 0 < m := by linarith
  have hs := summable_S2term m hm
  have hfib : ∀ t : ℕ, ∑' x : ℕ, S2term m (t, x) = ((t : ℝ) + 1) * Bsum m (t + 1) := by
    intro t
    simp only [S2term, Bsum]
    rw [tsum_mul_right]; ring
  have hT : Summable (fun t : ℕ => ((t : ℝ) + 1) * Bsum m (t + 1)) := by
    have := hs.prod
    simpa only [hfib] using this
  rw [hs.tsum_prod' (fun t => hs.prod_factor t)]
  simp only [hfib]
  set G : ℕ → ℝ := fun t => ((m + t + 1) * Bsum m (t + 1)) / 2 with hG
  have step : ∀ t : ℕ, ((t : ℝ) + 1) * Bsum m (t + 1) = G t - G (t + 1) := by
    intro t
    have h := Bsum_recur m hm0 (t + 1)
    simp only [hG]
    push_cast at h ⊢
    linarith
  have hpart : ∀ N, ∑ t ∈ Finset.range N, ((t : ℝ) + 1) * Bsum m (t + 1) = G 0 - G N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih, step]; ring
  have hzero := hT.tendsto_atTop_zero
  have hGlim : Filter.Tendsto G Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun t : ℕ => (m + 1) * |((t : ℝ) + 1) * Bsum m (t + 1)|) _ _
    · intro t
      have hp : (0 : ℝ) < (t : ℝ) + 1 := by positivity
      have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      simp only [hG, Real.norm_eq_abs, abs_div, abs_mul]
      rw [abs_of_nonneg (by linarith : 0 ≤ m + t + 1), abs_of_pos hp, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hB := abs_nonneg (Bsum m (t + 1))
      have : (m + t + 1) ≤ (m + 1) * ((t : ℝ) + 1) := by nlinarith
      have := mul_le_mul_of_nonneg_right this hB
      nlinarith [mul_nonneg hp.le hB]
    · simpa using (hzero.abs).const_mul (m + 1)
  have hlim := hT.hasSum.tendsto_sum_nat
  simp only [hpart] at hlim
  have hval : ∑' t : ℕ, ((t : ℝ) + 1) * Bsum m (t + 1) = G 0 :=
    tendsto_nhds_unique hlim (by simpa using (tendsto_const_nhds (x := G 0)).sub hGlim)
  rw [hval]
  have h0 := Bsum_recur m hm0 0
  have hB0 : Bsum m 0 = Gamma (2 * m + 1) / (Gamma (m + 1) * Gamma (m + 1)) := by
    have := (gauss_binom_real m hm0 hni 0).tsum_eq
    simpa [Bsum] using this
  simp only [hG]
  simp only [Nat.cast_zero, add_zero, zero_add, sub_zero] at h0 ⊢
  rw [h0, hB0]; ring

/-! ### Reduction of the higher skew moments -/

/-- Pascal's rule for real upper index. -/
theorem gchoose_pascal (m : ℝ) (a : ℕ) :
    gchoose (m + 1) (a + 1) = gchoose m a + gchoose m (a + 1) := by
  simp only [gchoose_eq_ringChoose]
  exact Ring.choose_succ_succ m a

/-- Absorption, one step: `(x+1) C(m,x+1) = m C(m-1,x)`. -/
theorem gchoose_absorb_one (m : ℝ) (x : ℕ) :
    ((x : ℝ) + 1) * gchoose m (x + 1) = m * gchoose (m - 1) x := by
  induction x with
  | zero => simp [gchoose_succ, gchoose_zero]
  | succ x ih =>
    have h1 : ((x : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (((x + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    rw [gchoose_succ m (x + 1), gchoose_succ (m - 1) x]
    have e : gchoose m (x + 1) = m * gchoose (m - 1) x / ((x : ℝ) + 1) := by
      rw [eq_div_iff h1, ← ih]; ring
    rw [e]; push_cast at h2 ⊢; field_simp; ring

/-- Absorption: a falling factorial in `x` lowers the upper index. -/
theorem gchoose_absorb (j : ℕ) : ∀ (m : ℝ) (x : ℕ),
    (∏ i ∈ Finset.range j, (((x + j : ℕ) : ℝ) - i)) * gchoose m (x + j) =
      (∏ i ∈ Finset.range j, (m - i)) * gchoose (m - j) x := by
  induction j with
  | zero => intro m x; simp
  | succ j ih =>
    intro m x
    have h := ih (m - 1) x
    have a1 := gchoose_absorb_one m (x + j)
    rw [Finset.prod_range_succ', Finset.prod_range_succ']
    have e1 : ∏ k ∈ Finset.range j, (((x + (j + 1) : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) =
        ∏ k ∈ Finset.range j, (((x + j : ℕ) : ℝ) - k) :=
      Finset.prod_congr rfl fun k _ => by push_cast; ring
    have e2 : ∏ k ∈ Finset.range j, (m - ((k + 1 : ℕ) : ℝ)) = ∏ k ∈ Finset.range j, (m - 1 - k) :=
      Finset.prod_congr rfl fun k _ => by push_cast; ring
    have e3 : m - ((j + 1 : ℕ) : ℝ) = m - 1 - j := by push_cast; ring
    have e4 : x + (j + 1) = (x + j) + 1 := by omega
    rw [e1, e2, e3, e4]
    set P := ∏ k ∈ Finset.range j, (((x + j : ℕ) : ℝ) - k) with hP
    set Q := ∏ k ∈ Finset.range j, (m - 1 - (k : ℝ)) with hQ
    push_cast at a1 h ⊢
    linear_combination P * a1 + m * h

/-- A falling factorial vanishes below its order. -/
theorem falling_eq_zero (j x : ℕ) (h : x < j) :
    ∏ i ∈ Finset.range j, ((x : ℝ) - i) = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.mpr h) (by simp)

/-- Vandermonde with natural step: brings different upper indices to a common one. -/
theorem gchoose_vandermonde (M : ℝ) (k : ℕ) : ∀ x : ℕ,
    gchoose (M + k) (x + k) =
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * gchoose M (x + i) := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    have hp := gchoose_pascal (M + k) (x + k)
    have e : M + ((k + 1 : ℕ) : ℝ) = (M + k) + 1 := by push_cast; ring
    rw [e, show x + (k + 1) = (x + k) + 1 by omega, hp, ih x,
      show x + k + 1 = (x + 1) + k by omega, ih (x + 1)]
    have A := Finset.sum_range_succ' (fun i => (k.choose i : ℝ) * gchoose M (x + i)) k
    have B := Finset.sum_range_succ (fun i => (k.choose (i + 1) : ℝ) * gchoose M (x + (i + 1))) k
    have C := Finset.sum_range_succ' (fun i => ((k + 1).choose i : ℝ) * gchoose M (x + i)) (k + 1)
    have D : ∑ i ∈ Finset.range (k + 1), ((k + 1).choose (i + 1) : ℝ) * gchoose M (x + (i + 1)) =
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * gchoose M (x + 1 + i) +
          ∑ i ∈ Finset.range (k + 1), (k.choose (i + 1) : ℝ) * gchoose M (x + (i + 1)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.choose_succ_succ, show x + 1 + i = x + (i + 1) by omega]
      push_cast; ring
    simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right,
      Nat.cast_one, one_mul] at A B C
    rw [C, D, B, A]
    ring

theorem summable_Bsum_succ (m : ℝ) (hm : 0 < m) : Summable (fun t : ℕ => Bsum m (t + 1)) := by
  have hn : Summable (fun a => ‖gchoose m a‖) := by
    simpa [Real.norm_eq_abs] using summable_abs_gchoose m hm
  have hF : Summable (fun p : ℕ × ℕ => gchoose m p.1 * gchoose m p.2) :=
    summable_mul_of_summable_norm hn hn
  let i : ℕ × ℕ → ℕ × ℕ := fun p => (p.2, p.2 + (p.1 + 1))
  have inj : Function.Injective i := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [i, Prod.mk.injEq] at h ⊢; omega
  simpa [Bsum, i, Function.comp] using (hF.comp_injective inj).prod

/-- Closed form of the half sums `H(m,s+1) = ∑_{b-a ≥ s+1} C(m,a) C(m,b)`. -/
theorem half_sum_value (m : ℝ) (hm : 0 < m) (s : ℕ) :
    ∑' t : ℕ, Bsum m (t + s + 1) =
      ((2 : ℝ) ^ m * (2 : ℝ) ^ m - Bsum m 0) / 2 - ∑ t ∈ Finset.range s, Bsum m (t + 1) := by
  have h := (summable_Bsum_succ m hm).sum_add_tsum_nat_add s
  have hsplit := four_pow_split m hm
  have e : ∑' t : ℕ, Bsum m (t + s + 1) = ∑' t : ℕ, Bsum m (t + s + 1) := rfl
  rw [e]
  linarith

/-! ### Composition: falling moments reduce to half sums -/

/-- Summand of the general half sum `H(p,q,s) = ∑_{a+s ≤ b} C(p,a) C(q,b)`, `s : ℤ`. -/
noncomputable def Hterm (p q : ℝ) (s : ℤ) (r : ℕ × ℕ) : ℝ :=
  if (r.1 : ℤ) + s ≤ r.2 then gchoose p r.1 * gchoose q r.2 else 0

noncomputable def Hz (p q : ℝ) (s : ℤ) : ℝ := ∑' r, Hterm p q s r

theorem summable_prod_gchoose (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    Summable (fun r : ℕ × ℕ => gchoose p r.1 * gchoose q r.2) :=
  summable_mul_of_summable_norm
    (by simpa [Real.norm_eq_abs] using summable_abs_gchoose p hp)
    (by simpa [Real.norm_eq_abs] using summable_abs_gchoose q hq)

theorem summable_Hterm (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (s : ℤ) : Summable (Hterm p q s) := by
  refine Summable.of_norm_bounded (summable_prod_gchoose p q hp hq).norm fun r => ?_
  unfold Hterm
  split_ifs
  · exact le_rfl
  · simp; positivity

/-- Complement: `H(p,q,s) + H(q,p,1-s) = 2^p 2^q`. -/
theorem Hz_complement (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (s : ℤ) :
    Hz p q s + Hz q p (1 - s) = (2 : ℝ) ^ p * (2 : ℝ) ^ q := by
  have sw : Hz q p (1 - s) = ∑' r : ℕ × ℕ, Hterm q p (1 - s) (r.2, r.1) := by
    unfold Hz
    exact ((Equiv.prodComm ℕ ℕ).tsum_eq (Hterm q p (1 - s))).symm
  have s2 : Summable (fun r : ℕ × ℕ => Hterm q p (1 - s) (r.2, r.1)) :=
    (Equiv.prodComm ℕ ℕ).summable_iff.mpr (summable_Hterm q p hq hp (1 - s))
  rw [sw, Hz, ← (summable_Hterm p q hp hq s).tsum_add s2,
    ← (gchoose_hasSum_two p hp).tsum_eq, ← (gchoose_hasSum_two q hq).tsum_eq,
    tsum_mul_tsum_of_summable_norm
      (by simpa [Real.norm_eq_abs] using summable_abs_gchoose p hp)
      (by simpa [Real.norm_eq_abs] using summable_abs_gchoose q hq)]
  refine tsum_congr fun r => ?_
  simp only [Hterm]
  by_cases h : (r.1 : ℤ) + s ≤ r.2
  · have h' : ¬ ((r.2 : ℤ) + (1 - s) ≤ r.1) := by omega
    simp [h, h']
  · have h' : (r.2 : ℤ) + (1 - s) ≤ r.1 := by omega
    simp [h, h', mul_comm]

/-- Pascal at the level of half sums. -/
theorem Hz_pascal (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (s : ℤ) :
    Hz (p + 1) q s = Hz p q s + Hz p q (s + 1) := by
  have S := summable_Hterm p q hp hq s
  have S1 := summable_Hterm p q hp hq (s + 1)
  have B := summable_Hterm (p + 1) q (by linarith) hq s
  unfold Hz
  rw [B.tsum_prod' (fun a => B.prod_factor a), S.tsum_prod' (fun a => S.prod_factor a),
    S1.tsum_prod' (fun a => S1.prod_factor a)]
  have hA : ∀ a : ℕ, ∑' b, Hterm (p + 1) q s (a + 1, b) =
      ∑' b, Hterm p q s (a + 1, b) + ∑' b, Hterm p q (s + 1) (a, b) := by
    intro a
    rw [← (S.prod_factor (a + 1)).tsum_add (S1.prod_factor a)]
    refine tsum_congr fun b => ?_
    simp only [Hterm, gchoose_pascal]
    have ca : ((a + 1 : ℕ) : ℤ) = (a : ℤ) + 1 := by push_cast; ring
    by_cases h : (a : ℤ) + 1 + s ≤ b
    · have h1 : ((a + 1 : ℕ) : ℤ) + s ≤ b := by omega
      have h2 : (a : ℤ) + (s + 1) ≤ b := by omega
      simp only [h1, h2, if_true]; ring
    · have h1 : ¬ ((a + 1 : ℕ) : ℤ) + s ≤ b := by omega
      have h2 : ¬ (a : ℤ) + (s + 1) ≤ b := by omega
      simp only [h1, h2, if_false]; ring
  have h0 : ∑' b, Hterm (p + 1) q s (0, b) = ∑' b, Hterm p q s (0, b) := by
    refine tsum_congr fun b => ?_
    simp [Hterm, gchoose_zero]
  have sB : Summable (fun a : ℕ => ∑' b, Hterm (p + 1) q s (a, b)) := B.prod
  have sS : Summable (fun a : ℕ => ∑' b, Hterm p q s (a, b)) := S.prod
  have sS1 : Summable (fun a : ℕ => ∑' b, Hterm p q (s + 1) (a, b)) := S1.prod
  rw [sB.tsum_eq_zero_add, sS.tsum_eq_zero_add, h0]
  simp only [hA]
  rw [((summable_nat_add_iff 1).mpr sS).tsum_add sS1]
  ring

/-- Common upper index: `H(M+k,M,s) = ∑ᵢ C(k,i) H(M,M,s+i)`. -/
theorem Hz_vandermonde (M : ℝ) (hM : 0 < M) (k : ℕ) : ∀ s : ℤ,
    Hz (M + k) M s = ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Hz M M (s + i) := by
  induction k with
  | zero => intro s; simp
  | succ k ih =>
    intro s
    have hk : 0 < M + (k : ℝ) := by positivity
    rw [show M + ((k + 1 : ℕ) : ℝ) = (M + k) + 1 by push_cast; ring,
      Hz_pascal (M + k) M hk hM s, ih s, ih (s + 1)]
    have A := Finset.sum_range_succ' (fun i => (k.choose i : ℝ) * Hz M M (s + i)) k
    have B := Finset.sum_range_succ (fun i => (k.choose (i + 1) : ℝ) * Hz M M (s + (i + 1 : ℕ))) k
    have C := Finset.sum_range_succ' (fun i => ((k + 1).choose i : ℝ) * Hz M M (s + i)) (k + 1)
    have D : ∑ i ∈ Finset.range (k + 1), ((k + 1).choose (i + 1) : ℝ) * Hz M M (s + (i + 1 : ℕ)) =
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Hz M M (s + 1 + i) +
          ∑ i ∈ Finset.range (k + 1), (k.choose (i + 1) : ℝ) * Hz M M (s + (i + 1 : ℕ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.choose_succ_succ, show s + 1 + (i : ℤ) = s + ((i + 1 : ℕ) : ℤ) by push_cast; ring]
      push_cast; ring
    simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right,
      Nat.cast_one, one_mul] at A B C
    rw [C, D, B, A]
    ring

/-- The half sums with equal upper index, in terms of `B(M,t)`. -/
theorem Hz_self (M : ℝ) (hM : 0 < M) (u : ℕ) :
    Hz M M ((u : ℤ) + 1) = ∑' t : ℕ, Bsum M (t + u + 1) := by
  let i : ℕ × ℕ → ℕ × ℕ := fun p => (p.2, p.2 + (p.1 + u + 1))
  have inj : Function.Injective i := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [i, Prod.mk.injEq] at h ⊢; omega
  have hsupp : Function.support (Hterm M M ((u : ℤ) + 1)) ⊆ Set.range i := by
    rintro ⟨a, b⟩ hr
    have hle : (a : ℤ) + ((u : ℤ) + 1) ≤ b := by
      by_contra hc
      exact hr (by simp [Hterm, hc])
    refine ⟨(b - a - u - 1, a), ?_⟩
    show (a, a + (b - a - u - 1 + u + 1)) = (a, b)
    congr 1; omega
  unfold Hz
  rw [← inj.tsum_eq hsupp]
  have hS : Summable (Hterm M M ((u : ℤ) + 1) ∘ i) :=
    (summable_Hterm M M hM hM _).comp_injective inj
  change ∑' p, (Hterm M M ((u : ℤ) + 1) ∘ i) p = _
  rw [hS.tsum_prod' (fun t => hS.prod_factor t)]
  refine tsum_congr fun t => ?_
  unfold Bsum
  refine tsum_congr fun a => ?_
  have hc : ((a : ℤ) + ((u : ℤ) + 1) ≤ ((a + (t + u + 1) : ℕ) : ℤ)) := by push_cast; omega
  simp [Function.comp, Hterm, i, hc]

/-- Falling factorial. -/
noncomputable def ffr (x : ℝ) (j : ℕ) : ℝ := ∏ i ∈ Finset.range j, (x - i)

/-- The moment `∑_{x<y} (x)_j (y)_l C(m,x) C(m,y)`. -/
noncomputable def FM (m : ℝ) (j l : ℕ) : ℝ :=
  ∑' r : ℕ × ℕ, if r.1 < r.2 then ffr r.1 j * ffr r.2 l * (gchoose m r.1 * gchoose m r.2) else 0

/-- Absorption turns every falling moment into a half sum. -/
theorem FM_reduce (m : ℝ) (j l : ℕ) :
    FM m j l = ffr m j * ffr m l * Hz (m - j) (m - l) ((j : ℤ) - l + 1) := by
  let e : ℕ × ℕ → ℕ × ℕ := fun r => (r.1 + j, r.2 + l)
  have inj : Function.Injective e := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [e, Prod.mk.injEq] at h ⊢; omega
  set f : ℕ × ℕ → ℝ := fun r =>
    if r.1 < r.2 then ffr r.1 j * ffr r.2 l * (gchoose m r.1 * gchoose m r.2) else 0 with hf
  have hsupp : Function.support f ⊆ Set.range e := by
    rintro ⟨x, y⟩ hr
    have hx : j ≤ x := by
      by_contra hc
      apply hr
      have : ffr (x : ℝ) j = 0 := falling_eq_zero j x (by omega)
      simp [hf, this]
    have hy : l ≤ y := by
      by_contra hc
      apply hr
      have : ffr (y : ℝ) l = 0 := falling_eq_zero l y (by omega)
      simp [hf, this]
    exact ⟨(x - j, y - l), by show (x - j + j, y - l + l) = (x, y); congr 1 <;> omega⟩
  unfold FM Hz
  rw [← tsum_mul_left]
  change ∑' r, f r = _
  rw [← inj.tsum_eq hsupp]
  refine tsum_congr fun r => ?_
  obtain ⟨a, b⟩ := r
  have A1 := gchoose_absorb j m a
  have A2 := gchoose_absorb l m b
  simp only [hf, e, Hterm]
  by_cases h : a + j < b + l
  · have h' : (a : ℤ) + ((j : ℤ) - l + 1) ≤ b := by omega
    simp only [h, h', if_true, ffr]
    calc (∏ i ∈ Finset.range j, (((a + j : ℕ) : ℝ) - i)) * (∏ i ∈ Finset.range l, (((b + l : ℕ) : ℝ) - i)) *
          (gchoose m (a + j) * gchoose m (b + l))
        = ((∏ i ∈ Finset.range j, (((a + j : ℕ) : ℝ) - i)) * gchoose m (a + j)) *
          ((∏ i ∈ Finset.range l, (((b + l : ℕ) : ℝ) - i)) * gchoose m (b + l)) := by ring
      _ = _ := by rw [A1, A2]; ring
  · have h' : ¬ (a : ℤ) + ((j : ℤ) - l + 1) ≤ b := by omega
    simp [h, h']

/-! ### Explicit values and ordinary moments -/

theorem Hz_closed_pos (M : ℝ) (hM : 0 < M) (u : ℕ) :
    Hz M M ((u : ℤ) + 1) =
      ((2 : ℝ) ^ M * (2 : ℝ) ^ M - Bsum M 0) / 2 - ∑ t ∈ Finset.range u, Bsum M (t + 1) := by
  rw [Hz_self M hM u, half_sum_value M hM u]

theorem Hz_closed_nonpos (M : ℝ) (hM : 0 < M) (u : ℕ) :
    Hz M M (-(u : ℤ)) = (2 : ℝ) ^ M * (2 : ℝ) ^ M -
      (((2 : ℝ) ^ M * (2 : ℝ) ^ M - Bsum M 0) / 2 - ∑ t ∈ Finset.range u, Bsum M (t + 1)) := by
  have h := Hz_complement M M hM hM (-(u : ℤ))
  rw [show (1 : ℤ) - -(u : ℤ) = (u : ℤ) + 1 by ring, Hz_closed_pos M hM u] at h
  linarith

/-- Value of the falling moment, `j ≤ l`. -/
theorem FM_value_le (m : ℝ) (j k : ℕ) (hM : 0 < m - j - k) :
    FM m j (j + k) = ffr m j * ffr m (j + k) *
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Hz (m - j - k) (m - j - k) (1 - (k : ℤ) + i) := by
  rw [FM_reduce]
  have e1 : m - (j : ℝ) = (m - j - k) + k := by ring
  have e2 : m - ((j + k : ℕ) : ℝ) = m - j - k := by push_cast; ring
  have e3 : (j : ℤ) - ((j + k : ℕ) : ℤ) + 1 = 1 - (k : ℤ) := by push_cast; ring
  have hv := Hz_vandermonde (m - j - k) hM k (1 - (k : ℤ))
  rw [show m - (j : ℝ) - k + k = m - j by ring] at hv
  rw [e2, e3, hv]

/-- Value of the falling moment, `j ≥ l`. -/
theorem FM_value_ge (m : ℝ) (l k : ℕ) (hM : 0 < m - l - k) :
    FM m (l + k) l = ffr m (l + k) * ffr m l *
      ((2 : ℝ) ^ (m - l - k) * (2 : ℝ) ^ (m - l) -
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Hz (m - l - k) (m - l - k) (-(k : ℤ) + i)) := by
  rw [FM_reduce]
  have e2 : m - ((l + k : ℕ) : ℝ) = m - l - k := by push_cast; ring
  have e3 : ((l + k : ℕ) : ℤ) - (l : ℤ) + 1 = (k : ℤ) + 1 := by push_cast; ring
  have hq : 0 < m - (l : ℝ) := by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
  rw [e2, e3]
  have hc := Hz_complement (m - l - k) (m - l) hM hq ((k : ℤ) + 1)
  rw [show (1 : ℤ) - ((k : ℤ) + 1) = -(k : ℤ) by ring] at hc
  have hv := Hz_vandermonde (m - l - k) hM k (-(k : ℤ))
  rw [show m - (l : ℝ) - k + k = m - l by ring] at hv
  rw [hv] at hc
  have : Hz (m - l - k) (m - l) ((k : ℤ) + 1) = (2 : ℝ) ^ (m - l - k) * (2 : ℝ) ^ (m - l) -
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Hz (m - l - k) (m - l - k) (-(k : ℤ) + i) := by
    linarith
  rw [this]

theorem ffr_natCast (x j : ℕ) : ffr (x : ℝ) j = (x.descFactorial j : ℝ) := by
  unfold ffr
  rw [← descPochhammer_eval_eq_prod_range, descPochhammer_eval_eq_descFactorial]

/-- Summand of the falling moment. -/
noncomputable def FMterm (m : ℝ) (j l : ℕ) (r : ℕ × ℕ) : ℝ :=
  if r.1 < r.2 then ffr r.1 j * ffr r.2 l * (gchoose m r.1 * gchoose m r.2) else 0

theorem summable_FMterm (m : ℝ) (j l : ℕ) (hj : (j : ℝ) < m) (hl : (l : ℝ) < m) :
    Summable (FMterm m j l) := by
  let e : ℕ × ℕ → ℕ × ℕ := fun r => (r.1 + j, r.2 + l)
  have inj : Function.Injective e := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [e, Prod.mk.injEq] at h ⊢; omega
  have hzero : ∀ r, r ∉ Set.range e → FMterm m j l r = 0 := by
    rintro ⟨x, y⟩ hr
    by_cases hx : j ≤ x
    · by_cases hy : l ≤ y
      · exact absurd ⟨(x - j, y - l), by show (x - j + j, y - l + l) = (x, y); congr 1 <;> omega⟩ hr
      · have : ffr (y : ℝ) l = 0 := falling_eq_zero l y (by omega)
        simp [FMterm, this]
    · have : ffr (x : ℝ) j = 0 := falling_eq_zero j x (by omega)
      simp [FMterm, this]
  rw [← inj.summable_iff hzero]
  have hS := (summable_Hterm (m - j) (m - l) (by linarith) (by linarith) ((j : ℤ) - l + 1)).mul_left
    (ffr m j * ffr m l)
  refine hS.congr fun r => ?_
  obtain ⟨a, b⟩ := r
  have A1 := gchoose_absorb j m a
  have A2 := gchoose_absorb l m b
  simp only [Function.comp, e, FMterm, Hterm]
  by_cases h : a + j < b + l
  · have h' : (a : ℤ) + ((j : ℤ) - l + 1) ≤ b := by omega
    simp only [h, h', ite_true, ffr]
    calc _ = ((∏ i ∈ Finset.range j, (m - i)) * gchoose (m - j) a) *
            ((∏ i ∈ Finset.range l, (m - i)) * gchoose (m - l) b) := by ring
      _ = _ := by rw [← A1, ← A2]; ring
  · have h' : ¬ (a : ℤ) + ((j : ℤ) - l + 1) ≤ b := by omega
    simp [h, h']

/-- The ordinary moment `∑_{x<y} x^a y^b C(m,x) C(m,y)`. -/
noncomputable def OM (m : ℝ) (a b : ℕ) : ℝ :=
  ∑' r : ℕ × ℕ, if r.1 < r.2 then (r.1 : ℝ) ^ a * (r.2 : ℝ) ^ b * (gchoose m r.1 * gchoose m r.2) else 0

/-- Stirling expansion: ordinary moments are finite combinations of falling moments.
The skew moment is `m_ab = OM m a b - OM m b a`. -/
theorem OM_eq_sum_FM (m : ℝ) (a b : ℕ) (ha : (a : ℝ) < m) (hb : (b : ℝ) < m) :
    OM m a b = ∑ p ∈ Finset.range (a + 1) ×ˢ Finset.range (b + 1),
      (a.stirlingSecond p.1 : ℝ) * (b.stirlingSecond p.2 : ℝ) * FM m p.1 p.2 := by
  have hpow : ∀ (x n : ℕ), (x : ℝ) ^ n =
      ∑ i ∈ Finset.range (n + 1), (n.stirlingSecond i : ℝ) * ffr (x : ℝ) i := by
    intro x n
    have := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial x n
    have h2 : ((x ^ n : ℕ) : ℝ) = ((∑ i ∈ Finset.range (n + 1), n.stirlingSecond i * x.descFactorial i : ℕ) : ℝ) := by
      rw [← this]
    push_cast at h2
    rw [h2]
    exact Finset.sum_congr rfl fun i _ => by rw [ffr_natCast]
  have hsum : HasSum (fun r : ℕ × ℕ => ∑ p ∈ Finset.range (a + 1) ×ˢ Finset.range (b + 1),
      (a.stirlingSecond p.1 : ℝ) * (b.stirlingSecond p.2 : ℝ) * FMterm m p.1 p.2 r)
      (∑ p ∈ Finset.range (a + 1) ×ˢ Finset.range (b + 1),
        (a.stirlingSecond p.1 : ℝ) * (b.stirlingSecond p.2 : ℝ) * FM m p.1 p.2) := by
    apply hasSum_sum
    rintro ⟨j, l⟩ hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    have hj : (j : ℝ) < m := lt_of_le_of_lt (by exact_mod_cast (by omega : j ≤ a)) ha
    have hl : (l : ℝ) < m := lt_of_le_of_lt (by exact_mod_cast (by omega : l ≤ b)) hb
    exact (summable_FMterm m j l hj hl).hasSum.mul_left _
  rw [← hsum.tsum_eq]
  unfold OM
  refine tsum_congr fun r => ?_
  by_cases h : r.1 < r.2
  · simp only [h, ite_true, FMterm]
    rw [hpow r.1 a, hpow r.2 b, Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  · simp [h, FMterm]

#print axioms FM_value_le
#print axioms FM_value_ge
#print axioms OM_eq_sum_FM

end GaussTarget
