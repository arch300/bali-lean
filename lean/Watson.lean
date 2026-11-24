import Mathlib

/-!
# Lemma watson of the Krawtchouk paper, by a Zeilberger certificate (Bali lab, 2026-10-31)

`F m j = (-m)_j (m-n)_j (-n/2)_j / (((1-n)/2)_j (-n)_j j!)`, `S m = Σ_{j ≤ m} F m j`.
Certificate (sage/watson_zeil.sage): `F m j - c F (m+2) j = G (j+1) - G j` with `c = ((n-m-1)/(m+1))^2`, hence
`S m = c S (m+2)`.  With `S 1 = 0` this gives `S m = 0` for odd `m ≤ H` when `n = 2H+1`.
-/

open Finset

namespace Bali.Watson

def num (m : ℕ) (n : ℚ) (j : ℕ) : ℚ := ((j : ℚ) - m) * ((m : ℚ) - n + j) * ((j : ℚ) - n / 2)
def den (n : ℚ) (j : ℕ) : ℚ := ((1 - n) / 2 + j) * (-n + j) * ((j : ℚ) + 1)

def F (m : ℕ) (n : ℚ) : ℕ → ℚ
  | 0 => 1
  | j + 1 => F m n j * (num m n j / den n j)

def S (m : ℕ) (n : ℚ) : ℚ := ∑ j ∈ range (m + 1), F m n j

def A (m : ℕ) (n : ℚ) (j : ℕ) : ℚ := ((m : ℚ) + 1 - j) * ((m : ℚ) + 2 - j) * ((m : ℚ) - n) * ((m : ℚ) + 1 - n)
def B (m : ℕ) (n : ℚ) (j : ℕ) : ℚ := ((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) - n + j) * ((m : ℚ) + 1 - n + j)

def G (m : ℕ) (n : ℚ) (j : ℕ) : ℚ :=
  F (m + 2) n j * ((j : ℚ) * ((j : ℚ) - 1 - n) * ((j : ℚ) - (1 + n) / 2))
    * (2 * (n - 2 * m - 2) * (n - m - 1) / ((m : ℚ) + 1)) / B m n j

/-- Hypotheses on `n` (all hold for odd `n = 2H+1` and `m + 2 ≤ H`). -/
structure Good (m : ℕ) (n : ℚ) : Prop where
  den_ne : ∀ i, i ≤ m + 1 → den n i ≠ 0
  B_ne : ∀ j, j ≤ m + 3 → B m n j ≠ 0

lemma F_zero_of_gt (m : ℕ) (n : ℚ) : ∀ j, m < j → F m n j = 0
  | 0, h => absurd h (Nat.not_lt_zero _)
  | j + 1, h => by
    rcases Nat.lt_or_ge m j with hj | hj
    · simp [F, F_zero_of_gt m n j hj]
    · have : j = m := by omega
      subst this; simp [F, num]

/-- `F (m+2) j · A j = F m j · B j` for `j ≤ m + 2`. -/
lemma F_shift (m : ℕ) (n : ℚ) (hg : Good m n) : ∀ j, j ≤ m + 2 → F (m + 2) n j * A m n j = F m n j * B m n j
  | 0, _ => by simp [F, A, B]
  | j + 1, hj => by
    have ih := F_shift m n hg j (by omega)
    have hd := hg.den_ne j (by omega)
    have hB := hg.B_ne j (by omega)
    simp only [F]
    have key : num (m + 2) n j * A m n (j + 1) * B m n j = num m n j * B m n (j + 1) * A m n j := by
      simp only [num, A, B]; push_cast; ring
    apply mul_left_cancel₀ hB
    have : B m n j * (F (m + 2) n j * (num (m + 2) n j / den n j) * A m n (j + 1))
        = (F (m + 2) n j * A m n j) * (num m n j * B m n (j + 1)) / den n j := by
      field_simp; linear_combination (F (m + 2) n j) * key
    rw [this, ih]; field_simp

set_option maxRecDepth 20000 in
/-- The certificate, termwise. -/
lemma cert (m : ℕ) (n : ℚ) (hg : Good m n) (j : ℕ) (hj : j ≤ m + 2) :
    F m n j - ((n - m - 1) / ((m : ℚ) + 1)) ^ 2 * F (m + 2) n j = G m n (j + 1) - G m n j := by
  have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hm2 : ((m : ℚ) + 2) ≠ 0 := by positivity
  have hB := hg.B_ne j (by omega)
  have hB1 := hg.B_ne (j + 1) (by omega)
  rcases Nat.lt_or_ge j (m + 2) with hlt | hge
  · have hd := hg.den_ne j (by omega)
    have hs := F_shift m n hg j (by omega)
    -- express F m j through F (m+2) j
    have hF : F m n j = F (m + 2) n j * A m n j / B m n j := by rw [hs]; field_simp
    rw [hF]; simp only [G, F]
    simp only [num, den, A, B] at hd hB hB1 ⊢
    push_cast at hd hB hB1 ⊢
    have d1 := left_ne_zero_of_mul (left_ne_zero_of_mul hd)
    have d2 := right_ne_zero_of_mul (left_ne_zero_of_mul hd)
    have a1 := right_ne_zero_of_mul (left_ne_zero_of_mul hB)
    have a2 := right_ne_zero_of_mul hB
    have b1 := right_ne_zero_of_mul (left_ne_zero_of_mul hB1)
    have b2 := right_ne_zero_of_mul hB1
    clear hF hs hd hB hB1
    generalize F (m + 2) n j = P
    have d3 : (j : ℚ) + 1 ≠ 0 := by positivity
    have d1' : 1 - n + 2 * (j : ℚ) ≠ 0 := by intro h; apply d1; linear_combination h / 2
    have d1'' : 1 - n + (j : ℚ) * 2 ≠ 0 := by intro h; apply d1'; linarith
    rw [show (1 - n) / 2 + (j : ℚ) = (1 - n + 2 * j) / 2 by ring]
    field_simp
    ring
  · have hj' : j = m + 2 := by omega
    subst hj'
    have h0 : F (m + 2) n (m + 2 + 1) = 0 := F_zero_of_gt _ _ _ (by omega)
    have h1 : F m n (m + 2) = 0 := F_zero_of_gt _ _ _ (by omega)
    simp only [G, h0, h1, zero_mul, zero_div, zero_sub]
    simp only [B] at hB ⊢
    push_cast at hB ⊢
    have a1 := right_ne_zero_of_mul (left_ne_zero_of_mul hB)
    have a2 := right_ne_zero_of_mul hB
    field_simp
    ring

theorem S_rec (m : ℕ) (n : ℚ) (hg : Good m n) :
    S m n = ((n - m - 1) / ((m : ℚ) + 1)) ^ 2 * S (m + 2) n := by
  have tel := Finset.sum_range_sub (G m n) (m + 3)
  have hG0 : G m n 0 = 0 := by simp [G]
  have hG3 : G m n (m + 3) = 0 := by
    simp [G, F_zero_of_gt (m + 2) n (m + 3) (by omega)]
  rw [hG0, hG3, sub_zero] at tel
  have hsum : ∑ j ∈ range (m + 3), (F m n j - ((n - m - 1) / ((m : ℚ) + 1)) ^ 2 * F (m + 2) n j) = 0 := by
    rw [← tel]; exact Finset.sum_congr rfl fun j hj => cert m n hg j (by simp at hj; omega)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have e1 : ∑ j ∈ range (m + 3), F m n j = S m n := by
    simp only [S, show m + 3 = m + 1 + 2 by omega, Finset.sum_range_succ,
      F_zero_of_gt m n (m + 1) (by omega), F_zero_of_gt m n (m + 2) (by omega)]; ring
  have e2 : ∑ j ∈ range (m + 3), F (m + 2) n j = S (m + 2) n := rfl
  rw [e1, e2] at hsum; linarith

lemma S_one (n : ℚ) (hd : den n 0 ≠ 0) : S 1 n = 0 := by
  have hnd : num 1 n 0 = - den n 0 := by
    simp only [num, den, Nat.cast_zero, Nat.cast_one]; ring
  simp only [S, Finset.sum_range_succ, Finset.sum_range_zero, F]
  rw [hnd, neg_div, div_self hd]; ring

/-- **Lemma watson, vanishing half.**  For odd `n = 2H+1` and odd `m ≤ H`, `S m = 0`. -/
theorem S_odd_zero (H : ℕ) : ∀ k, 2 * k + 1 ≤ H → S (2 * k + 1) (2 * H + 1) = 0
  | 0, hk => S_one _ (by simp [den]; constructor <;> (norm_cast; omega))
  | k + 1, hk => by
    have hg : Good (2 * k + 1) (2 * H + 1) := by
      refine ⟨fun i hi => ?_, fun j hj => ?_⟩
      · simp only [den]; push_cast
        have h1 : ((1 - (2 * (H : ℚ) + 1)) / 2 + i) ≠ 0 := by
          have : (i : ℚ) < H := by exact_mod_cast (by omega : i < H)
          intro h; linarith
        have h2 : (-(2 * (H : ℚ) + 1) + i) ≠ 0 := by
          have : (i : ℚ) < 2 * H + 1 := by exact_mod_cast (by omega : i < 2 * H + 1)
          intro h; linarith
        have h3 : ((i : ℚ) + 1) ≠ 0 := by positivity
        exact mul_ne_zero (mul_ne_zero h1 h2) h3
      · simp only [B]; push_cast
        have hj' : (j : ℚ) ≤ 2 * k + 4 := by exact_mod_cast (by omega : j ≤ 2 * k + 4)
        have hH : (2 * (k : ℚ) + 3) ≤ H := by exact_mod_cast (by omega : 2 * k + 3 ≤ H)
        have a1 : ((2 * (k : ℚ) + 1) - (2 * H + 1) + j) ≠ 0 := by intro h; linarith
        have a2 : ((2 * (k : ℚ) + 1) + 1 - (2 * H + 1) + j) ≠ 0 := by intro h; linarith
        have a3 : ((2 * (k : ℚ) + 1) + 1) ≠ 0 := by positivity
        have a4 : ((2 * (k : ℚ) + 1) + 2) ≠ 0 := by positivity
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero a3 a4) a1) a2
    have ih := S_odd_zero H k (by omega)
    have hr := S_rec (2 * k + 1) (2 * H + 1) hg
    rw [ih] at hr
    have hc : (((2 * (H : ℚ) + 1) - ((2 * k + 1 : ℕ) : ℚ) - 1) / (((2 * k + 1 : ℕ) : ℚ) + 1)) ^ 2 ≠ 0 := by
      push_cast
      have : (2 * (k : ℚ) + 3) ≤ H := by exact_mod_cast (by omega : 2 * k + 3 ≤ H)
      apply pow_ne_zero; apply div_ne_zero <;> intro h <;> linarith
    have : S (2 * k + 1 + 2) (2 * H + 1) = 0 := by
      rcases mul_eq_zero.mp hr.symm with h | h
      · exact absurd h hc
      · exact h
    simpa [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring] using this

/-- `Good m (2H+1)` whenever `m + 2 ≤ H`. -/
lemma good_odd (H m : ℕ) (hm : m + 2 ≤ H) : Good m (2 * H + 1) := by
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · simp only [den]; push_cast
    have h1 : ((1 - (2 * (H : ℚ) + 1)) / 2 + i) ≠ 0 := by
      have : (i : ℚ) < H := by exact_mod_cast (by omega : i < H)
      intro h; linarith
    have h2 : (-(2 * (H : ℚ) + 1) + i) ≠ 0 := by
      have : (i : ℚ) < 2 * H + 1 := by exact_mod_cast (by omega : i < 2 * H + 1)
      intro h; linarith
    have h3 : ((i : ℚ) + 1) ≠ 0 := by positivity
    exact mul_ne_zero (mul_ne_zero h1 h2) h3
  · simp only [B]
    have hj' : (j : ℚ) ≤ m + 3 := by exact_mod_cast hj
    have hH : ((m : ℚ) + 2) ≤ H := by exact_mod_cast hm
    have a1 : ((m : ℚ) - (2 * H + 1) + j) ≠ 0 := by intro h; linarith
    have a2 : ((m : ℚ) + 1 - (2 * H + 1) + j) ≠ 0 := by intro h; linarith
    have a3 : ((m : ℚ) + 1) ≠ 0 := by positivity
    have a4 : ((m : ℚ) + 2) ≠ 0 := by positivity
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero a3 a4) a1) a2

/-- **Lemma watson, even half.**  For `n = 2H+1` and `2k ≤ H`,
`S (2k) = ∏_{i<k} ((2i+1)/(2H-2i))^2`, i.e. `[(1/2)_k / (-H)_k]^2`. -/
theorem S_even (H : ℕ) : ∀ k, 2 * k ≤ H →
    S (2 * k) (2 * H + 1) = ∏ i ∈ range k, ((2 * (i : ℚ) + 1) / (2 * H - 2 * i)) ^ 2
  | 0, _ => by simp [S, F]
  | k + 1, hk => by
    have ih := S_even H k (by omega)
    have hr := S_rec (2 * k) (2 * H + 1) (good_odd H (2 * k) (by omega))
    rw [ih] at hr
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, Finset.prod_range_succ]
    have hH : (2 * (k : ℚ) + 2) ≤ H := by exact_mod_cast (by omega : 2 * k + 2 ≤ H)
    have hne : (2 * (H : ℚ) - 2 * k) ≠ 0 := by intro h; linarith
    have hne' : ((2 * H + 1 : ℚ) - ((2 * k : ℕ) : ℚ) - 1) ≠ 0 := by push_cast; intro h; linarith
    have hc : (((2 * H + 1 : ℚ) - ((2 * k : ℕ) : ℚ) - 1) / (((2 * k : ℕ) : ℚ) + 1)) ^ 2 ≠ 0 := by
      apply pow_ne_zero; apply div_ne_zero hne'; positivity
    have : S (2 * k + 2) (2 * H + 1) = (∏ i ∈ range k, ((2 * (i : ℚ) + 1) / (2 * H - 2 * i)) ^ 2)
        / (((2 * H + 1 : ℚ) - ((2 * k : ℕ) : ℚ) - 1) / (((2 * k : ℕ) : ℚ) + 1)) ^ 2 := by
      rw [eq_div_iff hc, hr]; ring
    rw [this]; push_cast
    rw [show (2 * (H : ℚ) + 1 - 2 * k - 1) = 2 * H - 2 * k by ring, div_eq_mul_inv, ← inv_pow, inv_div]

end Bali.Watson

#print axioms Bali.Watson.S_odd_zero
#print axioms Bali.Watson.S_rec
#print axioms Bali.Watson.S_even
