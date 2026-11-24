import P699.BplusGram
import P699.TWatson

/-!
# Type B⁺: the totals `T'_a = T'_0 / C(n,a)` (Bali lab, 2026-11-02)
`T'_a = 2 Σ_j c_j I_j` with the half sums `I_j = n^(2j) (n-2j) C(n-2j-1, L-j)`; the remaining sum in `j`
is Chu–Vandermonde `₂F₁(-a, a-n; -n; 1) = 1/C(n,a)` (WZ certificate `-j(j-n-1)/((a+1)(a-n))`).
-/

open Finset

namespace Bali.BP
open Bali

/-! ## Chu–Vandermonde -/

def v (n a : ℕ) : ℕ → ℚ
  | 0 => 1
  | j + 1 => v n a j * (((j : ℚ) - a) * ((a : ℚ) - n + j) / (((j : ℚ) - n) * ((j : ℚ) + 1)))

lemma v_gt (n a : ℕ) : ∀ i, v n a (a + 1 + i) = 0
  | 0 => by simp [v]
  | i + 1 => by
    rw [show a + 1 + (i + 1) = (a + 1 + i) + 1 by ring, v, v_gt n a i, zero_mul]

lemma v_shift (n a : ℕ) : ∀ j, v n (a + 1) j * ((a : ℚ) + 1 - j) * ((a : ℚ) - n)
    = v n a j * ((a : ℚ) + 1) * ((a : ℚ) - n + j)
  | 0 => by simp [v]
  | j + 1 => by
    have ih := v_shift n a j
    simp only [v]
    push_cast
    linear_combination (-((a : ℚ) - j) * ((a : ℚ) + 1 - n + j) / (((j : ℚ) - n) * ((j : ℚ) + 1))) * ih

lemma v_tele (n a : ℕ) (ha : 2 * a + 3 ≤ n) : ∀ J, J ≤ a + 2 →
    ∑ j ∈ range J, (((n : ℚ) - a) * v n (a + 1) j - ((a : ℚ) + 1) * v n a j)
      = -((J : ℚ) * ((J : ℚ) - n - 1) * ((n : ℚ) - 2 * a - 1) * v n (a + 1) J)
          / (((a : ℚ) + 1) * ((a : ℚ) - n + J))
  | 0, _ => by simp
  | J + 1, hJ => by
    rw [sum_range_succ, v_tele n a ha J (by omega)]
    have hJa : (J : ℚ) ≤ (a : ℚ) + 1 := by exact_mod_cast (by omega : J ≤ a + 1)
    have han : 2 * (a : ℚ) + 3 ≤ n := by exact_mod_cast ha
    have hJ0 : (0 : ℚ) ≤ J := by positivity
    have d1 : (a : ℚ) + 1 ≠ 0 := by positivity
    have d2 : (a : ℚ) - n + J ≠ 0 := by intro h; linarith
    have d3 : (a : ℚ) - n + J + 1 ≠ 0 := by intro h; linarith
    have d4 : (J : ℚ) - n ≠ 0 := by intro h; linarith
    have d5 : (J : ℚ) + 1 ≠ 0 := by positivity
    have d6 : (a : ℚ) - n ≠ 0 := by intro h; linarith
    have h0 : v n a J = v n (a + 1) J * ((a : ℚ) + 1 - J) * ((a : ℚ) - n) / (((a : ℚ) + 1) * ((a : ℚ) - n + J)) := by
      rw [v_shift]; field_simp
    have h1 : v n (a + 1) (J + 1) = v n (a + 1) J * (((J : ℚ) - (a + 1)) * ((a : ℚ) + 1 - n + J) / (((J : ℚ) - n) * ((J : ℚ) + 1))) := by
      simp only [v]; push_cast; ring
    rw [h0, h1]
    push_cast
    rw [show (a : ℚ) - n + (J + 1) = (a : ℚ) - n + J + 1 by ring]
    field_simp
    ring

theorem chu (n : ℕ) : ∀ a, 2 * a + 1 ≤ n → (n.choose a : ℚ) * ∑ j ∈ range (a + 1), v n a j = 1
  | 0, _ => by simp [v]
  | a + 1, ha => by
    have ih := chu n a (by omega)
    have ht := v_tele n a (by omega) (a + 2) le_rfl
    have hz : v n (a + 1) (a + 2) = 0 := by simpa using v_gt n (a + 1) 0
    rw [hz, mul_zero, neg_zero, zero_div, sum_sub_distrib, ← mul_sum, ← mul_sum] at ht
    have hS : ∑ j ∈ range (a + 2), v n a j = ∑ j ∈ range (a + 1), v n a j := by
      rw [sum_range_succ, show v n a (a + 1) = 0 by simpa using v_gt n a 0, add_zero]
    rw [hS] at ht
    have hc := Nat.choose_succ_right_eq n a
    have hcq : ((n.choose (a + 1) : ℕ) : ℚ) * ((a : ℚ) + 1) = (n.choose a : ℚ) * ((n : ℚ) - a) := by
      have := congrArg (fun z : ℕ => (z : ℚ)) hc
      push_cast [Nat.cast_sub (show a ≤ n by omega)] at this
      linarith
    have d1 : (a : ℚ) + 1 ≠ 0 := by positivity
    apply mul_left_cancel₀ d1
    rw [show a + 1 + 1 = a + 2 by ring]
    linear_combination (∑ j ∈ range (a + 2), v n (a + 1) j) * hcq + (n.choose a : ℚ) * ht + ((a : ℚ) + 1) * ih

/-! ## half sums -/

lemma half_sum (N : ℕ) : ∀ L, ∑ y ∈ range (L + 1), ((N + 1).choose y : ℚ) * (((N : ℚ) + 1) - 2 * y)
    = ((N : ℚ) + 1) * (N.choose L : ℚ)
  | 0 => by simp
  | L + 1 => by
    rw [sum_range_succ, half_sum N L, Nat.choose_succ_succ]
    have h : ((N.choose (L + 1) : ℕ) : ℚ) * ((L : ℚ) + 1) = (N.choose L : ℚ) * ((N : ℚ) - L) := by
      rcases le_or_gt L N with hl | hl
      · have := congrArg (fun z : ℕ => (z : ℚ)) (Nat.choose_succ_right_eq N L)
        push_cast [Nat.cast_sub hl] at this
        linarith
      · rw [Nat.choose_eq_zero_of_lt hl, Nat.choose_eq_zero_of_lt (by omega)]; simp
    push_cast
    linear_combination (-2 : ℚ) * h

/-- `E j = n^(2j) (n-2j) C(n-2j-1, L-j)`. -/
def E (n L j : ℕ) : ℚ := (n.descFactorial (2 * j) : ℚ) * ((n : ℚ) - 2 * j) * ((n - 2 * j - 1).choose (L - j) : ℚ)

lemma Ij (n L j : ℕ) (hL : 2 * L + 1 ≤ n) (hj : j ≤ L) :
    ∑ x ∈ range (L + 1), (n.choose x : ℚ) * (((n : ℚ) - 2 * x) * Bali.Racah.phi (n : ℚ) j (x : ℚ)) = E n L j := by
  rw [show L + 1 = j + (L - j + 1) by omega, sum_range_add]
  have hz : ∑ x ∈ range j, (n.choose x : ℚ) * (((n : ℚ) - 2 * x) * Bali.Racah.phi (n : ℚ) j (x : ℚ)) = 0 := by
    refine sum_eq_zero fun x hx => ?_
    have hx' := mem_range.1 hx
    rw [Bali.TW.phi_nat n x j (by omega), Nat.descFactorial_eq_zero_iff_lt.2 hx']; simp
  rw [hz, zero_add]
  obtain ⟨N, hN⟩ : ∃ N, n - 2 * j = N + 1 := ⟨n - 2 * j - 1, by omega⟩
  have key : ∀ y ∈ range (L - j + 1),
      (n.choose (j + y) : ℚ) * (((n : ℚ) - 2 * ((j + y : ℕ) : ℚ)) * Bali.Racah.phi (n : ℚ) j ((j + y : ℕ) : ℚ))
        = (n.descFactorial (2 * j) : ℚ) * (((N + 1).choose y : ℚ) * (((N : ℚ) + 1) - 2 * y)) := by
    intro y hy
    have hy' := mem_range.1 hy
    rw [Bali.TW.phi_nat n (j + y) j (by omega)]
    have h := Bali.TW.choose_desc n (j + y) j (by omega) (by omega)
    rw [show j + y - j = y by omega, hN] at h
    have hq := congrArg (fun z : ℕ => (z : ℚ)) h
    push_cast at hq
    have hNq : (N : ℚ) + 1 = (n : ℚ) - 2 * j := by
      have := congrArg (fun z : ℕ => (z : ℚ)) hN
      push_cast [Nat.cast_sub (show 2 * j ≤ n by omega)] at this
      linarith
    rw [hNq]
    push_cast
    linear_combination ((n : ℚ) - 2 * j - 2 * y) * hq
  rw [sum_congr rfl key, ← mul_sum, half_sum N (L - j)]
  unfold E
  have hNq : (N : ℚ) + 1 = (n : ℚ) - 2 * j := by
    have := congrArg (fun z : ℕ => (z : ℚ)) hN
    push_cast [Nat.cast_sub (show 2 * j ≤ n by omega)] at this
    linarith
  rw [hNq, show n - 2 * j - 1 = N by omega]
  ring

lemma E_succ (n L j : ℕ) (hL : 2 * L + 1 ≤ n) (hj : j + 1 ≤ L) :
    E n L (j + 1) = E n L j * ((L : ℚ) - j) * ((n : ℚ) - 1 - L - j) := by
  obtain ⟨N, hN⟩ : ∃ N, n - 2 * j - 1 = N + 2 := ⟨n - 2 * j - 3, by omega⟩
  obtain ⟨K, hK⟩ : ∃ K, L - j = K + 1 := ⟨L - j - 1, by omega⟩
  unfold E
  rw [show n - 2 * (j + 1) - 1 = N by omega, show L - (j + 1) = K by omega, hN, hK]
  have hd : (n.descFactorial (2 * (j + 1)) : ℚ)
      = (n.descFactorial (2 * j) : ℚ) * ((n : ℚ) - 2 * j) * ((n : ℚ) - 2 * j - 1) := by
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.descFactorial_succ, Nat.descFactorial_succ]
    push_cast [Nat.cast_sub (show 2 * j + 1 ≤ n by omega), Nat.cast_sub (show 2 * j ≤ n by omega)]
    ring
  have c1 := congrArg (fun z : ℕ => (z : ℚ)) (Nat.add_one_mul_choose_eq (N + 1) K)
  have c2 := congrArg (fun z : ℕ => (z : ℚ)) (Nat.choose_mul_succ_eq N K)
  rcases le_or_gt K N with hKN | hKN
  · push_cast [Nat.succ_eq_add_one, Nat.cast_sub (show K ≤ N + 1 by omega)] at c1 c2
    have hNn : (N : ℚ) + 2 = (n : ℚ) - 2 * j - 1 := by
      have : (n : ℚ) = (N : ℚ) + 3 + 2 * j := by exact_mod_cast (by omega : n = N + 3 + 2 * j)
      linarith
    have hKL : (K : ℚ) + 1 = (L : ℚ) - j := by
      have := congrArg (fun z : ℕ => (z : ℚ)) hK
      push_cast [Nat.cast_sub (show j ≤ L by omega)] at this
      linarith
    rw [hd]
    have e1 : (L : ℚ) - j = (K : ℚ) + 1 := hKL.symm
    have e2 : (n : ℚ) - 1 - L - j = (N : ℚ) + 1 - K := by linarith
    have e3 : (n : ℚ) - 2 * (j + 1 : ℕ) = (N : ℚ) + 1 := by push_cast; linarith
    have e4 : (n : ℚ) - 2 * j - 1 = (N : ℚ) + 2 := hNn.symm
    rw [e1, e2, e3, e4]
    push_cast at c1 c2 ⊢
    linear_combination (n.descFactorial (2 * j) : ℚ) * ((n : ℚ) - 2 * j) * (((N : ℚ) + 1 - K) * c1 + ((N : ℚ) + 2) * c2)
  · -- K > N: both sides vanish
    have hK0 : (N.choose K : ℚ) = 0 := by rw [Nat.choose_eq_zero_of_lt hKN]; simp
    have hKL : (n : ℚ) - 1 - L - j = 0 ∨ ((N + 2).choose (K + 1) : ℚ) = 0 := by
      rcases Nat.lt_or_ge (N + 2) (K + 1) with h | h
      · right; rw [Nat.choose_eq_zero_of_lt h]; simp
      · left
        have : K = N + 1 := by omega
        have hq1 : (n : ℚ) = (N : ℚ) + 3 + 2 * j := by exact_mod_cast (by omega : n = N + 3 + 2 * j)
        have hq2 : (L : ℚ) = (N : ℚ) + 2 + j := by exact_mod_cast (by omega : L = N + 2 + j)
        linarith
    rw [hK0]
    rcases hKL with h | h
    · rw [h]; ring
    · rw [h]; ring

/-! ## the totals -/

lemma cE_odd (H a : ℕ) (ha : a ≤ H) : ∀ j, j ≤ a →
    Bali.Racah.c (2 * H + 1) a j * E (2 * H + 1) H j = E (2 * H + 1) H 0 * v (2 * H + 1) a j
  | 0, _ => by simp [Bali.Racah.c, v]
  | j + 1, hj => by
    have ih := cE_odd H a ha j (by omega)
    rw [E_succ (2 * H + 1) H j (by omega) (by omega)]
    simp only [Bali.Racah.c, v]
    have hn : ((2 * H + 1 : ℕ) : ℚ) = 2 * (H : ℚ) + 1 := by push_cast; ring
    rw [hn]
    have hjH : (j : ℚ) + 1 ≤ H := by exact_mod_cast (by omega : j + 1 ≤ H)
    have hj0 : (0 : ℚ) ≤ j := by positivity
    have d1 : (j : ℚ) - H ≠ 0 := by intro h; linarith
    have d2 : (j : ℚ) - (2 * (H : ℚ) + 1) ≠ 0 := by intro h; linarith
    have d3 : (j : ℚ) + 1 ≠ 0 := by positivity
    have hr : ((j : ℚ) - a) * ((a : ℚ) - (2 * H + 1) + j)
          / (((1 - (2 * (H : ℚ) + 1)) / 2 + j) ^ 2 * (-(2 * (H : ℚ) + 1) + j) * ((j : ℚ) + 1))
          * (((H : ℚ) - j) * ((2 * (H : ℚ) + 1) - 1 - H - j))
        = ((j : ℚ) - a) * ((a : ℚ) - (2 * H + 1) + j) / (((j : ℚ) - (2 * (H : ℚ) + 1)) * ((j : ℚ) + 1)) := by
      rw [show (1 - (2 * (H : ℚ) + 1)) / 2 + j = (j : ℚ) - H by ring,
        show -(2 * (H : ℚ) + 1) + j = (j : ℚ) - (2 * (H : ℚ) + 1) by ring]
      field_simp
      ring
    linear_combination (((j : ℚ) - a) * ((a : ℚ) - (2 * H + 1) + j) / (((j : ℚ) - (2 * (H : ℚ) + 1)) * ((j : ℚ) + 1))) * ih
      + Bali.Racah.c (2 * H + 1) a j * E (2 * H + 1) H j * hr

lemma cE_even (M a : ℕ) (ha : a ≤ M) : ∀ j, j ≤ a →
    Bali.RE.ce (M + 1) a j * E (2 * M + 2) M j = E (2 * M + 2) M 0 * v (2 * M + 2) a j
  | 0, _ => by simp [Bali.RE.ce, v]
  | j + 1, hj => by
    have ih := cE_even M a ha j (by omega)
    rw [E_succ (2 * M + 2) M j (by omega) (by omega)]
    simp only [Bali.RE.ce, v]
    have hn : ((2 * M + 2 : ℕ) : ℚ) = 2 * (M : ℚ) + 2 := by push_cast; ring
    have hm : ((M + 1 : ℕ) : ℚ) = (M : ℚ) + 1 := by push_cast; ring
    rw [hn, hm]
    have hjM : (j : ℚ) + 1 ≤ M := by exact_mod_cast (by omega : j + 1 ≤ M)
    have hj0 : (0 : ℚ) ≤ j := by positivity
    have d1 : (j : ℚ) - M ≠ 0 := by intro h; linarith
    have d2 : (j : ℚ) - M - 1 ≠ 0 := by intro h; linarith
    have d3 : (j : ℚ) - (2 * (M : ℚ) + 2) ≠ 0 := by intro h; linarith
    have d4 : (j : ℚ) + 1 ≠ 0 := by positivity
    have hr : ((j : ℚ) - a) * ((a : ℚ) - 2 * ((M : ℚ) + 1) + j)
          / ((1 - ((M : ℚ) + 1) + j) * ((j : ℚ) - ((M : ℚ) + 1)) * ((j : ℚ) - 2 * ((M : ℚ) + 1)) * ((j : ℚ) + 1))
          * (((M : ℚ) - j) * ((2 * (M : ℚ) + 2) - 1 - M - j))
        = ((j : ℚ) - a) * ((a : ℚ) - (2 * M + 2) + j) / (((j : ℚ) - (2 * (M : ℚ) + 2)) * ((j : ℚ) + 1)) := by
      rw [show 1 - ((M : ℚ) + 1) + j = (j : ℚ) - M by ring,
        show (j : ℚ) - ((M : ℚ) + 1) = (j : ℚ) - M - 1 by ring,
        show (j : ℚ) - 2 * ((M : ℚ) + 1) = (j : ℚ) - (2 * (M : ℚ) + 2) by ring,
        show (a : ℚ) - 2 * ((M : ℚ) + 1) + j = (a : ℚ) - (2 * M + 2) + j by ring]
      field_simp
      ring
    linear_combination (((j : ℚ) - a) * ((a : ℚ) - (2 * M + 2) + j) / (((j : ℚ) - (2 * (M : ℚ) + 2)) * ((j : ℚ) + 1))) * ih
      + Bali.RE.ce (M + 1) a j * E (2 * M + 2) M j * hr

/-- **odd `n`:** `C(n,a) T'_a = 2 n C(n-1,H)`. -/
theorem TpO_closed (H a : ℕ) (ha : a ≤ H) :
    ((2 * H + 1).choose a : ℚ) * TpO H a = 2 * (2 * (H : ℚ) + 1) * ((2 * H).choose H : ℚ) := by
  have hn : ((2 * H + 1 : ℕ) : ℚ) = 2 * (H : ℚ) + 1 := by push_cast; ring
  have hk : ∀ k : ℕ, 2 * ((2 * H + 1).choose k : ℚ) * ((2 * (H : ℚ) + 1 - 2 * k) * Bali.Racah.Rq (2 * H + 1) a k)
      = ∑ j ∈ range (a + 1), 2 * (Bali.Racah.c (2 * H + 1) a j *
          (((2 * H + 1).choose k : ℚ) * ((2 * (H : ℚ) + 1 - 2 * k) * Bali.Racah.phi (2 * H + 1) j k))) := by
    intro k
    rw [Bali.Racah.Rq, mul_sum, mul_sum]
    exact sum_congr rfl fun _ _ => by ring
  have hT : TpO H a = 2 * ∑ j ∈ range (a + 1), Bali.Racah.c (2 * H + 1) a j * E (2 * H + 1) H j := by
    rw [TpO, sum_congr rfl fun k _ => hk k, sum_comm, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.1 hj
    rw [← Ij (2 * H + 1) H j (by omega) (by omega), hn, ← mul_sum, ← mul_sum]
  have hE0 : E (2 * H + 1) H 0 = (2 * (H : ℚ) + 1) * ((2 * H).choose H : ℚ) := by
    unfold E
    rw [show 2 * H + 1 - 2 * 0 - 1 = 2 * H by omega, show H - 0 = H from rfl,
      show 2 * 0 = 0 from rfl, Nat.descFactorial_zero]
    push_cast; ring
  have hS := sum_congr (rfl : range (a + 1) = range (a + 1))
    (fun j hj => cE_odd H a ha j (by have := mem_range.1 hj; omega))
  have hc := chu (2 * H + 1) a (by omega)
  rw [hT, hS, ← mul_sum, hE0]
  linear_combination (2 * ((2 * (H : ℚ) + 1) * ((2 * H).choose H : ℚ))) * hc

/-- **even `n`:** `C(n,a) T'_a = 2 n C(n-1,M)`. -/
theorem TpE_closed (M a : ℕ) (ha : a ≤ M) :
    ((2 * M + 2).choose a : ℚ) * TpE M a = 2 * (2 * (M : ℚ) + 2) * ((2 * M + 1).choose M : ℚ) := by
  have hn : ((2 * M + 2 : ℕ) : ℚ) = 2 * ((M + 1 : ℕ) : ℚ) := by push_cast; ring
  have hk : ∀ k : ℕ, 2 * ((2 * (M + 1)).choose k : ℚ) * ((2 * ((M + 1 : ℕ) : ℚ) - 2 * k) * Bali.RE.RE (M + 1) a k)
      = ∑ j ∈ range (a + 1), 2 * (Bali.RE.ce (M + 1) a j *
          (((2 * M + 2).choose k : ℚ) * ((2 * ((M + 1 : ℕ) : ℚ) - 2 * k) * Bali.Racah.phi (2 * ((M + 1 : ℕ) : ℚ)) j k))) := by
    intro k
    rw [Bali.RE.RE, mul_sum, mul_sum, show 2 * (M + 1) = 2 * M + 2 by ring]
    exact sum_congr rfl fun _ _ => by ring
  have hT : TpE M a = 2 * ∑ j ∈ range (a + 1), Bali.RE.ce (M + 1) a j * E (2 * M + 2) M j := by
    rw [TpE, sum_congr rfl fun k _ => hk k, sum_comm, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.1 hj
    rw [← Ij (2 * M + 2) M j (by omega) (by omega), hn, ← mul_sum, ← mul_sum]
  have hE0 : E (2 * M + 2) M 0 = (2 * (M : ℚ) + 2) * ((2 * M + 1).choose M : ℚ) := by
    unfold E
    rw [show 2 * M + 2 - 2 * 0 - 1 = 2 * M + 1 by omega, show M - 0 = M from rfl,
      show 2 * 0 = 0 from rfl, Nat.descFactorial_zero]
    push_cast; ring
  have hS := sum_congr (rfl : range (a + 1) = range (a + 1))
    (fun j hj => cE_even M a ha j (by have := mem_range.1 hj; omega))
  have hc := chu (2 * M + 2) a (by omega)
  rw [hT, hS, ← mul_sum, hE0]
  linear_combination (2 * ((2 * (M : ℚ) + 2) * ((2 * M + 1).choose M : ℚ))) * hc

end Bali.BP

#print axioms Bali.BP.chu
#print axioms Bali.BP.TpO_closed
#print axioms Bali.BP.TpE_closed
