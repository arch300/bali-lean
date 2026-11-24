import P699.RacahE

/-!
# Even `n = 2m`: orthogonality and norms of `R_a` (Bali lab, 2026-11-02)
Weight `w(x) = C(n,x)²(n-2x)` on `x = 0..m-1`.  The route of `RacahOrth`, with
`B(x) = (x-n)²(x-m+1)/(2(2x-n+1))`, `D(x) = x²(x-m-1)/(2(2x-n-1))`.
-/

open Finset

namespace Bali.REO
open Bali.Racah Bali.RE

def Be (m : ℕ) (y : ℚ) : ℚ := (y - 2 * m) ^ 2 * (y - m + 1) / (2 * (2 * y - 2 * m + 1))
def De (m : ℕ) (y : ℚ) : ℚ := y ^ 2 * (y - m - 1) / (2 * (2 * y - 2 * m - 1))
def nuE (m j : ℕ) : ℚ := -(((j : ℚ) - m) * ((j : ℚ) - 1 - m) * ((j : ℚ) - 1 - 2 * m) * j)
def Le (m : ℕ) (f : ℚ → ℚ) (y : ℚ) : ℚ := Be m y * (f (y + 1) - f y) + De m y * (f (y - 1) - f y)

set_option maxRecDepth 20000 in
lemma L_phi (m : ℕ) (y : ℚ) (h1 : 2 * y - 2 * m + 1 ≠ 0) (h2 : 2 * y - 2 * m - 1 ≠ 0) (j : ℕ) :
    Le m (phi (2 * (m : ℚ)) j) y = lam (2 * (m : ℚ)) j * phi (2 * (m : ℚ)) j y
      + nuE m j * phi (2 * (m : ℚ)) (j - 1) y := by
  have hP0 : ∀ a, P a 0 = 1 := fun _ => rfl
  rcases j with _ | _ | k
  · simp [Le, phi, P, lam, nuE]
  · have hu : 2 * (2 * y - 2 * (m : ℚ) + 1) ≠ 0 := mul_ne_zero two_ne_zero h1
    have hv : 2 * (2 * y - 2 * (m : ℚ) - 1) ≠ 0 := mul_ne_zero two_ne_zero h2
    simp only [Le, phi, P, hP0, lam, nuE, Be, De]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_add_div _ _ hu hv, div_eq_iff (mul_ne_zero hu hv)]
    push_cast; ring
  · set n : ℚ := 2 * (m : ℚ) with hn
    have e1 : P (-(y + 1)) (k + 1 + 1) = (-(y + 1)) * (-(y + 1) + 1) * P (-y + 1) k := by
      rw [P_two, show -(y + 1) + 2 = -y + 1 by ring]
    have e2 : P (y + 1 - n) (k + 1 + 1) = P (y - n + 1) k * (y - n + 1 + k) * (y - n + 1 + k + 1) := by
      rw [P_two', show y + 1 - n = y - n + 1 by ring]
    have e3 : P (-y) (k + 1 + 1) = -y * (P (-y + 1) k * (-y + 1 + k)) := by rw [P_succ', P]
    have e4 : P (y - n) (k + 1 + 1) = (y - n) * (P (y - n + 1) k * (y - n + 1 + k)) := by rw [P_succ', P]
    have e5 : P (-(y - 1)) (k + 1 + 1) = P (-y + 1) k * (-y + 1 + k) * (-y + 1 + k + 1) := by
      rw [P_two', show -(y - 1) = -y + 1 by ring]
    have e6 : P (y - 1 - n) (k + 1 + 1) = (y - 1 - n) * (y - 1 - n + 1) * P (y - n + 1) k := by
      rw [P_two, show y - 1 - n + 2 = y - n + 1 by ring]
    have e7 : P (-y) (k + 1) = -y * P (-y + 1) k := P_succ' _ _
    have e8 : P (y - n) (k + 1) = (y - n) * P (y - n + 1) k := P_succ' _ _
    simp only [Le, phi, show k + 1 + 1 - 1 = k + 1 from rfl]
    rw [e1, e2, e3, e4, e5, e6, e7, e8]
    simp only [Be, De, lam, nuE]
    generalize P (-y + 1) k = Q1
    generalize P (y - n + 1) k = Q2
    rw [hn] at h1 h2 ⊢
    have hu : 2 * (2 * y - 2 * (m : ℚ) + 1) ≠ 0 := mul_ne_zero two_ne_zero h1
    have hv : 2 * (2 * y - 2 * (m : ℚ) - 1) ≠ 0 := mul_ne_zero two_ne_zero h2
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_add_div _ _ hu hv, div_eq_iff (mul_ne_zero hu hv)]
    push_cast; ring

lemma c_nu (m a j : ℕ) (h1 : 1 - (m : ℚ) + j ≠ 0) (h2 : (j : ℚ) - m ≠ 0) (h3 : (j : ℚ) - 2 * m ≠ 0) :
    ce m a (j + 1) * nuE m (j + 1) = ce m a j * (lam (2 * (m : ℚ)) a - lam (2 * (m : ℚ)) j) := by
  have h4 : (j : ℚ) + 1 ≠ 0 := by positivity
  simp only [ce, nuE, lam]
  push_cast
  rw [show (j : ℚ) + 1 - 1 - m = (j : ℚ) - m by ring, show (j : ℚ) + 1 - 1 - 2 * m = (j : ℚ) - 2 * m by ring,
    show (j : ℚ) + 1 - m = 1 - (m : ℚ) + j by ring]
  field_simp
  ring

lemma L_R (m : ℕ) (y : ℚ) (h1 : 2 * y - 2 * m + 1 ≠ 0) (h2 : 2 * y - 2 * m - 1 ≠ 0) (a : ℕ) (ha : a < m) :
    Le m (RE m a) y = lam (2 * (m : ℚ)) a * RE m a y := by
  have hden : ∀ j, j < a → 1 - (m : ℚ) + j ≠ 0 ∧ (j : ℚ) - m ≠ 0 ∧ (j : ℚ) - 2 * m ≠ 0 := by
    intro j hj
    have : (j : ℚ) + 2 ≤ m := by exact_mod_cast (by omega : j + 2 ≤ m)
    have h0 : (0 : ℚ) ≤ j := by positivity
    refine ⟨?_, ?_, ?_⟩ <;> (intro h; linarith)
  have lin : Le m (RE m a) y = ∑ j ∈ range (a + 1), ce m a j * Le m (phi (2 * (m : ℚ)) j) y := by
    simp only [Le, RE]
    rw [← sum_sub_distrib, ← sum_sub_distrib, mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  rw [lin]
  have h1' : ∀ j ∈ range (a + 1), ce m a j * Le m (phi (2 * (m : ℚ)) j) y
      = ce m a j * lam (2 * (m : ℚ)) j * phi (2 * (m : ℚ)) j y
        + ce m a j * nuE m j * phi (2 * (m : ℚ)) (j - 1) y :=
    fun j _ => by rw [L_phi m y h1 h2]; ring
  rw [sum_congr rfl h1', sum_add_distrib, sum_range_succ' (fun j => ce m a j * nuE m j * phi (2 * (m : ℚ)) (j - 1) y)]
  have h2' : ∀ j ∈ range a, ce m a (j + 1) * nuE m (j + 1) * phi (2 * (m : ℚ)) (j + 1 - 1) y
      = ce m a j * (lam (2 * (m : ℚ)) a - lam (2 * (m : ℚ)) j) * phi (2 * (m : ℚ)) j y := fun j hj => by
    obtain ⟨d1, d2, d3⟩ := hden j (mem_range.1 hj)
    rw [c_nu m a j d1 d2 d3, Nat.add_sub_cancel]
  rw [sum_congr rfl h2']
  have hnu0 : nuE m 0 = 0 := by simp [nuE]
  have hs : ∑ j ∈ range a, ce m a j * lam (2 * (m : ℚ)) j * phi (2 * (m : ℚ)) j y
      + ∑ j ∈ range a, ce m a j * (lam (2 * (m : ℚ)) a - lam (2 * (m : ℚ)) j) * phi (2 * (m : ℚ)) j y
      = ∑ j ∈ range a, lam (2 * (m : ℚ)) a * (ce m a j * phi (2 * (m : ℚ)) j y) := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
  rw [hnu0, RE, sum_range_succ, sum_range_succ, mul_add, mul_sum]
  simp only [mul_zero, zero_mul, add_zero]
  linear_combination hs

/-! weight and symmetry -/

def wE (m x : ℕ) : ℚ := ((2 * m).choose x : ℚ) ^ 2 * (2 * (m : ℚ) - 2 * x)

lemma odd_ne (m y : ℕ) : 2 * (y : ℚ) - 2 * m + 1 ≠ 0 := by
  intro h
  have : (2 * y + 1 : ℤ) = 2 * m := by exact_mod_cast (by linarith : (2 * (y : ℚ)) + 1 = 2 * m)
  omega

lemma odd_ne' (m y : ℕ) : 2 * (y : ℚ) - 2 * m - 1 ≠ 0 := by
  intro h
  have : (2 * y : ℤ) = 2 * m + 1 := by exact_mod_cast (by linarith : (2 * (y : ℚ)) = 2 * m + 1)
  omega

lemma wB (m x : ℕ) (hx : x < 2 * m) :
    wE m x * Be m x = wE m (x + 1) * De m ((x + 1 : ℕ) : ℚ) := by
  have hc := Nat.choose_succ_right_eq (2 * m) x
  have hx1 : ((x : ℚ) + 1) ≠ 0 := by positivity
  have hc' : ((2 * m).choose (x + 1) : ℚ) = ((2 * m).choose x : ℚ) * (2 * m - x) / (x + 1) := by
    have := congrArg (fun t : ℕ => (t : ℚ)) hc
    push_cast [Nat.cast_sub (by omega : x ≤ 2 * m)] at this
    field_simp; linarith
  have d0 := odd_ne m x
  simp only [wE, Be, De]
  rw [hc']
  push_cast
  rw [show 2 * ((x : ℚ) + 1) - 2 * m - 1 = 2 * (x : ℚ) - 2 * m + 1 by ring]
  field_simp
  ring

lemma symm (M : ℕ) (f g : ℚ → ℚ) :
    ∑ x ∈ range (M + 1), wE (M + 1) x * (Le (M + 1) f x * g x - f x * Le (M + 1) g x) = 0 := by
  let A : ℕ → ℚ := fun x => wE (M + 1) x * Be (M + 1) x * (f ((x : ℚ) + 1) * g x - f x * g ((x : ℚ) + 1))
  let A' : ℕ → ℚ := fun x => wE (M + 1) x * De (M + 1) x * (f x * g ((x : ℚ) - 1) - f ((x : ℚ) - 1) * g x)
  have term : ∀ x ∈ range (M + 1), wE (M + 1) x * (Le (M + 1) f x * g x - f x * Le (M + 1) g x) = A x - A' x :=
    fun x _ => by simp only [Le, A, A']; ring
  rw [sum_congr rfl term, sum_sub_distrib]
  have hA' : ∑ x ∈ range (M + 1), A' x = ∑ x ∈ range M, A x := by
    rw [sum_range_succ']
    have h0 : A' 0 = 0 := by simp [A', De]
    rw [h0, add_zero]
    refine sum_congr rfl fun x hx => ?_
    have := wB (M + 1) x (by have := mem_range.1 hx; omega)
    simp only [A, A']
    rw [← this]; push_cast; rw [add_sub_cancel_right]
  rw [hA', sum_range_succ]
  have hH : A M = 0 := by
    have : Be (M + 1) (M : ℚ) = 0 := by simp only [Be]; push_cast; rw [show (M : ℚ) - (M + 1) + 1 = 0 by ring]; simp
    simp only [A, this]; ring
  rw [hH]; ring

/-- **Orthogonality.** -/
theorem orth (M a b : ℕ) (ha : a < M + 1) (hb : b < M + 1) (hab : a ≠ b) :
    ∑ x ∈ range (M + 1), wE (M + 1) x * RE (M + 1) a x * RE (M + 1) b x = 0 := by
  set n : ℚ := 2 * ((M + 1 : ℕ) : ℚ) with hn
  have eig : ∀ c, c < M + 1 → ∀ x : ℕ, Le (M + 1) (RE (M + 1) c) x = lam n c * RE (M + 1) c x :=
    fun c hc x => L_R (M + 1) x (odd_ne _ x) (odd_ne' _ x) c hc
  have hs := symm M (RE (M + 1) a) (RE (M + 1) b)
  have key : (lam n a - lam n b) * ∑ x ∈ range (M + 1), wE (M + 1) x * RE (M + 1) a x * RE (M + 1) b x = 0 := by
    rw [← hs, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [eig a ha x, eig b hb x]; ring
  have hl : lam n a - lam n b ≠ 0 := by
    simp only [lam, hn]
    have e : (a : ℚ) * (a - 2 * ((M + 1 : ℕ) : ℚ)) - b * (b - 2 * ((M + 1 : ℕ) : ℚ))
        = (a - b) * (a + b - 2 * ((M + 1 : ℕ) : ℚ)) := by ring
    rw [e]
    apply mul_ne_zero
    · exact sub_ne_zero.mpr (by exact_mod_cast hab)
    · have : (a : ℚ) + b + 1 ≤ 2 * ((M + 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : a + b + 1 ≤ 2 * (M + 1))
      intro h; linarith
  exact (mul_eq_zero.mp key).resolve_left hl

/-! duality -/

def dd (m j : ℕ) : ℚ := P (1 - (m : ℚ)) j * P (-(m : ℚ)) j * P (-(2 * (m : ℚ))) j * P 1 j

lemma dd_ne (m : ℕ) : ∀ j, j < m → dd m j ≠ 0
  | 0, _ => by simp [dd, P]
  | j + 1, hj => by
    have ih := dd_ne m j (by omega)
    simp only [dd] at ih ⊢
    have hA : P (1 - (m : ℚ)) j ≠ 0 := fun h0 => ih (by rw [h0]; ring)
    have hA' : P (-(m : ℚ)) j ≠ 0 := fun h0 => ih (by rw [h0]; ring)
    have hB : P (-(2 * (m : ℚ))) j ≠ 0 := fun h0 => ih (by rw [h0]; ring)
    have hC : P 1 j ≠ 0 := fun h0 => ih (by rw [h0]; ring)
    have hj' : (j : ℚ) + 2 ≤ m := by exact_mod_cast (by omega : j + 2 ≤ m)
    have h0 : (0 : ℚ) ≤ j := by positivity
    have h1 : 1 - (m : ℚ) + j ≠ 0 := by intro h; linarith
    have h1' : -(m : ℚ) + j ≠ 0 := by intro h; linarith
    have h2 : -(2 * (m : ℚ)) + j ≠ 0 := by intro h; linarith
    have h3 : (1 : ℚ) + j ≠ 0 := by positivity
    simp only [P]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hA h1) (mul_ne_zero hA' h1')) (mul_ne_zero hB h2)) (mul_ne_zero hC h3)

lemma ce_eq (m a : ℕ) : ∀ j, j < m → ce m a j = phi (2 * (m : ℚ)) j a / dd m j
  | 0, _ => by simp [ce, phi, dd, P]
  | j + 1, hj => by
    have ih := ce_eq m a j (by omega)
    have hd := dd_ne m j (by omega)
    rw [ce, ih]
    simp only [dd] at hd
    have hA : P (1 - (m : ℚ)) j ≠ 0 := fun h0 => hd (by rw [h0]; ring)
    have hA' : P (-(m : ℚ)) j ≠ 0 := fun h0 => hd (by rw [h0]; ring)
    have hB : P (-(2 * (m : ℚ))) j ≠ 0 := fun h0 => hd (by rw [h0]; ring)
    have hC : P 1 j ≠ 0 := fun h0 => hd (by rw [h0]; ring)
    have hj' : (j : ℚ) + 2 ≤ m := by exact_mod_cast (by omega : j + 2 ≤ m)
    have h0 : (0 : ℚ) ≤ j := by positivity
    have h1 : 1 - (m : ℚ) + j ≠ 0 := by intro h; linarith
    have h1' : (j : ℚ) - m ≠ 0 := by intro h; linarith
    have h1'' : -(m : ℚ) + j ≠ 0 := by intro h; linarith
    have h2 : (j : ℚ) - 2 * m ≠ 0 := by intro h; linarith
    have h2' : -(2 * (m : ℚ)) + j ≠ 0 := by intro h; linarith
    have h3 : (j : ℚ) + 1 ≠ 0 := by positivity
    have h3' : (1 : ℚ) + j ≠ 0 := by positivity
    simp only [phi, dd, P]
    field_simp
    ring

lemma RE_full (m a : ℕ) (ha : a < m) (y : ℚ) :
    RE m a y = ∑ j ∈ range m, phi (2 * (m : ℚ)) j a * phi (2 * (m : ℚ)) j y / dd m j := by
  calc RE m a y
      = ∑ j ∈ range (a + 1), phi (2 * (m : ℚ)) j a * phi (2 * (m : ℚ)) j y / dd m j := by
        refine sum_congr rfl fun j hj => ?_
        rw [ce_eq m a j (by have := mem_range.1 hj; omega)]; ring
    _ = _ := by
        apply sum_subset (range_subset_range.2 (show a + 1 ≤ m by omega))
        intro j hj hj'
        simp only [mem_range, not_lt] at hj hj'
        simp [phi, P_neg_nat_zero a j (by omega)]

lemma sym (m a x : ℕ) (ha : a < m) (hx : x < m) : RE m x (a : ℚ) = RE m a (x : ℚ) := by
  rw [RE_full m x hx, RE_full m a ha]
  exact sum_congr rfl fun j _ => by ring

/-! norms -/

def ipE (m : ℕ) (f g : ℕ → ℚ) : ℚ := ∑ x ∈ range m, wE m x * f x * g x
def RR (m a : ℕ) : ℕ → ℚ := fun x => RE m a x
/-- the norm `h_a`. -/
def hE (m a : ℕ) : ℚ := ipE m (RR m a) (RR m a)

lemma ip3 (m : ℕ) (a b d : ℚ) (f g k h : ℕ → ℚ) :
    ipE m (fun x => a * f x + b * g x + d * k x) h = a * ipE m f h + b * ipE m g h + d * ipE m k h := by
  simp only [ipE, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun x _ => by ring

lemma ip_orth (M a b : ℕ) (ha : a < M + 1) (hb : b < M + 1) (hab : a ≠ b) :
    ipE (M + 1) (RR (M + 1) a) (RR (M + 1) b) = 0 := by
  simpa [ipE, RR, mul_assoc] using orth M a b ha hb hab

lemma three_term (m a x : ℕ) (ha : a < m) (hx : x < m) :
    lam (2 * (m : ℚ)) x * RR m a x = Be m a * RE m x ((a : ℚ) + 1)
      + (-Be m a - De m a) * RR m a x + De m a * RE m x ((a : ℚ) - 1) := by
  have e := L_R m a (odd_ne m a) (odd_ne' m a) x hx
  simp only [Le] at e
  have s0 := sym m a x ha hx
  simp only [RR]
  rw [← s0]
  linear_combination -e

lemma ip_up (m a : ℕ) (ha : a + 1 < m) (g : ℕ → ℚ) :
    ipE m (fun x => RE m x ((a : ℚ) + 1)) g = ipE m (RR m (a + 1)) g := by
  simp only [ipE]; refine sum_congr rfl fun x hx => ?_
  have := sym m (a + 1) x ha (mem_range.1 hx)
  push_cast at this; simp only [RR]; rw [this]

lemma ip_down (m a : ℕ) (hpos : 1 ≤ a) (ha : a < m) (g : ℕ → ℚ) :
    ipE m (fun x => RE m x ((a : ℚ) - 1)) g = ipE m (RR m (a - 1)) g := by
  simp only [ipE]; refine sum_congr rfl fun x hx => ?_
  have := sym m (a - 1) x (by omega) (mem_range.1 hx)
  rw [show ((a : ℚ) - 1) = ((a - 1 : ℕ) : ℚ) by rw [Nat.cast_sub hpos]; simp, this]; rfl

lemma lam_ip (m a : ℕ) (ha : a < m) :
    ipE m (fun x => lam (2 * (m : ℚ)) x * RR m a x) = ipE m (fun x => Be m a * RE m x ((a : ℚ) + 1)
      + (-Be m a - De m a) * RR m a x + De m a * RE m x ((a : ℚ) - 1)) := by
  funext g; simp only [ipE]; refine sum_congr rfl fun x hx => ?_
  rw [three_term m a x ha (mem_range.1 hx)]

lemma norm_step (M a : ℕ) (ha : a + 1 < M + 1) :
    Be (M + 1) a * hE (M + 1) (a + 1) = De (M + 1) ((a + 1 : ℕ) : ℚ) * hE (M + 1) a := by
  have w1 : ipE (M + 1) (fun x => lam (2 * ((M + 1 : ℕ) : ℚ)) x * RR (M + 1) a x) (RR (M + 1) (a + 1))
      = Be (M + 1) a * hE (M + 1) (a + 1) := by
    rw [lam_ip (M + 1) a (by omega), ip3, ip_up (M + 1) a ha, ip_orth M a (a + 1) (by omega) ha (by omega)]
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      have : De (M + 1) ((0 : ℕ) : ℚ) = 0 := by simp [De]
      rw [this]; simp [hE]
    · rw [ip_down (M + 1) a hpos (by omega), ip_orth M (a - 1) (a + 1) (by omega) ha (by omega)]; simp [hE]
  have w2 : ipE (M + 1) (fun x => lam (2 * ((M + 1 : ℕ) : ℚ)) x * RR (M + 1) (a + 1) x) (RR (M + 1) a)
      = De (M + 1) ((a + 1 : ℕ) : ℚ) * hE (M + 1) a := by
    rw [lam_ip (M + 1) (a + 1) ha, ip3, ip_down (M + 1) (a + 1) (by omega) ha, Nat.add_sub_cancel,
      ip_orth M (a + 1) a ha (by omega) (by omega)]
    rcases Nat.lt_or_ge (a + 1 + 1) (M + 1) with hlt | hge
    · have := ip_up (M + 1) (a + 1) hlt (RR (M + 1) a)
      rw [this, ip_orth M (a + 1 + 1) a hlt (by omega) (by omega)]; simp [hE]
    · have hH : a + 1 = M := by omega
      have : Be (M + 1) ((a + 1 : ℕ) : ℚ) = 0 := by
        rw [hH]; simp only [Be]; push_cast; rw [show (M : ℚ) - (M + 1) + 1 = 0 by ring]; simp
      rw [this]; simp [hE]
  have eq : ipE (M + 1) (fun x => lam (2 * ((M + 1 : ℕ) : ℚ)) x * RR (M + 1) a x) (RR (M + 1) (a + 1))
      = ipE (M + 1) (fun x => lam (2 * ((M + 1 : ℕ) : ℚ)) x * RR (M + 1) (a + 1) x) (RR (M + 1) a) := by
    simp only [ipE]; exact sum_congr rfl fun x _ => by ring
  rw [← w1, ← w2, eq]

/-- `Σ_{x ≤ h} C(N+1,x)²(N+1-2x) = (N+1) C(N,h)²`. -/
lemma w_sum (N : ℕ) : ∀ h, h ≤ N →
    ∑ x ∈ range (h + 1), ((N + 1).choose x : ℚ) ^ 2 * ((N : ℚ) + 1 - 2 * x) = ((N : ℚ) + 1) * (N.choose h : ℚ) ^ 2
  | 0, _ => by simp
  | h + 1, hh => by
    rw [sum_range_succ, w_sum N h (by omega)]
    have a := Nat.add_one_mul_choose_eq N h
    have b := Nat.choose_succ_right_eq N h
    have a' := congrArg (fun t : ℕ => (t : ℚ)) a
    have b' := congrArg (fun t : ℕ => (t : ℚ)) b
    push_cast [Nat.cast_sub (by omega : h ≤ N)] at a' b'
    have hh1 : ((h : ℚ) + 1) ≠ 0 := by positivity
    have e1 : ((N + 1).choose (h + 1) : ℚ) = ((N : ℚ) + 1) * (N.choose h : ℚ) / (h + 1) := by
      field_simp; linarith
    have e2 : (N.choose (h + 1) : ℚ) = (N.choose h : ℚ) * ((N : ℚ) - h) / (h + 1) := by
      field_simp; linarith
    rw [e1, e2]; push_cast
    field_simp; ring

lemma RE_zero (m : ℕ) (y : ℚ) : RE m 0 y = 1 := by simp [RE, ce, phi, P]

lemma hE_zero (M : ℕ) : hE (M + 1) 0 = (2 * ((M + 1 : ℕ) : ℚ)) * ((2 * M + 1).choose M : ℚ) ^ 2 := by
  have := w_sum (2 * M + 1) M (by omega)
  simp only [hE, ipE, RR, RE_zero, mul_one, wE]
  rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring]
  push_cast at this ⊢
  rw [show 2 * ((M : ℚ) + 1) = 2 * (M : ℚ) + 1 + 1 by ring]
  exact this

/-- **Norms.** `h_a (n-2a) C(n,a)² = n² C(n-1,m-1)²`, `n = 2m`, `a < m`. -/
theorem hE_closed (M : ℕ) : ∀ a, a < M + 1 →
    hE (M + 1) a * ((2 * ((M + 1 : ℕ) : ℚ) - 2 * a) * ((2 * (M + 1)).choose a : ℚ) ^ 2)
      = (2 * ((M + 1 : ℕ) : ℚ)) ^ 2 * ((2 * M + 1).choose M : ℚ) ^ 2
  | 0, _ => by
    rw [hE_zero]; simp; ring
  | a + 1, ha => by
    have ih := hE_closed M a (by omega)
    have st := norm_step M a ha
    have hA : (a : ℚ) + 2 ≤ (M : ℚ) + 1 := by exact_mod_cast (by omega : a + 2 ≤ M + 1)
    have h0 : (0 : ℚ) ≤ a := by positivity
    have d0 := odd_ne (M + 1) a
    have d1 : (a : ℚ) - 2 * ((M + 1 : ℕ) : ℚ) ≠ 0 := by push_cast; intro h; linarith
    have d2 : (a : ℚ) - ((M + 1 : ℕ) : ℚ) + 1 ≠ 0 := by push_cast; intro h; linarith
    have hm1 : (a : ℚ) + 1 ≠ 0 := by positivity
    have st' : ((a : ℚ) - 2 * ((M + 1 : ℕ) : ℚ)) ^ 2 * ((a : ℚ) - ((M + 1 : ℕ) : ℚ) + 1) * hE (M + 1) (a + 1)
        = ((a : ℚ) + 1) ^ 2 * ((a : ℚ) - ((M + 1 : ℕ) : ℚ) - 0) * hE (M + 1) a := by
      simp only [Be, De] at st
      push_cast at st d0 ⊢
      rw [show 2 * ((a : ℚ) + 1) - 2 * ((M : ℚ) + 1) - 1 = 2 * (a : ℚ) - 2 * ((M : ℚ) + 1) + 1 by ring,
        show (a : ℚ) + 1 - ((M : ℚ) + 1) - 1 = (a : ℚ) - ((M : ℚ) + 1) by ring] at st
      field_simp at st
      have hD : 2 * ((a : ℚ) - ((M : ℚ) + 1)) + 1 ≠ 0 := by intro h; apply d0; linarith
      have st2 := (div_left_inj' hD).1 st
      linear_combination st2
    have key : (((2 * (M + 1)).choose (a + 1) : ℕ) : ℚ) * ((a : ℚ) + 1)
        = ((2 * (M + 1)).choose a : ℚ) * (2 * ((M + 1 : ℕ) : ℚ) - a) := by
      have := Nat.choose_succ_right_eq (2 * (M + 1)) a
      have hc : ((2 * (M + 1) - a : ℕ) : ℚ) = 2 * ((M + 1 : ℕ) : ℚ) - a := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [← hc]; exact_mod_cast this
    rw [← ih]
    apply mul_left_cancel₀ (pow_ne_zero 2 hm1)
    push_cast at key st' ⊢
    linear_combination hE (M + 1) (a + 1) * (2 * (2 * ((M : ℚ) + 1) - 2 * ((a : ℚ) + 1)) / 2) *
        (((2 * (M + 1)).choose (a + 1) : ℚ) * ((a : ℚ) + 1) + ((2 * (M + 1)).choose a : ℚ) * (2 * ((M : ℚ) + 1) - a)) * key
      - 2 * ((2 * (M + 1)).choose a : ℚ) ^ 2 * st'
end Bali.REO

#print axioms Bali.REO.orth
#print axioms Bali.REO.hE_closed
