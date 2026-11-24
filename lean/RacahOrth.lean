import Mathlib

/-!
# Orthogonality of the type B Racah polynomials (Bali lab, 2026-10-31)

`R_m(x) = ₄F₃(-m, m-n, -x, x-n; (1-n)/2, (1-n)/2, -n; 1)`, weight `w(x) = C(n,x)^2 (n-2x)` on `x = 0..H`, `n = 2H+1`.
Route: difference operator `L f(x) = B(x)(f(x+1)-f(x)) + D(x)(f(x-1)-f(x))`,
`B(x) = (x-n)^2 (x-H) / (2(2x-n))`, `D(x) = x^2 (x-H-1) / (2(2x-n))`.
1. `L φ_j = λ_j φ_j + ν_j φ_{j-1}` on the basis `φ_j(x) = (-x)_j (x-n)_j`;  2. hence `L R_m = λ_m R_m`, `λ_m = m(m-n)`;
3. `w(x) B(x) = w(x+1) D(x+1)`, `B(H) = 0`, `D(0) = 0` ⇒ `L` is symmetric;  4. distinct `λ` ⇒ orthogonality.
-/

open Finset

namespace Bali.Racah

def P (a : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => P a k * (a + k)

lemma P_succ' (a : ℚ) : ∀ k, P a (k + 1) = a * P (a + 1) k
  | 0 => by simp [P]
  | k + 1 => by
    rw [P, P_succ' a k, P]; push_cast; ring

lemma P_two (a : ℚ) (k : ℕ) : P a (k + 1 + 1) = a * (a + 1) * P (a + 2) k := by
  rw [P_succ', P_succ', show a + 1 + 1 = a + 2 by ring]; ring

lemma P_two' (a : ℚ) (k : ℕ) : P a (k + 1 + 1) = P a k * (a + k) * (a + k + 1) := by
  rw [P, P]; push_cast; ring

def phi (n : ℚ) (j : ℕ) (y : ℚ) : ℚ := P (-y) j * P (y - n) j
def Bc (n y : ℚ) : ℚ := (y - n) ^ 2 * (y - (n - 1) / 2) / (2 * (2 * y - n))
def Dc (n y : ℚ) : ℚ := y ^ 2 * (y - (n + 1) / 2) / (2 * (2 * y - n))
def lam (n : ℚ) (j : ℕ) : ℚ := j * (j - n)
def nu (n : ℚ) (j : ℕ) : ℚ := j * (n - 2 * j + 1) ^ 2 * (n - j + 1) / 4
def Lop (n : ℚ) (f : ℚ → ℚ) (y : ℚ) : ℚ := Bc n y * (f (y + 1) - f y) + Dc n y * (f (y - 1) - f y)

set_option maxRecDepth 20000 in
/-- Step 1: the operator on the basis. -/
lemma L_phi (n y : ℚ) (hy : 2 * y - n ≠ 0) (j : ℕ) :
    Lop n (phi n j) y = lam n j * phi n j y + nu n j * phi n (j - 1) y := by
  have hy' : y * 2 - n ≠ 0 := by intro h; apply hy; linarith
  have hP0 : ∀ a, P a 0 = 1 := fun _ => rfl
  rcases j with _ | _ | k
  · simp [Lop, phi, P, lam, nu]
  · simp only [Lop, phi, P, hP0, lam, nu, Bc, Dc]; push_cast; field_simp; ring
  · have e1 : P (-(y + 1)) (k + 1 + 1) = (-(y + 1)) * (-(y + 1) + 1) * P (-y + 1) k := by
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
    simp only [Lop, phi, show k + 1 + 1 - 1 = k + 1 from rfl]
    rw [e1, e2, e3, e4, e5, e6, e7, e8]
    simp only [Bc, Dc, lam, nu]
    generalize P (-y + 1) k = Q1
    generalize P (y - n + 1) k = Q2
    push_cast
    field_simp
    ring

def c (n : ℚ) (m : ℕ) : ℕ → ℚ
  | 0 => 1
  | j + 1 => c n m j * (((j : ℚ) - m) * ((m : ℚ) - n + j) / (((1 - n) / 2 + j) ^ 2 * (-n + j) * ((j : ℚ) + 1)))

def Rq (n : ℚ) (m : ℕ) (y : ℚ) : ℚ := ∑ j ∈ range (m + 1), c n m j * phi n j y

lemma c_nu (n : ℚ) (m j : ℕ) (h1 : (1 - n) / 2 + j ≠ 0) (h2 : -n + j ≠ 0) :
    c n m (j + 1) * nu n (j + 1) = c n m j * (lam n m - lam n j) := by
  have h1' : 1 - n + 2 * (j : ℚ) ≠ 0 := by intro h; apply h1; linear_combination h / 2
  have h1'' : 1 - n + (j : ℚ) * 2 ≠ 0 := by intro h; apply h1'; linarith
  rw [show (1 - n) / 2 + (j : ℚ) = (1 - n + 2 * j) / 2 by ring] at h1
  simp only [c, nu, lam]
  rw [show (1 - n) / 2 + (j : ℚ) = (1 - n + 2 * j) / 2 by ring]
  push_cast
  field_simp
  ring

/-- Step 2: `R_m` is an eigenfunction. -/
lemma L_R (n y : ℚ) (hy : 2 * y - n ≠ 0) (m : ℕ)
    (hden : ∀ j, j < m → (1 - n) / 2 + j ≠ 0 ∧ -n + j ≠ 0) :
    Lop n (Rq n m) y = lam n m * Rq n m y := by
  have lin : Lop n (Rq n m) y = ∑ j ∈ range (m + 1), c n m j * Lop n (phi n j) y := by
    simp only [Lop, Rq]
    rw [← sum_sub_distrib, ← sum_sub_distrib, mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  rw [lin]
  have h1 : ∀ j ∈ range (m + 1), c n m j * Lop n (phi n j) y
      = c n m j * lam n j * phi n j y + c n m j * nu n j * phi n (j - 1) y :=
    fun j _ => by rw [L_phi n y hy]; ring
  rw [sum_congr rfl h1, sum_add_distrib, sum_range_succ' (fun j => c n m j * nu n j * phi n (j - 1) y)]
  have h2 : ∀ j ∈ range m, c n m (j + 1) * nu n (j + 1) * phi n (j + 1 - 1) y
      = c n m j * (lam n m - lam n j) * phi n j y := fun j hj => by
    have := hden j (mem_range.1 hj)
    rw [c_nu n m j this.1 this.2, Nat.add_sub_cancel]
  rw [sum_congr rfl h2]
  have hnu0 : nu n 0 = 0 := by simp [nu]
  have hs : ∑ j ∈ range m, c n m j * lam n j * phi n j y
      + ∑ j ∈ range m, c n m j * (lam n m - lam n j) * phi n j y
      = ∑ j ∈ range m, lam n m * (c n m j * phi n j y) := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
  rw [hnu0, Rq, sum_range_succ, sum_range_succ, mul_add, mul_sum]
  simp only [mul_zero, zero_mul, add_zero]
  linear_combination hs

/-! Steps 3–4 for `n = 2H+1`, on the nodes `x = 0..H`. -/

def w (H x : ℕ) : ℚ := ((2 * H + 1).choose x : ℚ) ^ 2 * (2 * (H : ℚ) + 1 - 2 * x)

lemma two_ne (H : ℕ) (y : ℕ) : 2 * (y : ℚ) - (2 * H + 1) ≠ 0 := by
  intro h
  have : (2 * y : ℤ) = 2 * H + 1 := by exact_mod_cast (by linarith : (2 * (y : ℚ)) = 2 * H + 1)
  omega

lemma wB (H x : ℕ) (hx : x < H) :
    w H x * Bc (2 * H + 1) x = w H (x + 1) * Dc (2 * H + 1) ((x + 1 : ℕ) : ℚ) := by
  have hc := Nat.choose_succ_right_eq (2 * H + 1) x
  have hc' : ((2 * H + 1).choose (x + 1) : ℚ) = ((2 * H + 1).choose x : ℚ) * (2 * H + 1 - x) / (x + 1) := by
    have := congrArg (fun t : ℕ => (t : ℚ)) hc
    push_cast [Nat.cast_sub (by omega : x ≤ 2 * H + 1)] at this
    have hx1 : ((x : ℚ) + 1) ≠ 0 := by positivity
    field_simp; linarith
  have d0 := two_ne H x
  have d1 := two_ne H (x + 1)
  have hx1 : ((x : ℚ) + 1) ≠ 0 := by positivity
  simp only [w, Bc, Dc]
  rw [hc']
  push_cast at d1 ⊢
  field_simp
  ring

lemma B_H (H : ℕ) : Bc (2 * H + 1) H = 0 := by simp [Bc]
lemma D_0 (H : ℕ) : Dc (2 * H + 1) 0 = 0 := by simp [Dc]

/-- Step 3: symmetry of `L` for the weight `w` on `0..H`. -/
lemma symm (H : ℕ) (f g : ℚ → ℚ) :
    ∑ x ∈ range (H + 1), w H x * (Lop (2 * H + 1) f x * g x - f x * Lop (2 * H + 1) g x) = 0 := by
  set n : ℚ := 2 * H + 1
  let A : ℕ → ℚ := fun x => w H x * Bc n x * (f ((x : ℚ) + 1) * g x - f x * g ((x : ℚ) + 1))
  let A' : ℕ → ℚ := fun x => w H x * Dc n x * (f x * g ((x : ℚ) - 1) - f ((x : ℚ) - 1) * g x)
  have term : ∀ x ∈ range (H + 1), w H x * (Lop n f x * g x - f x * Lop n g x) = A x - A' x :=
    fun x _ => by simp only [Lop, A, A']; ring
  rw [sum_congr rfl term, sum_sub_distrib]
  have hA' : ∑ x ∈ range (H + 1), A' x = ∑ x ∈ range H, A x := by
    rw [sum_range_succ']
    have hD0 : Dc n 0 = 0 := D_0 H
    have h0 : A' 0 = 0 := by simp only [A', Nat.cast_zero, hD0]; ring
    rw [h0, add_zero]
    refine sum_congr rfl fun x hx => ?_
    have := wB H x (mem_range.1 hx)
    simp only [A, A']
    rw [← this]; push_cast; rw [add_sub_cancel_right]
  rw [hA', sum_range_succ]
  have hBH : Bc n H = 0 := B_H H
  have hH : A H = 0 := by simp only [A, hBH]; ring
  rw [hH]; ring

/-- **Orthogonality** of the type B Racah polynomials, `n = 2H+1`, `a ≠ b ≤ H`. -/
theorem orth (H a b : ℕ) (ha : a ≤ H) (hb : b ≤ H) (hab : a ≠ b) :
    ∑ x ∈ range (H + 1), w H x * Rq (2 * H + 1) a x * Rq (2 * H + 1) b x = 0 := by
  set n : ℚ := 2 * H + 1 with hn
  have hden : ∀ m, m ≤ H → ∀ j, j < m → (1 - n) / 2 + j ≠ 0 ∧ -n + j ≠ 0 := by
    intro m hm j hj
    have : (j : ℚ) < H := by exact_mod_cast (by omega : j < H)
    constructor <;> (intro h; rw [hn] at h; linarith)
  have eig : ∀ m, m ≤ H → ∀ x : ℕ, Lop n (Rq n m) x = lam n m * Rq n m x :=
    fun m hm x => L_R n x (two_ne H x) m (hden m hm)
  have hs := symm H (Rq n a) (Rq n b)
  have key : (lam n a - lam n b) * ∑ x ∈ range (H + 1), w H x * Rq n a x * Rq n b x = 0 := by
    rw [← hs, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [eig a ha x, eig b hb x]; ring
  have hl : lam n a - lam n b ≠ 0 := by
    simp only [lam, hn]
    have e : (a : ℚ) * (a - (2 * H + 1)) - b * (b - (2 * H + 1)) = (a - b) * (a + b - (2 * H + 1)) := by ring
    rw [e]
    apply mul_ne_zero
    · exact sub_ne_zero.mpr (by exact_mod_cast hab)
    · have : (a : ℚ) + b ≤ 2 * H := by exact_mod_cast (by omega : a + b ≤ 2 * H)
      intro h; linarith
  exact (mul_eq_zero.mp key).resolve_left hl

/-! ## Norms: `‖R_m‖² = n² C(n-1,H)² / ((n-2m) C(n,m)²)` -/

def dd (n : ℚ) (j : ℕ) : ℚ := P ((1 - n) / 2) j ^ 2 * P (-n) j * P 1 j

lemma P_neg_nat_zero (x : ℕ) : ∀ j, x < j → P (-(x : ℚ)) j = 0
  | 0, h => absurd h (Nat.not_lt_zero _)
  | j + 1, h => by
    rcases Nat.lt_or_ge x j with hj | hj
    · rw [P, P_neg_nat_zero x j hj, zero_mul]
    · have : j = x := by omega
      subst this; rw [P]; simp

lemma dd_ne (H : ℕ) : ∀ j, j ≤ H → dd (2 * H + 1) j ≠ 0
  | 0, _ => by simp [dd, P]
  | j + 1, hj => by
    have ih := dd_ne H j (by omega)
    simp only [dd] at ih ⊢
    have hA : P ((1 - (2 * (H : ℚ) + 1)) / 2) j ≠ 0 := fun h0 => ih (by rw [h0]; ring)
    have hB : P (-(2 * (H : ℚ) + 1)) j ≠ 0 := fun h0 => ih (by rw [h0]; ring)
    have hC : P 1 j ≠ 0 := fun h0 => ih (by rw [h0]; ring)
    have hjH : (j : ℚ) < H := by exact_mod_cast (by omega : j < H)
    have h1 : (1 - (2 * (H : ℚ) + 1)) / 2 + j ≠ 0 := by intro h; linarith
    have h2 : -(2 * (H : ℚ) + 1) + j ≠ 0 := by intro h; linarith
    have h3 : (1 : ℚ) + j ≠ 0 := by positivity
    simp only [P]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (mul_ne_zero hA h1)) (mul_ne_zero hB h2)) (mul_ne_zero hC h3)

lemma c_eq (H m : ℕ) : ∀ j, j ≤ H → c (2 * H + 1) m j = phi (2 * H + 1) j m / dd (2 * H + 1) j
  | 0, _ => by simp [c, phi, dd, P]
  | j + 1, hj => by
    have ih := c_eq H m j (by omega)
    have hd := dd_ne H j (by omega)
    rw [c, ih]
    simp only [dd] at hd
    have hA : P ((1 - (2 * (H : ℚ) + 1)) / 2) j ≠ 0 := fun h0 => hd (by rw [h0]; ring)
    have hB : P (-(2 * (H : ℚ) + 1)) j ≠ 0 := fun h0 => hd (by rw [h0]; ring)
    have hC : P 1 j ≠ 0 := fun h0 => hd (by rw [h0]; ring)
    have hjH : (j : ℚ) < H := by exact_mod_cast (by omega : j < H)
    have h1 : (1 - (2 * (H : ℚ) + 1)) / 2 + j ≠ 0 := by intro h; linarith
    have h2 : -(2 * (H : ℚ) + 1) + j ≠ 0 := by intro h; linarith
    have h3 : (j : ℚ) + 1 ≠ 0 := by positivity
    have h3' : (1 : ℚ) + j ≠ 0 := by positivity
    simp only [phi, dd, P]
    field_simp
    ring

/-- `R_m(y) = Σ_{j ≤ H} φ_j(m) φ_j(y) / dd_j`, symmetric in `m ↔ y`. -/
lemma Rq_full (H m : ℕ) (hm : m ≤ H) (y : ℚ) :
    Rq (2 * H + 1) m y = ∑ j ∈ range (H + 1),
      phi (2 * H + 1) j m * phi (2 * H + 1) j y / dd (2 * H + 1) j := by
  calc Rq (2 * H + 1) m y
      = ∑ j ∈ range (m + 1), phi (2 * H + 1) j m * phi (2 * H + 1) j y / dd (2 * H + 1) j := by
        refine sum_congr rfl fun j hj => ?_
        rw [c_eq H m j (by simp at hj; omega)]; ring
    _ = _ := by
        apply sum_subset (range_subset_range.2 (show m + 1 ≤ H + 1 by omega))
        intro j hj hj'
        simp only [mem_range, not_lt] at hj hj'
        simp [phi, P_neg_nat_zero m j (by omega)]

lemma sym (H m x : ℕ) (hm : m ≤ H) (hx : x ≤ H) :
    Rq (2 * H + 1) x (m : ℚ) = Rq (2 * H + 1) m (x : ℚ) := by
  rw [Rq_full H x hx, Rq_full H m hm]
  exact sum_congr rfl fun j _ => by ring

def ip (H : ℕ) (f g : ℕ → ℚ) : ℚ := ∑ x ∈ range (H + 1), w H x * f x * g x
def RR (H m : ℕ) : ℕ → ℚ := fun x => Rq (2 * H + 1) m x
def hN (H m : ℕ) : ℚ := ip H (RR H m) (RR H m)

lemma ip3 (H : ℕ) (a b d : ℚ) (f g k h : ℕ → ℚ) :
    ip H (fun x => a * f x + b * g x + d * k x) h = a * ip H f h + b * ip H g h + d * ip H k h := by
  simp only [ip, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun x _ => by ring

lemma ip_comm (H : ℕ) (f g : ℕ → ℚ) : ip H f g = ip H g f := by
  simp only [ip]; exact sum_congr rfl fun x _ => by ring

lemma ip_orth (H a b : ℕ) (ha : a ≤ H) (hb : b ≤ H) (hab : a ≠ b) : ip H (RR H a) (RR H b) = 0 := by
  have := orth H a b ha hb hab
  simpa [ip, RR, mul_assoc] using this

/-- the `m`-recurrence (unconverted neighbours), from the `x`-difference equation and self-duality. -/
lemma three_term (H m x : ℕ) (hm : m ≤ H) (hx : x ≤ H) :
    lam (2 * H + 1) x * RR H m x = Bc (2 * H + 1) m * Rq (2 * H + 1) x ((m : ℚ) + 1)
      + (-Bc (2 * H + 1) m - Dc (2 * H + 1) m) * RR H m x
      + Dc (2 * H + 1) m * Rq (2 * H + 1) x ((m : ℚ) - 1) := by
  have hden : ∀ j, j < x → (1 - (2 * (H : ℚ) + 1)) / 2 + j ≠ 0 ∧ -(2 * (H : ℚ) + 1) + j ≠ 0 := by
    intro j hj
    have : (j : ℚ) < H := by exact_mod_cast (by omega : j < H)
    constructor <;> (intro h; linarith)
  have e := L_R (2 * H + 1) m (two_ne H m) x hden
  simp only [Lop] at e
  have s0 := sym H m x hm hx
  simp only [RR]
  rw [← s0]
  linear_combination -e

lemma ip_up (H m : ℕ) (hm : m + 1 ≤ H) (g : ℕ → ℚ) :
    ip H (fun x => Rq (2 * H + 1) x ((m : ℚ) + 1)) g = ip H (RR H (m + 1)) g := by
  simp only [ip]; refine sum_congr rfl fun x hx => ?_
  have := sym H (m + 1) x hm (by simp at hx; omega)
  push_cast at this; simp only [RR]; rw [this]

lemma ip_down (H m : ℕ) (hpos : 1 ≤ m) (hm : m ≤ H) (g : ℕ → ℚ) :
    ip H (fun x => Rq (2 * H + 1) x ((m : ℚ) - 1)) g = ip H (RR H (m - 1)) g := by
  simp only [ip]; refine sum_congr rfl fun x hx => ?_
  have := sym H (m - 1) x (by omega) (by simp at hx; omega)
  rw [show ((m : ℚ) - 1) = ((m - 1 : ℕ) : ℚ) by rw [Nat.cast_sub hpos]; simp, this]; rfl

lemma Rq_zero (n y : ℚ) : Rq n 0 y = 1 := by simp [Rq, c, phi, P]

lemma lam_ip (H m x : ℕ) (hm : m ≤ H) :
    ip H (fun x => lam (2 * H + 1) x * RR H m x) = ip H (fun x => Bc (2 * H + 1) m * Rq (2 * H + 1) x ((m : ℚ) + 1)
      + (-Bc (2 * H + 1) m - Dc (2 * H + 1) m) * RR H m x
      + Dc (2 * H + 1) m * Rq (2 * H + 1) x ((m : ℚ) - 1)) := by
  funext g; simp only [ip]; refine sum_congr rfl fun x hx => ?_
  rw [three_term H m x hm (by simp at hx; omega)]

lemma norm_step (H m : ℕ) (hm : m + 1 ≤ H) :
    Bc (2 * H + 1) m * hN H (m + 1) = Dc (2 * H + 1) ((m + 1 : ℕ) : ℚ) * hN H m := by
  have w1 : ip H (fun x => lam (2 * H + 1) x * RR H m x) (RR H (m + 1)) = Bc (2 * H + 1) m * hN H (m + 1) := by
    rw [lam_ip H m 0 (by omega), ip3, ip_up H m hm, ip_orth H m (m + 1) (by omega) hm (by omega)]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      have : Dc (2 * H + 1) ((0 : ℕ) : ℚ) = 0 := by simp [Dc]
      rw [this]; simp [hN]
    · rw [ip_down H m hpos (by omega), ip_orth H (m - 1) (m + 1) (by omega) hm (by omega)]; simp [hN]
  have w2 : ip H (fun x => lam (2 * H + 1) x * RR H (m + 1) x) (RR H m)
      = Dc (2 * H + 1) ((m + 1 : ℕ) : ℚ) * hN H m := by
    rw [lam_ip H (m + 1) 0 hm, ip3, ip_down H (m + 1) (by omega) hm, Nat.add_sub_cancel,
      ip_orth H (m + 1) m hm (by omega) (by omega)]
    rcases Nat.lt_or_ge (m + 1) H with hlt | hge
    · rw [ip_up H (m + 1) hlt, ip_orth H (m + 1 + 1) m hlt (by omega) (by omega)]; simp [hN]
    · have hH : m + 1 = H := by omega
      have : Bc (2 * H + 1) ((m + 1 : ℕ) : ℚ) = 0 := by rw [hH]; exact B_H H
      rw [this]; simp [hN]
  have eq : ip H (fun x => lam (2 * H + 1) x * RR H m x) (RR H (m + 1))
      = ip H (fun x => lam (2 * H + 1) x * RR H (m + 1) x) (RR H m) := by
    simp only [ip]; exact sum_congr rfl fun x _ => by ring
  rw [← w1, ← w2, eq]

/-- `Σ_{x ≤ h} C(n,x)² (n-2x) = n C(n-1,h)²` for `n = 2H+1`, `h ≤ 2H`. -/
lemma w_sum (H : ℕ) : ∀ h, h ≤ 2 * H →
    ∑ x ∈ range (h + 1), w H x = (2 * (H : ℚ) + 1) * ((2 * H).choose h : ℚ) ^ 2
  | 0, _ => by simp [w]
  | h + 1, hh => by
    rw [sum_range_succ, w_sum H h (by omega)]
    have a := Nat.add_one_mul_choose_eq (2 * H) h
    have b := Nat.choose_succ_right_eq (2 * H) h
    have a' := congrArg (fun t : ℕ => (t : ℚ)) a
    have b' := congrArg (fun t : ℕ => (t : ℚ)) b
    push_cast [Nat.cast_sub (by omega : h ≤ 2 * H)] at a' b'
    have hh1 : ((h : ℚ) + 1) ≠ 0 := by positivity
    have e1 : ((2 * H + 1).choose (h + 1) : ℚ) = (2 * H + 1) * ((2 * H).choose h : ℚ) / (h + 1) := by
      field_simp; linarith
    have e2 : ((2 * H).choose (h + 1) : ℚ) = ((2 * H).choose h : ℚ) * (2 * H - h) / (h + 1) := by
      field_simp; linarith
    simp only [w]; rw [e1, e2]; push_cast
    field_simp; ring

lemma hN_zero (H : ℕ) : hN H 0 = (2 * (H : ℚ) + 1) * ((2 * H).choose H : ℚ) ^ 2 := by
  have := w_sum H H (by omega)
  simp only [hN, ip, RR, Rq_zero, mul_one]; exact this

/-- **Racah norms** (KLS (1.2.2) in our normalisation), `n = 2H+1`, `m ≤ H`. -/
theorem hN_closed (H : ℕ) : ∀ m, m ≤ H →
    hN H m = (2 * (H : ℚ) + 1) ^ 2 * ((2 * H).choose H : ℚ) ^ 2
      / ((2 * H + 1 - 2 * m) * ((2 * H + 1).choose m : ℚ) ^ 2)
  | 0, _ => by rw [hN_zero]; simp; field_simp
  | m + 1, hm => by
    have ih := hN_closed H m (by omega)
    have st := norm_step H m hm
    have hmH : (m : ℚ) + 1 ≤ H := by exact_mod_cast hm
    have hB : Bc (2 * H + 1) m ≠ 0 := by
      simp only [Bc]
      have h1 : ((m : ℚ) - (2 * H + 1)) ≠ 0 := by intro h; linarith
      have h2 : ((m : ℚ) - (2 * H + 1 - 1) / 2) ≠ 0 := by intro h; linarith
      have h3 : (2 * (2 * (m : ℚ) - (2 * H + 1))) ≠ 0 := by intro h; linarith
      exact div_ne_zero (mul_ne_zero (pow_ne_zero _ h1) h2) h3
    have hst : hN H (m + 1) = hN H m * (Dc (2 * H + 1) ((m + 1 : ℕ) : ℚ) / Bc (2 * H + 1) m) := by
      rw [eq_comm, mul_div_assoc', div_eq_iff hB, mul_comm (hN H m), ← st]; ring
    have d1 : (2 * (H : ℚ) + 1 - 2 * m) ≠ 0 := by intro h; linarith
    have d2 : (2 * (H : ℚ) + 1 - 2 * (m + 1)) ≠ 0 := by intro h; linarith
    have d3 : (2 * (H : ℚ) + 1 - m) ≠ 0 := by intro h; linarith
    have d4 : ((m : ℚ) - (2 * H + 1)) ≠ 0 := by intro h; linarith
    have d5 : ((m : ℚ) - H) ≠ 0 := by intro h; linarith
    have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
    have d6 : (2 * (m : ℚ) - 2 * H - 1) ≠ 0 := by intro h; linarith
    have d7 : (2 * (m : ℚ) + 1 - 2 * H) ≠ 0 := by intro h; linarith
    have bc : Bc (2 * H + 1) m = ((m : ℚ) - (2 * H + 1)) ^ 2 * ((m : ℚ) - H) / (2 * (2 * (m : ℚ) - 2 * H - 1)) := by
      simp only [Bc]; congr 1 <;> ring
    have dc : Dc (2 * H + 1) ((m + 1 : ℕ) : ℚ) = ((m : ℚ) + 1) ^ 2 * ((m : ℚ) - H) / (2 * (2 * (m : ℚ) + 1 - 2 * H)) := by
      simp only [Dc]; push_cast; congr 1 <;> ring
    have b := Nat.choose_succ_right_eq (2 * H + 1) m
    have b' := congrArg (fun t : ℕ => (t : ℚ)) b
    push_cast [Nat.cast_sub (by omega : m ≤ 2 * H + 1)] at b'
    have e : ((2 * H + 1).choose (m + 1) : ℚ) = ((2 * H + 1).choose m : ℚ) * (2 * H + 1 - m) / (m + 1) := by
      field_simp; linarith
    have hc : ((2 * H + 1).choose m : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    rw [hst, ih, bc, dc, e]
    push_cast
    field_simp
    ring

end Bali.Racah




#print axioms Bali.Racah.orth
#print axioms Bali.Racah.hN_closed
