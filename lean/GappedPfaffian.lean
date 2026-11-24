import Mathlib
import P699.ZonoK
import P699.Pfaffian
import P699.ConjB
import P699.EvenConj
import P699.PfaffianPerm
import P699.ShellX
import P699.VB
import P699.OddB
import P699.Unified

/-!
# Kernel vectors and shifted Pfaffian windows of a skew Gram matrix of Krawtchouk polynomials

Formal companion of the paper of that title (M. Bali, 2026). The file covers all numbered
lemmas and theorems of the paper (Stages 1–6), Cases A–D of the corollary (Stage 7), the
bordered Pfaffian (Stage 8) and the de Bruijn identities with the corollary for `d ≤ m+1`
(Stage 9). Namespaces: `Bali.GP`, `Bali.PfB`, `Bali.GPdB`. It imports the modules
`P699.ZonoK … P699.Unified` of the same project (earlier formalisation of the type B sums).

Stage 1 (this block): Lemmas 3.1–3.2 of the paper, `eq:spec`, central values.
`K_h(x;n) = [z^h] (1-z)^x (1+z)^(n-x)`, `S(h,h') = sgn((h'-h)(h'+h-n))`,
`Ê(x,y) = Σ_{h,h'=0}^{n} K_h(x;n) K_{h'}(y;n) S(h,h')`.

For `n = N + 2`, `x, y ≤ N`:
`Ê(x+2,y) - Ê(x,y+2) = -4 Σ_{i,j=0}^{N} K_i(x;N) K_j(y;N) δ(j-i) δ(i+j-N)`,
`δ(0) = 2, δ(±1) = 1, δ(t) = 0` otherwise.
-/

open Finset Polynomial

namespace Bali.GP

/-- generating function of `K_·(x;n)`: `(1-z)^x (1+z)^(n-x)`. -/
noncomputable def gf (n x : ℕ) : ℚ[X] := (1 - X) ^ x * (1 + X) ^ (n - x)

/-- `S(h,h') = sgn((h'-h)(h'+h-n))`. -/
def S (n h h' : ℕ) : ℤ := Int.sign (((h' : ℤ) - h) * ((h' : ℤ) + h - n))

/-- `δ(0) = 2, δ(±1) = 1, else 0`. -/
def dl (t : ℤ) : ℤ := if t = 0 then 2 else if t = 1 ∨ t = -1 then 1 else 0

/-- `Ê(F,G) = Σ_h F_h Σ_{h'} G_{h'} S(h,h')`, bilinear form on coefficient vectors. -/
noncomputable def Ehat (n : ℕ) (F G : ℚ[X]) : ℚ :=
  ∑ h ∈ range (n + 1), F.coeff h * ∑ h' ∈ range (n + 1), G.coeff h' * (S n h h' : ℚ)

lemma sign_diff (t : ℤ) : Int.sign (t + 1) - Int.sign (t - 1) = dl t := by
  unfold dl
  rcases (by omega : t ≤ -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ 2 ≤ t) with h | h | h | h | h
  · rw [Int.sign_eq_neg_one_of_neg (by omega), Int.sign_eq_neg_one_of_neg (by omega)]
    rw [if_neg (by omega), if_neg (by omega)]; norm_num
  · subst h; norm_num
  · subst h; norm_num
  · subst h; norm_num
  · rw [Int.sign_eq_one_of_pos (by omega), Int.sign_eq_one_of_pos (by omega)]
    rw [if_neg (by omega), if_neg (by omega)]; norm_num

/-- the four-sign identity behind `M = -4 δ(P) δ(Q')`. -/
theorem four_sign (P Q : ℤ) :
    Int.sign (P + 1) * Int.sign (Q - 1) - Int.sign (P - 1) * Int.sign (Q - 1)
      - Int.sign (P + 1) * Int.sign (Q + 1) + Int.sign (P - 1) * Int.sign (Q + 1)
      = -(dl P * dl Q) := by
  have h1 := sign_diff P
  have h2 := sign_diff Q
  have : Int.sign (Q - 1) - Int.sign (Q + 1) = -dl Q := by linarith
  calc _ = (Int.sign (P + 1) - Int.sign (P - 1)) * (Int.sign (Q - 1) - Int.sign (Q + 1)) := by ring
    _ = _ := by rw [h1, this]; ring

lemma S_shift (N i j e f : ℕ) :
    S (N + 2) (i + e) (j + f)
      = Int.sign (((j : ℤ) - i) + f - e) * Int.sign (((i : ℤ) + j - N) + e + f - 2) := by
  unfold S; rw [Int.sign_mul]; congr 2 <;> push_cast <;> ring

/-- the kernel `M(i,j)` equals `-4 δ(j-i) δ(i+j-N)`. -/
theorem M_eq (N i j : ℕ) :
    4 * ((S (N + 2) i (j + 1) : ℚ) - S (N + 2) (i + 1) j - S (N + 2) (i + 1) (j + 2)
      + S (N + 2) (i + 2) (j + 1))
      = -4 * ((dl ((j : ℤ) - i) * dl ((i : ℤ) + j - N) : ℤ) : ℚ) := by
  have e1 : S (N + 2) i (j + 1) = S (N + 2) (i + 0) (j + 1) := rfl
  have e2 : S (N + 2) (i + 1) j = S (N + 2) (i + 1) (j + 0) := rfl
  rw [e1, e2, S_shift, S_shift, S_shift, S_shift]
  have := four_sign ((j : ℤ) - i) ((i : ℤ) + j - N)
  have key : Int.sign ((j : ℤ) - i + ((1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
        * Int.sign ((i : ℤ) + j - N + ((0 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) - 2)
      - Int.sign ((j : ℤ) - i + ((0 : ℕ) : ℤ) - ((1 : ℕ) : ℤ))
        * Int.sign ((i : ℤ) + j - N + ((1 : ℕ) : ℤ) + ((0 : ℕ) : ℤ) - 2)
      - Int.sign ((j : ℤ) - i + ((2 : ℕ) : ℤ) - ((1 : ℕ) : ℤ))
        * Int.sign ((i : ℤ) + j - N + ((1 : ℕ) : ℤ) + ((2 : ℕ) : ℤ) - 2)
      + Int.sign ((j : ℤ) - i + ((1 : ℕ) : ℤ) - ((2 : ℕ) : ℤ))
        * Int.sign ((i : ℤ) + j - N + ((2 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) - 2)
      = -(dl ((j : ℤ) - i) * dl ((i : ℤ) + j - N)) := by
    push_cast
    have a1 : (j : ℤ) - i + 1 - 0 = (j : ℤ) - i + 1 := by ring
    have a2 : (i : ℤ) + j - N + 0 + 1 - 2 = (i : ℤ) + j - N - 1 := by ring
    have a3 : (j : ℤ) - i + 0 - 1 = (j : ℤ) - i - 1 := by ring
    have a4 : (i : ℤ) + j - N + 1 + 0 - 2 = (i : ℤ) + j - N - 1 := by ring
    have a5 : (j : ℤ) - i + 2 - 1 = (j : ℤ) - i + 1 := by ring
    have a6 : (i : ℤ) + j - N + 1 + 2 - 2 = (i : ℤ) + j - N + 1 := by ring
    have a7 : (j : ℤ) - i + 1 - 2 = (j : ℤ) - i - 1 := by ring
    have a8 : (i : ℤ) + j - N + 2 + 1 - 2 = (i : ℤ) + j - N + 1 := by ring
    rw [a1, a2, a3, a4, a5, a6, a7, a8]; exact this
  have kq := congrArg (fun z : ℤ => (z : ℚ)) key
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg] at kq ⊢
  linear_combination 4 * kq

/-- push a polynomial factor of degree ≤ 2 through a weighted coefficient sum. -/
theorem sum_mul_coeff (N : ℕ) (A F : ℚ[X]) (hA : A.natDegree < 3) (hF : F.natDegree < N + 1)
    (φ : ℕ → ℚ) :
    ∑ h ∈ range (N + 3), (A * F).coeff h * φ h
      = ∑ i ∈ range (N + 1), F.coeff i * ∑ e ∈ range 3, A.coeff e * φ (i + e) := by
  conv_lhs => rw [A.as_sum_range' 3 hA, F.as_sum_range' (N + 1) hF]
  simp only [Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial, finsetSum_coeff,
    coeff_monomial]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  have : i + e ∈ range (N + 3) := by
    simp only [Finset.mem_range] at he hi ⊢; omega
  rw [if_pos this, add_comm e i]; ring

lemma natDeg_gf (N x : ℕ) (hx : x ≤ N) : (gf N x).natDegree < N + 1 := by
  unfold gf
  have h1 : ((1 - X : ℚ[X]) ^ x).natDegree ≤ x := by
    refine (natDegree_pow_le).trans ?_
    have : (1 - X : ℚ[X]).natDegree ≤ 1 := by
      refine (natDegree_sub_le _ _).trans ?_; simp
    nlinarith
  have h2 : ((1 + X : ℚ[X]) ^ (N - x)).natDegree ≤ N - x := by
    refine (natDegree_pow_le).trans ?_
    have : (1 + X : ℚ[X]).natDegree ≤ 1 := by
      refine (natDegree_add_le _ _).trans ?_; simp
    nlinarith
  have := natDegree_mul_le (p := (1 - X : ℚ[X]) ^ x) (q := (1 + X : ℚ[X]) ^ (N - x))
  omega

lemma gf_up (N x : ℕ) (hx : x ≤ N) : gf (N + 2) (x + 2) = (1 - X) ^ 2 * gf N x := by
  unfold gf; rw [show N + 2 - (x + 2) = N - x by omega]; ring

lemma gf_same (N x : ℕ) (hx : x ≤ N) : gf (N + 2) x = (1 + X) ^ 2 * gf N x := by
  unfold gf; rw [show N + 2 - x = (N - x) + 2 by omega]; ring

lemma deg_sq_sub : ((1 - X : ℚ[X]) ^ 2).natDegree < 3 := by
  have : ((1 - X : ℚ[X]) ^ 2) = 1 - 2 * X + X ^ 2 := by ring
  rw [this]; compute_degree!

lemma deg_sq_add : ((1 + X : ℚ[X]) ^ 2).natDegree < 3 := by
  have : ((1 + X : ℚ[X]) ^ 2) = 1 + 2 * X + X ^ 2 := by ring
  rw [this]; compute_degree!

/-- `Ê(AF, BG)` in terms of the coefficients of `F, G`. -/
lemma Ehat_mul (N : ℕ) (A B F G : ℚ[X]) (hA : A.natDegree < 3) (hB : B.natDegree < 3)
    (hF : F.natDegree < N + 1) (hG : G.natDegree < N + 1) :
    Ehat (N + 2) (A * F) (B * G)
      = ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), F.coeff i * G.coeff j *
          ∑ e ∈ range 3, ∑ f ∈ range 3, A.coeff e * B.coeff f * (S (N + 2) (i + e) (j + f) : ℚ) := by
  unfold Ehat
  have inner : ∀ h, ∑ h' ∈ range (N + 2 + 1), (B * G).coeff h' * (S (N + 2) h h' : ℚ)
      = ∑ j ∈ range (N + 1), G.coeff j * ∑ f ∈ range 3, B.coeff f * (S (N + 2) h (j + f) : ℚ) :=
    fun h => sum_mul_coeff N B G hB hG (fun h' => (S (N + 2) h h' : ℚ))
  simp_rw [inner]
  rw [sum_mul_coeff N A F hA hF]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun e _ => ?_
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

/-- **Lemma 2** (displacement of `Ê`), `n = N + 2`. -/
theorem lemma2 (N x y : ℕ) (hx : x ≤ N) (hy : y ≤ N) :
    Ehat (N + 2) (gf (N + 2) (x + 2)) (gf (N + 2) y)
      - Ehat (N + 2) (gf (N + 2) x) (gf (N + 2) (y + 2))
      = -4 * ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), (gf N x).coeff i * (gf N y).coeff j *
          ((dl ((j : ℤ) - i) * dl ((i : ℤ) + j - N) : ℤ) : ℚ) := by
  rw [gf_up N x hx, gf_same N y hy, gf_same N x hx, gf_up N y hy]
  rw [Ehat_mul N _ _ _ _ deg_sq_sub deg_sq_add (natDeg_gf N x hx) (natDeg_gf N y hy),
    Ehat_mul N _ _ _ _ deg_sq_add deg_sq_sub (natDeg_gf N x hx) (natDeg_gf N y hy)]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : ((1 - X : ℚ[X]) ^ 2) = 1 - 2 * X + X ^ 2 := by ring
  have ha : ((1 + X : ℚ[X]) ^ 2) = 1 + 2 * X + X ^ 2 := by ring
  rw [hs, ha]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_add, coeff_sub, coeff_one,
    coeff_X_pow, coeff_X, coeff_ofNat_mul, coeff_C_mul]
  have hM := M_eq N i j
  simp only [add_zero] at hM ⊢
  norm_num
  push_cast at hM ⊢
  linear_combination (gf N x).coeff i * (gf N y).coeff j * hM

/-! ## Lemma 1: the entries from the paper's point definition -/

/-- `K_c(x;n) = [z^c] (1-z)^x (1+z)^(n-x)`. -/
noncomputable def K (n c x : ℕ) : ℚ := (gf n x).coeff c

/-- the paper's skew product
`⟨f,g⟩_B = Σ_{(2x-n)^2 < (2x'-n)^2} C(n,x) C(n,x') (f(x)g(x') - g(x)f(x'))`, `x, x' ∈ 0..n`. -/
noncomputable def brB (n : ℕ) (f g : ℕ → ℚ) : ℚ :=
  ∑ x ∈ range (n + 1), ∑ x' ∈ range (n + 1),
    if (2 * (x : ℤ) - n) ^ 2 < (2 * (x' : ℤ) - n) ^ 2 then
      (n.choose x : ℚ) * (n.choose x' : ℚ) * (f x * g x' - g x * f x') else 0

/-- `G_ab = ⟨K_2a, K_2b⟩_B`. -/
noncomputable def G (n a b : ℕ) : ℚ := brB n (K n (2 * a)) (K n (2 * b))

lemma ind_sub (A B : ℤ) :
    ((if A < B then (1 : ℚ) else 0) - (if B < A then 1 else 0)) = ((Int.sign (B - A) : ℤ) : ℚ) := by
  rcases lt_trichotomy A B with h | rfl | h
  · rw [if_pos h, if_neg (not_lt.2 h.le), Int.sign_eq_one_of_pos (by omega)]; norm_num
  · simp
  · rw [if_neg (not_lt.2 h.le), if_pos h, Int.sign_eq_neg_one_of_neg (by omega)]; norm_num

lemma S_eq (n x x' : ℕ) :
    S n x x' = Int.sign ((2 * (x' : ℤ) - n) ^ 2 - (2 * (x : ℤ) - n) ^ 2) := by
  unfold S
  rw [show (2 * (x' : ℤ) - n) ^ 2 - (2 * (x : ℤ) - n) ^ 2 = 4 * (((x' : ℤ) - x) * ((x' : ℤ) + x - n)) by ring,
    Int.sign_mul 4, show Int.sign (4 : ℤ) = 1 from rfl, one_mul, Int.sign_mul]

/-- the point form: `⟨f,g⟩_B = Σ_{x,x'} S(x,x') C(n,x) C(n,x') f(x) g(x')`. -/
theorem brB_eq (n : ℕ) (f g : ℕ → ℚ) :
    brB n f g = ∑ x ∈ range (n + 1), ∑ x' ∈ range (n + 1),
      (S n x x' : ℚ) * ((n.choose x : ℚ) * f x) * ((n.choose x' : ℚ) * g x') := by
  have h1 : brB n f g
      = ∑ x ∈ range (n + 1), ∑ x' ∈ range (n + 1),
          (if (2 * (x : ℤ) - n) ^ 2 < (2 * (x' : ℤ) - n) ^ 2 then (1 : ℚ) else 0) *
            ((n.choose x : ℚ) * f x * ((n.choose x' : ℚ) * g x'))
        - ∑ x ∈ range (n + 1), ∑ x' ∈ range (n + 1),
          (if (2 * (x : ℤ) - n) ^ 2 < (2 * (x' : ℤ) - n) ^ 2 then (1 : ℚ) else 0) *
            ((n.choose x' : ℚ) * f x' * ((n.choose x : ℚ) * g x)) := by
    unfold brB
    rw [← sum_sub_distrib]; refine sum_congr rfl fun x _ => ?_
    rw [← sum_sub_distrib]; refine sum_congr rfl fun x' _ => ?_
    split_ifs <;> ring
  have h2 : ∑ x ∈ range (n + 1), ∑ x' ∈ range (n + 1),
          (if (2 * (x : ℤ) - n) ^ 2 < (2 * (x' : ℤ) - n) ^ 2 then (1 : ℚ) else 0) *
            ((n.choose x' : ℚ) * f x' * ((n.choose x : ℚ) * g x))
      = ∑ x ∈ range (n + 1), ∑ x' ∈ range (n + 1),
          (if (2 * (x' : ℤ) - n) ^ 2 < (2 * (x : ℤ) - n) ^ 2 then (1 : ℚ) else 0) *
            ((n.choose x : ℚ) * f x * ((n.choose x' : ℚ) * g x')) := Finset.sum_comm
  rw [h1, h2, ← sum_sub_distrib]; refine sum_congr rfl fun x _ => ?_
  rw [← sum_sub_distrib]; refine sum_congr rfl fun x' _ => ?_
  have hs := ind_sub ((2 * (x : ℤ) - n) ^ 2) ((2 * (x' : ℤ) - n) ^ 2)
  rw [← S_eq] at hs
  rw [← sub_mul, hs]; ring

lemma gf_Fp (n x : ℕ) : gf n x = Bali.ZK.Fp (n - x) x := by unfold gf Bali.ZK.Fp; ring

/-- Krawtchouk duality `C(n,x) K_c(x;n) = C(n,c) K_x(c;n)` (from `Bali.ZK.W_symm`). -/
theorem dual (n c x : ℕ) : (n.choose x : ℚ) * K n c x = (n.choose c : ℚ) * K n x c := by
  have h := Bali.ZK.W_symm n c x
  unfold Bali.ZK.W at h
  unfold K; rw [gf_Fp, gf_Fp]; exact h

/-- Lemma 1 for arbitrary indices `c, d`. -/
theorem lemma1_gen (n c d : ℕ) :
    brB n (K n c) (K n d) = (n.choose c : ℚ) * (n.choose d : ℚ) * Ehat n (gf n c) (gf n d) := by
  rw [brB_eq]; unfold Ehat
  simp only [Finset.mul_sum]
  refine sum_congr rfl fun x _ => sum_congr rfl fun x' _ => ?_
  rw [dual n c x, dual n d x']; unfold K; ring

/-- **Lemma 1** (`lem:entries`): `G_ab = C(n,2a) C(n,2b) Ê(2a,2b)`. -/
theorem lemma1 (n a b : ℕ) :
    G n a b = (n.choose (2 * a) : ℚ) * (n.choose (2 * b) : ℚ)
      * Ehat n (gf n (2 * a)) (gf n (2 * b)) :=
  lemma1_gen n _ _

/-! ## Lemma 2, specialisations (`eq:spec`) -/

lemma gf_succ (N x : ℕ) (hx : x ≤ N) : gf (N + 1) x = (1 + X) * gf N x := by
  unfold gf; rw [show N + 1 - x = (N - x) + 1 by omega]; ring

/-- indicator of `{k, k+1}`. -/
def e1 (k i : ℕ) : ℤ := (if i = k then 1 else 0) + (if i = k + 1 then 1 else 0)

lemma w_odd (k i j : ℕ) :
    dl ((j : ℤ) - i) * dl ((i : ℤ) + j - ((2 * k + 1 : ℕ) : ℤ)) = 2 * e1 k i * e1 k j := by
  unfold dl e1; push_cast; split_ifs <;> omega

lemma sum_e1 (N k : ℕ) (hk : k + 1 < N + 1) (F : ℕ → ℚ) :
    ∑ i ∈ range (N + 1), F i * ((e1 k i : ℤ) : ℚ) = F k + F (k + 1) := by
  unfold e1
  simp only [Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero, mul_add, mul_ite, mul_one,
    mul_zero, sum_add_distrib, sum_ite_eq', mem_range]
  rw [if_pos (by omega), if_pos (by omega)]

lemma dsum (N : ℕ) (F H u v : ℕ → ℚ) :
    ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), F i * H j * (u i * v j)
      = (∑ i ∈ range (N + 1), F i * u i) * ∑ j ∈ range (N + 1), H j * v j := by
  rw [Finset.sum_mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- odd `n = 2k+3` (`m = k+1`), any `x, y ≤ n-2`. -/
theorem spec_odd_gen (k x y : ℕ) (hx : x ≤ 2 * k + 1) (hy : y ≤ 2 * k + 1) :
    Ehat (2 * k + 3) (gf (2 * k + 3) (x + 2)) (gf (2 * k + 3) y)
      - Ehat (2 * k + 3) (gf (2 * k + 3) x) (gf (2 * k + 3) (y + 2))
      = -8 * K (2 * k + 2) (k + 1) x * K (2 * k + 2) (k + 1) y := by
  have h := lemma2 (2 * k + 1) x y hx hy
  rw [show 2 * k + 1 + 2 = 2 * k + 3 by omega] at h
  rw [h]
  have hw : ∀ i j : ℕ, (gf (2 * k + 1) x).coeff i * (gf (2 * k + 1) y).coeff j *
      ((dl ((j : ℤ) - i) * dl ((i : ℤ) + j - ((2 * k + 1 : ℕ) : ℤ)) : ℤ) : ℚ)
      = 2 * ((gf (2 * k + 1) x).coeff i * (gf (2 * k + 1) y).coeff j *
          (((e1 k i : ℤ) : ℚ) * ((e1 k j : ℤ) : ℚ))) := by
    intro i j; rw [w_odd]; push_cast; ring
  simp only [hw, ← Finset.mul_sum]
  rw [dsum, sum_e1 _ _ (by omega), sum_e1 _ _ (by omega)]
  unfold K
  rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, gf_succ _ _ hx, gf_succ _ _ hy,
    Bali.ZK.coeff_one_add, Bali.ZK.coeff_one_add]
  ring

/-- `eq:spec`, odd case `n = 2m+1` (`m = k+1`, `a, b ≤ m-1`):
`Ê(2a+2,2b) - Ê(2a,2b+2) = -8 κ_a κ_b`, `κ_a = K_m(2a;2m)`. -/
theorem spec_odd (k a b : ℕ) (ha : a ≤ k) (hb : b ≤ k) :
    Ehat (2 * k + 3) (gf (2 * k + 3) (2 * a + 2)) (gf (2 * k + 3) (2 * b))
      - Ehat (2 * k + 3) (gf (2 * k + 3) (2 * a)) (gf (2 * k + 3) (2 * b + 2))
      = -8 * K (2 * k + 2) (k + 1) (2 * a) * K (2 * k + 2) (k + 1) (2 * b) :=
  spec_odd_gen k (2 * a) (2 * b) (by omega) (by omega)

def A1 (l i : ℕ) : ℤ := if i = l + 1 then 1 else 0
def B1 (l i : ℕ) : ℤ := (if i = l then 1 else 0) + (if i = l + 2 then 1 else 0)

lemma w_even (l i j : ℕ) :
    dl ((j : ℤ) - i) * dl ((i : ℤ) + j - ((2 * l + 2 : ℕ) : ℤ))
      = 4 * (A1 l i * A1 l j) + A1 l i * B1 l j + B1 l i * A1 l j := by
  unfold dl A1 B1; push_cast; split_ifs <;> omega

lemma sum_A1 (N l : ℕ) (hl : l + 1 < N + 1) (F : ℕ → ℚ) :
    ∑ i ∈ range (N + 1), F i * ((A1 l i : ℤ) : ℚ) = F (l + 1) := by
  unfold A1
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero, sum_ite_eq',
    mem_range]
  rw [if_pos (by omega)]

lemma sum_B1 (N l : ℕ) (hl : l + 2 < N + 1) (F : ℕ → ℚ) :
    ∑ i ∈ range (N + 1), F i * ((B1 l i : ℤ) : ℚ) = F l + F (l + 2) := by
  unfold B1
  simp only [Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero, mul_add, mul_ite, mul_one,
    mul_zero, sum_add_distrib, sum_ite_eq', mem_range]
  rw [if_pos (by omega), if_pos (by omega)]

lemma coeff_sq (H : ℚ[X]) (l : ℕ) :
    ((1 + X) * ((1 + X) * H)).coeff (l + 2) = H.coeff (l + 2) + 2 * H.coeff (l + 1) + H.coeff l := by
  rw [show l + 2 = (l + 1) + 1 by omega, Bali.ZK.coeff_one_add, Bali.ZK.coeff_one_add,
    Bali.ZK.coeff_one_add]
  ring

/-- even `n = 2l+4` (`m = l+2`), any `x, y ≤ n-2`. -/
theorem spec_even_gen (l x y : ℕ) (hx : x ≤ 2 * l + 2) (hy : y ≤ 2 * l + 2) :
    Ehat (2 * l + 4) (gf (2 * l + 4) (x + 2)) (gf (2 * l + 4) y)
      - Ehat (2 * l + 4) (gf (2 * l + 4) x) (gf (2 * l + 4) (y + 2))
      = -8 * (K (2 * l + 2) (l + 1) x * (K (2 * l + 4) (l + 2) y / 2)
          + K (2 * l + 4) (l + 2) x / 2 * K (2 * l + 2) (l + 1) y) := by
  have h := lemma2 (2 * l + 2) x y hx hy
  rw [show 2 * l + 2 + 2 = 2 * l + 4 by omega] at h
  rw [h]
  have hw : ∀ i j : ℕ, (gf (2 * l + 2) x).coeff i * (gf (2 * l + 2) y).coeff j *
      ((dl ((j : ℤ) - i) * dl ((i : ℤ) + j - ((2 * l + 2 : ℕ) : ℤ)) : ℤ) : ℚ)
      = 4 * ((gf (2 * l + 2) x).coeff i * (gf (2 * l + 2) y).coeff j
              * (((A1 l i : ℤ) : ℚ) * ((A1 l j : ℤ) : ℚ)))
        + (gf (2 * l + 2) x).coeff i * (gf (2 * l + 2) y).coeff j
              * (((A1 l i : ℤ) : ℚ) * ((B1 l j : ℤ) : ℚ))
        + (gf (2 * l + 2) x).coeff i * (gf (2 * l + 2) y).coeff j
              * (((B1 l i : ℤ) : ℚ) * ((A1 l j : ℤ) : ℚ)) := by
    intro i j; rw [w_even]; push_cast; ring
  simp only [hw, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [dsum, dsum, dsum, sum_A1 _ _ (by omega), sum_A1 _ _ (by omega), sum_B1 _ _ (by omega),
    sum_B1 _ _ (by omega)]
  unfold K
  rw [show 2 * l + 4 = (2 * l + 2) + 1 + 1 by omega, gf_succ (2 * l + 2 + 1) x (by omega),
    gf_succ (2 * l + 2) x hx, gf_succ (2 * l + 2 + 1) y (by omega), gf_succ (2 * l + 2) y hy,
    coeff_sq, coeff_sq]
  ring

/-- `eq:spec`, even case `n = 2m` (`m = l+2`, `a, b ≤ m-1`):
`Ê(2a+2,2b) - Ê(2a,2b+2) = -8(κ⁰_a κ¹_b + κ¹_a κ⁰_b)`, `κ⁰_a = K_{m-1}(2a;2m-2)`,
`κ¹_a = K_m(2a;2m)/2`. -/
theorem spec_even (l a b : ℕ) (ha : a ≤ l + 1) (hb : b ≤ l + 1) :
    Ehat (2 * l + 4) (gf (2 * l + 4) (2 * a + 2)) (gf (2 * l + 4) (2 * b))
      - Ehat (2 * l + 4) (gf (2 * l + 4) (2 * a)) (gf (2 * l + 4) (2 * b + 2))
      = -8 * (K (2 * l + 2) (l + 1) (2 * a) * (K (2 * l + 4) (l + 2) (2 * b) / 2)
          + K (2 * l + 4) (l + 2) (2 * a) / 2 * K (2 * l + 2) (l + 1) (2 * b)) :=
  spec_even_gen l (2 * a) (2 * b) (by omega) (by omega)

/-! ## central Krawtchouk values -/

lemma coeff_sub_pow (M a : ℕ) : ((1 - X : ℚ[X]) ^ M).coeff a = (-1) ^ a * (M.choose a : ℚ) := by
  have h := Bali.ZK.Fp_swap M 0 a
  simp only [Bali.ZK.Fp, pow_zero, one_mul, mul_one] at h
  rw [h, coeff_one_add_X_pow]

/-- `K_{2a}(M;2M) = [z^{2a}](1-z^2)^M = (-1)^a C(M,a)`. -/
lemma coeff_Fp_MM (M a : ℕ) : (Bali.ZK.Fp M M).coeff (2 * a) = (-1) ^ a * (M.choose a : ℚ) := by
  have e : Bali.ZK.Fp M M = expand ℚ 2 ((1 - X) ^ M) := by
    unfold Bali.ZK.Fp
    rw [map_pow, map_sub, map_one, expand_X, ← mul_pow]
    congr 1; ring
  rw [e, coeff_expand (by norm_num), if_pos (dvd_mul_right 2 a),
    Nat.mul_div_cancel_left a (by norm_num), coeff_sub_pow]

/-- `C(2M,2a) K_M(2a;2M) = (-1)^a C(2M,M) C(M,a)`. -/
theorem central_choose (M a : ℕ) :
    ((2 * M).choose (2 * a) : ℚ) * K (2 * M) M (2 * a)
      = (-1) ^ a * ((2 * M).choose M : ℚ) * (M.choose a : ℚ) := by
  rw [dual]; unfold K; rw [gf_Fp, show 2 * M - M = M by omega, coeff_Fp_MM]; ring

/-- **central values**: `K_M(2a;2M) = (-1)^a C(2M,M) C(M,a) / C(2M,2a)`. -/
theorem central (M a : ℕ) (ha : a ≤ M) :
    K (2 * M) M (2 * a)
      = (-1) ^ a * ((2 * M).choose M : ℚ) * (M.choose a : ℚ) / ((2 * M).choose (2 * a) : ℚ) := by
  have h0 : ((2 * M).choose (2 * a) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [eq_div_iff h0, mul_comm, central_choose]

/-- `K_M(2a;2M) = (-1)^a (2a)! (2M-2a)! / (M! a! (M-a)!)`. -/
theorem central_fact (M a : ℕ) (ha : a ≤ M) :
    K (2 * M) M (2 * a)
      = (-1) ^ a * (((2 * a).factorial : ℚ) * ((2 * M - 2 * a).factorial : ℚ))
          / ((M.factorial : ℚ) * (a.factorial : ℚ) * ((M - a).factorial : ℚ)) := by
  rw [central M a ha, Nat.cast_choose ℚ (show M ≤ 2 * M by omega), Nat.cast_choose ℚ ha,
    Nat.cast_choose ℚ (show 2 * a ≤ 2 * M by omega), show 2 * M - M = M by omega]
  have f1 : ((2 * M).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have f2 : (M.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have f3 : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have f4 : ((M - a).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have f5 : ((2 * a).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have f6 : ((2 * M - 2 * a).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

end Bali.GP

#print axioms Bali.GP.four_sign
#print axioms Bali.GP.M_eq
#print axioms Bali.GP.sum_mul_coeff
#print axioms Bali.GP.lemma2
#print axioms Bali.GP.brB_eq
#print axioms Bali.GP.dual
#print axioms Bali.GP.lemma1
#print axioms Bali.GP.spec_odd_gen
#print axioms Bali.GP.spec_odd
#print axioms Bali.GP.spec_even_gen
#print axioms Bali.GP.spec_even
#print axioms Bali.GP.coeff_Fp_MM
#print axioms Bali.GP.central_choose
#print axioms Bali.GP.central
#print axioms Bali.GP.central_fact

/-! # Stage 3 (2026-11-17): terminating Pfaff–Saalschütz, Chu–Vandermonde, Pfaff transformation
Used in Lemma `lem:orth`, Step 4 of Theorem K (Saalschütz) and the proof of Theorem K (Pfaff). -/

namespace Bali.GP

section Saalschutz

variable {K : Type*} [Field K] [CharZero K]

/-- `(x)_j` as Mathlib's `ascPochhammer`. -/
noncomputable def poch (x : K) (j : ℕ) : K := (ascPochhammer K j).eval x

lemma poch_zero (x : K) : poch x 0 = 1 := by simp [poch]

lemma poch_succ (x : K) (j : ℕ) : poch x (j + 1) = poch x j * (x + j) := by
  simp [poch, ascPochhammer_succ_eval]

lemma poch_succ_left (x : K) (j : ℕ) : poch x (j + 1) = x * poch (x + 1) j := by
  simp [poch, ascPochhammer_succ_left, eval_comp]

lemma poch_eq_prod (x : K) (j : ℕ) : poch x j = ∏ i ∈ range j, (x + i) := by
  induction j with
  | zero => simp [poch_zero]
  | succ j ih => rw [poch_succ, ih, prod_range_succ]

lemma poch_ne_of (x : K) (n : ℕ) (h : poch x n ≠ 0) (i : ℕ) (hi : i < n) : x + i ≠ 0 := by
  rw [poch_eq_prod, prod_ne_zero_iff] at h; exact h i (mem_range.2 hi)

lemma poch_ne_of_le (x : K) (n : ℕ) (h : poch x n ≠ 0) (j : ℕ) (hj : j ≤ n) : poch x j ≠ 0 := by
  rw [poch_eq_prod, prod_ne_zero_iff]; intro i hi
  exact poch_ne_of x n h i (by simp at hi; omega)

lemma poch_negnat (k j : ℕ) (h : k < j) : poch (-(k : K)) j = 0 := by
  rw [poch_eq_prod]; exact prod_eq_zero (i := k) (mem_range.2 h) (by ring)

lemma poch_negnat_desc (k j : ℕ) : poch (-(k : K)) j = (-1) ^ j * (k.descFactorial j : K) := by
  rw [poch, ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]

/-! ### Pfaff–Saalschütz -/

/-- lower parameter `1 + a + b - c - k`. -/
def dd (a b c : K) (k : ℕ) : K := 1 + a + b - c - k

/-- term `j` of `3F2(-k, a, b; c, 1+a+b-c-k; 1)`. -/
noncomputable def t3 (a b c : K) (k j : ℕ) : K :=
  poch (-(k : K)) j * poch a j * poch b j / ((j.factorial : K) * poch c j * poch (dd a b c k) j)

/-- `3F2(-k, a, b; c, 1+a+b-c-k; 1)` (terminating balanced series). -/
noncomputable def F3 (a b c : K) (k : ℕ) : K := ∑ j ∈ range (k + 1), t3 a b c k j

lemma t3_zero (a b c : K) (k : ℕ) : t3 a b c k 0 = 1 := by simp [t3, poch_zero]

lemma t3_over (a b c : K) (k : ℕ) : t3 a b c k (k + 1) = 0 := by
  simp [t3, poch_negnat k (k + 1) (by omega)]

lemma t3_ratio (a b c : K) (k j : ℕ) : t3 a b c k (j + 1) = t3 a b c k j *
    (((-(k : K)) + j) * (a + j) * (b + j) / ((j + 1) * (c + j) * (dd a b c k + j))) := by
  unfold t3
  rw [poch_succ, poch_succ, poch_succ, poch_succ, poch_succ, Nat.factorial_succ, div_mul_div_comm]
  congr 1 <;> push_cast <;> ring

lemma t3_ratio_succ (a b c : K) (k j : ℕ) : t3 a b c (k + 1) (j + 1) = t3 a b c k j *
    ((-((k : K) + 1)) * (a + j) * (b + j) / ((j + 1) * (c + j) * (dd a b c k - 1))) := by
  unfold t3
  have e1 : (-(((k + 1 : ℕ)) : K)) + 1 = -(k : K) := by push_cast; ring
  have e2 : dd a b c (k + 1) + 1 = dd a b c k := by unfold dd; push_cast; ring
  rw [poch_succ_left (-(((k + 1 : ℕ)) : K)), e1, poch_succ_left (dd a b c (k + 1)), e2,
    poch_succ a, poch_succ b, poch_succ c, Nat.factorial_succ, div_mul_div_comm]
  have e3 : dd a b c (k + 1) = dd a b c k - 1 := by unfold dd; push_cast; ring
  rw [e3]; congr 1 <;> push_cast <;> ring

/-- One Zeilberger step: `(c+k)(c-a-b+k) F(k+1) = (c-a+k)(c-b+k) F(k)`. -/
lemma F3_step (a b c : K) (k : ℕ) (hc : poch c (k + 1) ≠ 0)
    (hcab : poch (c - a - b) (k + 1) ≠ 0) :
    (c + k) * (c - a - b + k) * F3 a b c (k + 1) = (c - a + k) * (c - b + k) * F3 a b c k := by
  have hci : ∀ i ≤ k, c + i ≠ 0 := fun i hi => poch_ne_of c _ hc i (by omega)
  have hei : ∀ i ≤ k, c - a - b + i ≠ 0 := fun i hi => poch_ne_of _ _ hcab i (by omega)
  have hd1 : dd a b c k - 1 ≠ 0 := by
    intro h; apply hei k le_rfl; unfold dd at h; linear_combination -h
  have key : ∀ j ≤ k, (c + k) * (c - a - b + k) * t3 a b c (k + 1) (j + 1)
      - (c - a + k) * (c - b + k) * t3 a b c k (j + 1)
      = (a + j) * (b + j) * t3 a b c k j
        - (a + ((j + 1 : ℕ) : K)) * (b + ((j + 1 : ℕ) : K)) * t3 a b c k (j + 1) := by
    intro j hj
    rw [t3_ratio_succ, t3_ratio]
    have hj1 : (j : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have hcj := hci j hj
    rcases Nat.lt_or_ge j k with hlt | hge
    · have hdj : dd a b c k + j ≠ 0 := by
        obtain ⟨m, rfl⟩ : ∃ m, k = j + 1 + m := ⟨k - j - 1, by omega⟩
        intro h; apply hei m (by omega); unfold dd at h; push_cast at h; linear_combination -h
      field_simp
      push_cast
      unfold dd
      ring
    · have hjk : j = k := le_antisymm hj hge
      subst hjk
      have : (-(j : K)) + j = 0 := by ring
      rw [this]; simp only [zero_mul, zero_div, mul_zero, sub_zero]
      unfold dd at hd1 ⊢
      field_simp
      ring
  have ext : ∑ j ∈ range (k + 1), t3 a b c k j = ∑ j ∈ range (k + 1 + 1), t3 a b c k j := by
    rw [sum_range_succ (fun j => t3 a b c k j) (k + 1), t3_over, add_zero]
  unfold F3
  rw [ext]
  rw [← sub_eq_zero, mul_sum, mul_sum, ← sum_sub_distrib, sum_range_succ']
  rw [sum_congr rfl (fun j hj => key j (by simp at hj; omega))]
  rw [sum_range_sub' (fun j => (a + j) * (b + j) * t3 a b c k j), t3_over, t3_zero, t3_zero]
  push_cast; ring

/-- **Pfaff–Saalschütz** (terminating):
`3F2(-k, a, b; c, 1+a+b-c-k; 1) = (c-a)_k (c-b)_k / ((c)_k (c-a-b)_k)`,
for `(c)_k ≠ 0` and `(c-a-b)_k ≠ 0`, over any field of characteristic `0`. -/
theorem pfaff_saalschutz (a b c : K) (k : ℕ) (hc : poch c k ≠ 0)
    (hcab : poch (c - a - b) k ≠ 0) :
    F3 a b c k = poch (c - a) k * poch (c - b) k / (poch c k * poch (c - a - b) k) := by
  induction k with
  | zero => simp [F3, t3_zero, poch_zero]
  | succ k ih =>
    have hc' := poch_ne_of_le c _ hc k (by omega)
    have hcab' := poch_ne_of_le _ _ hcab k (by omega)
    have hck := poch_ne_of c _ hc k (by omega)
    have hek := poch_ne_of _ _ hcab k (by omega)
    have st := F3_step a b c k hc hcab
    rw [ih hc' hcab'] at st
    rw [poch_succ (c - a), poch_succ (c - b), poch_succ c, poch_succ (c - a - b)]
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero hc' hck) (mul_ne_zero hcab' hek))]
    field_simp at st
    linear_combination st

/-! ### Chu–Vandermonde and Pfaff's transformation (terminating) -/

/-- `(-n)_j (b)_j / ((c)_j j!)`, term `j` of `2F1(-n, b; c; ·)`. -/
noncomputable def v2 (b c : K) (n j : ℕ) : K :=
  poch (-(n : K)) j * poch b j / (poch c j * (j.factorial : K))

lemma v2_zero (b c : K) (n : ℕ) : v2 b c n 0 = 1 := by simp [v2, poch_zero]

lemma v2_over (b c : K) (n : ℕ) : v2 b c n (n + 1) = 0 := by
  simp [v2, poch_negnat n (n + 1) (by omega)]

lemma v2_ratio (b c : K) (n j : ℕ) : v2 b c n (j + 1) =
    v2 b c n j * (((-(n : K)) + j) * (b + j) / ((c + j) * (j + 1))) := by
  unfold v2
  rw [poch_succ, poch_succ, poch_succ, Nat.factorial_succ, div_mul_div_comm]
  congr 1 <;> push_cast <;> ring

lemma v2_ratio_succ (b c : K) (n j : ℕ) : v2 b c (n + 1) (j + 1) =
    v2 b c n j * ((-((n : K) + 1)) * (b + j) / ((c + j) * (j + 1))) := by
  unfold v2
  have e1 : (-(((n + 1 : ℕ)) : K)) + 1 = -(n : K) := by push_cast; ring
  rw [poch_succ_left (-(((n + 1 : ℕ)) : K)), e1, poch_succ b, poch_succ c, Nat.factorial_succ,
    div_mul_div_comm]
  congr 1 <;> push_cast <;> ring

/-- **Chu–Vandermonde**: `Σ_j (-n)_j (b)_j / ((c)_j j!) = (c-b)_n / (c)_n`, `(c)_n ≠ 0`. -/
theorem chu_vandermonde (b c : K) (n : ℕ) (hc : poch c n ≠ 0) :
    ∑ j ∈ range (n + 1), v2 b c n j = poch (c - b) n / poch c n := by
  induction n with
  | zero => simp [v2_zero, poch_zero]
  | succ n ih =>
    have hc' := poch_ne_of_le c _ hc n (by omega)
    have hci : ∀ i ≤ n, c + i ≠ 0 := fun i hi => poch_ne_of c _ hc i (by omega)
    have key : ∀ j ≤ n, (c + n) * v2 b c (n + 1) (j + 1) - (c - b + n) * v2 b c n (j + 1)
        = (b + ((j + 1 : ℕ) : K)) * v2 b c n (j + 1) - (b + j) * v2 b c n j := by
      intro j hj
      rw [v2_ratio_succ, v2_ratio]
      have hj1 : (j : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      have hcj := hci j hj
      field_simp
      push_cast
      ring
    have st : (c + n) * ∑ j ∈ range (n + 1 + 1), v2 b c (n + 1) j
        = (c - b + n) * ∑ j ∈ range (n + 1), v2 b c n j := by
      have ext : ∑ j ∈ range (n + 1), v2 b c n j = ∑ j ∈ range (n + 1 + 1), v2 b c n j := by
        rw [sum_range_succ (fun j => v2 b c n j) (n + 1), v2_over, add_zero]
      rw [ext]
      rw [← sub_eq_zero, mul_sum, mul_sum, ← sum_sub_distrib, sum_range_succ']
      rw [sum_congr rfl (fun j hj => key j (by simp at hj; omega))]
      rw [sum_range_sub (fun j => (b + j) * v2 b c n j), v2_over, v2_zero, v2_zero]
      push_cast; ring
    rw [ih hc'] at st
    have hcn := hci n le_rfl
    rw [poch_succ (c - b), poch_succ c, eq_div_iff (mul_ne_zero hc' hcn)]
    field_simp at st
    linear_combination st

lemma coeff_one_sub_X_pow' (m i : ℕ) :
    (((1 : K[X]) - X) ^ m).coeff i = (-1) ^ i * (m.choose i : K) := by
  have : ((1 : K[X]) - X) ^ m = C ((-1) ^ m) * (X + C (-1)) ^ m := by
    rw [show (1 : K[X]) - X = C (-1) * (X + C (-1)) by simp [C_neg]; ring, mul_pow, ← C_pow]
  rw [this, coeff_C_mul, coeff_X_add_C_pow]
  rcases Nat.lt_or_ge m i with h | h
  · simp [Nat.choose_eq_zero_of_lt h]
  · rw [← mul_assoc, ← pow_add]
    obtain ⟨r, rfl⟩ : ∃ r, m = i + r := ⟨m - i, by omega⟩
    rw [show i + r + (i + r - i) = i + 2 * r by omega, pow_add, pow_mul]; simp

/-- **Pfaff's transformation** (terminating, polynomial form): with `τ = u/(u-1)`,
`(1-u)^k · 2F1(-k, b; c; τ) = Σ_j (-k)_j (b)_j/((c)_j j!) (-u)^j (1-u)^(k-j) = 2F1(-k, c-b; c; u)`,
coefficientwise in `K[X]`, for `(c)_k ≠ 0`. -/
theorem pfaff_poly (b c : K) (k : ℕ) (hc : poch c k ≠ 0) :
    ∑ j ∈ range (k + 1), C (v2 b c k j) * (-X) ^ j * ((1 : K[X]) - X) ^ (k - j)
      = ∑ j ∈ range (k + 1), C (v2 (c - b) c k j) * X ^ j := by
  ext n
  have hterm : ∀ j, (C (v2 b c k j) * (-X) ^ j * ((1 : K[X]) - X) ^ (k - j)).coeff n
      = if j ≤ n then v2 b c k j * ((-1) ^ j * ((-1) ^ (n - j) * ((k - j).choose (n - j) : K)))
        else 0 := by
    intro j
    have hx : (-X : K[X]) ^ j = C ((-1) ^ j) * X ^ j := by rw [neg_pow, C_pow, C_neg, C_1]
    rw [hx, show C (v2 b c k j) * (C ((-1) ^ j) * X ^ j) * ((1 : K[X]) - X) ^ (k - j)
      = C (v2 b c k j * (-1) ^ j) * (X ^ j * ((1 : K[X]) - X) ^ (k - j)) by rw [C_mul]; ring,
      coeff_C_mul, coeff_X_pow_mul']
    split_ifs <;> simp [coeff_one_sub_X_pow', mul_assoc]
  simp only [finsetSum_coeff, hterm, coeff_C_mul, coeff_X_pow]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_range]
  rcases Nat.lt_or_ge k n with hkn | hnk
  · rw [if_neg (by omega)]
    apply sum_eq_zero; intro j hj; simp at hj
    split_ifs
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    · rfl
  rw [if_pos (by omega)]
  have hcn := poch_ne_of_le c _ hc n hnk
  have cv := chu_vandermonde b c n hcn
  have split : range (k + 1) = range (n + 1) ∪ (Ico (n + 1) (k + 1)) := by
    ext x; simp; omega
  rw [split, sum_union (by rw [disjoint_left]; intro x h1 h2; simp at h1 h2; omega)]
  rw [sum_eq_zero (s := Ico (n + 1) (k + 1)) (fun j hj => by simp at hj; rw [if_neg (by omega)]),
    add_zero]
  rw [sum_congr rfl (fun j hj => by simp at hj; rw [if_pos (by omega)])]
  have rhs : v2 (c - b) c k n = poch (-(k : K)) n / (n.factorial : K) *
      ∑ j ∈ range (n + 1), v2 b c n j := by
    rw [cv, v2]; have := Nat.factorial_ne_zero n
    field_simp
  rw [rhs, mul_sum]
  apply sum_congr rfl
  intro j hj; simp at hj
  unfold v2
  rw [poch_negnat_desc, poch_negnat_desc, poch_negnat_desc]
  have hcj := poch_ne_of_le c _ hc j (by omega)
  have hfj := Nat.factorial_ne_zero j
  have hfn := Nat.factorial_ne_zero n
  have comb : (k.descFactorial j : K) * ((k - j).choose (n - j) : K)
      = (k.descFactorial n : K) / (n.factorial : K) * (n.descFactorial j : K) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_factorial_mul_choose]
    have h := Nat.choose_mul (n := k) (k := n) (s := j) (by omega)
    have h' : ((k.choose n : ℕ) : K) * (n.choose j : K)
        = (k.choose j : K) * ((k - j).choose (n - j) : K) := by
      exact_mod_cast h
    push_cast
    field_simp
    linear_combination -h'
  have sgn : ((-1 : K) ^ j) * ((-1) ^ j * (-1) ^ (n - j)) = (-1) ^ n * (-1) ^ j := by
    rw [← mul_assoc, ← pow_add, ← pow_add, ← pow_add]
    obtain ⟨r, rfl⟩ : ∃ r, n = j + r := ⟨n - j, by omega⟩
    rw [show j + j + (j + r - j) = j + r + j by omega]
  calc _ = (k.descFactorial j : K) * ((k - j).choose (n - j) : K)
        * ((-1 : K) ^ j * ((-1) ^ j * (-1) ^ (n - j))) * poch b j / (poch c j * (j.factorial : K)) := by
        ring
    _ = _ := by rw [comb, sgn]; field_simp

/-- Pfaff's transformation in the rational form used in the paper (proof of Theorem K):
`(1-u)^k Σ_j (-k)_j (b)_j/((c)_j j!) (u/(u-1))^j = Σ_j (-k)_j (c-b)_j/((c)_j j!) u^j`, `u ≠ 1`. -/
theorem pfaff_eval (b c : K) (k : ℕ) (hc : poch c k ≠ 0) (u : K) (hu : u ≠ 1) :
    (1 - u) ^ k * ∑ j ∈ range (k + 1), v2 b c k j * (u / (u - 1)) ^ j
      = ∑ j ∈ range (k + 1), v2 (c - b) c k j * u ^ j := by
  have h := congrArg (Polynomial.eval u) (pfaff_poly b c k hc)
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_neg, eval_X, eval_sub,
    eval_one] at h
  rw [← h, mul_sum]
  apply sum_congr rfl; intro j hj; simp at hj
  have h2 : u - 1 ≠ 0 := sub_ne_zero.2 hu
  obtain ⟨r, rfl⟩ : ∃ r, k = j + r := ⟨k - j, by omega⟩
  rw [show j + r - j = r by omega, pow_add, div_pow]
  have : (1 - u) ^ j = (-1) ^ j * (u - 1) ^ j := by rw [← mul_pow]; ring
  rw [this, neg_pow u]
  field_simp

end Saalschutz

end Bali.GP

#print axioms Bali.GP.pfaff_saalschutz
#print axioms Bali.GP.chu_vandermonde
#print axioms Bali.GP.pfaff_poly
#print axioms Bali.GP.pfaff_eval

/-! # Stage 4 (2026-11-17): `L0`, `L1`, Lemma 3 (`lem:Omega`), remark (T), Lemma 4 (`lem:ker`),
`lem:orth`, Theorem K (`thm:K`). Statements follow `draft.tex` §§2–5. -/

namespace Bali.GP

section Stage4

/-! ## the moment functionals `L0`, `L1` -/

/-- `L0(u^l) = (1/2)_l / l!`, extended linearly. -/
noncomputable def L0 : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun l => (poch (1 / 2 : ℚ) l / (l.factorial : ℚ)) • LinearMap.id)

/-- `L1(f) = L0((1-u) f)`. -/
noncomputable def L1 : ℚ[X] →ₗ[ℚ] ℚ := L0 ∘ₗ LinearMap.mulLeft ℚ (1 - X)

lemma L1_apply (f : ℚ[X]) : L1 f = L0 ((1 - X) * f) := rfl

theorem L0_X_pow (l : ℕ) : L0 (X ^ l) = poch (1 / 2 : ℚ) l / (l.factorial : ℚ) := by
  rw [X_pow_eq_monomial]
  simp [L0, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

/-- the Beta value `B(i,j) = (1/2)_i (1/2)_j / (i+j)!`. -/
noncomputable def Bv (i j : ℕ) : ℚ := poch (1 / 2 : ℚ) i * poch (1 / 2 : ℚ) j / ((i + j).factorial : ℚ)

/-- `L0(u^i (1-u)^j) = (1/2)_i (1/2)_j / (i+j)!`. -/
theorem L0_beta (i j : ℕ) : L0 (X ^ i * (1 - X) ^ j) = Bv i j := by
  induction j generalizing i with
  | zero => simp [L0_X_pow, Bv, poch_zero]
  | succ j ih =>
    have e : (X : ℚ[X]) ^ i * (1 - X) ^ (j + 1) = X ^ i * (1 - X) ^ j - X ^ (i + 1) * (1 - X) ^ j := by
      ring
    rw [e, map_sub, ih, ih]
    unfold Bv
    rw [poch_succ, poch_succ, show i + 1 + j = (i + j) + 1 by omega,
      show i + (j + 1) = (i + j) + 1 by omega, Nat.factorial_succ]
    have h1 : ((i + j).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : ((i + j : ℕ) : ℚ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma poch_half (j : ℕ) : poch (1 / 2 : ℚ) j = ((2 * j).factorial : ℚ) / (4 ^ j * (j.factorial : ℚ)) := by
  induction j with
  | zero => simp [poch_zero]
  | succ j ih =>
    rw [poch_succ, ih, show 2 * (j + 1) = (2 * j + 1) + 1 by omega, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_succ]
    have h1 : ((2 * j).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    push_cast
    field_simp
    ring

/-- `K_M(2a;2M) = (-1)^a 4^M L0(u^a (1-u)^(M-a))`. -/
theorem central_L0 (M a : ℕ) (ha : a ≤ M) :
    K (2 * M) M (2 * a) = (-1) ^ a * 4 ^ M * L0 (X ^ a * (1 - X) ^ (M - a)) := by
  obtain ⟨c, rfl⟩ : ∃ c, M = a + c := ⟨M - a, by omega⟩
  rw [central_fact _ _ ha, L0_beta, Bv, poch_half, poch_half,
    show a + c - a = c by omega, show 2 * (a + c) - 2 * a = 2 * c by omega]
  have f1 : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have f2 : (c.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have f3 : ((a + c).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [pow_add]
  field_simp

/-- `η_a = u^a (1-u)^(m-1-a)`. -/
noncomputable def eta (m a : ℕ) : ℚ[X] := X ^ a * (1 - X) ^ (m - 1 - a)

/-- `ε_a = (-1)^a u^a (1-u)^(m-a)`. -/
noncomputable def eps (m a : ℕ) : ℚ[X] := ((-1 : ℚ) ^ a) • (X ^ a * (1 - X) ^ (m - a))

/-- `K_m(2a;2m) = (-1)^a 4^m L1(η_a)` (`a ≤ m-1`), i.e. `|K_m(2a;2m)| = 4^m L1(η_a)`. -/
theorem central_L1_eta (m a : ℕ) (ha : a + 1 ≤ m) :
    K (2 * m) m (2 * a) = (-1) ^ a * 4 ^ m * L1 (eta m a) := by
  rw [central_L0 m a (by omega), L1_apply, eta]
  congr 2
  rw [show m - a = (m - 1 - a) + 1 by omega]; ring

/-- `K_{m-1}(2a;2m-2) = (-1)^a 4^(m-1) L0(η_a)` (`a ≤ m-1`). -/
theorem central_L0_eta (m a : ℕ) (ha : a + 1 ≤ m) :
    K (2 * m - 2) (m - 1) (2 * a) = (-1) ^ a * 4 ^ (m - 1) * L0 (eta m a) := by
  rw [show 2 * m - 2 = 2 * (m - 1) by omega, central_L0 (m - 1) a (by omega), eta]

theorem abs_central_L1 (m a : ℕ) (ha : a + 1 ≤ m) :
    |K (2 * m) m (2 * a)| = 4 ^ m * L1 (eta m a) := by
  have hp : 0 ≤ L1 (eta m a) := by
    rw [L1_apply, eta, show (1 - X) * (X ^ a * (1 - X) ^ (m - 1 - a)) = (X : ℚ[X]) ^ a * (1 - X) ^ (m - 1 - a + 1) by ring,
      L0_beta, Bv, poch_eq_prod, poch_eq_prod]
    positivity
  rw [central_L1_eta m a ha, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (by positivity), abs_of_nonneg hp]

theorem abs_central_L0 (m a : ℕ) (ha : a + 1 ≤ m) :
    |K (2 * m - 2) (m - 1) (2 * a)| = 4 ^ (m - 1) * L0 (eta m a) := by
  have hp : 0 ≤ L0 (eta m a) := by
    rw [eta, L0_beta, Bv, poch_eq_prod, poch_eq_prod]
    positivity
  rw [central_L0_eta m a ha, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (by positivity), abs_of_nonneg hp]

/-! ## bilinear forms on `ℚ[u]` given on monomials -/

/-- the linear functional `q ↦ Σ_j q_j c(i,j)`. -/
noncomputable def row (c : ℕ → ℕ → ℚ) (i : ℕ) : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun j => c i j • LinearMap.id)

/-- the bilinear form with `B(u^i,u^j) = c(i,j)`. -/
noncomputable def bf (c : ℕ → ℕ → ℚ) : ℚ[X] →ₗ[ℚ] ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun i => LinearMap.smulRight LinearMap.id (row c i))

theorem bf_X_pow (c : ℕ → ℕ → ℚ) (i j : ℕ) : bf c (X ^ i) (X ^ j) = c i j := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial]
  simp [bf, row, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

theorem bil_ext {B B' : ℚ[X] →ₗ[ℚ] ℚ[X] →ₗ[ℚ] ℚ}
    (h : ∀ i j, B (X ^ i) (X ^ j) = B' (X ^ i) (X ^ j)) : B = B' := by
  apply Polynomial.lhom_ext'; intro i
  apply LinearMap.ext_ring
  apply Polynomial.lhom_ext'; intro j
  apply LinearMap.ext_ring
  simpa [← X_pow_eq_monomial] using h i j



/-! ## Lemma 3(a): the antisymmetric form `Ω` with displacement `(D)` -/

/-- the paper's coefficients: `Ω(u^i,u^j) = ½[Σ_{l=i}^{N-1} - Σ_{l=0}^{i-1}] R_l`,
`R_l = R(u^l, u^(N-1-l))`, `N = i+j`. -/
noncomputable def omc (R : ℚ[X] →ₗ[ℚ] ℚ[X] →ₗ[ℚ] ℚ) (i j : ℕ) : ℚ :=
  (1 / 2) * (∑ l ∈ Ico i (i + j), R (X ^ l) (X ^ (i + j - 1 - l))
    - ∑ l ∈ range i, R (X ^ l) (X ^ (i + j - 1 - l)))

/-- `Ω` (for a given symmetric `R`), extended bilinearly. -/
noncomputable def Om (R : ℚ[X] →ₗ[ℚ] ℚ[X] →ₗ[ℚ] ℚ) : ℚ[X] →ₗ[ℚ] ℚ[X] →ₗ[ℚ] ℚ := bf (omc R)

/-- `R = L1 ⊗ L1` (`n` odd). -/
noncomputable def Rodd : ℚ[X] →ₗ[ℚ] ℚ[X] →ₗ[ℚ] ℚ := (LinearMap.mul ℚ ℚ).compl₁₂ L1 L1

/-- `R = L1 ⊗ L0 + L0 ⊗ L1` (`n` even). -/
noncomputable def Reven : ℚ[X] →ₗ[ℚ] ℚ[X] →ₗ[ℚ] ℚ :=
  (LinearMap.mul ℚ ℚ).compl₁₂ L1 L0 + (LinearMap.mul ℚ ℚ).compl₁₂ L0 L1

lemma Rodd_apply (p q : ℚ[X]) : Rodd p q = L1 p * L1 q := by simp [Rodd]

lemma Reven_apply (p q : ℚ[X]) : Reven p q = L1 p * L0 q + L0 p * L1 q := by simp [Reven]

lemma Rodd_symm (p q : ℚ[X]) : Rodd p q = Rodd q p := by rw [Rodd_apply, Rodd_apply, mul_comm]

lemma Reven_symm (p q : ℚ[X]) : Reven p q = Reven q p := by rw [Reven_apply, Reven_apply]; ring

lemma omc_eq (R : ℚ[X] →ₗ[ℚ] ℚ[X] →ₗ[ℚ] ℚ) (i j : ℕ) :
    omc R i j = (1 / 2) * (∑ l ∈ range (i + j), R (X ^ l) (X ^ (i + j - 1 - l))
      - 2 * ∑ l ∈ range i, R (X ^ l) (X ^ (i + j - 1 - l))) := by
  unfold omc; rw [Finset.sum_Ico_eq_sub _ (by omega)]; ring

theorem omc_shift (R : ℚ[X] →ₗ[ℚ] ℚ[X] →ₗ[ℚ] ℚ) (i j : ℕ) :
    omc R (i + 1) j - omc R i (j + 1) = -R (X ^ i) (X ^ j) := by
  rw [omc_eq, omc_eq, show i + 1 + j = i + j + 1 by omega, show i + (j + 1) = i + j + 1 by omega,
    Finset.sum_range_succ (fun l => R (X ^ l) (X ^ (i + j + 1 - 1 - l))) i,
    show i + j + 1 - 1 - i = j by omega]
  ring

theorem omc_anti (R : ℚ[X] →ₗ[ℚ] ℚ[X] →ₗ[ℚ] ℚ) (hR : ∀ p q, R p q = R q p) (i j : ℕ) :
    omc R j i = -omc R i j := by
  rw [omc_eq, omc_eq, add_comm j i]
  have key : ∑ l ∈ range (i + j), R (X ^ l) (X ^ (i + j - 1 - l))
      = ∑ l ∈ range i, R (X ^ l) (X ^ (i + j - 1 - l))
        + ∑ l ∈ range j, R (X ^ l) (X ^ (i + j - 1 - l)) := by
    rw [Finset.sum_range_add]
    congr 1
    rw [← Finset.sum_range_reflect]
    refine sum_congr rfl fun l hl => ?_
    rw [mem_range] at hl
    rw [hR, show i + j - 1 - (i + (j - 1 - l)) = l by omega,
      show i + (j - 1 - l) = i + j - 1 - l by omega]
  rw [key]; ring

/-- **Lemma 3(a)**, antisymmetry of `Ω` (for symmetric `R`). -/
theorem Om_anti (R : ℚ[X] →ₗ[ℚ] ℚ[X] →ₗ[ℚ] ℚ) (hR : ∀ p q, R p q = R q p) (p q : ℚ[X]) :
    Om R p q = -Om R q p := by
  have h : Om R = -(Om R).flip := by
    apply bil_ext; intro i j
    simp only [Om, LinearMap.neg_apply, LinearMap.flip_apply, bf_X_pow]
    exact (omc_anti R hR j i)
  exact DFunLike.congr_fun (DFunLike.congr_fun h p) q

/-- **Lemma 3(a)**, the displacement `(D)`: `Ω(up,q) - Ω(p,uq) = -R(p,q)`. -/
theorem Om_D (R : ℚ[X] →ₗ[ℚ] ℚ[X] →ₗ[ℚ] ℚ) (p q : ℚ[X]) :
    Om R (X * p) q - Om R p (X * q) = -R p q := by
  have h : (Om R).comp (LinearMap.mulLeft ℚ X) - (Om R).compl₂ (LinearMap.mulLeft ℚ X) = -R := by
    apply bil_ext; intro i j
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.compl₂_apply,
      LinearMap.mulLeft_apply, LinearMap.neg_apply, ← pow_succ', Om, bf_X_pow]
    exact omc_shift R i j
  have := DFunLike.congr_fun (DFunLike.congr_fun h p) q
  simpa using this

/-! ## Lemma 3(b): uniqueness -/

/-- the chain argument on index pairs. -/
theorem chain (M : ℕ) (D : ℕ → ℕ → ℚ)
    (hanti : ∀ a b, a ≤ M → b ≤ M → D a b = -D b a)
    (hsh : ∀ a b, a < M → b < M → D (a + 1) b = D a (b + 1)) :
    ∀ a b, a ≤ M → b ≤ M → D a b = 0 := by
  have hmove : ∀ d b c, b + d ≤ M → c + d ≤ M → D (b + d) c = D b (c + d) := by
    intro d
    induction d with
    | zero => intro b c _ _; rfl
    | succ d ih =>
      intro b c h1 h2
      rw [show b + (d + 1) = (b + d) + 1 by omega, hsh _ _ (by omega) (by omega),
        ih b (c + 1) (by omega) (by omega), show c + 1 + d = c + (d + 1) by omega]
  have hge : ∀ a b, b ≤ a → a ≤ M → D a b = 0 := by
    intro a b hba haM
    obtain ⟨d, rfl⟩ : ∃ d, a = b + d := ⟨a - b, by omega⟩
    have h1 := hmove d b b haM haM
    have h2 := hanti (b + d) b haM (by omega)
    linarith
  intro a b ha hb
  rcases le_total b a with h | h
  · exact hge a b h ha
  · rw [hanti a b ha hb, hge b a h hb, neg_zero]

/-- **Lemma 3(b)**: an antisymmetric bilinear form `Δ` on `P_M` with `Δ(up,q) = Δ(p,uq)` for
`p, q ∈ P_{M-1}` is zero on `P_M`. -/
theorem lemma3b (M : ℕ) (Δ : ℚ[X] →ₗ[ℚ] ℚ[X] →ₗ[ℚ] ℚ)
    (hanti : ∀ p q : ℚ[X], p.natDegree ≤ M → q.natDegree ≤ M → Δ p q = -Δ q p)
    (hsh : ∀ p q : ℚ[X], p.natDegree < M → q.natDegree < M → Δ (X * p) q = Δ p (X * q)) :
    ∀ p q : ℚ[X], p.natDegree ≤ M → q.natDegree ≤ M → Δ p q = 0 := by
  have hz := chain M (fun a b => Δ (X ^ a) (X ^ b))
    (fun a b ha hb => hanti _ _ (by simpa using ha) (by simpa using hb))
    (fun a b ha hb => by
      simp only [pow_succ']
      exact hsh _ _ (by simpa using ha) (by simpa using hb))
  intro p q hp hq
  rw [p.as_sum_range' (M + 1) (by omega), q.as_sum_range' (M + 1) (by omega)]
  simp only [← smul_X_eq_monomial, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  have hz' : ∀ i ∈ range (M + 1), ∀ j ∈ range (M + 1), Δ (X ^ i) (X ^ j) = 0 := by
    intro i hi j hj; rw [mem_range] at hi hj; exact hz i j (by omega) (by omega)
  exact sum_eq_zero fun j hj => by
    rw [sum_eq_zero (fun i hi => by rw [hz' i hi j hj, mul_zero]), mul_zero]

/-! ## Lemma 3(c) -/

lemma S_anti (n h h' : ℕ) : S n h' h = -S n h h' := by
  unfold S
  rw [← Int.sign_neg]; congr 1; ring

theorem Ehat_anti (n : ℕ) (F G : ℚ[X]) : Ehat n G F = -Ehat n F G := by
  unfold Ehat
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine sum_congr rfl fun h _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine sum_congr rfl fun h' _ => ?_
  rw [S_anti]; push_cast; ring

/-- the `ε`-matrix of `Ω` has displacement `(-1)^(a+b) R(η_a,η_b)`. -/
theorem eps_shift (R : ℚ[X] →ₗ[ℚ] ℚ[X] →ₗ[ℚ] ℚ) (m a b : ℕ) (ha : a + 1 ≤ m) (hb : b + 1 ≤ m) :
    Om R (eps m (a + 1)) (eps m b) - Om R (eps m a) (eps m (b + 1))
      = (-1) ^ a * (-1) ^ b * R (eta m a) (eta m b) := by
  have e1 : ∀ c, c + 1 ≤ m → eps m (c + 1) = ((-1 : ℚ) ^ (c + 1)) • (X * eta m c) := by
    intro c hc; unfold eps eta
    rw [show m - (c + 1) = m - 1 - c by omega]; congr 1; ring
  have e0 : ∀ c, c + 1 ≤ m → eps m c = ((-1 : ℚ) ^ c) • (eta m c - X * eta m c) := by
    intro c hc; unfold eps eta
    rw [show m - c = (m - 1 - c) + 1 by omega]; congr 1; ring
  have hD := Om_D R (eta m a) (eta m b)
  rw [e1 a ha, e0 b hb, e0 a ha, e1 b hb]
  simp only [map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
  rw [pow_succ, pow_succ]
  linear_combination (-((-1 : ℚ) ^ a * (-1) ^ b)) * hD

/-- **Lemma 3(c)**, odd `n = 2m+1`: `G_ab = χ_n C(n,2a) C(n,2b) Ω(ε_a,ε_b)`, `χ_n = -2^(2n+1)`. -/
theorem lemma3c_odd (m a b : ℕ) (ha : a ≤ m) (hb : b ≤ m) :
    G (2 * m + 1) a b = -2 ^ (2 * (2 * m + 1) + 1) * ((2 * m + 1).choose (2 * a) : ℚ)
      * ((2 * m + 1).choose (2 * b) : ℚ) * Om Rodd (eps m a) (eps m b) := by
  rw [lemma1]
  have key := chain m (fun a b => Ehat (2 * m + 1) (gf (2 * m + 1) (2 * a)) (gf (2 * m + 1) (2 * b))
      - (-2 ^ (2 * (2 * m + 1) + 1)) * Om Rodd (eps m a) (eps m b))
    (fun a b _ _ => by
      rw [Ehat_anti, Om_anti Rodd Rodd_symm (eps m a)]; ring)
    (fun a b ha hb => by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hs := spec_odd k a b (by omega) (by omega)
      have he := eps_shift Rodd (k + 1) a b (by omega) (by omega)
      rw [Rodd_apply] at he
      rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega] at *
      rw [show 2 * k + 2 = 2 * (k + 1) by omega, central_L1_eta (k + 1) a (by omega),
        central_L1_eta (k + 1) b (by omega)] at hs
      rw [show 2 * (a + 1) = 2 * a + 2 by omega, show 2 * (b + 1) = 2 * b + 2 by omega]
      have e : (2 : ℚ) ^ (2 * (2 * k + 3) + 1) = 8 * 4 ^ (k + 1) * 4 ^ (k + 1) := by
        rw [show 2 * (2 * k + 3) + 1 = 3 + 2 * (k + 1) + 2 * (k + 1) by ring, pow_add, pow_add,
          pow_mul]; norm_num
      rw [e]
      linear_combination hs - (-(8 * 4 ^ (k + 1) * 4 ^ (k + 1)) : ℚ) * he)
    a b ha hb
  rw [sub_eq_zero.mp key]; ring

/-- `L0(1) = 1`, `L1(1) = 1/2`. -/
lemma L0_one : L0 1 = 1 := by simpa [poch_zero] using L0_X_pow 0

lemma L1_one : L1 1 = 1 / 2 := by
  rw [L1_apply, mul_one, map_sub, L0_one, show (X : ℚ[X]) = X ^ 1 by ring, L0_X_pow]
  simp [poch_succ, poch_zero]; norm_num

/-- **Lemma 3(c)**, even `n = 2m`: `G_ab = χ_n C(n,2a) C(n,2b) Ω(ε_a,ε_b)`, `χ_n = -2^(2n)`. -/
theorem lemma3c_even (m a b : ℕ) (ha : a ≤ m) (hb : b ≤ m) :
    G (2 * m) a b = -2 ^ (2 * (2 * m)) * ((2 * m).choose (2 * a) : ℚ)
      * ((2 * m).choose (2 * b) : ℚ) * Om Reven (eps m a) (eps m b) := by
  rw [lemma1]
  have key := chain m (fun a b => Ehat (2 * m) (gf (2 * m) (2 * a)) (gf (2 * m) (2 * b))
      - (-2 ^ (2 * (2 * m))) * Om Reven (eps m a) (eps m b))
    (fun a b _ _ => by
      rw [Ehat_anti, Om_anti Reven Reven_symm (eps m a)]; ring)
    (fun a b ha hb => by
      have he := eps_shift Reven m a b (by omega) (by omega)
      rw [Reven_apply] at he
      rw [show 2 * (a + 1) = 2 * a + 2 by omega, show 2 * (b + 1) = 2 * b + 2 by omega]
      rcases (by omega : m = 1 ∨ 2 ≤ m) with h1 | h2
      · subst h1
        obtain rfl : a = 0 := by omega
        obtain rfl : b = 0 := by omega
        have h2 := lemma2 0 0 0 le_rfl le_rfl
        have hc : (gf 0 0).coeff 0 = 1 := by simp [gf]
        rw [Finset.sum_range_one, Finset.sum_range_one, hc] at h2
        norm_num [dl] at h2
        simp only [eta, pow_zero, Nat.sub_self, mul_one, L0_one, L1_one] at he
        norm_num at h2 ⊢
        linear_combination h2 + 16 * he
      · obtain ⟨l, rfl⟩ : ∃ l, m = l + 2 := ⟨m - 2, by omega⟩
        have hs := spec_even l a b (by omega) (by omega)
        rw [show 2 * (l + 2) = 2 * l + 4 by omega] at *
        have c1 := central_L0 (l + 1) a (by omega)
        have c2 := central_L0 (l + 1) b (by omega)
        have c3 := central_L1_eta (l + 2) a (by omega)
        have c4 := central_L1_eta (l + 2) b (by omega)
        rw [show 2 * (l + 1) = 2 * l + 2 by omega, show l + 1 - a = l + 2 - 1 - a by omega,
          ← eta] at c1
        rw [show 2 * (l + 1) = 2 * l + 2 by omega, show l + 1 - b = l + 2 - 1 - b by omega,
          ← eta] at c2
        rw [show 2 * (l + 2) = 2 * l + 4 by omega] at c3 c4
        rw [c1, c2, c3, c4] at hs
        have e : (2 : ℚ) ^ (2 * (2 * l + 4)) = 4 * 4 ^ (l + 1) * 4 ^ (l + 2) := by
          rw [show 2 * (2 * l + 4) = 2 + 2 * (l + 1) + 2 * (l + 2) by ring, pow_add, pow_add,
            pow_mul, pow_mul]; norm_num
        rw [e]
        linear_combination hs - (-(4 * 4 ^ (l + 1) * 4 ^ (l + 2)) : ℚ) * he)
    a b ha hb
  rw [sub_eq_zero.mp key]; ring

/-! ## Remark (explicit splitting) and (T) -/

/-- `C_{αβ}(u^i,u^j) = -Σ_{l<i} L_α(u^l) L_β(u^(i+j-1-l))`. -/
noncomputable def Cab (La Lb : ℚ[X] →ₗ[ℚ] ℚ) : ℚ[X] →ₗ[ℚ] ℚ[X] →ₗ[ℚ] ℚ :=
  bf (fun i j => -∑ l ∈ range i, La (X ^ l) * Lb (X ^ (i + j - 1 - l)))

/-- `(L_α ⊗ L_β)[(g(ξ₁)-g(ξ₂))/(ξ₁-ξ₂) p(ξ₁) q(ξ₂)]`, written out with
`(ξ₁^k - ξ₂^k)/(ξ₁ - ξ₂) = Σ_{a<k} ξ₁^a ξ₂^(k-1-a)`:
`Σ_k g_k Σ_{a<k} L_α(u^a p) L_β(u^(k-1-a) q)`. -/
noncomputable def ddT (La Lb : ℚ[X] →ₗ[ℚ] ℚ) (g p q : ℚ[X]) : ℚ :=
  g.sum (fun k c => c * ∑ a ∈ range k, La (X ^ a * p) * Lb (X ^ (k - 1 - a) * q))

/-- (T) for `g = u`: `C(up,q) - C(p,uq) = -L_α(p) L_β(q)`. -/
theorem Cab_u (La Lb : ℚ[X] →ₗ[ℚ] ℚ) (p q : ℚ[X]) :
    Cab La Lb (X * p) q - Cab La Lb p (X * q) = -(La p * Lb q) := by
  have h : (Cab La Lb).comp (LinearMap.mulLeft ℚ X) - (Cab La Lb).compl₂ (LinearMap.mulLeft ℚ X)
      = -((LinearMap.mul ℚ ℚ).compl₁₂ La Lb) := by
    apply bil_ext; intro i j
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.compl₂_apply,
      LinearMap.mulLeft_apply, LinearMap.neg_apply, ← pow_succ', Cab, bf_X_pow,
      LinearMap.compl₁₂_apply, LinearMap.mul_apply']
    rw [show i + 1 + j = i + (j + 1) by omega, Finset.sum_range_succ,
      show i + (j + 1) - 1 - i = j by omega]
    ring
  have := DFunLike.congr_fun (DFunLike.congr_fun h p) q
  simpa using this

theorem Cab_pow (La Lb : ℚ[X] →ₗ[ℚ] ℚ) (k : ℕ) : ∀ p q : ℚ[X],
    Cab La Lb (X ^ k * p) q - Cab La Lb p (X ^ k * q)
      = -∑ a ∈ range k, La (X ^ a * p) * Lb (X ^ (k - 1 - a) * q) := by
  induction k with
  | zero => intro p q; simp
  | succ k ih =>
    intro p q
    have h1 := ih (X * p) q
    have h2 := Cab_u La Lb p (X ^ k * q)
    rw [show X ^ (k + 1) * p = X ^ k * (X * p) by ring, show X ^ (k + 1) * q = X * (X ^ k * q) by ring,
      Finset.sum_range_succ']
    simp only [pow_zero, one_mul, show k + 1 - 1 - 0 = k by omega]
    have e : ∀ a ∈ range k, La (X ^ (a + 1) * p) * Lb (X ^ (k + 1 - 1 - (a + 1)) * q)
        = La (X ^ a * (X * p)) * Lb (X ^ (k - 1 - a) * q) := by
      intro a _; rw [show k + 1 - 1 - (a + 1) = k - 1 - a by omega, pow_succ, mul_assoc]
    rw [Finset.sum_congr rfl e]
    linear_combination h1 + h2

/-- **(T)**: `C(gp,q) - C(p,gq) = -(L_α ⊗ L_β)[(g(ξ₁)-g(ξ₂))/(ξ₁-ξ₂) p(ξ₁) q(ξ₂)]` for every `g`. -/
theorem T_split (La Lb : ℚ[X] →ₗ[ℚ] ℚ) (g p q : ℚ[X]) :
    Cab La Lb (g * p) q - Cab La Lb p (g * q) = -ddT La Lb g p q := by
  induction g using Polynomial.induction_on' with
  | add f g hf hg =>
    unfold ddT at *
    rw [Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring), add_mul, add_mul,
      map_add, map_add, LinearMap.add_apply]
    linear_combination hf + hg
  | monomial n a =>
    unfold ddT
    rw [Polynomial.sum_monomial_index _ _ (by simp), ← C_mul_X_pow_eq_monomial, mul_assoc, mul_assoc,
      C_mul', C_mul', map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_sub, Cab_pow]
    ring

/-- the explicit splitting for even `n`: `Ω = C₁₀ - C₁₀ᵀ`. -/
theorem Om_even_eq (p q : ℚ[X]) :
    Om Reven p q = Cab L1 L0 p q - Cab L1 L0 q p := by
  have hz := lemma3b (p.natDegree + q.natDegree)
    (Om Reven - (Cab L1 L0 - (Cab L1 L0).flip))
    (fun x y _ _ => by
      simp only [LinearMap.sub_apply, LinearMap.flip_apply]
      rw [Om_anti Reven Reven_symm x y]; ring)
    (fun x y _ _ => by
      simp only [LinearMap.sub_apply, LinearMap.flip_apply]
      have h1 := Om_D Reven x y
      have h2 := Cab_u L1 L0 x y
      have h3 := Cab_u L1 L0 y x
      rw [Reven_apply] at h1
      linear_combination h1 - h2 - h3)
    p q (by omega) (by omega)
  simp only [LinearMap.sub_apply, LinearMap.flip_apply] at hz
  linear_combination hz

/-- the explicit splitting for odd `n`: `Ω = ½(C₁₁ - C₁₁ᵀ)`. -/
theorem Om_odd_eq (p q : ℚ[X]) :
    Om Rodd p q = (1 / 2) * (Cab L1 L1 p q - Cab L1 L1 q p) := by
  have hz := lemma3b (p.natDegree + q.natDegree)
    (Om Rodd - (1 / 2 : ℚ) • (Cab L1 L1 - (Cab L1 L1).flip))
    (fun x y _ _ => by
      simp only [LinearMap.sub_apply, LinearMap.flip_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [Om_anti Rodd Rodd_symm x y]; ring)
    (fun x y _ _ => by
      simp only [LinearMap.sub_apply, LinearMap.flip_apply, LinearMap.smul_apply, smul_eq_mul]
      have h1 := Om_D Rodd x y
      have h2 := Cab_u L1 L1 x y
      have h3 := Cab_u L1 L1 y x
      rw [Rodd_apply] at h1
      linear_combination h1 - (1 / 2 : ℚ) * h2 - (1 / 2 : ℚ) * h3)
    p q (by omega) (by omega)
  simp only [LinearMap.sub_apply, LinearMap.flip_apply, LinearMap.smul_apply, smul_eq_mul] at hz
  linear_combination hz

/-! ## Lemma 4 (`lem:ker`) -/

lemma ddT_eq_zero (La Lb : ℚ[X] →ₗ[ℚ] ℚ) (g p q : ℚ[X])
    (h : ∀ t, t ≤ g.natDegree → ∀ a < t, La (X ^ a * p) * Lb (X ^ (t - 1 - a) * q) = 0) :
    ddT La Lb g p q = 0 := by
  unfold ddT Polynomial.sum
  refine sum_eq_zero fun t ht => ?_
  dsimp only
  rw [sum_eq_zero (fun a ha => h t (le_natDegree_of_mem_supp t ht) a (mem_range.1 ha)), mul_zero]

/-- the three moves: `C(πpq,πr) - C(πr,πpq) = 0`. -/
theorem ker_core (La Lb : ℚ[X] →ₗ[ℚ] ℚ) (π p q r : ℚ[X]) (k : ℕ)
    (hp : p.natDegree ≤ k) (hq : q.natDegree ≤ k) (hr : r.natDegree ≤ 2 * k)
    (hA : ∀ i < k, La (π * p * X ^ i) = 0) (hB : ∀ i < k, Lb (π * q * X ^ i) = 0) :
    Cab La Lb (π * p * q) (π * r) - Cab La Lb (π * r) (π * p * q) = 0 := by
  have hA' : ∀ a < k, La (X ^ a * (π * p)) = 0 := fun a ha => by rw [← hA a ha]; ring_nf
  have hB' : ∀ a < k, Lb (X ^ a * (π * q)) = 0 := fun a ha => by rw [← hB a ha]; ring_nf
  have s1 := T_split La Lb q (π * p) (π * r)
  rw [ddT_eq_zero La Lb q _ _ (fun t ht a hat => by rw [hA' a (by omega), zero_mul]), neg_zero] at s1
  have s2 := T_split La Lb p (π * r) (π * q)
  rw [ddT_eq_zero La Lb p _ _ (fun t ht a hat => by rw [hB' (t - 1 - a) (by omega), mul_zero]),
    neg_zero] at s2
  have s3 := T_split La Lb r (π * p) (π * q)
  rw [ddT_eq_zero La Lb r _ _ (fun t ht a hat => by
    rcases (by omega : a < k ∨ t - 1 - a < k) with h | h
    · rw [hA' a h, zero_mul]
    · rw [hB' _ h, mul_zero]), neg_zero] at s3
  rw [show q * (π * p) = π * p * q by ring, show q * (π * r) = r * (π * q) by ring] at s1
  rw [show p * (π * r) = r * (π * p) by ring, show p * (π * q) = π * p * q by ring] at s2
  linear_combination s1 - s3 + s2


/-- **Lemma 4** (`lem:ker`), even `n`: if `deg p, deg q ≤ k`, `L1(π p u^i) = 0` and `L0(π q u^i) = 0`
for `i < k`, then `Ω(π p q, π r) = 0` for every `r ∈ P_{2k}`. -/
theorem lem_ker_even (π p q r : ℚ[X]) (k : ℕ)
    (hp : p.natDegree ≤ k) (hq : q.natDegree ≤ k) (hr : r.natDegree ≤ 2 * k)
    (h1 : ∀ i < k, L1 (π * p * X ^ i) = 0) (h0 : ∀ i < k, L0 (π * q * X ^ i) = 0) :
    Om Reven (π * p * q) (π * r) = 0 := by
  rw [Om_even_eq]; exact ker_core L1 L0 π p q r k hp hq hr h1 h0

/-- **Lemma 4** (`lem:ker`), odd `n` (`L⋆ = L1`, `q = p`). -/
theorem lem_ker_odd (π p r : ℚ[X]) (k : ℕ)
    (hp : p.natDegree ≤ k) (hr : r.natDegree ≤ 2 * k)
    (h1 : ∀ i < k, L1 (π * p * X ^ i) = 0) :
    Om Rodd (π * p * p) (π * r) = 0 := by
  rw [Om_odd_eq, ker_core L1 L1 π p p r k hp hp hr h1 h1, mul_zero]

/-! ## `lem:orth` (orthogonality via Pfaff–Saalschütz) -/

lemma poch_add (x : ℚ) (A j : ℕ) : poch x (A + j) = poch x A * poch (x + A) j := by
  induction j with
  | zero => simp [poch_zero]
  | succ j ih =>
    rw [← add_assoc, poch_succ, ih, poch_succ]; push_cast; ring

lemma fact_poch (N j : ℕ) : (((N + j).factorial : ℕ) : ℚ) = (N.factorial : ℚ) * poch ((N : ℚ) + 1) j := by
  induction j with
  | zero => simp [poch_zero]
  | succ j ih =>
    rw [← add_assoc, Nat.factorial_succ, poch_succ]; push_cast; rw [ih]; ring

lemma Bv_shift (A E j : ℕ) :
    Bv (A + j) E = Bv A E * poch ((A : ℚ) + 1 / 2) j / poch ((A : ℚ) + E + 1) j := by
  unfold Bv
  rw [poch_add, show A + j + E = (A + E) + j by omega, fact_poch, add_comm (1 / 2 : ℚ)]
  push_cast; ring

/-- `₂F₁(-k, b; c; u) = Σ_j (-k)_j (b)_j / ((c)_j j!) u^j`. -/
noncomputable def hyp2 (b c : ℚ) (k : ℕ) : ℚ[X] := ∑ j ∈ range (k + 1), C (v2 b c k j) * X ^ j

lemma natDegree_hyp2 (b c : ℚ) (k : ℕ) : (hyp2 b c k).natDegree ≤ k := by
  unfold hyp2
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (by rw [mem_range] at hj; omega)

lemma L0_hyp (A E : ℕ) (b c : ℚ) (k : ℕ) :
    L0 (X ^ A * (1 - X) ^ E * hyp2 b c k) = ∑ j ∈ range (k + 1), v2 b c k j * Bv (A + j) E := by
  unfold hyp2
  rw [Finset.mul_sum, map_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [show X ^ A * (1 - X) ^ E * (C (v2 b c k j) * X ^ j)
      = C (v2 b c k j) * (X ^ (A + j) * (1 - X) ^ E) by ring, C_mul', map_smul, L0_beta, smul_eq_mul]

lemma sum_Bv (A E : ℕ) (b c : ℚ) (k : ℕ) (hdd : (A : ℚ) + E + 1 = dd ((A : ℚ) + 1 / 2) b c k) :
    ∑ j ∈ range (k + 1), v2 b c k j * Bv (A + j) E = Bv A E * F3 ((A : ℚ) + 1 / 2) b c k := by
  unfold F3; rw [Finset.mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [Bv_shift, hdd]; unfold v2 t3; ring

lemma poch_pos_of (x : ℚ) (hx : 0 < x) (k : ℕ) : poch x k ≠ 0 := by
  rw [poch_eq_prod]; exact (Finset.prod_pos fun i _ => by positivity).ne'

/-- `π = u^s (1-u)^E`, `E = m - s - 2k`. -/
noncomputable def piW (m s k : ℕ) : ℚ[X] := X ^ s * (1 - X) ^ (m - s - 2 * k)

/-- `p = ₂F₁(-k, m+1-k; s+½; u)`. -/
noncomputable def pP (m s k : ℕ) : ℚ[X] := hyp2 ((m : ℚ) + 1 - k) ((s : ℚ) + 1 / 2) k

/-- `q = ₂F₁(-k, m-k; s+½; u)` (even `n`). -/
noncomputable def qP (m s k : ℕ) : ℚ[X] := hyp2 ((m : ℚ) - k) ((s : ℚ) + 1 / 2) k

/-- **`lem:orth`**, first half: `L1(π p u^i) = 0` for `0 ≤ i < k`. -/
theorem lem_orth_L1 (m s k : ℕ) (h : s + 2 * k ≤ m) (i : ℕ) (hi : i < k) :
    L1 (piW m s k * pP m s k * X ^ i) = 0 := by
  obtain ⟨e, rfl⟩ : ∃ e, m = s + 2 * k + e := ⟨m - s - 2 * k, by omega⟩
  rw [L1_apply, show (1 - X) * (piW (s + 2 * k + e) s k * pP (s + 2 * k + e) s k * X ^ i)
      = X ^ (s + i) * (1 - X) ^ (e + 1) * pP (s + 2 * k + e) s k by
        unfold piW; rw [show s + 2 * k + e - s - 2 * k = e by omega]; ring]
  unfold pP
  rw [L0_hyp, sum_Bv _ _ _ _ _ (by unfold dd; push_cast; ring),
    pfaff_saalschutz _ _ _ _ (poch_pos_of _ (by positivity) k)]
  · rw [show (s : ℚ) + 1 / 2 - ((s + i : ℕ) + 1 / 2) = -(i : ℚ) by push_cast; ring,
      poch_negnat i k hi]; simp
  · rw [poch_eq_prod, Finset.prod_ne_zero_iff]
    intro t ht
    have h1 : (t : ℚ) + 1 ≤ k := by exact_mod_cast mem_range.1 ht
    have h2 : (0 : ℚ) ≤ e := by positivity
    push_cast
    apply ne_of_lt; linarith

/-- **`lem:orth`**, second half (even `n`): `L0(π q u^i) = 0` for `0 ≤ i < k`. -/
theorem lem_orth_L0 (m s k : ℕ) (h : s + 2 * k ≤ m) (i : ℕ) (hi : i < k) :
    L0 (piW m s k * qP m s k * X ^ i) = 0 := by
  obtain ⟨e, rfl⟩ : ∃ e, m = s + 2 * k + e := ⟨m - s - 2 * k, by omega⟩
  rw [show piW (s + 2 * k + e) s k * qP (s + 2 * k + e) s k * X ^ i
      = X ^ (s + i) * (1 - X) ^ e * qP (s + 2 * k + e) s k by
        unfold piW; rw [show s + 2 * k + e - s - 2 * k = e by omega]; ring]
  unfold qP
  rw [L0_hyp, sum_Bv _ _ _ _ _ (by unfold dd; push_cast; ring),
    pfaff_saalschutz _ _ _ _ (poch_pos_of _ (by positivity) k)]
  · rw [show (s : ℚ) + 1 / 2 - ((s + i : ℕ) + 1 / 2) = -(i : ℚ) by push_cast; ring,
      poch_negnat i k hi]; simp
  · rw [poch_eq_prod, Finset.prod_ne_zero_iff]
    intro t ht
    have h1 : (t : ℚ) + 1 ≤ k := by exact_mod_cast mem_range.1 ht
    have h2 : (0 : ℚ) ≤ e := by positivity
    push_cast
    apply ne_of_lt; linarith

/-! ## Theorem K (`thm:K`) -/

/-- `b₁ = k + s - m - ½`. -/
noncomputable def b1 (m s k : ℕ) : ℚ := k + s - m - 1 / 2

/-- `g_i = (-k)_i (b)_i / ((s+½)_i i!)` (`b = b₁` or `b₂`). -/
noncomputable def gK (b : ℚ) (s k i : ℕ) : ℚ := v2 b ((s : ℚ) + 1 / 2) k i

/-- `d_ℓ = Σ_{i+i'=ℓ} g_i g'_{i'}`. -/
noncomputable def dK (b b' : ℚ) (s k l : ℕ) : ℚ :=
  ∑ i ∈ range (l + 1), gK b s k i * gK b' s k (l - i)

/-- `c_ℓ = d_ℓ / C(n, 2s+2ℓ)`. -/
noncomputable def cK (n : ℕ) (b b' : ℚ) (s k l : ℕ) : ℚ :=
  dK b b' s k l / (n.choose (2 * s + 2 * l) : ℚ)

/-- `(c_ℓ) ≠ 0` because `d_0 = 1`. -/
theorem dK_zero (b b' : ℚ) (s k : ℕ) : dK b b' s k 0 = 1 := by
  simp [dK, gK, v2_zero]

lemma v2_vanish (b c : ℚ) (k j : ℕ) (hj : k < j) : v2 b c k j = 0 := by
  simp [v2, poch_negnat k j hj]

lemma cauchy (g g' : ℕ → ℚ) (k : ℕ) (hg : ∀ j, k < j → g j = 0) (hg' : ∀ j, k < j → g' j = 0) :
    ∑ l ∈ range (2 * k + 1), C (∑ i ∈ range (l + 1), g i * g' (l - i)) * (-X) ^ l
        * ((1 : ℚ[X]) - X) ^ (2 * k - l)
      = (∑ j ∈ range (k + 1), C (g j) * (-X) ^ j * ((1 : ℚ[X]) - X) ^ (k - j))
        * (∑ j ∈ range (k + 1), C (g' j) * (-X) ^ j * ((1 : ℚ[X]) - X) ^ (k - j)) := by
  set f : ℕ → ℕ → ℚ[X] := fun i j => C (g i * g' j) * (-X) ^ (i + j) * ((1 : ℚ[X]) - X) ^ (2 * k - (i + j))
    with hf
  have hL : ∑ l ∈ range (2 * k + 1), C (∑ i ∈ range (l + 1), g i * g' (l - i)) * (-X) ^ l
        * ((1 : ℚ[X]) - X) ^ (2 * k - l)
      = ∑ l ∈ range (2 * k + 1), ∑ i ∈ range (l + 1), f i (l - i) := by
    refine sum_congr rfl fun l _ => ?_
    rw [map_sum, Finset.sum_mul, Finset.sum_mul]
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [hf]; dsimp only; rw [show i + (l - i) = l by omega]
  have hR : (∑ j ∈ range (k + 1), C (g j) * (-X) ^ j * ((1 : ℚ[X]) - X) ^ (k - j))
        * (∑ j ∈ range (k + 1), C (g' j) * (-X) ^ j * ((1 : ℚ[X]) - X) ^ (k - j))
      = ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1), f i j := by
    rw [Finset.sum_mul_sum]
    refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
    rw [mem_range] at hi hj
    rw [hf]; dsimp only
    rw [show 2 * k - (i + j) = (k - i) + (k - j) by omega, pow_add, pow_add, C_mul]; ring
  rw [hL, hR, Finset.sum_range_diag_flip]
  symm
  rw [Finset.sum_subset (range_mono (by omega : k + 1 ≤ 2 * k + 1))]
  · refine sum_congr rfl fun i hi => ?_
    by_cases hik : i ≤ k
    · exact Finset.sum_subset (range_mono (by omega)) fun j _ hj => by
        rw [mem_range, not_lt] at hj
        rw [hf]; dsimp only; rw [hg' j (by omega)]; simp
    · rw [Finset.sum_eq_zero, Finset.sum_eq_zero] <;> intro j _ <;> rw [hf] <;> dsimp only <;>
        rw [hg i (by omega)] <;> simp
  · intro i _ hi
    rw [mem_range, not_lt] at hi
    refine sum_eq_zero fun j _ => ?_
    rw [hf]; dsimp only; rw [hg i (by omega)]; simp

/-- `Σ_ℓ d_ℓ ε_{s+ℓ} = (-1)^s π (1-u)^{2k} Σ_ℓ d_ℓ τ^ℓ`, written polynomially. -/
lemma eps_sum (m s k : ℕ) (h : s + 2 * k ≤ m) (d : ℕ → ℚ) :
    ∑ l ∈ range (2 * k + 1), d l • eps m (s + l)
      = ((-1 : ℚ) ^ s) • (piW m s k * ∑ l ∈ range (2 * k + 1),
          C (d l) * (-X) ^ l * ((1 : ℚ[X]) - X) ^ (2 * k - l)) := by
  rw [Finset.mul_sum, Finset.smul_sum]
  refine sum_congr rfl fun l hl => ?_
  rw [mem_range] at hl
  unfold eps piW
  rw [show m - (s + l) = (m - s - 2 * k) + (2 * k - l) by omega]
  simp only [smul_eq_C_mul, map_mul, map_pow, map_neg, map_one, pow_add, neg_pow (X : ℚ[X])]
  ring

lemma eps_pi (m s k t : ℕ) (h : s + 2 * k ≤ m) (h1 : s ≤ t) (h2 : t ≤ s + 2 * k) :
    eps m t = piW m s k * (C ((-1 : ℚ) ^ t) * X ^ (t - s) * (1 - X) ^ (2 * k - (t - s))) := by
  unfold eps piW
  rw [smul_eq_C_mul, show m - t = (m - s - 2 * k) + (2 * k - (t - s)) by omega,
    show X ^ t = (X : ℚ[X]) ^ s * X ^ (t - s) by rw [← pow_add]; congr 1; omega, pow_add]
  ring

lemma natDegree_r (k s t : ℕ) (h1 : s ≤ t) (h2 : t ≤ s + 2 * k) :
    (C ((-1 : ℚ) ^ t) * X ^ (t - s) * ((1 : ℚ[X]) - X) ^ (2 * k - (t - s))).natDegree ≤ 2 * k := by
  have e1 : (C ((-1 : ℚ) ^ t) * X ^ (t - s)).natDegree ≤ t - s := natDegree_C_mul_X_pow_le ((-1 : ℚ) ^ t) (t - s)
  have e2 : (((1 : ℚ[X]) - X) ^ (2 * k - (t - s))).natDegree ≤ 2 * k - (t - s) := by
    have e3 : ((1 : ℚ[X]) - X).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
    exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (2 * k - (t - s)) e3)
  calc _ ≤ (C ((-1 : ℚ) ^ t) * X ^ (t - s)).natDegree
        + (((1 : ℚ[X]) - X) ^ (2 * k - (t - s))).natDegree := natDegree_mul_le
    _ ≤ 2 * k := by omega

lemma pfaffs (b : ℚ) (s k : ℕ) :
    ∑ j ∈ range (k + 1), C (gK b s k j) * (-X) ^ j * ((1 : ℚ[X]) - X) ^ (k - j)
      = hyp2 ((s : ℚ) + 1 / 2 - b) ((s : ℚ) + 1 / 2) k := by
  unfold gK hyp2
  exact pfaff_poly b _ k (poch_pos_of _ (by positivity) k)

/-- **Theorem K** (kernel vectors), odd `n = 2m+1` (`b₂ = b₁`):
`Σ_{ℓ=0}^{2k} c_ℓ G_{s+ℓ,t} = 0` for every `t ∈ {s, …, s+2k}`. -/
theorem thmK_odd (m s k : ℕ) (h : s + 2 * k ≤ m) (t : ℕ) (ht1 : s ≤ t) (ht2 : t ≤ s + 2 * k) :
    ∑ l ∈ range (2 * k + 1), cK (2 * m + 1) (b1 m s k) (b1 m s k) s k l * G (2 * m + 1) (s + l) t
      = 0 := by
  have hterm : ∀ l ∈ range (2 * k + 1), cK (2 * m + 1) (b1 m s k) (b1 m s k) s k l
        * G (2 * m + 1) (s + l) t
      = (-2 ^ (2 * (2 * m + 1) + 1) * ((2 * m + 1).choose (2 * t) : ℚ))
        * (dK (b1 m s k) (b1 m s k) s k l * Om Rodd (eps m (s + l)) (eps m t)) := by
    intro l hl
    rw [mem_range] at hl
    have hC : ((2 * m + 1).choose (2 * s + 2 * l) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    rw [lemma3c_odd m (s + l) t (by omega) (by omega), cK, show 2 * (s + l) = 2 * s + 2 * l by ring,
      div_mul_eq_mul_div, div_eq_iff hC]
    ring
  rw [sum_congr rfl hterm, ← Finset.mul_sum]
  have hA : ∑ l ∈ range (2 * k + 1), dK (b1 m s k) (b1 m s k) s k l * Om Rodd (eps m (s + l)) (eps m t)
      = Om Rodd (∑ l ∈ range (2 * k + 1), dK (b1 m s k) (b1 m s k) s k l • eps m (s + l)) (eps m t) := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hA, eps_sum m s k h, eps_pi m s k t h ht1 ht2]
  unfold dK
  rw [cauchy (gK _ s k) (gK _ s k) k (fun j hj => v2_vanish _ _ k j hj) (fun j hj => v2_vanish _ _ k j hj), pfaffs,
    show (s : ℚ) + 1 / 2 - b1 m s k = (m : ℚ) + 1 - k by unfold b1; ring, ← pP, ← mul_assoc (piW m s k) (pP m s k) (pP m s k),
    map_smul, LinearMap.smul_apply,
    lem_ker_odd (piW m s k) (pP m s k) _ k (natDegree_hyp2 _ _ _) (natDegree_r k s t ht1 ht2)
      (fun i hi => lem_orth_L1 m s k h i hi)]
  simp

/-- **Theorem K** (kernel vectors), even `n = 2m` (`b₂ = b₁ + 1`). -/
theorem thmK_even (m s k : ℕ) (h : s + 2 * k ≤ m) (t : ℕ) (ht1 : s ≤ t) (ht2 : t ≤ s + 2 * k) :
    ∑ l ∈ range (2 * k + 1), cK (2 * m) (b1 m s k) (b1 m s k + 1) s k l * G (2 * m) (s + l) t
      = 0 := by
  have hterm : ∀ l ∈ range (2 * k + 1), cK (2 * m) (b1 m s k) (b1 m s k + 1) s k l
        * G (2 * m) (s + l) t
      = (-2 ^ (2 * (2 * m)) * ((2 * m).choose (2 * t) : ℚ))
        * (dK (b1 m s k) (b1 m s k + 1) s k l * Om Reven (eps m (s + l)) (eps m t)) := by
    intro l hl
    rw [mem_range] at hl
    have hC : ((2 * m).choose (2 * s + 2 * l) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    rw [lemma3c_even m (s + l) t (by omega) (by omega), cK, show 2 * (s + l) = 2 * s + 2 * l by ring,
      div_mul_eq_mul_div, div_eq_iff hC]
    ring
  rw [sum_congr rfl hterm, ← Finset.mul_sum]
  have hA : ∑ l ∈ range (2 * k + 1), dK (b1 m s k) (b1 m s k + 1) s k l
        * Om Reven (eps m (s + l)) (eps m t)
      = Om Reven (∑ l ∈ range (2 * k + 1), dK (b1 m s k) (b1 m s k + 1) s k l • eps m (s + l))
          (eps m t) := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hA, eps_sum m s k h, eps_pi m s k t h ht1 ht2]
  unfold dK
  rw [cauchy (gK _ s k) (gK _ s k) k (fun j hj => v2_vanish _ _ k j hj) (fun j hj => v2_vanish _ _ k j hj), pfaffs,
    pfaffs, show (s : ℚ) + 1 / 2 - b1 m s k = (m : ℚ) + 1 - k by unfold b1; ring,
    show (s : ℚ) + 1 / 2 - (b1 m s k + 1) = (m : ℚ) - k by unfold b1; ring, ← pP, ← qP, ← mul_assoc (piW m s k) (pP m s k) (qP m s k),
    map_smul, LinearMap.smul_apply,
    lem_ker_even (piW m s k) (pP m s k) (qP m s k) _ k (natDegree_hyp2 _ _ _) (natDegree_hyp2 _ _ _) (natDegree_r k s t ht1 ht2)
      (fun i hi => lem_orth_L1 m s k h i hi) (fun i hi => lem_orth_L0 m s k h i hi)]
  simp

end Stage4

end Bali.GP

#print axioms Bali.GP.abs_central_L1
#print axioms Bali.GP.abs_central_L0
#print axioms Bali.GP.central_L1_eta
#print axioms Bali.GP.central_L0_eta
#print axioms Bali.GP.L0_beta
#print axioms Bali.GP.Om_anti
#print axioms Bali.GP.Om_D
#print axioms Bali.GP.lemma3b
#print axioms Bali.GP.lemma3c_odd
#print axioms Bali.GP.lemma3c_even
#print axioms Bali.GP.T_split
#print axioms Bali.GP.Om_even_eq
#print axioms Bali.GP.Om_odd_eq
#print axioms Bali.GP.lem_ker_even
#print axioms Bali.GP.lem_ker_odd
#print axioms Bali.GP.lem_orth_L1
#print axioms Bali.GP.lem_orth_L0
#print axioms Bali.GP.dK_zero
#print axioms Bali.GP.thmK_odd
#print axioms Bali.GP.thmK_even

/-! ## Stage 5 (2026-11-17): Pfaffian infrastructure (pfS, alternation, adjugate) -/

namespace Bali.GP

section PfInfra

/-- skip index `j`: `i ↦ i` for `i < j`, `i ↦ i + 1` otherwise. -/
def sk (j i : ℕ) : ℕ := if i < j then i else i + 1

/-- Pfaffian of `[g (e i) (e j)]_{i,j < 2n}` by expansion along the first row
(the same recursion as `Bali.Pf.pf`, see `pf_eq_pfS`). -/
def pfS (g : ℕ → ℕ → ℚ) : ℕ → (ℕ → ℕ) → ℚ
  | 0, _ => 1
  | n + 1, e => ∑ j ∈ range (2 * n + 1), (-1) ^ j * g (e 0) (e (j + 1)) * pfS g n (fun i => e (sk j i + 1))

lemma pfS_succ (g : ℕ → ℕ → ℚ) (n : ℕ) (e : ℕ → ℕ) : pfS g (n + 1) e =
    ∑ j ∈ range (2 * n + 1), (-1) ^ j * g (e 0) (e (j + 1)) * pfS g n (fun i => e (sk j i + 1)) := rfl

lemma le_sk (j i : ℕ) : i ≤ sk j i := by unfold sk; split_ifs <;> omega

theorem pfS_congr (g : ℕ → ℕ → ℚ) : ∀ (n : ℕ) (e e' : ℕ → ℕ), (∀ i < 2 * n, e i = e' i) →
    pfS g n e = pfS g n e'
  | 0, _, _, _ => rfl
  | n + 1, e, e', h => by
    rw [pfS_succ, pfS_succ]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [h 0 (by omega), h (j + 1) (by omega),
      pfS_congr g n _ _ (fun i hi => h _ (by unfold sk; split_ifs <;> omega))]

/-- `pfS` only uses `g` on the entries of the sequence. -/
theorem pfS_congr_g : ∀ (n : ℕ) (g g' : ℕ → ℕ → ℚ) (e : ℕ → ℕ),
    (∀ i j, i < 2 * n → j < 2 * n → g (e i) (e j) = g' (e i) (e j)) → pfS g n e = pfS g' n e
  | 0, _, _, _, _ => rfl
  | n + 1, g, g', e, h => by
    rw [pfS_succ, pfS_succ]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [h 0 (j + 1) (by omega) (by omega),
      pfS_congr_g n g g' _ (fun i i' hi hi' => h _ _ (by unfold sk; split_ifs <;> omega)
        (by unfold sk; split_ifs <;> omega))]

theorem pfS_comp (g : ℕ → ℕ → ℚ) (f : ℕ → ℕ) : ∀ (n : ℕ) (h : ℕ → ℕ),
    pfS g n (fun i => f (h i)) = pfS (fun a b => g (f a) (f b)) n h
  | 0, _ => rfl
  | n + 1, h => by
    rw [pfS_succ, pfS_succ]
    refine sum_congr rfl fun j _ => ?_
    rw [pfS_comp g f n]

lemma succAbove_val {n : ℕ} (j : Fin (n + 1)) (i : Fin n) : ((j.succAbove i : Fin (n + 1)) : ℕ) = sk j i := by
  unfold Fin.succAbove sk
  by_cases h : (i : ℕ) < j
  · rw [if_pos (by rw [Fin.lt_def]; simpa using h), if_pos h]; simp
  · rw [if_neg (by rw [Fin.lt_def]; simpa using h), if_neg h]; simp

/-- Bridge to the project's Pfaffian `Bali.Pf.pf` (first-row recursion on `Fin (2n)`). -/
theorem pf_eq_pfS (g : ℕ → ℕ → ℚ) : ∀ (n : ℕ) (e : ℕ → ℕ),
    Bali.Pf.pf n (Matrix.of fun i j : Fin (2 * n) => g (e i) (e j)) = pfS g n e
  | 0, e => rfl
  | n + 1, e => by
    rw [pfS_succ, ← Fin.sum_univ_eq_sum_range
      (fun j => (-1) ^ j * g (e 0) (e (j + 1)) * pfS g n (fun i => e (sk j i + 1))) (2 * n + 1)]
    simp only [Bali.Pf.pf]
    refine Fintype.sum_congr _ _ fun j => ?_
    have hs : (Matrix.of fun i j : Fin (2 * (n + 1)) => g (e i) (e j)).submatrix
        (fun i => (j.succAbove i).succ) (fun i => (j.succAbove i).succ)
        = Matrix.of fun a b : Fin (2 * n) => g (e (sk j a + 1)) (e (sk j b + 1)) := by
      ext a b; simp [Matrix.submatrix_apply, Fin.val_succ, succAbove_val]
    rw [hs, pf_eq_pfS g n (fun i => e (sk j i + 1))]
    simp [Fin.val_succ]

/-! ### Alternation: an adjacent transposition changes the sign -/

/-- adjacent transposition `p ↔ p + 1` of `ℕ`. -/
def tw (p x : ℕ) : ℕ := if x = p then p + 1 else if x = p + 1 then p else x

lemma sum_tw (F : ℕ → ℚ) (N p : ℕ) (hp : p + 1 < N) :
    ∑ j ∈ range N, F (tw p j) = ∑ j ∈ range N, F j := by
  apply Finset.sum_nbij' (tw p) (tw p)
  · intro x hx; simp only [mem_range] at hx ⊢; unfold tw; split_ifs <;> omega
  · intro x hx; simp only [mem_range] at hx ⊢; unfold tw; split_ifs <;> omega
  · intro x _; unfold tw; split_ifs <;> omega
  · intro x _; unfold tw; split_ifs <;> omega
  · intro x _; rfl

/-- the double first-row expansion (rows 0 and 1 removed). -/
noncomputable def Dbl (g : ℕ → ℕ → ℚ) (n : ℕ) (e : ℕ → ℕ) : ℚ :=
  ∑ x ∈ range (2 * n + 2) ×ˢ range (2 * n + 1),
    (-1) ^ (x.1 + 1 + x.2) * g (e 0) (e (x.1 + 2)) * g (e 1) (e (sk (x.1 + 1) (x.2 + 1) + 1))
      * pfS g n (fun i => e (sk (x.1 + 1) (sk x.2 i + 1) + 1))

lemma pfS_two (g : ℕ → ℕ → ℚ) (n : ℕ) (e : ℕ → ℕ) :
    pfS g (n + 2) e = g (e 0) (e 1) * pfS g (n + 1) (fun i => e (i + 2)) + Dbl g n e := by
  rw [pfS_succ, show 2 * (n + 1) + 1 = 2 * n + 2 + 1 by ring, sum_range_succ', add_comm]
  congr 1
  · simp [sk]
  · unfold Dbl
    rw [sum_product]
    refine sum_congr rfl fun j _ => ?_
    rw [pfS_succ, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    have h0 : sk (j + 1) 0 = 0 := by simp [sk]
    simp only [h0, zero_add]
    ring

theorem pfS_tw0 (g : ℕ → ℕ → ℚ) (hg : ∀ a b, g a b = -g b a) (n : ℕ) (e : ℕ → ℕ) :
    pfS g (n + 1) (fun x => e (tw 0 x)) = -pfS g (n + 1) e := by
  have t0 : tw 0 0 = 1 := by simp [tw]
  have t1 : tw 0 1 = 0 := by simp [tw]
  have tge : ∀ x, 2 ≤ x → tw 0 x = x := by intro x hx; unfold tw; split_ifs <;> omega
  rcases n with _ | n
  · simp [pfS, t0, t1]
    try exact hg _ _
  rw [pfS_two, pfS_two, t0, t1, hg (e 1) (e 0)]
  have hP : pfS g (n + 1) (fun i => e (tw 0 (i + 2))) = pfS g (n + 1) (fun i => e (i + 2)) := by
    have : (fun i => e (tw 0 (i + 2))) = (fun i => e (i + 2)) := funext fun i => by rw [tge _ (by omega)]
    rw [this]
  rw [hP]
  have hD : Dbl g n (fun x => e (tw 0 x)) = -Dbl g n e := by
    unfold Dbl
    rw [← sum_neg_distrib]
    apply Finset.sum_nbij' (fun x => if x.2 < x.1 then (x.2, x.1 - 1) else (x.2 + 1, x.1))
      (fun x => if x.2 < x.1 then (x.2, x.1 - 1) else (x.2 + 1, x.1))
    · rintro ⟨j, l⟩ hx
      simp only [mem_product, mem_range] at hx ⊢
      split_ifs <;> simp <;> omega
    · rintro ⟨j, l⟩ hx
      simp only [mem_product, mem_range] at hx ⊢
      split_ifs <;> simp <;> omega
    · rintro ⟨j, l⟩ _
      by_cases h : l < j
      · simp only [if_pos h]; rw [if_neg (by omega)]; ext <;> simp <;> omega
      · simp only [if_neg h]; rw [if_pos (by omega)]; ext <;> simp <;> omega
    · rintro ⟨j, l⟩ _
      by_cases h : l < j
      · simp only [if_pos h]; rw [if_neg (by omega)]; ext <;> simp <;> omega
      · simp only [if_neg h]; rw [if_pos (by omega)]; ext <;> simp <;> omega
    · rintro ⟨j, l⟩ _
      have a1 : tw 0 (j + 2) = j + 2 := tge _ (by omega)
      have a2 : tw 0 (sk (j + 1) (l + 1) + 1) = sk (j + 1) (l + 1) + 1 := tge _ (by have := le_sk (j + 1) (l + 1); omega)
      have a3 : (fun i => e (tw 0 (sk (j + 1) (sk l i + 1) + 1))) = (fun i => e (sk (j + 1) (sk l i + 1) + 1)) := by
        funext i; rw [tge _ (by have := le_sk (j + 1) (sk l i + 1); omega)]
      simp only [t0, t1, a1, a2, a3]
      by_cases h : l < j
      · simp only [if_pos h]
        have b1 : sk (j + 1) (l + 1) + 1 = l + 2 := by unfold sk; split_ifs <;> omega
        have b2 : sk (l + 1) (j - 1 + 1) + 1 = j + 2 := by unfold sk; split_ifs <;> omega
        have b3 : (fun i => e (sk (l + 1) (sk (j - 1) i + 1) + 1)) = (fun i => e (sk (j + 1) (sk l i + 1) + 1)) := by
          funext i; congr 1; unfold sk; split_ifs <;> omega
        rw [b1, b2, b3, show l + 1 + (j - 1) = j + l by omega, show j + 1 + l = j + l + 1 by ring, pow_succ]
        ring
      · simp only [if_neg h]
        have b1 : sk (j + 1) (l + 1) + 1 = l + 3 := by unfold sk; split_ifs <;> omega
        have b2 : sk (l + 1 + 1) (j + 1) + 1 = j + 2 := by unfold sk; split_ifs <;> omega
        have b3 : (fun i => e (sk (l + 1 + 1) (sk j i + 1) + 1)) = (fun i => e (sk (j + 1) (sk l i + 1) + 1)) := by
          funext i; congr 1; unfold sk; split_ifs <;> omega
        rw [b1, b2, b3, show l + 1 + 1 + j = j + 1 + l + 1 by ring, pow_succ, show l + 1 + 2 = l + 3 by ring]
        ring
  rw [hD]; ring

theorem pfS_tw (g : ℕ → ℕ → ℚ) (hg : ∀ a b, g a b = -g b a) :
    ∀ (n : ℕ) (e : ℕ → ℕ) (p : ℕ), p + 1 < 2 * n → pfS g n (fun x => e (tw p x)) = -pfS g n e
  | 0, _, _, hp => by omega
  | n + 1, e, 0, _ => pfS_tw0 g hg n e
  | n + 1, e, q + 1, hp => by
    rw [pfS_succ, pfS_succ, ← sum_tw _ (2 * n + 1) q (by omega), ← sum_neg_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    have h0 : tw (q + 1) 0 = 0 := by simp [tw]
    have h1 : ∀ x, tw (q + 1) (x + 1) = tw q x + 1 := by intro x; unfold tw; split_ifs <;> omega
    simp only [h0, h1]
    by_cases hjq : j = q
    · subst hjq
      have a1 : tw j j = j + 1 := by simp [tw]
      have a2 : tw j (j + 1) = j := by simp [tw]
      rw [a1, a2]
      have hm : (fun i => e (tw j (sk (j + 1) i) + 1)) = (fun i => e (sk j i + 1)) := by
        funext i; congr 2; unfold tw sk; split_ifs <;> omega
      rw [hm, pow_succ]; ring
    by_cases hjq1 : j = q + 1
    · subst hjq1
      have a1 : tw q q = q + 1 := by simp [tw]
      have a2 : tw q (q + 1) = q := by simp [tw]
      rw [a2, a1]
      have hm : (fun i => e (tw q (sk q i) + 1)) = (fun i => e (sk (q + 1) i + 1)) := by
        funext i; congr 2; unfold tw sk; split_ifs <;> omega
      rw [hm]; ring
    have htj : tw q j = j := by unfold tw; split_ifs <;> omega
    simp only [htj]
    set p' := if j < q then q - 1 else q with hp'
    have hm : (fun i => e (tw q (sk j i) + 1)) = (fun x => (fun i => e (sk j i + 1)) (tw p' x)) := by
      funext i; congr 2; rw [hp']; unfold tw sk; split_ifs <;> omega
    rw [hm]
    rw [pfS_tw g hg n (fun i => e (sk j i + 1)) p' (by rw [hp']; split_ifs <;> omega)]
    ring

/-- two equal entries in the sequence: the Pfaffian vanishes. -/
theorem pfS_rep (g : ℕ → ℕ → ℚ) (hg : ∀ a b, g a b = -g b a) (n : ℕ) :
    ∀ (q : ℕ) (e : ℕ → ℕ) (p : ℕ), p < q → q < 2 * n → e p = e q → pfS g n e = 0 := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro e p hpq hq hpe
    by_cases hq1 : q = p + 1
    · subst hq1
      have h := pfS_tw g hg n e p hq
      have he : (fun x => e (tw p x)) = e := by
        funext x; unfold tw; split_ifs with h1 h2
        · rw [h1, hpe]
        · rw [h2, hpe]
        · rfl
      rw [he] at h; linarith
    · have h := pfS_tw g hg n e (q - 1) (by omega)
      have h2 := ih (q - 1) (by omega) (fun x => e (tw (q - 1) x)) p (by omega) (by omega)
        (by
          show e (tw (q - 1) p) = e (tw (q - 1) (q - 1))
          rw [show tw (q - 1) p = p by unfold tw; split_ifs <;> omega,
            show tw (q - 1) (q - 1) = q by unfold tw; split_ifs <;> omega, hpe])
      rw [h2] at h; linarith

/-! ### The Pfaffian adjugate of an odd skew matrix -/

/-- `v_ℓ = (-1)^ℓ Pf Y[∖ℓ]` for `Y = [g (e i) (e j)]_{i,j ≤ 2k}`. -/
noncomputable def adjv (g : ℕ → ℕ → ℚ) (k : ℕ) (e : ℕ → ℕ) (l : ℕ) : ℚ :=
  (-1) ^ l * pfS g k (fun i => e (sk l i))

/-- **Adjugate, `Yv = 0`** (bordering by a copy of row `t`, two equal rows). -/
theorem adj_ker (g : ℕ → ℕ → ℚ) (hg : ∀ a b, g a b = -g b a) (k : ℕ) (e : ℕ → ℕ) (t : ℕ)
    (ht : t < 2 * k + 1) :
    ∑ l ∈ range (2 * k + 1), g (e t) (e l) * adjv g k e l = 0 := by
  have h := pfS_rep g hg (k + 1) (t + 1) (fun i => if i = 0 then e t else e (i - 1)) 0 (by omega)
    (by omega) (by simp)
  rw [pfS_succ] at h
  rw [← h]
  refine sum_congr rfl fun l _ => ?_
  unfold adjv
  simp only [if_pos rfl, Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false, if_true, ite_true]
  ring

lemma sum_skip (F : ℕ → ℚ) : ∀ (N l : ℕ), l ≤ N →
    ∑ i ∈ range (N + 1), F i = F l + ∑ j ∈ range N, F (sk l j)
  | 0, l, hl => by
    obtain rfl : l = 0 := by omega
    simp
  | N + 1, l, hl => by
    by_cases h : l ≤ N
    · rw [sum_range_succ, sum_skip F N l h, sum_range_succ, add_assoc]
      congr 2; unfold sk; rw [if_neg (by omega)]
    · obtain rfl : l = N + 1 := by omega
      rw [sum_range_succ, add_comm]
      congr 1
      refine sum_congr rfl fun j hj => ?_
      rw [mem_range] at hj
      unfold sk; rw [if_pos hj]

/-- an even skew matrix with non-zero Pfaffian has trivial kernel (over `ℚ`; via the adjugate of a
bordered odd matrix and a sum of squares). -/
theorem even_ker (g : ℕ → ℕ → ℚ) (hg : ∀ a b, g a b = -g b a) (k : ℕ) (f : ℕ → ℕ)
    (hpf : pfS g k f ≠ 0) (x : ℕ → ℚ)
    (hx : ∀ i < 2 * k, ∑ j ∈ range (2 * k), g (f i) (f j) * x j = 0) :
    ∀ j < 2 * k, x j = 0 := by
  classical
  let g' : ℕ → ℕ → ℚ := fun a b =>
    if a < 2 * k ∧ b < 2 * k then g (f a) (f b)
    else if a < 2 * k ∧ b = 2 * k then x a
    else if a = 2 * k ∧ b < 2 * k then -x b else 0
  have hg' : ∀ a b, g' a b = -g' b a := by
    intro a b
    simp only [g']
    split_ifs <;> first | omega | (rw [hg]) | simp | ring
  -- the bordered odd matrix on positions `0..2k`
  have hu : adjv g' k (fun i => i) (2 * k) = pfS g k f := by
    unfold adjv
    rw [show ((-1 : ℚ) ^ (2 * k)) = 1 by rw [pow_mul]; simp, one_mul]
    rw [pfS_congr g' k _ (fun i => i) (fun i hi => by unfold sk; rw [if_pos hi])]
    have : pfS g' k (fun i => i) = pfS (fun a b => g (f a) (f b)) k (fun i => i) :=
      pfS_congr_g k _ _ _ (fun i j hi hj => by simp [g', hi, hj])
    rw [this]
    exact (pfS_comp g f k (fun i => i)).symm
  set u := adjv g' k (fun i => i) with hu_def
  have hrow : ∀ t < 2 * k, ∑ l ∈ range (2 * k), g (f t) (f l) * u l + x t * u (2 * k) = 0 := by
    intro t ht
    have h := adj_ker g' hg' k (fun i => i) t (by omega)
    rw [sum_range_succ] at h
    rw [← h]
    congr 1
    · refine sum_congr rfl fun l hl => ?_
      rw [mem_range] at hl
      have e1 : g' t l = g (f t) (f l) := by simp [g', ht, hl]
      rw [e1]
    · have e2 : g' t (2 * k) = x t := by simp [g', ht]
      rw [e2]
  have hz : ∑ t ∈ range (2 * k), x t * ∑ l ∈ range (2 * k), g (f t) (f l) * u l = 0 := by
    have : ∑ t ∈ range (2 * k), x t * ∑ l ∈ range (2 * k), g (f t) (f l) * u l
        = -∑ l ∈ range (2 * k), u l * ∑ t ∈ range (2 * k), g (f l) (f t) * x t := by
      simp_rw [mul_sum]
      rw [sum_comm, ← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun t _ => ?_
      rw [hg (f t) (f l)]; ring
    rw [this, sum_eq_zero (fun l hl => by rw [hx l (mem_range.1 hl), mul_zero]), neg_zero]
  have hsum : ∑ t ∈ range (2 * k), x t * (∑ l ∈ range (2 * k), g (f t) (f l) * u l + x t * u (2 * k))
      = ∑ t ∈ range (2 * k), x t * ∑ l ∈ range (2 * k), g (f t) (f l) * u l
        + u (2 * k) * ∑ t ∈ range (2 * k), x t ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_
    ring
  rw [sum_eq_zero (fun t ht => by rw [hrow t (mem_range.1 ht), mul_zero]), hz, zero_add] at hsum
  have hsq : ∑ t ∈ range (2 * k), x t ^ 2 = 0 := by
    rcases mul_eq_zero.1 hsum.symm with h | h
    · exact absurd (hu ▸ h) hpf
    · exact h
  intro j hj
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).1 hsq j (mem_range.2 hj)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

/-- **Adjugate, kernel**: if `v_{ℓ₀} ≠ 0` then every kernel vector `c` of the odd skew matrix
`Y = [g (e t) (e ℓ)]_{t,ℓ ≤ 2k}` is proportional to `v`: `v_{ℓ₀} c = c_{ℓ₀} v`
(i.e. `ker Y = span v`). -/
theorem odd_ker_span (g : ℕ → ℕ → ℚ) (hg : ∀ a b, g a b = -g b a) (k : ℕ) (e : ℕ → ℕ) (l0 : ℕ)
    (hl0 : l0 ≤ 2 * k) (hv : adjv g k e l0 ≠ 0) (c : ℕ → ℚ)
    (hc : ∀ t < 2 * k + 1, ∑ l ∈ range (2 * k + 1), g (e t) (e l) * c l = 0) :
    ∀ l < 2 * k + 1, adjv g k e l0 * c l = c l0 * adjv g k e l := by
  set w : ℕ → ℚ := fun l => adjv g k e l0 * c l - c l0 * adjv g k e l with hw
  have hwk : ∀ t < 2 * k + 1, ∑ l ∈ range (2 * k + 1), g (e t) (e l) * w l = 0 := by
    intro t ht
    have h1 := hc t ht
    have h2 := adj_ker g hg k e t ht
    have : ∑ l ∈ range (2 * k + 1), g (e t) (e l) * w l
        = adjv g k e l0 * ∑ l ∈ range (2 * k + 1), g (e t) (e l) * c l
          - c l0 * ∑ l ∈ range (2 * k + 1), g (e t) (e l) * adjv g k e l := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun l _ => ?_
      simp only [hw]; ring
    rw [this, h1, h2]; ring
  have hw0 : w l0 = 0 := by simp only [hw]; ring
  have hpf : pfS g k (fun i => e (sk l0 i)) ≠ 0 := fun h => hv (by unfold adjv; rw [h, mul_zero])
  have hx := even_ker g hg k (fun i => e (sk l0 i)) hpf (fun j => w (sk l0 j)) (by
    intro i hi
    have := hwk (sk l0 i) (by unfold sk; split_ifs <;> omega)
    rw [sum_skip _ (2 * k) l0 hl0, hw0, mul_zero, zero_add] at this
    exact this)
  intro l hl
  have hwl : w l = 0 := by
    by_cases h : l = l0
    · rw [h]; exact hw0
    by_cases h' : l < l0
    · have := hx l (by omega)
      simpa [sk, h'] using this
    · have := hx (l - 1) (by omega)
      have e1 : sk l0 (l - 1) = l := by unfold sk; split_ifs <;> omega
      simpa [e1] using this
  simp only [hw] at hwl
  linarith

end PfInfra

end Bali.GP

/-! ## Stage 5 (2026-11-17): ratio (i) and positivity; Step 4 of (z) -/

namespace Bali.GP

section Stage5

/-- `G` is antisymmetric. -/
theorem G_anti (n a b : ℕ) : G n b a = -G n a b := by
  unfold G brB
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun x' _ => ?_
  split_ifs <;> ring

/-- `W(s,k) = Pf G[s..s+2k-1]`, `W(s,0) = 1`. -/
noncomputable def W (n s k : ℕ) : ℚ := pfS (G n) k (fun i => s + i)

/-- `W` is the project's Pfaffian `Bali.Pf.pf` of the window. -/
theorem W_eq_pf (n s k : ℕ) :
    W n s k = Bali.Pf.pf k (Matrix.of fun i j : Fin (2 * k) => G n (s + i) (s + j)) :=
  (pf_eq_pfS (G n) k (fun i => s + i)).symm

theorem W_zero (n s : ℕ) : W n s 0 = 1 := rfl

lemma adjv_first (n s k : ℕ) : adjv (G n) k (fun i => s + i) 0 = W n (s + 1) k := by
  unfold adjv W
  rw [pow_zero, one_mul]
  congr 1; funext i; simp [sk]; ring

lemma adjv_last (n s k : ℕ) : adjv (G n) k (fun i => s + i) (2 * k) = W n s k := by
  unfold adjv W
  rw [show ((-1 : ℚ) ^ (2 * k)) = 1 by rw [pow_mul]; simp, one_mul]
  exact pfS_congr _ k _ _ (fun i hi => by simp [sk, hi])

/-- The adjugate paragraph applied to the window `G[s..s+2k]`: a kernel vector `c` with `c_0 ≠ 0`
and `W(s,k) ≠ 0` gives `c_{2k} ≠ 0` and `W(s+1,k)/W(s,k) = c_0/c_{2k}`. -/
theorem ratio_of_ker (n s k : ℕ) (c : ℕ → ℚ)
    (hc : ∀ t ≤ 2 * k, ∑ l ∈ range (2 * k + 1), c l * G n (s + l) (s + t) = 0)
    (hW : W n s k ≠ 0) (hc0 : c 0 ≠ 0) :
    c (2 * k) ≠ 0 ∧ W n (s + 1) k / W n s k = c 0 / c (2 * k) := by
  have key := odd_ker_span (G n) (fun a b => G_anti n b a) k (fun i => s + i) (2 * k) le_rfl
    (by rw [adjv_last]; exact hW) c (by
      intro t ht
      rw [← neg_eq_zero, ← hc t (by omega), ← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      rw [G_anti n (s + l) (s + t)]; ring) 0 (by omega)
  rw [adjv_last, adjv_first] at key
  have hc2 : c (2 * k) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at key; exact mul_ne_zero hW hc0 key
  refine ⟨hc2, ?_⟩
  rw [div_eq_div_iff hW hc2]
  linear_combination -key

lemma dK_top (b b' : ℚ) (s k : ℕ) : dK b b' s k (2 * k) = gK b s k k * gK b' s k k := by
  unfold dK
  rw [Finset.sum_eq_single k]
  · rw [show 2 * k - k = k by omega]
  · intro i hi hik
    rw [mem_range] at hi
    rcases lt_or_gt_of_ne hik with h | h
    · rw [show gK b' s k (2 * k - i) = 0 from v2_vanish _ _ k _ (by omega), mul_zero]
    · rw [show gK b s k i = 0 from v2_vanish _ _ k _ h, zero_mul]
  · intro h; exact absurd (mem_range.2 (by omega)) h

lemma gK_top (b : ℚ) (s k : ℕ) : gK b s k k = (-1) ^ k * poch b k / poch ((s : ℚ) + 1 / 2) k := by
  unfold gK v2
  rw [poch_negnat_desc, Nat.descFactorial_self]
  have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
  have h2 := poch_pos_of ((s : ℚ) + 1 / 2) (by positivity) k
  field_simp

lemma poch_sign (b : ℚ) : ∀ k : ℕ, b + k - 1 < 0 → 0 < (-1) ^ k * poch b k
  | 0, _ => by simp [poch_zero]
  | k + 1, h => by
    push_cast at h
    have ih := poch_sign b k (by linarith)
    rw [poch_succ, show ((-1 : ℚ) ^ (k + 1)) * (poch b k * (b + k)) = ((-1) ^ k * poch b k) * (-(b + k)) by ring]
    exact mul_pos ih (by linarith)

lemma poch_pair_pos (b b' : ℚ) (k : ℕ) (hb : b + k - 1 < 0) (hb' : b' + k - 1 < 0) :
    0 < poch b k * poch b' k := by
  have e : ((-1 : ℚ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have : poch b k * poch b' k = ((-1) ^ k * poch b k) * ((-1) ^ k * poch b' k) := by
    linear_combination (-(poch b k * poch b' k)) * e
  rw [this]; exact mul_pos (poch_sign b k hb) (poch_sign b' k hb')

/-- the right-hand side of `eq:i`. -/
noncomputable def ratioI (n s k : ℕ) (b b' : ℚ) : ℚ :=
  (n.choose (2 * s + 4 * k) : ℚ) / (n.choose (2 * s) : ℚ) * (poch ((s : ℚ) + 1 / 2) k ^ 2 / (poch b k * poch b' k))

theorem ratioI_pos (n s k : ℕ) (b b' : ℚ) (hn : 2 * s + 4 * k ≤ n) (hb : b + k - 1 < 0) (hb' : b' + k - 1 < 0) :
    0 < ratioI n s k b b' := by
  unfold ratioI
  have h1 : (0 : ℚ) < n.choose (2 * s + 4 * k) := by exact_mod_cast Nat.choose_pos hn
  have h2 : (0 : ℚ) < n.choose (2 * s) := by exact_mod_cast Nat.choose_pos (by omega)
  have h3 : poch ((s : ℚ) + 1 / 2) k ≠ 0 := poch_pos_of _ (by positivity) k
  have h4 : 0 < poch ((s : ℚ) + 1 / 2) k ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h3))
  have h5 := poch_pair_pos b b' k hb hb'
  positivity

theorem ratio_core (n s k : ℕ) (b b' : ℚ)
    (hK : ∀ t ≤ 2 * k, ∑ l ∈ range (2 * k + 1), cK n b b' s k l * G n (s + l) (s + t) = 0)
    (hn : 2 * s + 4 * k ≤ n) (hb : b + k - 1 < 0) (hb' : b' + k - 1 < 0) (hW : W n s k ≠ 0) :
    W n (s + 1) k / W n s k = ratioI n s k b b' := by
  have hC0 : (n.choose (2 * s) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC1 : (n.choose (2 * s + 4 * k) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hn).ne'
  have hc0 : cK n b b' s k 0 ≠ 0 := by
    unfold cK; rw [dK_zero, mul_zero, add_zero]; exact one_div_ne_zero hC0
  obtain ⟨_, hr⟩ := ratio_of_ker n s k _ hK hW hc0
  rw [hr]
  have h3 : poch ((s : ℚ) + 1 / 2) k ≠ 0 := poch_pos_of _ (by positivity) k
  have hbb := (poch_pair_pos b b' k hb hb').ne'
  have hb0 : poch b k ≠ 0 := left_ne_zero_of_mul hbb
  have hb0' : poch b' k ≠ 0 := right_ne_zero_of_mul hbb
  have e : ((-1 : ℚ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  unfold cK ratioI
  rw [dK_zero, dK_top, gK_top, gK_top, mul_zero, add_zero, show 2 * s + 2 * (2 * k) = 2 * s + 4 * k by ring]
  rw [show (-1 : ℚ) ^ k * poch b k / poch ((s : ℚ) + 1 / 2) k * ((-1) ^ k * poch b' k / poch ((s : ℚ) + 1 / 2) k)
      = ((-1 : ℚ) ^ k) ^ 2 * (poch b k * poch b' k) / poch ((s : ℚ) + 1 / 2) k ^ 2 by ring, e, one_mul]
  field_simp
  try ring

lemma b1_neg (m s k : ℕ) (h : s + 2 * k ≤ m) : b1 m s k + 1 + k - 1 < 0 := by
  unfold b1
  have : (s : ℚ) + 2 * k ≤ m := by exact_mod_cast h
  linarith

/-- **Theorem `thm:ratios`, `eq:i`**, odd `n = 2m+1` (`b₂ = b₁`): for `s+2k ≤ m` and `W(s,k) ≠ 0`,
`W(s+1,k)/W(s,k) = C(n,2s+4k)/C(n,2s) · (s+½)_k² / ((b₁)_k (b₂)_k)`. -/
theorem ratio_i_odd (m s k : ℕ) (h : s + 2 * k ≤ m) (hW : W (2 * m + 1) s k ≠ 0) :
    W (2 * m + 1) (s + 1) k / W (2 * m + 1) s k
      = ((2 * m + 1).choose (2 * s + 4 * k) : ℚ) / ((2 * m + 1).choose (2 * s) : ℚ)
        * (poch ((s : ℚ) + 1 / 2) k ^ 2 / (poch (b1 m s k) k * poch (b1 m s k) k)) :=
  ratio_core _ s k _ _ (fun t ht => thmK_odd m s k h (s + t) (by omega) (by omega)) (by omega)
    (by linarith [b1_neg m s k h]) (by linarith [b1_neg m s k h]) hW

/-- **`eq:i`**, even `n = 2m` (`b₂ = b₁ + 1`). -/
theorem ratio_i_even (m s k : ℕ) (h : s + 2 * k ≤ m) (hW : W (2 * m) s k ≠ 0) :
    W (2 * m) (s + 1) k / W (2 * m) s k
      = ((2 * m).choose (2 * s + 4 * k) : ℚ) / ((2 * m).choose (2 * s) : ℚ)
        * (poch ((s : ℚ) + 1 / 2) k ^ 2 / (poch (b1 m s k) k * poch (b1 m s k + 1) k)) :=
  ratio_core _ s k _ _ (fun t ht => thmK_even m s k h (s + t) (by omega) (by omega)) (by omega)
    (by linarith [b1_neg m s k h]) (b1_neg m s k h) hW

/-- **Positivity** (odd `n`): from `W(0,k) > 0` (`2k ≤ m+1`, the de Bruijn base, assumed here),
`W(s,k) > 0` for all `s + 2k ≤ m + 1`. -/
theorem W_pos_odd (m : ℕ) (h0 : ∀ k, 2 * k ≤ m + 1 → 0 < W (2 * m + 1) 0 k) :
    ∀ s k, s + 2 * k ≤ m + 1 → 0 < W (2 * m + 1) s k := by
  intro s
  induction s with
  | zero => intro k hk; exact h0 k (by omega)
  | succ s ih =>
    intro k hk
    have hp := ih k (by omega)
    have hr := ratio_core _ s k (b1 m s k) (b1 m s k) (fun t ht => thmK_odd m s k (by omega) (s + t) (by omega) (by omega))
      (by omega) (by linarith [b1_neg m s k (by omega)]) (by linarith [b1_neg m s k (by omega)]) hp.ne'
    have hpos := ratioI_pos (2 * m + 1) s k (b1 m s k) (b1 m s k) (by omega) (by linarith [b1_neg m s k (by omega)])
      (by linarith [b1_neg m s k (by omega)])
    rw [div_eq_iff hp.ne'] at hr
    rw [hr]; exact mul_pos hpos hp

/-- **Positivity** (even `n`). -/
theorem W_pos_even (m : ℕ) (h0 : ∀ k, 2 * k ≤ m + 1 → 0 < W (2 * m) 0 k) :
    ∀ s k, s + 2 * k ≤ m + 1 → 0 < W (2 * m) s k := by
  intro s
  induction s with
  | zero => intro k hk; exact h0 k (by omega)
  | succ s ih =>
    intro k hk
    have hp := ih k (by omega)
    have hr := ratio_core _ s k (b1 m s k) (b1 m s k + 1) (fun t ht => thmK_even m s k (by omega) (s + t) (by omega) (by omega))
      (by omega) (by linarith [b1_neg m s k (by omega)]) (b1_neg m s k (by omega)) hp.ne'
    have hpos := ratioI_pos (2 * m) s k (b1 m s k) (b1 m s k + 1) (by omega) (by linarith [b1_neg m s k (by omega)])
      (b1_neg m s k (by omega))
    rw [div_eq_iff hp.ne'] at hr
    rw [hr]; exact mul_pos hpos hp

/-! ### Step 4 of the proof of `eq:z` (Pfaff–Saalschütz closed form) -/

lemma poch_one (k : ℕ) : poch (1 : ℚ) k = (k.factorial : ℚ) := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih => rw [poch_succ, ih, Nat.factorial_succ]; push_cast; ring

/-- reversing the factors: `(-x-k+1)_k = (-1)^k (x)_k`. -/
lemma poch_reflect (x : ℚ) : ∀ k : ℕ, poch (-x - k + 1) k = (-1) ^ k * poch x k
  | 0 => by simp [poch_zero]
  | k + 1 => by
    rw [poch_succ_left, show -x - ((k + 1 : ℕ) : ℚ) + 1 + 1 = -x - k + 1 by push_cast; ring, poch_reflect x k,
      poch_succ]
    push_cast; ring

/-- **Step 4**, `L₁`: with `ρ = u^s (1-u)^{m-s-2k-1}`, `p = ₂F₁(-k, m+1-k; α+1; u)`, `α = s+½`,
`β_p = m-s-2k-½`: `L₁(ρp) = L₁(ρ) k! (β_p+1)_k / ((α+1)_k (α+β_p+1)_k)`. -/
theorem step4_L1 (m s k : ℕ) (h : s + 2 * k + 1 ≤ m) :
    L1 (X ^ s * (1 - X) ^ (m - s - 2 * k - 1) * pP m (s + 1) k)
      = L1 (X ^ s * (1 - X) ^ (m - s - 2 * k - 1)) * ((k.factorial : ℚ) * poch ((m : ℚ) - s - 2 * k + 1 / 2) k)
        / (poch ((s : ℚ) + 1 / 2 + 1) k * poch ((m : ℚ) - 2 * k + 1) k) := by
  obtain ⟨e, rfl⟩ : ∃ e, m = s + 2 * k + 1 + e := ⟨m - s - 2 * k - 1, by omega⟩
  rw [show s + 2 * k + 1 + e - s - 2 * k - 1 = e by omega, L1_apply, L1_apply,
    show (1 - X) * (X ^ s * (1 - X) ^ e * pP (s + 2 * k + 1 + e) (s + 1) k)
      = X ^ s * (1 - X) ^ (e + 1) * pP (s + 2 * k + 1 + e) (s + 1) k by ring,
    show (1 - X) * (X ^ s * (1 - X : ℚ[X]) ^ e) = X ^ s * (1 - X) ^ (e + 1) by ring, L0_beta]
  unfold pP
  have hc : poch (((s + 1 : ℕ) : ℚ) + 1 / 2) k ≠ 0 := poch_pos_of _ (by positivity) k
  have hd : poch ((((s + 2 * k + 1 + e : ℕ) : ℚ)) - 2 * k + 1) k ≠ 0 :=
    poch_pos_of _ (by push_cast; linarith) k
  have hcab : ((s + 1 : ℕ) : ℚ) + 1 / 2 - ((s : ℚ) + 1 / 2) - (((s + 2 * k + 1 + e : ℕ) : ℚ) + 1 - k)
      = -((((s + 2 * k + 1 + e : ℕ) : ℚ)) - 2 * k + 1) - k + 1 := by push_cast; ring
  rw [L0_hyp, sum_Bv _ _ _ _ _ (by unfold dd; push_cast; ring), pfaff_saalschutz _ _ _ _ hc
    (by rw [hcab, poch_reflect]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hd)]
  rw [hcab, poch_reflect, show ((s + 1 : ℕ) : ℚ) + 1 / 2 - ((s : ℚ) + 1 / 2) = 1 by push_cast; ring, poch_one,
    show ((s + 1 : ℕ) : ℚ) + 1 / 2 - (((s + 2 * k + 1 + e : ℕ) : ℚ) + 1 - k)
      = -((((s + 2 * k + 1 + e : ℕ) : ℚ)) - s - 2 * k + 1 / 2) - k + 1 by push_cast; ring,
    poch_reflect, show (s : ℚ) + 1 / 2 + 1 = ((s + 1 : ℕ) : ℚ) + 1 / 2 by push_cast; ring]
  have e2 : ((-1 : ℚ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hs : ((-1 : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

end Stage5

end Bali.GP

#print axioms Bali.GP.pf_eq_pfS
#print axioms Bali.GP.pfS_tw
#print axioms Bali.GP.pfS_rep
#print axioms Bali.GP.adj_ker
#print axioms Bali.GP.even_ker
#print axioms Bali.GP.odd_ker_span
#print axioms Bali.GP.W_eq_pf
#print axioms Bali.GP.ratio_of_ker
#print axioms Bali.GP.ratio_i_odd
#print axioms Bali.GP.ratio_i_even
#print axioms Bali.GP.W_pos_odd
#print axioms Bali.GP.W_pos_even
#print axioms Bali.GP.step4_L1

/-! ## Stage 6 (2026-11-17): eq:z (Steps 1-5), positivity without the de Bruijn base -/

namespace Bali.GP

section Stage6

/-- **Step 4**, `L₀` (even `n`): `L₀(ρq) = L₀(ρ) k! (β_q+1)_k / ((α+1)_k (m-2k)_k)`. -/
theorem step4_L0 (m s k : ℕ) (h : s + 2 * k + 1 ≤ m) :
    L0 (X ^ s * (1 - X) ^ (m - s - 2 * k - 1) * qP m (s + 1) k)
      = L0 (X ^ s * (1 - X) ^ (m - s - 2 * k - 1)) * ((k.factorial : ℚ) * poch ((m : ℚ) - s - 2 * k - 1 / 2) k)
        / (poch ((s : ℚ) + 1 / 2 + 1) k * poch ((m : ℚ) - 2 * k) k) := by
  obtain ⟨e, rfl⟩ : ∃ e, m = s + 2 * k + 1 + e := ⟨m - s - 2 * k - 1, by omega⟩
  rw [show s + 2 * k + 1 + e - s - 2 * k - 1 = e by omega, L0_beta]
  unfold qP
  have hc : poch (((s + 1 : ℕ) : ℚ) + 1 / 2) k ≠ 0 := poch_pos_of _ (by positivity) k
  have hd : poch ((((s + 2 * k + 1 + e : ℕ) : ℚ)) - 2 * k) k ≠ 0 :=
    poch_pos_of _ (by push_cast; linarith) k
  have hcab : ((s + 1 : ℕ) : ℚ) + 1 / 2 - ((s : ℚ) + 1 / 2) - (((s + 2 * k + 1 + e : ℕ) : ℚ) - k)
      = -((((s + 2 * k + 1 + e : ℕ) : ℚ)) - 2 * k) - k + 1 := by push_cast; ring
  rw [L0_hyp, sum_Bv _ _ _ _ _ (by unfold dd; push_cast; ring), pfaff_saalschutz _ _ _ _ hc
    (by rw [hcab, poch_reflect]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hd)]
  rw [hcab, poch_reflect, show ((s + 1 : ℕ) : ℚ) + 1 / 2 - ((s : ℚ) + 1 / 2) = 1 by push_cast; ring, poch_one,
    show ((s + 1 : ℕ) : ℚ) + 1 / 2 - (((s + 2 * k + 1 + e : ℕ) : ℚ) - k)
      = -((((s + 2 * k + 1 + e : ℕ) : ℚ)) - s - 2 * k - 1 / 2) - k + 1 by push_cast; ring,
    poch_reflect, show (s : ℚ) + 1 / 2 + 1 = ((s + 1 : ℕ) : ℚ) + 1 / 2 by push_cast; ring]
  have hs : ((-1 : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-! ### Step 1 (row expansion + adjugate) -/

/-- Step 1: expanding `W(s,k+1)` along its first row and replacing the adjugate vector of
`G[s+1..s+2k+1]` by a kernel vector `c`: `c_{2k} W(s,k+1) = W(s+1,k) Σ_ℓ c_ℓ G_{s,s+1+ℓ}`. -/
theorem z_core (n s k : ℕ) (c : ℕ → ℚ)
    (hc : ∀ t ≤ 2 * k, ∑ l ∈ range (2 * k + 1), c l * G n (s + 1 + l) (s + 1 + t) = 0)
    (hW : W n (s + 1) k ≠ 0) :
    c (2 * k) * W n s (k + 1) = W n (s + 1) k * ∑ l ∈ range (2 * k + 1), c l * G n s (s + 1 + l) := by
  have key := odd_ker_span (G n) (fun a b => G_anti n b a) k (fun i => s + 1 + i) (2 * k) le_rfl
    (by rw [adjv_last]; exact hW) c (by
      intro t ht
      rw [← neg_eq_zero, ← hc t (by omega), ← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      rw [G_anti n (s + 1 + l) (s + 1 + t)]; ring)
  rw [adjv_last] at key
  have hexp : W n s (k + 1)
      = ∑ l ∈ range (2 * k + 1), G n s (s + 1 + l) * adjv (G n) k (fun i => s + 1 + i) l := by
    unfold W adjv
    rw [pfS_succ]
    refine sum_congr rfl fun l _ => ?_
    have e1 : (fun i => s + (sk l i + 1)) = (fun i => s + 1 + sk l i) := by funext i; ring
    dsimp only
    rw [e1, add_zero, show s + (l + 1) = s + 1 + l by ring]; ring
  rw [hexp, mul_sum, mul_sum]
  refine sum_congr rfl fun l hl => ?_
  have := key l (mem_range.1 hl)
  linear_combination (-(G n s (s + 1 + l))) * this

/-! ### Step 2 (removing the tail) -/

/-- `ρ = u^s (1-u)^{m-s-2k-1}`. -/
noncomputable def rho (m s k : ℕ) : ℚ[X] := X ^ s * (1 - X) ^ (m - s - 2 * k - 1)

/-- `h` with `(1-u)^{2k+1} = 1 + u h`. -/
noncomputable def rT (k : ℕ) : ℚ[X] := -∑ j ∈ range (2 * k + 1), (1 - X) ^ j

lemma one_sub_pow_rT (k : ℕ) : ((1 : ℚ[X]) - X) ^ (2 * k + 1) = 1 + X * rT k := by
  have := geom_sum_mul ((1 : ℚ[X]) - X) (2 * k + 1)
  unfold rT
  linear_combination -this

lemma natDegree_rT (k : ℕ) : (rT k).natDegree ≤ 2 * k := by
  unfold rT
  rw [natDegree_neg]
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  have e3 : ((1 : ℚ[X]) - X).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  have hj' := mem_range.1 hj
  exact natDegree_pow_le.trans ((Nat.mul_le_mul_left j e3).trans (by rw [mul_one]; omega))

lemma piW_succ (m s k : ℕ) (h : s + 2 * k + 1 ≤ m) : piW m (s + 1) k = X * rho m s k := by
  unfold piW rho
  rw [show m - (s + 1) - 2 * k = m - s - 2 * k - 1 by omega]; ring

lemma eps_split (m s k : ℕ) (h : s + 2 * k + 1 ≤ m) :
    eps m s = ((-1 : ℚ) ^ s) • (rho m s k + piW m (s + 1) k * rT k) := by
  rw [piW_succ m s k h]
  unfold eps rho
  congr 1
  rw [show ((1 : ℚ[X]) - X) ^ (m - s) = (1 - X) ^ (m - s - 2 * k - 1) * (1 - X) ^ (2 * k + 1) by
    rw [← pow_add]; congr 1; omega, one_sub_pow_rT]; ring

/-! ### Step 3 (the chain for `𝒯`) -/

/-- the three moves of Step 3: `C(uρpq, ρ) - C(ρ, uρpq) = -L_α(ρp) L_β(ρq)`. -/
theorem z_chain (La Lb : ℚ[X] →ₗ[ℚ] ℚ) (ρ p q : ℚ[X]) (k : ℕ)
    (hp : p.natDegree ≤ k) (hq : q.natDegree ≤ k)
    (hA : ∀ i < k, La (X * ρ * p * X ^ i) = 0) (hB : ∀ i < k, Lb (X * ρ * q * X ^ i) = 0) :
    Cab La Lb (X * ρ * p * q) ρ - Cab La Lb ρ (X * ρ * p * q) = -(La (ρ * p) * Lb (ρ * q)) := by
  have s1 := T_split La Lb q (X * ρ * p) ρ
  rw [ddT_eq_zero La Lb q _ _ (fun t ht a hat => by
    rw [show X ^ a * (X * ρ * p) = X * ρ * p * X ^ a by ring, hA a (by omega), zero_mul]), neg_zero] at s1
  have s2 := Cab_u La Lb (ρ * p) (ρ * q)
  have s3 := T_split La Lb p ρ (X * ρ * q)
  rw [ddT_eq_zero La Lb p _ _ (fun t ht a hat => by
    rw [show X ^ (t - 1 - a) * (X * ρ * q) = X * ρ * q * X ^ (t - 1 - a) by ring, hB _ (by omega),
      mul_zero]), neg_zero] at s3
  rw [show q * (X * ρ * p) = X * ρ * p * q by ring, show q * ρ = ρ * q by ring] at s1
  rw [show X * (ρ * p) = X * ρ * p by ring, show X * (ρ * q) = X * ρ * q by ring] at s2
  rw [show p * ρ = ρ * p by ring, show p * (X * ρ * q) = X * ρ * p * q by ring] at s3
  linear_combination s1 + s2 + s3

/-! ### Steps 1–3 assembled: `𝒯` in terms of `L₁(ρp)`, `L₀(ρq)` -/

theorem z_sum_even (m s k : ℕ) (h : s + 2 * k + 1 ≤ m) :
    ∑ l ∈ range (2 * k + 1), cK (2 * m) (b1 m (s + 1) k) (b1 m (s + 1) k + 1) (s + 1) k l
        * G (2 * m) s (s + 1 + l)
      = 2 ^ (2 * (2 * m)) * ((2 * m).choose (2 * s) : ℚ)
        * (L1 (rho m s k * pP m (s + 1) k) * L0 (rho m s k * qP m (s + 1) k)) := by
  have h' : s + 1 + 2 * k ≤ m := by omega
  have hterm : ∀ l ∈ range (2 * k + 1), cK (2 * m) (b1 m (s + 1) k) (b1 m (s + 1) k + 1) (s + 1) k l
        * G (2 * m) s (s + 1 + l)
      = (-2 ^ (2 * (2 * m)) * ((2 * m).choose (2 * s) : ℚ))
        * (dK (b1 m (s + 1) k) (b1 m (s + 1) k + 1) (s + 1) k l * Om Reven (eps m s) (eps m (s + 1 + l))) := by
    intro l hl
    rw [mem_range] at hl
    have hC : ((2 * m).choose (2 * (s + 1) + 2 * l) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    rw [lemma3c_even m s (s + 1 + l) (by omega) (by omega), cK,
      show 2 * (s + 1 + l) = 2 * (s + 1) + 2 * l by ring, div_mul_eq_mul_div, div_eq_iff hC]
    ring
  rw [sum_congr rfl hterm, ← Finset.mul_sum]
  have hA : ∑ l ∈ range (2 * k + 1), dK (b1 m (s + 1) k) (b1 m (s + 1) k + 1) (s + 1) k l
        * Om Reven (eps m s) (eps m (s + 1 + l))
      = Om Reven (eps m s) (∑ l ∈ range (2 * k + 1),
          dK (b1 m (s + 1) k) (b1 m (s + 1) k + 1) (s + 1) k l • eps m (s + 1 + l)) := by
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hA, eps_sum m (s + 1) k h']
  unfold dK
  rw [cauchy (gK _ (s + 1) k) (gK _ (s + 1) k) k (fun j hj => v2_vanish _ _ k j hj)
      (fun j hj => v2_vanish _ _ k j hj), pfaffs, pfaffs,
    show ((s + 1 : ℕ) : ℚ) + 1 / 2 - b1 m (s + 1) k = (m : ℚ) + 1 - k by unfold b1; ring,
    show ((s + 1 : ℕ) : ℚ) + 1 / 2 - (b1 m (s + 1) k + 1) = (m : ℚ) - k by unfold b1; ring, ← pP, ← qP]
  have hk : Om Reven (piW m (s + 1) k * rT k) (piW m (s + 1) k * (pP m (s + 1) k * qP m (s + 1) k)) = 0 := by
    rw [Om_anti Reven Reven_symm (piW m (s + 1) k * rT k), ← mul_assoc,
      lem_ker_even (piW m (s + 1) k) (pP m (s + 1) k) (qP m (s + 1) k) (rT k) k (natDegree_hyp2 _ _ _) (natDegree_hyp2 _ _ _) (natDegree_rT k)
        (fun i hi => lem_orth_L1 m (s + 1) k h' i hi) (fun i hi => lem_orth_L0 m (s + 1) k h' i hi), neg_zero]
  have hc : Om Reven (rho m s k) (piW m (s + 1) k * (pP m (s + 1) k * qP m (s + 1) k))
      = L1 (rho m s k * pP m (s + 1) k) * L0 (rho m s k * qP m (s + 1) k) := by
    rw [Om_anti Reven Reven_symm (rho m s k), Om_even_eq, piW_succ m s k h,
      show X * rho m s k * (pP m (s + 1) k * qP m (s + 1) k)
        = X * rho m s k * pP m (s + 1) k * qP m (s + 1) k by ring,
      z_chain L1 L0 (rho m s k) (pP m (s + 1) k) (qP m (s + 1) k) k (natDegree_hyp2 _ _ _) (natDegree_hyp2 _ _ _)
        (fun i hi => by rw [← piW_succ m s k h]; exact lem_orth_L1 m (s + 1) k h' i hi)
        (fun i hi => by rw [← piW_succ m s k h]; exact lem_orth_L0 m (s + 1) k h' i hi)]
    ring
  rw [map_smul, eps_split m s k h, map_smul, LinearMap.smul_apply, map_add, LinearMap.add_apply, hk, hc]
  simp only [smul_eq_mul]
  have e : ((-1 : ℚ) ^ s) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [pow_succ]
  linear_combination (2 ^ (2 * (2 * m)) * ((2 * m).choose (2 * s) : ℚ)
    * (L1 (rho m s k * pP m (s + 1) k) * L0 (rho m s k * qP m (s + 1) k))) * e

theorem z_sum_odd (m s k : ℕ) (h : s + 2 * k + 1 ≤ m) :
    ∑ l ∈ range (2 * k + 1), cK (2 * m + 1) (b1 m (s + 1) k) (b1 m (s + 1) k) (s + 1) k l
        * G (2 * m + 1) s (s + 1 + l)
      = 2 ^ (2 * (2 * m + 1)) * ((2 * m + 1).choose (2 * s) : ℚ) * L1 (rho m s k * pP m (s + 1) k) ^ 2 := by
  have h' : s + 1 + 2 * k ≤ m := by omega
  have hterm : ∀ l ∈ range (2 * k + 1), cK (2 * m + 1) (b1 m (s + 1) k) (b1 m (s + 1) k) (s + 1) k l
        * G (2 * m + 1) s (s + 1 + l)
      = (-2 ^ (2 * (2 * m + 1) + 1) * ((2 * m + 1).choose (2 * s) : ℚ))
        * (dK (b1 m (s + 1) k) (b1 m (s + 1) k) (s + 1) k l * Om Rodd (eps m s) (eps m (s + 1 + l))) := by
    intro l hl
    rw [mem_range] at hl
    have hC : ((2 * m + 1).choose (2 * (s + 1) + 2 * l) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    rw [lemma3c_odd m s (s + 1 + l) (by omega) (by omega), cK,
      show 2 * (s + 1 + l) = 2 * (s + 1) + 2 * l by ring, div_mul_eq_mul_div, div_eq_iff hC]
    ring
  rw [sum_congr rfl hterm, ← Finset.mul_sum]
  have hA : ∑ l ∈ range (2 * k + 1), dK (b1 m (s + 1) k) (b1 m (s + 1) k) (s + 1) k l
        * Om Rodd (eps m s) (eps m (s + 1 + l))
      = Om Rodd (eps m s) (∑ l ∈ range (2 * k + 1),
          dK (b1 m (s + 1) k) (b1 m (s + 1) k) (s + 1) k l • eps m (s + 1 + l)) := by
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hA, eps_sum m (s + 1) k h']
  unfold dK
  rw [cauchy (gK _ (s + 1) k) (gK _ (s + 1) k) k (fun j hj => v2_vanish _ _ k j hj)
      (fun j hj => v2_vanish _ _ k j hj), pfaffs,
    show ((s + 1 : ℕ) : ℚ) + 1 / 2 - b1 m (s + 1) k = (m : ℚ) + 1 - k by unfold b1; ring, ← pP]
  have hk : Om Rodd (piW m (s + 1) k * rT k) (piW m (s + 1) k * (pP m (s + 1) k * pP m (s + 1) k)) = 0 := by
    rw [Om_anti Rodd Rodd_symm (piW m (s + 1) k * rT k), ← mul_assoc,
      lem_ker_odd (piW m (s + 1) k) (pP m (s + 1) k) (rT k) k (natDegree_hyp2 _ _ _) (natDegree_rT k)
        (fun i hi => lem_orth_L1 m (s + 1) k h' i hi), neg_zero]
  have hc : Om Rodd (rho m s k) (piW m (s + 1) k * (pP m (s + 1) k * pP m (s + 1) k))
      = (1 / 2) * L1 (rho m s k * pP m (s + 1) k) ^ 2 := by
    rw [Om_anti Rodd Rodd_symm (rho m s k), Om_odd_eq, piW_succ m s k h,
      show X * rho m s k * (pP m (s + 1) k * pP m (s + 1) k)
        = X * rho m s k * pP m (s + 1) k * pP m (s + 1) k by ring,
      z_chain L1 L1 (rho m s k) (pP m (s + 1) k) (pP m (s + 1) k) k (natDegree_hyp2 _ _ _) (natDegree_hyp2 _ _ _)
        (fun i hi => by rw [← piW_succ m s k h]; exact lem_orth_L1 m (s + 1) k h' i hi)
        (fun i hi => by rw [← piW_succ m s k h]; exact lem_orth_L1 m (s + 1) k h' i hi)]
    ring
  rw [map_smul, eps_split m s k h, map_smul, LinearMap.smul_apply, map_add, LinearMap.add_apply, hk, hc]
  simp only [smul_eq_mul]
  have e : ((-1 : ℚ) ^ s) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [pow_succ]
  linear_combination (2 ^ (2 * (2 * m + 1)) * ((2 * m + 1).choose (2 * s) : ℚ)
    * L1 (rho m s k * pP m (s + 1) k) ^ 2) * e

/-! ### Steps 4–5 and `eq:z` -/

theorem z_even_poch (m s k : ℕ) (h : s + 2 * k + 1 ≤ m) (hW : W (2 * m) (s + 1) k ≠ 0) :
    cK (2 * m) (b1 m (s + 1) k) (b1 m (s + 1) k + 1) (s + 1) k (2 * k) * W (2 * m) s (k + 1)
      = W (2 * m) (s + 1) k * (2 ^ (2 * (2 * m)) * ((2 * m).choose (2 * s) : ℚ)
        * (L1 (rho m s k * pP m (s + 1) k) * L0 (rho m s k * qP m (s + 1) k))) := by
  rw [z_core (2 * m) s k _ (fun t ht => thmK_even m (s + 1) k (by omega) (s + 1 + t) (by omega) (by omega)) hW,
    z_sum_even m s k h]

theorem z_odd_poch (m s k : ℕ) (h : s + 2 * k + 1 ≤ m) (hW : W (2 * m + 1) (s + 1) k ≠ 0) :
    cK (2 * m + 1) (b1 m (s + 1) k) (b1 m (s + 1) k) (s + 1) k (2 * k) * W (2 * m + 1) s (k + 1)
      = W (2 * m + 1) (s + 1) k * (2 ^ (2 * (2 * m + 1)) * ((2 * m + 1).choose (2 * s) : ℚ)
        * L1 (rho m s k * pP m (s + 1) k) ^ 2) := by
  rw [z_core (2 * m + 1) s k _ (fun t ht => thmK_odd m (s + 1) k (by omega) (s + 1 + t) (by omega) (by omega)) hW,
    z_sum_odd m s k h]

lemma L1_rho (m s k : ℕ) (h : s + 2 * k + 1 ≤ m) :
    L1 (X ^ s * (1 - X) ^ (m - s - 2 * k - 1))
      = poch (1 / 2 : ℚ) s * poch (1 / 2 : ℚ) (m - s - 2 * k) / ((m - 2 * k).factorial : ℚ) := by
  obtain ⟨e, rfl⟩ : ∃ e, m = s + 2 * k + 1 + e := ⟨m - s - 2 * k - 1, by omega⟩
  rw [show s + 2 * k + 1 + e - s - 2 * k - 1 = e by omega, show s + 2 * k + 1 + e - s - 2 * k = e + 1 by omega,
    show s + 2 * k + 1 + e - 2 * k = s + (e + 1) by omega, L1_apply,
    show (1 - X) * (X ^ s * (1 - X : ℚ[X]) ^ e) = X ^ s * (1 - X) ^ (e + 1) by ring, L0_beta, Bv]

lemma L0_rho (m s k : ℕ) (h : s + 2 * k + 1 ≤ m) :
    L0 (X ^ s * (1 - X) ^ (m - s - 2 * k - 1))
      = poch (1 / 2 : ℚ) s * poch (1 / 2 : ℚ) (m - s - 2 * k - 1) / ((m - 2 * k - 1).factorial : ℚ) := by
  obtain ⟨e, rfl⟩ : ∃ e, m = s + 2 * k + 1 + e := ⟨m - s - 2 * k - 1, by omega⟩
  rw [show s + 2 * k + 1 + e - s - 2 * k - 1 = e by omega, show s + 2 * k + 1 + e - 2 * k - 1 = s + e by omega,
    L0_beta, Bv]

lemma poch_m1 (m k : ℕ) (h : 2 * k ≤ m) :
    poch ((m : ℚ) - 2 * k + 1) k = ((m - k).factorial : ℚ) / ((m - 2 * k).factorial : ℚ) := by
  have hf := fact_poch (m - 2 * k) k
  rw [show m - 2 * k + k = m - k by omega] at hf
  rw [hf, show (((m - 2 * k : ℕ) : ℚ)) + 1 = (m : ℚ) - 2 * k + 1 by push_cast [Nat.cast_sub h]; ring]
  have : ((m - 2 * k).factorial : ℚ) ≠ 0 := by positivity
  field_simp

lemma poch_m0 (m k : ℕ) (h : 2 * k + 1 ≤ m) :
    poch ((m : ℚ) - 2 * k) k = ((m - k - 1).factorial : ℚ) / ((m - 2 * k - 1).factorial : ℚ) := by
  have hf := fact_poch (m - 2 * k - 1) k
  rw [show m - 2 * k - 1 + k = m - k - 1 by omega] at hf
  rw [hf, show (((m - 2 * k - 1 : ℕ) : ℚ)) + 1 = (m : ℚ) - 2 * k by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring]
  have : ((m - 2 * k - 1).factorial : ℚ) ≠ 0 := by positivity
  field_simp

/-- `g̃_k = (β_p+1)_k/(α+1)_k`. -/
lemma gK_p (m s k : ℕ) :
    gK (b1 m (s + 1) k) (s + 1) k k = poch ((m : ℚ) - s - 2 * k + 1 / 2) k / poch ((s : ℚ) + 1 / 2 + 1) k := by
  rw [gK_top, show b1 m (s + 1) k = -((m : ℚ) - s - 2 * k + 1 / 2) - k + 1 by unfold b1; push_cast; ring,
    poch_reflect, show ((s + 1 : ℕ) : ℚ) + 1 / 2 = (s : ℚ) + 1 / 2 + 1 by push_cast; ring]
  have e2 : ((-1 : ℚ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  congr 1
  linear_combination (poch ((m : ℚ) - s - 2 * k + 1 / 2) k) * e2

/-- `g̃'_k = (β_q+1)_k/(α+1)_k` (even `n`). -/
lemma gK_q (m s k : ℕ) :
    gK (b1 m (s + 1) k + 1) (s + 1) k k = poch ((m : ℚ) - s - 2 * k - 1 / 2) k / poch ((s : ℚ) + 1 / 2 + 1) k := by
  rw [gK_top, show b1 m (s + 1) k + 1 = -((m : ℚ) - s - 2 * k - 1 / 2) - k + 1 by unfold b1; push_cast; ring,
    poch_reflect, show ((s + 1 : ℕ) : ℚ) + 1 / 2 = (s : ℚ) + 1 / 2 + 1 by push_cast; ring]
  have e2 : ((-1 : ℚ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  congr 1
  linear_combination (poch ((m : ℚ) - s - 2 * k - 1 / 2) k) * e2

lemma poch_pos' (x : ℚ) (hx : 0 < x) (k : ℕ) : 0 < poch x k := by
  rw [poch_eq_prod]; exact Finset.prod_pos fun i _ => by positivity

/-- **Theorem `thm:ratios`, `eq:z`**, even `n = 2m`, assuming `W(s+1,k) ≠ 0` (Step 1 of the paper). -/
theorem z_even_of (m s k : ℕ) (h : s + 2 * k + 1 ≤ m) (hW : W (2 * m) (s + 1) k ≠ 0) :
    W (2 * m) s (k + 1) / W (2 * m) (s + 1) k
      = 2 ^ (2 * (2 * m)) * ((2 * m).choose (2 * s) : ℚ) * ((2 * m).choose (2 * s + 4 * k + 2) : ℚ)
        * poch (1 / 2 : ℚ) s ^ 2 * (k.factorial : ℚ) ^ 2
        * (poch (1 / 2 : ℚ) (m - s - 2 * k) * poch (1 / 2 : ℚ) (m - s - 2 * k - 1)
          / (((m - k).factorial : ℚ) * ((m - k - 1).factorial : ℚ))) := by
  have key := z_even_poch m s k h hW
  unfold rho at key
  rw [step4_L1 m s k h, step4_L0 m s k h, L1_rho m s k h, L0_rho m s k h, poch_m1 m k (by omega),
    poch_m0 m k (by omega), cK, dK_top, gK_p, gK_q, show 2 * (s + 1) + 2 * (2 * k) = 2 * s + 4 * k + 2 by ring]
    at key
  have hm : (s : ℚ) + 2 * k + 1 ≤ m := by exact_mod_cast h
  have hp1 := (poch_pos' ((m : ℚ) - s - 2 * k + 1 / 2) (by linarith) k).ne'
  have hp2 := (poch_pos' ((m : ℚ) - s - 2 * k - 1 / 2) (by linarith) k).ne'
  have hp3 := (poch_pos' ((s : ℚ) + 1 / 2 + 1) (by positivity) k).ne'
  have hC : ((2 * m).choose (2 * s + 4 * k + 2) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have f1 : ((m - k).factorial : ℚ) ≠ 0 := by positivity
  have f2 : ((m - k - 1).factorial : ℚ) ≠ 0 := by positivity
  have f3 : ((m - 2 * k).factorial : ℚ) ≠ 0 := by positivity
  have f4 : ((m - 2 * k - 1).factorial : ℚ) ≠ 0 := by positivity
  generalize poch ((m : ℚ) - s - 2 * k + 1 / 2) k = P1 at key hp1
  generalize poch ((m : ℚ) - s - 2 * k - 1 / 2) k = P2 at key hp2
  generalize poch ((s : ℚ) + 1 / 2 + 1) k = P3 at key hp3
  generalize poch (1 / 2 : ℚ) s = Q1 at key ⊢
  generalize poch (1 / 2 : ℚ) (m - s - 2 * k) = Q2 at key ⊢
  generalize poch (1 / 2 : ℚ) (m - s - 2 * k - 1) = Q3 at key ⊢
  rw [div_eq_iff hW]
  field_simp at key ⊢
  linear_combination key

/-- **`eq:z`**, odd `n = 2m+1`, assuming `W(s+1,k) ≠ 0`. -/
theorem z_odd_of (m s k : ℕ) (h : s + 2 * k + 1 ≤ m) (hW : W (2 * m + 1) (s + 1) k ≠ 0) :
    W (2 * m + 1) s (k + 1) / W (2 * m + 1) (s + 1) k
      = 2 ^ (2 * (2 * m + 1)) * ((2 * m + 1).choose (2 * s) : ℚ) * ((2 * m + 1).choose (2 * s + 4 * k + 2) : ℚ)
        * poch (1 / 2 : ℚ) s ^ 2 * (k.factorial : ℚ) ^ 2
        * (poch (1 / 2 : ℚ) (m - s - 2 * k) / ((m - k).factorial : ℚ)) ^ 2 := by
  have key := z_odd_poch m s k h hW
  unfold rho at key
  rw [step4_L1 m s k h, L1_rho m s k h, poch_m1 m k (by omega), cK, dK_top, gK_p,
    show 2 * (s + 1) + 2 * (2 * k) = 2 * s + 4 * k + 2 by ring] at key
  have hm : (s : ℚ) + 2 * k + 1 ≤ m := by exact_mod_cast h
  have hp1 := (poch_pos' ((m : ℚ) - s - 2 * k + 1 / 2) (by linarith) k).ne'
  have hp3 := (poch_pos' ((s : ℚ) + 1 / 2 + 1) (by positivity) k).ne'
  have hC : ((2 * m + 1).choose (2 * s + 4 * k + 2) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have f1 : ((m - k).factorial : ℚ) ≠ 0 := by positivity
  have f3 : ((m - 2 * k).factorial : ℚ) ≠ 0 := by positivity
  generalize poch ((m : ℚ) - s - 2 * k + 1 / 2) k = P1 at key hp1
  generalize poch ((s : ℚ) + 1 / 2 + 1) k = P3 at key hp3
  generalize poch (1 / 2 : ℚ) s = Q1 at key ⊢
  generalize poch (1 / 2 : ℚ) (m - s - 2 * k) = Q2 at key ⊢
  rw [div_eq_iff hW]
  field_simp at key ⊢
  linear_combination key

/-- **Positivity without the de Bruijn base** (the paper's second route: induction on `k` via `eq:z`,
`W(·,0) = 1`): `W(s,k) > 0` for `s + 2k ≤ m + 1`, `n = 2m`. -/
theorem W_pos_even_all (m : ℕ) : ∀ k s, s + 2 * k ≤ m + 1 → 0 < W (2 * m) s k := by
  intro k
  induction k with
  | zero => intro s _; rw [W_zero]; norm_num
  | succ k ih =>
    intro s hs
    have h : s + 2 * k + 1 ≤ m := by omega
    have hp := ih (s + 1) (by omega)
    have hz := z_even_of m s k h hp.ne'
    rw [div_eq_iff hp.ne'] at hz
    rw [hz]
    have c1 : (0 : ℚ) < (2 * m).choose (2 * s) := by exact_mod_cast Nat.choose_pos (by omega)
    have c2 : (0 : ℚ) < (2 * m).choose (2 * s + 4 * k + 2) := by exact_mod_cast Nat.choose_pos (by omega)
    have q1 := poch_pos' (1 / 2 : ℚ) (by norm_num) s
    have q2 := poch_pos' (1 / 2 : ℚ) (by norm_num) (m - s - 2 * k)
    have q3 := poch_pos' (1 / 2 : ℚ) (by norm_num) (m - s - 2 * k - 1)
    positivity

/-- **Positivity without the de Bruijn base**, `n = 2m+1`. -/
theorem W_pos_odd_all (m : ℕ) : ∀ k s, s + 2 * k ≤ m + 1 → 0 < W (2 * m + 1) s k := by
  intro k
  induction k with
  | zero => intro s _; rw [W_zero]; norm_num
  | succ k ih =>
    intro s hs
    have h : s + 2 * k + 1 ≤ m := by omega
    have hp := ih (s + 1) (by omega)
    have hz := z_odd_of m s k h hp.ne'
    rw [div_eq_iff hp.ne'] at hz
    rw [hz]
    have c1 : (0 : ℚ) < (2 * m + 1).choose (2 * s) := by exact_mod_cast Nat.choose_pos (by omega)
    have c2 : (0 : ℚ) < (2 * m + 1).choose (2 * s + 4 * k + 2) := by exact_mod_cast Nat.choose_pos (by omega)
    have q1 := poch_pos' (1 / 2 : ℚ) (by norm_num) s
    have q2 := poch_pos' (1 / 2 : ℚ) (by norm_num) (m - s - 2 * k)
    positivity

/-- the base `W(0,k) > 0` (hypothesis of `W_pos_even`), now proved. -/
theorem W0_pos_even (m k : ℕ) (hk : 2 * k ≤ m + 1) : 0 < W (2 * m) 0 k := W_pos_even_all m k 0 (by omega)

theorem W0_pos_odd (m k : ℕ) (hk : 2 * k ≤ m + 1) : 0 < W (2 * m + 1) 0 k := W_pos_odd_all m k 0 (by omega)

/-- `W_pos_even` with its hypothesis discharged. -/
theorem W_pos_even' (m s k : ℕ) (h : s + 2 * k ≤ m + 1) : 0 < W (2 * m) s k :=
  W_pos_even m (fun k hk => W0_pos_even m k hk) s k h

theorem W_pos_odd' (m s k : ℕ) (h : s + 2 * k ≤ m + 1) : 0 < W (2 * m + 1) s k :=
  W_pos_odd m (fun k hk => W0_pos_odd m k hk) s k h

/-- **`eq:z`**, even `n = 2m`, unconditional. -/
theorem ratio_z_even (m s k : ℕ) (h : s + 2 * k + 1 ≤ m) :
    W (2 * m) s (k + 1) / W (2 * m) (s + 1) k
      = 2 ^ (2 * (2 * m)) * ((2 * m).choose (2 * s) : ℚ) * ((2 * m).choose (2 * s + 4 * k + 2) : ℚ)
        * poch (1 / 2 : ℚ) s ^ 2 * (k.factorial : ℚ) ^ 2
        * (poch (1 / 2 : ℚ) (m - s - 2 * k) * poch (1 / 2 : ℚ) (m - s - 2 * k - 1)
          / (((m - k).factorial : ℚ) * ((m - k - 1).factorial : ℚ))) :=
  z_even_of m s k h (W_pos_even_all m k (s + 1) (by omega)).ne'

/-- **`eq:z`**, odd `n = 2m+1`, unconditional. -/
theorem ratio_z_odd (m s k : ℕ) (h : s + 2 * k + 1 ≤ m) :
    W (2 * m + 1) s (k + 1) / W (2 * m + 1) (s + 1) k
      = 2 ^ (2 * (2 * m + 1)) * ((2 * m + 1).choose (2 * s) : ℚ) * ((2 * m + 1).choose (2 * s + 4 * k + 2) : ℚ)
        * poch (1 / 2 : ℚ) s ^ 2 * (k.factorial : ℚ) ^ 2
        * (poch (1 / 2 : ℚ) (m - s - 2 * k) / ((m - k).factorial : ℚ)) ^ 2 :=
  z_odd_of m s k h (W_pos_odd_all m k (s + 1) (by omega)).ne'

/-- **`eq:i`**, even `n`, unconditional. -/
theorem ratio_i_even' (m s k : ℕ) (h : s + 2 * k ≤ m) :
    W (2 * m) (s + 1) k / W (2 * m) s k
      = ((2 * m).choose (2 * s + 4 * k) : ℚ) / ((2 * m).choose (2 * s) : ℚ)
        * (poch ((s : ℚ) + 1 / 2) k ^ 2 / (poch (b1 m s k) k * poch (b1 m s k + 1) k)) :=
  ratio_i_even m s k h (W_pos_even_all m k s (by omega)).ne'

/-- **`eq:i`**, odd `n`, unconditional. -/
theorem ratio_i_odd' (m s k : ℕ) (h : s + 2 * k ≤ m) :
    W (2 * m + 1) (s + 1) k / W (2 * m + 1) s k
      = ((2 * m + 1).choose (2 * s + 4 * k) : ℚ) / ((2 * m + 1).choose (2 * s) : ℚ)
        * (poch ((s : ℚ) + 1 / 2) k ^ 2 / (poch (b1 m s k) k * poch (b1 m s k) k)) :=
  ratio_i_odd m s k h (W_pos_odd_all m k s (by omega)).ne'

end Stage6

end Bali.GP

#print axioms Bali.GP.step4_L0
#print axioms Bali.GP.z_core
#print axioms Bali.GP.one_sub_pow_rT
#print axioms Bali.GP.eps_split
#print axioms Bali.GP.z_chain
#print axioms Bali.GP.z_sum_even
#print axioms Bali.GP.z_sum_odd
#print axioms Bali.GP.z_even_poch
#print axioms Bali.GP.z_odd_poch
#print axioms Bali.GP.L1_rho
#print axioms Bali.GP.L0_rho
#print axioms Bali.GP.poch_m1
#print axioms Bali.GP.poch_m0
#print axioms Bali.GP.gK_p
#print axioms Bali.GP.gK_q
#print axioms Bali.GP.z_even_of
#print axioms Bali.GP.z_odd_of
#print axioms Bali.GP.W_pos_even_all
#print axioms Bali.GP.W_pos_odd_all
#print axioms Bali.GP.W0_pos_even
#print axioms Bali.GP.W0_pos_odd
#print axioms Bali.GP.W_pos_even'
#print axioms Bali.GP.W_pos_odd'
#print axioms Bali.GP.ratio_z_even
#print axioms Bali.GP.ratio_z_odd
#print axioms Bali.GP.ratio_i_even'
#print axioms Bali.GP.ratio_i_odd'

/-! # Stage 7 (2026-11-17): Corollary `cor:B` on the `W` side.
`Λ_d` built from `eq:i` and `eq:z` at `s = 0` equals the Γ ratio of Conjecture B / BKW (5.6)
(`Bali.ConjB.crB` for odd `n`, `Bali.VE.crE` for even `n`), for every `0 ≤ d ≤ m`.
The de Bruijn identification `V^B_d ↔ W` is not part of this stage; it is proved in Stage 9
(`Bali.GPdB.VB_even`, `Bali.GPdB.VB_odd`). -/

open Finset

namespace Bali.GP

section Stage7

lemma poch_half_fact (j : ℕ) :
    poch (1 / 2 : ℚ) j = ((2 * j).factorial : ℚ) / (4 ^ j * j.factorial) := by
  induction j with
  | zero => simp [poch_zero]
  | succ j ih =>
    rw [poch_succ, ih, show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring

lemma poch_neg_half (j : ℕ) : ∀ k : ℕ,
    poch (-(j : ℚ) - k + 1 / 2) k * poch (1 / 2 : ℚ) j = (-1) ^ k * poch (1 / 2 : ℚ) (j + k)
  | 0 => by simp [poch_zero]
  | k + 1 => by
    rw [poch_succ_left, show -(j : ℚ) - ((k + 1 : ℕ) : ℚ) + 1 / 2 + 1 = -(j : ℚ) - k + 1 / 2 by push_cast; ring,
      mul_assoc, poch_neg_half j k, show j + (k + 1) = (j + k) + 1 by ring, poch_succ]
    push_cast
    ring

lemma poch_half_pos (j : ℕ) : 0 < poch (1 / 2 : ℚ) j := by
  rw [poch_half_fact]; positivity

/-- `(b)_k` for `b = -j-k+1/2` as a quotient of `(1/2)`-Pochhammers. -/
lemma poch_neg_half' (j k : ℕ) :
    poch (-(j : ℚ) - k + 1 / 2) k = (-1) ^ k * poch (1 / 2 : ℚ) (j + k) / poch (1 / 2 : ℚ) j := by
  rw [eq_div_iff (poch_half_pos j).ne', poch_neg_half]

lemma Gh (j : ℕ) : Real.Gamma ((j : ℝ) + 1 / 2) = ((2 * j).factorial : ℝ) * √Real.pi / (4 ^ j * j.factorial) :=
  Bali.ConjB.Gamma_half j

lemma four_pow (a : ℕ) : (4 : ℝ) ^ a = 2 ^ (2 * a) := by rw [pow_mul]; norm_num

lemma sgn_mul (k : ℕ) (A B C D : ℚ) :
    (-1) ^ k * A / B * ((-1) ^ k * C / D) = A / B * (C / D) := by
  have : ((-1 : ℚ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  rw [mul_div_assoc, mul_div_assoc, mul_mul_mul_comm, this, one_mul]

/-! ### Case A: `n = 2m+1`, `d = 2k` -/

theorem corB_odd_even (m k : ℕ) (h : 2 * k ≤ m) :
    (((2 ^ (2 * m + 1) * ((4 * k).factorial : ℚ)) * (W (2 * m + 1) 1 k / W (2 * m + 1) 0 k) : ℚ) : ℝ)
      = Bali.ConjB.crB m (2 * k) (Bali.ConjB.Ke k) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 * k := ⟨m - 2 * k, by omega⟩
  have hr := ratio_i_odd' (j + 2 * k) 0 k (by omega)
  simp only [Nat.cast_zero, zero_add, mul_zero, Nat.choose_zero_right, Nat.cast_one, div_one] at hr
  rw [hr, show b1 (j + 2 * k) 0 k = -((j + 1 : ℕ) : ℚ) - k + 1 / 2 by unfold b1; push_cast; ring,
    poch_neg_half', sgn_mul, poch_half_fact, poch_half_fact, poch_half_fact,
    Nat.cast_choose ℚ (show 4 * k ≤ 2 * (j + 2 * k) + 1 by omega),
    show 2 * (j + 2 * k) + 1 - 4 * k = 2 * j + 1 by omega]
  have G1 : Real.Gamma ((2 * ((j + 2 * k : ℕ) : ℝ) + 1) / 2 - ((2 * k : ℕ) : ℝ) + 1)
      = ((2 * (j + 1)).factorial : ℝ) * √Real.pi / (4 ^ (j + 1) * (j + 1).factorial) := by
    rw [← Gh]; congr 1; push_cast; ring
  have G2 : Real.Gamma ((2 * ((j + 2 * k : ℕ) : ℝ) + 1) / 2 - ((2 * k : ℕ) : ℝ) + 1 / 2) = (j.factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]; congr 1; push_cast; ring
  have G3 : Real.Gamma ((2 * ((j + 2 * k : ℕ) : ℝ) + 1 - ((2 * k : ℕ) : ℝ) + 2) / 2)
      = ((2 * (j + 1 + k)).factorial : ℝ) * √Real.pi / (4 ^ (j + 1 + k) * (j + 1 + k).factorial) := by
    rw [← Gh]; congr 1; push_cast; ring
  unfold Bali.ConjB.crB Bali.ConjB.Ke
  rw [G1, G2, G3]
  rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.factorial_succ (2 * j + 1),
    Nat.factorial_succ j, show 2 * (j + 2 * k) + 1 = 2 * j + 4 * k + 1 by ring]
  have hs : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  push_cast
  have := hs.ne'
  field_simp
  simp only [four_pow]
  ring

/-! ### Case B: `n = 2m+1`, `d = 2k+1` -/

theorem corB_odd_odd (m k : ℕ) (h : 2 * k + 1 ≤ m) :
    ((((4 * k + 2).factorial : ℚ) / 2 ^ (2 * m + 1) * (W (2 * m + 1) 0 (k + 1) / W (2 * m + 1) 1 k) : ℚ) : ℝ)
      = Bali.ConjB.crB m (2 * k + 1) (Bali.ConjB.Ko k) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 * k + 1 := ⟨m - 2 * k - 1, by omega⟩
  have hr := ratio_z_odd (j + 2 * k + 1) 0 k (by omega)
  simp only [Nat.cast_zero, zero_add, mul_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, poch_zero,
    one_pow, Nat.sub_zero, show j + 2 * k + 1 - 2 * k = j + 1 by omega,
    show j + 2 * k + 1 - k = j + k + 1 by omega] at hr
  rw [hr]
  simp only [poch_half_fact]
  rw [Nat.cast_choose ℚ (show 4 * k + 2 ≤ 2 * (j + 2 * k + 1) + 1 by omega),
    show 2 * (j + 2 * k + 1) + 1 - (4 * k + 2) = 2 * j + 1 by omega]
  have G1 : Real.Gamma ((2 * ((j + 2 * k + 1 : ℕ) : ℝ) + 1) / 2 - ((2 * k + 1 : ℕ) : ℝ) + 1)
      = ((2 * (j + 1)).factorial : ℝ) * √Real.pi / (4 ^ (j + 1) * (j + 1).factorial) := by
    rw [← Gh]; congr 1; push_cast; ring
  have G2 : Real.Gamma ((2 * ((j + 2 * k + 1 : ℕ) : ℝ) + 1) / 2 - ((2 * k + 1 : ℕ) : ℝ) + 1 / 2)
      = (j.factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]; congr 1; push_cast; ring
  have G3 : Real.Gamma ((2 * ((j + 2 * k + 1 : ℕ) : ℝ) + 1 - ((2 * k + 1 : ℕ) : ℝ) + 2) / 2)
      = ((j + k + 1).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]; congr 1; push_cast; ring
  unfold Bali.ConjB.crB Bali.ConjB.Ko
  rw [G1, G2, G3]
  rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.factorial_succ (2 * j + 1),
    Nat.factorial_succ j, show 2 * (j + 2 * k + 1) + 1 = 2 * j + 4 * k + 3 by ring]
  have hs : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  push_cast
  have := hs.ne'
  field_simp
  simp only [four_pow]
  ring

/-! ### Case C: `n = 2m`, `d = 2k` -/

theorem corB_even_even (m k : ℕ) (h : 2 * k ≤ m) :
    (((2 ^ (2 * m) * ((4 * k).factorial : ℚ)) * (W (2 * m) 1 k / W (2 * m) 0 k) : ℚ) : ℝ)
      = Bali.VE.crE m (2 * k) (Bali.ConjB.Ke k) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 * k := ⟨m - 2 * k, by omega⟩
  have hr := ratio_i_even' (j + 2 * k) 0 k (by omega)
  simp only [Nat.cast_zero, zero_add, mul_zero, Nat.choose_zero_right, Nat.cast_one, div_one] at hr
  rw [hr, show b1 (j + 2 * k) 0 k + 1 = -(j : ℚ) - k + 1 / 2 by unfold b1; push_cast; ring,
    show b1 (j + 2 * k) 0 k = -((j + 1 : ℕ) : ℚ) - k + 1 / 2 by unfold b1; push_cast; ring,
    poch_neg_half' (j + 1) k, poch_neg_half' j k, sgn_mul]
  simp only [poch_half_fact]
  rw [Nat.cast_choose ℚ (show 4 * k ≤ 2 * (j + 2 * k) by omega),
    show 2 * (j + 2 * k) - 4 * k = 2 * j by omega]
  have G1 : Real.Gamma (((j + 2 * k : ℕ) : ℝ) - ((2 * k : ℕ) : ℝ) + 3 / 2)
      = ((2 * (j + 1)).factorial : ℝ) * √Real.pi / (4 ^ (j + 1) * (j + 1).factorial) := by
    rw [← Gh]; congr 1; push_cast; ring
  have G2 : Real.Gamma (((j + 2 * k : ℕ) : ℝ) - ((2 * k : ℕ) : ℝ) + 1) = (j.factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]; congr 1; push_cast; ring
  have G3 : Real.Gamma ((2 * ((j + 2 * k : ℕ) : ℝ) - ((2 * k : ℕ) : ℝ) + 1) / 2)
      = ((2 * (j + k)).factorial : ℝ) * √Real.pi / (4 ^ (j + k) * (j + k).factorial) := by
    rw [← Gh]; congr 1; push_cast; ring
  have G4 : Real.Gamma ((2 * ((j + 2 * k : ℕ) : ℝ) - ((2 * k : ℕ) : ℝ) + 3) / 2)
      = ((2 * (j + 1 + k)).factorial : ℝ) * √Real.pi / (4 ^ (j + 1 + k) * (j + 1 + k).factorial) := by
    rw [← Gh]; congr 1; push_cast; ring
  unfold Bali.VE.crE Bali.ConjB.Ke
  rw [G1, G2, G3, G4]
  rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.factorial_succ (2 * j + 1), Nat.factorial_succ (2 * j),
    Nat.factorial_succ j, show 2 * (j + 1 + k) = 2 * (j + k) + 1 + 1 by ring,
    Nat.factorial_succ (2 * (j + k) + 1), Nat.factorial_succ (2 * (j + k)),
    show j + 1 + k = (j + k) + 1 by ring, Nat.factorial_succ (j + k),
    show 2 * (j + 2 * k) = 2 * j + 4 * k by ring]
  have hs : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  push_cast
  have := hs.ne'
  field_simp
  simp only [four_pow]
  ring

/-! ### Case D: `n = 2m`, `d = 2k+1` -/

theorem corB_even_odd (m k : ℕ) (h : 2 * k + 1 ≤ m) :
    ((((4 * k + 2).factorial : ℚ) / 2 ^ (2 * m) * (W (2 * m) 0 (k + 1) / W (2 * m) 1 k) : ℚ) : ℝ)
      = Bali.VE.crE m (2 * k + 1) (Bali.ConjB.Ko k) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 * k + 1 := ⟨m - 2 * k - 1, by omega⟩
  have hr := ratio_z_even (j + 2 * k + 1) 0 k (by omega)
  simp only [Nat.cast_zero, zero_add, mul_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, poch_zero,
    one_pow, Nat.sub_zero, show j + 2 * k + 1 - 2 * k = j + 1 by omega,
    show j + 1 - 1 = j by omega,
    show j + 2 * k + 1 - k = j + k + 1 by omega, show j + k + 1 - 1 = j + k by omega] at hr
  rw [hr]
  simp only [poch_half_fact]
  rw [Nat.cast_choose ℚ (show 4 * k + 2 ≤ 2 * (j + 2 * k + 1) by omega),
    show 2 * (j + 2 * k + 1) - (4 * k + 2) = 2 * j by omega]
  have G1 : Real.Gamma (((j + 2 * k + 1 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) + 3 / 2)
      = ((2 * (j + 1)).factorial : ℝ) * √Real.pi / (4 ^ (j + 1) * (j + 1).factorial) := by
    rw [← Gh]; congr 1; push_cast; ring
  have G2 : Real.Gamma (((j + 2 * k + 1 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) + 1) = (j.factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]; congr 1; push_cast; ring
  have G3 : Real.Gamma ((2 * ((j + 2 * k + 1 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) + 1) / 2)
      = ((j + k).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]; congr 1; push_cast; ring
  have G4 : Real.Gamma ((2 * ((j + 2 * k + 1 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) + 3) / 2)
      = ((j + k + 1).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]; congr 1; push_cast; ring
  unfold Bali.VE.crE Bali.ConjB.Ko
  rw [G1, G2, G3, G4]
  rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.factorial_succ (2 * j + 1), Nat.factorial_succ (2 * j),
    Nat.factorial_succ j, Nat.factorial_succ (j + k),
    show 2 * (j + 2 * k + 1) = 2 * j + 4 * k + 2 by ring]
  have hs : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  push_cast
  have := hs.ne'
  field_simp
  simp only [four_pow]
  ring

end Stage7

end Bali.GP

#print axioms Bali.GP.corB_odd_even
#print axioms Bali.GP.corB_odd_odd
#print axioms Bali.GP.corB_even_even
#print axioms Bali.GP.corB_even_odd

section Stage8
open Finset Equiv Matrix

namespace Bali.PfB

/-! ## Stage 8 (2026-11-18): bridge `pfP` ↔ `pf` (step (1) of the de Bruijn identity) -/

open Bali.PfP

variable {R : Type*} [CommRing R]

/-- one term of the permutation-sum Pfaffian on `Fin (2m)`, pairs `(eι (i,0), eι (i,1)) = (2i, 2i+1)`. -/
def TF {m : ℕ} (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R) (σ : Perm (Fin (2 * m))) : R :=
  (Perm.sign σ : R) * ∏ i : Fin m, A (σ (eι m (i, 0))) (σ (eι m (i, 1)))

/-- permutation-sum Pfaffian on `Fin (2m)`. -/
def pfF (m : ℕ) (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R) : R := ∑ σ, TF A σ

theorem pfP_eq_pfF (m : ℕ) (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R) :
    pfP (A.submatrix (eι m) (eι m)) = pfF m A := by
  unfold pfP pfF TF
  refine Fintype.sum_equiv ((eι m).permCongr) _ _ (fun σ => ?_)
  simp [Perm.sign_permCongr, Equiv.permCongr_apply]

lemma TF_mul_prod {m : ℕ} (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R) (σ : Perm (Fin (2 * m)))
    (α : Perm (Fin m)) :
    TF A (σ * (eι m).permCongr (Equiv.prodCongrLeft fun _ : Fin 2 => α)) = TF A σ := by
  unfold TF
  rw [Perm.sign_mul, Perm.sign_permCongr, Perm.sign_prodCongrLeft]
  simp only [Fin.prod_univ_two, Int.units_mul_self, mul_one]
  congr 1
  simp only [Perm.mul_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.prodCongrLeft_apply]
  exact Fintype.prod_equiv α _ _ (fun i => rfl)

lemma TF_mul_swap {m : ℕ} (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R) (hA : ∀ i j, A j i = -A i j)
    (σ : Perm (Fin (2 * m))) (j : Fin m) :
    TF A (σ * (eι m).permCongr (swap (j, 0) (j, 1))) = TF A σ := by
  unfold TF
  rw [Perm.sign_mul, Perm.sign_permCongr, Perm.sign_swap (by simp)]
  have h : ∀ i : Fin m,
      A (σ (eι m (swap (j, 0) (j, 1) (i, 0)))) (σ (eι m (swap (j, 0) (j, 1) (i, 1))))
        = (if i = j then -1 else 1) * A (σ (eι m (i, 0))) (σ (eι m (i, 1))) := by
    intro i
    by_cases hij : i = j
    · subst hij; rw [swap_apply_left, swap_apply_right, hA]; simp
    · rw [swap_apply_of_ne_of_ne (by simp [hij]) (by simp [hij]),
        swap_apply_of_ne_of_ne (by simp [hij]) (by simp [hij])]
      simp [hij]
  simp only [Perm.mul_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply, h, prod_mul_distrib,
    prod_ite_eq', mem_univ, if_true]
  push_cast; ring

lemma eι_zero (n : ℕ) : eι (n + 1) (0, 0) = (0 : Fin (2 * n + 1 + 1)) := by
  ext; rw [eι_val]; simp

lemma eι_one (n : ℕ) : eι (n + 1) (0, 1) = (1 : Fin (2 * n + 1 + 1)) := by
  ext; rw [eι_val]; simp; exact (Nat.mod_eq_of_lt (by omega)).symm

lemma eι_succ (n : ℕ) (i : Fin n) (c : Fin 2) :
    eι (n + 1) (i.succ, c) = ((eι n (i, c)).succ).succ := by
  ext; rw [eι_val]; simp [eι_val]; ring

/-- the permutation moving position `0` to `p`, preserving every term. -/
def piP (n : ℕ) (p : Fin (2 * (n + 1))) : Perm (Fin (2 * (n + 1))) :=
  (eι (n + 1)).permCongr (Equiv.prodCongrLeft fun _ : Fin 2 => swap 0 ((eι (n + 1)).symm p).1) *
    (eι (n + 1)).permCongr (swap (0, 0) (0, ((eι (n + 1)).symm p).2))

lemma piP_zero (n : ℕ) (p : Fin (2 * (n + 1))) : piP n p (0 : Fin (2 * n + 1 + 1)) = p := by
  rw [← eι_zero n]
  simp [piP, Equiv.permCongr_apply]

lemma TF_piP (n : ℕ) (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) R) (hA : ∀ i j, A j i = -A i j)
    (σ : Perm (Fin (2 * (n + 1)))) (p : Fin (2 * (n + 1))) : TF A (σ * piP n p) = TF A σ := by
  unfold piP
  rw [← mul_assoc]
  rcases fin2_cases ((eι (n + 1)).symm p).2 with hb | hb
  · rw [hb, swap_self, Equiv.permCongr_refl, Perm.mul_refl, TF_mul_prod]
  · rw [hb, TF_mul_swap A hA, TF_mul_prod]

/-- reduction to permutations fixing `0`. -/
theorem pfF_reduce (n : ℕ) (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) R) (hA : ∀ i j, A j i = -A i j) :
    pfF (n + 1) A = (2 * (n + 1) : R) * ∑ σ : Perm (Fin (2 * n + 1 + 1)), if σ 0 = 0 then TF (m := n + 1) A σ else 0 := by
  have key : ∀ p : Fin (2 * n + 1 + 1), (∑ σ : Perm (Fin (2 * n + 1 + 1)), if σ p = 0 then TF (m := n + 1) A σ else 0)
      = ∑ σ : Perm (Fin (2 * n + 1 + 1)), if σ 0 = 0 then TF (m := n + 1) A σ else 0 := by
    intro p
    refine Fintype.sum_equiv (Equiv.mulRight (piP n p)) _ _ (fun σ => ?_)
    simp only [coe_mulRight, Perm.mul_apply, TF_piP n A hA]
    erw [piP_zero n p]
  have hone : ∀ σ : Perm (Fin (2 * n + 1 + 1)),
      TF (m := n + 1) A σ = ∑ p : Fin (2 * n + 1 + 1), if σ p = 0 then TF (m := n + 1) A σ else 0 := by
    intro σ
    simp_rw [Equiv.apply_eq_iff_eq_symm_apply]
    rw [sum_ite_eq']; simp
  show (∑ σ : Perm (Fin (2 * n + 1 + 1)), TF (m := n + 1) A σ) = _
  rw [sum_congr rfl fun σ _ => hone σ, sum_comm, sum_congr rfl fun p _ => key p, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- relabelling. -/
lemma pfF_relabel (n : ℕ) (B : Matrix (Fin (2 * n)) (Fin (2 * n)) R) (c : Perm (Fin (2 * n))) :
    pfF n (B.submatrix c c) = (Perm.sign c : R) * pfF n B := by
  unfold pfF
  have h : ∀ ρ : Perm (Fin (2 * n)), TF (B.submatrix c c) ρ = (Perm.sign c : R) * TF B (c * ρ) := by
    intro ρ
    unfold TF
    rw [Perm.sign_mul]
    have hc : ((Perm.sign c : ℤ) : R) * ((Perm.sign c : ℤ) : R) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
    simp only [submatrix_apply, Perm.mul_apply, Units.val_mul, Int.cast_mul]
    linear_combination (-(((Perm.sign ρ : ℤ) : R)) *
      ∏ i : Fin n, B (c (ρ (eι n (i, 0)))) (c (ρ (eι n (i, 1))))) * hc
  rw [sum_congr rfl fun ρ _ => h ρ, ← mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft c) _ _ (fun _ => rfl)

/-- the minor of the first-row expansion. -/
def mnr (n : ℕ) (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) R) (q : Fin (2 * n + 1)) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) R :=
  A.submatrix (fun i => (q.succAbove i).succ) (fun i => (q.succAbove i).succ)

/-- one step of the decomposition: permutations fixing `0`, by `q = σ 1 - 1`. -/
theorem sum_fix0 (n : ℕ) (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) R) :
    (∑ σ : Perm (Fin (2 * n + 1 + 1)), if σ 0 = 0 then TF (m := n + 1) A σ else 0)
      = ∑ q : Fin (2 * n + 1), (-1 : R) ^ (q : ℕ) * A (0 : Fin (2 * n + 1 + 1)) q.succ * pfF n (mnr n A q) := by
  refine (Fintype.sum_equiv (Perm.decomposeFin (n := 2 * n + 1)).symm _ _ (fun _ => rfl)).symm.trans ?_
  rw [Fintype.sum_prod_type]
  simp only [Perm.decomposeFin_symm_apply_zero]
  rw [Fintype.sum_eq_single (0 : Fin (2 * n + 1 + 1)) (fun x hx => by simp [hx])]
  simp only [↓reduceIte]
  refine (Fintype.sum_equiv (Perm.decomposeFin (n := 2 * n)).symm _ _ (fun _ => rfl)).symm.trans ?_
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun q _ => ?_
  -- the term
  have hterm : ∀ ρ : Perm (Fin (2 * n)),
      TF (m := n + 1) A ((Perm.decomposeFin (n := 2 * n + 1)).symm (0, (Perm.decomposeFin (n := 2 * n)).symm (q, ρ)))
        = ((if q = 0 then 1 else -1 : ℤ) : R) * A (0 : Fin (2 * n + 1 + 1)) q.succ *
          TF (A.submatrix (fun y : Fin (2 * n) => (swap 0 q y.succ).succ)
            (fun y : Fin (2 * n) => (swap 0 q y.succ).succ)) ρ := by
    intro ρ
    unfold TF
    rw [Fin.prod_univ_succ, eι_zero, eι_one]
    simp only [Perm.decomposeFin.symm_sign, if_true, one_mul, Units.val_mul, Int.cast_mul,
      Perm.decomposeFin_symm_apply_zero, eι_succ, Perm.decomposeFin_symm_apply_succ, swap_self,
      Equiv.refl_apply, submatrix_apply]
    rw [← Fin.succ_zero_eq_one, Perm.decomposeFin_symm_apply_succ, swap_self, Equiv.refl_apply,
      Perm.decomposeFin_symm_apply_zero]
    split_ifs <;> push_cast <;> ring
  rw [sum_congr rfl fun ρ _ => hterm ρ, ← mul_sum]
  change _ * pfF n _ = _
  refine Fin.cases ?_ (fun i => ?_) q
  · simp only [if_true, swap_self, Equiv.refl_apply, Fin.val_zero, pow_zero, mnr, Fin.succAbove_zero]
    push_cast; ring
  · have hg : (A.submatrix (fun y : Fin (2 * n) => (swap 0 i.succ y.succ).succ)
        (fun y : Fin (2 * n) => (swap 0 i.succ y.succ).succ))
        = (mnr n A i.succ).submatrix (Fin.cycleRange i) (Fin.cycleRange i) := by
      ext a b
      simp only [submatrix_apply, mnr, Fin.succAbove_cycleRange]
    rw [hg, pfF_relabel, Fin.sign_cycleRange, if_neg (Fin.succ_ne_zero i), Fin.val_succ]
    push_cast; ring

/-- **Bridge (first-row form).** -/
theorem pfF_eq_pf : ∀ (n : ℕ) (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R), (∀ i j, A j i = -A i j) →
    pfF n A = 2 ^ n * (n.factorial : R) * Bali.Pf.pf n A
  | 0, A, _ => by
    simp [pfF, TF, Bali.Pf.pf]
  | n + 1, A, hA => by
    rw [pfF_reduce n A hA, sum_fix0 n A]
    have ih : ∀ q : Fin (2 * n + 1), pfF n (mnr n A q) = 2 ^ n * (n.factorial : R) * Bali.Pf.pf n (mnr n A q) :=
      fun q => pfF_eq_pf n _ (fun i j => by simp only [mnr, submatrix_apply]; exact hA _ _)
    simp only [ih]
    rw [Bali.Pf.pf, mul_sum, mul_sum]
    show ∑ q : Fin (2 * n + 1), _ = ∑ q : Fin (2 * n + 1), 2 ^ (n + 1) * ((n + 1).factorial : R) *
      ((-1) ^ (q : ℕ) * A (0 : Fin (2 * n + 1 + 1)) q.succ * Bali.Pf.pf n (mnr n A q))
    refine sum_congr rfl fun q _ => ?_
    rw [Nat.factorial_succ, mnr]
    push_cast; ring

/-- **Bridge.**  `pfP (A ∘ eι) = 2^m m! · pf A` for skew `A`. -/
theorem pfP_eq_pf (m : ℕ) (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R) (hA : ∀ i j, A j i = -A i j) :
    pfP (A.submatrix (eι m) (eι m)) = 2 ^ m * (m.factorial : R) * Bali.Pf.pf m A := by
  rw [pfP_eq_pfF, pfF_eq_pf m A hA]

end Bali.PfB

end Stage8

#print axioms Bali.PfB.pfF_eq_pf
#print axioms Bali.PfB.pfP_eq_pf

/-! ## Stage 9 (2026-11-18): de Bruijn V^B_{2k} = prod (2a)! W(0,k), V^B_{2k+1} = 2^n prod (2a)! W(1,k), cor:B -/

open Finset Polynomial Matrix

namespace Bali.GPdB

/-! ## Step (2): the even Krawtchouk polynomials as polynomials in `y` -/

lemma deriv_gf (x r : ℕ) :
    (1 - X ^ 2) * derivative ((1 - X : ℚ[X]) ^ x * (1 + X) ^ r)
      = (((r : ℚ[X]) - (x : ℚ[X])) - ((x : ℚ[X]) + (r : ℚ[X])) * X) * ((1 - X) ^ x * (1 + X) ^ r) := by
  rcases x with _ | x <;> rcases r with _ | r <;>
    simp only [derivative_mul, derivative_pow, derivative_sub, derivative_add, derivative_one,
      derivative_X, pow_zero, Nat.add_sub_cancel, map_natCast, Nat.cast_add, Nat.cast_one,
      Nat.cast_zero, map_zero, zero_mul, mul_zero, zero_add, add_zero, map_add, map_one] <;> ring

lemma deriv_gf' (n x : ℕ) (hx : x ≤ n) :
    derivative (Bali.GP.gf n x) = X ^ 2 * derivative (Bali.GP.gf n x)
      + C ((n : ℚ) - 2 * x) * Bali.GP.gf n x - C (n : ℚ) * (X * Bali.GP.gf n x) := by
  have h := deriv_gf x (n - x)
  have hc : ((n - x : ℕ) : ℚ[X]) = (n : ℚ[X]) - x := by rw [Nat.cast_sub hx]
  rw [hc] at h
  unfold Bali.GP.gf
  simp only [map_sub, map_mul, map_natCast, map_ofNat]
  linear_combination h

lemma K0 (n x : ℕ) : Bali.GP.K n 0 x = 1 := by
  unfold Bali.GP.K Bali.GP.gf; rw [coeff_zero_eq_eval_zero]; simp

lemma K1 (n x : ℕ) (hx : x ≤ n) : Bali.GP.K n 1 x = (n : ℚ) - 2 * x := by
  have h := congrArg (fun p => p.coeff 0) (deriv_gf' n x hx)
  simp only [coeff_add, coeff_sub, coeff_derivative, coeff_X_pow_mul', coeff_C_mul,
    coeff_X_mul_zero] at h
  have h0 := K0 n x
  unfold Bali.GP.K at h0 ⊢
  simp at h
  rw [h0] at h; linarith

lemma K_rec (n x : ℕ) (hx : x ≤ n) (c : ℕ) :
    ((c : ℚ) + 2) * Bali.GP.K n (c + 2) x
      = ((n : ℚ) - 2 * x) * Bali.GP.K n (c + 1) x - ((n : ℚ) - c) * Bali.GP.K n c x := by
  unfold Bali.GP.K
  rcases c with _ | c
  · have h := congrArg (fun p => p.coeff 1) (deriv_gf' n x hx)
    simp only [coeff_add, coeff_sub, coeff_derivative, coeff_X_pow_mul', coeff_C_mul,
      coeff_X_mul] at h
    simp at h ⊢
    linarith
  · have h := congrArg (fun p => p.coeff (c + 2)) (deriv_gf' n x hx)
    simp only [coeff_add, coeff_sub, coeff_derivative, coeff_X_pow_mul', coeff_C_mul,
      coeff_X_mul] at h
    simp at h ⊢
    push_cast at h ⊢
    linarith

/-- `(E_a, O_a)`: `K_{2a} = E_a(y)`, `K_{2a+1} = u O_a(y)`, `u = n - 2x`, `y = u^2`. -/
noncomputable def EO (n : ℕ) : ℕ → ℚ[X] × ℚ[X]
  | 0 => (1, 1)
  | a + 1 =>
    (C (1 / (2 * (a : ℚ) + 2)) * (X * (EO n a).2 - C ((n : ℚ) - 2 * a) * (EO n a).1),
     C (1 / (2 * (a : ℚ) + 3)) * (C (1 / (2 * (a : ℚ) + 2)) * (X * (EO n a).2 - C ((n : ℚ) - 2 * a) * (EO n a).1)
        - C ((n : ℚ) - 2 * a - 1) * (EO n a).2))

noncomputable def Ev (n a : ℕ) : ℚ[X] := (EO n a).1
noncomputable def Od (n a : ℕ) : ℚ[X] := (EO n a).2

lemma Ev_zero (n : ℕ) : Ev n 0 = 1 := rfl
lemma Od_zero (n : ℕ) : Od n 0 = 1 := rfl
lemma Ev_succ (n a : ℕ) :
    Ev n (a + 1) = C (1 / (2 * (a : ℚ) + 2)) * (X * Od n a - C ((n : ℚ) - 2 * a) * Ev n a) := rfl
lemma Od_succ (n a : ℕ) :
    Od n (a + 1) = C (1 / (2 * (a : ℚ) + 3)) * (Ev n (a + 1) - C ((n : ℚ) - 2 * a - 1) * Od n a) := rfl

theorem K_EO (n x : ℕ) (hx : x ≤ n) : ∀ a : ℕ,
    Bali.GP.K n (2 * a) x = (Ev n a).eval (((n : ℚ) - 2 * x) ^ 2) ∧
    Bali.GP.K n (2 * a + 1) x = ((n : ℚ) - 2 * x) * (Od n a).eval (((n : ℚ) - 2 * x) ^ 2)
  | 0 => by
    refine ⟨?_, ?_⟩
    · simp [Ev_zero, K0]
    · simp [Od_zero, K1 n x hx]
  | a + 1 => by
    obtain ⟨ih1, ih2⟩ := K_EO n x hx a
    set u : ℚ := (n : ℚ) - 2 * x with hu
    have r1 := K_rec n x hx (2 * a)
    have r2 := K_rec n x hx (2 * a + 1)
    rw [show 2 * a + 2 = 2 * (a + 1) by ring] at r1
    rw [show 2 * a + 1 + 2 = 2 * (a + 1) + 1 by ring, show 2 * a + 1 + 1 = 2 * (a + 1) by ring] at r2
    rw [ih1, ih2] at r1
    rw [ih2] at r2
    push_cast at r1 r2
    have hE : Bali.GP.K n (2 * (a + 1)) x = (Ev n (a + 1)).eval (u ^ 2) := by
      rw [Ev_succ]
      simp only [eval_mul, eval_C, eval_sub, eval_X]
      have h2 : (2 * (a : ℚ) + 2) ≠ 0 := by positivity
      field_simp
      linear_combination r1
    refine ⟨hE, ?_⟩
    rw [hE] at r2
    rw [Od_succ]
    simp only [eval_mul, eval_C, eval_sub, eval_X]
    have h3 : (2 * (a : ℚ) + 3) ≠ 0 := by positivity
    field_simp
    linear_combination r2

theorem EO_coeff (n : ℕ) : ∀ a : ℕ,
    (∀ j, a < j → (Ev n a).coeff j = 0) ∧ (Ev n a).coeff a = 1 / ((2 * a).factorial : ℚ) ∧
    (∀ j, a < j → (Od n a).coeff j = 0) ∧ (Od n a).coeff a = 1 / ((2 * a + 1).factorial : ℚ)
  | 0 => by
    refine ⟨fun j hj => ?_, by simp [Ev_zero], fun j hj => ?_, by simp [Od_zero]⟩
    · rw [Ev_zero, coeff_one, if_neg (by omega)]
    · rw [Od_zero, coeff_one, if_neg (by omega)]
  | a + 1 => by
    obtain ⟨e1, e2, o1, o2⟩ := EO_coeff n a
    have hEz : ∀ j, a + 1 < j → (Ev n (a + 1)).coeff j = 0 := by
      intro j hj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [Ev_succ, coeff_C_mul, coeff_sub, coeff_X_mul, coeff_C_mul, o1 j' (by omega), e1 (j' + 1) (by omega)]
      ring
    have hEl : (Ev n (a + 1)).coeff (a + 1) = 1 / ((2 * (a + 1)).factorial : ℚ) := by
      have hf : ((2 * (a + 1)).factorial : ℚ) = (2 * a + 2) * (2 * a + 1).factorial := by
        rw [show 2 * (a + 1) = (2 * a + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
      rw [Ev_succ, coeff_C_mul, coeff_sub, coeff_X_mul, coeff_C_mul, o2, e1 (a + 1) (by omega), hf]
      have : ((2 * a + 1).factorial : ℚ) ≠ 0 := by positivity
      field_simp
      ring
    refine ⟨hEz, hEl, fun j hj => ?_, ?_⟩
    · rw [Od_succ, coeff_C_mul, coeff_sub, coeff_C_mul, hEz j hj, o1 j (by omega)]; ring
    · have hf : ((2 * (a + 1) + 1).factorial : ℚ) = (2 * a + 3) * (2 * (a + 1)).factorial := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [Od_succ, coeff_C_mul, coeff_sub, coeff_C_mul, hEl, o1 (a + 1) (by omega), hf]
      have : ((2 * (a + 1)).factorial : ℚ) ≠ 0 := by positivity
      field_simp
      ring

lemma Ev_natDegree (n a : ℕ) : (Ev n a).natDegree ≤ a :=
  natDegree_le_iff_coeff_eq_zero.2 fun j hj => (EO_coeff n a).1 j (by exact_mod_cast hj)

/-- point form: `K_{2a}(x) = E_a((2x-n)^2)`. -/
lemma K_even (n x a : ℕ) (hx : x ≤ n) :
    Bali.GP.K n (2 * a) x = (Ev n a).eval ((2 * (x : ℚ) - n) ^ 2) := by
  rw [(K_EO n x hx a).1]; congr 1; ring

/-! ## Step (3): sorted points, the sign matrix, de Bruijn -/

open Bali.PfP Bali.VB Bali.ShellX

/-- triangular basis change `K_{2a} = Σ_p B_{ap} y^p`. -/
noncomputable def Bm (n k : ℕ) : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ :=
  fun a p => (Ev n (eι k a)).coeff (eι k p)

theorem det_Bm (n k : ℕ) :
    det (Bm n k) = ∏ a ∈ range (2 * k), (1 / ((2 * a).factorial : ℚ)) := by
  rw [← det_reindex_self (eι k), det_of_lowerTriangular]
  · rw [← Fin.prod_univ_eq_prod_range (fun a => 1 / ((2 * a).factorial : ℚ)) (2 * k)]
    refine prod_congr rfl fun i _ => ?_
    simp only [reindex_apply, submatrix_apply, Bm, Equiv.apply_symm_apply]
    exact (EO_coeff n i).2.1
  · intro i j hij
    simp only [reindex_apply, submatrix_apply, Bm, Equiv.apply_symm_apply]
    exact (EO_coeff n i).1 j (by simpa using hij)

lemma BM_apply {N : ℕ} (n k : ℕ) (t ν : Fin (N + 1) → ℚ) (a : Fin k × Fin 2) (i : Fin (N + 1)) :
    (Bm n k * Mpow (m := k) t ν) a i = ν i * (Ev n (eι k a)).eval (t i) := by
  rw [Matrix.mul_apply]
  simp only [Bm, Mpow]
  have h1 := Equiv.sum_comp (eι k) (fun q : Fin (2 * k) => (Ev n (eι k a)).coeff q * (ν i * t i ^ (q : ℕ)))
  rw [h1, Fin.sum_univ_eq_sum_range (fun q => (Ev n (eι k a)).coeff q * (ν i * t i ^ q)) (2 * k),
    eval_eq_sum_range' (n := 2 * k) (lt_of_le_of_lt (Ev_natDegree n _) (eι k a).isLt), mul_sum]
  refine sum_congr rfl fun q _ => by ring

/-- sum of the maximal minors for weakly increasing points: no sign, ties give `0` on both sides. -/
theorem sum_minors_mono {m N : ℕ} (t ν : Fin (N + 1) → ℚ) (ht : Monotone t) :
    ∑ S ∈ (univ : Finset (Fin (N + 1))).powersetCard (2 * m),
        det ((Mpow (m := m) t ν).submatrix id (G' (m := m) S))
      = VBvol t ν (2 * m) := by
  classical
  unfold VBvol
  refine sum_congr rfl fun S hS => ?_
  have h : S.card = 2 * m := (mem_powersetCard.1 hS).2
  have hG : G' (m := m) S = GS S h := by simp [G', h]
  rw [hG, det_Mpow_S t ν S h, dif_pos h]
  congr 1
  refine prod_congr rfl fun i _ => prod_congr rfl fun j hj => ?_
  have hij : i < j := mem_Ioi.1 hj
  rw [abs_of_nonneg (sub_nonneg.2 (ht ((S.orderEmbOfFin h).strictMono hij).le))]

/-- `VBs` does not see a relabelling of the points. -/
lemma VBs_perm {N : ℕ} (σ : Equiv.Perm (Fin (N + 1))) (f w : Fin (N + 1) → ℚ) (d : ℕ) :
    VBs (f ∘ σ) (w ∘ σ) d = VBs f w d := by
  classical
  unfold VBs
  refine Finset.sum_nbij' (fun X => X.image σ) (fun Y => Y.image σ.symm) ?_ ?_ ?_ ?_ ?_
  · intro X hX
    simp only [mem_powersetCard, subset_univ, true_and] at hX ⊢
    rw [card_image_of_injective _ σ.injective, hX]
  · intro X hX
    simp only [mem_powersetCard, subset_univ, true_and] at hX ⊢
    rw [card_image_of_injective _ σ.symm.injective, hX]
  · intro X _; simp [image_image]
  · intro X _; simp [image_image]
  · intro X _
    rw [prod_image (fun a _ b _ e => σ.injective e), Pp_image f σ X (σ.injective.injOn)]
    rfl

lemma signM_swap {N : ℕ} (i j : Fin (N + 1)) :
    (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ) j i = -(signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ) i j := by
  simp only [signM]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [if_neg (not_lt.2 h.le), if_pos h, if_pos h]
  · simp
  · rw [if_pos h, if_neg (not_lt.2 h.le), if_pos h]; ring

/-- the sign-matrix form of a strict-order skew sum, for weakly increasing `t` and data equal on ties. -/
theorem signM_form {N : ℕ} (t F Gf : Fin (N + 1) → ℚ) (ht : Monotone t)
    (htie : ∀ i j, t i = t j → F i * Gf j = F j * Gf i) :
    ∑ i, ∑ j, F i * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ) i j * Gf j
      = ∑ i, ∑ j, if t i < t j then F i * Gf j - Gf i * F j else 0 := by
  have hR : (∑ i, ∑ j, if t i < t j then F i * Gf j - Gf i * F j else 0)
      = ∑ i, ∑ j, ((if t i < t j then (1 : ℚ) else 0) - (if t j < t i then 1 else 0)) * (F i * Gf j) := by
    have e1 : (∑ i, ∑ j, if t i < t j then F i * Gf j - Gf i * F j else 0)
        = (∑ i, ∑ j, (if t i < t j then (1 : ℚ) else 0) * (F i * Gf j))
          - ∑ i, ∑ j, (if t i < t j then (1 : ℚ) else 0) * (F j * Gf i) := by
      rw [← sum_sub_distrib]; refine sum_congr rfl fun i _ => ?_
      rw [← sum_sub_distrib]; refine sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    rw [e1, Finset.sum_comm (f := fun i j => (if t i < t j then (1 : ℚ) else 0) * (F j * Gf i)),
      ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]; refine sum_congr rfl fun j _ => ?_
    ring
  rw [hR]
  have hD : ∀ i j, F i * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ) i j * Gf j
      = ((if t i < t j then (1 : ℚ) else 0) - (if t j < t i then 1 else 0)) * (F i * Gf j)
        + (if t i = t j then (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ) i j * (F i * Gf j) else 0) := by
    intro i j
    rcases lt_trichotomy (t i) (t j) with h | h | h
    · have hij : i < j := lt_of_not_ge fun hji => (not_le.2 h) (ht hji)
      rw [if_pos h, if_neg (not_lt.2 h.le), if_neg h.ne]
      simp [signM, hij]
    · rw [if_neg (by rw [h]; exact lt_irrefl _), if_neg (by rw [h]; exact lt_irrefl _), if_pos h]; ring
    · have hji : j < i := lt_of_not_ge fun hij => (not_le.2 h) (ht hij)
      rw [if_neg (not_lt.2 h.le), if_pos h, if_neg h.ne']
      simp [signM, hji, not_lt.2 hji.le]
  simp_rw [hD, sum_add_distrib]
  have hT : ∑ i, ∑ j, (if t i = t j then (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ) i j * (F i * Gf j) else 0) = 0 := by
    have key : ∑ i, ∑ j, (if t i = t j then (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ) i j * (F i * Gf j) else 0)
        = ∑ i, ∑ j, -(if t i = t j then (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ) i j * (F i * Gf j) else 0) := by
      rw [Finset.sum_comm]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      by_cases h : t j = t i
      · rw [if_pos h, if_pos h.symm, signM_swap, htie j i h]; ring
      · rw [if_neg h, if_neg (Ne.symm h)]; ring
    simp only [sum_neg_distrib] at key
    linarith
  rw [hT, add_zero]

/-- the points `x = 0..n`, `y_x = (2x-n)^2`. -/
def yv (n : ℕ) (x : Fin (n + 1)) : ℚ := (2 * ((x : ℕ) : ℚ) - n) ^ 2

lemma choose_of_yv (n : ℕ) (x x' : Fin (n + 1)) (h : yv n x = yv n x') :
    (n.choose x : ℚ) = n.choose x' := by
  unfold yv at h
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h1 | h1
  · have : (x : ℕ) = x' := by exact_mod_cast (by linarith : ((x : ℕ) : ℚ) = x')
    rw [this]
  · have : n = (x : ℕ) + x' := by exact_mod_cast (by linarith : (n : ℚ) = (x : ℕ) + (x' : ℕ))
    rw [Nat.choose_symm_of_eq_add this]

/-- the sorting permutation and the sorted data. -/
noncomputable def σs (n : ℕ) : Equiv.Perm (Fin (n + 1)) := Tuple.sort (yv n)

lemma mono_sort (n : ℕ) : Monotone (yv n ∘ σs n) := Tuple.monotone_sort _

/-- the sorted row of `K_{2p}`: `ν_i E_p(t_i)`. -/
noncomputable def rw0 (n p : ℕ) (i : Fin (n + 1)) : ℚ :=
  (n.choose (σs n i) : ℚ) * (Ev n p).eval (yv n (σs n i))

/-- **`⟨K_{2p}, K_{2q}⟩_B` in sign-matrix form** for the sorted points. -/
theorem gram_core (n p q : ℕ) :
    ∑ i, ∑ j, rw0 n p i * (signM n : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) i j * rw0 n q j
      = Bali.GP.G n p q := by
  rw [signM_form (yv n ∘ σs n) (rw0 n p) (rw0 n q) (mono_sort n)]
  · unfold Bali.GP.G Bali.GP.brB
    rw [← Fin.sum_univ_eq_sum_range (fun x => ∑ x' ∈ range (n + 1), _) (n + 1)]
    conv_rhs => rw [← Equiv.sum_comp (σs n)]
    refine sum_congr rfl fun i _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun x' => _) (n + 1)]
    conv_rhs => rw [← Equiv.sum_comp (σs n)]
    refine sum_congr rfl fun j _ => ?_
    have hi := (σs n i).isLt
    have hj := (σs n j).isLt
    simp only [rw0, Function.comp, yv]
    rw [K_even n _ _ (by omega), K_even n _ _ (by omega), K_even n _ _ (by omega), K_even n _ _ (by omega)]
    have hc : ((2 * ((σs n i : ℕ) : ℤ) - n) ^ 2 < (2 * ((σs n j : ℕ) : ℤ) - n) ^ 2)
        ↔ ((2 * ((σs n i : ℕ) : ℚ) - n) ^ 2 < (2 * ((σs n j : ℕ) : ℚ) - n) ^ 2) := by
      constructor <;> intro h <;> exact_mod_cast h
    by_cases h : (2 * ((σs n i : ℕ) : ℚ) - n) ^ 2 < (2 * ((σs n j : ℕ) : ℚ) - n) ^ 2
    · have h' := hc.2 h
      simp only [h, h', if_true]; ring
    · have h' : ¬ ((2 * ((σs n i : ℕ) : ℤ) - n) ^ 2 < (2 * ((σs n j : ℕ) : ℤ) - n) ^ 2) :=
        fun h' => h (hc.1 h')
      simp only [h, h', if_false]
  · intro i j hij
    simp only [rw0, Function.comp] at hij ⊢
    rw [hij, choose_of_yv n _ _ hij]

/-- **Gram matrix = sign-matrix form** for the sorted points. -/
theorem gram_eq (n k : ℕ) (a b : Fin k × Fin 2) :
    ((Bm n k * Mpow (m := k) (yv n ∘ σs n) (fun i => (n.choose (σs n i) : ℚ))) *
        (signM n : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) *
        (Bm n k * Mpow (m := k) (yv n ∘ σs n) (fun i => (n.choose (σs n i) : ℚ)))ᵀ) a b
      = Bali.GP.G n (eι k a) (eι k b) := by
  set M := Bm n k * Mpow (m := k) (yv n ∘ σs n) (fun i => (n.choose (σs n i) : ℚ)) with hM
  have hl : (M * (signM n : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) * Mᵀ) a b
      = ∑ i, ∑ j, M a i * (signM n : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) i j * M b j := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, sum_mul]
    rw [Finset.sum_comm]
  rw [hl, ← gram_core]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  simp only [hM, BM_apply, rw0, Function.comp]

/-- the pairing matrix as a submatrix, and `pfP Ω = 2^k k!`. -/
def gOm (i j : ℕ) : ℚ :=
  if i / 2 = j / 2 then (if i % 2 = 0 ∧ j % 2 = 1 then 1 else if i % 2 = 1 ∧ j % 2 = 0 then -1 else 0) else 0

lemma Om_eq (k : ℕ) : (Bali.PfP.Om k : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    = (Matrix.of fun i j : Fin (2 * k) => gOm i j).submatrix (eι k) (eι k) := by
  ext ⟨i, p⟩ ⟨j, q⟩
  simp only [submatrix_apply, of_apply, eι_val, Bali.PfP.Om, gOm]
  have hi := i.isLt; have hj := j.isLt
  rcases fin2_cases p with rfl | rfl <;> rcases fin2_cases q with rfl | rfl <;>
    simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, add_zero] <;>
    split_ifs <;> first | rfl | omega | (exfalso; casesm* _ ∧ _ <;> omega) | (simp_all <;> omega) | (norm_num <;> omega)

lemma pfP_Om_val (k : ℕ) :
    pfP (Bali.PfP.Om k : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) = 2 ^ k * (k.factorial : ℚ) := by
  rw [Om_eq, Bali.PfB.pfP_eq_pf k _ (by
      intro i j; simp only [of_apply, gOm]; split_ifs <;> first | rfl | omega | (exfalso; casesm* _ ∧ _ <;> omega) | (simp_all <;> omega) | (norm_num <;> omega)),
    Bali.Pf.pf_triangular gOm k (by
      intro i c hi hc hc2; unfold gOm; rw [if_neg (by omega)])]
  rw [prod_eq_one, mul_one]
  intro i _
  unfold gOm
  rw [if_pos (by omega), if_pos (by omega)]

/-- **de Bruijn for paper 7, even rank, every `n`:** `V^B_{2k} = ∏_{a<2k} (2a)! · W(0,k)`. -/
theorem VB_even (n k : ℕ) :
    VBs (fun x : Fin (n + 1) => (2 * ((x : ℕ) : ℚ) - n) ^ 2) (fun x => (n.choose x : ℚ)) (2 * k)
      = (∏ a ∈ range (2 * k), ((2 * a).factorial : ℚ)) * Bali.GP.W n 0 k := by
  set M := Bm n k * Mpow (m := k) (yv n ∘ σs n) (fun i => (n.choose (σs n i) : ℚ))
  have h1 := pfP_deBruijn (R := ℚ) M
  rw [sum_minors_basis_change, sum_minors_mono _ _ (mono_sort n), pfP_J0, pfP_Om_val, det_Bm,
    VBvol_eq_VBs] at h1
  have hperm := VBs_perm (σs n) (yv n) (fun x => (n.choose (x : ℕ) : ℚ)) (2 * k)
  simp only [Function.comp_def] at hperm h1
  rw [hperm] at h1
  have hG : (M * (signM n : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) * Mᵀ)
      = (Matrix.of fun i j : Fin (2 * k) => Bali.GP.G n i j).submatrix (eι k) (eι k) := by
    ext a b; exact gram_eq n k a b
  rw [hG, Bali.PfB.pfP_eq_pf k (Matrix.of fun i j : Fin (2 * k) => Bali.GP.G n i j)
    (fun i j => Bali.GP.G_anti n i j)] at h1
  have hW := Bali.GP.W_eq_pf n 0 k
  simp only [zero_add] at hW
  rw [← hW] at h1
  have hP : (∏ a ∈ range (2 * k), (1 / ((2 * a).factorial : ℚ)))
      = 1 / ∏ a ∈ range (2 * k), ((2 * a).factorial : ℚ) := by
    rw [prod_div_distrib, prod_const_one]
  rw [hP] at h1
  have hP0 : (∏ a ∈ range (2 * k), ((2 * a).factorial : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.2 fun a _ => by positivity
  have h2 : (2 : ℚ) ^ k * (k.factorial : ℚ) ≠ 0 := by positivity
  unfold yv at h1
  field_simp at h1
  linear_combination -h1

/-! ## Step (4): odd rank, the bordered row `δ_∞` (pattern of `OddB.lean`) -/

open Bali.OddB Bali.Skew

/-- `Σ_x C(n,x) K_c(x;n) = 2^n δ_{c0}`. -/
lemma Ksum (n c : ℕ) :
    ∑ x ∈ range (n + 1), (n.choose x : ℚ) * Bali.GP.K n c x = if c = 0 then 2 ^ n else 0 := by
  simp_rw [Bali.GP.dual n c]
  rw [← mul_sum]
  rcases Nat.lt_or_ge n c with h | h
  · rw [Nat.choose_eq_zero_of_lt h, if_neg (by omega)]; simp
  · have hs : ∑ x ∈ range (n + 1), Bali.GP.K n x c = (Bali.GP.gf n c).eval 1 := by
      rw [eval_eq_sum_range' (Bali.GP.natDeg_gf n c h)]
      simp [Bali.GP.K]
    rw [hs]
    unfold Bali.GP.gf
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · norm_num
    · rw [if_neg (by omega)]; simp [zero_pow (by omega : c ≠ 0)]

/-- the total of a sorted row. -/
lemma rw0_sum (n p : ℕ) : ∑ i, rw0 n p i = if p = 0 then 2 ^ n else 0 := by
  have hif : (if p = 0 then (2 : ℚ) ^ n else 0) = if 2 * p = 0 then 2 ^ n else 0 := by simp
  rw [hif, ← Ksum n (2 * p), ← Fin.sum_univ_eq_sum_range (fun x => (n.choose x : ℚ) * Bali.GP.K n (2 * p) x) (n + 1)]
  conv_rhs => rw [← Equiv.sum_comp (σs n)]
  refine sum_congr rfl fun i _ => ?_
  have hi := (σs n i).isLt
  rw [rw0, K_even n _ _ (by omega)]; rfl

/-- the odd rows. -/
noncomputable def rO (n k : ℕ) : Fin (2 * k + 1) → Fin (n + 1) → ℚ := fun p => rw0 n p

/-- odd basis change. -/
noncomputable def Bo' (n k : ℕ) : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) ℚ :=
  fun p q => (Ev n p).coeff q

lemma det_Bo' (n k : ℕ) : det (Bo' n k) = ∏ a ∈ range (2 * k + 1), (1 / ((2 * a).factorial : ℚ)) := by
  rw [det_of_lowerTriangular, ← Fin.prod_univ_eq_prod_range (fun a => 1 / ((2 * a).factorial : ℚ))]
  · exact prod_congr rfl fun i _ => (EO_coeff n i).2.1
  · intro i j hij
    exact (EO_coeff n i).1 j (by simpa using hij)

lemma rO_basis (n k : ℕ) (p : Fin (2 * k + 1)) (i : Fin (n + 1)) :
    rO n k p i = ∑ q : Fin (2 * k + 1), Bo' n k p q * ((n.choose (σs n i) : ℚ) * (yv n (σs n i)) ^ (q : ℕ)) := by
  rw [rO, rw0]
  simp only [Bo']
  rw [Fin.sum_univ_eq_sum_range (fun q => (Ev n p).coeff q * ((n.choose (σs n i) : ℚ) * (yv n (σs n i)) ^ q)) (2 * k + 1),
    eval_eq_sum_range' (n := 2 * k + 1) (lt_of_le_of_lt (Ev_natDegree n _) p.isLt), mul_sum]
  exact sum_congr rfl fun q _ => by ring

lemma sum_rows_mono (n k : ℕ) :
    ∑ S ∈ (univ : Finset (Fin (n + 1))).powersetCard (2 * k + 1),
        det (Matrix.of fun p q : Fin (2 * k + 1) => rO n k p (Go S q))
      = det (Bo' n k) * VBvol (yv n ∘ σs n) (fun i => (n.choose (σs n i) : ℚ)) (2 * k + 1) := by
  unfold VBvol
  rw [mul_sum]
  refine sum_congr rfl fun S hS => ?_
  have h : S.card = 2 * k + 1 := (mem_powersetCard.1 hS).2
  have hGo : ∀ q, Go S q = S.orderEmbOfFin h q := fun q => by simp [Go, h]
  have : (Matrix.of fun p q : Fin (2 * k + 1) => rO n k p (Go S q))
      = Bo' n k * ((vandermonde (fun q => yv n (σs n (Go S q))))ᵀ *
          diagonal (fun q => (n.choose (σs n (Go S q)) : ℚ))) := by
    ext p q
    rw [of_apply, Matrix.mul_apply, rO_basis]
    refine sum_congr rfl fun r _ => ?_
    rw [Matrix.mul_diagonal, transpose_apply, vandermonde_apply]
    ring
  rw [this, det_mul, det_mul, det_transpose, det_diagonal, det_vandermonde, dif_pos h]
  simp only [hGo, Function.comp]
  congr 1
  rw [mul_comm]
  congr 1
  refine prod_congr rfl fun i _ => prod_congr rfl fun j hj => ?_
  have hij : i < j := mem_Ioi.1 hj
  exact (abs_of_nonneg (sub_nonneg.2 (mono_sort n ((S.orderEmbOfFin h).strictMono hij).le))).symm

/-- border vector `b_p = 2^n δ_{p0}` and the bordered Gram matrix. -/
noncomputable def bd (n p : ℕ) : ℚ := if p = 0 then 2 ^ n else 0

noncomputable def gA (n k i j : ℕ) : ℚ :=
  if i < 2 * k + 1 then (if j < 2 * k + 1 then Bali.GP.G n i j else bd n i)
  else (if j < 2 * k + 1 then -bd n j else 0)

lemma skew_rO (n k : ℕ) (p q : Fin (2 * k + 1)) : skew (rO n k p) (rO n k q) = Bali.GP.G n p q := by
  rw [skew_eq, ← gram_core]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun j _ => by simp only [rO]; ring

lemma gramO_entry (n k : ℕ) (a b : Fin (k + 1) × Fin 2) :
    (Ma (rO n k) * (signM (n + 1) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℚ) * (Ma (rO n k))ᵀ) a b
      = gA n k (sl a) (sl b) := by
  rw [gram_eq_skew]
  unfold Ma gA
  by_cases ha : sl a < 2 * k + 1 <;> by_cases hb : sl b < 2 * k + 1
  · rw [dif_pos ha, dif_pos hb, if_pos ha, if_pos hb, skew_ext_ext, skew_rO]
  · rw [dif_pos ha, dif_neg hb, if_pos ha, if_neg hb, skew_ext_dI]
    simp only [rO]; rw [rw0_sum, bd]
  · rw [dif_neg ha, dif_pos hb, if_neg ha, if_pos hb, skew_dI_ext]
    simp only [rO]; rw [rw0_sum, bd]
  · rw [dif_neg ha, dif_neg hb, if_neg ha, if_neg hb, skew_dI_dI]

lemma gA_skew (n k : ℕ) (i j : ℕ) : gA n k j i = -gA n k i j := by
  unfold gA
  split_ifs <;> first | rw [Bali.GP.G_anti] | ring

/-- the relabelling `0 ↦ ∞`, `j+1 ↦ j`. -/
noncomputable def cR (k : ℕ) : Equiv.Perm (Fin (2 * (k + 1))) := (Fin.cycleRange (Fin.last (2 * k + 1))).symm

lemma sign_cR (k : ℕ) : (Equiv.Perm.sign (cR k) : ℚ) = -1 := by
  unfold cR
  rw [Equiv.Perm.sign_symm, Fin.sign_cycleRange, Fin.val_last]
  push_cast
  rw [pow_succ, pow_mul]; norm_num

lemma cR_zero (k : ℕ) : ((cR k 0 : Fin (2 * (k + 1))) : ℕ) = 2 * k + 1 := by
  unfold cR
  rw [Fin.cycleRange_symm_zero]; rfl

lemma cR_succ (k : ℕ) (j : Fin (2 * k + 1)) : ((cR k j.succ : Fin (2 * (k + 1))) : ℕ) = j := by
  unfold cR
  rw [Fin.cycleRange_symm_succ, Fin.succAbove_last]; rfl

/-- **the bordered Pfaffian**: `Pf(A ∘ cR) = -2^n W(1,k)`. -/
lemma pf_bordered (n k : ℕ) :
    Bali.Pf.pf (k + 1) ((Matrix.of fun i j : Fin (2 * (k + 1)) => gA n k i j).submatrix (cR k) (cR k))
      = -(2 ^ n) * Bali.GP.W n 1 k := by
  rw [Bali.Pf.pf_first_row]
  · have h01 : ((Matrix.of fun i j : Fin (2 * (k + 1)) => gA n k i j).submatrix (cR k) (cR k)) 0 1
        = -(2 ^ n) := by
      simp only [submatrix_apply, of_apply, gA]
      rw [cR_zero, show (1 : Fin (2 * (k + 1))) = (0 : Fin (2 * k + 1)).succ from rfl, cR_succ]
      simp [bd]
    rw [h01, Bali.GP.W_eq_pf]
    congr 2
    ext i j
    simp only [submatrix_apply, of_apply, gA]
    rw [show (i.succ.succ : Fin (2 * (k + 1))) = (i.succ : Fin (2 * k + 1)).succ from rfl,
      show (j.succ.succ : Fin (2 * (k + 1))) = (j.succ : Fin (2 * k + 1)).succ from rfl, cR_succ, cR_succ]
    have hi := i.isLt; have hj := j.isLt
    simp only [Fin.val_succ]
    rw [if_pos (by omega), if_pos (by omega)]
    congr 1 <;> ring
  · intro j hj
    simp only [submatrix_apply, of_apply, gA]
    have hj' : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext (by simp [h]))
    rw [cR_zero, cR_succ, if_neg (by omega), if_pos j.isLt, bd, if_neg hj']
    ring

/-- **de Bruijn for paper 7, odd rank, every `n`:** `V^B_{2k+1} = 2^n ∏_{a≤2k} (2a)! · W(1,k)`. -/
theorem VB_odd (n k : ℕ) :
    VBs (fun x : Fin (n + 1) => (2 * ((x : ℕ) : ℚ) - n) ^ 2) (fun x => (n.choose x : ℚ)) (2 * k + 1)
      = 2 ^ n * (∏ a ∈ range (2 * k + 1), ((2 * a).factorial : ℚ)) * Bali.GP.W n 1 k := by
  have h1 := pfP_deBruijn (R := ℚ) (Ma (m := k) (rO n k))
  rw [sum_aug, sum_rows_mono, pfP_J0, pfP_Om_val, det_Bo', VBvol_eq_VBs] at h1
  have hperm := VBs_perm (σs n) (yv n) (fun x => (n.choose (x : ℕ) : ℚ)) (2 * k + 1)
  simp only [Function.comp_def] at hperm h1
  rw [hperm] at h1
  have hG : (Ma (rO n k) * (signM (n + 1) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℚ) * (Ma (rO n k))ᵀ)
      = (Matrix.of fun i j : Fin (2 * (k + 1)) => gA n k i j).submatrix (eι (k + 1)) (eι (k + 1)) := by
    ext a b; exact gramO_entry n k a b
  rw [hG, Bali.PfB.pfP_eq_pfF] at h1
  have hrel := Bali.PfB.pfF_relabel (k + 1) (Matrix.of fun i j : Fin (2 * (k + 1)) => gA n k i j) (cR k)
  rw [sign_cR, Bali.PfB.pfF_eq_pf (k + 1) _ (fun i j => by simp only [submatrix_apply, of_apply]; exact gA_skew n k _ _),
    pf_bordered] at hrel
  have hP : (∏ a ∈ range (2 * k + 1), (1 / ((2 * a).factorial : ℚ)))
      = 1 / ∏ a ∈ range (2 * k + 1), ((2 * a).factorial : ℚ) := by
    rw [prod_div_distrib, prod_const_one]
  rw [hP] at h1
  have hP0 : (∏ a ∈ range (2 * k + 1), ((2 * a).factorial : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.2 fun a _ => by positivity
  have h2 : (2 : ℚ) ^ (k + 1) * ((k + 1).factorial : ℚ) ≠ 0 := by positivity
  have hF : Bali.PfB.pfF (k + 1) (Matrix.of fun i j : Fin (2 * (k + 1)) => gA n k i j)
      = 2 ^ (k + 1) * ((k + 1).factorial : ℚ) * (2 ^ n * Bali.GP.W n 1 k) := by
    linear_combination hrel
  rw [hF] at h1
  unfold yv at h1
  field_simp at h1
  linear_combination -h1

/-! ## Step (5): cor:B = de Bruijn + `corB_*` (a second proof of conjecture B for `d ≤ m+1`) -/

/-- `V^B_d(n)` in the point form. -/
noncomputable def Vn (n d : ℕ) : ℚ :=
  VBs (fun x : Fin (n + 1) => (2 * ((x : ℕ) : ℚ) - n) ^ 2) (fun x => (n.choose x : ℚ)) d

lemma P_succ (k : ℕ) : (∏ a ∈ range (2 * k + 1), ((2 * a).factorial : ℚ))
    = (∏ a ∈ range (2 * k), ((2 * a).factorial : ℚ)) * ((4 * k).factorial : ℚ) := by
  rw [prod_range_succ, show 2 * (2 * k) = 4 * k by ring]

lemma P_succ' (k : ℕ) : (∏ a ∈ range (2 * (k + 1)), ((2 * a).factorial : ℚ))
    = (∏ a ∈ range (2 * k + 1), ((2 * a).factorial : ℚ)) * ((4 * k + 2).factorial : ℚ) := by
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, prod_range_succ, show 2 * (2 * k + 1) = 4 * k + 2 by ring]

lemma P_ne (d : ℕ) : (∏ a ∈ range d, ((2 * a).factorial : ℚ)) ≠ 0 :=
  prod_ne_zero_iff.2 fun a _ => by positivity

/-- one step `2k → 2k+1`. -/
lemma Vn_step_e (n k : ℕ) (hW : Bali.GP.W n 0 k ≠ 0) :
    Vn n (2 * k + 1) = Vn n (2 * k) * ((2 ^ n * ((4 * k).factorial : ℚ)) * (Bali.GP.W n 1 k / Bali.GP.W n 0 k)) := by
  unfold Vn; rw [VB_odd, VB_even, P_succ]; field_simp

/-- one step `2k+1 → 2k+2`. -/
lemma Vn_step_o (n k : ℕ) (hW : Bali.GP.W n 1 k ≠ 0) :
    Vn n (2 * (k + 1)) = Vn n (2 * k + 1) *
      (((4 * k + 2).factorial : ℚ) / 2 ^ n * (Bali.GP.W n 0 (k + 1) / Bali.GP.W n 1 k)) := by
  unfold Vn; rw [VB_odd, VB_even, P_succ']; field_simp

lemma Vn_zero (n : ℕ) : Vn n 0 = 1 := by
  have h := VB_even n 0
  simp only [mul_zero, prod_range_zero, one_mul, Bali.GP.W_zero] at h
  exact h

/-- **cor:B, odd `n = 2m+1`, via de Bruijn** (independent of the BKW/Racah route). -/
theorem conjB_odd_dB (m : ℕ) : ∀ d, d ≤ m + 1 →
    ((Vn (2 * m + 1) d : ℚ) : ℝ) = ∏ j ∈ range d, Bali.ConjB.crB m j (Bali.ConjBAll.Kc j)
  | 0, _ => by simp [Vn_zero]
  | d + 1, hd => by
    rw [prod_range_succ, ← conjB_odd_dB m d (by omega)]
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' d
    · rw [Vn_step_e _ k (Bali.GP.W0_pos_odd m k (by omega)).ne', Bali.ConjBAll.Kc_even,
        ← Bali.GP.corB_odd_even m k (by omega)]
      push_cast; ring
    · rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, Vn_step_o _ k (Bali.GP.W_pos_odd' m 1 k (by omega)).ne',
        Bali.ConjBAll.Kc_odd, ← Bali.GP.corB_odd_odd m k (by omega)]
      push_cast; ring

/-- **cor:B, even `n = 2m`, via de Bruijn.** -/
theorem conjB_even_dB (m : ℕ) : ∀ d, d ≤ m + 1 →
    ((Vn (2 * m) d : ℚ) : ℝ) = ∏ j ∈ range d, Bali.VE.crE m j (Bali.VE.Kc j)
  | 0, _ => by simp [Vn_zero]
  | d + 1, hd => by
    rw [prod_range_succ, ← conjB_even_dB m d (by omega)]
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' d
    · rw [Vn_step_e _ k (Bali.GP.W0_pos_even m k (by omega)).ne', Bali.VE.Kc_even,
        ← Bali.GP.corB_even_even m k (by omega)]
      push_cast; ring
    · rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, Vn_step_o _ k (Bali.GP.W_pos_even' m 1 k (by omega)).ne',
        Bali.VE.Kc_odd, ← Bali.GP.corB_even_odd m k (by omega)]
      push_cast; ring

/-! ### Comparison with `Bali.UN.conjB_*` (the first proof): same left side, same right side. -/

lemma Vn_odd_UN (m d : ℕ) :
    Vn (2 * m + 1) d = Bali.ShellX.VBs (fun x : Fin (2 * m + 2) => (2 * (x : ℚ) - (2 * m + 1)) ^ 2)
        (fun x => ((2 * m + 1).choose (x : ℕ) : ℚ)) d := by
  unfold Vn; push_cast; rfl

lemma Vn_even_UN (K d : ℕ) :
    Vn (2 * (K + 1)) d = Bali.ShellX.VBs (fun x : Fin (2 * K + 3) => (2 * (x : ℚ) - (2 * K + 2)) ^ 2)
        (fun x => ((2 * K + 2).choose (x : ℕ) : ℚ)) d := by
  unfold Vn
  congr 1
  funext x; push_cast; ring

/-- the de Bruijn route reproduces `UN.conjB_odd_all` for `d ≤ m+1`. -/
theorem conjB_odd_dB_UN (m d : ℕ) (hd : d ≤ m + 1) :
    ((Bali.ShellX.VBs (fun x : Fin (2 * m + 2) => (2 * (x : ℚ) - (2 * m + 1)) ^ 2)
        (fun x => ((2 * m + 1).choose (x : ℕ) : ℚ)) d : ℚ) : ℝ)
      = ∏ j ∈ range d, Bali.ConjB.crB m j (Bali.ConjBAll.Kc j) := by
  rw [← Vn_odd_UN]; exact conjB_odd_dB m d hd

/-- the de Bruijn route reproduces `UN.conjB_even_all` for `d ≤ K+2`. -/
theorem conjB_even_dB_UN (K d : ℕ) (hd : d ≤ K + 2) :
    ((Bali.ShellX.VBs (fun x : Fin (2 * K + 3) => (2 * (x : ℚ) - (2 * K + 2)) ^ 2)
        (fun x => ((2 * K + 2).choose (x : ℕ) : ℚ)) d : ℚ) : ℝ)
      = ∏ j ∈ range d, Bali.VE.crE (K + 1) j (Bali.VE.Kc j) := by
  rw [← Vn_even_UN]; exact conjB_even_dB (K + 1) d hd

/-- consistency: the statements are literally those of the first proof. -/
example (m d : ℕ) (hd : d ≤ m + 1) :
    conjB_odd_dB_UN m d hd = Bali.UN.conjB_odd_all m d := rfl
example (K d : ℕ) (hd : d ≤ K + 2) :
    conjB_even_dB_UN K d hd = Bali.UN.conjB_even_all K d := rfl

end Bali.GPdB

#print axioms Bali.GPdB.K_EO
#print axioms Bali.GPdB.EO_coeff
#print axioms Bali.GPdB.VB_even
#print axioms Bali.GPdB.VB_odd
#print axioms Bali.GPdB.conjB_odd_dB
#print axioms Bali.GPdB.conjB_even_dB
#print axioms Bali.GPdB.conjB_odd_dB_UN
#print axioms Bali.GPdB.conjB_even_dB_UN
#print axioms Bali.GP.Cab_u
#print axioms Bali.GP.adjv_first
#print axioms Bali.GP.adjv_last

/-! # Stage 10 (2026-11-23): Paper 7 open items (A) closed form (iv), (B) S_{r,n/2} and BKW (5.6),
(C) d ≥ m+2 by the second route. Merged verbatim from `GPOpenScratch.lean` (2026-11-20);
namespace `Bali.GPOpen`. See docs/PAPER7_OPEN_ITEMS_2026-11-20.md. -/

section Stage10

/-!
# Paper 7 open items, scratch (2026-11-20).  See docs/PAPER7_OPEN_ITEMS_2026-11-20.md.
(C) `d ≥ m+2` without the first route;  (B3) eq:bkwratio = crB / crE;  (B2) quotient of BKW (5.6).
-/

open Finset

namespace Bali.GPOpen

/-! ## (C) beyond the shells: both sides vanish (second route, no `Bali.UN`) -/

lemma Pp_zero_of_tie {β : Type*} [LinearOrder β] (f : β → ℚ) (X : Finset β) (a b : β)
    (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b) (hf : f a = f b) : Bali.ShellX.Pp f X = 0 := by
  unfold Bali.ShellX.Pp
  rcases lt_or_gt_of_ne hab with h | h
  · exact prod_eq_zero ha (prod_eq_zero (mem_filter.2 ⟨hb, h⟩) (by rw [hf, sub_self, abs_zero]))
  · exact prod_eq_zero hb (prod_eq_zero (mem_filter.2 ⟨ha, h⟩) (by rw [hf, sub_self, abs_zero]))

/-- `V^B_d(n) = 0` for `d ≥ m+2` (pigeonhole: `y_x = (2x-n)^2` takes only `m+1` values). -/
theorem Vn_beyond (n d : ℕ) (hd : n / 2 + 2 ≤ d) : Bali.GPdB.Vn n d = 0 := by
  unfold Bali.GPdB.Vn Bali.ShellX.VBs
  refine sum_eq_zero fun X hX => ?_
  have hc : X.card = d := (mem_powersetCard.1 hX).2
  obtain ⟨a, ha, b, hb, hab, he⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (s := X) (t := range (n / 2 + 1)) (f := fun x : Fin (n + 1) => min (x : ℕ) (n - x))
    (by rw [card_range]; omega)
    (fun x _ => by
      have := x.2
      simp only [coe_range, Set.mem_Iio]
      omega)
  have ha2 := a.2
  have hb2 := b.2
  have hcase : (a : ℕ) = b ∨ (a : ℕ) + b = n := by
    have he' : min (a : ℕ) (n - a) = min (b : ℕ) (n - b) := he
    omega
  rw [Pp_zero_of_tie _ X a b ha hb hab ?_, mul_zero]
  rcases hcase with h | h
  · exact absurd (Fin.ext h) hab
  · have h' : ((a : ℕ) : ℚ) + ((b : ℕ) : ℚ) = n := by exact_mod_cast h
    have e : 2 * ((a : ℕ) : ℚ) - n = -(2 * ((b : ℕ) : ℚ) - n) := by linarith
    show (2 * ((a : ℕ) : ℚ) - n) ^ 2 = (2 * ((b : ℕ) : ℚ) - n) ^ 2
    rw [e]; ring

lemma crB_pole (H : ℕ) (K : ℝ) : Bali.ConjB.crB H (H + 1) K = 0 := by
  unfold Bali.ConjB.crB
  rw [show (2 * (H : ℝ) + 1) / 2 - ((H + 1 : ℕ) : ℝ) + 1 / 2 = 0 by push_cast; ring, Real.Gamma_zero]
  simp

lemma crE_pole (m : ℕ) (K : ℝ) : Bali.VE.crE m (m + 1) K = 0 := by
  unfold Bali.VE.crE
  rw [show (m : ℝ) - ((m + 1 : ℕ) : ℝ) + 1 = 0 by push_cast; ring, Real.Gamma_zero]
  simp

/-- **cor:B for every `d`, odd `n`, through the de Bruijn route only.** -/
theorem conjB_odd_all2 (m d : ℕ) :
    ((Bali.GPdB.Vn (2 * m + 1) d : ℚ) : ℝ) = ∏ j ∈ range d, Bali.ConjB.crB m j (Bali.ConjBAll.Kc j) := by
  rcases Nat.lt_or_ge d (m + 2) with h | h
  · exact Bali.GPdB.conjB_odd_dB m d (by omega)
  · rw [Vn_beyond (2 * m + 1) d (by omega), Rat.cast_zero, eq_comm]
    exact prod_eq_zero (mem_range.2 (show m + 1 < d by omega)) (crB_pole m _)

/-- **cor:B for every `d`, even `n`, through the de Bruijn route only.** -/
theorem conjB_even_all2 (m d : ℕ) :
    ((Bali.GPdB.Vn (2 * m) d : ℚ) : ℝ) = ∏ j ∈ range d, Bali.VE.crE m j (Bali.VE.Kc j) := by
  rcases Nat.lt_or_ge d (m + 2) with h | h
  · exact Bali.GPdB.conjB_even_dB m d (by omega)
  · rw [Vn_beyond (2 * m) d (by omega), Rat.cast_zero, eq_comm]
    exact prod_eq_zero (mem_range.2 (show m + 1 < d by omega)) (crE_pole m _)

/-! ## (B3) eq:bkwratio equals the factors `crB` / `crE` -/

open Real

/-- the right side of `eq:bkwratio` of the paper (`m = ⌊n/2⌋` passed separately). -/
noncomputable def bkwR (n m d : ℕ) : ℝ :=
  2 ^ n * (n.factorial : ℝ) * (d.factorial : ℝ) / (((n - d).factorial : ℝ) * ((d : ℝ) + 1))
    * (Gamma (1 + ((d : ℝ) + 1) / 2) / Gamma (1 + (d : ℝ) / 2))
    * (Gamma ((m : ℝ) + 1 - (d : ℝ) / 2) / Gamma ((m : ℝ) + 3 / 2 - (d : ℝ) / 2))
    * (Gamma ((m : ℝ) - d + 3 / 2) / (Gamma (3 / 2) * ((m - d).factorial : ℝ)))

lemma Gamma_three_half : Gamma (3 / 2 : ℝ) = √π / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  ring

lemma four_pow (k : ℕ) : (4 : ℝ) ^ (k + 1) = 2 * 2 ^ (2 * k + 1) := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring

lemma four_pow' (k : ℕ) : (4 : ℝ) ^ k = 2 ^ (2 * k) := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]

/-- `2^{d+1} d!/(d+1) · Γ((d+3)/2)/Γ((d+2)/2) = K_d`, division-free. -/
lemma kappa (d : ℕ) :
    2 ^ (d + 1) * (d.factorial : ℝ) * Gamma (1 + ((d : ℝ) + 1) / 2)
      = Bali.ConjBAll.Kc d * Gamma (1 + (d : ℝ) / 2) * ((d : ℝ) + 1) := by
  have hs : (0 : ℝ) < √π := Real.sqrt_pos.2 Real.pi_pos
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' d
  · rw [Bali.ConjBAll.Kc_even]
    unfold Bali.ConjB.Ke
    rw [show 1 + (((2 * k : ℕ) : ℝ) + 1) / 2 = ((k + 1 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half,
      show 1 + ((2 * k : ℕ) : ℝ) / 2 = (k : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial,
      show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k),
      Nat.factorial_succ k, four_pow]
    have h1 : (k.factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · rw [Bali.ConjBAll.Kc_odd]
    unfold Bali.ConjB.Ko
    rw [show 1 + (((2 * k + 1 : ℕ) : ℝ) + 1) / 2 = ((k + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial,
      show 1 + ((2 * k + 1 : ℕ) : ℝ) / 2 = ((k + 1 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
      Bali.ConjB.Gamma_half,
      show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ (2 * k + 1),
      Nat.factorial_succ k, four_pow, four_pow' k, show 2 * k + 1 + 1 = 2 * k + 2 by ring, pow_succ, pow_succ, pow_succ]
    have h1 : (k.factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma two_rpow_sub (d n : ℕ) : (2 : ℝ) ^ ((d : ℝ) - (n : ℝ)) = 2 ^ d / 2 ^ n := by
  rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_natCast]

/-- the algebra common to both parities of `n`. -/
lemma bkw_alg (P N D F M Kc g1 g0 gz gz' A g32 s d1 pd : ℝ)
    (hF : F ≠ 0) (hM : M ≠ 0) (hg0 : g0 ≠ 0) (hgz' : gz' ≠ 0) (hs : s ≠ 0) (hd1 : d1 ≠ 0) (hP : P ≠ 0)
    (h1 : 2 * pd * D * g1 = Kc * g0 * d1) (h2 : gz * gz' = F * (pd / P) * s) (h3 : g32 = s / 2) :
    P * N * D / (F * d1) * (g1 / g0) * (gz / gz') * (A / (g32 * M)) = Kc * N * A / (M * gz' ^ 2) := by
  have hK : Kc = 2 * pd * D * g1 / (g0 * d1) := by rw [eq_div_iff (mul_ne_zero hg0 hd1)]; linarith
  have hz : gz = F * (pd / P) * s / gz' := by rw [eq_div_iff hgz']; linarith
  rw [hK, hz, h3]
  field_simp

/-- **(B3), odd `n = 2m+1`:** the right side of `eq:bkwratio` is `crB m d (Kc d)`, for `d ≤ m`. -/
theorem bkwR_crB (m d : ℕ) (hd : d ≤ m) :
    bkwR (2 * m + 1) m d = Bali.ConjB.crB m d (Bali.ConjBAll.Kc d) := by
  have hs : (0 : ℝ) < √π := Real.sqrt_pos.2 Real.pi_pos
  have hdm : (d : ℝ) ≤ m := by exact_mod_cast hd
  have hL := Real.Gamma_mul_Gamma_add_half ((m : ℝ) + 1 - (d : ℝ) / 2)
  rw [show 2 * ((m : ℝ) + 1 - (d : ℝ) / 2) = ((2 * m + 1 - d : ℕ) : ℝ) + 1 by
      rw [Nat.cast_sub (by omega)]; push_cast; ring, Real.Gamma_nat_eq_factorial,
    show (1 : ℝ) - (((2 * m + 1 - d : ℕ) : ℝ) + 1) = (d : ℝ) - ((2 * m + 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub (by omega)]; push_cast; ring, two_rpow_sub,
    show (m : ℝ) + 1 - (d : ℝ) / 2 + 1 / 2 = (m : ℝ) + 3 / 2 - (d : ℝ) / 2 by ring] at hL
  unfold bkwR Bali.ConjB.crB
  rw [show (2 * (m : ℝ) + 1) / 2 - (d : ℝ) + 1 = (m : ℝ) - d + 3 / 2 by ring,
    show (2 * (m : ℝ) + 1) / 2 - (d : ℝ) + 1 / 2 = ((m - d : ℕ) : ℝ) + 1 by
      rw [Nat.cast_sub hd]; ring, Real.Gamma_nat_eq_factorial,
    show (2 * (m : ℝ) + 1 - d + 2) / 2 = (m : ℝ) + 3 / 2 - (d : ℝ) / 2 by ring]
  have key := bkw_alg (2 ^ (2 * m + 1)) ((2 * m + 1).factorial : ℝ) (d.factorial : ℝ)
    ((2 * m + 1 - d).factorial : ℝ) ((m - d).factorial : ℝ) (Bali.ConjBAll.Kc d)
    (Gamma (1 + ((d : ℝ) + 1) / 2)) (Gamma (1 + (d : ℝ) / 2)) (Gamma ((m : ℝ) + 1 - (d : ℝ) / 2))
    (Gamma ((m : ℝ) + 3 / 2 - (d : ℝ) / 2)) (Gamma ((m : ℝ) - d + 3 / 2)) (Gamma (3 / 2)) (√π) ((d : ℝ) + 1) (2 ^ d)
    (by positivity) (by positivity) (Real.Gamma_pos_of_pos (by positivity)).ne'
    (Real.Gamma_pos_of_pos (by linarith)).ne' hs.ne' (by positivity) (by positivity)
    (by have := kappa d; rw [pow_succ] at this; linarith)
    hL Gamma_three_half
  rw [key]

/-- **(B3), even `n = 2m`:** the right side of `eq:bkwratio` is `crE m d (Kc d)`, for `d ≤ m`. -/
theorem bkwR_crE (m d : ℕ) (hd : d ≤ m) :
    bkwR (2 * m) m d = Bali.VE.crE m d (Bali.VE.Kc d) := by
  rw [show Bali.VE.Kc d = Bali.ConjBAll.Kc d from rfl]
  have hs : (0 : ℝ) < √π := Real.sqrt_pos.2 Real.pi_pos
  have hdm : (d : ℝ) ≤ m := by exact_mod_cast hd
  have hL := Real.Gamma_mul_Gamma_add_half ((m : ℝ) + 1 / 2 - (d : ℝ) / 2)
  rw [show 2 * ((m : ℝ) + 1 / 2 - (d : ℝ) / 2) = ((2 * m - d : ℕ) : ℝ) + 1 by
      rw [Nat.cast_sub (by omega)]; push_cast; ring, Real.Gamma_nat_eq_factorial,
    show (1 : ℝ) - (((2 * m - d : ℕ) : ℝ) + 1) = (d : ℝ) - ((2 * m : ℕ) : ℝ) by
      rw [Nat.cast_sub (by omega)]; push_cast; ring, two_rpow_sub,
    show (m : ℝ) + 1 / 2 - (d : ℝ) / 2 + 1 / 2 = (m : ℝ) + 1 - (d : ℝ) / 2 by ring] at hL
  unfold bkwR Bali.VE.crE
  rw [show (m : ℝ) - (d : ℝ) + 1 = ((m - d : ℕ) : ℝ) + 1 by rw [Nat.cast_sub hd], Real.Gamma_nat_eq_factorial,
    show (2 * (m : ℝ) - d + 1) / 2 = (m : ℝ) + 1 / 2 - (d : ℝ) / 2 by ring,
    show (2 * (m : ℝ) - d + 3) / 2 = (m : ℝ) + 3 / 2 - (d : ℝ) / 2 by ring]
  have hg0 : Gamma (1 + (d : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hgz : Gamma ((m : ℝ) + 1 / 2 - (d : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hgz1 : Gamma ((m : ℝ) + 3 / 2 - (d : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hF : ((2 * m - d).factorial : ℝ) ≠ 0 := by positivity
  have hM : ((m - d).factorial : ℝ) ≠ 0 := by positivity
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  have hk := kappa d
  rw [pow_succ] at hk
  rw [Gamma_three_half]
  generalize Gamma (1 + ((d : ℝ) + 1) / 2) = g1 at *
  generalize Gamma (1 + (d : ℝ) / 2) = g0 at *
  generalize Gamma ((m : ℝ) + 1 / 2 - (d : ℝ) / 2) = gz at *
  generalize Gamma ((m : ℝ) + 1 - (d : ℝ) / 2) = gzh at *
  generalize Gamma ((m : ℝ) + 3 / 2 - (d : ℝ) / 2) = gz1 at *
  generalize Gamma ((m : ℝ) - d + 3 / 2) = A at *
  generalize Bali.ConjBAll.Kc d = Kc at *
  have hK : Kc = 2 ^ d * 2 * (d.factorial : ℝ) * g1 / (g0 * ((d : ℝ) + 1)) := by
    rw [eq_div_iff (mul_ne_zero hg0 hd1)]; linarith
  have hz : gzh = ((2 * m - d).factorial : ℝ) * (2 ^ d / 2 ^ (2 * m)) * √π / gz := by
    rw [eq_div_iff hgz]; linarith
  rw [hK, hz]
  field_simp

/-! ## (B2) the quotient of the right side of BKW (5.6) is `eq:bkwratio` -/

/-- the right side of BKW (5.6) as quoted in the paper, `N = n/2`, `⌊N⌋ = m`. -/
noncomputable def bkwT (n m r : ℕ) : ℝ :=
  2 ^ (r * n) / 2 ^ (r * (r - 1)) * (Gamma (1 + (r : ℝ) / 2) * Gamma ((m : ℝ) - (r : ℝ) / 2 + 3 / 2)
      / (Gamma (3 / 2) * Gamma ((m : ℝ) + 1)))
    * ∏ i ∈ Ico 1 r, ((i.factorial : ℝ) * (n.factorial : ℝ) * Gamma ((m : ℝ) - i + 3 / 2)
        / (Gamma (3 / 2) * ((n - i).factorial : ℝ) * ((m - i).factorial : ℝ)))

lemma bkwT_pos (n m r : ℕ) (hr : r ≤ m + 1) : 0 < bkwT n m r := by
  have h32 : 0 < Gamma (3 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have hrm : (r : ℝ) ≤ m + 1 := by exact_mod_cast hr
  unfold bkwT
  refine mul_pos (mul_pos (by positivity) (div_pos (mul_pos (Real.Gamma_pos_of_pos (by positivity))
    (Real.Gamma_pos_of_pos (by linarith))) (mul_pos h32 (Real.Gamma_pos_of_pos (by positivity))))) ?_
  refine prod_pos fun i hi => ?_
  have hi2 := (mem_Ico.1 hi).2
  have him : (i : ℝ) ≤ m := by exact_mod_cast (show i ≤ m by omega)
  have : 0 < Gamma ((m : ℝ) - i + 3 / 2) := Real.Gamma_pos_of_pos (by linarith)
  positivity

/-- **(B2)**: with `S_r = r! 4^{-r(r-1)/2} V_r`, the quotient of (5.6) at `r = d+1` and `r = d`
(times `4^d/(d+1)`) is the right side of `eq:bkwratio`; `1 ≤ d ≤ m`. -/
theorem bkwT_ratio (n m e : ℕ) (hd : e + 1 ≤ m) :
    bkwT n m (e + 2) / bkwT n m (e + 1) * (4 ^ (e + 1) / ((e + 1 : ℕ) + 1 : ℝ)) = bkwR n m (e + 1) := by
  have hp := bkwT_pos n m (e + 1) (by omega)
  have h32 : 0 < Gamma (3 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have hem : ((e : ℝ) + 1) ≤ m := by exact_mod_cast hd
  rw [div_mul_eq_mul_div, div_eq_iff hp.ne']
  unfold bkwT bkwR
  rw [Finset.prod_Ico_succ_top (by omega : 1 ≤ e + 1),
    show (e + 2) * n = (e + 1) * n + n by ring, show (e + 2) * (e + 2 - 1) = (e + 1) * (e + 1 - 1) + 2 * (e + 1) by
      rw [show e + 2 - 1 = e + 1 from rfl, show e + 1 - 1 = e from rfl]; ring,
    pow_add, pow_add, show (4 : ℝ) ^ (e + 1) = 2 ^ (2 * (e + 1)) by rw [four_pow'],
    show (m : ℝ) - ((e + 2 : ℕ) : ℝ) / 2 + 3 / 2 = (m : ℝ) + 1 - ((e + 1 : ℕ) : ℝ) / 2 by push_cast; ring,
    show (m : ℝ) - ((e + 1 : ℕ) : ℝ) / 2 + 3 / 2 = (m : ℝ) + 3 / 2 - ((e + 1 : ℕ) : ℝ) / 2 by ring,
    show (1 : ℝ) + ((e + 2 : ℕ) : ℝ) / 2 = 1 + (((e + 1 : ℕ) : ℝ) + 1) / 2 by push_cast; ring,
    Real.Gamma_nat_eq_factorial]
  have g0 : Gamma (1 + ((e + 1 : ℕ) : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have g1 : Gamma ((m : ℝ) + 3 / 2 - ((e + 1 : ℕ) : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by push_cast; linarith)).ne'
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  have hF : ((n - (e + 1)).factorial : ℝ) ≠ 0 := by positivity
  have hM : ((m - (e + 1)).factorial : ℝ) ≠ 0 := by positivity
  have hP2 : (2 : ℝ) ^ ((e + 1) * (e + 1 - 1)) ≠ 0 := by positivity
  have hP3 : (2 : ℝ) ^ (2 * (e + 1)) ≠ 0 := by positivity
  have he : ((e + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  generalize (∏ i ∈ Ico 1 (e + 1), ((i.factorial : ℝ) * (n.factorial : ℝ) * Gamma ((m : ℝ) - i + 3 / 2)
        / (Gamma (3 / 2) * ((n - i).factorial : ℝ) * ((m - i).factorial : ℝ)))) = P
  generalize Gamma (1 + ((e + 1 : ℕ) : ℝ) / 2) = a0 at g0 ⊢
  generalize Gamma ((m : ℝ) + 3 / 2 - ((e + 1 : ℕ) : ℝ) / 2) = c0 at g1 ⊢
  generalize Gamma (1 + (((e + 1 : ℕ) : ℝ) + 1) / 2) = a1
  generalize Gamma ((m : ℝ) + 1 - ((e + 1 : ℕ) : ℝ) / 2) = c1
  generalize Gamma ((m : ℝ) - ((e + 1 : ℕ) : ℝ) + 3 / 2) = A
  generalize Gamma (3 / 2 : ℝ) = h at h32 ⊢
  have h32' := h32.ne'
  field_simp

/-- **(B2), `d = 0`**: `V_1/V_0 = S_1`, and (5.6) at `r = 1` is `eq:bkwratio` at `d = 0` (both are `2^n`). -/
theorem bkwT_one (n m : ℕ) : bkwT n m 1 = bkwR n m 0 ∧ bkwR n m 0 = 2 ^ n := by
  have h32 : Gamma (3 / 2 : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hm1 : Gamma ((m : ℝ) + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hm3 : Gamma ((m : ℝ) + 3 / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have e1 : bkwR n m 0 = 2 ^ n := by
    unfold bkwR
    simp only [Nat.cast_zero, zero_div, add_zero, sub_zero, Nat.sub_zero, Nat.factorial_zero, Nat.cast_one,
      zero_add, Real.Gamma_one]
    rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, Real.Gamma_nat_eq_factorial]
    have hm : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  refine ⟨?_, e1⟩
  rw [e1]
  unfold bkwT
  simp only [Finset.Ico_self, Finset.prod_empty, Nat.cast_one, one_mul, Nat.sub_self, mul_zero, pow_zero, div_one,
    mul_one]
  rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, show (m : ℝ) - 1 / 2 + 3 / 2 = (m : ℝ) + 1 by ring]
  field_simp

end Bali.GPOpen

#print axioms Bali.GPOpen.Vn_beyond
#print axioms Bali.GPOpen.conjB_odd_all2
#print axioms Bali.GPOpen.conjB_even_all2
#print axioms Bali.GPOpen.kappa
#print axioms Bali.GPOpen.bkwR_crB
#print axioms Bali.GPOpen.bkwR_crE
#print axioms Bali.GPOpen.bkwT_ratio
#print axioms Bali.GPOpen.bkwT_one

/-! ## (B1) the sum over all `r`-tuples is `r!` times the sum over `r`-subsets -/

namespace Bali.GPOpen

section B1
open Classical

variable {α : Type*} [Fintype α] [LinearOrder α]

lemma fiber_card (r : ℕ) (X : Finset α) (hX : X.card = r) :
    (univ.filter (fun x : Fin r → α => Function.Injective x ∧ univ.image x = X)).card = r.factorial := by
  have hp : (univ : Finset (Equiv.Perm (Fin r))).card = r.factorial := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← hp]
  symm
  refine Finset.card_bij (fun σ _ => fun i => X.orderEmbOfFin hX (σ i)) ?_ ?_ ?_
  · intro σ _
    rw [mem_filter]
    refine ⟨mem_univ _, fun i j h => σ.injective ((X.orderEmbOfFin hX).injective h), ?_⟩
    ext a
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact Finset.orderEmbOfFin_mem X hX _
    · intro ha
      have ha' : a ∈ Set.range (X.orderEmbOfFin hX) := by rw [Finset.range_orderEmbOfFin]; exact ha
      obtain ⟨j, hj⟩ := ha'
      exact ⟨σ.symm j, by simp [hj]⟩
  · intro σ _ τ _ h
    exact Equiv.ext fun i => (X.orderEmbOfFin hX).injective (congrFun h i)
  · intro x hx
    obtain ⟨_, hinj, him⟩ := mem_filter.1 hx
    have hmem : ∀ i, x i ∈ X := fun i => him ▸ mem_image_of_mem x (mem_univ i)
    have hg : Function.Injective (fun i => (X.orderIsoOfFin hX).symm ⟨x i, hmem i⟩) := fun i j h =>
      hinj (congrArg Subtype.val ((X.orderIsoOfFin hX).symm.injective h))
    refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hg), mem_univ _, ?_⟩
    funext i
    show X.orderEmbOfFin hX ((X.orderIsoOfFin hX).symm ⟨x i, hmem i⟩) = x i
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp

/-- generic form of (B1). -/
theorem tuple_sum (f w : α → ℚ) (r : ℕ) :
    ∑ x : Fin r → α, (∏ i, w (x i)) * Bali.ShellX.Pp (f ∘ x) univ
      = (r.factorial : ℚ) * Bali.ShellX.VBs f w r := by
  unfold Bali.ShellX.VBs
  have h0 : ∀ x : Fin r → α, ¬ Function.Injective x → (∏ i, w (x i)) * Bali.ShellX.Pp (f ∘ x) univ = 0 := by
    intro x hx
    rw [Bali.ShellX.Pp_zero f x univ (by rw [coe_univ, Set.injOn_univ]; exact hx), mul_zero]
  have h1 : ∀ x : Fin r → α, Function.Injective x → (∏ i, w (x i)) * Bali.ShellX.Pp (f ∘ x) univ
      = (∏ a ∈ univ.image x, w a) * Bali.ShellX.Pp f (univ.image x) := by
    intro x hx
    rw [Bali.ShellX.Pp_image f x univ hx.injOn, prod_image (fun a _ b _ h => hx h)]
  rw [← sum_filter_add_sum_filter_not univ (fun x : Fin r → α => Function.Injective x),
    sum_eq_zero (s := univ.filter fun x : Fin r → α => ¬ Function.Injective x)
      (fun x hx => h0 x (mem_filter.1 hx).2), add_zero,
    sum_congr rfl (fun x hx => h1 x (mem_filter.1 hx).2),
    ← sum_fiberwise_of_maps_to (g := fun x : Fin r → α => univ.image x) (t := powersetCard r univ)
      (fun x hx => by
        rw [mem_powersetCard]
        exact ⟨subset_univ _, by rw [card_image_of_injective _ (mem_filter.1 hx).2, card_univ, Fintype.card_fin]⟩),
    mul_sum]
  refine sum_congr rfl fun X hX => ?_
  rw [sum_congr rfl (fun x hx => by rw [(mem_filter.1 hx).2]), sum_const, filter_filter,
    fiber_card r X (mem_powersetCard.1 hX).2, nsmul_eq_mul]

end B1

lemma pairs_card (r : ℕ) : ∑ i : Fin r, (univ.filter (fun j : Fin r => i < j)).card = r * (r - 1) / 2 := by
  have h : ∀ i : Fin r, (univ.filter (fun j : Fin r => i < j)).card = r - 1 - i := by
    intro i
    rw [show (univ.filter (fun j : Fin r => i < j)) = Ioi i by ext j; simp, Fin.card_Ioi]
  rw [Finset.sum_congr rfl (fun i _ => h i), Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r,
    Finset.sum_range_reflect (fun i => i) r, Finset.sum_range_id]

lemma Pp_scale (c : ℚ) (hc : 0 ≤ c) (r : ℕ) (g : Fin r → ℚ) :
    Bali.ShellX.Pp (fun i => c * g i) univ = c ^ (r * (r - 1) / 2) * Bali.ShellX.Pp g univ := by
  unfold Bali.ShellX.Pp
  rw [← pairs_card r, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_const, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [← mul_sub, abs_mul, abs_of_nonneg hc]

/-- `S_{r,n/2}` of BKW (5.6): the sum over **all** `r`-tuples `k ∈ {-n/2, …, n/2}^r` (`k_i = x_i - n/2`)
of `∏_{i<j} |k_i² - k_j²| ∏_i C(n, n/2 + k_i)`. -/
noncomputable def Stup (n r : ℕ) : ℚ :=
  ∑ x : Fin r → Fin (n + 1), (∏ i, (n.choose (x i) : ℚ))
    * Bali.ShellX.Pp ((fun a : Fin (n + 1) => (((a : ℕ) : ℚ) - n / 2) ^ 2) ∘ x) univ

/-- **(B1)**: `S_{r,n/2} = r! · 4^{-r(r-1)/2} · V^B_r(n)`. -/
theorem Stup_eq (n r : ℕ) :
    Stup n r = (r.factorial : ℚ) * (1 / 4) ^ (r * (r - 1) / 2) * Bali.GPdB.Vn n r := by
  have key := tuple_sum (fun x : Fin (n + 1) => (2 * ((x : ℕ) : ℚ) - n) ^ 2) (fun x => (n.choose x : ℚ)) r
  unfold Stup Bali.GPdB.Vn
  rw [show (r.factorial : ℚ) * (1 / 4) ^ (r * (r - 1) / 2)
        * Bali.ShellX.VBs (fun x : Fin (n + 1) => (2 * ((x : ℕ) : ℚ) - n) ^ 2) (fun x => (n.choose x : ℚ)) r
      = (1 / 4) ^ (r * (r - 1) / 2) * ((r.factorial : ℚ)
        * Bali.ShellX.VBs (fun x : Fin (n + 1) => (2 * ((x : ℕ) : ℚ) - n) ^ 2) (fun x => (n.choose x : ℚ)) r) by ring,
    ← key, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  have e : ((fun a : Fin (n + 1) => (((a : ℕ) : ℚ) - n / 2) ^ 2) ∘ x)
      = fun i => (1 / 4 : ℚ) * ((fun a : Fin (n + 1) => (2 * ((a : ℕ) : ℚ) - n) ^ 2) ∘ x) i := by
    funext i; simp only [Function.comp_apply]; ring
  rw [e, Pp_scale _ (by norm_num)]
  ring

end Bali.GPOpen

#print axioms Bali.GPOpen.tuple_sum
#print axioms Bali.GPOpen.Stup_eq

/-! ## (B) assembled: BKW (5.6), as quoted in the paper, for `N = n/2`, `1 ≤ r ≤ m+1`, from cor:B -/

namespace Bali.GPOpen
open Real

lemma half_exp (e : ℕ) : (e + 2) * (e + 2 - 1) / 2 = (e + 1) * (e + 1 - 1) / 2 + (e + 1) := by
  rw [show e + 2 - 1 = e + 1 from rfl, show e + 1 - 1 = e from rfl,
    show (e + 2) * (e + 1) = (e + 1) * e + 2 * (e + 1) by ring, Nat.add_mul_div_left _ _ (by norm_num)]

theorem bkw56_core (n m : ℕ) (cr : ℕ → ℝ)
    (hV : ∀ d ≤ m + 1, ((Bali.GPdB.Vn n d : ℚ) : ℝ) = ∏ j ∈ range d, cr j)
    (hcr : ∀ d ≤ m, bkwR n m d = cr d) :
    ∀ e, e ≤ m → ((Stup n (e + 1) : ℚ) : ℝ) = bkwT n m (e + 1) := by
  intro e
  induction e with
  | zero =>
    intro _
    have h1 := hV 1 (by omega)
    rw [prod_range_one] at h1
    rw [Stup_eq, (bkwT_one n m).1, hcr 0 (Nat.zero_le _), ← h1]
    simp
  | succ e ih =>
    intro he
    have ih' := ih (by omega)
    show ((Stup n (e + 2) : ℚ) : ℝ) = bkwT n m (e + 2)
    rw [Stup_eq] at ih' ⊢
    have h2 := hV (e + 2) (by omega)
    rw [prod_range_succ, ← hV (e + 1) (by omega), ← hcr (e + 1) he, ← bkwT_ratio n m e he] at h2
    have hp := (bkwT_pos n m (e + 1) (by omega)).ne'
    rw [half_exp, pow_add, show (e + 2).factorial = (e + 2) * (e + 1).factorial from Nat.factorial_succ (e + 1)]
    push_cast at ih' h2 ⊢
    rw [h2]
    generalize bkwT n m (e + 1) = T1 at *
    generalize bkwT n m (e + 2) = T2 at *
    generalize ((Bali.GPdB.Vn n (e + 1) : ℚ) : ℝ) = V at *
    have he2 : (e : ℝ) + 2 ≠ 0 := by positivity
    have he1 : (e : ℝ) + 1 + 1 ≠ 0 := by positivity
    have hc : ((e : ℝ) + 2) * (1 / 4) ^ (e + 1) * (T2 / T1 * (4 ^ (e + 1) / ((e : ℝ) + 1 + 1))) * T1 = T2 := by
      have h4 : ((1 : ℝ) / 4) ^ (e + 1) * 4 ^ (e + 1) = 1 := by rw [← mul_pow]; norm_num
      field_simp
      linear_combination (T2 * ((e : ℝ) + 2)) * h4
    linear_combination (((e : ℝ) + 2) * (1 / 4) ^ (e + 1) * (T2 / T1 * (4 ^ (e + 1) / ((e : ℝ) + 1 + 1)))) * ih' + hc

/-- **BKW (5.6) for `N = n/2`, `n = 2m+1`, `1 ≤ r ≤ m+1`**, derived from cor:B (de Bruijn route). -/
theorem bkw56_odd (m e : ℕ) (he : e ≤ m) :
    ((Stup (2 * m + 1) (e + 1) : ℚ) : ℝ) = bkwT (2 * m + 1) m (e + 1) :=
  bkw56_core _ m _ (fun d _ => conjB_odd_all2 m d) (fun d hd => bkwR_crB m d hd) e he

/-- **BKW (5.6) for `N = n/2`, `n = 2m`, `1 ≤ r ≤ m+1`**. -/
theorem bkw56_even (m e : ℕ) (he : e ≤ m) :
    ((Stup (2 * m) (e + 1) : ℚ) : ℝ) = bkwT (2 * m) m (e + 1) :=
  bkw56_core _ m _ (fun d _ => conjB_even_all2 m d) (fun d hd => bkwR_crE m d hd) e he

end Bali.GPOpen

#print axioms Bali.GPOpen.bkw56_odd
#print axioms Bali.GPOpen.bkw56_even

/-! ## (A) Knuth's identity for `pfS`, and its instance on the windows of `G` -/

namespace Bali.GPOpen
open Bali.GP

/-- move the first entry to position `p`. -/
def rt (p i : ℕ) : ℕ := if i < p then i + 1 else if i = p then 0 else i

lemma rt_succ (p i : ℕ) : rt (p + 1) i = rt p (tw p i) := by
  unfold rt tw; split_ifs <;> omega

theorem pfS_rot (g : ℕ → ℕ → ℚ) (hg : ∀ a b, g a b = -g b a) (n : ℕ) (e : ℕ → ℕ) :
    ∀ p, p < 2 * n → pfS g n (fun i => e (rt p i)) = (-1) ^ p * pfS g n e
  | 0, _ => by
    rw [pow_zero, one_mul]
    refine pfS_congr g n _ _ (fun i _ => ?_)
    have : rt 0 i = i := by unfold rt; split_ifs <;> omega
    rw [this]
  | p + 1, hp => by
    have h := pfS_tw g hg n (fun i => e (rt p i)) p hp
    rw [pfS_rot g hg n e p (by omega)] at h
    rw [show (fun i => e (rt (p + 1) i)) = (fun x => (fun i => e (rt p i)) (tw p x)) from
      funext fun i => by rw [rt_succ], h, pow_succ]
    ring

def cons (x : ℕ) (e : ℕ → ℕ) (i : ℕ) : ℕ := if i = 0 then x else e (i - 1)

lemma pfS_cons (g : ℕ → ℕ → ℚ) (q : ℕ) (x : ℕ) (e : ℕ → ℕ) :
    pfS g (q + 1) (cons x e) = ∑ j ∈ range (2 * q + 1), g x (e j) * adjv g q e j := by
  rw [pfS_succ]
  refine sum_congr rfl fun j _ => ?_
  unfold adjv
  have c0 : cons x e 0 = x := by simp [cons]
  have c1 : cons x e (j + 1) = e j := by simp [cons]
  have c2 : (fun i => cons x e (sk j i + 1)) = (fun i => e (sk j i)) := by funext i; simp [cons]
  rw [c0, c1, c2]; ring

def e1 (E : ℕ → ℕ) (i : ℕ) : ℕ := if i = 0 then E 0 else E (i + 1)
def e3 (E : ℕ → ℕ) (i : ℕ) : ℕ := E (i + 1)

/-- **Knuth's identity** (Pfaffian Pluecker relation), in kernel form: for the sequence
`E = (a, b, I, c, d)` (`|I| = 2q`), with `e3 = (b, I, c, d)` and `e1 = (a, I)`. -/
theorem knuth_core (g : ℕ → ℕ → ℚ) (hg : ∀ a b, g a b = -g b a) (q : ℕ) (E : ℕ → ℕ) :
    adjv g (q + 1) (e3 E) 0 * pfS g (q + 1) (cons (e3 E 0) (e1 E))
      + adjv g (q + 1) (e3 E) (2 * q + 1) * pfS g (q + 1) (cons (e3 E (2 * q + 1)) (e1 E))
      + adjv g (q + 1) (e3 E) (2 * q + 2) * pfS g (q + 1) (cons (e3 E (2 * q + 2)) (e1 E))
    = -(pfS g (q + 2) E * pfS g q (fun i => E (i + 2))) := by
  have hR0 : ∀ l, 1 ≤ l → l ≤ 2 * q →
      ∑ j ∈ range (2 * q + 1), g (e3 E l) (e1 E j) * adjv g q (e1 E) j = 0 := by
    intro l h1 h2
    have := adj_ker g hg q (e1 E) l (by omega)
    rw [show e1 E l = e3 E l by unfold e1 e3; rw [if_neg (by omega)]] at this
    exact this
  have hC0 : ∀ j, 1 ≤ j → j ≤ 2 * q →
      ∑ l ∈ range (2 * (q + 1) + 1), g (e1 E j) (e3 E l) * adjv g (q + 1) (e3 E) l = 0 := by
    intro j h1 h2
    have := adj_ker g hg (q + 1) (e3 E) j (by omega)
    rw [show e3 E j = e1 E j by unfold e1 e3; rw [if_neg (by omega)]] at this
    exact this
  have hC : ∑ l ∈ range (2 * (q + 1) + 1), g (e1 E 0) (e3 E l) * adjv g (q + 1) (e3 E) l = pfS g (q + 2) E := by
    have := pfS_cons g (q + 1) (E 0) (e3 E)
    rw [show cons (E 0) (e3 E) = E from funext fun i => by
      unfold cons e3
      split_ifs with h
      · rw [h]
      · congr 1; omega] at this
    rw [this]
    rfl
  have hD : ∑ l ∈ range (2 * (q + 1) + 1), adjv g (q + 1) (e3 E) l
        * ∑ j ∈ range (2 * q + 1), g (e3 E l) (e1 E j) * adjv g q (e1 E) j
      = -∑ j ∈ range (2 * q + 1), adjv g q (e1 E) j
        * ∑ l ∈ range (2 * (q + 1) + 1), g (e1 E j) (e3 E l) * adjv g (q + 1) (e3 E) l := by
    simp only [mul_sum]
    rw [sum_comm, ← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun l _ => ?_
    rw [hg (e3 E l) (e1 E j)]; ring
  have hRHS : ∑ j ∈ range (2 * q + 1), adjv g q (e1 E) j
        * ∑ l ∈ range (2 * (q + 1) + 1), g (e1 E j) (e3 E l) * adjv g (q + 1) (e3 E) l
      = adjv g q (e1 E) 0 * pfS g (q + 2) E := by
    rw [sum_eq_single 0 (fun j hj hj0 => by
        rw [hC0 j (by omega) (by have := mem_range.1 hj; omega), mul_zero])
      (fun h => absurd (mem_range.2 (by omega)) h), hC]
  have hLHS : ∑ l ∈ range (2 * (q + 1) + 1), adjv g (q + 1) (e3 E) l
        * ∑ j ∈ range (2 * q + 1), g (e3 E l) (e1 E j) * adjv g q (e1 E) j
      = adjv g (q + 1) (e3 E) 0 * ∑ j ∈ range (2 * q + 1), g (e3 E 0) (e1 E j) * adjv g q (e1 E) j
        + adjv g (q + 1) (e3 E) (2 * q + 1)
          * ∑ j ∈ range (2 * q + 1), g (e3 E (2 * q + 1)) (e1 E j) * adjv g q (e1 E) j
        + adjv g (q + 1) (e3 E) (2 * q + 2)
          * ∑ j ∈ range (2 * q + 1), g (e3 E (2 * q + 2)) (e1 E j) * adjv g q (e1 E) j := by
    rw [show 2 * (q + 1) + 1 = 2 * q + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_eq_single 0 (fun l hl hl0 => by
        rw [hR0 l (by omega) (by have := mem_range.1 hl; omega), mul_zero])
      (fun h => absurd (mem_range.2 (by omega)) h)]
  have hv : adjv g q (e1 E) 0 = pfS g q (fun i => E (i + 2)) := by
    unfold adjv
    rw [pow_zero, one_mul]
    refine pfS_congr g q _ _ (fun i _ => ?_)
    unfold e1 sk
    simp
  rw [pfS_cons, pfS_cons, pfS_cons, ← hLHS, hD, hRHS, hv]
  ring

/-- `Pf G[I+{a,c}]`, `Pf G[I+{b,d}]`, `Pf G[I+{a,d}]` (`I = {s+2..s+2k-1}`, `a = s`, `b = s+1`, `c = s+2k`,
`d = s+2k+1`), as Pfaffians of increasing index sequences. -/
noncomputable def Pac (n s k : ℕ) : ℚ := pfS (G n) k (fun i => s + sk 1 i)
noncomputable def Pbd (n s k : ℕ) : ℚ := pfS (G n) k (fun i => s + 1 + sk (2 * k - 1) i)
noncomputable def Pad (n s k : ℕ) : ℚ :=
  pfS (G n) k (fun i => if i = 0 then s else if i = 2 * k - 1 then s + 2 * k + 1 else s + 1 + i)

lemma neg_one_pow_odd (q : ℕ) : (-1 : ℚ) ^ (2 * q + 1) = -1 := by rw [pow_succ, pow_mul]; simp
lemma neg_one_pow_even (q : ℕ) : (-1 : ℚ) ^ (2 * q + 2) = 1 := by
  rw [show 2 * q + 2 = 2 * (q + 1) by ring, pow_mul]; simp

/-- **Knuth's identity on the windows of `G`** (`k = q+1 ≥ 1`):
`W(s+2,k-1) W(s,k+1) = W(s,k) W(s+2,k) - Pf[I+ac] Pf[I+bd] + Pf[I+ad] W(s+1,k)`. -/
theorem knuth_G (n s q : ℕ) :
    W n (s + 2) q * W n s (q + 2)
      = W n s (q + 1) * W n (s + 2) (q + 1) - Pac n s (q + 1) * Pbd n s (q + 1)
        + Pad n s (q + 1) * W n (s + 1) (q + 1) := by
  have hg : ∀ a b, G n a b = -G n b a := fun a b => G_anti n b a
  have h := knuth_core (G n) hg q (fun i => s + i)
  have A0 : adjv (G n) (q + 1) (e3 fun i => s + i) 0 = W n (s + 2) (q + 1) := by
    unfold adjv W
    rw [pow_zero, one_mul]
    refine pfS_congr _ _ _ _ (fun i _ => ?_)
    unfold e3 sk; beta_reduce; split_ifs <;> omega
  have A1 : adjv (G n) (q + 1) (e3 fun i => s + i) (2 * q + 1) = -Pbd n s (q + 1) := by
    unfold adjv Pbd
    rw [neg_one_pow_odd, neg_one_mul]
    congr 1
    refine pfS_congr _ _ _ _ (fun i _ => ?_)
    unfold e3 sk; beta_reduce; split_ifs <;> omega
  have A2 : adjv (G n) (q + 1) (e3 fun i => s + i) (2 * q + 2) = W n (s + 1) (q + 1) := by
    unfold adjv W
    rw [neg_one_pow_even, one_mul]
    refine pfS_congr _ _ _ _ (fun i hi => ?_)
    unfold e3 sk; beta_reduce; split_ifs <;> omega
  have B0 : pfS (G n) (q + 1) (cons (e3 (fun i => s + i) 0) (e1 fun i => s + i)) = -W n s (q + 1) := by
    have := pfS_tw (G n) hg (q + 1) (fun i => s + i) 0 (by omega)
    unfold W
    rw [← this]
    refine pfS_congr _ _ _ _ (fun i _ => ?_)
    unfold cons e1 e3 tw; beta_reduce; split_ifs <;> omega
  have B1 : pfS (G n) (q + 1) (cons (e3 (fun i => s + i) (2 * q + 1)) (e1 fun i => s + i))
      = -Pac n s (q + 1) := by
    have := pfS_rot (G n) hg (q + 1) (cons (e3 (fun i => s + i) (2 * q + 1)) (e1 fun i => s + i)) (2 * q + 1)
      (by omega)
    rw [neg_one_pow_odd, neg_one_mul] at this
    rw [← neg_eq_iff_eq_neg, ← this]
    unfold Pac
    refine pfS_congr _ _ _ _ (fun i hi => ?_)
    beta_reduce
    rcases Nat.lt_or_ge i (2 * q + 1) with hlt | hge
    · have hr : rt (2 * q + 1) i = i + 1 := by unfold rt; rw [if_pos hlt]
      rw [hr]
      unfold cons e1 e3 sk; beta_reduce; split_ifs <;> first | contradiction | omega
    · obtain rfl : i = 2 * q + 1 := by omega
      have hr : rt (2 * q + 1) (2 * q + 1) = 0 := by unfold rt; simp
      rw [hr]
      unfold cons e1 e3 sk; beta_reduce; split_ifs <;> first | contradiction | omega
  have B2 : pfS (G n) (q + 1) (cons (e3 (fun i => s + i) (2 * q + 2)) (e1 fun i => s + i))
      = -Pad n s (q + 1) := by
    have := pfS_rot (G n) hg (q + 1) (cons (e3 (fun i => s + i) (2 * q + 2)) (e1 fun i => s + i)) (2 * q + 1)
      (by omega)
    rw [neg_one_pow_odd, neg_one_mul] at this
    rw [← neg_eq_iff_eq_neg, ← this]
    unfold Pad
    refine pfS_congr _ _ _ _ (fun i hi => ?_)
    beta_reduce
    rcases Nat.lt_or_ge i (2 * q + 1) with hlt | hge
    · have hr : rt (2 * q + 1) i = i + 1 := by unfold rt; rw [if_pos hlt]
      rw [hr]
      unfold cons e1 e3 ; beta_reduce; split_ifs <;> first | contradiction | omega
    · obtain rfl : i = 2 * q + 1 := by omega
      have hr : rt (2 * q + 1) (2 * q + 1) = 0 := by unfold rt; simp
      rw [hr]
      unfold cons e1 e3 ; beta_reduce; split_ifs <;> first | contradiction | omega
  rw [A0, A1, A2, B0, B1, B2] at h
  have hW2 : pfS (G n) (q + 2) (fun i => s + i) = W n s (q + 2) := rfl
  have hW0 : pfS (G n) q (fun i => s + (i + 2)) = W n (s + 2) q := by
    unfold W; exact pfS_congr _ _ _ _ (fun i _ => by omega)
  rw [hW2, hW0] at h
  linear_combination h

end Bali.GPOpen

#print axioms Bali.GPOpen.knuth_core
#print axioms Bali.GPOpen.knuth_G

/-! ## (A) the values (ii), (iii) from the kernel vector -/

namespace Bali.GPOpen
open Bali.GP

/-- kernel form of (ii): `W(s,k) c_1 = - c_{2k} Pf[I+ac]`. -/
theorem ker_ii (n s q : ℕ) (c : ℕ → ℚ)
    (hc : ∀ t ≤ 2 * (q + 1), ∑ l ∈ range (2 * (q + 1) + 1), c l * G n (s + l) (s + t) = 0)
    (hW : W n s (q + 1) ≠ 0) :
    W n s (q + 1) * c 1 = -(c (2 * (q + 1)) * Pac n s (q + 1)) := by
  have key := odd_ker_span (G n) (fun a b => G_anti n b a) (q + 1) (fun i => s + i) (2 * (q + 1)) le_rfl
    (by rw [adjv_last]; exact hW) c (by
      intro t ht
      rw [← neg_eq_zero, ← hc t (by omega), ← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      rw [G_anti n (s + l) (s + t)]; ring) 1 (by omega)
  rw [adjv_last] at key
  have h1 : adjv (G n) (q + 1) (fun i => s + i) 1 = -Pac n s (q + 1) := by
    unfold adjv Pac
    rw [pow_one, neg_one_mul]
  rw [h1] at key
  linarith

/-- kernel form of (iii), window `s+1`: `W(s+1,k) c'_{2k-1} = - c'_{2k} Pf[I+bd]`. -/
theorem ker_iii (n s q : ℕ) (c : ℕ → ℚ)
    (hc : ∀ t ≤ 2 * (q + 1), ∑ l ∈ range (2 * (q + 1) + 1), c l * G n (s + 1 + l) (s + 1 + t) = 0)
    (hW : W n (s + 1) (q + 1) ≠ 0) :
    W n (s + 1) (q + 1) * c (2 * q + 1) = -(c (2 * (q + 1)) * Pbd n s (q + 1)) := by
  have key := odd_ker_span (G n) (fun a b => G_anti n b a) (q + 1) (fun i => s + 1 + i) (2 * (q + 1)) le_rfl
    (by rw [adjv_last]; exact hW) c (by
      intro t ht
      rw [← neg_eq_zero, ← hc t (by omega), ← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      rw [G_anti n (s + 1 + l) (s + 1 + t)]; ring) (2 * q + 1) (by omega)
  rw [adjv_last] at key
  have h1 : adjv (G n) (q + 1) (fun i => s + 1 + i) (2 * q + 1) = -Pbd n s (q + 1) := by
    unfold adjv Pbd
    rw [neg_one_pow_odd, neg_one_mul, show 2 * (q + 1) - 1 = 2 * q + 1 by omega]
  rw [h1] at key
  linarith

lemma gK_one (b : ℚ) (s k : ℕ) : gK b s k 1 = -(k : ℚ) * b / ((s : ℚ) + 1 / 2) := by
  unfold gK
  rw [show (1 : ℕ) = 0 + 1 from rfl, v2_ratio, v2_zero]
  push_cast
  ring

lemma dK_one (b b' : ℚ) (s k : ℕ) : dK b b' s k 1 = gK b' s k 1 + gK b s k 1 := by
  unfold dK
  rw [show 1 + 1 = 2 from rfl, sum_range_succ, sum_range_one]
  simp only [Nat.sub_zero, Nat.sub_self]
  rw [show gK b s k 0 = 1 from v2_zero _ _ _, show gK b' s k 0 = 1 from v2_zero _ _ _]
  ring

lemma gK_prev (b : ℚ) (s q : ℕ) :
    gK b s (q + 1) (q + 1) * (((s : ℚ) + 1 / 2 + q) * ((q : ℚ) + 1)) = -(gK b s (q + 1) q * (b + q)) := by
  unfold gK
  rw [v2_ratio]
  have h1 : (s : ℚ) + 1 / 2 + q ≠ 0 := by positivity
  have h2 : (q : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma dK_top1 (b b' : ℚ) (s q : ℕ) :
    dK b b' s (q + 1) (2 * q + 1)
      = gK b s (q + 1) q * gK b' s (q + 1) (q + 1) + gK b s (q + 1) (q + 1) * gK b' s (q + 1) q := by
  unfold dK
  rw [Finset.sum_eq_add q (q + 1) (by omega) ?_ ?_ ?_]
  · rw [show 2 * q + 1 - q = q + 1 by omega, show 2 * q + 1 - (q + 1) = q by omega]
  · intro i _ hi
    rcases Nat.lt_or_ge i q with h | h
    · rw [show gK b' s (q + 1) (2 * q + 1 - i) = 0 from v2_vanish _ _ _ _ (by omega), mul_zero]
    · rw [show gK b s (q + 1) i = 0 from v2_vanish _ _ _ _ (by omega), zero_mul]
  · intro h; exact absurd (mem_range.2 (by omega)) h
  · intro h; exact absurd (mem_range.2 (by omega)) h

lemma sq_neg_one_pow (k : ℕ) : ((-1 : ℚ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp

/-- **(ii)**: `Pf[I+ac] = W(s,k) · k(b+b')/σ · C(n,2s+4k)/C(n,2s+2) · (σ)_k²/((b)_k (b')_k)`. -/
theorem ii_core (n s q : ℕ) (b b' : ℚ)
    (hK : ∀ t ≤ 2 * (q + 1), ∑ l ∈ range (2 * (q + 1) + 1), cK n b b' s (q + 1) l * G n (s + l) (s + t) = 0)
    (hn : 2 * s + 4 * (q + 1) ≤ n) (hb : b + (q + 1 : ℕ) - 1 < 0) (hb' : b' + (q + 1 : ℕ) - 1 < 0)
    (hW : W n s (q + 1) ≠ 0) :
    Pac n s (q + 1) = W n s (q + 1) * (((q + 1 : ℕ) : ℚ) * (b + b') / ((s : ℚ) + 1 / 2)
      * ((n.choose (2 * s + 4 * (q + 1)) : ℚ) / (n.choose (2 * s + 2) : ℚ))
      * (poch ((s : ℚ) + 1 / 2) (q + 1) ^ 2 / (poch b (q + 1) * poch b' (q + 1)))) := by
  have key := ker_ii n s q _ hK hW
  have hC2 : (n.choose (2 * s + 2) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC4 : (n.choose (2 * s + 4 * (q + 1)) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hn).ne'
  have h3 : poch ((s : ℚ) + 1 / 2) (q + 1) ≠ 0 := poch_pos_of _ (by positivity) _
  have hbb := (poch_pair_pos b b' (q + 1) hb hb').ne'
  have hb0 : poch b (q + 1) ≠ 0 := left_ne_zero_of_mul hbb
  have hb0' : poch b' (q + 1) ≠ 0 := right_ne_zero_of_mul hbb
  have hsg : (s : ℚ) + 1 / 2 ≠ 0 := by positivity
  unfold cK at key
  rw [dK_one, gK_one, gK_one, dK_top, gK_top, gK_top, show 2 * s + 2 * 1 = 2 * s + 2 by ring,
    show 2 * s + 2 * (2 * (q + 1)) = 2 * s + 4 * (q + 1) by ring,
    show (-1 : ℚ) ^ (q + 1) * poch b (q + 1) / poch ((s : ℚ) + 1 / 2) (q + 1)
        * ((-1) ^ (q + 1) * poch b' (q + 1) / poch ((s : ℚ) + 1 / 2) (q + 1))
      = ((-1 : ℚ) ^ (q + 1)) ^ 2 * (poch b (q + 1) * poch b' (q + 1)) / poch ((s : ℚ) + 1 / 2) (q + 1) ^ 2 by ring,
    sq_neg_one_pow, one_mul] at key
  generalize poch ((s : ℚ) + 1 / 2) (q + 1) = P at *
  generalize poch b (q + 1) = B1 at *
  generalize poch b' (q + 1) = B2 at *
  generalize (n.choose (2 * s + 2) : ℚ) = C2 at *
  generalize (n.choose (2 * s + 4 * (q + 1)) : ℚ) = C4 at *
  generalize W n s (q + 1) = w0 at *
  generalize Pac n s (q + 1) = pac at *
  have hX : B1 * B2 / P ^ 2 / C4 ≠ 0 := div_ne_zero (div_ne_zero hbb (pow_ne_zero 2 h3)) hC4
  refine mul_left_cancel₀ hX ?_
  have k2 : B1 * B2 / P ^ 2 / C4 * pac
      = -(w0 * ((-((q + 1 : ℕ) : ℚ) * b' / ((s : ℚ) + 1 / 2) + -((q + 1 : ℕ) : ℚ) * b / ((s : ℚ) + 1 / 2)) / C2)) := by
    linarith [key]
  rw [k2]
  field_simp
  ring

/-- **(iii)** (window `s+1`, parameters `b+1`, `b'+1`):
`Pf[I+bd] = W(s+1,k) · k(σ+k)(1/(b+k) + 1/(b'+k)) · C(n,2s+4k+2)/C(n,2s+4k)`. -/
theorem iii_core (n s q : ℕ) (b b' : ℚ)
    (hK : ∀ t ≤ 2 * (q + 1), ∑ l ∈ range (2 * (q + 1) + 1),
      cK n (b + 1) (b' + 1) (s + 1) (q + 1) l * G n (s + 1 + l) (s + 1 + t) = 0)
    (hn : 2 * s + 4 * (q + 1) + 2 ≤ n) (hb : b + 1 + (q + 1 : ℕ) - 1 < 0) (hb' : b' + 1 + (q + 1 : ℕ) - 1 < 0)
    (hW : W n (s + 1) (q + 1) ≠ 0) :
    Pbd n s (q + 1) = W n (s + 1) (q + 1) * (((q + 1 : ℕ) : ℚ) * ((s : ℚ) + 1 / 2 + (q + 1 : ℕ))
      * (1 / (b + (q + 1 : ℕ)) + 1 / (b' + (q + 1 : ℕ)))
      * ((n.choose (2 * s + 4 * (q + 1) + 2) : ℚ) / (n.choose (2 * s + 4 * (q + 1)) : ℚ))) := by
  have key := ker_iii n s q _ hK hW
  have hC4 : (n.choose (2 * s + 4 * (q + 1)) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC6 : (n.choose (2 * s + 4 * (q + 1) + 2) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hn).ne'
  have h3 : poch (((s + 1 : ℕ) : ℚ) + 1 / 2) (q + 1) ≠ 0 := poch_pos_of _ (by positivity) _
  have hbb := (poch_pair_pos (b + 1) (b' + 1) (q + 1) hb hb').ne'
  have hb0 : poch (b + 1) (q + 1) ≠ 0 := left_ne_zero_of_mul hbb
  have hb0' : poch (b' + 1) (q + 1) ≠ 0 := right_ne_zero_of_mul hbb
  push_cast at hb hb'
  have hbk : b + ((q : ℚ) + 1) ≠ 0 := by linarith
  have hbk' : b' + ((q : ℚ) + 1) ≠ 0 := by linarith
  have g1 := gK_prev (b + 1) (s + 1) q
  have g2 := gK_prev (b' + 1) (s + 1) q
  have t1 := gK_top (b + 1) (s + 1) (q + 1)
  have t2 := gK_top (b' + 1) (s + 1) (q + 1)
  have hs1 : ((-1 : ℚ) ^ (q + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hg1 : gK (b + 1) (s + 1) (q + 1) (q + 1) ≠ 0 := by
    rw [t1]; exact div_ne_zero (mul_ne_zero hs1 hb0) h3
  have hg2 : gK (b' + 1) (s + 1) (q + 1) (q + 1) ≠ 0 := by
    rw [t2]; exact div_ne_zero (mul_ne_zero hs1 hb0') h3
  unfold cK at key
  rw [dK_top1, dK_top, show 2 * (s + 1) + 2 * (2 * q + 1) = 2 * s + 4 * (q + 1) by ring,
    show 2 * (s + 1) + 2 * (2 * (q + 1)) = 2 * s + 4 * (q + 1) + 2 by ring] at key
  push_cast at g1 g2 key ⊢
  generalize gK (b + 1) (s + 1) (q + 1) (q + 1) = G1 at *
  generalize gK (b' + 1) (s + 1) (q + 1) (q + 1) = G2 at *
  generalize gK (b + 1) (s + 1) (q + 1) q = H1 at *
  generalize gK (b' + 1) (s + 1) (q + 1) q = H2 at *
  generalize (n.choose (2 * s + 4 * (q + 1)) : ℚ) = C4 at *
  generalize (n.choose (2 * s + 4 * (q + 1) + 2) : ℚ) = C6 at *
  generalize W n (s + 1) (q + 1) = w1 at *
  generalize Pbd n s (q + 1) = pbd at *
  have hH1 : H1 = -(G1 * (((s : ℚ) + 1 + 1 / 2 + q) * ((q : ℚ) + 1))) / (b + 1 + q) := by
    rw [eq_div_iff (by linarith [hb] : b + 1 + (q : ℚ) ≠ 0)]; linarith
  have hH2 : H2 = -(G2 * (((s : ℚ) + 1 + 1 / 2 + q) * ((q : ℚ) + 1))) / (b' + 1 + q) := by
    rw [eq_div_iff (by linarith [hb'] : b' + 1 + (q : ℚ) ≠ 0)]; linarith
  have hX : G1 * G2 / C6 ≠ 0 := div_ne_zero (mul_ne_zero hg1 hg2) hC6
  refine mul_left_cancel₀ hX ?_
  have k2 : G1 * G2 / C6 * pbd = -(w1 * ((H1 * G2 + G1 * H2) / C4)) := by linarith [key]
  rw [k2, hH1, hH2]
  have hbq : b + 1 + (q : ℚ) ≠ 0 := by linarith
  have hbq' : b' + 1 + (q : ℚ) ≠ 0 := by linarith
  field_simp
  ring

end Bali.GPOpen

#print axioms Bali.GPOpen.ii_core
#print axioms Bali.GPOpen.iii_core

/-! ## (A) the closed form (iv) for `Pf G[I+{a,d}]` -/

namespace Bali.GPOpen
open Bali.GP

lemma poch_shift' (x : ℚ) (hx : x ≠ 0) (k : ℕ) : poch (x + 1) k = poch x k * (x + k) / x := by
  rw [eq_div_iff hx, mul_comm, ← poch_succ_left, poch_succ]

/-- `W(s+2,k) W(s,k) / W(s+1,k)^2`, division-free. -/
theorem R1 (n s k : ℕ) (b b' : ℚ)
    (h0 : W n (s + 1) k = ratioI n s k b b' * W n s k)
    (h1 : W n (s + 2) k = ratioI n (s + 1) k (b + 1) (b' + 1) * W n (s + 1) k)
    (hn : 2 * s + 4 * k + 2 ≤ n) (hb : b + k < 0) (hb' : b' + k < 0) :
    W n (s + 2) k * W n s k * ((n.choose (2 * s + 2) : ℚ) * (n.choose (2 * s + 4 * k) : ℚ)
        * ((s : ℚ) + 1 / 2) ^ 2 * (b + k) * (b' + k))
      = W n (s + 1) k ^ 2 * ((n.choose (2 * s + 4 * k + 2) : ℚ) * (n.choose (2 * s) : ℚ)
        * ((s : ℚ) + 1 / 2 + k) ^ 2 * b * b') := by
  have hk0 : (0 : ℚ) ≤ k := by positivity
  have hC0 : (n.choose (2 * s) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC2 : (n.choose (2 * s + 2) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC4 : (n.choose (2 * s + 4 * k) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC6 : (n.choose (2 * s + 4 * k + 2) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hn).ne'
  have hsg : (s : ℚ) + 1 / 2 ≠ 0 := by positivity
  have hsk : (s : ℚ) + 1 / 2 + k ≠ 0 := by positivity
  have hb0 : b ≠ 0 := by linarith
  have hb0' : b' ≠ 0 := by linarith
  have hbk : b + k ≠ 0 := hb.ne
  have hbk' : b' + k ≠ 0 := hb'.ne
  have h3 : poch ((s : ℚ) + 1 / 2) k ≠ 0 := poch_pos_of _ (by positivity) _
  have hbb := (poch_pair_pos b b' k (by linarith) (by linarith)).ne'
  have hp1 : poch b k ≠ 0 := left_ne_zero_of_mul hbb
  have hp2 : poch b' k ≠ 0 := right_ne_zero_of_mul hbb
  rw [h1, h0]
  unfold ratioI
  rw [show 2 * (s + 1) + 4 * k = 2 * s + 4 * k + 2 by ring, show 2 * (s + 1) = 2 * s + 2 by ring,
    show (((s + 1 : ℕ) : ℚ) + 1 / 2) = ((s : ℚ) + 1 / 2) + 1 by push_cast; ring,
    poch_shift' _ hsg, poch_shift' _ hb0, poch_shift' _ hb0']
  generalize poch ((s : ℚ) + 1 / 2) k = P at *
  generalize poch b k = B1 at *
  generalize poch b' k = B2 at *
  field_simp

/-- `Pf[I+ac] Pf[I+bd] / W(s+1,k)^2`, division-free. -/
theorem R2 (n s q : ℕ) (b b' : ℚ)
    (h0 : W n (s + 1) (q + 1) = ratioI n s (q + 1) b b' * W n s (q + 1))
    (hii : Pac n s (q + 1) = W n s (q + 1) * (((q + 1 : ℕ) : ℚ) * (b + b') / ((s : ℚ) + 1 / 2)
      * ((n.choose (2 * s + 4 * (q + 1)) : ℚ) / (n.choose (2 * s + 2) : ℚ))
      * (poch ((s : ℚ) + 1 / 2) (q + 1) ^ 2 / (poch b (q + 1) * poch b' (q + 1)))))
    (hiii : Pbd n s (q + 1) = W n (s + 1) (q + 1) * (((q + 1 : ℕ) : ℚ) * ((s : ℚ) + 1 / 2 + (q + 1 : ℕ))
      * (1 / (b + (q + 1 : ℕ)) + 1 / (b' + (q + 1 : ℕ)))
      * ((n.choose (2 * s + 4 * (q + 1) + 2) : ℚ) / (n.choose (2 * s + 4 * (q + 1)) : ℚ))))
    (hn : 2 * s + 4 * (q + 1) + 2 ≤ n) (hb : b + (q + 1 : ℕ) < 0) (hb' : b' + (q + 1 : ℕ) < 0) :
    Pac n s (q + 1) * Pbd n s (q + 1) * ((n.choose (2 * s + 2) : ℚ) * (n.choose (2 * s + 4 * (q + 1)) : ℚ)
        * ((s : ℚ) + 1 / 2) * (b + (q + 1 : ℕ)) * (b' + (q + 1 : ℕ)))
      = W n (s + 1) (q + 1) ^ 2 * ((n.choose (2 * s + 4 * (q + 1) + 2) : ℚ) * (n.choose (2 * s) : ℚ)
        * ((q + 1 : ℕ) : ℚ) ^ 2 * (b + b') * ((s : ℚ) + 1 / 2 + (q + 1 : ℕ)) * (b + b' + 2 * (q + 1 : ℕ))) := by
  have hk0 : (0 : ℚ) ≤ ((q + 1 : ℕ) : ℚ) := by positivity
  have hC0 : (n.choose (2 * s) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC2 : (n.choose (2 * s + 2) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC4 : (n.choose (2 * s + 4 * (q + 1)) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC6 : (n.choose (2 * s + 4 * (q + 1) + 2) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hn).ne'
  have hsg : (s : ℚ) + 1 / 2 ≠ 0 := by positivity
  have hbk : b + ((q + 1 : ℕ) : ℚ) ≠ 0 := hb.ne
  have hbk' : b' + ((q + 1 : ℕ) : ℚ) ≠ 0 := hb'.ne
  have h3 : poch ((s : ℚ) + 1 / 2) (q + 1) ≠ 0 := poch_pos_of _ (by positivity) _
  have hbb := (poch_pair_pos b b' (q + 1) (by linarith) (by linarith)).ne'
  have hp1 : poch b (q + 1) ≠ 0 := left_ne_zero_of_mul hbb
  have hp2 : poch b' (q + 1) ≠ 0 := right_ne_zero_of_mul hbb
  rw [hii, hiii, h0]
  unfold ratioI
  generalize poch ((s : ℚ) + 1 / 2) (q + 1) = P at *
  generalize poch b (q + 1) = B1 at *
  generalize poch b' (q + 1) = B2 at *
  generalize ((q + 1 : ℕ) : ℚ) = κ at *
  field_simp
  ring

/-- `W(s+2,k-1) W(s,k+1) / W(s+1,k)^2` from `eq:z`, odd `n`, `m = s+2q+3+e`, `k = q+1`. -/
theorem R3_odd (s q e : ℕ) :
    W (2 * (s + 2 * q + 3 + e) + 1) (s + 2) q * W (2 * (s + 2 * q + 3 + e) + 1) s (q + 2)
        * (((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s + 2) : ℚ)
          * ((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s + 4 * (q + 1)) : ℚ)
          * ((s : ℚ) + 1 / 2) ^ 2 * ((e : ℚ) + 3 / 2) ^ 2)
      = W (2 * (s + 2 * q + 3 + e) + 1) (s + 1) (q + 1) ^ 2
        * (((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s + 4 * (q + 1) + 2) : ℚ)
          * ((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s) : ℚ)
          * ((q : ℚ) + 1) ^ 2 * ((s : ℚ) + q + e + 3) ^ 2) := by
  have hz1 := ratio_z_odd (s + 2 * q + 3 + e) s (q + 1) (by omega)
  have hz0 := ratio_z_odd (s + 2 * q + 3 + e) (s + 1) q (by omega)
  have hw1 := (W_pos_odd_all (s + 2 * q + 3 + e) (q + 1) (s + 1) (by omega)).ne'
  have hu := (W_pos_odd_all (s + 2 * q + 3 + e) q (s + 2) (by omega)).ne'
  rw [show s + 1 + 1 = s + 2 from rfl] at hz0
  rw [show q + 1 + 1 = q + 2 from rfl] at hz1
  rw [div_eq_iff hw1] at hz1
  rw [div_eq_iff hu] at hz0
  rw [show s + 2 * q + 3 + e - s - 2 * (q + 1) = e + 1 by omega,
    show s + 2 * q + 3 + e - (q + 1) = s + q + 2 + e by omega, Nat.factorial_succ q] at hz1
  rw [show s + 2 * q + 3 + e - (s + 1) - 2 * q = e + 1 + 1 by omega,
    show s + 2 * q + 3 + e - q = s + q + 2 + e + 1 by omega, show 2 * (s + 1) = 2 * s + 2 by ring,
    show 2 * s + 2 + 4 * q + 2 = 2 * s + 4 * (q + 1) by ring, poch_succ (1 / 2 : ℚ) (e + 1),
    poch_succ (1 / 2 : ℚ) s, Nat.factorial_succ (s + q + 2 + e)] at hz0
  push_cast at hz1 hz0
  have h' := hw1
  rw [hz0] at h'
  have hu' := eq_div_of_mul_eq (left_ne_zero_of_mul h') ((mul_comm _ _).trans hz0.symm)
  rw [hz1, hu']
  have hC0 : (((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC2 : (((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s + 2) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC4 : (((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s + 4 * (q + 1)) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC6 : (((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s + 4 * (q + 1) + 2) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hQ1 := (poch_pos' (1 / 2 : ℚ) (by norm_num) s).ne'
  have hA := (poch_pos' (1 / 2 : ℚ) (by norm_num) (e + 1)).ne'
  have hF : (q.factorial : ℚ) ≠ 0 := by positivity
  have hFm : ((s + q + 2 + e).factorial : ℚ) ≠ 0 := by positivity
  have hT : (2 : ℚ) ^ (2 * (2 * (s + 2 * q + 3 + e) + 1)) ≠ 0 := by positivity
  generalize (((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s) : ℕ) : ℚ) = C0 at *
  generalize (((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s + 2) : ℕ) : ℚ) = C2 at *
  generalize (((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s + 4 * (q + 1)) : ℕ) : ℚ) = C4 at *
  generalize (((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s + 4 * (q + 1) + 2) : ℕ) : ℚ) = C6 at *
  generalize poch (1 / 2 : ℚ) s = Q1 at *
  generalize poch (1 / 2 : ℚ) (e + 1) = A at *
  generalize (q.factorial : ℚ) = F at *
  generalize ((s + q + 2 + e).factorial : ℚ) = Fm at *
  generalize (2 : ℚ) ^ (2 * (2 * (s + 2 * q + 3 + e) + 1)) = T at *
  generalize W (2 * (s + 2 * q + 3 + e) + 1) (s + 1) (q + 1) = w1 at *
  push_cast
  have hs0 : (0 : ℚ) ≤ s := by positivity
  have he0 : (0 : ℚ) ≤ e := by positivity
  have hq0 : (0 : ℚ) ≤ q := by positivity
  have d1 : (1 / 2 : ℚ) + s ≠ 0 := by positivity
  have d2 : (1 / 2 : ℚ) + ((e : ℚ) + 1) ≠ 0 := by positivity
  have d3 : (s : ℚ) + q + 2 + e + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- the same for even `n`. -/
theorem R3_even (s q e : ℕ) :
    W (2 * (s + 2 * q + 3 + e)) (s + 2) q * W (2 * (s + 2 * q + 3 + e)) s (q + 2)
        * (((2 * (s + 2 * q + 3 + e)).choose (2 * s + 2) : ℚ)
          * ((2 * (s + 2 * q + 3 + e)).choose (2 * s + 4 * (q + 1)) : ℚ)
          * ((s : ℚ) + 1 / 2) ^ 2 * (((e : ℚ) + 3 / 2) * ((e : ℚ) + 1 / 2)))
      = W (2 * (s + 2 * q + 3 + e)) (s + 1) (q + 1) ^ 2
        * (((2 * (s + 2 * q + 3 + e)).choose (2 * s + 4 * (q + 1) + 2) : ℚ)
          * ((2 * (s + 2 * q + 3 + e)).choose (2 * s) : ℚ)
          * ((q : ℚ) + 1) ^ 2 * (((s : ℚ) + q + e + 3) * ((s : ℚ) + q + e + 2))) := by
  have hz1 := ratio_z_even (s + 2 * q + 3 + e) s (q + 1) (by omega)
  have hz0 := ratio_z_even (s + 2 * q + 3 + e) (s + 1) q (by omega)
  have hw1 := (W_pos_even_all (s + 2 * q + 3 + e) (q + 1) (s + 1) (by omega)).ne'
  have hu := (W_pos_even_all (s + 2 * q + 3 + e) q (s + 2) (by omega)).ne'
  rw [show s + 1 + 1 = s + 2 from rfl] at hz0
  rw [show q + 1 + 1 = q + 2 from rfl] at hz1
  rw [div_eq_iff hw1] at hz1
  rw [div_eq_iff hu] at hz0
  rw [show s + 2 * q + 3 + e - s - 2 * (q + 1) = e + 1 by omega, show e + 1 - 1 = e from rfl,
    show s + 2 * q + 3 + e - (q + 1) = s + q + 1 + e + 1 by omega,
    show s + q + 1 + e + 1 - 1 = s + q + 1 + e from rfl, Nat.factorial_succ q,
    Nat.factorial_succ (s + q + 1 + e), poch_succ (1 / 2 : ℚ) e] at hz1
  rw [show s + 2 * q + 3 + e - (s + 1) - 2 * q = e + 1 + 1 by omega, show e + 1 + 1 - 1 = e + 1 from rfl,
    show s + 2 * q + 3 + e - q = s + q + 1 + e + 1 + 1 by omega,
    show s + q + 1 + e + 1 + 1 - 1 = s + q + 1 + e + 1 from rfl, show 2 * (s + 1) = 2 * s + 2 by ring,
    show 2 * s + 2 + 4 * q + 2 = 2 * s + 4 * (q + 1) by ring, poch_succ (1 / 2 : ℚ) (e + 1),
    poch_succ (1 / 2 : ℚ) e, poch_succ (1 / 2 : ℚ) s, Nat.factorial_succ (s + q + 1 + e + 1),
    Nat.factorial_succ (s + q + 1 + e)] at hz0
  push_cast at hz1 hz0
  have h' := hw1
  rw [hz0] at h'
  have hu' := eq_div_of_mul_eq (left_ne_zero_of_mul h') ((mul_comm _ _).trans hz0.symm)
  rw [hz1, hu']
  have hC0 : (((2 * (s + 2 * q + 3 + e)).choose (2 * s) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC2 : (((2 * (s + 2 * q + 3 + e)).choose (2 * s + 2) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC4 : (((2 * (s + 2 * q + 3 + e)).choose (2 * s + 4 * (q + 1)) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC6 : (((2 * (s + 2 * q + 3 + e)).choose (2 * s + 4 * (q + 1) + 2) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hQ1 := (poch_pos' (1 / 2 : ℚ) (by norm_num) s).ne'
  have hA := (poch_pos' (1 / 2 : ℚ) (by norm_num) e).ne'
  have hF : (q.factorial : ℚ) ≠ 0 := by positivity
  have hFm : ((s + q + 1 + e).factorial : ℚ) ≠ 0 := by positivity
  have hT : (2 : ℚ) ^ (2 * (2 * (s + 2 * q + 3 + e))) ≠ 0 := by positivity
  generalize (((2 * (s + 2 * q + 3 + e)).choose (2 * s) : ℕ) : ℚ) = C0 at *
  generalize (((2 * (s + 2 * q + 3 + e)).choose (2 * s + 2) : ℕ) : ℚ) = C2 at *
  generalize (((2 * (s + 2 * q + 3 + e)).choose (2 * s + 4 * (q + 1)) : ℕ) : ℚ) = C4 at *
  generalize (((2 * (s + 2 * q + 3 + e)).choose (2 * s + 4 * (q + 1) + 2) : ℕ) : ℚ) = C6 at *
  generalize poch (1 / 2 : ℚ) s = Q1 at *
  generalize poch (1 / 2 : ℚ) e = A at *
  generalize (q.factorial : ℚ) = F at *
  generalize ((s + q + 1 + e).factorial : ℚ) = Fm at *
  generalize (2 : ℚ) ^ (2 * (2 * (s + 2 * q + 3 + e))) = T at *
  generalize W (2 * (s + 2 * q + 3 + e)) (s + 1) (q + 1) = w1 at *
  push_cast
  have hs0 : (0 : ℚ) ≤ s := by positivity
  have he0 : (0 : ℚ) ≤ e := by positivity
  have hq0 : (0 : ℚ) ≤ q := by positivity
  have d1 : (1 / 2 : ℚ) + s ≠ 0 := by positivity
  have d2 : (1 / 2 : ℚ) + ((e : ℚ) + 1) ≠ 0 := by positivity
  have d2' : (1 / 2 : ℚ) + (e : ℚ) ≠ 0 := by positivity
  have d3 : (s : ℚ) + q + 1 + e + 1 + 1 ≠ 0 := by positivity
  have d4 : (s : ℚ) + q + 1 + e + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- the polynomial `M` of (iv). -/
def Mpoly (σ κ b b' : ℚ) : ℚ :=
  σ * (κ ^ 2 - b * b') - κ ^ 2 * (b + b') - 2 * κ * b * b' + κ ^ 2 * (b + b') * (b + b' + 2 * κ) * (σ + κ)

/-- **(iv), odd `n = 2m+1`** (`k = q+1 ≥ 1`, `s+2k+1 ≤ m`, `b = b₁ = b₂`), division-free:
`Pf G[I+{a,d}] · C(n,2s+2) C(n,2s+4k) σ (b+k)² = W(s+1,k) · C(n,2s+4k+2) C(n,2s) · M`. -/
theorem iv_odd (m s q : ℕ) (h : s + 2 * (q + 1) + 1 ≤ m) :
    Pad (2 * m + 1) s (q + 1) * (((2 * m + 1).choose (2 * s + 2) : ℚ) * ((2 * m + 1).choose (2 * s + 4 * (q + 1)) : ℚ)
        * ((s : ℚ) + 1 / 2) * (b1 m s (q + 1) + (q + 1 : ℕ)) * (b1 m s (q + 1) + (q + 1 : ℕ)))
      = W (2 * m + 1) (s + 1) (q + 1) * (((2 * m + 1).choose (2 * s + 4 * (q + 1) + 2) : ℚ)
        * ((2 * m + 1).choose (2 * s) : ℚ)
        * Mpoly ((s : ℚ) + 1 / 2) ((q + 1 : ℕ) : ℚ) (b1 m s (q + 1)) (b1 m s (q + 1))) := by
  obtain ⟨e, rfl⟩ : ∃ e, m = s + 2 * q + 3 + e := ⟨m - (s + 2 * q + 3), by omega⟩
  have hβ : b1 (s + 2 * q + 3 + e) s (q + 1) = -((q : ℚ) + e + 5 / 2) := by unfold b1; push_cast; ring
  have hβ1 : b1 (s + 2 * q + 3 + e) (s + 1) (q + 1) = b1 (s + 2 * q + 3 + e) s (q + 1) + 1 := by
    unfold b1; push_cast; ring
  have he0 : (0 : ℚ) ≤ e := by positivity
  have hq0 : (0 : ℚ) ≤ q := by positivity
  have hw0 := (W_pos_odd_all (s + 2 * q + 3 + e) (q + 1) s (by omega)).ne'
  have hw1 := (W_pos_odd_all (s + 2 * q + 3 + e) (q + 1) (s + 1) (by omega)).ne'
  have hbk : b1 (s + 2 * q + 3 + e) s (q + 1) + ((q + 1 : ℕ) : ℚ) < 0 := by rw [hβ]; push_cast; linarith
  have h0 := (div_eq_iff hw0).1 (ratio_i_odd' (s + 2 * q + 3 + e) s (q + 1) (by omega))
  have h1 := (div_eq_iff hw1).1 (ratio_i_odd' (s + 2 * q + 3 + e) (s + 1) (q + 1) (by omega))
  rw [hβ1, show s + 1 + 1 = s + 2 from rfl] at h1
  have r1 := R1 (2 * (s + 2 * q + 3 + e) + 1) s (q + 1) _ _ h0 h1 (by omega) hbk hbk
  have hii := ii_core (2 * (s + 2 * q + 3 + e) + 1) s q _ _
    (fun t ht => thmK_odd (s + 2 * q + 3 + e) s (q + 1) (by omega) (s + t) (by omega) (by omega)) (by omega)
    (by linarith) (by linarith) hw0
  have hiii := iii_core (2 * (s + 2 * q + 3 + e) + 1) s q (b1 (s + 2 * q + 3 + e) s (q + 1))
    (b1 (s + 2 * q + 3 + e) s (q + 1))
    (fun t ht => by
      have := thmK_odd (s + 2 * q + 3 + e) (s + 1) (q + 1) (by omega) (s + 1 + t) (by omega) (by omega)
      rw [hβ1] at this; exact this) (by omega) (by linarith) (by linarith) hw1
  have r2 := R2 (2 * (s + 2 * q + 3 + e) + 1) s q _ _ h0 hii hiii (by omega) hbk hbk
  have r3 := R3_odd s q e
  have K := knuth_G (2 * (s + 2 * q + 3 + e) + 1) s q
  rw [hβ] at r1 r2 ⊢
  unfold Mpoly
  simp only [Nat.cast_add, Nat.cast_one] at r1 r2 r3 ⊢
  have hsg : (s : ℚ) + 1 / 2 ≠ 0 := by positivity
  have key : W (2 * (s + 2 * q + 3 + e) + 1) (s + 1) (q + 1) * ((s : ℚ) + 1 / 2)
      * (Pad (2 * (s + 2 * q + 3 + e) + 1) s (q + 1)
          * (((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s + 2) : ℚ)
            * ((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s + 4 * (q + 1)) : ℚ)
            * ((s : ℚ) + 1 / 2) * (-((q : ℚ) + e + 5 / 2) + ((q : ℚ) + 1)) * (-((q : ℚ) + e + 5 / 2) + ((q : ℚ) + 1)))
        - W (2 * (s + 2 * q + 3 + e) + 1) (s + 1) (q + 1)
          * (((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s + 4 * (q + 1) + 2) : ℚ)
            * ((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s) : ℚ)
            * (((s : ℚ) + 1 / 2) * (((q : ℚ) + 1) ^ 2 - -((q : ℚ) + e + 5 / 2) * -((q : ℚ) + e + 5 / 2))
              - ((q : ℚ) + 1) ^ 2 * (-((q : ℚ) + e + 5 / 2) + -((q : ℚ) + e + 5 / 2))
              - 2 * ((q : ℚ) + 1) * -((q : ℚ) + e + 5 / 2) * -((q : ℚ) + e + 5 / 2)
              + ((q : ℚ) + 1) ^ 2 * (-((q : ℚ) + e + 5 / 2) + -((q : ℚ) + e + 5 / 2))
                * (-((q : ℚ) + e + 5 / 2) + -((q : ℚ) + e + 5 / 2) + 2 * ((q : ℚ) + 1))
                * ((s : ℚ) + 1 / 2 + ((q : ℚ) + 1))))) = 0 := by
    linear_combination (-(((s : ℚ) + 1 / 2) * (((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s + 2) : ℚ)
            * ((2 * (s + 2 * q + 3 + e) + 1).choose (2 * s + 4 * (q + 1)) : ℚ)
            * ((s : ℚ) + 1 / 2) * (-((q : ℚ) + e + 5 / 2) + ((q : ℚ) + 1))
            * (-((q : ℚ) + e + 5 / 2) + ((q : ℚ) + 1))))) * K + r3 - r1 + ((s : ℚ) + 1 / 2) * r2
  rcases mul_eq_zero.1 key with hz | hz
  · exact absurd hz (mul_ne_zero hw1 hsg)
  · exact sub_eq_zero.1 hz

/-- **(iv), even `n = 2m`** (`b₂ = b₁ + 1`), division-free. -/
theorem iv_even (m s q : ℕ) (h : s + 2 * (q + 1) + 1 ≤ m) :
    Pad (2 * m) s (q + 1) * (((2 * m).choose (2 * s + 2) : ℚ) * ((2 * m).choose (2 * s + 4 * (q + 1)) : ℚ)
        * ((s : ℚ) + 1 / 2) * (b1 m s (q + 1) + (q + 1 : ℕ)) * (b1 m s (q + 1) + 1 + (q + 1 : ℕ)))
      = W (2 * m) (s + 1) (q + 1) * (((2 * m).choose (2 * s + 4 * (q + 1) + 2) : ℚ)
        * ((2 * m).choose (2 * s) : ℚ)
        * Mpoly ((s : ℚ) + 1 / 2) ((q + 1 : ℕ) : ℚ) (b1 m s (q + 1)) (b1 m s (q + 1) + 1)) := by
  obtain ⟨e, rfl⟩ : ∃ e, m = s + 2 * q + 3 + e := ⟨m - (s + 2 * q + 3), by omega⟩
  have hβ : b1 (s + 2 * q + 3 + e) s (q + 1) = -((q : ℚ) + e + 5 / 2) := by unfold b1; push_cast; ring
  have hβ1 : b1 (s + 2 * q + 3 + e) (s + 1) (q + 1) = b1 (s + 2 * q + 3 + e) s (q + 1) + 1 := by
    unfold b1; push_cast; ring
  have he0 : (0 : ℚ) ≤ e := by positivity
  have hq0 : (0 : ℚ) ≤ q := by positivity
  have hw0 := (W_pos_even_all (s + 2 * q + 3 + e) (q + 1) s (by omega)).ne'
  have hw1 := (W_pos_even_all (s + 2 * q + 3 + e) (q + 1) (s + 1) (by omega)).ne'
  have hbk : b1 (s + 2 * q + 3 + e) s (q + 1) + ((q + 1 : ℕ) : ℚ) < 0 := by rw [hβ]; push_cast; linarith
  have hbk' : b1 (s + 2 * q + 3 + e) s (q + 1) + 1 + ((q + 1 : ℕ) : ℚ) < 0 := by rw [hβ]; push_cast; linarith
  have h0 := (div_eq_iff hw0).1 (ratio_i_even' (s + 2 * q + 3 + e) s (q + 1) (by omega))
  have h1 := (div_eq_iff hw1).1 (ratio_i_even' (s + 2 * q + 3 + e) (s + 1) (q + 1) (by omega))
  rw [hβ1, show s + 1 + 1 = s + 2 from rfl] at h1
  have r1 := R1 (2 * (s + 2 * q + 3 + e)) s (q + 1) _ _ h0 h1 (by omega) hbk hbk'
  have hii := ii_core (2 * (s + 2 * q + 3 + e)) s q _ _
    (fun t ht => thmK_even (s + 2 * q + 3 + e) s (q + 1) (by omega) (s + t) (by omega) (by omega)) (by omega)
    (by linarith) (by linarith) hw0
  have hiii := iii_core (2 * (s + 2 * q + 3 + e)) s q (b1 (s + 2 * q + 3 + e) s (q + 1))
    (b1 (s + 2 * q + 3 + e) s (q + 1) + 1)
    (fun t ht => by
      have := thmK_even (s + 2 * q + 3 + e) (s + 1) (q + 1) (by omega) (s + 1 + t) (by omega) (by omega)
      rw [hβ1] at this; exact this) (by omega) (by linarith) (by linarith) hw1
  have r2 := R2 (2 * (s + 2 * q + 3 + e)) s q _ _ h0 hii hiii (by omega) hbk hbk'
  have r3 := R3_even s q e
  have K := knuth_G (2 * (s + 2 * q + 3 + e)) s q
  rw [hβ] at r1 r2 ⊢
  unfold Mpoly
  simp only [Nat.cast_add, Nat.cast_one] at r1 r2 r3 ⊢
  have hsg : (s : ℚ) + 1 / 2 ≠ 0 := by positivity
  have key : W (2 * (s + 2 * q + 3 + e)) (s + 1) (q + 1) * ((s : ℚ) + 1 / 2)
      * (Pad (2 * (s + 2 * q + 3 + e)) s (q + 1)
          * (((2 * (s + 2 * q + 3 + e)).choose (2 * s + 2) : ℚ)
            * ((2 * (s + 2 * q + 3 + e)).choose (2 * s + 4 * (q + 1)) : ℚ)
            * ((s : ℚ) + 1 / 2) * (-((q : ℚ) + e + 5 / 2) + ((q : ℚ) + 1))
            * (-((q : ℚ) + e + 5 / 2) + 1 + ((q : ℚ) + 1)))
        - W (2 * (s + 2 * q + 3 + e)) (s + 1) (q + 1)
          * (((2 * (s + 2 * q + 3 + e)).choose (2 * s + 4 * (q + 1) + 2) : ℚ)
            * ((2 * (s + 2 * q + 3 + e)).choose (2 * s) : ℚ)
            * (((s : ℚ) + 1 / 2) * (((q : ℚ) + 1) ^ 2 - -((q : ℚ) + e + 5 / 2) * (-((q : ℚ) + e + 5 / 2) + 1))
              - ((q : ℚ) + 1) ^ 2 * (-((q : ℚ) + e + 5 / 2) + (-((q : ℚ) + e + 5 / 2) + 1))
              - 2 * ((q : ℚ) + 1) * -((q : ℚ) + e + 5 / 2) * (-((q : ℚ) + e + 5 / 2) + 1)
              + ((q : ℚ) + 1) ^ 2 * (-((q : ℚ) + e + 5 / 2) + (-((q : ℚ) + e + 5 / 2) + 1))
                * (-((q : ℚ) + e + 5 / 2) + (-((q : ℚ) + e + 5 / 2) + 1) + 2 * ((q : ℚ) + 1))
                * ((s : ℚ) + 1 / 2 + ((q : ℚ) + 1))))) = 0 := by
    linear_combination (-(((s : ℚ) + 1 / 2) * (((2 * (s + 2 * q + 3 + e)).choose (2 * s + 2) : ℚ)
            * ((2 * (s + 2 * q + 3 + e)).choose (2 * s + 4 * (q + 1)) : ℚ)
            * ((s : ℚ) + 1 / 2) * (-((q : ℚ) + e + 5 / 2) + ((q : ℚ) + 1))
            * (-((q : ℚ) + e + 5 / 2) + 1 + ((q : ℚ) + 1))))) * K + r3 - r1 + ((s : ℚ) + 1 / 2) * r2
  rcases mul_eq_zero.1 key with hz | hz
  · exact absurd hz (mul_ne_zero hw1 hsg)
  · exact sub_eq_zero.1 hz

end Bali.GPOpen

#print axioms Bali.GPOpen.iv_odd
#print axioms Bali.GPOpen.iv_even

end Stage10
