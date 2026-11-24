import P699.GaussDeBruijn

/-!
# The case `d = 4` of the real-`n` continuation (Bali lab, 2026-11-05)

For non-integer `w > 3`, the truncated sums `V_N` of `∏ C(w,xᵢ) ∏ (xⱼ-xᵢ)` over 4-subsets of `{0..N}` converge to
`(1/2) w² (w-1) (w-2) B(w-1) B(w-2)`, where `B(k) = Γ(2k+1)/Γ(k+1)²`.  No Carlson theorem is used.
-/

open Finset Matrix Filter Real

namespace Bali.GD4
open Bali.PfP Bali.VB Bali.GDB GaussTarget

/-- `∑ᵢ C(k,i) (H(1-k+i) + H(-k+i)) - 2^M 2^(M+k)`. -/
noncomputable def Xf (M : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), (k.choose i : ℝ) * (Hz M M (1 - (k : ℤ) + i) + Hz M M (-(k : ℤ) + i)) -
    (2 : ℝ) ^ M * (2 : ℝ) ^ (M + k)

theorem skew_FM (w : ℝ) (j k : ℕ) (hM : 0 < w - j - k) :
    FM w j (j + k) - FM w (j + k) j = ffr w j * ffr w (j + k) * Xf (w - j - k) k := by
  rw [FM_value_le w j k hM, FM_value_ge w j k hM, Xf,
    show w - (j : ℝ) - k + k = w - j by ring, mul_sum]
  simp only [mul_add, sum_add_distrib, mul_sum, mul_sub]
  ring

section Closed
variable (M : ℝ) (hM : 0 < M)
include hM

lemma B1 : Bsum M 1 = Bsum M 0 * M / (M + 1) := by
  have h := Bsum_recur M hM 0
  have hp : M + 1 ≠ 0 := by linarith
  simp only [Nat.cast_zero, add_zero, sub_zero, zero_add] at h
  rw [eq_div_iff hp]; linarith

lemma B2 : Bsum M 2 = Bsum M 1 * (M - 1) / (M + 2) := by
  have h := Bsum_recur M hM 1
  have hp : M + 2 ≠ 0 := by linarith
  simp only [Nat.cast_one, one_add_one_eq_two] at h
  rw [eq_div_iff hp]
  linarith

lemma B3 : Bsum M 3 = Bsum M 2 * (M - 2) / (M + 3) := by
  have h := Bsum_recur M hM 2
  have hp : M + 3 ≠ 0 := by linarith
  norm_num at h
  rw [eq_div_iff hp]
  linarith

lemma Hneg0 : Hz M M 0 = (2 : ℝ) ^ M * (2 : ℝ) ^ M - (((2 : ℝ) ^ M * (2 : ℝ) ^ M - Bsum M 0) / 2) := by
  have := Hz_closed_nonpos M hM 0
  simpa using this

lemma Hneg1 : Hz M M (-1) = (2 : ℝ) ^ M * (2 : ℝ) ^ M -
    (((2 : ℝ) ^ M * (2 : ℝ) ^ M - Bsum M 0) / 2 - Bsum M 1) := by
  have := Hz_closed_nonpos M hM 1
  simpa using this

lemma Hneg2 : Hz M M (-2) = (2 : ℝ) ^ M * (2 : ℝ) ^ M -
    (((2 : ℝ) ^ M * (2 : ℝ) ^ M - Bsum M 0) / 2 - (Bsum M 1 + Bsum M 2)) := by
  have := Hz_closed_nonpos M hM 2
  simpa [sum_range_succ] using this

lemma Hneg3 : Hz M M (-3) = (2 : ℝ) ^ M * (2 : ℝ) ^ M -
    (((2 : ℝ) ^ M * (2 : ℝ) ^ M - Bsum M 0) / 2 - (Bsum M 1 + Bsum M 2 + Bsum M 3)) := by
  have := Hz_closed_nonpos M hM 3
  simpa [sum_range_succ] using this

lemma Hpos1 : Hz M M 1 = ((2 : ℝ) ^ M * (2 : ℝ) ^ M - Bsum M 0) / 2 := by
  have := Hz_closed_pos M hM 0
  simpa using this

lemma two_add (k : ℕ) : (2 : ℝ) ^ (M + k) = (2 : ℝ) ^ M * 2 ^ k := by
  rw [Real.rpow_add (by norm_num), Real.rpow_natCast]

theorem Xf1 : Xf M 1 = Bsum M 0 * (2 * M + 1) / (M + 1) := by
  have hp : M + 1 ≠ 0 := by linarith
  unfold Xf
  rw [two_add M hM 1]
  norm_num [sum_range_succ]
  rw [Hneg0 M hM, Hneg1 M hM, Hpos1 M hM, B1 M hM]
  field_simp
  ring

theorem Xf2 : Xf M 2 = 2 * Bsum M 0 * (2 * M + 1) * (2 * M + 3) / ((M + 1) * (M + 2)) := by
  have hp : M + 1 ≠ 0 := by linarith
  have hq : M + 2 ≠ 0 := by linarith
  unfold Xf
  rw [two_add M hM 2]
  norm_num [sum_range_succ, Nat.choose]
  rw [Hneg0 M hM, Hneg1 M hM, Hneg2 M hM, Hpos1 M hM, B2 M hM, B1 M hM]
  field_simp
  ring

theorem Xf3 : Xf M 3 =
    2 * Bsum M 0 * (2 * M + 1) * (2 * M + 3) * (3 * M + 7) / ((M + 1) * (M + 2) * (M + 3)) := by
  have hp : M + 1 ≠ 0 := by linarith
  have hq : M + 2 ≠ 0 := by linarith
  have hr : M + 3 ≠ 0 := by linarith
  unfold Xf
  rw [two_add M hM 3]
  norm_num [sum_range_succ, Nat.choose]
  rw [Hneg0 M hM, Hneg1 M hM, Hneg2 M hM, Hneg3 M hM, Hpos1 M hM, B3 M hM, B2 M hM, B1 M hM]
  field_simp
  ring

end Closed

/-- `B(k) = Γ(2k+1)/Γ(k+1)²`. -/
noncomputable def B0 (k : ℝ) : ℝ := Gamma (2 * k + 1) / (Gamma (k + 1) * Gamma (k + 1))

theorem Bsum_zero (M : ℝ) (hM : 0 < M) (hni : ∀ n : ℕ, M ≠ n) : Bsum M 0 = B0 M := by
  have := (gauss_binom_real M hM hni 0).tsum_eq
  simpa [Bsum, B0] using this

theorem B0_succ (M : ℝ) (hM : 0 < M) : B0 (M + 1) = B0 M * (2 * (2 * M + 1)) / (M + 1) := by
  unfold B0
  have a1 : M + 1 ≠ 0 := by linarith
  have a2 : 2 * M + 1 ≠ 0 := by linarith
  have a3 : 2 * M + 2 ≠ 0 := by linarith
  rw [show 2 * (M + 1) + 1 = (2 * M + 2) + 1 by ring, Real.Gamma_add_one a3,
    show 2 * M + 2 = (2 * M + 1) + 1 by ring, Real.Gamma_add_one a2, Real.Gamma_add_one a1]
  have g1 : Gamma (M + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  field_simp
  ring

/-- Pfaffian of a skew `4 × 4` matrix with `G₀₁ ≠ 0`, through `pfP_gram`. -/
theorem pf4 (G : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) (hskew : Gᵀ = -G)
    (h01 : G (0, 0) (0, 1) ≠ 0)
    (hP : G (0, 0) (0, 1) * G (1, 0) (1, 1) - G (0, 0) (1, 0) * G (0, 1) (1, 1) +
      G (0, 0) (1, 1) * G (0, 1) (1, 0) ≠ 0) :
    pfP G = (G (0, 0) (0, 1) * G (1, 0) (1, 1) - G (0, 0) (1, 0) * G (0, 1) (1, 1) +
      G (0, 0) (1, 1) * G (0, 1) (1, 0)) * pfP (Om 2 : Matrix _ _ ℝ) := by
  classical
  have sk : ∀ a b, G b a = -G a b := fun a b => by
    have := congrFun (congrFun hskew a) b
    simpa [Matrix.transpose_apply] using this
  have diag : ∀ a, G a a = 0 := fun a => by have := sk a a; linarith
  set α : ℝ := G (0, 1) (1, 1) / G (0, 0) (0, 1) with hα
  let i : Fin 2 × Fin 2 := (1, 1)
  let j : Fin 2 × Fin 2 := (0, 0)
  have hij : i ≠ j := by decide
  let T := Matrix.transvection i j α
  have hdet : det T = 1 := Matrix.det_transvection_of_ne i j hij α
  have htr : Tᵀ = Matrix.transvection j i α := by
    ext a b
    simp [T, Matrix.transvection, Matrix.one_apply, Matrix.single_apply, Matrix.transpose_apply, eq_comm, and_comm]
  set G' := T * G * Tᵀ with hG'
  have hcong : pfP G' = det T * pfP G := pfP_congr G T
  have hent : ∀ a b, G' a b =
      (if b = i then G a b + α * G a j else G a b) +
        (if a = i then α * (if b = i then G j b + α * G j j else G j b) else 0) := by
    intro a b
    have e1 : ∀ c, (G * Tᵀ) c b = if b = i then G c b + α * G c j else G c b := by
      intro c
      rw [htr]
      by_cases hb : b = i
      · subst hb
        simp only [if_true]
        exact Matrix.mul_transvection_apply_same _ _ _ _ _
      · simp only [hb, if_false]
        exact Matrix.mul_transvection_apply_of_ne j i c b hb α G
    rw [hG', Matrix.mul_assoc]
    by_cases ha : a = i
    · subst ha
      simp only [if_true]
      show (T * (G * Tᵀ)) i b = _
      rw [show (T * (G * Tᵀ)) i b = (G * Tᵀ) i b + α * (G * Tᵀ) j b from
        Matrix.transvection_mul_apply_same _ _ _ _ _, e1, e1]
    · simp only [ha, if_false, add_zero]
      rw [show (T * (G * Tᵀ)) a b = (G * Tᵀ) a b from
        Matrix.transvection_mul_apply_of_ne i j a b ha α _, e1]
  have hne : ∀ x y : Fin 2 × Fin 2, x ≠ y → x ≠ y := fun _ _ h => h
  have n01 : ((0 : Fin 2), (1 : Fin 2)) ≠ i := by decide
  have n00 : ((0 : Fin 2), (0 : Fin 2)) ≠ i := by decide
  have n10 : ((1 : Fin 2), (0 : Fin 2)) ≠ i := by decide
  have E0001 : G' (0, 0) (0, 1) = G (0, 0) (0, 1) := by rw [hent]; simp [n00, n01]
  have E0011 : G' (0, 0) (1, 1) = G (0, 0) (1, 1) := by
    rw [hent]; simp [n00, i, j, diag]
  have E1001 : G' (1, 0) (0, 1) = G (1, 0) (0, 1) := by rw [hent]; simp [n10, n01]
  have E1011 : G' (1, 0) (1, 1) = G (1, 0) (1, 1) + α * G (1, 0) (0, 0) := by
    rw [hent]; simp [n10, i, j]
  have E0111 : G' (0, 1) (1, 1) = 0 := by
    rw [hent]; simp only [n01, if_false, add_zero, i, j, if_true]
    rw [sk (0, 0) (0, 1), hα]; field_simp; ring
  have skew' : G'ᵀ = -G' := by
    rw [hG', Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hskew]
    simp [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
  have sk' : ∀ a b, G' b a = -G' a b := fun a b => by
    have := congrFun (congrFun skew' a) b
    simpa [Matrix.transpose_apply] using this
  have diag' : ∀ a, G' a a = 0 := fun a => by have := sk' a a; linarith
  have hOO : ∀ p q : Fin 2, G' (p, 1) (q, 1) = 0 := by
    intro p q
    fin_cases p <;> fin_cases q
    · exact diag' _
    · exact E0111
    · have := sk' (0, 1) (1, 1); simp only [Fin.isValue] at this ⊢
      show G' (1, 1) (0, 1) = 0
      rw [this, E0111]; simp
    · exact diag' _
  have hdetY : det (fun p q => G' (p, 0) (q, 1) : Matrix (Fin 2) (Fin 2) ℝ) =
      G (0, 0) (0, 1) * G (1, 0) (1, 1) - G (0, 0) (1, 0) * G (0, 1) (1, 1) +
        G (0, 0) (1, 1) * G (0, 1) (1, 0) := by
    refine (Matrix.det_fin_two _).trans ?_
    show G' (0, 0) (0, 1) * G' (1, 0) (1, 1) - G' (0, 0) (1, 1) * G' (1, 0) (0, 1) = _
    rw [E0001, E1011, E0011, E1001, hα, sk (0, 0) (1, 0), sk (0, 1) (1, 0)]
    field_simp
    ring
  have hg := pfP_gram G' skew' hOO (by rw [hdetY]; exact isUnit_iff_ne_zero.mpr hP)
  rw [hdetY] at hg
  rw [hcong, hdet, one_mul] at hg
  exact hg

/-- Ordinary moments up to order 3 through falling moments. -/
theorem OM_table (w : ℝ) (hw : 3 < w) :
    OM w 0 1 = FM w 0 0 * 0 + FM w 0 1 ∧ OM w 1 0 = FM w 1 0 ∧
    OM w 0 2 = FM w 0 1 + FM w 0 2 ∧ OM w 2 0 = FM w 1 0 + FM w 2 0 ∧
    OM w 0 3 = FM w 0 1 + 3 * FM w 0 2 + FM w 0 3 ∧ OM w 3 0 = FM w 1 0 + 3 * FM w 2 0 + FM w 3 0 ∧
    OM w 1 2 = FM w 1 1 + FM w 1 2 ∧ OM w 2 1 = FM w 1 1 + FM w 2 1 ∧
    OM w 1 3 = FM w 1 1 + 3 * FM w 1 2 + FM w 1 3 ∧ OM w 3 1 = FM w 1 1 + 3 * FM w 2 1 + FM w 3 1 ∧
    OM w 2 3 = FM w 1 1 + 3 * FM w 1 2 + FM w 1 3 + FM w 2 1 + 3 * FM w 2 2 + FM w 2 3 ∧
    OM w 3 2 = FM w 1 1 + FM w 1 2 + 3 * FM w 2 1 + 3 * FM w 2 2 + FM w 3 1 + FM w 3 2 := by
  have S : ∀ a b : ℕ, a ≤ 3 → b ≤ 3 → OM w a b = _ := fun a b ha hb =>
    OM_eq_sum_FM w a b
      (lt_of_le_of_lt (by exact_mod_cast ha) hw) (lt_of_le_of_lt (by exact_mod_cast hb) hw)
  have s10 : Nat.stirlingSecond 1 0 = 0 := by decide
  have s11 : Nat.stirlingSecond 1 1 = 1 := by decide
  have s00 : Nat.stirlingSecond 0 0 = 1 := by decide
  have s20 : Nat.stirlingSecond 2 0 = 0 := by decide
  have s21 : Nat.stirlingSecond 2 1 = 1 := by decide
  have s22 : Nat.stirlingSecond 2 2 = 1 := by decide
  have s30 : Nat.stirlingSecond 3 0 = 0 := by decide
  have s31 : Nat.stirlingSecond 3 1 = 1 := by decide
  have s32 : Nat.stirlingSecond 3 2 = 3 := by decide
  have s33 : Nat.stirlingSecond 3 3 = 1 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [S _ _ (by norm_num) (by norm_num), sum_product]
     simp only [sum_range_succ, sum_range_zero, zero_add, s00, s10, s11, s20, s21, s22, s30, s31, s32, s33,
       Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul, one_mul]
     try ring)

/-- **The case `d = 4` of the real-`n` continuation.** -/
theorem d4_limit (w : ℝ) (hw : 3 < w) (hni : ∀ n : ℕ, w ≠ n) :
    Tendsto (fun N => VTr w 2 N) atTop
      (nhds (1 / 2 * w ^ 2 * (w - 1) * (w - 2) * B0 (w - 1) * B0 (w - 2))) := by
  have w0 : w ≠ 0 := by linarith
  have w1 : w - 1 ≠ 0 := by linarith
  have w2 : w - 2 ≠ 0 := by linarith
  have p3 : 0 < w - 3 := by linarith
  have p2 : 0 < w - 2 := by linarith
  have p1 : 0 < w - 1 := by linarith
  have nn : ∀ l : ℕ, ∀ n : ℕ, w - l ≠ n := by
    intro l n h
    apply hni (n + l)
    push_cast; linarith
  have n1 : ∀ n : ℕ, w - 1 ≠ n := by simpa using nn 1
  have n2 : ∀ n : ℕ, w - 2 ≠ n := by simpa using nn 2
  have n3 : ∀ n : ℕ, w - 3 ≠ n := by simpa using nn 3
  set β := B0 (w - 3) with hβ
  have βpos : 0 < β := div_pos (Real.Gamma_pos_of_pos (by linarith))
    (mul_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos (by linarith)))
  have b2 : B0 (w - 2) = β * (2 * (2 * w - 5)) / (w - 2) := by
    have := B0_succ (w - 3) p3
    rw [show w - 3 + 1 = w - 2 by ring, show 2 * (w - 3) + 1 = 2 * w - 5 by ring] at this
    exact this
  have b1 : B0 (w - 1) = B0 (w - 2) * (2 * (2 * w - 3)) / (w - 1) := by
    have := B0_succ (w - 2) p2
    rw [show w - 2 + 1 = w - 1 by ring, show 2 * (w - 2) + 1 = 2 * w - 3 by ring] at this
    exact this
  have X1a : Xf (w - 1) 1 = B0 (w - 1) * (2 * w - 1) / w := by
    rw [Xf1 _ p1, Bsum_zero _ p1 n1, show w - 1 + 1 = w by ring, show 2 * (w - 1) + 1 = 2 * w - 1 by ring]
  have X2a : Xf (w - 2) 2 = 2 * B0 (w - 2) * (2 * w - 3) * (2 * w - 1) / ((w - 1) * w) := by
    rw [Xf2 _ p2, Bsum_zero _ p2 n2, show w - 2 + 1 = w - 1 by ring, show w - 2 + 2 = w by ring,
      show 2 * (w - 2) + 1 = 2 * w - 3 by ring, show 2 * (w - 2) + 3 = 2 * w - 1 by ring]
  have X1b : Xf (w - 2) 1 = B0 (w - 2) * (2 * w - 3) / (w - 1) := by
    rw [Xf1 _ p2, Bsum_zero _ p2 n2, show w - 2 + 1 = w - 1 by ring, show 2 * (w - 2) + 1 = 2 * w - 3 by ring]
  have X3c : Xf (w - 3) 3 = 2 * β * (2 * w - 5) * (2 * w - 3) * (3 * w - 2) / ((w - 2) * (w - 1) * w) := by
    rw [Xf3 _ p3, Bsum_zero _ p3 n3, show w - 3 + 1 = w - 2 by ring, show w - 3 + 2 = w - 1 by ring,
      show w - 3 + 3 = w by ring, show 2 * (w - 3) + 1 = 2 * w - 5 by ring,
      show 2 * (w - 3) + 3 = 2 * w - 3 by ring, show 3 * (w - 3) + 7 = 3 * w - 2 by ring]
  have X2c : Xf (w - 3) 2 = 2 * β * (2 * w - 5) * (2 * w - 3) / ((w - 2) * (w - 1)) := by
    rw [Xf2 _ p3, Bsum_zero _ p3 n3, show w - 3 + 1 = w - 2 by ring, show w - 3 + 2 = w - 1 by ring,
      show 2 * (w - 3) + 1 = 2 * w - 5 by ring, show 2 * (w - 3) + 3 = 2 * w - 3 by ring]
  have X1c : Xf (w - 3) 1 = β * (2 * w - 5) / (w - 2) := by
    rw [Xf1 _ p3, Bsum_zero _ p3 n3, show w - 3 + 1 = w - 2 by ring, show 2 * (w - 3) + 1 = 2 * w - 5 by ring]
  have sk : ∀ (j k : ℕ) (M : ℝ), (w : ℝ) - j - k = M → 0 < M →
      FM w j (j + k) - FM w (j + k) j = ffr w j * ffr w (j + k) * Xf M k := by
    intro j k M h hM
    have := skew_FM w j k (by rw [h]; exact hM)
    rwa [h] at this
  have f01 : FM w 0 1 - FM w 1 0 = w * Xf (w - 1) 1 := by
    have := sk 0 1 (w - 1) (by push_cast; ring) p1
    simp only [zero_add] at this
    rw [this]; simp [ffr]
  have f02 : FM w 0 2 - FM w 2 0 = w * (w - 1) * Xf (w - 2) 2 := by
    have := sk 0 2 (w - 2) (by push_cast; ring) p2
    simp only [zero_add] at this
    rw [this]; simp [ffr, prod_range_succ]
  have f03 : FM w 0 3 - FM w 3 0 = w * (w - 1) * (w - 2) * Xf (w - 3) 3 := by
    have := sk 0 3 (w - 3) (by push_cast; ring) p3
    simp only [zero_add] at this
    rw [this]; simp [ffr, prod_range_succ]
  have f12 : FM w 1 2 - FM w 2 1 = w * (w * (w - 1)) * Xf (w - 2) 1 := by
    have := sk 1 1 (w - 2) (by push_cast; ring) p2
    rw [show (1 : ℕ) + 1 = 2 from rfl] at this
    rw [this]; simp [ffr, prod_range_succ]
  have f13 : FM w 1 3 - FM w 3 1 = w * (w * (w - 1) * (w - 2)) * Xf (w - 3) 2 := by
    have := sk 1 2 (w - 3) (by push_cast; ring) p3
    rw [show (1 : ℕ) + 2 = 3 from rfl] at this
    rw [this]; simp [ffr, prod_range_succ]
  have f23 : FM w 2 3 - FM w 3 2 = w * (w - 1) * (w * (w - 1) * (w - 2)) * Xf (w - 3) 1 := by
    have := sk 2 1 (w - 3) (by push_cast; ring) p3
    rw [show (2 : ℕ) + 1 = 3 from rfl] at this
    rw [this]; simp [ffr, prod_range_succ]
  obtain ⟨o01, o10, o02, o20, o03, o30, o12, o21, o13, o31, o23, o32⟩ := OM_table w hw
  have lt4 : ∀ c : Fin 2 × Fin 2, (((eι 2 c : Fin (2 * 2)) : ℕ) : ℝ) < w := by
    intro c
    have h1 : ((eι 2 c : Fin (2 * 2)) : ℕ) ≤ 3 := by have := (eι 2 c).isLt; omega
    have h2 : (((eι 2 c : Fin (2 * 2)) : ℕ) : ℝ) ≤ 3 := by exact_mod_cast h1
    linarith
  set G : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
    fun a b => skM w (eι 2 a : ℕ) (eι 2 b : ℕ) with hG
  have hskew : Gᵀ = -G := by
    ext a b
    show skM w _ _ = - skM w _ _
    rw [skM_eq_OM w _ _ (lt4 b) (lt4 a), skM_eq_OM w _ _ (lt4 a) (lt4 b), add_comm]
    ring
  have idx : ∀ (p q : Fin 2), ((eι 2 (p, q) : Fin (2 * 2)) : ℕ) = 2 * (p : ℕ) + (q : ℕ) := fun p q => eι_val 2 (p, q)
  have E : ∀ (p q r s : Fin 2) (e f : ℕ), 2 * (p : ℕ) + (q : ℕ) = e → 2 * (r : ℕ) + (s : ℕ) = f →
      G (p, q) (r, s) = (-1 : ℝ) ^ (e + f) * (OM w e f - OM w f e) := by
    intro p q r s e f h1 h2
    have l1 := lt4 (p, q)
    have l2 := lt4 (r, s)
    show skM w _ _ = _
    rw [skM_eq_OM w _ _ l1 l2, idx, idx, h1, h2]
  have a01 : G (0, 0) (0, 1) = -(w * Xf (w - 1) 1) := by
    rw [E 0 0 0 1 0 1 (by simp) (by simp), o01, o10, ← f01]; norm_num
  have a23 : G (1, 0) (1, 1) = -(2 * (w * (w * (w - 1)) * Xf (w - 2) 1) +
      w * (w * (w - 1) * (w - 2)) * Xf (w - 3) 2 + w * (w - 1) * (w * (w - 1) * (w - 2)) * Xf (w - 3) 1) := by
    rw [E 1 0 1 1 2 3 (by simp) (by simp), o23, o32, ← f12, ← f13, ← f23]; norm_num <;> ring
  have a02 : G (0, 0) (1, 0) = w * Xf (w - 1) 1 + w * (w - 1) * Xf (w - 2) 2 := by
    rw [E 0 0 1 0 0 2 (by simp) (by simp), o02, o20, ← f01, ← f02]; norm_num <;> ring
  have a13 : G (0, 1) (1, 1) = 3 * (w * (w * (w - 1)) * Xf (w - 2) 1) +
      w * (w * (w - 1) * (w - 2)) * Xf (w - 3) 2 := by
    rw [E 0 1 1 1 1 3 (by simp) (by simp), o13, o31, ← f12, ← f13]; norm_num <;> ring
  have a03 : G (0, 0) (1, 1) = -(w * Xf (w - 1) 1 + 3 * (w * (w - 1) * Xf (w - 2) 2) +
      w * (w - 1) * (w - 2) * Xf (w - 3) 3) := by
    rw [E 0 0 1 1 0 3 (by simp) (by simp), o03, o30, ← f01, ← f02, ← f03]; norm_num <;> ring
  have a12 : G (0, 1) (1, 0) = -(w * (w * (w - 1)) * Xf (w - 2) 1) := by
    rw [E 0 1 1 0 1 2 (by simp) (by simp), o12, o21, ← f12]; norm_num <;> ring
  have hval : G (0, 0) (0, 1) * G (1, 0) (1, 1) - G (0, 0) (1, 0) * G (0, 1) (1, 1) +
      G (0, 0) (1, 1) * G (0, 1) (1, 0) = 1 / 2 * w ^ 2 * (w - 1) * (w - 2) * B0 (w - 1) * B0 (w - 2) := by
    rw [a01, a23, a02, a13, a03, a12, X1a, X2a, X1b, X3c, X2c, X1c, b1, b2]
    field_simp
    ring
  have h5 : 2 * w - 5 ≠ 0 := by linarith
  have h3 : 2 * w - 3 ≠ 0 := by linarith
  have h1' : 2 * w - 1 ≠ 0 := by linarith
  have βne : β ≠ 0 := βpos.ne'
  have hB2 : B0 (w - 2) ≠ 0 := by
    rw [b2]; exact div_ne_zero (mul_ne_zero βne (mul_ne_zero two_ne_zero h5)) w2
  have hB1 : B0 (w - 1) ≠ 0 := by
    rw [b1]; exact div_ne_zero (mul_ne_zero hB2 (mul_ne_zero two_ne_zero h3)) w1
  have h01 : G (0, 0) (0, 1) ≠ 0 := by
    rw [a01, X1a]
    exact neg_ne_zero.mpr (mul_ne_zero w0 (div_ne_zero (mul_ne_zero hB1 h1') w0))
  have hP : G (0, 0) (0, 1) * G (1, 0) (1, 1) - G (0, 0) (1, 0) * G (0, 1) (1, 1) +
      G (0, 0) (1, 1) * G (0, 1) (1, 0) ≠ 0 := by
    rw [hval]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 w0)) w1) w2) hB1 |>.symm.symm |> fun h => mul_ne_zero h hB2
  have hpf := pf4 G hskew h01 hP
  have hO : pfP (Om 2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) ≠ 0 := pfP_Om_ne_zero 2
  have hsg : (sgnPairs (2 * 2) : ℝ) = 1 := by
    simp [sgnPairs, Finset.prod_const, Fin.prod_univ_four, Fin.card_Ioi]
    norm_num
  have ht := VTr_tendsto w 2 (by norm_num; linarith)
  have ev : pfP (fun a b : Fin 2 × Fin 2 => skM w (eι 2 a : ℕ) (eι 2 b : ℕ)) /
      (pfP (J0 2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) * sgnPairs (2 * 2)) =
      1 / 2 * w ^ 2 * (w - 1) * (w - 2) * B0 (w - 1) * B0 (w - 2) := by
    rw [show (fun a b : Fin 2 × Fin 2 => skM w (eι 2 a : ℕ) (eι 2 b : ℕ)) = G from rfl, hpf, hval, pfP_J0, hsg,
      mul_one]
    field_simp
  rwa [ev] at ht

end Bali.GD4

#print axioms Bali.GD4.pf4
#print axioms Bali.GD4.Xf3
#print axioms Bali.GD4.OM_table
#print axioms Bali.GD4.d4_limit
