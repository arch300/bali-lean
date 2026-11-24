import P699.Final
import P699.TWatson

/-!
# Reservation 2: odd `d = 2m+1` via a virtual point `∞` (Bali lab, 2026-11-02)
Append a point `∞` after the shells and an extra row `δ_∞`.  Then
`⟨f, δ_∞⟩ = Σ f = T(f)`, the `(2m+2)`-minors containing `∞` are the `(2m+1)`-minors, and the even
de Bruijn theorem `sum_minors_eq_det` applies unchanged.
-/

open Finset Polynomial Matrix

namespace Bali.OddB
open Bali Bali.PfP Bali.VB Bali.Skew

/-! ## Part 1: generic augmentation -/

section Aug
variable {N : ℕ}

/-- extend by `0` at `∞ = last`. -/
def ext (f : Fin (N + 1) → ℚ) : Fin (N + 1 + 1) → ℚ :=
  fun x => if hx : (x : ℕ) < N + 1 then f ⟨x, hx⟩ else 0
/-- the indicator of `∞`. -/
def dI : Fin (N + 1 + 1) → ℚ := fun x => if (x : ℕ) = N + 1 then 1 else 0

@[simp] lemma ext_cs (f : Fin (N + 1) → ℚ) (k : Fin (N + 1)) : ext f k.castSucc = f k := by
  unfold ext; rw [dif_pos (show (k.castSucc : ℕ) < N + 1 from k.isLt)]; rfl
@[simp] lemma ext_last (f : Fin (N + 1) → ℚ) : ext f (Fin.last (N + 1)) = 0 := by simp [ext]
@[simp] lemma dI_cs (k : Fin (N + 1)) : (dI : Fin (N + 1 + 1) → ℚ) k.castSucc = 0 := by
  simp [dI]; omega
@[simp] lemma dI_last : (dI : Fin (N + 1 + 1) → ℚ) (Fin.last (N + 1)) = 1 := by simp [dI]

lemma skew_eq (f g : Fin (N + 1) → ℚ) :
    skew f g = ∑ k, f k * ∑ l, g l * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ) k l := by
  unfold skew
  exact sum_congr rfl fun k _ => by rw [row_signM]

@[simp] lemma signM_cs (k l : Fin (N + 1)) :
    (signM (N + 1) : Matrix (Fin (N + 1 + 1)) (Fin (N + 1 + 1)) ℚ) k.castSucc l.castSucc
      = (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ) k l := by
  simp [signM, Fin.castSucc_lt_castSucc_iff]
@[simp] lemma signM_cs_last (k : Fin (N + 1)) :
    (signM (N + 1) : Matrix (Fin (N + 1 + 1)) (Fin (N + 1 + 1)) ℚ) k.castSucc (Fin.last _) = 1 := by
  simp [signM, Fin.castSucc_lt_last]
@[simp] lemma signM_last_cs (k : Fin (N + 1)) :
    (signM (N + 1) : Matrix (Fin (N + 1 + 1)) (Fin (N + 1 + 1)) ℚ) (Fin.last _) k.castSucc = -1 := by
  simp [signM, Fin.castSucc_lt_last, not_lt.2 (Fin.castSucc_lt_last k).le]
@[simp] lemma signM_last_last :
    (signM (N + 1) : Matrix (Fin (N + 1 + 1)) (Fin (N + 1 + 1)) ℚ) (Fin.last _) (Fin.last _) = 0 := by
  simp [signM]

lemma skew_ext_ext (f g : Fin (N + 1) → ℚ) : skew (ext f) (ext g) = skew f g := by
  rw [skew_eq, skew_eq]
  simp [Fin.sum_univ_castSucc]
lemma skew_ext_dI (f : Fin (N + 1) → ℚ) : skew (ext f) dI = ∑ k, f k := by
  rw [skew_eq]
  simp [Fin.sum_univ_castSucc]
lemma skew_dI_ext (g : Fin (N + 1) → ℚ) : skew dI (ext g) = -∑ k, g k := by
  rw [skew_eq]
  simp [Fin.sum_univ_castSucc]; ring
lemma skew_dI_dI : skew (dI : Fin (N + 1 + 1) → ℚ) dI = 0 := by
  rw [skew_eq]
  simp [Fin.sum_univ_castSucc]

lemma skew_anti (f g : Fin (N + 1) → ℚ) : skew f g = -skew g f := by
  rw [skew_eq, skew_eq, ← sum_neg_distrib]
  simp only [mul_sum, ← sum_neg_distrib]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  have : (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ) l k
      = -(signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ) k l := by
    have := congrFun (congrFun (signM_transpose (K := ℚ) (N := N)) k) l
    simpa using this
  rw [this]; ring

variable {m : ℕ}

/-- the slot of a row index, `0 .. 2m+1`. -/
abbrev sl (a : Fin (m + 1) × Fin 2) : ℕ := ((eι (m + 1) a : Fin (2 * (m + 1))) : ℕ)

/-- augmented matrix: rows `r_0..r_{2m}` extended by `0`, last row `δ_∞`. -/
def Ma (r : Fin (2 * m + 1) → Fin (N + 1) → ℚ) : Matrix (Fin (m + 1) × Fin 2) (Fin (N + 1 + 1)) ℚ :=
  fun a => if ha : sl a < 2 * m + 1 then ext (r ⟨sl a, ha⟩) else dI

/-- the augmented point set. -/
def aug (S : Finset (Fin (N + 1))) : Finset (Fin (N + 1 + 1)) := insert (Fin.last _) (S.map Fin.castSuccEmb)

lemma card_aug (S : Finset (Fin (N + 1))) (h : S.card = 2 * m + 1) : (aug S).card = 2 * (m + 1) := by
  rw [aug, card_insert_of_notMem (by simp [Fin.castSucc_ne_last]), card_map, h]; ring

/-- sorted enumeration of `aug S`: the old points, then `∞`. -/
lemma orderEmb_aug (S : Finset (Fin (N + 1))) (h : S.card = 2 * m + 1) (i : Fin (2 * (m + 1))) :
    (aug S).orderEmbOfFin (card_aug S h) i
      = if hi : (i : ℕ) < 2 * m + 1 then (S.orderEmbOfFin h ⟨i, hi⟩).castSucc else Fin.last _ := by
  have hfs : ∀ x : Fin (2 * (m + 1)), (fun i : Fin (2 * (m + 1)) =>
      if hi : (i : ℕ) < 2 * m + 1 then (S.orderEmbOfFin h ⟨i, hi⟩).castSucc else Fin.last (N + 1)) x ∈ aug S := by
    intro x
    dsimp only
    unfold aug
    split_ifs
    · exact mem_insert_of_mem (mem_map_of_mem _ (S.orderEmbOfFin_mem h _))
    · exact mem_insert_self _ _
  have hmono : StrictMono (fun i : Fin (2 * (m + 1)) =>
      if hi : (i : ℕ) < 2 * m + 1 then (S.orderEmbOfFin h ⟨i, hi⟩).castSucc else Fin.last (N + 1)) := by
    intro i j hij
    have hij' : (i : ℕ) < j := hij
    dsimp only
    split_ifs with hi hj hj
    · exact Fin.castSucc_lt_castSucc_iff.2 ((S.orderEmbOfFin h).strictMono (Fin.mk_lt_mk.2 hij'))
    · exact Fin.castSucc_lt_last _
    · omega
    · have := i.isLt; have := j.isLt; omega
  rw [← Finset.orderEmbOfFin_unique (card_aug S h) hfs hmono]
lemma sl_symm (a : Fin (2 * m + 1 + 1)) :
    sl ((eι (m + 1)).symm (finCongr (by ring) a)) = (a : ℕ) := by
  simp [sl]

/-- **minor of the augmented matrix on `aug S` = minor of the rows on `S`.** -/
lemma det_aug (r : Fin (2 * m + 1) → Fin (N + 1) → ℚ) (S : Finset (Fin (N + 1))) (h : S.card = 2 * m + 1) :
    det ((Ma r).submatrix id (G' (m := m + 1) (aug S)))
      = det (Matrix.of fun p q : Fin (2 * m + 1) => r p (S.orderEmbOfFin h q)) := by
  have hG : G' (m := m + 1) (aug S) = GS (aug S) (card_aug S h) := by simp [G', card_aug S h]
  set e : Fin (m + 1) × Fin 2 ≃ Fin (2 * m + 1 + 1) := (eι (m + 1)).trans (finCongr (by ring)) with he
  rw [← det_reindex_self e, det_succ_row _ (Fin.last _), Fin.sum_univ_castSucc]
  have hent : ∀ p q : Fin (2 * m + 1 + 1), reindex e e ((Ma r).submatrix id (G' (m := m + 1) (aug S))) p q
      = Ma r (e.symm p) (if hq : (q : ℕ) < 2 * m + 1 then (S.orderEmbOfFin h ⟨q, hq⟩).castSucc else Fin.last _) := by
    intro p q
    simp only [reindex_apply, submatrix_apply, id, hG, GS]
    rw [orderEmb_aug S h]
    simp [he]
  have hlast : ∀ q : Fin (2 * m + 1 + 1), reindex e e ((Ma r).submatrix id (G' (m := m + 1) (aug S))) (Fin.last _) q
      = if (q : ℕ) < 2 * m + 1 then 0 else 1 := by
    intro q
    rw [hent]
    have : ¬ sl (e.symm (Fin.last (2 * m + 1))) < 2 * m + 1 := by
      rw [he]; simp [sl]
    simp only [Ma, dif_neg this]
    split_ifs with hq <;> simp
  rw [sum_eq_zero (fun j _ => by rw [hlast, if_pos (by simpa using j.isLt)]; simp), zero_add, hlast]
  simp only [Fin.val_last, lt_irrefl, if_false, mul_one, Fin.succAbove_last]
  rw [show ((-1 : ℚ) ^ (2 * m + 1 + (2 * m + 1))) = 1 by
    rw [← two_mul, pow_mul]; simp, one_mul]
  congr 1
  ext p q
  simp only [submatrix_apply, of_apply]
  rw [hent]
  have hp : sl (e.symm p.castSucc) < 2 * m + 1 := by have := p.isLt; rw [he]; simp [sl]; omega
  simp only [Ma, dif_pos hp, Fin.coe_castSucc, q.isLt, dif_pos, ext_cs]
  congr 1
  ext
  show sl (e.symm p.castSucc) = p
  simp [he, sl]

/-- the sorted enumeration of an odd set (junk if the size is wrong). -/
noncomputable def Go (S : Finset (Fin (N + 1))) (q : Fin (2 * m + 1)) : Fin (N + 1) :=
  if h : S.card = 2 * m + 1 then S.orderEmbOfFin h q else 0

/-- **the augmented minor sum is the odd minor sum.** -/
theorem sum_aug (r : Fin (2 * m + 1) → Fin (N + 1) → ℚ) :
    ∑ T ∈ (univ : Finset (Fin (N + 1 + 1))).powersetCard (2 * (m + 1)),
        det ((Ma r).submatrix id (G' (m := m + 1) T))
      = ∑ S ∈ (univ : Finset (Fin (N + 1))).powersetCard (2 * m + 1),
          det (Matrix.of fun p q : Fin (2 * m + 1) => r p (Go S q)) := by
  have huniv : (univ : Finset (Fin (N + 1 + 1))) = insert (Fin.last _) (univ.map Fin.castSuccEmb) := by
    ext x
    rcases Fin.eq_castSucc_or_eq_last x with ⟨y, rfl⟩ | rfl <;> simp
  have hnot : Fin.last (N + 1) ∉ (univ : Finset (Fin (N + 1))).map Fin.castSuccEmb := by
    simp [Fin.castSucc_ne_last]
  rw [huniv, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, powersetCard_succ_insert hnot]
  rw [sum_union]
  · rw [sum_eq_zero, zero_add]
    · rw [sum_image]
      · rw [powersetCard_map, sum_map]
        refine sum_congr rfl fun S hS => ?_
        have h := (mem_powersetCard.1 hS).2
        have e := det_aug r S h
        simp only [aug] at e
        rw [show (mapEmbedding Fin.castSuccEmb).toEmbedding S = S.map Fin.castSuccEmb from rfl, e]
        congr 1
        ext p q
        simp [Go, h]
      · intro A hA B hB hAB
        have hA' : Fin.last (N + 1) ∉ A := fun hm => hnot ((mem_powersetCard.1 hA).1 hm)
        have hB' : Fin.last (N + 1) ∉ B := fun hm => hnot ((mem_powersetCard.1 hB).1 hm)
        rw [← erase_insert hA', hAB, erase_insert hB']
    · intro T hT
      have hTs := (mem_powersetCard.1 hT).1
      have hTc : T.card = 2 * (m + 1) := by rw [(mem_powersetCard.1 hT).2]; omega
      have hlt : 2 * m + 1 < 2 * (m + 1) := by omega
      apply det_eq_zero_of_row_eq_zero ((eι (m + 1)).symm ⟨2 * m + 1, hlt⟩)
      intro b
      have hns : ¬ sl ((eι (m + 1)).symm ⟨2 * m + 1, hlt⟩) < 2 * m + 1 := by simp [sl]
      simp only [submatrix_apply, id, Ma, dif_neg hns, dI]
      rw [if_neg]
      intro hv
      have hmem : G' (m := m + 1) T b ∈ T := by simp only [G', dif_pos hTc]; exact GS_mem T hTc b
      have : G' (m := m + 1) T b = Fin.last (N + 1) := Fin.ext (by simpa using hv)
      exact hnot (hTs (this ▸ hmem))
  · rw [disjoint_left]
    intro T hT hT'
    obtain ⟨A, -, rfl⟩ := mem_image.1 hT'
    exact hnot ((mem_powersetCard.1 hT).1 (mem_insert_self _ _))
end Aug

/-! ## Part 2: the Racah rows, totals `T(R_a)`, the odd Gram matrix -/

section Racah
open Bali.Racah Bali.GR Bali.Final Bali.PsiA Bali.TW Bali.Watson

lemma Rq_symm (H a x : ℕ) (hx : x ≤ 2 * H + 1) :
    Rq (2 * H + 1) a ((2 * H + 1 - x : ℕ) : ℚ) = Rq (2 * H + 1) a (x : ℚ) := by
  rw [← RP_eval, ← RP_eval, Nat.cast_sub hx]
  congr 1; push_cast; ring

lemma row_total (H a : ℕ) :
    ∑ h : Fin (H + 1), row H a h
      = ∑ x ∈ range (2 * H + 1 + 1), ((2 * H + 1).choose x : ℚ) * Rq ((2 * H + 1 : ℕ) : ℚ) a x := by
  rw [show ∑ h : Fin (H + 1), row H a h
      = ∑ h ∈ range (H + 1), 2 * ((2 * H + 1).choose h : ℚ) * (fun x : ℕ => Rq (2 * H + 1) a (x : ℚ)) h from
    Fin.sum_univ_eq_sum_range (fun h => 2 * ((2 * H + 1).choose h : ℚ) * Rq (2 * H + 1) a (h : ℚ)) (H + 1),
    shell_total H _ (fun x hx => (Rq_symm H a x hx).symm)]
  push_cast; rfl

lemma tot_odd (H k : ℕ) (hk : 2 * k + 1 ≤ H) : ∑ h : Fin (H + 1), row H (2 * k + 1) h = 0 := by
  rw [row_total, T_R_odd H k hk]

/-- `T(R_{2k}) = 2ⁿ ∏_{i<k} ((2i+1)/(2H-2i))²` (Watson). -/
lemma tot_even (H k : ℕ) (hk : 2 * k ≤ H) :
    ∑ h : Fin (H + 1), row H (2 * k) h = 2 ^ (2 * H + 1) * ∏ i ∈ range k, ((2 * (i : ℚ) + 1) / (2 * H - 2 * i)) ^ 2 := by
  rw [row_total, T_R H (2 * k) hk]; push_cast; rw [S_even H k hk]

variable (H m : ℕ)

/-- the odd row family `R_0 .. R_{2m}` on the shells. -/
noncomputable def rR : Fin (2 * m + 1) → Fin (H + 1) → ℚ := fun p => row H p
/-- the augmented Racah matrix. -/
noncomputable def MR : Matrix (Fin (m + 1) × Fin 2) (Fin (H + 1 + 1)) ℚ := Ma (rR H m)

lemma MR_lt (a : Fin (m + 1) × Fin 2) (ha : sl a < 2 * m + 1) : MR H m a = ext (row H (sl a)) := by
  simp [MR, Ma, ha, rR]
lemma MR_ge (a : Fin (m + 1) × Fin 2) (ha : ¬ sl a < 2 * m + 1) : MR H m a = dI := by
  simp [MR, Ma, ha]
lemma sl_val (i : Fin (m + 1)) (s : Fin 2) : sl (i, s) = 2 * (i : ℕ) + s := eι_val (m + 1) (i, s)

noncomputable def GramO : Matrix (Fin (m + 1) × Fin 2) (Fin (m + 1) × Fin 2) ℚ :=
  MR H m * (signM (H + 1) : Matrix (Fin (H + 1 + 1)) (Fin (H + 1 + 1)) ℚ) * (MR H m)ᵀ

lemma GramO_entry (a b : Fin (m + 1) × Fin 2) : GramO H m a b = skew (MR H m a) (MR H m b) :=
  gram_eq_skew _ a b

lemma hOO_R (hm : 2 * m ≤ H) (i j : Fin (m + 1)) : GramO H m (i, 1) (j, 1) = 0 := by
  rw [GramO_entry]
  have si := sl_val m i 1
  have sj := sl_val m j 1
  simp only [Fin.val_one] at si sj
  by_cases hi : (i : ℕ) < m <;> by_cases hj : (j : ℕ) < m
  · rw [MR_lt H m _ (by omega), MR_lt H m _ (by omega), skew_ext_ext, si, sj]
    rcases le_or_gt (j : ℕ) i with hji | hij
    · exact skew_rows_zero H (2 * i + 1) j (by omega) (by omega)
    · rw [skew_anti, skew_rows_zero H (2 * j + 1) i (by omega) (by omega), neg_zero]
  · rw [MR_lt H m _ (by omega), MR_ge H m _ (by omega), skew_ext_dI, si, tot_odd H i (by omega)]
  · rw [MR_ge H m _ (by omega), MR_lt H m _ (by omega), skew_dI_ext, sj, tot_odd H j (by omega), neg_zero]
  · rw [MR_ge H m _ (by omega), MR_ge H m _ (by omega), skew_dI_dI]

/-- the even–odd block. -/
noncomputable def YR : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ := fun i j => GramO H m (i, 0) (j, 1)

lemma YR_tri (hm : 2 * m ≤ H) : (YR H m).BlockTriangular id := by
  intro i j hji
  have hji' : (j : ℕ) < i := hji
  have hj : (j : ℕ) < m := by have := i.isLt; omega
  have si := sl_val m i 0
  have sj := sl_val m j 1
  simp only [Fin.val_one, Fin.val_zero, add_zero] at si sj
  simp only [YR]
  rw [GramO_entry, MR_lt H m _ (by omega), MR_lt H m _ (by omega), skew_ext_ext, si, sj]
  exact skew_rows_zero H (2 * i) j (by omega) (by omega)

lemma det_YR (hm : 2 * m ≤ H) :
    det (YR H m) = (∏ i : Fin m, Dval H i) *
      (2 ^ (2 * H + 1) * ∏ i ∈ range m, ((2 * (i : ℚ) + 1) / (2 * H - 2 * i)) ^ 2) := by
  rw [det_of_upperTriangular (YR_tri H m hm), Fin.prod_univ_castSucc]
  congr 1
  · refine prod_congr rfl fun i _ => ?_
    have si := sl_val m i.castSucc 0
    have sj := sl_val m i.castSucc 1
    simp only [Fin.val_one, Fin.val_zero, add_zero, Fin.coe_castSucc] at si sj
    have hi := i.isLt
    simp only [YR]
    rw [GramO_entry, MR_lt H m _ (by omega), MR_lt H m _ (by omega), skew_ext_ext, si, sj,
      skew_rows_diag H i (by omega)]
    rfl
  · have si := sl_val m (Fin.last m) 0
    have sj := sl_val m (Fin.last m) 1
    simp only [Fin.val_one, Fin.val_zero, add_zero, Fin.val_last] at si sj
    simp only [YR]
    rw [GramO_entry, MR_lt H m _ (by omega), MR_ge H m _ (by omega), skew_ext_dI, si, tot_even H m hm]

lemma det_YR_ne (hm : 2 * m ≤ H) : det (YR H m) ≠ 0 := by
  rw [det_YR H m hm]
  refine mul_ne_zero (prod_ne_zero_iff.2 fun i _ => Dval_ne H i (by have := i.isLt; omega))
    (mul_ne_zero (by positivity) (prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ (div_ne_zero (by positivity) ?_)))
  have := mem_range.1 hi
  have : (i : ℚ) + 1 ≤ H := by exact_mod_cast (by omega : i + 1 ≤ H)
  linarith

/-- the basis matrix `R_a = Σ_q (Pa a)_q · ν t^q`, `a, q ≤ 2m`. -/
noncomputable def Bo : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℚ :=
  fun a q => (Pa (2 * H + 1) (a : ℕ)).coeff (q : ℕ)

lemma row_basis (hm : 2 * m ≤ H) (a : Fin (2 * m + 1)) (h : Fin (H + 1)) :
    row H a h = ∑ q : Fin (2 * m + 1), Bo H m a q * (nuS H h * tS H h ^ (q : ℕ)) := by
  have ha : (a : ℕ) ≤ H := by have := a.isLt; omega
  have hdeg : (Pa (2 * H + 1) (a : ℕ)).natDegree < 2 * m + 1 := by
    rw [Pa_natDegree H _ ha]; exact a.isLt
  simp only [Bo]
  rw [show ∑ q : Fin (2 * m + 1), (Pa (2 * H + 1) (a : ℕ)).coeff (q : ℕ) * (nuS H h * tS H h ^ (q : ℕ))
      = nuS H h * ∑ q : Fin (2 * m + 1), (Pa (2 * H + 1) (a : ℕ)).coeff (q : ℕ) * tS H h ^ (q : ℕ) by
    rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring]
  rw [Fin.sum_univ_eq_sum_range (fun q => (Pa (2 * H + 1) (a : ℕ)).coeff q * tS H h ^ q) (2 * m + 1),
    ← eval_eq_sum_range' hdeg, tS, Pa_eval_shell, GR.row, nuS]

lemma det_Bo (hm : 2 * m ≤ H) :
    det (Bo H m) = ∏ a : Fin (2 * m + 1), (RP (2 * H + 1) (a : ℕ)).leadingCoeff * (1 / 4) ^ (a : ℕ) := by
  rw [det_of_lowerTriangular]
  · refine prod_congr rfl fun a _ => ?_
    have ha : (a : ℕ) ≤ H := by have := a.isLt; omega
    rw [← Pa_leading H a ha, Polynomial.leadingCoeff, Pa_natDegree H a ha]
    rfl
  · intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    have hi : (i : ℕ) ≤ H := by have := i.isLt; omega
    simp only [Bo]
    apply coeff_eq_zero_of_natDegree_lt
    rw [Pa_natDegree H i hi]; exact hij'

lemma det_rows (hm : 2 * m ≤ H) (S : Finset (Fin (H + 1))) :
    det (Matrix.of fun p q : Fin (2 * m + 1) => row H p (Go S q))
      = det (Bo H m) * ((∏ q : Fin (2 * m + 1), nuS H (Go S q)) *
          ∏ i : Fin (2 * m + 1), ∏ j ∈ Ioi i, (tS H (Go S j) - tS H (Go S i))) := by
  have : (Matrix.of fun p q : Fin (2 * m + 1) => row H p (Go S q))
      = Bo H m * ((vandermonde (fun q => tS H (Go S q)))ᵀ * diagonal (fun q => nuS H (Go S q))) := by
    ext p q
    rw [of_apply, Matrix.mul_apply, row_basis H m hm]
    refine sum_congr rfl fun r _ => ?_
    rw [Matrix.mul_diagonal, transpose_apply, vandermonde_apply]
    ring
  rw [this, det_mul, det_mul, det_transpose, det_diagonal, det_vandermonde]
  ring

lemma sum_rows (hm : 2 * m ≤ H) :
    ∑ S ∈ (univ : Finset (Fin (H + 1))).powersetCard (2 * m + 1),
        det (Matrix.of fun p q : Fin (2 * m + 1) => row H p (Go S q))
      = det (Bo H m) * (sgnPairs (2 * m + 1) * VBvol (tS H) (nuS H) (2 * m + 1)) := by
  unfold VBvol sgnPairs
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun S hS => ?_
  have h : S.card = 2 * m + 1 := (mem_powersetCard.1 hS).2
  rw [det_rows H m hm S, dif_pos h]
  have hGo : ∀ q, Go S q = S.orderEmbOfFin h q := fun q => by simp [Go, h]
  simp only [hGo]
  have hneg : ∀ i : Fin (2 * m + 1), ∀ j ∈ Ioi i,
      tS H (S.orderEmbOfFin h j) - tS H (S.orderEmbOfFin h i)
        = (-1) * |tS H (S.orderEmbOfFin h j) - tS H (S.orderEmbOfFin h i)| := by
    intro i j hj
    have hij : i < j := mem_Ioi.1 hj
    have : tS H (S.orderEmbOfFin h j) < tS H (S.orderEmbOfFin h i) :=
      tS_anti H ((S.orderEmbOfFin h).strictMono hij)
    rw [abs_of_neg (sub_neg.2 this)]; ring
  rw [prod_congr rfl fun i _ => prod_congr rfl (hneg i)]
  simp only [prod_mul_distrib]
  ring

/-- **Theorem Bodd, odd `d = 2m+1`.**  `n = 2H+1`, `2m ≤ H`:
`det B · sgn · V^B_{2m+1} = ∏_{i<m} D_i · T(R_{2m})`, `T(R_{2m}) = 2ⁿ ∏_{i<m} ((2i+1)/(2H-2i))²`. -/
theorem theorem_Bodd_odd (hm : 2 * m ≤ H) :
    det (Bo H m) * (sgnPairs (2 * m + 1) * VBvol (tS H) (nuS H) (2 * m + 1))
      = (∏ i : Fin m, Dval H i) *
        (2 ^ (2 * H + 1) * ∏ i ∈ range m, ((2 * (i : ℚ) + 1) / (2 * H - 2 * i)) ^ 2) := by
  rw [← sum_rows H m hm, ← det_YR H m hm]
  have hY : IsUnit (det (YR H m)) := isUnit_iff_ne_zero.2 (det_YR_ne H m hm)
  have key := sum_minors_eq_det (MR H m) (hOO_R H m hm) hY
  simp only [MR] at key
  rw [sum_aug] at key
  exact key

end Racah
end Bali.OddB

#print axioms Bali.OddB.det_aug
#print axioms Bali.OddB.sum_aug
#print axioms Bali.OddB.theorem_Bodd_odd
