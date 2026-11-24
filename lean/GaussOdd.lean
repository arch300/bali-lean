import P699.GaussAbs

/-!
# de Bruijn's formula for the infinite binomial measure, odd `d = 2m+1` (Bali lab, 2026-11-05)

Same virtual point `∞` as in `OddB.lean` (there over `ℚ`), here over `ℝ`: append `∞` after the points
`0..N` and the extra row `δ_∞`.  The `(2m+2)`-minors containing `∞` are the `(2m+1)`-minors, the even
finite theorem `pfP_deBruijn` applies, and the border entries are the plain moments `∑ C(w,x) (-x)^a`.
-/

open Finset Matrix Filter

namespace Bali.GOdd
open Bali.PfP Bali.VB Bali.GDB Bali.GAbs GaussTarget

section Aug
variable {N : ℕ}

/-- extend by `0` at `∞ = last`. -/
noncomputable def ext (f : Fin (N + 1) → ℝ) : Fin (N + 1 + 1) → ℝ :=
  fun x => if hx : (x : ℕ) < N + 1 then f ⟨x, hx⟩ else 0
/-- the indicator of `∞`. -/
noncomputable def dI : Fin (N + 1 + 1) → ℝ := fun x => if (x : ℕ) = N + 1 then 1 else 0

@[simp] lemma ext_cs (f : Fin (N + 1) → ℝ) (k : Fin (N + 1)) : ext f k.castSucc = f k := by
  unfold ext; rw [dif_pos (show (k.castSucc : ℕ) < N + 1 from k.isLt)]; rfl
@[simp] lemma ext_last (f : Fin (N + 1) → ℝ) : ext f (Fin.last (N + 1)) = 0 := by simp [ext]
@[simp] lemma dI_cs (k : Fin (N + 1)) : (dI : Fin (N + 1 + 1) → ℝ) k.castSucc = 0 := by
  simp [dI]; omega
@[simp] lemma dI_last : (dI : Fin (N + 1 + 1) → ℝ) (Fin.last (N + 1)) = 1 := by simp [dI]

@[simp] lemma signM_cs (k l : Fin (N + 1)) :
    (signM (N + 1) : Matrix (Fin (N + 1 + 1)) (Fin (N + 1 + 1)) ℝ) k.castSucc l.castSucc
      = (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) k l := by
  simp [signM, Fin.castSucc_lt_castSucc_iff]
@[simp] lemma signM_cs_last (k : Fin (N + 1)) :
    (signM (N + 1) : Matrix (Fin (N + 1 + 1)) (Fin (N + 1 + 1)) ℝ) k.castSucc (Fin.last _) = 1 := by
  simp [signM, Fin.castSucc_lt_last]
@[simp] lemma signM_last_cs (k : Fin (N + 1)) :
    (signM (N + 1) : Matrix (Fin (N + 1 + 1)) (Fin (N + 1 + 1)) ℝ) (Fin.last _) k.castSucc = -1 := by
  simp [signM, Fin.castSucc_lt_last, not_lt.2 (Fin.castSucc_lt_last k).le]
@[simp] lemma signM_last_last :
    (signM (N + 1) : Matrix (Fin (N + 1 + 1)) (Fin (N + 1 + 1)) ℝ) (Fin.last _) (Fin.last _) = 0 := by
  simp [signM]

/-- the bilinear form of `signM (N+1)`. -/
noncomputable def Bl (u v : Fin (N + 1 + 1) → ℝ) : ℝ :=
  ∑ l, (∑ k, u k * (signM (N + 1) : Matrix (Fin (N + 1 + 1)) (Fin (N + 1 + 1)) ℝ) k l) * v l

lemma Bl_ext_ext (f g : Fin (N + 1) → ℝ) :
    Bl (ext f) (ext g) = ∑ l, (∑ k, f k * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) k l) * g l := by
  simp [Bl, Fin.sum_univ_castSucc]
lemma Bl_ext_dI (f : Fin (N + 1) → ℝ) : Bl (ext f) dI = ∑ k, f k := by
  simp [Bl, Fin.sum_univ_castSucc]
lemma Bl_dI_ext (g : Fin (N + 1) → ℝ) : Bl dI (ext g) = -∑ k, g k := by
  simp [Bl, Fin.sum_univ_castSucc]
lemma Bl_dI_dI : Bl (dI : Fin (N + 1 + 1) → ℝ) dI = 0 := by
  simp [Bl, Fin.sum_univ_castSucc]

variable {m : ℕ}

/-- the slot of a row index, `0 .. 2m+1`. -/
abbrev sl (a : Fin (m + 1) × Fin 2) : ℕ := ((eι (m + 1) a : Fin (2 * (m + 1))) : ℕ)

/-- augmented matrix: rows `r_0..r_{2m}` extended by `0`, last row `δ_∞`. -/
noncomputable def Ma (r : Fin (2 * m + 1) → Fin (N + 1) → ℝ) :
    Matrix (Fin (m + 1) × Fin 2) (Fin (N + 1 + 1)) ℝ :=
  fun a => if ha : sl a < 2 * m + 1 then ext (r ⟨sl a, ha⟩) else dI

/-- the augmented point set. -/
def aug (S : Finset (Fin (N + 1))) : Finset (Fin (N + 1 + 1)) := insert (Fin.last _) (S.map Fin.castSuccEmb)

lemma card_aug (S : Finset (Fin (N + 1))) (h : S.card = 2 * m + 1) : (aug S).card = 2 * (m + 1) := by
  rw [aug, card_insert_of_notMem (by simp [Fin.castSucc_ne_last]), card_map, h]; ring

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

/-- minor of the augmented matrix on `aug S` = minor of the rows on `S`. -/
lemma det_aug (r : Fin (2 * m + 1) → Fin (N + 1) → ℝ) (S : Finset (Fin (N + 1))) (h : S.card = 2 * m + 1) :
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
  rw [show ((-1 : ℝ) ^ (2 * m + 1 + (2 * m + 1))) = 1 by
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

/-- the augmented minor sum is the odd minor sum. -/
theorem sum_aug (r : Fin (2 * m + 1) → Fin (N + 1) → ℝ) :
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

/-! ## Odd minors are volumes -/

/-- the power rows. -/
noncomputable def rw' (w : ℝ) (m N : ℕ) : Fin (2 * m + 1) → Fin (N + 1) → ℝ :=
  fun p x => nu w N x * tt N x ^ (p : ℕ)

lemma det_odd (t ν : Fin (N + 1) → ℝ) {d : ℕ} (g : Fin d → Fin (N + 1)) :
    det (Matrix.of fun p q : Fin d => ν (g q) * t (g q) ^ (p : ℕ)) =
      (∏ q, ν (g q)) * ∏ i : Fin d, ∏ j ∈ Ioi i, (t (g j) - t (g i)) := by
  have : (Matrix.of fun p q : Fin d => ν (g q) * t (g q) ^ (p : ℕ))
      = (vandermonde (fun q => t (g q)))ᵀ * diagonal (fun q => ν (g q)) := by
    ext p q
    simp [vandermonde, Matrix.mul_diagonal, mul_comm]
  rw [this, det_mul, det_transpose, det_diagonal, det_vandermonde, mul_comm]

theorem sum_odd_minors (w : ℝ) (m N : ℕ) :
    ∑ S ∈ (univ : Finset (Fin (N + 1))).powersetCard (2 * m + 1),
        det (Matrix.of fun p q : Fin (2 * m + 1) => rw' w m N p (Go S q))
      = sgnPairs (2 * m + 1) * VBvol (tt N) (nu w N) (2 * m + 1) := by
  classical
  unfold VBvol sgnPairs
  rw [mul_sum]
  refine sum_congr rfl fun S hS => ?_
  have h : S.card = 2 * m + 1 := (mem_powersetCard.1 hS).2
  have hG : (fun q => Go (m := m) S q) = fun q => S.orderEmbOfFin h q := by
    funext q; simp [Go, h]
  rw [dif_pos h]
  simp only [rw']
  rw [show (Matrix.of fun p q : Fin (2 * m + 1) => nu w N (Go S q) * tt N (Go S q) ^ (p : ℕ))
      = Matrix.of fun p q : Fin (2 * m + 1) => nu w N (S.orderEmbOfFin h q) * tt N (S.orderEmbOfFin h q) ^ (p : ℕ) by
    ext p q; simp [Go, h]]
  rw [det_odd]
  have hneg : ∀ i : Fin (2 * m + 1), ∀ j ∈ Ioi i,
      tt N (S.orderEmbOfFin h j) - tt N (S.orderEmbOfFin h i)
        = (-1) * |tt N (S.orderEmbOfFin h j) - tt N (S.orderEmbOfFin h i)| := by
    intro i j hj
    have hij : i < j := mem_Ioi.1 hj
    have : tt N (S.orderEmbOfFin h j) < tt N (S.orderEmbOfFin h i) :=
      tt_anti N ((S.orderEmbOfFin h).strictMono hij)
    rw [abs_of_neg (sub_neg.2 this)]; ring
  rw [prod_congr rfl fun i _ => prod_congr rfl (hneg i)]
  simp only [prod_mul_distrib]
  ring

/-- The truncated volume is the partial sum over `d`-subsets of `{0..N}` (any `d`). -/
theorem VB_eq_sum (w : ℝ) (d N : ℕ) :
    VBvol (tt N) (nu w N) d = ∑ S ∈ (range (N + 1)).powersetCard d, V w d S := by
  classical
  have hmap : (univ : Finset (Fin (N + 1))).map Fin.valEmbedding = range (N + 1) := by
    ext x; simp [Fin.exists_iff]
  rw [← hmap, powersetCard_map, sum_map]
  unfold VBvol
  refine sum_congr rfl fun S hS => ?_
  have h : S.card = d := (mem_powersetCard.1 hS).2
  have hm : (S.map Fin.valEmbedding).card = d := by simpa using h
  have hg : ∀ q, ((S.map Fin.valEmbedding).orderEmbOfFin hm q) = ((S.orderEmbOfFin h q : Fin (N + 1)) : ℕ) := by
    intro q
    have hu := Finset.orderEmbOfFin_unique (s := S.map Fin.valEmbedding) hm
      (f := fun q => ((S.orderEmbOfFin h q : Fin (N + 1)) : ℕ))
      (fun q => mem_map_of_mem _ (orderEmbOfFin_mem S h q))
      (fun a b hab => (S.orderEmbOfFin h).strictMono hab)
    exact (congrFun hu q).symm
  rw [dif_pos h]
  show _ = V w d (S.map Fin.valEmbedding)
  unfold V
  rw [dif_pos hm]
  simp only [hg, tt, nu]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j hj
  have hlt : S.orderEmbOfFin h i < S.orderEmbOfFin h j := (S.orderEmbOfFin h).strictMono (mem_Ioi.mp hj)
  have : (((S.orderEmbOfFin h i : Fin (N + 1)) : ℕ) : ℝ) ≤ ((S.orderEmbOfFin h j : Fin (N + 1)) : ℕ) := by
    exact_mod_cast (Fin.lt_def.mp hlt).le
  rw [show -(((S.orderEmbOfFin h j : Fin (N + 1)) : ℕ) : ℝ) - -(((S.orderEmbOfFin h i : Fin (N + 1)) : ℕ) : ℝ) =
      -((((S.orderEmbOfFin h j : Fin (N + 1)) : ℕ) : ℝ) - ((S.orderEmbOfFin h i : Fin (N + 1)) : ℕ)) by ring,
    abs_neg, abs_of_nonneg (by linarith)]

/-! ## The limit -/

/-- the plain moment `∑ C(w,x) (-x)^e`. -/
noncomputable def mom (w : ℝ) (e : ℕ) : ℝ := ∑' x : ℕ, gchoose w x * (-(x : ℝ)) ^ e

/-- the limiting bordered skew matrix. -/
noncomputable def Ginf (w : ℝ) (m : ℕ) : Matrix (Fin (m + 1) × Fin 2) (Fin (m + 1) × Fin 2) ℝ :=
  fun a b => if sl a < 2 * m + 1 then
      (if sl b < 2 * m + 1 then skM w (sl a) (sl b) else mom w (sl a))
    else (if sl b < 2 * m + 1 then -mom w (sl b) else 0)

lemma ext_entry (w : ℝ) (m N : ℕ) (p q : Fin (2 * m + 1)) :
    ∑ l, (∑ k, rw' w m N p k * (signM N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) k l) * rw' w m N q l =
      ∑ r ∈ range (N + 1) ×ˢ range (N + 1), Fsk w p q r := by
  rw [sum_product, ← Fin.sum_univ_eq_sum_range
    (fun k : ℕ => ∑ l ∈ range (N + 1), Fsk w p q (k, l)) (N + 1)]
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun l : ℕ => Fsk w p q ((k : ℕ), l)) (N + 1)]
  refine sum_congr rfl fun l _ => ?_
  simp only [Fsk, signM, tt, nu, rw', Fin.lt_def]
  ring

lemma row_sum (w : ℝ) (m N : ℕ) (p : Fin (2 * m + 1)) :
    ∑ k, rw' w m N p k = ∑ x ∈ range (N + 1), gchoose w x * (-(x : ℝ)) ^ (p : ℕ) := by
  rw [← Fin.sum_univ_eq_sum_range (fun x : ℕ => gchoose w x * (-(x : ℝ)) ^ (p : ℕ)) (N + 1)]
  rfl

/-- **Odd de Bruijn formula for the infinite binomial measure.** -/
theorem VTrO_tendsto (w : ℝ) (m : ℕ) (hw : (2 * m : ℝ) < w) :
    Tendsto (fun N => VBvol (tt N) (nu w N) (2 * m + 1)) atTop
      (nhds (pfP (Ginf w m) /
        (pfP (J0 (m + 1) : Matrix (Fin (m + 1) × Fin 2) (Fin (m + 1) × Fin 2) ℝ) * sgnPairs (2 * m + 1)))) := by
  have hJ : pfP (J0 (m + 1) : Matrix (Fin (m + 1) × Fin 2) (Fin (m + 1) × Fin 2) ℝ) ≠ 0 := by
    rw [pfP_J0]; exact pfP_Om_ne_zero (m + 1)
  have hS : (sgnPairs (2 * m + 1) : ℝ) ≠ 0 := by
    unfold sgnPairs
    exact prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr fun _ _ => by norm_num
  have hfin : ∀ N, VBvol (tt N) (nu w N) (2 * m + 1) =
      pfP (Ma (rw' w m N) * (signM (N + 1) : Matrix (Fin (N + 1 + 1)) (Fin (N + 1 + 1)) ℝ) *
          (Ma (rw' w m N))ᵀ) /
        (pfP (J0 (m + 1) : Matrix (Fin (m + 1) × Fin 2) (Fin (m + 1) × Fin 2) ℝ) * sgnPairs (2 * m + 1)) := by
    intro N
    rw [pfP_deBruijn, sum_aug, sum_odd_minors]
    field_simp
  simp only [hfin]
  apply Tendsto.div_const
  have ltw : ∀ p : Fin (2 * m + 1), ((p : ℕ) : ℝ) < w := by
    intro p
    have h1 : (p : ℕ) ≤ 2 * m := by have := p.isLt; omega
    have h2 : ((p : ℕ) : ℝ) ≤ 2 * m := by exact_mod_cast h1
    linarith
  have hmom : ∀ p : Fin (2 * m + 1), Tendsto (fun N => ∑ k, rw' w m N p k) atTop (nhds (mom w p)) := by
    intro p
    simp only [row_sum]
    exact ((summable_pow_abs w p (ltw p)).of_norm.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hent : ∀ a b : Fin (m + 1) × Fin 2, Tendsto (fun N =>
      (Ma (rw' w m N) * (signM (N + 1) : Matrix (Fin (N + 1 + 1)) (Fin (N + 1 + 1)) ℝ) *
        (Ma (rw' w m N))ᵀ) a b) atTop (nhds (Ginf w m a b)) := by
    intro a b
    have hE : ∀ N, (Ma (rw' w m N) * (signM (N + 1) : Matrix (Fin (N + 1 + 1)) (Fin (N + 1 + 1)) ℝ) *
        (Ma (rw' w m N))ᵀ) a b = Bl (Ma (rw' w m N) a) (Ma (rw' w m N) b) := by
      intro N; simp only [Matrix.mul_apply, Matrix.transpose_apply, Bl]
    simp only [hE]
    by_cases ha : sl a < 2 * m + 1 <;> by_cases hb : sl b < 2 * m + 1
    · simp only [Ma, dif_pos ha, dif_pos hb, Bl_ext_ext, ext_entry, Ginf, if_pos ha, if_pos hb]
      exact (summable_Fsk w _ _ (ltw ⟨sl a, ha⟩) (ltw ⟨sl b, hb⟩)).hasSum.comp tendsto_squares
    · simp only [Ma, dif_pos ha, dif_neg hb, Bl_ext_dI, Ginf, if_pos ha, if_neg hb]
      exact hmom ⟨sl a, ha⟩
    · simp only [Ma, dif_neg ha, dif_pos hb, Bl_dI_ext, Ginf, if_neg ha, if_pos hb]
      exact (hmom ⟨sl b, hb⟩).neg
    · simp only [Ma, dif_neg ha, dif_neg hb, Bl_dI_dI, Ginf, if_neg ha, if_neg hb]
      exact tendsto_const_nhds
  unfold pfP
  refine tendsto_finsetSum _ fun σ _ => Tendsto.const_mul _ ?_
  exact tendsto_finsetProd _ fun i _ => hent _ _

/-- `Ginf` is skew. -/
theorem Ginf_skew (w : ℝ) (m : ℕ) (hw : (2 * m : ℝ) < w) : (Ginf w m)ᵀ = -Ginf w m := by
  have ltw : ∀ a : Fin (m + 1) × Fin 2, sl a < 2 * m + 1 → ((sl a : ℕ) : ℝ) < w := by
    intro a h
    have h2 : ((sl a : ℕ) : ℝ) ≤ 2 * m := by exact_mod_cast (show sl a ≤ 2 * m by omega)
    linarith
  ext a b
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Ginf]
  by_cases ha : sl a < 2 * m + 1 <;> by_cases hb : sl b < 2 * m + 1 <;>
    simp only [ha, hb, if_true, if_false, neg_neg, neg_zero]
  rw [skM_eq_OM w _ _ (ltw b hb) (ltw a ha), skM_eq_OM w _ _ (ltw a ha) (ltw b hb), add_comm]
  ring

end Bali.GOdd

#print axioms Bali.GOdd.sum_aug
#print axioms Bali.GOdd.VTrO_tendsto
#print axioms Bali.GOdd.Ginf_skew
