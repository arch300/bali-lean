import P699.GaussD4

/-!
# Absolute convergence of the `d`-fold sum (Bali lab, 2026-11-05)

`V w d S = ∏_{x∈S} C(w,x) ∏_{x<y∈S} (y-x)` over `d`-subsets `S ⊂ ℕ` is absolutely summable for `w > d-1`,
and for `d = 4` its sum is the product formula.
-/

open Finset Filter Real

namespace Bali.GAbs
open Bali.VB Bali.GDB Bali.GD4 GaussTarget

lemma pll {ι : Type*} (s : Finset ι) (f g : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact mul_le_mul (h1 a (mem_insert_self _ _))
      (ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi)))
      (prod_nonneg fun i hi => h0 i (mem_insert_of_mem hi))
      ((h0 a (mem_insert_self _ _)).trans (h1 a (mem_insert_self _ _)))

/-- The summand, listing the points of `S` in increasing order. -/
noncomputable def V (w : ℝ) (d : ℕ) (S : Finset ℕ) : ℝ :=
  if h : S.card = d then
    (∏ q : Fin d, gchoose w (S.orderEmbOfFin h q)) *
      ∏ i : Fin d, ∏ j ∈ Ioi i, (((S.orderEmbOfFin h j : ℕ) : ℝ) - ((S.orderEmbOfFin h i : ℕ) : ℝ))
  else 0

/-- The majorant `|C(w,x)| (x+1)^(d-1)`. -/
noncomputable def hh (w : ℝ) (d : ℕ) (x : ℕ) : ℝ := |gchoose w x| * ((x : ℝ) + 1) ^ (d - 1)

lemma hh_nonneg (w : ℝ) (d x : ℕ) : 0 ≤ hh w d x := by unfold hh; positivity

lemma summable_hh (w : ℝ) (d : ℕ) (hw : ((d : ℝ) - 1) < w) (hd : 1 ≤ d) : Summable (hh w d) := by
  have hw1 : -1 ≤ w := by have := (Nat.cast_nonneg d : (0 : ℝ) ≤ d); linarith
  obtain ⟨C, hC0, hC⟩ := gchoose_bound w hw1
  have cd : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd]; simp
  have hs : Summable (fun a : ℕ => C * ((a : ℝ) + 1) ^ (-(w + 1 - ((d : ℝ) - 1)))) := by
    apply Summable.mul_left
    have h1 : Summable (fun a : ℕ => ((a : ℝ)) ^ (-(w + 1 - ((d : ℝ) - 1)))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    simpa using (summable_nat_add_iff 1).mpr h1
  refine Summable.of_nonneg_of_le (hh_nonneg w d) (fun a => ?_) hs
  have hpos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have e1 : ((a : ℝ) + 1) ^ (d - 1) * ((a : ℝ) + 1) ^ (-(w + 1)) =
      ((a : ℝ) + 1) ^ (-(w + 1 - ((d : ℝ) - 1))) := by
    rw [← Real.rpow_natCast, cd, ← Real.rpow_add hpos]; ring_nf
  calc hh w d a ≤ (C * ((a : ℝ) + 1) ^ (-(w + 1))) * ((a : ℝ) + 1) ^ (d - 1) :=
        mul_le_mul_of_nonneg_right (hC a) (by positivity)
    _ = _ := by rw [← e1]; ring

lemma prod_orderEmb (S : Finset ℕ) (d : ℕ) (h : S.card = d) (f : ℕ → ℝ) :
    ∏ q : Fin d, f (S.orderEmbOfFin h q) = ∏ x ∈ S, f x := by
  rw [← Finset.prod_coe_sort S f]
  exact Fintype.prod_equiv (S.orderIsoOfFin h).toEquiv _ _ fun q => by simp

/-- Pointwise bound by the majorant. -/
lemma abs_V_le (w : ℝ) (d : ℕ) (S : Finset ℕ) (h : S.card = d) :
    |V w d S| ≤ ∏ x ∈ S, hh w d x := by
  set g := S.orderEmbOfFin h with hg
  have hV : V w d S = (∏ q : Fin d, gchoose w (g q)) *
      ∏ i : Fin d, ∏ j ∈ Ioi i, (((g j : ℕ) : ℝ) - ((g i : ℕ) : ℝ)) := by
    simp [V, h, hg]
  have hnn : ∀ i : Fin d, ∀ j ∈ Ioi i, 0 ≤ ((g j : ℕ) : ℝ) - ((g i : ℕ) : ℝ) := by
    intro i j hj
    have : g i < g j := g.strictMono (mem_Ioi.mp hj)
    have : ((g i : ℕ) : ℝ) ≤ ((g j : ℕ) : ℝ) := by exact_mod_cast this.le
    linarith
  have pairs : ∏ i : Fin d, ∏ j ∈ Ioi i, (((g j : ℕ) : ℝ) - ((g i : ℕ) : ℝ)) ≤
      ∏ q : Fin d, (((g q : ℕ) : ℝ) + 1) ^ (d - 1) := by
    calc ∏ i : Fin d, ∏ j ∈ Ioi i, (((g j : ℕ) : ℝ) - ((g i : ℕ) : ℝ))
        ≤ ∏ i : Fin d, ∏ j ∈ Ioi i, (((g j : ℕ) : ℝ) + 1) := by
          refine pll _ _ _ (fun i _ => prod_nonneg (hnn i)) fun i _ => ?_
          refine pll _ _ _ (hnn i) fun j _ => ?_
          have : (0 : ℝ) ≤ ((g i : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
      _ = ∏ j : Fin d, ∏ _i ∈ Iio j, (((g j : ℕ) : ℝ) + 1) := by
          apply Finset.prod_comm'
          intro i j
          simp [mem_Ioi, mem_Iio]
      _ ≤ ∏ q : Fin d, (((g q : ℕ) : ℝ) + 1) ^ (d - 1) := by
          refine pll _ _ _ (fun j _ => prod_nonneg fun _ _ => by positivity) fun j _ => ?_
          rw [prod_const]
          apply pow_le_pow_right₀
          · have : (0 : ℝ) ≤ ((g j : ℕ) : ℝ) := Nat.cast_nonneg _
            linarith
          · rw [Fin.card_Iio]; have := j.isLt; omega
  rw [hV, abs_mul, abs_of_nonneg (prod_nonneg fun i _ => prod_nonneg (hnn i)), Finset.abs_prod]
  calc (∏ q : Fin d, |gchoose w (g q)|) * ∏ i : Fin d, ∏ j ∈ Ioi i, (((g j : ℕ) : ℝ) - ((g i : ℕ) : ℝ))
      ≤ (∏ q : Fin d, |gchoose w (g q)|) * ∏ q : Fin d, (((g q : ℕ) : ℝ) + 1) ^ (d - 1) :=
        mul_le_mul_of_nonneg_left pairs (prod_nonneg fun _ _ => abs_nonneg _)
    _ = ∏ q : Fin d, hh w d (g q) := by rw [← prod_mul_distrib]; rfl
    _ = _ := prod_orderEmb S d h (hh w d)

/-- **Absolute convergence of the `d`-fold sum**, `w > d-1`. -/
theorem summable_V (w : ℝ) (d : ℕ) (hw : ((d : ℝ) - 1) < w) (hd : 1 ≤ d) :
    Summable (fun S : {S : Finset ℕ // S.card = d} => |V w d S|) := by
  have hs := summable_hh w d hw hd
  refine summable_of_sum_le (c := Real.exp (∑' x, hh w d x)) (fun _ => abs_nonneg _) fun A => ?_
  classical
  set U : Finset ℕ := A.biUnion fun S => S.1 with hU
  have sub : ∀ S ∈ A, (S : Finset ℕ) ⊆ U := fun S hS => subset_biUnion_of_mem (fun S : {S : Finset ℕ // S.card = d} => S.1) hS
  have inj : Set.InjOn (fun S : {S : Finset ℕ // S.card = d} => S.1) (A : Set _) :=
    fun a _ b _ h => Subtype.ext h
  calc ∑ S ∈ A, |V w d S|
      ≤ ∑ S ∈ A, ∏ x ∈ (S : Finset ℕ), hh w d x := sum_le_sum fun S _ => abs_V_le w d S S.2
    _ = ∑ T ∈ A.image (fun S => S.1), ∏ x ∈ T, hh w d x := (sum_image (f := fun T => ∏ x ∈ T, hh w d x) inj).symm
    _ ≤ ∑ T ∈ U.powerset, ∏ x ∈ T, hh w d x := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro T hT
          obtain ⟨S, hS, rfl⟩ := mem_image.mp hT
          exact mem_powerset.mpr (sub S hS)
        · intro T _ _
          exact prod_nonneg fun x _ => hh_nonneg w d x
    _ = ∏ x ∈ U, (1 + hh w d x) := (prod_one_add U).symm
    _ ≤ ∏ x ∈ U, Real.exp (hh w d x) := by
        refine pll _ _ _ (fun x _ => add_nonneg zero_le_one (hh_nonneg w d x)) fun x _ => ?_
        have := Real.add_one_le_exp (hh w d x); linarith
    _ = Real.exp (∑ x ∈ U, hh w d x) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' x, hh w d x) :=
        Real.exp_le_exp.mpr (hs.sum_le_tsum U fun x _ => hh_nonneg w d x)

/-- The truncated volume is the partial sum over `d`-subsets of `{0..N}`. -/
theorem VTr_eq_sum (w : ℝ) (m N : ℕ) :
    VTr w m N = ∑ S ∈ (range (N + 1)).powersetCard (2 * m), V w (2 * m) S := by
  classical
  have hmap : (univ : Finset (Fin (N + 1))).map Fin.valEmbedding = range (N + 1) := by
    ext x; simp [Fin.exists_iff]
  rw [← hmap, powersetCard_map, sum_map]
  unfold VTr VBvol
  refine sum_congr rfl fun S hS => ?_
  have h : S.card = 2 * m := (mem_powersetCard.1 hS).2
  have hm : (S.map Fin.valEmbedding).card = 2 * m := by simpa using h
  have hg : ∀ q, ((S.map Fin.valEmbedding).orderEmbOfFin hm q) = ((S.orderEmbOfFin h q : Fin (N + 1)) : ℕ) := by
    intro q
    have hu := Finset.orderEmbOfFin_unique (s := S.map Fin.valEmbedding) hm
      (f := fun q => ((S.orderEmbOfFin h q : Fin (N + 1)) : ℕ))
      (fun q => mem_map_of_mem _ (orderEmbOfFin_mem S h q))
      (fun a b hab => (S.orderEmbOfFin h).strictMono hab)
    exact (congrFun hu q).symm
  rw [dif_pos h]
  show _ = V w (2 * m) (S.map Fin.valEmbedding)
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

/-- The partial sums over `{0..N}` converge to the full sum. -/
theorem tendsto_partial (w : ℝ) (d : ℕ) (hw : ((d : ℝ) - 1) < w) (hd : 1 ≤ d) :
    Tendsto (fun N => ∑ S ∈ (range (N + 1)).powersetCard d, V w d S) atTop
      (nhds (∑' S : {S : Finset ℕ // S.card = d}, V w d S)) := by
  classical
  have hs : Summable (fun S : {S : Finset ℕ // S.card = d} => V w d S) :=
    (summable_V w d hw hd).of_abs
  let AN : ℕ → Finset {S : Finset ℕ // S.card = d} := fun N =>
    ((range (N + 1)).powersetCard d).attach.map
      ⟨fun S => ⟨S.1, (mem_powersetCard.1 S.2).2⟩, fun a b h => Subtype.ext (congrArg (fun x => x.1) h)⟩
  have hA : ∀ N, ∑ S ∈ AN N, V w d S = ∑ S ∈ (range (N + 1)).powersetCard d, V w d S := by
    intro N
    simp only [AN, sum_map, Function.Embedding.coeFn_mk]
    exact sum_attach _ (fun S => V w d S)
  have memA : ∀ N (S : {S : Finset ℕ // S.card = d}), S ∈ AN N ↔ (S : Finset ℕ) ⊆ range (N + 1) := by
    intro N S
    rw [Finset.mem_map]
    constructor
    · rintro ⟨T, -, rfl⟩
      exact (mem_powersetCard.1 T.2).1
    · intro h
      exact ⟨⟨S.1, mem_powersetCard.2 ⟨h, S.2⟩⟩, mem_attach _ _, Subtype.ext rfl⟩
  have hT : Tendsto AN atTop atTop := by
    apply tendsto_atTop_finset_of_monotone
    · intro a b hab S hS
      rw [memA] at hS ⊢
      exact hS.trans (range_mono (by omega))
    · intro S
      refine ⟨(S : Finset ℕ).sup id, ?_⟩
      rw [memA]
      intro x hx
      have : x ≤ (S : Finset ℕ).sup id := Finset.le_sup (f := id) hx
      exact mem_range.mpr (by omega)
  exact (hs.hasSum.comp hT).congr fun N => hA N

/-- **`d = 4`, in the form stated in the paper:** the absolutely convergent sum equals the product formula. -/
theorem d4_value (w : ℝ) (hw : 3 < w) (hni : ∀ n : ℕ, w ≠ n) :
    ∑' S : {S : Finset ℕ // S.card = 4}, V w 4 S =
      1 / 2 * w ^ 2 * (w - 1) * (w - 2) * B0 (w - 1) * B0 (w - 2) := by
  have h1 := tendsto_partial w 4 (by norm_num; linarith) (by norm_num)
  have h2 := d4_limit w hw hni
  simp only [VTr_eq_sum] at h2
  exact tendsto_nhds_unique h1 h2

end Bali.GAbs

#print axioms Bali.GAbs.summable_V
#print axioms Bali.GAbs.d4_value
