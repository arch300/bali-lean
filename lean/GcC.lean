import P699.ProductC
import P699.PfaffianPerm

/-!
# The Pfaffian over `ℂ`, normalized, as a function of polynomial growth (Bali lab, 2026-11-05)

Every entry is the closed form of the real moments of `GaussTarget`, divided by `4^z`
(by `2^z` on the border, for odd `d`).
-/

open Complex Finset

namespace Bali.GC
open Bali.PC Bali.PfP

/-- `H(z-k,z-k,s) / 4^z` for an integer `s`. -/
noncomputable def Hc (k : ℕ) (s : ℤ) (z : ℂ) : ℂ :=
  if 1 ≤ s then hP k (s - 1).toNat z else hN k (-s).toNat z

theorem Hc_poly (t : ℝ) (k : ℕ) (s : ℤ) (hk : (k : ℝ) ≤ t) : PolyH t (Hc k s) := by
  unfold Hc
  by_cases h : 1 ≤ s
  · simpa [h] using hP_poly t k _ hk
  · simpa [h] using hN_poly t k _ hk

/-- Falling factorial over `ℂ`. -/
noncomputable def ffc (j : ℕ) (z : ℂ) : ℂ := ∏ i ∈ range j, (z - i)

theorem ffc_poly (t : ℝ) (j : ℕ) : PolyH t (ffc j) :=
  PolyH.prod _ fun _ _ => PolyH.sub_const _ _

/-- `FM z j l / 4^z`, the closed form of `FM_value_le` and `FM_value_ge`. -/
noncomputable def FMc (j l : ℕ) (z : ℂ) : ℂ :=
  ffc j z * ffc l z *
    (if j ≤ l then
      ∑ i ∈ range (l - j + 1), ((l - j).choose i : ℂ) * Hc l (1 - ((l - j : ℕ) : ℤ) + i) z
    else
      ((2 : ℂ) ^ (j + l))⁻¹ -
        ∑ i ∈ range (j - l + 1), ((j - l).choose i : ℂ) * Hc j (-((j - l : ℕ) : ℤ) + i) z)

theorem FMc_poly (t : ℝ) (j l : ℕ) (hj : (j : ℝ) ≤ t) (hl : (l : ℝ) ≤ t) : PolyH t (FMc j l) := by
  have hsum : ∀ (n k : ℕ) (hk : (k : ℝ) ≤ t) (g : ℕ → ℤ),
      PolyH t (fun z => ∑ i ∈ range (n + 1), (n.choose i : ℂ) * Hc k (g i) z) := fun n k hk g =>
    PolyH.finset_sum _ fun i _ => (PolyH.const t _).mul (Hc_poly t k _ hk)
  have base := (ffc_poly t j).mul (ffc_poly t l)
  unfold FMc
  by_cases h : j ≤ l
  · simp only [h, if_true]
    exact base.mul (hsum _ _ hl _)
  · simp only [h, if_false]
    have := (PolyH.const t ((2 : ℂ) ^ (j + l))⁻¹).add (hsum (j - l) j hj fun i => -((j - l : ℕ) : ℤ) + i).neg_one_mul
    refine base.mul ?_
    simpa only [sub_eq_add_neg] using this

/-- `OM z a b / 4^z`. -/
noncomputable def OMc (a b : ℕ) (z : ℂ) : ℂ :=
  ∑ p ∈ range (a + 1) ×ˢ range (b + 1),
    (a.stirlingSecond p.1 : ℂ) * (b.stirlingSecond p.2 : ℂ) * FMc p.1 p.2 z

theorem OMc_poly (t : ℝ) (a b : ℕ) (ha : (a : ℝ) ≤ t) (hb : (b : ℝ) ≤ t) : PolyH t (OMc a b) := by
  refine PolyH.finset_sum _ ?_
  rintro ⟨j, l⟩ hp
  rw [mem_product, mem_range, mem_range] at hp
  have hj : (j : ℝ) ≤ a := by exact_mod_cast (by omega : j ≤ a)
  have hl : (l : ℝ) ≤ b := by exact_mod_cast (by omega : l ≤ b)
  exact (PolyH.const t _).mul (FMc_poly t j l (hj.trans ha) (hl.trans hb))

/-- The skew moment `skM z e f / 4^z`. -/
noncomputable def skc (e f : ℕ) (z : ℂ) : ℂ := (-1 : ℂ) ^ (e + f) * (OMc e f z - OMc f e z)

theorem skc_poly (t : ℝ) (e f : ℕ) (he : (e : ℝ) ≤ t) (hf : (f : ℝ) ≤ t) : PolyH t (skc e f) := by
  have := (PolyH.const t ((-1 : ℂ) ^ (e + f))).mul
    ((OMc_poly t e f he hf).add (OMc_poly t f e hf he).neg_one_mul)
  have e' : skc e f = fun z => (-1 : ℂ) ^ (e + f) * (OMc e f z + -OMc f e z) := by
    funext z; simp only [skc, sub_eq_add_neg]
  rw [e']; exact this

/-- Pfaffian of a matrix of `PolyH` entries is `PolyH`. -/
theorem pfP_poly {t : ℝ} {m : ℕ} (A : Fin m × Fin 2 → Fin m × Fin 2 → ℂ → ℂ)
    (hA : ∀ a b, PolyH t (A a b)) :
    PolyH t (fun z => pfP (fun a b => A a b z)) := by
  unfold pfP
  exact PolyH.finset_sum _ fun σ _ => (PolyH.const t _).mul (PolyH.prod _ fun i _ => hA _ _)

/-- The normalized Pfaffian for `d = 2m`. -/
noncomputable def Gc (m : ℕ) (z : ℂ) : ℂ :=
  pfP (fun a b : Fin m × Fin 2 => skc (eι m a : ℕ) (eι m b : ℕ) z)

theorem Gc_poly (m : ℕ) : PolyH ((2 * m : ℝ) - 1) (Gc m) := by
  have lt : ∀ c : Fin m × Fin 2, (((eι m c : Fin (2 * m)) : ℕ) : ℝ) ≤ (2 * m : ℝ) - 1 := by
    intro c
    have h1 : ((eι m c : Fin (2 * m)) : ℕ) + 1 ≤ 2 * m := (eι m c).isLt
    have h2 : (((eι m c : Fin (2 * m)) : ℕ) : ℝ) + 1 ≤ 2 * m := by exact_mod_cast h1
    linarith
  exact pfP_poly _ fun a b => skc_poly _ _ _ (lt a) (lt b)

/-- The difference with the product side is the function Carlson's theorem is applied to. -/
theorem diff_poly (m : ℕ) (κ : ℂ) :
    PolyH ((2 * m : ℝ) - 1) (fun z => Gc m z - Pc κ (2 * m) z) := by
  have := (Gc_poly m).add (by
    have h := (Pc_poly κ (2 * m)).neg_one_mul
    push_cast at h
    exact h)
  simpa only [sub_eq_add_neg] using this

end Bali.GC

#print axioms Bali.GC.pfP_poly
#print axioms Bali.GC.Gc_poly
#print axioms Bali.GC.diff_poly
