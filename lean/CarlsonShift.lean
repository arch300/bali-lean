import P699.Carlson
import P699.ProductC

/-!
# Carlson on a shifted half-plane (Bali lab, 2026-11-05)
-/

open Complex

namespace Bali.CS
open Bali.PC

/-- If `f` is `PolyH` on `Re z > s` (`s : ℕ`) and vanishes at every integer `n > s`, then `f = 0` there. -/
theorem carlson_shift {f : ℂ → ℂ} (s : ℕ) (hf : PolyH (s : ℝ) f)
    (hzero : ∀ n : ℕ, s < n → f n = 0) : ∀ z : ℂ, (s : ℝ) < z.re → f z = 0 := by
  obtain ⟨hd, A, K, hA, hb⟩ := hf
  set g : ℂ → ℂ := fun w => f (w + s) with hg
  have hre : ∀ w : ℂ, 0 < w.re → (s : ℝ) < (w + s).re := fun w hw => by
    simp only [add_re, natCast_re]; linarith
  have hgd : DifferentiableOn ℂ g {z : ℂ | 0 < z.re} := by
    intro w hw
    have hopen : IsOpen {z : ℂ | (s : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h1 : DifferentiableAt ℂ f (w + s) := (hd _ (hre w hw)).differentiableAt (hopen.mem_nhds (hre w hw))
    have h2 : DifferentiableAt ℂ (fun w : ℂ => w + (s : ℂ)) w := by fun_prop
    exact (DifferentiableAt.comp w h1 h2).differentiableWithinAt
  have hgb : ∀ w : ℂ, 0 < w.re → ‖g w‖ ≤ (A * (1 + (s : ℝ)) ^ K) * (1 + ‖w‖) ^ K := by
    intro w hw
    have h := hb _ (hre w hw)
    have hn : 1 + ‖w + (s : ℂ)‖ ≤ (1 + (s : ℝ)) * (1 + ‖w‖) := by
      have : ‖w + (s : ℂ)‖ ≤ ‖w‖ + s := by
        simpa using norm_add_le w (s : ℂ)
      nlinarith [norm_nonneg w, (Nat.cast_nonneg s : (0 : ℝ) ≤ s), mul_nonneg (norm_nonneg w) (Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
    calc ‖g w‖ ≤ A * (1 + ‖w + (s : ℂ)‖) ^ K := h
      _ ≤ A * ((1 + (s : ℝ)) * (1 + ‖w‖)) ^ K :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hn K) hA
      _ = _ := by rw [mul_pow]; ring
  have hg0 : ∀ n : ℕ, 0 < n → g n = 0 := by
    intro n hn
    have := hzero (n + s) (by omega)
    simpa [hg] using this
  have key := Bali.Carlson.carlson hgd (by positivity) hgb hg0
  intro z hz
  have := key (z - s) (by simp only [sub_re, natCast_re]; linarith)
  simpa [hg] using this

end Bali.CS

#print axioms Bali.CS.carlson_shift
