import Mathlib.Data.Complex.Basic
open ComplexConjugate
open Complex


theorem mul_conj_1 (z : ℂ) :
  z * conj z = (z.re^2 + z.im^2 : ℝ) := by

  apply Complex.ext
  ·
    calc
      (z * conj z).re
          = z.re * (conj z).re - z.im * (conj z).im := rfl
      _   = z.re * z.re - z.im * (-z.im) := rfl
      _   = z.re * z.re - (-(z.im * z.im)) := by rw [mul_neg z.im z.im]
      _   = z.re * z.re + z.im * z.im := sub_neg_eq_add (z.re * z.re) (z.im * z.im) ▸ rfl
      _   = z.re^2 + z.im^2 := (pow_two z.re).symm ▸ (pow_two z.im).symm ▸ rfl
      _   = ((z.re^2 + z.im^2 : ℝ) : ℂ).re := rfl
  ·
    calc
      (z * conj z).im
          = z.re * (conj z).im + z.im * (conj z).re := rfl
      _   = z.re * (-z.im) + z.im * z.re := rfl
      _   = -(z.re * z.im) + z.im * z.re := by rw [mul_neg  z.re z.im ]
      _   = -(z.re * z.im) + z.re * z.im := mul_comm z.im z.re ▸ rfl
      _   = 0 := neg_add_cancel (z.re * z.im)
      _   = ((z.re^2 + z.im^2 : ℝ) : ℂ).im := rfl



theorem add_conj_1 (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
  Complex.ext
    (show (z + conj z).re = ((2 * z.re : ℝ) : ℂ).re from
      calc (z + conj z).re
          = z.re + (conj z).re := rfl
        _ = z.re + z.re := rfl
        _ = 2 * z.re := (two_mul z.re).symm
        _ = ((2 * z.re : ℝ) : ℂ).re := rfl)

    (show (z + conj z).im = ((2 * z.re : ℝ) : ℂ).im from
      calc (z + conj z).im
          = z.im + (conj z).im := rfl
        _ = z.im + (-z.im) := rfl
        _ = z.im - z.im := (sub_eq_add_neg z.im z.im).symm
        _ = 0 := sub_self z.im
        _ = ((2 * z.re : ℝ) : ℂ).im := rfl)



theorem sub_conj_1 (z : ℂ) : z - conj z = (2 * z.im : ℝ) * I :=
  Complex.ext
    (show (z - conj z).re = ((2 * z.im : ℝ) * I).re from
      calc (z - conj z).re
          = z.re - (conj z).re := rfl
        _ = z.re - z.re := rfl
        _ = 0 := sub_self z.re
        _ = (2 * z.im) * 0 - 0 * 1 := by rw [mul_zero, zero_mul, sub_zero]
        _ = (2 * z.im) * I.re - 0 * I.im := by rw [Complex.I_re, Complex.I_im]
        _ = ((2 * z.im : ℝ) * I).re := rfl)
    (show (z - conj z).im = ((2 * z.im : ℝ) * I).im from
      calc (z - conj z).im
          = z.im - (conj z).im := rfl
        _ = z.im - (-z.im) := rfl
        _ = z.im + z.im := sub_neg_eq_add z.im z.im
        _ = 2 * z.im := (two_mul z.im).symm
        _ = (2 * z.im) * 1 + 0 * 0 := by rw [mul_one, mul_zero, add_zero]
        _ = (2 * z.im) * I.im + 0 * I.re := by rw [Complex.I_re, Complex.I_im]
        _ = ((2 * z.im : ℝ) * I).im := rfl)




------------------------------------------------------------------------------------------------
--  ***** Preuve 1    z x conj (z) = z.re^2 + z.im^2
--- **** version 1
-------------------------------------------------------------------------------------------------
theorem mul_conj_calc (z : ℂ) :
  z * conj z = (z.re^2 + z.im^2 : ℝ) := by
  -- On prouve l'égalité complexe par parties réelle et imaginaire
  apply Complex.ext
  · -- Partie réelle
    calc
      (z * conj z).re
          = z.re * (conj z).re - z.im * (conj z).im := rfl
      _   = z.re * z.re - z.im * (-z.im) := rfl
      _   = z.re * z.re + z.im * z.im := by simp
      _   = z.re^2 + z.im^2 := by simp [sq]
      _   = ((z.re^2 + z.im^2 : ℝ) : ℂ).re := rfl
  · -- Partie imaginaire
    calc
      (z * conj z).im
          = z.re * (conj z).im + z.im * (conj z).re := rfl
      _   = z.re * (-z.im) + z.im * z.re := rfl
      _   = -(z.re * z.im) + z.re * z.im := by simp [mul_neg, mul_comm]
      _   = 0 := by simp
      _   = ((z.re^2 + z.im^2 : ℝ) : ℂ).im := rfl
------------------------------------------------------------------------------------------------


------------------------------------------------------------------------------------------------
--  ***** utilisation de la fonction mul_conj_calc1 dans une autre preuve
---
------------------------------------------------------------------------------------------------
theorem four_mul_conj_detailed (z : ℂ) :
  4 * (z * conj z) = (4 * z.re^2 + 4 * z.im^2 : ℝ) := by
  calc
    4 * (z * conj z)
        = 4 * (z.re^2 + z.im^2 : ℝ) := by rw [mul_conj_1] --  PREUVE HROUZ mul_conj_calc1
    _   = (4 : ℂ) * ((z.re^2 + z.im^2 : ℝ) : ℂ) := rfl
    _   = ((4 : ℝ) : ℂ) * ((z.re^2 + z.im^2 : ℝ) : ℂ) := rfl
    _   = ((4 * (z.re^2 + z.im^2) : ℝ) : ℂ) := by rw [← Complex.ofReal_mul]
    _   = ((4 * z.re^2 + 4 * z.im^2 : ℝ) : ℂ) := by rw [mul_add]
    _   = (4 * z.re^2 + 4 * z.im^2 : ℝ) := rfl

------------------------------------------------------------------------------------------------
--  ***** Preuve 2    z - conj (z) =  2 * z.im * I
--- **** version 1
------------------------------------------------------------------------------------------------
theorem sub_conj_atomique (z : ℂ) : z - conj z = (2 * z.im : ℝ) * I := by
  calc
    z - conj z
        = ⟨z.re - (conj z).re, z.im - (conj z).im⟩ := rfl
    _   = ⟨z.re - z.re, z.im - (-z.im)⟩ := rfl
    _   = ⟨z.re - z.re, z.im - -z.im⟩ := rfl
    _   = ⟨0, z.im + z.im⟩ := by simp
    _   = ⟨0, 2 * z.im⟩ := by rw [two_mul]
    _   = (2 * z.im : ℝ)* I := Complex.ext_iff.2 <| by simp

------------------------------------------------------------------------------------------------
--  ***** Preuve 4    -1 complexe est un - 1 reel
--- **** version 1  sans tactiques
------------------------------------------------------------------------------------------------

theorem minus_one_complex_eq_real_cast : (-1 : ℂ) = ((-1 : ℝ) : ℂ) := by
  rw [Complex.ofReal_neg]
  rw [Complex.ofReal_one]

theorem three_mul_two_re (z : ℂ) :
  (3 : ℂ) * ((2 * z.re : ℝ) : ℂ)
    = ((6 * z.re : ℝ) : ℂ) :=

calc
  (3 : ℂ) * ((2 * z.re : ℝ) : ℂ)
      = ((3 : ℝ) : ℂ) * ((2 * z.re : ℝ) : ℂ) := rfl

  _   = ((3 * (2 * z.re) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul]

  _   = (((3 * 2) * z.re : ℝ) : ℂ) := by
          rw [mul_assoc]

  _   = ((6 * z.re : ℝ) : ℂ) := by
          norm_num


theorem three_mul_two_re1 (a : ℝ ) (z : ℂ) :
  (a : ℝ) * ((2 * z.re : ℝ) : ℂ)
    = ((a * 2 * z.re : ℝ) : ℂ) :=

calc
  (a : ℂ) * ((2 * z.re : ℝ) : ℂ)
      = ((a : ℝ) : ℂ) * ((2 * z.re : ℝ) : ℂ) := rfl

  _   = ((a * (2 * z.re) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul]

  _   = (((a * 2) * z.re : ℝ) : ℂ) := by
          rw [mul_assoc]

  _   = ((a * 2 * z.re : ℝ) : ℂ) := by
          norm_num



theorem three_mul_two_re2 (z : ℂ) :
  (a : ℝ) * ((2 * z.re : ℝ) : ℂ)
    = (((2 * a) * z.re : ℝ) : ℂ) :=
calc
  (a : ℝ) * ((2 * z.re : ℝ) : ℂ)
      = ((a : ℝ) : ℂ) * ((2 * z.re : ℝ) : ℂ) := rfl

  _   = ((a * (2 * z.re) : ℝ) : ℂ) :=
        (Complex.ofReal_mul a (2 * z.re)).symm

  _   = (((a * 2) * z.re : ℝ) : ℂ) := by rw [mul_assoc]

  _   = (((2 * a) * z.re : ℝ) : ℂ) := by
          rw [show a * 2 = 2 * a from mul_comm a 2]

  _   = ((2 * a * z.re : ℝ) : ℂ) := rfl
