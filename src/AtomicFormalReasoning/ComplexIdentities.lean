import Mathlib.Data.Complex.Basic
open ComplexConjugate
open Complex
-----------------------------------------------------------------------------------------------
--  ***** Preuve 1    z x conj (z) = z.re^2 + z.im^2
--- **** version 1 sans tactiques
-------------------------------------------------------------------------------------------------
theorem mul_conj_z (z : ℂ) :
  z * conj z = ( z.re^2 + z.im^2 : ℝ) := by

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


-----------------------------------------------------------------------------------------------
--  ***** Preuve 2   (z : ℂ) : z + conj z = (2 * z.re : ℝ)
--- **** version 1 sans tactiques
-------------------------------------------------------------------------------------------------
theorem add_conj_z (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
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


-----------------------------------------------------------------------------------------------
--  ***** Preuve 3   z - conj z = (2 * z.im : ℝ) * I
--- **** version 1 sans tactiques
-------------------------------------------------------------------------------------------------
theorem sub_conj_z (z : ℂ) : z - conj z = (2 * z.im : ℝ) * I :=
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
-----------------------------------------------------------------------------------------------
--  ***** Preuve 4  (-1 : ℂ) = ((-1 : ℝ) : ℂ)
-- version 1 sans tactiques
-------------------------------------------------------------------------------------------------


theorem minus_one_complex_eq_real_cast : (-1 : ℂ) = ((-1 : ℝ) : ℂ) := by
  rw [Complex.ofReal_neg]
  rw [Complex.ofReal_one]

-----------------------------------------------------------------------------------------------
--  ***** Preuve 5  (a : ℝ) (z : ℂ) :(a : ℝ) * ((2 * z.re : ℝ) : ℂ)= (((2 * a) * z.re : ℝ) : ℂ)
--- **** version 1 sans tactiques
-------------------------------------------------------------------------------------------------
theorem a_mul_two_re2 (a : ℝ) (z : ℂ) :
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

theorem brouillon1 (z : ℂ) :
 (6: ℝ) * ((2 * z.re : ℝ) : ℂ)
    = (( 12 * z.re : ℝ) : ℂ) :=
calc
  (6: ℝ) * ((2 * z.re : ℝ) : ℂ)
  = (((2 * 6) * z.re : ℝ) : ℂ) := a_mul_two_re2 (6 : ℝ) (z.re: ℂ)
_ = ((12 * z.re : ℝ) : ℂ) := by norm_num

-----------------------------------------------------------------------------------------------
--  ***** Preuve 1   z - w = ⟨z.re - w.re, z.im - w.im⟩
--- **** version 1 sans tactiques
-------------------------------------------------------------------------------------------------

theorem sub_complex (z w : ℂ) :
  z - w = ⟨z.re - w.re, z.im - w.im⟩ :=
Complex.ext
  -- Partie réelle
  (show (z - w).re = (⟨z.re - w.re, z.im - w.im⟩ : ℂ).re from
    calc (z - w).re
        -- Soustraction définie comme addition de l'opposé
        = (z + (-w)).re := rfl

        -- Partie réelle d'une somme
    _   = z.re + (-w).re := rfl

        -- Partie réelle de l'opposé
    _   = z.re + (-w.re) := rfl

        -- Définition de la soustraction réelle
    _   = z.re - w.re := (sub_eq_add_neg z.re w.re).symm

        -- Partie réelle du résultat
    _   = (⟨z.re - w.re, z.im - w.im⟩ : ℂ).re := rfl)

  -- Partie imaginaire
  (show (z - w).im = (⟨z.re - w.re, z.im - w.im⟩ : ℂ).im from
    calc (z - w).im
        -- Soustraction définie comme addition de l'opposé
        = (z + (-w)).im := rfl

        -- Partie imaginaire d'une somme
    _   = z.im + (-w).im := rfl

        -- Partie imaginaire de l'opposé
    _   = z.im + (-w.im) := rfl

        -- Définition de la soustraction réelle
    _   = z.im - w.im := (sub_eq_add_neg z.im w.im).symm

        -- Partie imaginaire du résultat
    _   = (⟨z.re - w.re, z.im - w.im⟩ : ℂ).im := rfl)

-----------------------------------------------------------------------------------------------
--  ***** Preuve 1  z * w = ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
--- **** version 1 sans tactiques
-------------------------------------------------------------------------------------------------
theorem mul_complex (z w : ℂ) :
  z * w = ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩ :=

  Complex.ext
    (show (z * w).re = (⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩ : ℂ).re from
      calc (z * w).re
          -- Formule de la partie réelle du produit
          = z.re * w.re - z.im * w.im := rfl

          -- Partie réelle du résultat
      _   = (⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩ : ℂ).re := rfl)

    (show (z * w).im = (⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩ : ℂ).im from
      calc (z * w).im
          -- Formule de la partie imaginaire du produit
          = z.re * w.im + z.im * w.re := rfl

          -- Partie imaginaire du résultat
      _   = (⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩ : ℂ).im := rfl)

-----------------------------------------------------------------------------------------------
--  ***** Preuve 1  z + w = ⟨z.re + w.re, z.im + w.im⟩
--- **** version 1 sans tactiques
-------------------------------------------------------------------------------------------------
theorem add_complex (z w : ℂ) :
  z + w = ⟨z.re + w.re, z.im + w.im⟩ :=

  Complex.ext
    (show (z + w).re = (⟨z.re + w.re, z.im + w.im⟩ : ℂ).re from
      calc (z + w).re
          -- Formule de la partie réelle de la somme
          = z.re + w.re := rfl

          -- Partie réelle du résultat
      _   = (⟨z.re + w.re, z.im + w.im⟩ : ℂ).re := rfl)

    (show (z + w).im = (⟨z.re + w.re, z.im + w.im⟩ : ℂ).im from
      calc (z + w).im
          -- Formule de la partie imaginaire de la somme
          = z.im + w.im := rfl

          -- Partie imaginaire du résultat
      _   = (⟨z.re + w.re, z.im + w.im⟩ : ℂ).im := rfl)

-----------------------------------------------------------------------------------------------
--  ***** Preuve : z / w = ⟨(z.re * w.re + z.im * w.im) / (w.re^2 + w.im^2),
--                          (z.im * w.re - z.re * w.im) / (w.re^2 + w.im^2)⟩
--- **** version 1 sans tactiques (Style Atomique)
-------------------------------------------------------------------------------------------------



lemma conj_ne_zero (w : ℂ) (hw : w ≠ 0) : conj w ≠ 0 :=
  (map_ne_zero (starRingEnd ℂ)).mpr hw

lemma div_mul_conj (z w : ℂ) (hw : w ≠ 0) : z / w = z * conj w / (w * conj w) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, ← mul_assoc, mul_assoc z]
  conv_rhs => rw [mul_inv_cancel₀ (conj_ne_zero w hw)]
  rw [mul_one]


theorem div_complex (z w : ℂ) (hw : w ≠ 0) :
  z / w = ⟨(z.re * w.re + z.im * w.im) / (w.re^2 + w.im^2),
           (z.im * w.re - z.re * w.im) / (w.re^2 + w.im^2)⟩ :=

  have h1 : w * conj w= (w.re^2 + w.im^2 : ℝ) := by rw [mul_conj_z]
  Complex.ext
 -- PARTIE RÉELLE
    (show (z / w).re = (⟨(z.re * w.re + z.im * w.im) / (w.re^2 + w.im^2), (z.im * w.re - z.re * w.im) / (w.re^2 + w.im^2)⟩ : ℂ).re from
    calc (z / w).re
  = (z * conj w / (w * conj w)).re := by rw [div_mul_conj z w hw]

  _ = (z * conj w / (w.re^2 + w.im^2 : ℝ)).re := by rw [h1]

  _ = ((⟨z.re * (conj w).re - z.im * (conj w).im, z.re * (conj w).im + z.im * (conj w).re⟩ : ℂ) / (w.re^2 + w.im^2 : ℝ)).re := by
      rw [mul_complex z (conj w)]

  _ = (z.re * (conj w).re - z.im * (conj w).im) / (w.re^2 + w.im^2) := by rw [Complex.div_ofReal_re]

  _ = (z.re * w.re - z.im * (-w.im)) / (w.re^2 + w.im^2) := by rw [Complex.conj_re, Complex.conj_im]
  _ = (z.re * w.re + z.im * w.im) / (w.re^2 + w.im^2) := by
      rw [mul_neg, sub_neg_eq_add]
    )

    -- PARTIE IMAGINAIRE
  (show (z / w).im = (⟨(z.re * w.re + z.im * w.im) / (w.re^2 + w.im^2), (z.im * w.re - z.re * w.im) / (w.re^2 + w.im^2)⟩ : ℂ).im from
  calc (z / w).im
  = (z * conj w / (w * conj w)).im := by rw [div_mul_conj z w hw]
  _ = (z * conj w / (w.re^2 + w.im^2 : ℝ)).im := by rw [h1]
  _ = ((⟨z.re * (conj w).re - z.im * (conj w).im, z.re * (conj w).im + z.im * (conj w).re⟩ : ℂ) / (w.re^2 + w.im^2 : ℝ)).im := by
      rw [mul_complex z (conj w)]
  _ = (z.re * (conj w).im + z.im * (conj w).re) / (w.re^2 + w.im^2) := Complex.div_ofReal_im _ _
  _ = (z.re * (-w.im) + z.im * w.re) / (w.re^2 + w.im^2) := by rw [Complex.conj_re, Complex.conj_im]
  _ = (-(z.re * w.im) + z.im * w.re) / (w.re^2 + w.im^2) := by rw [mul_neg]
  _ = (z.im * w.re - z.re * w.im) / (w.re^2 + w.im^2) := by rw [add_comm, sub_eq_add_neg])
