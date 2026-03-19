
import Std
namespace FormalPass

-- ============================================================
-- SafePassword
-- ============================================================

structure SafePassword where
  value          : String
  is_long_enough : value.length ≥ 8

def checkPassword (s : String) : Option SafePassword :=
  if h : s.length ≥ 8 then some ⟨s, h⟩ else none

theorem password_never_too_short (p : SafePassword) :
    p.value.length ≥ 8 := p.is_long_enough

instance : ToString SafePassword where
  toString p := p.value


-- ============================================================
-- Bool (calculables)
-- ============================================================

def hasDigitBool (s : String) : Bool :=
  s.toList.any Char.isDigit

def hasUpperBool (s : String) : Bool :=
  s.toList.any Char.isUpper

def hasSpecialBool (s : String) : Bool :=
  s.toList.any (fun c => !(c.isAlphanum))


-- ============================================================
-- Prop (mathématiques)
-- ============================================================

def HasDigit (s : String) : Prop :=
  ∃ c ∈ s.toList, c.isDigit = true

def HasUpper (s : String) : Prop :=
  ∃ c ∈ s.toList, c.isUpper = true

def HasSpecial (s : String) : Prop :=
  ∃ c ∈ s.toList, c.isAlphanum = false


-- ============================================================
-- Lemmata Bool → Prop
-- ============================================================

lemma hasDigit_of_bool (s : String)
    (h : hasDigitBool s = true) : HasDigit s := by
  unfold HasDigit hasDigitBool at *
  rw [List.any_eq_true] at h
  obtain ⟨c, hc, hd⟩ := h
  exact ⟨c, hc, hd⟩

lemma hasUpper_of_bool (s : String)
    (h : hasUpperBool s = true) : HasUpper s := by
  unfold HasUpper hasUpperBool at *
  rw [List.any_eq_true] at h
  obtain ⟨c, hc, hu⟩ := h
  exact ⟨c, hc, hu⟩

lemma hasSpecial_of_bool (s : String)
    (h : hasSpecialBool s = true) : HasSpecial s := by
  unfold HasSpecial hasSpecialBool at *
  rw [List.any_eq_true] at h
  obtain ⟨c, hc, hs⟩ := h
  simp at hs
  exact ⟨c, hc, hs⟩


-- ============================================================
-- StrongPassword
-- ============================================================

structure StrongPassword where
  value            : String
  is_long_enough   : value.length ≥ 8
  contains_digit   : HasDigit value
  contains_upper   : HasUpper value
  contains_special : HasSpecial value

instance : ToString StrongPassword where
  toString p := p.value


-- ============================================================
-- Smart constructor
-- ============================================================

def checkStrongPassword (s : String) : Option StrongPassword :=
  if hLen : s.length ≥ 8 then
    if hd : hasDigitBool s = true then
      if hu : hasUpperBool s = true then
        if hs : hasSpecialBool s = true then
          some ⟨s,
            hLen,
            hasDigit_of_bool   s hd,
            hasUpper_of_bool   s hu,
            hasSpecial_of_bool s hs⟩
        else none
      else none
    else none
  else none


-- ============================================================
-- Théorèmes
-- ============================================================

theorem strong_implies_safe (p : StrongPassword) :
    p.value.length ≥ 8 :=
  p.is_long_enough

theorem strong_has_digit (p : StrongPassword) :
    HasDigit p.value :=
  p.contains_digit

theorem checkStrong_sound (s : String) (p : StrongPassword)
    (h : checkStrongPassword s = some p) :
    HasDigit p.value ∧ HasUpper p.value ∧ HasSpecial p.value :=
  ⟨p.contains_digit, p.contains_upper, p.contains_special⟩


-- ============================================================
-- Tests
-- ============================================================

#eval checkPassword "password123"
#eval checkPassword "123"
#eval checkStrongPassword "Abc!1234"
#eval checkStrongPassword "abc123"
#eval checkStrongPassword "abc!1234"

end FormalPass


-- Quand rw échoue mystérieusement,
-- utilise check_defeq_abuse pour diagnostiquer :

--import Mathlib.Tactic.CheckDefEqAbuse

--example ... := by
  -- check_defeq_abuse rw [mon_lemme]
  -- Si output = "defeq abuse detected"
  -- → problème d'instances, pas de logique
  -- → solution : set_option ou paramètres explicites
