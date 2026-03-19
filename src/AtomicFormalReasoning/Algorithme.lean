import Mathlib.Data.Complex.Basic
import Init.Data.List.Basic
open List

------------------------------------------------------------------------------------------
------------- fonction paire -------------------------------------------------------------
def estPair (n : Nat) : Bool :=
  n % 2 == 0
------------------------------------------------------------------------------------------
------------- fonction impaire -----------------------------------------------------------
def estimpair (n : Nat) : Bool :=
  n % 2 == 1

#eval estimpair 9 -- affiche true
#eval estPair 4   -- devrait donner true
#eval estPair 7   -- devrait donner false

------------------------------------------------------------------------------------------
------------- fonction double -----------------------------------------------------------
def double (n : Nat) : Nat := n * 2

-- Étape 1 : Avec simp (automatique)
theorem double_zero_auto : double 0 = 0 := by
  unfold double
  simp

-- Étape 2 : Encore plus manuelle
theorem double_zero_super_manual : double 0 = 0 := by
  unfold double
  have h : 0 * 2 = 0 := by exact Nat.zero_mul 2
  rw [h]

-- Théorème : le double est toujours pair
theorem double_estPair (n : Nat) : estPair (double n) = true := by
  unfold double estPair
  -- Étape 1 : (n * 2) % 2 = (n % 2 * 2 % 2) % 2
  --C'est le lemme de la distributivité du modulo sur la multiplication.
  --Mathématiquement, il dit :(a x b) mod c = ( (a mod c) x (b mod c) ) mod c
  rw [Nat.mul_mod]
  -- Étape 2 : 2 % 2 = 0
  rw [Nat.mod_self 2]
  -- Étape 3 : n % 2 * 0 = 0
  rw [Nat.mul_zero]
  -- Étape 4 : 0 % 2 = 0
  rw [Nat.zero_mod]
  -- Conclusion
  rfl



-- 1. Créons deux paires à comparer
def p1 : ℕ × ℤ := (1, 5)
def p2 : ℕ × ℤ := (2, 3)
def p3 : ℕ × ℤ := (1, 10)

-- Sans avoir à réécrire la logique à chaque fois
def comparerPaires (p1 p2 : ℕ × ℤ) : Ordering :=
  (lexOrd : Ord (ℕ × ℤ)).compare p1 p2
#check lexOrd

#eval comparerPaires p1 p2
-- 2. Testons la comparaison
#eval (lexOrd : Ord (ℕ × ℤ)).compare p1 p2  -- Résultat : Ordering.lt (car 1 < 2)
#eval (lexOrd : Ord (ℕ × ℤ)).compare p2 p1  -- Résultat : Ordering.gt
#eval (lexOrd : Ord (ℕ × ℤ)).compare p1 p3  -- Résultat : Ordering.lt (1=1, 5<10)
#eval (lexOrd : Ord (ℕ × ℤ)).compare p1 p1  -- Résultat : Ordering.eq




theorem reverse_reverse : ∀ (l : List α), reverse (reverse l) = l
  | []     => rfl
  | a :: l => calc
    reverse (reverse (a :: l))
      = reverse (reverse l ++ [a]) := by rw [reverse_cons]
    _ = reverse [a] ++ reverse (reverse l) := reverse_append
    _ = reverse [a] ++ l := by rw [reverse_reverse l]
    _ = a :: l := rfl





-- Théorème simple : 0 est pair
theorem zero_estPair : estPair 0 = true := by
  unfold estPair
  simp


def fact : Nat → Nat
| 0     => 1
| n+1   => (n+1) * fact n

#eval fact 5

--- longuer de liste
def longueur {α : Type} : List α → Nat
| []      => 0
| _ :: t  => 1 + longueur t

#eval longueur [10,20,30]


--- arbre binaire
inductive Arbre where
| vide
| noeud (g : Arbre) (val : Nat) (d : Arbre)
deriving Repr


inductive Arbre_binaire where
| vide : Arbre_binaire
| noeud : Arbre_binaire → Nat → Arbre_binaire → Arbre_binaire
deriving Repr

#check Arbre_binaire.vide


-- Exemple de ce que vous écrivez dès ce soir :
def is_valid_password (p : String) : Prop :=
  p.length ≥ 12 ∧ (∃ c ∈ p.toList, c.isUpper)
