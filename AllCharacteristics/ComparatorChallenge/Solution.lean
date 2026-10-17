import AllCharacteristics.InternalCorayPaperConclusions

/-! Solution adapter for the independent Mathlib-only challenge. Do not import
Challenge here: Comparator compares two separate environments. -/

namespace CasselsSwinnertonDyerChallenge
universe u
set_option autoImplicit false

theorem rational_point_descent
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (p : MvPolynomial (Fin 4) k) (_hp0 : p ≠ 0) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (x : Fin 4 → L) (hx : x ≠ 0)
    (heval : p.eval₂ (algebraMap k L) x = 0) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 :=
  AllCharacteristics.twoProofs_finite_point_coprime_has_point_internalCoray001
    p hp hdegree x hx heval

end CasselsSwinnertonDyerChallenge

#print axioms CasselsSwinnertonDyerChallenge.rational_point_descent
