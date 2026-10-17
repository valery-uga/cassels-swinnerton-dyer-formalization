import PfaffianDescent.MonomialTripleCoefficientRotation300
import PfaffianDescent.NativeTripleSchemeGluingCuts300
import PfaffianDescent.MonomialOverlapSchemeTransition298

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B C D : Fin n → (Fin m →₀ ℕ)) (kB kC : Fin n)
variable (hkB : B kB = 0) (hkC : C kC = 0)

/-- Actual triple Scheme rotation from the SAME original double localization.
The ring map is derived from the original whole-ideal representing equivalence. -/
def monomialTripleSchemeRotate300 :
    monomialTripleOverlapScheme300 R m n B C D kB hkB ⟶
      monomialTripleOverlapScheme300 R m n C D B kC hkC :=
  Spec.map (CommRingCat.ofHom
    (monomialTripleRotationCoefficientMap300 R m n B C D kB kC hkB hkC).toRingHom)

/-- EXACT pairwise transition compatibility for298's actual Scheme map on
the genuine triple domain, rather than equality of points or reduced ideals. -/
lemma monomialTripleSchemeRotate_pairFac300 :
    monomialTripleSchemeRotate300 R m n B C D kB kC hkB hkC ≫
        monomialTripleOverlapFirstLastSchemeMap300 R m n C D B kC hkC =
      monomialTripleOverlapFirstSchemeMap300 R m n B C D kB hkB ≫
        (monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC).hom := by
  have hr :
      (monomialTripleRotationCoefficientMap300 R m n B C D kB kC hkB hkC).toRingHom.comp
        (monomialTripleOverlapFirstLastCoefficientMap300 R m n C D B kC hkC).toRingHom =
      (monomialTripleOverlapFirstCoefficientMap300 R m n B C D kB hkB).toRingHom.comp
        (monomialOverlapForwardCoefficientMap293 R m n C B kC kB hkC hkB).toRingHom :=
    congrArg (fun z => z.toRingHom)
      (monomialTripleRotationCoefficientMap_edge300 R m n B C D kB kC hkB hkC)
  calc
    _ = monomialTripleOverlapFirstSchemeMap300 R m n B C D kB hkB ≫
        Spec.map (CommRingCat.ofHom
          (monomialOverlapForwardCoefficientMap293 R m n C B kC kB hkC hkB).toRingHom) :=
      nativeRingSquareSpec300 _ _ _ _ hr
    _ = _ := congrArg
      (fun f => monomialTripleOverlapFirstSchemeMap300 R m n B C D kB hkB ≫ f)
      (monomialOverlapAffineSchemeIso_hom298 R m n B C kB kC hkB hkC).symm

variable (kD : Fin n) (hkD : D kD = 0)

/-- Actual triple Scheme rotations satisfy the literal threefold cocycle,
internally derived from the whole coefficient-map identity. -/
lemma monomialTripleSchemeRotate_cycle300 :
    monomialTripleSchemeRotate300 R m n B C D kB kC hkB hkC ≫
        monomialTripleSchemeRotate300 R m n C D B kC kD hkC hkD ≫
        monomialTripleSchemeRotate300 R m n D B C kD kB hkD hkB =
      𝟙 (monomialTripleOverlapScheme300 R m n B C D kB hkB) :=
  nativeAlgebraTripleSpec_cycle300
    (monomialTripleRotationCoefficientMap300 R m n B C D kB kC hkB hkC)
    (monomialTripleRotationCoefficientMap300 R m n C D B kC kD hkC hkD)
    (monomialTripleRotationCoefficientMap300 R m n D B C kD kB hkD hkB)
    (monomialTripleRotationCoefficientMap_cycle300 R m n B C D kB kC hkB hkC kD hkD)

end PfaffianDescent
