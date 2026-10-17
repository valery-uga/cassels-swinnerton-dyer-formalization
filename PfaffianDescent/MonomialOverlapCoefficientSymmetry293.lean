import PfaffianDescent.MonomialWholeIdealOverlapSymmetry293
import PfaffianDescent.MonomialChartOverlapLocalization292

noncomputable section
namespace PfaffianDescent
open CategoryTheory Opposite
universe u

private def nativeCoefficientIsoOfCoyonedaIso293
    {T : Type*} [Category T] {X Y : T}
    (e : coyoneda.obj (op X) ≅ coyoneda.obj (op Y)) : X ≅ Y :=
  (Coyoneda.fullyFaithful.preimageIso e).unop.symm

private lemma nativeCoefficientIsoOfCoyonedaIso_hom293
    {T : Type*} [Category T] {X Y : T}
    (e : coyoneda.obj (op X) ≅ coyoneda.obj (op Y)) :
    (nativeCoefficientIsoOfCoyonedaIso293 e).hom = e.inv.app Y (𝟙 Y) := rfl

variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B C : Fin n → (Fin m →₀ ℕ)) (kB kC : Fin n)
variable (hkB : B kB = 0) (hkC : C kC = 0)

/-- A genuine isomorphism of the two original coefficient localizations is derived from
proved localization classification and literal same-ideal reversal. -/
def monomialOverlapCoefficientIso293 :
    monomialOverlapCoefficientObject292 R m n B C kB hkB ≅
      monomialOverlapCoefficientObject292 R m n C B kC hkC :=
  nativeCoefficientIsoOfCoyonedaIso293
    ((monomialOverlapLocalizationNatIso292 R m n B C kB hkB).trans
      ((monomialWholeIdealOverlapFlipNatIso293 B C R kB kC hkB hkC).trans
        (monomialOverlapLocalizationNatIso292 R m n C B kC hkC).symm))

/-- The forward coefficient map is explicit: reverse the second localization's actual universal
whole-ideal point, then apply the inverse of the first localization's proved classification. -/
def monomialOverlapForwardCoefficientMap293 :=
  (monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB
    (MonomialOverlapCoefficientAlgebra292 R m n C B kC hkC)).symm
      (monomialWholeIdealOverlapFlip293 C B
        (monomialOverlapLocalizationAlgHomEquiv292 R m n C B kC hkC
          (MonomialOverlapCoefficientAlgebra292 R m n C B kC hkC)
          (AlgHom.id R (MonomialOverlapCoefficientAlgebra292 R m n C B kC hkC))))

lemma monomialOverlapCoefficientIso_hom293 :
    (monomialOverlapCoefficientIso293 R m n B C kB kC hkB hkC).hom.hom =
      monomialOverlapForwardCoefficientMap293 R m n B C kB kC hkB hkC := rfl

lemma monomialOverlapCoefficientIso_inv293 :
    (monomialOverlapCoefficientIso293 R m n B C kB kC hkB hkC).inv.hom =
      monomialOverlapForwardCoefficientMap293 R m n C B kC kB hkC hkB := rfl

lemma monomialOverlapForwardCoefficientMap_classifies293 :
    monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB
        (MonomialOverlapCoefficientAlgebra292 R m n C B kC hkC)
        (monomialOverlapForwardCoefficientMap293 R m n B C kB kC hkB hkC) =
      monomialWholeIdealOverlapFlip293 C B
        (monomialOverlapLocalizationAlgHomEquiv292 R m n C B kC hkC
          (MonomialOverlapCoefficientAlgebra292 R m n C B kC hkC)
          (AlgHom.id R (MonomialOverlapCoefficientAlgebra292 R m n C B kC hkC))) :=
  (monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB
    (MonomialOverlapCoefficientAlgebra292 R m n C B kC hkC)).apply_symm_apply _

/-- The actual coefficient transition identifies the same entire ideal, including nilpotents. -/
lemma monomialOverlapForwardCoefficientMap_sameIdeal293 :
    (monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB
        (MonomialOverlapCoefficientAlgebra292 R m n C B kC hkC)
        (monomialOverlapForwardCoefficientMap293 R m n B C kB kC hkB hkC)).val.val =
      (monomialOverlapLocalizationAlgHomEquiv292 R m n C B kC hkC
        (MonomialOverlapCoefficientAlgebra292 R m n C B kC hkC)
        (AlgHom.id R (MonomialOverlapCoefficientAlgebra292 R m n C B kC hkC))).val.val :=
  congrArg (fun x : MonomialWholeIdealChartOverlap290
      (A := MonomialOverlapCoefficientAlgebra292 R m n C B kC hkC) B C => x.val.val)
    (monomialOverlapForwardCoefficientMap_classifies293 R m n B C kB kC hkB hkC)

end PfaffianDescent
