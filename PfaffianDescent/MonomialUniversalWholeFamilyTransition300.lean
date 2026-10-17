import PfaffianDescent.NativeWholeIdealComparisonDescent300
import PfaffianDescent.NativeWholeIdealChartFamily302
import PfaffianDescent.MonomialOverlapCoefficientPointTransport300
import PfaffianDescent.MonomialOverlapPrincipalOpen294

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B C : Fin n → (Fin m →₀ ℕ)) (kB kC : Fin n)
variable (hkB : B kB = 0) (hkC : C kC = 0)

/-- The genuine universal overlap point has EXACT original localized whole ideal294. -/
lemma monomialOverlapClassification_originalWholeIdeal300 :
    (monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB
      (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB)
      (AlgHom.id R (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB))).val.val =
    monomialOverlapWholeIdeal294 R m n B C kB hkB := by
  have h := monomialOverlapClassification_chart300
    (R := R) (m := m) (n := n) (B := B) (C := C) (kB := kB) (hkB := hkB)
    (AlgHom.id R (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB))
  rw [AlgHom.id_comp] at h
  have hi := congrArg
    (fun x : MonomialWholeIdealChart287
      (A := MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB) B => x.val) h
  exact hi.trans (cyclicCoefficientWholeIdealChart_ideal302 R B kB hkB
    (Algebra.algHom R (UniversalCyclicCoefficientAlgebra282 R m n B kB)
      (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB)))

/-- The SAME inverse coefficient map defining298's B→C geometric transition maps
C's entire localized universal ideal to B's entire localized universal ideal. -/
lemma monomialOverlapOriginalWholeIdeal_transition300 :
    (monomialOverlapWholeIdeal294 R m n C B kC hkC).map
      (MvPolynomial.map
        (monomialOverlapForwardCoefficientMap293 R m n C B kC kB hkC hkB).toRingHom) =
    monomialOverlapWholeIdeal294 R m n B C kB hkB := by
  let S := MonomialOverlapCoefficientAlgebra292 R m n C B kC hkC
  let T := MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB
  let f := monomialOverlapForwardCoefficientMap293 R m n C B kC kB hkC hkB
  have hn := monomialOverlapLocalizationAlgHomEquiv_natural292 R m n C B kC hkC
    (AlgHom.id R S) f
  rw [AlgHom.comp_id] at hn
  have hi :
      (monomialOverlapLocalizationAlgHomEquiv292 R m n C B kC hkC T f).val.val =
      (monomialOverlapLocalizationAlgHomEquiv292 R m n C B kC hkC S
        (AlgHom.id R S)).val.val.map (MvPolynomial.map f.toRingHom) :=
    congrArg (fun x : MonomialWholeIdealChartOverlap290 (A := T) C B => x.val.val) hn
  calc
    _ = (monomialOverlapLocalizationAlgHomEquiv292 R m n C B kC hkC S
        (AlgHom.id R S)).val.val.map (MvPolynomial.map f.toRingHom) :=
      congrArg (fun I : Ideal (MvPolynomial (Fin m) S) =>
        I.map (MvPolynomial.map f.toRingHom))
        (monomialOverlapClassification_originalWholeIdeal300 R m n C B kC hkC).symm
    _ = (monomialOverlapLocalizationAlgHomEquiv292 R m n C B kC hkC T f).val.val := hi.symm
    _ = (monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB T
        (AlgHom.id R T)).val.val :=
      monomialOverlapForwardCoefficientMap_sameIdeal293 R m n C B kC kB hkC hkB
    _ = _ := monomialOverlapClassification_originalWholeIdeal300 R m n B C kB hkB

/-- The actual polynomial-ambient map over the SAME298 affine coefficient transition.
Its Spec direction is B→C, so the coefficient ring map is the original reverse C→B map. -/
def monomialOverlapUniversalAmbientMap300 :
    Spec (.of (MvPolynomial (Fin m) (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB))) ⟶
      Spec (.of (MvPolynomial (Fin m) (MonomialOverlapCoefficientAlgebra292 R m n C B kC hkC))) :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.map
      (monomialOverlapForwardCoefficientMap293 R m n C B kC kB hkC hkB).toRingHom))

/-- Native universal WHOLE closed families on the two coefficient overlaps agree by
actual Cartesian scalar extension along the SAME original geometric coefficient map. -/
lemma monomialOverlapUniversalClosedFamily_kernel_comap300 :
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (monomialOverlapWholeIdeal294 R m n C B kC hkC)))).ker.comap
      (monomialOverlapUniversalAmbientMap300 R m n B C kB kC hkB hkC) =
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (monomialOverlapWholeIdeal294 R m n B C kB hkB)))).ker :=
  nativePolynomialIdealImageKernel_comap300
    (monomialOverlapForwardCoefficientMap293 R m n C B kC kB hkC hkB).toRingHom
    (monomialOverlapWholeIdeal294 R m n C B kC hkC)
    (monomialOverlapWholeIdeal294 R m n B C kB hkB)
    (monomialOverlapOriginalWholeIdeal_transition300 R m n B C kB kC hkB hkC)

/-- Genuine native comparison Iso to the pullback of C's ORIGINAL whole closed family.
No reduced-support substitution or supplied family comparison Iso is used. -/
def monomialOverlapUniversalClosedFamilyIso300 :
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (monomialOverlapWholeIdeal294 R m n B C kB hkB)))).ker.subscheme ≅
    pullback (monomialOverlapUniversalAmbientMap300 R m n B C kB kC hkB hkC)
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (monomialOverlapWholeIdeal294 R m n C B kC hkC)))).ker.subschemeι :=
  nativeClosedIdealComparisonIso300
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (monomialOverlapWholeIdeal294 R m n C B kC hkC)))).ker
    (monomialOverlapUniversalAmbientMap300 R m n B C kB kC hkB hkC)
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (monomialOverlapWholeIdeal294 R m n B C kB hkB)))).ker
    (monomialOverlapUniversalClosedFamily_kernel_comap300 R m n B C kB kC hkB hkC)

/-- The comparison preserves the actual original whole closed embedding on B's overlap. -/
lemma monomialOverlapUniversalClosedFamilyIso_hom_fst300 :
    (monomialOverlapUniversalClosedFamilyIso300 R m n B C kB kC hkB hkC).hom ≫
      pullback.fst _ _ =
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (monomialOverlapWholeIdeal294 R m n B C kB hkB)))).ker.subschemeι :=
  nativeClosedIdealComparisonIso_hom_fst300
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (monomialOverlapWholeIdeal294 R m n C B kC hkC)))).ker
    (monomialOverlapUniversalAmbientMap300 R m n B C kB kC hkB hkC)
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (monomialOverlapWholeIdeal294 R m n B C kB hkB)))).ker
    (monomialOverlapUniversalClosedFamily_kernel_comap300 R m n B C kB kC hkB hkC)

end PfaffianDescent
