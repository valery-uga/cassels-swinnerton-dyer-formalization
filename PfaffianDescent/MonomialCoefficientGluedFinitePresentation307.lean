import PfaffianDescent.NativeAlgebraSpecFinitePresentation307
import PfaffianDescent.MonomialCoefficientGluedBase300
import PfaffianDescent.UniversalCyclicMatrixQuotient282

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Transport native LFP along ordinary equality of the SAME scheme morphisms. -/
private lemma originalLFP_mapEquality_transport307
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (hg : LocallyOfFinitePresentation g) : LocallyOfFinitePresentation f := by
  cases h
  exact hg

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- The ORIGINAL coefficient chart is locally of finite presentation over R.
Its finite-presentation property is derived from its actual finite matrix/cyclic relations. -/
lemma monomialCoefficientChartToBase_locallyOfFinitePresentation307
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) :
    LocallyOfFinitePresentation (monomialCoefficientChartToBase300 R m n B k) := by
  letI : Algebra.FinitePresentation R (UniversalCyclicCoefficientAlgebra282 R m n B k) :=
    universalCyclicCoefficientAlgebra_finitePresentation282 R m n B k
  exact nativeAlgebraSpecProjection_locallyOfFinitePresentation307 R
    (UniversalCyclicCoefficientAlgebra282 R m n B k)

/-- The actual original cover's composite, with its exact original structure map. -/
private lemma originalCoefficientGluedOpenCover_toBase307
    (i : ULift.{u} (MonomialCoefficientChartIndex300 m n)) :
    (monomialCoefficientGluedOpenCover300 R m n).f i ≫
      monomialCoefficientGluedToBase300 R m n =
    monomialCoefficientChartToBase300 R m n i.down.monomials i.down.zeroIndex :=
  monomialCoefficientGluedChartMap_toBase300 R m n i.down

/-- The SAME actually glued coefficient Scheme has a genuine LFP morphism
to Spec R. No representing scheme, LFP conclusion, or smoothness certificate is input. -/
theorem monomialCoefficientGluedToBase_locallyOfFinitePresentation307 :
    LocallyOfFinitePresentation (monomialCoefficientGluedToBase300 R m n) := by
  apply nativeLocallyOfFinitePresentation_of_sourceOpenCover307
    (monomialCoefficientGluedToBase300 R m n) (monomialCoefficientGluedOpenCover300 R m n)
  intro i
  change ULift.{u} (MonomialCoefficientChartIndex300 m n) at i
  exact originalLFP_mapEquality_transport307
    (originalCoefficientGluedOpenCover_toBase307 R m n i)
    (monomialCoefficientChartToBase_locallyOfFinitePresentation307 R m n
      i.down.monomials i.down.zeroIndex)

end PfaffianDescent
end
