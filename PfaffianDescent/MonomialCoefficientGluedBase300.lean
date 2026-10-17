import PfaffianDescent.NativeSchemeGlueDataDescent300
import PfaffianDescent.MonomialCoefficientSchemeGlueData300

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
/-- Bound the localization/base composition BEFORE substituting the original
universal quotient ring and determinant. All scalar maps are native and unchanged. -/
private lemma nativeLocalizationSpecMap_toBase300
    {R C : Type u} [CommRing R] [CommRing C] [Algebra R C] (a : C) :
    localizationPrincipalOpenMap294 a ≫
      Spec.map (CommRingCat.ofHom (algebraMap R C)) =
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a))) :=
  algebraHomSpecMap_overBase298 (Algebra.algHom R C (Localization.Away a))

variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B C : Fin n → (Fin m →₀ ℕ)) (kB kC : Fin n)
variable (hkB : B kB = 0) (hkC : C kC = 0)

/-- Original coefficient affine chart's literal structure morphism to Spec R. -/
def monomialCoefficientChartToBase300 :
    Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n B kB)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap R (UniversalCyclicCoefficientAlgebra282 R m n B kB)))

/-- Original294 localization square commutes with these original base maps. -/
lemma monomialOverlapPrincipalOpenMap_toBase300 :
    monomialOverlapPrincipalOpenMap294 R m n B C kB hkB ≫
      monomialCoefficientChartToBase300 R m n B kB =
    Spec.map (CommRingCat.ofHom
      (algebraMap R (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB))) := by
  simpa only [monomialOverlapPrincipalOpenMap294, monomialCoefficientChartToBase300] using
    (nativeLocalizationSpecMap_toBase300 (R := R)
      (universalMonomialOverlapDet292 R m n B C kB hkB))

/-- The SAME298 ORIGINAL principal-open transition commutes with the ORIGINAL base maps. -/
lemma monomialOverlapPrincipalSchemeIso_toBase300 :
    (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC).hom ≫
      monomialOverlapOriginalOpenInclusion300 R m n C B kC hkC ≫
      monomialCoefficientChartToBase300 R m n C kC =
    monomialOverlapOriginalOpenInclusion300 R m n B C kB hkB ≫
      monomialCoefficientChartToBase300 R m n B kB := by
  apply nativePairTransition_overBase300
    (monomialOverlapPrincipalOpenIso294 R m n B C kB hkB)
    (monomialOverlapPrincipalOpenIso294 R m n C B kC hkC)
    (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC).hom
    (monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC).hom
    (monomialOverlapOriginalOpenInclusion300 R m n B C kB hkB ≫
      monomialCoefficientChartToBase300 R m n B kB)
    (monomialOverlapOriginalOpenInclusion300 R m n C B kC hkC ≫
      monomialCoefficientChartToBase300 R m n C kC)
    (Spec.map (CommRingCat.ofHom
      (algebraMap R (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB))))
    (Spec.map (CommRingCat.ofHom
      (algebraMap R (MonomialOverlapCoefficientAlgebra292 R m n C B kC hkC))))
  · exact monomialOverlapPrincipalSchemeIso_transport300 R m n B C kB kC hkB hkC
  · calc
      _ = monomialOverlapPrincipalOpenMap294 R m n B C kB hkB ≫
          monomialCoefficientChartToBase300 R m n B kB := by
        simpa only [monomialOverlapOriginalOpenInclusion300, Category.assoc] using congrArg
          (fun f => f ≫ monomialCoefficientChartToBase300 R m n B kB)
          (monomialOverlapPrincipalOpenIso_hom_fac294 R m n B C kB hkB)
      _ = _ := monomialOverlapPrincipalOpenMap_toBase300 R m n B C kB hkB
  · calc
      _ = monomialOverlapPrincipalOpenMap294 R m n C B kC hkC ≫
          monomialCoefficientChartToBase300 R m n C kC := by
        simpa only [monomialOverlapOriginalOpenInclusion300, Category.assoc] using congrArg
          (fun f => f ≫ monomialCoefficientChartToBase300 R m n C kC)
          (monomialOverlapPrincipalOpenIso_hom_fac294 R m n C B kC hkC)
      _ = _ := monomialOverlapPrincipalOpenMap_toBase300 R m n C B kC hkC
  · exact monomialOverlapAffineSchemeIso_overBase298 R m n B C kB kC hkB hkC

/-- The actually constructed native coefficient Scheme has an original structure map over R. -/
def monomialCoefficientGluedToBase300 :
    monomialCoefficientGluedScheme300 R m n ⟶ Spec (.of R) :=
  nativeSchemeGlueDataDesc300 (monomialCoefficientSchemeGlueData300 R m n) (Spec (.of R))
    (fun i => monomialCoefficientChartToBase300 R m n i.down.monomials i.down.zeroIndex)
    (fun i j => monomialOverlapPrincipalSchemeIso_toBase300 R m n
      i.down.monomials j.down.monomials i.down.zeroIndex j.down.zeroIndex
      i.down.zero_eq j.down.zero_eq)

/-- Every original coefficient chart immersion preserves the SAME base morphism. -/
lemma monomialCoefficientGluedChartMap_toBase300
    (i : MonomialCoefficientChartIndex300 m n) :
    monomialCoefficientGluedChartMap300 R m n i ≫ monomialCoefficientGluedToBase300 R m n =
      monomialCoefficientChartToBase300 R m n i.monomials i.zeroIndex :=
  nativeSchemeGlueDataDesc_chart300 (monomialCoefficientSchemeGlueData300 R m n)
    (Spec (.of R)) _ _ ⟨i⟩

end PfaffianDescent
