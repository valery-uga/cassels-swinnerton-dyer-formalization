import PfaffianDescent.ActualP3QuadraticDictionaryFactorNaturality

/-! SOURCE ONLY / UNVERIFIED165. Generic actual H0 factor inclusion together
with its established polynomial law. No original quartic-point context here. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Bundle the genuine map and its proved polynomial law before any large
original-point specialization. The map is the actual induced sheaf map. -/
def p3ActualIdealQuadraticFactorData165
    {K : Type u} [Field K] {Z P : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (r : P ⟶ Z) (q : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hfac : r ≫ i = q) [IsClosedImmersion i] [IsClosedImmersion q] :
    { m : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
        (closedImmersionIdealTwist i
          (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)) →ₗ[K]
      SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
        (closedImmersionIdealTwist q
          (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)) //
      ∀ s, (p3ActualIdealQuadraticIntrinsicLinearEquiv q (m s)).val =
        (p3ActualIdealQuadraticIntrinsicLinearEquiv i s).val } :=
  ⟨actualAmbientClosedIdealTwistHZeroFactorInclusion
      (ambientToBase (R := K) (σ := Fin 4)) i r q hfac
      (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2),
    fun s => p3ActualIdealQuadraticIntrinsicLinearEquiv_factor_naturality i r q hfac s⟩

/-- Exact generic map identity; no original-point conversion. -/
lemma p3ActualIdealQuadraticFactorData_map165
    {K : Type u} [Field K] {Z P : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (r : P ⟶ Z) (q : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hfac : r ≫ i = q) [IsClosedImmersion i] [IsClosedImmersion q] :
    (p3ActualIdealQuadraticFactorData165 i r q hfac).val =
      actualAmbientClosedIdealTwistHZeroFactorInclusion
        (ambientToBase (R := K) (σ := Fin 4)) i r q hfac
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2) := rfl

end PfaffianDescent
