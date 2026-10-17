import PfaffianDescent.IntrinsicFiniteCycle
import PfaffianDescent.IntrinsicFullQuadraticSystem

/-! Actual standard-chart algebras of EVERY finite projective subscheme.
Finite schemes over fields are Artinian, so their open immersions are also
closed. Consequently every chart preimage has a finite actual coefficient
algebra. No reducedness or ground hyperplane avoidance is used. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k]

theorem finiteScheme_openImmersion_isClosedImmersion
    {Z U : Scheme.{u}} (t : Z ⟶ Spec (.of k)) [IsFinite t]
    (j : U ⟶ Z) [IsOpenImmersion j] : IsClosedImmersion j := by
  letI : IsArtinianScheme Z := finiteScheme_isArtinian t
  exact IsClosedImmersion.of_isPreimmersion j (isClosed_discrete _)

theorem finiteScheme_openImmersion_isFinite
    {Z U : Scheme.{u}} (t : Z ⟶ Spec (.of k)) [IsFinite t]
    (j : U ⟶ Z) [IsOpenImmersion j] : IsFinite (j ≫ t) := by
  letI : IsClosedImmersion j := finiteScheme_openImmersion_isClosedImmersion t j
  infer_instance

def finiteProjectiveStandardChartOpen
    {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k)) (j : Fin 4) : Z.Opens :=
  i ⁻¹ᵁ (intrinsicQuadraticAmbientOpen (K := k) j).1

def finiteProjectiveStandardChart
    {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k)) (j : Fin 4) : Scheme.{u} :=
  (finiteProjectiveStandardChartOpen i j).toScheme

def finiteProjectiveStandardChartToBase
    {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k)) (j : Fin 4) :
    finiteProjectiveStandardChart i j ⟶ Spec (.of k) :=
  (finiteProjectiveStandardChartOpen i j).ι ≫ (i ≫ ambientToBase)

theorem finiteProjectiveStandardChartToBase_isFinite
    {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsFinite (i ≫ ambientToBase)] (j : Fin 4) :
    IsFinite (finiteProjectiveStandardChartToBase i j) :=
  finiteScheme_openImmersion_isFinite (i ≫ ambientToBase)
    (finiteProjectiveStandardChartOpen i j).ι

/-- All four actual chart coefficient algebras, including empty-chart zero
rings and all nonreduced local factors, are finite over the ground field. -/
theorem finiteProjectiveStandardChart_coefficient_finite
    {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsFinite (i ≫ ambientToBase)] (j : Fin 4) :
    letI := finiteProjectiveStandardChartToBase_isFinite i j
    letI := finiteSchemeCoefficientAlgebra (finiteProjectiveStandardChartToBase i j)
    Module.Finite k Γ(finiteProjectiveStandardChart i j, ⊤) := by
  letI := finiteProjectiveStandardChartToBase_isFinite i j
  letI := finiteSchemeCoefficientAlgebra (finiteProjectiveStandardChartToBase i j)
  exact finiteSchemeCoefficient_finite (finiteProjectiveStandardChartToBase i j)

abbrev finiteProjectiveStandardChartCoefficientAlgebra
    {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsFinite (i ≫ ambientToBase)] (j : Fin 4) :
    Algebra k Γ(finiteProjectiveStandardChart i j, ⊤) :=
  letI := finiteProjectiveStandardChartToBase_isFinite i j
  finiteSchemeCoefficientAlgebra (finiteProjectiveStandardChartToBase i j)

theorem finiteProjectiveStandardChartOpen_iSup
    {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k)) :
    ⨆ j : Fin 4, finiteProjectiveStandardChartOpen i j = ⊤ := by
  change ⨆ j : Fin 4, i ⁻¹ᵁ (intrinsicQuadraticAmbientOpen (K := k) j).1 = ⊤
  exact i.iSup_preimage_eq_top intrinsicQuadraticAmbientOpen_iSup

end PfaffianDescent
