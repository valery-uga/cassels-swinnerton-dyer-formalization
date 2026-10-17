import PfaffianDescent.RelativeProjectiveLinearSystem
import AllCharacteristics.ProjectiveBaseChange

/-!
# Relative projective systems and coefficient change

The projective parameter space over a chart coefficient ring maps canonically
to the original coefficient parameter space.  Composing a chart's relative
linear system with this map gives the local morphism used by the global
Grassmannian construction.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable {R S : Type u} [CommRing R] [CommRing S] {σ τ : Type}
variable [Finite σ] [Finite τ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Coefficient extension gives the canonical morphism from projective
parameters over the extended ring to the original parameter space. -/
noncomputable def projectiveParametersCoefficientMap (f : R →+* S) :
    projectiveParameters S σ d ⟶ projectiveParameters R σ d :=
  projectiveCoefficientMap f (ParameterIdeal R σ d) (ParameterIdeal S σ d)
    (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- Successive coefficient changes of projective equation parameters compose
in the same order as their coefficient-ring homomorphisms. -/
theorem projectiveParametersCoefficientMap_comp
    {T : Type u} [CommRing T] (f : R →+* S) (g : S →+* T) :
    projectiveParametersCoefficientMap d (σ := σ) g ≫
      projectiveParametersCoefficientMap d (σ := σ) f =
    projectiveParametersCoefficientMap d (σ := σ) (g.comp f) := by
  unfold projectiveParametersCoefficientMap
  simpa using projectiveCoefficientMap_comp f g
    (ParameterIdeal R σ d) (ParameterIdeal S σ d) (ParameterIdeal T σ d)
    (by simp) (by simp)

/-- Viewing a field-valued equation first over its coefficient field and then
restricting projective parameters to the original base ring gives its direct
classifying morphism over that base ring. -/
theorem projectiveClassifyingMap_comp_projectiveParametersCoefficientMap
    {k : Type u} [Field k] (f : R →+* k) (p : MvPolynomial σ k)
    (hp : p.IsHomogeneous d) (hne : p ≠ 0) :
    projectiveClassifyingMap p hp hne (RingHom.id k) ≫
        projectiveParametersCoefficientMap d f =
      projectiveClassifyingMap p hp hne f := by
  let j := chosenEquationCoefficient p hp hne
  let hj := chosenEquationCoefficient_ne_zero p hp hne
  rw [projectiveClassifyingMap_eq_chart p hp hne (RingHom.id k) j hj,
    projectiveClassifyingMap_eq_chart p hp hne f j hj]
  unfold projectiveEquationParameter
  rw [Category.assoc]
  rw [show parameterChartι k σ d j ≫
        projectiveParametersCoefficientMap d f =
      Spec.map (CommRingCat.ofHom (chartCoefficientMap f
        (ParameterIdeal R σ d) (ParameterIdeal k σ d) (by simp) j)) ≫
        parameterChartι R σ d j by
    exact chartι_projectiveCoefficientMap f
      (ParameterIdeal R σ d) (ParameterIdeal k σ d) (by simp) j]
  rw [← Category.assoc, ← Spec.map_comp]
  apply congrArg (fun k => k ≫ parameterChartι R σ d j)
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply projectiveChartMap_ext j
  · apply RingHom.ext
    intro r
    change projectiveEquationChartMap (RingHom.id k) p j hj
        (chartCoefficientMap f _ _ _ j (chartBaseMap _ j r)) = _
    rw [chartCoefficientMap_baseMap, projectiveEquationChartMap_baseMap]
    change f r = projectiveEquationChartMap f p j hj
      (chartBaseMap (ParameterIdeal R σ d) j r)
    exact (projectiveEquationChartMap_baseMap f p j hj r).symm
  · intro m
    change projectiveEquationChartMap (RingHom.id k) p j hj
        (chartCoefficientMap f _ _ _ j (chartCoordinate _ j m)) = _
    rw [chartCoefficientMap_coordinate, projectiveEquationChartMap_coordinate]
    change (p.coeff j.1)⁻¹ * p.coeff m.1 =
      projectiveEquationChartMap f p j hj
        (chartCoordinate (ParameterIdeal R σ d) j m)
    exact (projectiveEquationChartMap_coordinate f p j hj m).symm

/-- The projective coefficient morphism is compatible with the two base
spectra. -/
theorem projectiveParametersCoefficientMap_toBase (f : R →+* S) :
    projectiveParametersCoefficientMap d f ≫ projectiveParametersToBase R σ d =
      projectiveParametersToBase S σ d ≫ Spec.map (CommRingCat.ofHom f) := by
  exact projectiveCoefficientMap_toBase f (ParameterIdeal R σ d)
    (ParameterIdeal S σ d) (by simp)

/-- Projective parameter base change along an open affine map is itself an
open immersion.  This makes the relative projective coordinate spaces on
Grassmannian chart overlaps into genuine open subcharts. -/
instance projectiveParametersCoefficientMap_isOpenImmersion (f : R →+* S)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))] :
    IsOpenImmersion (projectiveParametersCoefficientMap d (σ := σ) f) := by
  unfold projectiveParametersCoefficientMap
  apply MorphismProperty.of_isPullback
    (isPullback_projectiveCoefficientMap f (ParameterIdeal R σ d)
      (ParameterIdeal S σ d) (by simp)).flip
  infer_instance

/-- A relative system, viewed in the original coefficient parameter space. -/
noncomputable def relativeProjectiveLinearSystemToGlobalParameters
    (f : R →+* S)
    (g : MvPolynomial (Monomials σ d) S →ₐ[S] MvPolynomial τ S)
    (hdeg : ∀ (r : ℕ) (p : MvPolynomial (Monomials σ d) S),
      p.IsHomogeneous r → (g p).IsHomogeneous r)
    (hsurj : Function.Surjective g) :
    relativeProjectiveLinearSystemParameters (R := S) (τ := τ) ⟶
      projectiveParameters R σ d :=
  relativeProjectiveLinearSystemToParameters d g hdeg hsurj ≫
    projectiveParametersCoefficientMap d f

/-- The local global-parameter map lies over the chart's structural map to
the original coefficient spectrum. -/
theorem relativeProjectiveLinearSystemToGlobalParameters_toBase
    (f : R →+* S)
    (g : MvPolynomial (Monomials σ d) S →ₐ[S] MvPolynomial τ S)
    (hdeg : ∀ (r : ℕ) (p : MvPolynomial (Monomials σ d) S),
      p.IsHomogeneous r → (g p).IsHomogeneous r)
    (hsurj : Function.Surjective g) :
    relativeProjectiveLinearSystemToGlobalParameters d f g hdeg hsurj ≫
      projectiveParametersToBase R σ d =
        toBase (⊥ : HomogeneousIdeal
          (MvPolynomial.homogeneousSubmodule τ S)) ≫
            Spec.map (CommRingCat.ofHom f) := by
  rw [relativeProjectiveLinearSystemToGlobalParameters, Category.assoc,
    projectiveParametersCoefficientMap_toBase]
  rw [← Category.assoc, relativeProjectiveLinearSystemToParameters_toBase]

/-- The local chart family, mapped into the original coefficient parameter
space. -/
noncomputable def grassmannianChartHomogeneousFrameToGlobalParameters
    {m n : ℕ} (f : R →+* S)
    (e : Fin (m + n) ≃ Monomials σ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) S) :
    relativeProjectiveLinearSystemParameters (R := S) (τ := Fin m) ⟶
      projectiveParameters R σ d :=
  grassmannianChartHomogeneousFrameToParameters (R := S) d e ρ T ≫
    projectiveParametersCoefficientMap d f

/-- The chart family has the expected structural map to the original
coefficient spectrum. -/
theorem grassmannianChartHomogeneousFrameToGlobalParameters_toBase
    {m n : ℕ} (f : R →+* S)
    (e : Fin (m + n) ≃ Monomials σ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) S) :
    grassmannianChartHomogeneousFrameToGlobalParameters d f e ρ T ≫
      projectiveParametersToBase R σ d =
        toBase (⊥ : HomogeneousIdeal
          (MvPolynomial.homogeneousSubmodule (Fin m) S)) ≫
            Spec.map (CommRingCat.ofHom f) := by
  rw [grassmannianChartHomogeneousFrameToGlobalParameters, Category.assoc,
    projectiveParametersCoefficientMap_toBase]
  rw [← Category.assoc, grassmannianChartHomogeneousFrameToParameters_toBase]

end PfaffianDescent
