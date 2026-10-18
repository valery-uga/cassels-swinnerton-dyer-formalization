import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Stalk

namespace AllCharacteristics

open AlgebraicGeometry CategoryTheory MvPolynomial

universe u

attribute [local instance] MvPolynomial.algebraMvPolynomial

set_option backward.isDefEq.respectTransparency.types false in
noncomputable local instance affineSourceAlgebra
    (R : Type u) [CommRing R] [IsDomain R] :
    Algebra R (Spec (.of R)).functionField := by
  letI : IsDomain (CommRingCat.of R) := inferInstanceAs (IsDomain R)
  exact AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of R)

set_option backward.isDefEq.respectTransparency.types false in
noncomputable local instance affineSourceFractionRing
    (R : Type u) [CommRing R] [IsDomain R] :
    IsFractionRing R (Spec (.of R)).functionField := by
  letI : IsDomain (CommRingCat.of R) := inferInstanceAs (IsDomain R)
  exact AlgebraicGeometry.functionField_isFractionRing_of_affine (CommRingCat.of R)

/-- A localization of a domain embeds canonically into its actual affine
scheme function field, which is also a fraction field of the localization. -/
theorem exists_localization_map_to_affineFunctionField
    {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (hM : M ≤ nonZeroDivisors R) :
    ∃ f : S →+* (Spec (.of R)).functionField,
      f.comp (algebraMap R S) = algebraMap R (Spec (.of R)).functionField ∧
      letI : Algebra S (Spec (.of R)).functionField := f.toAlgebra
      IsScalarTower R S (Spec (.of R)).functionField ∧
        IsFractionRing S (Spec (.of R)).functionField := by
  let T := (Spec (.of R)).functionField
  have hunits : ∀ m : M, IsUnit (algebraMap R T (m : R)) := by
    intro m
    exact IsLocalization.map_units T ⟨(m : R), hM m.property⟩
  let f : S →+* T := IsLocalization.lift (S := S) hunits
  have hf : f.comp (algebraMap R S) = algebraMap R T :=
    IsLocalization.lift_comp hunits
  refine ⟨f, hf, ?_⟩
  letI : Algebra S T := f.toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' hf.symm
  exact ⟨inferInstance,
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S T⟩

/-- The actual affine source for the universal line plus two triples of
tangent parameters.  Its coefficients are polynomials in the three line
coordinates; the six outer variables are all independent tangent parameters. -/
abbrev KollarUniversalParameterRing (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2 × Fin 3) (MvPolynomial (Fin 3) k)

/-- The generic line field together with the independent tangent parameters. -/
abbrev KollarUniversalLocalizedParameterRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2 × Fin 3) (FractionRing (MvPolynomial (Fin 3) k))

/-- The iterated generic parameter ring is an actual localization of the
nine-variable source ring and embeds into that source scheme's own function
field.  This supplies a concrete affine source for the universal construction. -/
theorem exists_kollarUniversalLocalizedParameterMap
    (k : Type u) [Field k] :
    ∃ f : KollarUniversalLocalizedParameterRing k →+*
        (Spec (.of (KollarUniversalParameterRing k))).functionField,
      f.comp (algebraMap (KollarUniversalParameterRing k)
        (KollarUniversalLocalizedParameterRing k)) =
          algebraMap (KollarUniversalParameterRing k)
            (Spec (.of (KollarUniversalParameterRing k))).functionField ∧
      letI : Algebra (KollarUniversalLocalizedParameterRing k)
          (Spec (.of (KollarUniversalParameterRing k))).functionField := f.toAlgebra
      IsScalarTower (KollarUniversalParameterRing k)
          (KollarUniversalLocalizedParameterRing k)
          (Spec (.of (KollarUniversalParameterRing k))).functionField ∧
        IsFractionRing (KollarUniversalLocalizedParameterRing k)
          (Spec (.of (KollarUniversalParameterRing k))).functionField := by
  let P := MvPolynomial (Fin 3) k
  let R := KollarUniversalParameterRing k
  let S := KollarUniversalLocalizedParameterRing k
  let M : Submonoid R := (nonZeroDivisors P).map (MvPolynomial.C : P →+* R)
  letI : Algebra R S := MvPolynomial.algebraMvPolynomial
  letI : IsLocalization M S :=
    MvPolynomial.isLocalization (nonZeroDivisors P) (FractionRing P)
  apply exists_localization_map_to_affineFunctionField M
  rintro x ⟨y, hy, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hC
  apply (mem_nonZeroDivisors_iff_ne_zero.mp hy)
  apply MvPolynomial.C_injective (σ := Fin 2 × Fin 3)
  exact hC.trans (map_zero (MvPolynomial.C : P →+* R)).symm

/-- The actual affine source structure map to the original coefficient field. -/
noncomputable def kollarUniversalSourceToBase
    (k : Type u) [Field k] :
    Spec (.of (KollarUniversalParameterRing k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom
    ((MvPolynomial.C : MvPolynomial (Fin 3) k →+* KollarUniversalParameterRing k).comp
      MvPolynomial.C))

set_option backward.isDefEq.respectTransparency.types false in
/-- Its function-field coefficient map is compatible with the actual generic
point morphism, as required by the rational-map spreading theorem. -/
theorem kollarUniversalSource_functionField_baseMap
    (k : Type u) [Field k] :
    Spec.map (CommRingCat.ofHom
      ((algebraMap (KollarUniversalParameterRing k)
          (Spec (.of (KollarUniversalParameterRing k))).functionField).comp
        ((MvPolynomial.C : MvPolynomial (Fin 3) k →+* KollarUniversalParameterRing k).comp
          MvPolynomial.C))) =
      (Spec (.of (KollarUniversalParameterRing k))).fromSpecStalk
        (genericPoint (Spec (.of (KollarUniversalParameterRing k)))) ≫
        kollarUniversalSourceToBase k := by
  unfold kollarUniversalSourceToBase
  have hfrom :
      (Spec (.of (KollarUniversalParameterRing k))).fromSpecStalk
        (genericPoint (Spec (.of (KollarUniversalParameterRing k)))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (KollarUniversalParameterRing k)
          (Spec (.of (KollarUniversalParameterRing k))).functionField)) := by
    exact Spec.fromSpecStalk_eq' _ _
  rw [hfrom]
  change Spec.map ((CommRingCat.ofHom
      ((MvPolynomial.C : MvPolynomial (Fin 3) k →+* KollarUniversalParameterRing k).comp
        MvPolynomial.C)) ≫ CommRingCat.ofHom
      (algebraMap (KollarUniversalParameterRing k)
        (Spec (.of (KollarUniversalParameterRing k))).functionField)) = _
  exact Spec.map_comp _ _

end AllCharacteristics
