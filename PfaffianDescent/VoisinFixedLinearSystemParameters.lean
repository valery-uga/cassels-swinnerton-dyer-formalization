import PfaffianDescent.ProjectiveLinearSystem
import PfaffianDescent.SchemeModuleGlobalSections
import Mathlib.LinearAlgebra.TensorProduct.Free

/-!
# Projective parameter spaces of finite-dimensional section systems

For a finite-dimensional vector space `V`, its nonzero vectors modulo scalar
are parametrized by projective space on a chosen finite basis.  This file
constructs that scheme in the form used by the homogeneous-projective API,
proves its structure morphism proper, and associates a field-valued
parameter to every nonzero vector.  It is then specialized to the literal
global sections of a scheme module.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct

universe u

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective parameter scheme of lines in a finite-dimensional vector
space, expressed using coordinates in `Module.finBasis`. -/
noncomputable abbrev finiteDimensionalProjectiveParameters
    (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Scheme.{u} :=
  projectiveLinearSystemParameters
    (K := K) (τ := Fin (Module.finrank K V))

/-- The structure morphism of the projective parameter scheme. -/
noncomputable def finiteDimensionalProjectiveParametersToBase
    (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] :
    finiteDimensionalProjectiveParameters K V ⟶ Spec (.of K) :=
  toBase (⊥ : HomogeneousIdeal
    (MvPolynomial.homogeneousSubmodule (Fin (Module.finrank K V)) K))

/-- Projective space on a finite-dimensional vector space is proper over the
coefficient field. -/
instance finiteDimensionalProjectiveParametersToBase_isProper
    (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] :
    IsProper (finiteDimensionalProjectiveParametersToBase K V) := by
  unfold finiteDimensionalProjectiveParametersToBase
  infer_instance

/-- Coordinates of a vector in the chosen finite basis. -/
noncomputable def finiteDimensionalProjectiveCoordinates
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] :
    V ≃ₗ[K] (Fin (Module.finrank K V) → K) :=
  (Module.finBasis K V).equivFun

/-- The chosen projective coordinates of a nonzero vector are nonzero. -/
theorem finiteDimensionalProjectiveCoordinates_ne_zero
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (v : V) (hv : v ≠ 0) :
    finiteDimensionalProjectiveCoordinates (K := K) (V := V) v ≠ 0 :=
  finiteDimensionalProjectiveCoordinates.map_ne_zero_iff.mpr hv

/-- Every nonzero vector defines a rational point of its projective parameter
scheme over the coefficient field. -/
theorem exists_finiteDimensionalProjectiveParameter_of_ne_zero
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (v : V) (hv : v ≠ 0) :
    ∃ t : Spec (.of K) ⟶ finiteDimensionalProjectiveParameters K V,
      t ≫ finiteDimensionalProjectiveParametersToBase K V =
        Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
  exact exists_projectiveLinearSystemParameter_of_nonzero_coordinates
    (RingHom.id K)
    (finiteDimensionalProjectiveCoordinates (K := K) (V := V) v)
    (finiteDimensionalProjectiveCoordinates_ne_zero v hv)

/-- Coordinates of a scalar-extended vector in the base change of a
finite-dimensional vector space.  These are the coordinates used by the
same ground-field projective parameter space at an extension-field point. -/
noncomputable def finiteDimensionalScalarExtensionCoordinates
    (K L V : Type u) [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    (L ⊗[K] V) ≃ₗ[L] (Fin (Module.finrank K V) → L) :=
  Algebra.TensorProduct.equivPiOfFiniteBasis L (Module.finBasis K V)

/-- A nonzero scalar-extended vector has a nonzero coordinate vector. -/
theorem finiteDimensionalScalarExtensionCoordinates_ne_zero
    {K L V : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (v : L ⊗[K] V) (hv : v ≠ 0) :
    finiteDimensionalScalarExtensionCoordinates K L V v ≠ 0 :=
  (finiteDimensionalScalarExtensionCoordinates K L V).map_ne_zero_iff.mpr hv

/-- On a pure tensor, the chosen scalar-extension coordinates are obtained by
mapping the ground coordinates to the extension field and multiplying by the
scalar.  This is the coordinate compatibility needed when a descended global
section is evaluated after base change. -/
theorem finiteDimensionalScalarExtensionCoordinates_tmul
    {K L V : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (l : L) (v : V) (i : Fin (Module.finrank K V)) :
    finiteDimensionalScalarExtensionCoordinates K L V (l ⊗ₜ[K] v) i =
      l * algebraMap K L
        (finiteDimensionalProjectiveCoordinates (K := K) (V := V) v i) := by
  simp [finiteDimensionalScalarExtensionCoordinates,
    Algebra.TensorProduct.equivPiOfFiniteBasis,
    finiteDimensionalProjectiveCoordinates, Algebra.smul_def, mul_comm]

/-- Evaluation of a scalar-extended vector is the finite linear combination
of the evaluations of the chosen ground basis, with coefficients given by its
projective coordinate vector.  Thus a global-sections base-change isomorphism
only has to identify the geometric evaluation map; all subsequent coordinate
vanishing is ordinary finite-dimensional linear algebra. -/
theorem liftBaseChange_eq_sum_scalarExtensionCoordinates
    {K L V : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (phi : V →ₗ[K] L) (v : L ⊗[K] V) :
    LinearMap.liftBaseChange L phi v =
      ∑ i : Fin (Module.finrank K V),
        finiteDimensionalScalarExtensionCoordinates K L V v i *
          phi ((Module.finBasis K V) i) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp [map_add, hx, hy, Finset.sum_add_distrib, add_mul]
  | tmul l x =>
      rw [LinearMap.liftBaseChange_tmul]
      simp only [finiteDimensionalScalarExtensionCoordinates,
        Algebra.TensorProduct.equivPiOfFiniteBasis,
        LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
        TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul]
      have hx := congrArg phi ((Module.finBasis K V).sum_equivFun x)
      simp only [map_sum, LinearMap.map_smul_of_tower] at hx
      rw [← hx]
      simp [Finset.mul_sum, Algebra.smul_def, mul_assoc, mul_comm]

/-- Vanishing after scalar extension is equivalent to vanishing of the
coordinate combination of ground-basis evaluations. -/
theorem liftBaseChange_eq_zero_iff_sum_scalarExtensionCoordinates_eq_zero
    {K L V : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (phi : V →ₗ[K] L) (v : L ⊗[K] V) :
    LinearMap.liftBaseChange L phi v = 0 ↔
      (∑ i : Fin (Module.finrank K V),
        finiteDimensionalScalarExtensionCoordinates K L V v i *
          phi ((Module.finBasis K V) i)) = 0 := by
  rw [liftBaseChange_eq_sum_scalarExtensionCoordinates]

/-- Compatibility of a geometric evaluation map with a supplied
global-sections base-change isomorphism turns geometric vanishing into the
coordinate equation for the corresponding ground projective linear system. -/
theorem sum_scalarExtensionCoordinates_eq_zero_of_baseChangeEquiv_evaluation_eq_zero
    {K L V W : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module L W]
    (e : (L ⊗[K] V) ≃ₗ[L] W)
    (groundEvaluation : V →ₗ[K] L)
    (geometricEvaluation : W →ₗ[L] L)
    (hcompat : geometricEvaluation.comp e.toLinearMap =
      LinearMap.liftBaseChange L groundEvaluation)
    (s : W) (hs : geometricEvaluation s = 0) :
    (∑ i : Fin (Module.finrank K V),
      finiteDimensionalScalarExtensionCoordinates K L V (e.symm s) i *
        groundEvaluation ((Module.finBasis K V) i)) = 0 := by
  rw [← liftBaseChange_eq_zero_iff_sum_scalarExtensionCoordinates_eq_zero]
  rw [← hcompat]
  simpa using hs

/-- Two evaluations on a scalar extension agree once they agree on the
scalar-extended chosen finite basis.  This replaces a global naturality
identity by the finitely many literal pullback-section identities needed in
the fixed-divisor application. -/
theorem baseChangeEquiv_evaluation_comp_eq_liftBaseChange_of_finBasis
    {K L V W : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module L W]
    (e : (L ⊗[K] V) ≃ₗ[L] W)
    (groundEvaluation : V →ₗ[K] L)
    (geometricEvaluation : W →ₗ[L] L)
    (hbasis : ∀ i : Fin (Module.finrank K V),
      geometricEvaluation
          (e (1 ⊗ₜ[K] (Module.finBasis K V) i)) =
        groundEvaluation ((Module.finBasis K V) i)) :
    geometricEvaluation.comp e.toLinearMap =
      LinearMap.liftBaseChange L groundEvaluation := by
  apply (Module.finBasis K V).baseChange L |>.ext
  intro i
  rw [Module.Basis.baseChange_apply]
  simpa using hbasis i

/-- A nonzero member of a scalar-extended finite-dimensional vector space
defines an extension-field point of the original ground-field projective
space.  This is the parameter-space part of global-sections base change. -/
theorem exists_finiteDimensionalProjectiveParameter_of_scalarExtension_ne_zero
    {K L V : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (v : L ⊗[K] V) (hv : v ≠ 0) :
    ∃ t : Spec (.of L) ⟶ finiteDimensionalProjectiveParameters K V,
      t ≫ finiteDimensionalProjectiveParametersToBase K V =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  exact exists_projectiveLinearSystemParameter_of_nonzero_coordinates
    (algebraMap K L)
    (finiteDimensionalScalarExtensionCoordinates K L V v)
    (finiteDimensionalScalarExtensionCoordinates_ne_zero v hv)

/-- A nonzero section in any vector space identified with the scalar extension
of a ground space defines a point of the ground projective parameter scheme.
This is the form directly supplied by a global-sections base-change
isomorphism. -/
theorem exists_finiteDimensionalProjectiveParameter_of_baseChangeEquiv_ne_zero
    {K L V W : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module L W]
    (e : (L ⊗[K] V) ≃ₗ[L] W) (s : W) (hs : s ≠ 0) :
    ∃ t : Spec (.of L) ⟶ finiteDimensionalProjectiveParameters K V,
      t ≫ finiteDimensionalProjectiveParametersToBase K V =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  exact exists_finiteDimensionalProjectiveParameter_of_scalarExtension_ne_zero
    (e.symm s) (e.symm.map_ne_zero_iff.mpr hs)

/-- Projective parameter scheme of nonzero global sections of a scheme
module. -/
noncomputable abbrev schemeModuleGlobalSectionsProjectiveParameters
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)] : Scheme.{u} :=
  finiteDimensionalProjectiveParameters K
    (SchemeModuleGlobalSectionsOver base M)

/-- Structure morphism of the projective space of global sections. -/
noncomputable def schemeModuleGlobalSectionsProjectiveParametersToBase
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)] :
    schemeModuleGlobalSectionsProjectiveParameters base M ⟶ Spec (.of K) :=
  finiteDimensionalProjectiveParametersToBase K
    (SchemeModuleGlobalSectionsOver base M)

instance schemeModuleGlobalSectionsProjectiveParametersToBase_isProper
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)] :
    IsProper (schemeModuleGlobalSectionsProjectiveParametersToBase base M) := by
  unfold schemeModuleGlobalSectionsProjectiveParametersToBase
  infer_instance

/-- A nonzero genuine global section gives a rational point of the proper
projective section parameter scheme. -/
theorem exists_schemeModuleGlobalSection_projectiveParameter
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (s : SchemeModuleGlobalSectionsOver base M) (hs : s ≠ 0) :
    ∃ t : Spec (.of K) ⟶
        schemeModuleGlobalSectionsProjectiveParameters base M,
      t ≫ schemeModuleGlobalSectionsProjectiveParametersToBase base M =
        Spec.map (CommRingCat.ofHom (RingHom.id K)) :=
  exists_finiteDimensionalProjectiveParameter_of_ne_zero s hs

/-- A nonzero element of the scalar extension of the ground global-section
space gives an extension-field point of its ground projective parameter
scheme.  No descent of the section itself is required at this stage. -/
theorem exists_schemeModuleGlobalSection_projectiveParameter_of_scalarExtension_ne_zero
    {K L : Type u} [Field K] [Field L] [Algebra K L] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (s : L ⊗[K] SchemeModuleGlobalSectionsOver base M) (hs : s ≠ 0) :
    ∃ t : Spec (.of L) ⟶
        schemeModuleGlobalSectionsProjectiveParameters base M,
      t ≫ schemeModuleGlobalSectionsProjectiveParametersToBase base M =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
  exists_finiteDimensionalProjectiveParameter_of_scalarExtension_ne_zero s hs

end

end PfaffianDescent
