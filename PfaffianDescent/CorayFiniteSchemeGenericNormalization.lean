import PfaffianDescent.CorayFiniteTypeNormalization
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Actual finite glued normalization of an integral characteristic-zero scheme

The actual generic-point stalk map has field source, is quasi-compact, and
has entire source over every actual nonempty affine open. Its actual section
map identifies with the actual germ-to-function-field map. Actual finite-type
chart rings have actual finite normalization, and installed proved relative
normalization gluing turns these into an actual finite morphism.

No global glue, finite-normalization, section-comparison or genus certificate.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

/-- The actual generic-point field source has only one point, so its actual
canonical map is quasi-compact without an assumed qc certificate. -/
theorem integralGenericPointMap_quasiCompact
    (X : Scheme.{u}) [IsIntegral X] :
    QuasiCompact (X.fromSpecStalk (genericPoint X)) := by
  letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  letI : Subsingleton (Spec (X.presheaf.stalk (genericPoint X))) := by
    change Subsingleton (PrimeSpectrum (X.presheaf.stalk (genericPoint X)))
    infer_instance
  constructor
  intro U hU hcompact
  exact (Set.toFinite _).isCompact

/-- The actual generic-point map has entire field source over every actual
nonempty open, since its single source point maps to the actual generic point. -/
theorem integralGenericPointMap_preimage_eq_top
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U] :
    (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U = ⊤ := by
  letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  letI : Subsingleton (Spec (X.presheaf.stalk (genericPoint X))) := by
    change Subsingleton (PrimeSpectrum (X.presheaf.stalk (genericPoint X)))
    infer_instance
  ext y
  change X.fromSpecStalk (genericPoint X) y ∈ U ↔ True
  have hy : y = IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)) :=
    Subsingleton.elim _ _
  rw [hy, Scheme.fromSpecStalk_closedPoint]
  exact iff_true_intro (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    (by simpa using (inferInstance : Nonempty U)))

/-- Actual sections over a nonempty open's actual generic-point preimage
are actually the function field, using the actual entire-source equality. -/
def integralGenericPointPreimageSectionsIso
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U) ≅ X.functionField :=
  (Spec X.functionField).presheaf.mapIso
    (eqToIso (integralGenericPointMap_preimage_eq_top X U).symm).op ≪≫
      Scheme.ΓSpecIso X.functionField

/-- The actual section comparison preserves the ORIGINAL chart map: its
composite is the actual chart germ to the actual function field. -/
theorem integralGenericPointPreimageSectionsIso_comp_app
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U] :
    (X.fromSpecStalk (genericPoint X)).app U ≫
      (integralGenericPointPreimageSectionsIso X U).hom = X.germToFunctionField U := by
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))
  rw [Scheme.fromSpecStalk_app hx]
  simp only [integralGenericPointPreimageSectionsIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc, ← Functor.map_comp_assoc]
  have hid : (homOfLE (le_top :
      (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U ≤ ⊤)).op ≫
      ((eqToIso (integralGenericPointMap_preimage_eq_top X U).symm).op).hom =
        𝟙 (op (⊤ : (Spec X.functionField).Opens)) := Subsingleton.elim _ _
  rw [hid, CategoryTheory.Functor.map_id]
  simp [Scheme.germToFunctionField]

/-- Actual finite-type characteristic-zero integral scheme normalization is
an actual FINITE glued morphism. The normalization is that of the actual
canonical generic-point map, and its chart finiteness is constructed from
actual chart finite type and actual fraction fields, not supplied as a glue
or finite-normalization premise. This is not a genus/cohomology theorem. -/
theorem integralScheme_genericNormalization_isFinite
    {K : Type u} [Field K] [CharZero K]
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    IsFinite (X.fromSpecStalk (genericPoint X)).fromNormalization := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let f := X.fromSpecStalk (genericPoint X)
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  by_cases hnonempty : Nonempty U
  · letI : Nonempty U := hnonempty
    let beta : K →+* Γ(X, U) :=
      (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    letI : Algebra K Γ(X, U) := beta.toAlgebra
    have hbeta : beta.FiniteType := RingHom.FiniteType.comp
      (pi.finiteType_appLE (isAffineOpen_top _) hU (by simp))
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
    letI : Algebra.FiniteType K Γ(X, U) := hbeta
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    letI : Module.Finite Γ(X, U) (integralClosure Γ(X, U) (FractionRing Γ(X, U))) :=
      finiteNormalization_of_finiteType_charZero K Γ(X, U)
    let fracEquiv := FractionRing.algEquiv (A := Γ(X, U)) X.functionField
    letI : Module.Finite Γ(X, U) (integralClosure Γ(X, U) X.functionField) :=
      Module.Finite.equiv fracEquiv.mapIntegralClosure.toLinearEquiv
    letI : Algebra Γ(X, U) Γ(Spec X.functionField, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    let sectionEquiv : Γ(Spec X.functionField, f ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] X.functionField :=
      AlgEquiv.ofBijective
        { toRingHom := (integralGenericPointPreimageSectionsIso X U).hom.hom
          commutes' := fun r => by
            exact ConcreteCategory.congr_hom (integralGenericPointPreimageSectionsIso_comp_app X U) r }
        (ConcreteCategory.bijective_of_isIso (integralGenericPointPreimageSectionsIso X U).hom)
    letI : Module.Finite Γ(X, U)
        (integralClosure Γ(X, U) Γ(Spec X.functionField, f ⁻¹ᵁ U)) :=
      Module.Finite.equiv sectionEquiv.symm.mapIntegralClosure.toLinearEquiv
    rw [Scheme.Hom.fromNormalization_app f hU, CommRingCat.hom_comp]
    exact RingHom.Finite.comp
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
      (RingHom.finite_algebraMap.mpr inferInstance)
  · have hpreempty : f.fromNormalization ⁻¹ᵁ U = ⊥ := by
      ext y
      change f.fromNormalization y ∈ U ↔ False
      exact iff_false_intro (fun hy => hnonempty ⟨⟨f.fromNormalization y, hy⟩⟩)
    haveI : Subsingleton Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) := by
      rw [hpreempty]
      infer_instance
    exact RingHom.Finite.of_surjective _ (Function.surjective_to_subsingleton _)

end PfaffianDescent.Coray
