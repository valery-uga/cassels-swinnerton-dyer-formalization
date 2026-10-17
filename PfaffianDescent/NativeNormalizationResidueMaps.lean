import PfaffianDescent.CorayNormalizationClosedPointNongeneric
import PfaffianDescent.CorayOwnComponentProperConstants
import PfaffianDescent.SchemeModuleOriginalBaseStalkResidueTower
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! Source-only native normalization/residue bridges. The closed lift is
constructed from finite surjective normalization; its residue field is NOT
asserted to agree with the original point's residue field. The maps below
are the actual evaluation, section and residue maps, with their original
base-field algebras. No defect bound is assumed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AllCharacteristics
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Each point above a closed point under a quasi-finite morphism is closed:
the actual fibre is a closed discrete subset of the source. -/
theorem locallyQuasiFinite_closedPoint_above_closedPoint
    {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f]
    (P : closedPoints X) (q : Y) (hq : f q = P.1) : IsClosed ({q} : Set Y) := by
  apply isClosed_of_subset_discrete_closed
    (t := f ⁻¹' ({P.1} : Set X))
  · exact Set.singleton_subset_iff.mpr (Set.mem_singleton_iff.mpr hq)
  · exact f.isDiscrete_preimage_singleton P.1
  · exact P.2.preimage f.continuous

/-- A genuine original closed point has an actual closed point above it on
the canonical finite normalization. If three divides the FULL normalization
constants rank, it divides this actual lifted residue degree. No regularity
or residue-preserving lift is assumed. -/
theorem integralProper_genericNormalization_exists_closedPoint_above_with_three_degree
    {K : Type u} [Field K] [CharZero K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [IsProper pi] (P : closedPoints X) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    3 ∣ Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) →
    ∃ Q : closedPoints N, ν Q.1 = P.1 ∧ 3 ∣ (ν ≫ pi).residueDegree Q.1 := by
  classical
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : IsFinite ν := integralScheme_genericNormalization_isFinite X pi
  letI : IsProper (ν ≫ pi) := inferInstance
  change (3 ∣ Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
    (SheafOfModules.unit N.ringCatSheaf) ⊤)) → _
  intro hthree
  have hsurj : Function.Surjective ν :=
    (integralGenericNormalization_fromNormalization_surjective X).surj
  let q := Classical.choose (hsurj P.1)
  have hq : ν q = P.1 := Classical.choose_spec (hsurj P.1)
  let Q : closedPoints N :=
    ⟨q, locallyQuasiFinite_closedPoint_above_closedPoint ν P q hq⟩
  have hdiv := integralProper_originalUnitSections_finrank_dvd_residueDegree (ν ≫ pi) Q
  exact ⟨Q, hq, dvd_trans hthree hdiv⟩

/-- The actual residue-field map of an original scheme morphism is linear
over the SAME original base. Compatibility is derived from its actual Spec
square and pointAlgebra, not supplied as a scalar-action hypothesis. -/
def originalBaseResidueFieldMapAlgHom
    {K : Type u} [Field K] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (pi : X ⟶ Spec (.of K)) (q : Y) :
    letI := pointAlgebra pi (f q)
    letI := pointAlgebra (f ≫ pi) q
    X.residueField (f q) →ₐ[K] Y.residueField q := by
  letI := pointAlgebra pi (f q)
  letI := pointAlgebra (f ≫ pi) q
  let a := Spec.preimage (X.fromSpecResidueField (f q) ≫ pi)
  let b := Spec.preimage (Y.fromSpecResidueField q ≫ (f ≫ pi))
  have hcat : a ≫ f.residueFieldMap q = b := by
    apply Spec.map_injective
    calc
      Spec.map (a ≫ f.residueFieldMap q) =
          Spec.map (f.residueFieldMap q) ≫ Spec.map a := Spec.map_comp _ _
      _ = Spec.map (f.residueFieldMap q) ≫ (X.fromSpecResidueField (f q) ≫ pi) := by
        rw [Spec.map_preimage]
      _ = Y.fromSpecResidueField q ≫ (f ≫ pi) := by
        rw [← Category.assoc, f.SpecMap_residueFieldMap_fromSpecResidueField q,
          Category.assoc]
      _ = Spec.map b := (Spec.map_preimage _).symm
  refine { toRingHom := (f.residueFieldMap q).hom, commutes' := ?_ }
  intro c
  exact ConcreteCategory.congr_hom hcat c

/-- Original open evaluation as an original-K algebra map. Its scalar
compatibility uses the actual germ/residue tower already proved for pi. -/
def originalOpenResidueEvaluationAlgHom
    {K : Type u} [Field K] {X : Scheme.{u}}
    (pi : X ⟶ Spec (.of K)) (U : X.Opens) (x : X) (hx : x ∈ U) :
    letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
    letI := pointAlgebra pi x
    Γ(X, U) →ₐ[K] X.residueField x := by
  letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
  letI := pointAlgebra pi x
  refine { toRingHom := (X.evaluation U x hx).hom, commutes' := ?_ }
  intro c
  change X.residue x (X.presheaf.germ U x hx (schemeOpenBaseRingHom pi U c)) =
    (Spec.preimage (X.fromSpecResidueField x ≫ pi)).hom c
  rw [schemeStalkBaseRingHom_germ]
  exact congrArg (fun a : K →+* X.residueField x => a c)
    (schemeStalkBaseRingHom_residue pi x)

private theorem originalOpenBaseRingHom_eq_appLE
    {K : Type u} [Field K] {X : Scheme.{u}} (pi : X ⟶ Spec (.of K)) (U : X.Opens) :
    CommRingCat.ofHom (schemeOpenBaseRingHom pi U) =
      (Scheme.ΓSpecIso (.of K)).inv ≫ pi.appLE ⊤ U (by simp) := by
  change ((Scheme.ΓSpecIso (.of K)).inv ≫ pi.appTop) ≫
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op = _
  exact Category.assoc _ _ _

/-- Actual section pullback preserves the ORIGINAL base constants on
every actual open. This identifies the independent pi and f>>pi actions. -/
theorem originalOpenBaseRingHom_section_naturality
    {K : Type u} [Field K] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (pi : X ⟶ Spec (.of K)) (U : X.Opens) (c : K) :
    f.app U (schemeOpenBaseRingHom pi U c) =
      schemeOpenBaseRingHom (f ≫ pi) (f ⁻¹ᵁ U) c := by
  have hcat : CommRingCat.ofHom (schemeOpenBaseRingHom pi U) ≫ f.app U =
      CommRingCat.ofHom (schemeOpenBaseRingHom (f ≫ pi) (f ⁻¹ᵁ U)) := by
    rw [originalOpenBaseRingHom_eq_appLE, originalOpenBaseRingHom_eq_appLE,
      Category.assoc, f.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact ConcreteCategory.congr_hom hcat c

/-- The native section pullback, with both ORIGINAL base-field algebras.
No replacement scalar structure is used on the normalization sections. -/
def originalOpenSectionPullbackAlgHom
    {K : Type u} [Field K] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (pi : X ⟶ Spec (.of K)) (U : X.Opens) :
    letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
    letI : Algebra K Γ(Y, f ⁻¹ᵁ U) := (schemeOpenBaseRingHom (f ≫ pi) (f ⁻¹ᵁ U)).toAlgebra
    Γ(X, U) →ₐ[K] Γ(Y, f ⁻¹ᵁ U) := by
  letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
  letI : Algebra K Γ(Y, f ⁻¹ᵁ U) := (schemeOpenBaseRingHom (f ≫ pi) (f ⁻¹ᵁ U)).toAlgebra
  exact
    { toRingHom := (f.app U).hom
      commutes' := originalOpenBaseRingHom_section_naturality f pi U }

/-- The original evaluation/residue/normalization-section square commutes
as a square of ORIGINAL-K algebra maps. -/
theorem originalOpenEvaluation_residue_section_square
    {K : Type u} [Field K] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (pi : X ⟶ Spec (.of K)) (U : X.Opens) (q : Y) (hq : f q ∈ U) :
    letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
    letI : Algebra K Γ(Y, f ⁻¹ᵁ U) := (schemeOpenBaseRingHom (f ≫ pi) (f ⁻¹ᵁ U)).toAlgebra
    letI := pointAlgebra pi (f q)
    letI := pointAlgebra (f ≫ pi) q
    (originalOpenResidueEvaluationAlgHom (f ≫ pi) (f ⁻¹ᵁ U) q hq).comp
        (originalOpenSectionPullbackAlgHom f pi U) =
      (originalBaseResidueFieldMapAlgHom f pi q).comp
        (originalOpenResidueEvaluationAlgHom pi U (f q) hq) := by
  letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
  letI : Algebra K Γ(Y, f ⁻¹ᵁ U) := (schemeOpenBaseRingHom (f ≫ pi) (f ⁻¹ᵁ U)).toAlgebra
  letI := pointAlgebra pi (f q)
  letI := pointAlgebra (f ≫ pi) q
  ext s
  exact (Scheme.evaluation_naturality_apply f q hq s).symm

end PfaffianDescent.Coray
