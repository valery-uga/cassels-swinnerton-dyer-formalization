import AllCharacteristics.ClosedPointRank

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

section
variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The ground-field map on the residue field, extracted from the actual structure morphism. -/
noncomputable def closedPointBaseHom (f : X ⟶ Spec (.of K)) (x : closedPoints X) :
    K →+* X.residueField x.val :=
  (Spec.preimage (X.fromSpecResidueField x.val ≫ f)).hom

theorem closedPointBaseHom_spec (f : X ⟶ Spec (.of K)) (x : closedPoints X) :
    Spec.map (CommRingCat.ofHom (closedPointBaseHom f x)) = X.fromSpecResidueField x.val ≫ f :=
  Spec.map_preimage _

/-- A closed point of a scheme locally of finite type gives the finite field extension
of precisely its scheme-theoretic residue degree. -/
theorem closedPoint_field_degree (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (x : closedPoints X) :
    letI : Algebra K (X.residueField x.val) := (closedPointBaseHom f x).toAlgebra
    FiniteDimensional K (X.residueField x.val) ∧
      Module.finrank K (X.residueField x.val) = f.residueDegree x.val := by
  letI : Algebra K (X.residueField x.val) := (closedPointBaseHom f x).toAlgebra
  let b := CommRingCat.ofHom (closedPointBaseHom f x)
  have hg : Spec.map b = X.fromSpecResidueField x.val ≫ f := closedPointBaseHom_spec f x
  have hfinite : IsFinite (Spec.map b) := by rw [hg]; infer_instance
  have hfin : b.hom.Finite := (IsFinite.SpecMap_iff b).mp hfinite
  haveI : FiniteDimensional K (X.residueField x.val) := hfin
  refine ⟨inferInstance, ?_⟩
  have hr : (Spec.map b).finrank (IsLocalRing.closedPoint K) =
      Module.finrank K (X.residueField x.val) := by
    change (Spec.map (CommRingCat.ofHom (algebraMap K (X.residueField x.val)))).finrank _ = _
    rw [Scheme.Hom.finrank_SpecMap_algebraMap]
    exact congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := X.residueField x.val)) _
  calc
    Module.finrank K (X.residueField x.val) = (Spec.map b).finrank (IsLocalRing.closedPoint K) := hr.symm
    _ = (X.fromSpecResidueField x.val ≫ f).finrank (IsLocalRing.closedPoint K) := by rw [hg]
    _ = AllCharacteristics.finiteSchemeRank (X.fromSpecResidueField x.val ≫ f) :=
      (AllCharacteristics.finiteSchemeRank_eq_finrank _).symm
    _ = f.residueDegree x.val := AllCharacteristics.closedPoint_finiteSchemeRank_eq_residueDegree f x

end
end PfaffianDescent
