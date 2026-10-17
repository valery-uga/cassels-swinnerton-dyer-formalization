import PfaffianDescent.GoodGraphFiberAlgebraEquiv
import PfaffianDescent.GoodFiberScheme

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [Field K] [NeZero (2 : K)]

/-- The scheme cut out by the full graph restriction equations for the displayed triple. -/
noncomputable def goodGraphFiberScheme : Scheme.{u} := Spec (.of (GoodGraphFiberAlgebra K))

noncomputable def goodGraphFiberToBase : goodGraphFiberScheme K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (GoodGraphFiberAlgebra K)))

noncomputable def goodGraphFiberSchemeIso : goodGraphFiberScheme K ≅ goodFiberScheme K :=
  Scheme.Spec.mapIso (goodGraphFiberEquiv K).symm.toRingEquiv.toCommRingCatIso.op

lemma goodGraphFiberSchemeIso_toBase :
    (goodGraphFiberSchemeIso K).hom ≫ goodFiberToBase K = goodGraphFiberToBase K := by
  change Spec.map (CommRingCat.ofHom (goodGraphFiberEquiv K).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (GoodFiberAlgebra K))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (goodGraphFiberEquiv K).symm.toAlgHom.comp_algebraMap

instance goodGraphFiberToBase_finite : IsFinite (goodGraphFiberToBase K) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

instance goodGraphFiberToBase_etale : Etale (goodGraphFiberToBase K) := by
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  exact RingHom.etale_algebraMap.mpr inferInstance

lemma goodGraphFiberToBase_finrank (x : Spec (.of K)) :
    (goodGraphFiberToBase K).finrank x = 2 := by
  change (Spec.map (CommRingCat.ofHom (algebraMap K (GoodGraphFiberAlgebra K)))).finrank x = 2
  have hr := Scheme.Hom.finrank_SpecMap_algebraMap K (GoodGraphFiberAlgebra K) x
  have hd := congrFun (Module.rankAtStalk_eq_finrank_of_free
    (R := K) (M := GoodGraphFiberAlgebra K)) x
  exact hr.trans (hd.trans (goodGraphFiberAlgebra_finrank K))

/-- Finite étaleness and degree two for the full graph-chart fiber scheme. -/
theorem goodGraphFiber_finite_etale_degree_two :
    IsFinite (goodGraphFiberToBase K) ∧ Etale (goodGraphFiberToBase K) ∧
      ∀ x : Spec (.of K), (goodGraphFiberToBase K).finrank x = 2 :=
  ⟨inferInstance, inferInstance, goodGraphFiberToBase_finrank K⟩

end
end PfaffianDescent
