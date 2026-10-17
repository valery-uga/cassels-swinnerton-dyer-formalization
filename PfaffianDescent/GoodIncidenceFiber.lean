import PfaffianDescent.GoodIncidenceFieldPoints
import PfaffianDescent.GoodChartFiberCartesian
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [Field K] [NeZero (2 : K)]

/-- The computed open graph chart covers every point of the actual good fiber. -/
theorem goodGraphFiberToGlobalFiber_surjective : Function.Surjective (goodGraphFiberToGlobalFiber K) := by
  intro x
  let L : Type u := (goodIncidenceFiber K).residueField x
  let z : Spec (.of L) ⟶ goodIncidenceFiber K := (goodIncidenceFiber K).fromSpecResidueField x
  let ψ : K →+* L := (Spec.preimage (z ≫ goodIncidenceFiberToBase K)).hom
  letI : Algebra K L := ψ.toAlgebra
  have hz : Spec.map (CommRingCat.ofHom (algebraMap K L)) = z ≫ goodIncidenceFiberToBase K :=
    Spec.map_preimage _
  let f : Spec (.of L) ⟶ incidenceScheme K :=
    z ≫ pullback.fst (incidenceToTriples K) (goodTripleSection K)
  have ht : f ≫ incidenceToTriples K =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ goodTripleSection K := by
    calc
      f ≫ incidenceToTriples K = z ≫
          (pullback.fst (incidenceToTriples K) (goodTripleSection K) ≫ incidenceToTriples K) :=
        Category.assoc _ _ _
      _ = z ≫ (goodIncidenceFiberToBase K ≫ goodTripleSection K) :=
        congrArg (fun t => z ≫ t) pullback.condition
      _ = (z ≫ goodIncidenceFiberToBase K) ≫ goodTripleSection K := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun t => t ≫ goodTripleSection K) hz.symm
  obtain ⟨g, hg⟩ := goodIncidence_field_factor K f ht
  let hP := goodGraphFiber_global_chart_isPullback K
  let q : Spec (.of L) ⟶ goodGraphFiberScheme K := hP.lift z g hg.symm
  refine ⟨q (IsLocalRing.closedPoint L), ?_⟩
  have hq : q ≫ goodGraphFiberToGlobalFiber K = z := hP.lift_fst z g hg.symm
  exact (congrArg (fun t : Spec (.of L) ⟶ goodIncidenceFiber K => t (IsLocalRing.closedPoint L)) hq).trans
    ((goodIncidenceFiber K).fromSpecResidueField_apply x (IsLocalRing.closedPoint L))

instance goodGraphFiberToGlobalFiber_isIso : IsIso (goodGraphFiberToGlobalFiber K) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply TopologicalSpace.Opens.ext
  exact Set.range_eq_univ.mpr (goodGraphFiberToGlobalFiber_surjective K)

/-- The entire scheme-theoretic good fiber is the computed graph-fiber scheme. -/
noncomputable def goodIncidenceFiberIso : goodIncidenceFiber K ≅ goodGraphFiberScheme K :=
  (asIso (goodGraphFiberToGlobalFiber K)).symm

lemma goodIncidenceFiberIso_toBase :
    (goodIncidenceFiberIso K).hom ≫ goodGraphFiberToBase K = goodIncidenceFiberToBase K := by
  apply (asIso (goodGraphFiberToGlobalFiber K)).inv_comp_eq.mpr
  exact (goodGraphFiberToGlobalFiber_toBase K).symm

instance goodIncidenceFiberToBase_finite : IsFinite (goodIncidenceFiberToBase K) := by
  have h : IsFinite ((goodIncidenceFiberIso K).hom ≫ goodGraphFiberToBase K) := inferInstance
  exact goodIncidenceFiberIso_toBase K ▸ h

instance goodIncidenceFiberToBase_etale : Etale (goodIncidenceFiberToBase K) := by
  have h : Etale ((goodIncidenceFiberIso K).hom ≫ goodGraphFiberToBase K) := inferInstance
  exact goodIncidenceFiberIso_toBase K ▸ h

lemma goodIncidenceFiberToBase_finrank (x : Spec (.of K)) : (goodIncidenceFiberToBase K).finrank x = 2 := by
  have he := congrArg (fun f : goodIncidenceFiber K ⟶ Spec (.of K) => f.finrank x)
    (goodIncidenceFiberIso_toBase K)
  rw [Scheme.Hom.finrank_comp_left_of_isIso] at he
  exact he.symm.trans (goodGraphFiberToBase_finrank K x)

/-- The actual full incidence fiber over the displayed rational triple is finite étale of degree two. -/
theorem goodIncidenceFiber_finite_etale_degree_two :
    IsFinite (goodIncidenceFiberToBase K) ∧ Etale (goodIncidenceFiberToBase K) ∧
      ∀ x : Spec (.of K), (goodIncidenceFiberToBase K).finrank x = 2 :=
  ⟨inferInstance, inferInstance, goodIncidenceFiberToBase_finrank K⟩

end
end PfaffianDescent
