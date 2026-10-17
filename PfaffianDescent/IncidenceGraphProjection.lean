import PfaffianDescent.IncidenceGraphFunctor

namespace PfaffianDescent
open Module AlgebraicGeometry CategoryTheory

/-- The coefficients of three alternating forms on a six-dimensional space. -/
abbrev AlternatingTripleIndex := Fin 3 × Set.powersetCard (Fin 6) 2

noncomputable instance : Fintype AlternatingTripleIndex := Fintype.ofFinite _

lemma alternatingTripleIndex_card : Fintype.card AlternatingTripleIndex = 45 := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (Fin 3 × Set.powersetCard (Fin 6) 2) = 45
  rw [Nat.card_prod, Set.powersetCard.card]
  norm_num [Nat.choose]

universe u
section
variable (K : Type u) [CommRing K]

abbrev AlternatingTripleRing := MvPolynomial AlternatingTripleIndex K

/-- The affine scheme of ordered triples of alternating forms. -/
noncomputable def alternatingTripleScheme : Scheme.{u} := Spec (.of (AlternatingTripleRing K))

noncomputable def alternatingTripleToBase : alternatingTripleScheme K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (AlternatingTripleRing K)))

instance alternatingTripleToBase_smooth : Smooth (alternatingTripleToBase K) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  apply RingHom.smooth_algebraMap.mpr
  change Algebra.Smooth K (MvPolynomial AlternatingTripleIndex K)
  exact ⟨inferInstance, inferInstance⟩

/-- The original-coordinate coefficients of the universal graph-isotropic triple. -/
noncomputable def incidenceGraphTripleCoefficients (j : AlternatingTripleIndex) :
    IncidenceGraphRing K :=
  alternatingCoordinates
    (((Pi.basisFun (IncidenceGraphRing K) (Fin 3)).prod
      (Pi.basisFun (IncidenceGraphRing K) (Fin 3))).reindex finSumFinEquiv)
    ((incidenceGraphUniversal K).2 j.1).1 j.2

/-- Forget the universal graph and retain its triple of alternating forms. -/
noncomputable def incidenceGraphProjection : incidenceGraphScheme K ⟶ alternatingTripleScheme K :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (incidenceGraphTripleCoefficients K)).toRingHom)

lemma incidenceGraphProjection_toBase :
    incidenceGraphProjection K ≫ alternatingTripleToBase K = incidenceGraphToBase K := by
  change Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (incidenceGraphTripleCoefficients K)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (AlternatingTripleRing K))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (MvPolynomial.aeval (incidenceGraphTripleCoefficients K)).comp_algebraMap

end
end PfaffianDescent
