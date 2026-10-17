import PfaffianDescent.IncidenceAmbientCoordinates
import PfaffianDescent.IncidenceSchemeCocycle

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K]

lemma incidenceChartPoint_universal {X : Scheme.{u}} (f : X ⟶ incidenceGraphScheme K) :
    incidenceChartPoint K f = incidenceGraphPointMap (affineFunctionHom f) (incidenceGraphUniversal K) := by
  apply (incidenceGraphPointCoordinates Γ(X, ⊤)).injective
  rw [incidenceChartPoint_coordinates, incidenceGraphPointMap_coordinates, incidenceGraphUniversal_coordinates]
  rfl

/-- The projection from a chosen incidence chart to the original ambient triple. -/
noncomputable def incidenceChartToTriples (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceGraphScheme K ⟶ alternatingTripleScheme K :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (R := K) (incidenceOriginalCoefficients i (incidenceGraphUniversal K))).toRingHom)

lemma incidenceChartToTriples_toBase (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceChartToTriples K i ≫ alternatingTripleToBase K = incidenceGraphToBase K := by
  change Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := K) (incidenceOriginalCoefficients i (incidenceGraphUniversal K))).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (AlternatingTripleRing K))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (MvPolynomial.aeval (R := K) (incidenceOriginalCoefficients i (incidenceGraphUniversal K))).comp_algebraMap

lemma incidenceChartToTriples_coordinates {X : Scheme.{u}}
    (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) (f : X ⟶ incidenceGraphScheme K) (k : AlternatingTripleIndex) :
    affineFunctionHom (f ≫ incidenceChartToTriples K i) (MvPolynomial.X k) =
      incidenceOriginalCoefficients i (incidenceChartPoint K f) k := by
  have h := RingHom.congr_fun (affineFunctionHom_comp_Spec f
    (MvPolynomial.aeval (R := K) (incidenceOriginalCoefficients i (incidenceGraphUniversal K))).toRingHom)
    (MvPolynomial.X k)
  rw [incidenceChartPoint_universal, incidenceOriginalCoefficients_map]
  exact h.trans (congrArg (affineFunctionHom f) (MvPolynomial.aeval_X _ k))

lemma alternatingTriple_morphism_ext {X : Scheme.{u}} (f g : X ⟶ alternatingTripleScheme K)
    (hb : f ≫ alternatingTripleToBase K = g ≫ alternatingTripleToBase K)
    (hc : ∀ k, affineFunctionHom f (MvPolynomial.X k) = affineFunctionHom g (MvPolynomial.X k)) : f = g := by
  apply affineFunctionHom_injective
  apply MvPolynomial.ringHom_ext'
  · have h := congrArg affineFunctionHom hb
    exact (affineFunctionHom_comp_Spec f MvPolynomial.C).symm.trans
      (h.trans (affineFunctionHom_comp_Spec g MvPolynomial.C))
  · exact hc

/-- Overlapping charts give the same original triple on every test scheme. -/
lemma incidenceChartToTriples_overlap {X : Scheme.{u}}
    (i j : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (g : X ⟶ incidenceOverlapScheme K (grassmannianChartChange i j)) :
    (g ≫ incidenceOverlapι K (grassmannianChartChange i j)) ≫ incidenceChartToTriples K i =
      (g ≫ incidenceOverlapOtherι K (grassmannianChartChange i j)) ≫ incidenceChartToTriples K j := by
  apply alternatingTriple_morphism_ext K
  · simp only [Category.assoc, incidenceChartToTriples_toBase, incidenceOverlapOtherι_toBase]
  · intro k
    refine (incidenceChartToTriples_coordinates K i (g ≫ incidenceOverlapι K _) k).trans
      (Eq.trans ?_ (incidenceChartToTriples_coordinates K j (g ≫ incidenceOverlapOtherι K _) k).symm)
    have hp := (incidenceChart_factor_iff K
      (g ≫ incidenceOverlapι K (grassmannianChartChange i j)) (grassmannianChartChange i j)).mp ⟨g, rfl⟩
    rw [incidenceChartPoint_transition K _ g hp]
    exact (incidenceOriginalCoefficients_transition i j _ hp k).symm

end
end PfaffianDescent
