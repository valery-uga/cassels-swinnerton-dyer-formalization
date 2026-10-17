import PfaffianDescent.GoodFiberGlobalMap
import PfaffianDescent.GoodChartIncidencePoints

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A] {X : Scheme.{u}}

lemma incidenceChartEvaluation_point (g : X ⟶ Spec (.of A)) (p : IncidenceGraphPoints A) :
    incidenceChartPoint K (g ≫ incidenceChartEvaluation K p) =
      incidenceGraphPointMap (affineFunctionHom g) p := by
  apply (incidenceGraphPointCoordinates Γ(X, ⊤)).injective
  rw [incidenceChartPoint_coordinates, incidenceGraphPointMap_coordinates]
  funext j
  exact (RingHom.congr_fun (affineFunctionHom_comp_Spec g
    (MvPolynomial.aeval (R := K) (incidenceGraphPointCoordinates A p)).toRingHom)
    (MvPolynomial.X j)).trans (congrArg (affineFunctionHom g) (MvPolynomial.aeval_X _ j))

lemma goodChart_morphism_coefficients (f : X ⟶ incidenceGraphScheme K) (g : X ⟶ Spec (.of K))
    (h : f ≫ incidenceChartToTriples K goodChartPermutation = g ≫ goodTripleSection K) :
    incidenceOriginalCoefficients goodChartPermutation (incidenceChartPoint K f) =
      goodTripleSchemeCoefficients Γ(X, ⊤) := by
  funext j
  have he := congrArg (fun t => affineFunctionHom t (MvPolynomial.X j)) h
  have he' := (incidenceChartToTriples_coordinates K goodChartPermutation f j).symm.trans he
  have hg := RingHom.congr_fun (affineFunctionHom_comp_Spec g
    (MvPolynomial.aeval (R := K) (goodTripleSchemeCoefficients K)).toRingHom) (MvPolynomial.X j)
  have hg' := hg.trans (congrArg (affineFunctionHom g) (MvPolynomial.aeval_X _ j))
  exact he'.trans (hg'.trans (goodTripleSchemeCoefficients_map (affineFunctionHom g) j).symm)

end
section
variable (K : Type u) [Field K] [NeZero (2 : K)] {X : Scheme.{u}}

/-- Recover the graph-fiber morphism from any test-scheme incidence morphism over the displayed triple. -/
noncomputable def goodChartFiberLift (f : X ⟶ incidenceGraphScheme K) (g : X ⟶ Spec (.of K))
    (h : f ≫ incidenceChartToTriples K goodChartPermutation = g ≫ goodTripleSection K) :
    X ⟶ goodGraphFiberScheme K :=
  letI : Algebra K Γ(X, ⊤) := (affineFunctionHom g).toAlgebra
  morphismFromAffineFunctions X
    (goodChartIncidenceLift K (incidenceChartPoint K f) (goodChart_morphism_coefficients K f g h)).toRingHom

lemma goodChartFiberLift_toBase (f : X ⟶ incidenceGraphScheme K) (g : X ⟶ Spec (.of K))
    (h : f ≫ incidenceChartToTriples K goodChartPermutation = g ≫ goodTripleSection K) :
    goodChartFiberLift K f g h ≫ goodGraphFiberToBase K = g := by
  letI : Algebra K Γ(X, ⊤) := (affineFunctionHom g).toAlgebra
  let φ : GoodGraphFiberAlgebra K →ₐ[K] Γ(X, ⊤) :=
    goodChartIncidenceLift K (incidenceChartPoint K f) (goodChart_morphism_coefficients K f g h)
  change morphismFromAffineFunctions X φ.toRingHom ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (GoodGraphFiberAlgebra K))) = g
  rw [morphismFromAffineFunctions_comp_Spec]
  have he : φ.toRingHom.comp (algebraMap K (GoodGraphFiberAlgebra K)) = affineFunctionHom g :=
    φ.comp_algebraMap
  rw [he, from_affineFunctionHom]

lemma goodChartFiberLift_point (f : X ⟶ incidenceGraphScheme K) (g : X ⟶ Spec (.of K))
    (h : f ≫ incidenceChartToTriples K goodChartPermutation = g ≫ goodTripleSection K) :
    incidenceChartPoint K (goodChartFiberLift K f g h ≫ goodGraphFiberToIncidenceChart K) =
      incidenceChartPoint K f := by
  letI : Algebra K Γ(X, ⊤) := (affineFunctionHom g).toAlgebra
  let φ : GoodGraphFiberAlgebra K →ₐ[K] Γ(X, ⊤) :=
    goodChartIncidenceLift K (incidenceChartPoint K f) (goodChart_morphism_coefficients K f g h)
  change incidenceChartPoint K (morphismFromAffineFunctions X φ.toRingHom ≫
    incidenceChartEvaluation K (goodGraphFiberIncidencePoint K)) = incidenceChartPoint K f
  rw [incidenceChartEvaluation_point, affineFunctionHom_from]
  exact goodChartIncidenceLift_recovers K (incidenceChartPoint K f) _

lemma goodGraphFiberToIncidenceChart_toBase :
    goodGraphFiberToIncidenceChart K ≫ incidenceGraphToBase K = goodGraphFiberToBase K :=
  incidenceChartEvaluation_toBase K (goodGraphFiberIncidencePoint K)

/-- Recovery holds as equality of actual scheme morphisms, for arbitrary test schemes. -/
lemma goodChartFiberLift_toChart (f : X ⟶ incidenceGraphScheme K) (g : X ⟶ Spec (.of K))
    (h : f ≫ incidenceChartToTriples K goodChartPermutation = g ≫ goodTripleSection K) :
    goodChartFiberLift K f g h ≫ goodGraphFiberToIncidenceChart K = f := by
  have hb : f ≫ incidenceGraphToBase K = g := by
    have he := congrArg (fun t => t ≫ alternatingTripleToBase K) h
    simpa only [Category.assoc, incidenceChartToTriples_toBase,
      goodTripleSection_toBase, Category.comp_id] using he
  apply incidenceChart_morphism_ext K
  · calc
      (goodChartFiberLift K f g h ≫ goodGraphFiberToIncidenceChart K) ≫ incidenceGraphToBase K =
          goodChartFiberLift K f g h ≫ goodGraphFiberToBase K := by
            rw [Category.assoc, goodGraphFiberToIncidenceChart_toBase]
      _ = g := goodChartFiberLift_toBase K f g h
      _ = f ≫ incidenceGraphToBase K := hb.symm
  · exact goodChartFiberLift_point K f g h

end
end PfaffianDescent
