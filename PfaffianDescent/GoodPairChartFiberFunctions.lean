import PfaffianDescent.GoodPairFiberGlobalMap
import PfaffianDescent.GoodChartFiberFunctions
import PfaffianDescent.GoodPairChartIncidencePoints

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A] {X : Scheme.{u}}

lemma goodPairChart_morphism_coefficients (f : X ⟶ incidenceGraphScheme K) (g : X ⟶ Spec (.of K))
    (h : f ≫ incidenceChartToTriples K goodChartPermutation = g ≫ goodPairTripleSection K) :
    incidenceOriginalCoefficients goodChartPermutation (incidenceChartPoint K f) =
      goodPairTripleSchemeCoefficients Γ(X, ⊤) := by
  funext j
  have he := congrArg (fun t => affineFunctionHom t (MvPolynomial.X j)) h
  have he' := (incidenceChartToTriples_coordinates K goodChartPermutation f j).symm.trans he
  have hg := RingHom.congr_fun (affineFunctionHom_comp_Spec g
    (MvPolynomial.aeval (R := K) (goodPairTripleSchemeCoefficients K)).toRingHom) (MvPolynomial.X j)
  have hg' := hg.trans (congrArg (affineFunctionHom g) (MvPolynomial.aeval_X _ j))
  exact he'.trans (hg'.trans (goodPairTripleSchemeCoefficients_map (affineFunctionHom g) j).symm)

end
section
variable (K : Type u) [CommRing K] {X : Scheme.{u}}

/-- Recover the graph-fiber morphism from any test-scheme incidence morphism over the displayed triple. -/
noncomputable def goodPairChartFiberLift (f : X ⟶ incidenceGraphScheme K) (g : X ⟶ Spec (.of K))
    (h : f ≫ incidenceChartToTriples K goodChartPermutation = g ≫ goodPairTripleSection K) :
    X ⟶ goodPairGraphScheme K :=
  letI : Algebra K Γ(X, ⊤) := (affineFunctionHom g).toAlgebra
  morphismFromAffineFunctions X
    (goodPairChartIncidenceLift K (incidenceChartPoint K f) (goodPairChart_morphism_coefficients K f g h)).toRingHom

lemma goodPairChartFiberLift_toBase (f : X ⟶ incidenceGraphScheme K) (g : X ⟶ Spec (.of K))
    (h : f ≫ incidenceChartToTriples K goodChartPermutation = g ≫ goodPairTripleSection K) :
    goodPairChartFiberLift K f g h ≫ goodPairGraphToBase K = g := by
  letI : Algebra K Γ(X, ⊤) := (affineFunctionHom g).toAlgebra
  let φ : GoodPairGraphAlgebra K →ₐ[K] Γ(X, ⊤) :=
    goodPairChartIncidenceLift K (incidenceChartPoint K f) (goodPairChart_morphism_coefficients K f g h)
  change morphismFromAffineFunctions X φ.toRingHom ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (GoodPairGraphAlgebra K))) = g
  rw [morphismFromAffineFunctions_comp_Spec]
  have he : φ.toRingHom.comp (algebraMap K (GoodPairGraphAlgebra K)) = affineFunctionHom g :=
    φ.comp_algebraMap
  rw [he, from_affineFunctionHom]

lemma goodPairChartFiberLift_point (f : X ⟶ incidenceGraphScheme K) (g : X ⟶ Spec (.of K))
    (h : f ≫ incidenceChartToTriples K goodChartPermutation = g ≫ goodPairTripleSection K) :
    incidenceChartPoint K (goodPairChartFiberLift K f g h ≫ goodPairGraphToIncidenceChart K) =
      incidenceChartPoint K f := by
  letI : Algebra K Γ(X, ⊤) := (affineFunctionHom g).toAlgebra
  let φ : GoodPairGraphAlgebra K →ₐ[K] Γ(X, ⊤) :=
    goodPairChartIncidenceLift K (incidenceChartPoint K f) (goodPairChart_morphism_coefficients K f g h)
  change incidenceChartPoint K (morphismFromAffineFunctions X φ.toRingHom ≫
    incidenceChartEvaluation K (goodPairGraphIncidencePoint K)) = incidenceChartPoint K f
  rw [incidenceChartEvaluation_point, affineFunctionHom_from]
  exact goodPairChartIncidenceLift_recovers K (incidenceChartPoint K f) _

lemma goodPairGraphToIncidenceChart_toBase :
    goodPairGraphToIncidenceChart K ≫ incidenceGraphToBase K = goodPairGraphToBase K :=
  incidenceChartEvaluation_toBase K (goodPairGraphIncidencePoint K)

/-- Recovery holds as equality of actual scheme morphisms, for arbitrary test schemes. -/
lemma goodPairChartFiberLift_toChart (f : X ⟶ incidenceGraphScheme K) (g : X ⟶ Spec (.of K))
    (h : f ≫ incidenceChartToTriples K goodChartPermutation = g ≫ goodPairTripleSection K) :
    goodPairChartFiberLift K f g h ≫ goodPairGraphToIncidenceChart K = f := by
  have hb : f ≫ incidenceGraphToBase K = g := by
    have he := congrArg (fun t => t ≫ alternatingTripleToBase K) h
    simpa only [Category.assoc, incidenceChartToTriples_toBase,
      goodPairTripleSection_toBase, Category.comp_id] using he
  apply incidenceChart_morphism_ext K
  · calc
      (goodPairChartFiberLift K f g h ≫ goodPairGraphToIncidenceChart K) ≫ incidenceGraphToBase K =
          goodPairChartFiberLift K f g h ≫ goodPairGraphToBase K := by
            rw [Category.assoc, goodPairGraphToIncidenceChart_toBase]
      _ = g := goodPairChartFiberLift_toBase K f g h
      _ = f ≫ incidenceGraphToBase K := hb.symm
  · exact goodPairChartFiberLift_point K f g h

end
end PfaffianDescent
