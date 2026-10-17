import PfaffianDescent.GoodPairMixedGlobalMap
import PfaffianDescent.GoodChartFiberFunctions

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {X : Scheme.{u}}

lemma goodMixedPair_morphism_coefficients (ε : Fin 3 → Bool)
    (f : X ⟶ incidenceGraphScheme K) (g : X ⟶ Spec (.of K))
    (h : f ≫ incidenceChartToTriples K (goodMixedChartPermutation ε) = g ≫ goodPairTripleSection K) :
    incidenceOriginalCoefficients (goodMixedChartPermutation ε) (incidenceChartPoint K f) =
      goodPairTripleSchemeCoefficients Γ(X, ⊤) := by
  funext j
  have he := congrArg (fun t => affineFunctionHom t (MvPolynomial.X j)) h
  have he' := (incidenceChartToTriples_coordinates K (goodMixedChartPermutation ε) f j).symm.trans he
  have hg := RingHom.congr_fun (affineFunctionHom_comp_Spec g
    (MvPolynomial.aeval (R := K) (goodPairTripleSchemeCoefficients K)).toRingHom) (MvPolynomial.X j)
  have hg' := hg.trans (congrArg (affineFunctionHom g) (MvPolynomial.aeval_X _ j))
  exact he'.trans (hg'.trans (goodPairTripleSchemeCoefficients_map (affineFunctionHom g) j).symm)

noncomputable def goodMixedPairFiberLift
    (f : X ⟶ incidenceGraphScheme K) (g : X ⟶ Spec (.of K)) : X ⟶ goodMixedPairScheme K :=
  letI : Algebra K Γ(X, ⊤) := (affineFunctionHom g).toAlgebra
  morphismFromAffineFunctions X (goodMixedPairIncidenceLift K (incidenceChartPoint K f)).toRingHom

lemma goodMixedPairFiberLift_toBase
    (f : X ⟶ incidenceGraphScheme K) (g : X ⟶ Spec (.of K)) :
    goodMixedPairFiberLift K f g ≫ goodMixedPairToBase K = g := by
  letI : Algebra K Γ(X, ⊤) := (affineFunctionHom g).toAlgebra
  let φ : MvPolynomial (Fin 3) K →ₐ[K] Γ(X, ⊤) := goodMixedPairIncidenceLift K (incidenceChartPoint K f)
  change morphismFromAffineFunctions X φ.toRingHom ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 3) K))) = g
  rw [morphismFromAffineFunctions_comp_Spec]
  have he : φ.toRingHom.comp (algebraMap K (MvPolynomial (Fin 3) K)) = affineFunctionHom g :=
    φ.comp_algebraMap
  rw [he, from_affineFunctionHom]

lemma goodMixedPairFiberLift_point (h2 : IsUnit (2 : K)) (ε : Fin 3 → Bool)
    (f : X ⟶ incidenceGraphScheme K) (g : X ⟶ Spec (.of K))
    (h : f ≫ incidenceChartToTriples K (goodMixedChartPermutation ε) = g ≫ goodPairTripleSection K) :
    incidenceChartPoint K (goodMixedPairFiberLift K f g ≫ goodMixedPairToIncidenceChart K ε) =
      incidenceChartPoint K f := by
  letI : Algebra K Γ(X, ⊤) := (affineFunctionHom g).toAlgebra
  let φ : MvPolynomial (Fin 3) K →ₐ[K] Γ(X, ⊤) := goodMixedPairIncidenceLift K (incidenceChartPoint K f)
  change incidenceChartPoint K (morphismFromAffineFunctions X φ.toRingHom ≫
    incidenceChartEvaluation K (goodMixedPairUniversalPoint K ε)) = incidenceChartPoint K f
  rw [incidenceChartEvaluation_point, affineFunctionHom_from]
  have h2' : IsUnit (2 : Γ(X, ⊤)) := by
    simpa only [map_ofNat] using h2.map (affineFunctionHom g)
  exact goodMixedPairIncidenceLift_recovers K h2' ε (incidenceChartPoint K f)
    (goodMixedPair_morphism_coefficients K ε f g h)

lemma goodMixedPairToIncidenceChart_toBase (ε : Fin 3 → Bool) :
    goodMixedPairToIncidenceChart K ε ≫ incidenceGraphToBase K = goodMixedPairToBase K :=
  incidenceChartEvaluation_toBase K (goodMixedPairUniversalPoint K ε)

lemma goodMixedPairFiberLift_toChart (h2 : IsUnit (2 : K)) (ε : Fin 3 → Bool)
    (f : X ⟶ incidenceGraphScheme K) (g : X ⟶ Spec (.of K))
    (h : f ≫ incidenceChartToTriples K (goodMixedChartPermutation ε) = g ≫ goodPairTripleSection K) :
    goodMixedPairFiberLift K f g ≫ goodMixedPairToIncidenceChart K ε = f := by
  have hb : f ≫ incidenceGraphToBase K = g := by
    have he := congrArg (fun t => t ≫ alternatingTripleToBase K) h
    simpa only [Category.assoc, incidenceChartToTriples_toBase,
      goodPairTripleSection_toBase, Category.comp_id] using he
  apply incidenceChart_morphism_ext K
  · calc
      (goodMixedPairFiberLift K f g ≫ goodMixedPairToIncidenceChart K ε) ≫ incidenceGraphToBase K =
          goodMixedPairFiberLift K f g ≫ goodMixedPairToBase K := by
            rw [Category.assoc, goodMixedPairToIncidenceChart_toBase]
      _ = g := goodMixedPairFiberLift_toBase K f g
      _ = f ≫ incidenceGraphToBase K := hb.symm
  · exact goodMixedPairFiberLift_point K h2 ε f g h

end
end PfaffianDescent
