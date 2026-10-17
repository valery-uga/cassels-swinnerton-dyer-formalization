import PfaffianDescent.GoodPairIncidenceOverlap
import PfaffianDescent.IncidenceChartRechart
import PfaffianDescent.GoodPairMixedGlobalMap

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A]

lemma incidenceChartEvaluation_goodPair_coefficients
    (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints A)
    (h : incidenceChartEvaluation K p ≫ incidenceChartToTriples K i =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) ≫ goodPairTripleSection K) :
    incidenceOriginalCoefficients i p = goodPairTripleSchemeCoefficients A := by
  let φ : AlternatingTripleRing K →+* A :=
    (MvPolynomial.aeval (R := K) (incidenceOriginalCoefficients i p)).toRingHom
  let ψ : AlternatingTripleRing K →+* A :=
    (MvPolynomial.aeval (R := K) (goodPairTripleSchemeCoefficients A)).toRingHom
  have he : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ) :=
    (incidenceChartEvaluation_toTriples K i p).symm.trans
      (h.trans (goodPairTripleSection_baseChange K (A := A)))
  have hφ : φ = ψ := congrArg CommRingCat.Hom.hom (Spec.map_injective he)
  funext j
  exact (MvPolynomial.aeval_X (R := K) (incidenceOriginalCoefficients i p) j).symm.trans
    ((RingHom.congr_fun hφ (MvPolynomial.X j)).trans
      (MvPolynomial.aeval_X (R := K) (goodPairTripleSchemeCoefficients A) j))

end
section
variable (K : Type u) [Field K] [CharZero K] {L : Type u} [Field L] [Algebra K L]

/-- Every field-valued point of the global incidence over the first two forms factors
through one of the eight specified charts. This applies to all residue fields of the fiber. -/
theorem goodPairIncidence_field_factor (f : Spec (.of L) ⟶ incidenceScheme K)
    (h : f ≫ incidenceToTriples K =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ goodPairTripleSection K) :
    ∃ ε : Fin 3 → Bool, ∃ g : Spec (.of L) ⟶ incidenceGraphScheme K,
      g ≫ incidenceChartι K (goodMixedChartPermutation ε) = f := by
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have hf : f ≫ incidenceToBase K = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    have he := congrArg (fun t => t ≫ alternatingTripleToBase K) h
    simpa only [Category.assoc, incidenceToTriples_toBase,
      goodPairTripleSection_toBase, Category.comp_id] using he
  obtain ⟨i, p, hp⟩ := incidence_local_algebra_point K f hf
  have ht : incidenceChartEvaluation K p ≫ incidenceChartToTriples K i =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ goodPairTripleSection K := by
    calc
      incidenceChartEvaluation K p ≫ incidenceChartToTriples K i =
          incidenceChartEvaluation K p ≫ (incidenceChartι K i ≫ incidenceToTriples K) :=
        congrArg (fun t => incidenceChartEvaluation K p ≫ t) (incidenceChartι_toTriples K i).symm
      _ = (incidenceChartEvaluation K p ≫ incidenceChartι K i) ≫ incidenceToTriples K :=
        (Category.assoc _ _ _).symm
      _ = f ≫ incidenceToTriples K := congrArg (fun t => t ≫ incidenceToTriples K) hp
      _ = _ := h
  have hc := incidenceChartEvaluation_goodPair_coefficients K i p ht
  obtain ⟨ε, hε⟩ := goodPairIncidenceGraph_overlap i p hc
  obtain ⟨g, hg⟩ := incidenceChartEvaluation_rechart K i (goodMixedChartPermutation ε) p hε
  exact ⟨ε, g, hg.trans hp⟩

end
end PfaffianDescent
