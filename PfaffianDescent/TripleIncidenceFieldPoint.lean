import PfaffianDescent.IncidenceAlgebraPoints
import PfaffianDescent.GoodAmbientIsotropicChart

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u
section
variable (K : Type u) [CommRing K]

/-- A triple specified by its forty-five alternating coefficients. -/
noncomputable def tripleCoefficientSection (c : AlternatingTripleIndex → K) :
    Spec (.of K) ⟶ alternatingTripleScheme K :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) c).toRingHom)

lemma tripleCoefficientSection_toBase (c : AlternatingTripleIndex → K) :
    tripleCoefficientSection K c ≫ alternatingTripleToBase K = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) c).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (AlternatingTripleRing K))) = _
  rw [← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap K (AlternatingTripleRing K)) ≫
      CommRingCat.ofHom (MvPolynomial.aeval (R := K) c).toRingHom = 𝟙 (CommRingCat.of K) := by
    apply CommRingCat.hom_ext
    exact (MvPolynomial.aeval (R := K) c).comp_algebraMap
  rw [he, Spec.map_id]

noncomputable def tripleCoefficientForm (c : AlternatingTripleIndex → K) (k : Fin 3) :
    AlternatingTwoForms K ((Fin 3 → K) × (Fin 3 → K)) :=
  (alternatingCoordinates (incidenceAmbientBasis K)).symm (fun s => c (k, s))

/-- The same actual forms on the six-dimensional coordinate vector space. -/
noncomputable def tripleCoefficientFormSix (c : AlternatingTripleIndex → K) (k : Fin 3) :
    AlternatingTwoForms K (Fin 6 → K) :=
  alternatingTransport (incidenceAmbientBasis K).equivFun (tripleCoefficientForm K c k)

end
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A]

lemma tripleCoefficientSection_baseChange (c : AlternatingTripleIndex → K) :
    Spec.map (CommRingCat.ofHom (algebraMap K A)) ≫ tripleCoefficientSection K c =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (R := K) (fun j => algebraMap K A (c j))).toRingHom) := by
  change Spec.map (CommRingCat.ofHom (algebraMap K A)) ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) c).toRingHom) = _
  rw [← Spec.map_comp]
  have he : (Algebra.ofId K A).comp (MvPolynomial.aeval (R := K) c) =
      MvPolynomial.aeval (R := K) (fun j => algebraMap K A (c j)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, Algebra.ofId_apply]
  exact congrArg (fun φ : AlternatingTripleRing K →ₐ[K] A =>
    Spec.map (CommRingCat.ofHom φ.toRingHom)) he

lemma incidenceChartEvaluation_coefficients (c : AlternatingTripleIndex → K)
    (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints A)
    (h : incidenceChartEvaluation K p ≫ incidenceChartToTriples K i =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) ≫ tripleCoefficientSection K c) :
    incidenceOriginalCoefficients i p = fun j => algebraMap K A (c j) := by
  let φ : AlternatingTripleRing K →+* A :=
    (MvPolynomial.aeval (R := K) (incidenceOriginalCoefficients i p)).toRingHom
  let ψ : AlternatingTripleRing K →+* A :=
    (MvPolynomial.aeval (R := K) (fun j => algebraMap K A (c j))).toRingHom
  have he : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ) :=
    (incidenceChartEvaluation_toTriples K i p).symm.trans
      (h.trans (tripleCoefficientSection_baseChange K c))
  have hφ : φ = ψ := congrArg CommRingCat.Hom.hom (Spec.map_injective he)
  funext j
  exact (MvPolynomial.aeval_X (R := K) (incidenceOriginalCoefficients i p) j).symm.trans
    ((RingHom.congr_fun hφ (MvPolynomial.X j)).trans
      (MvPolynomial.aeval_X (R := K) (fun j => algebraMap K A (c j)) j))

end
section
variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L]

/-- Every field-valued point of the actual incidence produces a common isotropic
three-dimensional subspace, with the prescribed original coefficients. -/
theorem incidence_field_point_subspace (c : AlternatingTripleIndex → K)
    (f : Spec (.of L) ⟶ incidenceScheme K)
    (h : f ≫ incidenceToTriples K =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ tripleCoefficientSection K c) :
    ∃ W : Submodule L (Fin 6 → L), finrank L W = 3 ∧ ∀ k : Fin 3,
      alternatingRestriction L _ W
        (tripleCoefficientFormSix L (fun j => algebraMap K L (c j)) k) = 0 := by
  have hf : f ≫ incidenceToBase K = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    have he := congrArg (fun t => t ≫ alternatingTripleToBase K) h
    simpa only [Category.assoc, incidenceToTriples_toBase,
      tripleCoefficientSection_toBase, Category.comp_id] using he
  obtain ⟨i, p, hp⟩ := incidence_local_algebra_point K f hf
  have ht : incidenceChartEvaluation K p ≫ incidenceChartToTriples K i =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ tripleCoefficientSection K c := by
    rw [← incidenceChartι_toTriples K i, ← Category.assoc, hp]
    exact h
  have hc := incidenceChartEvaluation_coefficients K c i p ht
  let e := graphCoordinatePermutation L i.symm
  let W := p.1.graph.map e.toLinearMap
  have hdim : finrank L W = 3 := by
    calc
      finrank L W = finrank L p.1.graph := e.finrank_map_eq _
      _ = finrank L (Fin 3 → L) := (graphSourceEquiv L p.1).finrank_eq
      _ = 3 := Module.finrank_fin_fun L
  have hforms (k : Fin 3) : incidenceOriginalForm i p k =
      tripleCoefficientForm L (fun j => algebraMap K L (c j)) k := by
    apply (alternatingCoordinates (incidenceAmbientBasis L)).injective
    rw [tripleCoefficientForm, LinearEquiv.apply_symm_apply]
    funext s
    exact congrFun hc (k, s)
  have hiso (k : Fin 3) : alternatingRestriction L _ W
      (tripleCoefficientForm L (fun j => algebraMap K L (c j)) k) = 0 := by
    rw [← hforms k]
    exact alternatingTransport_isotropic e p.1.graph W rfl (p.2 k).1 (p.2 k).2
  let b := (incidenceAmbientBasis L).equivFun
  refine ⟨W.map b.toLinearMap, (b.finrank_map_eq W).trans hdim, ?_⟩
  intro k
  exact alternatingTransport_isotropic b W _ rfl _ (hiso k)

end
end PfaffianDescent
