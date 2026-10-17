import AllCharacteristics.ProjectiveEquationParameters
import AllCharacteristics.ProjectiveTripleOverlap

/-!
# Factoring a local projective equation parameter through a coefficient chart

An open chart containing the image of the closed point of a local spectrum
contains the entire image. This gives a coefficient-ring homomorphism into
the local ring. Its residue is the chosen field-point chart homomorphism.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.UniversalHomogeneous

universe u

/-- A morphism from a local spectrum factors through an open immersion as
soon as its closed point lies in that open. -/
theorem localSpec_factor_open
    {T : Type u} [CommRing T] [IsLocalRing T]
    {Y U : Scheme.{u}} (q : Spec (.of T) ⟶ Y) (i : U ⟶ Y)
    [IsOpenImmersion i]
    (hclosed : q (IsLocalRing.closedPoint T) ∈ Set.range i) :
    ∃ qU : Spec (.of T) ⟶ U, qU ≫ i = q := by
  have hrange : Set.range q ⊆ Set.range i := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map q.continuous).mem_open
      i.opensRange.2 hclosed
  exact ⟨IsOpenImmersion.lift i q hrange, IsOpenImmersion.lift_fac i q hrange⟩

/-- If a local projective equation parameter has the specified residue-field
point, then it lies in that point's normalized coefficient chart. The local
coefficient homomorphism reduces to the field-point chart homomorphism. -/
theorem localSpec_projectiveEquationChartMap
    {K T : Type u} [Field K] [CommRing T] [IsLocalRing T]
    [Algebra K T]
    (q : Spec (.of T) ⟶ projectiveParameters K (Fin 4) 3)
    (p : MvPolynomial (Fin 4) (IsLocalRing.ResidueField T))
    (_hp : p.IsHomogeneous 3)
    (j : Monomials (Fin 4) 3) (hj : p.coeff j.1 ≠ 0)
    (hpoint : Spec.map (CommRingCat.ofHom
        (algebraMap T (IsLocalRing.ResidueField T))) ≫ q =
      projectiveEquationParameter
        (algebraMap K (IsLocalRing.ResidueField T)) p j hj) :
    ∃ f : ParameterChartRing K (Fin 4) 3 j →+* T,
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j = q ∧
      (algebraMap T (IsLocalRing.ResidueField T)).comp f =
        projectiveEquationChartMap
          (algebraMap K (IsLocalRing.ResidueField T)) p j hj := by
  let c := projectiveEquationChartMap
      (algebraMap K (IsLocalRing.ResidueField T)) p j hj
  let _ : IsLocalHom (algebraMap T (IsLocalRing.ResidueField T)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    infer_instance
  have hclosed : q (IsLocalRing.closedPoint T) ∈
      Set.range (parameterChartι K (Fin 4) 3 j) := by
    refine ⟨Spec.map (CommRingCat.ofHom c)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField T)), ?_⟩
    have hc : Spec.map (CommRingCat.ofHom
        (algebraMap T (IsLocalRing.ResidueField T)))
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField T)) =
        IsLocalRing.closedPoint T := by
      exact IsLocalRing.comap_closedPoint _
    have he := congrArg
      (fun g : Spec (.of (IsLocalRing.ResidueField T)) ⟶
        projectiveParameters K (Fin 4) 3 =>
          g (IsLocalRing.closedPoint (IsLocalRing.ResidueField T))) hpoint
    change q ((Spec.map (CommRingCat.ofHom
      (algebraMap T (IsLocalRing.ResidueField T))))
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField T))) =
      (parameterChartι K (Fin 4) 3 j)
        ((Spec.map (CommRingCat.ofHom c))
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField T))) at he
    rw [hc] at he
    exact he.symm
  obtain ⟨qU, hqU⟩ := localSpec_factor_open q
    (parameterChartι K (Fin 4) 3 j) hclosed
  let f := (Spec.preimage qU).hom
  have hf : Spec.map (CommRingCat.ofHom f) = qU := Spec.map_preimage qU
  refine ⟨f, ?_, ?_⟩
  · rw [hf]
    exact hqU
  · apply RingHom.ext
    intro x
    have heq : Spec.map (CommRingCat.ofHom
        ((algebraMap T (IsLocalRing.ResidueField T)).comp f)) =
        Spec.map (CommRingCat.ofHom c) := by
      apply (cancel_mono (parameterChartι K (Fin 4) 3 j)).mp
      rw [AllCharacteristics.HomogeneousProjective.specMap_ringHom_comp,
        hf, Category.assoc, hqU]
      exact hpoint
    exact congrArg (fun g :
      ParameterChartRing K (Fin 4) 3 j →+*
        IsLocalRing.ResidueField T => g x)
      (congrArg CommRingCat.Hom.hom (Spec.map_injective heq))

end PfaffianDescent
