import PfaffianDescent.SingleClosedPointFiniteSchemeAlgebra
import PfaffianDescent.ProjectiveClosedPointCoordinates

/-! A standard projective chart of the ACTUAL supplied singleton-support
scheme over every field. A chart containing its support contains the whole
scheme; its actual ambient coordinate evaluator is surjective. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k] {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original finite immersion factors through a standard coordinate
chart, with the actual Γ(Z)-valued chart map. No infinite-field hypothesis. -/
theorem singleSupport_projective_actual_chart
    (I : HomogeneousIdeal (homogeneousSubmodule σ k))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (p : closedPoints (scheme I))
    (hSupport : Set.range i = {p.1}) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    ∃ j : σ, ∃ g : ChartRing I j →+* Γ(Z, ⊤), Function.Surjective g ∧
      g.comp (chartBaseMap I j) = algebraMap k Γ(Z, ⊤) ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι I j = Z.isoSpec.inv ≫ i := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  obtain ⟨j, y, hy⟩ := exists_coordinate_chart I p.1
  have hrange : Set.range i ⊆ Set.range (chartι I j) := by
    rintro _ ⟨z, rfl⟩
    have hiz : i z = p.1 := by
      apply Set.mem_singleton_iff.mp
      rw [← hSupport]
      exact Set.mem_range_self z
    exact ⟨y, hy.trans hiz.symm⟩
  let iU := IsOpenImmersion.lift (chartι I j) i hrange
  have hU : iU ≫ chartι I j = i := IsOpenImmersion.lift_fac _ _ _
  letI : IsClosedImmersion (iU ≫ chartι I j) := hU.symm ▸ inferInstance
  letI : IsClosedImmersion iU := IsClosedImmersion.of_comp iU (chartι I j)
  let g := Spec.preimage (Z.isoSpec.inv ≫ iU)
  have hg : Spec.map g = Z.isoSpec.inv ≫ iU := Spec.map_preimage _
  refine ⟨j, g.hom,
    AllCharacteristics.spec_preimage_surjective_of_closedImmersion
      (Z.isoSpec.inv ≫ iU), ?_, ?_⟩
  · have he : CommRingCat.ofHom (chartBaseMap I j) ≫ g =
        CommRingCat.ofHom (algebraMap k Γ(Z, ⊤)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hg, ← chartι_toBase, finiteSchemeCoefficient_spec]
      have hUbase : iU ≫ chartι I j ≫ toBase I = i ≫ toBase I := by
        rw [← Category.assoc, hU]
      rw [Category.assoc, hUbase]
    exact congrArg CommRingCat.Hom.hom he
  · change Spec.map g ≫ chartι I j = Z.isoSpec.inv ≫ i
    rw [hg, Category.assoc, hU]

/-- Entire-polynomial coordinates on the given Γ(Z), with the true chart
and ambient identity retained. Nilpotents remain in this evaluator. -/
theorem singleSupport_projective_generating_coordinates
    (I : HomogeneousIdeal (homogeneousSubmodule σ k))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (p : closedPoints (scheme I))
    (hSupport : Set.range i = {p.1}) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    ∃ j : σ, ∃ (g : ChartRing I j →+* Γ(Z, ⊤)) (x : σ → Γ(Z, ⊤)),
      x j = 1 ∧ Function.Surjective (aeval (R := k) x) ∧
      (∀ m, x m = g (chartCoordinate I j m)) ∧
      (∀ q ∈ I.toIdeal, aeval x q = 0) ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι I j = Z.isoSpec.inv ≫ i := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  obtain ⟨j, g, hgs, hgb, hpoint⟩ := singleSupport_projective_actual_chart I i p hSupport
  let x : σ → Γ(Z, ⊤) := fun m => g (chartCoordinate I j m)
  have he : (aeval x).toRingHom =
      g.comp (eval₂Hom (chartBaseMap I j) (chartCoordinate I j)) := by
    apply RingHom.ext
    intro q
    change q.eval₂ (algebraMap k Γ(Z, ⊤)) x = g (q.eval₂ _ _)
    rw [hom_eval₂, hgb]
  refine ⟨j, g, x, ?_, ?_, fun _ => rfl, ?_, hpoint⟩
  · change g (chartCoordinate I j j) = 1
    rw [chartCoordinate_self, map_one]
  · change Function.Surjective (aeval x).toRingHom
    rw [he]
    exact hgs.comp (eval₂_chartCoordinate_surjective I j)
  · intro q hq
    change (aeval x).toRingHom q = 0
    rw [he, RingHom.comp_apply]
    change g (q.eval₂ (chartBaseMap I j) (chartCoordinate I j)) = 0
    rw [eval₂_chartCoordinate_eq_zero_of_mem I j q hq, map_zero]

end PfaffianDescent
