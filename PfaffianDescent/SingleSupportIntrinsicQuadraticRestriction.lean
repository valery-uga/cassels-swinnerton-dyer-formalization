import PfaffianDescent.SingleSupportProjectiveCoordinates
import PfaffianDescent.IntrinsicQuadraticChosenChartKernel
import PfaffianDescent.HomogeneousVanishingLinearSystem

/-! The actual intrinsic quadratic series restricts into the true quadratic
kernel of Gamma(Z) on its internally selected standard chart. The map is
inclusion inside the same polynomial space, so no dimension is lost. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem singleSupport_intrinsic_quadratics_actual_restriction
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (P : closedPoints (scheme I))
    (hSupport : Set.range i = {P.1}) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
    ∃ j : Fin 4, ∃ (g : ChartRing I j →+* Γ(Z, ⊤)) (x : Fin 4 → Γ(Z, ⊤)),
      x j = 1 ∧ Function.Surjective (aeval (R := k) x) ∧
      g.comp (chartBaseMap I j) = algebraMap k Γ(Z, ⊤) ∧
      (∀ r, x r = g (chartCoordinate I j r)) ∧
      intrinsicFullQuadraticSystem (i ≫ quotientProjMap I) ≤
        homogeneousVanishingPolynomialSubmodule x 2 ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι I j = Z.isoSpec.inv ≫ i := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  obtain ⟨j, g, hgs, hgb, hpoint⟩ := singleSupport_projective_actual_chart I i P hSupport
  let x : Fin 4 → Γ(Z, ⊤) := fun r => g (chartCoordinate I j r)
  let evI := eval₂Hom (chartBaseMap I j) (chartCoordinate I j)
  let evA := ambientChartEvaluation (R := k) (σ := Fin 4) j
  let quo := quotientAmbientChartMap I j
  let h := g.comp quo
  let f := ambientCoordinateChartSpecPoint j h
  have hfac : f = Z.isoSpec.inv ≫ i ≫ quotientProjMap I := by
    have hh : CommRingCat.ofHom h = CommRingCat.ofHom quo ≫ CommRingCat.ofHom g := rfl
    calc
      f = Spec.map (CommRingCat.ofHom g) ≫ chartι I j ≫ quotientProjMap I := by
        dsimp only [f, ambientCoordinateChartSpecPoint]
        rw [hh, Spec.map_comp, Category.assoc, chartι_comp_quotientProjMap]
      _ = Z.isoSpec.inv ≫ i ≫ quotientProjMap I := by
        rw [← Category.assoc, hpoint, Category.assoc]
  letI : QuasiCompact f := by rw [hfac]; infer_instance
  have hW : intrinsicFullQuadraticSystem f =
      intrinsicFullQuadraticSystem (i ≫ quotientProjMap I) := by
    unfold intrinsicFullQuadraticSystem intrinsicQuadraticChartIdeal
    rw [hfac, Scheme.Hom.ker_comp_of_isIso]
  have hcomp : quo.comp evA = evI := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, evA, evI, ambientChartEvaluation,
        eval₂Hom_C] using quotientAmbientChartMap_baseMap I j r
    · intro r
      simpa only [RingHom.comp_apply, evA, evI, ambientChartEvaluation,
        eval₂Hom_X', ambientChartCoordinate] using
        quotientAmbientChartMap_coordinate I j r
  have heval : (aeval x).toRingHom = g.comp evI := by
    apply RingHom.ext
    intro q
    change q.eval₂ (algebraMap k Γ(Z, ⊤)) x = g (q.eval₂ _ _)
    rw [hom_eval₂, hgb]
  have hgen : Function.Surjective (aeval (R := k) x) := by
    change Function.Surjective (aeval (R := k) x).toRingHom
    rw [heval]
    exact hgs.comp (eval₂_chartCoordinate_surjective I j)
  refine ⟨j, g, x, ?_, hgen, hgb, fun _ => rfl, ?_, hpoint⟩
  · change g (chartCoordinate I j j) = 1
    rw [chartCoordinate_self, map_one]
  · intro q hq
    have hqf : q ∈ intrinsicFullQuadraticSystem f := by rw [hW]; exact hq
    have hqchart : q ∈ intrinsicQuadraticChartIdeal f j :=
      ((Submodule.mem_iInf _).mp hqf.2) j
    have hzero : h (evA q) = 0 :=
      intrinsicQuadraticChartIdeal_specPoint_evaluation_zero j h q hqchart
    apply (mem_homogeneousVanishingPolynomialSubmodule_iff x 2 q).mpr
    refine ⟨hq.1, ?_⟩
    change (aeval x).toRingHom q = 0
    rw [heval, ← hcomp]
    exact hzero

end PfaffianDescent
