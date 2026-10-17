import PfaffianDescent.IntrinsicQuadraticChosenChartKernel
import PfaffianDescent.IntrinsicFullQuadraticSystem

/- SOURCE ONLY / UNVERIFIED. SAME actual point/ambient square identifies
native normalized quadratic evaluation, including original scheme kernels. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma actualIntrinsicQuadratic_nativeResidue_zero
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface p hp) [QuasiCompact q]
    (j : Fin 4) (rho : ChartRing (equationIdeal p hp) j →+* L)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ chartι (equationIdeal p hp) j = q)
    (Q : MvPolynomial (Fin 4) K)
    (hQ : Q ∈ intrinsicFullQuadraticSystem (q ≫ quotientProjMap (equationIdeal p hp))) :
    rho (Q.eval₂ (chartBaseMap (equationIdeal p hp) j)
      (chartCoordinate (equationIdeal p hp) j)) = 0 := by
  let I := equationIdeal p hp
  let evI := eval₂Hom (chartBaseMap I j) (chartCoordinate I j)
  let evA := ambientChartEvaluation (R := K) (σ := Fin 4) j
  let quo := quotientAmbientChartMap I j
  let h := rho.comp quo
  let f := ambientCoordinateChartSpecPoint j h
  have hPoint : f = q ≫ quotientProjMap I := by
    have hh : CommRingCat.ofHom h = CommRingCat.ofHom quo ≫ CommRingCat.ofHom rho := rfl
    change Spec.map (CommRingCat.ofHom h) ≫ _ = _
    rw [hh, Spec.map_comp, Category.assoc, ← chartι_comp_quotientProjMap,
      ← Category.assoc, hfac]
    rfl
  letI : QuasiCompact f := by rw [hPoint]; infer_instance
  have hcomp : quo.comp evA = evI := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simpa only [RingHom.comp_apply, evA, evI, ambientChartEvaluation,
        eval₂Hom_C] using quotientAmbientChartMap_baseMap I j c
    · intro r
      simpa only [RingHom.comp_apply, evA, evI, ambientChartEvaluation,
        eval₂Hom_X', ambientChartCoordinate] using quotientAmbientChartMap_coordinate I j r
  have hQf : Q ∈ intrinsicFullQuadraticSystem f := by rw [hPoint]; exact hQ
  have hz := intrinsicQuadraticChartIdeal_specPoint_evaluation_zero j h Q
    (((Submodule.mem_iInf _).mp hQf.2) j)
  change rho ((quo.comp evA) Q) = 0 at hz
  rw [hcomp] at hz
  exact hz

end PfaffianDescent
