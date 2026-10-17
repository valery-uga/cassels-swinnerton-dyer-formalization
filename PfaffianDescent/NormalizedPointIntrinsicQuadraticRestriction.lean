import PfaffianDescent.IntrinsicQuadraticChosenChartKernel
import PfaffianDescent.NormalizedPointIntrinsicQuadraticInclusion

/-! Intrinsic quadratic vanishing detects the actual normalized algebra
evaluation whenever one coordinate is a unit. No reducedness is used. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem intrinsicFullQuadraticSystem_le_comp
    {K : Type u} [Field K] {Z Y : Scheme.{u}}
    (f : Z ⟶ Y) (i : Y ⟶ Proj (homogeneousSubmodule (Fin 4) K)) :
    intrinsicFullQuadraticSystem i ≤ intrinsicFullQuadraticSystem (f ≫ i) := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  apply (Submodule.mem_iInf _).mpr
  intro j
  have hj := ((Submodule.mem_iInf _).mp hp.2) j
  change Proj.awayToSection (homogeneousSubmodule (Fin 4) K) (X j)
    (ambientChartEvaluation j p) ∈ i.ker.ideal (intrinsicQuadraticAmbientOpen j) at hj
  change Proj.awayToSection (homogeneousSubmodule (Fin 4) K) (X j)
    (ambientChartEvaluation j p) ∈ (f ≫ i).ker.ideal (intrinsicQuadraticAmbientOpen j)
  exact (Scheme.Hom.le_ker_comp f i) _ hj

set_option backward.isDefEq.respectTransparency false in
theorem linearNormalizedPoint_intrinsicQuadratics_evaluation_zero_of_unit_coordinate
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → A) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hOne : ell.eval₂ (algebraMap K A) x = 1)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0)
    (j : Fin 4) (u : Aˣ) (hu : (u : A) = x j)
    (p : MvPolynomial (Fin 4) K)
    (hp : p ∈ intrinsicFullQuadraticSystem
      (linearNormalizedPoint I x ell hell hOne he ≫ quotientProjMap I)) :
    p.eval₂ (algebraMap K A) x = 0 := by
  let q := linearNormalizedPoint I x ell hell hOne he
  obtain ⟨g, hcoords, hpoint⟩ :=
    exists_coordinateChartMap_eq_linearNormalizedPoint I x ell hell hOne he j u hu
  have hbase : g.comp (chartBaseMap I j) = algebraMap K A := by
    have h := congrArg (fun t => t ≫ toBase I) hpoint
    rw [Category.assoc, chartι_toBase, ← Spec.map_comp,
      linearNormalizedPoint_toBase] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  letI : IsFinite (q ≫ toBase I) := by
    rw [linearNormalizedPoint_toBase]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : IsFinite q := IsFinite.of_comp q (toBase I)
  let evI := eval₂Hom (chartBaseMap I j) (chartCoordinate I j)
  let evA := ambientChartEvaluation (R := K) (σ := Fin 4) j
  let quo := quotientAmbientChartMap I j
  let h := g.comp quo
  let f := ambientCoordinateChartSpecPoint j h
  have hfac : f = q ≫ quotientProjMap I := by
    have hh : CommRingCat.ofHom h = CommRingCat.ofHom quo ≫ CommRingCat.ofHom g := rfl
    dsimp only [f, ambientCoordinateChartSpecPoint]
    rw [hh, Spec.map_comp, Category.assoc, ← chartι_comp_quotientProjMap,
      ← Category.assoc, hpoint]
  letI : QuasiCompact f := by rw [hfac]; infer_instance
  have hcomp : quo.comp evA = evI := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, evA, evI, ambientChartEvaluation,
        eval₂Hom_C] using quotientAmbientChartMap_baseMap I j r
    · intro r
      simpa only [RingHom.comp_apply, evA, evI, ambientChartEvaluation,
        eval₂Hom_X', ambientChartCoordinate] using
        quotientAmbientChartMap_coordinate I j r
  have hpf : p ∈ intrinsicFullQuadraticSystem f := by rw [hfac]; exact hp
  have hz : h (evA p) = 0 :=
    intrinsicQuadraticChartIdeal_specPoint_evaluation_zero j h p
      (((Submodule.mem_iInf _).mp hpf.2) j)
  have hscaled : p.eval₂ (algebraMap K A) (fun r => (↑(u⁻¹) : A) * x r) = 0 := by
    change g ((quo.comp evA) p) = 0 at hz
    rw [hcomp] at hz
    change g (p.eval₂ (chartBaseMap I j) (chartCoordinate I j)) = 0 at hz
    rw [hom_eval₂, hbase] at hz
    simpa only [Function.comp_def, hcoords] using hz
  have hmul : (↑(u⁻¹) : A) ^ 2 * p.eval₂ (algebraMap K A) x = 0 := by
    exact (AllCharacteristics.eval₂_homogeneous_smul p hp.1
      (algebraMap K A) x (↑(u⁻¹) : A)).symm.trans hscaled
  exact ((u⁻¹).isUnit.pow 2).mul_left_cancel (by simpa using hmul)

end PfaffianDescent
