import PfaffianDescent.GrassmannianFrameProjectivePullback
import PfaffianDescent.GrassmannianAlgebraPoints
import PfaffianDescent.GrassmannianGlobalModuli
import PfaffianDescent.HomogeneousFrameCoordinateParameter

/-!
# Field-valued members of the projective Grassmannian-frame family

A nonzero homogeneous form in the subspace classified by a field-valued
Grassmannian point gives an actual point of the associated global projective
family.  The ambient equation represented by that point is a nonzero scalar
multiple of the original form.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false

/-- A nonzero member of a homogeneous system over a field is represented by
an actual field-valued point of the global projective family over its
Grassmannian point.  The represented ambient equation differs from the given
member only by a nonzero scalar. -/
theorem exists_grassmannianFrameProjectiveFamilyPullback_point_of_mem
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    {tau : Type} [Finite tau] {d m n : ℕ}
    (e : Fin (m + n) ≃ Monomials tau d)
    (W : Module.Grassmannian F ((Fin m → F) × (Fin n → F)) n)
    (q : homogeneousSubmodule tau F d)
    (hq : (grassmannianChartHomogeneousCoordinateEquiv (R := F) d e).symm q ∈
      W.toSubmodule)
    (hq0 : q ≠ 0) :
    ∃ (t : Spec (.of F) ⟶
        grassmannianFrameProjectiveFamilyPullback K d e
          (grassmannianQuotientMorphism K W))
      (p : MvPolynomial tau F) (hp : p.IsHomogeneous d) (hp0 : p ≠ 0)
      (alpha : F),
      alpha ≠ 0 ∧ p = MvPolynomial.C alpha * q.1 ∧
      t ≫ grassmannianFrameProjectiveFamilyPullbackToBase K d e
          (grassmannianQuotientMorphism K W) = 𝟙 _ ∧
      t ≫ grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e
          (grassmannianQuotientMorphism K W) =
        projectiveClassifyingMap p hp hp0 (RingHom.id F) ≫
          projectiveParametersCoefficientMap d (algebraMap K F) := by
  classical
  obtain ⟨rho, T, hchart⟩ := grassmannian_local_algebra_point K
    (grassmannianQuotientMorphism K W)
    (grassmannianQuotientMorphism_toBase K W)
  let phi : GrassmannianChartRing K m n →+* F :=
    (MvPolynomial.aeval (R := K) (fun ij : Fin n × Fin m => T ij.1 ij.2)).toRingHom
  have hEval : Spec.map (CommRingCat.ofHom phi) = grassmannianChartEvaluation K T := rfl
  have hW : W = grassmannianChartQuotient F rho T := by
    apply grassmannianQuotientAlgebraPoint_injective K
    calc
      grassmannianQuotientAlgebraPoint K W =
          grassmannianChartAlgebraPoint K F m n rho T := by
        apply Subtype.ext
        exact hchart.symm
      _ = grassmannianQuotientAlgebraPoint K
          (grassmannianChartQuotient F rho T) :=
        (grassmannianQuotientAlgebraPoint_chart K rho T).symm
  let x : (Fin m → F) × (Fin n → F) :=
    (grassmannianChartHomogeneousCoordinateEquiv (R := F) d e).symm q
  have hxmem : x ∈ grassmannianChartSubmodule F rho T := by
    change x ∈ (grassmannianChartQuotient F rho T).toSubmodule
    rw [← hW]
    exact hq
  have hqmem : q ∈ grassmannianChartHomogeneousSystem (R := F) d e rho T := by
    refine ⟨x, hxmem, ?_⟩
    exact (grassmannianChartHomogeneousCoordinateEquiv (R := F) d e).apply_symm_apply q
  rw [grassmannianChartHomogeneousSystem_span] at hqmem
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun F).mp hqmem
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hq0
    rw [← hc, hc0]
    simp
  obtain ⟨s, p, hp, hp0, alpha, halpha, hpScale, hsbase, hsclass⟩ :=
    exists_homogeneousFrame_parameter_of_nonzero_coordinates
      (RingHom.id F) e
      (grassmannianChartHomogeneousFrame (R := F) d e rho T)
      (grassmannianChartHomogeneousFrame_linearIndependent (R := F) d e rho T)
      c hc0
  let sChart : Spec (.of F) ⟶ grassmannianFrameProjectiveChartSpace K m n :=
    s ≫ projectiveFrameCoordinateCoefficientMap (m := m) phi
  have hsChartBase : sChart ≫
      toBase (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n))) =
      grassmannianChartEvaluation K T := by
    dsimp only [sChart]
    rw [Category.assoc, projectiveFrameCoordinateCoefficientMap_toBase]
    rw [← Category.assoc, hsbase]
    calc
      Spec.map (CommRingCat.ofHom (RingHom.id F)) ≫
          Spec.map (CommRingCat.ofHom phi) =
        Spec.map (CommRingCat.ofHom ((RingHom.id F).comp phi)) := by
          rw [← Spec.map_comp]
          congr 2
      _ = Spec.map (CommRingCat.ofHom phi) := by
        congr 2
      _ = grassmannianChartEvaluation K T := hEval
  let sGlobal : Spec (.of F) ⟶ grassmannianFrameProjectiveScheme K d e :=
    sChart ≫ grassmannianFrameProjectiveChartι K d e rho
  have hsGlobalBase : sGlobal ≫ grassmannianFrameProjectiveToGrassmannian K d e =
      grassmannianQuotientMorphism K W := by
    dsimp only [sGlobal]
    rw [Category.assoc, grassmannianFrameProjectiveChartι_toGrassmannian]
    rw [← Category.assoc, hsChartBase]
    exact hchart
  let t : Spec (.of F) ⟶
      grassmannianFrameProjectiveFamilyPullback K d e
        (grassmannianQuotientMorphism K W) :=
    pullback.lift sGlobal (𝟙 _) hsGlobalBase
  refine ⟨t, p, hp, hp0, alpha, halpha, ?_, ?_, ?_⟩
  · calc
      p = MvPolynomial.C alpha *
          (∑ j, MvPolynomial.C (c j) *
            ((grassmannianChartHomogeneousFrame (R := F) d e rho T j).1.map
              (RingHom.id F))) := hpScale
      _ = MvPolynomial.C alpha * q.1 := by
        congr 1
        simpa [smul_eq_C_mul, MvPolynomial.map_id] using congrArg Subtype.val hc
  · exact pullback.lift_snd _ _ _
  · dsimp only [t, grassmannianFrameProjectiveFamilyPullbackToGlobalParameters]
    rw [pullback.lift_fst_assoc]
    dsimp only [sGlobal]
    rw [Category.assoc, grassmannianFrameProjectiveChartι_toGlobalParameters]
    dsimp only [sChart, grassmannianFrameProjectiveChartToGlobalParameters]
    rw [Category.assoc]
    rw [grassmannianChartHomogeneousFrameToGlobalParameters_naturality]
    have hcomp : phi.comp (algebraMap K (GrassmannianChartRing K m n)) =
        algebraMap K F := by
      apply RingHom.ext
      intro a
      simp [phi]
    have hT : (grassmannianFrameChartUniversalMatrix K).map phi = T := by
      ext i j
      simp [grassmannianFrameChartUniversalMatrix, phi]
    rw [hcomp, hT]
    unfold grassmannianChartHomogeneousFrameToGlobalParameters
    rw [← Category.assoc]
    have hmaps :
        grassmannianChartHomogeneousFrameToParameters (R := F) d e rho T =
          homogeneousFrameToParameters d e
            (grassmannianChartHomogeneousFrame (R := F) d e rho T)
            (grassmannianChartHomogeneousFrame_linearIndependent
              (R := F) d e rho T) := by
      rfl
    rw [hmaps, hsclass]

end PfaffianDescent
