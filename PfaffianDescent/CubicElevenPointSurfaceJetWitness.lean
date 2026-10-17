import PfaffianDescent.CubicElevenPointNativeJetWitness

/-!
The eleven-point and first-jet restrictions on the actual cubic homogeneous
coordinate ring. The defining equation is divided out using the literal
quotient map. In degree three the surface ideal of the eleven points has
dimension eight and still realizes all six first derivatives.
-/

namespace PfaffianDescent

open MvPolynomial Module AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective

universe u
variable {K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

noncomputable def cubicSurfaceCoordinateEvaluationAlgHom
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {A : Type u} [CommRing A] [Algebra K A]
    (x : Fin 4 → A) (hpx : aeval x p = 0) :
    CoordinateRing (equationIdeal p hp) →ₐ[K] A :=
  Ideal.Quotient.liftₐ (equationIdeal p hp).toIdeal (aeval x) (by
    intro q hq
    change q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) at hq
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hq
    rw [hr, map_mul, hpx, zero_mul])

theorem cubicSurfaceCoordinateEvaluationAlgHom_projection
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {A : Type u} [CommRing A] [Algebra K A]
    (x : Fin 4 → A) (hpx : aeval x p = 0)
    (q : homogeneousSubmodule (Fin 4) K 3) :
    cubicSurfaceCoordinateEvaluationAlgHom p hp x hpx
      (cubicSurfaceHomogeneousCoordinateProjection p hp 3 q).1 = aeval x q.1 := rfl

noncomputable def cubicSurfaceElevenPointValueRestriction
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 11 → Fin 4 → K) (hpx : ∀ i, aeval (x i) p = 0) :
    grading (equationIdeal p hp) 3 →ₗ[K] (Fin 11 → K) :=
  LinearMap.pi fun i =>
    (cubicSurfaceCoordinateEvaluationAlgHom p hp (x i) (hpx i)).toLinearMap.domRestrict _

noncomputable def cubicSurfaceElevenPointFullJetRestriction
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 11 → Fin 4 → K) (hpx : ∀ i, aeval (x i) p = 0)
    (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K) (hpJ : ∀ i, aeval (J i) p = 0) :
    grading (equationIdeal p hp) 3 →ₗ[K]
      ((Fin 3 → CubicSurfaceFirstJet K) × (Fin 8 → K)) :=
  (LinearMap.pi fun i =>
    (cubicSurfaceCoordinateEvaluationAlgHom p hp (J i) (hpJ i)).toLinearMap.domRestrict _).prod
    (LinearMap.pi fun i =>
      (cubicSurfaceCoordinateEvaluationAlgHom p hp (x (i.natAdd 3))
        (hpx (i.natAdd 3))).toLinearMap.domRestrict _)

noncomputable def cubicSurfaceElevenPointIdealFirstDerivativeRestriction
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 11 → Fin 4 → K) (hpx : ∀ i, aeval (x i) p = 0)
    (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K) (hpJ : ∀ i, aeval (J i) p = 0) :
    LinearMap.ker (cubicSurfaceElevenPointValueRestriction p hp x hpx) →ₗ[K]
      (Fin 3 → Fin 2 → K) :=
  (LinearMap.pi fun i => (TrivSqZeroExt.sndHom K (Fin 2 → K)).comp
    ((cubicSurfaceCoordinateEvaluationAlgHom p hp (J i) (hpJ i)).toLinearMap.domRestrict _)
  ).domRestrict _

theorem cubicSurfaceElevenPointValueRestriction_projection
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 11 → Fin 4 → K) (hpx : ∀ i, aeval (x i) p = 0)
    (q : homogeneousSubmodule (Fin 4) K 3) :
    cubicSurfaceElevenPointValueRestriction p hp x hpx
      (cubicSurfaceHomogeneousCoordinateProjection p hp 3 q) =
      cubicElevenPointValueRestriction x q := by
  funext i
  exact (finite_product_evaluation_apply x q.1 i).symm

theorem cubicSurfaceElevenPointFullJetRestriction_projection
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 11 → Fin 4 → K) (hpx : ∀ i, aeval (x i) p = 0)
    (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K) (hpJ : ∀ i, aeval (J i) p = 0)
    (q : homogeneousSubmodule (Fin 4) K 3) :
    cubicSurfaceElevenPointFullJetRestriction p hp x hpx J hpJ
      (cubicSurfaceHomogeneousCoordinateProjection p hp 3 q) =
      cubicElevenPointFullJetRestriction x J q := rfl

theorem cubicSurfaceElevenPointValueRestriction_surjective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 11 → Fin 4 → K) (hpx : ∀ i, aeval (x i) p = 0)
    (hsurj : Function.Surjective (cubicElevenPointValueRestriction x)) :
    Function.Surjective (cubicSurfaceElevenPointValueRestriction p hp x hpx) := by
  intro z
  obtain ⟨q, hq⟩ := hsurj z
  exact ⟨cubicSurfaceHomogeneousCoordinateProjection p hp 3 q,
    (cubicSurfaceElevenPointValueRestriction_projection p hp x hpx q).trans hq⟩

theorem cubicSurfaceElevenPointFullJetRestriction_surjective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 11 → Fin 4 → K) (hpx : ∀ i, aeval (x i) p = 0)
    (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K) (hpJ : ∀ i, aeval (J i) p = 0)
    (hsurj : Function.Surjective (cubicElevenPointFullJetRestriction x J)) :
    Function.Surjective (cubicSurfaceElevenPointFullJetRestriction p hp x hpx J hpJ) := by
  intro z
  obtain ⟨q, hq⟩ := hsurj z
  exact ⟨cubicSurfaceHomogeneousCoordinateProjection p hp 3 q, hq⟩

theorem cubicSurfaceElevenPointValueRestriction_ker_finrank
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (x : Fin 11 → Fin 4 → K) (hpx : ∀ i, aeval (x i) p = 0)
    (hsurj : Function.Surjective (cubicElevenPointValueRestriction x)) :
    finrank K (LinearMap.ker (cubicSurfaceElevenPointValueRestriction p hp x hpx)) = 8 := by
  letI : FiniteDimensional K (homogeneousSubmodule (Fin 4) K 3) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 4) K 3)
  letI : FiniteDimensional K (grading (equationIdeal p hp) 3) :=
    Module.Finite.of_surjective (cubicSurfaceHomogeneousCoordinateProjection p hp 3)
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp 3)
  have hdim := (cubicSurfaceElevenPointValueRestriction p hp x hpx).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
      (cubicSurfaceElevenPointValueRestriction_surjective p hp x hpx hsurj),
    finrank_top, cubicSurface_grade_three_finrank p hp hp0, Module.finrank_pi] at hdim
  norm_num at hdim
  omega

theorem cubicSurfaceElevenPointIdealFirstDerivativeRestriction_surjective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 11 → Fin 4 → K) (hpx : ∀ i, aeval (x i) p = 0)
    (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K) (hpJ : ∀ i, aeval (J i) p = 0)
    (hsurj : Function.Surjective (cubicElevenPointIdealFirstDerivativeRestriction x J)) :
    Function.Surjective
      (cubicSurfaceElevenPointIdealFirstDerivativeRestriction p hp x hpx J hpJ) := by
  intro z
  obtain ⟨q, hq⟩ := hsurj z
  have hzero : cubicSurfaceElevenPointValueRestriction p hp x hpx
      (cubicSurfaceHomogeneousCoordinateProjection p hp 3 q.1) = 0 := by
    rw [cubicSurfaceElevenPointValueRestriction_projection]
    exact LinearMap.mem_ker.mp q.2
  refine ⟨⟨cubicSurfaceHomogeneousCoordinateProjection p hp 3 q.1,
    LinearMap.mem_ker.mpr hzero⟩, ?_⟩
  exact hq

/-- The actual degree-three coordinate-ring ideal of eleven points on a
smooth cubic has dimension eight and restricts surjectively to the six
derivatives of three full surface jets, all constructed internally. -/
theorem exists_cubicSurfaceElevenPoint_surface_fullJet_witness
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K)
      (hpx : ∀ i, aeval (x i) p = 0) (hpJ : ∀ i, aeval (J i) p = 0),
      (∀ i, x i ≠ 0) ∧ (∀ i j, i ≠ j → ∀ a : K, a • x i ≠ x j) ∧
      (∀ i j, (J i j).fst = x (i.castAdd 8) j) ∧
      Function.Surjective (cubicSurfaceElevenPointFullJetRestriction p hp x hpx J hpJ) ∧
      Function.Surjective (cubicSurfaceElevenPointValueRestriction p hp x hpx) ∧
      finrank K (LinearMap.ker (cubicSurfaceElevenPointValueRestriction p hp x hpx)) = 8 ∧
      Function.Surjective
        (cubicSurfaceElevenPointIdealFirstDerivativeRestriction p hp x hpx J hpJ) := by
  obtain ⟨x, J, hx, hpx, hdir, hresidue, hpJ, hfull, hvalues, hderivatives⟩ :=
    exists_cubicSurfaceElevenPoint_native_fullJet_witness p hp hp0
  exact ⟨x, J, hpx, hpJ, hx, hdir, hresidue,
    cubicSurfaceElevenPointFullJetRestriction_surjective p hp x hpx J hpJ hfull,
    cubicSurfaceElevenPointValueRestriction_surjective p hp x hpx hvalues,
    cubicSurfaceElevenPointValueRestriction_ker_finrank p hp hp0 x hpx hvalues,
    cubicSurfaceElevenPointIdealFirstDerivativeRestriction_surjective
      p hp x hpx J hpJ hderivatives⟩

end PfaffianDescent
