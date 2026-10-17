import PfaffianDescent.CorayActualGenericPlaneCubicSmooth
import PfaffianDescent.CorayPlaneCubicIrreducible
import PfaffianDescent.CorayPlaneCubicIntegral
import PfaffianDescent.CorayPlaneHomogeneousCommonZero
import AllCharacteristics.ProjectivePoints
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! SOURCE ONLY / UNVERIFIED150. ORIGINAL smooth cubic over ANY field produces
irreducibility, prime equation ideals and native geometric integrality of the
SAME actual generic Fin3 plane cubic. Every-extension normalized nonsingularity
is generated internally by149. No supplied integral/smooth plane, chosen
component, Infinite original K, CharZero, constants=K or genus bound. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Nonsingularity of the SAME actual generic plane equation after ANY
coefficient map and ANY further field extension, derived from original cubic
smoothness. The coefficient diagrams/towers are installed internally. -/
theorem genericPlaneCubic_map_normalizedFieldPoint_exists_nonzero_partial
    {K M N : Type u} [Field K] [Field M] [Field N] [Algebra M N]
    (f : GenericHyperplaneField K →+* M)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (y : Fin 3 → N) (j : Fin 3) (hyj : y j = 1)
    (hpy : ((genericPlaneCubic p).map f).eval₂ (algebraMap M N) y = 0) :
    ∃ i : Fin 3, (pderiv i ((genericPlaneCubic p).map f)).eval₂
      (algebraMap M N) y ≠ 0 := by
  let L := GenericHyperplaneField K
  letI : Algebra L N := ((algebraMap M N).comp f).toAlgebra
  letI : Algebra K N := ((algebraMap L N).comp (algebraMap K L)).toAlgebra
  letI : IsScalarTower K L N := IsScalarTower.of_algebraMap_eq fun b => rfl
  have hmap : algebraMap L N = (algebraMap M N).comp f := rfl
  have hpy' : (genericPlaneCubic p).eval₂ (algebraMap L N) y = 0 := by
    rw [MvPolynomial.eval₂_map, ← hmap] at hpy
    exact hpy
  obtain ⟨i, hi⟩ :=
    genericPlaneCubic_normalizedFieldPoint_exists_nonzero_partial p hp hp0 y j hyj hpy'
  exact ⟨i, by simpa only [MvPolynomial.pderiv_map, MvPolynomial.eval₂_map, ← hmap] using hi⟩

/-- The actual parameter field is infinite even if ORIGINAL K is finite.
This uses the literal injection of its polynomial ring into its fraction field. -/
theorem genericHyperplaneField_infinite {K : Type u} [Field K] :
    Infinite (GenericHyperplaneField K) :=
  Infinite.of_injective
    (algebraMap (MvPolynomial (Fin 3) K) (GenericHyperplaneField K))
    (IsFractionRing.injective (MvPolynomial (Fin 3) K) (GenericHyperplaneField K))

/-- Nonzero of the SAME actual plane equation persists under each coefficient
map, with original smoothness constructing the starting nonzero equation. -/
theorem smoothCubic_actualGenericPlaneCubic_map_ne_zero
    {K M : Type u} [Field K] [Field M]
    (f : GenericHyperplaneField K →+* M)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] : (genericPlaneCubic p).map f ≠ 0 := by
  intro hz
  apply genericPlaneCubic_ne_zero p hp hp0
  exact MvPolynomial.map_injective f (RingHom.injective f) (by simpa using hz)

/-- ORIGINAL cubic smoothness produces irreducibility of its SAME actual
generic plane cubic after ANY field coefficient map. Neither pointwise
nonsingularity nor geometric integrality is a caller input. -/
theorem smoothCubic_actualGenericPlaneCubic_map_irreducible
    {K M : Type u} [Field K] [Field M]
    (f : GenericHyperplaneField K →+* M)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] : Irreducible ((genericPlaneCubic p).map f) := by
  apply planeCubic_irreducible_of_normalizedFieldPoints _
    ((genericPlaneCubic_isHomogeneous p hp).map f)
    (smoothCubic_actualGenericPlaneCubic_map_ne_zero f p hp hp0)
  intro N _ _ y j hyj hpy
  exact genericPlaneCubic_map_normalizedFieldPoint_exists_nonzero_partial f p hp hp0 y j hyj hpy

/-- The literal prime equation ideal over every extension is derived from the
ORIGINAL cubic, not supplied to a geometric-integrality adapter. -/
theorem smoothCubic_actualGenericPlaneCubic_map_principalIdeal_prime
    {K M : Type u} [Field K] [Field M]
    (f : GenericHyperplaneField K →+* M)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    (Ideal.span ({(genericPlaneCubic p).map f} :
      Set (MvPolynomial (Fin 3) M))).IsPrime :=
  planeCubic_principalIdeal_prime_of_irreducible _
    (smoothCubic_actualGenericPlaneCubic_map_irreducible f p hp hp0)

/-- Actual generic plane irreducibility over its own native parameter field. -/
theorem smoothCubic_actualGenericPlaneCubic_irreducible
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] : Irreducible (genericPlaneCubic p) := by
  simpa only [MvPolynomial.map_id] using smoothCubic_actualGenericPlaneCubic_map_irreducible
    (RingHom.id (GenericHyperplaneField K)) p hp hp0

/-- Its actual own principal equation ideal is prime. -/
theorem smoothCubic_actualGenericPlaneCubic_principalIdeal_prime
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    (Ideal.span ({genericPlaneCubic p} :
      Set (MvPolynomial (Fin 3) (GenericHyperplaneField K)))).IsPrime :=
  planeCubic_principalIdeal_prime_of_irreducible _
    (smoothCubic_actualGenericPlaneCubic_irreducible p hp hp0)

/-- The SAME actual generic plane curve is nonempty. Infinite K is not a
premise: its literal parameter field is proved infinite internally. -/
theorem smoothCubic_actualGenericPlaneCubic_nonempty
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    Nonempty (hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) := by
  let L := GenericHyperplaneField K
  let Ω := AlgebraicClosure L
  obtain ⟨x, hx, hFx, _hXx⟩ :=
    plane_exists_nonzero_common_zero_of_homogeneous_pos
      ((genericPlaneCubic p).map (algebraMap L Ω)) (MvPolynomial.X (0 : Fin 3))
      ((genericPlaneCubic_isHomogeneous p hp).map (algebraMap L Ω))
      (MvPolynomial.isHomogeneous_X Ω (0 : Fin 3)) (by decide) (by decide)
  have hF : (genericPlaneCubic p).eval₂ (algebraMap L Ω) x = 0 := by
    simpa only [MvPolynomial.aeval_def, MvPolynomial.eval₂_map,
      Algebra.algebraMap_self, RingHom.id_comp] using hFx
  obtain ⟨q, _hq⟩ := hypersurface_point_of_coordinates (algebraMap L Ω)
    (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp) x hx hF
  exact ⟨q (IsLocalRing.closedPoint Ω)⟩

/-- Native integrality of the SAME actual generic plane cubic, from original
cubic smoothness, real prime equation, nonempty scheme and reduced stalks. -/
theorem smoothCubic_actualGenericPlaneCubic_isIntegral
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    IsIntegral (hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) := by
  letI : Smooth (hypersurfaceToBase (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) :=
    smoothCubic_actualGenericPlaneCubic_smooth p hp hp0
  letI : Nonempty (hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) :=
    smoothCubic_actualGenericPlaneCubic_nonempty p hp hp0
  exact planeCubic_isIntegral_of_smooth_of_principalIdeal_prime _ _
    (smoothCubic_actualGenericPlaneCubic_principalIdeal_prime p hp hp0)

/-- The SAME actual generic plane cubic is NATIVELY geometrically integral.
All field-fiber prime ideals, original-to-plane nonsingularity, nonempty and
smooth inputs are generated internally from the ORIGINAL smooth cubic. -/
theorem smoothCubic_actualGenericPlaneCubic_geometricallyIntegral
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    GeometricallyIntegral
      (hypersurfaceToBase (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) := by
  letI : Smooth (hypersurfaceToBase (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) :=
    smoothCubic_actualGenericPlaneCubic_smooth p hp hp0
  letI : Nonempty (hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) :=
    smoothCubic_actualGenericPlaneCubic_nonempty p hp hp0
  apply planeCubic_geometricallyIntegral_of_smooth_of_map_prime _
    (genericPlaneCubic_isHomogeneous p hp)
  intro M _ f
  exact smoothCubic_actualGenericPlaneCubic_map_principalIdeal_prime f p hp hp0

end PfaffianDescent.Coray
