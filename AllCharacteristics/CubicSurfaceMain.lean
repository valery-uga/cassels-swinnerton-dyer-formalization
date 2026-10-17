import AllCharacteristics.CubicSingularPointReduction
import AllCharacteristics.HomogeneousClosedPoints
import AllCharacteristics.MaCubicPencilLifting
import AllCharacteristics.SmoothCubicReference
import AllCharacteristics.VoisinDegreeTenReduction

/-!
# The Cassels--Swinnerton-Dyer theorem for arbitrary cubic surfaces

This file assembles the residue-field point, multiplicity, smoothing,
degree-one, and specialization arguments.  Voisin's characteristic-zero
theorem is the only external input.  Ma's degree-preserving lifting step and
the auxiliary smooth equation used in the pencil are proved internally.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
open HomogeneousProjective

universe u

/-- Finite-extension form of the main theorem, modulo Voisin's theorem. -/
theorem cubic_coordinates_of_finite_point_coprime_of_voisin
    (voisin : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeOneOrFourFor K)
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (x : Fin 4 → L) (hx : x ≠ 0)
    (he : p.eval₂ (algebraMap k L) x = 0) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain hground | ⟨x', hx'⟩ :=
    cubic_point_or_smooth_extension_point p hp hdegree x hx he
  · exact hground
  · obtain ⟨q, hq, hq0, hqs⟩ := smoothCubicReferenceFor k
    exact cubic_coordinates_of_smooth_extension_point_of_voisin
      voisin p q hp hq hq0 hqs x' hx' hdegree

/-- A degree-one integral zero-cycle on an arbitrary homogeneous cubic
surface produces rational coordinates, modulo the stated external inputs. -/
theorem cubic_coordinates_of_zeroCycle_degree_one_of_voisin
    (voisin : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeOneOrFourFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  let f := hypersurfaceToBase p hp
  obtain ⟨x, _, hx⟩ := ZeroCycle.exists_coprime_degree f z hz
  let := pointAlgebra f x.1
  have := closedPoint_moduleFinite f x
  obtain ⟨v, hv, he⟩ := hypersurface_residueField_coordinates p hp x.1
  have hdegree : Nat.Coprime
      (Module.finrank k ((hypersurface p hp).residueField x.1)) 3 := by
    rw [closedPoint_finrank_eq_residueDegree f x]
    exact hx
  exact cubic_coordinates_of_finite_point_coprime_of_voisin
    voisin p hp hdegree v hv he

/-- Scheme-theoretic form: a degree-one zero-cycle gives a rational section
of the cubic surface. -/
theorem cubic_section_of_zeroCycle_degree_one_of_voisin
    (voisin : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeOneOrFourFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨y, hy, hey⟩ :=
    cubic_coordinates_of_zeroCycle_degree_one_of_voisin
      voisin p hp z hz
  obtain ⟨a, ha⟩ := hypersurface_point_of_coordinates
    (RingHom.id k) p hp y hy hey
  exact ⟨a, by simpa using ha⟩

/-- The arbitrary-characteristic degree-one reduction with Coray's theorem
and Voisin's degree-ten constructions supplied as the only characteristic-
zero external inputs. -/
theorem cubic_coordinates_of_zeroCycle_degree_one_of_coray_and_degree_ten_geometry
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeTenPointGeometryFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  exact cubic_coordinates_of_zeroCycle_degree_one_of_voisin
    (fun K _ _ => voisinDegreeOneOrFourFor_of_coray_and_degree_ten_point_geometry
      (coray K) (geometry K))
    p hp z hz

/-- The arbitrary-characteristic reduction can use Voisin's three concrete
pencils with endpoint identities in the finite-flat-family cycle quotient.
This is the scheme-level input supplied by the refined degree-ten bridge. -/
theorem cubic_coordinates_of_zeroCycle_degree_one_of_coray_and_lineSectionPencilClassGeometry
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K],
      VoisinDegreeTenPointLineSectionPencilClassGeometryFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  exact cubic_coordinates_of_zeroCycle_degree_one_of_coray_and_degree_ten_geometry
    coray (fun K _ _ =>
      voisinDegreeTenPointGeometryFor_of_lineSectionPencilClassGeometryFor (geometry K))
    p hp z hz

/-- The complete-intersection version of the same reduction identifies its
rank-sixteen endpoint only up to isomorphism over the cubic surface.  The
finite-subscheme fundamental-cycle transport discharges that identification
before the Coray--Voisin arithmetic is applied. -/
theorem cubic_coordinates_of_zeroCycle_degree_one_of_coray_and_lineSectionPencilClassGeometryForIso
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K],
      VoisinDegreeTenPointLineSectionPencilClassGeometryForIso K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  exact cubic_coordinates_of_zeroCycle_degree_one_of_coray_and_degree_ten_geometry
    coray (fun K _ _ =>
      voisinDegreeTenPointGeometryFor_of_lineSectionPencilClassGeometryForIso (geometry K))
    p hp z hz

/-- Arbitrary-characteristic transport of the full dependency chain.  The
characteristic-zero lift is discharged by Coray, Voisin's degree-ten input,
the quadratic effectivity bridge, and the Pfaffian descent, then specialized
back to the original field. -/
theorem cubic_coordinates_of_zeroCycle_degree_one_of_coray_and_quadratic_effectivity
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeTenPointGeometryFor K)
    (effectivity : ∀ (K : Type u) [Field K] [CharZero K], VoisinQuadraticEffectivityFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain ⟨K, _, _, q, hq, hq0, hs, ⟨w, hw⟩, hspecialize⟩ :=
    exists_charZero_smooth_cubic_degree_one_reduction p hp hne z hz
  let _ : Smooth (hypersurfaceToBase q hq) := hs
  exact hspecialize
    (charZero_smooth_cubic_coordinates_of_voisin_and_quadratic_effectivity
      (voisinDegreeOneOrFourFor_of_coray_and_degree_ten_point_geometry
      (coray K) (geometry K)) (effectivity K) q hq hq0 w hw)

/-- Arbitrary-characteristic transport with Voisin's quadratic input supplied
directly as endpoint families over every characteristic-zero lift. -/
theorem cubic_coordinates_of_zeroCycle_degree_one_of_coray_and_quadratic_family_effectivity
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeTenPointGeometryFor K)
    (families : ∀ (K : Type u) [Field K] [CharZero K], VoisinQuadraticFamilyEffectivityFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain ⟨K, _, _, q, hq, hq0, hs, ⟨w, hw⟩, hspecialize⟩ :=
    exists_charZero_smooth_cubic_degree_one_reduction p hp hne z hz
  let _ : Smooth (hypersurfaceToBase q hq) := hs
  exact hspecialize
    (charZero_smooth_cubic_coordinates_of_voisin_and_quadratic_effectivity
      (voisinDegreeOneOrFourFor_of_coray_and_degree_ten_point_geometry
      (coray K) (geometry K))
      ((voisinQuadraticEffectivityFor_of_familyEffectivityFor (families K)))
      q hq hq0 w hw)

/-- The arbitrary-characteristic degree-one reduction with Coray's theorem
and the concrete endpoint-family version of Voisin's degree-ten input. -/
theorem cubic_coordinates_of_zeroCycle_degree_one_of_coray_and_degree_ten_family_geometry
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (familyGeometry : ∀ (K : Type u) [Field K] [CharZero K],
      VoisinDegreeTenFamilyGeometryFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  exact cubic_coordinates_of_zeroCycle_degree_one_of_coray_and_degree_ten_geometry
    coray (fun K _ _ => voisinDegreeTenPointGeometryFor_of_familyGeometryFor
      (familyGeometry K)) p hp z hz

/-- Scheme-theoretic form of the same reduction, with Coray and the
degree-ten Voisin constructions exposed separately. -/
theorem cubic_section_of_zeroCycle_degree_one_of_coray_and_degree_ten_geometry
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeTenPointGeometryFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨y, hy, hey⟩ :=
    cubic_coordinates_of_zeroCycle_degree_one_of_coray_and_degree_ten_geometry
      coray geometry p hp z hz
  obtain ⟨a, ha⟩ := hypersurface_point_of_coordinates
    (RingHom.id k) p hp y hy hey
  exact ⟨a, by simpa using ha⟩

/-- Scheme-theoretic version of the reduction using the quotient-level
endpoint calculations of Voisin's three pencils. -/
theorem cubic_section_of_zeroCycle_degree_one_of_coray_and_lineSectionPencilClassGeometry
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K],
      VoisinDegreeTenPointLineSectionPencilClassGeometryFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨y, hy, hey⟩ :=
    cubic_coordinates_of_zeroCycle_degree_one_of_coray_and_lineSectionPencilClassGeometry
      coray geometry p hp z hz
  obtain ⟨a, ha⟩ := hypersurface_point_of_coordinates
    (RingHom.id k) p hp y hy hey
  exact ⟨a, by simpa using ha⟩

/-- Scheme-theoretic endpoint-isomorphism form of the Coray--Voisin
reduction. -/
theorem cubic_section_of_zeroCycle_degree_one_of_coray_and_lineSectionPencilClassGeometryForIso
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K],
      VoisinDegreeTenPointLineSectionPencilClassGeometryForIso K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨y, hy, hey⟩ :=
    cubic_coordinates_of_zeroCycle_degree_one_of_coray_and_lineSectionPencilClassGeometryForIso
      coray geometry p hp z hz
  obtain ⟨a, ha⟩ := hypersurface_point_of_coordinates
    (RingHom.id k) p hp y hy hey
  exact ⟨a, by simpa using ha⟩

/-- Scheme-theoretic form with Coray's theorem and explicit endpoint families
as the only characteristic-zero external inputs. -/
theorem cubic_section_of_zeroCycle_degree_one_of_coray_and_degree_ten_family_geometry
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (familyGeometry : ∀ (K : Type u) [Field K] [CharZero K],
      VoisinDegreeTenFamilyGeometryFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨y, hy, hey⟩ :=
    cubic_coordinates_of_zeroCycle_degree_one_of_coray_and_degree_ten_family_geometry
      coray familyGeometry p hp z hz
  obtain ⟨a, ha⟩ := hypersurface_point_of_coordinates
    (RingHom.id k) p hp y hy hey
  exact ⟨a, by simpa using ha⟩

/-- The characteristic-zero dependency chain written in the same order as the
paper: Coray's `1/4/10` alternative and Voisin's degree-ten elimination give
`1/4`, then Voisin's quadratic effectivity turns the degree-four branch into
degree five, which is discharged by the Pfaffian descent. -/
theorem charZero_cubic_section_of_zeroCycle_degree_one_of_coray_and_quadratic_effectivity
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenPointGeometryFor k)
    (effectivity : VoisinQuadraticEffectivityFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  exact smooth_cubic_section_of_voisin_and_quadratic_effectivity
    (voisinDegreeOneOrFourFor_of_coray_and_degree_ten_point_geometry coray geometry)
    effectivity p hp hne z hz

/- The direct arbitrary-field cubic-cycle descent also yields the scheme
   conclusion without a separate quadratic-effectivity hypothesis. -/
theorem charZero_cubic_section_of_zeroCycle_degree_one_of_coray_direct
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenPointGeometryFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  exact smooth_cubic_section_of_voisin_direct
    (voisinDegreeOneOrFourFor_of_coray_and_degree_ten_point_geometry coray geometry)
    p hp hne z hz

/-- The same characteristic-zero dependency chain with Voisin's quadratic
effectivity supplied directly by its finite-flat endpoint families. -/
theorem charZero_cubic_section_of_zeroCycle_degree_one_of_coray_and_quadratic_family_effectivity
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenPointGeometryFor k)
    (families : VoisinQuadraticFamilyEffectivityFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  exact smooth_cubic_section_of_voisin_and_quadratic_family_effectivity
    (voisinDegreeOneOrFourFor_of_coray_and_degree_ten_point_geometry coray geometry)
    families p hp hne z hz

/-- Coordinate form of the characteristic-zero family-level dependency chain. -/
theorem charZero_cubic_coordinates_of_zeroCycle_degree_one_of_coray_and_quadratic_family_effectivity
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (geometry : VoisinDegreeTenPointGeometryFor k)
    (families : VoisinQuadraticFamilyEffectivityFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain ⟨a, ha⟩ :=
    charZero_cubic_section_of_zeroCycle_degree_one_of_coray_and_quadratic_family_effectivity
      coray geometry families p hp hne z hz
  exact hypersurface_coordinates_of_point (RingHom.id k) p hp a (by simpa using ha)

/- A fully explicit endpoint-family interface can be supplied without
separately choosing the degree-three reference cycle. -/
theorem cubic_section_of_zeroCycle_degree_one_of_coray_and_uniform_familySteps
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (familySteps : ∀ (K : Type u) [Field K] [CharZero K]
      (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3), p ≠ 0 →
      Smooth (hypersurfaceToBase p hp) →
      ∀ h : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3 →
        PfaffianDescent.VoisinDegreeTenFamilySteps
          (hypersurfaceToBase p hp) h)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  exact cubic_section_of_zeroCycle_degree_one_of_coray_and_degree_ten_family_geometry
    coray (fun K _ _ => voisinDegreeTenFamilyGeometryFor_of_uniform_familySteps
      (familySteps K)) p hp z hz

/- The same fully explicit family interface has a coordinate-level form.  This
   avoids making callers pass through the scheme-theoretic section when the
   downstream argument only needs a nonzero homogeneous solution. -/
theorem cubic_coordinates_of_zeroCycle_degree_one_of_coray_and_uniform_familySteps
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (familySteps : ∀ (K : Type u) [Field K] [CharZero K]
      (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3), p ≠ 0 →
      Smooth (hypersurfaceToBase p hp) →
      ∀ h : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3 →
        PfaffianDescent.VoisinDegreeTenFamilySteps
          (hypersurfaceToBase p hp) h)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain ⟨a, ha⟩ := cubic_section_of_zeroCycle_degree_one_of_coray_and_uniform_familySteps
    coray familySteps p hp z hz
  exact hypersurface_coordinates_of_point (RingHom.id k) p hp a (by simpa using ha)

end AllCharacteristics
