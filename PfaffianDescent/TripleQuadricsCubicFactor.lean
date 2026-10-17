import PfaffianDescent.TripleQuadricsLengthEquality
import PfaffianDescent.ProjectiveIdealCancellation
import PfaffianDescent.ProjectiveIdealSaturation
import PfaffianDescent.CompleteIntersectionSocleHom
import PfaffianDescent.ThreeGeneratorKoszulShortExact
import PfaffianDescent.CoordinateRegularExt
import AllCharacteristics.HomogeneousProjectiveAmbient

/-!
# The scheme-theoretic containment step for a net of quadrics

This records the equality step in the net-of-quadrics argument.  Once a
length-eight closed subscheme of a regular three-quadric intersection lies on
a cubic, the entire complete intersection lies on that cubic as a closed
projective subscheme.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective

universe u

section

variable {K : Type u} [Field K]

/-- A finite rank-eight three-quadric intersection containing a finite
rank-eight subscheme of a cubic factors through that cubic.  This is the
scheme-theoretic containment primitive; a regular sequence supplies the
finiteness and rank in the usual complete-intersection application. -/
theorem triple_quadrics_factor_through_cubic_of_finite_rank_eight
    (F f g h : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 3)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    (hW : AllCharacteristics.finiteSchemeRank
      (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase f hf)]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker)
    (hZ : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase f hf) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient f hf) :
    ∃ q : scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) ⟶
        hypersurface F hF,
      IsClosedImmersion q ∧
        q ≫ hypersurfaceToAmbient F hF =
          tripleCompleteIntersectionToHypersurface f g h hf hg hh ≫
            hypersurfaceToAmbient f hf := by
  let l := tripleCompleteIntersectionLift f g h hf hg hh i hker
  letI : IsIso l := triple_quadrics_lift_isIso_of_finite_rank_eight
    f g h hf hg hh hW i hker hZ
  let q : scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) ⟶
      hypersurface F hF := inv l ≫ j
  have hq : q ≫ hypersurfaceToAmbient F hF =
      tripleCompleteIntersectionToHypersurface f g h hf hg hh ≫
        hypersurfaceToAmbient f hf := by
    calc
      q ≫ hypersurfaceToAmbient F hF =
          inv l ≫ i ≫ hypersurfaceToAmbient f hf := by
        exact congrArg (fun r => inv l ≫ r) hcompat
      _ = inv l ≫ (l ≫ tripleCompleteIntersectionToHypersurface f g h hf hg hh) ≫
          hypersurfaceToAmbient f hf := by
        rw [tripleCompleteIntersectionLift_fac f g h hf hg hh i hker]
      _ = tripleCompleteIntersectionToHypersurface f g h hf hg hh ≫
          hypersurfaceToAmbient f hf := by
        simpa only [Category.assoc] using
          (IsIso.inv_hom_id_assoc l
            (tripleCompleteIntersectionToHypersurface f g h hf hg hh ≫
              hypersurfaceToAmbient f hf))
  refine ⟨q, ?_, hq⟩
  letI : IsClosedImmersion (q ≫ hypersurfaceToAmbient F hF) := by
    rw [hq]
    infer_instance
  exact IsClosedImmersion.of_comp q (hypersurfaceToAmbient F hF)

/-- A regular degree-eight three-quadric intersection containing a
length-eight subscheme of a cubic factors through that cubic.  The displayed
ambient equality makes this the scheme-theoretic form of the containment
step in `lem:net-of-quadrics`. -/
theorem triple_quadrics_factor_through_cubic_of_rank_eight
    (F f g h : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 3)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase f hf)]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker)
    (hZ : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase f hf) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient f hf) :
    ∃ q : scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) ⟶
        hypersurface F hF,
      IsClosedImmersion q ∧
        q ≫ hypersurfaceToAmbient F hF =
          tripleCompleteIntersectionToHypersurface f g h hf hg hh ≫
            hypersurfaceToAmbient f hf := by
  let l := tripleCompleteIntersectionLift f g h hf hg hh i hker
  letI : IsIso l := triple_quadrics_lift_isIso_of_rank_eight
    f g h hf hg hh hf0 hg0 hrel hregular i hker hZ
  let q : scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) ⟶
      hypersurface F hF := inv l ≫ j
  have hq : q ≫ hypersurfaceToAmbient F hF =
      tripleCompleteIntersectionToHypersurface f g h hf hg hh ≫
        hypersurfaceToAmbient f hf := by
    calc
      q ≫ hypersurfaceToAmbient F hF =
          inv l ≫ i ≫ hypersurfaceToAmbient f hf := by
        exact congrArg (fun r => inv l ≫ r) hcompat
      _ = inv l ≫ (l ≫ tripleCompleteIntersectionToHypersurface f g h hf hg hh) ≫
          hypersurfaceToAmbient f hf := by
        rw [tripleCompleteIntersectionLift_fac f g h hf hg hh i hker]
      _ = tripleCompleteIntersectionToHypersurface f g h hf hg hh ≫
          hypersurfaceToAmbient f hf := by
        simpa only [Category.assoc] using
          (IsIso.inv_hom_id_assoc l
            (tripleCompleteIntersectionToHypersurface f g h hf hg hh ≫
              hypersurfaceToAmbient f hf))
  refine ⟨q, ?_, hq⟩
  letI : IsClosedImmersion (q ≫ hypersurfaceToAmbient F hF) := by
    rw [hq]
    infer_instance
  exact IsClosedImmersion.of_comp q (hypersurfaceToAmbient F hF)

end

end PfaffianDescent

namespace PfaffianDescent

open CategoryTheory Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective

section

variable {K : Type*} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coordinate-Ext form of saturation for a regular three-quadric
complete intersection.  The four Ext hypotheses are exactly what the Koszul
resolution of the four homogeneous coordinates must supply. -/
theorem triple_quadrics_no_irrelevant_annihilator_of_coordinate_ext_vanishing
    [HasExt (ModuleCat (MvPolynomial (Fin 4) K))]
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ a : MvPolynomial (Fin 4) K,
      h * a ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        a ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    [Subsingleton (Ext
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span
          (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))))
      (ModuleCat.of (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) K)) 3)]
    [Subsingleton (Ext
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span
          (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))))
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K × MvPolynomial (Fin 4) K × MvPolynomial (Fin 4) K)) 2)]
    [Subsingleton (Ext
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span
          (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))))
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K × MvPolynomial (Fin 4) K × MvPolynomial (Fin 4) K)) 1)]
    [Subsingleton (Ext
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span
          (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))))
      (ModuleCat.of (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) K)) 0)]
    (x : CoordinateRing (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    (hx : ∀ r : Fin 4,
      coordinate (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) r * x = 0) :
    x = 0 := by
  letI : Subsingleton (Ext
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span
          (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))))
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 4) K)))) 0) :=
    threeGenerator_quotient_ext_subsingleton hf0 hg0 hrel hregular
  have hHom : Subsingleton
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span
          (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))) ⟶
        ModuleCat.of (MvPolynomial (Fin 4) K)
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 4) K)))) :=
    Ext.homEquiv₀.symm.injective.subsingleton
  apply quotient_no_common_annihilator_of_span_hom_subsingleton
    (I := Ideal.span ({f, g, h} : Set (MvPolynomial (Fin 4) K)))
    (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K)) hHom x
  rintro r ⟨j, rfl⟩
  change coordinate (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) j * x = 0
  exact hx j

/-- A regular three-quadric complete intersection has no irrelevant coordinate
socle.  The four coordinate Ext groups are supplied by the regular coordinate
sequence in the ambient polynomial ring. -/
theorem triple_quadrics_no_irrelevant_annihilator
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ a : MvPolynomial (Fin 4) K,
      h * a ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        a ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    (x : CoordinateRing (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    (hx : ∀ r : Fin 4,
      coordinate (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) r * x = 0) :
    x = 0 := by
  letI : Subsingleton (Ext
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span
          (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))))
      (ModuleCat.of (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) K)) 3) :=
    coordinate_ext_subsingleton 3 (by omega)
  letI : Subsingleton (Ext
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span
          (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))))
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K × MvPolynomial (Fin 4) K × MvPolynomial (Fin 4) K)) 2) :=
    coordinate_ext_subsingleton_triple 2 (by omega)
  letI : Subsingleton (Ext
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span
          (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))))
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K × MvPolynomial (Fin 4) K × MvPolynomial (Fin 4) K)) 1) :=
    coordinate_ext_subsingleton_triple 1 (by omega)
  letI : Subsingleton (Ext
      (ModuleCat.of (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K ⧸ Ideal.span
          (Set.range (MvPolynomial.X : Fin 4 → MvPolynomial (Fin 4) K))))
      (ModuleCat.of (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) K)) 0) :=
    coordinate_ext_subsingleton 0 (by omega)
  exact triple_quadrics_no_irrelevant_annihilator_of_coordinate_ext_vanishing
    f g h hf hg hh hf0 hg0 hrel hregular x hx

end

end PfaffianDescent

namespace PfaffianDescent

open MvPolynomial

section

variable {K : Type*} [Field K] [Infinite K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A polynomial vanishing on the projective three-quadric intersection is in
its polynomial ideal if the degree-one system avoids the associated primes of
the quotient.  The localized vanishing assumption is precisely what remains
to be extracted from a factorization through a projective hypersurface. -/
theorem triple_quadrics_mem_of_degreeOne_localization_zero
    (F f g h : MvPolynomial (Fin 4) K)
    (havoid : ∀ P ∈ associatedPrimes
      (MvPolynomial (Fin 4) K ⧸ tripleCompleteIntersectionIdeal f g h)
      (MvPolynomial (Fin 4) K ⧸ tripleCompleteIntersectionIdeal f g h),
      ∃ z ∈ MvPolynomial.homogeneousSubmodule (Fin 4) K 1,
        Ideal.Quotient.mk (tripleCompleteIntersectionIdeal f g h) z ∉ P)
    (hzero : ∀ z ∈ MvPolynomial.homogeneousSubmodule (Fin 4) K 1,
      algebraMap (MvPolynomial (Fin 4) K ⧸ tripleCompleteIntersectionIdeal f g h)
        (Localization (Submonoid.powers
          (Ideal.Quotient.mk (tripleCompleteIntersectionIdeal f g h) z)))
        (Ideal.Quotient.mk (tripleCompleteIntersectionIdeal f g h) F) = 0) :
    F ∈ tripleCompleteIntersectionIdeal f g h := by
  apply mem_of_localization_eq_zero_of_avoids_associatedPrimes
    (tripleCompleteIntersectionIdeal f g h)
    (MvPolynomial.homogeneousSubmodule (Fin 4) K 1) F havoid
  exact hzero

end

end PfaffianDescent

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective

universe u

section

variable {K : Type u} [Field K] [Infinite K]
attribute [local instance] MvPolynomial.gradedAlgebra

omit [Infinite K] in
/-- A finite rank-eight three-quadric intersection contained in a cubic
annihilates the cubic ideal sheaf in the ambient projective space.  This is
the kernel-ideal consequence of the degree comparison alone. -/
theorem triple_quadrics_cubic_ker_le_of_finite_rank_eight
    (F f g h : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 3)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    (hW : AllCharacteristics.finiteSchemeRank
      (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase f hf)]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker)
    (hZ : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase f hf) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient f hf) :
    (hypersurfaceToAmbient F hF).ker ≤
      (tripleCompleteIntersectionToHypersurface f g h hf hg hh ≫
        hypersurfaceToAmbient f hf).ker := by
  obtain ⟨q, _, hq⟩ :=
    triple_quadrics_factor_through_cubic_of_finite_rank_eight
      F f g h hF hf hg hh hW i hker hZ j hcompat
  exact hypersurface_ker_le_of_factor F hF q
    (tripleCompleteIntersectionToHypersurface f g h hf hg hh ≫
      hypersurfaceToAmbient f hf) hq

omit [Infinite K] in
/-- The rank-eight three-quadric intersection annihilates the cubic ideal
sheaf in the ambient projective space.  This is the kernel-ideal form of the
scheme containment produced above. -/
theorem triple_quadrics_cubic_ker_le_of_rank_eight
    (F f g h : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 3)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase f hf)]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker)
    (hZ : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase f hf) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient f hf) :
    (hypersurfaceToAmbient F hF).ker ≤
      (tripleCompleteIntersectionToHypersurface f g h hf hg hh ≫
        hypersurfaceToAmbient f hf).ker := by
  obtain ⟨q, _, hq⟩ := triple_quadrics_factor_through_cubic_of_rank_eight
    F f g h hF hf hg hh hf0 hg0 hrel hregular i hker hZ j hcompat
  exact hypersurface_ker_le_of_factor F hF q
    (tripleCompleteIntersectionToHypersurface f g h hf hg hh ≫
      hypersurfaceToAmbient f hf) hq

omit [Infinite K] in
/-- The rank-eight cubic containment gives the normalized cubic equation on
every coordinate chart of the three-quadric complete intersection. -/
theorem triple_quadrics_cubic_coordinate_away_mk_eq_zero_of_rank_eight
    (F f g h : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 3)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase f hf)]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker)
    (hZ : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase f hf) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient f hf)
    (r : Fin 4) :
    Away.mk (grading (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
      (coordinate_mem (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) r) 3
      (Ideal.Quotient.mk
        ((tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal) F)
      (by
        simpa using (polynomial_class_mem_grading
          (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) F hF)) = 0 := by
  apply away_mk_eq_zero_of_hypersurface_ker_le_quotientProjMap_coordinate
    F hF (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)
  rw [← tripleCompleteIntersectionToHypersurface_comp_hypersurfaceToAmbient]
  exact triple_quadrics_cubic_ker_le_of_rank_eight
    F f g h hF hf hg hh hf0 hg0 hrel hregular i hker hZ j hcompat

omit [Infinite K] in
/-- The rank-eight cubic containment gives the normalized cubic equation on
every degree-one projective chart of the three-quadric complete intersection. -/
theorem triple_quadrics_cubic_away_mk_eq_zero_of_rank_eight
    (F f g h : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 3)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase f hf)]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker)
    (hZ : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase f hf) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient f hf)
    (z : MvPolynomial (Fin 4) K)
    (hz : z ∈ MvPolynomial.homogeneousSubmodule (Fin 4) K 1) :
    Away.mk (grading (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
      ((quotientGradedRingHom
        (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)).map_mem hz) 3
      (Ideal.Quotient.mk
        ((tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal) F)
      (by
        simpa using (polynomial_class_mem_grading
          (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) F hF)) = 0 := by
  apply away_mk_eq_zero_of_hypersurface_ker_le_quotientProjMap
    F hF (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) z hz
  rw [← tripleCompleteIntersectionToHypersurface_comp_hypersurfaceToAmbient]
  exact triple_quadrics_cubic_ker_le_of_rank_eight
    F f g h hF hf hg hh hf0 hg0 hrel hregular i hker hZ j hcompat

/-- A rank-eight three-quadric intersection is contained in the cubic as soon
as its degree-one system avoids the associated primes of its quotient.  The
associated-prime hypothesis is the remaining commutative-algebra input in the
net-of-quadrics argument. -/
theorem triple_quadrics_mem_of_rank_eight_and_avoids_associatedPrimes
    (F f g h : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 3)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase f hf)]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker)
    (hZ : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase f hf) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient f hf)
    (havoid : ∀ P ∈ associatedPrimes
      (MvPolynomial (Fin 4) K ⧸
        (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal)
      (MvPolynomial (Fin 4) K ⧸
        (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal),
      ∃ z ∈ MvPolynomial.homogeneousSubmodule (Fin 4) K 1,
        Ideal.Quotient.mk
          (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal z ∉ P) :
    F ∈ (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal := by
  refine @mem_of_away_mk_eq_zero_of_avoids_associatedPrimes
    K (MvPolynomial (Fin 4) K) _ _ _ _ _
    (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal
    (MvPolynomial.homogeneousSubmodule (Fin 4) K 1)
    (grading (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) (gradedRing _)
    F 3 havoid ?_ ?_ ?_
  · intro z hz
    change (quotientGradedRingHom
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) z ∈
        grading (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) 1
    exact (quotientGradedRingHom
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)).map_mem hz
  · change (quotientGradedRingHom
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) F ∈
        grading (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) 3
    exact polynomial_class_mem_grading
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) F hF
  · intro z hz
    exact triple_quadrics_cubic_away_mk_eq_zero_of_rank_eight
      F f g h hF hf hg hh hf0 hg0 hrel hregular i hker hZ j hcompat z hz

/-- The associated-prime condition in the rank-eight net argument follows
from the geometric statement that every associated component meets a standard
projective chart.  Thus the remaining input is precisely exclusion of an
associated component at the irrelevant locus. -/
theorem triple_quadrics_mem_of_rank_eight_and_coordinate_avoidance
    (F f g h : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 3)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase f hf)]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker)
    (hZ : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase f hf) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient f hf)
    (hcoordinate : ∀ P ∈ associatedPrimes
      (CoordinateRing (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
      (CoordinateRing (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)),
      ∃ r : Fin 4,
        coordinate (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) r ∉ P) :
    F ∈ (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal := by
  apply triple_quadrics_mem_of_rank_eight_and_avoids_associatedPrimes
    F f g h hF hf hg hh hf0 hg0 hrel hregular i hker hZ j hcompat
  change ∀ P ∈ associatedPrimes
    (CoordinateRing (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    (CoordinateRing (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)),
    ∃ z ∈ MvPolynomial.homogeneousSubmodule (Fin 4) K 1,
      Ideal.Quotient.mk
        (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal z ∉ P
  exact degreeOne_avoids_associatedPrimes_of_coordinate_avoidance
    (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) hcoordinate

omit [Infinite K] in
/-- A cubic whose ideal sheaf vanishes on a three-quadric intersection belongs
to its polynomial ideal when the quotient has no irrelevant coordinate socle.
This saturation argument is valid over every field. -/
theorem triple_quadrics_mem_of_cubic_ker_le_and_no_irrelevant_annihilator
    (F f g h : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 3)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    (hker : (hypersurfaceToAmbient F hF).ker ≤
      (tripleCompleteIntersectionToHypersurface f g h hf hg hh ≫
        hypersurfaceToAmbient f hf).ker)
    (hsocle : ∀ x : CoordinateRing
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh),
      (∀ r : Fin 4,
        coordinate (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) r * x = 0) →
        x = 0) :
    F ∈ (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal := by
  apply mem_of_coordinate_localization_eq_zero_of_no_irrelevant_annihilator
    (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal
    (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3) F
  · intro x hx0 hx1 hx2 hx3
    apply hsocle x
    intro r
    fin_cases r
    · exact hx0
    · exact hx1
    · exact hx2
    · exact hx3
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · change algebraMap (CoordinateRing
        (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
        (Localization (Submonoid.powers
          (coordinate (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) 0)))
        (Ideal.Quotient.mk
          (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal F) = 0
      apply localization_eq_zero_of_away_mk_eq_zero
        (grading (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
        (coordinate_mem (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) 0) 3
      · apply away_mk_eq_zero_of_hypersurface_ker_le_quotientProjMap_coordinate
          F hF (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)
        rw [← tripleCompleteIntersectionToHypersurface_comp_hypersurfaceToAmbient]
        exact hker
      · simpa using (polynomial_class_mem_grading
          (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) F hF)
    · change algebraMap (CoordinateRing
        (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
        (Localization (Submonoid.powers
          (coordinate (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) 1)))
        (Ideal.Quotient.mk
          (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal F) = 0
      apply localization_eq_zero_of_away_mk_eq_zero
        (grading (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
        (coordinate_mem (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) 1) 3
      · apply away_mk_eq_zero_of_hypersurface_ker_le_quotientProjMap_coordinate
          F hF (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)
        rw [← tripleCompleteIntersectionToHypersurface_comp_hypersurfaceToAmbient]
        exact hker
      · simpa using (polynomial_class_mem_grading
          (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) F hF)
    · change algebraMap (CoordinateRing
        (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
        (Localization (Submonoid.powers
          (coordinate (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) 2)))
        (Ideal.Quotient.mk
          (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal F) = 0
      apply localization_eq_zero_of_away_mk_eq_zero
        (grading (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
        (coordinate_mem (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) 2) 3
      · apply away_mk_eq_zero_of_hypersurface_ker_le_quotientProjMap_coordinate
          F hF (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)
        rw [← tripleCompleteIntersectionToHypersurface_comp_hypersurfaceToAmbient]
        exact hker
      · simpa using (polynomial_class_mem_grading
          (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) F hF)
    · change algebraMap (CoordinateRing
        (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
        (Localization (Submonoid.powers
          (coordinate (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) 3)))
        (Ideal.Quotient.mk
          (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal F) = 0
      apply localization_eq_zero_of_away_mk_eq_zero
        (grading (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
        (coordinate_mem (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) 3) 3
      · apply away_mk_eq_zero_of_hypersurface_ker_le_quotientProjMap_coordinate
          F hF (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)
        rw [← tripleCompleteIntersectionToHypersurface_comp_hypersurfaceToAmbient]
        exact hker
      · simpa using (polynomial_class_mem_grading
          (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) F hF)

omit [Infinite K] in
/-- The finite-net conclusion follows directly from chartwise cubic
vanishing once the three-quadric quotient has no element annihilated by all
projective coordinates.  This is the homogeneous saturation statement
supplied by a complete-intersection proof. -/
theorem triple_quadrics_mem_of_rank_eight_and_no_irrelevant_annihilator
    (F f g h : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 3)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase f hf)]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker)
    (hZ : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase f hf) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient f hf)
    (hsocle : ∀ x : CoordinateRing
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh),
      (∀ r : Fin 4,
        coordinate (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) r * x = 0) →
        x = 0) :
    F ∈ (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal := by
  apply triple_quadrics_mem_of_cubic_ker_le_and_no_irrelevant_annihilator
    F f g h hF hf hg hh
  · exact triple_quadrics_cubic_ker_le_of_rank_eight
      F f g h hF hf hg hh hf0 hg0 hrel hregular i hker hZ j hcompat
  · exact hsocle

omit [Infinite K] in
/-- The rank-eight finite-net containment gives literal membership in the
three-quadric ideal.  The saturation step is discharged by the coordinate
regular-sequence calculation. -/
theorem triple_quadrics_mem_of_rank_eight
    (F f g h : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 3)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase f hf)]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker)
    (hZ : AllCharacteristics.finiteSchemeRank
      (i ≫ hypersurfaceToBase f hf) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient f hf) :
    F ∈ (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh).toIdeal := by
  apply triple_quadrics_mem_of_rank_eight_and_no_irrelevant_annihilator
    F f g h hF hf hg hh hf0 hg0 hrel hregular i hker hZ j hcompat
  exact triple_quadrics_no_irrelevant_annihilator f g h hf hg hh hf0 hg0 hrel hregular

end

end PfaffianDescent
