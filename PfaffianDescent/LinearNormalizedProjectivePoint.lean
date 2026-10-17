import PfaffianDescent.LinearChartCoordinates
import PfaffianDescent.FiniteSchemeAlgebra
import AllCharacteristics.FiniteLocalClosedImmersion
import AllCharacteristics.HomogeneousChartEvaluation
import AllCharacteristics.GradedOverlapLifting
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Projective points normalized by an arbitrary linear form

The usual affine-chart construction need not normalize one of the original
coordinates.  Voisin's finite subschemes naturally come with a ground-field
linear form which is one on the whole finite scheme.  This file gives the
corresponding closed-immersion construction.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

section
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra

variable (I : HomogeneousIdeal (homogeneousSubmodule σ K))
    (x : σ → A) (ell : MvPolynomial σ K) (hell : ell.IsHomogeneous 1)
    (hxell : ell.eval₂ (algebraMap K A) x = 1)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0)

noncomputable def linearNormalizedPointChartMap :
    Away (grading I) (Ideal.Quotient.mk I.toIdeal ell) →+* A :=
  let e := Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K A) x) he
  AllCharacteristics.GradedChart.liftCoordinateOne
    (grading I) (Ideal.Quotient.mk I.toIdeal ell) e (by
      change ell.eval₂ (algebraMap K A) x = 1
      exact hxell)

lemma linearNormalizedPointChartMap_base (r : K) :
    linearNormalizedPointChartMap I x ell hxell he
      (AllCharacteristics.GradedChart.baseMap (grading I) r) = algebraMap K A r := by
  let e := Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K A) x) he
  have heell : e (Ideal.Quotient.mk I.toIdeal ell) = 1 := by
    change ell.eval₂ (algebraMap K A) x = 1
    exact hxell
  exact (AllCharacteristics.GradedChart.liftCoordinateOne_baseMap
    (grading I) (Ideal.Quotient.mk I.toIdeal ell) e heell r).trans
      (eval₂_C _ _ r)

lemma linearNormalizedPointChartMap_coordinate (j : σ) :
    linearNormalizedPointChartMap I x ell hxell he
      (linearChartCoordinate I (Ideal.Quotient.mk I.toIdeal ell)
        (polynomial_class_mem_grading I ell hell) j) = x j := by
  let e := Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K A) x) he
  have heell : e (Ideal.Quotient.mk I.toIdeal ell) = 1 := by
    change ell.eval₂ (algebraMap K A) x = 1
    exact hxell
  exact (AllCharacteristics.GradedChart.liftCoordinateOne_normalized
    (grading I) (Ideal.Quotient.mk I.toIdeal ell) e heell
    (polynomial_class_mem_grading I ell hell)
    (coordinate I j) (coordinate_mem I j)).trans
      (eval₂_X _ _ j)

lemma linearNormalizedPointChartMap_eval (p : MvPolynomial σ K) :
    linearNormalizedPointChartMap I x ell hxell he
      (p.eval₂ (AllCharacteristics.GradedChart.baseMap (grading I))
        (linearChartCoordinate I (Ideal.Quotient.mk I.toIdeal ell)
          (polynomial_class_mem_grading I ell hell))) =
      p.eval₂ (algebraMap K A) x := by
  rw [hom_eval₂]
  have hb : (linearNormalizedPointChartMap I x ell hxell he).comp
      (AllCharacteristics.GradedChart.baseMap (grading I)) = algebraMap K A :=
    RingHom.ext (linearNormalizedPointChartMap_base I x ell hxell he)
  rw [hb]
  congr 1
  funext j
  exact linearNormalizedPointChartMap_coordinate I x ell hell hxell he j

/-- The normalized chart map based at an arbitrary degree-one homogeneous
element.  Keeping the chart element as an explicit parameter is essential
when the element came from an existing projective immersion: replacing it by
definitionally equal quotient coordinates loses the original chart map. -/
noncomputable def linearNormalizedPointChartMapAt
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K A) x) he) z = 1) :
    Away (grading I) z →+* A :=
  AllCharacteristics.GradedChart.liftCoordinateOne
    (grading I) z (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K A) x) he) hzOne

lemma linearNormalizedPointChartMapAt_base
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K A) x) he) z = 1) (r : K) :
    linearNormalizedPointChartMapAt I x he z hz hzOne
      (AllCharacteristics.GradedChart.baseMap (grading I) r) = algebraMap K A r := by
  exact (AllCharacteristics.GradedChart.liftCoordinateOne_baseMap
    (grading I) z (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K A) x) he) hzOne r).trans
      (eval₂_C _ _ r)

lemma linearNormalizedPointChartMapAt_coordinate
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K A) x) he) z = 1) (j : σ) :
    linearNormalizedPointChartMapAt I x he z hz hzOne
      (linearChartCoordinate I z hz j) = x j := by
  exact (AllCharacteristics.GradedChart.liftCoordinateOne_normalized
    (grading I) z (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K A) x) he) hzOne hz
    (coordinate I j) (coordinate_mem I j)).trans
      (eval₂_X _ _ j)

lemma linearNormalizedPointChartMapAt_eval
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K A) x) he) z = 1)
    (p : MvPolynomial σ K) :
    linearNormalizedPointChartMapAt I x he z hz hzOne
      (p.eval₂ (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
        (linearChartCoordinate I z hz)) =
      p.eval₂ (algebraMap K A) x := by
  rw [hom_eval₂]
  have hb : (linearNormalizedPointChartMapAt I x he z hz hzOne).comp
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) = algebraMap K A :=
    RingHom.ext (linearNormalizedPointChartMapAt_base I x he z hz hzOne)
  rw [hb]
  congr 1
  funext j
  exact linearNormalizedPointChartMapAt_coordinate I x he z hz hzOne j

/-- A chart morphism is the normalized chart morphism as soon as it has the
same coefficient map and the same projective coordinates. -/
theorem linearNormalizedPointChartMapAt_eq_of_base_and_coordinates
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K A) x) he) z = 1)
    (g : Away (grading I) z →+* A)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) =
      algebraMap K A)
    (hcoordinates : ∀ j : σ, g (linearChartCoordinate I z hz j) = x j) :
    g = linearNormalizedPointChartMapAt I x he z hz hzOne := by
  apply RingHom.ext
  intro a
  obtain ⟨p, hp⟩ := eval₂_linearChartCoordinate_surjective I z hz a
  rw [← hp]
  calc
    g (p.eval₂ (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
        (linearChartCoordinate I z hz)) = p.eval₂ (algebraMap K A) x := by
      rw [hom_eval₂, hbase]
      congr 1
      funext j
      exact hcoordinates j
    _ = linearNormalizedPointChartMapAt I x he z hz hzOne
        (p.eval₂ (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
          (linearChartCoordinate I z hz)) := by
      exact (linearNormalizedPointChartMapAt_eval I x he z hz hzOne p).symm

/-- The projective map reconstructed in a specified normalized chart. -/
noncomputable def linearNormalizedPointAt
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K A) x) he) z = 1) :
    Spec (.of A) ⟶ scheme I :=
  Spec.map (CommRingCat.ofHom (linearNormalizedPointChartMapAt I x he z hz hzOne)) ≫
    Proj.awayι (grading I) z hz (by decide : 0 < 1)

/-- A projective point reconstructed in a specified normalized chart is over
the original coefficient field. -/
theorem linearNormalizedPointAt_toBase
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K A) x) he) z = 1) :
    linearNormalizedPointAt I x he z hz hzOne ≫ toBase I =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  let g := linearNormalizedPointChartMapAt I x he z hz hzOne
  let j : Spec (.of (Away (grading I) z)) ⟶ scheme I :=
    Proj.awayι (grading I) z hz (by decide : 0 < 1)
  have hj : j ≫ toBase I =
      Spec.map (CommRingCat.ofHom
        (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))) := by
    dsimp [j]
    change Proj.awayι (grading I) z hz (by decide : 0 < 1) ≫
      (Proj.toSpecZero (grading I) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (grading I 0)))) = _
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    rfl
  change (Spec.map (CommRingCat.ofHom g) ≫ j) ≫ toBase I = _
  rw [Category.assoc, hj, ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext
    (RingHom.ext (linearNormalizedPointChartMapAt_base I x he z hz hzOne))

/-- Applying an algebra homomorphism to normalized homogeneous coordinates
commutes with the resulting projective point.  The normalization element is
kept fixed in the ground-field homogeneous coordinate ring. -/
theorem linearNormalizedPointAt_naturality
    {L : Type u} [CommRing L] [Algebra K L]
    (φ : A →ₐ[K] L) (xL : σ → L)
    (hxL : ∀ j, xL j = φ (x j))
    (heL : ∀ p ∈ I.toIdeal,
      (eval₂Hom (algebraMap K L) xL) p = 0)
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (hzOneA : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K A) x) he) z = 1)
    (hzOneL : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K L) xL) heL) z = 1) :
    linearNormalizedPointAt I xL heL z hz hzOneL =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        linearNormalizedPointAt I x he z hz hzOneA := by
  let gA := linearNormalizedPointChartMapAt I x he z hz hzOneA
  let gL := linearNormalizedPointChartMapAt I xL heL z hz hzOneL
  have hg : gL = φ.toRingHom.comp gA := by
    symm
    apply linearNormalizedPointChartMapAt_eq_of_base_and_coordinates
      I xL heL z hz hzOneL
    · ext r
      change φ (gA
        (AllCharacteristics.GradedChart.baseMap (grading I) r)) =
          algebraMap K L r
      rw [linearNormalizedPointChartMapAt_base]
      exact φ.commutes r
    · intro j
      change φ (gA (linearChartCoordinate I z hz j)) = xL j
      rw [linearNormalizedPointChartMapAt_coordinate, hxL]
  change Spec.map (CommRingCat.ofHom gL) ≫
      Proj.awayι (grading I) z hz (by decide : 0 < 1) =
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom gA) ≫
        Proj.awayι (grading I) z hz (by decide : 0 < 1))
  rw [hg, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- Generating normalized coordinates make the reconstructed map in its
specified chart a closed immersion. -/
theorem linearNormalizedPointAt_isClosedImmersion [Module.Finite K A]
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K A) x) he) z = 1)
    (hgen : Function.Surjective (eval₂Hom (algebraMap K A) x)) :
    IsClosedImmersion (linearNormalizedPointAt I x he z hz hzOne) := by
  let g := linearNormalizedPointChartMapAt I x he z hz hzOne
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨p, hp⟩ := hgen a
    exact ⟨p.eval₂ (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
      (linearChartCoordinate I z hz),
      (linearNormalizedPointChartMapAt_eval I x he z hz hzOne p).trans hp⟩
  let j : Spec (.of (Away (grading I) z)) ⟶ scheme I :=
    Proj.awayι (grading I) z hz (by decide : 0 < 1)
  letI : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (Proj.awayι (grading I) z hz (by decide : 0 < 1)))
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) :=
    IsClosedImmersion.spec_of_surjective _ hg
  haveI : IsFinite (linearNormalizedPointAt I x he z hz hzOne ≫ toBase I) := by
    rw [linearNormalizedPointAt_toBase]
    exact (IsFinite.SpecMap_iff _).mpr
      (RingHom.finite_algebraMap.mpr inferInstance)
  haveI : IsFinite (linearNormalizedPointAt I x he z hz hzOne) :=
    IsFinite.of_comp _ (toBase I)
  haveI : IsPreimmersion (linearNormalizedPointAt I x he z hz hzOne) := by
    change IsPreimmersion (Spec.map (CommRingCat.ofHom g) ≫ j)
    infer_instance
  exact IsClosedImmersion.of_isPreimmersion _
    (linearNormalizedPointAt I x he z hz hzOne).isClosedMap.isClosed_range

/-- A normalized chart map is determined by its coefficient map and the
images of the projective coordinates.  This is the comparison principle that
keeps a reconstructed projective point attached to its original closed
subscheme instead of merely preserving its map to the base field. -/
theorem linearNormalizedPointChartMap_eq_of_base_and_coordinates
    (g : Away (grading I) (Ideal.Quotient.mk I.toIdeal ell) →+* A)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I)
      (z := Ideal.Quotient.mk I.toIdeal ell)) = algebraMap K A)
    (hcoordinates : ∀ j : σ,
      g (linearChartCoordinate I (Ideal.Quotient.mk I.toIdeal ell)
        (polynomial_class_mem_grading I ell hell) j) = x j) :
    g = linearNormalizedPointChartMap I x ell hxell he := by
  apply RingHom.ext
  intro a
  let z := Ideal.Quotient.mk I.toIdeal ell
  have hz : z ∈ grading I 1 := polynomial_class_mem_grading I ell hell
  obtain ⟨p, hp⟩ := eval₂_linearChartCoordinate_surjective I z hz a
  rw [← hp]
  calc
    g (p.eval₂ (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
        (linearChartCoordinate I z hz)) = p.eval₂ (algebraMap K A) x := by
      rw [hom_eval₂, hbase]
      congr 1
      funext j
      exact hcoordinates j
    _ = linearNormalizedPointChartMap I x ell hxell he
        (p.eval₂ (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
          (linearChartCoordinate I z hz)) := by
      exact (linearNormalizedPointChartMap_eval I x ell hell hxell he p).symm

/-- The projective morphism defined by a normalized set of homogeneous
coordinates.  Naming this map makes it possible to compare it directly with
an existing closed immersion. -/
noncomputable def linearNormalizedPoint : Spec (.of A) ⟶ scheme I :=
  let z := Ideal.Quotient.mk I.toIdeal ell
  let hz : z ∈ grading I 1 := polynomial_class_mem_grading I ell hell
  Spec.map (CommRingCat.ofHom (linearNormalizedPointChartMap I x ell hxell he)) ≫
    Proj.awayι (grading I) z hz (by decide : 0 < 1)

/-- If one of the original homogeneous coordinates is nonzero, a point first
normalized by an arbitrary linear form has an exact presentation in that
coordinate chart.  The new chart coordinates are the original normalized
coordinates divided by the selected one. -/
theorem exists_coordinateChartMap_eq_linearNormalizedPoint
    (j : σ) (u : Aˣ) (huj : (u : A) = x j) :
    ∃ g : ChartRing I j →+* A,
      (∀ i : σ, g (chartCoordinate I j i) =
        (↑(u⁻¹) : A) * x i) ∧
        Spec.map (CommRingCat.ofHom g) ≫ chartι I j =
          linearNormalizedPoint I x ell hell hxell he := by
  let z : CoordinateRing I := Ideal.Quotient.mk I.toIdeal ell
  let hz : z ∈ grading I 1 := polynomial_class_mem_grading I ell hell
  let φ := linearNormalizedPointChartMap I x ell hxell he
  have hφ : ∀ i : σ, φ (linearChartCoordinate I z hz i) = x i := by
    intro i
    dsimp [φ, z, hz]
    exact linearNormalizedPointChartMap_coordinate I x ell hell hxell he i
  have hu : IsUnit (φ (linearChartCoordinate I z hz j)) := by
    rw [hφ, ← huj]
    exact u.isUnit
  obtain ⟨ψ, hψ⟩ := AllCharacteristics.GradedChart.exists_overlap_hom
    (grading I) hz (coordinate_mem I j) φ hu
  let g : ChartRing I j →+* A :=
    ψ.comp (awayMap (grading I) hz (mul_comm z (coordinate I j)))
  refine ⟨g, ?_, ?_⟩
  · intro i
    have hleft : ψ (awayMap (grading I) (coordinate_mem I j) rfl
        (AllCharacteristics.GradedChart.normalized (grading I) hz
          (coordinate I j) (coordinate_mem I j))) = x j := by
      rw [show ψ (awayMap (grading I) (coordinate_mem I j) rfl
          (AllCharacteristics.GradedChart.normalized (grading I) hz
            (coordinate I j) (coordinate_mem I j))) =
          φ (linearChartCoordinate I z hz j) by
            exact RingHom.congr_fun hψ _]
      exact hφ j
    have hmiddle : ψ (awayMap (grading I) hz (mul_comm z (coordinate I j))
        (AllCharacteristics.GradedChart.normalized (grading I) (coordinate_mem I j)
          (coordinate I i) (coordinate_mem I i))) =
        g (chartCoordinate I j i) := rfl
    have hright : ψ (awayMap (grading I) (coordinate_mem I j) rfl
        (AllCharacteristics.GradedChart.normalized (grading I) hz
          (coordinate I i) (coordinate_mem I i))) = x i := by
      rw [show ψ (awayMap (grading I) (coordinate_mem I j) rfl
          (AllCharacteristics.GradedChart.normalized (grading I) hz
            (coordinate I i) (coordinate_mem I i))) =
          φ (linearChartCoordinate I z hz i) by
            exact RingHom.congr_fun hψ _]
      exact hφ i
    have h := congrArg ψ
      (AllCharacteristics.GradedChart.normalized_overlap_mul (grading I) hz
        (coordinate_mem I j) (coordinate I i) (coordinate_mem I i))
    rw [map_mul, hleft, hmiddle, hright] at h
    apply (IsUnit.mul_left_cancel u.isUnit)
    calc
      (u : A) * g (chartCoordinate I j i) = x j * g (chartCoordinate I j i) := by
        rw [huj]
      _ = x i := h
      _ = (u : A) * ((↑(u⁻¹) : A) * x i) := by
        simp
  · change Spec.map (CommRingCat.ofHom g) ≫
        Proj.awayι (grading I) (coordinate I j) (coordinate_mem I j)
          (by decide : 0 < 1) =
      Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (grading I) z hz (by decide : 0 < 1)
    have hleft :
        Spec.map (CommRingCat.ofHom ψ) ≫
          Spec.map (CommRingCat.ofHom
            (awayMap (grading I) (coordinate_mem I j) rfl)) ≫
              Proj.awayι (grading I) z hz (by decide : 0 < 1) =
          Spec.map (CommRingCat.ofHom φ) ≫
            Proj.awayι (grading I) z hz (by decide : 0 < 1) := by
      rw [← Category.assoc, ← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom
        (ψ.comp (awayMap (grading I) (coordinate_mem I j) rfl))) ≫ _ = _
      rw [hψ]
    have hright :
        Spec.map (CommRingCat.ofHom g) ≫
          Proj.awayι (grading I) (coordinate I j) (coordinate_mem I j)
            (by decide : 0 < 1) =
        Spec.map (CommRingCat.ofHom ψ) ≫
          Proj.awayι (grading I) (z * coordinate I j)
            (SetLike.mul_mem_graded hz (coordinate_mem I j)) (by decide : 0 < 2) := by
      calc
        Spec.map (CommRingCat.ofHom g) ≫
            Proj.awayι (grading I) (coordinate I j) (coordinate_mem I j)
              (by decide : 0 < 1) =
          (Spec.map (CommRingCat.ofHom ψ) ≫
            Spec.map (CommRingCat.ofHom
              (awayMap (grading I) hz (mul_comm z (coordinate I j))))) ≫
                Proj.awayι (grading I) (coordinate I j) (coordinate_mem I j)
                  (by decide : 0 < 1) := by
            rw [← Spec.map_comp]
            rfl
        _ = _ := by
          rw [Category.assoc, Proj.SpecMap_awayMap_awayι]
    rw [hright]
    calc
      Spec.map (CommRingCat.ofHom ψ) ≫
          Proj.awayι (grading I) (z * coordinate I j)
            (SetLike.mul_mem_graded hz (coordinate_mem I j)) (by decide : 0 < 2) =
        Spec.map (CommRingCat.ofHom ψ) ≫
          Spec.map (CommRingCat.ofHom
            (awayMap (grading I) (coordinate_mem I j) rfl)) ≫
              Proj.awayι (grading I) z hz (by decide : 0 < 1) := by
          symm
          rw [Proj.SpecMap_awayMap_awayι]
      _ = _ := hleft

/-- The normalized projective morphism is over the coefficient field. -/
theorem linearNormalizedPoint_toBase :
    linearNormalizedPoint I x ell hell hxell he ≫ toBase I =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  let z := Ideal.Quotient.mk I.toIdeal ell
  let hz : z ∈ grading I 1 := polynomial_class_mem_grading I ell hell
  let g := linearNormalizedPointChartMap I x ell hxell he
  let j : Spec (.of (Away (grading I) z)) ⟶ scheme I :=
    Proj.awayι (grading I) z hz (by decide : 0 < 1)
  have hj : j ≫ toBase I =
      Spec.map (CommRingCat.ofHom
        (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))) := by
    dsimp [j]
    change Proj.awayι (grading I) z hz (by decide : 0 < 1) ≫
      (Proj.toSpecZero (grading I) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (grading I 0)))) = _
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    rfl
  change (Spec.map (CommRingCat.ofHom g) ≫ j) ≫ toBase I = _
  rw [Category.assoc, hj, ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext
    (RingHom.ext (linearNormalizedPointChartMap_base I x ell hxell he))

/-- Generating normalized coordinates make the named projective point a
closed immersion. -/
theorem linearNormalizedPoint_isClosedImmersion [Module.Finite K A]
    (hgen : Function.Surjective (eval₂Hom (algebraMap K A) x)) :
    IsClosedImmersion (linearNormalizedPoint I x ell hell hxell he) := by
  let z := Ideal.Quotient.mk I.toIdeal ell
  let hz : z ∈ grading I 1 := polynomial_class_mem_grading I ell hell
  let g := linearNormalizedPointChartMap I x ell hxell he
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨p, hp⟩ := hgen a
    exact ⟨p.eval₂ (AllCharacteristics.GradedChart.baseMap (grading I))
      (linearChartCoordinate I z hz),
      (linearNormalizedPointChartMap_eval I x ell hell hxell he p).trans hp⟩
  let j : Spec (.of (Away (grading I) z)) ⟶ scheme I :=
    Proj.awayι (grading I) z hz (by decide : 0 < 1)
  letI : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (Proj.awayι (grading I) z hz (by decide : 0 < 1)))
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) :=
    IsClosedImmersion.spec_of_surjective _ hg
  haveI : IsFinite (linearNormalizedPoint I x ell hell hxell he ≫ toBase I) := by
    rw [linearNormalizedPoint_toBase]
    exact (IsFinite.SpecMap_iff _).mpr
      (RingHom.finite_algebraMap.mpr inferInstance)
  haveI : IsFinite (linearNormalizedPoint I x ell hell hxell he) :=
    IsFinite.of_comp _ (toBase I)
  haveI : IsPreimmersion (linearNormalizedPoint I x ell hell hxell he) := by
    change IsPreimmersion (Spec.map (CommRingCat.ofHom g) ≫ j)
    infer_instance
  exact IsClosedImmersion.of_isPreimmersion _
    (linearNormalizedPoint I x ell hell hxell he).isClosedMap.isClosed_range

include hell hxell he in
/-- Coordinates generating a finite algebra and normalized by a linear form
define a closed immersion of its spectrum into the projective scheme. -/
theorem closed_point_of_linear_normalized_coordinates [Module.Finite K A]
    (hgen : Function.Surjective (eval₂Hom (algebraMap K A) x)) :
    ∃ q : Spec (.of A) ⟶ scheme I, IsClosedImmersion q ∧
      q ≫ toBase I = Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  let z := Ideal.Quotient.mk I.toIdeal ell
  have hz : z ∈ grading I 1 := polynomial_class_mem_grading I ell hell
  let g := linearNormalizedPointChartMap I x ell hxell he
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨p, hp⟩ := hgen a
    exact ⟨p.eval₂ (AllCharacteristics.GradedChart.baseMap (grading I))
      (linearChartCoordinate I z hz),
      (linearNormalizedPointChartMap_eval I x ell hell hxell he p).trans hp⟩
  let j : Spec (.of (Away (grading I) z)) ⟶ scheme I :=
    Proj.awayι (grading I) z hz (by decide : 0 < 1)
  have hjopen : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (Proj.awayι (grading I) z hz (by decide : 0 < 1)))
  letI : IsOpenImmersion j := hjopen
  let q : Spec (.of A) ⟶ scheme I := Spec.map (CommRingCat.ofHom g) ≫ j
  have hs : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) :=
    IsClosedImmersion.spec_of_surjective _ hg
  have hj : j ≫ toBase I =
      Spec.map (CommRingCat.ofHom
        (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))) := by
    dsimp [j]
    change Proj.awayι (grading I) z hz (by decide : 0 < 1) ≫
      (Proj.toSpecZero (grading I) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (grading I 0)))) = _
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    rfl
  have hq : q ≫ toBase I = Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
    change (Spec.map (CommRingCat.ofHom g) ≫ j) ≫ toBase I = _
    rw [Category.assoc, hj, ← Spec.map_comp]
    apply congrArg Spec.map
    exact CommRingCat.hom_ext
      (RingHom.ext (linearNormalizedPointChartMap_base I x ell hxell he))
  have : IsFinite (q ≫ toBase I) := by
    rw [hq]
    exact (IsFinite.SpecMap_iff _).mpr
      (RingHom.finite_algebraMap.mpr inferInstance)
  have : IsFinite q := IsFinite.of_comp q (toBase I)
  have : IsPreimmersion q := by
    dsimp [q]
    infer_instance
  exact ⟨q, IsClosedImmersion.of_isPreimmersion q q.isClosedMap.isClosed_range, hq⟩

end

end PfaffianDescent
