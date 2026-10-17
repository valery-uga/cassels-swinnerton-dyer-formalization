import PfaffianDescent.CubicExtensionVectorConfigurationWitness
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridAffineChart

/-! Actual integral affine configuration charts in a chosen ground-field linear chart. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

def cubicGroundChartClass
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (c : Fin 4 → K) :
    CoordinateRing (equationIdeal p hp) :=
  Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c)

theorem cubicGroundChartClass_mem
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (c : Fin 4 → K) :
    cubicGroundChartClass p hp c ∈ grading (equationIdeal p hp) 1 :=
  polynomial_class_mem_grading (equationIdeal p hp) (homogeneousLinearForm c)
    (homogeneousLinearForm_isHomogeneous c)

theorem cubicExtensionVectorPointInGroundChart_mem
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (v : Fin 4 → L)
    (hv : p.eval₂ (algebraMap K L) v = 0)
    (hc : (homogeneousLinearForm c).eval₂ (algebraMap K L) v ≠ 0) :
    cubicExtensionVectorPointInGroundChart p hp c v hv hc (IsLocalRing.closedPoint L) ∈
      Proj.basicOpen (grading (equationIdeal p hp)) (cubicGroundChartClass p hp c) := by
  let I := equationIdeal p hp
  let z := cubicGroundChartClass p hp c
  let hz := cubicGroundChartClass_mem p hp c
  let j := Proj.awayι (grading I) z hz (by decide : 0 < 1)
  let he := voisinDegreeTenSelectedAvoidance_equationIdeal_eval₂_zero p hp
    (cubicGroundChartNormalizedVector c v) (cubicGroundChartNormalizedVector_cubic p hp c v hv)
  have hOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K L) (cubicGroundChartNormalizedVector c v)) he) z = 1 :=
    cubicGroundChartNormalizedVector_linearForm c v hc
  have hmem : cubicExtensionVectorPointInGroundChart p hp c v hv hc
      (IsLocalRing.closedPoint L) ∈ j.opensRange := by
    change (linearNormalizedPointAt I (cubicGroundChartNormalizedVector c v) he z hz hOne)
      (IsLocalRing.closedPoint L) ∈ j.opensRange
    refine ⟨(Spec.map (CommRingCat.ofHom (linearNormalizedPointChartMapAt I
      (cubicGroundChartNormalizedVector c v) he z hz hOne))) (IsLocalRing.closedPoint L), ?_⟩
    rfl
  simpa only [j, Proj.opensRange_awayι] using hmem

theorem cubicGroundChart_orderedConfiguration_mem_commonOpen
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {n : ℕ} (c : Fin 4 → K) (v : Fin n → Fin 4 → L)
    (hv : ∀ i, p.eval₂ (algebraMap K L) (v i) = 0)
    (hc : ∀ i, (homogeneousLinearForm c).eval₂ (algebraMap K L) (v i) ≠ 0)
    (A : Spec (.of L) ⟶
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
    (hcoord : ∀ i, (A ≫ Over.Hom.left (orderedFamilyConfigurationι
      (hypersurfaceToBase p hp) n)) ≫ (orderedFamilyCoordinate
        (hypersurfaceToBase p hp) n i).left =
      cubicExtensionVectorPointInGroundChart p hp c (v i) (hv i) (hc i)) :
    (A (IsLocalRing.closedPoint L)).val ∈ orderedFamilyCommonOpen
      (hypersurfaceToBase p hp)
      (Proj.basicOpen (grading (equationIdeal p hp)) (cubicGroundChartClass p hp c)) n := by
  apply (mem_orderedFamilyCommonOpen_iff (hypersurfaceToBase p hp)
    (Proj.basicOpen (grading (equationIdeal p hp)) (cubicGroundChartClass p hp c)) n _).mpr
  intro i
  have hi := congrArg (fun q : Spec (.of L) ⟶ hypersurface p hp =>
    q (IsLocalRing.closedPoint L)) (hcoord i)
  change ((A ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
    (orderedFamilyCoordinate (hypersurfaceToBase p hp) n i).left) (IsLocalRing.closedPoint L) ∈ _
  exact hi.symm ▸ cubicExtensionVectorPointInGroundChart_mem p hp c (v i) (hv i) (hc i)

/-- Actual compatible integral ordered/unordered affine charts through the
extension-field witness, with literal common-chart coordinate functions. -/
theorem cubicGroundChart_exists_integral_affine_configuration_charts
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    [IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left]
    [IsIntegral (cubicConfigurationBase p hp n)]
    (c : Fin 4 → K) (v : Fin n → Fin 4 → L)
    (hv : ∀ i, p.eval₂ (algebraMap K L) (v i) = 0)
    (hc : ∀ i, (homogeneousLinearForm c).eval₂ (algebraMap K L) (v i) ≠ 0)
    (A : Spec (.of L) ⟶
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
    (hcoord : ∀ k, (A ≫ Over.Hom.left (orderedFamilyConfigurationι
      (hypersurfaceToBase p hp) n)) ≫ (orderedFamilyCoordinate
        (hypersurfaceToBase p hp) n k).left =
      cubicExtensionVectorPointInGroundChart p hp c (v k) (hv k) (hc k)) :
    ∃ (U Q : Scheme.{u}) (_ : IsAffine U) (_ : IsAffine Q)
      (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
      (j : Q ⟶ cubicConfigurationBase p hp n) (r : U ⟶ Q)
      (a : Spec (.of L) ⟶ U)
      (t : Fin n → (U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
        (cubicGroundChartClass p hp c))))),
      IsOpenImmersion i ∧ IsOpenImmersion j ∧ Surjective r ∧ IsFinite r ∧
      IsIntegral U ∧ IsIntegral Q ∧ a ≫ i = A ∧
      genericPoint (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left ∈ Set.range i ∧
      genericPoint (cubicConfigurationBase p hp n) ∈ Set.range j ∧
      i ≫ configurationQuotientMap (equationIdeal p hp) n = r ≫ j ∧
      (∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
          (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c)
          (by decide : 0 < 1) =
        (i ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) n k).left) ∧
      ∀ k z, a.appTop.hom (pulledLinearChartCoordinate (equationIdeal p hp)
        (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c) U (t k) z) =
          (StructureSheaf.globalSectionsIso L).hom (cubicGroundChartNormalizedVector c (v k) z) := by
  classical
  let I := equationIdeal p hp
  let z := cubicGroundChartClass p hp c
  let hz := cubicGroundChartClass_mem p hp c
  let V : (hypersurface p hp).affineOpens :=
    ⟨Proj.basicOpen (grading I) z,
      Proj.isAffineOpen_basicOpen (grading I) z hz (by decide : 0 < 1)⟩
  let x := A (IsLocalRing.closedPoint L)
  have hxV := cubicGroundChart_orderedConfiguration_mem_commonOpen p hp c v hv hc A hcoord
  obtain ⟨U, hUa, τ, hτ₁, hτcomp, i, hi, hτi, b, hb, j, hj,
    hxi, hcomm, _, hinside⟩ :=
    exists_projectiveConfigurationQuotient_affineChart_inside_commonOpen
      (grading I) (hypersurfaceToBase p hp) n V x hxV
  let Q := affineSchemeActionQuotient (Equiv.Perm (Fin n)) τ hτ₁ hτcomp b hb
  let r : U ⟶ Q := affineSchemeActionQuotientMap (Equiv.Perm (Fin n)) τ hτ₁ hτcomp b hb
  have hQa : IsAffine Q := inferInstance
  have hrSurj : Surjective r := by dsimp [r]; infer_instance
  have hrInt : IsIntegralHom r := by dsimp [r]; infer_instance
  letI : IsSeparated (hypersurfaceToBase p hp) := isSeparated_homogeneousToBase I
  letI : Etale r := by
    dsimp [r]
    exact etale_affineConfigurationActionQuotientMap (hypersurfaceToBase p hp) n
      τ hτ₁ hτcomp b hb i hτi
  have hrFinite : IsFinite r :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType r).mpr ⟨hrInt, inferInstance⟩
  letI : IsOpenImmersion i := hi
  letI : IsOpenImmersion j := hj
  letI : Nonempty U := ⟨Classical.choose hxi⟩
  have hUi : IsIntegral U := isIntegral_of_isOpenImmersion i
  have hQpoint : configurationQuotientMap I n x ∈ Set.range j := by
    obtain ⟨u, hu⟩ := hxi
    refine ⟨r u, ?_⟩
    have hs := congrArg (fun f : U ⟶ cubicConfigurationBase p hp n => f u) hcomm
    exact hs.symm.trans (congrArg (configurationQuotientMap I n) hu)
  letI : Nonempty Q := ⟨Classical.choose hQpoint⟩
  have hQi : IsIntegral Q := isIntegral_of_isOpenImmersion j
  have hgenU := (genericPoint_specializes x).mem_open (IsOpenImmersion.isOpen_range i) hxi
  letI : IsIntegral (configurationQuotientOpen I n).toScheme :=
    inferInstanceAs (IsIntegral (cubicConfigurationBase p hp n))
  have hgenQ : genericPoint (cubicConfigurationBase p hp n) ∈ Set.range j :=
    (genericPoint_specializes (configurationQuotientMap I n x)).mem_open
      (IsOpenImmersion.isOpen_range j) hQpoint
  obtain ⟨a, ha⟩ := exists_fieldPoint_lift_through_openImmersion i A hxi
  let chart := Proj.awayι (grading I) z hz (by decide : 0 < 1)
  have hcommon : ∀ u : U, (i u).val ∈
      orderedFamilyCommonOpen (hypersurfaceToBase p hp) chart.opensRange n := by
    intro u
    rw [Proj.opensRange_awayι]
    exact hinside u
  have hlifts := voisinDegreeTenSelectedAvoidance_ordered_coordinate_lifts
    (hypersurfaceToBase p hp) n chart i hcommon
  choose t ht using hlifts
  refine ⟨U, Q, hUa, hQa, i, j, r, a, t, hi, hj, hrSurj, hrFinite,
    hUi, hQi, ha, hgenU, hgenQ, hcomm, ht, ?_⟩
  intro k d
  apply pulledLinearChartCoordinate_value_of_normalizedPointAt (equationIdeal p hp)
    z hz (cubicGroundChartNormalizedVector c (v k)) _ _ U a (t k)
  rw [Category.assoc, ht k]
  change ((a ≫ i) ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
    (orderedFamilyCoordinate (hypersurfaceToBase p hp) n k).left = _
  rw [ha]
  exact hcoord k

end PfaffianDescent
