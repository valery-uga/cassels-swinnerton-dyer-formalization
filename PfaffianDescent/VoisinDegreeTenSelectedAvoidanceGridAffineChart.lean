import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridOriginalCoordinates
import AllCharacteristics.ProjectiveConfigurationAffineCharts
import AllCharacteristics.ConfigurationFreeQuotientCharts

/-! # Actual integral affine configuration charts through the selected grid -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial Module HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_ordered_configuration_mem_zero_chart
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {n : ℕ} (v : Fin n → Fin 4 → L)
    (hpv : ∀ i, p.eval₂ (algebraMap K L) (v i) = 0) (hv0 : ∀ i, v i 0 = 1)
    (A : Spec (.of L) ⟶
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
    (hcoord : ∀ i, (A ≫ Over.Hom.left
        (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) n i).left =
      voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver p hp (v i) (hpv i) (hv0 i)) :
    (A (IsLocalRing.closedPoint L)).val ∈ orderedFamilyCommonOpen (hypersurfaceToBase p hp)
      (Proj.basicOpen (grading (equationIdeal p hp)) (coordinate (equationIdeal p hp) 0)) n := by
  apply (mem_orderedFamilyCommonOpen_iff (hypersurfaceToBase p hp)
    (Proj.basicOpen (grading (equationIdeal p hp)) (coordinate (equationIdeal p hp) 0)) n
    (A (IsLocalRing.closedPoint L)).val).mpr
  intro i
  have hi := congrArg (fun f : Spec (.of L) ⟶ hypersurface p hp =>
    f (IsLocalRing.closedPoint L)) (hcoord i)
  change ((A ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
    (orderedFamilyCoordinate (hypersurfaceToBase p hp) n i).left) (IsLocalRing.closedPoint L) ∈ _
  let chart := Proj.awayι (grading (equationIdeal p hp)) (coordinate (equationIdeal p hp) 0)
    (coordinate_mem (equationIdeal p hp) 0) (by decide : 0 < 1)
  have hmem : voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver p hp (v i) (hpv i) (hv0 i)
      (IsLocalRing.closedPoint L) ∈ chart.opensRange := by
    refine ⟨(Spec.map (CommRingCat.ofHom (linearNormalizedPointChartMapAt (equationIdeal p hp)
      (v i) (voisinDegreeTenSelectedAvoidance_equationIdeal_eval₂_zero p hp (v i) (hpv i))
      (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0)
      (by change (eval₂Hom (algebraMap K L) (v i)) (X 0) = 1; simpa using hv0 i))))
        (IsLocalRing.closedPoint L), ?_⟩
    rfl
  have hpointmem :
      voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver p hp (v i) (hpv i) (hv0 i)
        (IsLocalRing.closedPoint L) ∈
        Proj.basicOpen (grading (equationIdeal p hp)) (coordinate (equationIdeal p hp) 0) := by
    simpa only [chart, Proj.opensRange_awayι] using hmem
  exact hi.symm ▸ hpointmem

set_option backward.isDefEq.respectTransparency false in
/-- Coordinates confined to one open chart lift there, for any number of
ordered points. This is the native sixteen-coordinate form of the existing
eight-coordinate open-immersion argument. -/
theorem voisinDegreeTenSelectedAvoidance_ordered_coordinate_lifts
    {X S U W : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (n : ℕ)
    (j : W ⟶ X) [IsOpenImmersion j]
    (i : U ⟶ (orderedFamilyConfigurationOver f n).left)
    (hinside : ∀ u : U, (i u).val ∈ orderedFamilyCommonOpen f j.opensRange n) :
    ∀ k : Fin n, ∃ t : U ⟶ W, t ≫ j =
      (i ≫ Over.Hom.left (orderedFamilyConfigurationι f n)) ≫
        (orderedFamilyCoordinate f n k).left := by
  intro k
  let a : U ⟶ X := (i ≫ Over.Hom.left (orderedFamilyConfigurationι f n)) ≫
    (orderedFamilyCoordinate f n k).left
  have hrange : Set.range a ⊆ Set.range j := by
    rintro x ⟨u, rfl⟩
    have hu := (mem_orderedFamilyCommonOpen_iff f j.opensRange n (i u).val).mp (hinside u) k
    change Over.Hom.left (orderedFamilyCoordinate f n k) (i u).val ∈ j.opensRange at hu
    change a u ∈ Set.range j
    exact hu
  exact ⟨IsOpenImmersion.lift j a hrange, IsOpenImmersion.lift_fac j a hrange⟩

set_option backward.isDefEq.respectTransparency false in
/-- Actual compatible integral ordered/unordered affine charts through an
extension-field normalized configuration. They reach both generic points and
carry actual coordinate lifts into the original cubic's fixed `X₀` chart. -/
theorem voisinDegreeTenSelectedAvoidance_exists_integral_affine_charts
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    [IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left]
    [IsIntegral (cubicConfigurationBase p hp n)]
    (v : Fin n → Fin 4 → L)
    (hpv : ∀ i, p.eval₂ (algebraMap K L) (v i) = 0) (hv0 : ∀ i, v i 0 = 1)
    (A : Spec (.of L) ⟶
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
    (hcoord : ∀ k, (A ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) n k).left =
      voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver p hp (v k) (hpv k) (hv0 k)) :
    ∃ (U Q : Scheme.{u}) (_ : IsAffine U) (_ : IsAffine Q)
      (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
      (j : Q ⟶ cubicConfigurationBase p hp n) (r : U ⟶ Q)
      (aU : Spec (.of L) ⟶ U)
      (t : Fin n → (U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
        (coordinate (equationIdeal p hp) 0))))),
      IsOpenImmersion i ∧ IsOpenImmersion j ∧ Surjective r ∧ IsFinite r ∧
      IsIntegral U ∧ IsIntegral Q ∧ aU ≫ i = A ∧
      genericPoint (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left ∈ Set.range i ∧
      genericPoint (cubicConfigurationBase p hp n) ∈ Set.range j ∧
      i ≫ configurationQuotientMap (equationIdeal p hp) n = r ≫ j ∧
      (∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
          (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0)
          (by decide : 0 < 1) =
        (i ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) n k).left) ∧
      ∀ k z, aU.appTop.hom (pulledLinearChartCoordinate (equationIdeal p hp)
        (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0) U (t k) z) =
        (StructureSheaf.globalSectionsIso L).hom (v k z) := by
  classical
  let I := equationIdeal p hp
  let V : (hypersurface p hp).affineOpens :=
    ⟨Proj.basicOpen (grading I) (coordinate I 0),
      Proj.isAffineOpen_basicOpen (grading I) (coordinate I 0) (coordinate_mem I 0) (by decide : 0 < 1)⟩
  have hAV := voisinDegreeTenSelectedAvoidance_ordered_configuration_mem_zero_chart p hp v hpv hv0 A hcoord
  let x := A (IsLocalRing.closedPoint L)
  obtain ⟨U, hUa, τ, hτ₁, hτcomp, i, hi, hτi, b, hb, j, hj,
    hxi, hcomm, _, hinside⟩ :=
    exists_projectiveConfigurationQuotient_affineChart_inside_commonOpen
      (grading I) (hypersurfaceToBase p hp) n V x hAV
  let Q := affineSchemeActionQuotient (Equiv.Perm (Fin n)) τ hτ₁ hτcomp b hb
  let r : U ⟶ Q := affineSchemeActionQuotientMap (Equiv.Perm (Fin n)) τ hτ₁ hτcomp b hb
  have hQa : IsAffine Q := inferInstance
  have hsurjr : Surjective r := by dsimp [r]; infer_instance
  have hintr : IsIntegralHom r := by dsimp [r]; infer_instance
  letI : IsSeparated (hypersurfaceToBase p hp) := isSeparated_homogeneousToBase I
  have hret : Etale r := by
    dsimp [r]
    exact etale_affineConfigurationActionQuotientMap (hypersurfaceToBase p hp) n
      τ hτ₁ hτcomp b hb i hτi
  letI : Etale r := hret
  have hfinr : IsFinite r :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType r).mpr ⟨hintr, inferInstance⟩
  letI : IsOpenImmersion i := hi
  letI : IsOpenImmersion j := hj
  letI : Nonempty U := ⟨Classical.choose hxi⟩
  have hUi : IsIntegral U := isIntegral_of_isOpenImmersion i
  have hBj : configurationQuotientMap I n x ∈ Set.range j := by
    obtain ⟨u, hu⟩ := hxi
    refine ⟨r u, ?_⟩
    have hs := congrArg (fun f : U ⟶ cubicConfigurationBase p hp n => f u) hcomm
    exact hs.symm.trans (congrArg (configurationQuotientMap I n) hu)
  letI : Nonempty Q := ⟨Classical.choose hBj⟩
  have hQi : IsIntegral Q := isIntegral_of_isOpenImmersion j
  have hgenU := (genericPoint_specializes x).mem_open (IsOpenImmersion.isOpen_range i) hxi
  letI : IsIntegral (configurationQuotientOpen I n).toScheme :=
    inferInstanceAs (IsIntegral (cubicConfigurationBase p hp n))
  have hgenQ : genericPoint (cubicConfigurationBase p hp n) ∈ Set.range j :=
    (genericPoint_specializes (configurationQuotientMap I n x)).mem_open
      (IsOpenImmersion.isOpen_range j) hBj
  obtain ⟨aU, haU⟩ := exists_fieldPoint_lift_through_openImmersion i A hxi
  let chart := Proj.awayι (grading I) (coordinate I 0) (coordinate_mem I 0) (by decide : 0 < 1)
  have hcommon : ∀ u : U, (i u).val ∈ orderedFamilyCommonOpen (hypersurfaceToBase p hp) chart.opensRange n := by
    intro u
    rw [Proj.opensRange_awayι]
    exact hinside u
  have hlifts := voisinDegreeTenSelectedAvoidance_ordered_coordinate_lifts
    (hypersurfaceToBase p hp) n chart i hcommon
  choose t ht using hlifts
  refine ⟨U, Q, hUa, hQa, i, j, r, aU, t, hi, hj, hsurjr, hfinr,
    hUi, hQi, haU, hgenU, hgenQ, hcomm, ht, ?_⟩
  intro k z
  apply voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver_pulled_coordinate
    p hp (v k) (hpv k) (hv0 k) U aU (t k)
  rw [Category.assoc, ht k]
  change ((aU ≫ i) ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
    (orderedFamilyCoordinate (hypersurfaceToBase p hp) n k).left = _
  rw [haU]
  exact hcoord k

end PfaffianDescent
