import AllCharacteristics.VoisinFiniteEtaleResidualSpecialization
import AllCharacteristics.ClosedPointFiniteSubscheme
import AllCharacteristics.CycleDegreeAssembly
import Mathlib.RingTheory.Smooth.Field
import PfaffianDescent.VoisinGenericCubicResidual

/-!
# Specializing arbitrary effective cycles

In characteristic zero, each closed point in the support is finite étale.
Its unordered tuple specializes through the proper full tuple quotient.
Replacing each point in the cycle by its specialized cycle, with the same
multiplicity, preserves any effective degree.  The degree-four case also has
the older small-degree proof below.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AllCharacteristics

universe u

/-- Over a characteristic-zero field, the canonical finite subscheme of a
closed point is etale over the field. -/
theorem finiteSubschemeDatumOfClosedPoint_toBase_etale
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : closedPoints X) :
    Etale ((finiteSubschemeDatumOfClosedPoint f x).val.subschemeι ≫ f) := by
  let q : Spec (.of (X.residueField x.1)) ⟶ X := X.fromSpecResidueField x.1
  letI : IsClosedImmersion q := by
    dsimp only [q]
    exact isClosed_singleton_iff_isClosedImmersion.mp x.2
  letI : IsFinite (q ≫ f) := by
    dsimp only [q]
    infer_instance
  letI : Algebra k (X.residueField x.1) := pointAlgebra f x.1
  letI : Module.Finite k (X.residueField x.1) := closedPoint_moduleFinite f x
  letI : Algebra.IsSeparable k (X.residueField x.1) := inferInstance
  letI : Module.FinitePresentation k (X.residueField x.1) :=
    Module.finitePresentation_of_finite k (X.residueField x.1)
  letI : Algebra.Etale k (X.residueField x.1) := {
    formallyEtale := Algebra.FormallyEtale.of_isSeparable k (X.residueField x.1)
    finitePresentation := Algebra.FinitePresentation.of_finitePresentation
      k (X.residueField x.1)
  }
  haveI : Etale (q ≫ f) := by
    rw [← pointAlgebra_spec f x.1]
    exact HasRingHomProperty.Spec_iff.mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  unfold finiteSubschemeDatumOfClosedPoint
  exact finiteSubschemeDatumOfClosedImmersion_toBase_etale q f
    (f.residueDegree x.1) _

/-- Reindexing the canonical closed-point datum by its stated residue degree
preserves etaleness. -/
theorem finiteSubschemeDatumOfClosedPointOfResidueDegree_toBase_etale
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : closedPoints X) (n : ℕ) (hx : f.residueDegree x.1 = n) :
    Etale ((finiteSubschemeDatumOfClosedPointOfResidueDegree f x n hx).val.subschemeι ≫ f) := by
  subst n
  exact finiteSubschemeDatumOfClosedPoint_toBase_etale f x

end AllCharacteristics

namespace PfaffianDescent

open AllCharacteristics AllCharacteristics.HomogeneousProjective

variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A closed point of degree `n` on the generic coefficient-changed cubic
specializes, through the full unordered-tuple quotient, to an effective cycle
of degree `n` on the original cubic, for any input configuration size `k`. -/
theorem effectiveCycle_of_genericClosedPoint_general
    (k : ℕ)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) k)
    [Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp k) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne k D
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp k).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp k ≫
          cubicConfigurationToBase p hp k)
      (x : closedPoints (hypersurface (p.map a.hom) (hp.map a.hom)))
      (n : ℕ)
      (hn : (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)).residueDegree x.1 = n),
      ∃ w : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) w = n := by
  letI : IsIntegral (cubicConfigurationBase p hp k) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne k D
  intro a ha x n hn
  let B := cubicConfigurationBase p hp k
  let F := B.functionField
  letI : CharZero F := charZero_cubicConfigurationFunctionField_of_flat p hp k
  letI : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) k).left := by
    change IsIntegral
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) k).left
    exact
      isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
        p hp hne k D
  let Dn := finiteSubschemeDatumOfClosedPointOfResidueDegree
    (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) x n hn
  letI : Etale (Dn.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    AllCharacteristics.finiteSubschemeDatumOfClosedPointOfResidueDegree_toBase_etale
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) x n hn
  obtain ⟨s, hs⟩ :=
    exists_tupleQuotientPoint_of_finiteEtaleHypersurfaceCoefficientChange
      a.hom p hp n Dn
  have hsep : IsSeparated (hypersurfaceToBase p hp) := inferInstance
  have hsmooth : Smooth (hypersurfaceToBase p hp) := inferInstance
  have hordered : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) k).left :=
    inferInstance
  have hD : Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) :=
    inferInstance
  let I := equationIdeal p hp
  letI : IsSeparated (toBase I) := by
    dsimp only [I]
    exact hsep
  letI : Smooth (toBase I) := by
    dsimp only [I]
    exact hsmooth
  letI : IsIntegral (orderedFamilyConfigurationOver (toBase I) k).left := by
    dsimp only [I]
    exact hordered
  let D' : FiniteSubschemeDatum (toBase I) k := D
  letI : Etale (D'.val.subschemeι ≫ toBase I) := by
    dsimp only [D', I]
    exact hD
  exact effectiveZeroCycle_of_finiteEtaleSubscheme_configurationFunctionFieldTuple
    I k n D' s (hs.trans ha)

/-- Any effective cycle on the cubic over the generic configuration field
specializes to an effective cycle of the same degree on the original cubic.
The generic cycle may have multiplicities and need not define an étale finite
subscheme. -/
theorem effectiveCycle_of_genericEffectiveCycle
    (k : ℕ)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) k)
    [Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp k) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne k D
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp k).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp k ≫
          cubicConfigurationToBase p hp k)
      (zη : EffectiveZeroCycle
        (hypersurface (p.map a.hom) (hp.map a.hom))),
      ∃ z : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z =
          EffectiveZeroCycle.degree
            (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) zη := by
  letI : IsIntegral (cubicConfigurationBase p hp k) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne k D
  intro a ha zη
  apply exists_effectiveZeroCycle_of_support_replacements
    (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
    (hypersurfaceToBase p hp) zη
  intro x _
  exact effectiveCycle_of_genericClosedPoint_general k p hp hne D a ha x
    ((hypersurfaceToBase (p.map a.hom) (hp.map a.hom)).residueDegree x.1) rfl

/-- A closed point of degree `n` on the generic coefficient-changed cubic
specializes, through the full unordered-tuple quotient, to an effective cycle
of degree `n` on the original cubic. -/
theorem effectiveCycle_of_genericClosedPoint
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8)
      (x : closedPoints (hypersurface (p.map a.hom) (hp.map a.hom)))
      (n : ℕ)
      (hn : (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)).residueDegree x.1 = n),
      ∃ w : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) w = n := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha x n hn
  let B := cubicConfigurationBase p hp 8
  let F := B.functionField
  letI : CharZero F := charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left := by
    change IsIntegral
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 8).left
    exact
      isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
  let Dn := finiteSubschemeDatumOfClosedPointOfResidueDegree
    (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) x n hn
  letI : Etale (Dn.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    AllCharacteristics.finiteSubschemeDatumOfClosedPointOfResidueDegree_toBase_etale
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) x n hn
  obtain ⟨s, hs⟩ :=
    exists_tupleQuotientPoint_of_finiteEtaleHypersurfaceCoefficientChange
      a.hom p hp n Dn
  have hsep : IsSeparated (hypersurfaceToBase p hp) := inferInstance
  have hsmooth : Smooth (hypersurfaceToBase p hp) := inferInstance
  have hordered : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left :=
    inferInstance
  have hD₈ : Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) :=
    inferInstance
  let I := equationIdeal p hp
  letI : IsSeparated (toBase I) := by
    dsimp only [I]
    exact hsep
  letI : Smooth (toBase I) := by
    dsimp only [I]
    exact hsmooth
  letI : IsIntegral (orderedFamilyConfigurationOver (toBase I) 8).left := by
    dsimp only [I]
    exact hordered
  let D₈' : FiniteSubschemeDatum (toBase I) 8 := D₈
  letI : Etale (D₈'.val.subschemeι ≫ toBase I) := by
    dsimp only [D₈', I]
    exact hD₈
  exact effectiveZeroCycle_of_finiteEtaleSubscheme_configurationFunctionFieldTuple
    I 8 n D₈' s (hs.trans ha)

/-- A degree-four effective cycle on the cubic over the function field of
the rank-eight configuration space specializes to a degree-four effective
cycle on the original cubic.  The generic cycle need not be represented by
a reduced or etale rank-four subscheme. -/
theorem effectiveDegreeFourCycle_of_genericEffectiveDegreeFourCycle
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8)
      (zη : EffectiveZeroCycle
        (hypersurface (p.map a.hom) (hp.map a.hom))),
      EffectiveZeroCycle.degree
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) zη = 4 →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha zη hzη
  let B := cubicConfigurationBase p hp 8
  let F := B.functionField
  letI : CharZero F := charZero_cubicConfigurationFunctionField_of_flat p hp 8
  obtain ⟨x, hxmem, hxdeg⟩ :=
    EffectiveZeroCycle.exists_degree_one_two_four
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) zη hzη
  rcases hxdeg with hx1 | hx2 | hx4
  · obtain ⟨w, hw⟩ := effectiveCycle_of_genericClosedPoint
      p hp hne D₈ a ha x 1 hx1
    refine ⟨4 • w, ?_⟩
    rw [← EffectiveZeroCycle.degreeLinearMap_apply, map_smul,
      EffectiveZeroCycle.degreeLinearMap_apply, hw]
    norm_num
  · obtain ⟨w, hw⟩ := effectiveCycle_of_genericClosedPoint
      p hp hne D₈ a ha x 2 hx2
    refine ⟨2 • w, ?_⟩
    rw [← EffectiveZeroCycle.degreeLinearMap_apply, map_smul,
      EffectiveZeroCycle.degreeLinearMap_apply, hw]
    norm_num
  · exact effectiveCycle_of_genericClosedPoint p hp hne D₈ a ha x 4 hx4

end PfaffianDescent
