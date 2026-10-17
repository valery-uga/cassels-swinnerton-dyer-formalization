import PfaffianDescent.VoisinGeometricEightWitnessDescent
import PfaffianDescent.VoisinDetectedResidueBadLocus
import PfaffianDescent.VoisinNormalizedAmbientCoordinateChart
import PfaffianDescent.VoisinGenericEightNoCommonAtGeneric
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The geometric eight-point witness gives a good ground-field point

The algebraic-closure witness is transported to the original ordered
configuration scheme.  Standard ambient charts descend its coordinates to
the image residue field, where frame detection excludes the original bad
incidence locus.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Residue-field coordinates of the eight marked points which reconstruct
their ambient projective morphisms and detect the fixed quadratic frame. -/
def OriginalCubicOrderedEightDetectingCoordinatesAt
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) : Prop :=
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let Q := O.residueField z
  letI : Algebra K Q := pointAlgebra
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom z
  ∃ (j : Fin 8 → Fin 4) (y : Fin 8 → Fin 4 → Q),
    (∀ i, y i (j i) = 1) ∧
    (∀ i, ∃ (he0 : ∀ r ∈ (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) K)).toIdeal,
        r.eval₂ (algebraMap K Q) (y i) = 0)
      (hX : (X (j i)).eval₂ (algebraMap K Q) (y i) = 1),
      linearNormalizedPoint
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
          (y i) (X (j i)) (isHomogeneous_X K (j i)) hX he0 ≫
        quotientProjMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) =
        O.fromSpecResidueField z ≫
          (@orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp)
            hsep 8 (hypersurfaceToAmbient p hp) i)) ∧
    (∀ c : Fin 8 → Q,
      (∀ i, eval (y i)
        (homogeneousFrameMap 2 (quadraticEightFrame Q) c).1 = 0) →
      c = 0)

/-- A prime coefficient extension supplies a point of the original ordered
configuration scheme together with its detecting residue coordinates. -/
theorem exists_originalCubic_orderedEight_detectingCoordinates
    {K L : Type u} [Field K] [Field L] [IsAlgClosed L]
    (b : K →+* L)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p.map b ≠ 0)
    (hpprime : (Ideal.span ({p.map b} : Set
      (MvPolynomial (Fin 4) L))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase p hp)] :
    ∃ z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left,
      OriginalCubicOrderedEightDetectingCoordinatesAt p hp z := by
  letI : Algebra K L := b.toAlgebra
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let marked : Fin 8 →
      (O ⟶ Proj (homogeneousSubmodule (Fin 4) K)) := fun i =>
    @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 8
      (hypersurfaceToAmbient p hp) i
  obtain ⟨S, ell, hcommon, E, aK, haK, hcoordinates, hdetect⟩ :=
    exists_originalCubic_orderedEight_geometricFrameWitness
      b p hp hpne hpprime
  let z : O := aK (IsLocalRing.closedPoint L)
  have haK' : aK ≫
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    simpa only [show algebraMap K L = b by rfl] using haK
  letI : Algebra K (O.residueField z) :=
    pointAlgebra
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom z
  let e : O.residueField z →ₐ[K] L :=
    fieldPointResidueAlgHomAt
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom
      aK haK' z rfl
  have heSpec : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      O.fromSpecResidueField z = aK :=
    fieldPointResidueAlgHomAt_spec
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom
      aK haK' z rfl
  have hcharts : ∀ i : Fin 8, ∃ (j : Fin 4)
      (g : Away (homogeneousSubmodule (Fin 4) K) (X j) →+* L),
      (Spec.map (CommRingCat.ofHom g) ≫
          Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
            (isHomogeneous_X K j) (by decide : 0 < 1) =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          (O.fromSpecResidueField z ≫ marked i)) ∧
      ∀ k, g (AllCharacteristics.GradedChart.normalized
        (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K j)
        (X k) (isHomogeneous_X K k)) =
          let n := cubicSurfaceAffinePointNormalizedConeCoordinates
            ell (E i).1.1
          (n j)⁻¹ * n k := by
    intro i
    obtain ⟨j, u, gL, hu, hgLCoordinates, hgLPoint⟩ :=
      exists_ambientCoordinateChartMap_of_cubicSurfaceAffinePoint
        (p.map b) (hp.map b) ell (E i).1
          (hcommon (E i).1 (E i).2)
    let g : Away (homogeneousSubmodule (Fin 4) K) (X j) →+* L :=
      gL.comp (ambientCoefficientChartMap b j)
    refine ⟨j, g, ?_, ?_⟩
    · calc
        Spec.map (CommRingCat.ofHom g) ≫
            Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
              (isHomogeneous_X K j) (by decide : 0 < 1) =
          (Spec.map (CommRingCat.ofHom gL) ≫
            Proj.awayι (homogeneousSubmodule (Fin 4) L) (X j)
              (isHomogeneous_X L j) (by decide : 0 < 1)) ≫
                ambientCoefficientMap b := by
          calc
            _ = (Spec.map (CommRingCat.ofHom gL) ≫
                Spec.map (CommRingCat.ofHom
                  (ambientCoefficientChartMap b j))) ≫
                Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
                  (isHomogeneous_X K j) (by decide : 0 < 1) := by
              rw [← Spec.map_comp]
              rfl
            _ = Spec.map (CommRingCat.ofHom gL) ≫
                (Proj.awayι (homogeneousSubmodule (Fin 4) L) (X j)
                  (isHomogeneous_X L j) (by decide : 0 < 1) ≫
                    ambientCoefficientMap b) := by
              rw [Category.assoc, awayι_comp_ambientCoefficientMap]
            _ = _ := (Category.assoc _ _ _).symm
        _ = (cubicSurfaceAffinePointLinearNormalizedProjectivePoint
              (p.map b) (hp.map b) ell (E i).1
              (hcommon (E i).1 (E i).2) ≫
            hypersurfaceToAmbient (p.map b) (hp.map b)) ≫
              ambientCoefficientMap b := by rw [hgLPoint]
        _ = (cubicSurfaceAffinePointLinearNormalizedProjectivePoint
              (p.map b) (hp.map b) ell (E i).1
              (hcommon (E i).1 (E i).2) ≫
            projectiveCoefficientMap b
              (equationIdeal p hp)
              (equationIdeal (p.map b) (hp.map b))
              (equationIdeal_map b p hp)) ≫
                hypersurfaceToAmbient p hp := by
          have hnat : projectiveCoefficientMap b
                (equationIdeal p hp)
                (equationIdeal (p.map b) (hp.map b))
                (equationIdeal_map b p hp) ≫
              hypersurfaceToAmbient p hp =
              hypersurfaceToAmbient (p.map b) (hp.map b) ≫
                ambientCoefficientMap b := by
            exact projectiveCoefficientMap_comp_quotientProjMap b
              (equationIdeal p hp)
              (equationIdeal (p.map b) (hp.map b))
              (equationIdeal_map b p hp)
          simp only [Category.assoc]
          rw [← hnat]
          exact (Category.assoc _ _ _).symm
        _ = ((aK ≫ Over.Hom.left
              (orderedFamilyConfigurationι
                (hypersurfaceToBase p hp) 8)) ≫
              (orderedFamilyCoordinate
                (hypersurfaceToBase p hp) 8 i).left) ≫
            hypersurfaceToAmbient p hp := by
          exact congrArg (fun t => t ≫ hypersurfaceToAmbient p hp)
            (hcoordinates i).symm
        _ = aK ≫ marked i := rfl
        _ = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
            (O.fromSpecResidueField z ≫ marked i) := by
          rw [← Category.assoc, heSpec]
    · intro k
      change gL (ambientCoefficientChartMap b j
        (AllCharacteristics.GradedChart.normalized
          (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K j)
          (X k) (isHomogeneous_X K k))) = _
      rw [ambientCoefficientChartMap_coordinate, hgLCoordinates k]
      dsimp only
      rw [Units.val_inv_eq_inv_val, hu]
  choose j g hfactor hgcoords using hcharts
  let q : Fin 8 →
      (Spec (.of (O.residueField z)) ⟶
        Proj (homogeneousSubmodule (Fin 4) K)) := fun i =>
    O.fromSpecResidueField z ≫ marked i
  have hqBase : ∀ i, q i ≫ ambientToBase =
      Spec.map (CommRingCat.ofHom (algebraMap K (O.residueField z))) := by
    intro i
    have hmarkedBase : marked i ≫ ambientToBase =
        (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).hom := by
      change (((orderedFamilyConfigurationOpen
          (hypersurfaceToBase p hp) 8).ι ≫
        (orderedFamilyCoordinate
          (hypersurfaceToBase p hp) 8 i).left) ≫
        hypersurfaceToAmbient p hp) ≫ ambientToBase = _
      have hamb : hypersurfaceToAmbient p hp ≫ ambientToBase =
          hypersurfaceToBase p hp := by
        exact quotientProjMap_toBase (equationIdeal p hp)
      simp only [Category.assoc]
      rw [hamb]
      change Over.Hom.left (orderedFamilyConfigurationι
          (hypersurfaceToBase p hp) 8) ≫
          (orderedFamilyCoordinate
            (hypersurfaceToBase p hp) 8 i).left ≫
            hypersurfaceToBase p hp = _
      rw [orderedFamilyCoordinate_toBase
        (f := hypersurfaceToBase p hp)]
      exact (orderedFamilyConfigurationι
        (hypersurfaceToBase p hp) 8).w
    calc
      q i ≫ ambientToBase =
          O.fromSpecResidueField z ≫
            (orderedFamilyConfigurationOver
              (hypersurfaceToBase p hp) 8).hom := by
        dsimp only [q]
        rw [Category.assoc, hmarkedBase]
      _ = Spec.map (CommRingCat.ofHom
          (algebraMap K (O.residueField z))) := by
        exact (pointAlgebra_spec
          (orderedFamilyConfigurationOver
            (hypersurfaceToBase p hp) 8).hom z).symm
  have hdesc : ∀ i, ∃ y : Fin 4 → O.residueField z,
      y (j i) = 1 ∧
      (∀ k, e (y k) = g i
        (AllCharacteristics.GradedChart.normalized
          (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K (j i))
          (X k) (isHomogeneous_X K k))) ∧
      ∃ (he0 : ∀ r ∈ (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) K)).toIdeal,
          r.eval₂ (algebraMap K (O.residueField z)) y = 0)
        (hX : (X (j i)).eval₂
          (algebraMap K (O.residueField z)) y = 1),
        linearNormalizedPoint
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
            y (X (j i)) (isHomogeneous_X K (j i)) hX he0 ≫
          quotientProjMap
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) = q i := by
    intro i
    exact exists_coordinates_of_ambientPoint_chart_factorization
      e (q i) (hqBase i) (j i) (g i) (hfactor i)
  choose y hyj hymap hmarked using hdesc
  let xchart : Fin 8 → Fin 4 → L := fun i k => g i
    (AllCharacteristics.GradedChart.normalized
      (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K (j i))
      (X k) (isHomogeneous_X K k))
  have hxchartDetect : ∀ c : Fin 8 → L,
      (∀ i, eval (xchart i)
        (homogeneousFrameMap 2 (quadraticEightFrame L) c).1 = 0) →
      c = 0 := by
    let n : Fin 8 → Fin 4 → L := fun i =>
      cubicSurfaceAffinePointNormalizedConeCoordinates ell (E i).1.1
    let s : Fin 8 → L := fun i => (n i (j i))⁻¹ *
      (MvPolynomial.aeval (E i).1.1 (homogeneousLinearForm ell))⁻¹
    have hs : ∀ i, s i ≠ 0 := by
      intro i
      have hnj : n i (j i) ≠ 0 := by
        have hself : xchart i (j i) = 1 := by
          dsimp only [xchart]
          rw [← hymap i (j i), hyj i, map_one]
        have hratio := hgcoords i (j i)
        change xchart i (j i) =
          (n i (j i))⁻¹ * n i (j i) at hratio
        intro hzero
        rw [hself, hzero, inv_zero, zero_mul] at hratio
        exact one_ne_zero hratio
      exact mul_ne_zero (inv_ne_zero hnj)
        (inv_ne_zero (hcommon (E i).1 (E i).2))
    have hxscale : xchart = fun i => s i • (E i).1.1 := by
      funext i k
      rw [show xchart i k = (n i (j i))⁻¹ * n i k by
        exact hgcoords i k]
      simp only [n, s, cubicSurfaceAffinePointNormalizedConeCoordinates,
        Pi.smul_apply, smul_eq_mul]
      ring
    have hsDetect := quadraticEightFrame_detection_rowScaling
      (fun i => (E i).1.1) s hs hdetect
    simpa only [hxscale] using hsDetect
  have hyDetect : ∀ c : Fin 8 → O.residueField z,
      (∀ i, eval (y i)
        (homogeneousFrameMap 2
          (quadraticEightFrame (O.residueField z)) c).1 = 0) →
      c = 0 := by
    apply quadraticEightFrame_detection_reflects e.toRingHom y
    intro c hc
    apply hxchartDetect c
    intro i
    have hfun : (fun k => e (y i k)) = xchart i := by
      funext k
      exact hymap i k
    rw [← hfun]
    exact hc i
  exact ⟨z, j, y, hyj, hmarked, hyDetect⟩

/-- A prime coefficient extension supplies a point of the original ordered
configuration scheme outside the fixed quadratic-frame bad locus. -/
theorem exists_originalCubic_orderedEight_goodPoint
    {K L : Type u} [Field K] [Field L] [IsAlgClosed L]
    (b : K →+* L)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p.map b ≠ 0)
    (hpprime : (Ideal.span ({p.map b} : Set
      (MvPolynomial (Fin 4) L))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase p hp)] :
    ∃ z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left,
      z ∉ quadraticEightFixedFrameBadLocus p hp := by
  obtain ⟨z, j, y, hyj, hmarked, hyDetect⟩ :=
    exists_originalCubic_orderedEight_detectingCoordinates
      b p hp hpne hpprime
  refine ⟨z, ?_⟩
  exact residuePoint_not_mem_quadraticEightFrameBadLocus_of_detecting_coordinates
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom
    (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 8
      (hypersurfaceToAmbient p hp) i)
    z j y hyj hmarked hyDetect

/-- Every nonzero smooth cubic over an arbitrary field has a point of its
ordered eight-point configuration carrying detecting residue coordinates. -/
theorem exists_smoothCubic_orderedEight_detectingCoordinates
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    [hsep : IsSeparated (hypersurfaceToBase p hp)] :
    ∃ z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left,
      OriginalCubicOrderedEightDetectingCoordinatesAt p hp z := by
  let L : Type u := AlgebraicClosure K
  letI : Field L := inferInstanceAs (Field (AlgebraicClosure K))
  letI : Algebra K L := inferInstanceAs (Algebra K (AlgebraicClosure K))
  have hprime := smoothCubic_coefficientExtension_ne_zero_and_prime
    (algebraMap K L) p hp hpne
  exact exists_originalCubic_orderedEight_detectingCoordinates
    (algebraMap K L) p hp hprime.1 hprime.2

/-- Every nonzero smooth cubic over an arbitrary field has a point of its
ordered eight-point configuration outside the fixed quadratic-frame bad
locus.  The detecting configuration is constructed over an algebraic closure,
then retained as a (possibly non-rational) point of the original configuration
scheme. -/
theorem exists_smoothCubic_orderedEight_goodPoint
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    [hsep : IsSeparated (hypersurfaceToBase p hp)] :
    ∃ z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left,
      z ∉ quadraticEightFixedFrameBadLocus p hp := by
  obtain ⟨z, j, y, hyj, hmarked, hyDetect⟩ :=
    exists_smoothCubic_orderedEight_detectingCoordinates p hp hpne
  refine ⟨z, ?_⟩
  exact residuePoint_not_mem_quadraticEightFrameBadLocus_of_detecting_coordinates
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom
    (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp)
      hsep 8 (hypersurfaceToAmbient p hp) i)
    z j y hyj hmarked hyDetect

end PfaffianDescent
