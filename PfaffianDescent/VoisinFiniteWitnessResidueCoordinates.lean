import PfaffianDescent.VoisinGeometricEightGoodPoint

/-!
# Residue coordinates retaining a geometric finite witness

The earlier good-point descent only retained quadratic-frame detection.  For
finiteness descent we also retain the residue-field embedding and the exact
row scaling relating residue coordinates to a prescribed geometric
configuration.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem normalizedVectorInLinearChart_map
    {Q L : Type u} [Field Q] [Field L]
    (e : Q →+* L) (c x : Fin 4 → Q) :
    (fun j => e (normalizedVectorInLinearChart c x j)) =
      normalizedVectorInLinearChart (fun j => e (c j))
        (fun j => e (x j)) := by
  funext j
  simp only [normalizedVectorInLinearChart, Pi.smul_apply, smul_eq_mul,
    homogeneousLinearForm, MvPolynomial.eval_C, MvPolynomial.eval_X,
    map_mul, map_inv₀, map_sum]

theorem normalizedVectorInLinearChart_smul
    {L : Type u} [Field L]
    (c y : Fin 4 → L) (s : L) (hs : s ≠ 0) :
    normalizedVectorInLinearChart c (s • y) =
      normalizedVectorInLinearChart c y := by
  funext j
  simp only [normalizedVectorInLinearChart, homogeneousLinearForm,
    MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Pi.smul_apply, smul_eq_mul]
  have heval : (∑ i, c i * (s * y i)) = s * ∑ i, c i * y i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heval]
  field_simp

theorem exists_residueCoordinates_of_originalCubic_geometricConfiguration
    {K L : Type u} [Field K] [Field L]
    (b : K →+* L)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (y : Fin 8 → Fin 4 → L)
    (hzero : ∀ i, (p.map b).eval (y i) = 0)
    (hy0 : ∀ i, y i ≠ 0)
    (ell : Fin 4 → L)
    (hell : ∀ i, (homogeneousLinearForm ell).eval (y i) ≠ 0)
    (aK : Spec (.of L) ⟶
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
    (haK : aK ≫
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom =
        Spec.map (CommRingCat.ofHom b))
    (hcoordinates : ∀ i, (aK ≫ Over.Hom.left
        (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i).left =
      cubicSurfaceAffinePointLinearNormalizedProjectivePoint
        (p.map b) (hp.map b) ell
        (⟨y i, by simpa using hzero i, hy0 i⟩ :
          cubicSurfaceAffinePoints (p.map b))
        (by simpa using hell i) ≫
      projectiveCoefficientMap b (equationIdeal p hp)
        (equationIdeal (p.map b) (hp.map b)) (equationIdeal_map b p hp))
    [hsep : IsSeparated (hypersurfaceToBase p hp)] :
    letI : Algebra K L := b.toAlgebra
    ∃ z : (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left,
      let O := (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left
      let Q := O.residueField z
      letI : Algebra K Q := pointAlgebra
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom z
      ∃ (e : Q →ₐ[K] L) (j : Fin 8 → Fin 4)
        (x : Fin 8 → Fin 4 → Q),
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          O.fromSpecResidueField z = aK ∧
        (∀ i, x i (j i) = 1) ∧
        (∀ i k, e (x i k) =
          let n := cubicSurfaceAffinePointNormalizedConeCoordinates ell (y i)
          (n (j i))⁻¹ * n k) ∧
        ∀ i, ∃ (he0 : ∀ r ∈ (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) K)).toIdeal,
            r.eval₂ (algebraMap K Q) (x i) = 0)
          (hX : (X (j i)).eval₂ (algebraMap K Q) (x i) = 1),
          linearNormalizedPoint
              (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
              (x i) (X (j i)) (isHomogeneous_X K (j i)) hX he0 ≫
            quotientProjMap
              (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) =
            O.fromSpecResidueField z ≫
              (@orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
                (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp)
                hsep 8 (hypersurfaceToAmbient p hp) i) := by
  dsimp only
  letI : Algebra K L := b.toAlgebra
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let marked : Fin 8 →
      (O ⟶ Proj (homogeneousSubmodule (Fin 4) K)) := fun i =>
    @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp) hsep 8
      (hypersurfaceToAmbient p hp) i
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
          let n := cubicSurfaceAffinePointNormalizedConeCoordinates ell (y i)
          (n j)⁻¹ * n k := by
    intro i
    obtain ⟨j, u, gL, hu, hgLCoordinates, hgLPoint⟩ :=
      exists_ambientCoordinateChartMap_of_cubicSurfaceAffinePoint
        (p.map b) (hp.map b) ell
        (⟨y i, by simpa using hzero i, hy0 i⟩ :
          cubicSurfaceAffinePoints (p.map b))
        (by simpa using hell i)
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
              (p.map b) (hp.map b) ell
              (⟨y i, by simpa using hzero i, hy0 i⟩ :
                cubicSurfaceAffinePoints (p.map b))
              (by simpa using hell i) ≫
            hypersurfaceToAmbient (p.map b) (hp.map b)) ≫
              ambientCoefficientMap b := by rw [hgLPoint]
        _ = (cubicSurfaceAffinePointLinearNormalizedProjectivePoint
              (p.map b) (hp.map b) ell
              (⟨y i, by simpa using hzero i, hy0 i⟩ :
                cubicSurfaceAffinePoints (p.map b))
              (by simpa using hell i) ≫
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
                ambientCoefficientMap b :=
            projectiveCoefficientMap_comp_quotientProjMap b
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
          hypersurfaceToBase p hp := quotientProjMap_toBase (equationIdeal p hp)
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
  have hdesc : ∀ i, ∃ x : Fin 4 → O.residueField z,
      x (j i) = 1 ∧
      (∀ k, e (x k) = g i
        (AllCharacteristics.GradedChart.normalized
          (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K (j i))
          (X k) (isHomogeneous_X K k))) ∧
      ∃ (he0 : ∀ r ∈ (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) K)).toIdeal,
          r.eval₂ (algebraMap K (O.residueField z)) x = 0)
        (hX : (X (j i)).eval₂
          (algebraMap K (O.residueField z)) x = 1),
        linearNormalizedPoint
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
            x (X (j i)) (isHomogeneous_X K (j i)) hX he0 ≫
          quotientProjMap
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) = q i := by
    intro i
    exact exists_coordinates_of_ambientPoint_chart_factorization
      e (q i) (hqBase i) (j i) (g i) (hfactor i)
  choose x hxj hxmap hmarked using hdesc
  refine ⟨z, e, j, x, heSpec, hxj, ?_, ?_⟩
  · intro i k
    exact (hxmap i k).trans (hgcoords i k)
  · intro i
    simpa only [q] using hmarked i

end PfaffianDescent
