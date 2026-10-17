import PfaffianDescent.VoisinNormalizedFieldPointRegular
import PfaffianDescent.ProjectiveCoefficientIdealMap

/-!
# Flat intersection charts at local points of the moving-cubic family

The field-point regularity theorem is applied to the residue point of an
actual local morphism into Voisin's nontrivial moving-cubic family. The
resulting regular cubic supplies normalized intersection charts flat over
the local ring. This leaves only the geometric identification of these
charts with the pullback-defined relative zero locus.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A local point of the actual nontrivial moving-cubic family has a
normalized coefficient chart on which every affine chart of the two-cubic
intersection is flat over the local parameter ring. -/
theorem flatGradedNontrivialOpen_localPoint_intersectionCharts_flat
    {K R T : Type u} [Field K] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra K R]
    [CommRing T] [IsLocalRing T] [Algebra R T]
    [Algebra K T] [IsScalarTower K R T]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase
      (a.map (algebraMap K (IsLocalRing.ResidueField T)))
      (ha.map (algebraMap K (IsLocalRing.ResidueField T))))]
    (n : Spec (.of T) ⟶
      flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0)
    (hn : n ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
        J r q e hRank a ha ha0 =
      Spec.map (CommRingCat.ofHom (algebraMap R T))) :
    ∃ (p : MvPolynomial (Fin 4) (IsLocalRing.ResidueField T))
      (_hp : p.IsHomogeneous 3)
      (j : Monomials (Fin 4) 3) (_hj : p.coeff j.1 ≠ 0)
      (f : ParameterChartRing K (Fin 4) 3 j →+* T),
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j =
        n ≫ flatGradedNontrivialOpenToGlobalParameters
          a ha J r q e hRank ha0 ∧
      ∀ i : Fin 4,
        let q := (normalizedForm K (Fin 4) 3 j).map f
        let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
        let Jₐ := equationIdeal (a.map (algebraMap K T))
          (ha.map (algebraMap K T))
        ((chartQuotientMap Jₐ (Jₐ ⊔ equationIdeal q hq)
          (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) i).comp
          (chartBaseMap Jₐ i)).Flat := by
  let S := IsLocalRing.ResidueField T
  let g := algebraMap T S
  let b := algebraMap R S
  let m : Spec (.of S) ⟶
      flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0 :=
    Spec.map (CommRingCat.ofHom g) ≫ n
  have hm : m ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
      J r q e hRank a ha ha0 =
      Spec.map (CommRingCat.ofHom b) := by
    calc
      m ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
          J r q e hRank a ha ha0 =
        Spec.map (CommRingCat.ofHom g) ≫
          (n ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
            J r q e hRank a ha ha0) := Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom g) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R T)) := by rw [hn]
      _ = Spec.map (CommRingCat.ofHom b) := by
        rw [← specMap_ringHom_comp]
        exact congrArg (fun h : R →+* S =>
          Spec.map (CommRingCat.ofHom h))
          (IsScalarTower.algebraMap_eq R T S).symm
  let s : Spec (.of S) ⟶
      pullback (flatGradedProjectiveFamilyNontrivialOpenToBase
        J r q e hRank a ha ha0)
        (Spec.map (CommRingCat.ofHom b)) :=
    pullback.lift m (𝟙 _) hm
  have hs : s ≫ pullback.snd
      (flatGradedProjectiveFamilyNontrivialOpenToBase
        J r q e hRank a ha ha0)
      (Spec.map (CommRingCat.ofHom b)) = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hfst : s ≫ pullback.fst
      (flatGradedProjectiveFamilyNontrivialOpenToBase
        J r q e hRank a ha ha0)
      (Spec.map (CommRingCat.ofHom b)) = m :=
    pullback.lift_fst _ _ _
  let C := coefficientChangedHomogeneousIdeal b J
  have hJC : J.toIdeal.map (MvPolynomial.map b) = C.toIdeal :=
    coefficientChangedHomogeneousIdeal_toIdeal b J
  obtain ⟨p, hp, j, hj, _hpC, hreg, _hcharts, hparam⟩ :=
    flatGradedProjectiveFamilyNontrivialOpen_baseChange_fieldPoint_regularCharts_equationParameter
      J r q e hRank C hJC a ha ha0 s hs
  have hpoint : Spec.map (CommRingCat.ofHom g) ≫
      (n ≫ flatGradedNontrivialOpenToGlobalParameters
        a ha J r q e hRank ha0) =
      projectiveEquationParameter (algebraMap K S) p j hj := by
    calc
      _ = m ≫ flatGradedNontrivialOpenToGlobalParameters
          a ha J r q e hRank ha0 := (Category.assoc _ _ _).symm
      _ = _ := by
        rw [← hfst]
        exact hparam
  obtain ⟨f, hf, hflat⟩ :=
    fixedCubic_localProjectiveIntersectionCharts_flat
      a ha (n ≫ flatGradedNontrivialOpenToGlobalParameters
        a ha J r q e hRank ha0) p hp j hj hpoint hreg
  exact ⟨p, hp, j, hj, f, hf, hflat⟩

/-- At every local point of Voisin's nontrivial moving-equation family,
the actual projective intersection is cut on each fixed-surface chart by
a regular principal equation. -/
theorem flatGradedNontrivialOpen_localPoint_intersectionCharts_regular_principalKernel
    {K R T : Type u} [Field K] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra K R]
    [CommRing T] [IsLocalRing T] [Algebra R T]
    [Algebra K T] [IsScalarTower K R T]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase
      (a.map (algebraMap K (IsLocalRing.ResidueField T)))
      (ha.map (algebraMap K (IsLocalRing.ResidueField T))))]
    (n : Spec (.of T) ⟶
      flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0)
    (hn : n ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
        J r q e hRank a ha ha0 =
      Spec.map (CommRingCat.ofHom (algebraMap R T))) :
    ∃ (j : Monomials (Fin 4) 3)
      (f : ParameterChartRing K (Fin 4) 3 j →+* T),
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j =
        n ≫ flatGradedNontrivialOpenToGlobalParameters
          a ha J r q e hRank ha0 ∧
      ∀ i : Fin 4,
        let p := (normalizedForm K (Fin 4) 3 j).map f
        let hp := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
        let Jₐ := equationIdeal (a.map (algebraMap K T))
          (ha.map (algebraMap K T))
        let x := p.eval₂ (chartBaseMap Jₐ i) (chartCoordinate Jₐ i)
        IsRegular x ∧
          RingHom.ker (chartQuotientMap Jₐ (Jₐ ⊔ equationIdeal p hp)
            (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) i) =
            Ideal.span ({x} : Set (ChartRing Jₐ i)) := by
  let S := IsLocalRing.ResidueField T
  let g := algebraMap T S
  let b := algebraMap R S
  let m : Spec (.of S) ⟶
      flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0 :=
    Spec.map (CommRingCat.ofHom g) ≫ n
  have hm : m ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
      J r q e hRank a ha ha0 =
      Spec.map (CommRingCat.ofHom b) := by
    calc
      m ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
          J r q e hRank a ha ha0 =
        Spec.map (CommRingCat.ofHom g) ≫
          (n ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
            J r q e hRank a ha ha0) := Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom g) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R T)) := by rw [hn]
      _ = Spec.map (CommRingCat.ofHom b) := by
        rw [← specMap_ringHom_comp]
        exact congrArg (fun h : R →+* S =>
          Spec.map (CommRingCat.ofHom h))
          (IsScalarTower.algebraMap_eq R T S).symm
  let s : Spec (.of S) ⟶
      pullback (flatGradedProjectiveFamilyNontrivialOpenToBase
        J r q e hRank a ha ha0)
        (Spec.map (CommRingCat.ofHom b)) :=
    pullback.lift m (𝟙 _) hm
  have hs : s ≫ pullback.snd
      (flatGradedProjectiveFamilyNontrivialOpenToBase
        J r q e hRank a ha ha0)
      (Spec.map (CommRingCat.ofHom b)) = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hfst : s ≫ pullback.fst
      (flatGradedProjectiveFamilyNontrivialOpenToBase
        J r q e hRank a ha ha0)
      (Spec.map (CommRingCat.ofHom b)) = m :=
    pullback.lift_fst _ _ _
  let C := coefficientChangedHomogeneousIdeal b J
  have hJC : J.toIdeal.map (MvPolynomial.map b) = C.toIdeal :=
    coefficientChangedHomogeneousIdeal_toIdeal b J
  obtain ⟨p, hp, j, hj, _hpC, hreg, _hcharts, hparam⟩ :=
    flatGradedProjectiveFamilyNontrivialOpen_baseChange_fieldPoint_regularCharts_equationParameter
      J r q e hRank C hJC a ha ha0 s hs
  have hpoint : Spec.map (CommRingCat.ofHom g) ≫
      (n ≫ flatGradedNontrivialOpenToGlobalParameters
        a ha J r q e hRank ha0) =
      projectiveEquationParameter (algebraMap K S) p j hj := by
    calc
      _ = m ≫ flatGradedNontrivialOpenToGlobalParameters
          a ha J r q e hRank ha0 := (Category.assoc _ _ _).symm
      _ = _ := by
        rw [← hfst]
        exact hparam
  obtain ⟨f, hf, hcartier⟩ :=
    fixedCubic_localProjectiveIntersectionCharts_regular_principalKernel
      a ha (n ≫ flatGradedNontrivialOpenToGlobalParameters
        a ha J r q e hRank ha0) p hp j hj hpoint hreg
  exact ⟨j, f, hf, hcartier⟩

end PfaffianDescent
