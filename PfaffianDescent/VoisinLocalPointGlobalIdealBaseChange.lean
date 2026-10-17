import PfaffianDescent.VoisinNormalizedGlobalIdealBaseChange
import PfaffianDescent.VoisinLocalPointIntersectionFlat

/-!
# Canonical global ideal comparison at actual Voisin local points

Every local point of the nontrivial moving-cubic parameter family has
a normalized coefficient chart whose explicit projective intersection
with the fixed cubic admits canonical ideal-module base change along
an arbitrary further coefficient map.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem flatGradedNontrivialOpen_localPoint_exists_globalIdealBaseChange_any
    {K R T U : Type u} [Field K] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra K R]
    [CommRing T] [IsLocalRing T] [Algebra R T]
    [Algebra K T] [IsScalarTower K R T] [CommRing U]
    (g : T →+* U)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r qRank : ℕ) (e : Fin (r + qRank) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = qRank)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase
      (a.map (algebraMap K (IsLocalRing.ResidueField T)))
      (ha.map (algebraMap K (IsLocalRing.ResidueField T))))]
    (n : Spec (.of T) ⟶
      flatGradedProjectiveFamilyNontrivialOpen J r qRank e hRank a ha ha0)
    (hn : n ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
        J r qRank e hRank a ha ha0 =
      Spec.map (CommRingCat.ofHom (algebraMap R T))) :
    ∃ (p : MvPolynomial (Fin 4) (IsLocalRing.ResidueField T))
      (hp : p.IsHomogeneous 3)
      (j : Monomials (Fin 4) 3) (hj : p.coeff j.1 ≠ 0)
      (f : ParameterChartRing K (Fin 4) 3 j →+* T),
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j =
        n ≫ flatGradedNontrivialOpenToGlobalParameters
          a ha J r qRank e hRank ha0 ∧
      IsRegular (Ideal.Quotient.mk
        (equationIdeal
          (a.map (algebraMap K (IsLocalRing.ResidueField T)))
          (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal
        (((normalizedForm K (Fin 4) 3 j).map f).map
          (algebraMap T (IsLocalRing.ResidueField T)))) ∧
      (let q := (normalizedForm K (Fin 4) 3 j).map f
       let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
       let Jₐ := equationIdeal (a.map (algebraMap K T))
         (ha.map (algebraMap K T))
       let Q := Jₐ ⊔ equationIdeal q hq
       let hJQ : Jₐ.toIdeal ≤ Q.toIdeal := by
         rw [HomogeneousIdeal.toIdeal_sup]
         exact le_sup_left
       let cJ := projectiveCoefficientMap g Jₐ
         (coefficientChangedHomogeneousIdeal g Jₐ)
         (coefficientChangedHomogeneousIdeal_toIdeal g Jₐ)
       let i := schemeQuotientMap Jₐ Q hJQ
       letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion Jₐ Q hJQ
       IsIso (closedImmersionIdealBaseChangeHom cJ i)) := by
  let S := IsLocalRing.ResidueField T
  let b : R →+* S := algebraMap R S
  let m : Spec (.of S) ⟶
      flatGradedProjectiveFamilyNontrivialOpen J r qRank e hRank a ha ha0 :=
    Spec.map (CommRingCat.ofHom (algebraMap T S)) ≫ n
  have hm : m ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
      J r qRank e hRank a ha ha0 =
      Spec.map (CommRingCat.ofHom b) := by
    calc
      m ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
          J r qRank e hRank a ha ha0 =
        Spec.map (CommRingCat.ofHom (algebraMap T S)) ≫
          (n ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
            J r qRank e hRank a ha ha0) := Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom (algebraMap T S)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R T)) := by rw [hn]
      _ = Spec.map (CommRingCat.ofHom b) := by
        rw [← specMap_ringHom_comp]
        exact congrArg (fun h : R →+* S =>
          Spec.map (CommRingCat.ofHom h))
          (IsScalarTower.algebraMap_eq R T S).symm
  let s : Spec (.of S) ⟶
      pullback (flatGradedProjectiveFamilyNontrivialOpenToBase
        J r qRank e hRank a ha ha0)
        (Spec.map (CommRingCat.ofHom b)) :=
    pullback.lift m (𝟙 _) hm
  have hs : s ≫ pullback.snd
      (flatGradedProjectiveFamilyNontrivialOpenToBase
        J r qRank e hRank a ha ha0)
      (Spec.map (CommRingCat.ofHom b)) = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hfst : s ≫ pullback.fst
      (flatGradedProjectiveFamilyNontrivialOpenToBase
        J r qRank e hRank a ha ha0)
      (Spec.map (CommRingCat.ofHom b)) = m :=
    pullback.lift_fst _ _ _
  let C := coefficientChangedHomogeneousIdeal b J
  have hJC : J.toIdeal.map (MvPolynomial.map b) = C.toIdeal :=
    coefficientChangedHomogeneousIdeal_toIdeal b J
  obtain ⟨p, hp, j, hj, _hpC, hreg, _hcharts, hparam⟩ :=
    flatGradedProjectiveFamilyNontrivialOpen_baseChange_fieldPoint_regularCharts_equationParameter
      J r qRank e hRank C hJC a ha ha0 s hs
  have hpoint : Spec.map (CommRingCat.ofHom (algebraMap T S)) ≫
      (n ≫ flatGradedNontrivialOpenToGlobalParameters
        a ha J r qRank e hRank ha0) =
      projectiveEquationParameter (algebraMap K S) p j hj := by
    calc
      _ = m ≫ flatGradedNontrivialOpenToGlobalParameters
          a ha J r qRank e hRank ha0 := (Category.assoc _ _ _).symm
      _ = _ := by
        rw [← hfst]
        exact hparam
  obtain ⟨f, hf, hres, hIso⟩ :=
    exists_fixedCubic_localProjectiveGlobalIdealBaseChange_any
      g a ha (n ≫ flatGradedNontrivialOpenToGlobalParameters
        a ha J r qRank e hRank ha0) p hp j hj hpoint hreg
  exact ⟨p, hp, j, hj, f, hf, hres, hIso⟩

end PfaffianDescent
